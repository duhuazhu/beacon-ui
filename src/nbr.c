/*
 * nbr.c - "附近基站" page. See include/nbr.h.
 *
 * Files (all written by background shell jobs, read by the render path):
 *   /tmp/u60-nbr.json        datad neighbor.status reply (live, passive)
 *   /tmp/u60-nbrfw.json      firmware lists: {"nr5g_nbr_contents":"..."} then
 *                            {"lte_nbr_contents":"..."} (pci,arfcn,band,rsrp;...)
 *   /tmp/u60-nbrscan.state   "run <epoch>" while the firmware scan runs, then
 *                            "ok <epoch>" / "fail <epoch>"
 *   /tmp/u60-nbr-lease       touched every 30 s while the page is in use;
 *                            idle-guard.sh stops a collector whose lease is
 *                            older than 90 s (covers a crashed/restarted UI)
 *   /tmp/u60-nbr-off.json    datad's reply to neighbor.set false (confirms it)
 *
 * SPDX-License-Identifier: MIT
 */
#include "nbr.h"
#include "json.h"

#include <arpa/inet.h>
#include <ctype.h>
#include <netinet/in.h>
#include <pthread.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>

#define DATAD_PORT  9460
#define DATAD_TOKEN "/data/plugins/zwrt-datad/auth.token"
#define F_LIVE      "/tmp/u60-nbr.json"
#define F_FW        "/tmp/u60-nbrfw.json"
#define F_SCAN      "/tmp/u60-nbrscan.state"
#define F_LEASE     "/tmp/u60-nbr-lease"
#define F_OFF       "/tmp/u60-nbr-off.json"
#define MAX_CELLS   16
#define F_SCAN_SH   "/tmp/u60-nbrscan.sh"
/* Firmware neighbour scan button. Off: on this MU5250 firmware the modem
 * answers manual_search_fail within ~2 s (tested 2026-10-02 both in auto and
 * in Only_5G mode) while the firmware still drops the data call for 2-6 s. */
#define NBR_FW_SCAN 0

/* state file: "run <t>" then "ok <t>" / "fail <t> <rejected|nosa|timeout>" */
static const char SCAN_SH[] =
    "S=" F_SCAN "; F=" F_FW "; NI='ubus -t 5 call zte_nwinfo_api'\n"
    "echo \"run $(date +%s)\" > $S\n"
    "orig=$($NI nwinfo_get_netinfo 2>/dev/null | sed -n 's/.*\"net_select\": *\"\\([A-Za-z0-9_]*\\)\".*/\\1/p' | head -1)\n"
    "r=fail; why=rejected\n"
    "if [ -n \"$orig\" ] && [ \"$orig\" != Only_5G ]; then\n"
    "  $NI nwinfo_set_netselect '{\"net_select\":\"Only_5G\"}' >/dev/null 2>&1\n"
    "  why=nosa; i=0\n"
    "  while [ $i -lt 40 ]; do sleep 1; i=$((i+1))\n"
    "    t=$($NI nwinfo_get_netinfo 2>/dev/null | sed -n 's/.*\"network_type\": *\"\\([^\"]*\\)\".*/\\1/p' | head -1)\n"
    "    [ \"$t\" = SA ] && { why=rejected; break; }\n"
    "  done\n"
    "fi\n"
    "if [ \"$why\" != nosa ]; then\n"
    "  $NI nwinfo_scan_nbr '{}' >/dev/null 2>&1; sleep 2; i=0; why=timeout\n"
    "  while [ $i -lt 100 ]; do\n"
    "    s=$($NI nwinfo_m_netselect_status 2>/dev/null)\n"
    "    case \"$s\" in \"\"|*manual_selecting*) ;; *manual_search_fail*) why=rejected; break ;; *) r=ok; why=; break ;; esac\n"
    "    sleep 1; i=$((i+1))\n"
    "  done\n"
    "  ($NI nwinfo_get_nr5g_nbr_contents; $NI nwinfo_get_lte_nbr_contents) > $F.n 2>/dev/null && mv $F.n $F\n"
    "fi\n"
    "if [ -n \"$orig\" ] && [ \"$orig\" != Only_5G ]; then\n"
    "  $NI nwinfo_set_netselect \"{\\\"net_select\\\":\\\"$orig\\\"}\" >/dev/null 2>&1\n"
    "fi\n"
    "echo \"$r $(date +%s) $why\" > $S\n";

typedef struct {
    int  nr;              /* 1 = NR, 0 = LTE */
    int  pci;
    long arfcn;           /* 0 = unknown */
    int  band;            /* 0 = unknown */
    int  has_rsrp;
    double rsrp;
} cell_t;

static int      g_live_on;          /* we asked datad to collect */
static uint32_t g_live_set_at;      /* last neighbor.set true */
static uint32_t g_live_poll_at;
static uint32_t g_off_since;        /* page left / screen dark since */
static int      g_off_pending = 1;  /* neighbor.set false not confirmed yet (1 at start:
                                     * a previous UI may have died with it on) */
static uint32_t g_off_try_at;
static int      g_off_tries;        /* datad 没装或不认这个动作时，不能无限每 2 秒开线程 */
static uint32_t g_fw_poll_at;
static uint32_t g_scan_armed_until; /* first tap on "scan" arms it */

static uint32_t elapsed(uint32_t now, uint32_t then) { return now - then; }

/* ---- datad control (POST JSON with the bearer token) ---- */
static int read_token(char *out, size_t cap)
{
    FILE *f = fopen(DATAD_TOKEN, "r");
    if (!f) return 0;
    size_t n = fread(out, 1, cap - 1, f);
    fclose(f);
    out[n] = 0;
    out[strcspn(out, "\r\n \t")] = 0;
    if (!out[0]) return 0;
    for (char *p = out; *p; p++)            /* it goes into an HTTP header line */
        if (!isalnum((unsigned char)*p) && *p != '-' && *p != '_' && *p != '.') return 0;
    return 1;
}

/* Fire-and-forget POST on a detached thread (the firmware wget has no
 * --header, and the render path must never wait on datad). The reply body
 * (if out != NULL) lands atomically in out. At most 3 requests in flight. */
struct post_req { char body[160]; char out[64]; };
static volatile int g_inflight;

static void *post_thread(void *arg)
{
    struct post_req *r = arg;
    char tok[160], buf[16384];
    int fd = -1, len = 0;
    if (!read_token(tok, sizeof tok)) goto done;
    fd = socket(AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0);
    if (fd < 0) goto done;
    struct timeval tv = { 3, 0 };
    setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);
    setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof tv);
    struct sockaddr_in sa; memset(&sa, 0, sizeof sa);
    sa.sin_family = AF_INET; sa.sin_port = htons(DATAD_PORT);
    sa.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    if (connect(fd, (struct sockaddr *)&sa, sizeof sa) < 0) goto done;
    char req[512];
    int rl = snprintf(req, sizeof req,
                      "POST /control HTTP/1.0\r\nHost: 127.0.0.1\r\nAuthorization: Bearer %s\r\n"
                      "Content-Type: application/json\r\nContent-Length: %d\r\nConnection: close\r\n\r\n%s",
                      tok, (int)strlen(r->body), r->body);
    if (rl <= 0 || rl >= (int)sizeof req || send(fd, req, rl, MSG_NOSIGNAL) != rl) goto done;
    if (!r->out[0]) goto done;
    for (;;) {
        ssize_t n = recv(fd, buf + len, sizeof buf - 1 - len, 0);
        if (n <= 0) break;
        len += (int)n;
        if (len >= (int)sizeof buf - 1) break;
    }
    buf[len] = 0;
    if (strncmp(buf, "HTTP/1.", 7) || atoi(buf + 9) != 200) goto done;
    char *body = strstr(buf, "\r\n\r\n");
    if (!body) goto done;
    body += 4;
    char tmp[80]; snprintf(tmp, sizeof tmp, "%s.n", r->out);
    FILE *f = fopen(tmp, "w");
    if (f) {
        fputs(body, f);
        if (fclose(f) == 0) rename(tmp, r->out); else unlink(tmp);
    }
done:
    if (fd >= 0) close(fd);
    free(r);
    __sync_fetch_and_sub(&g_inflight, 1);
    return NULL;
}

static void datad_post(const char *body, const char *out)
{
    if (g_inflight >= 3) return;                    /* datad stuck/frozen: don't pile up */
    struct post_req *r = calloc(1, sizeof *r);
    if (!r) return;
    snprintf(r->body, sizeof r->body, "%s", body);
    if (out) snprintf(r->out, sizeof r->out, "%s", out);
    pthread_attr_t at; pthread_attr_init(&at);
    pthread_attr_setdetachstate(&at, PTHREAD_CREATE_DETACHED);
    pthread_attr_setstacksize(&at, 64 * 1024);
    pthread_t th;
    __sync_fetch_and_add(&g_inflight, 1);
    if (pthread_create(&th, &at, post_thread, r) != 0) { __sync_fetch_and_sub(&g_inflight, 1); free(r); }
    pthread_attr_destroy(&at);
}

static int scan_running(time_t *since)
{
    char buf[64] = "";
    FILE *f = fopen(F_SCAN, "r");
    if (!f) return 0;
    if (!fgets(buf, sizeof buf, f)) buf[0] = 0;
    fclose(f);
    long t = 0;
    if (strncmp(buf, "run ", 4) || sscanf(buf + 4, "%ld", &t) != 1) return 0;
    if (time(NULL) - t > 150) return 0;     /* job died: don't block the button forever */
    if (since) *since = (time_t)t;
    return 1;
}

static void fw_refresh(void)
{
    /* the getters only read the firmware's cached lists: no radio activity */
    system("(ubus -t 4 call zte_nwinfo_api nwinfo_get_nr5g_nbr_contents; "
           "ubus -t 4 call zte_nwinfo_api nwinfo_get_lte_nbr_contents) > " F_FW ".n 2>/dev/null "
           "&& mv " F_FW ".n " F_FW " &");
}

static void touch_lease(void)
{
    FILE *f = fopen(F_LEASE, "w");
    if (f) fclose(f);
}

void nbr_tick(int on_page, int screen_on, uint32_t now)
{
    if (g_scan_armed_until && (int32_t)(now - g_scan_armed_until) > 0) g_scan_armed_until = 0;   /* armed prompt expired */
    if (on_page) {
        g_off_since = 0;
        g_off_pending = 0;
        /* (re)enable every 30 s: a datad restart silently resets it to off;
         * the same beat renews the lease idle-guard checks */
        if (!g_live_on || elapsed(now, g_live_set_at) >= 30000) {
            datad_post("{\"action\":\"neighbor.set\",\"params\":{\"enabled\":true}}", NULL);
            touch_lease();
            g_live_on = 1; g_live_set_at = now ? now : 1;
            g_live_poll_at = now - 1500;    /* first status read ~0.5 s later */
        }
        if (elapsed(now, g_live_poll_at) >= 2000) {
            datad_post("{\"action\":\"neighbor.status\",\"params\":{}}", F_LIVE);
            g_live_poll_at = now;
        }
        /* 先比时间再查扫描状态：这个函数每帧都进，别每 30ms 就 fopen 一次 */
        if (!g_fw_poll_at || (elapsed(now, g_fw_poll_at) >= 3000 &&
                              elapsed(now, g_fw_poll_at) >= (scan_running(NULL) ? 3000u : 10000u))) {
            if (!scan_running(NULL)) fw_refresh();
            g_fw_poll_at = now ? now : 1;
        }
        return;
    }
    /* off the page: stop the collector right away when the screen goes dark,
     * after 10 s otherwise (quick back-and-forth keeps it) */
    if (g_live_on) {
        if (!g_off_since) g_off_since = now ? now : 1;
        if (!screen_on || elapsed(now, g_off_since) >= 10000) {
            g_live_on = 0; g_off_since = 0; g_fw_poll_at = 0;
            g_off_pending = 1; g_off_try_at = 0; g_off_tries = 0;
            unlink(F_LIVE);
            unlink(F_LEASE);
        }
    }
    /* datad_post drops requests while 3 are in flight (slow or frozen datad),
     * so resend every 2 s until datad's reply confirms the collector is off */
    if (g_off_pending) {
        if (access(F_OFF, F_OK) == 0) {
            unlink(F_OFF);
            g_off_pending = 0;
        } else if (!g_off_try_at || elapsed(now, g_off_try_at) >= 2000) {
            if (++g_off_tries > 30) g_off_pending = 0;   /* 约 60 秒没确认就放弃 */
            else datad_post("{\"action\":\"neighbor.set\",\"params\":{\"enabled\":false}}", F_OFF);
            g_off_try_at = now ? now : 1;
        }
    }
}

/* ---- parsing ---- */
static char *slurp(const char *path, size_t max)
{
    FILE *f = fopen(path, "r");
    if (!f) return NULL;
    char *b = malloc(max + 1);
    if (!b) { fclose(f); return NULL; }
    size_t n = fread(b, 1, max, f);
    fclose(f);
    b[n] = 0;
    return b;
}

/* "pci,arfcn,band,rsrp;..." as parsed by the stock web UI (util.js
 * parseNeighborCellInfo). Band may come as "78" or "n78". */
static int parse_fw_list(const char *s, int nr, cell_t *out, int n, int cap)
{
    char buf[2048];
    snprintf(buf, sizeof buf, "%s", s);
    for (char *sv = NULL, *row = strtok_r(buf, ";", &sv); row && n < cap; row = strtok_r(NULL, ";", &sv)) {
        char *f[6] = { 0 }; int nf = 0;
        for (char *sv2 = NULL, *x = strtok_r(row, ",", &sv2); x && nf < 6; x = strtok_r(NULL, ",", &sv2)) f[nf++] = x;
        if (nf < 2) continue;
        cell_t c = { 0 };
        c.nr = nr;
        c.pci = atoi(f[0]);
        c.arfcn = atol(f[1]);
        if (nf > 2) { const char *b = f[2]; while (*b && !isdigit((unsigned char)*b)) b++; c.band = atoi(b); }
        if (nf > 3 && f[3][0]) {
            char *e; double v = strtod(f[3], &e);
            if (e != f[3] && v < 0 && v > -160) { c.has_rsrp = 1; c.rsrp = v; }
        }
        if (c.pci < 0 || c.pci > 1007 || (c.pci == 0 && c.arfcn == 0)) continue;
        out[n++] = c;
    }
    return n;
}

/* datad: ..."cells":[{"rat":"NR","pci":1,"arfcn":2,"band":78,"rsrp_dbm":-90.5,...},...] */
static int parse_live(const char *js, cell_t *out, int cap, char *status, size_t scap, char *reason, size_t rcap, int *partial)
{
    const char *nb = strstr(js, "\"neighbor\"");
    const char *base = nb ? nb : js;
    status[0] = reason[0] = 0; *partial = 0;
    json_get(base, "status", status, scap);
    json_get(base, "reason", reason, rcap);
    char pv[8] = "";
    if (json_get(base, "partial", pv, sizeof pv)) *partial = !strcmp(pv, "true");
    const char *p = strstr(base, "\"cells\"");
    if (!p) return 0;
    p = strchr(p, '[');
    if (!p) return 0;
    int n = 0;
    while (n < cap) {
        const char *o = strchr(p, '{'), *end = strchr(p, ']');
        if (!o || (end && end < o)) break;
        const char *c = strchr(o, '}');
        if (!c) break;
        char obj[512];
        size_t l = (size_t)(c - o + 1); if (l >= sizeof obj) l = sizeof obj - 1;
        memcpy(obj, o, l); obj[l] = 0;
        char rat[8] = "", v[32];
        cell_t cl = { 0 };
        json_get(obj, "rat", rat, sizeof rat);
        cl.nr = !strcmp(rat, "NR");
        cl.pci = (int)json_get_int(obj, "pci", -1);
        cl.arfcn = json_get_int(obj, "arfcn", 0);
        cl.band = (int)json_get_int(obj, "band", 0);
        if (json_get(obj, "rsrp_dbm", v, sizeof v) && strcmp(v, "null")) {
            char *e; double r = strtod(v, &e);
            if (e != v) { cl.has_rsrp = 1; cl.rsrp = r; }
        }
        if (cl.pci >= 0 && cl.pci <= 1007 && (rat[0] == 'N' || rat[0] == 'L')) out[n++] = cl;
        p = c + 1;
    }
    return n;
}

static int by_rsrp(const void *a, const void *b)
{
    const cell_t *x = a, *y = b;
    if (x->has_rsrp != y->has_rsrp) return y->has_rsrp - x->has_rsrp;
    if (x->has_rsrp && x->rsrp != y->rsrp) return x->rsrp < y->rsrp ? 1 : -1;
    return x->pci - y->pci;
}

/* signal bar width (0-100) for RSRP -125..-75 dBm */
static int rsrp_pct(double r)
{
    int p = (int)((r + 125.0) * 2.0);
    return p < 4 ? 4 : p > 100 ? 100 : p;
}
static const char *rsrp_cls(double r) { return r >= -95 ? "good" : r >= -110 ? "mid" : "bad"; }

#define APP(...) do { if (o < (int)sizeof g_html) o += snprintf(g_html + o, sizeof g_html - o, __VA_ARGS__); } while (0)
static char g_html[20000];   /* 16+16 行邻区约 330 字节一行，12000 会在标签中间截断 */

/* an aggregated carrier already in use (pci on that arfcn) is not a neighbour */
static int in_ca(const nbr_serving_t *sv, const cell_t *c)
{
    if (!sv || !c->nr || !c->arfcn) return 0;
    char ca[256]; snprintf(ca, sizeof ca, "%s", sv->nrca);
    for (char *s1 = NULL, *g = strtok_r(ca, ";", &s1); g; g = strtok_r(NULL, ";", &s1)) {
        int idx, pci, x, band; long arf;
        if (sscanf(g, "%d,%d,%d,%d,%ld", &idx, &pci, &x, &band, &arf) == 5 && pci == c->pci && arf == c->arfcn) return 1;
    }
    return 0;
}

/* measured cells as full rows; the rest (seen in system info, never measured)
 * as one compact line - nothing to rank and too risky to offer for locking */
static void rows(int *po, const cell_t *c, int n, const nbr_serving_t *sv, const char *armed)
{
    int o = *po, shown = 0;
    char rest[600] = ""; int ro = 0, nrest = 0;
    for (int k = 0; k < n; k++) {
        if (in_ca(sv, &c[k])) continue;
        if (!c[k].has_rsrp) {
            if (ro < (int)sizeof rest - 40)
                ro += c[k].band ? snprintf(rest + ro, sizeof rest - ro, "%s%s%d PCI %d", nrest ? "、" : "",
                                           c[k].nr ? "n" : "B", c[k].band, c[k].pci)
                                : snprintf(rest + ro, sizeof rest - ro, "%sPCI %d", nrest ? "、" : "", c[k].pci);
            nrest++;
            continue;
        }
        shown++;
        char sub[48], rs[16], btn[200] = "";
        if (c[k].band && c[k].arfcn) snprintf(sub, sizeof sub, "%s%d · %ld", c[k].nr ? "n" : "B", c[k].band, c[k].arfcn);
        else if (c[k].arfcn) snprintf(sub, sizeof sub, "%s · %ld", c[k].nr ? "5G" : "4G", c[k].arfcn);
        else snprintf(sub, sizeof sub, "%s · 频点未知", c[k].nr ? "5G" : "4G");
        if (c[k].has_rsrp) snprintf(rs, sizeof rs, "%.0f", c[k].rsrp); else snprintf(rs, sizeof rs, "--");
        int serving = sv && c[k].pci == sv->pci && (!c[k].arfcn || c[k].arfcn == sv->arfcn) && c[k].nr == sv->nr;
        if (serving)
            snprintf(btn, sizeof btn, "<span class='pill good nbpill'><i></i>当前</span>");
        else if (c[k].nr && c[k].arfcn > 0 && c[k].band > 0) {
            char key[64]; snprintf(key, sizeof key, "lock:%d:%ld:%d", c[k].pci, c[k].arfcn, c[k].band);
            snprintf(btn, sizeof btn, "<a href='act:cl:%s' class='mini-btn'>%s</a>", key,
                     armed && !strcmp(armed, key) ? "再点一次" : "锁定");
        }
        /* floats first (litehtml wraps a right float that follows inline text) */
        APP("<div class='nbrow'>%s<span class='nbr-v'><span class='n %s'>%s</span><span class='u'>dBm</span></span>"
            "<span class='nbr-l'><span class='n'>PCI %d</span><span class='k'>%s</span></span>"
            "<span class='nbr-bar'><i class='%s' style='width:%d%%'></i></span></div>",
            btn, c[k].has_rsrp ? rsrp_cls(c[k].rsrp) : "", rs, c[k].pci, sub,
            c[k].has_rsrp ? rsrp_cls(c[k].rsrp) : "", c[k].has_rsrp ? rsrp_pct(c[k].rsrp) : 0);
    }
    if (!shown) APP("<div class='k nbr-empty'>还没有测到邻区信号强度</div>");
    if (nrest) APP("<div class='k nbr-rest'>另有 %d 个小区未测到信号：%s</div>", nrest, rest);
    *po = o;
}

static const char *live_word(const char *st, const char *reason)
{
    if (!st[0] || !strcmp(st, "starting") || !strcmp(st, "disabled")) return "正在启动采集…";
    if (!strcmp(st, "collecting")) return "正在监听基带信令…";
    if (!strcmp(st, "empty"))
        return !strcmp(reason, "no_supported_reports") ? "收到信令但当前固件格式无法识别" : "暂时没有听到邻区";
    if (!strcmp(st, "stale")) return "数据已过期，正在更新";
    if (!strcmp(st, "blocked")) return "诊断通道被其他程序占用";
    if (!strcmp(st, "dependency_missing")) return "固件缺少 diag_mdlog，无法采集";
    if (!strcmp(st, "error")) return "采集出错，稍后自动重试";
    if (!strcmp(st, "stopping")) return "正在停止…";
    return "";
}

const char *nbr_body_html(const nbr_serving_t *sv, const char *armed)
{
    int o = 0;
    g_html[0] = 0;

    /* serving cell */
    if (sv && sv->pci > 0) {
        APP("<div class='card clcur'><div class='k'>当前基站 · %s%s</div><span class='n clbig'>PCI %d</span>"
            "<span class='u'>ARFCN %ld</span><div class='k'>RSRP <span class='n hv'>%s</span> · SINR <span class='n hv'>%s</span></div></div>",
            sv->nr ? "n" : "B", sv->band[0] ? sv->band : "?", sv->pci, sv->arfcn, sv->rsrp, sv->sinr);
    } else {
        APP("<div class='card'><div class='k'>当前没有注册到基站</div></div>");
    }

    /* an active 5G cell lock (set here, on 锁基站, or by 断网自救): show it, undo in place */
    if (sv && sv->lock[0]) {
        int lp = 0; long la = 0;
        sscanf(sv->lock, "%d,%ld", &lp, &la);
        APP("<div class='card clcur'><a href='act:cl:unlock' class='mini-btn'>解除锁定</a>"
            "<div class='k'>已锁定 5G 基站</div><span class='n'>PCI %d</span><span class='u'>ARFCN %ld</span></div>", lp, la);
    }

    /* live (datad, passive) */
    cell_t live[MAX_CELLS]; int nl = 0, partial = 0;
    char st[24] = "", reason[48] = "";
    char *js = slurp(F_LIVE, 32768);
    if (js) { nl = parse_live(js, live, MAX_CELLS, st, sizeof st, reason, sizeof reason, &partial); free(js); }
    qsort(live, nl, sizeof live[0], by_rsrp);
    APP("<div class='card list'><div class='k cap'>实时邻区<span class='nbr-tag'>不断网</span></div>");
    if (nl) {
        rows(&o, live, nl, sv, armed);
        if (partial) APP("<div class='k pxnote'>部分信令丢失，列表可能不完整</div>");
    } else {
        APP("<div class='k nbr-empty'>%s</div>", live_word(st, reason));
    }
    APP("</div>");

    /* firmware lists (cached by the modem; NR filled only by a scan) */
    cell_t fw[MAX_CELLS]; int nf = 0;
    char *fj = slurp(F_FW, 8192);
    if (fj) {
        char v[2048];
        if (json_get(fj, "nr5g_nbr_contents", v, sizeof v)) nf = parse_fw_list(v, 1, fw, nf, MAX_CELLS);
        if (json_get(fj, "lte_nbr_contents", v, sizeof v)) nf = parse_fw_list(v, 0, fw, nf, MAX_CELLS);
        free(fj);
    }
    qsort(fw, nf, sizeof fw[0], by_rsrp);
    time_t since = 0;
    int running = scan_running(&since);
    char when[48] = "";
    {
        char buf[64] = ""; long t = 0;
        FILE *f = fopen(F_SCAN, "r");
        if (f) { if (!fgets(buf, sizeof buf, f)) buf[0] = 0; fclose(f); }
        char why[16] = "";
        if (!running && sscanf(buf, "%*s %ld %15s", &t, why) >= 1 && t > 0) {
            struct tm tm; time_t tt = (time_t)t; localtime_r(&tt, &tm);
            const char *w = !strncmp(buf, "ok", 2) ? "上次扫描" : !strcmp(why, "nosa") ? "失败·无 SA 信号"
                          : !strcmp(why, "timeout") ? "失败·超时" : "扫描失败";
            snprintf(when, sizeof when, "%s %02d:%02d", w, tm.tm_hour, tm.tm_min);
        }
    }
    if (NBR_FW_SCAN || nf || running) {
        APP("<div class='card list'><div class='k cap'>%s%s%s%s</div>",
            when[0] ? "<span class='nbr-when'>" : "", when, when[0] ? "</span>" : "",
            NBR_FW_SCAN ? "原厂扫描<span class='nbr-tag nbr-warn'>会断网</span>" : "原厂邻区列表");
        if (nf) rows(&o, fw, nf, sv, armed);
        else APP("<div class='k nbr-empty'>%s</div>", running ? "正在扫描…" : "还没有扫描结果（4G 邻区在连 4G 时会自动出现）");
        APP("</div>");
    }

    if (!NBR_FW_SCAN) {
        APP("<div class='k pxnote'>只显示同频邻区 · 点两次「锁定」锁到该基站</div>");
        return g_html;
    }
    if (running) {
        long s = (long)(time(NULL) - since);
        APP("<div class='card resetbtn2 nbr-busy'>正在扫描附近 5G 基站… %ld 秒</div>", s < 0 ? 0 : s);
    } else if (g_scan_armed_until) {
        APP("<a href='act:nbr:scan' class='card resetbtn2 nbr-arm'>再点一次开始扫描（断网约 15 秒）</a>");
    } else {
        APP("<a href='act:nbr:scan' class='card resetbtn2'>扫描附近 5G 基站</a>");
    }
    APP("<div class='k pxnote'>实时邻区靠旁听基带信令，不影响上网，只在打开本页时运行。"
        "原厂扫描更全，但扫描期间会断网十几秒，结束后自动重连。点「锁定」两次可锁到该 5G 基站，锁错可在「锁基站」页解除。</div>");
    return g_html;
}

int nbr_handle_action(const char *a, uint32_t now, char *toast, size_t tcap)
{
    if (strncmp(a, "nbr:", 4)) return 0;
    if (!strcmp(a + 4, "scan")) {
        if (!NBR_FW_SCAN) return 1;
        if (scan_running(NULL)) return 1;
        if (!g_scan_armed_until || (int32_t)(now - g_scan_armed_until) > 0) {   /* first tap: arm for 4 s */
            g_scan_armed_until = now + 4000;
            if (!g_scan_armed_until) g_scan_armed_until = 1;
            return 1;
        }
        g_scan_armed_until = 0;
        /* stock web flow (service_rpc.js): scan_nbr, poll m_netselect_status while
         * "manual_selecting", then read the NR list. The firmware answers
         * manual_search_fail unless the bearer is "5G SA only" (the stock page
         * tells users to switch by hand), so switch to Only_5G for the scan and
         * always put the original mode back. Runs detached: finishes (and
         * restores) even if the UI restarts meanwhile. */
        FILE *f = fopen(F_SCAN_SH, "w");
        if (!f) return 1;
        fputs(SCAN_SH, f);
        fclose(f);
        system("sh " F_SCAN_SH " >/dev/null 2>&1 &");
        g_fw_poll_at = now ? now : 1;
        if (toast && tcap) snprintf(toast, tcap, "开始扫描，网络会断开十几秒");
        return 1;
    }
    return 0;
}
