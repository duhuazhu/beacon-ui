/*
 * htmlmain.c - HTML UI shell. The program is fixed; the UI lives in
 * /data/plugins/u60pro-devui/ui
 * as plain HTML/CSS. Each *.html (except menu.html) is a swipeable page;
 * {{TOKENS}} are filled from the zwrt-datad snapshot. Touch swipes pages and
 * taps fire anchor actions (href="act:..."). Power key: short = backlight,
 * long = the menu.html overlay.
 *
 * SPDX-License-Identifier: MIT
 */
#include "drm_disp.h"
#include "data.h"
#include "json.h"
#include "touch_input.h"
#include "key_input.h"
#include "backlight.h"
#include "devui_ext.h"
#include "nbr.h"
#include "update.h"
#include "qrcodegen.h"

#include <arpa/inet.h>
#include <dirent.h>
#include <math.h>
#include <netinet/in.h>
#include <pthread.h>
#include <signal.h>
#include <poll.h>
#include <ctype.h>
#include <ucontext.h>
#include <fcntl.h>
#include <stdint.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <time.h>
#include <unistd.h>

extern void        html_view_init(uint16_t *fb, int w, int h, int pitch_px, int rotate, const char *font_path);
extern void        html_view_set_num_font(const char *path);
extern void        html_view_set_wallpaper(const char *path);
extern void        html_view_paint_wallpaper(int x, int y, int w, int h, int tr, int tg, int tb, int ta);
extern int         html_view_has_wallpaper(void);
extern void        html_view_native_num(int on);
extern void        html_view_aa_line(float x0, float y0, float x1, float y1, float wd, int r, int g, int b, int a);
extern void        html_view_clip_rect(int x, int y, int w, int h);
extern void        html_view_save_rect(int x, int y, int w, int h, uint16_t *buf);
extern void        html_view_restore_rect(int x, int y, int w, int h, const uint16_t *buf);
extern void        html_view_draw_thumb(const char *path, int x, int y, int w, int h, int rad);
extern void        html_view_aa_disc(float cx, float cy, float rad, int r, int g, int b, int a);
extern void        html_view_set_uidir(const char *dir);
extern int         html_view_render_html(const char *html);
extern int         html_view_render_to(uint16_t *buf, const char *html);
extern int         html_view_render_to_scroll(uint16_t *buf, const char *html, int scroll);
extern void        html_view_target_begin(uint16_t *buf, int scroll);
extern void        html_view_target_end(void);
extern const char *html_view_click(float x, float y);
extern int         html_view_rect(const char *sel, int *x, int *y, int *w, int *h);
extern void        html_view_polyline(int x, int y, int w, int h, const int *vals, int n,
                                      int vmin, int vmax, int r, int g, int b, int thick, int fill_a);
extern void        html_view_set_scroll(int y);
extern void        html_view_set_clip_top(int y);
extern void        html_view_fill_rect(int x, int y, int w, int h, int r, int g, int b, int a);
extern void        html_view_fill_poly(const int *xs, const int *ys, int n, int r, int g, int b, int a);
extern void        html_view_fill_round_rect(int x, int y, int w, int h, int rad, int r, int g, int b, int a);
extern int         html_view_text_width_px(const char *text, int size);
extern void        html_view_text_bounds_px(const char *text, int size, int *x0, int *y0, int *x1, int *y1);
extern void        html_view_draw_text_px(int x, int y, const char *text, int size, int bold,
                                          int r, int g, int b, int a);
extern void        html_view_draw_text_contrast_px(int x, int y, const char *text, int size, int bold,
                                                   int dr, int dg, int db, int lr, int lg, int lb, int a);
extern int         html_view_render_tall(uint16_t *buf, const char *html, int bufh);
extern int         html_view_render_overlay(const char *html);
static void        maybe_dump_fb(drm_disp_t *d);

#ifndef UI_DIR
#define UI_DIR "/data/plugins/u60pro-devui/ui"
#endif
#define FUNCTIONS_DIR UI_DIR "/functions"
#define UI_FONT "/usr/ui/fonts/ZTEZhengYuan.ttf"
#define UI_NUM_FONT "/usr/ui/fonts/Oswald-Regular.ttf"

/* The rootfs is read-only and the vendor font is thin at small sizes, so allow
 * an override via the DEVUI_FONT env var. Falls back to UI_FONT (with a log
 * line) when the override is unset or unreadable. */
static const char *resolve_ui_font(void)
{
    const char *env = getenv("DEVUI_FONT");
    if (env && *env) {
        if (access(env, R_OK) == 0) return env;
        fprintf(stderr, "DEVUI_FONT=%s unreadable, using %s\n", env, UI_FONT);
    }
    return UI_FONT;
}
#define DATAD_HTTP_ADDR "127.0.0.1"
#define DATAD_HTTP_PORT 9460
#define DATAD_HTTP_TIMEOUT_MS 300

static volatile sig_atomic_t g_run = 1;
static void on_sig(int s) { (void)s; g_run = 0; }

static uint32_t millis(void)
{
    struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint32_t)(ts.tv_sec * 1000 + ts.tv_nsec / 1000000);
}

#define TEMPLATE_CACHE_CAP 8
#define PAGE_HTML_CACHE_CAP 1048576

struct template_cache_entry {
    char path[320];
    long long mtime_ns;
    char *content;
    int used;
};

static struct template_cache_entry g_tmpl_cache[TEMPLATE_CACHE_CAP];
static int g_tmpl_next;

/* ---- pages / theme ---- */
static char g_pages[24][288];
static int  g_npages, g_cur;
static char g_subpage[64];       /* non-empty = a second-level page under ui/subpages */
static char g_subpage_path[300];
static int  g_theme;      /* effective: 0 = dark, 1 = light */
static int  g_theme_mode; /* 0 = follow wallpaper, 1 = dark, 2 = light */
static int  g_wifi_sleep_min = 30; /* WiFi sleep after N min with no clients (0 = never); applied by idle-guard.sh */
static int  g_chg_cap;            /* 充电上限 %: 0 = off, else 70/80/90/95 (idle-guard switches direct supply) */
static int  g_plan_on = 0, g_plan_gb = 2000;   /* 流量套餐: monthly cap on/off + GB (1 GB = 2^30 bytes, like the counters) */
static int  g_chg_cur;            /* 充电限流 mA: 0 = stock, else 2000/1500/1000/500 (idle-guard writes qcom-battery) */
#define CHGCAP_USER "/tmp/u60-chgcap-user"   /* user picked a supply mode by hand: idle-guard leaves it alone */
#define CHGCAP_MARK "/data/plugins/u60pro-devui/chgcap.dps"   /* idle-guard turned direct supply on for the cap */
#define IDLE_GUARD_CHARGE "sh /data/ufi-tools/data/idle-guard.sh charge >/dev/null 2>&1 &"

static int  g_show_key;   /* reveal WiFi password (default hidden) */
static int  g_show_cellid; /* reveal NR Cell ID (default hidden) */
static int  g_show_imei;   /* reveal IMEI (default hidden) */
static int  g_speed_bits = 1; /* 1 = Mbps (bit rate), 0 = MB/s (byte rate) */
static int  g_show_batpct = 1; /* show percent text inside status battery */
static int  g_charging;   /* set from snapshot; drives charge animation cadence */
static int  g_stat_bat, g_stat_sig, g_stat_lowbat;
static char g_stat_time[8], g_stat_speed[40], g_stat_gen[8];
static char g_stat_up[16], g_stat_dn[16];   /* stacked status-bar speeds, e.g. "0.3M" */
/* power source, from sysfs (see pwr_refresh) */
enum { PWR_BATT, PWR_CHG, PWR_FAST, PWR_DIRECT, PWR_PC, PWR_OUT, PWR_FULL };
static struct { int state; double in_w; double in_v; int eta_min; int empty_min; int estimating; int drain; } g_pwr;
static unsigned g_phase;  /* animation tick (battery charge sweep) */
static int  g_charge_boot; /* power-off charging boot: full-screen charging UI */
static int  g_scroll;     /* current page vertical scroll offset */
static int  g_page_h;     /* last rendered page content height */
static int  g_autooff_ms; /* auto screen-off timeout, 0 = never */
static int  g_refresh_ms = 1000; /* state refresh interval, 0 = paused */
static int  g_sig_read;   /* ML1/raw signaling read switch */
static int  g_sig_parse;  /* decoded LTE/NR signaling parse switch + page visibility */
static int  g_neighbor_open; /* expand neighbor-cell list on the first signal page */
static int  g_saved_bright = -1; /* persisted backlight level, -1 = none yet */
enum { ST_STATE_MISSING = 0, ST_STATE_IDLE, ST_STATE_RUNNING, ST_STATE_DONE, ST_STATE_FAIL };
#define SPEEDTEST_BIN "/data/plugins/better-speedtest/better-speedtest"
#define SPEEDTEST_LOG "/tmp/better-speedtest.log"
#define SPEEDTEST_LOOP_FLAG "/tmp/better-speedtest.loop"
#define SPEEDTEST_LOOP_PID "/tmp/better-speedtest.loop.pid"
/* better-speedtest counts bytes on the WAN interface it finds in /proc/net/route (the main table:
 * always the cellular one). When the WiFi relay is the uplink (its rule 5300 -> table 100) it
 * measured 0: point it at wlan9 then. Checked per run, so a loop follows an uplink switch. */
#define SPEEDTEST_WAN_ENV "unset BETTER_SPEEDTEST_CONFIG; ip rule 2>/dev/null | grep -q '^5300:.*lookup 100' && " \
    "echo '{\"engine\":{\"wan_iface\":\"wlan9\"}}' > /tmp/u60-bst-wlan9.json && export BETTER_SPEEDTEST_CONFIG=/tmp/u60-bst-wlan9.json; "
static char g_st_src[16] = "auto";
static char g_st_dir[8] = "both";
static int  g_st_dur = 15;
static int  g_st_state = ST_STATE_MISSING;
static int  g_st_installed = -1;
static int  g_st_have_result;
static uint32_t g_st_poll_at;
static char g_st_phase[24], g_st_msg[160], g_st_err[160];
static char g_st_node[96], g_st_source[32], g_st_carrier[32], g_st_city[32], g_st_ulmsg[96];
static double g_st_cur_mbps, g_st_cur_peak;
static double g_st_dl_avg, g_st_dl_peak, g_st_ul_avg, g_st_ul_peak, g_st_ping, g_st_jitter;
#define ST_HIST 48
static int g_st_dl_hist[ST_HIST], g_st_ul_hist[ST_HIST], g_st_dl_n, g_st_ul_n;
static int g_last_clock_min = -1;       /* HH:MM changes only once per minute */
static char g_render_html_cache[PAGE_HTML_CACHE_CAP];
static size_t g_render_html_cache_len;
static char g_render_html_cache_path[320];
static int g_render_html_cache_scroll;
static int g_render_html_cache_modal;
static long g_render_html_cache_sms_open;
static int g_render_html_cache_lock;
static long long g_render_html_cache_css_mtime = -1;
static long long g_pages_dir_mtime = -1;
static uint32_t g_pages_scan_at;
static int normalize_refresh_ms(int ms);

/* ---- page-2 aux state, cached (-1 = unknown). Like the reference plugin,
 * bands are controlled purely with `ifconfig wlanN up/down` and read back from
 * operstate (wlan0=main 2.4G, wlan2=main 5G); uci/`wifi reload`/`zwrt_wlan
 * reload` are NOT used (they don't work / wedge the radios). PSM = `iw
 * power_save`, persisted via a self-written /etc/hotplug.d/iface/99-disable-powersave
 * script that re-applies the chosen mode on every ifup (so power_save=on sticks
 * across reconnect/reboot). The DHCP pool is computed live from uci. Toggles flip
 * optimistically; a throttle reconciles. */
static int  g_w24 = -1, g_w5 = -1, g_wpsm = -1;
static int  g_dps = -1;   /* power direct-supply mode (zwrt_bsp.charger), -1 unknown */
static int  g_adb_pending = -1; /* optimistic ADB state while USB re-enumerates */
static int  g_usb_net = -1;     /* Type-C network sharing composition active */
static int  g_typec_source = -1; /* 1 = reverse charge peer, 0 = charge U60 */
/* 刚点了开关：后台状态文件里还是点之前的值，8 秒内不读，否则开关/图标会被弹回去 */
static uint32_t g_aux_hold_until;
static void aux_hold(void) { g_aux_hold_until = (millis() + 8000) | 1; }
static int  g_typec_attached = -1;
static int  g_usb_net_pending = -1;
static int  g_typec_pending = -1;
static uint32_t g_usb_net_until, g_typec_until;
static char g_dhcp_pool[48];
/* currently WiFi-associated client MACs (lowercased, comma-joined). DHCP leases
 * linger after a device leaves, so the device list filters against this (live
 * station dump) to match the vendor's "only connected" behavior. */
static char g_assoc_macs[2048];   /* 每个 MAC 18 字节：640 只够 35 台，不够就会把设备从列表里漏掉 */
static uint32_t g_wifi_aux_at;

/* Is this MAC currently associated to a radio? (case-insensitive substring) */
static int mac_assoc(const char *mac)
{
    if (!g_assoc_macs[0] || !mac || !mac[0]) return 1;   /* unknown -> don't hide */
    char lc[24]; int j = 0;
    for (const char *p = mac; *p && j < 23; p++) {
        char c = *p; if (c >= 'A' && c <= 'Z') c += 32; lc[j++] = c;
    }
    lc[j] = 0;
    return strstr(g_assoc_macs, lc) != NULL;
}

static int read_long_path(const char *path, long *out)
{
    FILE *fp = fopen(path, "r");
    if (!fp) return 0;
    long v;
    int ok = fscanf(fp, "%ld", &v) == 1;
    fclose(fp);
    if (!ok) return 0;
    *out = v;
    return 1;
}

static int read_line_path(const char *path, char *out, size_t cap)
{
    FILE *fp = fopen(path, "r");
    size_t n;
    if (!fp || cap == 0) { if (fp) fclose(fp); return 0; }
    if (!fgets(out, (int)cap, fp)) { fclose(fp); return 0; }
    fclose(fp);
    n = strcspn(out, "\r\n");
    out[n] = 0;
    return 1;
}

static int boot_is_nonsilent(void)
{
    char cmdline[2048];
    FILE *fp = fopen("/proc/cmdline", "r");
    if (!fp) return 0;
    size_t n = fread(cmdline, 1, sizeof cmdline - 1, fp);
    fclose(fp);
    cmdline[n] = 0;
    return strstr(cmdline, "silent_boot.mode=nonsilent") != NULL;
}

static int read_mode_main_state(char *out, size_t cap)
{
    FILE *fp = fopen("/etc/config/zwrt_zte_mc_tmp", "r");
    char line[256];
    if (!fp || cap == 0) { if (fp) fclose(fp); return 0; }
    while (fgets(line, sizeof line, fp)) {
        if (!strstr(line, "option mode_main_state")) continue;
        char *q = strchr(line, '\'');
        if (!q) continue;
        char *e = strchr(q + 1, '\'');
        if (!e) continue;
        size_t n = (size_t)(e - (q + 1));
        if (n >= cap) n = cap - 1;
        memcpy(out, q + 1, n);
        out[n] = 0;
        fclose(fp);
        return 1;
    }
    fclose(fp);
    return 0;
}

static int boot_is_charge_mode(void)
{
    char mode[64];
    if (read_mode_main_state(mode, sizeof mode)) {
        if (!strncmp(mode, "mode_power_off_", 15)) return 1;
        if (!strcmp(mode, "mode_power_on") || !strcmp(mode, "mode_power_on_charger")) return 0;
    }
    return !boot_is_nonsilent();
}

static int boot_has_external_power(void)
{
    long v;
    char st[32];
    if (read_long_path("/sys/class/power_supply/usb/online", &v) && v != 0) return 1;
    if (read_long_path("/sys/class/power_supply/charger_zte/present_mbb", &v) && v != 0) return 1;
    if (read_long_path("/sys/class/power_supply/type-c_zte/present_mbb", &v) && v != 0) return 1;
    if (read_line_path("/sys/class/power_supply/battery/status", st, sizeof st)) {
        if (!strcmp(st, "Charging") || !strcmp(st, "Full")) return 1;
    }
    if (read_long_path("/sys/class/power_supply/charger_zte/status_mbb", &v) && v == 1) return 1;
    if (read_long_path("/sys/class/power_supply/battery_zte/status_mbb", &v) && v == 1) return 1;
    if (read_long_path("/sys/class/power_supply/statistics_zte/batt_status", &v) && v == 1) return 1;
    return 0;
}

/* ---- screen lock (4-digit PIN) ---- */
static char g_pin[8];        /* stored PIN ("" = lock disabled) */
static int  g_cover = 1;     /* show the clock cover on wake when no PIN */
static int  g_lock_state;    /* 0=normal, 1=locked cover, 2=setup pad, 3=unlock pad, 4=cover (no PIN) */
static char g_pin_entry[8];  /* digits typed so far */
static int  g_lock_err;      /* 1 = show the unlock-pad error message */

static void scan_pages(void)
{
    g_npages = 0;
    DIR *dp = opendir(UI_DIR);
    if (!dp) return;
    char names[24][64]; int n = 0;
    struct dirent *de;
    while ((de = readdir(dp)) && n < 24) {
        size_t l = strlen(de->d_name);
        if (de->d_name[0] != '.' &&
            l > 5 && strcmp(de->d_name + l - 5, ".html") == 0 &&
            strcmp(de->d_name, "menu.html") != 0 &&
            strcmp(de->d_name, "lockscreen.html") != 0 &&
            strcmp(de->d_name, "cover.html") != 0) {
            if (!g_sig_parse && strcmp(de->d_name, "01a-cell.html") == 0)
                continue;
            strncpy(names[n], de->d_name, 63); names[n][63] = 0; n++;
        }
    }
    closedir(dp);
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++)
            if (strcmp(names[i], names[j]) > 0) {
                char t[64]; strcpy(t, names[i]); strcpy(names[i], names[j]); strcpy(names[j], t);
            }
    for (int i = 0; i < n; i++)
        snprintf(g_pages[i], sizeof g_pages[i], "%s/%s", UI_DIR, names[i]);
    g_npages = n;
}

static void rescan_pages_keep_current(void)
{
    char cur_name[64];

    cur_name[0] = 0;
    if (g_npages > 0 && g_cur >= 0 && g_cur < g_npages) {
        const char *base = strrchr(g_pages[g_cur], '/');
        snprintf(cur_name, sizeof cur_name, "%s", base ? base + 1 : g_pages[g_cur]);
    }

    scan_pages();
    if (g_npages <= 0) {
        g_cur = 0;
        return;
    }
    if (cur_name[0]) {
        for (int i = 0; i < g_npages; i++) {
            const char *base = strrchr(g_pages[i], '/');
            const char *name = base ? base + 1 : g_pages[i];
            if (!strcmp(name, cur_name)) {
                g_cur = i;
                return;
            }
        }
    }
    if (g_cur >= g_npages) g_cur = g_npages - 1;
    if (g_cur < 0) g_cur = 0;
}

/* ---- value formatting ---- */
static int clampi(int v, int lo, int hi) { return v < lo ? lo : v > hi ? hi : v; }
static void fmt_bytes(char *o, size_t n, long b) {
    if (b >= 1024L * 1024 * 1024) snprintf(o, n, "%.2f GB", b / 1073741824.0);
    else                          snprintf(o, n, "%.1f MB", b / 1048576.0);
}
static void fmt_uptime(char *o, size_t n, long s) {
    long d = s / 86400; s %= 86400;
    snprintf(o, n, "%ldd %02ld:%02ld:%02ld", d, s / 3600, (s / 60) % 60, s % 60);
}
static void fmt_uptime_s(char *o, size_t n, long s) {   /* compact, for the grid */
    long d = s / 86400, hh = (s % 86400) / 3600, mm = (s % 3600) / 60;
    if (d > 0)       snprintf(o, n, "%ldd %ldh", d, hh);
    else if (hh > 0) snprintf(o, n, "%ldh %ldm", hh, mm);
    else             snprintf(o, n, "%ldm", mm);
}
/* compact speed for the status bar: 3.0M / 80K / 224B */
static void fmt_speed_c(char *o, size_t n, long bps) {
    if (bps >= 1024 * 1024) snprintf(o, n, "%.1fM", bps / 1048576.0);
    else if (bps >= 1024)   snprintf(o, n, "%.0fK", bps / 1024.0);
    else                    snprintf(o, n, "%ldB", bps);
}
static void fmt_one(char *o, size_t n, double v) {
    if (v >= 10) snprintf(o, n, "%.0f", v);
    else         snprintf(o, n, "%.1f", v);
}
/* Single speed value with unit, honoring the bit/byte-rate setting (matches the
 * status-bar units): bits=1 -> Mbps/Kbps/bps, bits=0 -> MB/s/KB/s/B/s. */
static void fmt_speed_u(char *o, size_t n, long bps, int bits)
{
    double v = bps * (bits ? 8.0 : 1.0);
    const char *unit; double div;
    if (bits) { if (v >= 1e6) { unit = "Mbps"; div = 1e6; } else if (v >= 1e3) { unit = "Kbps"; div = 1e3; } else { unit = "bps"; div = 1; } }
    else      { if (v >= 1e6) { unit = "MB/s"; div = 1e6; } else if (v >= 1e3) { unit = "KB/s"; div = 1e3; } else { unit = "B/s"; div = 1; } }
    double val = v / div;
    if (val >= 10) snprintf(o, n, "%.0f %s", val, unit);
    else           snprintf(o, n, "%.1f %s", val, unit);
}

/* Compact per-direction speed for the stacked status bar: "↓4.6M" / "↓596K". */
static void fmt_speed_short(char *o, size_t n, const char *arrow, long bps, int bits)
{
    double v = bps * (bits ? 8.0 : 1.0);
    const char *u = bits ? "" : "B";
    if (v >= 1e6)      snprintf(o, n, v >= 1e8 ? "%s%.0fM%s" : "%s%.1fM%s", arrow, v / 1e6, u);
    else if (v >= 1e3) snprintf(o, n, "%s%.0fK%s", arrow, v / 1e3, u);
    else               snprintf(o, n, "%s0K%s", arrow, u);
}

/* Status-bar speed pair: "up/down <unit>", shared unit picked from the
 * larger of the two. bits=1 -> Mbps/Kbps/bps; bits=0 -> MB/s/KB/s/B/s. */
static void fmt_speed_pair(char *buf, size_t cap, long up, long down, int bits) {
    double mul = bits ? 8.0 : 1.0;
    double u = up * mul, d = down * mul, mx = u > d ? u : d;
    const char *unit; double div;
    if (bits) { if (mx >= 1e6) { unit = "Mbps"; div = 1e6; } else if (mx >= 1e3) { unit = "Kbps"; div = 1e3; } else { unit = "bps"; div = 1; } }
    else      { if (mx >= 1e6) { unit = "MB/s"; div = 1e6; } else if (mx >= 1e3) { unit = "KB/s"; div = 1e3; } else { unit = "B/s"; div = 1; } }
    char us[12], ds[12];
    fmt_one(us, sizeof us, u / div); fmt_one(ds, sizeof ds, d / div);
    snprintf(buf, cap, "\xe2\x86\x91%s \xe2\x86\x93%s %s", us, ds, unit);
}

/* ---- {{key}} template substitution ---- */
struct kv { const char *k; const char *v; };

/* Append to a fixed char array; stops at the end instead of running past it
 * (plain `o += snprintf(...)` goes negative once output is truncated). */
#define APPEND(buf, o, ...) do { \
    if ((o) < (int)sizeof(buf) - 1) { \
        int _w = snprintf((buf) + (o), sizeof(buf) - (size_t)(o), __VA_ARGS__); \
        if (_w > 0) (o) += _w; \
        if ((o) > (int)sizeof(buf) - 1) (o) = (int)sizeof(buf) - 1; \
    } } while (0)
static void html_esc(char *dst, size_t cap, const char *src);
static int signal_value_present(const char *s);

static char *apply_template(const char *tmpl, struct kv *t, int n)
{
    static char out[1048576];
    size_t o = 0;
    for (const char *p = tmpl; *p && o < sizeof(out) - 1; ) {
        if (p[0] == '{' && p[1] == '{') {
            const char *end = strstr(p + 2, "}}");
            if (end) {
                int kl = (int)(end - (p + 2));
                const char *v = "";
                for (int i = 0; i < n; i++)
                    if ((int)strlen(t[i].k) == kl && strncmp(t[i].k, p + 2, kl) == 0) { v = t[i].v; break; }
                size_t vl = strlen(v);
                if (o + vl < sizeof(out) - 1) { memcpy(out + o, v, vl); o += vl; }
                else {
                    size_t room = sizeof(out) - 1 - o;
                    if (room) memcpy(out + o, v, room);
                    o = sizeof(out) - 1;
                    out[o] = 0;
                    break;
                }
                p = end + 2;
                continue;
            }
        }
        out[o++] = *p++;
    }
    out[o] = 0;
    return out;
}

static char *read_file(const char *path)
{
    FILE *fp = fopen(path, "rb");
    if (!fp) return NULL;
    size_t cap = 4096, n = 0;
    char *buf = malloc(cap);
    if (!buf) { fclose(fp); return NULL; }
    for (;;) {
        if (n + 1 >= cap) {
            size_t ncap = cap * 2;
            char *nbuf = realloc(buf, ncap);
            if (!nbuf) { free(buf); fclose(fp); return NULL; }
            buf = nbuf; cap = ncap;
        }
        size_t r = fread(buf + n, 1, cap - n - 1, fp);
        n += r;
        if (r == 0) break;
    }
    if (ferror(fp)) { free(buf); fclose(fp); return NULL; }
    buf[n] = 0; fclose(fp);
    return buf;
}

static long long file_mtime_ns(const char *path)
{
    struct stat st;
    if (stat(path, &st) != 0) return -1;
    return (long long)st.st_mtime * 1000000000LL + (long long)st.st_mtim.tv_nsec;
}

static long long ui_scan_mtime_ns(void)
{
    long long a = file_mtime_ns(UI_DIR);
    long long b = file_mtime_ns(FUNCTIONS_DIR);
    if (a < 0) a = 0;
    if (b < 0) b = 0;
    return a ^ (b << 1);
}

static int rescan_pages_if_changed(void)
{
    long long mtime = ui_scan_mtime_ns();
    if (mtime < 0 || mtime == g_pages_dir_mtime) return 0;
    g_pages_dir_mtime = mtime;
    rescan_pages_keep_current();
    g_render_html_cache_len = 0;
    g_render_html_cache_path[0] = 0;
    g_render_html_cache_css_mtime = -1;
    return 1;
}

static const char *read_template_cached(const char *path)
{
    long long mtime = file_mtime_ns(path);
    if (mtime < 0) return NULL;

    for (int i = 0; i < TEMPLATE_CACHE_CAP; i++) {
        struct template_cache_entry *e = &g_tmpl_cache[i];
        if (!e->used || !e->path[0]) continue;
        if (strcmp(e->path, path) != 0) continue;

        if (e->mtime_ns == mtime && e->content) return e->content;

        char *next = read_file(path);
        if (!next) return e->content;   /* keep previous cached copy if read fails */
        free(e->content);
        e->content = next;
        e->mtime_ns = mtime;
        return e->content;
    }

    char *tmpl = read_file(path);
    if (!tmpl) return NULL;

    for (int i = 0; i < TEMPLATE_CACHE_CAP; i++) {
        if (!g_tmpl_cache[i].used) {
            snprintf(g_tmpl_cache[i].path, sizeof(g_tmpl_cache[i].path), "%s", path);
            g_tmpl_cache[i].mtime_ns = mtime;
            g_tmpl_cache[i].content = tmpl;
            g_tmpl_cache[i].used = 1;
            return g_tmpl_cache[i].content;
        }
    }

    struct template_cache_entry *e = &g_tmpl_cache[g_tmpl_next];
    free(e->content);
    snprintf(e->path, sizeof(e->path), "%s", path);
    e->mtime_ns = mtime;
    e->content = tmpl;
    e->used = 1;
    g_tmpl_next = (g_tmpl_next + 1) % TEMPLATE_CACHE_CAP;
    return e->content;
}

static int usb_pid_is(const char *needle)
{
    int ok = 0;
    char *pid = read_file("/sys/kernel/config/usb_gadget/g1/idProduct");
    if (pid) {
        ok = strstr(pid, needle) != NULL;
        free(pid);
    }
    return ok;
}

/* 当前 USB 配置是网络模式：原厂 rndis_gsi(1403)、RNDIS(9057)、ECM(90B1) */
static int usb_pid_is_net(void)
{
    return usb_pid_is("1403") || usb_pid_is("9057") || usb_pid_is("90b1") || usb_pid_is("90B1");
}

static int usb_net_has_carrier(void)
{
    int ok = 0;
    char *c = read_file("/sys/class/net/rndis0/carrier");
    if (c) { if (c[0] == '1') ok = 1; free(c); }
    c = read_file("/sys/class/net/ecm0/carrier");
    if (c) { if (c[0] == '1') ok = 1; free(c); }
    return ok;
}

static void usb_net_watchdog_stop(void)
{
    system("pid=$(cat /tmp/u60-usbnet-watchdog.pid 2>/dev/null); "
           "[ -n \"$pid\" ] && kill \"$pid\" 2>/dev/null; "
           "rm -f /tmp/u60-usbnet-watchdog.pid /tmp/u60-usbnet-enabled");
}

static void usb_net_apply_source_async(void)
{
    system("(flock 9; touch /tmp/u60-typec-source /tmp/u60-usbnet-switching; "
           "date '+%F %T usbnet apply source' >>/tmp/usb.log 2>/dev/null; "
           "ubus call zwrt_bsp.powerbank set '{\"state\":0}'; "
           "sleep 1; ubus call zwrt_bsp.typec set '{\"DR_Swap\":\"device\",\"PR_Swap\":\"sink\"}'; "
           "sleep 1; echo peripheral > /sys/bus/platform/devices/a600000.ssusb/mode 2>/dev/null; "
           "/sbin/usb_composition 90B1 n n y n; "
           "for i in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20; do "
           "att=$(ubus call zwrt_bsp.typec list 2>/dev/null | grep cc_attch_state | grep -o '[0-9]' | head -1); "
           "pid2=$(cat /sys/kernel/config/usb_gadget/g1/idProduct 2>/dev/null); "
           "e=$(cat /sys/class/net/ecm0/carrier 2>/dev/null); "
           "if [ \"$att\" = \"1\" ] && { [ \"$pid2\" = \"0x90b1\" ] || [ \"$pid2\" = \"0x90B1\" ]; } && [ \"$e\" = \"1\" ]; then break; fi; "
           "sleep 1; done; "
           "if [ \"$att\" = \"1\" ] && { [ \"$pid2\" = \"0x90b1\" ] || [ \"$pid2\" = \"0x90B1\" ]; } && [ \"$e\" = \"1\" ]; then "
           "ubus call zwrt_bsp.typec set '{\"DR_Swap\":\"device\",\"PR_Swap\":\"source\"}'; "
           "sleep 1; ubus call zwrt_bsp.powerbank set '{\"state\":1}'; "
           "sleep 1; ubus call zwrt_bsp.typec set '{\"DR_Swap\":\"device\"}'; "
           "sleep 1; /sbin/usb_composition 90B1 n n y n; "
           "for i in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15; do "
           "r=$(cat /sys/class/net/rndis0/carrier 2>/dev/null); "
           "e=$(cat /sys/class/net/ecm0/carrier 2>/dev/null); "
           "if [ \"$r\" = \"1\" ] || [ \"$e\" = \"1\" ]; then break; fi; "
           "sleep 1; done; "
           "else "
           "date '+%F %T usbnet source no ecm carrier, try rndis' >>/tmp/usb.log 2>/dev/null; "
           "rm -f /tmp/u60-typec-source; "
           "/sbin/usb_composition 9057 n n y n; "
           "sleep 10; "
           "r=$(cat /sys/class/net/rndis0/carrier 2>/dev/null); "
           "e=$(cat /sys/class/net/ecm0/carrier 2>/dev/null); "
           "if [ \"$r\" != \"1\" ] && [ \"$e\" != \"1\" ]; then "
           "date '+%F %T usbnet rndis no carrier, fallback 90B1' >>/tmp/usb.log 2>/dev/null; "
           "/sbin/usb_composition 90B1 n n y n; fi; "
           "fi; "
           "rm -f /tmp/u60-usbnet-switching) 9>/tmp/u60-usb.lock >/tmp/u60-usbnet-switch.log 2>&1 &");
}

/* 接电脑开 USB 网络：用原厂的 rndis_gsi(0x1403)，原厂程序也会切到这个模式，两边不再来回抢。
 * 每秒看一次网卡，15 秒都不通（Mac 不认 RNDIS）才换 ECM(90B1)。 */
static void usb_net_apply_sink_async(void)
{
    system("(flock 9; touch /tmp/u60-usbnet-switching; rm -f /tmp/u60-typec-source; "
           "date '+%F %T usbnet apply sink' >>/tmp/usb.log 2>/dev/null; "
           "ubus call zwrt_bsp.powerbank set '{\"state\":0}'; "
           "sleep 1; ubus call zwrt_bsp.typec set '{\"DR_Swap\":\"device\",\"PR_Swap\":\"sink\"}'; "
           "sleep 1; echo peripheral > /sys/bus/platform/devices/a600000.ssusb/mode 2>/dev/null; "
           "SER=$(cat /sys/kernel/config/usb_gadget/g1/strings/0x409/serialnumber 2>/dev/null); "
           "sh /sbin/usb/compositions/usb_switch 0x19d2 0x1403 rndis_gsi \"$SER\"; "
           "ok=0; for i in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15; do "
           "r=$(cat /sys/class/net/rndis0/carrier 2>/dev/null); "
           "e=$(cat /sys/class/net/ecm0/carrier 2>/dev/null); "
           "if [ \"$r\" = \"1\" ] || [ \"$e\" = \"1\" ]; then ok=1; break; fi; "
           "sleep 1; done; "
           "if [ \"$ok\" != \"1\" ]; then "
           "date '+%F %T usbnet rndis no carrier, try ecm' >>/tmp/usb.log 2>/dev/null; "
           "/sbin/usb_composition 90B1 n n y n; fi; "
           "rm -f /tmp/u60-usbnet-switching) 9>/tmp/u60-usb.lock >/tmp/u60-usbnet-switch.log 2>&1 &");
}

static void usb_power_only_apply_async(int source)
{
    if (source) {
        system("(flock 9; touch /tmp/u60-typec-source /tmp/u60-usbnet-switching; "
               "date '+%F %T usbpower apply source' >>/tmp/usb.log 2>/dev/null; "
               "ubus call zwrt_bsp.typec set '{\"DR_Swap\":\"device\",\"PR_Swap\":\"source\"}'; "
               "sleep 1; ubus call zwrt_bsp.powerbank set '{\"state\":1}'; "
               "sleep 1; ubus call zwrt_bsp.typec set '{\"DR_Swap\":\"device\"}'; "
               "sleep 1; SER=$(cat /sys/kernel/config/usb_gadget/g1/strings/0x409/serialnumber 2>/dev/null); "
               "sh /sbin/usb/compositions/usb_switch 0x19d2 0x1225 mass_storage \"$SER\"; "
               "rm -f /tmp/u60-usbnet-switching) 9>/tmp/u60-usb.lock >/tmp/u60-usbnet-switch.log 2>&1 &");
    } else {
        system("(flock 9; touch /tmp/u60-usbnet-switching; rm -f /tmp/u60-typec-source; "
               "date '+%F %T usbpower apply sink' >>/tmp/usb.log 2>/dev/null; "
               "ubus call zwrt_bsp.powerbank set '{\"state\":0}'; "
               "sleep 1; ubus call zwrt_bsp.typec set '{\"DR_Swap\":\"device\",\"PR_Swap\":\"sink\"}'; "
               "sleep 1; SER=$(cat /sys/kernel/config/usb_gadget/g1/strings/0x409/serialnumber 2>/dev/null); "
               "sh /sbin/usb/compositions/usb_switch 0x19d2 0x1225 mass_storage \"$SER\"; "
               "rm -f /tmp/u60-usbnet-switching) 9>/tmp/u60-usb.lock >/tmp/u60-usbnet-switch.log 2>&1 &");
    }
}

/* ---- 插线选择供电方式 (power-role sheet, g_modal == 5). The stock UI asked this on
 * every Type-C attach (TUFormPowerRoleSelection) and defaulted to powering the peer;
 * our UI replaced it, so without this sheet the port just stayed a power source. ---- */
static uint32_t g_pr_open_at, g_pr_quiet_until;
/* 静默期内不弹供电方式；到期清零，避免 millis 过 2^31 后差值反转 */
static int pr_quiet(uint32_t now)
{
    if (g_pr_quiet_until && (int32_t)(now - g_pr_quiet_until) >= 0) g_pr_quiet_until = 0;
    return g_pr_quiet_until != 0;
}
static int g_toast_pill;                   /* toast drawn as the small top capsule */

static int pr_partner_present(void) { return access("/sys/class/typec/port0-partner", F_OK) == 0; }
static int pr_role_source(void)
{
    char b[48] = "";
    if (!read_line_path("/sys/class/typec/port0/power_role", b, sizeof b)) return g_typec_source == 1;
    return strstr(b, "[source]") != NULL;
}
/* the peer can take power from us: it already does (we are source), or it is a USB
 * host (computer / phone) that enumerated us; a plain charger is neither */
static int pr_peer_can_sink(void)
{
    char b[32] = "";
    if (pr_role_source()) return 1;
    return read_line_path("/sys/class/udc/a600000.dwc3/state", b, sizeof b) &&
           (!strcmp(b, "configured") || !strcmp(b, "addressed"));
}
/* 直供电 keeps the battery between 40 % and 60 % (stock charger firmware): switched on
 * above 60 %, the input is suspended (usb/online = 0) and the battery runs the device
 * down to 60 % before the cable takes over. The cable is still in and we are the sink. */
static int dps_draining(void)
{
    long on = 0;
    read_long_path("/sys/class/power_supply/usb/online", &on);
    return g_dps == 1 && !on && pr_partner_present() && !pr_role_source();
}

static int pr_current_mode(void)           /* 0 charge, 1 direct supply, 2 power the peer */
{
    if (pr_role_source()) return 2;
    return g_dps == 1 ? 1 : 0;
}

static int g_pr_mode_pref = -1, g_pr_net_pref = -1;   /* last choice in the sheet (-1 = never chosen) */
static uint32_t g_pr_restore_at;            /* attach: re-apply the remembered choice at this time */
/* chosen in the sheet while a USB switch was still running: applied as soon as it ends (taps used
 * to be dropped then, and that window is exactly when the sheet has just popped up) */
static int g_pr_pend_mode = -1, g_pr_pend_net = -1;

/* A role / composition switch is in flight: its script holds /tmp/u60-usbnet-switching
 * (plus a short grace for the fork to start). New requests are refused meanwhile. */
static uint32_t g_usb_busy_until;
static int usb_switch_busy(uint32_t now)
{
    if (g_usb_busy_until && (int32_t)(now - g_usb_busy_until) >= 0) g_usb_busy_until = 0;   /* 到期清零，见 aux_hold */
    return access("/tmp/u60-usbnet-switching", F_OK) == 0 || g_usb_busy_until != 0;
}

static int usb_net_now(void)
{
    return g_usb_net_pending >= 0 ? g_usb_net_pending :
           ((g_usb_net == 1) || usb_pid_is_net());
}
static void usb_net_off_async(void)         /* back to the plain composition (U 盘 + ADB re-added by adb-on.sh) */
{
    system("(flock 9; rm -f /tmp/u60-usbnet-switching; "
           "SER=$(cat /sys/kernel/config/usb_gadget/g1/strings/0x409/serialnumber 2>/dev/null); "
           "sh /sbin/usb/compositions/usb_switch 0x19d2 0x1225 mass_storage \"$SER\") 9>/tmp/u60-usb.lock >/dev/null 2>&1 &");
}

/* Swap the Type-C power role (shared by the 反向供电 switch and the sheet). */
static void typec_switch_to(int target, uint32_t now)
{
    g_usb_busy_until = (now + 3000) | 1;
    int net_active = ((g_usb_net_pending >= 0 ? g_usb_net_pending : g_usb_net) == 1 ||
                      usb_pid_is_net());
    if (net_active) {
        system("touch /tmp/u60-usbnet-switching");
        if (target) usb_net_apply_source_async();
        else        usb_net_apply_sink_async();
        g_usb_net = 1;
    } else {
        usb_power_only_apply_async(target);
    }
    g_typec_source = target;
    g_typec_pending = target;
    g_typec_until = now + 20000;
    aux_hold();
    g_pr_quiet_until = (now + 25000) | 1;        /* a role swap can re-attach the partner: no re-prompt */
}

/* Apply a sheet choice in one go. mode: 0 charge, 1 direct supply, 2 power the peer;
 * net: 1/0 USB 有线上网 on/off, -1 leave it. Role and composition changes go through
 * ONE async script so two of them never race on the gadget. */
static void pr_apply(int mode, int net, uint32_t now)
{
    int want_src = mode == 2, cur_src = pr_role_source(), cur_net = usb_net_now();
    if (mode == 0 || mode == 1) {
        char cmd[160];
        unlink(CHGCAP_MARK);                  /* an explicit choice overrides the 充电上限 logic */
        close(open(CHGCAP_USER, O_WRONLY | O_CREAT, 0644));
        snprintf(cmd, sizeof cmd,
            "ubus call zwrt_bsp.charger set '{\"direct_power_supply_mode\":\"%s\"}' >/dev/null 2>&1 &",
            mode == 1 ? "enable" : "disable");
        system(cmd);
        g_dps = mode == 1;
    }
    aux_hold();
    int role_change = want_src != cur_src;
    if ((net >= 0 && net != cur_net) || role_change) g_usb_busy_until = (now + 3000) | 1;
    if (net == 1 && (!cur_net || role_change)) {
        system("touch /tmp/u60-usbnet-switching");
        if (want_src) usb_net_apply_source_async(); else usb_net_apply_sink_async();
        g_usb_net = 1; g_usb_net_pending = 1; g_usb_net_until = now + 20000;
    } else if (net == 0 && cur_net) {
        usb_net_watchdog_stop();
        if (role_change) usb_power_only_apply_async(want_src);   /* also drops the network composition */
        else usb_net_off_async();
        g_usb_net = 0; g_usb_net_pending = 0; g_usb_net_until = now + 20000;
    } else if (role_change) {
        typec_switch_to(want_src, now);
        return;
    } else return;
    if (role_change) {
        g_typec_source = want_src; g_typec_pending = want_src; g_typec_until = now + 20000;
    }
    g_pr_quiet_until = (now + 25000) | 1;
}

static void usb_net_watchdog_start(void)
{
    usb_net_watchdog_stop();
    system("cat >/tmp/u60-usbnet-watchdog.sh <<'EOF'\n"
           "#!/bin/sh\n"
           "touch /tmp/u60-usbnet-enabled\n"
           "echo $$ >/tmp/u60-usbnet-watchdog.pid\n"
           "while [ -f /tmp/u60-usbnet-enabled ]; do\n"
           "  if [ -f /tmp/u60-usbnet-switching ]; then sleep 2; continue; fi\n"
           "  pid=$(cat /sys/kernel/config/usb_gadget/g1/idProduct 2>/dev/null)\n"
           "  tc=$(ubus call zwrt_bsp.typec list 2>/dev/null)\n"
           "  att=$(echo \"$tc\" | grep cc_attch_state | grep -o '[0-9]' | head -1)\n"
           "  pr=$(echo \"$tc\" | grep power_role | grep -o 'source\\|sink' | head -1)\n"
           "  r=$(cat /sys/class/net/rndis0/carrier 2>/dev/null)\n"
           "  e=$(cat /sys/class/net/ecm0/carrier 2>/dev/null)\n"
            "  case \"$pid\" in 0x9057|0x90b1|0x90B1) netpid=1;; *) netpid=0;; esac\n"
            "  wantsrc=0; [ -f /tmp/u60-typec-source ] && wantsrc=1\n"
            "  rolebad=0\n"
            "  if [ \"$wantsrc\" = 1 ] && [ \"$pr\" != source ]; then rolebad=1; fi\n"
            "  if [ \"$wantsrc\" != 1 ] && [ \"$pr\" != sink ]; then rolebad=1; fi\n"
            "  if [ \"$att\" = 1 ] && { [ \"$rolebad\" = 1 ] || [ \"$netpid\" != 1 ] || { [ \"$r\" != 1 ] && [ \"$e\" != 1 ]; }; }; then\n"
            "    date '+%F %T usbnet watchdog rearm' >>/tmp/usb.log 2>/dev/null\n"
            "    touch /tmp/u60-usbnet-switching\n"
            "    if [ \"$wantsrc\" = 1 ]; then\n"
            "      ubus call zwrt_bsp.powerbank set '{\"state\":0}' >/dev/null 2>&1\n"
            "      sleep 1\n"
            "      ubus call zwrt_bsp.typec set '{\"DR_Swap\":\"device\",\"PR_Swap\":\"sink\"}' >/dev/null 2>&1\n"
            "      sleep 1\n"
            "      echo peripheral > /sys/bus/platform/devices/a600000.ssusb/mode 2>/dev/null\n"
            "      /sbin/usb_composition 90B1 n n y n >>/tmp/usb.log 2>&1\n"
            "      for i in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20; do\n"
            "        att=$(ubus call zwrt_bsp.typec list 2>/dev/null | grep cc_attch_state | grep -o '[0-9]' | head -1)\n"
            "        pid2=$(cat /sys/kernel/config/usb_gadget/g1/idProduct 2>/dev/null)\n"
            "        e=$(cat /sys/class/net/ecm0/carrier 2>/dev/null)\n"
            "        if [ \"$att\" = 1 ] && { [ \"$pid2\" = 0x90b1 ] || [ \"$pid2\" = 0x90B1 ]; } && [ \"$e\" = 1 ]; then break; fi\n"
            "        sleep 1\n"
            "      done\n"
            "      if [ \"$att\" = 1 ] && { [ \"$pid2\" = 0x90b1 ] || [ \"$pid2\" = 0x90B1 ]; } && [ \"$e\" = 1 ]; then\n"
            "      ubus call zwrt_bsp.typec set '{\"DR_Swap\":\"device\",\"PR_Swap\":\"source\"}' >/dev/null 2>&1\n"
            "      sleep 1\n"
            "      ubus call zwrt_bsp.powerbank set '{\"state\":1}' >/dev/null 2>&1\n"
            "      sleep 1\n"
            "      ubus call zwrt_bsp.typec set '{\"DR_Swap\":\"device\"}' >/dev/null 2>&1\n"
            "      sleep 1\n"
            "      /sbin/usb_composition 90B1 n n y n >>/tmp/usb.log 2>&1\n"
            "      for i in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15; do\n"
            "        r=$(cat /sys/class/net/rndis0/carrier 2>/dev/null)\n"
            "        e=$(cat /sys/class/net/ecm0/carrier 2>/dev/null)\n"
            "        if [ \"$r\" = 1 ] || [ \"$e\" = 1 ]; then break; fi\n"
            "        sleep 1\n"
            "      done\n"
            "      else\n"
            "        date '+%F %T usbnet watchdog source no ecm carrier, try rndis' >>/tmp/usb.log 2>/dev/null\n"
            "        rm -f /tmp/u60-typec-source\n"
            "        /sbin/usb_composition 9057 n n y n >>/tmp/usb.log 2>&1\n"
            "        sleep 10\n"
            "        r=$(cat /sys/class/net/rndis0/carrier 2>/dev/null)\n"
            "        e=$(cat /sys/class/net/ecm0/carrier 2>/dev/null)\n"
            "        if [ \"$r\" != 1 ] && [ \"$e\" != 1 ]; then\n"
            "          date '+%F %T usbnet watchdog rndis no carrier, fallback 90B1' >>/tmp/usb.log 2>/dev/null\n"
            "          /sbin/usb_composition 90B1 n n y n >>/tmp/usb.log 2>&1\n"
            "        fi\n"
            "      fi\n"
            "    else\n"
            "      ubus call zwrt_bsp.powerbank set '{\"state\":0}' >/dev/null 2>&1\n"
            "      ubus call zwrt_bsp.typec set '{\"DR_Swap\":\"device\",\"PR_Swap\":\"sink\"}' >/dev/null 2>&1\n"
            "      sleep 1\n"
            "      echo peripheral > /sys/bus/platform/devices/a600000.ssusb/mode 2>/dev/null\n"
            "      /sbin/usb_composition 9057 n n y n >>/tmp/usb.log 2>&1\n"
            "      sleep 10\n"
            "      r=$(cat /sys/class/net/rndis0/carrier 2>/dev/null)\n"
            "      e=$(cat /sys/class/net/ecm0/carrier 2>/dev/null)\n"
            "      if [ \"$r\" != 1 ] && [ \"$e\" != 1 ]; then\n"
            "        date '+%F %T usbnet watchdog fallback 90B1' >>/tmp/usb.log 2>/dev/null\n"
            "        /sbin/usb_composition 90B1 n n y n >>/tmp/usb.log 2>&1\n"
            "      fi\n"
            "    fi\n"
            "    rm -f /tmp/u60-usbnet-switching\n"
            "  fi\n"
            "  sleep 12\n"
            "done\n"
           "EOF\n"
           "chmod +x /tmp/u60-usbnet-watchdog.sh\n"
           "nohup /tmp/u60-usbnet-watchdog.sh >/tmp/u60-usbnet-watchdog.log 2>&1 &");
}

/* Read page-2 aux state into the cache: band on/off from netdev operstate (the
 * live truth on this firmware), PSM from `iw power_save`, and the DHCP pool
 * range computed live from uci (lan ip + start/limit offsets). One shell
 * round-trip, called on a throttle. sync=0: 读上次结果，后台刷新（主循环里不阻塞） */
#define AUX_FILE "/tmp/u60-aux.txt"
static void wifi_aux_refresh(int sync)
{
    static const char *sh =
        "echo W0=$(cat /sys/class/net/wlan0/operstate 2>/dev/null);"
        "echo W2=$(cat /sys/class/net/wlan2/operstate 2>/dev/null);"
        "ps=$(iw dev wlan0 get power_save 2>/dev/null | grep -o 'o[nf]*' | tail -1);"
        "[ -z \"$ps\" ] && ps=$(iw dev wlan2 get power_save 2>/dev/null | grep -o 'o[nf]*' | tail -1);"
        "echo PSM=$([ \"$ps\" = on ] && echo 1 || echo 0);"
        "ip=$(uci -q get network.lan.ipaddr); st=$(uci -q get dhcp.lan.start); lim=$(uci -q get dhcp.lan.limit);"
        "if [ -n \"$ip\" ] && [ -n \"$st\" ]; then pre=${ip%.*}; end=$((st+lim-1)); [ $end -gt 254 ] && end=254;"
        "echo \"POOL=$pre.$st - $pre.$end\"; fi;"
        /* "connected now" = WiFi-associated stations plus ARP-complete entries
         * (ARP covers LAN/USB clients too; leases alone linger 24h). */
        "echo MACS=$({ for w in wlan0 wlan1 wlan2 wlan3; do iw dev $w station dump 2>/dev/null | awk '/Station/{print $2}'; done;"
        " awk 'NR>1 && $3!=\"0x0\"{print $4}' /proc/net/arp 2>/dev/null; } | sort -u | tr 'A-Z\\n' 'a-z,');"
        "echo DPS=$(ubus -t 2 call zwrt_bsp.charger list 2>/dev/null | grep direct_power_supply_mode | grep -o 'enable\\|disable');"
        "pid=$(cat /sys/kernel/config/usb_gadget/g1/idProduct 2>/dev/null);"
        "echo USBNET=$([ \"$pid\" = 0x9057 ] || [ \"$pid\" = 0x90b1 ] || [ \"$pid\" = 0x90B1 ] && echo 1 || echo 0);"
        "tc=$(ubus -t 2 call zwrt_bsp.typec list 2>/dev/null);"
        "echo TYPECSRC=$(echo \"$tc\" | grep power_role | grep -o 'source\\|sink' | head -1);"
        "echo TYPECATTACH=$(echo \"$tc\" | grep cc_attch_state | grep -o '[0-9]' | head -1)";
    FILE *fp;
    if (sync) {
        fp = popen(sh, "r");
    } else {
        fp = fopen(AUX_FILE, "r");
        /* 后台跑：ubus 慢时最多卡 4 秒，不能放在主线程；用 $$ 临时名避免两次重叠互相写坏 */
        char cmd[4096];
        snprintf(cmd, sizeof cmd, "(t=" AUX_FILE ".$$; { %s; } > $t 2>/dev/null && mv $t " AUX_FILE ") >/dev/null 2>&1 &", sh);
        system(cmd);
        if (fp && g_aux_hold_until) {
            if ((int32_t)(millis() - g_aux_hold_until) < 0) { fclose(fp); return; }
            g_aux_hold_until = 0;   /* 到期清零：不清的话开机 24.85 天后差值又变负，会一直不读 */
        }
    }
    if (!fp) return;
    char line[2304];
    while (fgets(line, sizeof line, fp)) {
        if      (!strncmp(line, "W0=", 3))   g_w24 = strstr(line, "=up") != NULL;
        else if (!strncmp(line, "W2=", 3))   g_w5  = strstr(line, "=up") != NULL;
        else if (!strncmp(line, "PSM=", 4))  g_wpsm = atoi(line + 4);
        else if (!strncmp(line, "POOL=", 5)) {
            char *nl = strchr(line, '\n'); if (nl) *nl = 0;
            snprintf(g_dhcp_pool, sizeof g_dhcp_pool, "%s", line + 5);
        }
        else if (!strncmp(line, "MACS=", 5)) {
            char *nl = strchr(line, '\n'); if (nl) *nl = 0;
            snprintf(g_assoc_macs, sizeof g_assoc_macs, "%s", line + 5);
        }
        else if (!strncmp(line, "DPS=", 4)) {
            if (strstr(line, "disable")) g_dps = 0;
            else if (strstr(line, "enable")) g_dps = 1;
        }
        else if (!strncmp(line, "USBNET=", 7)) {
            g_usb_net = atoi(line + 7) ? 1 : 0;
        }
        else if (!strncmp(line, "TYPECSRC=", 9)) {
            if (strstr(line, "source")) g_typec_source = 1;
            else if (strstr(line, "sink")) g_typec_source = 0;
        }
        else if (!strncmp(line, "TYPECATTACH=", 12)) {
            g_typec_attached = atoi(line + 12) ? 1 : 0;
        }
    }
    if (sync) pclose(fp); else fclose(fp);
}

/* ---- screen lock (PIN) persistence. The PIN lives in a dotfile under the UI
 * dir (which always exists) so it survives reboots and isn't clobbered by
 * pushing the .html pages. lock_enabled() == "a PIN is set". ---- */
#define LOCK_PIN_FILE UI_DIR "/.lockpin"
static int lock_enabled(void) { return g_pin[0] != 0; }
static void load_pin(void)
{
    g_pin[0] = 0;
    FILE *fp = fopen(LOCK_PIN_FILE, "r");
    if (!fp) return;
    char b[16]; int o = 0;
    if (fgets(b, sizeof b, fp))
        for (const char *p = b; *p && o < 4; p++)
            if (*p >= '0' && *p <= '9') g_pin[o++] = *p;
    g_pin[o] = 0;
    if (o != 4) g_pin[0] = 0;   /* ignore anything malformed */
    fclose(fp);
    g_refresh_ms = normalize_refresh_ms(g_refresh_ms);
}
static void save_pin(const char *pin)
{
    snprintf(g_pin, sizeof g_pin, "%s", pin);
    FILE *fp = fopen(LOCK_PIN_FILE, "w");
    if (fp) { fprintf(fp, "%s\n", pin); fclose(fp); }
}
static void clear_pin(void) { g_pin[0] = 0; remove(LOCK_PIN_FILE); }
/* Enter the lock pad. setup=1 -> set a new PIN; setup=0 -> unlock prompt. */
static void enter_lock(int setup)
{
    g_lock_state = setup ? 2 : 1;
    g_pin_entry[0] = 0; g_lock_err = 0; g_scroll = 0;
}
/* On screen-off: with a PIN, the locked cover (swipe -> PIN pad); without one,
 * the plain cover (swipe -> back to where you were) if enabled. */
static int cover_wanted(void) { return lock_enabled() || g_cover; }
static void enter_cover(void)
{
    if (lock_enabled()) { enter_lock(0); return; }
    if (g_cover) { g_lock_state = 4; g_scroll = 0; }
}

/* ---- persisted UI settings (theme / speed unit / auto-off / refresh interval).
 * Stored next to the binary in /data/plugins/u60pro-devui so they survive reinstalling the
 * binary and re-pushing UI files (the PIN persists separately in .lockpin). */
#define CONF_FILE "/data/plugins/u60pro-devui/devui.conf"
/* wallpaper choice (file in WALL_DIR, or "none") and the wake cover screen */
#define WALL_DIR "/data/plugins/u60pro-devui/wallpapers"
static const char *const g_walls[] = { "deepsea", "dusk", "forest", "mist", "none" };
static const char *const g_wall_labels[] = { "深海", "暮色", "森林", "晨雾", "纯色" };
#define NWALLS ((int)(sizeof g_walls / sizeof g_walls[0]))
static char g_wallname[16] = "deepsea";
static void apply_theme(void)
{
    if (g_theme_mode == 1) g_theme = 0;
    else if (g_theme_mode == 2) g_theme = 1;
    else g_theme = !strcmp(g_wallname, "mist");      /* light wallpapers get dark text */
}
static void apply_wallpaper(void)
{
    apply_theme();
    char path[160];
    if (!strcmp(g_wallname, "none")) path[0] = 0;
    else snprintf(path, sizeof path, "%s/%s.png", WALL_DIR, g_wallname);
    html_view_set_wallpaper(path);
}
static void load_conf(void)
{
    FILE *fp = fopen(CONF_FILE, "r");
    int have_mode = 0;
    if (!fp) return;
    char line[64], sval[16]; int v;
    while (fgets(line, sizeof line, fp)) {
        if      (sscanf(line, "theme=%d", &v) == 1)      g_theme = !!v;
        else if (sscanf(line, "theme_mode=%d", &v) == 1) { g_theme_mode = v < 0 || v > 2 ? 0 : v; have_mode = 1; }
        else if (sscanf(line, "wifi_sleep_min=%d", &v) == 1) g_wifi_sleep_min = v < 0 || v > 240 ? 0 : v;
        else if (sscanf(line, "plan_on=%d", &v) == 1) g_plan_on = v ? 1 : 0;
        else if (sscanf(line, "plan_gb=%d", &v) == 1) g_plan_gb = v >= 10 && v <= 99990 ? v : 2000;
        else if (sscanf(line, "pr_mode=%d", &v) == 1) g_pr_mode_pref = v >= 0 && v <= 2 ? v : -1;
        else if (sscanf(line, "pr_net=%d", &v) == 1) g_pr_net_pref = v == 0 || v == 1 ? v : -1;
        else if (sscanf(line, "chg_cap=%d", &v) == 1) g_chg_cap = v == 70 || v == 80 || v == 90 || v == 95 ? v : 0;
        else if (sscanf(line, "chg_cur=%d", &v) == 1) g_chg_cur = v == 2000 || v == 1500 || v == 1000 || v == 500 ? v : 0;
        else if (sscanf(line, "speed_bits=%d", &v) == 1) g_speed_bits = !!v;
        else if (sscanf(line, "show_batpct=%d", &v) == 1) g_show_batpct = !!v;
        else if (sscanf(line, "autooff=%d", &v) == 1)    g_autooff_ms = v;
        else if (sscanf(line, "refresh_ms=%d", &v) == 1) g_refresh_ms = normalize_refresh_ms(v);
        else if (sscanf(line, "sig_read=%d", &v) == 1)   g_sig_read = !!v;
        else if (sscanf(line, "sig_parse=%d", &v) == 1)  g_sig_parse = !!v;
        else if (sscanf(line, "bright=%d", &v) == 1)     g_saved_bright = v;
        else if (sscanf(line, "cover=%d", &v) == 1)      g_cover = !!v;
        else if (sscanf(line, "wallpaper=%15s", sval) == 1) {
            for (int k = 0; k < NWALLS; k++)
                if (!strcmp(sval, g_walls[k])) snprintf(g_wallname, sizeof g_wallname, "%s", g_walls[k]);
        }
        else if (sscanf(line, "st_src=%15s", sval) == 1) snprintf(g_st_src, sizeof g_st_src, "%s", sval);
        else if (sscanf(line, "st_dir=%15s", sval) == 1) snprintf(g_st_dir, sizeof g_st_dir, "%s", sval);
        else if (sscanf(line, "st_dur=%d", &v) == 1)     g_st_dur = v;
    }
    fclose(fp);
    if (!have_mode) g_theme_mode = g_theme ? 2 : 0;   /* older config: keep an explicit light choice */
}
static void save_conf(void)
{
    /* write-then-rename: idle-guard.sh reads this file, never let it see half a file */
    FILE *fp = fopen(CONF_FILE ".tmp", "w");
    if (!fp) return;
    fprintf(fp,
            "theme=%d\nspeed_bits=%d\nshow_batpct=%d\nautooff=%d\nrefresh_ms=%d\nsig_read=%d\nsig_parse=%d\nbright=%d\nst_src=%s\nst_dir=%s\nst_dur=%d\ncover=%d\nwallpaper=%s\ntheme_mode=%d\nwifi_sleep_min=%d\nchg_cap=%d\nchg_cur=%d\npr_mode=%d\npr_net=%d\nplan_on=%d\nplan_gb=%d\n",
            g_theme, g_speed_bits, g_show_batpct, g_autooff_ms, g_refresh_ms,
            g_sig_read, g_sig_parse, backlight_get(), g_st_src, g_st_dir, g_st_dur,
            g_cover, g_wallname, g_theme_mode, g_wifi_sleep_min, g_chg_cap, g_chg_cur, g_pr_mode_pref, g_pr_net_pref, g_plan_on, g_plan_gb);
    if (fclose(fp) == 0) rename(CONF_FILE ".tmp", CONF_FILE);
}

static const char *speedtest_norm_src(const char *src)
{
    if (!strcmp(src, "cnspeed")) return "cnspeed";
    if (!strcmp(src, "ookla")) return "ookla";
    if (!strcmp(src, "cdn")) return "cdn";
    return "auto";
}

static const char *speedtest_norm_dir(const char *dir)
{
    if (!strcmp(dir, "dl")) return "dl";
    if (!strcmp(dir, "ul")) return "ul";
    return "both";
}

static int speedtest_norm_dur(int sec)
{
    if (sec == 0) return 0;   /* 0 = loop until stopped by the user */
    if (sec == 10 || sec == 15 || sec == 20) return sec;
    return 15;
}

static int speedtest_loop_mode(void)
{
    return g_st_dur == 0;
}

static void speedtest_apply_saved_prefs(void)
{
    snprintf(g_st_src, sizeof g_st_src, "%s", speedtest_norm_src(g_st_src));
    snprintf(g_st_dir, sizeof g_st_dir, "%s", speedtest_norm_dir(g_st_dir));
    g_st_dur = speedtest_norm_dur(g_st_dur);
}

static int speedtest_binary_ready(void)
{
    return access(SPEEDTEST_BIN, X_OK) == 0;
}

static int speedtest_running(void)     /* pidof without forking: this runs every 300 ms */
{
    DIR *dir = opendir("/proc");
    struct dirent *e;
    int found = 0;
    if (!dir) return 0;
    while (!found && (e = readdir(dir))) {
        char path[64], comm[32];
        if (e->d_name[0] < '1' || e->d_name[0] > '9') continue;
        snprintf(path, sizeof path, "/proc/%s/comm", e->d_name);
        if (read_line_path(path, comm, sizeof comm) && !strncmp(comm, "better-speedtes", 15)) found = 1;
    }
    closedir(dir);
    return found;
}

static int speedtest_loop_running(void)
{
    long pid = 0;
    if (access(SPEEDTEST_LOOP_FLAG, F_OK) != 0) return 0;
    if (read_long_path(SPEEDTEST_LOOP_PID, &pid) && pid > 0 && kill((pid_t)pid, 0) == 0)
        return 1;
    return speedtest_running();
}

static double g_st_ping_live;       /* from the "node" lines, before the result arrives */
static char g_st_node_live[48];

static void speedtest_clear_data(void)
{
    g_st_have_result = 0;
    g_st_phase[0] = 0;
    g_st_msg[0] = 0;
    g_st_err[0] = 0;
    g_st_node[0] = 0;
    g_st_source[0] = 0;
    g_st_carrier[0] = 0;
    g_st_city[0] = 0;
    g_st_ulmsg[0] = 0;
    g_st_cur_mbps = g_st_cur_peak = 0;
    g_st_dl_avg = g_st_dl_peak = 0;
    g_st_ul_avg = g_st_ul_peak = 0;
    g_st_ping = g_st_jitter = 0;
    g_st_ping_live = 0;
    g_st_node_live[0] = 0;
}

static void speedtest_hist_clear(void)
{
    g_st_dl_n = 0;
    g_st_ul_n = 0;
}

static void speedtest_hist_push(int *hist, int *n, double mbps)
{
    int v;
    if (mbps < 0.0) mbps = 0.0;
    v = (int)(mbps * 10.0 + 0.5);
    if (*n < ST_HIST) {
        hist[(*n)++] = v;
    } else {
        memmove(hist, hist + 1, (ST_HIST - 1) * sizeof hist[0]);
        hist[ST_HIST - 1] = v;
    }
}

static int speedtest_json_str(const char *line, const char *key, char *out, size_t cap)
{
    char needle[48];
    const char *p;
    size_t o = 0;
    snprintf(needle, sizeof needle, "\"%s\":", key);
    p = strstr(line, needle);
    if (!p || cap == 0) return 0;
    p += strlen(needle);
    while (*p == ' ' || *p == '\t') p++;
    if (*p != '"') return 0;
    p++;
    while (*p && *p != '"' && o + 1 < cap) {
        if (*p == '\\' && p[1]) p++;
        out[o++] = *p++;
    }
    out[o] = 0;
    return 1;
}

static int speedtest_json_num(const char *line, const char *key, double *out)
{
    char needle[48];
    char *end = NULL;
    const char *p;
    snprintf(needle, sizeof needle, "\"%s\":", key);
    p = strstr(line, needle);
    if (!p) return 0;
    p += strlen(needle);
    while (*p == ' ' || *p == '\t') p++;
    *out = strtod(p, &end);
    return end && end != p;
}

static const char *speedtest_phase_label(const char *phase)
{
    if (!strcmp(phase, "download")) return "下行测速";
    if (!strcmp(phase, "upload")) return "上行测速";
    if (!strcmp(phase, "start")) return "准备测速";
    if (!strcmp(phase, "geo")) return "定位中";
    if (!strcmp(phase, "node")) return "选择节点";
    if (!strcmp(phase, "probe")) return "探测中";
    if (!strcmp(phase, "result")) return "测速完成";
    if (!strcmp(phase, "error")) return "测速失败";
    return "测速中";
}

static void speedtest_parse_line(const char *line)
{
    char phase[24];
    if (!line || !line[0] || !strcmp(line, "DONE")) return;
    if (!speedtest_json_str(line, "phase", phase, sizeof phase)) return;
    snprintf(g_st_phase, sizeof g_st_phase, "%s", phase);
    if (!strcmp(phase, "download") || !strcmp(phase, "upload")) {
        (void)speedtest_json_num(line, "mbps", &g_st_cur_mbps);
        (void)speedtest_json_num(line, "peak", &g_st_cur_peak);
        if (!strcmp(phase, "download"))
            speedtest_hist_push(g_st_dl_hist, &g_st_dl_n, g_st_cur_mbps);
        else
            speedtest_hist_push(g_st_ul_hist, &g_st_ul_n, g_st_cur_mbps);
        g_st_state = ST_STATE_RUNNING;
        return;
    }
    if (!strcmp(phase, "result")) {
        g_st_have_result = 1;
        (void)speedtest_json_str(line, "node", g_st_node, sizeof g_st_node);
        (void)speedtest_json_str(line, "source", g_st_source, sizeof g_st_source);
        (void)speedtest_json_str(line, "carrier", g_st_carrier, sizeof g_st_carrier);
        (void)speedtest_json_str(line, "city", g_st_city, sizeof g_st_city);
        (void)speedtest_json_str(line, "ul_msg", g_st_ulmsg, sizeof g_st_ulmsg);
        (void)speedtest_json_num(line, "dl_avg", &g_st_dl_avg);
        (void)speedtest_json_num(line, "dl_peak", &g_st_dl_peak);
        (void)speedtest_json_num(line, "ul_avg", &g_st_ul_avg);
        (void)speedtest_json_num(line, "ul_peak", &g_st_ul_peak);
        (void)speedtest_json_num(line, "ping", &g_st_ping);
        (void)speedtest_json_num(line, "jitter", &g_st_jitter);
        g_st_state = ST_STATE_DONE;
        return;
    }
    if (speedtest_json_str(line, "msg", g_st_msg, sizeof g_st_msg)) {
        const char *pg = strstr(g_st_msg, "ping=");       /* "武汉联通 1.2.3.4:5 ping=16ms 下载中" */
        if (pg) g_st_ping_live = atof(pg + 5);
        if (!strcmp(phase, "node")) {
            snprintf(g_st_node_live, sizeof g_st_node_live, "%s", g_st_msg);
            char *sp = strchr(g_st_node_live, ' '); if (sp) *sp = 0;
        }
        if (!strcmp(phase, "error")) {
            snprintf(g_st_err, sizeof g_st_err, "Test failed");
            g_st_state = ST_STATE_FAIL;
        } else {
            g_st_state = ST_STATE_RUNNING;
        }
    }
}

static int speedtest_poll(uint32_t now_ms)
{
    int prev_state = g_st_state, prev_installed = g_st_installed, prev_have_result = g_st_have_result;
    double prev_dl = g_st_dl_avg, prev_ul = g_st_ul_avg;
    double prev_ping = g_st_ping, prev_jitter = g_st_jitter;
    char prev_phase[24], prev_msg[160], prev_err[160], prev_node[96], prev_source[32], prev_ulmsg[96];
    snprintf(prev_phase, sizeof prev_phase, "%s", g_st_phase);
    snprintf(prev_msg, sizeof prev_msg, "%s", g_st_msg);
    snprintf(prev_err, sizeof prev_err, "%s", g_st_err);
    snprintf(prev_node, sizeof prev_node, "%s", g_st_node);
    snprintf(prev_source, sizeof prev_source, "%s", g_st_source);
    snprintf(prev_ulmsg, sizeof prev_ulmsg, "%s", g_st_ulmsg);

    g_st_installed = speedtest_binary_ready();
    if (g_st_installed < 0) g_st_installed = 0;
    {
        int running = speedtest_running();
        int loop_running = speedtest_loop_running();
        char *log = read_file(SPEEDTEST_LOG);
        if (loop_running) running = 1;
        if (log && log[0]) {
            char *save = NULL;
            speedtest_clear_data();
            speedtest_hist_clear();
            for (char *line = strtok_r(log, "\r\n", &save); line; line = strtok_r(NULL, "\r\n", &save))
                speedtest_parse_line(line);
            if (running) {
                if (!g_st_have_result && g_st_state != ST_STATE_FAIL)
                    g_st_state = ST_STATE_RUNNING;
                if (loop_running && g_st_have_result)
                    g_st_state = ST_STATE_RUNNING;
            } else if (g_st_have_result) {
                g_st_state = ST_STATE_DONE;
            } else if (g_st_err[0] || g_st_phase[0] || g_st_msg[0]) {
                if (!g_st_err[0]) snprintf(g_st_err, sizeof g_st_err, "测速结束但没有结果");
                g_st_state = ST_STATE_FAIL;
            } else {
                g_st_state = g_st_installed ? ST_STATE_IDLE : ST_STATE_MISSING;
            }
        } else if (!running) {
            if (!g_st_installed) g_st_state = ST_STATE_MISSING;
            else if (g_st_state == ST_STATE_RUNNING) g_st_state = ST_STATE_IDLE;
            else if (g_st_state == ST_STATE_MISSING) g_st_state = ST_STATE_IDLE;
        } else {
            g_st_state = ST_STATE_RUNNING;
            if (!g_st_msg[0] && !g_st_phase[0]) snprintf(g_st_msg, sizeof g_st_msg, "测速中");
        }
        free(log);
    }
    g_st_poll_at = now_ms;
    return prev_state != g_st_state || prev_installed != g_st_installed || prev_have_result != g_st_have_result ||
           strcmp(prev_phase, g_st_phase) || strcmp(prev_msg, g_st_msg) || strcmp(prev_err, g_st_err) ||
           strcmp(prev_node, g_st_node) || strcmp(prev_source, g_st_source) || strcmp(prev_ulmsg, g_st_ulmsg) ||
           fabs(prev_dl - g_st_dl_avg) > 0.04 || fabs(prev_ul - g_st_ul_avg) > 0.04 ||
           fabs(prev_ping - g_st_ping) > 0.04 || fabs(prev_jitter - g_st_jitter) > 0.04;
}


/* ---- 测速 page v2 (Speedtest-style): header row ping/dl/ul, a GO ring when idle, a
 * 240° gauge while running, two result cards when done. Backend logic above is
 * unchanged; these build the HTML, draw_speedtest_widgets() paints the native parts. */
static double st_hist_avg(const int *h, int n)
{
    long s = 0; for (int i = 0; i < n; i++) s += h[i];
    return n ? s / 10.0 / n : 0;    /* hist stores Mbps * 10 */
}
static double st_ping_now(void)
{
    return g_st_ping > 0 ? g_st_ping : g_st_ping_live;
}
static const char *st_fmt(char *b, size_t n, double v)
{
    if (v <= 0) snprintf(b, n, "—");
    else if (v < 10) snprintf(b, n, "%.1f", v);
    else snprintf(b, n, "%.0f", v);
    return b;
}
/* v3 layout (320x480, absolute): 10 px gutters, 3 columns of 100 px, 2 columns of
 * 145 px + 10 px gap. Header only while idle/running; the result screen has its own cards. */
static const char *speedtest_hdr_html(void)
{
    static char b[760];
    char p[16], d[16], u[16];
    if (g_st_state == ST_STATE_DONE && g_st_have_result) { b[0] = 0; return b; }
    /* a value freezes once its phase is over: download during the upload phase */
    int dl_over = g_st_state == ST_STATE_RUNNING && g_st_dl_n > 0 && strcmp(g_st_phase, "download");
    double dl = dl_over ? st_hist_avg(g_st_dl_hist, g_st_dl_n) : 0;
    snprintf(b, sizeof b,
        "<div class='sthdr'><div class='sth'><div class='k'><i class='stdot pg'></i>延迟</div><div class='%s'>%s<span class='u'>ms</span></div></div>"
        "<div class='sth'><div class='k'><i class='stdot dl'></i>下载</div><div class='%s'>%s<span class='u'>Mbps</span></div></div>"
        "<div class='sth'><div class='k'><i class='stdot ul'></i>上传</div><div class='stv ph dim'>--<span class='u'>Mbps</span></div></div></div>",
        st_ping_now() > 0 ? "n stv" : "stv ph dim", st_ping_now() > 0 ? st_fmt(p, sizeof p, st_ping_now()) : "--",
        dl > 0 ? "n stv" : "stv ph dim", dl > 0 ? st_fmt(d, sizeof d, dl) : "--");
    (void)u;
    return b;
}
static const char *speedtest_main_html(void)
{
    static char b[2400];
    if (g_st_state == ST_STATE_MISSING) {
        snprintf(b, sizeof b, "<div class='stmiss k'>测速程序未安装（/data/plugins/better-speedtest）</div>");
    } else if (g_st_state == ST_STATE_RUNNING) {
        snprintf(b, sizeof b, "<a href='act:ststop' id='st-ring' class='string'></a><div id='st-live' class='card stlive'></div>");
    } else if (g_st_state == ST_STATE_DONE && g_st_have_result) {
        int secs = g_st_dur > 0 ? g_st_dur : 15;
        double mb = (g_st_dl_avg + g_st_ul_avg) * secs / 8.0;
        char d[16], u[16], pg[16], jt[16];
        snprintf(b, sizeof b,
            "<div class='card strc l'><div class='k'>↓ 下载 · 峰值 %.0f</div><div class='n stbig dl'>%s<span class='u'>Mbps</span></div><div id='st-chart-dl' class='stspk'></div></div>"
            "<div class='card strc r'><div class='k'>↑ 上传 · 峰值 %.0f</div><div class='n stbig ul'>%s<span class='u'>Mbps</span></div><div id='st-chart-ul' class='stspk'></div></div>"
            "<div class='card ststat'><div class='stc'><div class='k'>延迟</div><span class='n'>%s</span><span class='k u'>ms</span></div>"
            "<div class='stc sep'><div class='k'>抖动</div><span class='n'>%s</span><span class='k u'>ms</span></div>"
            "<div class='stc sep'><div class='k'>约用流量</div><span class='n'>%.0f</span><span class='k u'>MB</span></div></div>"
            "<a href='act:ststart' class='stagain'>再测一次</a>",
            g_st_dl_peak, st_fmt(d, sizeof d, g_st_dl_avg), g_st_ul_peak, st_fmt(u, sizeof u, g_st_ul_avg),
            st_fmt(pg, sizeof pg, st_ping_now()), g_st_jitter > 0 ? st_fmt(jt, sizeof jt, g_st_jitter) : "0", mb);
    } else {
        snprintf(b, sizeof b, "<a href='act:ststart' id='st-go' class='stgo'></a>%s",
                 g_st_state == ST_STATE_FAIL ? "<div class='k stfail'>上次测速失败，点开始重试</div>" : "");
    }
    return b;
}
static const char *speedtest_pills_html(void)
{
    static char b[600];
    if (g_st_state == ST_STATE_RUNNING || g_st_state == ST_STATE_MISSING) { b[0] = 0; return b; }
    const char *src = !strcmp(g_st_src, "cnspeed") ? "国内" : !strcmp(g_st_src, "cdn") ? "CDN" : !strcmp(g_st_src, "ookla") ? "Ookla" : "自动";
    const char *dir = !strcmp(g_st_dir, "dl") ? "下载" : !strcmp(g_st_dir, "ul") ? "上传" : "双向";
    char dur[16]; if (g_st_dur > 0) snprintf(dur, sizeof dur, "%d 秒", g_st_dur); else snprintf(dur, sizeof dur, "一直测");
    snprintf(b, sizeof b, "<div class='stpills%s'><a href='act:stcyc:src' class='stpill'><span class='k'>节点 </span>%s</a>"
             "<a href='act:stcyc:dir' class='stpill'><span class='k'>方向 </span>%s</a><a href='act:stcyc:dur' class='stpill'><span class='k'>时长 </span>%s</a></div>",
             g_st_state == ST_STATE_DONE && g_st_have_result ? " res" : "", src, dir, dur);
    return b;
}
static const char *speedtest_node_sub(void)
{
    static char b[64];
    if (g_st_state == ST_STATE_RUNNING) {
        if (st_ping_now() > 0) snprintf(b, sizeof b, "ping %.0f ms", st_ping_now());
        else snprintf(b, sizeof b, "%s", speedtest_phase_label(g_st_phase));
    } else if (g_st_state == ST_STATE_DONE && g_st_have_result) {
        const char *src = !strcmp(g_st_source, "cnspeed") ? "国内节点" : g_st_source[0] ? g_st_source : "测速节点";
        if (g_st_dur > 0) snprintf(b, sizeof b, "%s · %d 秒", src, g_st_dur);
        else snprintf(b, sizeof b, "%s", src);
    } else snprintf(b, sizeof b, "测速节点");
    return b;
}
static const char *speedtest_node_text(void)
{
    static char b[64];
    snprintf(b, sizeof b, "%s", g_st_node[0] ? g_st_node : g_st_node_live[0] ? g_st_node_live : "自动选点");
    char *sp = strchr(b, ' '); if (sp) *sp = 0;    /* "武汉联通 1.2.3.4:5 …" -> name only */
    return b;
}

static double g_st_disp, g_st_disp_t, g_st_disp_vmax = 1;   /* eased ring value / chart tip / chart scale */

static void speedtest_start(void)
{
    g_st_disp = g_st_disp_t = 0; g_st_disp_vmax = 1;
    char cmd[1536], extra[32] = "";
    speedtest_apply_saved_prefs();
    g_st_installed = speedtest_binary_ready();
    if (!g_st_installed) {
        speedtest_clear_data();
        speedtest_hist_clear();
        snprintf(g_st_err, sizeof g_st_err, "未安装测速器");
        g_st_state = ST_STATE_MISSING;
        return;
    }
    if (!strcmp(g_st_dir, "dl")) snprintf(extra, sizeof extra, " --no-upload");
    else if (!strcmp(g_st_dir, "ul")) snprintf(extra, sizeof extra, " --no-download");
    speedtest_clear_data();
    speedtest_hist_clear();
    snprintf(g_st_msg, sizeof g_st_msg, "正在启动");
    g_st_state = ST_STATE_RUNNING;
    if (speedtest_loop_mode()) {
        snprintf(cmd, sizeof cmd,
                 "rm -f " SPEEDTEST_LOG " " SPEEDTEST_LOOP_PID "; : > " SPEEDTEST_LOG "; touch " SPEEDTEST_LOOP_FLAG "; "
                 "(while [ -f " SPEEDTEST_LOOP_FLAG " ]; do "
                 ": > " SPEEDTEST_LOG "; "
                 "echo '{\"phase\":\"start\",\"msg\":\"循环测速中，手动停止前不会自动结束\"}' >> " SPEEDTEST_LOG "; "
                 SPEEDTEST_WAN_ENV SPEEDTEST_BIN " test --json --src %s --dur 15%s >> " SPEEDTEST_LOG " 2>&1; "
                 "sleep 1; "
                 "done) & echo $! > " SPEEDTEST_LOOP_PID,
                 g_st_src, extra);
    } else {
        unlink(SPEEDTEST_LOOP_FLAG);
        unlink(SPEEDTEST_LOOP_PID);
        snprintf(cmd, sizeof cmd,
                 "rm -f " SPEEDTEST_LOG "; : > " SPEEDTEST_LOG "; (" SPEEDTEST_WAN_ENV SPEEDTEST_BIN " test --json --src %s --dur %d%s > " SPEEDTEST_LOG " 2>&1) &",
                 g_st_src, g_st_dur, extra);
    }
    if (system(cmd) != 0) {
        speedtest_hist_clear();
        snprintf(g_st_err, sizeof g_st_err, "启动失败");
        g_st_state = ST_STATE_FAIL;
    }
}

static void speedtest_stop(void)
{
    unlink(SPEEDTEST_LOOP_FLAG);
    system("if [ -s " SPEEDTEST_LOOP_PID " ]; then kill -9 $(cat " SPEEDTEST_LOOP_PID ") 2>/dev/null || true; fi; "
           "for p in $(pidof better-speedtest 2>/dev/null); do kill -9 $p; done");
    unlink(SPEEDTEST_LOOP_PID);
    unlink(SPEEDTEST_LOG);
    speedtest_clear_data();
    speedtest_hist_clear();
    g_st_installed = speedtest_binary_ready();
    g_st_state = g_st_installed ? ST_STATE_IDLE : ST_STATE_MISSING;
    snprintf(g_st_msg, sizeof g_st_msg, "已停止");
}

static int path_is_speedtest(const char *path)
{
    const char *base = strrchr(path, '/');
    if (!base) base = path; else base++;
    return !strcmp(base, "07-speedtest.html") || !strcmp(base, "speedtest.html") ||
           strstr(base, "-speedtest.html") != NULL;
}

static int path_is_signal_detail(const char *path)
{
    if (!path) return 0;           /* refresh_status_cache() passes NULL */
    const char *base = strrchr(path, '/');
    if (!base) base = path; else base++;
    return !strcmp(base, "01a-cell.html") || strstr(base, "cell.html") != NULL;
}

static int path_is_signal_home(const char *path)
{
    if (!path) return 0;           /* refresh_status_cache() passes NULL */
    const char *base = strrchr(path, '/');
    if (!base) base = path; else base++;
    return !strcmp(base, "01-signal.html") || strstr(base, "-signal.html") != NULL;
}

static int path_is_signal_page(const char *path)
{
    return path_is_signal_home(path) || path_is_signal_detail(path);
}

static int signal_live_enabled(void)
{
    /* Raw reads may stay on for datad, but UI decoded cards obey parse only. */
    return g_sig_parse;
}

static int speedtest_page_index(void)
{
    for (int i = 0; i < g_npages; i++)
        if (path_is_speedtest(g_pages[i])) return i;
    return -1;
}

static int subpage_name_ok(const char *name)
{
    size_t l;
    if (!name || !*name) return 0;
    if (strstr(name, "..") || strchr(name, '/') || strchr(name, '\\')) return 0;
    if (strpbrk(name, "\"'<>&")) return 0;
    l = strlen(name);
    return l > 5 && strcmp(name + l - 5, ".html") == 0;
}

static int subpage_open(const char *name)
{
    char path[300];
    if (!subpage_name_ok(name)) return 0;
    snprintf(path, sizeof path, "%s/subpages/%s", UI_DIR, name);
    if (access(path, R_OK) != 0) return 0;
    snprintf(g_subpage, sizeof g_subpage, "%s", name);
    snprintf(g_subpage_path, sizeof g_subpage_path, "%s", path);
    g_scroll = 0;
    return 1;
}

static int function_page_open(const char *name)
{
    char path[300];
    if (!subpage_name_ok(name)) return 0;
    snprintf(path, sizeof path, "%s/%s", FUNCTIONS_DIR, name);
    if (access(path, R_OK) != 0) return 0;
    snprintf(g_subpage, sizeof g_subpage, "func:%s", name);
    snprintf(g_subpage_path, sizeof g_subpage_path, "%s", path);
    g_scroll = 0;
    return 1;
}

static void subpage_close(void)
{
    g_subpage[0] = 0;
    g_subpage_path[0] = 0;
    g_scroll = 0;
}

static const char *active_page_path(void)
{
    if (g_subpage[0]) return g_subpage_path;
    if (g_npages > 0 && g_cur >= 0 && g_cur < g_npages) return g_pages[g_cur];
    return "";
}

static int path_is_function_page(const char *path)
{
    size_t l = strlen(FUNCTIONS_DIR);
    return path && !strncmp(path, FUNCTIONS_DIR, l) && path[l] == '/';
}

static void function_label_from_name(char *dst, size_t cap, const char *name)
{
    size_t l;
    if (!dst || cap == 0) return;
    dst[0] = 0;
    if (!name) return;
    l = strlen(name);
    if (l > 5 && !strcmp(name + l - 5, ".html")) l -= 5;
    if (l >= cap) l = cap - 1;
    memcpy(dst, name, l);
    dst[l] = 0;
    for (size_t i = 0; dst[i]; i++)
        if (dst[i] == '_' || dst[i] == '-') dst[i] = ' ';
}

static int function_title_from_html(const char *html, char *dst, size_t cap)
{
    const char *p, *gt, *end;
    size_t l;
    if (!html || !dst || cap == 0) return 0;
    p = strcasestr(html, "<title");
    if (!p) return 0;
    gt = strchr(p, '>');
    if (!gt) return 0;
    gt++;
    end = strcasestr(gt, "</title>");
    if (!end || end <= gt) return 0;
    while (gt < end && (*gt == ' ' || *gt == '\t' || *gt == '\r' || *gt == '\n')) gt++;
    while (end > gt && (end[-1] == ' ' || end[-1] == '\t' || end[-1] == '\r' || end[-1] == '\n')) end--;
    l = (size_t)(end - gt);
    if (l >= cap) l = cap - 1;
    memcpy(dst, gt, l);
    dst[l] = 0;
    return dst[0] != 0;
}

static void function_title_for_file(char *dst, size_t cap, const char *path, const char *name)
{
    char *html = read_file(path);
    if (html) {
        if (function_title_from_html(html, dst, cap)) {
            free(html);
            return;
        }
        free(html);
    }
    function_label_from_name(dst, cap, name);
}

static int g_st_home_open = 0;

static const char *speedtest_home_button_html(void)
{
    if (g_lock_state || !speedtest_binary_ready()) return "";
    return g_st_home_open ?
           "<a href='act:sttoggle' class='speed-home on'>收起测速</a>" :
           "<a href='act:sttoggle' class='speed-home'>网络测速</a>";
}

static const char *speedtest_function_tile_html(void)
{
    if (!speedtest_binary_ready()) return "";
    return "<a href='act:sub:speedtest.html' class='card tile'>"
           "<span class='th'>测速</span>"
           "<span class='ts'>完整测速仪表盘</span>"
           "</a>";
}

static const char *custom_function_tiles_html(void)
{
    static char buf[8192];
    char names[32][64];
    int n = 0;
    DIR *dp;
    struct dirent *de;
    int o = 0;

    buf[0] = 0;
    mkdir(FUNCTIONS_DIR, 0755);
    dp = opendir(FUNCTIONS_DIR);
    if (!dp) return buf;
    while ((de = readdir(dp)) && n < 32) {
        if (de->d_name[0] == '.') continue;
        if (!subpage_name_ok(de->d_name)) continue;
        snprintf(names[n], sizeof names[n], "%s", de->d_name);
        n++;
    }
    closedir(dp);
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++)
            if (strcmp(names[i], names[j]) > 0) {
                char t[64]; strcpy(t, names[i]); strcpy(names[i], names[j]); strcpy(names[j], t);
            }

    for (int i = 0; i < n; i++) {
        char path[300], raw[96], title[160], href[160];
        snprintf(path, sizeof path, "%s/%s", FUNCTIONS_DIR, names[i]);
        function_title_for_file(raw, sizeof raw, path, names[i]);
        html_esc(title, sizeof title, raw);
        html_esc(href, sizeof href, names[i]);
        o += snprintf(buf + o, sizeof buf - o,
                      "<a href=\"act:func:%s\" class=\"func-tile func-custom\">"
                      "<span class=\"func-name\">%s</span>"
                      "<span class=\"func-desc\">自定义页面</span>"
                      "</a>",
                      href, title);
        if (o >= (int)sizeof(buf) - 256) break;
    }
    return buf;
}

static const char *speedtest_src_html(void)
{
    static const struct { const char *v; const char *lab; } opts[4] = {
        { "auto", "自动" }, { "cnspeed", "全球网测" }, { "ookla", "Ookla" }, { "cdn", "CDN" } };
    static char buf[512];
    int o = snprintf(buf, sizeof buf, "<div class='stseg'>");
    for (int i = 0; i < 4; i++)
        o += snprintf(buf + o, sizeof buf - o, "<a href='act:stsrc:%s' class='stsegc%s'>%s</a>",
                      opts[i].v, !strcmp(g_st_src, opts[i].v) ? " on" : "", opts[i].lab);
    snprintf(buf + o, sizeof buf - o, "</div>");
    return buf;
}

static const char *speedtest_dir_html(void)
{
    static const struct { const char *v; const char *lab; } opts[3] = {
        { "both", "上下行" }, { "dl", "下行" }, { "ul", "上行" } };
    static char buf[384];
    int o = snprintf(buf, sizeof buf, "<div class='stseg'>");
    for (int i = 0; i < 3; i++)
        o += snprintf(buf + o, sizeof buf - o, "<a href='act:stdir:%s' class='stsegc%s'>%s</a>",
                      opts[i].v, !strcmp(g_st_dir, opts[i].v) ? " on" : "", opts[i].lab);
    snprintf(buf + o, sizeof buf - o, "</div>");
    return buf;
}

static const char *speedtest_dur_html(void)
{
    static const struct { int sec; const char *lab; } opts[4] = {
        { 10, "10s" }, { 15, "15s" }, { 20, "20s" }, { 0, "循环" } };
    static char buf[420];
    int o = snprintf(buf, sizeof buf, "<div class='stseg'>");
    for (int i = 0; i < 4; i++)
        o += snprintf(buf + o, sizeof buf - o, "<a href='act:stdur:%d' class='stsegc%s'>%s</a>",
                      opts[i].sec,
                      g_st_dur == opts[i].sec ? (opts[i].sec == 0 ? " loop on" : " on") : (opts[i].sec == 0 ? " loop" : ""),
                      opts[i].lab);
    snprintf(buf + o, sizeof buf - o, "</div>");
    return buf;
}

static const char *speedtest_loop_hint_html(void)
{
    if (!speedtest_loop_mode()) return "";
    return "<div class='stloop-warn'>循环测速不会自动停止，注意流量消耗。</div>";
}

static const char *speedtest_install_html(void)
{
    static char buf[256], esc[160];
    if (g_st_installed > 0) return "";
    html_esc(esc, sizeof esc, SPEEDTEST_BIN);
    snprintf(buf, sizeof buf, "<div class='sthint bad'>未安装：<span class='mono'>%s</span></div>", esc);
    return buf;
}

static const char *speedtest_action_html(void)
{
    if (g_st_installed <= 0) return "<span class='stbtn dis'>安装后可用</span>";
    if (g_st_state == ST_STATE_RUNNING) return "<a href='act:ststop' class='stbtn stop'>停止测速</a>";
    if (speedtest_loop_mode()) return "<a href='act:ststart' class='stbtn loop'>开始循环测速</a>";
    return "<a href='act:ststart' class='stbtn'>开始测速</a>";
}

static int speedtest_pct(double v, double scale)
{
    int pct;
    if (scale < 1.0) scale = 1.0;
    if (v < 0.0) v = 0.0;
    pct = (int)(v * 100.0 / scale + 0.5);
    if (v > 0.0 && pct < 4) pct = 4;
    if (pct > 100) pct = 100;
    return pct;
}

static void speedtest_chart_row(char *buf, size_t cap, int *o,
                                const char *lab, double val, double scale,
                                const char *unit, const char *cls)
{
    int pct = speedtest_pct(val, scale);
    if (*o >= (int)cap) return;
    *o += snprintf(buf + *o, cap - (size_t)*o,
                   "<div class='stbar-row'><span class='stbar-lab'>%s</span>"
                   "<span class='stbar-box'><span class='stbar-fill %s' style='width:%d%%'></span></span>"
                   "<span class='stbar-val'>%.1f%s</span></div>",
                   lab, cls ? cls : "", pct, val, unit);
}

static const char *speedtest_gauge_html(void)
{
    static char buf[640];
    double cur = 0.0, peak = 0.0, scale = 100.0;
    const char *label = "待机";
    char sub[128];
    int pct;
    if (g_st_state == ST_STATE_RUNNING) {
        cur = g_st_cur_mbps;
        peak = g_st_cur_peak;
        label = (!strcmp(g_st_phase, "upload")) ? "当前上行" :
                (!strcmp(g_st_phase, "download")) ? "当前下行" : "测速中";
        snprintf(sub, sizeof sub, "%s / 峰值 %.1f Mbps", speedtest_phase_label(g_st_phase), peak);
    } else if (g_st_have_result) {
        cur = g_st_dl_avg >= g_st_ul_avg ? g_st_dl_avg : g_st_ul_avg;
        peak = g_st_dl_peak >= g_st_ul_peak ? g_st_dl_peak : g_st_ul_peak;
        label = "本次速度";
        snprintf(sub, sizeof sub, "下行 %.1f / 上行 %.1f Mbps", g_st_dl_avg, g_st_ul_avg);
    } else if (g_st_state == ST_STATE_MISSING) {
        label = "未安装";
        snprintf(sub, sizeof sub, "安装测速器后可用");
    } else if (g_st_state == ST_STATE_FAIL) {
        label = "失败";
        snprintf(sub, sizeof sub, "%s", g_st_err[0] ? g_st_err : "测速失败");
    } else {
        label = "准备就绪";
        snprintf(sub, sizeof sub, "点击开始测速");
    }
    if (peak > scale) scale = peak;
    if (cur > scale) scale = cur;
    pct = speedtest_pct(cur, scale);
    snprintf(buf, sizeof buf,
             "<div class='st-card st-gauge'>"
             "<div class='st-gauge-title'>网速仪表盘</div>"
             "<div class='st-gauge-face'><span class='st-gauge-num'>%.1f</span><span class='st-gauge-unit'>Mbps</span></div>"
             "<div class='st-scale'><span class='st-fill' style='width:%d%%'></span></div>"
             "<div class='st-gauge-sub'>%s · %s</div>"
             "</div>",
             cur, pct, label, sub);
    return buf;
}

static const char *speedtest_chart_html(void)
{
    static char buf[1200];
    int o = 0;
    double speed_scale = 100.0;
    double max_speed = g_st_dl_peak;
    if (g_st_ul_peak > max_speed) max_speed = g_st_ul_peak;
    if (g_st_cur_peak > max_speed) max_speed = g_st_cur_peak;
    if (max_speed > speed_scale) speed_scale = max_speed;
    o += snprintf(buf + o, sizeof buf - (size_t)o, "<div class='st-card st-chart'><div class='st-chart-title'>测速图表</div>");
    if (g_st_have_result) {
        speedtest_chart_row(buf, sizeof buf, &o, "下行", g_st_dl_avg, speed_scale, "M", "");
        speedtest_chart_row(buf, sizeof buf, &o, "峰值", g_st_dl_peak, speed_scale, "M", "");
        speedtest_chart_row(buf, sizeof buf, &o, "上行", g_st_ul_avg, speed_scale, "M", "up");
        speedtest_chart_row(buf, sizeof buf, &o, "峰值", g_st_ul_peak, speed_scale, "M", "up");
        speedtest_chart_row(buf, sizeof buf, &o, "延迟", g_st_ping, 100.0, "ms", "ping");
    } else if (g_st_state == ST_STATE_RUNNING) {
        speedtest_chart_row(buf, sizeof buf, &o, "当前", g_st_cur_mbps, speed_scale, "M", !strcmp(g_st_phase, "upload") ? "up" : "");
        speedtest_chart_row(buf, sizeof buf, &o, "峰值", g_st_cur_peak, speed_scale, "M", !strcmp(g_st_phase, "upload") ? "up" : "");
    } else {
        speedtest_chart_row(buf, sizeof buf, &o, "下行", 0.0, speed_scale, "M", "");
        speedtest_chart_row(buf, sizeof buf, &o, "上行", 0.0, speed_scale, "M", "up");
        speedtest_chart_row(buf, sizeof buf, &o, "延迟", 0.0, 100.0, "ms", "ping");
    }
    snprintf(buf + o, sizeof buf - (size_t)o, "</div>");
    return buf;
}

static double speedtest_display_mbps(void)
{
    if (g_st_state == ST_STATE_RUNNING) return g_st_cur_mbps;
    if (g_st_have_result) return g_st_dl_avg >= g_st_ul_avg ? g_st_dl_avg : g_st_ul_avg;
    return 0.0;
}

static double speedtest_display_peak_mbps(void)
{
    double peak = g_st_cur_peak;
    if (g_st_dl_peak > peak) peak = g_st_dl_peak;
    if (g_st_ul_peak > peak) peak = g_st_ul_peak;
    if (peak < speedtest_display_mbps()) peak = speedtest_display_mbps();
    if (peak < 100.0) peak = 100.0;
    return peak;
}

static const char *speedtest_dial_html(void)
{
    static char buf[720], sub[160], esc[220];
    double cur = speedtest_display_mbps();
    if (g_st_state == ST_STATE_RUNNING) {
        snprintf(sub, sizeof sub, "%s / 峰值 %.1f Mbps", speedtest_phase_label(g_st_phase), g_st_cur_peak);
    } else if (g_st_have_result) {
        snprintf(sub, sizeof sub, "下行 %.1f / 上行 %.1f Mbps", g_st_dl_avg, g_st_ul_avg);
    } else if (g_st_state == ST_STATE_MISSING) {
        snprintf(sub, sizeof sub, "安装测速器后可用");
    } else if (g_st_state == ST_STATE_FAIL) {
        snprintf(sub, sizeof sub, "%s", g_st_err[0] ? g_st_err : "测速失败");
    } else if (speedtest_loop_mode()) {
        snprintf(sub, sizeof sub, "循环模式 / 手动停止");
    } else {
        snprintf(sub, sizeof sub, "准备就绪 / %d秒", g_st_dur);
    }
    html_esc(esc, sizeof esc, sub);
    snprintf(buf, sizeof buf,
             "<div class='st-card st-gauge'>"
             "<div id='st-gauge-dial' class='st-gauge-dial' style='width:184px;height:184px;margin:0 auto'></div>"
             "<div class='st-gauge-sub'>%.1f Mbps · %s</div>"
             "</div>",
             cur, esc);
    return buf;
}

static const char *speedtest_lines_html(void)
{
    static char buf[720];
    double dl = g_st_have_result ? g_st_dl_avg : (g_st_dl_n > 0 ? g_st_dl_hist[g_st_dl_n - 1] / 10.0 : 0.0);
    double ul = g_st_have_result ? g_st_ul_avg : (g_st_ul_n > 0 ? g_st_ul_hist[g_st_ul_n - 1] / 10.0 : 0.0);
    snprintf(buf, sizeof buf,
             "<div class='st-card st-lines'>"
             "<div class='st-line-head'>下行折线<b>%.1f Mbps</b></div>"
             "<div id='st-chart-dl' class='st-line-chart'></div>"
             "<div class='st-line-head'>上行折线<b>%.1f Mbps</b></div>"
             "<div id='st-chart-ul' class='st-line-chart'></div>"
             "</div>",
             dl, ul);
    return buf;
}

static const char *speedtest_home_inline_html(void)
{
    static char buf[8192];
    if (g_lock_state || !g_st_home_open || !speedtest_binary_ready()) return "";
    snprintf(buf, sizeof buf,
             "<div class='st-home-panel'>"
             "%s"
             "%s"
             "<div class='st-card st-options'>"
             "<div class='st-caption'>测速源</div>%s"
             "<div class='st-caption'>方向</div>%s"
             "<div class='st-caption'>时长</div>%s"
             "%s"
             "</div>"
             "<div class='st-actionbar'>%s</div>"
             "</div>",
             speedtest_dial_html(),
             speedtest_lines_html(),
             speedtest_src_html(),
             speedtest_dir_html(),
             speedtest_dur_html(),
             speedtest_loop_hint_html(),
             speedtest_action_html());
    return buf;
}
static const char *speedtest_status_html(void)
{
    static char buf[320], raw[180], esc[256];
    const char *cls = "idle";
    if (g_st_state == ST_STATE_RUNNING) {
        cls = "run";
        if (speedtest_loop_mode() && g_st_have_result)
            snprintf(raw, sizeof raw, "循环测速中 / 手动停止");
        else if (!strcmp(g_st_phase, "download") || !strcmp(g_st_phase, "upload"))
            snprintf(raw, sizeof raw, "%s %.1f Mbps / 峰值 %.1f",
                     speedtest_phase_label(g_st_phase), g_st_cur_mbps, g_st_cur_peak);
        else if (speedtest_loop_mode())
            snprintf(raw, sizeof raw, "循环测速中 / 手动停止");
        else if (g_st_phase[0]) snprintf(raw, sizeof raw, "%s", speedtest_phase_label(g_st_phase));
        else if (g_st_msg[0]) snprintf(raw, sizeof raw, "测速中");
        else snprintf(raw, sizeof raw, "测速中");
    } else if (g_st_state == ST_STATE_DONE) {
        cls = "done";
        snprintf(raw, sizeof raw, "完成 / 下行 %.1f Mbps", g_st_dl_avg);
    } else if (g_st_state == ST_STATE_FAIL) {
        cls = "fail";
        snprintf(raw, sizeof raw, "%s", g_st_err[0] ? g_st_err : "测速失败");
    } else if (g_st_state == ST_STATE_MISSING) {
        cls = "fail";
        snprintf(raw, sizeof raw, "未安装测速器");
    } else {
        snprintf(raw, sizeof raw, "准备就绪 / %d秒", g_st_dur);
    }
    html_esc(esc, sizeof esc, raw);
    snprintf(buf, sizeof buf, "<div class='ststat %s'>%s</div>", cls, esc);
    return buf;
}

static const char *speedtest_result_html(void)
{
    static char buf[1400], node[192], source[96], loc[128], ul[192], err[192];
    char loc_raw[96];
    if (g_st_have_result) {
        html_esc(node, sizeof node, g_st_node[0] ? g_st_node : "-");
        html_esc(source, sizeof source, g_st_source[0] ? g_st_source : "-");
        if (g_st_carrier[0] || g_st_city[0])
            snprintf(loc_raw, sizeof loc_raw, "%s%s%s", g_st_carrier, (g_st_carrier[0] && g_st_city[0]) ? " / " : "", g_st_city);
        else
            snprintf(loc_raw, sizeof loc_raw, "-");
        html_esc(loc, sizeof loc, loc_raw);
        snprintf(ul, sizeof ul, "%.1f / %.1f Mbps", g_st_ul_avg, g_st_ul_peak);
        snprintf(buf, sizeof buf,
                 "<div class='stres'>"
                 "<div class='strow'><span>节点</span><b>%s</b></div>"
                 "<div class='strow'><span>来源</span><b>%s</b></div>"
                 "<div class='strow'><span>位置</span><b>%s</b></div>"
                 "<div class='strow'><span>下行</span><b>%.1f / %.1f Mbps</b></div>"
                 "<div class='strow'><span>上行</span><b>%s</b></div>"
                 "<div class='strow'><span>延迟</span><b>%.1f ms / 抖动 %.1f ms</b></div>"
                 "</div>",
                 node, source, loc, g_st_dl_avg, g_st_dl_peak, ul, g_st_ping, g_st_jitter);
        return buf;
    }
    if (g_st_state == ST_STATE_FAIL) {
        html_esc(err, sizeof err, g_st_err[0] ? g_st_err : "测速失败");
        snprintf(buf, sizeof buf, "<div class='stempty bad'>%s</div>", err);
        return buf;
    }
    if (g_st_state == ST_STATE_RUNNING && speedtest_loop_mode()) return "<div class='stempty'>循环测速中，手动停止前不会自动结束。</div>";
    if (g_st_state == ST_STATE_RUNNING) return "<div class='stempty'>测速进行中，结果稍后显示。</div>";
    if (g_st_state == ST_STATE_MISSING) return "<div class='stempty'>安装测速器后显示结果。</div>";
    return "<div class='stempty'>暂无测速结果。</div>";
}

static const char *speedtest_log_card_html(void)
{
    static char buf[2200];
    snprintf(buf, sizeof buf,
             "<div class='st-card st-log'>"
             "<div class='st-caption'>测速日志</div>"
             "%s%s"
             "</div>",
             speedtest_status_html(),
             speedtest_result_html());
    return buf;
}

static int hsr_freq_is_whitelist(long arfcn)
{
    static const long hsr_arfcn[] = {
        507150, 527070, 531390, 153370,
        505230, 627744, 634464, 423630
    };

    for (size_t i = 0; i < sizeof(hsr_arfcn) / sizeof(hsr_arfcn[0]); i++)
        if (arfcn == hsr_arfcn[i])
            return 1;
    return 0;
}

static int hsr_freq_hint(int mcc, const char *arfcn)
{
    char *end = NULL;
    long v;

    if (mcc != 460 || !arfcn || !arfcn[0] || !strcmp(arfcn, "-"))
        return 0;
    v = strtol(arfcn, &end, 10);
    if (end == arfcn || v <= 0)
        return 0;
    return hsr_freq_is_whitelist(v);
}

#define SIGNAL_MAX_CARRIERS 16
#define SIGNAL_MAX_NEIGHBORS 16

struct signal_carrier_metric {
    int valid;
    int used;
    char name[32];
    char type[16];
    char pci[16];
    char arfcn[32];
    char rb[16];
    char grants[16];
    char dl_rb[16];
    char dl_grants[16];
    char ul_rb[16];
    char ul_grants[16];
    char mcs[16];
    char modulation[32];
    char mimo[48];
    char layers[16];
    char bler[16];
    char ssb[16];
    char serving_ssb[16];
    char ml1_rsrp[16];
    char ml1_rsrq[16];
    char ml1_sinr[16];
};

struct signal_neighbor_metric {
    int valid;
    char pci[16];
    char band[24];
    char arfcn[32];
    char rsrp[16];
    char rsrq[16];
};

static void signal_carrier_metric_reset(struct signal_carrier_metric *c)
{
    if (!c) return;
    memset(c, 0, sizeof *c);
    snprintf(c->name, sizeof c->name, "-");
    snprintf(c->type, sizeof c->type, "-");
    snprintf(c->pci, sizeof c->pci, "-");
    snprintf(c->arfcn, sizeof c->arfcn, "-");
    snprintf(c->rb, sizeof c->rb, "-");
    snprintf(c->grants, sizeof c->grants, "-");
    snprintf(c->dl_rb, sizeof c->dl_rb, "-");
    snprintf(c->dl_grants, sizeof c->dl_grants, "-");
    snprintf(c->ul_rb, sizeof c->ul_rb, "-");
    snprintf(c->ul_grants, sizeof c->ul_grants, "-");
    snprintf(c->mcs, sizeof c->mcs, "-");
    snprintf(c->modulation, sizeof c->modulation, "-");
    snprintf(c->mimo, sizeof c->mimo, "-");
    snprintf(c->layers, sizeof c->layers, "-");
    snprintf(c->bler, sizeof c->bler, "-");
    snprintf(c->ssb, sizeof c->ssb, "-");
    snprintf(c->serving_ssb, sizeof c->serving_ssb, "-");
    snprintf(c->ml1_rsrp, sizeof c->ml1_rsrp, "-");
    snprintf(c->ml1_rsrq, sizeof c->ml1_rsrq, "-");
    snprintf(c->ml1_sinr, sizeof c->ml1_sinr, "-");
}

static void signal_neighbor_metric_reset(struct signal_neighbor_metric *n)
{
    if (!n) return;
    memset(n, 0, sizeof *n);
    snprintf(n->pci, sizeof n->pci, "-");
    snprintf(n->band, sizeof n->band, "-");
    snprintf(n->arfcn, sizeof n->arfcn, "-");
    snprintf(n->rsrp, sizeof n->rsrp, "-");
    snprintf(n->rsrq, sizeof n->rsrq, "-");
}

static const char *signal_carrier_val(const char *v)
{
    return signal_value_present(v) ? v : "-";
}

static void carrier_metric_html(char *dst, size_t cap,
                                const struct signal_carrier_metric *m,
                                int is_nr)
{
    char a[64], b[64], c[64], d[64], e[64], f[64];
    size_t off;

    if (!dst || cap == 0) return;
    dst[0] = 0;
    if (!m || !m->valid) return;

    if (is_nr) {
        const char *ssb = signal_value_present(m->serving_ssb) ? m->serving_ssb : m->ssb;
        html_esc(a, sizeof a, signal_carrier_val(m->mimo));
        html_esc(b, sizeof b, signal_carrier_val(m->layers));
        html_esc(c, sizeof c, signal_carrier_val(m->dl_grants));
        html_esc(d, sizeof d, signal_carrier_val(m->ul_grants));
        html_esc(e, sizeof e, signal_carrier_val(m->dl_rb));
        html_esc(f, sizeof f, signal_carrier_val(m->ul_rb));
        snprintf(dst, cap,
                 "<div class='cx'><span>MIMO %s</span><span>L %s</span>"
                 "<span>G %s/%s</span><span>RB %s/%s</span>",
                 a, b, c, d, e, f);
        html_esc(a, sizeof a, signal_carrier_val(m->bler));
        html_esc(b, sizeof b, signal_carrier_val(ssb));
        snprintf(dst + strlen(dst), cap - strlen(dst),
                 "<span>BLER %s</span><span>SSB %s</span></div>", a, b);
    } else {
        const char *mod = signal_value_present(m->modulation) ? m->modulation : m->mcs;
        html_esc(a, sizeof a, signal_carrier_val(mod));
        html_esc(b, sizeof b, signal_carrier_val(m->layers));
        html_esc(c, sizeof c, signal_carrier_val(m->grants));
        html_esc(d, sizeof d, signal_carrier_val(m->rb));
        html_esc(e, sizeof e, signal_carrier_val(m->bler));
        snprintf(dst, cap,
                 "<div class='cx'><span>MCS %s</span><span>L %s</span>"
                 "<span>G %s</span><span>RB %s</span><span>BLER %s</span></div>",
                 a, b, c, d, e);
    }
    if (signal_value_present(m->ml1_rsrp) ||
        signal_value_present(m->ml1_rsrq) ||
        signal_value_present(m->ml1_sinr)) {
        html_esc(a, sizeof a, signal_carrier_val(m->ml1_rsrp));
        html_esc(b, sizeof b, signal_carrier_val(m->ml1_rsrq));
        html_esc(c, sizeof c, signal_carrier_val(m->ml1_sinr));
        off = strlen(dst);
        snprintf(dst + off, cap - off,
                 "<div class='cx sigsrc'><span>ML1 RSRP %s</span><span>RSRQ %s</span>",
                 a, b);
        if (signal_value_present(m->ml1_sinr)) {
            off = strlen(dst);
            snprintf(dst + off, cap - off, "<span>SINR %s</span>", c);
        }
        off = strlen(dst);
        snprintf(dst + off, cap - off, "</div>");
    }
}

/* Append one carrier card (band/bw + PCI, then RSRP/SINR colored by quality).
 * A carrier reporting the floor sentinel (RSRP <= -140) is "configured but not
 * active"; its values are grayed out and tagged inactive. */
static int car_row(char *buf, int o, int cap, const char *band, const char *bw,
                    const char *arfcn, const char *pci, const char *rsrp, const char *sinr,
                    int hsr_hint, const struct signal_carrier_metric *metric)
{
    const char *rsrp_show = signal_value_present(rsrp) ? rsrp : "-";
    const char *sinr_show = signal_value_present(sinr) ? sinr : "-";
    int has_rsrp;
    int has_sinr;
    double rp;
    double sn;
    int inactive;
    const char *rq;
    const char *sq;
    const char *tag;
    const char *hsr = hsr_hint ? "<span class='chsr'>高铁专网</span>" : "";
    int is_nr_metric = band && band[0] == 'n';
    const char *al = is_nr_metric ? "ARFCN" : "EARFCN";
    char bw_text[20];
    char extra[768];

    has_rsrp = signal_value_present(rsrp_show);
    has_sinr = signal_value_present(sinr_show);
    rp = has_rsrp ? atof(rsrp_show) : -150.0;
    sn = has_sinr ? atof(sinr_show) : -99.0;
    inactive = has_rsrp && rp <= -140.0;
    rq = !has_rsrp || inactive ? "q-off" : rp >= -85 ? "q-good" : rp >= -105 ? "q-mid" : "q-bad";
    sq = !has_sinr || inactive ? "q-off" : sn >= 13  ? "q-good" : sn >= 0    ? "q-mid" : "q-bad";
    tag = inactive ? "<span class='coff'>未激活</span>" : "";
    carrier_metric_html(extra, sizeof extra, metric, is_nr_metric);
    if (signal_value_present(bw))
        snprintf(bw_text, sizeof bw_text, "%sM", bw);
    else
        snprintf(bw_text, sizeof bw_text, "-");
    if (o >= cap - 1) return o;   /* 截断后 cap-o 变负会转成巨大的 size_t，直接越界写 */
    int n = snprintf(buf + o, cap - o,
        "<div class='ccd%s%s'><span class='cb'>%s</span><span class='cbw'> %s</span>%s%s"
        "<span class='cinfo'><span class='carfcn'>%s %s</span><span class='cpci'>PCI %s</span></span>"
        "<div class='cm'><span class='ml'>RSRP</span><span class='%s'>%s</span>"
        "<span class='ml ml2'>SINR</span><span class='%s'>%s</span></div>%s</div>",
        inactive ? " off" : "", hsr_hint ? " hsrhint" : "",
        band, bw_text, tag, hsr,
        al, (arfcn && arfcn[0]) ? arfcn : "-", (pci && pci[0]) ? pci : "-",
        rq, rsrp_show, sq, sinr_show,
        extra);
    return n < 0 ? o : (o + n >= cap ? cap - 1 : o + n);
}

static int carrier_is_inactive(const char *rsrp)
{
    return atof((rsrp && rsrp[0]) ? rsrp : "") <= -140.0;
}

/* Split a CA group "f0,f1,..." into fields[] (returns count). */
static int ca_split(char *g, char **f, int maxf)
{
    int n = 0; char *save;
    for (char *tk = strtok_r(g, ",", &save); tk && n < maxf; tk = strtok_r(NULL, ",", &save)) f[n++] = tk;
    return n;
}

static int ca_groups(char *s, char **g, int maxg)
{
    int n = 0; char *save;
    for (char *tk = strtok_r(s, ";", &save); tk && n < maxg; tk = strtok_r(NULL, ";", &save)) g[n++] = tk;
    return n;
}

/* LTE SCC signal is sometimes exposed separately from legacy 5-field lteca.
 * We accept both full 11-field groups and shorter signal-only groups by
 * locating the first "RSRP-like" value (typically <= -40 dBm), then taking
 * SINR from two fields later when present. */
static int ca_sig_pick(char *g, const char **rsrp, const char **sinr)
{
    char *f[16];
    int nf = ca_split(g, f, 16), rp = -1;
    *rsrp = *sinr = NULL;
    for (int i = 0; i < nf; i++) {
        if (atof(f[i]) <= -40.0) { rp = i; break; }
    }
    if (rp < 0) return 0;
    *rsrp = f[rp];
    if (rp + 2 < nf)      *sinr = f[rp + 2];
    else if (rp + 1 < nf) *sinr = f[rp + 1];
    return 1;
}

static int signal_level(int rsrp)
{
    int lvl;
    if      (rsrp == 0)    lvl = 0;   /* unknown / no signal */
    else if (rsrp >= -80)  lvl = 5;
    else if (rsrp >= -90)  lvl = 4;
    else if (rsrp >= -100) lvl = 3;
    else if (rsrp >= -110) lvl = 2;
    else                   lvl = 1;
    return lvl;
}

/* ---- rolling history for the charts page (sampled once per second) ---- */
#define HIST 48
static int    h_n;
static int    h_cpu[HIST], h_mem[HIST], h_ct[HIST], h_bt[HIST], h_pwr[HIST];
static long   h_rx[HIST], h_tx[HIST];
static time_t h_last;

/* charge (charger input) or discharge (battery) power, in milliwatts. */
/* Battery power in milliwatts (use battery_voltage * |battery_current|). */
static int power_mw(const devui_data_t *d)
{
    double w = (d->bat_uv / 1e6) * (labs(d->bat_ua) / 1e6);
    return (int)(w * 1000);
}

static void hist_push(const devui_data_t *d)
{
    if (h_n < HIST) h_n++;
    else {
        memmove(h_cpu, h_cpu + 1, (HIST - 1) * sizeof h_cpu[0]);
        memmove(h_mem, h_mem + 1, (HIST - 1) * sizeof h_mem[0]);
        memmove(h_ct,  h_ct + 1,  (HIST - 1) * sizeof h_ct[0]);
        memmove(h_bt,  h_bt + 1,  (HIST - 1) * sizeof h_bt[0]);
        memmove(h_pwr, h_pwr + 1, (HIST - 1) * sizeof h_pwr[0]);
        memmove(h_rx,  h_rx + 1,  (HIST - 1) * sizeof h_rx[0]);
        memmove(h_tx,  h_tx + 1,  (HIST - 1) * sizeof h_tx[0]);
    }
    int i = h_n - 1;
    h_cpu[i] = d->cpu_usage < 0 ? 0 : (int)d->cpu_usage;
    h_mem[i] = d->mem_used_pct < 0 ? 0 : (int)d->mem_used_pct;
    h_ct[i]  = (int)d->cpu_temp;
    h_bt[i]  = d->bat_temp;
    h_pwr[i] = power_mw(d);
    h_rx[i]  = d->rx_speed;
    h_tx[i]  = d->tx_speed;
}

/* Draw the chart placeholders (#chart-cpu/#chart-mem/#chart-net) natively as
 * Bresenham polylines over the history. Called after the page is rendered; a
 * no-op on pages without those elements. */
/* one series, auto-scaled with some headroom, gradient area under the line */
static void chart_one(const char *sel, const int *v, int n, int floor_lo, int min_span, int r, int g, int b)
{
    int x, y, w, h;
    if (n < 2 || !html_view_rect(sel, &x, &y, &w, &h)) return;
    int lo = v[0], hi = v[0];
    for (int i = 1; i < n; i++) { if (v[i] < lo) lo = v[i]; if (v[i] > hi) hi = v[i]; }
    if (floor_lo >= 0) lo = floor_lo;
    if (hi - lo < min_span) hi = lo + min_span;
    hi += (hi - lo) / 6 + 1;
    html_view_polyline(x, y + 2, w, h - 2, v, n, lo, hi, r, g, b, 2, 110);
}

/* 首页速率图：下行面积 + 上行线，共用一个纵轴，两条线的高低可以直接比 */
static void chart_two(const char *sel, const int *a, const int *b, int n)
{
    int x, y, w, h;
    if (n < 2 || !html_view_rect(sel, &x, &y, &w, &h)) return;
    int hi = 80;
    for (int i = 0; i < n; i++) { if (a[i] > hi) hi = a[i]; if (b[i] > hi) hi = b[i]; }
    hi += hi / 6 + 1;
    html_view_polyline(x, y + 2, w, h - 2, a, n, 0, hi, 0x5b, 0x97, 0xff, 2, 110);
    html_view_polyline(x, y + 2, w, h - 2, b, n, 0, hi, 0xff, 0x9f, 0x5a, 2, 0);
}

static void draw_charts(void)
{
    static int tmp[HIST];
    chart_one("#chart-cpu", h_cpu, h_n, 0, 20, 0x5b, 0x97, 0xff);
    chart_one("#chart-mem", h_mem, h_n, 0, 100, 0x4f, 0xd0, 0x7a);
    for (int i = 0; i < h_n; i++) tmp[i] = (int)(h_rx[i] / 125);          /* kbit/s */
    chart_one("#chart-net", tmp, h_n, 0, 80, 0xa7, 0x8b, 0xfa);
    int mn = 999;
    for (int i = 0; i < h_n; i++) if (h_bt[i] < mn) mn = h_bt[i];
    chart_one("#chart-batt", h_bt, h_n, mn - 3, 6, 0xff, 0x9f, 0x5a);
    /* speed sparklines on the cover and home page */
    for (int i = 0; i < h_n; i++) tmp[i] = (int)(h_rx[i] / 125);
    chart_one("#cvspark", tmp, h_n, 0, 80, 0x5b, 0x97, 0xff);
    static int tmp2[HIST];
    for (int i = 0; i < h_n; i++) tmp2[i] = (int)(h_tx[i] / 125);
    chart_two("#spk-both", tmp, tmp2, h_n);
}

/* Padlock glyph centered in the lower screen, shown on the locked preview
 * (state 1). Drawn natively so it does not depend on font glyph coverage. */
__attribute__((unused)) static void draw_lock_icon(void)
{
    const int cx = 160, cy = 406;          /* icon center, lower-middle */
    int dark = !g_theme;
    int lv = dark ? 0xff : 0x00;           /* lock color: white(dark) / black(light) */
    /* shackle: arch ring (semicircle + short legs); legs end inside the body */
    {
        int xs[40], ys[40], n = 0;
        const int ro = 7, ri = 5, arc_cy = cy - 2, leg = cy + 3;
        xs[n] = cx - ro; ys[n] = leg; n++;
        for (int aa = 180; aa >= 0; aa -= 30) { double r = aa * 3.14159265 / 180; xs[n] = cx + (int)(ro * cos(r)); ys[n] = arc_cy - (int)(ro * sin(r)); n++; }
        xs[n] = cx + ro; ys[n] = leg; n++;
        xs[n] = cx + ri; ys[n] = leg; n++;
        for (int aa = 0; aa <= 180; aa += 30) { double r = aa * 3.14159265 / 180; xs[n] = cx + (int)(ri * cos(r)); ys[n] = arc_cy - (int)(ri * sin(r)); n++; }
        xs[n] = cx - ri; ys[n] = leg; n++;
        html_view_fill_poly(xs, ys, n, lv, lv, lv, 255);
    }
    /* body + keyhole (keyhole in page bg tone to look punched through) */
    html_view_fill_round_rect(cx - 10, cy + 1, 20, 15, 4, lv, lv, lv, 255);
    html_view_fill_round_rect(cx - 2, cy + 6, 4, 4, 2,
                              dark ? 0x15 : 0xec, dark ? 0x16 : 0xee, dark ? 0x1a : 0xf1, 255);
}

/* SMS detail dialog + status-bar envelope state. */
static long g_sms_open = -1;   /* opened SMS message id for detail dialog (-1 = none) */
static int  g_sms_idx = -1;    /* 短信详情页: index into the list snapshot (same order as the list) */
static int  g_sms_unread_now;  /* unread SMS present -> draw the status-bar envelope */
static char g_sms_num[40], g_sms_date[16], g_sms_text[DEVUI_SMS_TEXT_MAX];   /* opened message */
static int  g_sms_scroll, g_sms_scroll_max;
static int  g_sms_view_x, g_sms_view_y, g_sms_view_w, g_sms_view_h;

/* Closing an SMS removes its overlay before the next input pass.  Discard every
 * latched gesture, rather than one queue entry, so an older release cannot be
 * replayed against the SMS card exposed underneath. */
static void sms_close(touch_input_t *touch, int *need_render)
{
    g_sms_open = -1;
    g_sms_scroll = g_sms_scroll_max = 0;
    touch_input_clear_taps(touch);
    *need_render = 1;
}

/* Draw a small envelope in the fixed status bar, just right of the clock, when
 * there are unread messages. Native shape; the font has no envelope glyph. */
static void draw_sms_icon(void)
{
    if (!g_sms_unread_now) return;
    const int ew = 16, eh = 11;
    if (g_lock_state == 1 || g_lock_state == 4) return;
    html_view_native_num(1);
    int ex = 12 + html_view_text_width_px(g_stat_time, 17) + 6;
    html_view_native_num(0);
    int ey = (26 - eh) / 2;
    /* body: blue rounded rectangle */
    html_view_fill_round_rect(ex, ey, ew, eh, 2, 0x2f, 0x6f, 0xe0, 255);
    /* flap: white inverted-V from the two top corners down to center */
    int xs[3] = { ex + 1, ex + ew - 1, ex + ew / 2 };
    int ys[3] = { ey + 1, ey + 1,      ey + eh / 2 + 1 };
    html_view_fill_poly(xs, ys, 3, 0xff, 0xff, 0xff, 255);
}

/* ---- band lock (éé¢): comma-list band sets ---- */
extern void html_view_stroke_round_rect(int x, int y, int w, int h, int rad, int t, int r, int g, int b, int a);

/* ---- native vector icons (anti-aliased), all in a 10x10 design box ---- */
struct rgb { int r, g, b; };
/* power-source glyph drawn over the battery body */
/* Anti-aliased polygon fill: 4x4 supersampled even-odd coverage per pixel. Only used
 * for tiny glyphs (a dozen pixels square), so the brute force is cheap. */
static void aa_poly_f(const float *xs, const float *ys, int n, struct rgb c, int a)
{
    float x0 = xs[0], x1 = xs[0], y0 = ys[0], y1 = ys[0];
    for (int i = 1; i < n; i++) {
        if (xs[i] < x0) x0 = xs[i]; if (xs[i] > x1) x1 = xs[i];
        if (ys[i] < y0) y0 = ys[i]; if (ys[i] > y1) y1 = ys[i];
    }
    for (int py = (int)floorf(y0); py <= (int)ceilf(y1); py++)
        for (int px = (int)floorf(x0); px <= (int)ceilf(x1); px++) {
            int hit = 0;
            for (int sy = 0; sy < 4; sy++)
                for (int sx = 0; sx < 4; sx++) {
                    float tx = px + (sx + 0.5f) / 4, ty = py + (sy + 0.5f) / 4;
                    int in = 0;
                    for (int i = 0, j = n - 1; i < n; j = i++)
                        if ((ys[i] > ty) != (ys[j] > ty) &&
                            tx < (xs[j] - xs[i]) * (ty - ys[i]) / (ys[j] - ys[i]) + xs[i]) in = !in;
                    hit += in;
                }
            if (hit) html_view_fill_rect(px, py, 1, 1, c.r, c.g, c.b, a * hit / 16);
        }
}

/* Battery glyphs, drawn in a 12x12 design box (ox,oy, scale s) with a knockout ring
 * in the bar colour so they stay crisp over the level fill: bolt = charging,
 * plug = direct supply (powered, battery idle), arrow = powering the peer. */
static void batt_glyph(int state, float ox, float oy, float s, struct rgb fg, struct rgb bg)
{
    #define GX(v) (ox + (v) * s)
    #define GY(v) (oy + (v) * s)
    const float ko = 1.3f * s;                          /* knockout ring width */
    if (state == PWR_CHG || state == PWR_FAST || state == PWR_PC) {
        static const float bx[6] = { 7.6f, 2.6f, 5.8f, 4.6f, 9.4f, 6.2f }, by[6] = { 0.4f, 6.8f, 6.8f, 11.6f, 5.0f, 5.0f };
        float xs[6], ys[6];
        for (int i = 0; i < 6; i++) { xs[i] = GX(bx[i]); ys[i] = GY(by[i]); }
        for (int i = 0, j = 5; i < 6; j = i++)
            html_view_aa_line(xs[j], ys[j], xs[i], ys[i], ko, bg.r, bg.g, bg.b, 255);
        aa_poly_f(xs, ys, 6, fg, 255);
    } else if (state == PWR_DIRECT) {                   /* plug: two prongs, solid head, short cord */
        static const float hx[6] = { 3.2f, 8.8f, 8.8f, 7.2f, 4.8f, 3.2f }, hy[6] = { 4.4f, 4.4f, 6.4f, 8.2f, 8.2f, 6.4f };
        float xs[6], ys[6];
        for (int i = 0; i < 6; i++) { xs[i] = GX(hx[i]); ys[i] = GY(hy[i]); }
        html_view_aa_line(GX(4.9f), GY(2.0f), GX(4.9f), GY(4.4f), 1.3f * s + 2 * ko, bg.r, bg.g, bg.b, 255);
        html_view_aa_line(GX(7.1f), GY(2.0f), GX(7.1f), GY(4.4f), 1.3f * s + 2 * ko, bg.r, bg.g, bg.b, 255);
        html_view_aa_line(GX(6.0f), GY(8.2f), GX(6.0f), GY(10.0f), 1.5f * s + 2 * ko, bg.r, bg.g, bg.b, 255);
        for (int i = 0, j = 5; i < 6; j = i++)
            html_view_aa_line(xs[j], ys[j], xs[i], ys[i], 2 * ko, bg.r, bg.g, bg.b, 255);
        html_view_aa_line(GX(4.9f), GY(2.0f), GX(4.9f), GY(4.6f), 1.3f * s, fg.r, fg.g, fg.b, 255);
        html_view_aa_line(GX(7.1f), GY(2.0f), GX(7.1f), GY(4.6f), 1.3f * s, fg.r, fg.g, fg.b, 255);
        html_view_aa_line(GX(6.0f), GY(8.0f), GX(6.0f), GY(10.0f), 1.5f * s, fg.r, fg.g, fg.b, 255);
        aa_poly_f(xs, ys, 6, fg, 255);
    } else if (state == PWR_OUT) {                      /* arrow pointing out of the battery */
        static const float seg[3][4] = { { 2.4f, 6.0f, 9.0f, 6.0f }, { 6.2f, 2.8f, 9.4f, 6.0f }, { 9.4f, 6.0f, 6.2f, 9.2f } };
        for (int i = 0; i < 3; i++)
            html_view_aa_line(GX(seg[i][0]), GY(seg[i][1]), GX(seg[i][2]), GY(seg[i][3]), 1.7f * s + 2 * ko, bg.r, bg.g, bg.b, 255);
        for (int i = 0; i < 3; i++)
            html_view_aa_line(GX(seg[i][0]), GY(seg[i][1]), GX(seg[i][2]), GY(seg[i][3]), 1.7f * s, fg.r, fg.g, fg.b, 255);
    }
    #undef GX
    #undef GY
}

/* Battery (iPhone-style): faint outline + short round tip, a full-bleed level fill whose
 * colour says where the power flows (green in, cyan direct supply, amber out, red low),
 * and one centred glyph. Everything is anti-aliased. */
static void draw_batt(int x, int y, int w, int h, int pct, int state, int low, struct rgb fg)
{
    const int dark = !g_theme;
    struct rgb bg = dark ? (struct rgb){ 0x10, 0x16, 0x22 } : (struct rgb){ 0xe9, 0xed, 0xf2 };
    struct rgb fill = fg;
    if (state == PWR_CHG || state == PWR_FAST || state == PWR_PC || state == PWR_FULL) fill = (struct rgb){ 0x4f, 0xd0, 0x7a };
    else if (state == PWR_DIRECT) fill = (struct rgb){ 0x1f, 0xd1, 0xd6 };
    else if (state == PWR_OUT) fill = (struct rgb){ 0xf0, 0xb8, 0x4a };
    else if (low) fill = (struct rgb){ 0xff, 0x6a, 0x52 };
    float s = h / 12.0f;
    int rad = (int)lroundf(h * 0.3f);
    html_view_stroke_round_rect(x, y, w, h, rad, 1, fg.r, fg.g, fg.b, 115);
    {                                                        /* tip: short rounded bar */
        float tx = x + w + 1.2f * s, cy = y + h / 2.0f, hh = 1.6f * s;
        html_view_aa_line(tx, cy - hh, tx, cy + hh, 1.4f * s, fg.r, fg.g, fg.b, 115);
    }
    int pad = h >= 14 ? 3 : 2;
    int fw = (w - 2 * pad) * clampi(pct, 0, 100) / 100;
    if (fw < 2 && pct > 0) fw = 2;
    if (fw > 0) html_view_fill_round_rect(x + pad, y + pad, fw, h - 2 * pad, h >= 14 ? 3 : 2, fill.r, fill.g, fill.b, 255);
    if (state != PWR_BATT && state != PWR_FULL)
        batt_glyph(state, x + w / 2.0f - 6 * s, y + h / 2.0f - 6 * s, s, fg, bg);
}

/* 高铁 (HST, detected by the baseband) and roaming, from the stock nwinfo config the
 * stock daemon keeps current. Plain file read every 5 s while lit: no forks. */
static int g_hst, g_roam;
static void hstroam_refresh(void)
{
    static uint32_t at;
    uint32_t now = millis();
    if (at && now - at < 5000) return;
    at = now ? now : 1;
    char *f = read_file("/etc/config/zte_nwinfo");
    if (!f) return;
    const char *h = strstr(f, "option hst_info '"), *r = strstr(f, "option simcard_roam '");
    g_hst = h && h[17] != '0' && h[17] != '\'';
    g_roam = r && strncmp(r + 21, "Home", 4) && r[21] != '\'';
    free(f);
}

/* cubic bezier samples appended to a polygon (design units) */
static int bez(float *xs, float *ys, int n, float x0, float y0, float x1, float y1, float x2, float y2, float x3, float y3)
{
    for (int k = 1; k <= 6; k++) {
        float t = k / 6.0f, u = 1 - t;
        xs[n] = u*u*u*x0 + 3*u*u*t*x1 + 3*u*t*t*x2 + t*t*t*x3;
        ys[n] = u*u*u*y0 + 3*u*u*t*y1 + 3*u*t*t*y2 + t*t*t*y3;
        n++;
    }
    return n;
}

/* status-bar icon, 高铁 (design B: streamlined side view), 16x16 design box at ox,oy */
static void icon_train(float ox, float oy, float s, struct rgb c, struct rgb bg)
{
    float xs[40], ys[40]; int n = 0;
    xs[n] = 2.5f; ys[n++] = 12; xs[n] = 13.2f; ys[n++] = 12;
    n = bez(xs, ys, n, 13.2f, 12, 14.5f, 12, 15.3f, 11.2f, 15.3f, 10.2f);
    n = bez(xs, ys, n, 15.3f, 10.2f, 15.3f, 8.4f, 12.2f, 5, 7.6f, 5);
    xs[n] = 2.5f; ys[n++] = 5;
    for (int i = 0; i < n; i++) { xs[i] = ox + xs[i] * s; ys[i] = oy + ys[i] * s; }
    aa_poly_f(xs, ys, n, c, 255);
    float wx[20], wy[20]; int m = 0;                       /* nose window */
    wx[m] = 7.2f; wy[m++] = 6.6f; wx[m] = 9.6f; wy[m++] = 6.6f;
    m = bez(wx, wy, m, 9.6f, 6.6f, 11, 6.6f, 12.3f, 7.3f, 13, 8.1f);
    wx[m] = 7.2f; wy[m++] = 8.1f;
    for (int i = 0; i < m; i++) { wx[i] = ox + wx[i] * s; wy[i] = oy + wy[i] * s; }
    aa_poly_f(wx, wy, m, bg, 255);
    float rx[4] = { ox + 3.6f * s, ox + 6 * s, ox + 6 * s, ox + 3.6f * s }, ry[4] = { oy + 6.6f * s, oy + 6.6f * s, oy + 8.1f * s, oy + 8.1f * s };
    aa_poly_f(rx, ry, 4, bg, 255);                         /* cabin window */
    html_view_aa_line(ox + 2.5f * s, oy + 13.8f * s, ox + 15 * s, oy + 13.8f * s, 1.2f * s, c.r, c.g, c.b, 255);    /* rail */
    html_view_aa_line(ox + 0.4f * s, oy + 7.2f * s, ox + 1.6f * s, oy + 7.2f * s, 1.1f * s, c.r, c.g, c.b, 180);    /* speed lines */
    html_view_aa_line(ox + 0.4f * s, oy + 9.6f * s, ox + 1.6f * s, oy + 9.6f * s, 1.1f * s, c.r, c.g, c.b, 180);
}

/* status-bar icon, 漫游 (design B: globe + arrow) */
static void icon_roam(float ox, float oy, float s, struct rgb c)
{
    float cx = ox + 8 * s, cy = oy + 8 * s, r = 5.4f * s;
    for (int k = 0; k < 48; k++) {                         /* outline + meridian ellipse */
        float a0 = k * 2 * (float)M_PI / 48, a1 = (k + 1) * 2 * (float)M_PI / 48;
        /* at 14 px the inner lines must stay thin or the globe turns into a blob */
        html_view_aa_line(cx + r * cosf(a0), cy + r * sinf(a0), cx + r * cosf(a1), cy + r * sinf(a1), 1.3f * s, c.r, c.g, c.b, 255);
        html_view_aa_line(cx + 2.2f * s * cosf(a0), cy + r * sinf(a0), cx + 2.2f * s * cosf(a1), cy + r * sinf(a1), 0.8f * s, c.r, c.g, c.b, 210);
    }
    html_view_aa_line(ox + 2.8f * s, cy, ox + 13.2f * s, cy, 0.8f * s, c.r, c.g, c.b, 210);
    html_view_aa_line(ox + 11.9f * s, oy + 1.4f * s, ox + 15.0f * s, oy + 1.6f * s, 1.5f * s, c.r, c.g, c.b, 255);
    html_view_aa_line(ox + 15.0f * s, oy + 1.6f * s, ox + 14.7f * s, oy + 4.8f * s, 1.5f * s, c.r, c.g, c.b, 255);
}

static void draw_native_statusbar(void)
{
    const int dark = !g_theme;
    struct rgb fg = dark ? (struct rgb){ 0xf1, 0xf3, 0xf6 } : (struct rgb){ 0x14, 0x18, 0x20 };
    const int dim_a = dark ? 60 : 45;

    if (html_view_has_wallpaper())
        html_view_paint_wallpaper(0, 0, 320, 26, dark ? 0 : 0xff, dark ? 0 : 0xff, dark ? 0 : 0xff, dark ? 40 : 70);
    else
        html_view_fill_rect(0, 0, 320, 26, dark ? 0x0c : 0xe9, dark ? 0x0e : 0xed, dark ? 0x12 : 0xf2, 255);

    html_view_native_num(1);
    if (g_lock_state != 1 && g_lock_state != 4)          /* the cover shows a big clock instead */
        html_view_draw_text_px(12, 3, g_stat_time, 17, 0, fg.r, fg.g, fg.b, 255);

    const int bat_w = 23, bat_h = 12, bat_x = 320 - 12 - 3 - bat_w, bat_y = (26 - bat_h) / 2;
    int bat_pct = clampi(g_stat_bat, 0, 100);
    draw_batt(bat_x, bat_y, bat_w, bat_h, bat_pct, g_pwr.state, g_stat_lowbat, fg);
    int right = bat_x - 6;
    if (g_show_batpct) {
        char bp[8]; snprintf(bp, sizeof bp, "%d%%", bat_pct);
        int w = html_view_text_width_px(bp, 14);
        html_view_draw_text_px(right - w, 5, bp, 14, 0, fg.r, fg.g, fg.b, 255);
        right -= w + 7;
    } else right -= 2;
    hstroam_refresh();
    const int icw = 14;                                   /* 16-unit design box drawn 14 px tall */
    const float ics = icw / 16.0f;
    if (g_roam) {                                         /* globe sits between the bars and the battery */
        icon_roam(right - icw, (26 - icw) / 2.0f, ics, (struct rgb){ 0xf0, 0xb8, 0x4a });
        right -= icw + 5;
    }

    const int bw = 3, gap = 2, nb = 5, base = bat_y + bat_h;
    int bars_x = right - (nb * bw + (nb - 1) * gap);
    for (int i = 0; i < nb; i++) {
        int bh = 3 + i * 2;
        html_view_fill_round_rect(bars_x + i * (bw + gap), base - bh, bw, bh, 1,
                                  fg.r, fg.g, fg.b, i < g_stat_sig ? 255 : dim_a);
    }
    int gw = html_view_text_width_px(g_stat_gen, 14);
    int gx = bars_x - 5 - gw;
    html_view_draw_text_px(gx, 5, g_stat_gen, 14, 0, fg.r, fg.g, fg.b, 255);
    if (g_hst) {                                          /* 高铁: train before the 5G label */
        struct rgb bgc = dark ? (struct rgb){ 0x0f, 0x2c, 0x3f } : (struct rgb){ 0xe9, 0xed, 0xf2 };
        gx -= icw + 5;
        icon_train(gx, (26 - icw) / 2.0f, ics, (struct rgb){ 0x1f, 0xd1, 0xd6 }, bgc);
    }

    /* speeds on one line, each with its own unit: "↑116 Kbps ↓4.6 Mbps";
     * compact "↑116K ↓4.6M" when that doesn't fit */
    int minx = (g_lock_state == 1 || g_lock_state == 4) ? 10 : 64;
    const char *sp = g_stat_speed;
    char alt[40];
    int sw = html_view_text_width_px(sp, 14);
    if (gx - 8 - sw < minx) {
        snprintf(alt, sizeof alt, "%s %s", g_stat_up, g_stat_dn);
        sp = alt; sw = html_view_text_width_px(sp, 14);
    }
    int sx = gx - 8 - sw;
    if (sx >= minx) html_view_draw_text_px(sx, 5, sp, 14, 0, fg.r, fg.g, fg.b, 255);
    html_view_native_num(0);
}

static void ic_arc(float cx, float cy, float rad, float a0, float a1, float wd, struct rgb c)
{
    /* angles in degrees, clockwise from 12 o'clock */
    float step = 12, px = 0, py = 0;
    for (float t = a0; ; t += step) {
        if (t > a1) t = a1;
        float rr = t * 3.14159265f / 180;
        float x = cx + rad * sinf(rr), y = cy - rad * cosf(rr);
        if (t > a0) html_view_aa_line(px, py, x, y, wd, c.r, c.g, c.b, 255);
        px = x; py = y;
        if (t >= a1) break;
    }
}

/* Native icons into their placeholders: back chevron, header bolt, cover
 * swipe chevron, battery on the home card, power sheet glyphs. */
static void pm_glyph(const char *sel, int kind, int cr, int cg, int cb);   /* power-sheet glyphs, reused */
static void draw_icons(void)
{
    int x, y, w, h;
    const int dark = !g_theme;
    struct rgb ac = dark ? (struct rgb){ 0x8f, 0xb6, 0xff } : (struct rgb){ 0x2f, 0x6f, 0xe0 };
    struct rgb fg = dark ? (struct rgb){ 0xf1, 0xf3, 0xf6 } : (struct rgb){ 0x14, 0x18, 0x20 };
    struct rgb mu = dark ? (struct rgb){ 0xc8, 0xce, 0xd7 } : (struct rgb){ 0x3a, 0x43, 0x50 };
    pm_glyph("#pwrb", 0, 0xb8, 0x3c, 0x30);          /* 控制中心 title: power button -> act:menu */
    if (html_view_rect("#bk", &x, &y, &w, &h)) {
        float cx = x + w / 2.0f - 1, cy = y + h / 2.0f;
        html_view_aa_line(cx + 2.8f, cy - 6, cx - 3.2f, cy, 2.2f, ac.r, ac.g, ac.b, 255);
        html_view_aa_line(cx - 3.2f, cy, cx + 2.8f, cy + 6, 2.2f, ac.r, ac.g, ac.b, 255);
    }
    if (html_view_rect("#hup", &x, &y, &w, &h)) {
        float cx = x + w / 2.0f, cy = y + h / 2.0f + 1;
        html_view_aa_line(cx - 4.5f, cy + 2, cx, cy - 2.5f, 1.8f, fg.r, fg.g, fg.b, 255);
        html_view_aa_line(cx, cy - 2.5f, cx + 4.5f, cy + 2, 1.8f, fg.r, fg.g, fg.b, 255);
    }
    for (int k = 0; k < NWALLS - 1; k++) {               /* wallpaper swatches: real thumbnails */
        char sel[32], pth[160];
        snprintf(sel, sizeof sel, "#wpt-%s", g_walls[k]);
        if (!html_view_rect(sel, &x, &y, &w, &h)) continue;
        snprintf(pth, sizeof pth, "%s/%s.png", WALL_DIR, g_walls[k]);
        int on = !strcmp(g_walls[k], g_wallname);
        int in = on ? 3 : 0;                               /* keep the selection ring visible */
        html_view_draw_thumb(pth, x + in, y + in, w - 2 * in, h - 2 * in, on ? 7 : 10);
        int light = !strcmp(g_walls[k], "mist");
        int tw = html_view_text_width_px(g_wall_labels[k], 11);
        html_view_draw_text_px(x + (w - tw) / 2, y + h - 18, g_wall_labels[k], 11, 0,
                               light ? 0x1e : 0xf1, light ? 0x2a : 0xf3, light ? 0x3a : 0xf6, 255);
    }
    static const char *chevs[] = { "#chev", "#chev2", "#chev3", "#chev4", "#chev5", "#chev6" };
    for (int k = 0; k < 6; k++)                         /* entry-row chevrons */
        if (html_view_rect(chevs[k], &x, &y, &w, &h)) {
            float cx = x + w / 2.0f, cy = y + h / 2.0f;
            html_view_aa_line(cx - 2.5f, cy - 5.5f, cx + 2.5f, cy, 2, mu.r, mu.g, mu.b, 255);
            html_view_aa_line(cx + 2.5f, cy, cx - 2.5f, cy + 5.5f, 2, mu.r, mu.g, mu.b, 255);
        }
    if (html_view_rect(".bigbar", &x, &y, &w, &h)) {    /* screen page: sun glyph + thumb on the big bar */
        int m = backlight_max(); if (m <= 0) m = 255;
        int pct = clampi(backlight_get() * 100 / m, 0, 100);
        /* fill: gradient from deep amber to a level-dependent end colour
         * (dim amber at low brightness, bright gold at full) */
        {
            const int r0 = 0x6e, g0 = 0x4c, b0 = 0x16;
            int r1 = 0x9a + (0xff - 0x9a) * pct / 100, g1 = 0x70 + (0xd4 - 0x70) * pct / 100, b1 = 0x22 + (0x5c - 0x22) * pct / 100;
            int fw = w * pct / 100, rad = 16;
            for (int c = 0; c < fw; c++) {
                int inset = 0;
                int dl = c, dr = w - 1 - c;                    /* rounded ends of the bar */
                int dd = dl < rad ? dl : (dr < rad ? dr : rad);
                if (dd < rad) { float q = rad - dd - 0.5f; inset = (int)(rad - sqrtf(rad * rad - q * q) + 0.5f); }
                int rr = r0 + (r1 - r0) * c / (fw > 1 ? fw - 1 : 1);
                int gg = g0 + (g1 - g0) * c / (fw > 1 ? fw - 1 : 1);
                int bb = b0 + (b1 - b0) * c / (fw > 1 ? fw - 1 : 1);
                html_view_fill_rect(x + c, y + inset, 1, h - 2 * inset, rr, gg, bb, 255);
            }
        }
        float cx = x + 22, cy = y + h / 2.0f;
        html_view_aa_disc(cx, cy, 4.6f, 0xff, 0xff, 0xff, 255);
        for (int k = 0; k < 8; k++) {
            float r = k * 3.14159265f / 4;
            html_view_aa_line(cx + 7.5f * sinf(r), cy - 7.5f * cosf(r), cx + 10 * sinf(r), cy - 10 * cosf(r), 1.8f, 0xff, 0xff, 0xff, 255);
        }
        int tx = x + w * pct / 100 - 7;
        if (tx < x + 38) tx = x + 38;
        if (tx > x + w - 10) tx = x + w - 10;
        html_view_fill_round_rect(tx, y + 12, 4, h - 24, 2, 0xff, 0xff, 0xff, 255);
    }
    if (html_view_rect("#eye", &x, &y, &w, &h)) {    /* open eye = tap to show, slashed = tap to hide */
        float cx = x + w / 2.0f, cy = y + h / 2.0f;
        ic_arc(cx, cy + 5.5f, 9, -52, 52, 1.6f, mu);                 /* upper lid */
        ic_arc(cx, cy - 5.5f, 9, 128, 232, 1.6f, mu);                /* lower lid */
        html_view_aa_disc(cx, cy, 2.6f, mu.r, mu.g, mu.b, 255);
        if (g_show_imei) html_view_aa_line(cx - 7, cy + 6, cx + 7, cy - 6, 1.6f, mu.r, mu.g, mu.b, 255);
    }
    if (html_view_rect("#batic", &x, &y, &w, &h))
        draw_batt(x, y + (h - 14) / 2, w - 4, 14, g_stat_bat, g_pwr.state, g_stat_lowbat, fg);
    if (html_view_rect("#pmi-off", &x, &y, &w, &h)) {
        float cx = x + w / 2.0f, cy = y + h / 2.0f + 1;
        struct rgb c = { 0xff, 0x6a, 0x52 };
        ic_arc(cx, cy, 9, 40, 320, 2.6f, c);
        html_view_aa_line(cx, cy - 12, cx, cy - 2, 2.6f, c.r, c.g, c.b, 255);
    }
    if (html_view_rect("#pmi-reb", &x, &y, &w, &h)) {
        float cx = x + w / 2.0f, cy = y + h / 2.0f + 1;
        struct rgb c = { 0xf0, 0xc2, 0x50 };
        ic_arc(cx, cy, 9, 50, 350, 2.6f, c);
        float ex = cx + 9 * sinf(350 * 3.14159265f / 180), ey = cy - 9 * cosf(350 * 3.14159265f / 180);
        html_view_aa_line(ex, ey, ex + 5, ey - 1.5f, 2.6f, c.r, c.g, c.b, 255);
        html_view_aa_line(ex, ey, ex + 1.2f, ey + 5, 2.6f, c.r, c.g, c.b, 255);
    }
    if (html_view_rect("#pmi-x", &x, &y, &w, &h)) {
        float cx = x + w / 2.0f, cy = y + h / 2.0f;
        html_view_aa_line(cx - 7, cy - 7, cx + 7, cy + 7, 2.6f, mu.r, mu.g, mu.b, 255);
        html_view_aa_line(cx + 7, cy - 7, cx - 7, cy + 7, 2.6f, mu.r, mu.g, mu.b, 255);
    }
}

static void draw_center_text_px(int cx, int y, const char *text, int size, int bold,
                                int r, int g, int b, int a)
{
    int x0, y0, x1, y1;
    html_view_text_bounds_px(text, size, &x0, &y0, &x1, &y1);
    html_view_draw_text_px(cx - (x1 - x0) / 2 - x0, y - y0, text, size, bold, r, g, b, a);
}

struct charge_boot_state {
    int pct;
    int charger;
    int charging;
    int full;
    long chg_uv;
    long chg_ua;
};

static void charge_boot_refresh(struct charge_boot_state *s)
{
    static devui_data_t d;
    char st[32];
    long v;
    memset(s, 0, sizeof *s);
    s->pct = -1;

    if (data_refresh(&d)) {
        s->pct = d.bat_percent;
        s->charger = d.charger_connect ? 1 : 0;
        s->charging = (d.charger_connect || d.charging) ? 1 : 0;
        s->chg_uv = d.chg_uv;
        s->chg_ua = d.chg_ua;
    }
    if (s->pct < 0 && read_long_path("/sys/class/power_supply/battery/capacity", &v))
        s->pct = (int)v;
    if (read_line_path("/sys/class/power_supply/battery/status", st, sizeof st)) {
        if (!strcmp(st, "Full")) s->full = 1;
        if (!strcmp(st, "Charging")) s->charging = 1;
    }
    if (!s->charger && read_long_path("/sys/class/power_supply/usb/online", &v))
        s->charger = v != 0;
    if (!s->charger && read_long_path("/sys/class/power_supply/usb/present", &v))
        s->charger = v != 0;
    if (!s->charger && (s->charging || s->full)) s->charger = 1;
    if (s->pct < 0) s->pct = 0;
    if (s->pct > 100) s->pct = 100;
}

static void render_charge_boot(drm_disp_t *disp)
{
    struct charge_boot_state s;
    const int W = disp->width, H = disp->height;
    const int bx = 54, by = 130, bw = 208, bh = 104;
    const int ix = bx + 7, iy = by + 7, iw = bw - 14, ih = bh - 14;
    const int tipw = 10, tiph = 32;
    int fill_w, pulse, fr, fg, fb;
    char pct[8], line1[32], line2[64];

    charge_boot_refresh(&s);
    g_phase++;

    html_view_fill_rect(0, 0, W, H, 0x09, 0x0d, 0x14, 255);
    html_view_fill_round_rect(-28, 36, 154, 154, 72, 0x18, 0x24, 0x38, 88);
    html_view_fill_round_rect(184, 282, 156, 156, 78, 0x0f, 0x2a, 0x22, 72);
    draw_center_text_px(W / 2, 50, "关机充电", 20, 0, 0xd9, 0xdf, 0xea, 255);

    html_view_fill_round_rect(bx, by, bw, bh, 26, 0xd9, 0xdf, 0xea, 255);
    html_view_fill_round_rect(bx + 3, by + 3, bw - 6, bh - 6, 23, 0x0f, 0x14, 0x1d, 255);
    html_view_fill_round_rect(bx + bw, by + (bh - tiph) / 2, tipw, tiph, 4, 0xd9, 0xdf, 0xea, 255);

    pulse = (int)(g_phase % 24);
    if (pulse > 12) pulse = 24 - pulse;
    fr = 0x5e; fg = 0xc8; fb = 0x5e;
    if (s.full) { fr = 0x58; fg = 0xb7; fb = 0xff; }
    else if (s.pct <= 20 && !s.charger) { fr = 0xe8; fg = 0x53; fb = 0x3a; }
    if (s.charger && !s.full) {
        fr = clampi(fr + pulse * 3, 0, 255);
        fg = clampi(fg + pulse * 2, 0, 255);
        fb = clampi(fb + pulse * 3 / 2, 0, 255);
    }
    fill_w = iw * s.pct / 100;
    if (fill_w <= 0 && s.charger) fill_w = 8;
    if (fill_w > 0) {
        html_view_fill_round_rect(ix, iy, fill_w, ih, 18, fr, fg, fb, 255);
        if (s.charger && !s.full && fill_w > 20) {
            int sheen = ix + ((int)(g_phase * 11) % (fill_w + 28)) - 28;
            if (sheen < ix) sheen = ix;
            if (sheen < ix + fill_w)
                html_view_fill_rect(sheen, iy + 6, 18, ih - 12, 0xff, 0xff, 0xff, 42);
        }
    }

    if (s.charger) {
        int cx = W / 2, cy = by + bh / 2;
        int xs[7] = { cx - 12, cx + 2, cx - 3, cx + 11, cx - 8, cx - 2, cx - 11 };
        int ys[7] = { cy - 30, cy - 30, cy - 6, cy - 6, cy + 30, cy + 5, cy + 5 };
        int shx[7], shy[7];
        int br = s.full ? 0xf5 : 0xff;
        int bg = s.full ? 0xfb : 0xf4;
        int bb = s.full ? 0xff : 0xa7;
        for (int i = 0; i < 7; i++) { shx[i] = xs[i] + 1; shy[i] = ys[i] + 2; }
        html_view_fill_poly(shx, shy, 7, 0x05, 0x08, 0x0c, 120);
        html_view_fill_poly(xs, ys, 7, br, bg, bb, 245);
    }

    snprintf(pct, sizeof pct, "%d%%", s.pct);
    draw_center_text_px(W / 2, 274, pct, 46, 1, 0xf5, 0xf7, 0xfa, 255);

    if (s.full) snprintf(line1, sizeof line1, "已充满");
    else if (s.charging) snprintf(line1, sizeof line1, "充电中");
    else if (s.charger) snprintf(line1, sizeof line1, "已接入电源");
    else snprintf(line1, sizeof line1, "等待充电");
    draw_center_text_px(W / 2, 330, line1, 20, 0, 0x9f, 0xd6, 0xb5, 255);

    if (s.chg_uv > 0 && s.chg_ua > 0)
        snprintf(line2, sizeof line2, "输入 %.1fV · %ldmA", s.chg_uv / 1000000.0, s.chg_ua / 1000);
    else
        snprintf(line2, sizeof line2, "按电源键可熄屏/亮屏");
    draw_center_text_px(W / 2, 364, line2, 14, 0, 0x8e, 0x98, 0xa6, 255);

    drm_disp_dirty(disp, 0, 0, W - 1, H - 1);
    maybe_dump_fb(disp);
}

static int  g_modal;           /* 0 none, 1 SA, 2 NSA, 3 LTE, 4 signal settings */
static int  g_segdrag;         /* dragging the segmented control (suppress cell highlight) */
static char g_toast[96];       /* toast message ("" = hidden) */
static uint32_t g_toast_until; /* millis the toast hides at */
static int  g_pwr_confirm;     /* power menu: 0 none, 1 poweroff armed, 2 reboot armed */
static uint32_t g_pwr_until;   /* millis the armed state auto-resets at */
static char g_net_pending[16]; /* optimistic net mode until net_select catches up */
static char g_uni_sa[256], g_uni_nsa[256], g_uni_lte[256];   /* available bands (max seen) */
static char g_sel_sa[256], g_sel_nsa[256], g_sel_lte[256];   /* selected (to lock) */

static int band_count(const char *s) { if (!s[0]) return 0; int n = 1; for (; *s; s++) if (*s == ',') n++; return n; }

static int band_in(const char *list, const char *b)
{
    size_t bl = strlen(b);
    for (const char *p = list; *p; ) {
        const char *c = p; while (*c && *c != ',') c++;
        if ((size_t)(c - p) == bl && !strncmp(p, b, bl)) return 1;
        p = *c ? c + 1 : c;
    }
    return 0;
}
static void band_toggle(char *list, size_t cap, const char *b)
{
    if (band_in(list, b)) {
        char out[256]; int o = 0; size_t bl = strlen(b);
        for (const char *p = list; *p; ) {
            const char *c = p; while (*c && *c != ',') c++;
            if (!((size_t)(c - p) == bl && !strncmp(p, b, bl))) {
                if (o) out[o++] = ',';
                int n = (int)(c - p); if (o + n < (int)sizeof out) { memcpy(out + o, p, n); o += n; }
            }
            p = *c ? c + 1 : c;
        }
        out[o] = 0; snprintf(list, cap, "%s", out);
    } else {
        size_t l = strlen(list);
        snprintf(list + l, cap - l, "%s%s", l ? "," : "", b);
    }
}
/* Render bands as pill chips (selected = highlighted) with the given classes. */
static void build_chips_cls(char *buf, size_t cap, const char *uni, const char *sel,
                            const char *act, const char *pfx, const char *on, const char *off)
{
    char u[256]; snprintf(u, sizeof u, "%s", uni);
    int o = 0;
    for (char *tk = strtok(u, ","); tk && o < (int)cap - 1; tk = strtok(NULL, ",")) {
        int n = snprintf(buf + o, cap - o, "<a href='act:%s:%s' class='%s'>%s%s</a>",
                         act, tk, band_in(sel, tk) ? on : off, pfx, tk);
        if (n < 0) break;
        o += n;
        if (o >= (int)cap) { o = (int)cap - 1; break; }   /* 频段太多时截断，不越界 */
    }
    if (o == 0) snprintf(buf, cap, "<span class='muted'>暂无可选频段</span>");
}

/* One-line summary of a card's current band selection. */
static void band_summary(char *buf, size_t cap, const char *uni, const char *sel, const char *pfx)
{
    if (!sel[0]) { snprintf(buf, cap, "未选择频段"); return; }
    if (!strcmp(uni, sel)) { snprintf(buf, cap, "全部频段（未锁定）"); return; }
    char s[256]; snprintf(s, sizeof s, "%s", sel);
    int o = 0;
    for (char *tk = strtok(s, ","); tk; tk = strtok(NULL, ","))
        o += snprintf(buf + o, cap - o, "%s%s%s", o ? " " : "已锁 ", pfx, tk);
}

/* segmented-control cells (shared with the touch handler). */
static const struct { const char *v, *lab; } g_netmodes[4] = {
    { "WL_AND_5G", "自动" }, { "Only_5G", "5G SA" },
    { "LTE_AND_5G", "5G NSA" }, { "Only_LTE", "4G" } };
static const struct { int ms; const char *lab; } g_autooffs[6] = {
    { 0, "关" }, { 30000, "30秒" }, { 60000, "1分" },
    { 120000, "2分" }, { 300000, "5分" }, { 600000, "10分" } };
static const struct { int ms; const char *lab; } g_refresh_rates[5] = {
    { 0, "停止" }, { 500, "0.5s" }, { 1000, "1s" }, { 2000, "2s" }, { 5000, "5s" } };
static int normalize_refresh_ms(int ms)
{
    switch (ms) {
    case 0:
    case 500:
    case 1000:
    case 2000:
    case 5000:
        return ms;
    default:
        return 1000;
    }
}

static int datad_set_refresh_ms(int ms)
{
    char cmd[192];

    ms = normalize_refresh_ms(ms);
    if (snprintf(cmd, sizeof cmd,
                 "/usr/bin/wget -T 2 -qO- --post-data='' 'http://%s:%d/modem/control?poll_ms=%d' >/dev/null 2>&1",
                 DATAD_HTTP_ADDR, DATAD_HTTP_PORT, ms) >= (int)sizeof cmd)
        return -1;
    return system(cmd) == 0 ? 0 : -1;
}

static int datad_set_signal_read(int on)
{
    char cmd[224];
    int active = on || g_sig_parse;

    if (snprintf(cmd, sizeof cmd,
                 "/usr/bin/wget -T 2 -qO- --post-data='' 'http://%s:%d/modem/control?ml1_raw=%d&active=%d' >/dev/null 2>&1",
                 DATAD_HTTP_ADDR, DATAD_HTTP_PORT, on ? 1 : 0, active ? 1 : 0) >= (int)sizeof cmd)
        return -1;
    return system(cmd) == 0 ? 0 : -1;
}

static int datad_set_signal_parse(int on)
{
    char cmd[256];
    int active = g_sig_read || on;

    if (snprintf(cmd, sizeof cmd,
                 "/usr/bin/wget -T 2 -qO- --post-data='' 'http://%s:%d/modem/control?lte=%d&nr=%d&active=%d' >/dev/null 2>&1",
                 DATAD_HTTP_ADDR, DATAD_HTTP_PORT, on ? 1 : 0, on ? 1 : 0, active ? 1 : 0) >= (int)sizeof cmd)
        return -1;
    return system(cmd) == 0 ? 0 : -1;
}

#define SIGNAL_CACHE_PATH "/data/plugins/u60pro-devui/signal.cache"

static int signal_cache_get(const char *key, char *dst, size_t cap)
{
    FILE *fp;
    char line[192];
    size_t key_len;
    int found = 0;

    if (!key || !dst || cap == 0)
        return 0;
    key_len = strlen(key);
    fp = fopen(SIGNAL_CACHE_PATH, "r");
    if (!fp)
        return 0;
    while (fgets(line, sizeof line, fp)) {
        char *v;
        char *e;

        if (strncmp(line, key, key_len) || line[key_len] != '=')
            continue;
        v = line + key_len + 1;
        e = v + strlen(v);
        while (e > v && (e[-1] == '\n' || e[-1] == '\r' || e[-1] == ' '))
            *--e = '\0';
        if (*v) {
            snprintf(dst, cap, "%s", v);
            found = 1;
        }
    }
    fclose(fp);
    return found;
}

static void signal_cache_put(const char *key, const char *value)
{
    FILE *in;
    FILE *out;
    char line[256];
    char old[128];
    char tmp_path[sizeof(SIGNAL_CACHE_PATH) + 8];
    size_t key_len;

    if (!key || !value || !value[0] || !strcmp(value, "-") ||
        !strcmp(value, "已关闭"))
        return;
    if (strchr(key, '=') || strchr(key, '\n') || strchr(value, '\n') ||
        strchr(value, '\r'))
        return;
    if (signal_cache_get(key, old, sizeof old) && !strcmp(old, value))
        return;
    snprintf(tmp_path, sizeof tmp_path, "%s.tmp", SIGNAL_CACHE_PATH);
    out = fopen(tmp_path, "w");
    if (!out)
        return;
    key_len = strlen(key);
    in = fopen(SIGNAL_CACHE_PATH, "r");
    if (in) {
        while (fgets(line, sizeof line, in)) {
            if (!strncmp(line, key, key_len) && line[key_len] == '=')
                continue;
            fputs(line, out);
        }
        fclose(in);
    }
    fprintf(out, "%s=%s\n", key, value);
    if (fclose(out) != 0 || rename(tmp_path, SIGNAL_CACHE_PATH) != 0)
        unlink(tmp_path);
}

struct signal_bundle {
    char cell_key[64];
    char ta[32];
    char lte_ta[32];
    char lte_rrc[128];
    char lte_nas[128];
    char lte_mcs[32];
    char lte_modulation[32];
    char lte_rb[32];
    char lte_grants[32];
    char lte_bler[32];
    char lte_pusch[96];
    char lte_pucch[96];
    char nr_ta[32];
    char nr_rrc[128];
    char nr_nas[128];
    char nr_mcs[32];
    char nr_modulation[32];
    char nr_mimo[64];
    char nr_layers[32];
    char nr_dl_rb[32];
    char nr_dl_grants[32];
    char nr_ul_rb[32];
    char nr_ul_grants[32];
    char nr_bler[32];
    char nr_pusch[96];
    char nr_pucch[96];
    char nr_ports[64];
    char nr_beam[128];
    char nr_serving_ssb[32];
    char nr_vendor[64];
    int lte_carrier_n;
    int nr_carrier_n;
    int lte_neighbor_n;
    int nr_neighbor_n;
    struct signal_carrier_metric lte_carriers[SIGNAL_MAX_CARRIERS];
    struct signal_carrier_metric nr_carriers[SIGNAL_MAX_CARRIERS];
    struct signal_neighbor_metric lte_neighbors[SIGNAL_MAX_NEIGHBORS];
    struct signal_neighbor_metric nr_neighbors[SIGNAL_MAX_NEIGHBORS];
};

static void signal_bundle_reset(struct signal_bundle *b)
{
    if (!b) return;
    snprintf(b->cell_key, sizeof b->cell_key, "-");
    snprintf(b->ta, sizeof b->ta, "-");
    snprintf(b->lte_ta, sizeof b->lte_ta, "-");
    snprintf(b->lte_rrc, sizeof b->lte_rrc, "-");
    snprintf(b->lte_nas, sizeof b->lte_nas, "-");
    snprintf(b->lte_mcs, sizeof b->lte_mcs, "-");
    snprintf(b->lte_modulation, sizeof b->lte_modulation, "-");
    snprintf(b->lte_rb, sizeof b->lte_rb, "-");
    snprintf(b->lte_grants, sizeof b->lte_grants, "-");
    snprintf(b->lte_bler, sizeof b->lte_bler, "-");
    snprintf(b->lte_pusch, sizeof b->lte_pusch, "-");
    snprintf(b->lte_pucch, sizeof b->lte_pucch, "-");
    snprintf(b->nr_ta, sizeof b->nr_ta, "-");
    snprintf(b->nr_rrc, sizeof b->nr_rrc, "-");
    snprintf(b->nr_nas, sizeof b->nr_nas, "-");
    snprintf(b->nr_mcs, sizeof b->nr_mcs, "-");
    snprintf(b->nr_modulation, sizeof b->nr_modulation, "-");
    snprintf(b->nr_mimo, sizeof b->nr_mimo, "-");
    snprintf(b->nr_layers, sizeof b->nr_layers, "-");
    snprintf(b->nr_dl_rb, sizeof b->nr_dl_rb, "-");
    snprintf(b->nr_dl_grants, sizeof b->nr_dl_grants, "-");
    snprintf(b->nr_ul_rb, sizeof b->nr_ul_rb, "-");
    snprintf(b->nr_ul_grants, sizeof b->nr_ul_grants, "-");
    snprintf(b->nr_bler, sizeof b->nr_bler, "-");
    snprintf(b->nr_pusch, sizeof b->nr_pusch, "-");
    snprintf(b->nr_pucch, sizeof b->nr_pucch, "-");
    snprintf(b->nr_ports, sizeof b->nr_ports, "-");
    snprintf(b->nr_beam, sizeof b->nr_beam, "-");
    snprintf(b->nr_serving_ssb, sizeof b->nr_serving_ssb, "-");
    snprintf(b->nr_vendor, sizeof b->nr_vendor, "-");
    b->lte_carrier_n = 0;
    b->nr_carrier_n = 0;
    b->lte_neighbor_n = 0;
    b->nr_neighbor_n = 0;
    for (int i = 0; i < SIGNAL_MAX_CARRIERS; i++) {
        signal_carrier_metric_reset(&b->lte_carriers[i]);
        signal_carrier_metric_reset(&b->nr_carriers[i]);
    }
    for (int i = 0; i < SIGNAL_MAX_NEIGHBORS; i++) {
        signal_neighbor_metric_reset(&b->lte_neighbors[i]);
        signal_neighbor_metric_reset(&b->nr_neighbors[i]);
    }
}

static int signal_value_present(const char *s)
{
    return s && s[0] && strcmp(s, "-") != 0 && strcmp(s, "已关闭") != 0;
}

static void signal_value_keep_last(char *cur, size_t cur_cap, char *sticky, size_t sticky_cap)
{
    if (!cur || cur_cap == 0 || !sticky || sticky_cap == 0)
        return;
    if (signal_value_present(cur)) {
        snprintf(sticky, sticky_cap, "%s", cur);
        return;
    }
    if (signal_value_present(sticky))
        snprintf(cur, cur_cap, "%s", sticky);
}

static void signal_metric_get(const char *obj, const char *key, char *dst, size_t cap)
{
    char tmp[128];

    if (!obj || !key || !dst || cap == 0)
        return;
    if (json_get(obj, key, tmp, sizeof tmp) && signal_value_present(tmp))
        snprintf(dst, cap, "%s", tmp);
}

static void signal_copy_value(char *dst, size_t cap, const char *src)
{
    size_t n;

    if (!dst || cap == 0)
        return;
    if (!src)
        src = "";
    n = strlen(src);
    if (n >= cap)
        n = cap - 1;
    memcpy(dst, src, n);
    dst[n] = 0;
}

static int signal_json_next_object(const char **pp, char *dst, size_t cap)
{
    const char *p;
    size_t n = 0;
    int depth = 0;
    int in_str = 0;

    if (!pp || !*pp || !dst || cap == 0)
        return 0;
    p = *pp;
    while (*p && *p != '{')
        p++;
    if (*p != '{')
        return 0;
    while (*p && n < cap - 1) {
        char ch = *p;
        if (in_str) {
            if (ch == '\\' && p[1]) {
                dst[n++] = *p++;
                if (n < cap - 1)
                    dst[n++] = *p++;
                continue;
            }
            if (ch == '"')
                in_str = 0;
        } else {
            if (ch == '"')
                in_str = 1;
            else if (ch == '{')
                depth++;
            else if (ch == '}') {
                depth--;
                dst[n++] = *p++;
                if (depth == 0)
                    break;
                continue;
            }
        }
        dst[n++] = *p++;
    }
    dst[n] = 0;
    *pp = p;
    return depth == 0 && n > 0;
}

static void signal_carrier_metric_get(const char *obj, const char *key,
                                      char *dst, size_t cap)
{
    char tmp[96];

    if (!obj || !key || !dst || cap == 0)
        return;
    if (json_get(obj, key, tmp, sizeof tmp) && signal_value_present(tmp))
        signal_copy_value(dst, cap, tmp);
}

static int signal_parse_carriers(const char *parent, int is_nr,
                                 struct signal_carrier_metric *out, int max)
{
    char arr[16384];
    char obj[1536];
    const char *p;
    int n = 0;

    if (!parent || !out || max <= 0)
        return 0;
    if (!json_get(parent, "carriers", arr, sizeof arr))
        return 0;
    p = arr;
    while (n < max && signal_json_next_object(&p, obj, sizeof obj)) {
        struct signal_carrier_metric *m = &out[n];
        signal_carrier_metric_reset(m);
        m->valid = 1;
        signal_carrier_metric_get(obj, "name", m->name, sizeof m->name);
        signal_carrier_metric_get(obj, "type", m->type, sizeof m->type);
        signal_carrier_metric_get(obj, "pci", m->pci, sizeof m->pci);
        signal_carrier_metric_get(obj, is_nr ? "nrarfcn" : "earfcn", m->arfcn, sizeof m->arfcn);
        signal_carrier_metric_get(obj, "rb", m->rb, sizeof m->rb);
        signal_carrier_metric_get(obj, "grants", m->grants, sizeof m->grants);
        signal_carrier_metric_get(obj, "dl_rb", m->dl_rb, sizeof m->dl_rb);
        signal_carrier_metric_get(obj, "dl_grants", m->dl_grants, sizeof m->dl_grants);
        signal_carrier_metric_get(obj, "ul_rb", m->ul_rb, sizeof m->ul_rb);
        signal_carrier_metric_get(obj, "ul_grants", m->ul_grants, sizeof m->ul_grants);
        signal_carrier_metric_get(obj, "mcs", m->mcs, sizeof m->mcs);
        signal_carrier_metric_get(obj, "modulation", m->modulation, sizeof m->modulation);
        signal_carrier_metric_get(obj, "mimo", m->mimo, sizeof m->mimo);
        signal_carrier_metric_get(obj, "layers", m->layers, sizeof m->layers);
        signal_carrier_metric_get(obj, "bler_pct", m->bler, sizeof m->bler);
        signal_carrier_metric_get(obj, "ssb", m->ssb, sizeof m->ssb);
        signal_carrier_metric_get(obj, "serving_ssb", m->serving_ssb, sizeof m->serving_ssb);
        signal_carrier_metric_get(obj, "ml1_rsrp", m->ml1_rsrp, sizeof m->ml1_rsrp);
        signal_carrier_metric_get(obj, "ml1_rsrq", m->ml1_rsrq, sizeof m->ml1_rsrq);
        signal_carrier_metric_get(obj, "ml1_sinr", m->ml1_sinr, sizeof m->ml1_sinr);
        n++;
    }
    return n;
}

static void signal_lte_band_from_earfcn(const char *earfcn, char *dst, size_t cap)
{
    struct range { long lo, hi; const char *band; };
    static const struct range ranges[] = {
        { 0, 599, "B1" }, { 600, 1199, "B2" }, { 1200, 1949, "B3" },
        { 1950, 2399, "B4" }, { 2400, 2649, "B5" }, { 2750, 3449, "B7" },
        { 3450, 3799, "B8" }, { 5010, 5179, "B12" }, { 5180, 5279, "B13" },
        { 5730, 5849, "B17" }, { 5850, 5999, "B18" }, { 6000, 6149, "B19" },
        { 6150, 6449, "B20" }, { 8690, 9039, "B26" }, { 9210, 9659, "B28" },
        { 36200, 36349, "B34" }, { 37750, 38249, "B38" },
        { 38250, 38649, "B39" }, { 38650, 39649, "B40" },
        { 39650, 41589, "B41" },
    };
    char *end = NULL;
    long v;

    if (!dst || cap == 0) return;
    if (!signal_value_present(earfcn)) { snprintf(dst, cap, "-"); return; }
    v = strtol(earfcn, &end, 10);
    if (end == earfcn || v <= 0) { snprintf(dst, cap, "-"); return; }
    for (size_t i = 0; i < sizeof(ranges) / sizeof(ranges[0]); i++)
        if (v >= ranges[i].lo && v <= ranges[i].hi) {
            snprintf(dst, cap, "%s", ranges[i].band);
            return;
        }
    snprintf(dst, cap, "E%.20s", earfcn);
}

static void signal_nr_band_from_nrarfcn(const char *nrarfcn, char *dst, size_t cap)
{
    struct range { long lo, hi; const char *band; };
    static const struct range ranges[] = {
        { 151600, 160600, "n28" }, { 173800, 178800, "n5" },
        { 185000, 192000, "n8" }, { 361000, 376000, "n3" },
        { 422000, 434000, "n1" }, { 460000, 480000, "n40" },
        { 499200, 537999, "n41" }, { 514000, 524000, "n38" },
        { 620000, 653333, "n78" }, { 653334, 680000, "n77" },
        { 636667, 646666, "n48" }, { 693334, 733333, "n79" },
    };
    char *end = NULL;
    long v;

    if (!dst || cap == 0) return;
    if (!signal_value_present(nrarfcn)) { snprintf(dst, cap, "-"); return; }
    v = strtol(nrarfcn, &end, 10);
    if (end == nrarfcn || v <= 0) { snprintf(dst, cap, "-"); return; }
    for (size_t i = 0; i < sizeof(ranges) / sizeof(ranges[0]); i++)
        if (v >= ranges[i].lo && v <= ranges[i].hi) {
            snprintf(dst, cap, "%s", ranges[i].band);
            return;
        }
    snprintf(dst, cap, "N%.20s", nrarfcn);
}

static int signal_parse_neighbors(const char *parent, int is_nr,
                                  struct signal_neighbor_metric *out, int max)
{
    char arr[8192];
    char obj[1024];
    const char *p;
    int n = 0;

    if (!parent || !out || max <= 0)
        return 0;
    if (!json_get(parent, "neighbors", arr, sizeof arr))
        return 0;
    p = arr;
    while (n < max && signal_json_next_object(&p, obj, sizeof obj)) {
        struct signal_neighbor_metric *m = &out[n];
        signal_neighbor_metric_reset(m);
        signal_carrier_metric_get(obj, "pci", m->pci, sizeof m->pci);
        signal_carrier_metric_get(obj, "band", m->band, sizeof m->band);
        signal_carrier_metric_get(obj, is_nr ? "nrarfcn" : "earfcn", m->arfcn, sizeof m->arfcn);
        if (!signal_value_present(m->arfcn))
            signal_carrier_metric_get(obj, "arfcn", m->arfcn, sizeof m->arfcn);
        signal_carrier_metric_get(obj, "rsrp", m->rsrp, sizeof m->rsrp);
        signal_carrier_metric_get(obj, "rsrq", m->rsrq, sizeof m->rsrq);
        if (!signal_value_present(m->band)) {
            if (is_nr)
                signal_nr_band_from_nrarfcn(m->arfcn, m->band, sizeof m->band);
            else
                signal_lte_band_from_earfcn(m->arfcn, m->band, sizeof m->band);
        }
        if (signal_value_present(m->pci) ||
            signal_value_present(m->rsrp) ||
            signal_value_present(m->rsrq)) {
            m->valid = 1;
            n++;
        }
    }
    return n;
}

static int signal_carrier_is_pcell(const struct signal_carrier_metric *m)
{
    if (!m || !m->valid)
        return 0;
    return !strcasecmp(m->type, "PCell") || !strcasecmp(m->name, "PCell");
}

static int signal_carrier_same_text(const char *a, const char *b)
{
    return signal_value_present(a) && signal_value_present(b) && !strcmp(a, b);
}

static struct signal_carrier_metric *signal_pick_carrier_metric(struct signal_carrier_metric *list,
                                                               int n,
                                                               const char *pci,
                                                               const char *arfcn,
                                                               int prefer_pcell)
{
    struct signal_carrier_metric *pcell_fallback = NULL;

    if (!list || n <= 0)
        return NULL;

    for (int i = 0; i < n; i++) {
        struct signal_carrier_metric *m = &list[i];
        if (!m->valid || m->used)
            continue;
        if (prefer_pcell && !signal_carrier_is_pcell(m))
            continue;
        if (!prefer_pcell && signal_carrier_is_pcell(m))
            continue;
        if (signal_carrier_same_text(m->arfcn, arfcn)) {
            if (signal_value_present(m->pci) && signal_value_present(pci) &&
                !signal_carrier_same_text(m->pci, pci))
                continue;
            m->used = 1;
            return m;
        }
        if (prefer_pcell && signal_carrier_same_text(m->pci, pci)) {
            m->used = 1;
            return m;
        }
        if (prefer_pcell && !pcell_fallback)
            pcell_fallback = m;
    }

    if (pcell_fallback)
        pcell_fallback->used = 1;
    return prefer_pcell ? pcell_fallback : NULL;
}

static void signal_bundle_apply_metrics(struct signal_bundle *b)
{
    static char json[32768];
    static char lte[8192];
    static char nr[24576];
    FILE *fp;
    size_t n;
    int rc;

    if (!b || !g_sig_read)
        return;
    fp = popen("/usr/bin/wget -T 1 -qO- 'http://127.0.0.1:9460/modem/signal-metrics' 2>/dev/null", "r");
    if (!fp)
        return;
    n = fread(json, 1, sizeof(json) - 1, fp);
    rc = pclose(fp);
    if (rc != 0 || n == 0)
        return;
    json[n] = 0;

    signal_metric_get(json, "cell_vendor", b->nr_vendor, sizeof b->nr_vendor);
    signal_metric_get(json, "cell_key", b->cell_key, sizeof b->cell_key);
    signal_metric_get(json, "ta", b->ta, sizeof b->ta);
    if (json_get(json, "lte", lte, sizeof lte)) {
        signal_metric_get(lte, "ta", b->lte_ta, sizeof b->lte_ta);
        signal_metric_get(lte, "mcs", b->lte_mcs, sizeof b->lte_mcs);
        signal_metric_get(lte, "modulation", b->lte_modulation, sizeof b->lte_modulation);
        signal_metric_get(lte, "rb", b->lte_rb, sizeof b->lte_rb);
        signal_metric_get(lte, "grants", b->lte_grants, sizeof b->lte_grants);
        signal_metric_get(lte, "bler_pct", b->lte_bler, sizeof b->lte_bler);
        signal_metric_get(lte, "pusch", b->lte_pusch, sizeof b->lte_pusch);
        signal_metric_get(lte, "pucch", b->lte_pucch, sizeof b->lte_pucch);
        b->lte_carrier_n = signal_parse_carriers(lte, 0, b->lte_carriers,
                                                 SIGNAL_MAX_CARRIERS);
        b->lte_neighbor_n = signal_parse_neighbors(lte, 0, b->lte_neighbors,
                                                   SIGNAL_MAX_NEIGHBORS);
    }
    if (json_get(json, "nr", nr, sizeof nr)) {
        signal_metric_get(nr, "ta", b->nr_ta, sizeof b->nr_ta);
        signal_metric_get(nr, "mcs", b->nr_mcs, sizeof b->nr_mcs);
        signal_metric_get(nr, "modulation", b->nr_modulation, sizeof b->nr_modulation);
        signal_metric_get(nr, "mimo", b->nr_mimo, sizeof b->nr_mimo);
        signal_metric_get(nr, "layers", b->nr_layers, sizeof b->nr_layers);
        signal_metric_get(nr, "dl_rb", b->nr_dl_rb, sizeof b->nr_dl_rb);
        signal_metric_get(nr, "dl_grants", b->nr_dl_grants, sizeof b->nr_dl_grants);
        signal_metric_get(nr, "ul_rb", b->nr_ul_rb, sizeof b->nr_ul_rb);
        signal_metric_get(nr, "ul_grants", b->nr_ul_grants, sizeof b->nr_ul_grants);
        signal_metric_get(nr, "bler_pct", b->nr_bler, sizeof b->nr_bler);
        signal_metric_get(nr, "pusch", b->nr_pusch, sizeof b->nr_pusch);
        signal_metric_get(nr, "pucch", b->nr_pucch, sizeof b->nr_pucch);
        signal_metric_get(nr, "ports", b->nr_ports, sizeof b->nr_ports);
        signal_metric_get(nr, "ssb", b->nr_beam, sizeof b->nr_beam);
        signal_metric_get(nr, "serving_ssb", b->nr_serving_ssb, sizeof b->nr_serving_ssb);
        b->nr_carrier_n = signal_parse_carriers(nr, 1, b->nr_carriers,
                                                SIGNAL_MAX_CARRIERS);
        b->nr_neighbor_n = signal_parse_neighbors(nr, 1, b->nr_neighbors,
                                                  SIGNAL_MAX_NEIGHBORS);
    }
    if (!signal_value_present(b->ta)) {
        if (signal_value_present(b->nr_ta))
            snprintf(b->ta, sizeof b->ta, "%s", b->nr_ta);
        else if (signal_value_present(b->lte_ta))
            snprintf(b->ta, sizeof b->ta, "%s", b->lte_ta);
    }
}

static void signal_slot_label(const char *slot_json, char *dst, size_t cap)
{
    char data[8192];
    char decoded[8192];
    char message[1024];
    char name[256];
    char scope[256];
    char summary[256];

    if (!dst || cap == 0) return;
    if (!slot_json || !slot_json[0] || !strncmp(slot_json, "null", 4)) {
        snprintf(dst, cap, "-");
        return;
    }
    if (json_get(slot_json, "data", data, sizeof data)) {
        if (json_get(data, "decoded", decoded, sizeof decoded)) {
            if (json_get(decoded, "message", message, sizeof message) && message[0]) {
                if (message[0] == '{') {
                    if (json_get(message, "name", name, sizeof name) && name[0]) {
                        snprintf(dst, cap, "%s", name);
                        return;
                    }
                } else {
                    snprintf(dst, cap, "%s", message);
                    return;
                }
            }
            if (json_get(decoded, "scope", scope, sizeof scope) && scope[0]) {
                snprintf(dst, cap, "%s", scope);
                return;
            }
        }
        if (json_get(data, "summary", summary, sizeof summary) && summary[0]) {
            snprintf(dst, cap, "%s", summary);
            return;
        }
    }
    snprintf(dst, cap, "-");
}

static int json_pick_scalar_string(const char *obj, const char *const *keys, size_t nkeys,
                                   char *dst, size_t cap);
static int fetch_signal_raw_field(const char *kind, const char *const *keys, size_t nkeys,
                                  char *dst, size_t cap);
static int fetch_signal_raw_vendor(const char *kind, char *dst, size_t cap);

static int fetch_signal_raw_int_field(const char *kind, const char *const *keys, size_t nkeys,
                                      char *dst, size_t cap)
{
    char json[4096];
    char data[3600];
    char cmd[256];
    FILE *fp;
    size_t n;
    int rc;

    if (!dst || cap == 0 || !kind || !keys || nkeys == 0 || !g_sig_read)
        return 0;
    if (snprintf(cmd, sizeof cmd,
                 "/usr/bin/wget -T 1 -qO- 'http://127.0.0.1:9460/modem/latest?kind=%s' 2>/dev/null",
                 kind) >= (int)sizeof cmd)
        return 0;

    fp = popen(cmd, "r");
    if (!fp) return 0;
    n = fread(json, 1, sizeof json - 1, fp);
    rc = pclose(fp);
    if (rc != 0 || n == 0) return 0;
    json[n] = 0;
    if (!json_get(json, "data", data, sizeof data))
        return 0;

    for (size_t i = 0; i < nkeys; i++) {
        long v = json_get_int(data, keys[i], -2147483647L);
        if (v != -2147483647L) {
            snprintf(dst, cap, "%ld", v);
            return 1;
        }
    }
    return 0;
}

static int signal_key_tail_is_boundary(char c)
{
    return !((c >= 'A' && c <= 'Z') ||
             (c >= 'a' && c <= 'z') ||
             (c >= '0' && c <= '9') ||
             c == '_' || c == '-');
}

static int signal_parse_deltaf_number(const char *p, int *out)
{
    int sign = 1;
    int v = 0;
    int any = 0;

    if (!p || !out)
        return 0;
    if (*p == '-') {
        sign = -1;
        p++;
    }
    while (*p >= '0' && *p <= '9') {
        any = 1;
        v = v * 10 + (*p - '0');
        p++;
    }
    if (!any)
        return 0;
    *out = sign * v;
    return 1;
}

static int signal_extract_deltaf_value(const char *text, const char *key, int *out)
{
    const size_t key_len = strlen(key);
    const char *p;

    if (!text || !key || !out)
        return 0;
    for (p = strstr(text, key); p; p = strstr(p + 1, key)) {
        const char *q;
        const char *limit;
        const char *v;
        const char *colon;

        if (!signal_key_tail_is_boundary(p[key_len]))
            continue;
        q = p + key_len;
        limit = q + 160;
        v = strstr(q, "deltaF");
        if (v && v < limit && signal_parse_deltaf_number(v + 6, out))
            return 1;
        colon = strchr(q, ':');
        if (!colon || colon >= limit)
            continue;
        colon++;
        while (*colon == ' ' || *colon == '\t' || *colon == '"' || *colon == '\\')
            colon++;
        if (signal_parse_deltaf_number(colon, out))
            return 1;
    }
    return 0;
}

static int signal_detect_vendor_from_text(const char *text, char *dst, size_t cap)
{
    static const char *const keys[5] = {
        "deltaF-PUCCH-Format1",
        "deltaF-PUCCH-Format1b",
        "deltaF-PUCCH-Format2",
        "deltaF-PUCCH-Format2a",
        "deltaF-PUCCH-Format2b"
    };
    int v[5];

    if (!text || !dst || cap == 0)
        return 0;
    if (signal_extract_deltaf_value(text, keys[0], &v[0]) &&
        signal_extract_deltaf_value(text, keys[1], &v[1]) &&
        signal_extract_deltaf_value(text, keys[2], &v[2]) &&
        signal_extract_deltaf_value(text, keys[3], &v[3]) &&
        signal_extract_deltaf_value(text, keys[4], &v[4])) {
        if (v[0] == 0 && v[1] == 3 && v[2] == 0 && v[3] == 0 && v[4] == 0)
            snprintf(dst, cap, "Ericsson");
        else if (v[0] == 0 && v[1] == 3 && v[2] == 1 && v[3] == 2 && v[4] == 2)
            snprintf(dst, cap, "Huawei");
        else if (v[0] == 0 && v[1] == 1 && v[2] == 0 && v[3] == 0 && v[4] == 0)
            snprintf(dst, cap, "Nokia");
        else if (v[0] == 2 && v[1] == 3 && v[2] == 1 && v[3] == 2 && v[4] == 2)
            snprintf(dst, cap, "ZTE");
        else
            return 0;
        return 1;
    }
    if (strstr(text, "maxCarriersRequestedDL") &&
        strstr(text, "maxCarriersRequestedUL")) {
        snprintf(dst, cap, "Huawei");
        return 1;
    }
    return 0;
}

static int fetch_signal_bundle(struct signal_bundle *out)
{
    static uint32_t cached_at;
    static int cached_valid;
    static struct signal_bundle cached;
    char json[16384];
    char slot[8192];
    char data[8192];
    char decoded[8192];
    uint32_t now = millis();
    FILE *fp;
    size_t n;
    int rc;
    static const char *const nr_port_keys[] = {
        "csi_rs_ports", "csi_rs_nrof_ports", "nrofPorts", "ports", "num_ports"
    };
    static const char *const nr_ssb_keys[] = {
        "ssb_positions_in_burst_active", "ssb_positions_in_burst", "ssb_index",
        "csi_ssb_resource_set", "ssb_positions_in_burst_short_bitmap",
        "ssb_positions_in_burst_medium_bitmap", "ssb_positions_in_burst_long_bitmap"
    };

    if (out) signal_bundle_reset(out);
    if (cached_at && (uint32_t)(now - cached_at) < 50) {
        if (out) *out = cached;
        return cached_valid;
    }

    cached_at = now;
    cached_valid = 0;
    signal_bundle_reset(&cached);
    fp = popen("/usr/bin/wget -T 1 -qO- 'http://127.0.0.1:9460/modem/latest-signals' 2>/dev/null", "r");
    if (!fp) {
        if (out) *out = cached;
        return 0;
    }
    n = fread(json, 1, sizeof(json) - 1, fp);
    rc = pclose(fp);
    if (rc == 0 && n > 0) {
        json[n] = 0;
        if (json_get(json, "lte_rrc", slot, sizeof slot)) {
            signal_slot_label(slot, cached.lte_rrc, sizeof cached.lte_rrc);
            if (json_get(slot, "data", data, sizeof data)) {
                if (json_get(data, "decoded", decoded, sizeof decoded))
                    (void)signal_detect_vendor_from_text(decoded, cached.nr_vendor, sizeof cached.nr_vendor);
                if (!signal_value_present(cached.nr_vendor))
                    (void)signal_detect_vendor_from_text(data, cached.nr_vendor, sizeof cached.nr_vendor);
            }
        }
        if (json_get(json, "lte_nas", slot, sizeof slot)) signal_slot_label(slot, cached.lte_nas, sizeof cached.lte_nas);
        if (json_get(json, "nr_rrc", slot, sizeof slot)) {
            signal_slot_label(slot, cached.nr_rrc, sizeof cached.nr_rrc);
            if (json_get(slot, "data", data, sizeof data)) {
                if (json_get(data, "decoded", decoded, sizeof decoded)) {
                    (void)json_pick_scalar_string(decoded, nr_port_keys,
                                                  sizeof nr_port_keys / sizeof nr_port_keys[0],
                                                  cached.nr_ports, sizeof cached.nr_ports);
                    (void)json_pick_scalar_string(decoded, nr_ssb_keys,
                                                  sizeof nr_ssb_keys / sizeof nr_ssb_keys[0],
                                                  cached.nr_beam, sizeof cached.nr_beam);
                    (void)signal_detect_vendor_from_text(decoded, cached.nr_vendor, sizeof cached.nr_vendor);
                }
                if (!strcmp(cached.nr_ports, "-")) {
                    (void)json_pick_scalar_string(data, nr_port_keys,
                                                  sizeof nr_port_keys / sizeof nr_port_keys[0],
                                                  cached.nr_ports, sizeof cached.nr_ports);
                }
                if (!strcmp(cached.nr_beam, "-")) {
                    (void)json_pick_scalar_string(data, nr_ssb_keys,
                                                  sizeof nr_ssb_keys / sizeof nr_ssb_keys[0],
                                                  cached.nr_beam, sizeof cached.nr_beam);
                }
                if (!strcmp(cached.nr_ports, "-")) {
                    fetch_signal_raw_field("nr_rrc_full&scope=rrc_reconfiguration",
                                           nr_port_keys,
                                           sizeof nr_port_keys / sizeof nr_port_keys[0],
                                           cached.nr_ports, sizeof cached.nr_ports);
                }
                if (!strcmp(cached.nr_beam, "-")) {
                    fetch_signal_raw_field("nr_rrc_full&scope=rrc_reconfiguration",
                                           nr_ssb_keys,
                                           sizeof nr_ssb_keys / sizeof nr_ssb_keys[0],
                                           cached.nr_beam, sizeof cached.nr_beam);
                }
                if (!signal_value_present(cached.nr_vendor))
                    (void)signal_detect_vendor_from_text(data, cached.nr_vendor, sizeof cached.nr_vendor);
            }
        }
        if (json_get(json, "nr_nas", slot, sizeof slot)) signal_slot_label(slot, cached.nr_nas, sizeof cached.nr_nas);
        signal_bundle_apply_metrics(&cached);
        if (!signal_value_present(cached.nr_vendor)) {
            if (!fetch_signal_raw_vendor("lte_rrc_full&scope=rrc_system_information",
                                         cached.nr_vendor, sizeof cached.nr_vendor) &&
                !fetch_signal_raw_vendor("lte_rrc_full&scope=rrc_capability_enquiry",
                                         cached.nr_vendor, sizeof cached.nr_vendor))
                (void)fetch_signal_raw_vendor("nr_rrc_full&scope=rrc_capability_enquiry",
                                              cached.nr_vendor, sizeof cached.nr_vendor);
        }
        cached_valid = 1;
    }
    if (out) *out = cached;
    return cached_valid;
}

static pthread_mutex_t g_signal_async_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_t g_signal_async_thread;
static int g_signal_async_started;
static int g_signal_async_valid;
static uint32_t g_signal_async_at;
static struct signal_bundle g_signal_async_bundle;

static int signal_async_snapshot(struct signal_bundle *out)
{
    int ok;
    uint32_t max_age;

    if (!out)
        return 0;
    pthread_mutex_lock(&g_signal_async_lock);
    ok = g_signal_async_valid;
    max_age = (uint32_t)((g_refresh_ms > 0 ? g_refresh_ms : 1000) * 2 + 250);
    if (max_age < 1500) max_age = 1500;   /* 一轮抓取要几个 wget，刷新很快时 2 倍间隔不够用 */
    if (ok && g_signal_async_at &&
        (uint32_t)(millis() - g_signal_async_at) > max_age)
        ok = 0;
    if (ok)
        *out = g_signal_async_bundle;
    pthread_mutex_unlock(&g_signal_async_lock);
    return ok;
}

static void signal_async_publish(const struct signal_bundle *src, int valid)
{
    pthread_mutex_lock(&g_signal_async_lock);
    if (src && valid) {
        g_signal_async_bundle = *src;
        g_signal_async_valid = 1;
        g_signal_async_at = millis();
    } else {
        signal_bundle_reset(&g_signal_async_bundle);
        g_signal_async_valid = 0;
        g_signal_async_at = 0;
    }
    pthread_mutex_unlock(&g_signal_async_lock);
}

/* Set by the main loop: the screen is lit and showing a signal page. The worker only
 * fetches then (each fetch is a few wget/popen forks), not in the dark or elsewhere. */
static volatile int g_sig_view;

static void *signal_async_worker(void *arg)
{
    uint32_t next_at = 0;
    int was_enabled = 0;
    int last_wait_ms = 0;

    (void)arg;
    signal_async_publish(NULL, 0);
    while (g_run) {
        int enabled = signal_live_enabled();
        int wait_ms = g_refresh_ms > 0 ? g_refresh_ms : 1000;
        uint32_t now = millis();

        if (!enabled) {
            if (was_enabled)
                signal_async_publish(NULL, 0);
            was_enabled = 0;
            next_at = 0;
            usleep(500000);                         /* 实时信号关着：只等它被打开，半秒看一次够了 */
            continue;
        }
        if (g_refresh_ms <= 0 || !g_sig_view) {    /* keep the last snapshot; just stop fetching */
            next_at = 0;
            usleep(g_sig_view ? 100000 : 500000);   /* 不在信号页/熄屏：少醒 */
            continue;
        }
        if (wait_ms != last_wait_ms) {
            next_at = 0;
            last_wait_ms = wait_ms;
        }

        was_enabled = 1;
        if (next_at == 0 || (int32_t)(now - next_at) >= 0) {
            struct signal_bundle tmp;
            int ok;

            signal_bundle_reset(&tmp);
            ok = fetch_signal_bundle(&tmp);
            if (ok)
                signal_async_publish(&tmp, 1);
            next_at = millis() + (uint32_t)wait_ms;
        }
        usleep(50000);
    }
    return NULL;
}

static void signal_async_start(void)
{
    if (g_signal_async_started)
        return;
    signal_bundle_reset(&g_signal_async_bundle);
    if (pthread_create(&g_signal_async_thread, NULL, signal_async_worker, NULL) == 0)
        g_signal_async_started = 1;
}

static void signal_async_stop(void)
{
    if (!g_signal_async_started)
        return;
    (void)pthread_join(g_signal_async_thread, NULL);
    g_signal_async_started = 0;
}

static int json_pick_int_string(const char *obj, const char *const *keys, size_t nkeys,
                                char *dst, size_t cap)
{
    const long miss = -2147483647L;

    if (!dst || cap == 0) return 0;
    for (size_t i = 0; i < nkeys; i++) {
        long v = json_get_int(obj, keys[i], miss);
        if (v != miss) {
            snprintf(dst, cap, "%ld", v);
            return 1;
        }
    }
    snprintf(dst, cap, "-");
    return 0;
}

static int json_pick_scalar_string(const char *obj, const char *const *keys, size_t nkeys,
                                   char *dst, size_t cap)
{
    char tmp[512];

    if (!dst || cap == 0) return 0;
    for (size_t i = 0; i < nkeys; i++) {
        if (json_get(obj, keys[i], tmp, sizeof tmp) && tmp[0]) {
            snprintf(dst, cap, "%s", tmp);
            return 1;
        }
    }
    return json_pick_int_string(obj, keys, nkeys, dst, cap);
}

static int fetch_signal_raw_field(const char *kind, const char *const *keys, size_t nkeys,
                                  char *dst, size_t cap)
{
    char cmd[256];
    char json[4096];
    char data[3600];
    char decoded[3200];
    FILE *fp;
    size_t n;
    int rc;

    if (!dst || cap == 0) return 0;
    snprintf(dst, cap, "-");
    if (!g_sig_read) return 0;
    if (snprintf(cmd, sizeof cmd,
                 "/usr/bin/wget -T 1 -qO- 'http://127.0.0.1:9460/modem/latest?kind=%s' 2>/dev/null",
                 kind) >= (int)sizeof cmd)
        return 0;
    fp = popen(cmd, "r");
    if (!fp) return 0;
    n = fread(json, 1, sizeof(json) - 1, fp);
    rc = pclose(fp);
    if (rc != 0 || n == 0) return 0;
    json[n] = 0;
    if (!strncmp(json, "null", 4)) return 0;
    if (!json_get(json, "data", data, sizeof data)) return 0;
    if (json_get(data, "decoded", decoded, sizeof decoded) &&
        json_pick_scalar_string(decoded, keys, nkeys, dst, cap))
        return 1;
    return json_pick_scalar_string(data, keys, nkeys, dst, cap);
}

static int json_scan_last_scalar_string(const char *json, const char *const *keys, size_t nkeys,
                                        char *dst, size_t cap)
{
    char needle[128];

    if (!json || !dst || cap == 0) return 0;
    for (size_t i = 0; i < nkeys; i++) {
        const char *p = json;
        char last[256] = "";
        int found = 0;

        if (snprintf(needle, sizeof needle, "\"%s\":", keys[i]) >= (int)sizeof needle)
            continue;
        while ((p = strstr(p, needle)) != NULL) {
            const char *v = p + strlen(needle);
            char tmp[256];
            size_t o = 0;

            while (*v == ' ' || *v == '\t' || *v == '\r' || *v == '\n')
                v++;
            if (*v == '"') {
                v++;
                while (*v && o + 1 < sizeof tmp) {
                    if (*v == '\\' && v[1]) {
                        v++;
                        tmp[o++] = *v++;
                        continue;
                    }
                    if (*v == '"')
                        break;
                    tmp[o++] = *v++;
                }
            } else {
                while (*v && *v != ',' && *v != '}' && *v != ']' &&
                       *v != ' ' && *v != '\t' && *v != '\r' && *v != '\n' &&
                       o + 1 < sizeof tmp)
                    tmp[o++] = *v++;
            }
            tmp[o] = 0;
            if (tmp[0] && strcmp(tmp, "null") != 0) {
                snprintf(last, sizeof last, "%s", tmp);
                found = 1;
            }
            p += strlen(needle);
        }
        if (found) {
            snprintf(dst, cap, "%s", last);
            return 1;
        }
    }
    return 0;
}

static int fetch_signal_recent_raw_field(const char *kind, const char *const *keys, size_t nkeys,
                                         char *dst, size_t cap)
{
    char cmd[256];
    static char json[65536];
    FILE *fp;
    size_t n;
    int rc;

    if (!dst || cap == 0) return 0;
    if (!g_sig_read) return 0;
    if (snprintf(cmd, sizeof cmd,
                 "/usr/bin/wget -T 1 -qO- 'http://127.0.0.1:9460/modem/recent?kind=%s&limit=96' 2>/dev/null",
                 kind) >= (int)sizeof cmd)
        return 0;
    fp = popen(cmd, "r");
    if (!fp) return 0;
    n = fread(json, 1, sizeof(json) - 1, fp);
    rc = pclose(fp);
    if (rc != 0 || n == 0) return 0;
    json[n] = 0;
    return json_scan_last_scalar_string(json, keys, nkeys, dst, cap);
}

static int fetch_signal_raw_vendor(const char *kind, char *dst, size_t cap)
{
    char cmd[256];
    char json[4096];
    char data[3600];
    char decoded[3200];
    FILE *fp;
    size_t n;
    int rc;

    if (!dst || cap == 0 || !g_sig_read)
        return 0;
    if (snprintf(cmd, sizeof cmd,
                 "/usr/bin/wget -T 1 -qO- 'http://127.0.0.1:9460/modem/latest?kind=%s' 2>/dev/null",
                 kind) >= (int)sizeof cmd)
        return 0;
    fp = popen(cmd, "r");
    if (!fp)
        return 0;
    n = fread(json, 1, sizeof(json) - 1, fp);
    rc = pclose(fp);
    if (rc != 0 || n == 0)
        return 0;
    json[n] = 0;
    if (!strncmp(json, "null", 4))
        return 0;
    if (!json_get(json, "data", data, sizeof data))
        return 0;
    if (json_get(data, "decoded", decoded, sizeof decoded) &&
        signal_detect_vendor_from_text(decoded, dst, cap))
        return 1;
    return signal_detect_vendor_from_text(data, dst, cap);
}

static void signal_settings_summary(char *dst, size_t cap)
{
    if (!dst || cap == 0) return;
    snprintf(dst, cap, "读取 %s · 解析 %s",
             g_sig_read ? "已开启" : "已关闭",
             g_sig_parse ? "已开启" : "已关闭");
}
/* escape &,<,> for safe litehtml parsing of arbitrary SMS text */
static void html_esc(char *dst, size_t cap, const char *src)
{
    size_t o = 0;
    for (const char *s = src; *s && o + 7 < cap; s++) {
        const char *r = NULL;
        if      (*s == '&') r = "&amp;";
        else if (*s == '<') r = "&lt;";
        else if (*s == '>') r = "&gt;";
        if (r) { size_t L = strlen(r); memcpy(dst + o, r, L); o += L; }
        else dst[o++] = *s;
    }
    dst[o] = 0;
}

/* SMS bodies are text nodes too, but preserve their original line breaks. */
static void html_esc_breaks(char *dst, size_t cap, const char *src)
{
    size_t o = 0;
    for (const char *s = src; *s && o + 7 < cap; s++) {
        const char *r = NULL;
        if      (*s == '&')  r = "&amp;";
        else if (*s == '<')  r = "&lt;";
        else if (*s == '>')  r = "&gt;";
        else if (*s == '\n') r = "<br>";
        else if (*s == '\r') continue;
        if (r) { size_t L = strlen(r); memcpy(dst + o, r, L); o += L; }
        else dst[o++] = *s;
    }
    dst[o] = 0;
}

/* Copy at most maxb bytes of UTF-8 without splitting a multibyte char; stop at
 * a newline. Sets *cut if the source was longer, so the caller can add ellipsis. */
static void utf8_trunc(char *dst, size_t cap, const char *src, int maxb, int *cut)
{
    int o = 0; *cut = 0;
    const unsigned char *s = (const unsigned char *)src;
    while (*s) {
        if (*s == '\n' || *s == '\r') { *cut = 1; break; }
        int len = (*s >= 0xF0) ? 4 : (*s >= 0xE0) ? 3 : (*s >= 0xC0) ? 2 : 1;
        if (o + len > maxb || (size_t)(o + len) >= cap) { *cut = 1; break; }
        for (int k = 0; k < len && *s; k++) dst[o++] = (char)*s++;
    }
    dst[o] = 0;
}

static void signal_ui_compact(char *dst, size_t cap, const char *src)
{
    int cut = 0;

    if (!dst || cap == 0) return;
    if (!src || !src[0]) {
        snprintf(dst, cap, "-");
        return;
    }

    if (strstr(src, "rrc_reconfiguration_complete") || strstr(src, "RRCReconfigurationComplete"))
        snprintf(dst, cap, "RRC重配完成");
    else if (strstr(src, "rrc_reconfiguration") || strstr(src, "RRCReconfiguration"))
        snprintf(dst, cap, "RRC重配");
    else if (strstr(src, "rrc_setup_complete") || strstr(src, "RRCSetupComplete"))
        snprintf(dst, cap, "RRC建立完成");
    else if (strstr(src, "rrc_setup") || strstr(src, "RRCSetup"))
        snprintf(dst, cap, "RRC建立");
    else if (strstr(src, "ueCapabilityEnquiry") || strstr(src, "rrc_capability_enquiry"))
        snprintf(dst, cap, "UE能力查询");
    else if (strstr(src, "ueCapabilityInformation") || strstr(src, "rrc_capability_information"))
        snprintf(dst, cap, "UE能力上报");
    else if (strstr(src, "SystemInformation") || strstr(src, "rrc_system_information"))
        snprintf(dst, cap, "系统信息");
    else if (strstr(src, "MasterInformationBlock") || strstr(src, "rrc_mib"))
        snprintf(dst, cap, "MIB");
    else if (strstr(src, "securityModeCommand"))
        snprintf(dst, cap, "安全模式命令");
    else if (strstr(src, "securityModeComplete"))
        snprintf(dst, cap, "安全模式完成");
    else if (strstr(src, "registration_accept"))
        snprintf(dst, cap, "注册接受");
    else if (strstr(src, "registration_request"))
        snprintf(dst, cap, "注册请求");
    else if (strstr(src, "service_request"))
        snprintf(dst, cap, "业务请求");
    else {
        utf8_trunc(dst, cap, src, 18, &cut);
        if (cut && strlen(dst) + 3 < cap)
            strcat(dst, "...");
    }
}

static void signal_bler_compact(char *dst, size_t cap, const char *src)
{
    char *endp = NULL;
    double v;

    if (!dst || cap == 0) return;
    if (!src || !src[0]) {
        snprintf(dst, cap, "-");
        return;
    }
    v = strtod(src, &endp);
    if (endp && endp != src && *endp == '\0') {
        snprintf(dst, cap, "%.1f%%", v);
        return;
    }
    signal_ui_compact(dst, cap, src);
}

/* Second-level SMS detail dialog (number + date + full text), overlaid dimmed. */
static const char *sms_modal_html(void)
{
    static char out[DEVUI_SMS_TEXT_MAX * 6 + 1536];
    static char esc[DEVUI_SMS_TEXT_MAX * 6];
    html_esc_breaks(esc, sizeof esc, g_sms_text);
    snprintf(out, sizeof out,
        "<!DOCTYPE html><html><head><meta charset='UTF-8'><link rel='stylesheet' href='style.css'></head>"
        "<body class='mo'><div class='modal %s'>"
        "<div class='mtitle'>%s</div>"
        "<div class='smsmdate'>%s</div>"
        "<div id='smsview' class='smsmview'><div id='smsbody' class='smsmbody' style='top:-%dpx'>%s</div></div>"
        "<div class='mbtns'><a href='act:smsclose' class='mbtn2 prim mfull'>关闭</a></div>"
        "</div></body></html>",
        g_theme ? "light" : "dark", g_sms_num, g_sms_date, g_sms_scroll, esc);
    return out;
}

/* Build the second-level band-lock dialog (overlaid on the dimmed page). */
static const char *modal_html(void)
{
    static char out[3200];
    const char *uni, *sel, *pfx, *title, *act;
    if (g_modal == 5) {                    /* 插线选择供电方式: bottom sheet, plain radio rows */
        int can_out = pr_peer_can_sink(), cur = g_pr_pend_mode >= 0 ? g_pr_pend_mode : pr_current_mode(), n = can_out ? 4 : 2;
        int hgt = 18 + 22 + 24 + 50 * n + 1 + 22, left = 15000 - (int)(millis() - g_pr_open_at);
        char netrow[320] = "";
        if (can_out) {
            int on = g_pr_pend_net >= 0 ? g_pr_pend_net : usb_net_now();   /* on: say which way the power flows with it */
            snprintf(netrow, sizeof netrow,
                     "<a href='act:prnet' class='prli prnet%s'><span class='prsw %s'><i></i></span><span class='prt'>USB 有线上网%s</span></a>",
                     on ? " two" : "", on ? "on" : "off",
                     !on ? "" : cur == 2 ? "<span class='prs'>本机供电给对方 · 本机给对方网络</span>"
                                         : "<span class='prs'>对方供电给本机 · 本机给对方网络</span>");
        }
        if (left < 0) left = 0;
        snprintf(out, sizeof out,
            "<!DOCTYPE html><html><head><meta charset='UTF-8'><link rel='stylesheet' href='style.css'></head>"
            "<body class='mo'><div class='prsheet %s' style='top:%dpx; height:%dpx'>"
            "<div class='prttl'><span class='n prpct'>%d%%</span><b>%s</b></div><div class='prsub'>选择供电方式</div>"
            "<a href='act:pr:0' class='prli%s'><span class='prck'></span><span class='prt'>给本机充电</span></a>"
            "<a href='act:pr:1' class='prli two%s'><span class='prck'></span><span class='prt'>直供电<span class='prs'>不充电池，适合长期插电</span></span></a>"
            "%s%s<div class='prbar'><i style='width:%dpx'></i></div></div></body></html>",   /* countdown: 264 px track */
            g_theme ? "light" : "dark", 480 - 10 - hgt, hgt, clampi(g_stat_bat, 0, 100),
            can_out ? "已连接 USB" : "已连接充电器",
            cur == 0 ? " on" : "", cur == 1 ? " on" : "",
            can_out ? (cur == 2 ? "<a href='act:pr:2' class='prli on'><span class='prck'></span><span class='prt'>给对方供电</span></a>"
                                : "<a href='act:pr:2' class='prli'><span class='prck'></span><span class='prt'>给对方供电</span></a>") : "",
            netrow, left > 0 ? 6 + 258 * left / 15000 : 0);
        return out;
    }
    if (g_modal == 4) {
        snprintf(out, sizeof out,
            "<!DOCTYPE html><html><head><meta charset='UTF-8'><link rel='stylesheet' href='style.css'></head>"
            "<body class='mo'><div class='modal %s'>"
            "<div class='mtitle'>高级设置</div>"
            "<a href='act:sigread' class='row'><span class='lab'>读取信令<span class='st'>控制 ML1 / 原始信令读取，影响 TA / Ports / Beam</span></span>"
            "<span class='ctrl'><span class='sw %s'><span class='kn'></span></span></span></a>"
            "<a href='act:sigparse' class='row'><span class='lab'>解析信令<span class='st'>控制 LTE / NR RRC / NAS 解析，并决定第二页是否显示</span></span>"
            "<span class='ctrl'><span class='sw %s'><span class='kn'></span></span></span></a>"
            "<div class='sec'>开启解析后才显示第二页。读取关闭时，TA / Ports / SSB Index 会显示为空。</div>"
            "<div class='mbtns'><a href='act:closemodal' class='mbtn2 prim mfull'>关闭</a></div>"
            "</div></body></html>",
            g_theme ? "light" : "dark",
            g_sig_read ? "on" : "off",
            g_sig_parse ? "on" : "off");
        return out;
    }
    if (g_modal == 1)      { uni = g_uni_sa;  sel = g_sel_sa;  pfx = "n"; act = "bsa";  title = "5G SA 锁频"; }
    else if (g_modal == 2) { uni = g_uni_nsa; sel = g_sel_nsa; pfx = "n"; act = "bnsa"; title = "5G NSA 锁频"; }
    else                   { uni = g_uni_lte; sel = g_sel_lte; pfx = "B"; act = "blte"; title = "4G 锁频"; }
    char chips[2200];
    build_chips_cls(chips, sizeof chips, uni, sel, act, pfx, "bchip-on", "bchip");
    snprintf(out, sizeof out,
        "<!DOCTYPE html><html><head><meta charset='UTF-8'><link rel='stylesheet' href='style.css'></head>"
        "<body class='mo'><div class='modal %s'>"
        "<div class='mtitle'>%s</div><div class='mbands'>%s</div>"
        "<div class='mbtns'>"
        "<a href='act:mall' class='mbtn2'>全选/全不选</a>"
        "<a href='act:minv' class='mbtn2'>反选</a>"
        "<a href='act:mapply' class='mbtn2 prim'>应用</a></div>"
        "</div></body></html>",
        g_theme ? "light" : "dark", title, chips);
    return out;
}

static int fetch_lte_ta(int *ta_out)
{
    static uint32_t cached_at;
    static uint32_t enable_req_at;
    static int cached_valid;
    static int cached_ta = -1;
    char json[2048];
    char data[1800];
    char cmd[192];
    uint32_t now = millis();
    FILE *fp;
    size_t n;
    int rc;
    int fresh_ta = -1;

    if (ta_out) *ta_out = -1;
    if (!g_sig_read) return 0;
    if (cached_ta < 0) {
        char cached_text[24];
        if (signal_cache_get("ta", cached_text, sizeof cached_text)) {
            char *endp = NULL;
            long v = strtol(cached_text, &endp, 10);

            if (endp && *endp == '\0' && v >= 0 && v <= 4096) {
                cached_ta = (int)v;
                cached_valid = 1;
            }
        }
    }
    if (cached_at && (uint32_t)(now - cached_at) < 900) {
        if (cached_valid && ta_out) *ta_out = cached_ta;
        return cached_valid;
    }

    cached_at = now;
    cached_valid = cached_ta >= 0;
    fp = popen("/usr/bin/wget -T 1 -qO- 'http://127.0.0.1:9460/modem/latest?kind=lte_ml1_raw' 2>/dev/null", "r");
    if (fp) {
        n = fread(json, 1, sizeof(json) - 1, fp);
        rc = pclose(fp);
        if (rc == 0 && n > 0) {
            json[n] = 0;
            if (!strncmp(json, "null", 4)) {
                if ((uint32_t)(now - enable_req_at) >= 5000 &&
                    snprintf(cmd, sizeof cmd,
                            "/usr/bin/wget -T 2 -qO- --post-data='' 'http://127.0.0.1:9460/modem/control?ml1_raw=1&active=1' >/dev/null 2>&1")
                        < (int)sizeof cmd) {
                    (void)system(cmd);
                    enable_req_at = now;
                }
            } else if (json_get(json, "data", data, sizeof data)) {
                fresh_ta = (int)json_get_int(data, "ta", -1);
            }
        }
    }
    if (fresh_ta < 0) {
        fp = popen("/usr/bin/wget -T 1 -qO- 'http://127.0.0.1:9460/modem/recent?kind=lte_ml1_raw&log_origin=direct&limit=64' 2>/dev/null", "r");
        if (fp) {
            n = fread(json, 1, sizeof(json) - 1, fp);
            rc = pclose(fp);
            if (rc == 0 && n > 0) {
                const char *p;
                json[n] = 0;
                p = json;
                while ((p = strstr(p, "\"ta\":")) != NULL) {
                    char *endp = NULL;
                    long v = strtol(p + 5, &endp, 10);

                    if (endp && endp != p + 5 && v >= 0 && v <= 4096)
                        fresh_ta = (int)v;
                    p = endp && endp > p ? endp : p + 5;
                }
            }
        }
    }
    if (fresh_ta >= 0) {
        char ta_text[24];

        cached_ta = fresh_ta;
        cached_valid = 1;
        snprintf(ta_text, sizeof ta_text, "%d", fresh_ta);
        signal_cache_put("ta", ta_text);
    }
    if (cached_ta < 0) return 0;

    cached_valid = 1;
    if (ta_out) *ta_out = cached_ta;
    return 1;
}

static double nr_ta_unit_m(const devui_data_t *d, const struct signal_bundle *sig)
{
    long arfcn = d ? d->nr_channel : 0;

    if (sig && signal_value_present(sig->cell_key)) {
        const char *p = strrchr(sig->cell_key, ':');
        if (p && p[1]) {
            char *endp = NULL;
            long v = strtol(p + 1, &endp, 10);
            if (endp && endp != p + 1 && v > 0) arfcn = v;
        }
    }
    if (arfcn >= 499200 && arfcn <= 537999) return 39.06; /* n41, 30 kHz */
    if (arfcn >= 620000 && arfcn <= 653333) return 39.06; /* n78, 30 kHz */
    if (arfcn >= 693334 && arfcn <= 733333) return 39.06; /* n79, 30 kHz */
    if (d && (strstr(d->nr_band, "n41") || strstr(d->nr_band, "n77") ||
              strstr(d->nr_band, "n78") || strstr(d->nr_band, "n79")))
        return 39.06;
    return 78.12;
}

static double ta_unit_m_for_signal(const devui_data_t *d, const struct signal_bundle *sig, int ta)
{
    if (sig && signal_value_present(sig->nr_ta)) {
        char *endp = NULL;
        long nr_ta = strtol(sig->nr_ta, &endp, 10);
        if (endp && endp != sig->nr_ta && nr_ta == ta)
            return nr_ta_unit_m(d, sig);
    }
    return 78.12; /* LTE / 15 kHz */
}

static void fmt_ta_distance(char *dst, size_t cap, int ta, double unit_m)
{
    double meters;

    if (!dst || cap == 0) return;
    if (ta < 0) { snprintf(dst, cap, "-"); return; }
    if (unit_m <= 0.0) unit_m = 78.12;
    meters = (double)ta * unit_m;
    if (meters >= 1000.0) snprintf(dst, cap, "约 %.1f km", meters / 1000.0);
    else                  snprintf(dst, cap, "约 %.0f m", meters);
}

static int signal_neighbor_count(const struct signal_neighbor_metric *list, int n)
{
    int count = 0;

    if (!list || n <= 0) return 0;
    for (int i = 0; i < n; i++)
        if (list[i].valid)
            count++;
    return count;
}

static const char *signal_rsrp_class(const char *rsrp)
{
    double v;

    if (!signal_value_present(rsrp)) return "q-off";
    v = atof(rsrp);
    if (v >= -85.0) return "q-good";
    if (v >= -105.0) return "q-mid";
    return "q-bad";
}

static const char *signal_rsrq_class(const char *rsrq)
{
    double v;

    if (!signal_value_present(rsrq)) return "q-off";
    v = atof(rsrq);
    if (v >= -10.0) return "q-good";
    if (v >= -15.0) return "q-mid";
    return "q-bad";
}

static int signal_neighbor_row(char *buf, int o, int cap,
                               const struct signal_neighbor_metric *n)
{
    char pci[32], band[48], rsrp[32], rsrq[32];

    if (!buf || cap <= 0 || o >= cap || !n || !n->valid)
        return o;
    html_esc(pci, sizeof pci, signal_carrier_val(n->pci));
    html_esc(band, sizeof band, signal_carrier_val(n->band));
    html_esc(rsrp, sizeof rsrp, signal_carrier_val(n->rsrp));
    html_esc(rsrq, sizeof rsrq, signal_carrier_val(n->rsrq));
    return o + snprintf(buf + o, cap - o,
                        "<div class='nrow'><span>%s</span><span>%s</span>"
                        "<span class='%s'>%s</span><span class='%s'>%s</span></div>",
                        pci, band, signal_rsrp_class(n->rsrp), rsrp,
                        signal_rsrq_class(n->rsrq), rsrq);
}

static int signal_neighbor_section(char *buf, int o, int cap, const char *title,
                                   const struct signal_neighbor_metric *list, int n)
{
    int count = signal_neighbor_count(list, n);

    if (!count || !buf || cap <= 0 || o >= cap)
        return o;
    o += snprintf(buf + o, cap - o,
                  "<div class='nsec'>%s <span>%d</span></div>"
                  "<div class='nhead'><span>PCI</span><span>频段</span><span>RSRP</span><span>RSRQ</span></div>",
                  title, count);
    for (int i = 0; i < n; i++)
        o = signal_neighbor_row(buf, o, cap, &list[i]);
    return o;
}

static const char *signal_neighbor_empty_text(void)
{
    return "等待 LTE / NR ML1 邻区测量。";
}

static const char *signal_neighbors_html(const struct signal_bundle *sig)
{
    static char buf[7000];
    int nr_count = sig ? signal_neighbor_count(sig->nr_neighbors, sig->nr_neighbor_n) : 0;
    int lte_count = sig ? signal_neighbor_count(sig->lte_neighbors, sig->lte_neighbor_n) : 0;
    int total = nr_count + lte_count;
    const char *source = g_sig_parse ? "信令解析" : "";
    int o = 0;

    if (!g_sig_parse) {
        buf[0] = 0;
        return buf;
    }

    if (!g_neighbor_open) {
        if (source[0])
            snprintf(buf, sizeof buf,
                     "<a href='act:neighbors' class='card neigh-toggle'>"
                     "<span class='title'>邻小区</span><span class='r muted'>%s · %d 个 · 点击展开</span>"
                     "</a>",
                     source, total);
        else
            snprintf(buf, sizeof buf,
                     "<a href='act:neighbors' class='card neigh-toggle'>"
                     "<span class='title'>邻小区</span><span class='r muted'>%d 个 · 点击展开</span>"
                     "</a>",
                     total);
        return buf;
    }

    if (source[0])
        o += snprintf(buf + o, sizeof buf - o,
                      "<div class='card neigh-card'>"
                      "<div class='title'>邻小区 <span class='muted nsrc'>%s</span>"
                      "<a href='act:neighbors' class='rev r'>收起</a></div>",
                      source);
    else
        o += snprintf(buf + o, sizeof buf - o,
                      "<div class='card neigh-card'>"
                      "<div class='title'>邻小区 <a href='act:neighbors' class='rev r'>收起</a></div>");
    if (total <= 0) {
        o += snprintf(buf + o, sizeof buf - o,
                      "<div class='sec'>%s</div>",
                      signal_neighbor_empty_text());
    } else {
        o = signal_neighbor_section(buf, o, sizeof buf, "NR", sig->nr_neighbors, sig->nr_neighbor_n);
        o = signal_neighbor_section(buf, o, sizeof buf, "LTE", sig->lte_neighbors, sig->lte_neighbor_n);
    }
    if (o > (int)sizeof buf - 1) o = (int)sizeof buf - 1;
    snprintf(buf + o, sizeof buf - o, "</div>");
    return buf;
}

/* ---- power source + time-to-full ----
 * usb/online + usb_type tell charger vs PC vs PD fast charger; with direct
 * supply on (or a full battery) the battery current sits near zero. The ETA
 * uses the kernel value when it has one, else remaining charge / smoothed
 * charge current, and only changes once a minute so it doesn't jitter. */
static long sysfs_long(const char *path, long dflt)
{
    FILE *fp = fopen(path, "r"); long v = dflt;
    if (fp) { if (fscanf(fp, "%ld", &v) != 1) v = dflt; fclose(fp); }
    return v;
}
static void sysfs_str(const char *path, char *out, size_t cap)
{
    FILE *fp = fopen(path, "r"); out[0] = 0;
    if (fp) { if (fgets(out, (int)cap, fp)) out[strcspn(out, "\r\n")] = 0; fclose(fp); }
}
static void pwr_refresh(void)
{
    static uint32_t at, eta_at;
    static double ibat_avg;            /* µA, charging positive */
    uint32_t now = millis();
    if (at && now - at < 2000) return;
    at = now ? now : 1;
    const char *PS = "/sys/class/power_supply";
    char path[128], utype[128], st[32];
    snprintf(path, sizeof path, "%s/usb/online", PS);        long online = sysfs_long(path, 0);
    snprintf(path, sizeof path, "%s/usb/usb_type", PS);      sysfs_str(path, utype, sizeof utype);
    snprintf(path, sizeof path, "%s/usb/voltage_now", PS);   long uv = sysfs_long(path, 0);
    snprintf(path, sizeof path, "%s/usb/current_now", PS);   long ua = sysfs_long(path, 0);
    snprintf(path, sizeof path, "%s/battery/status", PS);    sysfs_str(path, st, sizeof st);
    snprintf(path, sizeof path, "%s/battery/current_now", PS); long ib = sysfs_long(path, 0);
    snprintf(path, sizeof path, "%s/battery/charge_counter", PS); long cc = sysfs_long(path, 0);
    snprintf(path, sizeof path, "%s/battery/charge_full", PS);    long cf = sysfs_long(path, 0);
    snprintf(path, sizeof path, "%s/battery/time_to_full_now", PS); long ttf = sysfs_long(path, -1);
    snprintf(path, sizeof path, "%s/battery/capacity", PS);   long cap = sysfs_long(path, 0);
    static uint32_t plug_at;
    char *br = strchr(utype, '['), cur[24] = "";
    if (br) { snprintf(cur, sizeof cur, "%s", br + 1); cur[strcspn(cur, "]")] = 0; }
    static long last_online = -1;
    double mag = ib < 0 ? -(double)ib : (double)ib;   /* sign differs between gauges; status says which way */
    if (online != last_online) { ibat_avg = 0; g_pwr.eta_min = -1; eta_at = 0; last_online = online; }  /* plug change: start fresh */
    ibat_avg = ibat_avg == 0 ? mag : ibat_avg * 0.85 + mag * 0.15;
    g_pwr.in_v = uv / 1e6;
    g_pwr.in_w = (uv / 1e6) * (ua / 1e6);
    if (!online) plug_at = 0;
    else if (!plug_at) plug_at = now ? now : 1;
    g_pwr.estimating = 0;
    g_pwr.drain = 0;
    if (!online && dps_draining()) {           /* direct supply, battery drifting down to 60 % */
        g_pwr.state = PWR_DIRECT;
        g_pwr.drain = 1;
        g_pwr.eta_min = -1;
        g_pwr.empty_min = -1;
        return;
    }
    if (!online) {
        g_pwr.state = g_typec_source == 1 ? PWR_OUT : PWR_BATT;
        g_pwr.eta_min = -1;
        double dis = strcmp(st, "Charging") ? ibat_avg : 0;
        g_pwr.empty_min = dis > 20000 && cc > 0 ? (int)(cc / dis * 60) : -1;
        return;
    }
    g_pwr.empty_min = -1;
    /* 直供电 on: the firmware holds the battery at 40-60 %, topping it up now and then;
     * that is never "charging to full", so no charging state and no time-to-full */
    if (g_dps == 1) {
        g_pwr.state = PWR_DIRECT;
        g_pwr.eta_min = -1;
        return;
    }
    /* full: gauge at 100 %, "Full", or no time left near the top (the charger
     * keeps topping off at 100 % with "Charging" and a sizeable current) */
    if (cap >= 100 || !strcmp(st, "Full") || (ttf == 0 && cap >= 98) || (cf > 0 && cc >= cf)) {
        g_pwr.state = PWR_FULL;
        g_pwr.eta_min = -1;
        return;
    }
    int charging = !strcmp(st, "Charging") && ibat_avg > 60000;
    if (!charging) {
        /* battery idle on the charger: that's direct supply when the DPS switch is
         * on; otherwise it is just the slow top-off near full. 直供电已关就是充电模式
         * （刚关掉时固件要过一会儿才真正开始充，电流接近 0，不能当成直供电）；
         * 开关状态还没读到时才按电量猜 */
        g_pwr.state = (g_dps == 1 || (g_dps < 0 && cap < 95)) ? PWR_DIRECT : PWR_CHG;
        g_pwr.eta_min = -1;
        return;
    }
    if (!strcmp(cur, "SDP") || !strcmp(cur, "CDP")) g_pwr.state = PWR_PC;
    else if (!strncmp(cur, "PD", 2) || g_pwr.in_w >= 15) g_pwr.state = PWR_FAST;
    else g_pwr.state = PWR_CHG;
    if (!eta_at || now - eta_at > 60000 || g_pwr.eta_min < 0) {
        eta_at = now ? now : 1;
        if (ttf > 0) g_pwr.eta_min = (int)(ttf / 60);
        else if (cf > cc && ibat_avg > 60000) g_pwr.eta_min = (int)((double)(cf - cc) / ibat_avg * 60);
        else g_pwr.eta_min = -1;
    }
    g_pwr.estimating = g_pwr.eta_min < 0 && now - plug_at < 60000;
}

/* datad reports the WiFi key empty (uci stores it encrypted); hostapd's runtime
 * config has the passphrase, so look the SSID up there. Re-read every 10 s. */
static void wifi_key_fallback(const char *ssid, char *out, size_t cap)
{
    static char c_ssid[64], c_key[80];
    static uint32_t c_at;
    uint32_t now = millis();
    if (!ssid || !ssid[0]) return;
    if (!c_at || now - c_at > 10000 || strcmp(c_ssid, ssid)) {
        c_at = now ? now : 1;
        snprintf(c_ssid, sizeof c_ssid, "%s", ssid);
        c_key[0] = 0;
        for (int k = 0; k < 4 && !c_key[0]; k++) {
            char path[64], line[160], fs[64] = "", fk[80] = "";
            snprintf(path, sizeof path, "/data/vendor/wifi/hostapd-wlan%d.conf", k);
            FILE *fp = fopen(path, "r");
            if (!fp) continue;
            while (fgets(line, sizeof line, fp)) {
                line[strcspn(line, "\r\n")] = 0;
                if (!strncmp(line, "ssid=", 5)) snprintf(fs, sizeof fs, "%s", line + 5);
                else if (!strncmp(line, "wpa_passphrase=", 15)) snprintf(fk, sizeof fk, "%s", line + 15);
                else if (!fk[0] && !strncmp(line, "sae_password=", 13)) snprintf(fk, sizeof fk, "%s", line + 13);
            }
            fclose(fp);
            if (!strcmp(fs, ssid)) snprintf(c_key, sizeof c_key, "%s", fk);
        }
    }
    if (c_key[0]) snprintf(out, cap, "%s", c_key);
}

/* ---- cell lock (same ubus calls the vendor goform CELL_LOCK uses) ---- */
static char g_cl_nr[64], g_cl_lte[64];   /* "pci,arfcn,band" / "pci,earfcn"; "" or "0,.." = none */
static char g_cl_armed[64];              /* action armed by a first tap */
static uint32_t g_cl_until, g_cl_at;
static void celllock_refresh(int force)
{
    uint32_t now = millis();
    if (!force && g_cl_at && now - g_cl_at < 5000) return;
    g_cl_at = now ? now : 1;
    /* never block the UI thread on ubus: read the last result, refresh it in the background */
    FILE *fp = fopen("/tmp/u60-netinfo.json", "r");
    system("(ubus -t 3 call zte_nwinfo_api nwinfo_get_netinfo > /tmp/u60-netinfo.json.new 2>/dev/null && "
           "mv /tmp/u60-netinfo.json.new /tmp/u60-netinfo.json) >/dev/null 2>&1 &");
    if (!fp) return;
    char line[256];
    while (fgets(line, sizeof line, fp)) {
        char *k, *v, *e;
        if ((k = strstr(line, "\"lock_nr_cell\"")) || (k = strstr(line, "\"lock_lte_cell\""))) {
            int nr = k[6] == 'n';
            char *kq = strchr(k + 1, '"'); if (!kq) continue;
            v = strchr(kq + 1, '"'); if (!v) continue; v++;
            e = strchr(v, '"'); if (!e) continue; *e = 0;
            snprintf(nr ? g_cl_nr : g_cl_lte, sizeof g_cl_nr, "%s", v);
        }
    }
    fclose(fp);
}
static int cl_locked(const char *v) { return v[0] && strncmp(v, "0,", 2) && strcmp(v, "0"); }

/* ---- WiFi link rate per client (iw station dump on wlan0 = 2.4G, wlan2 = 5G) ---- */
static struct { char mac[20]; int rate; const char *band, *gen; } g_sta[16];
static int g_sta_n;
static void sta_refresh(void)
{
    static uint32_t at;
    uint32_t now = millis();
    if (at && now - at < 5000) return;
    at = now ? now : 1;
    g_sta_n = 0;
    static const char *ifs[2] = { "wlan0", "wlan2" };
    for (int k = 0; k < 2; k++) {
        char cmd[64]; snprintf(cmd, sizeof cmd, "iw dev %s station dump 2>/dev/null", ifs[k]);
        FILE *fp = popen(cmd, "r");
        if (!fp) continue;
        char line[256];
        int cur = -1;
        while (fgets(line, sizeof line, fp)) {
            char mac[20];
            if (sscanf(line, "Station %19s", mac) == 1 && g_sta_n < 16) {
                cur = g_sta_n++;
                snprintf(g_sta[cur].mac, sizeof g_sta[cur].mac, "%s", mac);
                g_sta[cur].rate = 0; g_sta[cur].band = k ? "5G" : "2.4G"; g_sta[cur].gen = "";
            } else if (cur >= 0 && strstr(line, "tx bitrate:")) {
                double r = 0; char *c = strchr(line, ':');
                if (c) r = atof(c + 1);
                g_sta[cur].rate = (int)(r + .5);
                g_sta[cur].gen = strstr(line, "EHT") ? "WiFi 7" : strstr(line, "HE-") ? "WiFi 6" :
                                 strstr(line, "VHT") ? "WiFi 5" : strstr(line, "MCS") ? "WiFi 4" : "";
            }
        }
        pclose(fp);
    }
}
static int sta_find(const char *mac)
{
    for (int i = 0; i < g_sta_n; i++) if (!strcasecmp(g_sta[i].mac, mac)) return i;
    return -1;
}

/* Short band label: "n78" / "B3" from whatever the modem reports
 * ("78", "n78", "LTE BAND 3", "B3"...); never longer than a few chars. */
static void short_band(char *out, size_t cap, const char *raw, int nr)
{
    const char *p = raw ? raw : "";
    while (*p && (*p < '0' || *p > '9')) p++;
    if (*p) { int n = atoi(p); snprintf(out, cap, "%s%d", nr ? "n" : "B", n); }
    else snprintf(out, cap, "%.6s", raw && raw[0] ? raw : "--");
}

/* ---- monthly data usage: the firmware's own counters (zwrt_data), the same the
 * stock web page shows; independent of zwrt-datad (which is frozen while dark).
 * Fetched in the background into /tmp files, parsed from there: never blocks. ---- */
static struct { long long mon, day; long long limit; int lim_on, ratio, clearday, valid; } g_wd;
static long long json_ll(const char *buf, const char *key)
{
    char k[64]; snprintf(k, sizeof k, "\"%s\":", key);
    const char *p = strstr(buf, k);
    if (!p) return -1;
    p += strlen(k);
    while (*p == ' ' || *p == '"') p++;
    return atoll(p);
}
static void wwandst_refresh(void)
{
    static uint32_t at;
    uint32_t now = millis();
    if (at && now - at < 60000) return;
    at = now ? now : 1;
    char buf[4096];
    FILE *fp = fopen("/tmp/u60-wd.json", "r");
    if (fp) {
        size_t n = fread(buf, 1, sizeof buf - 1, fp); buf[n] = 0; fclose(fp);
        long long mt = json_ll(buf, "month_tx_bytes"), mr = json_ll(buf, "month_rx_bytes");
        long long dt = json_ll(buf, "day_tx_bytes"), dr = json_ll(buf, "day_rx_bytes");
        if (mt >= 0 && mr >= 0) { g_wd.mon = mt + mr; g_wd.day = (dt >= 0 && dr >= 0) ? dt + dr : -1; g_wd.valid = 1; }
    }
    fp = fopen("/tmp/u60-wdlim.json", "r");
    if (fp) {
        size_t n = fread(buf, 1, sizeof buf - 1, fp); buf[n] = 0; fclose(fp);
        g_wd.lim_on = json_ll(buf, "enable") == 1;
        g_wd.limit = json_ll(buf, "value");
        g_wd.ratio = (int)json_ll(buf, "ratio");
    }
    fp = fopen("/tmp/u60-wdclr.json", "r");
    if (fp) {
        size_t n = fread(buf, 1, sizeof buf - 1, fp); buf[n] = 0; fclose(fp);
        g_wd.clearday = (int)json_ll(buf, "clearday");
    }
    system("(ubus -t 3 call zwrt_data get_wwandst '{\"source_module\":\"web\",\"cid\":1,\"type\":4}' > /tmp/u60-wd.json.n && mv /tmp/u60-wd.json.n /tmp/u60-wd.json; "
           "ubus -t 3 call zwrt_data get_wwandst_monthlimit '{\"source_module\":\"web\",\"cid\":1}' > /tmp/u60-wdlim.json.n && mv /tmp/u60-wdlim.json.n /tmp/u60-wdlim.json; "
           "ubus -t 3 call zwrt_data get_wwandst_clearday '{\"source_module\":\"web\",\"cid\":1}' > /tmp/u60-wdclr.json.n && mv /tmp/u60-wdclr.json.n /tmp/u60-wdclr.json) >/dev/null 2>&1 &");    if (!g_wd.valid) at = now - 57000;            /* first time: pick the result up in ~3 s */
}
static void fmt_vol(char *v, size_t vc, char *u, size_t uc, long long b)
{
    double g = b / 1073741824.0;
    if (b < 0) { snprintf(v, vc, "--"); snprintf(u, uc, "%s", ""); }
    else if (g >= 10) { snprintf(v, vc, "%.1f", g); snprintf(u, uc, "GB"); }
    else if (g >= 1)  { snprintf(v, vc, "%.2f", g); snprintf(u, uc, "GB"); }
    else              { snprintf(v, vc, "%.0f", b / 1048576.0); snprintf(u, uc, "MB"); }
}

/* WiFi QR (MECARD-style "WIFI:" payload), rebuilt by build_kv, drawn by draw_qr. */
static char g_qr_text[320];
static void qr_escape(char *dst, size_t cap, const char *src)
{
    size_t o = 0;
    for (; src && *src && o + 2 < cap; src++) {
        if (strchr("\\;,:\"", *src)) dst[o++] = '\\';
        dst[o++] = *src;
    }
    dst[o] = 0;
}

static void draw_qr(void)
{
    static char last[320];
    static uint8_t qr[qrcodegen_BUFFER_LEN_FOR_VERSION(12)];
    static int ok;
    int x, y, w, h;
    if (!html_view_rect("#qr", &x, &y, &w, &h) || !g_qr_text[0]) return;
    if (strcmp(last, g_qr_text)) {
        uint8_t tmp[qrcodegen_BUFFER_LEN_FOR_VERSION(12)];
        snprintf(last, sizeof last, "%s", g_qr_text);
        ok = qrcodegen_encodeText(g_qr_text, tmp, qr, qrcodegen_Ecc_LOW, 1, 12, qrcodegen_Mask_AUTO, true);
    }
    if (!ok) return;
    int n = qrcodegen_getSize(qr);
    int m = (w < h ? w : h) / (n + 2);          /* 1-module quiet zone each side */
    if (m < 1) m = 1;
    int ox = x + (w - n * m) / 2, oy = y + (h - n * m) / 2;
    html_view_fill_round_rect(ox - m - 3, oy - m - 3, n * m + 2 * m + 6, n * m + 2 * m + 6, 8, 0xff, 0xff, 0xff, 255);
    for (int r = 0; r < n; r++)
        for (int c = 0; c < n; c++)
            if (qrcodegen_getModule(qr, c, r))
                html_view_fill_rect(ox + c * m, oy + r * m, m, m, 0x11, 0x14, 0x19, 255);
}

/* ---- 网络自救: tap (twice) on the 网络 page -> drop every WiFi client; they rejoin
 * on their own within seconds. Same as the user switching WiFi off and on: when the
 * phone shows WiFi but apps load nothing, rejoining makes it drop dead connections
 * and open new ones. Manual only; idle-guard.sh does the work and writes the result. */
#define KICK_CMD   "sh /data/ufi-tools/data/idle-guard.sh kick 网络自救 >/dev/null 2>&1 &"
#define KICK_LAST  "/tmp/u60-kick.last"   /* "<epoch> <clients dropped>" */
#define RESCUE_ARM_MS 4000

static uint32_t g_rescue_armed_at;     /* first tap; 0 = not armed */

static int rescue_armed(void)
{
    return g_rescue_armed_at && millis() - g_rescue_armed_at < RESCUE_ARM_MS;
}

/* 网络 page tile next to 附近基站 */
static void rescue_entry(char *out, size_t cap)
{
    char sub[48] = "断开 WiFi 重连";   /* the half tile fits ~6 CJK chars */
    long t = 0; int n = -1;
    FILE *f = fopen(KICK_LAST, "r");
    if (f) { if (fscanf(f, "%ld %d", &t, &n) != 2) n = -1; fclose(f); }
    if (rescue_armed()) snprintf(sub, sizeof sub, "再点一次执行");
    else if (n >= 0 && t > 0 && time(NULL) - t < 120) snprintf(sub, sizeof sub, "已断开 %d 台", n);
    snprintf(out, cap, "<a href='act:rescue:start' class='card half tl2'><span id='chev4' class='chev'></span>"
             "<span class='et'>网络自救</span><span class='k'>%s</span></a>", sub);
}

/* ---- 锁频 page (subpages/lock.html): 5G bands, 4G bands and network mode on one
 * screen. Taps only stage a change (yellow edge); the bottom button sends it and
 * needs a second tap within 4 s. 5G bands apply to both SA and NSA. Mode is three
 * toggles mapped onto the four stock net_select values; NSA needs a 4G anchor, so
 * NSA pulls 4G in and dropping 4G drops NSA. ---- */
#define BL_ARM_MS 4000
static const char *g_bl5m[4] = { "78", "1", "41", "28" };
static const char *g_bl5l[4] = { "联通 3.5G", "联通 2.1G", "移动 2.6G", "700M" };
static const char *g_bl4m[4] = { "3", "1", "8", "41" };
static const char *g_bl4l[4] = { "1800M", "2100M", "900M", "2.6G" };
static char g_bl5[256], g_bl4[256];           /* staged lists */
static char g_bldev5[256], g_bldevn[256], g_bldev4[256], g_bldevmode[16];   /* what the modem has */
static int  g_blnet = -1, g_bldirty;          /* staged mode bits: 1 SA, 2 NSA, 4 4G */
static uint32_t g_blarm_at, g_bldone_at;
static int  g_blarm;                          /* 1 = apply armed, 2 = reset armed */

static int bl_mode_bits(const char *m)
{
    return !strcmp(m, "Only_5G") ? 1 : !strcmp(m, "LTE_AND_5G") ? 6 : !strcmp(m, "Only_LTE") ? 4 : 7;
}
static const char *bl_bits_mode(int b)        /* SA+4G has no stock value: auto (NSA stays on) */
{
    return b == 1 ? "Only_5G" : b == 6 ? "LTE_AND_5G" : b == 4 ? "Only_LTE" : "WL_AND_5G";
}
/* rebuild a band list from the universe order with band b switched on/off */
static void bl_set(char *list, size_t cap, const char *uni, const char *b, int on)
{
    char u[256], out[256]; int o = 0;
    snprintf(u, sizeof u, "%s", uni);
    for (char *t = strtok(u, ","); t; t = strtok(NULL, ","))
        if (!strcmp(t, b) ? on : band_in(list, t))
            o += snprintf(out + o, sizeof out - o, "%s%s", o ? "," : "", t);
    out[o] = 0;
    snprintf(list, cap, "%s", out);
}
static int bl_is_main(const char **m, const char *b) { for (int k = 0; k < 4; k++) if (!strcmp(m[k], b)) return 1; return 0; }
/* "other" bands (universe minus the four shown): how many, how many on */
static void bl_others(const char *uni, const char *list, const char **m, int *tot, int *on)
{
    char u[256]; *tot = *on = 0;
    snprintf(u, sizeof u, "%s", uni);
    for (char *t = strtok(u, ","); t; t = strtok(NULL, ","))
        if (!bl_is_main(m, t)) { (*tot)++; if (band_in(list, t)) (*on)++; }
}
static void bl_others_set(char *list, size_t cap, const char *uni, const char **m, int on)
{
    char u[256];
    snprintf(u, sizeof u, "%s", uni);
    for (char *t = strtok(u, ","); t; t = strtok(NULL, ","))
        if (!bl_is_main(m, t)) bl_set(list, cap, uni, t, on);
}
static int bl_armed(int kind) { return g_blarm == kind && millis() - g_blarm_at < BL_ARM_MS; }
/* why the staged set can't be sent ("" = it can) */
static const char *bl_invalid(void)
{
    if (!g_blnet) return "选网至少留一种";
    if (!g_bl4[0]) return "4G 至少留一个频段";
    if ((g_blnet & 3) && !g_bl5[0]) return "5G 至少留一个频段";
    return "";
}
static int bl_first_num(const char *s) { while (*s && (*s < '0' || *s > '9')) s++; return atoi(s); }

/* called from build_kv every render: keep the staged copy in sync until the user edits */
static void bl_sync(const devui_data_t *d)
{
    if (g_bldone_at && millis() - g_bldone_at < 10000) return;   /* just sent: modem still reports the old set */
    snprintf(g_bldev5, sizeof g_bldev5, "%s", d->sa_bands);
    snprintf(g_bldevn, sizeof g_bldevn, "%s", d->nsa_bands);
    snprintf(g_bldev4, sizeof g_bldev4, "%s", d->lte_bands);
    snprintf(g_bldevmode, sizeof g_bldevmode, "%s", d->net_select);
    if (!g_bldirty || g_blnet < 0) {
        snprintf(g_bl5, sizeof g_bl5, "%s", d->sa_bands);
        snprintf(g_bl4, sizeof g_bl4, "%s", d->lte_bands);
        g_blnet = bl_mode_bits(d->net_select);
        g_bldirty = 0;
    }
}

static void bl_chips(char *out, size_t cap, int *po, const char *uni, const char *list, const char *dev,
                     const char **m, const char **lab, const char *pfx, const char *act, int cur)
{
    int o = *po;
    for (int k = 0; k < 4; k++) {
        if (!band_in(uni, m[k])) continue;
        int on = band_in(list, m[k]), was = band_in(dev, m[k]);
        o += snprintf(out + o, cap - o, "<a href='act:bl:%s:%s' class='blc%s%s%s'><b>%s%s</b><span>%s</span></a>",
                      act, m[k], on ? " on" : "", on != was ? " dirty" : "", atoi(m[k]) == cur ? " cur" : "",
                      pfx, m[k], lab[k]);
    }
    *po = o;
}

static void bl_body(char *out, size_t cap, const devui_data_t *d)
{
    int o = 0, nr = d->nr_rsrp && (strstr(d->net_type, "SA") || strstr(d->net_type, "NSA") || strstr(d->net_type, "ENDC"));
    int cur5 = nr ? bl_first_num(d->nr_band[0] ? d->nr_band : d->band) : 0;
    int cur4 = strstr(d->net_type, "SA") && !strstr(d->net_type, "NSA") ? 0 : bl_first_num(d->band);
    char what[64];
    if (nr) snprintf(what, sizeof what, "5G %s n%d · %d dBm", strstr(d->net_type, "NSA") ? "NSA" : "SA", cur5, d->nr_rsrp);
    else    snprintf(what, sizeof what, "4G B%d · %d dBm", cur4, d->lte_rsrp);
    /* status: what is in use, and a cell lock if one is pinning it */
    celllock_refresh(0);
    if (cl_locked(g_cl_nr))
        o += snprintf(out + o, cap - o, "<div class='card blnow warn'><a href='act:cl:unlock' class='mini-btn'>解除锁定</a>"
                      "<div class='k'>正在用</div><div class='blv'>%s</div><div class='k'>已锁基站 PCI %d</div></div>",
                      what, atoi(g_cl_nr));
    else
        o += snprintf(out + o, cap - o, "<div class='card blnow'><div class='k'>正在用</div><div class='blv'>%s</div></div>", what);
    /* 5G */
    int t5, n5, t4, n4;
    bl_others(g_uni_sa, g_bl5, g_bl5m, &t5, &n5);
    bl_others(g_uni_lte, g_bl4, g_bl4m, &t4, &n4);
    int d5 = strcmp(g_bl5, g_bldev5) != 0, d4 = strcmp(g_bl4, g_bldev4) != 0;
    o += snprintf(out + o, cap - o, "<div class='card blcard'><div class='blhd'><span class='k blsum'>%s</span>5G 频段%s</div><div class='blg'>",
                  !g_bl5[0] ? "全部关闭" : band_count(g_bl5) == band_count(g_uni_sa) ? "全部可用" : band_count(g_bl5) == 1 ? "只用 1 个" : "部分可用",
                  d5 ? "<span class='bltag'>未生效</span>" : "");
    bl_chips(out, cap, &o, g_uni_sa, g_bl5, g_bldev5, g_bl5m, g_bl5l, "n", "5g", cur5);
    o += snprintf(out + o, cap - o, "</div><a href='act:bl:5go' class='blmore'>其他 %d 个频段 · %s</a></div>", t5,
                  n5 == t5 ? "全开 · 点此关闭" : n5 ? "部分开 · 点此关闭" : "已关 · 点此打开");
    /* 4G */
    o += snprintf(out + o, cap - o, "<div class='card blcard'><div class='blhd'><span class='k blsum'>%s</span>4G 频段%s</div><div class='blg'>",
                  band_count(g_bl4) == band_count(g_uni_lte) ? "全部可用" : !g_bl4[0] ? "全部关闭" : "部分可用",
                  d4 ? "<span class='bltag'>未生效</span>" : "");
    bl_chips(out, cap, &o, g_uni_lte, g_bl4, g_bldev4, g_bl4m, g_bl4l, "B", "4g", cur4);
    o += snprintf(out + o, cap - o, "</div><a href='act:bl:4go' class='blmore'>其他 %d 个频段 · %s</a></div>", t4,
                  n4 == t4 ? "全开 · 点此关闭" : n4 ? "部分开 · 点此关闭" : "已关 · 点此打开");
    /* mode */
    int dm = bl_mode_bits(g_bldevmode), dirtym = g_blnet != dm;
    const char *curm = nr ? (strstr(d->net_type, "NSA") || strstr(d->net_type, "ENDC") ? "nsa" : "sa") : "lte";
    o += snprintf(out + o, cap - o, "<div class='card blcard'><div class='blhd'><span class='k blsum'>%s</span>选网方式%s</div><div class='blg bl3'>",
                  g_blnet == 5 ? "SA+4G 按自动（NSA 也开着）" : "多选", dirtym ? "<span class='bltag'>未生效</span>" : "");
    static const struct { int bit; const char *id, *lab; } nm[3] = { { 1, "sa", "5G SA" }, { 2, "nsa", "5G NSA" }, { 4, "lte", "4G" } };
    for (int k = 0; k < 3; k++)
        o += snprintf(out + o, cap - o, "<a href='act:bl:net:%s' class='blc%s%s%s'><b>%s</b></a>", nm[k].id,
                      g_blnet & nm[k].bit ? " on" : "", (g_blnet & nm[k].bit) != (dm & nm[k].bit) ? " dirty" : "",
                      !strcmp(curm, nm[k].id) ? " cur" : "", nm[k].lab);
    o += snprintf(out + o, cap - o, "</div></div>");
    /* bottom bar */
    int dirty = d5 || d4 || dirtym;
    const char *bad = bl_invalid();
    char sub[64];
    if (!dirty) snprintf(sub, sizeof sub, "%s", g_bldone_at && millis() - g_bldone_at < 15000 ? "已下发，正在重新搜网" : "还没改动");
    else if (bad[0]) snprintf(sub, sizeof sub, "%s", bad);
    else if (bl_armed(1)) snprintf(sub, sizeof sub, "%s", g_blnet == 1 ? "只用 SA：信号差时会完全没网" : "会断网约 10 秒重新搜网");
    else if (d5 && band_count(g_bl5) == 1 && !d4 && !dirtym) snprintf(sub, sizeof sub, "5G 只用 n%s，4G 不变", g_bl5);
    else snprintf(sub, sizeof sub, "%s%s%s", d5 ? "改 5G 频段 " : "", d4 ? "改 4G 频段 " : "", dirtym ? "改选网" : "");
    o += snprintf(out + o, cap - o, "<div class='blbar'>%s<a href='act:bl:apply' class='btn blbtn%s'>%s<small>%s</small></a></div>",
                  dirty ? "<a href='act:bl:undo' class='btn blside'>撤销</a>"
                        : bl_armed(2) ? "<a href='act:bl:reset' class='btn blside arm'>再点恢复</a>"
                                      : "<a href='act:bl:reset' class='btn blside'>全部恢复</a>",
                  !dirty || bad[0] ? " dim" : bl_armed(1) ? " arm" : " pri",
                  bl_armed(1) ? "再点一次确认" : "应用", sub);
}

/* act:bl:* - returns 1 if handled */
static int bl_action(const char *a, uint32_t now)
{
    if (strncmp(a, "bl:", 3)) return 0;
    a += 3;
    if (!strncmp(a, "5g:", 3))      { bl_set(g_bl5, sizeof g_bl5, g_uni_sa, a + 3, !band_in(g_bl5, a + 3)); g_bldirty = 1; g_blarm = 0; }
    else if (!strncmp(a, "4g:", 3)) { bl_set(g_bl4, sizeof g_bl4, g_uni_lte, a + 3, !band_in(g_bl4, a + 3)); g_bldirty = 1; g_blarm = 0; }
    else if (!strcmp(a, "5go") || !strcmp(a, "4go")) {
        int f = a[0] == '5', t, n;
        bl_others(f ? g_uni_sa : g_uni_lte, f ? g_bl5 : g_bl4, f ? g_bl5m : g_bl4m, &t, &n);
        bl_others_set(f ? g_bl5 : g_bl4, 256, f ? g_uni_sa : g_uni_lte, f ? g_bl5m : g_bl4m, n == 0);
        g_bldirty = 1; g_blarm = 0;
    }
    else if (!strncmp(a, "net:", 4)) {
        int bit = !strcmp(a + 4, "sa") ? 1 : !strcmp(a + 4, "nsa") ? 2 : 4;
        if (g_blnet < 0) g_blnet = 7;
        g_blnet ^= bit;
        if (bit == 2 && (g_blnet & 2)) g_blnet |= 4;       /* NSA needs a 4G anchor */
        if (bit == 4 && !(g_blnet & 4)) g_blnet &= ~2;
        g_bldirty = 1; g_blarm = 0;
    }
    else if (!strcmp(a, "undo")) { g_bldirty = 0; g_blarm = 0; }
    else if (!strcmp(a, "reset")) {
        if (!bl_armed(2)) { g_blarm = 2; g_blarm_at = now ? now : 1; }
        else {
            system("(ubus call zte_nwinfo_api nwinfo_reset_band_cell_setting '{}'; "
                   "ubus call zte_nwinfo_api nwinfo_set_netselect '{\"net_select\":\"WL_AND_5G\"}') >/dev/null 2>&1 &");
            g_blarm = 0; g_bldirty = 0; g_bldone_at = now ? now : 1;
        }
    }
    else if (!strcmp(a, "apply")) {
        int dirty = strcmp(g_bl5, g_bldev5) || strcmp(g_bl4, g_bldev4) || g_blnet != bl_mode_bits(g_bldevmode);
        if (!dirty || bl_invalid()[0]) return 1;
        if (!bl_armed(1)) { g_blarm = 1; g_blarm_at = now ? now : 1; return 1; }
        char cmd[1400]; int o = snprintf(cmd, sizeof cmd, "(");
        if (strcmp(g_bl5, g_bldev5) && g_bl5[0])
            o += snprintf(cmd + o, sizeof cmd - o, "ubus call zte_nwinfo_api nwinfo_set_nrbandlock '{\"nr5g_type\":\"0\",\"nr5g_band\":\"%s\"}'; ", g_bl5);
        if (strcmp(g_bl5, g_bldevn) && g_bl5[0])
            o += snprintf(cmd + o, sizeof cmd - o, "ubus call zte_nwinfo_api nwinfo_set_nrbandlock '{\"nr5g_type\":\"1\",\"nr5g_band\":\"%s\"}'; ", g_bl5);
        if (strcmp(g_bl4, g_bldev4))
            o += snprintf(cmd + o, sizeof cmd - o, "ubus call zte_nwinfo_api nwinfo_set_lte_ext_band '{\"lte_band\":\"%s\"}'; ", g_bl4);
        if (g_blnet != bl_mode_bits(g_bldevmode)) {
            o += snprintf(cmd + o, sizeof cmd - o, "ubus call zte_nwinfo_api nwinfo_set_netselect '{\"net_select\":\"%s\"}'; ", bl_bits_mode(g_blnet));
            snprintf(g_net_pending, sizeof g_net_pending, "%s", bl_bits_mode(g_blnet));
        }
        snprintf(cmd + o, sizeof cmd - o, ") >/dev/null 2>&1 &");
        system(cmd);
        g_blarm = 0; g_bldone_at = now ? now : 1;
        /* keep showing the staged set until the modem reports it back */
        snprintf(g_bldev5, sizeof g_bldev5, "%s", g_bl5); snprintf(g_bldev4, sizeof g_bldev4, "%s", g_bl4);
        snprintf(g_bldevmode, sizeof g_bldevmode, "%s", bl_bits_mode(g_blnet));
        g_bldirty = 0;
    }
    return 1;
}

/* ---- WiFi 功率 (subpages/wifipower.html): the stock coverage setting, exactly as the
 * stock web UI sets it - zwrt_wlan set txpowerpercent on both chips. The firmware only
 * takes 40 / 80 / 100 (= 15/14, 18/17, 19/18 dBm on 2.4G/5G); it persists the value
 * itself and changes power without dropping clients. ---- */
#define TXP_FILE "/tmp/u60-txp"          /* "<percent> <2.4G dBm> <5G dBm>" */
static int g_txp_pending;                  /* tapped level until the modem reports it */
static uint32_t g_txp_at;
static void txp_refresh(int force)
{
    static uint32_t at;
    uint32_t now = millis();
    if (!force && at && now - at < 3000) return;
    at = now ? now : 1;
    system("(p=$(uci -q get wireless.wifi0.txpowerpercent); "
           "a=$(iw dev wlan0 info 2>/dev/null | awk '/txpower/{print $2}'); "
           "b=$(iw dev wlan2 info 2>/dev/null | awk '/txpower/{print $2}'); "
           "echo \"${p:-100} ${a:-0} ${b:-0}\" > " TXP_FILE ".n && mv " TXP_FILE ".n " TXP_FILE ") >/dev/null 2>&1 &");
}
static void txp_read(int *pct, double *d2, double *d5)
{
    FILE *f = fopen(TXP_FILE, "r");
    *pct = 100; *d2 = *d5 = 0;
    if (f) { if (fscanf(f, "%d %lf %lf", pct, d2, d5) < 1) *pct = 100; fclose(f); }
    if (g_txp_pending) {
        if (*pct == g_txp_pending || millis() - g_txp_at > 20000) g_txp_pending = 0;
        else *pct = g_txp_pending;
    }
}
static const char *txp_label(int pct) { return pct <= 40 ? "近距离" : pct <= 80 ? "中距离" : "穿墙"; }

/* Fill a kv table from the current device state. Buffers are static. */
static void fit_px(char *out, size_t cap, const char *src, int px, int size);

/* ---- 升级高级版：devupd（本程序的软链）在后台下单、等付款、下载、安装，进度写进 UPD_STATE；
 * 这边只读状态和画页面，按钮只是拉起对应的 devupd 动作。 ---- */
struct upg { char st[16], msg[160], url[200]; long amt, exp, total, price, orig, left, at; };
static void upg_read(struct upg *u)
{
    memset(u, 0, sizeof *u);
    char *b = read_file(UPD_STATE);
    if (!b) return;
    for (char *ln = strtok(b, "\n"); ln; ln = strtok(NULL, "\n")) {
        char *v = strchr(ln, '=');
        if (!v) continue;
        *v++ = 0;
        if (!strcmp(ln, "st")) snprintf(u->st, sizeof u->st, "%s", v);
        else if (!strcmp(ln, "msg")) snprintf(u->msg, sizeof u->msg, "%s", v);
        else if (!strcmp(ln, "url")) snprintf(u->url, sizeof u->url, "%s", v);
        else if (!strcmp(ln, "amt")) u->amt = atol(v);
        else if (!strcmp(ln, "exp")) u->exp = atol(v);
        else if (!strcmp(ln, "total")) u->total = atol(v);
        else if (!strcmp(ln, "price")) u->price = atol(v);
        else if (!strcmp(ln, "orig")) u->orig = atol(v);
        else if (!strcmp(ln, "left")) u->left = atol(v);
        else if (!strcmp(ln, "at")) u->at = atol(v);
    }
    free(b);
}
static long upg_got(void)
{
    struct stat st;
    return stat(UPD_FILE, &st) ? 0 : (long)st.st_size;
}
static void upg_run(const char *what)
{
    if (access(UPD_CLI, F_OK)) symlink("u60pro-devui", UPD_CLI);
    char c[200];
    snprintf(c, sizeof c, "(nohup " UPD_CLI " upd %s >/dev/null 2>&1 </dev/null &)", what);
    system(c);
}
/* 进行中的状态：按秒刷新（倒计时、下载进度） */
static int upg_busy(const char *st)
{
    return !strcmp(st, "probe") || !strcmp(st, "pay") || !strcmp(st, "cancel") || !strcmp(st, "dl") || !strcmp(st, "install");
}
static const char *upg_page_html(void)
{
    static char b[2400];
    struct upg u;
    char msg[200];
    upg_read(&u);
    html_esc(msg, sizeof msg, u.msg);
    const char *intro =
        "<div class='card'><div class='rlet'>没有流量时借用身边 WiFi</div>"
        "<div class='k'>把酒店、公司、咖啡店的 WiFi 当作上行，U60 继续给你的手机、电脑共享网络，蜂窝流量一点不花。</div></div>";
    if (!strcmp(u.st, "pay")) {
        long left = u.exp - (long)time(NULL);
        if (left < 0) left = 0;
        snprintf(b, sizeof b,
            "<div class='card upc'><div id='qr' class='upqr'></div>"
            "<div class='upt'>微信扫一扫付款 <span class='upa'>¥%ld.%02ld</span></div>"
            "<div class='k upk'>付款后自动确认 · 剩余 %ld:%02ld</div></div>"
            "<div class='btns'><a href='act:upg:cancel' class='btn'>取消</a></div>",
            u.amt / 100, u.amt % 100, left / 60, left % 60);
    } else if (!strcmp(u.st, "ready")) {
        char sz[32] = "";
        if (u.total > 0) snprintf(sz, sizeof sz, "（约 %.1f MB）", u.total / 1048576.0);
        snprintf(b, sizeof b,
            "<div class='card'><div class='rlet'>%s</div>"
            "<div class='k'>点“立即升级”下载高级版%s，装好后屏幕会重启一次，回来就能用 WiFi 中继。</div></div>"
            "<div class='btns'><a href='act:upg:go' class='btn pri upb'>立即升级</a></div>",
            msg[0] ? msg : "已购买高级版", sz);
    } else if (!strcmp(u.st, "dl") || !strcmp(u.st, "install")) {
        int dl = !strcmp(u.st, "dl");
        long got = dl ? upg_got() : u.total;
        int pct = u.total > 0 ? (int)(got * 100 / u.total) : 0;
        if (pct > 100) pct = 100;
        char t[80];
        if (dl) snprintf(t, sizeof t, "%d%% · %.1f / %.1f MB", pct, got / 1048576.0, u.total / 1048576.0);
        else snprintf(t, sizeof t, "请不要断电");
        snprintf(b, sizeof b,
            "<div class='card'><div class='rlet'>%s</div>"
            "<div class='bar'><i style='width:%d%%'></i></div>"
            "<div class='k upk'>%s</div></div>",
            dl ? "正在下载高级版" : "正在安装，屏幕即将重启", pct, t);
    } else if (!strcmp(u.st, "idle")) {
        char pr[160] = "", yuan[24];
        if (u.price % 100) snprintf(yuan, sizeof yuan, "%ld.%02ld", u.price / 100, u.price % 100);
        else snprintf(yuan, sizeof yuan, "%ld", u.price / 100);
        if (u.orig > u.price && u.left > 0)
            snprintf(pr, sizeof pr, "<span class='upo'>¥%ld</span> 首发价 · 还剩 %ld 份", u.orig / 100, u.left);
        snprintf(b, sizeof b,
            "%s<div class='card'><div class='rlet'>升级高级版 <span class='upa'>¥%s</span></div>"
            "<div class='k'>%s%s一次付费，后续更新免费。在屏幕上扫码付款，付完直接升级，不用连电脑。</div></div>"
            "<div class='btns'><a href='act:upg:buy' class='btn pri upb'>购买升级</a></div>",
            intro, yuan, pr, pr[0] ? "。" : "");
        if (msg[0]) {
            size_t o = strlen(b);
            snprintf(b + o, sizeof b - o, "<div class='k upk upw'>%s</div>", msg);
        }
    } else if (!strcmp(u.st, "offline") || !strcmp(u.st, "fail")) {
        snprintf(b, sizeof b,
            "%s<div class='card'><div class='rlet'>%s</div><div class='k'>%s</div></div>"
            "<div class='btns'><a href='act:upg:probe' class='btn pri upb'>重试</a></div>",
            intro, !strcmp(u.st, "fail") ? "没有完成" : "暂时连不上", msg);
    } else {
        snprintf(b, sizeof b, "%s<div class='card'><div class='k'>%s</div></div>", intro, msg[0] ? msg : "正在查询…");
    }
    return b;
}

/* ---- 扫描所有频段 (附近基站): scripts/bandscan.sh runs on its own and leaves its
 * progress / results in /tmp; this side only reads them and draws. ---- */
#define BS_SH "/data/plugins/u60pro-devui/bandscan.sh"
static const char *const BS_BANDS[] = { "78", "41", "28", "1", "3", "5", "8", "79", NULL };
static int  g_bs_confirm;          /* confirm card shown in place of the button */
static char g_bs_locked[8];        /* band locked from the results (this session) */
struct bs_row { char band[8]; int ok, rsrp, pci; char sinr[12]; };
/* state: 1 running, 2 done, 3 stopped, 4 failed, 0 never */
static int bs_state(char *scan, size_t sc, int *idx, int *tot, long *at)
{
    char b[96] = "", w[16] = "";
    *idx = *tot = 0; *at = 0; if (scan) scan[0] = 0;
    if (!read_line_path("/tmp/u60-bandscan.state", b, sizeof b)) return 0;
    sscanf(b, "%15s", w);
    if (!strcmp(w, "run")) {
        char bd[8] = "";
        sscanf(b, "run %7s %d %d %ld", bd, idx, tot, at);
        if (scan) snprintf(scan, sc, "%s", bd);
        /* a dead script would leave "run" behind forever: trust it only with a live pid */
        long pid = 0;
        if (!read_long_path("/tmp/u60-bandscan.pid", &pid) || pid <= 0 || kill((pid_t)pid, 0) != 0) return 3;
        return 1;
    }
    sscanf(b, "%*s %ld", at);
    return !strcmp(w, "done") ? 2 : !strcmp(w, "stopped") ? 3 : 4;
}
static int bs_results(struct bs_row *r, int max)
{
    char *f = read_file("/tmp/u60-bandscan.res");
    int n = 0;
    if (!f) return 0;
    for (char *save = NULL, *ln = strtok_r(f, "\n", &save); ln && n < max; ln = strtok_r(NULL, "\n", &save)) {
        char st[8] = "";
        memset(&r[n], 0, sizeof r[n]);
        if (sscanf(ln, "%7s %7s %d %11s %d", r[n].band, st, &r[n].rsrp, r[n].sinr, &r[n].pci) >= 2) {
            r[n].ok = !strcmp(st, "ok");
            n++;
        }
    }
    free(f);
    return n;
}
static int bs_cmp(const void *a, const void *b)
{
    const struct bs_row *x = a, *y = b;
    if (x->ok != y->ok) return y->ok - x->ok;
    return y->rsrp - x->rsrp;
}
static const char *bs_col(int r) { return r > -100 ? "good" : r > -110 ? "mid" : "bad"; }

static const char *bs_entry_html(void)        /* bottom of the 附近基站 page */
{
    static char b[900];
    char scan[8]; int idx, tot; long at;
    int st = bs_state(scan, sizeof scan, &idx, &tot, &at);
    if (st == 1)
        snprintf(b, sizeof b, "<a href='act:sub:bandscan.html' class='card bsnow'><span class='bsnt'>正在扫描所有频段 · %s</span><span class='k bsr'>查看 ›</span></a>", scan);
    else if (g_bs_confirm)
        snprintf(b, sizeof b, "<div class='card bscf'><div class='bscft'>扫描期间会断网约 1 分钟</div>"
                 "<div class='k bscfk'>依次试 8 个频段，扫完自动恢复原来的设置。</div>"
                 "<div class='blg bscfb'><a href='act:bs:cancel' class='blc'><b>取消</b></a><a href='act:bs:start' class='blc on'><b>开始扫描</b></a></div></div>");
    else
        snprintf(b, sizeof b, "<a href='act:bs:ask' class='bsbtn'>扫描所有频段</a>"
                 "<div class='k bshint'>查看附近还有哪些 5G 频段可用 · 约 1 分钟%s</div>",
                 st >= 2 && st <= 3 ? "　<a href='act:sub:bandscan.html' class='bslast'>上次结果 ›</a>" : "");
    return b;
}

static const char *bs_page_html(void)         /* 扫描所有频段 page: progress or results */
{
    static char b[6000];
    char scan[8], cur[16] = ""; int idx, tot; long at;
    int st = bs_state(scan, sizeof scan, &idx, &tot, &at);
    struct bs_row r[12]; int n = bs_results(r, 12);
    read_line_path("/tmp/u60-bandscan.cur", cur, sizeof cur);
    int o = 0;
    #define AP(...) do { if (o < (int)sizeof b) o += snprintf(b + o, sizeof b - o, __VA_ARGS__); } while (0)
    if (st == 1) {
        long el = (long)time(NULL) - at; if (el < 0) el = 0; if (el > 10) el = 10;
        int pct = tot ? (int)(((idx - 1) + el / 10.0) * 100 / tot) : 0; if (pct > 100) pct = 100;
        int left = (tot - idx + 1) * 9 - (int)el; if (left < 3) left = 3;
        AP("<div class='card bsprog'><div class='bsph'><span class='bspt'>正在扫描 %s</span><span class='k bsr'>约剩 %d 秒</span></div>"
           "<span class='bsbar'><i style='width:%d%%'></i></span><div class='k bspn'>扫描中网络会断断续续，完成后自动恢复</div></div>",
           scan, left, pct < 3 ? 3 : pct);
        AP("<div class='card bslist'>");
        char orig[256] = ""; read_line_path("/tmp/u60-bandscan.orig", orig, sizeof orig);
        for (int k = 0; BS_BANDS[k]; k++) {
            char pat[8]; snprintf(pat, sizeof pat, ",%s,", BS_BANDS[k]);
            char wrapped[260]; snprintf(wrapped, sizeof wrapped, ",%s,", orig);
            if (orig[0] && !strstr(wrapped, pat)) continue;
            char bn[8]; snprintf(bn, sizeof bn, "n%s", BS_BANDS[k]);
            int done = -1;
            for (int j = 0; j < n; j++) if (!strcmp(r[j].band, bn)) done = j;
            if (done >= 0 && r[done].ok)
                AP("<div class='bsr2'><span class='n bsb'>%s</span><span class='bsok'>√</span><span class='n bsv %s'>%d</span><span class='k'> dBm · SINR %s</span></div>",
                   bn, bs_col(r[done].rsrp), r[done].rsrp, r[done].sinr);
            else if (done >= 0)
                AP("<div class='bsr2 mu'><span class='n bsb'>%s</span><span class='k'>√ 未发现</span></div>", bn);
            else if (!strcmp(bn, scan))
                AP("<div class='bsr2'><span class='n bsb'>%s</span><span class='teal'>扫描中…</span></div>", bn);
            else
                AP("<div class='bsr2 mu'><span class='n bsb'>%s</span><span class='k'>等待</span></div>", bn);
        }
        AP("</div><a href='act:bs:stop' class='bsbtn ghost'>停止扫描</a>");
        return b;
    }
    if (st == 0 || n == 0) {
        AP("<div class='card'><div class='k'>%s</div></div>", st == 4 ? "扫描没能开始：读不到当前网络信息" : "还没有扫描结果");
        AP("<a href='act:bs:ask' class='bsbtn'>扫描所有频段</a>");
        if (g_bs_confirm) AP("%s", bs_entry_html());
        return b;
    }
    qsort(r, n, sizeof r[0], bs_cmp);
    struct tm tm; time_t tt = (time_t)at; localtime_r(&tt, &tm);
    if (g_bs_confirm)
        AP("%s", bs_entry_html());
    else
        AP("<div class='bshd'><span class='k'>%02d:%02d 扫描%s · 已恢复原设置</span><a href='act:bs:ask' class='bsre'>重新扫描 ›</a></div>",
           tm.tm_hour, tm.tm_min, st == 3 ? "（中途停止）" : "");
    AP("<div class='card bslist'>");
    int best = -1;
    for (int j = 0; j < n; j++) if (r[j].ok) { best = j; break; }
    for (int j = 0; j < n; j++) {
        if (r[j].ok) {
            int w = (r[j].rsrp + 125) * 32 / 10; if (w < 8) w = 8; if (w > 100) w = 100;
            int locked = g_bs_locked[0] && !strcmp(g_bs_locked, r[j].band);
            /* line 1: values; line 2: strength bar + tags (tags on line 1 ran into the button) */
            AP("<div class='bsrow'><span class='n bsb'>%s</span><span class='bsmid'><span class='bsl1'><span class='n bsv %s'>%d</span><span class='k'> dBm · SINR %s</span></span>"
               "<span class='bsl2'><span class='bsbar sm'><i class='%s' style='width:%d%%'></i></span>%s%s</span></span>"
               "<a href='act:bs:lock:%s' class='bslk%s'>%s</a></div>",
               r[j].band, bs_col(r[j].rsrp), r[j].rsrp, r[j].sinr,
               bs_col(r[j].rsrp), w,
               j == best ? "<span class='bstag best'>最佳</span>" : "",
               !strcmp(cur, r[j].band) ? "<span class='bstag cur'>当前</span>" : "",
               r[j].band + 1, locked ? " on" : "", locked ? "已锁" : "锁定");
        } else
            AP("<div class='bsr2 mu'><span class='n bsb'>%s</span><span class='k'>未发现</span></div>", r[j].band);
    }
    AP("</div>");
    #undef AP
    return b;
}

/* SMS text -> HTML: escaped, line breaks kept, links and 4-8 digit codes in teal
 * (display only; nothing on this screen opens them). */
static void sms_body_html(char *out, size_t cap, const char *t)
{
    size_t o = 0;
    /* digits are only a "code" when the message says so (else years, model numbers… light up) */
    int codes = strstr(t, "验证码") || strstr(t, "校验码") || strstr(t, "动态码") || strstr(t, "确认码") ||
                strstr(t, "code") || strstr(t, "Code") || strstr(t, "CODE");
    #define PUT(str) do { const char *q_ = (str); while (*q_ && o + 1 < cap) out[o++] = *q_++; } while (0)
    while (*t && o + 32 < cap) {
        /* a link: "http(s)://…" or a bare "host.tld/path" run (no scheme, as in carrier SMS) */
        {
            int n = 0, dot = 0, slash = 0;
            while (t[n] && (unsigned char)t[n] < 0x80 && (isalnum((unsigned char)t[n]) || strchr(".:/?=&_-%#+~", t[n]))) {
                if (t[n] == '.') dot = 1;
                if (t[n] == '/') slash = 1;
                n++;
            }
            int lead = isalpha((unsigned char)*t);
            if (n >= 8 && lead && dot && slash) {
                PUT("<span class='sdl'>");
                for (int k = 0; k < n && o + 16 < cap; k++) {
                    char c[8]; html_esc(c, sizeof c, (char[2]){ t[k], 0 }); PUT(c);
                }
                PUT("</span>");
                t += n;
                continue;
            }
        }
        if (*t >= '0' && *t <= '9') {
            int n = 0; while (t[n] >= '0' && t[n] <= '9') n++;
            int edge = !(t[n] >= 'A' && t[n] <= 'z') && !(o > 0 && ((out[o - 1] >= 'A' && out[o - 1] <= 'Z') || (out[o - 1] >= 'a' && out[o - 1] <= 'z')));
            if (codes && n >= 4 && n <= 8 && edge) { PUT("<span class='sdl'>"); for (int k = 0; k < n; k++) out[o++] = t[k]; PUT("</span>"); }
            else for (int k = 0; k < n && o + 1 < cap; k++) out[o++] = t[k];
            t += n;
            continue;
        }
        if (*t == '\n') { PUT("<br>"); t++; continue; }
        if (*t == '\r') { t++; continue; }
        if (*t == '&') { PUT("&amp;"); t++; continue; }
        if (*t == '<') { PUT("&lt;"); t++; continue; }
        if (*t == '>') { PUT("&gt;"); t++; continue; }
        {   /* keep a closing CJK punctuation mark on the same line as the character before it */
            unsigned char c0 = (unsigned char)*t;
            int L = c0 >= 0xF0 ? 4 : c0 >= 0xE0 ? 3 : c0 >= 0xC0 ? 2 : 1;
            static const char *PN[] = { "，", "。", "、", "；", "：", "！", "？", "）", "】", "」", "』", "》", "”", "’", "…", NULL };
            int pl = 0;
            for (int k = 0; PN[k]; k++) if (!strncmp(t + L, PN[k], strlen(PN[k]))) { pl = (int)strlen(PN[k]); break; }
            if (pl && *t != '\n') {
                PUT("<span class='nw'>");
                for (int k = 0; k < L + pl && o + 1 < cap; k++) out[o++] = t[k];
                PUT("</span>");
                t += L + pl;
                continue;
            }
            for (int k = 0; k < L && t[k] && o + 1 < cap; k++) out[o++] = t[k];
            t += L;
        }
    }
    out[o] = 0;
    #undef PUT
}

/* 流量套餐 summary for the network card / lock screen / settings page:
 * right = "上限 2000 GB · 3%" | "已超出 · 104%" | "不限量"; bar = progress markup (capped only). */
static int plan_pct(void)
{
    if (!g_plan_on || g_plan_gb <= 0 || !g_wd.valid) return -1;
    return (int)(g_wd.mon * 100 / ((long long)g_plan_gb * 1073741824LL));
}
static void plan_text(char *right, size_t rc, char *bar, size_t bc, const char *barcls)
{
    int pct = plan_pct();
    bar[0] = 0;
    if (pct < 0) { snprintf(right, rc, "不限量"); return; }
    const char *c = pct >= 100 ? "bad" : pct >= 80 ? "mid" : "teal";
    if (pct >= 100) snprintf(right, rc, "已超出 · %d%%", pct);
    else snprintf(right, rc, "上限 %d GB · %d%%", g_plan_gb, pct);
    int w = pct > 100 ? 100 : pct < 2 ? 2 : pct;
    snprintf(bar, bc, "<span class='%s'><i class='%s' style='width:%d%%'></i></span>", barcls, c, w);
}


/* 已连接设备：前几台的名字（按 WiFi 关联过滤），用于控制中心设备条 */
static void client_names(char *out, size_t cap, const devui_data_t *d, int max)
{
    int o = 0, shown = 0;
    out[0] = 0;
    for (int k = 0; k < d->client_n && shown < max; k++) {
        if (g_assoc_macs[0] && !mac_assoc(d->client[k].mac)) continue;
        if (!d->client[k].name[0]) continue;
        char e[96];
        html_esc(e, sizeof e, d->client[k].name);
        o += snprintf(out + o, cap > (size_t)o ? cap - o : 0, "%s%s", shown ? " · " : "", e);
        shown++;
    }
}

/* 5G / 2.4G 各几台（iw station dump，5 秒一次） */
static void sta_band_text(char *out, size_t cap)
{
    int n5 = 0, n24 = 0;
    sta_refresh();
    for (int i = 0; i < g_sta_n; i++) { if (!strcmp(g_sta[i].band, "5G")) n5++; else n24++; }
    if (n5 && n24) snprintf(out, cap, "5G %d 台 · 2.4G %d 台", n5, n24);
    else if (n5) snprintf(out, cap, "都在 5G");
    else if (n24) snprintf(out, cap, "都在 2.4G");
    else snprintf(out, cap, "WiFi 暂无设备");
}

/* 控制中心第六格：已连接设备，副标题是各频段台数 */
static const char *rl_tile_html(void)
{
    static char h[256];
    char bands[64];
    sta_band_text(bands, sizeof bands);
    snprintf(h, sizeof h, "<a href='act:sub:clients.html' class='card tile'><span class='th'>已连接设备</span>"
             "<span class='ts'>%s</span></a>", bands);
    return h;
}

static int build_kv(struct kv *t, const char *path)
{
    int is_cellinfo = path_is_signal_detail(path);
    int is_signalhome = path_is_signal_home(path);
    int is_charts = path && strstr(path, "charts.html") != NULL;
    g_phase++;

    static char s_time[8], s_bat[8], s_rsrp[12], s_rsrq[12], s_sinr[12], s_bw[12];
    static char s_cellid[20], s_pci[12], s_clients[8], s_up[24], s_rxs[20], s_txs[20];
    static char s_rxb[16], s_txb[16], s_cpu[8], s_mem[8], w_rsrp[6], w_rsrq[6], w_sinr[6], w_bw[6];
    static char s_oper[48], s_ssid[64], s_key[64], s_page[8], s_np[8], s_model[64], s_fw[80];
    static char s_qci[8], s_ambr[24], s_sbar[640], s_dots[1024], s_ta[16], s_tadist[24];
    static char s_nrports[64], s_nrbeam[128], s_nrvendor[64], s_sigadvstate[64], s_sigrefresh[16], s_signalcards[10000], s_neighborcards[7000];
    static char s_last_lte_nas[128] = "-";
        static char s_last_nr_nas[128] = "-";
        static char s_last_nrports[64] = "-";
        static char s_last_nrbeam[128] = "-";
        static char s_last_nrvendor[64] = "-";
        static char s_nrrows[4096], s_lterows[4096], s_carriers[9000], s_nr_block[6000], s_lte_block[5000], s_sigcards[11000], s_gen[8];

    static devui_data_t d;
    static struct signal_bundle sig;
    int ta = -1;
    if (!data_refresh(&d)) memset(&d, 0, sizeof d);
    /* battery %: read the gauge directly. idle-guard freezes zwrt-datad a minute
     * after the screen goes dark, so d.bat_percent still holds the value from
     * then (e.g. 100 % before unplugging) and the first frames after wake would
     * show it until datad catches up. Same number as zwrt_bsp.battery. */
    { long cap; if (read_long_path("/sys/class/power_supply/battery/capacity", &cap)) d.bat_percent = (int)cap; }
    if (!d.wifi_key[0] && !strstr(d.wifi_enc, "none")) wifi_key_fallback(d.wifi_ssid, d.wifi_key, sizeof d.wifi_key);
    g_charging = d.charger_connect;
    snprintf(s_page, sizeof s_page, "%d", g_cur + 1);
    snprintf(s_np, sizeof s_np, "%d", g_npages);

    time_t now = time(NULL); struct tm tmv; localtime_r(&now, &tmv);
    if (now != h_last) { hist_push(&d); h_last = now; }   /* sample once per second */
    snprintf(s_time, sizeof s_time, "%02d:%02d", tmv.tm_hour, tmv.tm_min);
    snprintf(s_sigrefresh, sizeof s_sigrefresh, "%02d:%02d:%02d",
             tmv.tm_hour, tmv.tm_min, tmv.tm_sec);
    snprintf(s_bat, sizeof s_bat, "%d", d.bat_percent);
    snprintf(s_rsrp, sizeof s_rsrp, "%d", d.nr_rsrp);
    snprintf(s_rsrq, sizeof s_rsrq, "%d", d.nr_rsrq);
    snprintf(s_sinr, sizeof s_sinr, "%s", d.nr_snr[0] ? d.nr_snr : "-");
    snprintf(s_bw, sizeof s_bw, "%s", d.nr_bw[0] ? d.nr_bw : "-");
    if (g_show_cellid) snprintf(s_cellid, sizeof s_cellid, "%ld", d.nr_cell_id);
    else               strcpy(s_cellid, "********");
    snprintf(s_pci, sizeof s_pci, "%d", d.nr_pci);
    snprintf(s_clients, sizeof s_clients, "%d", d.clients_total);
    fmt_uptime(s_up, sizeof s_up, d.uptime);
    fmt_speed_u(s_rxs, sizeof s_rxs, d.rx_speed, g_speed_bits);
    fmt_speed_u(s_txs, sizeof s_txs, d.tx_speed, g_speed_bits);
    fmt_bytes(s_rxb, sizeof s_rxb, d.rx_bytes);
    fmt_bytes(s_txb, sizeof s_txb, d.tx_bytes);
    snprintf(s_cpu, sizeof s_cpu, "%ld", d.cpu_temp);
    snprintf(s_mem, sizeof s_mem, "%ld", d.mem_used_pct);
    snprintf(s_oper, sizeof s_oper, "%s", d.operator_name[0] ? d.operator_name : "--");
    html_esc(s_ssid, sizeof s_ssid, d.wifi_ssid[0] ? d.wifi_ssid : "-");
    if (!d.wifi_key[0]) strcpy(s_key, "-");
    else if (g_show_key) html_esc(s_key, sizeof s_key, d.wifi_key);
    else { int kn = (int)strlen(d.wifi_key); if (kn > 16) kn = 16; s_key[0] = 0;
           for (int k = 0; k < kn; k++) strcat(s_key, "•"); }
    snprintf(s_model, sizeof s_model, "%s", d.model[0] ? d.model : "-");
    snprintf(s_fw, sizeof s_fw, "%s", d.fw[0] ? d.fw : "-");
    if (is_cellinfo && !g_sig_read) {
        snprintf(s_ta, sizeof s_ta, "已关闭");
        snprintf(s_tadist, sizeof s_tadist, "已关闭");
    } else if (is_cellinfo && fetch_lte_ta(&ta)) {
        snprintf(s_ta, sizeof s_ta, "%d", ta);
        fmt_ta_distance(s_tadist, sizeof s_tadist, ta, 78.12);
    } else if (is_cellinfo) {
        snprintf(s_ta, sizeof s_ta, "-");
        snprintf(s_tadist, sizeof s_tadist, "-");
    } else {
        snprintf(s_ta, sizeof s_ta, "-");
        snprintf(s_tadist, sizeof s_tadist, "-");
    }
    signal_settings_summary(s_sigadvstate, sizeof s_sigadvstate);
    snprintf(w_rsrp, sizeof w_rsrp, "%d", clampi((d.nr_rsrp + 120) * 2, 3, 100));
    snprintf(w_rsrq, sizeof w_rsrq, "%d", clampi((d.nr_rsrq + 20) * 100 / 17, 3, 100));
    snprintf(w_sinr, sizeof w_sinr, "%d", clampi((int)((atof(d.nr_snr) + 10) * 100 / 40), 3, 100));
    snprintf(w_bw, sizeof w_bw, "%d", clampi(atoi(d.nr_bw), 3, 100));

    /* qci / ambr (from modem qos): unified Mbps, e.g. 3000/200 Mbps */
    if (d.qci > 0) snprintf(s_qci, sizeof s_qci, "%d", d.qci);
    else           snprintf(s_qci, sizeof s_qci, "-");
    if (d.ambr_dl > 0.0 || d.ambr_ul > 0.0) {
        char dl[12], ul[12];
        if (d.ambr_dl > 0.0) snprintf(dl, sizeof dl, "%.0f", d.ambr_dl);
        else                 snprintf(dl, sizeof dl, "-");
        if (d.ambr_ul > 0.0) snprintf(ul, sizeof ul, "%.0f", d.ambr_ul);
        else                 snprintf(ul, sizeof ul, "-");
        snprintf(s_ambr, sizeof s_ambr, "%s/%s Mbps", dl, ul);
    } else {
        snprintf(s_ambr, sizeof s_ambr, "-");
    }

    /* ---- per-carrier display + generation badge ----
     * nrca group: idx,pci,?,band,arfcn,bw,?,rsrp,rsrq,sinr,rssi
     * lteca is seen in both legacy 5-field and newer 11-field variants.
     * Some firmwares expose LTE SCC signal details separately via ltecasig. */
    int is_endc = strstr(d.net_type, "ENDC") || strstr(d.net_type, "EN-DC");
    int is_nsa  = strstr(d.net_type, "NSA") != NULL;
    int is_sa   = strstr(d.net_type, "SA") && !is_nsa;
    int is_lte  = !is_nsa && !is_sa && (strstr(d.net_type, "LTE") || strstr(d.net_type, "4G"));
    int show_nr  = is_sa || is_nsa || is_endc;
    int show_lte = is_nsa || is_endc || is_lte;
    int show_nr_nas = is_sa;
    int nr_cc = 0, nr_bw = 0, lte_cc = 0, lte_bw = 0;
    int nr_show_cc = 0, nr_show_bw = 0, lte_show_cc = 0, lte_show_bw = 0, no = 0, lo = 0;
    char rp[12] = "-", pc[12] = "-", ac[16] = "-";
    const char *nr_band = d.nr_band[0] ? d.nr_band : d.band;

    signal_bundle_reset(&sig);
    if (signal_live_enabled() && (is_cellinfo || is_signalhome)) {
        /* 有后台线程就等它发布：主线程同步抓会卡 UI 几百毫秒，还和线程共用同一组静态缓冲 */
        if (!signal_async_snapshot(&sig) && !g_signal_async_started) {
            if (fetch_signal_bundle(&sig))
                signal_async_publish(&sig, 1);
        }
    }
    snprintf(s_neighborcards, sizeof s_neighborcards, "%s",
             is_signalhome ? signal_neighbors_html(&sig) : "");

    if (is_cellinfo) {
        char c_lte_rrc[96], c_lte_nas[96], c_nr_rrc[96], c_nr_nas[96];
        char c_lteta[96], c_nrta[96];
        char c_nrports[96], c_nrbeam[96], c_nrservssb[96], c_nrbler[96], c_ltebler[96];
        char c_nrmcs[96], c_nrmod[96], c_nrmimo[96], c_nrlayers[96], c_nrdlgrant[96], c_nrdlrb[96], c_nrulgrant[96], c_nrulrb[96], c_nrpusch[128], c_nrpucch[128];
        char c_ltemcs[96], c_ltemod[96], c_ltegrant[96], c_lterb[96], c_ltepusch[128], c_ltepucch[128];
        char e_lte_rrc[256], e_lte_nas[256], e_nr_rrc[256], e_nr_nas[256];
        char e_lteta[128], e_nrta[128];
        char e_nrports[160], e_nrbeam[256], e_nrservssb[128], e_nrbler[128], e_ltebler[128], e_nrvendor[128];
        char e_nrmcs[128], e_nrmod[128], e_nrmimo[128], e_nrlayers[128], e_nrdlgrant[128], e_nrdlrb[128], e_nrulgrant[128], e_nrulrb[128], e_nrpusch[192], e_nrpucch[192];
        char e_ltemcs[128], e_ltemod[128], e_ltegrant[128], e_lterb[128], e_ltepusch[192], e_ltepucch[192];
        char s_lteta[64], s_nrta[64], s_nrservssb[64], s_nrbler[64], s_ltebler[64];
        char s_nrmcs[64], s_nrmod[64], s_nrmimo[64], s_nrlayers[64], s_nrdlgrant[64], s_nrdlrb[64], s_nrulgrant[64], s_nrulrb[64], s_nrpusch[96], s_nrpucch[96];
        char s_ltemcs[64], s_ltemod[64], s_ltegrant[64], s_lterb[64], s_ltepusch[96], s_ltepucch[96];
        static char s_last_signal_cell_key[64] = "";
        static char s_last_nrservssb[64] = "-";
        static char s_last_nrbler[64] = "-";
        static char s_last_ltebler[64] = "-";
        int so = 0;

        if (signal_value_present(sig.cell_key) &&
            strcmp(sig.cell_key, s_last_signal_cell_key) != 0) {
            snprintf(s_last_signal_cell_key, sizeof s_last_signal_cell_key, "%s", sig.cell_key);
            snprintf(s_last_nrports, sizeof s_last_nrports, "-");
            snprintf(s_last_nrbeam, sizeof s_last_nrbeam, "-");
            snprintf(s_last_nrservssb, sizeof s_last_nrservssb, "-");
            snprintf(s_last_nrbler, sizeof s_last_nrbler, "-");
            snprintf(s_last_ltebler, sizeof s_last_ltebler, "-");
            snprintf(s_last_nrvendor, sizeof s_last_nrvendor, "-");
        }
        signal_value_keep_last(sig.lte_nas, sizeof sig.lte_nas, s_last_lte_nas, sizeof s_last_lte_nas);
        signal_value_keep_last(sig.nr_nas, sizeof sig.nr_nas, s_last_nr_nas, sizeof s_last_nr_nas);
        if (!signal_live_enabled()) {
            snprintf(s_lteta, sizeof s_lteta, "已关闭");
            snprintf(s_nrta, sizeof s_nrta, "已关闭");
            snprintf(s_nrports, sizeof s_nrports, "已关闭");
            snprintf(s_nrbeam, sizeof s_nrbeam, "已关闭");
            snprintf(s_nrservssb, sizeof s_nrservssb, "已关闭");
            snprintf(s_nrbler, sizeof s_nrbler, "已关闭");
            snprintf(s_ltebler, sizeof s_ltebler, "已关闭");
            snprintf(s_nrmcs, sizeof s_nrmcs, "已关闭");
            snprintf(s_nrmod, sizeof s_nrmod, "已关闭");
            snprintf(s_nrmimo, sizeof s_nrmimo, "已关闭");
            snprintf(s_nrlayers, sizeof s_nrlayers, "已关闭");
            snprintf(s_nrdlgrant, sizeof s_nrdlgrant, "已关闭");
            snprintf(s_nrdlrb, sizeof s_nrdlrb, "已关闭");
            snprintf(s_nrulgrant, sizeof s_nrulgrant, "已关闭");
            snprintf(s_nrulrb, sizeof s_nrulrb, "已关闭");
            snprintf(s_nrpusch, sizeof s_nrpusch, "已关闭");
            snprintf(s_nrpucch, sizeof s_nrpucch, "已关闭");
            snprintf(s_ltemcs, sizeof s_ltemcs, "已关闭");
            snprintf(s_ltemod, sizeof s_ltemod, "已关闭");
            snprintf(s_ltegrant, sizeof s_ltegrant, "已关闭");
            snprintf(s_lterb, sizeof s_lterb, "已关闭");
            snprintf(s_ltepusch, sizeof s_ltepusch, "已关闭");
            snprintf(s_ltepucch, sizeof s_ltepucch, "已关闭");
            snprintf(s_nrvendor, sizeof s_nrvendor, "-");
        } else {
            snprintf(s_lteta, sizeof s_lteta, "%s", sig.lte_ta);
            snprintf(s_nrta, sizeof s_nrta, "%s", sig.nr_ta);
            snprintf(s_nrports, sizeof s_nrports, "%s", sig.nr_ports);
            snprintf(s_nrbeam, sizeof s_nrbeam, "%s", sig.nr_beam);
            snprintf(s_nrservssb, sizeof s_nrservssb, "-");
            snprintf(s_nrbler, sizeof s_nrbler, "-");
            snprintf(s_ltebler, sizeof s_ltebler, "-");
            snprintf(s_nrmcs, sizeof s_nrmcs, "%s", sig.nr_mcs);
            snprintf(s_nrmod, sizeof s_nrmod, "%s", sig.nr_modulation);
            snprintf(s_nrmimo, sizeof s_nrmimo, "%s", sig.nr_mimo);
            snprintf(s_nrlayers, sizeof s_nrlayers, "%s", sig.nr_layers);
            snprintf(s_nrdlgrant, sizeof s_nrdlgrant, "%s", sig.nr_dl_grants);
            snprintf(s_nrdlrb, sizeof s_nrdlrb, "%s", sig.nr_dl_rb);
            snprintf(s_nrulgrant, sizeof s_nrulgrant, "%s", sig.nr_ul_grants);
            snprintf(s_nrulrb, sizeof s_nrulrb, "%s", sig.nr_ul_rb);
            snprintf(s_nrpusch, sizeof s_nrpusch, "%s", sig.nr_pusch);
            snprintf(s_nrpucch, sizeof s_nrpucch, "%s", sig.nr_pucch);
            snprintf(s_ltemcs, sizeof s_ltemcs, "%s", sig.lte_mcs);
            snprintf(s_ltemod, sizeof s_ltemod, "%s", sig.lte_modulation);
            snprintf(s_ltegrant, sizeof s_ltegrant, "%s", sig.lte_grants);
            snprintf(s_lterb, sizeof s_lterb, "%s", sig.lte_rb);
            snprintf(s_ltepusch, sizeof s_ltepusch, "%s", sig.lte_pusch);
            snprintf(s_ltepucch, sizeof s_ltepucch, "%s", sig.lte_pucch);
            snprintf(s_nrservssb, sizeof s_nrservssb, "%s", sig.nr_serving_ssb);
            snprintf(s_nrbler, sizeof s_nrbler, "%s", sig.nr_bler);
            snprintf(s_ltebler, sizeof s_ltebler, "%s", sig.lte_bler);
            snprintf(s_nrvendor, sizeof s_nrvendor, "%s", sig.nr_vendor);
            if (!signal_value_present(sig.nr_ta))
                snprintf(s_nrta, sizeof s_nrta, "等待ML1");
            if (!signal_value_present(sig.lte_ta))
                snprintf(s_lteta, sizeof s_lteta, "等待ML1");
            signal_value_keep_last(s_nrports, sizeof s_nrports, s_last_nrports, sizeof s_last_nrports);
            signal_value_keep_last(s_nrbeam, sizeof s_nrbeam, s_last_nrbeam, sizeof s_last_nrbeam);
            signal_value_keep_last(s_nrservssb, sizeof s_nrservssb,
                                   s_last_nrservssb, sizeof s_last_nrservssb);
            signal_value_keep_last(s_nrbler, sizeof s_nrbler,
                                   s_last_nrbler, sizeof s_last_nrbler);
            signal_value_keep_last(s_ltebler, sizeof s_ltebler,
                                   s_last_ltebler, sizeof s_last_ltebler);
            signal_value_keep_last(s_nrvendor, sizeof s_nrvendor,
                                   s_last_nrvendor, sizeof s_last_nrvendor);
            if (!strcmp(s_nrports, "-"))
                snprintf(s_nrports, sizeof s_nrports, "等待RRC CSI-RS");
            if (!strcmp(s_nrservssb, "-"))
                snprintf(s_nrservssb, sizeof s_nrservssb, "等待ML1");
            if (!strcmp(s_nrbeam, "-"))
                snprintf(s_nrbeam, sizeof s_nrbeam, "等待RRC配置");
            if (!strcmp(s_nrbler, "-"))
                snprintf(s_nrbler, sizeof s_nrbler, "等待PDSCH");
            if (!strcmp(s_ltebler, "-"))
                snprintf(s_ltebler, sizeof s_ltebler, "等待PDSCH");
            if (!strcmp(s_nrmcs, "-"))
                snprintf(s_nrmcs, sizeof s_nrmcs, "等待PDSCH");
            if (!strcmp(s_nrmod, "-"))
                snprintf(s_nrmod, sizeof s_nrmod, "等待PDSCH");
            if (!strcmp(s_nrmimo, "-"))
                snprintf(s_nrmimo, sizeof s_nrmimo, "等待PDSCH");
            if (!strcmp(s_nrlayers, "-"))
                snprintf(s_nrlayers, sizeof s_nrlayers, "等待PDSCH");
            if (!signal_value_present(sig.nr_dl_grants))
                snprintf(s_nrdlgrant, sizeof s_nrdlgrant, "等待PDSCH");
            if (!signal_value_present(sig.nr_dl_rb))
                snprintf(s_nrdlrb, sizeof s_nrdlrb, "等待PDSCH");
            if (!signal_value_present(sig.nr_ul_grants))
                snprintf(s_nrulgrant, sizeof s_nrulgrant, "等待UL调度");
            if (!signal_value_present(sig.nr_ul_rb))
                snprintf(s_nrulrb, sizeof s_nrulrb, "等待UL调度");
            if (!strcmp(s_nrpusch, "-"))
                snprintf(s_nrpusch, sizeof s_nrpusch, "等待UL功控");
            if (!strcmp(s_nrpucch, "-"))
                snprintf(s_nrpucch, sizeof s_nrpucch, "等待UL功控");
            if (!strcmp(s_ltemcs, "-"))
                snprintf(s_ltemcs, sizeof s_ltemcs, "等待PDSCH");
            if (!strcmp(s_ltemod, "-"))
                snprintf(s_ltemod, sizeof s_ltemod, "等待PDSCH");
            if (!signal_value_present(sig.lte_grants))
                snprintf(s_ltegrant, sizeof s_ltegrant, "等待PDSCH");
            if (!signal_value_present(sig.lte_rb))
                snprintf(s_lterb, sizeof s_lterb, "等待PDSCH");
            if (!strcmp(s_ltepusch, "-"))
                snprintf(s_ltepusch, sizeof s_ltepusch, "等待PUSCH");
            if (!strcmp(s_ltepucch, "-"))
                snprintf(s_ltepucch, sizeof s_ltepucch, "等待PUCCH");
            if (signal_value_present(sig.ta)) {
                char *endp = NULL;
                long ta_val = strtol(sig.ta, &endp, 10);
                if (endp && endp != sig.ta && ta_val >= 0 && ta_val <= 65535) {
                    snprintf(s_ta, sizeof s_ta, "%ld", ta_val);
                    fmt_ta_distance(s_tadist, sizeof s_tadist, (int)ta_val,
                                    ta_unit_m_for_signal(&d, &sig, (int)ta_val));
                } else {
                    snprintf(s_ta, sizeof s_ta, "%.15s", sig.ta);
                    snprintf(s_tadist, sizeof s_tadist, "-");
                }
            }
        }
        signal_ui_compact(c_lte_rrc, sizeof c_lte_rrc, sig.lte_rrc);
        signal_ui_compact(c_lte_nas, sizeof c_lte_nas, sig.lte_nas);
        signal_ui_compact(c_nr_rrc, sizeof c_nr_rrc, sig.nr_rrc);
        signal_ui_compact(c_nr_nas, sizeof c_nr_nas, sig.nr_nas);
        signal_ui_compact(c_lteta, sizeof c_lteta, s_lteta);
        signal_ui_compact(c_nrta, sizeof c_nrta, s_nrta);
        signal_ui_compact(c_nrports, sizeof c_nrports, s_nrports);
        signal_ui_compact(c_nrbeam, sizeof c_nrbeam, s_nrbeam);
        signal_ui_compact(c_nrservssb, sizeof c_nrservssb, s_nrservssb);
        signal_bler_compact(c_nrbler, sizeof c_nrbler, s_nrbler);
        signal_bler_compact(c_ltebler, sizeof c_ltebler, s_ltebler);
        signal_ui_compact(c_nrmcs, sizeof c_nrmcs, s_nrmcs);
        signal_ui_compact(c_nrmod, sizeof c_nrmod, s_nrmod);
        signal_ui_compact(c_nrmimo, sizeof c_nrmimo, s_nrmimo);
        signal_ui_compact(c_nrlayers, sizeof c_nrlayers, s_nrlayers);
        signal_ui_compact(c_nrdlgrant, sizeof c_nrdlgrant, s_nrdlgrant);
        signal_ui_compact(c_nrdlrb, sizeof c_nrdlrb, s_nrdlrb);
        signal_ui_compact(c_nrulgrant, sizeof c_nrulgrant, s_nrulgrant);
        signal_ui_compact(c_nrulrb, sizeof c_nrulrb, s_nrulrb);
        signal_ui_compact(c_nrpusch, sizeof c_nrpusch, s_nrpusch);
        signal_ui_compact(c_nrpucch, sizeof c_nrpucch, s_nrpucch);
        signal_ui_compact(c_ltemcs, sizeof c_ltemcs, s_ltemcs);
        signal_ui_compact(c_ltemod, sizeof c_ltemod, s_ltemod);
        signal_ui_compact(c_ltegrant, sizeof c_ltegrant, s_ltegrant);
        signal_ui_compact(c_lterb, sizeof c_lterb, s_lterb);
        signal_ui_compact(c_ltepusch, sizeof c_ltepusch, s_ltepusch);
        signal_ui_compact(c_ltepucch, sizeof c_ltepucch, s_ltepucch);
        html_esc(e_lte_rrc, sizeof e_lte_rrc, c_lte_rrc);
        html_esc(e_lte_nas, sizeof e_lte_nas, c_lte_nas);
        html_esc(e_nr_rrc, sizeof e_nr_rrc, c_nr_rrc);
        html_esc(e_nr_nas, sizeof e_nr_nas, c_nr_nas);
        html_esc(e_lteta, sizeof e_lteta, c_lteta);
        html_esc(e_nrta, sizeof e_nrta, c_nrta);
        html_esc(e_nrports, sizeof e_nrports, c_nrports);
        html_esc(e_nrbeam, sizeof e_nrbeam, c_nrbeam);
        html_esc(e_nrservssb, sizeof e_nrservssb, c_nrservssb);
        html_esc(e_nrbler, sizeof e_nrbler, c_nrbler);
        html_esc(e_ltebler, sizeof e_ltebler, c_ltebler);
        html_esc(e_nrmcs, sizeof e_nrmcs, c_nrmcs);
        html_esc(e_nrmod, sizeof e_nrmod, c_nrmod);
        html_esc(e_nrmimo, sizeof e_nrmimo, c_nrmimo);
        html_esc(e_nrlayers, sizeof e_nrlayers, c_nrlayers);
        html_esc(e_nrdlgrant, sizeof e_nrdlgrant, c_nrdlgrant);
        html_esc(e_nrdlrb, sizeof e_nrdlrb, c_nrdlrb);
        html_esc(e_nrulgrant, sizeof e_nrulgrant, c_nrulgrant);
        html_esc(e_nrulrb, sizeof e_nrulrb, c_nrulrb);
        html_esc(e_nrpusch, sizeof e_nrpusch, c_nrpusch);
        html_esc(e_nrpucch, sizeof e_nrpucch, c_nrpucch);
        html_esc(e_ltemcs, sizeof e_ltemcs, c_ltemcs);
        html_esc(e_ltemod, sizeof e_ltemod, c_ltemod);
        html_esc(e_ltegrant, sizeof e_ltegrant, c_ltegrant);
        html_esc(e_lterb, sizeof e_lterb, c_lterb);
        html_esc(e_ltepusch, sizeof e_ltepusch, c_ltepusch);
        html_esc(e_ltepucch, sizeof e_ltepucch, c_ltepucch);
        html_esc(e_nrvendor, sizeof e_nrvendor, s_nrvendor);
        s_signalcards[0] = 0;
        so += snprintf(s_signalcards + so, sizeof s_signalcards - so,
                       "<div class='card'><div class='title'>基站品牌识别</div><table class='sigtab'>"
                       "<tr><td class='kv-l'>刷新时间</td><td class='val'>%s</td></tr>"
                       "<tr><td class='kv-l'>识别结果</td><td class='val sm'>%s</td></tr>"
                       "<tr><td class='kv-l'>TA</td><td class='val'>%s</td></tr>"
                       "<tr><td class='kv-l'>估算距离</td><td class='val'>%s</td></tr>"
                       "</table></div>",
                       s_sigrefresh, e_nrvendor, s_ta, s_tadist);
        if (show_nr) {
            if (show_nr_nas) {
                so += snprintf(s_signalcards + so, sizeof s_signalcards - so,
                               "<div class='card'><div class='title'>NR 信令 <span class='r muted'>5G</span></div><table class='sigtab'>"
                               "<tr><td class='kv-l'>最近 RRC</td><td class='val sm'>%s</td></tr>"
                               "<tr><td class='kv-l'>最近 NAS</td><td class='val sm'>%s</td></tr>"
                               "<tr><td class='kv-l'>TA</td><td class='val sm'>%s</td></tr>"
                               "<tr><td class='kv-l'>MCS</td><td class='val sm'>%s</td></tr>"
                               "<tr><td class='kv-l'>调制</td><td class='val sm'>%s</td></tr>"
                               "<tr><td class='kv-l'>MIMO</td><td class='val sm'>%s</td></tr>"
                               "<tr><td class='kv-l'>layers</td><td class='val sm'>%s</td></tr>"
                               "<tr><td class='kv-l'>DL/UL Grant</td><td class='val sm'>%s/%s</td></tr>"
                               "<tr><td class='kv-l'>DL/UL RB</td><td class='val sm'>%s/%s</td></tr>"
                               "<tr><td class='kv-l'>BLER</td><td class='val sm'>%s</td></tr>"
                               "<tr><td class='kv-l'>PUSCH</td><td class='val sm'>%s</td></tr>"
                               "<tr><td class='kv-l'>PUCCH</td><td class='val sm'>%s</td></tr>"
                               "<tr><td class='kv-l'>Ports</td><td class='val sm'>%s</td></tr>"
                               "<tr><td class='kv-l'>SSB Index</td><td class='val sm'>%s</td></tr>"
                               "</table></div>",
                               e_nr_rrc, e_nr_nas, e_nrta, e_nrmcs, e_nrmod, e_nrmimo, e_nrlayers,
                               e_nrdlgrant, e_nrulgrant, e_nrdlrb, e_nrulrb, e_nrbler,
                               e_nrpusch, e_nrpucch, e_nrports, e_nrservssb);
            } else {
                so += snprintf(s_signalcards + so, sizeof s_signalcards - so,
                               "<div class='card'><div class='title'>NR 信令 <span class='r muted'>5G</span></div><table class='sigtab'>"
                               "<tr><td class='kv-l'>最近 RRC</td><td class='val sm'>%s</td></tr>"
                               "<tr><td class='kv-l'>TA</td><td class='val sm'>%s</td></tr>"
                               "<tr><td class='kv-l'>MCS</td><td class='val sm'>%s</td></tr>"
                               "<tr><td class='kv-l'>调制</td><td class='val sm'>%s</td></tr>"
                               "<tr><td class='kv-l'>MIMO</td><td class='val sm'>%s</td></tr>"
                               "<tr><td class='kv-l'>layers</td><td class='val sm'>%s</td></tr>"
                               "<tr><td class='kv-l'>DL/UL Grant</td><td class='val sm'>%s/%s</td></tr>"
                               "<tr><td class='kv-l'>DL/UL RB</td><td class='val sm'>%s/%s</td></tr>"
                               "<tr><td class='kv-l'>BLER</td><td class='val sm'>%s</td></tr>"
                               "<tr><td class='kv-l'>PUSCH</td><td class='val sm'>%s</td></tr>"
                               "<tr><td class='kv-l'>PUCCH</td><td class='val sm'>%s</td></tr>"
                               "<tr><td class='kv-l'>Ports</td><td class='val sm'>%s</td></tr>"
                               "<tr><td class='kv-l'>SSB Index</td><td class='val sm'>%s</td></tr>"
                               "</table></div>",
                               e_nr_rrc, e_nrta, e_nrmcs, e_nrmod, e_nrmimo, e_nrlayers,
                               e_nrdlgrant, e_nrulgrant, e_nrdlrb, e_nrulrb, e_nrbler, e_nrpusch,
                               e_nrpucch, e_nrports, e_nrservssb);
            }
        }
        if (show_lte) {
            so += snprintf(s_signalcards + so, sizeof s_signalcards - so,
                           "<div class='card'><div class='title'>LTE 信令 <span class='r muted'>4G</span></div><table class='sigtab'>"
                           "<tr><td class='kv-l'>最近 RRC</td><td class='val sm'>%s</td></tr>"
                           "<tr><td class='kv-l'>最近 NAS</td><td class='val sm'>%s</td></tr>"
                           "<tr><td class='kv-l'>TA</td><td class='val sm'>%s</td></tr>"
                           "<tr><td class='kv-l'>MCS</td><td class='val sm'>%s</td></tr>"
                           "<tr><td class='kv-l'>调制</td><td class='val sm'>%s</td></tr>"
                           "<tr><td class='kv-l'>Grant</td><td class='val sm'>%s</td></tr>"
                           "<tr><td class='kv-l'>RB</td><td class='val sm'>%s</td></tr>"
                           "<tr><td class='kv-l'>BLER</td><td class='val sm'>%s</td></tr>"
                           "<tr><td class='kv-l'>PUSCH</td><td class='val sm'>%s</td></tr>"
                           "<tr><td class='kv-l'>PUCCH</td><td class='val sm'>%s</td></tr>"
                           "</table></div>",
                           e_lte_rrc, e_lte_nas, e_lteta, e_ltemcs, e_ltemod,
                           e_ltegrant, e_lterb, e_ltebler, e_ltepusch, e_ltepucch);
        }
        if (so == 0) {
            snprintf(s_signalcards, sizeof s_signalcards,
                     "<div class='card'><div class='title'>信令信息</div><div class='sec'>当前网络没有可展示的 LTE / NR 信令卡片。</div></div>");
            so = (int)strlen(s_signalcards);
        }
    } else {
        snprintf(s_nrports, sizeof s_nrports, "-");
        snprintf(s_nrbeam, sizeof s_nrbeam, "-");
        snprintf(s_nrvendor, sizeof s_nrvendor, "-");
        s_signalcards[0] = 0;
    }

    /* NR carriers: PCell from main fields + nrca SCells */
    s_nrrows[0] = 0;
    if (show_nr && nr_band[0] && d.nr_bw[0]) {
        struct signal_carrier_metric *metric;
        snprintf(rp, sizeof rp, "%d", d.nr_rsrp); snprintf(pc, sizeof pc, "%d", d.nr_pci);
        snprintf(ac, sizeof ac, "%ld", d.nr_channel);
        metric = signal_pick_carrier_metric(sig.nr_carriers, sig.nr_carrier_n, pc, ac, 1);
        no = car_row(s_nrrows, no, sizeof s_nrrows, nr_band, d.nr_bw, ac, pc, rp, d.nr_snr,
                     hsr_freq_hint(d.mcc, ac), metric);
        nr_show_cc = 1; nr_show_bw = atoi(d.nr_bw);
        if (!carrier_is_inactive(rp)) { nr_cc = 1; nr_bw = atoi(d.nr_bw); }
    }
    if (show_nr) {
        char nrca[256]; strncpy(nrca, d.nrca, sizeof nrca - 1); nrca[sizeof nrca - 1] = 0;
        for (char *grp = strtok(nrca, ";"); grp; grp = strtok(NULL, ";")) {
            char g[96]; strncpy(g, grp, sizeof g - 1); g[sizeof g - 1] = 0;
            char *f[12]; int nf = ca_split(g, f, 12);
            if (nf > 5 && atoi(f[5]) > 0) {
                double rpv = (nf > 7 && f[7] && f[7][0]) ? atof(f[7]) : 0.0;
                char bn[12]; snprintf(bn, sizeof bn, "n%s", f[3]);
                const char *nr_ac = nf > 4 ? f[4] : "-";
                const char *nr_pci = nf > 1 ? f[1] : "-";
                struct signal_carrier_metric *metric =
                    signal_pick_carrier_metric(sig.nr_carriers, sig.nr_carrier_n,
                                               nr_pci, nr_ac, 0);
                no = car_row(s_nrrows, no, sizeof s_nrrows, bn, f[5], nr_ac,
                             nr_pci, nf > 7 ? f[7] : "-", nf > 9 ? f[9] : "-",
                             hsr_freq_hint(d.mcc, nr_ac), metric);
                nr_show_cc++;
                nr_show_bw += atoi(f[5]);
                if (rpv > -140.0) { nr_cc++; nr_bw += atoi(f[5]); }
            }
        }
    }
    /* LTE carriers: support both legacy 5-field and newer 11-field groups. */
    s_lterows[0] = 0;
    if (show_lte) {
        char lteca[256]; strncpy(lteca, d.lteca, sizeof lteca - 1); lteca[sizeof lteca - 1] = 0;
        char ltecasig[256]; strncpy(ltecasig, d.ltecasig, sizeof ltecasig - 1); ltecasig[sizeof ltecasig - 1] = 0;
        char *lgrps[8], *sgrps[8];
        int lgn = ca_groups(lteca, lgrps, 8);
        int sgn = ca_groups(ltecasig, sgrps, 8);
        int sig_off = (sgn > 0 && lgn == sgn + 1);   /* ltecasig often contains SCC only */
        for (int gi = 0; gi < lgn; gi++) {
            char *grp = lgrps[gi];
            const char *siggrp = NULL;
            char g[96]; strncpy(g, grp, sizeof g - 1); g[sizeof g - 1] = 0;
            char *f[12]; int nf = ca_split(g, f, 12);
            const char *f_band = NULL, *f_bw = NULL, *f_arfcn = NULL, *f_pci = NULL, *f_rp = NULL, *f_sn = NULL;
            const char *sig_rp = NULL, *sig_sn = NULL;
            char sig_rp_buf[16] = "", sig_sn_buf[16] = "";
            if (nf >= 11) {
                f_band = f[3]; f_arfcn = f[4]; f_bw = f[5]; f_pci = f[1]; f_rp = f[7]; f_sn = f[9];
            } else if (nf >= 5) {
                f_band = f[1]; f_arfcn = f[3]; f_bw = f[4]; f_pci = f[0];
            }
            if (sgn == lgn && gi < sgn) siggrp = sgrps[gi];
            else if (sig_off && gi > 0 && gi - 1 < sgn) siggrp = sgrps[gi - 1];
            else if (gi < sgn) siggrp = sgrps[gi];
            if (siggrp && siggrp[0]) {
                char sg[96]; strncpy(sg, siggrp, sizeof sg - 1); sg[sizeof sg - 1] = 0;
                if (ca_sig_pick(sg, &sig_rp, &sig_sn)) {
                    if (sig_rp && sig_rp[0]) snprintf(sig_rp_buf, sizeof sig_rp_buf, "%s", sig_rp);
                    if (sig_sn && sig_sn[0]) snprintf(sig_sn_buf, sizeof sig_sn_buf, "%s", sig_sn);
                }
            }
            if ((!f_rp || !f_rp[0]) && sig_rp_buf[0]) f_rp = sig_rp_buf;
            if ((!f_sn || !f_sn[0]) && sig_sn_buf[0]) f_sn = sig_sn_buf;
            if (f_bw && atoi(f_bw) > 0) {
                char bn[12];
                if (f_band && (f_band[0] == 'B' || f_band[0] == 'b')) snprintf(bn, sizeof bn, "%s", f_band);
                else snprintf(bn, sizeof bn, "B%s", (f_band && f_band[0]) ? f_band : "-");
                char lr[12] = "-", ls[12] = "-";
                if (f_rp && f_rp[0]) snprintf(lr, sizeof lr, "%s", f_rp);
                if (f_sn && f_sn[0]) snprintf(ls, sizeof ls, "%s", f_sn);
                if (lte_cc == 0) {   /* serving-cell signal from main fields */
                    if (d.lte_rsrp) snprintf(lr, sizeof lr, "%d", d.lte_rsrp);
                    if (d.lte_snr[0]) snprintf(ls, sizeof ls, "%s", d.lte_snr);
                }
                struct signal_carrier_metric *metric =
                    signal_pick_carrier_metric(sig.lte_carriers, sig.lte_carrier_n,
                                               f_pci ? f_pci : "-", f_arfcn ? f_arfcn : "-",
                                               gi == 0);
                lo = car_row(s_lterows, lo, sizeof s_lterows, bn, f_bw, f_arfcn ? f_arfcn : "-",
                             f_pci ? f_pci : "-", lr, ls, hsr_freq_hint(d.mcc, f_arfcn),
                             metric);
                lte_show_cc++;
                lte_show_bw += atoi(f_bw);
                if (!carrier_is_inactive(lr)) { lte_cc++; lte_bw += atoi(f_bw); }
            }
        }
    }
    (void)no; (void)lo; (void)pc; (void)ac;

    /* Display summary includes inactive/configured carriers; generation badge
     * still uses active carrier stats above. */
    int total_bw, total_show_bw; const char *cmode;
    if (is_endc)     { total_bw = nr_bw + lte_bw; total_show_bw = nr_show_bw + lte_show_bw; cmode = "EN-DC"; }
    else if (is_nsa) { total_bw = nr_bw + lte_bw; total_show_bw = nr_show_bw + lte_show_bw; cmode = "5G NSA"; }
    else if (is_sa)  { total_bw = nr_bw;          total_show_bw = nr_show_bw;               cmode = "5G SA"; }
    else if (is_lte) { total_bw = lte_bw;         total_show_bw = lte_show_bw;              cmode = "4G LTE"; }
    else             { total_bw = 0;              total_show_bw = 0;                         cmode = d.net_type[0] ? d.net_type : "No Service"; }
    { char cnt[48];
      if (lte_show_cc && nr_show_cc) snprintf(cnt, sizeof cnt, "%d LTE + %d NR 载波", lte_show_cc, nr_show_cc);
      else if (nr_show_cc)           snprintf(cnt, sizeof cnt, "%d NR 载波", nr_show_cc);
      else if (lte_show_cc)          snprintf(cnt, sizeof cnt, "%d LTE 载波", lte_show_cc);
      else                 snprintf(cnt, sizeof cnt, "无载波");
      snprintf(s_carriers, sizeof s_carriers, "<div class='sec'>%s · %s · %d MHz</div>%s%s",
               cmode, cnt, total_show_bw, s_nrrows, s_lterows); }
    const char *hsr_card_cls = d.hsr ? " hsrmode" : "";
    const char *hsr_mode_note = d.hsr ? "<div class='hsrmode-note'>高铁模式</div>" : "";
    if ((is_endc || is_nsa) && s_nrrows[0] && s_lterows[0]) {
        snprintf(s_nr_block, sizeof s_nr_block,
                 "<div class='card%s'>"
                 "<div class='title'>%s <span class='sub'>%s</span>"
                 "<span class='qa'><b>QCI %s</b><br>AMBR %s</span></div>"
                 "%s"
                 "<div class='sec'>%s · %d LTE + %d NR 载波 · %d MHz</div>"
                 "<div class='ctitle'>NR</div>%s"
                 "</div>",
                 hsr_card_cls, s_oper, d.net_type, s_qci, s_ambr, hsr_mode_note,
                 cmode, lte_show_cc, nr_show_cc, total_show_bw, s_nrrows);
        snprintf(s_lte_block, sizeof s_lte_block,
                 "<div class='card'><div class='ctitle'>LTE</div>"
                 "<div class='sec'>%d LTE 载波 · %d MHz</div>%s</div>",
                 lte_show_cc, lte_show_bw, s_lterows);
        snprintf(s_sigcards, sizeof s_sigcards, "%s%s", s_nr_block, s_lte_block);
    } else {
        snprintf(s_sigcards, sizeof s_sigcards,
                 "<div class='card%s'>"
                 "<div class='title'>%s <span class='sub'>%s</span>"
                 "<span class='qa'><b>QCI %s</b><br>AMBR %s</span></div>"
                 "%s"
                 "%s"
                 "</div>",
                 hsr_card_cls, s_oper, d.net_type, s_qci, s_ambr, hsr_mode_note, s_carriers);
    }

    /* generation badge: 5GA / 5G+ / 5G / 4G / LTE / 3G */
    int gen_nr_cc = nr_show_cc;
    int gen_nr_bw = nr_show_bw;
    int op = 0;   /* 1 mobile, 2 unicom, 3 telecom, 4 broadnet, 5 other-mainland */
    if (d.mcc == 460) {
        int m = d.mnc;
        if (m == 0 || m == 2 || m == 4 || m == 7 || m == 8) op = 1;
        else if (m == 1 || m == 6 || m == 9) op = 2;
        else if (m == 3 || m == 5 || m == 11) op = 3;
        else if (m == 15) op = 4;
        else op = 5;
    }
    if (d.mcc == 460) {
        const char *cn = op == 1 ? "中国移动" : op == 2 ? "中国联通" :
                         op == 3 ? "中国电信" : op == 4 ? "中国广电" : NULL;
        if (cn) snprintf(s_oper, sizeof s_oper, "%s", cn);
    }
    const char *gen = "--";
    if (is_sa) {
        if ((op == 1 || op == 4) && gen_nr_cc >= 3) gen = "5GA";
        else if ((op == 2 || op == 3) && gen_nr_bw >= 200) gen = "5GA";
        else if (gen_nr_bw > 100) gen = "5G+";
        else gen = "5G";
    } else if (is_nsa || is_endc) gen = "5G";
    else if (is_lte) gen = (d.mcc == 460) ? "4G" : "LTE";
    else if (d.net_type[0]) gen = "3G";
    snprintf(s_gen, sizeof s_gen, "%s", gen);
    const char *genc = "g3";
    if      (!strcmp(gen, "5GA")) genc = "g5ga";
    else if (!strcmp(gen, "5G+")) genc = "g5p";
    else if (!strcmp(gen, "5G"))  genc = "g5";
    else if (!strcmp(gen, "4G"))  genc = "g4";
    else if (!strcmp(gen, "LTE")) genc = "glte";
    snprintf(g_stat_time, sizeof g_stat_time, "%s", s_time);
    g_stat_sig = signal_level(d.nr_rsrp ? d.nr_rsrp : d.lte_rsrp);
    snprintf(g_stat_gen, sizeof g_stat_gen, "%s", gen);

    /* ---- shared status bar: native-drawn content over a simple 26px slot ---- */
    {
        char sp[40];
        char us[20], ds[20];
        (void)sp;
        fmt_speed_u(us, sizeof us, d.tx_speed, g_speed_bits);
        fmt_speed_u(ds, sizeof ds, d.rx_speed, g_speed_bits);
        snprintf(g_stat_speed, sizeof g_stat_speed, "↑%s ↓%s", us, ds);
        fmt_speed_short(g_stat_up, sizeof g_stat_up, "↑", d.tx_speed, g_speed_bits);
        fmt_speed_short(g_stat_dn, sizeof g_stat_dn, "↓", d.rx_speed, g_speed_bits);
        pwr_refresh();
        g_stat_bat = clampi(d.bat_percent, 0, 100);
        g_stat_lowbat = d.bat_percent <= 20;
        g_sms_unread_now = d.sms_unread > 0;
        snprintf(s_sbar, sizeof s_sbar, "<div class='sbar'></div>");
    }

    /* ---- bottom page dots ---- */
    {
        int o = snprintf(s_dots, sizeof s_dots, "<div class='dots'>");
        for (int p = 0; p < g_npages && o < (int)sizeof s_dots - 40; p++)
            o += snprintf(s_dots + o, sizeof s_dots - o, "<span class='dot%s'></span>", p == g_cur ? " on" : "");
        if (o < (int)sizeof s_dots - 8) snprintf(s_dots + o, sizeof s_dots - o, "</div>");
    }

    /* charts are drawn natively after render (see draw_charts), not via tokens. */

    /* ---- band lock: universe grows to the largest set seen; selection mirrors
     * the live lock unless the user is editing in the modal ---- */
    static char s_netseg[640], s_cursa[300], s_curnsa[300], s_curlte[300], s_toast[160];
    if (band_count(d.sa_bands)  >= band_count(g_uni_sa))  snprintf(g_uni_sa,  sizeof g_uni_sa,  "%s", d.sa_bands);
    if (band_count(d.nsa_bands) >= band_count(g_uni_nsa)) snprintf(g_uni_nsa, sizeof g_uni_nsa, "%s", d.nsa_bands);
    if (band_count(d.lte_bands) >= band_count(g_uni_lte)) snprintf(g_uni_lte, sizeof g_uni_lte, "%s", d.lte_bands);
    if (!g_modal) {
        if (d.sa_bands[0])  snprintf(g_sel_sa,  sizeof g_sel_sa,  "%s", d.sa_bands);
        if (d.nsa_bands[0]) snprintf(g_sel_nsa, sizeof g_sel_nsa, "%s", d.nsa_bands);
        if (d.lte_bands[0]) snprintf(g_sel_lte, sizeof g_sel_lte, "%s", d.lte_bands);
    }
    band_summary(s_cursa,  sizeof s_cursa,  g_uni_sa,  g_sel_sa,  "n");
    band_summary(s_curnsa, sizeof s_curnsa, g_uni_nsa, g_sel_nsa, "n");
    band_summary(s_curlte, sizeof s_curlte, g_uni_lte, g_sel_lte, "B");
    {   /* segmented control: highlight current mode (pending overrides until it applies) */
        if (g_net_pending[0] && !strcmp(g_net_pending, d.net_select)) g_net_pending[0] = 0;
        const char *cur = g_net_pending[0] ? g_net_pending : d.net_select;
        int active = 0;
        for (int k = 0; k < 4; k++) if (!strcmp(g_netmodes[k].v, cur)) active = k;
        int hl = g_segdrag == 1 ? -1 : active;   /* during drag the native box is the highlight */
        int o = snprintf(s_netseg, sizeof s_netseg, "<div id='netseg' class='seg seg4'>");
        for (int k = 0; k < 4; k++)
            o += snprintf(s_netseg + o, sizeof s_netseg - o, "<a href='act:net:%s' class='segc%s'>%s</a>",
                          g_netmodes[k].v, k == hl ? " seg-on" : "", g_netmodes[k].lab);
        snprintf(s_netseg + o, sizeof s_netseg - o, "</div>");
    }
    s_toast[0] = 0;
    if (g_toast[0]) snprintf(s_toast, sizeof s_toast, "<div class='toast%s'>%s</div>", g_toast_pill ? " tcap" : "", g_toast);

    /* ---- system extras: usage, temps, version, imei, brightness, auto-off ---- */
    static char s_cusage[8], s_ctemp[8], s_btemp[8], s_swver[80], s_imei[72], s_spu[8], s_bright[8];
    static char s_memdet[24], s_upshort[16], s_autooff[420], s_refreshseg[480];
    { int bmax = backlight_max(); if (bmax <= 0) bmax = 255;
      snprintf(s_bright, sizeof s_bright, "%d", clampi(backlight_get() * 100 / bmax, 0, 100)); }
    { long mt = d.mem_total, ma = d.mem_avail;
      snprintf(s_memdet, sizeof s_memdet, "%ld/%ld MB", mt ? (mt - ma) / 1048576 : 0, mt / 1048576); }
    static char s_chgv[8], s_chgi[10], s_batv[8], s_bati[10], s_pwr[10], s_batpwr[10], s_batpwrlbl[8];
    snprintf(s_chgv, sizeof s_chgv, "%.2f", d.chg_uv / 1e6);
    snprintf(s_chgi, sizeof s_chgi, "%ld", d.chg_ua / 1000);
    snprintf(s_batv, sizeof s_batv, "%.2f", d.bat_uv / 1e6);
    /* signed: + while charging, - while discharging (matches PWRLBL) */
    snprintf(s_bati, sizeof s_bati, "%s%ld", d.charger_connect ? "+" : "-", labs(d.bat_ua) / 1000);
    { double pw = d.charger_connect ? (d.chg_uv / 1e6) * (d.chg_ua / 1e6)
                                    : (d.bat_uv / 1e6) * (labs(d.bat_ua) / 1e6);
      snprintf(s_pwr, sizeof s_pwr, "%.1f", pw); }
    {
        double bat_pw = (d.bat_uv / 1e6) * (labs(d.bat_ua) / 1e6);
        snprintf(s_batpwr, sizeof s_batpwr, "%.1f", bat_pw);
        snprintf(s_batpwrlbl, sizeof s_batpwrlbl, "%s", d.bat_ua >= 0 ? "充电" : "放电");
    }
    fmt_uptime_s(s_upshort, sizeof s_upshort, d.uptime);
    {   /* auto-off segmented control (#autoseg), same UI as net mode */
        int active = 0;
        for (int k = 0; k < 6; k++) if (g_autooffs[k].ms == g_autooff_ms) active = k;
        int hl = g_segdrag == 2 ? -1 : active;
        int o = snprintf(s_autooff, sizeof s_autooff, "<div id='autoseg' class='seg seg6'>");
        for (int k = 0; k < 6; k++)
            o += snprintf(s_autooff + o, sizeof s_autooff - o,
                "<a href='act:autooff:%d' class='segc%s'>%s</a>",
                g_autooffs[k].ms, k == hl ? " seg-on" : "", g_autooffs[k].lab);
        snprintf(s_autooff + o, sizeof s_autooff - o, "</div>");
    }
    {   /* refresh segmented control (#refreshseg), same UI as auto-off */
        int active = 0;
        for (int k = 0; k < 5; k++) if (g_refresh_rates[k].ms == g_refresh_ms) active = k;
        int hl = g_segdrag == 3 ? -1 : active;
        /* chips (not a .seg table: plain links in table cells don't take taps) */
        int o = snprintf(s_refreshseg, sizeof s_refreshseg, "<div class='blg b5 rfchips'>");
        for (int k = 0; k < 5; k++)
            o += snprintf(s_refreshseg + o, sizeof s_refreshseg - o,
                "<a href='act:refreshms:%d' class='blc%s'><b>%s</b></a>",
                g_refresh_rates[k].ms, k == hl ? " on" : "", g_refresh_rates[k].lab);
        snprintf(s_refreshseg + o, sizeof s_refreshseg - o, "</div>");
    }
    snprintf(s_cusage, sizeof s_cusage, "%ld", d.cpu_usage < 0 ? 0 : d.cpu_usage);
    snprintf(s_ctemp, sizeof s_ctemp, "%ld", d.cpu_temp);
    snprintf(s_btemp, sizeof s_btemp, "%d", d.bat_temp);
    snprintf(s_swver, sizeof s_swver, "%s", d.sw_version[0] ? d.sw_version : "-");
    if (g_show_imei && d.imei[0]) snprintf(s_imei, sizeof s_imei, "%s", d.imei);
    else if (strlen(d.imei) > 6) snprintf(s_imei, sizeof s_imei, "%.2s •••• %s", d.imei, d.imei + strlen(d.imei) - 4);
    else snprintf(s_imei, sizeof s_imei, "-");
    snprintf(s_spu, sizeof s_spu, "%s", g_speed_bits ? "Mbps" : "MB/s");

    /* ---- connected device list (page 2): all of them, filtered to currently
     * WiFi-associated MACs (leases linger after a device leaves) ---- */
    static char s_clist[4000];
    if (path && (strstr(path, "wifi") || strstr(path, "clients"))) sta_refresh();
    {
        int o = 0, shown = 0;
        int all = path && strstr(path, "clients");      /* full list sub-page; WiFi page shows 3 */
        for (int i = 0; i < d.client_n; i++) {
            if (!mac_assoc(d.client[i].mac)) continue;
            if (!all && shown >= 3) { shown++; continue; }
            char cn[96], cip[48];                    /* DHCP hostnames come from the clients: escape */
            html_esc(cn, sizeof cn, d.client[i].name);
            html_esc(cip, sizeof cip, d.client[i].ip);
            int si = sta_find(d.client[i].mac);
            if (si >= 0 && g_sta[si].rate > 0)
                APPEND(s_clist, o,
                    "<div class='cli two'><span class='cn'>%s<span class='cs'>%s · %s%s%s</span></span>"
                    "<span class='cip'>%d<span class='u'>Mbps</span></span></div>",
                    cn, cip, g_sta[si].band, g_sta[si].gen[0] ? " · " : "", g_sta[si].gen, g_sta[si].rate);
            else
                APPEND(s_clist, o,
                    "<div class='cli'><span class='cn'>%s</span><span class='cip'>%s</span></div>",
                    cn, cip);
            shown++;
        }
        if (shown == 0)
            snprintf(s_clist, sizeof s_clist, "<div class='cli muted'>暂无已连接设备</div>");
        else if (!all && shown > 3)
            APPEND(s_clist, o, "<a href='act:sub:clients.html' class='cli more'>还有 %d 台 · 查看全部 ›</a>", shown - 3);
        /* keep the header count consistent with the filtered list */
        if (g_assoc_macs[0]) snprintf(s_clients, sizeof s_clients, "%d", shown);
    }

    /* ---- sms list (read-only page): collapsed cards, newest first. Each card is
     * a tap target (act:sms:ID) that opens the full message in a dialog. ---- */
    static char s_smslist[131072];
    {
        int o = 0;
        for (int si = 0; si < d.sms_n; si++) {
            char prev[80]; int cut;
            utf8_trunc(prev, sizeof prev, d.sms[si].text, 40, &cut);
            char esc[512];
            char smsnum[96]; html_esc(smsnum, sizeof smsnum, d.sms[si].num);   /* sender can be alphanumeric */
            html_esc(esc, sizeof esc, prev);
            if (o >= (int)sizeof(s_smslist)) break;
            int wr = snprintf(s_smslist + o, sizeof(s_smslist) - o,
                "<a href='act:smsi:%d' class='sms%s'>"
                "<div class='smsh'><span class='smsn'>%s</span><span class='smsd'>%s</span></div>"
                "<div class='smsp'>%s%s</div></a>",
                si, d.sms[si].unread ? " un" : "", smsnum, d.sms[si].date,
                esc, cut ? "…" : "");
            if (wr < 0) wr = 0;
            if (wr >= (int)(sizeof(s_smslist) - o)) {
                o = (int)sizeof(s_smslist) - 1;
                s_smslist[o] = 0;
                break;
            }
            o += wr;
        }
        if (d.sms_n == 0)
            snprintf(s_smslist, sizeof s_smslist, "<div class='sms muted'>暂无短信</div>");
    }

    /* ---- dhcp summary (page 2) ---- */
    static char s_pool[64], s_lease[24];
    snprintf(s_pool, sizeof s_pool, "%s · 共 %s",
             d.dhcp_start[0] ? d.dhcp_start : "-", d.dhcp_limit[0] ? d.dhcp_limit : "-");
    { long lt = atol(d.dhcp_leasetime);
      if (lt >= 3600)     snprintf(s_lease, sizeof s_lease, "%ld 小时", lt / 3600);
      else if (lt >= 60)  snprintf(s_lease, sizeof s_lease, "%ld 分钟", lt / 60);
      else if (lt > 0)    snprintf(s_lease, sizeof s_lease, "%ld 秒", lt);
      else                strcpy(s_lease, "-"); }

    int adb_on = !strcmp(d.usb_mode, "debug");
    int usb_net_on = (g_usb_net == 1) || usb_pid_is_net();
    int usb_reverse = (g_typec_source == 1);
    uint32_t now_ms = millis();
    if (g_adb_pending >= 0) {
        if (g_adb_pending == adb_on) g_adb_pending = -1;
        else                         adb_on = g_adb_pending;
    }
    if (g_usb_net_pending >= 0) {
        if (g_usb_net_pending == usb_net_on || (int32_t)(now_ms - g_usb_net_until) > 0) g_usb_net_pending = -1;
        else                                                            usb_net_on = g_usb_net_pending;
    }
    if (g_typec_pending >= 0) {
        if (g_typec_pending == usb_reverse || (int32_t)(now_ms - g_typec_until) > 0) g_typec_pending = -1;
        else                                                         usb_reverse = g_typec_pending;
    }
    const char *adb_state = g_adb_pending >= 0 ? "切换中" : (adb_on ? "已开启" : "已关闭");
    const char *usb_pwr_state = g_typec_pending >= 0 ? "切换中" : (usb_reverse ? "给对方供电" : "给本机充电");
    const char *usb_net_state = g_usb_net_pending >= 0 ? "切换中" : (usb_net_on ? "共享中" : "仅充电");

    int connected = strstr(d.wan_status, "connect") && !strstr(d.wan_status, "dis");
    int wifi_master = (g_w24 == 1 || g_w5 == 1);
    int i = 0;
    t[i++] = (struct kv){ "STATUSBAR", s_sbar };   t[i++] = (struct kv){ "DOTS", s_dots };
    t[i++] = (struct kv){ "SIGBARS", "" };
    t[i++] = (struct kv){ "TIME", s_time };        t[i++] = (struct kv){ "BAT", s_bat };
    t[i++] = (struct kv){ "OPER", s_oper };        t[i++] = (struct kv){ "NETTYPE", d.net_type };
    t[i++] = (struct kv){ "BAND", d.band };        t[i++] = (struct kv){ "WAN", connected ? "已连接" : "未连接" };
    t[i++] = (struct kv){ "RSRP", s_rsrp };        t[i++] = (struct kv){ "RSRP_W", w_rsrp };
    t[i++] = (struct kv){ "RSRQ", s_rsrq };        t[i++] = (struct kv){ "RSRQ_W", w_rsrq };
    t[i++] = (struct kv){ "SINR", s_sinr };        t[i++] = (struct kv){ "SINR_W", w_sinr };
    t[i++] = (struct kv){ "BW", s_bw };            t[i++] = (struct kv){ "BW_W", w_bw };
    t[i++] = (struct kv){ "CELLID", s_cellid };    t[i++] = (struct kv){ "PCI", s_pci };
    t[i++] = (struct kv){ "TA", s_ta };            t[i++] = (struct kv){ "TADIST", s_tadist };
    t[i++] = (struct kv){ "SIGDETAILCARDS", s_signalcards };
    t[i++] = (struct kv){ "CELLBTN", g_show_cellid ? "隐藏" : "显示" };
    t[i++] = (struct kv){ "CLIENTS", s_clients };  t[i++] = (struct kv){ "UPTIME", s_up };
    t[i++] = (struct kv){ "RXSPEED", s_rxs };      t[i++] = (struct kv){ "TXSPEED", s_txs };
    t[i++] = (struct kv){ "RXBYTES", s_rxb };      t[i++] = (struct kv){ "TXBYTES", s_txb };
    t[i++] = (struct kv){ "CPU", s_cpu };          t[i++] = (struct kv){ "MEM", s_mem };
    t[i++] = (struct kv){ "QCI", s_qci };          t[i++] = (struct kv){ "AMBR", s_ambr };
    t[i++] = (struct kv){ "SSID", s_ssid };        t[i++] = (struct kv){ "KEY", s_key };
    t[i++] = (struct kv){ "ENC", d.wifi_enc[0] ? d.wifi_enc : "-" };
    t[i++] = (struct kv){ "MODEL", s_model };      t[i++] = (struct kv){ "FW", s_fw };
    t[i++] = (struct kv){ "PAGE", s_page };        t[i++] = (struct kv){ "NPAGES", s_np };
    t[i++] = (struct kv){ "CARRIERS", s_carriers }; t[i++] = (struct kv){ "GEN", s_gen };
    t[i++] = (struct kv){ "SIGNALCARDS", s_sigcards };
    t[i++] = (struct kv){ "NEIGHBORCARDS", s_neighborcards };
    t[i++] = (struct kv){ "GENCLASS", genc };
    { int nowp = !strcmp(g_wallname, "none");
      t[i++] = (struct kv){ "THEME", g_theme ? (nowp ? "light nowp" : "light") : (nowp ? "dark nowp" : "dark") }; }
    t[i++] = (struct kv){ "BATCLASS", d.bat_percent <= 20 ? "low" : "" };
    t[i++] = (struct kv){ "KEYBTN", g_show_key ? "隐藏密码" : "显示密码" };
    t[i++] = (struct kv){ "ADBCLASS", adb_on ? "on" : "off" };
    t[i++] = (struct kv){ "ADBSTATE", adb_state };
    t[i++] = (struct kv){ "USBPWRCLASS", usb_reverse ? "on" : "off" };
    t[i++] = (struct kv){ "USBPWRSTATE", usb_pwr_state };
    t[i++] = (struct kv){ "USBNETCLASS", usb_net_on ? "on" : "off" };
    t[i++] = (struct kv){ "USBNETSTATE", usb_net_state };
    t[i++] = (struct kv){ "BATPCTCLASS", g_show_batpct ? "on" : "off" };
    t[i++] = (struct kv){ "BATPCTSTATE", g_show_batpct ? "已显示" : "已隐藏" };
    t[i++] = (struct kv){ "THEMECLASS", g_theme ? "on" : "off" };
    t[i++] = (struct kv){ "THEMESTATE", g_theme ? "浅色模式" : "深色模式" };
    t[i++] = (struct kv){ "SPUNITCLASS", g_speed_bits ? "on" : "off" };
    t[i++] = (struct kv){ "SPUNITSTATE", g_speed_bits ? "比特率 Mbps" : "字节率 MB/s" };
    t[i++] = (struct kv){ "SPUNITSHORT", g_speed_bits ? "Mbps" : "MB/s" };
    t[i++] = (struct kv){ "SPUNIT", s_spu };
    t[i++] = (struct kv){ "CPUUSAGE", s_cusage }; t[i++] = (struct kv){ "CPUTEMP", s_ctemp };
    t[i++] = (struct kv){ "BATTEMP", s_btemp };   t[i++] = (struct kv){ "SWVER", s_swver };
    {   /* 关于本机: SIM identity from the stock MDM API, fetched in the background while the page is open */
        static char s_num[40], s_iccid[48], s_imsi[40], s_simop[80], s_nettag[96];
        static uint32_t sim_at;
        char num[32] = "", iccid[32] = "", imsi[32] = "";
        if (path && strstr(path, "sys.html")) {
            uint32_t now = millis();
            if (!sim_at || now - sim_at > 30000) {
                sim_at = now ? now : 1;
                system("(ubus -t 3 call zwrt_zte_mdm.api get_sim_info > /tmp/u60-sim.json.n && mv /tmp/u60-sim.json.n /tmp/u60-sim.json) >/dev/null 2>&1 &");
            }
            char *j = read_file("/tmp/u60-sim.json");
            if (j) {
                const char *keys[3] = { "\"msisdn\": \"", "\"sim_iccid\": \"", "\"sim_imsi\": \"" };
                char *outs[3] = { num, iccid, imsi };
                for (int k = 0; k < 3; k++) {
                    const char *p = strstr(j, keys[k]);
                    if (!p) continue;
                    p += strlen(keys[k]);
                    int n = 0; while (p[n] && p[n] != '"' && n < 30) { outs[k][n] = p[n]; n++; } outs[k][n] = 0;
                }
                free(j);
            }
        } else if (path) g_show_imei = 0;              /* leaving the page masks everything again */
        /* masked: keep a short head and the last 4 digits */
        #define MASKED(dst, src, head) do { int L = (int)strlen(src); \
            if (!L) snprintf(dst, sizeof dst, "-"); \
            else if (g_show_imei || L <= (head) + 4) snprintf(dst, sizeof dst, "%s", src); \
            else { snprintf(dst, sizeof dst, "%.*s", head, src); strcat(dst, " •••• "); strcat(dst, src + L - 4); } } while (0)
        const char *nm = num; if (!strncmp(nm, "86", 2) && strlen(nm) == 13) nm += 2;   /* +86 prefix */
        MASKED(s_num, nm, 3); MASKED(s_iccid, iccid, 6); MASKED(s_imsi, imsi, 5);
        #undef MASKED
        snprintf(s_simop, sizeof s_simop, "%s · %s", s_oper[0] ? s_oper : "-", g_roam ? "<span class='amber'>漫游中</span>" : "国内");
        snprintf(s_nettag, sizeof s_nettag, "%s%s", g_hst ? " · <span class='teal'>高铁</span>" : "", g_roam ? " · <span class='amber'>漫游</span>" : "");
        t[i++] = (struct kv){ "SIMNUM", s_num };   t[i++] = (struct kv){ "SIMICCID", s_iccid };
        t[i++] = (struct kv){ "SIMIMSI", s_imsi }; t[i++] = (struct kv){ "SIMOP", s_simop };
        t[i++] = (struct kv){ "NETTAG", s_nettag };
        /* device name / model / version / uptime for 关于本机 */
        static char s_abmodel[32], s_abver[64], s_abup[40];
        if (!s_abmodel[0]) {                   /* stock model name, read once (d.model is the SoC vendor) */
            char *f = read_file("/etc/config/zwrt_common_info");
            const char *m = f ? strstr(f, "option model_name '") : NULL;
            if (m) { m += 19; int n = 0; while (m[n] && m[n] != '\'' && n < 30) n++; snprintf(s_abmodel, sizeof s_abmodel, "%.*s", n, m); }
            else snprintf(s_abmodel, sizeof s_abmodel, "MU5250");
            free(f);
        }
        const char *ver = strstr(s_swver, "MU");    /* "BD_CNMU5250V1.0.0B31" -> "MU5250V1.0.0B31" */
        snprintf(s_abver, sizeof s_abver, "%s", ver ? ver : s_swver);
        long up = d.uptime;
        if (up >= 86400) snprintf(s_abup, sizeof s_abup, "%ld 天 %ld 小时", up / 86400, up % 86400 / 3600);
        else if (up >= 3600) snprintf(s_abup, sizeof s_abup, "%ld 小时 %ld 分钟", up / 3600, up % 3600 / 60);
        else snprintf(s_abup, sizeof s_abup, "%ld 分钟", up / 60);
        t[i++] = (struct kv){ "ABMODEL", s_abmodel }; t[i++] = (struct kv){ "ABVER", s_abver };
        t[i++] = (struct kv){ "ABUP", s_abup };
    }
    t[i++] = (struct kv){ "IMEI", s_imei };
    t[i++] = (struct kv){ "IMEIBTN", g_show_imei ? "隐藏" : "显示" };
    t[i++] = (struct kv){ "BRIGHT", s_bright };   t[i++] = (struct kv){ "AUTOOFF", s_autooff };
    t[i++] = (struct kv){ "REFRESHSEG", s_refreshseg };
    t[i++] = (struct kv){ "STSRCSEG", speedtest_src_html() };
    t[i++] = (struct kv){ "STDIRSEG", speedtest_dir_html() };
    t[i++] = (struct kv){ "STDURSEG", speedtest_dur_html() };
    t[i++] = (struct kv){ "STLOOPHINT", speedtest_loop_hint_html() };
    t[i++] = (struct kv){ "STSTATUS", speedtest_status_html() };
    t[i++] = (struct kv){ "STRESULT", speedtest_result_html() };
    t[i++] = (struct kv){ "STLOGCARD", speedtest_log_card_html() };
    t[i++] = (struct kv){ "STACTION", speedtest_action_html() };
    t[i++] = (struct kv){ "STINSTALL", speedtest_install_html() };
    t[i++] = (struct kv){ "STGAUGE", speedtest_dial_html() };
    t[i++] = (struct kv){ "STHDR", speedtest_hdr_html() };     t[i++] = (struct kv){ "STMAIN", speedtest_main_html() };
    t[i++] = (struct kv){ "STPILLS", speedtest_pills_html() }; t[i++] = (struct kv){ "STNODE", speedtest_node_text() };
    t[i++] = (struct kv){ "STNODESUB", speedtest_node_sub() };
    t[i++] = (struct kv){ "STCHART", speedtest_lines_html() };
    t[i++] = (struct kv){ "STHOMEBTN", speedtest_home_button_html() };
    t[i++] = (struct kv){ "STHOMEINLINE", speedtest_home_inline_html() };
    t[i++] = (struct kv){ "STFUNCTIONTILE", speedtest_function_tile_html() };
    t[i++] = (struct kv){ "CUSTOMFUNCTIONTILES", custom_function_tiles_html() };
    t[i++] = (struct kv){ "SIGADVSTATE", s_sigadvstate };
    t[i++] = (struct kv){ "SIGRDCLASS", g_sig_read ? "on" : "off" };
    t[i++] = (struct kv){ "SIGPSCLASS", g_sig_parse ? "on" : "off" };
    t[i++] = (struct kv){ "SIGADVSHORT", g_sig_read ? (g_sig_parse ? "信令读取+解析" : "信令读取") : "信令已关" };
    t[i++] = (struct kv){ "MEMDETAIL", s_memdet }; t[i++] = (struct kv){ "UPSHORT", s_upshort };
    t[i++] = (struct kv){ "CHGV", s_chgv };       t[i++] = (struct kv){ "CHGI", s_chgi };
    t[i++] = (struct kv){ "BATV", s_batv };       t[i++] = (struct kv){ "BATI", s_bati };
    t[i++] = (struct kv){ "PWR", s_pwr };         t[i++] = (struct kv){ "PWRLBL", d.charger_connect ? "充电" : "放电" };
    if (is_charts) {
        t[i++] = (struct kv){ "BATPWR", s_batpwr };
        t[i++] = (struct kv){ "BATPWRLBL", s_batpwrlbl };
    } else {
        t[i++] = (struct kv){ "BATPWR", "" };
        t[i++] = (struct kv){ "BATPWRLBL", "" };
    }
    t[i++] = (struct kv){ "NETSEG", s_netseg };   t[i++] = (struct kv){ "TOAST", s_toast };
    t[i++] = (struct kv){ "PWROFFLBL",  g_pwr_confirm == 1 ? "再按一次" : "关机" };
    t[i++] = (struct kv){ "PWROFFCLS",  g_pwr_confirm == 1 ? "armed" : "" };
    t[i++] = (struct kv){ "PWRREBLBL",  g_pwr_confirm == 2 ? "再按一次" : "重启" };
    t[i++] = (struct kv){ "PWRREBCLS",  g_pwr_confirm == 2 ? "armed" : "" };
    t[i++] = (struct kv){ "CURSA", s_cursa };     t[i++] = (struct kv){ "CURNSA", s_curnsa };
    {   /* one-screen 锁频 page */
        static char s_blbody[5200];
        s_blbody[0] = 0;
        bl_sync(&d);
        if (path) { const char *bn = strrchr(path, '/'); bn = bn ? bn + 1 : path;
                    if (!strcmp(bn, "lock.html")) bl_body(s_blbody, sizeof s_blbody, &d); }
        t[i++] = (struct kv){ "BLBODY", s_blbody };
    }
    {   /* WiFi 功率: chip on the WiFi page + its sub-page */
        static char s_txlbl[16], s_txpct[8], s_txdbm[160], s_txopts[1400];
        int pct; double d2, d5;
        if (path && (strstr(path, "wifi") || strstr(path, "control"))) txp_refresh(0);
        txp_read(&pct, &d2, &d5);
        snprintf(s_txlbl, sizeof s_txlbl, "%s", txp_label(pct));
        snprintf(s_txpct, sizeof s_txpct, "%d", pct);
        if (d2 > 0) snprintf(s_txdbm, sizeof s_txdbm, "2.4G <span class='n'>%.0f</span> dBm · 5G <span class='n'>%.0f</span> dBm", d2, d5);
        else snprintf(s_txdbm, sizeof s_txdbm, "读取中…");
        static const struct { int p; const char *t, *d, *db; } lv[3] = {
            { 40,  "近距离", "同一房间，最省电、最凉快", "15 / 14 dBm" },
            { 80,  "中距离", "隔一两堵墙", "18 / 17 dBm" },
            { 100, "穿墙",   "满功率，覆盖最大", "19 / 18 dBm" } };
        int o = 0;
        for (int k = 0; k < 3; k++)
            o += snprintf(s_txopts + o, sizeof s_txopts - o,
                          "<a href='act:txp:%d' class='card txo%s'><span class='txdb k'>%s</span><span class='tl'>%s</span><span class='k'>%s</span></a>",
                          lv[k].p, lv[k].p == pct ? " on" : "", lv[k].db, lv[k].t, lv[k].d);
        t[i++] = (struct kv){ "TXLBL", s_txlbl };  t[i++] = (struct kv){ "TXPCT", s_txpct };
        t[i++] = (struct kv){ "TXDBM", s_txdbm };  t[i++] = (struct kv){ "TXOPTS", s_txopts };
        static char s_txdbm2[24];                       /* control-center tile: "19 dBm" */
        if (d2 > 0) snprintf(s_txdbm2, sizeof s_txdbm2, "%.0f dBm", d2); else snprintf(s_txdbm2, sizeof s_txdbm2, "%d%%", pct);
        t[i++] = (struct kv){ "TXDBM2", s_txdbm2 };
    }
    {   /* control-center tiles: battery + speedtest summaries */
        static char s_battile[48], s_sttile[48];
        long on = 0; read_long_path("/sys/class/power_supply/usb/online", &on);
        snprintf(s_battile, sizeof s_battile, "%d%% · %s", d.bat_percent,
                 g_pwr.drain ? "直供电 · 放到60%" : !on ? "用电池" : !access(CHGCAP_MARK, F_OK) && g_chg_cap ? "到充电上限" : g_dps == 1 ? "直供电中" : d.bat_percent >= 100 ? "已充满" : "充电中");
        if (g_st_state == ST_STATE_RUNNING) snprintf(s_sttile, sizeof s_sttile, "测速中…");
        else if (g_st_have_result) snprintf(s_sttile, sizeof s_sttile, "上次 %.0f / %.0f Mbps", g_st_dl_avg, g_st_ul_avg);
        else if (g_st_state == ST_STATE_MISSING) snprintf(s_sttile, sizeof s_sttile, "未安装");
        else snprintf(s_sttile, sizeof s_sttile, "点开测速");
        t[i++] = (struct kv){ "BATTILE", s_battile }; t[i++] = (struct kv){ "STTILE", s_sttile };
    }
    if (path && strstr(path, "battery.html")) {   /* 电池与充电 page: live sysfs */
        static char s_bst1[32], s_bst2[48], s_bin[32], s_btmp[16], s_bhl[32], s_bpct[8], s_bbar[8], s_capseg[600], s_curseg[600];
        const char *PS = "/sys/class/power_supply";
        char pth[96], st[24] = "";
        long cap = 0, temp = 0, ib = 0, vb = 0, on = 0, uv = 0, ua = 0, cf = 0, cfd = 0, cyc = 0;
        snprintf(pth, sizeof pth, "%s/battery/capacity", PS);           read_long_path(pth, &cap);
        snprintf(pth, sizeof pth, "%s/battery/temp", PS);               read_long_path(pth, &temp);
        snprintf(pth, sizeof pth, "%s/battery/current_now", PS);        read_long_path(pth, &ib);
        snprintf(pth, sizeof pth, "%s/battery/voltage_now", PS);        read_long_path(pth, &vb);
        snprintf(pth, sizeof pth, "%s/battery/charge_full", PS);        read_long_path(pth, &cf);
        snprintf(pth, sizeof pth, "%s/battery/charge_full_design", PS); read_long_path(pth, &cfd);
        snprintf(pth, sizeof pth, "%s/battery/cycle_count", PS);        read_long_path(pth, &cyc);
        snprintf(pth, sizeof pth, "%s/usb/online", PS);                 read_long_path(pth, &on);
        snprintf(pth, sizeof pth, "%s/usb/voltage_now", PS);            read_long_path(pth, &uv);
        snprintf(pth, sizeof pth, "%s/usb/current_now", PS);            read_long_path(pth, &ua);
        snprintf(pth, sizeof pth, "%s/battery/status", PS);             read_line_path(pth, st, sizeof st);
        double bw = (vb / 1e6) * (labs(ib) / 1e6);                     /* battery W, charging current is positive */
        int capheld = !access(CHGCAP_MARK, F_OK);
        if (!on && dps_draining())    { snprintf(s_bst1, sizeof s_bst1, "直供电中"); snprintf(s_bst2, sizeof s_bst2, "先放电到 60%%，再由电源直供"); }
        else if (!on)                 { snprintf(s_bst1, sizeof s_bst1, "用电池中"); snprintf(s_bst2, sizeof s_bst2, "放电 %.1f W", bw); }
        else if (capheld && g_chg_cap){ snprintf(s_bst1, sizeof s_bst1, "已到充电上限"); snprintf(s_bst2, sizeof s_bst2, "直供中，降到 %d%% 再充", g_chg_cap - 5); }
        else if (g_dps == 1)          { snprintf(s_bst1, sizeof s_bst1, "直供电中"); snprintf(s_bst2, sizeof s_bst2, "电池不充不放"); }
        else if (cap >= 100 || !strcmp(st, "Full")) { snprintf(s_bst1, sizeof s_bst1, "已充满"); snprintf(s_bst2, sizeof s_bst2, "可以拔掉充电器"); }
        else { snprintf(s_bst1, sizeof s_bst1, "充电中"); snprintf(s_bst2, sizeof s_bst2, "充入 %.1f W%s", bw, g_chg_cur ? " · 限流中" : ""); }
        if (on) snprintf(s_bin, sizeof s_bin, "%.1fV %.1fW", uv / 1e6, (uv / 1e6) * (ua / 1e6));
        else    snprintf(s_bin, sizeof s_bin, "未接电源");
        snprintf(s_btmp, sizeof s_btmp, "%.1f℃", temp / 10.0);
        snprintf(s_bhl, sizeof s_bhl, "%ld%% · %ld 次", cfd > 0 ? (cf * 100 / cfd > 100 ? 100 : cf * 100 / cfd) : 0, cyc);
        snprintf(s_bpct, sizeof s_bpct, "%ld", cap);
        snprintf(s_bbar, sizeof s_bbar, "%ld", cap < 2 ? 2 : cap > 100 ? 100 : cap);
        static const int caps[5] = { 0, 70, 80, 90, 95 }, curs[5] = { 0, 2000, 1500, 1000, 500 };
        static const char *curl[5] = { "不限", "2A", "1.5A", "1A", "0.5A" };
        /* chip rows, not .seg tables: plain links inside table cells don't take taps */
        int o = snprintf(s_capseg, sizeof s_capseg, "<div class='blg b5'>");
        for (int k = 0; k < 5; k++) {
            char lab[8]; if (k) snprintf(lab, sizeof lab, "%d%%", caps[k]); else snprintf(lab, sizeof lab, "关");
            o += snprintf(s_capseg + o, sizeof s_capseg - o, "<a href='act:chgcap:%d' class='blc%s'><b>%s</b></a>",
                          caps[k], caps[k] == g_chg_cap ? " on" : "", lab);
        }
        snprintf(s_capseg + o, sizeof s_capseg - o, "</div>");
        o = snprintf(s_curseg, sizeof s_curseg, "<div class='blg b5'>");
        for (int k = 0; k < 5; k++)
            o += snprintf(s_curseg + o, sizeof s_curseg - o, "<a href='act:chgcur:%d' class='blc%s'><b>%s</b></a>",
                          curs[k], curs[k] == g_chg_cur ? " on" : "", curl[k]);
        snprintf(s_curseg + o, sizeof s_curseg - o, "</div>");
        t[i++] = (struct kv){ "BST1", s_bst1 };  t[i++] = (struct kv){ "BST2", s_bst2 };
        t[i++] = (struct kv){ "BIN", s_bin };    t[i++] = (struct kv){ "BTMP", s_btmp };
        t[i++] = (struct kv){ "BHL", s_bhl };    t[i++] = (struct kv){ "BPCT", s_bpct };
        t[i++] = (struct kv){ "BBAR", s_bbar };  t[i++] = (struct kv){ "CAPSEG", s_capseg };
        t[i++] = (struct kv){ "CURSEG", s_curseg };
    }
    t[i++] = (struct kv){ "CURLTE", s_curlte };
    t[i++] = (struct kv){ "NFCCLASS", d.nfc_switch ? "on" : "off" };
    t[i++] = (struct kv){ "NFCSTATE", d.nfc_switch ? "已开启" : "已关闭" };
    t[i++] = (struct kv){ "WIFICLASS", wifi_master ? "on" : "off" };
    t[i++] = (struct kv){ "WIFISTATE", (g_w24 < 0 && g_w5 < 0) ? "—" : wifi_master ? "已开启" : "已关闭" };
    t[i++] = (struct kv){ "WIFI24CLASS", g_w24 == 1 ? "on" : "off" };
    t[i++] = (struct kv){ "WIFI24STATE", g_w24 < 0 ? "—" : g_w24 ? "已开启" : "已关闭" };
    t[i++] = (struct kv){ "WIFI5CLASS", g_w5 == 1 ? "on" : "off" };
    t[i++] = (struct kv){ "WIFI5STATE", g_w5 < 0 ? "—" : g_w5 ? "已开启" : "已关闭" };
    t[i++] = (struct kv){ "DPSCLASS", g_dps == 1 ? "on" : "off" };
    t[i++] = (struct kv){ "DPSSTATE", g_dps < 0 ? "—" : g_dps ? "已开启" : "已关闭" };
    t[i++] = (struct kv){ "PSMCLASS", g_wpsm == 1 ? "on" : "off" };
    t[i++] = (struct kv){ "PSMSTATE", g_wpsm < 0 ? "—" : g_wpsm ? "已开启（省电）" : "已关闭（高性能）" };
    t[i++] = (struct kv){ "CLIENTLIST", s_clist }; t[i++] = (struct kv){ "DHCP_IP", d.dhcp_ip[0] ? d.dhcp_ip : "-" };
    t[i++] = (struct kv){ "SMSLIST", s_smslist };
    {   /* 短信详情页: one message from the same snapshot the list was drawn from */
        static char s_sdnum[96], s_sddate[48], s_sdpos[24], s_sdbody[24576];
        s_sdnum[0] = s_sddate[0] = s_sdpos[0] = s_sdbody[0] = 0;
        if (path && strstr(path, "smsdetail") && d.sms_n > 0) {
            if (g_sms_idx < 0) g_sms_idx = 0;
            if (g_sms_idx >= d.sms_n) g_sms_idx = d.sms_n - 1;
            html_esc(s_sdnum, sizeof s_sdnum, d.sms[g_sms_idx].num);
            snprintf(s_sddate, sizeof s_sddate, "%s", d.sms[g_sms_idx].date);
            snprintf(s_sdpos, sizeof s_sdpos, "%d / %d", g_sms_idx + 1, d.sms_n);
            sms_body_html(s_sdbody, sizeof s_sdbody, d.sms[g_sms_idx].text);
        } else if (path && strstr(path, "smsdetail")) snprintf(s_sdbody, sizeof s_sdbody, "<span class='k'>这条短信已不在列表里</span>");
        t[i++] = (struct kv){ "SDNUM", s_sdnum };  t[i++] = (struct kv){ "SDDATE", s_sddate };
        t[i++] = (struct kv){ "SDPOS", s_sdpos };  t[i++] = (struct kv){ "SDBODY", s_sdbody };
        t[i++] = (struct kv){ "SDPREV", g_sms_idx > 0 ? "" : " off" };
        t[i++] = (struct kv){ "SDNEXT", g_sms_idx < d.sms_n - 1 ? "" : " off" };
    }
    t[i++] = (struct kv){ "DHCP_POOL", g_dhcp_pool[0] ? g_dhcp_pool : s_pool };
    t[i++] = (struct kv){ "DHCP_LEASE", s_lease };
    {   /* short pool for the WiFi page: "a.b.c.2 - a.b.c.253" -> "2 到 253" */
        static char s_pools[40];
        const char *dash = strstr(g_dhcp_pool, " - "), *b = dash ? strrchr(dash, '.') : NULL;
        if (dash && b) {
            const char *a = dash;
            while (a > g_dhcp_pool && a[-1] != '.') a--;
            snprintf(s_pools, sizeof s_pools, "%.*s 到 %s", (int)(dash - a), a, b + 1);
        } else snprintf(s_pools, sizeof s_pools, "%s", g_dhcp_pool[0] ? g_dhcp_pool : s_pool);
        t[i++] = (struct kv){ "DHCP_POOLS", s_pools };
    }

    /* ---- lock screen (PIN pad): dots reflect typed digits. ---- */
    static char s_pindots[512], s_lockaux[140];
    {
        int filled = (int)strlen(g_pin_entry);
        int o = snprintf(s_pindots, sizeof s_pindots, "<div class='pin-slots'>");
        for (int k = 0; k < 4; k++)
            o += (k < filled)
               ? snprintf(s_pindots + o, sizeof s_pindots - o, "<span class='ps'><span class='dot'></span></span>")
               : snprintf(s_pindots + o, sizeof s_pindots - o,
                          "<span class='ps'><span class='ring'><span class='ri'></span></span></span>");
        snprintf(s_pindots + o, sizeof s_pindots - o, "</div>");
    }
    if (g_lock_state == 2)
        snprintf(s_lockaux, sizeof s_lockaux, "<a href='act:lockcancel' class='kp kpx'>取消</a>");
    else s_lockaux[0] = 0;
    t[i++] = (struct kv){ "PINDOTS", s_pindots };
    t[i++] = (struct kv){ "LOCKAUX", s_lockaux };
    t[i++] = (struct kv){ "LOCKTITLE", g_lock_state == 2 ? "设置锁屏密码" : "请输入锁屏密码" };
    t[i++] = (struct kv){ "LOCKMSG", g_lock_err ? "<div class='lock-err'>密码错误</div>" : "" };
    t[i++] = (struct kv){ "LOCKCLASS", lock_enabled() ? "on" : "off" };
    t[i++] = (struct kv){ "LOCKSTATE", lock_enabled() ? "已开启" : "已关闭" };

    /* ---- redesign tokens: cover/home hero, quality words,
     * wallpaper chooser, WiFi QR payload ---- */
    static char s_date[48], s_bandsum[48], s_qbars[400], s_rsrpx[12], s_sinrx[12];
    static char s_rsrpw[6], s_sinrw[6], s_smslast[96], s_smsbadge[64];
    static char s_wpsel[900], s_netmode[16], s_gensub[8], s_sigwarn[480], s_rescueent[480];
    {
        static const char *wk[7] = { "日", "一", "二", "三", "四", "五", "六" };
        snprintf(s_date, sizeof s_date, "%d月%d日　星期%s", tmv.tm_mon + 1, tmv.tm_mday, wk[tmv.tm_wday % 7]);
    }
    int use_nr = is_sa || is_nsa || is_endc;
    int rsrp = use_nr && d.nr_rsrp ? d.nr_rsrp : d.lte_rsrp;
    const char *sinr = use_nr && d.nr_snr[0] ? d.nr_snr : d.lte_snr;
    int lv = signal_level(rsrp);
    double sinr_v = atof(sinr);
    const char *sigq = lv >= 5 ? "信号极好" : lv == 4 ? "信号良好" : lv == 3 ? "信号一般" :
                       lv == 2 ? "信号较弱" : lv == 1 ? "信号很差" : "无信号";
    const char *sigqc = lv >= 4 ? "good" : lv == 3 ? "mid" : "bad";
    const char *sinrc = !sinr[0] ? "mu" : sinr_v >= 13 ? "good" : sinr_v >= 3 ? "mid" : "bad";
    if (rsrp) snprintf(s_rsrpx, sizeof s_rsrpx, "%d", rsrp); else strcpy(s_rsrpx, "--");
    snprintf(s_sinrx, sizeof s_sinrx, "%s", sinr[0] ? sinr : "--");
    snprintf(s_rsrpw, sizeof s_rsrpw, "%d", rsrp ? clampi((rsrp + 125) * 100 / 50, 4, 100) : 0);
    snprintf(s_sinrw, sizeof s_sinrw, "%d", sinr[0] ? clampi((int)((sinr_v + 5) * 100 / 30), 4, 100) : 0);
    {
        int o = snprintf(s_qbars, sizeof s_qbars, "<span class='qbars %s'>", sigqc);
        for (int k = 0; k < 5; k++)
            o += snprintf(s_qbars + o, sizeof s_qbars - o, "<i class='q%d%s'></i>", k, k < lv ? "" : " off");
        snprintf(s_qbars + o, sizeof s_qbars - o, "</span>");
    }
    snprintf(s_gensub, sizeof s_gensub, "%s", is_sa ? "SA" : (is_nsa || is_endc) ? "NSA" : "");
    {
        char sb[16];
        short_band(sb, sizeof sb, use_nr ? nr_band : d.band, use_nr);
        if (total_show_bw > 0) snprintf(s_bandsum, sizeof s_bandsum, "%s · %d MHz", sb, total_show_bw);
        else                   snprintf(s_bandsum, sizeof s_bandsum, "%s", sb);
    }
    s_sigwarn[0] = 0;
    {   /* 无信号 / 未联网提示：数据有效且持续 8 秒才显示。亮屏、后台刚解冻或程序刚启动时的空数据不算 */
        static uint32_t bad_since;
        uint32_t nowm = millis();
        if (d.valid && (!connected || lv == 0)) { if (!bad_since) bad_since = nowm | 1; }
        else bad_since = 0;
        if (bad_since && nowm - bad_since >= 8000)
            snprintf(s_sigwarn, sizeof s_sigwarn, "<div class='card warn'><b>%s</b><div class='k'>%s</div></div>",
                     lv == 0 ? "无网络信号" : "未连接互联网", lv == 0 ? "请检查 SIM 卡或换个位置" : "已注册网络，但数据连接未建立");
    }
    rescue_entry(s_rescueent, sizeof s_rescueent);
    {
        const char *cur = g_net_pending[0] ? g_net_pending : d.net_select;
        snprintf(s_netmode, sizeof s_netmode, "自动");
        for (int k = 0; k < 4; k++) if (!strcmp(g_netmodes[k].v, cur)) snprintf(s_netmode, sizeof s_netmode, "%s", g_netmodes[k].lab);
    }
    if (d.sms_n > 0) { char sn[96]; html_esc(sn, sizeof sn, d.sms[0].num); snprintf(s_smslast, sizeof s_smslast, "%s · %s", sn, d.sms[0].date); }
    else             snprintf(s_smslast, sizeof s_smslast, "暂无短信");
    if (d.sms_unread > 0) snprintf(s_smsbadge, sizeof s_smsbadge, "<span class='badge n'>%d</span>", d.sms_unread);
    else s_smsbadge[0] = 0;
    {
        int o = snprintf(s_wpsel, sizeof s_wpsel, "<div class='wps'>");
        for (int k = 0; k < NWALLS; k++)
            APPEND(s_wpsel, o,
                          "<a href='act:wp:%s' id='wpt-%s' class='wpo wp-%s%s'><span class='wpl'>%s</span></a>",
                          g_walls[k], g_walls[k], g_walls[k], strcmp(g_walls[k], g_wallname) ? "" : " on", g_wall_labels[k]);
        snprintf(s_wpsel + o, sizeof s_wpsel - o, "</div>");
    }
    /* WiFi QR payload (drawn natively into #qr) */
    {
        char esc_s[140], esc_k[140];
        qr_escape(esc_s, sizeof esc_s, d.wifi_ssid);
        qr_escape(esc_k, sizeof esc_k, d.wifi_key);
        if (!d.wifi_ssid[0]) g_qr_text[0] = 0;
        else if (!d.wifi_key[0] || strstr(d.wifi_enc, "none")) snprintf(g_qr_text, sizeof g_qr_text, "WIFI:T:nopass;S:%s;;", esc_s);
        else snprintf(g_qr_text, sizeof g_qr_text, "WIFI:T:WPA;S:%s;P:%s;;", esc_s, esc_k);
    }
    if (path && strstr(path, "upgrade.html")) {         /* 微信付款码：只在等待付款时画 */
        struct upg u;
        upg_read(&u);
        snprintf(g_qr_text, sizeof g_qr_text, "%s", !strcmp(u.st, "pay") ? u.url : "");
    }
    static char s_rxv[12], s_rxu[8], s_txv[12], s_txu[8];
    s_rxv[0] = s_rxu[0] = s_txv[0] = s_txu[0] = 0;
    sscanf(s_rxs, "%11s %7s", s_rxv, s_rxu);
    sscanf(s_txs, "%11s %7s", s_txv, s_txu);
    t[i++] = (struct kv){ "RXV", s_rxv };         t[i++] = (struct kv){ "RXU", s_rxu };
    t[i++] = (struct kv){ "TXV", s_txv };         t[i++] = (struct kv){ "TXU", s_txu };
    t[i++] = (struct kv){ "DATE", s_date };       t[i++] = (struct kv){ "CMODE", cmode };
    t[i++] = (struct kv){ "GENSUB", s_gensub };   t[i++] = (struct kv){ "BANDSUM", s_bandsum };
    t[i++] = (struct kv){ "SIGQ", sigq };         t[i++] = (struct kv){ "SIGQC", sigqc };
    t[i++] = (struct kv){ "QBARS", s_qbars };     t[i++] = (struct kv){ "SIGWARN", s_sigwarn };
    t[i++] = (struct kv){ "RESCUEENT", s_rescueent };
    t[i++] = (struct kv){ "RSRPX", s_rsrpx };     t[i++] = (struct kv){ "SINRX", s_sinrx };
    t[i++] = (struct kv){ "RSRPW", s_rsrpw };     t[i++] = (struct kv){ "SINRW", s_sinrw };
    t[i++] = (struct kv){ "SINRC", sinrc };       t[i++] = (struct kv){ "NETMODE", s_netmode };
    t[i++] = (struct kv){ "SMSLAST", s_smslast }; t[i++] = (struct kv){ "SMSBADGE", s_smsbadge };
    t[i++] = (struct kv){ "WPSEL", s_wpsel };
    t[i++] = (struct kv){ "CHGSTATE", d.charger_connect ? "充电中" : "电池" };
    t[i++] = (struct kv){ "COVERCLASS", g_cover ? "on" : "off" };
    t[i++] = (struct kv){ "COVERSTATE", g_cover ? "按电源键唤醒时先显示时钟和信号" : "唤醒直接进入界面" };
    t[i++] = (struct kv){ "COVERSHORT", g_cover ? "先显示时钟" : "直接进入" };
    t[i++] = (struct kv){ "COVERHINT", g_lock_state == 1 ? "滑动输入密码" : "滑动进入" };
    t[i++] = (struct kv){ "COVERTIME", s_time };

    /* ---- v3 tokens ---- */
    static char s_opshort[32], s_bandonly[16], s_arfcn[16], s_cvfootr[96], s_homerow2[1400], s_themeseg[400];
    static char s_celllock[3000], s_cltile[64], s_w24s[8], s_w5s[8], s_psms[8], s_pwrlab[24];
    snprintf(s_opshort, sizeof s_opshort, "%s", !strncmp(s_oper, "中国", 6) ? s_oper + 6 : s_oper);
    short_band(s_bandonly, sizeof s_bandonly, use_nr ? nr_band : d.band, use_nr);
    snprintf(s_arfcn, sizeof s_arfcn, "%ld", d.nr_channel);
    snprintf(s_w24s, sizeof s_w24s, "%s", g_w24 == 1 ? "已开" : "已关");
    snprintf(s_w5s, sizeof s_w5s, "%s", g_w5 == 1 ? "已开" : "已关");
    snprintf(s_psms, sizeof s_psms, "%s", g_wpsm == 1 ? "已开" : "已关");
    /* power words */
    char eta[24] = "", etaclk[24] = "";
    if (g_pwr.eta_min >= 0) {
        snprintf(eta, sizeof eta, "%d:%02d", g_pwr.eta_min / 60, g_pwr.eta_min % 60);
        time_t fin = now + (time_t)g_pwr.eta_min * 60; struct tm ft; localtime_r(&fin, &ft);
        snprintf(etaclk, sizeof etaclk, "%02d:%02d", ft.tm_hour, ft.tm_min);
    }
    int online = g_pwr.state == PWR_CHG || g_pwr.state == PWR_FAST || g_pwr.state == PWR_PC || g_pwr.state == PWR_DIRECT || g_pwr.state == PWR_FULL;
    const char *noeta = g_pwr.estimating ? "正在估算…" : d.bat_percent >= 95 ? "即将充满" : "充电中";
    const char *cvc = "";
    if (g_pwr.state == PWR_DIRECT) { cvc = "blue"; snprintf(s_cvfootr, sizeof s_cvfootr, "%s", g_pwr.drain ? "直供电 · 先放电到 60%" : "直供电 · 电池不充不放"); }
    else if (g_pwr.state == PWR_FULL) { cvc = "good"; snprintf(s_cvfootr, sizeof s_cvfootr, "已充满 · 可以拔掉充电器"); }
    else if (online) {          /* lock screen: show the charging power too */
        cvc = "good";
        const char *how = g_pwr.state == PWR_FAST ? "快充" : g_pwr.state == PWR_PC ? "电脑充电" : "充电";
        char w[24] = "";
        if (g_pwr.in_w >= 0.5) snprintf(w, sizeof w, " %.0f W", g_pwr.in_w);
        if (eta[0]) snprintf(s_cvfootr, sizeof s_cvfootr, "%s%s · 约 %s 充满", how, w, eta);
        else if (w[0] && g_pwr.estimating) snprintf(s_cvfootr, sizeof s_cvfootr, "%s%s · 估算中", how, w);
        else if (w[0] && d.bat_percent >= 95) snprintf(s_cvfootr, sizeof s_cvfootr, "%s%s · 即将充满", how, w);
        else if (w[0]) snprintf(s_cvfootr, sizeof s_cvfootr, "%s中 ·%s", how, w);
        else snprintf(s_cvfootr, sizeof s_cvfootr, "%s", noeta);
    }
    else snprintf(s_cvfootr, sizeof s_cvfootr, "%s 台 · 电量 %d%%", s_clients, d.bat_percent);
    { static char s_cvbat[64], s_cvnet[96];
      char tmp[96];
      if (g_pwr.state == PWR_DIRECT) snprintf(tmp, sizeof tmp, "直供电");
      else if (g_pwr.state == PWR_FULL) snprintf(tmp, sizeof tmp, "已充满");
      else if (g_pwr.state == PWR_OUT) snprintf(tmp, sizeof tmp, "对外供电");
      else if (online && eta[0]) snprintf(tmp, sizeof tmp, "%s 充满", eta);
      else if (online) snprintf(tmp, sizeof tmp, "充电中");
      else snprintf(tmp, sizeof tmp, "电池");
      fit_px(s_cvbat, sizeof s_cvbat, tmp, 62, 11);
      snprintf(tmp, sizeof tmp, "%s %s", s_opshort, s_bandonly);
      fit_px(s_cvnet, sizeof s_cvnet, tmp, 62, 11);
      t[i++] = (struct kv){ "CVBATL", s_cvbat }; t[i++] = (struct kv){ "CVNETL", s_cvnet }; }
    { const char *lab = g_pwr.state == PWR_FULL ? "已充满" : g_pwr.state == PWR_DIRECT ? "直供电" : g_pwr.state == PWR_FAST ? "快充" : g_pwr.state == PWR_PC ? "接电脑" :
                        g_pwr.state == PWR_CHG ? "充电中" : g_pwr.state == PWR_OUT ? "对外供电" : "电池";
      snprintf(s_pwrlab, sizeof s_pwrlab, "%s", lab); }
    /* 首页第二行：今日流量 / 已连接两格，下面是电源（接电）或电池（未接电）宽卡 */
    {
        char pwr[900];
        if (online) {
            const char *bc = g_pwr.state == PWR_DIRECT ? "blue" : "good";
            char top[96], tr[120], br[64];
            if (g_pwr.state == PWR_DIRECT) {
                if (g_pwr.drain) {             /* input suspended until the battery reaches 60 % */
                    snprintf(top, sizeof top, "直供电 · 先放电到 60%%");
                    snprintf(tr, sizeof tr, "<span class='blue'>到 60%% 后电源直供</span>");
                    snprintf(br, sizeof br, "输入暂停");
                } else {
                    snprintf(top, sizeof top, "直供电 · %.0f V 输入", g_pwr.in_v);
                    snprintf(tr, sizeof tr, "<span class='blue'>电池不充不放</span>");
                    snprintf(br, sizeof br, "输入 %.1f W", g_pwr.in_w);
                }
            } else if (g_pwr.state == PWR_FULL) {
                snprintf(top, sizeof top, "已充满 · %.0f V 输入", g_pwr.in_v);
                snprintf(tr, sizeof tr, "<span class='good'>电池已满</span>");
                snprintf(br, sizeof br, "可以拔掉充电器");
            } else {
                snprintf(top, sizeof top, "%s · %.0f W", g_pwr.state == PWR_FAST ? "充电中 · 快充" : s_pwrlab, g_pwr.in_w);
                if (eta[0]) snprintf(tr, sizeof tr, "约 <span class='n good eta'>%s</span> 充满", eta);
                else snprintf(tr, sizeof tr, "%s", noeta);
                if (etaclk[0]) snprintf(br, sizeof br, "预计 %s 充满", etaclk); else br[0] = 0;
            }
            snprintf(pwr, sizeof pwr,
                "<a href='act:sub:battery.html' class='card pwrc pwr2'><div class='pwt'><span class='k pl'>%s</span><span class='k pr'>%s</span></div>"
                "<div class='pwm'><span class='n pwp'>%d<span class='u'>%%</span></span><span class='pbar'><i class='%s' style='width:%d%%'></i></span></div>"
                "<div class='pwb k'><span class='pl'>电源已接入</span><span class='pr'>%s</span></div></a>",
                top, tr, d.bat_percent, bc, clampi(d.bat_percent, 2, 100), br);
        } else {
            char life[48] = "";
            if (g_pwr.state == PWR_BATT && g_pwr.empty_min > 0)
                snprintf(life, sizeof life, "约可用 %d 小时", (g_pwr.empty_min + 30) / 60);
            const char *bc = g_stat_lowbat ? "bad" : "good";
            snprintf(pwr, sizeof pwr,
                "<a href='act:sub:battery.html' class='card pwrc pwr2'><div class='pwt'><span class='k pl'>%s</span><span class='k pr'>%s</span></div>"
                "<div class='pwm'><span class='n pwp'>%d<span class='u'>%%</span></span><span class='pbar'><i class='%s' style='width:%d%%'></i></span></div>"
                "<div class='pwb k'><span class='pl'>未接电源</span><span class='pr'></span></div></a>",
                s_pwrlab, life, d.bat_percent, bc, clampi(d.bat_percent, 2, 100));
        }
        {   /* 今日流量 / 已连接 两格 */
            char dv[16], du[8], mv[16], mu[8], plan[64], bar[160], bands[48];
            fmt_vol(dv, sizeof dv, du, sizeof du, g_wd.valid ? g_wd.day : -1);
            fmt_vol(mv, sizeof mv, mu, sizeof mu, g_wd.valid ? g_wd.mon : -1);
            plan_text(plan, sizeof plan, bar, sizeof bar, "pbar");
            sta_band_text(bands, sizeof bands);
            snprintf(s_homerow2, sizeof s_homerow2,
                "<div class='duo'><a href='act:sub:dataplan.html' class='card half mini2'><span class='k'>今日流量</span>"
                "<div class='v'><span class='n'>%s</span><span class='u'>%s</span></div><span class='sub'>本月 %s %s · %s</span></a>"
                "<a href='act:sub:clients.html' class='card half mini2'><span class='k'>已连接</span>"
                "<div class='v'><span class='n'>%s</span><span class='u'>台</span></div><span class='sub'>%s</span></a></div>%s",
                dv, du, mv, mu, plan, s_clients, bands, pwr);
        }
    }
    {   /* follow wallpaper / dark / light */
        static const char *lab[3] = { "跟随壁纸", "深色", "浅色" };
        int o = snprintf(s_themeseg, sizeof s_themeseg, "<div class='blg bl3 thchips'>");
        for (int k = 0; k < 3; k++)
            APPEND(s_themeseg, o, "<a href='act:thememode:%d' class='blc%s'><b>%s</b></a>",
                          k, k == g_theme_mode ? " on" : "", lab[k]);
        snprintf(s_themeseg + o, sizeof s_themeseg - o, "</div>");
    }
    /* cell lock page + control tile */
    s_celllock[0] = 0;
    if (path && (strstr(path, "celllock") || strstr(path, "control"))) {
        celllock_refresh(0);
        if (g_cl_armed[0] && (int32_t)(millis() - g_cl_until) > 0) g_cl_armed[0] = 0;
    }
    int nrlk = cl_locked(g_cl_nr), ltelk = cl_locked(g_cl_lte);
    if (nrlk) { int lp = atoi(g_cl_nr); snprintf(s_cltile, sizeof s_cltile, "已锁定 PCI %d", lp); }
    else if (ltelk) snprintf(s_cltile, sizeof s_cltile, "已锁定 4G 小区");
    else if (d.nr_pci) snprintf(s_cltile, sizeof s_cltile, "未锁定 · PCI %d", d.nr_pci);
    else snprintf(s_cltile, sizeof s_cltile, "未锁定");
    if (path && strstr(path, "celllock")) {
        int o = 0;
        char bandnum[8] = "";
        { const char *bp = nr_band; while (*bp && (*bp < '0' || *bp > '9')) bp++; snprintf(bandnum, sizeof bandnum, "%s", bp); }
        if (!use_nr || !d.nr_pci) {
            APPEND(s_celllock, o,
                "<div class='card'><div class='k'>当前没有连接 5G 基站。锁基站只支持 5G（和 2333 面板一致）。</div></div>");
        } else {
            char key[64]; snprintf(key, sizeof key, "lock:%d:%ld:%s", d.nr_pci, d.nr_channel, bandnum);
            int here = nrlk && atoi(g_cl_nr) == d.nr_pci;
            char btn[160];
            if (here) snprintf(btn, sizeof btn, "<span class='pill good'><i></i>已锁定</span>");
            else snprintf(btn, sizeof btn, "<a href='act:cl:%s' class='mini-btn pri'>%s</a>", key, strcmp(g_cl_armed, key) ? "锁定" : "再点一次");
            APPEND(s_celllock, o,
                "<div class='card clcur'>%s<div class='k'>当前基站 · %s</div><span class='n clbig'>PCI %d</span><span class='u'>ARFCN %ld</span>"
                "<div class='k'>RSRP <span class='n hv'>%s</span> · SINR <span class='n hv'>%s</span></div></div>",
                btn, s_bandonly, d.nr_pci, d.nr_channel, s_rsrpx, s_sinrx);
            if (nrlk && !here) {
                int lp = 0; long la = 0; sscanf(g_cl_nr, "%d,%ld", &lp, &la);
                APPEND(s_celllock, o,
                    "<div class='card'><div class='k'>已锁定</div><div>PCI <span class='n'>%d</span> · ARFCN <span class='n'>%ld</span></div></div>", lp, la);
            }
            /* aggregated carriers (nrca: idx,pci,?,band,arfcn,bw,?,rsrp,...;) */
            char ca[256]; snprintf(ca, sizeof ca, "%s", d.nrca);
            int rows = 0;
            for (char *sv = NULL, *g = strtok_r(ca, ";", &sv); g; g = strtok_r(NULL, ";", &sv)) {
                char *f[12] = { 0 }; int nf = 0;
                for (char *sv2 = NULL, *x = strtok_r(g, ",", &sv2); x && nf < 12; x = strtok_r(NULL, ",", &sv2)) f[nf++] = x;
                if (nf < 5) continue;
                int pci = atoi(f[1]); long arf = atol(f[4]);
                if (pci == d.nr_pci && arf == d.nr_channel) continue;
                char k2[64]; snprintf(k2, sizeof k2, "lock:%d:%ld:%s", pci, arf, f[3]);
                if (!rows++) APPEND(s_celllock, o, "<div class='card list'><div class='k cap'>聚合载波</div>");
                APPEND(s_celllock, o,
                    "<div class='nb'><span class='nbl'><span class='n'>PCI %d</span> <span class='k'>n%s · %ld</span></span>"
                    "<span class='n nbv'>%s</span><a href='act:cl:%s' class='mini-btn'>%s</a></div>",
                    pci, f[3], arf, nf > 7 ? f[7] : "", k2, strcmp(g_cl_armed, k2) ? "锁定" : "再点一次");
            }
            if (rows) APPEND(s_celllock, o, "</div>");
        }
        APPEND(s_celllock, o,
            "<a href='act:cl:unlock' class='card resetbtn2'>解除所有锁定</a>"
            "<div class='k pxnote'>锁错基站可能会没信号。附近基站需要在「设置 · 高级设置」里打开信令解析后才有数据；这里列出当前基站和聚合载波。</div>");
    }
    static char s_stisp[512];
    {
        snprintf(s_stisp, sizeof s_stisp,
                 "<div class='stisp'><span class='stic'>联</span>"
                 "<span class='stit'><b>%s</b><span class='k'>%s · %s</span></span></div>", s_oper, cmode, s_bandonly);
    }
    t[i++] = (struct kv){ "STISP", s_stisp };
    t[i++] = (struct kv){ "OPERSHORT", s_opshort }; t[i++] = (struct kv){ "BANDONLY", s_bandonly };
    t[i++] = (struct kv){ "ARFCN", s_arfcn };       t[i++] = (struct kv){ "CVFOOTR", s_cvfootr };
    t[i++] = (struct kv){ "CVFOOTC", cvc };         t[i++] = (struct kv){ "HOMEROW2", s_homerow2 };
    {   /* 控制中心：WiFi 中继格 + 已连接设备条 */
        static char s_devbar[600];
        s_devbar[0] = 0;
        int ctl = path && strstr(path, "control");
        if (ctl) {
            char names[400], fit[400];
            client_names(names, sizeof names, &d, 3);
            fit_px(fit, sizeof fit, names, 150, 12);
            snprintf(s_devbar, sizeof s_devbar,
                     "<a href='act:sub:clients.html' class='card devbar'><span class='dl'>已连接 %s 台设备</span><span class='dr'>%s ›</span></a>",
                     s_clients, fit);
        }
        t[i++] = (struct kv){ "RLTILE", ctl ? rl_tile_html() : "" };
        t[i++] = (struct kv){ "DEVBAR", s_devbar };
    }
    t[i++] = (struct kv){ "THEMESEG", s_themeseg }; t[i++] = (struct kv){ "THEMEBASE", g_theme ? "light" : "dark" };
    t[i++] = (struct kv){ "CELLLOCK", s_celllock }; t[i++] = (struct kv){ "CLTILE", s_cltile };
    t[i++] = (struct kv){ "W24S", s_w24s };         t[i++] = (struct kv){ "W5S", s_w5s };
    {   /* nearby cells page */
        const char *nb = "";
        if (path && strstr(path, "nbr.html")) {
            nbr_serving_t sv; memset(&sv, 0, sizeof sv);
            sv.nr = use_nr && d.nr_pci > 0;
            sv.pci = sv.nr ? d.nr_pci : 0;          /* no LTE PCI in the datad snapshot */
            sv.arfcn = sv.nr ? d.nr_channel : 0;
            const char *bp = sv.nr ? nr_band : d.band;
            while (*bp && (*bp < '0' || *bp > '9')) bp++;
            snprintf(sv.band, sizeof sv.band, "%s", bp);
            snprintf(sv.rsrp, sizeof sv.rsrp, "%s", s_rsrpx);
            snprintf(sv.sinr, sizeof sv.sinr, "%s", s_sinrx);
            snprintf(sv.nrca, sizeof sv.nrca, "%s", d.nrca);
            celllock_refresh(0);
            if (cl_locked(g_cl_nr)) snprintf(sv.lock, sizeof sv.lock, "%s", g_cl_nr);
            if (g_cl_armed[0] && (int32_t)(millis() - g_cl_until) > 0) g_cl_armed[0] = 0;
            nb = nbr_body_html(&sv, g_cl_armed);
        }
        t[i++] = (struct kv){ "NBRBODY", nb };
    t[i++] = (struct kv){ "BSENTRY", (path && strstr(path, "nbr.html")) ? bs_entry_html() : "" };
    t[i++] = (struct kv){ "BSBODY", (path && strstr(path, "bandscan")) ? bs_page_html() : "" };
    t[i++] = (struct kv){ "UPGBODY", (path && strstr(path, "upgrade.html")) ? upg_page_html() : "" };
    t[i++] = (struct kv){ "RLENTRY", "" };
    }
    t[i++] = (struct kv){ "PSMS", s_psms };
    {   /* data usage card (network page) */
        static char s_usage[900];
        s_usage[0] = 0;
        if (path && (strstr(path, "signal") || strstr(path, "cover") || strstr(path, "dataplan") || strstr(path, "home"))) wwandst_refresh();
        if (path && strstr(path, "signal")) {
            if (g_wd.valid) {
                char mv[16], mu[8], dv[16], du[8], lv[16], lu[8], bar[160] = "", right[64];
                fmt_vol(mv, sizeof mv, mu, sizeof mu, g_wd.mon);
                fmt_vol(dv, sizeof dv, du, sizeof du, g_wd.day);
                plan_text(right, sizeof right, bar, sizeof bar, "pbar");
                char clr[32];
                if (g_wd.clearday > 0) snprintf(clr, sizeof clr, "每月 %d 日清零", g_wd.clearday); else snprintf(clr, sizeof clr, " ");
                (void)lv; (void)lu;
                /* two aligned rows (one-screen layout): 本月已用 / 今日已用; plan on the right; tap = 流量套餐 */
                snprintf(s_usage, sizeof s_usage,
                    "<a href='act:sub:dataplan.html' class='card usec'>"
                    "<div class='urow'><span class='k ur'>%s ›</span><span class='k ul'>本月已用</span><span class='n uv'>%s</span><span class='k uu'>%s</span></div>"
                    "<div class='urow'><span class='k ur'>%s</span><span class='k ul'>今日已用</span><span class='n uv'>%s</span><span class='k uu'>%s</span></div>%s</a>",
                    right, mv, mu, g_wd.clearday > 0 ? clr : "", dv, du, bar);
            }
        }
        t[i++] = (struct kv){ "USAGECARD", s_usage };
        static char s_dpseg[300], s_dpcap[1400], s_dpuse[500];
        if (path && (strstr(path, "cover") || strstr(path, "dataplan")) && g_wd.valid) {
            char mv[16], mu[8], dv[16], du[8], right[64], bar[160];
            fmt_vol(mv, sizeof mv, mu, sizeof mu, g_wd.mon);
            fmt_vol(dv, sizeof dv, du, sizeof du, g_wd.day);
            plan_text(right, sizeof right, bar, sizeof bar, "cvbar");
            if (plan_pct() >= 0) {      /* "53.9 GB · 3%" */
                snprintf(s_dpuse, sizeof s_dpuse,
                         "<div class='dprow'><span class='k'>本月已用</span><span class='dpr'><span class='n dpv'>%s</span><span class='k'> %s · %d%%</span></span></div>"
                         "%s<div class='dprow'><span class='k'>今日已用</span><span class='dpr'><span class='n dpv2'>%s</span><span class='k'> %s</span></span></div>"
                         "<div class='k dpnote'>每月 %d 日清零（跟随原厂设置）</div>",
                         mv, mu, plan_pct(), bar, dv, du, g_wd.clearday > 0 ? g_wd.clearday : 1);
            } else {
                snprintf(s_dpuse, sizeof s_dpuse,
                         "<div class='dprow'><span class='k'>本月已用</span><span class='dpr'><span class='n dpv'>%s</span><span class='k'> %s</span></span></div>"
                         "<div class='dprow'><span class='k'>今日已用</span><span class='dpr'><span class='n dpv2'>%s</span><span class='k'> %s</span></span></div>"
                         "<div class='k dpnote'>每月 %d 日清零（跟随原厂设置）</div>",
                         mv, mu, dv, du, g_wd.clearday > 0 ? g_wd.clearday : 1);
            }
        } else snprintf(s_dpuse, sizeof s_dpuse, "<div class='k'>正在读取用量…</div>");
        snprintf(s_dpseg, sizeof s_dpseg, "<a href='act:plan:cap' class='blc%s'><b>有上限</b></a><a href='act:plan:unl' class='blc%s'><b>不限量</b></a>",
                 g_plan_on ? " on" : "", g_plan_on ? "" : " on");
        if (g_plan_on) {
            static const int GB[6] = { 100, 200, 500, 1000, 2000, 3000 };
            int o = snprintf(s_dpcap, sizeof s_dpcap,
                             "<div class='card dpc'><div class='dphd'><span class='k'>每月上限</span><span class='dpr'><span class='n dpgb'>%d</span><span class='k'> GB</span></span></div><div class='blg dpg'>",
                             g_plan_gb);
            for (int k = 0; k < 6; k++)
                o += snprintf(s_dpcap + o, sizeof s_dpcap - o, "%s<a href='act:plan:set:%d' class='blc%s'><b>%dG</b></a>%s",
                              k == 3 ? "</div><div class='blg dpg'>" : "", GB[k], GB[k] == g_plan_gb ? " on" : "", GB[k], "");
            snprintf(s_dpcap + o, sizeof s_dpcap - o,
                     "</div><div class='blg dpst'><a href='act:plan:dec' class='blc'><b>-</b></a><span class='k dpsl'>每次 10 GB</span><a href='act:plan:inc' class='blc'><b>+</b></a></div></div>");
        } else snprintf(s_dpcap, sizeof s_dpcap, "<div class='card dpc'><div class='k'>不限量时只统计用量，不显示进度。</div></div>");
        t[i++] = (struct kv){ "DPSEG", s_dpseg };
        t[i++] = (struct kv){ "DPCAP", s_dpcap };   t[i++] = (struct kv){ "DPUSE", s_dpuse };
    }
    {   /* screen page: auto-off as six big tiles + summary label */
        static char s_aot[900], s_aolbl[32];
        static const char *lab[6] = { "从不", "30 秒", "1 分钟", "2 分钟", "5 分钟", "10 分钟" };
        int o = 0;
        for (int k = 0; k < 6; k++)
            APPEND(s_aot, o, "<a href='act:autooff:%d' class='aot%s'>%s</a>",
                          g_autooffs[k].ms, g_autooffs[k].ms == g_autooff_ms ? " on" : "", lab[k]);
        snprintf(s_aolbl, sizeof s_aolbl, "%s", "从不息屏");
        for (int k = 1; k < 6; k++)
            if (g_autooffs[k].ms == g_autooff_ms) snprintf(s_aolbl, sizeof s_aolbl, "%s后息屏", lab[k]);
        {
            static char s_aoshort[24];
            snprintf(s_aoshort, sizeof s_aoshort, "不息屏");
            for (int k = 1; k < 6; k++)
                if (g_autooffs[k].ms == g_autooff_ms) snprintf(s_aoshort, sizeof s_aoshort, "%s", lab[k]);
            t[i++] = (struct kv){ "AUTOOFFSHORT", s_aoshort };
        }
        t[i++] = (struct kv){ "AUTOOFFTILES", s_aot };
        static char s_wst[900], s_wslbl[48];
        static const int wsm[7] = { 0, 5, 10, 20, 30, 60, 120 };
        static const char *wsl[7] = { "从不", "5 分钟", "10 分钟", "20 分钟", "30 分钟", "1 小时", "2 小时" };
        int wo = 0;
        for (int k = 0; k < 7; k++)
            wo += snprintf(s_wst + wo, sizeof s_wst - wo, "<a href='act:wifisleep:%d' class='aot%s'>%s</a>",
                           wsm[k], wsm[k] == g_wifi_sleep_min ? " on" : "", wsl[k]);
        snprintf(s_wslbl, sizeof s_wslbl, "WiFi 从不休眠");
        for (int k = 1; k < 7; k++)
            if (wsm[k] == g_wifi_sleep_min) snprintf(s_wslbl, sizeof s_wslbl, "无设备 %s后关闭 WiFi", wsl[k]);
        {   /* short form for the half-width tile on the one-screen settings page */
            static char s_wsshort[32];
            snprintf(s_wsshort, sizeof s_wsshort, "WiFi 不休眠");
            for (int k = 1; k < 7; k++)
                if (wsm[k] == g_wifi_sleep_min) snprintf(s_wsshort, sizeof s_wsshort, "无设备 %s关", wsl[k]);
            t[i++] = (struct kv){ "WSLEEPSHORT", s_wsshort };
        }
        t[i++] = (struct kv){ "WSLEEPTILES", s_wst };
        t[i++] = (struct kv){ "WSLEEPLBL", s_wslbl };
        t[i++] = (struct kv){ "AUTOOFFLBL", s_aolbl };
    }         t[i++] = (struct kv){ "PWRLABEL", s_pwrlab };
    return i;
}

static void refresh_status_cache(void)
{
    struct kv t[320];
    (void)build_kv(t, NULL);
}

static const char *kv_get(struct kv *t, int n, const char *key)
{
    for (int i = 0; i < n; i++)
        if (!strcmp(t[i].k, key)) return t[i].v ? t[i].v : "";
    return "";
}

static const char *custom_page_html(const char *path)
{
    static char out[PAGE_HTML_CACHE_CAP];
    const char *tmpl = read_template_cached(path);
    const char *start, *end, *body, *gt;
    char *body_src;
    size_t len;
    struct kv t[320];
    int n;
    char raw_title[96], title[160];
    const char *base;
    char *filled;
    int o;

    if (!tmpl) return NULL;
    start = tmpl;
    end = tmpl + strlen(tmpl);
    body = strcasestr(tmpl, "<body");
    if (body) {
        gt = strchr(body, '>');
        if (gt) {
            start = gt + 1;
            end = strcasestr(start, "</body>");
            if (!end) end = tmpl + strlen(tmpl);
        }
    }
    len = (size_t)(end - start);
    body_src = malloc(len + 1);
    if (!body_src) return NULL;
    memcpy(body_src, start, len);
    body_src[len] = 0;

    n = build_kv(t, path);
    filled = apply_template(body_src, t, n);
    free(body_src);

    base = strrchr(path, '/');
    base = base ? base + 1 : path;
    if (!function_title_from_html(tmpl, raw_title, sizeof raw_title))
        function_label_from_name(raw_title, sizeof raw_title, base);
    html_esc(title, sizeof title, raw_title);

    o = snprintf(out, sizeof out,
                 "<!DOCTYPE html><html lang=\"zh-CN\">"
                 "<head><meta charset=\"UTF-8\"><link rel=\"stylesheet\" href=\"style.css\"></head>"
                 "<body class=\"%s\">"
                 "%s"
                 "<div class=\"subtop\"><a href=\"act:backfunc\" id=\"bk\" class=\"bk\"></a>"
                 "<a href=\"act:backfunc\" class=\"tl\">%s</a></div>"
                 "<div class=\"custom-page\">",
                 kv_get(t, n, "THEME"), kv_get(t, n, "STATUSBAR"), title);
    if (o < 0) o = 0;
    if (o < (int)sizeof(out) - 1) {
        size_t room = sizeof(out) - (size_t)o - 1;
        size_t fl = strlen(filled);
        if (fl > room) fl = room;
        memcpy(out + o, filled, fl);
        o += (int)fl;
        out[o] = 0;
    }
    if (o < (int)sizeof(out) - 1)
        snprintf(out + o, sizeof(out) - (size_t)o,
                 "</div>%s<div class=\"pgpad\"></div></body></html>",
                 kv_get(t, n, "TOAST"));
    return out;
}

/* Build the data-filled HTML for a page (returns a static buffer). */
static const char *page_html(const char *path)
{
    if (path_is_function_page(path)) return custom_page_html(path);
    const char *tmpl = read_template_cached(path);   /* cache templates with mtime invalidation */
    if (!tmpl) return NULL;
    struct kv t[320];
    int n = build_kv(t, path);
    char *html = apply_template(tmpl, t, n);
    return html;
}

static void invalidate_render_html_cache(void)
{
    g_render_html_cache_len = 0;
    g_render_html_cache_path[0] = 0;
    g_render_html_cache_css_mtime = -1;
}

/* ---- power menu: three large round buttons with native-drawn glyphs
 * (litehtml can't render a power symbol / circular arrow / X reliably). The
 * HTML provides the circle placeholders (#pmc-*) + labels + tap targets; we
 * fill the disc and draw the glyph centered over each. ---- */
#define PM_PI 3.14159265358979

static void pm_disc(int cx, int cy, int rad, int r, int g, int b, int a)
{
    html_view_fill_round_rect(cx - rad, cy - rad, rad * 2, rad * 2, rad, r, g, b, a);
}

/* thick line segment (a-b) as a filled quad */
static void pm_line(double x1, double y1, double x2, double y2, double th, int r, int g, int b)
{
    double dx = x2 - x1, dy = y2 - y1, len = sqrt(dx * dx + dy * dy);
    if (len < 0.001) return;
    double nx = -dy / len * th / 2.0, ny = dx / len * th / 2.0;
    int xs[4] = { (int)(x1 + nx + 0.5), (int)(x2 + nx + 0.5), (int)(x2 - nx + 0.5), (int)(x1 - nx + 0.5) };
    int ys[4] = { (int)(y1 + ny + 0.5), (int)(y2 + ny + 0.5), (int)(y2 - ny + 0.5), (int)(y1 - ny + 0.5) };
    html_view_fill_poly(xs, ys, 4, r, g, b, 255);
}

/* annular sector (ring band) from a0..a1 degrees (math angles; screen y down) */
static void pm_arc(int cx, int cy, double ro, double ri, int a0, int a1, int r, int g, int b)
{
    int xs[160], ys[160], N = 0;
    for (int a = a0; a <= a1 && N < 158; a += 8) {
        double t = a * PM_PI / 180.0;
        xs[N] = cx + (int)(ro * cos(t) + 0.5); ys[N] = cy - (int)(ro * sin(t) + 0.5); N++;
    }
    for (int a = a1; a >= a0 && N < 160; a -= 8) {
        double t = a * PM_PI / 180.0;
        xs[N] = cx + (int)(ri * cos(t) + 0.5); ys[N] = cy - (int)(ri * sin(t) + 0.5); N++;
    }
    html_view_fill_poly(xs, ys, N, r, g, b, 255);
}

/* kind: 0=power, 1=reboot, 2=cancel */
static void pm_glyph(const char *sel, int kind, int cr, int cg, int cb)
{
    int x, y, w, h;
    if (!html_view_rect(sel, &x, &y, &w, &h)) return;
    int rad = (w < h ? w : h) / 2;
    int cx = x + w / 2, cy = y + h / 2;
    int armed = (kind == 0 && g_pwr_confirm == 1) || (kind == 1 && g_pwr_confirm == 2);
    if (armed) pm_disc(cx, cy, rad + 4, 0xff, 0xff, 0xff, 255);   /* white halo when armed */
    pm_disc(cx, cy, rad, cr, cg, cb, 255);
    const int W = 0xff;
    double ro = rad * 0.54, ri = ro - rad * 0.15, th = rad * 0.15;
    if (kind == 0) {                         /* power: ring with a gap at top + vertical bar */
        pm_arc(cx, cy, ro, ri, 110, 430, W, W, W);
        pm_line(cx, cy - rad * 0.06, cx, cy - rad * 0.60, th, W, W, W);
    } else if (kind == 1) {                  /* reboot: about 290 degree ring + arrowhead */
        int a0 = 120, a1 = 410;
        pm_arc(cx, cy, ro, ri, a0, a1, W, W, W);
        double te = a1 * PM_PI / 180.0, rm = (ro + ri) / 2.0;
        double pex = cx + rm * cos(te), pey = cy - rm * sin(te);
        double tx = -sin(te), ty = -cos(te), rxx = cos(te), ryy = -sin(te);
        double L = (ro - ri) * 1.9, hw = (ro - ri) * 1.25;
        int ax[3] = { (int)(pex + tx * L + 0.5), (int)(pex + rxx * hw + 0.5), (int)(pex - rxx * hw + 0.5) };
        int ay[3] = { (int)(pey + ty * L + 0.5), (int)(pey + ryy * hw + 0.5), (int)(pey - ryy * hw + 0.5) };
        html_view_fill_poly(ax, ay, 3, W, W, W, 255);
    } else {                                 /* cancel: X */
        double d = rad * 0.40;
        pm_line(cx - d, cy - d, cx + d, cy + d, th, W, W, W);
        pm_line(cx - d, cy + d, cx + d, cy - d, th, W, W, W);
    }
}

__attribute__((unused)) static void draw_power_menu(void)
{
    pm_glyph("#pmc-off",    0, 0xd2, 0x48, 0x3c);   /* red */
    pm_glyph("#pmc-reboot", 1, 0xe0, 0x89, 0x2a);   /* orange */
    pm_glyph("#pmc-cancel", 2, 0x4a, 0x51, 0x5c);   /* gray */
}

static int st_hist_max(const int *hist, int n)
{
    int mx = 10;
    for (int i = 0; i < n; i++) if (hist[i] > mx) mx = hist[i];
    return mx;
}

static void st_chart_grid(int x, int y, int w, int h)
{
    const int dark = !g_theme;
    const int r = dark ? 0x2d : 0xb8;
    const int g = dark ? 0x3c : 0xcc;
    const int b = dark ? 0x4a : 0xd8;
    const int a = dark ? 150 : 180;

    html_view_fill_rect(x + 1, y + h / 3, w - 2, 1, r, g, b, a);
    html_view_fill_rect(x + 1, y + h * 2 / 3, w - 2, 1, r, g, b, a);
}

static void st_draw_one_chart(const char *sel, const int *hist, int n, int r, int g, int b)
{
    int x, y, w, h;
    if (!html_view_rect(sel, &x, &y, &w, &h)) return;
    st_chart_grid(x, y, w, h);
    if (n >= 2) {
        html_view_polyline(x + 3, y + 3, w - 6, h - 6, hist, n, 0, st_hist_max(hist, n), r, g, b, 2, 24);
    } else if (n == 1) {
        int cy = y + h - 6 - (hist[0] * (h - 12)) / st_hist_max(hist, n);
        html_view_fill_round_rect(x + w - 10, cy - 3, 6, 6, 3, r, g, b, 255);
    }
}

/* ---- 测速 v2 native parts ---- */
static const int g_st_ticks[8] = { 0, 5, 10, 50, 100, 250, 500, 1000 };
static double st_frac(double v)            /* 0..1 along the dial; ticks evenly spaced */
{
    if (v <= 0) return 0;
    for (int i = 0; i < 7; i++)
        if (v <= g_st_ticks[i + 1]) return (i + (v - g_st_ticks[i]) / (g_st_ticks[i + 1] - g_st_ticks[i])) / 7.0;
    return 1;
}

/* 测速 v3 native parts. The ring and the live chart are repainted at up to 25 fps by
 * speedtest_anim_tick(): the page is laid out once, the clean background under each
 * widget is kept, every frame restores it and repaints. DIRTYFB on this QPIC panel
 * always pushes the whole frame (~30 ms whatever the clip), so one flush per frame. */
struct st_slot { int x, y, w, h, valid; uint16_t *bg; int cap; };
static struct st_slot g_stg, g_stl;        /* ring, live chart */
static int g_st_capture;                   /* set by render(): this pass draws into the live fb */
static int g_st_disp_up = -1;
static uint32_t g_st_anim_at;

static void st_slot_capture(struct st_slot *sl, int x, int y, int w, int h)
{
    if (sl->cap < w * h) {
        free(sl->bg);
        sl->bg = malloc(sizeof(uint16_t) * w * h);
        sl->cap = sl->bg ? w * h : 0;
    }
    if (!sl->bg) { sl->valid = 0; return; }
    sl->x = x; sl->y = y; sl->w = w; sl->h = h; sl->valid = 1;
    html_view_save_rect(x, y, w, h, sl->bg);
}

static const int ST_DL0[3] = { 0x1f, 0xd1, 0xd6 }, ST_DL1[3] = { 0x2f, 0x6f, 0xe0 };
static const int ST_UL0[3] = { 0xa9, 0x70, 0xff }, ST_UL1[3] = { 0xff, 0x5f, 0xb8 };

/* Anti-aliased ring band (centre-line radius R, width wd) from angle hi down to lo
 * (math degrees, y up; the span must sit inside (-90, 270]). Coverage comes from each
 * pixel's distance to the band and, with caps, to the two round end caps; colour runs
 * c0 at hi to c1 at lo. */
static void st_aa_ring(float cx, float cy, float R, float wd, float hi, float lo,
                       const int *c0, const int *c1, int alpha, int caps)
{
    float hw = wd / 2.0f, span = hi - lo;
    if (span <= 0) return;
    float th = hi * (float)PM_PI / 180, tl = lo * (float)PM_PI / 180;
    float hx = cx + R * cosf(th), hy = cy - R * sinf(th), lx = cx + R * cosf(tl), ly = cy - R * sinf(tl);
    int x0 = (int)floorf(cx - R - hw - 1), x1 = (int)ceilf(cx + R + hw + 1);
    int y0 = (int)floorf(cy - R - hw - 1), y1 = (int)ceilf(cy + R + hw + 1);
    for (int py = y0; py <= y1; py++) {
        float dy = py + 0.5f - cy;
        for (int px = x0; px <= x1; px++) {
            float dx = px + 0.5f - cx, d = sqrtf(dx * dx + dy * dy);
            float band = hw + 0.5f - fabsf(d - R);
            if (band <= 0) continue;
            if (band > 1) band = 1;
            float a = atan2f(-dy, dx) * 180.0f / (float)PM_PI;
            if (a <= -90) a += 360;
            float cov = 0, t;
            if (a >= lo && a <= hi) { cov = band; t = (hi - a) / span; }
            else {
                if (!caps) continue;
                float ex = px + 0.5f - hx, ey = py + 0.5f - hy, fx = px + 0.5f - lx, fy = py + 0.5f - ly;
                float dh = sqrtf(ex * ex + ey * ey), dl = sqrtf(fx * fx + fy * fy);
                float dm = dh < dl ? dh : dl;
                cov = hw + 0.5f - dm;
                if (cov <= 0) continue;
                if (cov > 1) cov = 1;
                t = dh < dl ? 0 : 1;
            }
            html_view_fill_rect(px, py, 1, 1, c0[0] + (int)((c1[0] - c0[0]) * t), c0[1] + (int)((c1[1] - c0[1]) * t),
                                c0[2] + (int)((c1[2] - c0[2]) * t), (int)(alpha * cov));
        }
    }
}

/* idle: the GO button — glow, faint fill, a thin teal→purple ring, 开始 */
static void st_paint_go(int x, int y, int w, int h)
{
    float cx = x + w / 2.0f, cy = y + h / 2.0f, R = 86;
    html_view_aa_disc(cx, cy, R + 22, 0x1f, 0xd1, 0xd6, 10);
    html_view_aa_disc(cx, cy, R + 12, 0x1f, 0xd1, 0xd6, 12);
    html_view_aa_disc(cx, cy, R + 4, 0x1f, 0xd1, 0xd6, 14);
    html_view_aa_disc(cx, cy, R - 2, 0x1f, 0xd1, 0xd6, 22);
    st_aa_ring(cx, cy, R, 4, 270, 90, ST_UL0, ST_DL0, 255, 0);    /* left half: purple bottom → teal top */
    st_aa_ring(cx, cy, R, 4, 90, -90, ST_DL0, ST_UL0, 255, 0);    /* right half: teal top → purple bottom */
    draw_center_text_px((int)cx, (int)cy - 17, "开始", 34, 0, 0xff, 0xff, 0xff, 255);
}

/* running: 240° progress ring + big number, no needle. The track and the tick labels
 * never change, so they are painted once before the slot background is captured;
 * each animation frame then only adds the progress arc and the number. */
#define ST_RING_GEOM float cx = x + w / 2.0f, cy = y + 90, R = 80   /* 4 px of air inside the slot */
static void st_paint_ring_static(int x, int y, int w, int h)
{
    static const int TRK[3] = { 0x26, 0x33, 0x47 };
    ST_RING_GEOM;
    html_view_clip_rect(x, y, w, h);
    st_aa_ring(cx, cy, R, 12, 210, -30, TRK, TRK, 255, 1);
    for (int i = 0; i < 8; i++) {
        double a = (210 - 240.0 * i / 7) * PM_PI / 180.0;
        char lab[8]; snprintf(lab, sizeof lab, "%d", g_st_ticks[i]);
        draw_center_text_px((int)lround(cx + 58 * cos(a)), (int)lround(cy - 58 * sin(a)) - 6, lab, 11, 1, 0x8c, 0x99, 0xab, 255);
    }
    html_view_clip_rect(0, 0, 0, 0);
}
static void st_paint_ring(int x, int y, int w, int h)
{
    int up = !strcmp(g_st_phase, "upload");
    const int *c0 = up ? ST_UL0 : ST_DL0, *c1 = up ? ST_UL1 : ST_DL1;
    double cur = g_st_disp;
    ST_RING_GEOM;
    float lo = 210 - 240 * (float)st_frac(cur);
    /* never paint outside the slot: the animation only restores the slot's own
     * background, so anything outside it would pile up frame after frame */
    html_view_clip_rect(x, y, w, h);
    if (lo < 209.5f) st_aa_ring(cx, cy, R, 12, 210, lo, c0, c1, 255, 1);
    char num[16]; snprintf(num, sizeof num, cur < 10 ? "%.1f" : "%.0f", cur);
    draw_center_text_px((int)cx, (int)cy - 24, num, 44, 1, 0xff, 0xff, 0xff, 255);
    draw_center_text_px((int)cx, (int)cy + 37, up ? "上传 · Mbps" : !strcmp(g_st_phase, "download") ? "下载 · Mbps" : "准备中…",
                        11, 0, 0xa8, 0xb4, 0xc4, 255);
    html_view_clip_rect(0, 0, 0, 0);
}

/* live chart timeline: download then upload, each g_st_dur seconds */
static int st_seg_secs(void) { return g_st_dur > 0 ? g_st_dur : 15; }
static double st_ul_off(void) { return strcmp(g_st_dir, "both") ? 0 : st_seg_secs(); }
static double st_total_secs(void) { return strcmp(g_st_dir, "both") ? st_seg_secs() : 2.0 * st_seg_secs(); }
static double st_tip_target(void)
{
    if (!strcmp(g_st_phase, "upload")) return st_ul_off() + g_st_ul_n;
    if (!strcmp(g_st_phase, "download")) return g_st_dl_n;
    return g_st_dl_n > 0 ? g_st_dl_n : 0;
}
static double st_vmax_target(void)
{
    int m = 10;
    for (int i = 0; i < g_st_dl_n; i++) if (g_st_dl_hist[i] > m) m = g_st_dl_hist[i];
    for (int i = 0; i < g_st_ul_n; i++) if (g_st_ul_hist[i] > m) m = g_st_ul_hist[i];
    return m / 10.0 * 1.15;
}
/* one series: (t0,0), (t0+1,h[0]) … clipped at the animated tip */
static void st_live_series(const int *hist, int n, double t0, double tip, double T, double vmax,
                           int x0, int x1, int y0, int y1, const int *c, int active)
{
    if (n <= 0 || tip <= t0) return;
    double tend = t0 + n < tip ? t0 + n : tip;
    #define ST_V(k) ((k) <= 0 ? 0.0 : hist[(k) - 1] / 10.0)
    #define ST_X(t) (x0 + (x1 - x0) * (t) / T)
    #define ST_Y(v) (y1 - (y1 - y0) * ((v) > vmax ? 1.0 : (v) / vmax))
    int cx0 = (int)ceil(ST_X(t0)), cx1 = (int)floor(ST_X(tend));
    for (int px = cx0; px <= cx1; px++) {                    /* fill: fades from the line to the floor */
        double t = (px - x0) * T / (x1 - x0) - t0;
        int k = (int)t; double f = t - k;
        double v = ST_V(k) + (ST_V(k + 1) - ST_V(k)) * f;
        int top = (int)ST_Y(v), span = y1 - top;
        for (int py = top; py < y1; py++)
            html_view_fill_rect(px, py, 1, 1, c[0], c[1], c[2], 80 * (span - (py - top)) / (span > 0 ? span : 1));
    }
    double lx = ST_X(t0), ly = y1;
    for (int k = 1; k <= n && t0 + k - 1 < tend; k++) {
        double t = t0 + k, v = ST_V(k);
        if (t > tend) { v = ST_V(k - 1) + (v - ST_V(k - 1)) * (tend - (t - 1)); t = tend; }
        double nx = ST_X(t), ny = ST_Y(v);
        html_view_aa_line((float)lx, (float)ly, (float)nx, (float)ny, 2.0f, c[0], c[1], c[2], 255);
        lx = nx; ly = ny;
    }
    if (active) html_view_aa_disc((float)lx, (float)ly, 3.5f, 0xff, 0xff, 0xff, 255);
    #undef ST_V
    #undef ST_X
    #undef ST_Y
}
static void st_paint_live(int x, int y, int w, int h)
{
    const int dark = !g_theme;
    int x0 = x + 12, x1 = x + w - 12, y0 = y + 26, y1 = y + h - 20;
    double T = st_total_secs(), off = st_ul_off(), tip = g_st_disp_t, vmax = g_st_disp_vmax;
    int up = !strcmp(g_st_phase, "upload");
    char b[48];
    html_view_clip_rect(x, y, w, h);
    for (int k = 1; k <= 2; k++)
        html_view_fill_rect(x0, y0 + (y1 - y0) * k / 3, x1 - x0, 1, 0x2d, 0x3c, 0x4a, dark ? 150 : 90);
    if (off > 0) {
        int dx = (int)lround(x0 + (x1 - x0) * off / T);
        for (int yy = y0 - 4; yy < y1; yy += 6) html_view_fill_rect(dx, yy, 1, 3, 0x5b, 0x67, 0x78, 255);
        draw_center_text_px((x0 + dx) / 2, y1 + 5, "下载", 10, 0, 0x7f, 0x8c, 0x9e, 255);
        draw_center_text_px((dx + x1) / 2, y1 + 5, "上传", 10, 0, 0x7f, 0x8c, 0x9e, 255);
    } else {
        draw_center_text_px((x0 + x1) / 2, y1 + 5, strcmp(g_st_dir, "ul") ? "下载" : "上传", 10, 0, 0x7f, 0x8c, 0x9e, 255);
    }
    if (strcmp(g_st_dir, "ul"))
        st_live_series(g_st_dl_hist, g_st_dl_n, 0, tip, T, vmax, x0, x1, y0, y1, ST_DL0, !up);
    if (strcmp(g_st_dir, "dl"))
        st_live_series(g_st_ul_hist, g_st_ul_n, off, tip, T, vmax, x0, x1, y0, y1, ST_UL0, up);
    if (up || !strcmp(g_st_phase, "download")) snprintf(b, sizeof b, "%s · 峰值 %.0f", up ? "上传" : "下载", g_st_cur_peak);
    else snprintf(b, sizeof b, "%s", speedtest_phase_label(g_st_phase));
    html_view_draw_text_px(x0, y + 8, b, 11, 0, 0x9a, 0xa6, 0xb6, 255);
    draw_center_text_px((x0 + x1) / 2, y + 9, "点圆环停止", 10, 0, 0x6d, 0x7a, 0x8c, 255);
    int secs = (int)tip, tot = (int)T;
    snprintf(b, sizeof b, "0:%02d / 0:%02d", secs > tot ? tot : secs, tot);
    html_view_native_num(1);
    int tw = html_view_text_width_px(b, 13);
    html_view_draw_text_px(x1 - tw, y + 7, b, 13, 0, 0x9a, 0xa6, 0xb6, 255);
    html_view_native_num(0);
    html_view_clip_rect(0, 0, 0, 0);
}

static void maybe_dump_fb(drm_disp_t *d);

/* Owns the screen while a test runs: data refreshes then only touch the status bar
 * here instead of re-laying-out the whole page (~60 ms while the test eats CPU). */
static int g_st_sb_dirty;
static int speedtest_anim_owns(const char *path)
{
    return g_stg.valid && g_st_state == ST_STATE_RUNNING && path_is_speedtest(path);
}

/* Per-frame: ease the shown speed, chart tip and chart scale toward the latest samples
 * (they land once a second) and repaint, at most every 40 ms. */
static int speedtest_anim_tick(drm_disp_t *d, uint32_t now, const char *path)
{
    if (!g_stg.valid || g_st_state != ST_STATE_RUNNING) return 0;
    if (now - g_st_anim_at < 40) return 1;
    uint32_t dt = g_st_anim_at ? now - g_st_anim_at : 40;
    g_st_anim_at = now;
    if (dt > 200) dt = 200;
    int up = !strcmp(g_st_phase, "upload");
    double tgt = (!strcmp(g_st_phase, "download") || up) ? g_st_cur_mbps : 0;
    double nv = g_st_disp + (tgt - g_st_disp) * (1.0 - exp(-(double)dt / 420.0));
    if (fabs(tgt - nv) < 0.05) nv = tgt;
    /* the tip glides about one sample per second, so it is always moving a little */
    double tt = st_tip_target(), nt = g_st_disp_t + (tt - g_st_disp_t) * (1.0 - exp(-(double)dt / 600.0));
    if (fabs(tt - nt) < 0.01) nt = tt;
    double vt = st_vmax_target(), nm = g_st_disp_vmax + (vt - g_st_disp_vmax) * (1.0 - exp(-(double)dt / 400.0));
    if (fabs(vt - nm) < 0.01) nm = vt;
    int ring_dirty = fabs(nv - g_st_disp) > 0.004 || up != g_st_disp_up;
    int live_dirty = g_stl.valid && (fabs(nt - g_st_disp_t) > 0.003 || fabs(nm - g_st_disp_vmax) > 0.01 || up != g_st_disp_up);
    int sb_dirty = g_st_sb_dirty;
    if (!ring_dirty && !live_dirty && !sb_dirty) return 1;
    g_st_disp = nv; g_st_disp_t = nt; g_st_disp_vmax = nm; g_st_disp_up = up;
    html_view_set_clip_top(26);
    if (ring_dirty) {
        html_view_restore_rect(g_stg.x, g_stg.y, g_stg.w, g_stg.h, g_stg.bg);
        st_paint_ring(g_stg.x, g_stg.y, g_stg.w, g_stg.h);
    }
    if (live_dirty) {
        html_view_restore_rect(g_stl.x, g_stl.y, g_stl.w, g_stl.h, g_stl.bg);
        st_paint_live(g_stl.x, g_stl.y, g_stl.w, g_stl.h);
    }
    html_view_set_clip_top(0);
    if (sb_dirty) {
        g_st_sb_dirty = 0;
        struct kv t[320];
        (void)build_kv(t, path);         /* refreshes the status-bar strings */
        draw_native_statusbar();
        draw_sms_icon();
    }
    drm_disp_dirty(d, 0, 0, d->width - 1, d->height - 1);
    maybe_dump_fb(d);
    return 1;
}

static void draw_speedtest_widgets(void)
{
    int x, y, w, h;
    html_view_set_clip_top(26);
    if (html_view_rect("#st-go", &x, &y, &w, &h)) st_paint_go(x, y, w, h);
    if (html_view_rect("#st-ring", &x, &y, &w, &h)) {
        st_paint_ring_static(x, y, w, h);          /* part of the saved background */
        if (g_st_capture) st_slot_capture(&g_stg, x, y, w, h);
        st_paint_ring(x, y, w, h);
    }
    if (html_view_rect("#st-live", &x, &y, &w, &h)) {
        if (g_st_capture) st_slot_capture(&g_stl, x, y, w, h);
        st_paint_live(x, y, w, h);
    }
    if (html_view_rect("#st-gauge-dial", &x, &y, &w, &h)) {
        const int dark = !g_theme;
        double cur = speedtest_display_mbps();
        double scale = speedtest_display_peak_mbps();
        int pct = speedtest_pct(cur, scale);
        int rad = (w < h ? w : h) / 2 - 3;
        int cx = x + w / 2, cy = y + h / 2;
        double ang = (210.0 - 240.0 * pct / 100.0) * PM_PI / 180.0;
        double vx = cos(ang), vy = -sin(ang);
        double len = rad * 0.58, back = rad * 0.14, half = rad * 0.055;
        double tipx = cx + vx * len, tipy = cy + vy * len;
        double basex = cx - vx * back, basey = cy - vy * back;
        double px = -vy, py = vx;
        int nx[3] = {
            (int)(tipx + 0.5),
            (int)(basex + px * half + 0.5),
            (int)(basex - px * half + 0.5)
        };
        int ny[3] = {
            (int)(tipy + 0.5),
            (int)(basey + py * half + 0.5),
            (int)(basey - py * half + 0.5)
        };
        char num[32];
        const int outer_r = dark ? 0x0b : 0xd9;
        const int outer_g = dark ? 0x12 : 0xf0;
        const int outer_b = dark ? 0x1b : 0xf6;
        const int inner_r = dark ? 0x12 : 0xf7;
        const int inner_g = dark ? 0x20 : 0xfc;
        const int inner_b = dark ? 0x2e : 0xfe;
        const int track_r = dark ? 0x34 : 0xc0;
        const int track_g = dark ? 0x43 : 0xd8;
        const int track_b = dark ? 0x51 : 0xe2;
        const int tick_r = dark ? 0xd8 : 0x3d;
        const int tick_g = dark ? 0xe5 : 0x58;
        const int tick_b = dark ? 0xee : 0x65;
        const int num_r = dark ? 0xff : 0x18;
        const int num_g = dark ? 0xff : 0x33;
        const int num_b = dark ? 0xff : 0x42;
        const int unit_r = dark ? 0x9f : 0x68;
        const int unit_g = dark ? 0xb4 : 0x7f;
        const int unit_b = dark ? 0xc5 : 0x8b;
        const int hub_outer_r = dark ? 0xf4 : 0x18;
        const int hub_outer_g = dark ? 0xf7 : 0x33;
        const int hub_outer_b = dark ? 0xfb : 0x42;
        const int hub_inner_r = dark ? 0x12 : 0xf7;
        const int hub_inner_g = dark ? 0x20 : 0xfc;
        const int hub_inner_b = dark ? 0x2e : 0xfe;

        pm_disc(cx, cy, rad, outer_r, outer_g, outer_b, 255);
        pm_disc(cx, cy, rad - 5, inner_r, inner_g, inner_b, 255);
        pm_arc(cx, cy, rad - 12, rad - 20, -30, 210, track_r, track_g, track_b);
        if (pct > 0)
            pm_arc(cx, cy, rad - 12, rad - 20, (int)(210.0 - 240.0 * pct / 100.0), 210, 0x2f, 0xb8, 0xc9);
        for (int i = 0; i <= 10; i++) {
            double a = (210.0 - 240.0 * i / 10.0) * PM_PI / 180.0;
            double tx = cos(a), ty = -sin(a);
            pm_line(cx + tx * (rad - 30), cy + ty * (rad - 30),
                    cx + tx * (rad - 22), cy + ty * (rad - 22),
                    i % 5 == 0 ? 3.0 : 2.0, tick_r, tick_g, tick_b);
        }
        html_view_fill_poly(nx, ny, 3, 0xf0, 0xb2, 0x47, 255);
        pm_disc(cx, cy, 8, hub_outer_r, hub_outer_g, hub_outer_b, 255);
        pm_disc(cx, cy, 4, hub_inner_r, hub_inner_g, hub_inner_b, 255);
        snprintf(num, sizeof num, "%.1f", cur);
        draw_center_text_px(cx, cy + 38, num, 28, 1, num_r, num_g, num_b, 255);
        draw_center_text_px(cx, cy + 62, "Mbps", 12, 0, unit_r, unit_g, unit_b, 255);
    }
    st_draw_one_chart("#st-chart-dl", g_st_dl_hist, g_st_dl_n, 0x1f, 0xd1, 0xd6);
    st_draw_one_chart("#st-chart-ul", g_st_ul_hist, g_st_ul_n, 0xa9, 0x70, 0xff);
    html_view_set_clip_top(0);
}

static void capture_fb(drm_disp_t *d);   /* fwd: fb snapshot for modal overlay */
static void render_sms_overlay(drm_disp_t *d, int restore_background);

static void maybe_dump_fb(drm_disp_t *d)
{
    if (access("/tmp/u60-dumpfb", F_OK) != 0) return;
    unlink("/tmp/u60-dumpfb");            /* one dump per request: frames now come at 25 fps */
    FILE *f = fopen("/tmp/fb.dump.tmp", "wb");
    if (!f) return;
    const int W = d->width, H = d->height, pp = d->pitch_px;
    for (int y = 0; y < H; y++) {
        for (int x = 0; x < W; x++) {
            uint16_t px = d->fb[(size_t)(H - 1 - y) * pp + (W - 1 - x)];
            fwrite(&px, sizeof px, 1, f);
        }
    }
    fclose(f);
    rename("/tmp/fb.dump.tmp", "/tmp/fb.dump");
}

/* Fit (HTML-escaped) text into px at the given font size: cut at a UTF-8 boundary
 * (never inside an &entity;) and add "…". Used where a line must never wrap. */
static void fit_px(char *out, size_t cap, const char *src, int px, int size)
{
    if (out != src) snprintf(out, cap, "%s", src);
    if (html_view_text_width_px(out, size) <= px) return;
    size_t n = strlen(out);
    while (n > 0) {
        do n--; while (n > 0 && ((unsigned char)out[n] & 0xC0) == 0x80);   /* previous char start */
        size_t amp = n;                                                   /* not inside an entity */
        while (amp > 0 && out[amp - 1] != '&' && out[amp - 1] != ';' && n - amp < 8) amp--;
        if (amp > 0 && out[amp - 1] == '&') n = amp - 1;
        char tmp[256];
        snprintf(tmp, sizeof tmp, "%.*s…", (int)n, out);
        if (html_view_text_width_px(tmp, size) <= px || n == 0) { snprintf(out, cap, "%s", tmp); return; }
    }
}

/* Anti-aliased progress ring: starts at 12 o'clock, runs clockwise for frac of a turn,
 * round ends; a faint full track underneath. */
static void aa_ring_cw(float cx, float cy, float R, float wd, float frac, struct rgb c, struct rgb trk, int trk_a)
{
    float hw = wd / 2.0f, sweep = frac * 2 * (float)PM_PI;
    float ex = cx + R * sinf(sweep), ey = cy - R * cosf(sweep);
    for (int py = (int)floorf(cy - R - hw - 1); py <= (int)ceilf(cy + R + hw + 1); py++)
        for (int px = (int)floorf(cx - R - hw - 1); px <= (int)ceilf(cx + R + hw + 1); px++) {
            float dx = px + 0.5f - cx, dy = py + 0.5f - cy, d = sqrtf(dx * dx + dy * dy);
            float band = hw + 0.5f - fabsf(d - R);
            if (band <= 0) continue;
            if (band > 1) band = 1;
            html_view_fill_rect(px, py, 1, 1, trk.r, trk.g, trk.b, (int)(trk_a * band));
            if (frac <= 0.001f) continue;
            float th = atan2f(dx, -dy); if (th < 0) th += 2 * (float)PM_PI;
            float cov = 0;
            if (frac >= 0.999f || th <= sweep) cov = band;
            else {                                              /* round caps at both ends */
                float ax = px + 0.5f - cx, ay = py + 0.5f - (cy - R);
                float bx = px + 0.5f - ex, by = py + 0.5f - ey;
                float dm = fminf(sqrtf(ax * ax + ay * ay), sqrtf(bx * bx + by * by));
                cov = hw + 0.5f - dm;
                if (cov > 1) cov = 1;
            }
            if (cov > 0) html_view_fill_rect(px, py, 1, 1, c.r, c.g, c.b, (int)(255 * cov));
        }
}

static void cover_ring(const char *sel, float frac, struct rgb c, const char *txt)
{
    int x, y, w, h, x0, y0, x1, y1;
    if (!html_view_rect(sel, &x, &y, &w, &h)) return;
    const int dark = !g_theme;
    struct rgb fg = dark ? (struct rgb){ 0xff, 0xff, 0xff } : (struct rgb){ 0x14, 0x18, 0x20 };
    float cx = x + w / 2.0f, cy = y + h / 2.0f;
    aa_ring_cw(cx, cy, w / 2.0f - 4, 5, frac, c, fg, dark ? 46 : 40);
    html_view_native_num(1);
    html_view_text_bounds_px(txt, 16, &x0, &y0, &x1, &y1);
    draw_center_text_px((int)cx, (int)(cy - (y1 - y0) / 2.0f + 0.5f), txt, 16, 0, fg.r, fg.g, fg.b, 255);
    html_view_native_num(0);
}

/* 圆环中间两行：数值 + 小单位（锁屏本月流量） */
static void cover_ring_unit(const char *sel, float frac, struct rgb c, const char *val, const char *unit)
{
    int x, y, w, h, vx0, vy0, vx1, vy1, ux0, uy0, ux1, uy1;
    if (!html_view_rect(sel, &x, &y, &w, &h)) return;
    const int dark = !g_theme;
    struct rgb fg = dark ? (struct rgb){ 0xff, 0xff, 0xff } : (struct rgb){ 0x14, 0x18, 0x20 };
    struct rgb mu = dark ? (struct rgb){ 0xc8, 0xce, 0xd7 } : (struct rgb){ 0x3a, 0x43, 0x50 };
    float cx = x + w / 2.0f, cy = y + h / 2.0f;
    aa_ring_cw(cx, cy, w / 2.0f - 4, 5, frac, c, fg, dark ? 46 : 40);
    html_view_native_num(1);
    html_view_text_bounds_px(val, 15, &vx0, &vy0, &vx1, &vy1);
    if (!unit[0]) {
        draw_center_text_px((int)cx, (int)(cy - (vy1 - vy0) / 2.0f + 0.5f), val, 15, 0, fg.r, fg.g, fg.b, 255);
        html_view_native_num(0);
        return;
    }
    html_view_text_bounds_px(unit, 10, &ux0, &uy0, &ux1, &uy1);
    int th = (vy1 - vy0) + 3 + (uy1 - uy0);
    int top = (int)(cy - th / 2.0f + 0.5f);
    draw_center_text_px((int)cx, top, val, 15, 0, fg.r, fg.g, fg.b, 255);
    html_view_native_num(0);
    draw_center_text_px((int)cx, top + (vy1 - vy0) + 3, unit, 10, 0, mu.r, mu.g, mu.b, 255);
}

/* 锁屏小组件 (cover, design A): battery ring + network ring + data ring */
static void draw_cover_widgets(void)
{
    char b[16];
    struct rgb bc = { 0xf1, 0xf3, 0xf6 };
    if (g_theme) bc = (struct rgb){ 0x14, 0x18, 0x20 };
    switch (g_pwr.state) {
    case PWR_CHG: case PWR_FAST: case PWR_PC: case PWR_FULL: bc = (struct rgb){ 0x4f, 0xd0, 0x7a }; break;
    case PWR_DIRECT: bc = (struct rgb){ 0x1f, 0xd1, 0xd6 }; break;
    case PWR_OUT: bc = (struct rgb){ 0xf0, 0xb8, 0x4a }; break;
    default: if (g_stat_lowbat) bc = (struct rgb){ 0xff, 0x6a, 0x52 };
    }
    int pct = clampi(g_stat_bat, 0, 100);
    snprintf(b, sizeof b, "%d", pct);
    cover_ring("#cv-bat", pct / 100.0f, bc, b);
    cover_ring("#cv-sig", clampi(g_stat_sig, 0, 5) / 5.0f, (struct rgb){ 0x1f, 0xd1, 0xd6 }, g_stat_gen[0] ? g_stat_gen : "--");
    {   /* 本月流量：设了套餐按已用比例转，不限量按本月已过天数转 */
        char v[16] = "--";
        if (g_wd.valid) {
            double gb = g_wd.mon / 1073741824.0;
            snprintf(v, sizeof v, gb >= 100 ? "%.0f" : "%.1f", gb);
        }
        float fr;
        int pp = plan_pct();
        if (pp >= 0) fr = clampi(pp, 0, 100) / 100.0f;
        else {
            time_t now = time(NULL);
            struct tm tm;
            localtime_r(&now, &tm);
            static const int md[12] = { 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 };
            int y = tm.tm_year + 1900, days = md[tm.tm_mon];
            if (tm.tm_mon == 1 && ((y % 4 == 0 && y % 100) || y % 400 == 0)) days = 29;
            fr = tm.tm_mday / (float)days;
        }
        cover_ring_unit("#cv-data", fr, (struct rgb){ 0x5b, 0x97, 0xff }, v, g_wd.valid ? "GB" : "");
    }
}

static void render(drm_disp_t *disp, const char *path)
{
    /* the power menu is a bottom sheet over the current page */
    const char *menu_doc = strstr(path, "menu.html") ? path : NULL;
    if (menu_doc) { path = active_page_path(); if (!path[0]) path = g_pages[0]; }
    const char *html = page_html(path);
    if (!html) return;
    int special_page = strstr(path, "menu.html") || strstr(path, "lockscreen.html") || strstr(path, "cover.html");
    int scroll = special_page ? 0 : g_scroll;
    size_t html_len = strlen(html);
    int is_speedtest = path_is_speedtest(path);
    int has_charts = strstr(path, "charts.html") != NULL || is_speedtest ||
                     strstr(html, "cvspark") || strstr(html, "spk-");
    long long css_mtime = file_mtime_ns(UI_DIR "/style.css");
    if (is_speedtest) css_mtime ^= file_mtime_ns(UI_DIR "/speedtest.css");
    int cacheable = html_len > 0 && html_len < sizeof(g_render_html_cache);
    int reuse = cacheable && !has_charts &&
                 g_render_html_cache_scroll == scroll &&
                 g_render_html_cache_modal == g_modal &&
                 g_render_html_cache_sms_open == g_sms_open &&
                 g_render_html_cache_lock == g_lock_state &&
                 g_render_html_cache_css_mtime == css_mtime &&
                 g_render_html_cache_len == html_len &&
                 !strcmp(g_render_html_cache_path, path) &&
                 !strncmp(g_render_html_cache, html, html_len);
    html_view_set_scroll(scroll);
    if (!reuse) {
        g_page_h = html_view_render_html(html);
        if (cacheable) {
            memcpy(g_render_html_cache, html, html_len + 1);
            g_render_html_cache_len = html_len;
            snprintf(g_render_html_cache_path, sizeof g_render_html_cache_path, "%s", path);
            g_render_html_cache_scroll = scroll;
            g_render_html_cache_modal = g_modal;
            g_render_html_cache_sms_open = g_sms_open;
            g_render_html_cache_lock = g_lock_state;
            g_render_html_cache_css_mtime = css_mtime;
        } else {
            invalidate_render_html_cache();
        }
    }
    if (!reuse) {       /* a reused frame already has them: drawing again would pile up */
        draw_charts();  /* native polylines into any #chart-* placeholders */
        draw_qr();
        draw_icons();
        if (strstr(path, "cover.html")) draw_cover_widgets();
    }
    g_stg.valid = g_stl.valid = 0;
    g_st_capture = 1;
    if (!g_lock_state && (is_speedtest || g_st_home_open)) draw_speedtest_widgets();
    g_st_capture = 0;
    draw_native_statusbar();
    draw_sms_icon();    /* native envelope in the status bar when unread SMS */
    int H = disp->height, maxs = g_page_h - H;
    (void)maxs;
    if (menu_doc) {
        html_view_fill_rect(0, 0, disp->width, H, 0, 0, 0, 150);
        html_view_render_overlay(page_html(menu_doc));
        draw_icons();
        invalidate_render_html_cache();   /* next frame repaints the page without the sheet */
    }
    if (g_modal) {                                    /* dim page + second-level dialog */
        html_view_fill_rect(0, 28, disp->width, H - 28, 0, 0, 0, 150);
        capture_fb(disp);                             /* snapshot page+dim for fast modal refresh */
        html_view_render_overlay(modal_html());
    } else if (g_sms_open >= 0) {                     /* dim page + SMS detail dialog */
        html_view_fill_rect(0, 28, disp->width, H - 28, 0, 0, 0, 150);
        capture_fb(disp);
        render_sms_overlay(disp, 0);
    }
    drm_disp_dirty(disp, 0, 0, disp->width - 1, disp->height - 1);
    maybe_dump_fb(disp);
}

static void render_ext_view(drm_disp_t *disp, devui_ext_t *ext)
{
    devui_ext_render(ext, disp);
    draw_native_statusbar();
    draw_sms_icon();
    drm_disp_dirty(disp, 0, 0, disp->width - 1, disp->height - 1);
    maybe_dump_fb(disp);
}

/* Offscreen page bitmaps (logical, no rotation) for slide transitions.
 * During a drag: g_bufA = left page, g_bufB = right page (windowed by offset o:
 * window column x shows [left|right][x+o], o in 0..W). */
static uint16_t g_bufA[320 * 480], g_bufB[320 * 480];

/* Status bar stays pinned during a swipe (only the content below slides), so
 * we keep the already-rendered native status bar rows untouched and only
 * update the content area beneath it. */
#define SBAR_H DEVUI_EXT_STATUSBAR_H
/* Keep only a tiny hysteresis so page/scroll drags respond immediately,
 * without turning every resting-finger jitter into a swipe. */
#define DRAG_START_PX 2
#define DRAG_CANCEL_PX 8
#define SCROLL_INERTIA_MIN_V 180.0f
#define SCROLL_INERTIA_MAX_V 2200.0f
#define SCROLL_INERTIA_DECEL 3600.0f
#define STATE_RENDER_THROTTLE_MS 1500
#define STATE_RENDER_IDLE_THROTTLE_MS 2500
#define EXT_BACK_EDGE_PX 24
#define EXT_BACK_COMMIT_PX 56
#define EXT_BACK_MAX_DY 44
#define TOUCH_FRAME_MIN_MS 16
#define QUEUED_SWIPE_PX 52
#define QUEUED_SCROLL_PX 28
#define IDLE_SLEEP_ON_US 8000
#define IDLE_SLEEP_OFF_US 120000   /* screen off: only the power key matters; fewer wakeups */

static int motion_frame_due(uint32_t now, uint32_t *last)
{
    if (*last == 0 || now - *last >= TOUCH_FRAME_MIN_MS) {
        *last = now;
        return 1;
    }
    return 0;
}

static inline uint16_t *copy_rev_span(uint16_t *dp, const uint16_t *src, int n)
{
    for (int i = 0; i < n; i++) *dp-- = src[i];
    return dp;
}

static inline void fill_rev_span(uint16_t *dp, uint16_t px, int n)
{
    while (n-- > 0) *dp-- = px;
}

static float clamp_scroll_v(float v)
{
    if (v >  SCROLL_INERTIA_MAX_V) return  SCROLL_INERTIA_MAX_V;
    if (v < -SCROLL_INERTIA_MAX_V) return -SCROLL_INERTIA_MAX_V;
    return v;
}

static void compose_frame(drm_disp_t *d, int o)
{
    const int W = d->width, H = d->height, pp = d->pitch_px;
    int left;
    if (o < 0) o = 0; if (o > W) o = W;
    left = W - o;
    for (int y = SBAR_H; y < H; y++) {
        uint16_t *dp = d->fb + (size_t)(H - 1 - y) * pp + (W - 1);
        const uint16_t *lr = g_bufA + (size_t)y * W, *rr = g_bufB + (size_t)y * W;
        if (left > 0) dp = copy_rev_span(dp, lr + o, left);
        if (o > 0)    copy_rev_span(dp, rr, o);
    }
    /* Only the content area changes during a horizontal swipe. With the
     * framebuffer rotated 180 degrees that maps to the top physical rows. */
    drm_disp_dirty(d, 0, 0, W - 1, H - SBAR_H - 1);
    maybe_dump_fb(d);
}

/* Render the page pair for a drag direction into A(left)/B(right). dir>0 = next.
 * The current page keeps its scroll; the target page comes in at the top. */
static void render_page_to_pair_buf(uint16_t *buf, const char *path, const char *html, int scroll)
{
    if (!html) return;
    html_view_render_to_scroll(buf, html, scroll);
    html_view_target_begin(buf, scroll);
    draw_charts();
    draw_qr();
    draw_icons();
    if (!g_lock_state && (path_is_speedtest(path) || g_st_home_open)) draw_speedtest_widgets();
    draw_native_statusbar();
    draw_sms_icon();
    html_view_target_end();
}

static void prep_pair(int target, int dir)
{
    const char *h;
    if (dir > 0) {   /* next: left=current, right=target */
        html_view_set_scroll(g_scroll); h = page_html(g_pages[g_cur]);  render_page_to_pair_buf(g_bufA, g_pages[g_cur], h, g_scroll);
        html_view_set_scroll(0);        h = page_html(g_pages[target]); render_page_to_pair_buf(g_bufB, g_pages[target], h, 0);
    } else {         /* prev: left=target, right=current */
        html_view_set_scroll(0);        h = page_html(g_pages[target]); render_page_to_pair_buf(g_bufA, g_pages[target], h, 0);
        html_view_set_scroll(g_scroll); h = page_html(g_pages[g_cur]);  render_page_to_pair_buf(g_bufB, g_pages[g_cur], h, g_scroll);
    }
    html_view_set_scroll(g_scroll);
}

/* Settle the offset from o0 to o1 over a few frames. */
static void anim_o(drm_disp_t *d, int o0, int o1)
{
    const int FR = 3;
    for (int f = 1; f <= FR; f++) compose_frame(d, o0 + (o1 - o0) * f / FR);
}

/* Smooth vertical scrolling: the full page is pre-rendered once into g_scrollbuf
 * (logical, unrotated); each drag frame just blits the visible window + scrollbar
 * without re-parsing/re-layout, so it keeps up like the horizontal swipe. */
#define SCROLLMAX 2048
static uint16_t g_scrollbuf[320 * SCROLLMAX];
static int g_scroll_h;

static void scroll_blit(drm_disp_t *d, int scroll)
{
    const int W = d->width, Hh = d->height, pp = d->pitch_px;
    for (int y = SBAR_H; y < Hh; y++) {
        int sy = y + scroll;
        const uint16_t *src = (sy >= 0 && sy < g_scroll_h) ? &g_scrollbuf[(size_t)sy * W] : NULL;
        uint16_t *dp = d->fb + (size_t)(Hh - 1 - y) * pp + (W - 1);
        if (src) copy_rev_span(dp, src, W);
        else     fill_rev_span(dp, 0, W);
    }
    html_view_set_scroll(scroll);
    html_view_set_clip_top(SBAR_H);       /* keep native layers off the pinned status bar */
    draw_charts();
    draw_qr();
    draw_icons();
    html_view_set_clip_top(0);
    if (!g_lock_state && (path_is_speedtest(active_page_path()) || g_st_home_open)) draw_speedtest_widgets();
    /* The native status bar is pinned; dragging only changes the content below it.
     * With the framebuffer rotated 180 degrees, that content maps to the top
     * framebuffer rows, so the dirty rectangle intentionally excludes the tail. */
    drm_disp_dirty(d, 0, 0, W - 1, Hh - SBAR_H - 1);
}

/* fb snapshot for fast overlay refresh (modal toggles, segmented-control drag):
 * avoids re-laying-out the whole page on every interaction. */
static uint16_t g_overbg[320 * 480];
static void capture_fb(drm_disp_t *d) { memcpy(g_overbg, d->fb, (size_t)d->pitch_px * d->height * sizeof(uint16_t)); }
static void restore_fb(drm_disp_t *d) { memcpy(d->fb, g_overbg, (size_t)d->pitch_px * d->height * sizeof(uint16_t)); }

static int sms_scroll_metrics(void)
{
    int bx, by, bw, bh;
    int vx, vy, vw, vh;
    int old_scroll = g_sms_scroll;

    if (html_view_rect("#smsview", &vx, &vy, &vw, &vh) &&
        html_view_rect("#smsbody", &bx, &by, &bw, &bh)) {
        g_sms_view_x = vx;
        g_sms_view_y = vy;
        g_sms_view_w = vw;
        g_sms_view_h = vh;
        g_sms_scroll_max = bh > vh ? bh - vh : 0;
    } else {
        g_sms_view_x = g_sms_view_y = g_sms_view_w = g_sms_view_h = 0;
        g_sms_scroll_max = 0;
    }
    g_sms_scroll = clampi(g_sms_scroll, 0, g_sms_scroll_max);
    return g_sms_scroll != old_scroll;
}

static int sms_point_in_view(int x, int y)
{
    return g_sms_view_w > 0 && g_sms_view_h > 0 &&
           x >= g_sms_view_x && x < g_sms_view_x + g_sms_view_w &&
           y >= g_sms_view_y && y < g_sms_view_y + g_sms_view_h;
}

/* Redraw only the SMS dialog while dragging; the dimmed page remains cached. */
static void render_sms_overlay(drm_disp_t *d, int restore_background)
{
    if (restore_background) restore_fb(d);
    html_view_render_overlay(sms_modal_html());
    if (sms_scroll_metrics()) {
        restore_fb(d);
        html_view_render_overlay(sms_modal_html());
        (void)sms_scroll_metrics();
    }
    if (g_sms_scroll_max > 0 && g_sms_view_h > 0) {
        int content_h = g_sms_view_h + g_sms_scroll_max;
        int thumb_h = g_sms_view_h * g_sms_view_h / content_h;
        int travel, thumb_y;
        if (thumb_h < 18) thumb_h = 18;
        if (thumb_h > g_sms_view_h) thumb_h = g_sms_view_h;
        travel = g_sms_view_h - thumb_h;
        thumb_y = g_sms_view_y + g_sms_scroll * travel / g_sms_scroll_max;
        html_view_fill_round_rect(g_sms_view_x + g_sms_view_w - 3, thumb_y,
                                  3, thumb_h, 2, 0x8a, 0x92, 0x9d, 190);
    }
    drm_disp_dirty(d, 0, 0, d->width - 1, d->height - 1);
}

/* Redraw the modal over the cached dimmed page (fast: no page relayout). */
static void render_modal_overlay(drm_disp_t *d)
{
    restore_fb(d);
    html_view_render_overlay(modal_html());
    drm_disp_dirty(d, 0, 0, d->width - 1, d->height - 1);
}

static void handle_modal_tap(drm_disp_t *disp, int x, int y, uint32_t now,
                             int *need_render, int *animating)
{
    const char *act = html_view_click((float)x, (float)y);

    if (g_modal == 5) {
        if ((!strcmp(act, "act:prnet") || !strncmp(act, "act:pr:", 7)) && usb_switch_busy(now)) {
            g_pr_restore_at = 0;                 /* the hand choice wins over the auto-restore */
            if (!strcmp(act, "act:prnet")) {     /* flip what will be applied; the sheet stays open */
                g_pr_pend_net = !(g_pr_pend_net >= 0 ? g_pr_pend_net : usb_net_now());
                g_pr_net_pref = g_pr_pend_net;
                save_conf();
                g_pr_open_at = now;
                render_modal_overlay(disp);
                *animating = 1;
                return;
            }
            int mode = atoi(act + 7);
            if (mode == 2 && !pr_role_source() && !pr_peer_can_sink()) {
                snprintf(g_toast, sizeof g_toast, "充电器不能取电");
            } else {
                g_pr_pend_mode = mode;
                g_pr_mode_pref = mode;
                save_conf();
                if (mode == pr_current_mode())       /* already so: nothing to wait for */
                    snprintf(g_toast, sizeof g_toast, "%s", mode == 2 ? "正在给对方供电" : mode == 1 ? "直供电 · 电池不充" : "正在充电");
                else
                    snprintf(g_toast, sizeof g_toast, "USB 切换完就%s", mode == 2 ? "给对方供电" : mode == 1 ? "改为直供电" : "开始充电");
            }
            g_toast_pill = 1; g_toast_until = now + 2000;
            g_modal = 0;
            invalidate_render_html_cache();
            *need_render = 1;
            return;
        }
        if (!strncmp(act, "act:pr", 6)) g_pr_restore_at = 0;   /* a hand choice beats the auto-restore */
        if (!strcmp(act, "act:prnet")) {       /* toggle only: the sheet stays open, countdown restarts */
            int on = !usb_net_now();
            pr_apply(pr_current_mode(), on, now);
            g_pr_net_pref = on;
            save_conf();
            g_pr_open_at = now;
            render_modal_overlay(disp);
            *animating = 1;
        } else if (!strncmp(act, "act:pr:", 7)) {
            int mode = atoi(act + 7);
            if (mode == 2 && !pr_role_source() && !pr_peer_can_sink()) {
                snprintf(g_toast, sizeof g_toast, "充电器不能取电");
            } else {
                pr_apply(mode, -1, now);
                g_pr_mode_pref = mode;
                save_conf();
                if (mode == 2) snprintf(g_toast, sizeof g_toast, "正在给对方供电");
                else if (mode == 1) snprintf(g_toast, sizeof g_toast, "直供电 · 电池不充");
                else snprintf(g_toast, sizeof g_toast, "正在充电 · %d%%", clampi(g_stat_bat, 0, 100));
            }
            g_toast_pill = 1;
            g_toast_until = now + 2000;
            g_modal = 0;
            invalidate_render_html_cache();
            *need_render = 1;
        } else {
            int sx, sy, sw, sh;               /* tap outside the sheet: keep the current mode */
            if (!html_view_rect(".prsheet", &sx, &sy, &sw, &sh) || y < sy) { g_modal = 0; *need_render = 1; }
        }
        return;
    }

    if (g_modal == 4) {
        if (strncmp(act, "act:", 4)) return;
        const char *a = act + 4;
        if (!strcmp(a, "sigread")) {
            g_sig_read = !g_sig_read;
            (void)datad_set_signal_read(g_sig_read);
            signal_async_publish(NULL, 0);
            save_conf();
            snprintf(g_toast, sizeof g_toast, "信令读取已%s", g_sig_read ? "开启" : "关闭");
            g_toast_until = now + 1600;
            invalidate_render_html_cache();
            *need_render = 1;
        } else if (!strcmp(a, "sigparse")) {
            g_sig_parse = !g_sig_parse;
            (void)datad_set_signal_parse(g_sig_parse);
            signal_async_publish(NULL, 0);
            save_conf();
            rescan_pages_keep_current();
            invalidate_render_html_cache();
            snprintf(g_toast, sizeof g_toast, "信令解析已%s", g_sig_parse ? "开启" : "关闭");
            g_toast_until = now + 1600;
            *need_render = 1;
        } else if (!strcmp(a, "closemodal")) {
            g_modal = 0;
            *need_render = 1;
        }
        return;
    }

    char *sel = g_modal == 1 ? g_sel_sa : g_modal == 2 ? g_sel_nsa : g_sel_lte;
    const char *uni = g_modal == 1 ? g_uni_sa : g_modal == 2 ? g_uni_nsa : g_uni_lte;
    if (!strncmp(act, "act:", 4)) {
        const char *a = act + 4;
        if (!strncmp(a, "bsa:", 4) || !strncmp(a, "bnsa:", 5) || !strncmp(a, "blte:", 5)) {
            band_toggle(sel, 256, strchr(a, ':') + 1);
            render_modal_overlay(disp);
            *animating = 1;
        } else if (!strcmp(a, "mall")) {
            if (!strcmp(sel, uni)) sel[0] = 0;
            else snprintf(sel, 256, "%s", uni);
            render_modal_overlay(disp);
            *animating = 1;
        } else if (!strcmp(a, "minv")) {
            char u[256], out[256];
            int o = 0;
            snprintf(u, sizeof u, "%s", uni);
            for (char *tk = strtok(u, ","); tk; tk = strtok(NULL, ","))
                if (!band_in(sel, tk))
                    o += snprintf(out + o, sizeof out - o, "%s%s", o ? "," : "", tk);
            out[o] = 0;
            snprintf(sel, 256, "%s", out);
            render_modal_overlay(disp);
            *animating = 1;
        } else if (!strcmp(a, "mapply")) {
            if (sel[0]) {
                char cmd[360];
                if (g_modal == 3)
                    snprintf(cmd, sizeof cmd,
                             "ubus call zte_nwinfo_api nwinfo_set_lte_ext_band '{\"lte_band\":\"%s\"}' >/dev/null 2>&1 &",
                             sel);
                else
                    snprintf(cmd, sizeof cmd,
                             "ubus call zte_nwinfo_api nwinfo_set_nrbandlock '{\"nr5g_type\":\"%s\",\"nr5g_band\":\"%s\"}' >/dev/null 2>&1 &",
                             g_modal == 1 ? "0" : "1", sel);
                system(cmd);
            }
            snprintf(g_toast, sizeof g_toast, "锁频成功");
            g_toast_until = now + 1600;
            g_modal = 0;
            *need_render = 1;
        }
    } else {
        g_modal = 0;   /* band-lock dialogs keep their existing tap-outside behavior */
        *need_render = 1;
    }
}

/* Draw the sliding segmented-control highlight box at the finger, over cached fb.
 * n = number of cells. */
static void seg_box(drm_disp_t *d, int sx, int sy, int sw, int sh, int n, int fx)
{
    restore_fb(d);
    int cw = sw / n, bx = fx - cw / 2;
    if (bx < sx) bx = sx; if (bx > sx + sw - cw) bx = sx + sw - cw;
    html_view_fill_rect(bx, sy, cw, sh, 0x2f, 0x6f, 0xe0, 150);
    drm_disp_dirty(d, 0, 0, d->width - 1, d->height - 1);
}

/* Set backlight from a tap/drag x within the brightness bar [bx, bx+bw). */
static void set_bright_x(int x, int bx, int bw)
{
    if (bw <= 0) return;
    int f = (x - bx) * 100 / bw; if (f < 3) f = 3; if (f > 100) f = 100;
    int m = backlight_max(); if (m <= 0) m = 255;
    backlight_set(f * m / 100);
}

/* Screen off: fade backlight down (content still shown) then blank the fb. */
/* 亮灭屏联动：亮屏时通知 idle-guard 解冻后台服务 */
#define IDLE_GUARD "/data/ufi-tools/data/idle-guard.sh"
static void power_dark(int dark)
{
    /* nothing blocking here: it runs on the power-key path. idle-guard freezes
     * zwrt-datad a minute after the screen goes dark and thaws it on wake. */
    if (!dark && access(IDLE_GUARD, X_OK) == 0) system("sh " IDLE_GUARD " wake screen >/dev/null 2>&1 &");
}

static void screen_off(drm_disp_t *d)
{
    g_st_home_open = 0;           /* its 300 ms speedtest polling must not continue in the dark */
    power_dark(1);
    backlight_fade_off();
    invalidate_render_html_cache();
    memset(d->fb, 0, (size_t)d->pitch_px * d->height * sizeof(uint16_t));
    drm_disp_dirty(d, 0, 0, d->width - 1, d->height - 1);
}
/* Screen on: render, then "warm up" the command-mode panel with several frame
 * pushes while the backlight is still 0; this drives it past the idle-exit
 * transient invisibly, then fades the backlight up from 0. */
static void screen_on(drm_disp_t *d, const char *path)
{
    if (!g_charge_boot) power_dark(0);
    if (g_charge_boot) render_charge_boot(d);
    else               render(d, path);       /* backlight still 0 from screen_off */
    for (int k = 0; k < 5; k++) {            /* ~175ms of dark refresh */
        usleep(35000);
        drm_disp_dirty(d, 0, 0, d->width - 1, d->height - 1);
    }
    backlight_fade_on();   /* 0 -> user level */
}

static void screen_on_ext(drm_disp_t *d, devui_ext_t *ext)
{
    power_dark(0);
    render_ext_view(d, ext);                  /* backlight still 0 from screen_off */
    for (int k = 0; k < 5; k++) {
        usleep(35000);
        drm_disp_dirty(d, 0, 0, d->width - 1, d->height - 1);
    }
    backlight_fade_on();
}

/* Leave the fault PC/LR behind for addr2line: the binary is static and non-PIE. */
static void on_fault(int sig, siginfo_t *si, void *ctx)
{
    ucontext_t *uc = ctx;
    char b[160];
    int fd = open("/tmp/u60pro-devui-crash.log", O_WRONLY | O_CREAT | O_APPEND, 0644);
    if (fd >= 0) {
        int n = snprintf(b, sizeof b, "sig=%d addr=%p pc=%llx lr=%llx\n", sig, si->si_addr,
                         (unsigned long long)uc->uc_mcontext.pc, (unsigned long long)uc->uc_mcontext.regs[30]);
        (void)!write(fd, b, n);
        close(fd);
    }
    signal(sig, SIG_DFL);
    raise(sig);
}

int main(int argc, char **argv)
{
    if (argc >= 2 && !strcmp(argv[1], "upd")) return update_cli(argc - 2, argv + 2);
    {   /* 守护和安装脚本按这个 pid 认屏幕进程：busybox pidof 会把 devupd 软链也算成 u60pro-devui */
        FILE *pf = fopen("/tmp/u60pro-devui.pid", "w");
        if (pf) { fprintf(pf, "%d\n", (int)getpid()); fclose(pf); }
    }
    signal(SIGINT, on_sig);
    signal(SIGTERM, on_sig);
    signal(SIGPIPE, SIG_IGN);            /* 对端关闭 socket 时不能让 UI 退出 */
    {
        struct sigaction sa;
        memset(&sa, 0, sizeof sa);
        sa.sa_sigaction = on_fault;
        sa.sa_flags = SA_SIGINFO;
        sigaction(SIGSEGV, &sa, NULL);
        sigaction(SIGBUS, &sa, NULL);
        sigaction(SIGABRT, &sa, NULL);
    }

    g_charge_boot = boot_is_charge_mode();
    if (!g_charge_boot) {
        scan_pages();
        if (g_npages == 0) { fprintf(stderr, "no pages in %s\n", UI_DIR); return 1; }
    }

    drm_disp_t disp;
    if (drm_disp_init(&disp) != 0) { fprintf(stderr, "drm init failed\n"); return 1; }
    html_view_init(disp.fb, disp.width, disp.height, disp.pitch_px, 1, resolve_ui_font());
    html_view_set_num_font(UI_NUM_FONT);
    html_view_set_uidir(UI_DIR);

    touch_input_t touch;
    int touch_ok = touch_input_init(&touch, disp.width, disp.height) == 0;
    key_input_t key;     key_input_init(&key);
    backlight_init();
    (void)data_backend_init();
    (void)data_backend_commit_latest();

    if (!g_charge_boot && !touch_ok && boot_has_external_power()) {
        fprintf(stderr, "boot: forcing charge UI (touch missing, external power present)\n");
        g_charge_boot = 1;
    }

    int menu = 0, prev_press = 0, prev_lock = 0, was_on = 1, down_x = 0, down_y = 0;
    int eat_gesture = 0;   /* swallow the remainder of the swipe that dismissed the cover */
    int ctl_pending = 0;   /* 1 = brightness slider, 2 = segmented control: pressed, direction not known yet */
    char tap_page_before[300] = ""; int tap_menu_before = 0;
    int dragging = 0, drag_dir = 0, drag_target = 0;
    int scroll_dir = 0, scroll_start = 0;
    int sms_dragging = 0, sms_scroll_start = 0;
    int scroll_inertia = 0, scroll_track_valid = 0;
    int scroll_track_pos = 0;
    uint32_t drag_down_ms = 0;
    uint32_t scroll_track_ms = 0;
    uint32_t last_motion_frame = 0;
    float scroll_v = 0.0f, scroll_pos = 0.0f;
    int sliding = 0, bar_x = 0, bar_w = 0;   /* brightness slider drag */
    int segging = 0, seg_x = 0, seg_y = 0, seg_w = 0, seg_h = 0;   /* segmented control drag */
    int seg_which = 0, seg_n = 4;   /* 1 = net mode, 2 = auto-off, 3 = refresh */
    const int W = disp.width, H = disp.height;
    devui_ext_t ext;
    memset(&ext, 0, sizeof ext);
    ext.srv_fd = -1;
    int ext_ok = 0;
    if (!g_charge_boot) {
        ext_ok = devui_ext_init(&ext, W, H) == 0;
        if (!ext_ok) fprintf(stderr, "warning: external display socket disabled\n");
    }
    char menu_path[300], lock_path[300], cover_path[300];
    snprintf(menu_path, sizeof menu_path, "%s/menu.html", UI_DIR);
    snprintf(lock_path, sizeof lock_path, "%s/lockscreen.html", UI_DIR);
    snprintf(cover_path, sizeof cover_path, "%s/cover.html", UI_DIR);
    if (access(cover_path, R_OK) != 0) snprintf(cover_path, sizeof cover_path, "%s", g_pages[0]);

    /* lock pad takes priority over the power menu and the normal pages */
    /* lock states: 1=preview (page 1), 2=setup pad, 3=unlock pad */
    #define CUR_PATH ((g_lock_state == 1 || g_lock_state == 4) ? cover_path : g_lock_state ? lock_path : menu ? menu_path : active_page_path())

    load_conf();                          /* restore persisted UI settings */
    apply_wallpaper();
    mkdir(FUNCTIONS_DIR, 0755);
    speedtest_apply_saved_prefs();
    speedtest_poll(millis());
    if (!g_charge_boot) rescan_pages_keep_current();
    g_pages_dir_mtime = ui_scan_mtime_ns();
    g_pages_scan_at = millis();
    (void)datad_set_refresh_ms(g_refresh_ms);
    (void)datad_set_signal_read(g_sig_read);
    (void)datad_set_signal_parse(g_sig_parse);
    if (!g_charge_boot)
        signal_async_start();
    if (g_saved_bright >= 0) backlight_set(g_saved_bright);   /* restore brightness */
    if (!g_charge_boot) {
        load_pin();
        wifi_aux_refresh(1);                  /* prime page-2 switch states */
        /* 不再开机自启 USB 网络看门狗：它靠反复重做 usb_composition 追网络载波，
         * 会把正在进行的充电一次次掐断（原厂默认组合本就是 ECM 网卡，网线能自愈）。 */
        if (lock_enabled()) enter_lock(0);   /* boot straight into the unlock pad */
        render(&disp, CUR_PATH);
    } else {
        render_charge_boot(&disp);
    }
    uint32_t last_data = millis(), last_act = millis();
    int state_pending = 0;

    while (g_run) {
        uint32_t now = millis();
        int need_render = 0, animating = 0;
        int live_changed = data_backend_poll(now);
        if (live_changed) state_pending = 1;

        if (ext_ok && g_lock_state && devui_ext_active(&ext)) {
            devui_ext_deactivate(&ext);
            touch_input_clear_taps(&touch);
            need_render = 1;
        }
        if (ext_ok && !g_lock_state) {
            int ext_changed = devui_ext_poll(&ext, now);
            if (ext_changed) {
                dragging = 0; drag_dir = 0; scroll_dir = 0; sliding = 0; segging = 0;
                scroll_inertia = 0; scroll_track_valid = 0; scroll_v = 0.0f;
                menu = 0; g_modal = 0; g_sms_open = -1; subpage_close();
                touch_input_clear_taps(&touch);
                if (devui_ext_active(&ext)) {
                    refresh_status_cache();
                    if (backlight_is_on()) {
                        render_ext_view(&disp, &ext);
                        animating = 1;
                    }
                } else {
                    need_render = 1;
                }
            }
        }

        /* power key */
        int ev = key_input_poll(&key, now);
        if (ev == KEY_EV_SHORT || ev == KEY_EV_LONG) last_act = now;
        if (ev == KEY_EV_SHORT) {
            scroll_inertia = 0; scroll_track_valid = 0; scroll_v = 0.0f;
            if (backlight_is_on()) {
                screen_off(&disp);
                if (g_modal == 5) g_modal = 0;   /* 供电方式弹层不能带进锁屏封面（封面上点不到它） */
                if (!g_charge_boot && cover_wanted()) {
                    if (ext_ok) devui_ext_deactivate(&ext);
                    enter_cover();   /* power key locks / shows the cover */
                }
            } else {
                if (ext_ok && devui_ext_active(&ext) && !g_lock_state)
                    screen_on_ext(&disp, &ext);
                else
                    screen_on(&disp, g_charge_boot ? NULL : CUR_PATH);
            }
        } else if (ev == KEY_EV_LONG) {
            scroll_inertia = 0; scroll_track_valid = 0; scroll_v = 0.0f;
            if (ext_ok && devui_ext_active(&ext) && !g_lock_state) {
                if (!backlight_is_on()) screen_on_ext(&disp, &ext);
                else { devui_ext_deactivate(&ext); need_render = 1; }
            } else if (g_charge_boot) {
                if (!backlight_is_on()) screen_on(&disp, NULL);
            } else if (g_lock_state) {               /* no power menu while locked */
                if (!backlight_is_on()) screen_on(&disp, CUR_PATH);
            } else {
                menu = !menu; g_pwr_confirm = 0;
                if (!backlight_is_on()) screen_on(&disp, CUR_PATH);
                else need_render = 1;
            }
        }

        /* charger plugged in / pulled out: wake to the cover (lock screen) like a
         * phone does. Polled here because pwr_refresh only runs while rendering.
         * The state must hold for two reads (~0.5 s) so a USB-C role swap or a
         * flaky cable doesn't flash the screen. */
        if (!g_charge_boot) {
            static long plug_last = -1, plug_cand = -1;
            static uint32_t plug_at;
            if (!plug_at || now - plug_at >= 250) {
                plug_at = now ? now : 1;
                long on = sysfs_long("/sys/class/power_supply/usb/online", 0) ? 1 : 0;
                if (plug_last < 0) plug_last = on;                  /* boot: just remember it */
                else if (on != plug_last) {
                    if (plug_cand == on) {
                        plug_last = on; plug_cand = -1;
                        last_act = now;                             /* auto-off counts from here */
                        if (!backlight_is_on()) {
                            if (ext_ok && devui_ext_active(&ext) && !g_lock_state)
                                screen_on_ext(&disp, &ext);
                            else
                                screen_on(&disp, CUR_PATH);
                        } else need_render = 1;
                    } else plug_cand = on;
                } else plug_cand = -1;
            }
        }

        /* Type-C partner attached: wake and ask how to power (usb/online above only sees
         * us taking power, not giving it). Two equal reads (~0.5 s) to ride out role swaps. */
        if (!g_charge_boot) {
            static int pr_last = -1, pr_cand = -1;
            static uint32_t pr_at;
            if (!pr_at || now - pr_at >= 250) {
                pr_at = now ? now : 1;
                /* screenshot requests are served even when nothing re-renders (static page) */
                if (backlight_is_on() && access("/tmp/u60-dumpfb", F_OK) == 0) maybe_dump_fb(&disp);
                int att = pr_partner_present();
                if (access("/tmp/u60-prsheet-test", F_OK) == 0) {      /* simulate an attach (testing) */
                    unlink("/tmp/u60-prsheet-test");
                    pr_last = 0; pr_cand = 1; att = 1; g_pr_quiet_until = 0;
                }
                if (pr_last < 0) pr_last = att;                       /* boot: just remember it */
                else if (att != pr_last) {
                    if (pr_cand == att) {
                        pr_last = att; pr_cand = -1;
                        if (att && !pr_quiet(now))
                            g_pr_restore_at = now + 2500;            /* let PD / enumeration settle first */
                        if (att && !pr_quiet(now) && g_lock_state != 1 && g_lock_state != 2 && g_lock_state != 3) {
                            if (g_lock_state == 4) g_lock_state = 0;  /* plain cover: straight to the sheet */
                            if (ext_ok && devui_ext_active(&ext)) devui_ext_deactivate(&ext);
                            menu = 0; g_sms_open = -1;
                            g_modal = 5; g_pr_open_at = now;
                            last_act = now;
                            touch_input_clear_taps(&touch);
                            if (!backlight_is_on()) screen_on(&disp, CUR_PATH);
                            else need_render = 1;
                        } else if (!att && g_modal == 5) {
                            g_modal = 0; need_render = 1;
                        }
                        if (!att) g_pr_pend_mode = g_pr_pend_net = -1;   /* unplugged: nothing left to apply */
                    } else pr_cand = att;
                } else pr_cand = -1;
            }
            /* a choice made while USB was switching: apply it now that the switch is over */
            if ((g_pr_pend_mode >= 0 || g_pr_pend_net >= 0) && !usb_switch_busy(now)) {
                int pm = g_pr_pend_mode, pn = g_pr_pend_net;
                g_pr_pend_mode = g_pr_pend_net = -1;
                if (pr_partner_present()) {
                    if (pn >= 0 && (!pr_peer_can_sink() || pn == usb_net_now())) pn = -1;
                    if (pm < 0) pm = pr_current_mode();
                    if (pm != pr_current_mode() || pn >= 0) { pr_apply(pm, pn, now); need_render = 1; }
                }
            }
            /* re-apply the remembered choice (power mode always; network only towards a host) */
            if (g_pr_restore_at && (int32_t)(now - g_pr_restore_at) >= 0 && !usb_switch_busy(now)) {
                g_pr_restore_at = 0;
                if (pr_partner_present()) {
                    int host = pr_peer_can_sink(), mode = g_pr_mode_pref;
                    if (mode < 0 || (mode == 2 && !host)) mode = pr_current_mode();
                    int net = host ? g_pr_net_pref : -1;
                    if (net >= 0 && net == usb_net_now()) net = -1;
                    if (mode != pr_current_mode() || net >= 0) {
                        pr_apply(mode, net, now);
                        if (g_modal == 5) need_render = 1;
                    }
                }
            }
            if (g_modal == 5 && backlight_is_on()) {
                static uint32_t pr_tick;
                if (now - g_pr_open_at >= 15000) { g_modal = 0; need_render = 1; }   /* no choice: keep the current mode */
                else if (!need_render && now - pr_tick >= 250) { pr_tick = now; render_modal_overlay(&disp); }
            }
        }

        if (g_charge_boot) {
            if (live_changed && data_backend_commit_latest()) {
                state_pending = 0;
                need_render = 1;
            }
            touch_input_clear_taps(&touch);
            prev_press = 0;
            if (now - last_data >= 120) { need_render = 1; last_data = now; }
            if (need_render && backlight_is_on()) render_charge_boot(&disp);
            was_on = backlight_is_on();
            if (!animating) usleep(backlight_is_on() ? IDLE_SLEEP_ON_US : IDLE_SLEEP_OFF_US);
            continue;
        }

        /* touch: follow-finger swipe (pages) / drag (scroll) + tap actions */
        int x, y, pressed;
        int replay_release = 0;
        touch_input_read(&touch, &x, &y, &pressed);

        int on_now = backlight_is_on();
        if (on_now && !was_on) {          /* first frame after waking: drop the wake touch */
            touch_input_clear_taps(&touch);
            pressed = 0;
        }
        if (pressed && on_now) last_act = now;

        if (!on_now) {
            /* screen off: ignore touch entirely and discard any taps the panel
             * reported while dark, so they can't replay on wake. Power key is the
             * only way to wake (double-tap-to-wake removed). */
            touch_input_clear_taps(&touch);
            pressed = 0;
            scroll_inertia = 0; scroll_track_valid = 0; scroll_v = 0.0f;
            /* 按着屏幕时熄屏：手势状态不复位的话，亮屏后时钟/状态刷新都会被 !dragging 挡住 */
            dragging = 0; drag_dir = 0; scroll_dir = 0; sliding = 0; segging = 0; g_segdrag = 0;
            ctl_pending = 0;
        } else if (g_lock_state == 1 || g_lock_state == 4) {
            /* cover: clock + signal card, no actions. A swipe in any direction
             * opens the PIN pad (1) or dismisses the cover (4). */
            if (pressed && !prev_press) { down_x = x; down_y = y; }
            else if (pressed && prev_press) {
                int dx = x - down_x, dy = y - down_y;
                if (dx * dx + dy * dy > 22 * 22) {
                    if (g_lock_state == 1) { g_lock_state = 3; g_pin_entry[0] = 0; g_lock_err = 0; }
                    else g_lock_state = 0;
                    g_scroll = 0;
                    need_render = 1;
                    touch_input_clear_taps(&touch);
                    eat_gesture = 1;   /* the finger is still down: its release must not act on the page below */
                }
            }
        } else if (eat_gesture) {
            /* rest of the cover-dismiss swipe: swallow it until the finger lifts
             * (a release here once "tapped" a card on the page that appeared) */
            if (!pressed) eat_gesture = 0;
            touch_input_clear_taps(&touch);
            pressed = 0;
        } else if (g_lock_state) {
            /* PIN pad (3=unlock / 2=setup): tap only, no confirm key; a 4th digit
             * auto-submits. Drain the tap queue so a fast burst of taps all land
             * (the per-digit re-render would otherwise let polls miss presses). */
            int tx, ty;
            while (g_lock_state && touch_input_take_tap(&touch, &tx, &ty)) {
                const char *act = html_view_click((float)tx, (float)ty);
                if (strncmp(act, "act:", 4)) continue;
                const char *a = act + 4;
                if (!strncmp(a, "pin:", 4)) {
                    const char *k = a + 4;
                    int len = (int)strlen(g_pin_entry);
                    if (!strcmp(k, "del")) {
                        if (len > 0) g_pin_entry[len - 1] = 0;
                        g_lock_err = 0;
                    } else if (k[0] >= '0' && k[0] <= '9' && !k[1]) {
                        if (len < 4) { g_pin_entry[len] = k[0]; g_pin_entry[len + 1] = 0; len++; g_lock_err = 0; }
                        if (len == 4) {                       /* auto-submit */
                            if (g_lock_state == 2) {          /* setup: store + enable */
                                save_pin(g_pin_entry);
                                g_pin_entry[0] = 0; g_lock_state = 0;
                            } else if (!strcmp(g_pin_entry, g_pin)) {   /* unlock ok */
                                g_pin_entry[0] = 0; g_lock_err = 0; g_lock_state = 0;
                            } else {                          /* wrong: keep pad, show error */
                                g_pin_entry[0] = 0; g_lock_err = 1;
                            }
                        }
                    }
                    need_render = 1;
                } else if (!strcmp(a, "lockcancel")) {        /* abort PIN setup */
                    g_pin_entry[0] = 0; g_lock_err = 0; g_lock_state = 0; need_render = 1;
                }
            }
        } else if (ext_ok && devui_ext_active(&ext)) {
            if (!pressed) {
                int sx, sy, ex, ey;
                while (devui_ext_active(&ext) &&
                       touch_input_take_stroke(&touch, &sx, &sy, &ex, &ey)) {
                    int dx = ex - sx, dy = ey - sy;
                    int ady = dy < 0 ? -dy : dy;
                    if (sx <= EXT_BACK_EDGE_PX && sy >= ext.content_y &&
                        dx > EXT_BACK_COMMIT_PX && ady <= EXT_BACK_MAX_DY) {
                        devui_ext_deactivate(&ext);
                        touch_input_clear_taps(&touch);
                        need_render = 1;
                        break;
                    }
                }
            }

            if (devui_ext_active(&ext) && !pressed) {
                int tx, ty, cx, cy;
                while (touch_input_take_tap(&touch, &tx, &ty))
                    if (devui_ext_content_point(&ext, tx, ty, &cx, &cy))
                        devui_ext_handle_tap(&ext, cx, cy, now);
            }
            dragging = 0; drag_dir = 0; scroll_dir = 0; sliding = 0; segging = 0;
            scroll_inertia = 0; scroll_track_valid = 0; scroll_v = 0.0f;
        } else if (g_sms_open >= 0) {
            if (pressed && !prev_press) {
                down_x = x;
                down_y = y;
                sms_scroll_start = g_sms_scroll;
                sms_dragging = 0;
            } else if (pressed && prev_press) {
                int dy = y - down_y;
                int ady = dy < 0 ? -dy : dy;
                int next = clampi(sms_scroll_start - dy, 0, g_sms_scroll_max);
                if (!sms_dragging && ady > 6 && next != g_sms_scroll &&
                    sms_point_in_view(down_x, down_y))
                    sms_dragging = 1;
                if (sms_dragging) {
                    if (next != g_sms_scroll && motion_frame_due(now, &last_motion_frame)) {
                        g_sms_scroll = next;
                        render_sms_overlay(&disp, 1);
                        animating = 1;
                    }
                }
            } else if (!pressed && prev_press) {
                int dx = x - down_x, dy = y - down_y;
                int release_was_tap = dx * dx + dy * dy <= 14 * 14;
                if (sms_dragging) {
                    int next = clampi(sms_scroll_start - dy, 0, g_sms_scroll_max);
                    if (next != g_sms_scroll) {
                        g_sms_scroll = next;
                        render_sms_overlay(&disp, 1);
                        animating = 1;
                    }
                } else if (release_was_tap) {
                    const char *act = html_view_click((float)down_x, (float)down_y);
                    if (!strcmp(act, "act:smsclose")) {
                        sms_close(&touch, &need_render);
                    }
                }
                if (g_sms_open >= 0)
                    touch_input_drop_replayed_release(&touch, release_was_tap);
                sms_dragging = 0;
            } else if (!pressed) {
                /* A complete gesture can land while layout is busy. Collapse queued
                 * input to its newest stroke so it cannot replay below the dialog. */
                int sx, sy, ex, ey;
                if (touch_input_take_latest_stroke(&touch, &sx, &sy, &ex, &ey)) {
                    int tx = sx, ty = sy;
                    int dx = ex - sx, dy = ey - sy;
                    int was_tap = dx * dx + dy * dy <= 14 * 14;
                    int have_tap = touch_input_take_latest_tap(&touch, &tx, &ty);
                    if (was_tap) {
                        const char *act = html_view_click((float)(have_tap ? tx : sx),
                                                          (float)(have_tap ? ty : sy));
                        if (!strcmp(act, "act:smsclose")) {
                            sms_close(&touch, &need_render);
                        }
                    } else if (sms_point_in_view(sx, sy) && g_sms_scroll_max > 0) {
                        int next = clampi(g_sms_scroll - dy, 0, g_sms_scroll_max);
                        if (next != g_sms_scroll) {
                            g_sms_scroll = next;
                            render_sms_overlay(&disp, 1);
                            animating = 1;
                        }
                    }
                } else {
                    int tx, ty;
                    if (touch_input_take_latest_tap(&touch, &tx, &ty)) {
                        const char *act = html_view_click((float)tx, (float)ty);
                        if (!strcmp(act, "act:smsclose")) {
                            sms_close(&touch, &need_render);
                        }
                    }
                }
            }
        } else if (g_modal) {
            /* second-level band-lock dialog: tap only (level-1 is disabled) */
            if (pressed && !prev_press) {
                down_x = x;
                down_y = y;
            } else if (!pressed && prev_press) {
                int mdx = x - down_x, mdy = y - down_y;
                int modal_was_tap = mdx * mdx + mdy * mdy <= 14 * 14;
                if (modal_was_tap)
                    handle_modal_tap(&disp, x, y, now, &need_render, &animating);
                /* The renderer has already handled this release. Remove its matching
                 * queue entries before a closed modal exposes the button underneath. */
                touch_input_drop_replayed_release(&touch, modal_was_tap);
            } else if (!pressed) {
                int sx, sy, ex, ey, tx, ty;
                int have_stroke = touch_input_take_latest_stroke(&touch, &sx, &sy, &ex, &ey);
                int have_tap = touch_input_take_latest_tap(&touch, &tx, &ty);
                if (have_tap && (!have_stroke ||
                    (ex - sx) * (ex - sx) + (ey - sy) * (ey - sy) <= 14 * 14))
                    handle_modal_tap(&disp, tx, ty, now, &need_render, &animating);
            }
        } else {
            int maxs = g_page_h > H ? g_page_h - H : 0;
            if (pressed && scroll_inertia) {
                scroll_inertia = 0;
                scroll_track_valid = 0;
                scroll_v = 0.0f;
            }
            if (scroll_inertia && !pressed && !dragging && !menu && maxs > 0) {
                uint32_t dtm = now > scroll_track_ms ? now - scroll_track_ms : 0;
                if (dtm > 0) {
                    float dt = dtm / 1000.0f;
                    float dv = SCROLL_INERTIA_DECEL * dt;
                    if (scroll_v > 0.0f) {
                        scroll_v -= dv;
                        if (scroll_v < 0.0f) scroll_v = 0.0f;
                    } else if (scroll_v < 0.0f) {
                        scroll_v += dv;
                        if (scroll_v > 0.0f) scroll_v = 0.0f;
                    }
                    scroll_pos += scroll_v * dt;
                    int ns = (int)(scroll_pos + (scroll_pos >= 0.0f ? 0.5f : -0.5f));
                    if (ns < 0) { ns = 0; scroll_pos = 0.0f; scroll_v = 0.0f; }
                    if (ns > maxs) { ns = maxs; scroll_pos = (float)maxs; scroll_v = 0.0f; }
                    if (ns != g_scroll) {
                        g_scroll = ns;
                        if (motion_frame_due(now, &last_motion_frame)) {
                            scroll_blit(&disp, g_scroll);
                            animating = 1;
                        }
                    }
                    if (scroll_v == 0.0f || ns == 0 || ns == maxs) { scroll_inertia = 0; need_render = 1; }
                    scroll_track_ms = now;
                }
            }
            if (!pressed && !prev_press && !dragging && !menu) {
                int sx, sy, ex, ey, queued_motion = 0;
                if (touch_input_take_latest_stroke(&touch, &sx, &sy, &ex, &ey)) {
                    int qdx = ex - sx, qdy = ey - sy;
                    int qadx = qdx < 0 ? -qdx : qdx;
                    int qady = qdy < 0 ? -qdy : qdy;
                    if (!g_subpage[0] && g_npages > 1 && qadx >= QUEUED_SWIPE_PX && qadx > qady) {
                        int dir = qdx < 0 ? 1 : -1;
                        int target = (g_cur + (dir > 0 ? 1 : g_npages - 1)) % g_npages;
                        int o_now = dir > 0 ? -qdx : (W - qdx);
                        if (o_now < 0) o_now = 0;
                        if (o_now > W) o_now = W;
                        scroll_inertia = 0;
                        scroll_track_valid = 0;
                        scroll_v = 0.0f;
                        prep_pair(target, dir);
                        anim_o(&disp, o_now, dir > 0 ? W : 0);
                        g_cur = target;
                        g_scroll = 0;
                        invalidate_render_html_cache();
                        need_render = 1;
                        animating = 1;
                        last_motion_frame = now;
                        queued_motion = 1;
                        touch_input_clear_taps(&touch);
                    } else if (qady >= QUEUED_SCROLL_PX && qady >= qadx && maxs > 0) {
                        int bufh = g_page_h > SCROLLMAX ? SCROLLMAX : g_page_h;
                        uint32_t t0 = millis();
                        const char *hp = page_html(CUR_PATH);
                        uint32_t t1 = millis();
                        int rh = hp ? html_view_render_tall(g_scrollbuf, hp, bufh) : g_page_h;
                        fprintf(stderr, "scroll prerender: html %u ms, render %u ms, h=%d len=%zu page_h=%d path=%s\n",
                                t1 - t0, millis() - t1, rh, hp ? strlen(hp) : 0, g_page_h, CUR_PATH);
                        int ns;
                        g_scroll_h = rh > bufh ? bufh : rh;
                        maxs = g_scroll_h > H ? g_scroll_h - H : 0;
                        ns = g_scroll - qdy;
                        if (ns < 0) ns = 0;
                        if (ns > maxs) ns = maxs;
                        scroll_inertia = 0;
                        scroll_track_valid = 0;
                        scroll_v = 0.0f;
                        if (ns != g_scroll) {
                            g_scroll = ns;
                            scroll_pos = (float)g_scroll;
                            scroll_blit(&disp, g_scroll);
                            animating = 1;
                            last_motion_frame = now;
                        }
                        queued_motion = 1;
                        touch_input_clear_taps(&touch);
                    }
                }
                if (!queued_motion) {
                    int tx, ty;
                    if (touch_input_take_latest_tap(&touch, &tx, &ty)) {
                        x = tx; y = ty;
                        down_x = tx; down_y = ty;
                        dragging = 1; drag_dir = 0; scroll_dir = 0; scroll_start = g_scroll; sliding = 0; segging = 0;
                        drag_down_ms = now;
                        scroll_inertia = 0;
                        scroll_track_valid = 0;
                        scroll_v = 0.0f;
                        last_motion_frame = 0;
                        replay_release = 1;
                        prev_press = 1;  /* reuse the normal release/action path below */
                    }
                }
            }
            if (pressed && !prev_press) {
                down_x = x; down_y = y; dragging = 1; drag_dir = 0; scroll_dir = 0; scroll_start = g_scroll; sliding = 0; segging = 0;
                last_motion_frame = 0;
                drag_down_ms = now;
                scroll_track_valid = 0; scroll_v = 0.0f;
                int bx, by, bw, bh;   /* slider / segmented control under the finger: only a candidate
                                       * until the gesture proves horizontal (or ends as a tap), so a
                                       * vertical scroll that starts on it never changes the setting */
                ctl_pending = 0;
                if (html_view_rect("#bright-bar", &bx, &by, &bw, &bh) &&
                    x >= bx && x < bx + bw && y >= by - 5 && y < by + bh + 5) {
                    ctl_pending = 1; bar_x = bx; bar_w = bw;
                } else {   /* segmented controls: net mode / auto-off / refresh */
                    int which = 0, n = 4;
                    if (html_view_rect("#netseg", &bx, &by, &bw, &bh) &&
                        x >= bx && x < bx + bw && y >= by - 4 && y < by + bh + 4) { which = 1; n = 4; }
                    else if (html_view_rect("#autoseg", &bx, &by, &bw, &bh) &&
                             x >= bx && x < bx + bw && y >= by - 4 && y < by + bh + 4) { which = 2; n = 6; }
                    else if (html_view_rect("#refreshseg", &bx, &by, &bw, &bh) &&
                             x >= bx && x < bx + bw && y >= by - 4 && y < by + bh + 4) { which = 3; n = 5; }
                    if (which) {
                        ctl_pending = 2; seg_which = which; seg_n = n;
                        seg_x = bx; seg_y = by; seg_w = bw; seg_h = bh;
                    }
                }
            }
            else if (pressed && dragging && !menu) {
                if (ctl_pending) {
                    int cdx = x - down_x, cdy = y - down_y;
                    int acx = cdx < 0 ? -cdx : cdx, acy = cdy < 0 ? -cdy : cdy;
                    if (acx > 8 && acx * 10 > acy * 12) {          /* clearly sideways: take the control */
                        if (ctl_pending == 1) {
                            sliding = 1;
                            set_bright_x(x, bar_x, bar_w);
                            render(&disp, CUR_PATH);
                        } else {
                            segging = 1; g_segdrag = seg_which;
                            render(&disp, CUR_PATH);
                            capture_fb(&disp);
                            seg_box(&disp, seg_x, seg_y, seg_w, seg_h, seg_n, x);
                        }
                        ctl_pending = 0;
                        last_motion_frame = now;
                        animating = 1;
                    } else if (acy > 8) {
                        ctl_pending = 0;                          /* vertical: it's a page scroll */
                    }
                }
                if (ctl_pending) { /* still undecided */ }
                else if (sliding) {
                    set_bright_x(x, bar_x, bar_w);
                    if (motion_frame_due(now, &last_motion_frame)) {
                        render(&disp, CUR_PATH);
                        animating = 1;
                    }
                }
                else if (segging) {
                    if (motion_frame_due(now, &last_motion_frame)) {
                        seg_box(&disp, seg_x, seg_y, seg_w, seg_h, seg_n, x);
                        animating = 1;
                    }
                }
                else {
                int dx = x - down_x, dy = y - down_y;
                int adx = dx < 0 ? -dx : dx, ady = dy < 0 ? -dy : dy;
                if (drag_dir == 0 && scroll_dir == 0) {
                    if (!g_subpage[0] && g_npages > 1 && adx > DRAG_START_PX && adx > ady) {
                        drag_dir = dx < 0 ? 1 : -1;
                        drag_target = (g_cur + (drag_dir > 0 ? 1 : g_npages - 1)) % g_npages;
                        prep_pair(drag_target, drag_dir);
                    } else if (ady > DRAG_START_PX && ady >= adx && maxs > 0) {
                        scroll_dir = 1; scroll_start = g_scroll;
                        int bufh = g_page_h > SCROLLMAX ? SCROLLMAX : g_page_h;  /* prerender once */
                        uint32_t t0 = millis();
                        const char *hp = page_html(CUR_PATH);
                        uint32_t t1 = millis();
                        int rh = hp ? html_view_render_tall(g_scrollbuf, hp, bufh) : g_page_h;
                        fprintf(stderr, "scroll prerender: html %u ms, render %u ms, h=%d len=%zu page_h=%d path=%s\n",
                                t1 - t0, millis() - t1, rh, hp ? strlen(hp) : 0, g_page_h, CUR_PATH);
                        g_scroll_h = rh > bufh ? bufh : rh;
                        maxs = g_scroll_h > H ? g_scroll_h - H : 0;
                        scroll_track_pos = g_scroll;
                        scroll_track_ms = now;
                        scroll_track_valid = 0;
                        scroll_v = 0.0f;
                    } else if (ady > DRAG_CANCEL_PX) dragging = 0;
                }
                if (drag_dir != 0) {
                    if (motion_frame_due(now, &last_motion_frame)) {
                        compose_frame(&disp, drag_dir > 0 ? -dx : (W - dx));
                        animating = 1;
                    }
                } else if (scroll_dir != 0) {
                    int ns = scroll_start - dy;
                    if (ns < 0) ns = 0;
                    if (ns > maxs) ns = maxs;
                    if (ns != g_scroll) {
                        if (scroll_track_ms && now > scroll_track_ms) {
                            float inst = (ns - scroll_track_pos) * 1000.0f / (float)(now - scroll_track_ms);
                            scroll_v = scroll_track_valid ? (scroll_v * 0.65f + inst * 0.35f) : inst;
                            scroll_v = clamp_scroll_v(scroll_v);
                            scroll_track_valid = 1;
                        }
                        g_scroll = ns;
                        scroll_pos = (float)g_scroll;
                        scroll_track_pos = g_scroll;
                        scroll_track_ms = now;
                        if (motion_frame_due(now, &last_motion_frame)) {
                            scroll_blit(&disp, g_scroll);
                            animating = 1;
                        }
                    }
                }
                }
            }
            else if (!pressed && prev_press) {
                if (ctl_pending) {                                 /* tap without movement */
                    if (ctl_pending == 1) { sliding = 1; set_bright_x(down_x, bar_x, bar_w); }
                    else { segging = 1; x = down_x; }
                    ctl_pending = 0;
                }
                int rel_dx = x - down_x, rel_dy = y - down_y;
                int release_was_tap = dragging && !sliding && !segging &&
                                      drag_dir == 0 && scroll_dir == 0 &&
                                      rel_dx * rel_dx + rel_dy * rel_dy <= 14 * 14;
                int dx = rel_dx;
                if (sliding) { save_conf(); need_render = 1; /* persist brightness after drag, show the final level */ }
                else if (segging) {   /* snap to nearest cell + apply */
                    int c = clampi((x - seg_x) * seg_n / (seg_w > 0 ? seg_w : 1), 0, seg_n - 1);
                    if (seg_which == 1) {
                        char cmd[160];
                        snprintf(cmd, sizeof cmd,
                            "ubus call zte_nwinfo_api nwinfo_set_netselect '{\"net_select\":\"%s\"}' >/dev/null 2>&1 &", g_netmodes[c].v);
                        system(cmd);
                        snprintf(g_net_pending, sizeof g_net_pending, "%s", g_netmodes[c].v);
                    } else if (seg_which == 2) {
                        g_autooff_ms = g_autooffs[c].ms; last_act = now; save_conf();
                    } else {
                        g_refresh_ms = normalize_refresh_ms(g_refresh_rates[c].ms);
                        (void)datad_set_refresh_ms(g_refresh_ms);
                        if (g_refresh_ms > 0) {
                            if (data_backend_commit_latest()) need_render = 1;
                            state_pending = 0;
                        }
                        last_data = 0;
                        save_conf();
                    }
                    g_segdrag = 0; need_render = 1;
                }
                else if (dragging && drag_dir != 0) {            /* finish or snap back */
                    int adx = dx < 0 ? -dx : dx;
                    int commit = adx > W * 30 / 100;
                    int o_now = drag_dir > 0 ? -dx : (W - dx);
                    if (o_now < 0) o_now = 0; if (o_now > W) o_now = W;
                    anim_o(&disp, o_now, drag_dir > 0 ? (commit ? W : 0) : (commit ? 0 : W));
                    if (commit) { g_cur = drag_target; g_scroll = 0; }
                    /* After a page-swipe preview or snap-back, the on-screen pixels no
                     * longer match the cached HTML of the current page. Force a full
                     * re-render so native-drawn content from the neighbor page (for
                     * example charts) cannot leak onto the restored page. */
                    invalidate_render_html_cache();
                    need_render = 1;
                } else if (dragging && scroll_dir != 0) {   /* scroll settled */
                    uint32_t gdt = (drag_down_ms && now > drag_down_ms) ? (now - drag_down_ms) : 0;
                    if (gdt > 0) {
                        float rel_v = (-(float)(y - down_y)) * 1000.0f / (float)gdt;
                        if (scroll_track_valid) scroll_v = clamp_scroll_v(scroll_v * 0.55f + rel_v * 0.45f);
                        else                    scroll_v = clamp_scroll_v(rel_v);
                    }
                    if (fabsf(scroll_v) >= SCROLL_INERTIA_MIN_V && maxs > 0) {
                        scroll_inertia = 1;
                        scroll_pos = (float)g_scroll;
                        scroll_track_ms = now;
                    } else {
                        scroll_inertia = 0;
                        scroll_v = 0.0f;
                    }
                    need_render = 1;
                } else if (dragging) {                      /* tap -> action */
                    snprintf(tap_page_before, sizeof tap_page_before, "%s", active_page_path());
                    tap_menu_before = menu;
                    const char *act = html_view_click((float)x, (float)y);
                    if (!strncmp(act, "act:", 4)) {
                        const char *a = act + 4;
                        if (!strcmp(a, "poweroff")) {
                            if (g_pwr_confirm == 1) {        /* confirmed: blank first (instant feedback), then power off */
                                screen_off(&disp); system("poweroff");
                            } else { g_pwr_confirm = 1; g_pwr_until = now + 4000; need_render = 1; }
                        }
                        else if (!strcmp(a, "reboot")) {
                            if (g_pwr_confirm == 2) { screen_off(&disp); system("reboot"); }
                            else { g_pwr_confirm = 2; g_pwr_until = now + 4000; need_render = 1; }
                        }
                        else if (!strcmp(a, "close"))     { menu = 0; g_pwr_confirm = 0; need_render = 1; }
                        else if (!strcmp(a, "menu"))      { backlight_on(); menu = 1; g_pwr_confirm = 0; need_render = 1; }
                        else if (!strncmp(a, "sub:", 4)) {
                            if (subpage_open(a + 4)) {
                                menu = 0;
                                g_modal = 0;
                                g_sms_open = -1;
                                invalidate_render_html_cache();
                            } else {
                                snprintf(g_toast, sizeof g_toast, "页面不可用");
                                g_toast_until = now + 1600;
                            }
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strncmp(a, "func:", 5)) {
                            if (function_page_open(a + 5)) {
                                menu = 0;
                                g_modal = 0;
                                g_sms_open = -1;
                                invalidate_render_html_cache();
                            } else {
                                snprintf(g_toast, sizeof g_toast, "页面不可用");
                                g_toast_until = now + 1600;
                            }
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strcmp(a, "backfunc")) {
                            subpage_close();
                            menu = 0;
                            g_modal = 0;
                            g_sms_open = -1;
                            invalidate_render_html_cache();
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strcmp(a, "theme"))     { g_theme_mode = g_theme ? 1 : 2; apply_theme(); save_conf(); need_render = 1; }
                        else if (!strncmp(a, "thememode:", 10)) {
                            g_theme_mode = atoi(a + 10); if (g_theme_mode < 0 || g_theme_mode > 2) g_theme_mode = 0;
                            apply_theme(); save_conf(); invalidate_render_html_cache(); need_render = 1;
                        }
                        else if (!strcmp(a, "cover"))     { g_cover = !g_cover; save_conf(); need_render = 1; }
                        else if (!strncmp(a, "wifisleep:", 10)) {
                            int v = atoi(a + 10);
                            if (v >= 0 && v <= 240) { g_wifi_sleep_min = v; save_conf(); }
                            need_render = 1;
                        }
                        else if (!strncmp(a, "wp:", 3)) {
                            for (int k = 0; k < NWALLS; k++)
                                if (!strcmp(a + 3, g_walls[k])) {
                                    snprintf(g_wallname, sizeof g_wallname, "%s", g_walls[k]);
                                    apply_wallpaper(); save_conf();
                                    invalidate_render_html_cache();
                                }
                            need_render = 1;
                        }
                        else if (!strcmp(a, "revealkey")) { g_show_key = !g_show_key; need_render = 1; }
                        else if (!strcmp(a, "revealcell")) { g_show_cellid = !g_show_cellid; need_render = 1; }
                        else if (!strcmp(a, "revealimei")) { g_show_imei = !g_show_imei; need_render = 1; }
                        else if (!strcmp(a, "refreshambr")) {
                            system("(kill -USR1 $(pidof zwrt-datad 2>/dev/null) >/dev/null 2>&1) || true");
                            snprintf(g_toast, sizeof g_toast, "已请求刷新 AMBR");
                            g_toast_until = now + 1600;
                            need_render = 1;
                        }
                        else if (!strcmp(a, "neighbors")) {
                            g_neighbor_open = !g_neighbor_open;
                            invalidate_render_html_cache();
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strcmp(a, "spunit"))    { g_speed_bits = !g_speed_bits; save_conf(); need_render = 1; }
                        else if (!strcmp(a, "batpct"))    { g_show_batpct = !g_show_batpct; save_conf(); need_render = 1; }
                        else if (!strcmp(a, "nfc")) {
                            static devui_data_t dd; char cmd[120];
                            int on = (data_refresh_live(&dd) && dd.nfc_switch) ? 0 : 1;
                            snprintf(cmd, sizeof cmd,
                                "ubus call zwrt_nfc zwrt_nfc_wifi_set '{\"switch\":%d,\"flag\":2}'", on);
                            system(cmd);
                            need_render = 1;
                        }
                        else if (!strcmp(a, "wifi")) {   /* master: both main bands (wlan0+wlan2) */
                            int on = (g_w24 == 1 || g_w5 == 1);
                            const char *ic = on ? "down" : "up";
                            char cmd[160];
                            snprintf(cmd, sizeof cmd,
                                "(ifconfig wlan0 %s; ifconfig wlan2 %s) >/dev/null 2>&1 &", ic, ic);
                            system(cmd);
                            g_w24 = g_w5 = !on;
                            aux_hold();
                            need_render = 1;
                        }
                        else if (!strcmp(a, "wifi24") || !strcmp(a, "wifi5")) {
                            int is24 = !strcmp(a, "wifi24");
                            int on = (is24 ? g_w24 : g_w5) == 1;
                            char cmd[120];
                            snprintf(cmd, sizeof cmd, "ifconfig %s %s >/dev/null 2>&1 &",
                                     is24 ? "wlan0" : "wlan2", on ? "down" : "up");
                            system(cmd);
                            if (is24) g_w24 = !on; else g_w5 = !on;
                            aux_hold();
                            need_render = 1;
                        }
                        else if (!strcmp(a, "sigread") || !strcmp(a, "sigparse")) {   /* 高级设置 sub-page (was a modal) */
                            if (a[3] == 'r') {
                                g_sig_read = !g_sig_read;
                                (void)datad_set_signal_read(g_sig_read);
                            } else {
                                g_sig_parse = !g_sig_parse;
                                (void)datad_set_signal_parse(g_sig_parse);
                                rescan_pages_keep_current();
                            }
                            signal_async_publish(NULL, 0);
                            save_conf();
                            invalidate_render_html_cache();
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strncmp(a, "txp:", 4)) {      /* WiFi 功率: stock levels only */
                            int v = atoi(a + 4);
                            if (v == 40 || v == 80 || v == 100) {
                                char cmd[200];
                                snprintf(cmd, sizeof cmd, "ubus call zwrt_wlan set '{\"wifi0\":{\"txpowerpercent\":\"%d\"},\"wifi1\":{\"txpowerpercent\":\"%d\"}}' >/dev/null 2>&1 &", v, v);
                                system(cmd);
                                g_txp_pending = v; g_txp_at = now ? now : 1;
                            }
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strncmp(a, "plan:", 5)) {                 /* 流量套餐 page */
                            const char *v = a + 5;
                            if (!strcmp(v, "cap")) g_plan_on = 1;
                            else if (!strcmp(v, "unl")) g_plan_on = 0;
                            else if (!strncmp(v, "set:", 4)) { int gb = atoi(v + 4); if (gb >= 10) { g_plan_gb = gb; g_plan_on = 1; } }
                            else if (!strcmp(v, "inc")) g_plan_gb = g_plan_gb + 10 > 99990 ? 99990 : g_plan_gb + 10;
                            else if (!strcmp(v, "dec")) g_plan_gb = g_plan_gb - 10 < 10 ? 10 : g_plan_gb - 10;
                            save_conf();
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strncmp(a, "chgcap:", 7) || !strncmp(a, "chgcur:", 7)) {   /* 电池与充电 page */
                            int v = atoi(a + 7);
                            if (a[3] == 'c' && a[4] == 'a') g_chg_cap = v == 70 || v == 80 || v == 90 || v == 95 ? v : 0;
                            else                            g_chg_cur = v == 2000 || v == 1500 || v == 1000 || v == 500 ? v : 0;
                            save_conf();
                            system(IDLE_GUARD_CHARGE);                       /* apply now, not at the next guard loop */
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strcmp(a, "dps")) {   /* power direct-supply mode */
                            int on = (g_dps == 1);
                            unlink(CHGCAP_MARK);         /* the user takes direct supply over from the 充电上限 logic */
                            close(open(CHGCAP_USER, O_WRONLY | O_CREAT, 0644));
                            char cmd[160];
                            snprintf(cmd, sizeof cmd,
                                "ubus call zwrt_bsp.charger set '{\"direct_power_supply_mode\":\"%s\"}' >/dev/null 2>&1 &",
                                on ? "disable" : "enable");
                            system(cmd);
                            g_dps = !on;
                            aux_hold();
                            need_render = 1;
                        }
                        else if (!strcmp(a, "psm")) {
                            int turn_on = g_wpsm == 1 ? 0 : 1;   /* power_save on = battery saving */
                            const char *m = turn_on ? "on" : "off";
                            /* The switch owns /etc/hotplug.d/iface/99-disable-powersave: it writes
                             * the script itself (re-applying the chosen mode on every ifup) and
                             * applies it now, so the feature is self-contained; nothing needs to be
                             * pre-installed. (Also drop the legacy "psm" file from older builds, which
                             * sorts later and would otherwise override this one.) */
                            char cmd[700];
                            snprintf(cmd, sizeof cmd,
                                "(mkdir -p /etc/hotplug.d/iface; rm -f /etc/hotplug.d/iface/psm; "
                                "{ echo '#!/bin/sh'; echo '[ \"$ACTION\" = ifup ] && {'; "
                                "echo '  iw dev wlan0 set power_save %s 2>/dev/null'; "
                                "echo '  iw dev wlan1 set power_save %s 2>/dev/null'; "
                                "echo '  iw dev wlan2 set power_save %s 2>/dev/null'; "
                                "echo '  iw dev wlan3 set power_save %s 2>/dev/null'; echo '}'; } "
                                "> /etc/hotplug.d/iface/99-disable-powersave; "
                                "chmod +x /etc/hotplug.d/iface/99-disable-powersave; "
                                "for w in wlan0 wlan1 wlan2 wlan3; do iw dev $w set power_save %s 2>/dev/null; done) "
                                ">/dev/null 2>&1 &",
                                m, m, m, m, m);
                            system(cmd);
                            g_wpsm = turn_on;
                            aux_hold();
                            need_render = 1;
                        }
                        else if (!strcmp(a, "adb")) {
                            static devui_data_t dd;
                            const char *mode = "debug";
                            if (data_refresh_live(&dd) && !strcmp(dd.usb_mode, "debug") &&
                                !usb_pid_is("90b1") && !usb_pid_is("90B1"))
                                mode = "user";
                            g_adb_pending = !strcmp(mode, "debug");
                            char cmd[160];
                            if (g_adb_pending)
                                snprintf(cmd, sizeof cmd,
                                    "/sbin/usb_composition 9059 n n y y >/dev/null 2>&1 &");
                            else
                                snprintf(cmd, sizeof cmd,
                                    "ubus call zwrt_bsp.usb set '{\"mode\":\"user\"}' >/dev/null 2>&1 &");
                            system(cmd);
                            need_render = 1;
                        }
                        else if (!strcmp(a, "usbpower")) {
                            if ((g_typec_pending >= 0 && (int32_t)(now - g_typec_until) < 0) || usb_switch_busy(now)) {
                                need_render = 1;
                                goto action_done;
                            }
                            int cur = g_typec_source == 1;
                            int target = !cur;
                            if (target && g_charging) {
                                snprintf(g_toast, sizeof g_toast, "充电器供电中，无法对外供电");
                                g_toast_until = now + 2600;
                                need_render = 1;
                                goto action_done;
                            }
                            typec_switch_to(target, now);
                            need_render = 1;
                        }
                        else if (!strcmp(a, "usbnet")) {
                            if ((g_usb_net_pending >= 0 && (int32_t)(now - g_usb_net_until) < 0) || usb_switch_busy(now)) {
                                need_render = 1;
                                goto action_done;
                            }
                            int on = !usb_net_now();
                            pr_apply(pr_current_mode(), on, now);
                            g_pr_net_pref = on;          /* 和插线面板记同一个选择，下次插线按这个恢复 */
                            save_conf();
                            need_render = 1;
                        }
                        else if (!strcmp(a, "bright")) {    /* tap position on the bar = level */
                            int bx, by, bw, bh;
                            if (html_view_rect("#bright-bar", &bx, &by, &bw, &bh) && bw > 0) {
                                int frac = (x - bx) * 100 / bw;
                                if (frac < 3) frac = 3; if (frac > 100) frac = 100;
                                int bmax = backlight_max(); if (bmax <= 0) bmax = 255;
                                backlight_set(frac * bmax / 100);
                                save_conf();   /* persist brightness */
                            }
                            need_render = 1;
                        }
                        else if (!strncmp(a, "autooff:", 8)) {   /* preset select */
                            g_autooff_ms = atoi(a + 8); last_act = now; save_conf(); need_render = 1;
                        }
                        else if (!strncmp(a, "refreshms:", 10)) {   /* preset select */
                            g_refresh_ms = normalize_refresh_ms(atoi(a + 10));
                            (void)datad_set_refresh_ms(g_refresh_ms);
                            if (g_refresh_ms > 0) {
                                if (data_backend_commit_latest()) need_render = 1;
                                state_pending = 0;
                            }
                            last_data = 0;
                            save_conf();
                            need_render = 1;
                        }
                        else if (!strncmp(a, "gopage:", 7)) {      /* jump to a main page by file name, e.g. gopage:signal */
                            for (int pi = 0; pi < g_npages; pi++)
                                if (a[7] && strstr(g_pages[pi], a + 7)) {
                                    subpage_close();
                                    g_cur = pi;
                                    g_scroll = 0;
                                    menu = 0;
                                    invalidate_render_html_cache();
                                    break;
                                }
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strcmp(a, "stpage")) {
                            if (subpage_open("speedtest.html")) {
                                menu = 0;
                                g_modal = 0;
                                g_sms_open = -1;
                                g_st_home_open = 0;
                            } else {
                                int pi = speedtest_page_index();
                                if (pi >= 0) {
                                    subpage_close();
                                    g_cur = pi;
                                    g_scroll = 0;
                                    menu = 0;
                                }
                            }
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strcmp(a, "sttoggle")) {
                            if (speedtest_binary_ready())
                                g_st_home_open = !g_st_home_open;
                            else
                                g_st_home_open = 0;
                            subpage_close();
                            g_cur = 0;
                            g_scroll = 0;
                            menu = 0;
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strcmp(a, "stclose")) {
                            g_st_home_open = 0;
                            subpage_close();
                            g_cur = 0;
                            g_scroll = 0;
                            menu = 0;
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strcmp(a, "ststart")) {
                            speedtest_start();
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strcmp(a, "ststop")) {
                            speedtest_stop();
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strncmp(a, "stcyc:", 6)) {   /* 测速 pills: tap = next value */
                            static const char *srcs[] = { "auto", "cnspeed", "cdn", "ookla" }, *dirs[] = { "both", "dl", "ul" };
                            static const int durs[] = { 10, 15, 20, 0 };
                            int k;
                            if (!strcmp(a + 6, "src")) {
                                for (k = 0; k < 4 && strcmp(srcs[k], g_st_src); k++) ;
                                snprintf(g_st_src, sizeof g_st_src, "%s", srcs[(k + 1) % 4]);
                            } else if (!strcmp(a + 6, "dir")) {
                                for (k = 0; k < 3 && strcmp(dirs[k], g_st_dir); k++) ;
                                snprintf(g_st_dir, sizeof g_st_dir, "%s", dirs[(k + 1) % 3]);
                            } else {
                                for (k = 0; k < 4 && durs[k] != g_st_dur; k++) ;
                                g_st_dur = durs[(k + 1) % 4];
                            }
                            save_conf();
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strncmp(a, "stsrc:", 6)) {
                            snprintf(g_st_src, sizeof g_st_src, "%s", speedtest_norm_src(a + 6));
                            save_conf();
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strncmp(a, "stdir:", 6)) {
                            snprintf(g_st_dir, sizeof g_st_dir, "%s", speedtest_norm_dir(a + 6));
                            save_conf();
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strncmp(a, "stdur:", 6)) {
                            g_st_dur = speedtest_norm_dur(atoi(a + 6));
                            save_conf();
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strcmp(a, "locktoggle")) {   /* on->off clears PIN; off->on opens setup pad */
                            if (lock_enabled()) clear_pin();
                            else                enter_lock(1);
                            need_render = 1;
                        }
                        else if (!strncmp(a, "net:", 4)) {   /* segmented control tap fallback */
                            char cmd[160];
                            snprintf(cmd, sizeof cmd,
                                "ubus call zte_nwinfo_api nwinfo_set_netselect '{\"net_select\":\"%s\"}' >/dev/null 2>&1 &", a + 4);
                            system(cmd);
                            snprintf(g_net_pending, sizeof g_net_pending, "%s", a + 4);
                            snprintf(g_toast, sizeof g_toast, "网络模式已切换"); g_toast_until = now + 1600;
                        }
                        else if (!strncmp(a, "openmodal:", 10)) {   /* open band-lock dialog */
                            const char *r = a + 10;
                            if (!strcmp(r, "sig")) g_modal = 4;
                            else g_modal = !strcmp(r, "sa") ? 1 : !strcmp(r, "nsa") ? 2 : 3;
                            need_render = 1;
                        }
                        else if (!strncmp(a, "smsi:", 5) || !strncmp(a, "smsnav:", 7)) {   /* 短信详情页 */
                            static devui_data_t sd;
                            if (!strncmp(a, "smsi:", 5)) g_sms_idx = atoi(a + 5);
                            else g_sms_idx += atoi(a + 7);
                            if (data_refresh(&sd)) {
                                if (g_sms_idx >= sd.sms_n) g_sms_idx = sd.sms_n - 1;
                                if (g_sms_idx < 0) g_sms_idx = 0;
                                if (sd.sms_n > 0 && sd.sms[g_sms_idx].unread && sd.sms[g_sms_idx].id > 0) {   /* mark read */
                                    char cmd[128];
                                    snprintf(cmd, sizeof cmd,
                                        "ubus call zwrt_wms zwrt_wms_modify_tag '{\"id\":\"%ld;\",\"tag\":0}' >/dev/null 2>&1 &",
                                        sd.sms[g_sms_idx].id);
                                    system(cmd);
                                }
                            }
                            if (!strncmp(a, "smsi:", 5)) subpage_open("smsdetail.html");
                            g_scroll = 0;
                            invalidate_render_html_cache();
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strncmp(a, "upg:", 4)) {                   /* 升级高级版 */
                            const char *v = a + 4;
                            if (!strcmp(v, "buy") || !strcmp(v, "go") || !strcmp(v, "probe") || !strcmp(v, "cancel")) upg_run(v);
                            invalidate_render_html_cache();
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strncmp(a, "bs:", 3)) {                    /* 扫描所有频段 */
                            const char *v = a + 3;
                            if (!strcmp(v, "ask")) g_bs_confirm = 1;
                            else if (!strcmp(v, "cancel")) g_bs_confirm = 0;
                            else if (!strcmp(v, "start")) {
                                g_bs_confirm = 0; g_bs_locked[0] = 0;
                                system("(nohup sh " BS_SH " >/dev/null 2>&1 </dev/null &)");
                                subpage_open("bandscan.html");
                            } else if (!strcmp(v, "stop")) {
                                close(open("/tmp/u60-bandscan.stop", O_WRONLY | O_CREAT, 0644));
                            } else if (!strncmp(v, "lock:", 5)) {
                                int bn = atoi(v + 5);
                                if (bn > 0) {
                                    char cmd[200];
                                    snprintf(cmd, sizeof cmd,
                                        "ubus call zte_nwinfo_api nwinfo_set_nrbandlock '{\"nr5g_type\":\"0\",\"nr5g_band\":\"%d\"}' >/dev/null 2>&1 &", bn);
                                    system(cmd);
                                    snprintf(g_bs_locked, sizeof g_bs_locked, "n%d", bn);
                                    snprintf(g_toast, sizeof g_toast, "已锁定 n%d · 出门前到锁频页恢复默认", bn);
                                    g_toast_pill = 1; g_toast_until = now + 2600;
                                }
                            }
                            invalidate_render_html_cache();
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strcmp(a, "bsback")) {            /* results -> 附近基站 */
                            g_bs_confirm = 0;
                            subpage_open("nbr.html");
                            invalidate_render_html_cache();
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strcmp(a, "smsback")) {           /* detail -> list, not all the way out */
                            subpage_open("sms.html");
                            invalidate_render_html_cache();
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strncmp(a, "sms:", 4)) {   /* open SMS detail + mark read */
                            const char *id_txt = a + 4;
                            char *endp = NULL;
                            long sid = strtol(id_txt, &endp, 10);
                            static devui_data_t sd;
                            g_sms_open = -1;
                            g_sms_scroll = g_sms_scroll_max = 0;
                            g_sms_view_x = g_sms_view_y = g_sms_view_w = g_sms_view_h = 0;
                            g_sms_num[0] = g_sms_date[0] = g_sms_text[0] = 0;
                            need_render = 1;
                            if (id_txt != endp && endp && *endp == '\0' && data_refresh(&sd)) {
                                if (sid > 0) {
                                    for (int i = 0; i < sd.sms_n; i++) {
                                        if (sd.sms[i].id != sid) continue;
                                        snprintf(g_sms_num,  sizeof g_sms_num,  "%s", sd.sms[i].num);
                                        snprintf(g_sms_date, sizeof g_sms_date, "%s", sd.sms[i].date);
                                        snprintf(g_sms_text, sizeof g_sms_text, "%s", sd.sms[i].text);
                                        g_sms_open = sid;
                                        if (sd.sms[i].unread && sd.sms[i].id > 0) {
                                            char cmd[128];
                                            snprintf(cmd, sizeof cmd,
                                                "ubus call zwrt_wms zwrt_wms_modify_tag '{\"id\":\"%ld;\",\"tag\":0}' >/dev/null 2>&1 &",
                                                sd.sms[i].id);
                                            system(cmd);
                                        }
                                        need_render = 1;
                                        break;
                                    }
                                }
                            }
                        }
                        else if (!strncmp(a, "nbr:", 4) && nbr_handle_action(a, now, g_toast, sizeof g_toast)) {
                            if (g_toast[0]) g_toast_until = now + 2200;
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strncmp(a, "bl:", 3) && bl_action(a, now)) {
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strncmp(a, "rescue:", 7)) {
                            /* no toast: the tile itself shows 再点一次执行 / 已断开 N 台 */
                            if (!rescue_armed()) g_rescue_armed_at = now ? now : 1;   /* first tap only arms it */
                            else { g_rescue_armed_at = 0; system(KICK_CMD); }
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strncmp(a, "cl:", 3)) {
                            const char *c = a + 3;
                            if (!strcmp(c, "unlock")) {
                                system("(ubus call zte_nwinfo_api nwinfo_lock_nr_cell '{\"lock_nr_pci\":\"0\",\"lock_nr_earfcn\":\"0\",\"lock_nr_cell_band\":\"0\"}'; "
                                       "ubus call zte_nwinfo_api nwinfo_lock_lte_cell '{\"lock_lte_pci\":\"0\",\"lock_lte_earfcn\":\"0\"}') >/dev/null 2>&1 &");
                                snprintf(g_toast, sizeof g_toast, "已解除锁定，正在重新搜网");
                                g_toast_until = now + 2000; g_cl_armed[0] = 0;
                            } else if (!strncmp(c, "lock:", 5)) {
                                if (g_cl_armed[0] && (int32_t)(now - g_cl_until) > 0) g_cl_armed[0] = 0;   /* first tap expired */
                                int pci = 0; long arf = 0; char band[8] = "";
                                if (sscanf(c + 5, "%d:%ld:%7[0-9]", &pci, &arf, band) >= 2 && pci > 0 && arf > 0) {
                                    if (strcmp(g_cl_armed, c)) {          /* first tap arms, second locks */
                                        snprintf(g_cl_armed, sizeof g_cl_armed, "%s", c);
                                        g_cl_until = now + 4000;
                                    } else {
                                        char cmd[300];
                                        snprintf(cmd, sizeof cmd, "ubus call zte_nwinfo_api nwinfo_lock_nr_cell "
                                                 "'{\"lock_nr_pci\":\"%d\",\"lock_nr_earfcn\":\"%ld\",\"lock_nr_cell_band\":\"%s\"}' >/dev/null 2>&1 &",
                                                 pci, arf, band);
                                        system(cmd);
                                        g_cl_armed[0] = 0;
                                        snprintf(g_toast, sizeof g_toast, "已锁定 PCI %d", pci);
                                        g_toast_until = now + 2000;
                                    }
                                }
                            }
                            g_cl_at = millis() - 3500;                 /* re-read in ~1.5 s, after ubus applied it */
                            last_act = now;
                            need_render = 1;
                        }
                        else if (!strcmp(a, "resetband")) {
                            system("ubus call zte_nwinfo_api nwinfo_reset_band_cell_setting '{}' >/dev/null 2>&1 &");
                            snprintf(g_toast, sizeof g_toast, "锁频已恢复默认"); g_toast_until = now + 1600;
                            need_render = 1;   /* selection re-syncs from the live lock automatically */
                        }
                    }
                }
action_done:
                if (!replay_release)
                    touch_input_drop_replayed_release(&touch, release_was_tap);
                /* a tap that switched page/sheet must not also land on the new one */
                if (tap_page_before[0] && (strcmp(tap_page_before, active_page_path()) || tap_menu_before != menu))
                    touch_input_clear_taps(&touch);
                tap_page_before[0] = 0;
                last_motion_frame = 0;
                dragging = 0; drag_dir = 0; scroll_dir = 0; sliding = 0; segging = 0; g_segdrag = 0;
                scroll_track_valid = 0;
            }
        }
        prev_press = pressed;

        /* when the lock pad first appears, drop taps that were queued before it
         * (e.g. the toggle tap that opened it) so they don't phantom-press keys */
        if (g_lock_state != prev_lock) touch_input_clear_taps(&touch);
        prev_lock = g_lock_state;

        g_sig_view = backlight_is_on() && !g_lock_state && path_is_signal_page(CUR_PATH);
        {   /* 升级页：进入时查一次状态；进行中每秒刷新倒计时和下载进度 */
            static uint32_t up_at;
            static int up_on;
            int on = backlight_is_on() && !g_lock_state && strstr(CUR_PATH, "upgrade.html") != NULL;
            if (on && !up_on) {
                struct upg u;
                upg_read(&u);
                if (!upg_busy(u.st)) upg_run("probe");          /* 每次进来都向服务器确认一次（授权可能被解绑或吊销） */
            }
            up_on = on;
            if (on && now - up_at >= 1000) {
                up_at = now;
                static char last_sig[64];
                char sig[64];
                struct upg u;
                upg_read(&u);
                snprintf(sig, sizeof sig, "%s|%ld|%ld|%ld", u.st, u.at, upg_busy(u.st) ? (long)time(NULL) : 0L, upg_got());
                if (strcmp(sig, last_sig)) { snprintf(last_sig, sizeof last_sig, "%s", sig); need_render = 1; invalidate_render_html_cache(); }
            }
        }
        {   /* 扫描所有频段: redraw progress every second while visible */
            static uint32_t bs_at;
            if (backlight_is_on() && (strstr(CUR_PATH, "bandscan") || strstr(CUR_PATH, "nbr.html")) && now - bs_at >= 1000) {
                bs_at = now;
                char sc[8]; int ix, tt; long a0;
                static int last_st = -1; static char last_scan[8];
                int stt = bs_state(sc, sizeof sc, &ix, &tt, &a0);
                if (stt == 1 || stt != last_st || strcmp(sc, last_scan)) { need_render = 1; invalidate_render_html_cache(); }
                last_st = stt; snprintf(last_scan, sizeof last_scan, "%s", sc);
            }
        }

        /* nearby-cells collector runs only while its page is on screen */
        nbr_tick(backlight_is_on() && !menu && !g_lock_state && strstr(CUR_PATH, "nbr.html") != NULL,
                 backlight_is_on(), now);

        /* dismiss the toast after its timeout */
        if (g_toast[0] && (int32_t)(now - g_toast_until) >= 0) { g_toast[0] = 0; g_toast_pill = 0; need_render = 1; }

        /* power-menu armed state auto-reverts if the second tap doesn't come */
        if (g_pwr_confirm && (int32_t)(now - g_pwr_until) >= 0) { g_pwr_confirm = 0; if (menu) need_render = 1; }

        /* auto screen-off after the configured idle timeout (locks if enabled) */
        if (g_autooff_ms > 0 && backlight_is_on() && now - last_act >= (uint32_t)g_autooff_ms) {
            screen_off(&disp);
            if (cover_wanted()) {
                if (ext_ok) devui_ext_deactivate(&ext);
                enter_cover();
            }
        }

        /* periodic clock/state check (not mid-drag). refresh=0 pauses promotion of
         * live backend updates, but the minute clock still ticks once per second. */
        {
            uint32_t poll_ms = g_refresh_ms > 0 ? (uint32_t)g_refresh_ms : 1000;
            if (!dragging && !scroll_inertia && now - last_data >= poll_ms) {
                time_t now_t = time(NULL);
                int state_changed = 0;
                int clock_changed = 0;
                int state_render = 0;
                int cur_min = (int)(now_t / 60);
                if (cur_min != g_last_clock_min) {
                    g_last_clock_min = cur_min;
                    clock_changed = 1;
                    need_render = 1;   /* update HH:MM and any minute-level derived tokens */
                }

                if (g_refresh_ms > 0 && state_pending && data_backend_commit_latest()) {
                    state_changed = 1;
                    state_render = 1;
                    state_pending = 0;
                }
                if (g_refresh_ms > 0 && signal_live_enabled() && path_is_signal_page(CUR_PATH))
                    state_render = 1;
                if (state_render) {
                    if (speedtest_anim_owns(CUR_PATH)) g_st_sb_dirty = 1;
                    else need_render = 1;
                }
                if (ext_ok && devui_ext_active(&ext) && !g_lock_state &&
                    (clock_changed || (g_refresh_ms > 0 && state_changed)))
                    refresh_status_cache();
                last_data = now;
            }
        }

        /* reconcile page-2 WiFi switch states from uci/iw on a slow throttle */
        /* ~30 forks per call: only worth it while someone can see the switches */
        if (backlight_is_on() && !dragging && !scroll_inertia && now - g_wifi_aux_at >= 4000) { g_wifi_aux_at = now; wifi_aux_refresh(0); }

        if (!g_charge_boot && now - g_pages_scan_at >= 1000) {
            g_pages_scan_at = now;
            if (rescan_pages_if_changed()) need_render = 1;
        }

        /* speedtest state: fast while a test runs on screen, slow on the pages that show
         * a result (测速 / 控制中心 tile), not at all when dark (the next wake catches up) */
        int st_view = path_is_speedtest(CUR_PATH) || g_st_home_open || strstr(CUR_PATH, "control") != NULL;
        /* 不在测速相关页：每次轮询要扫一遍 /proc，没人看结果，放到 30 秒（切回来时马上补一次） */
        int st_poll_ms = (g_st_state == ST_STATE_RUNNING && st_view) ? 300 : st_view ? 900 : 30000;
        if (backlight_is_on() && !dragging && !scroll_inertia && now - g_st_poll_at >= (uint32_t)st_poll_ms) {
            int st_changed = speedtest_poll(now);
            if (!g_lock_state && (path_is_speedtest(CUR_PATH) || g_st_home_open) && st_changed)
                need_render = 1;
        }
        if (!need_render && !dragging && !scroll_inertia && backlight_is_on() && !g_lock_state && !g_modal &&
            g_sms_open < 0 && !(ext_ok && devui_ext_active(&ext)) && path_is_speedtest(CUR_PATH))
            speedtest_anim_tick(&disp, now, CUR_PATH);

        if (need_render && backlight_is_on()) {
            if (ext_ok && devui_ext_active(&ext) && !g_lock_state)
                render_ext_view(&disp, &ext);
            else
                render(&disp, CUR_PATH);
        }
        was_on = backlight_is_on();   /* track for next frame's wake-touch discard */
        if (!animating) {
            /* Idle: sleep until touch / power key input or the next periodic deadline,
             * instead of a fixed 8 ms tick (125 wake-ups a second kept the CPU out of
             * deep idle). 30 ms covers the 40 ms animation ticks while lit; dark, only
             * the key and the plug / attach checks matter. 熄屏 500ms：按键会立刻唤醒 poll，
             * 插拔充电器要连续两次读到才算，约 1 秒内亮屏。 */
            struct pollfd pf[2] = { { touch.fd, POLLIN, 0 }, { key.fd, POLLIN, 0 } };
            /* 电源键按住时要按时判断长按，不能睡太久 */
            poll(pf, 2, backlight_is_on() || key.pressed ? 30 : 500);
        }
    }

    if (ext_ok) devui_ext_close(&ext);
    signal_async_stop();
    data_backend_close();
    drm_disp_close(&disp);
    return 0;
}
