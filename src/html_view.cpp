/*
 * html_view.cpp - render an HTML/CSS page to the RGB565 framebuffer using
 * litehtml (layout/CSS) + FreeType (text). devui becomes a thin HTML shell:
 * the UI is authored in ui/index.html, this draws it.
 *
 * No JavaScript; CSS grid is unsupported by litehtml (falls back to block).
 *
 * SPDX-License-Identifier: MIT
 */
#include <litehtml.h>

#include <ft2build.h>
#include FT_FREETYPE_H
#include FT_OUTLINE_H

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <string>
#include <vector>
#include <algorithm>
#include <sys/stat.h>
#include <cstdlib>
#include <cmath>
#include <ctime>
#include "stb_image.h"

using namespace litehtml;

/* ---- target framebuffer (shared with drm_disp, 180° rotated panel) ---- */
static uint16_t *g_fb;
static int g_w, g_h, g_pitch_px, g_rotate = 1;
static int g_clip_top = 0;
static int g_scr_w = 320, g_scr_h = 480;   /* the real screen (g_w/g_h change for off-screen targets) */
static int g_cl = -100000, g_cr = 100000, g_ct = -100000, g_cb = 100000;   /* native clip rect */

static inline void put_px(int x, int y, int r, int g, int b, int a)
{
    if (y < g_clip_top) return;
    if (x < g_cl || x >= g_cr || y < g_ct || y >= g_cb) return;
    if (x < 0 || y < 0 || x >= g_w || y >= g_h || a <= 0) return;
    int dx = g_rotate ? (g_w - 1 - x) : x;
    int dy = g_rotate ? (g_h - 1 - y) : y;
    uint16_t *p = &g_fb[dy * g_pitch_px + dx];
    if (a < 255) {
        uint16_t o = *p;
        int orr = ((o >> 11) & 0x1F) << 3, og = ((o >> 5) & 0x3F) << 2, ob = (o & 0x1F) << 3;
        r = (r * a + orr * (255 - a)) / 255;
        g = (g * a + og * (255 - a)) / 255;
        b = (b * a + ob * (255 - a)) / 255;
    }
    *p = (uint16_t)(((r & 0xF8) << 8) | ((g & 0xFC) << 3) | (b >> 3));
}

static inline uint16_t get_px565(int x, int y)
{
    if (x < 0 || y < 0 || x >= g_w || y >= g_h || !g_fb) return 0;
    int dx = g_rotate ? (g_w - 1 - x) : x;
    int dy = g_rotate ? (g_h - 1 - y) : y;
    return g_fb[dy * g_pitch_px + dx];
}

/* Is (x,y) inside a rounded rectangle? Used by both rounded fill and rounded
 * border stroking (litehtml hands us radii but leaves the drawing to us). */
static bool pt_in_round(int x, int y, int fx, int fy, int fw, int fh,
                        int rtl, int rtr, int rbr, int rbl)
{
    if (x < fx || y < fy || x >= fx + fw || y >= fy + fh) return false;
    int r = 0, cx = 0, cy = 0;
    if      (x < fx + rtl       && y < fy + rtl)       { r = rtl; cx = fx + rtl;          cy = fy + rtl; }
    else if (x >= fx + fw - rtr && y < fy + rtr)       { r = rtr; cx = fx + fw - 1 - rtr; cy = fy + rtr; }
    else if (x >= fx + fw - rbr && y >= fy + fh - rbr) { r = rbr; cx = fx + fw - 1 - rbr; cy = fy + fh - 1 - rbr; }
    else if (x < fx + rbl       && y >= fy + fh - rbl) { r = rbl; cx = fx + rbl;          cy = fy + fh - 1 - rbl; }
    if (r > 0) { int dx = x - cx, dy = y - cy; if (dx * dx + dy * dy > r * r) return false; }
    return true;
}

/* 4x4 supersampled coverage (0..16) of pixel (x,y) against a rounded rect whose
 * corner arcs are centred on continuous coordinates, so edges get fractional
 * alpha instead of a hard in/out staircase. */
static int rr_cov(int x, int y, float fx, float fy, float fw, float fh,
                  float rtl, float rtr, float rbr, float rbl)
{
    int n = 0;
    for (int sy = 0; sy < 4; sy++) {
        float py = y + (sy + 0.5f) * 0.25f;
        for (int sx = 0; sx < 4; sx++) {
            float px = x + (sx + 0.5f) * 0.25f;
            if (px < fx || py < fy || px > fx + fw || py > fy + fh) continue;
            float r = 0, cx = 0, cy = 0;
            if      (px < fx + rtl      && py < fy + rtl)      { r = rtl; cx = fx + rtl;      cy = fy + rtl; }
            else if (px > fx + fw - rtr && py < fy + rtr)      { r = rtr; cx = fx + fw - rtr; cy = fy + rtr; }
            else if (px > fx + fw - rbr && py > fy + fh - rbr) { r = rbr; cx = fx + fw - rbr; cy = fy + fh - rbr; }
            else if (px < fx + rbl      && py > fy + fh - rbl) { r = rbl; cx = fx + rbl;      cy = fy + fh - rbl; }
            if (r > 0) { float dx = px - cx, dy = py - cy; if (dx * dx + dy * dy > r * r) continue; }
            n++;
        }
    }
    return n;
}

static inline bool in_corner_zone(int x, int y, int fx, int fy, int fw, int fh,
                                  int rtl, int rtr, int rbr, int rbl)
{
    return (x < fx + rtl && y < fy + rtl) || (x >= fx + fw - rtr && y < fy + rtr) ||
           (x >= fx + fw - rbr && y >= fy + fh - rbr) || (x < fx + rbl && y >= fy + fh - rbl);
}

/* Coverage of a pixel by a rounded rect: exact 0/16 away from the corners. */
static inline int rr_cov_fast(int x, int y, int fx, int fy, int fw, int fh,
                              int rtl, int rtr, int rbr, int rbl)
{
    if (x < fx || y < fy || x >= fx + fw || y >= fy + fh) return 0;
    if (!in_corner_zone(x, y, fx, fy, fw, fh, rtl, rtr, rbr, rbl)) return 16;
    return rr_cov(x, y, (float)fx, (float)fy, (float)fw, (float)fh,
                  (float)rtl, (float)rtr, (float)rbr, (float)rbl);
}

/* ---- FreeType ---- */
static FT_Library g_ft;
static FT_Face    g_face;
static FT_Face    g_face2;   /* optional numeral face (Oswald), picked by font-family "num" */

struct ft_font { int size; int ascent, descent, height; FT_Face face; int bold; };

/* Glyph face for a codepoint: the numeral face falls back to the CJK face for
 * characters it lacks (arrows, CJK, symbols). */
static inline FT_Face glyph_face(const ft_font *f, unsigned cp)
{
    if (f->face != g_face && FT_Get_Char_Index(f->face, cp) == 0) return g_face;
    return f->face;
}

static void set_sizes(const ft_font *f)
{
    FT_Set_Pixel_Sizes(f->face, 0, f->size);
    if (f->face != g_face) FT_Set_Pixel_Sizes(g_face, 0, f->size);
}

/* Load (and render) one glyph, emboldening the outline for bold weights. */
static int load_glyph(const ft_font *f, unsigned cp, int render, FT_Face *out)
{
    FT_Face fc = glyph_face(f, cp);
    *out = fc;
    /* NO_BITMAP: embedded bitmap strikes come back 1-bit, but the blitters read 8-bit gray */
    if (!f->bold) return FT_Load_Char(fc, cp, (render ? FT_LOAD_RENDER : FT_LOAD_DEFAULT) | FT_LOAD_NO_BITMAP);
    if (FT_Load_Char(fc, cp, FT_LOAD_NO_BITMAP)) return 1;
    if (fc->glyph->format == FT_GLYPH_FORMAT_OUTLINE) {
        FT_Pos str = (FT_Pos)(f->size * 64 / 22);
        FT_Outline_Embolden(&fc->glyph->outline, str);
        fc->glyph->advance.x += str;
    }
    if (render && FT_Render_Glyph(fc->glyph, FT_RENDER_MODE_NORMAL)) return 1;
    return 0;
}

/* ---- 字形缓存：同一个 (字体, 字号, 粗体, 字符) 只栅格化一次 ----
 * 每帧每个字都 FT_Load_Char(RENDER) 是整页重绘的主要 CPU 开销。直接映射 + 总量上限，
 * 满了整体清空；单个过大的字形（大号数字）不缓存。 */
struct gc_ent {
    FT_Face face; int size, emb; unsigned cp;
    int adv, left, top, w, rows, pitch;
    unsigned char *buf; bool used;
};
#define GC_SLOTS 2048
#define GC_MAX_BYTES (1536 * 1024)
static gc_ent g_gc[GC_SLOTS];
static gc_ent g_gc_tmp;
static size_t g_gc_bytes;

static void gc_flush()
{
    for (int i = 0; i < GC_SLOTS; i++) { free(g_gc[i].buf); g_gc[i] = gc_ent(); }
    g_gc_bytes = 0;
}

/* f 非空：走容器字体（可能加粗），缓存未命中时自己设字号；f 为空：调用方已设好字号。 */
static const gc_ent *gc_get(FT_Face face, int size, int emb, unsigned cp, const ft_font *f)
{
    unsigned h = (unsigned)(((uintptr_t)face >> 4) * 2654435761u) ^ (cp * 40503u) ^ ((unsigned)size * 2246822519u) ^ (unsigned)emb;
    gc_ent *e = &g_gc[(h ^ (h >> 11)) & (GC_SLOTS - 1)];
    if (e->used && e->face == face && e->size == size && e->emb == emb && e->cp == cp) return e;

    FT_Face fc = face;
    int rc;
    if (f) { set_sizes(f); rc = load_glyph(f, cp, 1, &fc); }
    else rc = FT_Load_Char(fc, cp, FT_LOAD_RENDER | FT_LOAD_NO_BITMAP);
    if (rc) return nullptr;
    FT_GlyphSlot gl = fc->glyph;
    FT_Bitmap &bm = gl->bitmap;
    size_t n = (size_t)bm.width * bm.rows;
    int pitch = bm.pitch < 0 ? -bm.pitch : bm.pitch;
    if (n > 16384) {                 /* 太大不缓存：直接指向 FreeType 的缓冲，下一次 load 前用完 */
        g_gc_tmp.adv = gl->advance.x >> 6; g_gc_tmp.left = gl->bitmap_left; g_gc_tmp.top = gl->bitmap_top;
        g_gc_tmp.w = (int)bm.width; g_gc_tmp.rows = (int)bm.rows; g_gc_tmp.pitch = bm.pitch; g_gc_tmp.buf = bm.buffer;
        return &g_gc_tmp;
    }
    if (g_gc_bytes + n > GC_MAX_BYTES) gc_flush();
    free(e->buf); g_gc_bytes -= e->used ? (size_t)e->w * e->rows : 0;
    e->buf = nullptr;
    if (n) {
        e->buf = (unsigned char *)malloc(n);
        if (!e->buf) { e->used = false; return nullptr; }
        for (int r = 0; r < (int)bm.rows; r++) memcpy(e->buf + (size_t)r * bm.width, bm.buffer + (size_t)r * pitch, bm.width);
    }
    e->face = face; e->size = size; e->emb = emb; e->cp = cp;
    e->adv = gl->advance.x >> 6; e->left = gl->bitmap_left; e->top = gl->bitmap_top;
    e->w = (int)bm.width; e->rows = (int)bm.rows; e->pitch = (int)bm.width;
    e->used = true; g_gc_bytes += n;
    return e;
}

/* UI base dir (for <link> CSS / images) and last-clicked anchor href. */
static std::string g_ui_dir = "/data/plugins/u60pro-devui/ui";
static std::string g_clicked;

static long long css_file_mtime_ns(const std::string &path)
{
    struct stat st;
    if (stat(path.c_str(), &st) != 0) return -1;
    return (long long)st.st_mtime * 1000000000LL + (long long)st.st_mtim.tv_nsec;
}

struct css_cache_entry {
    std::string path;
    std::string text;
    long long mtime = -1;
    bool used = false;
};

static css_cache_entry g_css_cache[4];
static int g_css_cache_next;

static int read_file_text(const char *path, std::string &out)
{
    FILE *f = fopen(path, "rb");
    if (!f) return 0;
    long n;
    int ok = 0;
    if (fseek(f, 0, SEEK_END) == 0) {
        n = ftell(f);
        if (n >= 0) {
            if (n > 0) {
                out.resize((size_t)n);
                fseek(f, 0, SEEK_SET);
                ok = (fread(&out[0], 1, (size_t)n, f) == (size_t)n);
            } else {
                out.clear();
                ok = 1;
            }
        }
    }
    fclose(f);
    if (!ok) out.clear();
    return ok;
}

static void css_get_cached(std::string &out, const std::string &path)
{
    long long mtime = css_file_mtime_ns(path);
    if (mtime < 0) return;

    for (int i = 0; i < 4; i++) {
        css_cache_entry &e = g_css_cache[i];
        if (!e.used || e.path != path) continue;
        if (e.mtime == mtime && !e.text.empty()) {
            out = e.text;
            return;
        }
        if (read_file_text(path.c_str(), e.text)) {
            e.mtime = mtime;
            out = e.text;
            return;
        }
        out = e.text;
        return;
    }

    css_cache_entry *e = nullptr;
    for (int i = 0; i < 4; i++) {
        if (!g_css_cache[i].used) { e = &g_css_cache[i]; break; }
    }
    if (!e) {
        e = &g_css_cache[g_css_cache_next];
        g_css_cache_next = (g_css_cache_next + 1) % 4;
    }
    std::string next;
    if (!read_file_text(path.c_str(), next)) return;
    e->path = path;
    e->text = std::move(next);
    e->mtime = mtime;
    e->used = true;
    out = e->text;
}

static unsigned utf8_next(const char *&s)
{
    unsigned c = (unsigned char)*s++;
    if (c < 0x80) return c;
    int n = (c >= 0xF0) ? 3 : (c >= 0xE0) ? 2 : 1;
    c &= (0x3F >> n);
    while (n-- && (*s & 0xC0) == 0x80) c = (c << 6) | (*s++ & 0x3F);
    return c;
}

/* ---- container ---- */
class fb_container : public document_container {
    std::vector<position> m_clip;

    position eff_clip() const {
        position r(0, 0, (pixel_t)g_w, (pixel_t)g_h);
        for (auto &c : m_clip) {
            pixel_t x1 = std::max(r.left(), c.left()), y1 = std::max(r.top(), c.top());
            pixel_t x2 = std::min(r.right(), c.right()), y2 = std::min(r.bottom(), c.bottom());
            r = position(x1, y1, std::max<pixel_t>(0, x2 - x1), std::max<pixel_t>(0, y2 - y1));
        }
        return r;
    }
public:
    void fill(pixel_t fx, pixel_t fy, pixel_t fw, pixel_t fh, web_color c) {
        if (c.alpha == 0) return;
        position cl = eff_clip();
        int x1 = std::max((int)fx, (int)cl.left()),  y1 = std::max((int)fy, (int)cl.top());
        int x2 = std::min((int)(fx + fw), (int)cl.right()), y2 = std::min((int)(fy + fh), (int)cl.bottom());
        for (int y = y1; y < y2; y++)
            for (int x = x1; x < x2; x++)
                put_px(x, y, c.red, c.green, c.blue, c.alpha);
    }
    /* Filled rectangle with rounded corners. litehtml only hands us the radii;
     * it's up to the container to honor them, so a pixel inside one of the four
     * corner squares but outside its quarter-circle arc is skipped. */
    void fill_rounded(int fx, int fy, int fw, int fh, int rtl, int rtr, int rbr, int rbl, web_color c) {
        if (c.alpha == 0 || fw <= 0 || fh <= 0) return;
        int hw = fw / 2, hh = fh / 2;
        if (rtl > hw) rtl = hw; if (rtl > hh) rtl = hh;
        if (rtr > hw) rtr = hw; if (rtr > hh) rtr = hh;
        if (rbr > hw) rbr = hw; if (rbr > hh) rbr = hh;
        if (rbl > hw) rbl = hw; if (rbl > hh) rbl = hh;
        position cl = eff_clip();
        int x1 = std::max(fx, (int)cl.left()),  y1 = std::max(fy, (int)cl.top());
        int x2 = std::min(fx + fw, (int)cl.right()), y2 = std::min(fy + fh, (int)cl.bottom());
        for (int y = y1; y < y2; y++) {
            for (int x = x1; x < x2; x++) {
                int cov = rr_cov_fast(x, y, fx, fy, fw, fh, rtl, rtr, rbr, rbl);
                if (cov) put_px(x, y, c.red, c.green, c.blue, c.alpha * cov / 16);
            }
        }
    }
    /* Stroke a rounded-rect outline of uniform thickness t: a pixel inside the
     * outer rounded rect but outside the inner one (inset by t). */
    void stroke_rounded(int fx, int fy, int fw, int fh, int rtl, int rtr, int rbr, int rbl, int t, web_color c) {
        if (c.alpha == 0 || t <= 0 || fw <= 0 || fh <= 0) return;
        int hw = fw / 2, hh = fh / 2;
        if (rtl > hw) rtl = hw; if (rtl > hh) rtl = hh;
        if (rtr > hw) rtr = hw; if (rtr > hh) rtr = hh;
        if (rbr > hw) rbr = hw; if (rbr > hh) rbr = hh;
        if (rbl > hw) rbl = hw; if (rbl > hh) rbl = hh;
        int itl = rtl - t > 0 ? rtl - t : 0, itr = rtr - t > 0 ? rtr - t : 0;
        int ibr = rbr - t > 0 ? rbr - t : 0, ibl = rbl - t > 0 ? rbl - t : 0;
        position cl = eff_clip();
        int x1 = std::max(fx, (int)cl.left()),  y1 = std::max(fy, (int)cl.top());
        int x2 = std::min(fx + fw, (int)cl.right()), y2 = std::min(fy + fh, (int)cl.bottom());
        for (int y = y1; y < y2; y++)
            for (int x = x1; x < x2; x++) {
                int cov = rr_cov_fast(x, y, fx, fy, fw, fh, rtl, rtr, rbr, rbl)
                        - rr_cov_fast(x, y, fx + t, fy + t, fw - 2 * t, fh - 2 * t, itl, itr, ibr, ibl);
                if (cov > 0) put_px(x, y, c.red, c.green, c.blue, c.alpha * cov / 16);
            }
    }

    void fill_background_box(const background_layer &layer, web_color c) {
        const position &b = layer.border_box;
        const border_radiuses &br = layer.border_radius;
        if (br.top_left_x > 0 || br.top_right_x > 0 || br.bottom_right_x > 0 || br.bottom_left_x > 0)
            fill_rounded(b.x, b.y, b.width, b.height,
                         (int)br.top_left_x, (int)br.top_right_x,
                         (int)br.bottom_right_x, (int)br.bottom_left_x, c);
        else
            fill(b.x, b.y, b.width, b.height, c);
    }

public:
    uint_ptr create_font(const font_description &d, const document *, font_metrics *fm) override {
        auto *f = new ft_font();
        f->size = (int)d.size;
        f->face = (g_face2 && d.family.find("num") != std::string::npos) ? g_face2 : g_face;
        f->bold = d.weight >= 600;
        if (!f->face) {                       /* main font missing: metrics only, draw nothing */
            f->ascent = f->size * 4 / 5; f->descent = f->size - f->ascent; f->height = f->size;
            if (fm) { fm->font_size = d.size; fm->ascent = f->ascent; fm->descent = f->descent; fm->height = f->size; fm->x_height = f->size / 2; }
            return (uint_ptr)f;
        }
        FT_Set_Pixel_Sizes(f->face, 0, f->size);
        f->ascent  = f->face->size->metrics.ascender >> 6;
        f->descent = -(f->face->size->metrics.descender >> 6);
        f->height  = f->face->size->metrics.height >> 6;
        if (fm) {
            fm->font_size = d.size;
            fm->ascent = f->ascent; fm->descent = f->descent;
            fm->height = f->height ? f->height : f->size;
            fm->x_height = f->size / 2; fm->ch_width = f->size / 2;
            fm->draw_spaces = true;
        }
        return (uint_ptr)f;
    }
    void delete_font(uint_ptr h) override { delete (ft_font *)h; }

    pixel_t text_width(const char *text, uint_ptr h) override {
        auto *f = (ft_font *)h;
        if (!f || !f->face) return 0;
        pixel_t w = 0;
        for (const char *s = text; *s; ) {
            unsigned cp = utf8_next(s);
            const gc_ent *g = gc_get(f->face, f->size, f->bold, cp, f);
            if (g) w += g->adv;
        }
        return w;
    }

    void draw_text(uint_ptr, const char *text, uint_ptr h, web_color color, const position &pos) override {
        auto *f = (ft_font *)h;
        if (!f || !f->face) return;
        int pen = (int)pos.x;
        int base = (int)pos.y + f->ascent;
        position cl = eff_clip();
        for (const char *s = text; *s; ) {
            unsigned cp = utf8_next(s);
            const gc_ent *g = gc_get(f->face, f->size, f->bold, cp, f);
            if (!g) continue;
            int ox = pen + g->left, oy = base - g->top;
            for (int r = 0; r < g->rows; r++) {
                int yy = oy + r;
                if (yy < (int)cl.top() || yy >= (int)cl.bottom()) continue;
                for (int cx = 0; cx < g->w; cx++) {
                    int xx = ox + cx;
                    if (xx < (int)cl.left() || xx >= (int)cl.right()) continue;
                    int a = g->buf[r * g->pitch + cx];
                    if (a) put_px(xx, yy, color.red, color.green, color.blue, a * color.alpha / 255);
                }
            }
            pen += g->adv;
        }
    }

    pixel_t pt_to_px(float pt) const override { return (pixel_t)(pt * 96.0f / 72.0f + 0.5f); }
    pixel_t get_default_font_size() const override { return 16; }
    const char *get_default_font_name() const override { return "sans-serif"; }

    void draw_solid_fill(uint_ptr, const background_layer &layer, const web_color &color) override {
        fill_background_box(layer, color);
    }
    /* Approximate gradients with a representative flat dark color. */
    void draw_linear_gradient(uint_ptr, const background_layer &l, const background_layer::linear_gradient &) override {
        fill_background_box(l, web_color(45, 46, 50));
    }
    void draw_radial_gradient(uint_ptr, const background_layer &l, const background_layer::radial_gradient &) override {
        fill_background_box(l, web_color(45, 46, 50));
    }
    void draw_conic_gradient(uint_ptr, const background_layer &l, const background_layer::conic_gradient &) override {
        fill_background_box(l, web_color(45, 46, 50));
    }

    void draw_borders(uint_ptr, const borders &b, const position &p, bool) override {
        /* Rounded outline for the common case: all four sides equal width, same
         * color, with a corner radius (cards, the battery frame, ...). */
        int rtl = (int)b.radius.top_left_x, rtr = (int)b.radius.top_right_x;
        int rbr = (int)b.radius.bottom_right_x, rbl = (int)b.radius.bottom_left_x;
        const web_color &tc = b.top.color;
        bool same_w = b.top.width == b.left.width && b.top.width == b.right.width && b.top.width == b.bottom.width;
        bool same_c = tc.red == b.left.color.red && tc.green == b.left.color.green && tc.blue == b.left.color.blue && tc.alpha == b.left.color.alpha
                   && tc.red == b.right.color.red && tc.green == b.right.color.green && tc.blue == b.right.color.blue && tc.alpha == b.right.color.alpha
                   && tc.red == b.bottom.color.red && tc.green == b.bottom.color.green && tc.blue == b.bottom.color.blue && tc.alpha == b.bottom.color.alpha;
        bool all_solid = b.top.style != border_style_none && b.left.style != border_style_none
                      && b.right.style != border_style_none && b.bottom.style != border_style_none;
        if ((rtl || rtr || rbr || rbl) && same_w && same_c && all_solid && b.top.width > 0) {
            stroke_rounded(p.x, p.y, p.width, p.height, rtl, rtr, rbr, rbl, b.top.width, tc);
            return;
        }
        if (b.top.width > 0    && b.top.style    != border_style_none) fill(p.x, p.y, p.width, b.top.width, b.top.color);
        if (b.bottom.width > 0 && b.bottom.style != border_style_none) fill(p.x, p.bottom() - b.bottom.width, p.width, b.bottom.width, b.bottom.color);
        if (b.left.width > 0   && b.left.style   != border_style_none) fill(p.x, p.y, b.left.width, p.height, b.left.color);
        if (b.right.width > 0  && b.right.style  != border_style_none) fill(p.right() - b.right.width, p.y, b.right.width, p.height, b.right.color);
    }

    void draw_list_marker(uint_ptr, const list_marker &) override {}

    /* images: not supported (the example uses none) */
    void load_image(const char *, const char *, bool) override {}
    void get_image_size(const char *, const char *, size &sz) override { sz.width = sz.height = 0; }
    void draw_image(uint_ptr, const background_layer &, const std::string &, const std::string &) override {}

    void set_clip(const position &pos, const border_radiuses &) override { m_clip.push_back(pos); }
    void del_clip() override { if (!m_clip.empty()) m_clip.pop_back(); }
    void reset_state() { m_clip.clear(); }

    void get_viewport(position &v) const override { v = position(0, 0, (pixel_t)g_w, (pixel_t)g_h); }
    void get_media_features(media_features &m) const override {
        m.type = media_type_screen;
        m.width = m.device_width = (pixel_t)g_w;
        m.height = m.device_height = (pixel_t)g_h;
        m.color = 8; m.resolution = 96;
    }
    void get_language(string &, string &) const override {}

    /* trivial stubs */
    void set_caption(const char *) override {}
    void set_base_url(const char *) override {}
    void link(const std::shared_ptr<document> &, const element::ptr &) override {}
    void on_anchor_click(const char *url, const element::ptr &) override { g_clicked = url ? url : ""; }
    void on_mouse_event(const element::ptr &, mouse_event) override {}
    void set_cursor(const char *) override {}
    void transform_text(string &, text_transform) override {}
    void import_css(string &text, const string &url, string &) override {
        std::string path = g_ui_dir + "/" + url;
        css_get_cached(text, path);
    }
    element::ptr create_element(const char *, const string_map &, const std::shared_ptr<document> &) override { return nullptr; }
};

/* ---- C interface for the (C) main harness ---- */
static fb_container   *g_container;
static document::ptr   g_doc;
static int             g_scroll_y;   /* vertical scroll offset (logical px) */
static int             g_doc_overlay; /* overlay docs are already in screen coords */

extern "C" void html_view_init(uint16_t *fb, int w, int h, int pitch_px, int rotate, const char *font_path)
{
    g_fb = fb; g_w = w; g_h = h; g_pitch_px = pitch_px; g_rotate = rotate;
    g_scr_w = w; g_scr_h = h;
    FT_Init_FreeType(&g_ft);
    if (FT_New_Face(g_ft, font_path, 0, &g_face))
        fprintf(stderr, "html_view: cannot load font %s\n", font_path);
    g_container = new fb_container();
}

/* Numeral face for elements whose font-family mentions "num". */
extern "C" void html_view_set_num_font(const char *path)
{
    gc_flush();   /* 缓存按 face 指针做键，换字体前先清空 */
    if (g_face2) { FT_Done_Face(g_face2); g_face2 = nullptr; }
    if (path && FT_New_Face(g_ft, path, 0, &g_face2)) {
        fprintf(stderr, "html_view: cannot load numeral font %s\n", path);
        g_face2 = nullptr;
    }
}

/* Wallpaper: a PNG/JPEG scaled to cover the logical screen, painted instead of
 * black before every page render. Reloaded when the file's mtime changes. */
static uint16_t *g_wall;
static int       g_wall_w, g_wall_h;
static std::string g_wall_path;
static long long g_wall_mtime = -2;
static long long g_wall_checked_ms;

static long long now_ms_hv(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (long long)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

static void wallpaper_reload(void)
{
    long long now = now_ms_hv();
    if (g_wall_mtime != -2 && now - g_wall_checked_ms < 2000) return;
    g_wall_checked_ms = now;
    long long mt = g_wall_path.empty() ? -1 : css_file_mtime_ns(g_wall_path);
    if (mt == g_wall_mtime) return;
    g_wall_mtime = mt;
    free(g_wall); g_wall = nullptr;
    if (mt < 0) return;
    int iw = 0, ih = 0, comp = 0;
    unsigned char *img = stbi_load(g_wall_path.c_str(), &iw, &ih, &comp, 3);
    if (!img || iw <= 0 || ih <= 0) { if (img) stbi_image_free(img); return; }
    g_wall_w = g_scr_w; g_wall_h = g_scr_h;   /* screen size, not a temporary tall/small target */
    g_wall = (uint16_t *)malloc(sizeof(uint16_t) * g_wall_w * g_wall_h);
    if (g_wall) {
        /* cover-fit, centred crop, nearest sample */
        float sc = std::max((float)g_wall_w / iw, (float)g_wall_h / ih);
        float ox = (iw * sc - g_wall_w) / 2, oy = (ih * sc - g_wall_h) / 2;
        for (int y = 0; y < g_wall_h; y++) {
            int sy = std::min(ih - 1, std::max(0, (int)((y + oy) / sc)));
            for (int x = 0; x < g_wall_w; x++) {
                int sx = std::min(iw - 1, std::max(0, (int)((x + ox) / sc)));
                const unsigned char *p = img + (sy * iw + sx) * 3;
                g_wall[y * g_wall_w + x] = (uint16_t)(((p[0] & 0xF8) << 8) | ((p[1] & 0xFC) << 3) | (p[2] >> 3));
            }
        }
    }
    stbi_image_free(img);
}

extern "C" void html_view_set_wallpaper(const char *path)
{
    g_wall_path = path ? path : "";
    g_wall_mtime = -2;
    wallpaper_reload();
}

/* Clear the target to the wallpaper (tiled vertically for tall buffers) or black. */
static void clear_target(void)
{
    wallpaper_reload();
    if (!g_wall) { for (int i = 0; i < g_pitch_px * g_h; i++) g_fb[i] = 0; return; }
    for (int y = 0; y < g_h; y++) {
        int yy = (y + g_scroll_y) % (2 * g_wall_h);  /* scrolls with the page; mirror-tiled, no seam */
        if (yy >= g_wall_h) yy = 2 * g_wall_h - 1 - yy;
        const uint16_t *src = g_wall + yy * g_wall_w;
        for (int x = 0; x < g_w; x++) {
            int dx = g_rotate ? (g_w - 1 - x) : x;
            int dy = g_rotate ? (g_h - 1 - y) : y;
            g_fb[dy * g_pitch_px + dx] = src[x < g_wall_w ? x : g_wall_w - 1];
        }
    }
}

/* Parse + lay out + paint an HTML string into the framebuffer. Returns height. */
extern "C" int html_view_render_html(const char *html)
{
    if (!html || !g_container) return -1;
    long long tp = now_ms_hv();
    g_container->reset_state();
    g_doc.reset();
    document::ptr doc = document::createFromString(html, g_container);
    if (!doc) return -1;

    g_doc = doc;
    g_doc_overlay = 0;
    long long t0 = now_ms_hv();
    g_doc->render((pixel_t)g_w);
    long long t1 = now_ms_hv();
    clear_target();
    long long t2 = now_ms_hv();
    position clip(0, 0, (pixel_t)g_w, (pixel_t)g_h);
    g_doc->draw((uint_ptr)0, 0, -g_scroll_y, &clip);   /* shift up by scroll */
    if (g_h > 480) fprintf(stderr, "render_tall: parse %lld ms, layout %lld ms, clear %lld ms, draw %lld ms (h=%d)\n",
                           t0 - tp, t1 - t0, t2 - t1, now_ms_hv() - t2, g_h);
    element::ptr root = g_doc->root();                 /* full content height */
    return root ? (int)root->get_placement().height : g_h;
}

/* Render an overlay on top of the current framebuffer (no clear): the body must
 * be transparent so only its boxes paint. g_doc is set to the overlay so taps
 * hit it. Used for modal dialogs. */
extern "C" int html_view_render_overlay(const char *html)
{
    if (!html || !g_container) return -1;
    g_container->reset_state();
    g_doc.reset();
    document::ptr doc = document::createFromString(html, g_container);
    if (!doc) return -1;

    g_doc = doc;
    g_doc_overlay = 1;
    g_doc->render((pixel_t)g_w);
    position clip(0, 0, (pixel_t)g_w, (pixel_t)g_h);
    g_doc->draw((uint_ptr)0, 0, 0, &clip);
    return 0;
}

/* Render into a plain logical W*H RGB565 buffer (no rotation) for animations. */
extern "C" int html_view_render_to(uint16_t *buf, const char *html)
{
    uint16_t *sfb = g_fb; int sw = g_w, sh = g_h, sp = g_pitch_px, sr = g_rotate, ssc = g_scroll_y;
    g_fb = buf; g_w = sw; g_h = sh; g_pitch_px = sw; g_rotate = 0; g_scroll_y = 0;
    int hh = html_view_render_html(html);
    g_fb = sfb; g_w = sw; g_h = sh; g_pitch_px = sp; g_rotate = sr; g_scroll_y = ssc;
    return hh;
}

extern "C" int html_view_render_to_scroll(uint16_t *buf, const char *html, int scroll)
{
    uint16_t *sfb = g_fb; int sw = g_w, sh = g_h, sp = g_pitch_px, sr = g_rotate, ssc = g_scroll_y;
    g_fb = buf; g_w = sw; g_h = sh; g_pitch_px = sw; g_rotate = 0; g_scroll_y = scroll < 0 ? 0 : scroll;
    int hh = html_view_render_html(html);
    g_fb = sfb; g_w = sw; g_h = sh; g_pitch_px = sp; g_rotate = sr; g_scroll_y = ssc;
    return hh;
}

static uint16_t *g_saved_fb = nullptr;
static int g_saved_w = 0, g_saved_h = 0, g_saved_pitch = 0, g_saved_rotate = 0, g_saved_scroll = 0;

extern "C" void html_view_target_begin(uint16_t *buf, int scroll)
{
    if (g_saved_fb) return;
    g_saved_fb = g_fb; g_saved_w = g_w; g_saved_h = g_h;
    g_saved_pitch = g_pitch_px; g_saved_rotate = g_rotate; g_saved_scroll = g_scroll_y;
    g_fb = buf; g_pitch_px = g_w; g_rotate = 0; g_scroll_y = scroll < 0 ? 0 : scroll;
}

extern "C" void html_view_target_end(void)
{
    if (!g_saved_fb) return;
    g_fb = g_saved_fb; g_w = g_saved_w; g_h = g_saved_h;
    g_pitch_px = g_saved_pitch; g_rotate = g_saved_rotate; g_scroll_y = g_saved_scroll;
    g_saved_fb = nullptr;
}

extern "C" int html_view_render_to_size(uint16_t *buf, int w, int h, const char *html)
{
    uint16_t *sfb = g_fb; int sw = g_w, sh = g_h, sp = g_pitch_px, sr = g_rotate, ssc = g_scroll_y;
    g_fb = buf; g_w = w; g_h = h; g_pitch_px = w; g_rotate = 0; g_scroll_y = 0;
    int hh = html_view_render_html(html);
    g_fb = sfb; g_w = sw; g_h = sh; g_pitch_px = sp; g_rotate = sr; g_scroll_y = ssc;
    return hh;
}

extern "C" void html_view_set_uidir(const char *d) { g_ui_dir = d; }
extern "C" void html_view_set_scroll(int y) { g_scroll_y = y < 0 ? 0 : y; }
extern "C" void html_view_set_clip_top(int y) { g_clip_top = y < 0 ? 0 : y; }

/* Render the full page (no rotation, no clip to 480) into a tall W*bufh logical
 * buffer, for smooth windowed scrolling. Returns content height. */
extern "C" int html_view_render_tall(uint16_t *buf, const char *html, int bufh)
{
    uint16_t *sfb = g_fb; int sh = g_h, sp = g_pitch_px, sr = g_rotate, ssc = g_scroll_y;
    g_fb = buf; g_h = bufh; g_pitch_px = g_w; g_rotate = 0; g_scroll_y = 0;
    int hh = html_view_render_html(html);
    g_fb = sfb; g_h = sh; g_pitch_px = sp; g_rotate = sr; g_scroll_y = ssc;
    return hh;
}

/* Fill a rect directly (used for the scrollbar overlay). */
extern "C" void html_view_fill_rect(int x, int y, int w, int h, int r, int g, int b, int a)
{
    for (int yy = y; yy < y + h; yy++)
        for (int xx = x; xx < x + w; xx++)
            put_px(xx, yy, r, g, b, a);
}

/* Fill an arbitrary (possibly concave) polygon via scanline parity. Used by the
 * host to draw shapes litehtml/CSS can't — e.g. the battery charging bolt. */
extern "C" void html_view_fill_poly(const int *xs, const int *ys, int n, int r, int g, int b, int a)
{
    if (n < 3) return;
    int ymin = ys[0], ymax = ys[0];
    for (int i = 1; i < n; i++) { if (ys[i] < ymin) ymin = ys[i]; if (ys[i] > ymax) ymax = ys[i]; }
    for (int y = ymin; y <= ymax; y++) {
        int xi[16], cnt = 0;
        for (int i = 0; i < n && cnt < 16; i++) {
            int j = (i + 1) % n;
            int y0 = ys[i], y1 = ys[j], x0 = xs[i], x1 = xs[j];
            if (y0 == y1) continue;
            if ((y >= y0 && y < y1) || (y >= y1 && y < y0))
                xi[cnt++] = x0 + (int)((long)(y - y0) * (x1 - x0) / (y1 - y0));
        }
        for (int i = 0; i < cnt; i++)            /* sort intersections ascending */
            for (int k = i + 1; k < cnt; k++)
                if (xi[k] < xi[i]) { int t = xi[i]; xi[i] = xi[k]; xi[k] = t; }
        for (int i = 0; i + 1 < cnt; i += 2)
            for (int x = xi[i]; x <= xi[i + 1]; x++)
                put_px(x, y, r, g, b, a);
    }
}

/* Filled rounded rectangle directly (host overlays like the lock icon). */
extern "C" void html_view_fill_round_rect(int x, int y, int w, int h, int rad, int r, int g, int b, int a)
{
    if (w <= 0 || h <= 0) return;
    for (int yy = y; yy < y + h; yy++)
        for (int xx = x; xx < x + w; xx++)
        {
            int cov = rr_cov_fast(xx, yy, x, y, w, h, rad, rad, rad, rad);
            if (cov) put_px(xx, yy, r, g, b, a * cov / 16);
        }
}

/* Repaint a screen rect with the wallpaper (then an optional tint), so native
 * overlays like the status bar sit on the same backdrop as the page. */
extern "C" void html_view_paint_wallpaper(int x, int y, int w, int h, int tr, int tg, int tb, int ta)
{
    wallpaper_reload();
    for (int yy = y; yy < y + h; yy++)
        for (int xx = x; xx < x + w; xx++) {
            if (xx < 0 || yy < 0 || xx >= g_w || yy >= g_h) continue;
            uint16_t c = g_wall ? g_wall[(yy % g_wall_h) * g_wall_w + (xx % g_wall_w)] : 0;
            int dx = g_rotate ? (g_w - 1 - xx) : xx;
            int dy = g_rotate ? (g_h - 1 - yy) : yy;
            g_fb[dy * g_pitch_px + dx] = c;
            if (ta > 0) put_px(xx, yy, tr, tg, tb, ta);
        }
}
extern "C" int html_view_has_wallpaper(void) { wallpaper_reload(); return g_wall != nullptr; }

/* Native text calls use the numeral face while this is set (falls back per glyph). */
static int g_native_num;
extern "C" void html_view_native_num(int on) { g_native_num = on; }
static inline FT_Face native_face(unsigned cp)
{
    if (g_native_num && g_face2 && FT_Get_Char_Index(g_face2, cp)) return g_face2;
    return g_face;
}

extern "C" int html_view_text_width_px(const char *text, int size)
{
    if (!g_face || !text) return 0;
    FT_Set_Pixel_Sizes(g_face, 0, size);
    if (g_face2) FT_Set_Pixel_Sizes(g_face2, 0, size);
    int w = 0;
    for (const char *s = text; *s; ) {
        unsigned cp = utf8_next(s);
        const gc_ent *g = gc_get(native_face(cp), size, 0, cp, nullptr);
        if (g) w += g->adv;
    }
    return w;
}

extern "C" void html_view_text_bounds_px(const char *text, int size,
                                         int *x0, int *y0, int *x1, int *y1)
{
    if (x0) *x0 = 0;
    if (y0) *y0 = 0;
    if (x1) *x1 = 0;
    if (y1) *y1 = 0;
    if (!g_face || !text) return;
    FT_Set_Pixel_Sizes(g_face, 0, size);
    if (g_face2) FT_Set_Pixel_Sizes(g_face2, 0, size);
    int ascent = g_face->size->metrics.ascender >> 6;
    int pen = 0, minx = 0, miny = 0, maxx = 0, maxy = 0, seen = 0;
    for (const char *s = text; *s; ) {
        unsigned cp = utf8_next(s);
        const gc_ent *g = gc_get(native_face(cp), size, 0, cp, nullptr);
        if (!g) continue;
        int gx0 = pen + g->left;
        int gy0 = ascent - g->top;
        int gx1 = gx0 + g->w;
        int gy1 = gy0 + g->rows;
        if (!seen) {
            minx = gx0; miny = gy0; maxx = gx1; maxy = gy1; seen = 1;
        } else {
            if (gx0 < minx) minx = gx0;
            if (gy0 < miny) miny = gy0;
            if (gx1 > maxx) maxx = gx1;
            if (gy1 > maxy) maxy = gy1;
        }
        pen += g->adv;
    }
    if (!seen) return;
    if (x0) *x0 = minx;
    if (y0) *y0 = miny;
    if (x1) *x1 = maxx;
    if (y1) *y1 = maxy;
}

extern "C" void html_view_draw_text_px(int x, int y, const char *text, int size, int bold,
                                       int r, int g, int b, int a)
{
    if (!g_face || !text) return;
    FT_Set_Pixel_Sizes(g_face, 0, size);
    if (g_face2) FT_Set_Pixel_Sizes(g_face2, 0, size);
    int ascent = g_face->size->metrics.ascender >> 6;
    int pen = x, base = y + ascent;
    for (const char *s = text; *s; ) {
        unsigned cp = utf8_next(s);
        const gc_ent *gc = gc_get(native_face(cp), size, 0, cp, nullptr);
        if (!gc) continue;
        for (int pass = 0; pass < (bold ? 2 : 1); pass++) {
            int ox = pen + gc->left + pass, oy = base - gc->top;
            for (int row = 0; row < gc->rows; row++)
                for (int col = 0; col < gc->w; col++) {
                    int aa = gc->buf[row * gc->pitch + col];
                    if (aa) put_px(ox + col, oy + row, r, g, b, aa * a / 255);
                }
        }
        pen += gc->adv;
    }
}

extern "C" void html_view_draw_text_contrast_px(int x, int y, const char *text, int size, int bold,
                                                int dr, int dg, int db, int lr, int lg, int lb, int a)
{
    if (!g_face || !text) return;
    FT_Set_Pixel_Sizes(g_face, 0, size);
    if (g_face2) FT_Set_Pixel_Sizes(g_face2, 0, size);
    int ascent = g_face->size->metrics.ascender >> 6;
    int pen = x, base = y + ascent;
    for (const char *s = text; *s; ) {
        unsigned cp = utf8_next(s);
        const gc_ent *gc = gc_get(native_face(cp), size, 0, cp, nullptr);
        if (!gc) continue;
        for (int pass = 0; pass < (bold ? 2 : 1); pass++) {
            int ox = pen + gc->left + pass, oy = base - gc->top;
            for (int row = 0; row < gc->rows; row++)
                for (int col = 0; col < gc->w; col++) {
                    int aa = gc->buf[row * gc->pitch + col];
                    if (!aa) continue;
                    uint16_t bg = get_px565(ox + col, oy + row);
                    int br = ((bg >> 11) & 0x1F) * 255 / 31;
                    int bgc = ((bg >> 5) & 0x3F) * 255 / 63;
                    int bb = (bg & 0x1F) * 255 / 31;
                    int luma = (br * 299 + bgc * 587 + bb * 114) / 1000;
                    int r = luma > 116 ? dr : lr;
                    int g = luma > 116 ? dg : lg;
                    int b = luma > 116 ? db : lb;
                    put_px(ox + col, oy + row, r, g, b, aa * a / 255);
                }
        }
        pen += gc->adv;
    }
}

/* Hit-test a tap; returns the clicked anchor href ("" if none). */
extern "C" const char *html_view_click(float x, float y)
{
    g_clicked.clear();
    if (g_doc) {
        position::vector rb;
        float yy = y + (g_doc_overlay ? 0 : g_scroll_y);
        g_doc->on_lbutton_down(x, yy, x, yy, rb);
        g_doc->on_lbutton_up(x, yy, x, yy, rb);
    }
    return g_clicked.c_str();
}

/* ---- custom chart drawing: native polylines into a litehtml placeholder ----
 * Flow: render the page (which lays out an empty <div id="chart-..">), query the
 * div's box with html_view_rect(), then draw series into it with html_view_polyline().
 * Coords are logical (pre-rotation); put_px maps to the panel. */

/* Bresenham line, thick px wide, clipped to [rx,rx+rw) x [ry,ry+rh). */
/* Anti-aliased thick segment with round caps: coverage from the distance of
 * each pixel centre to the segment. Used for icons and chart lines. */
extern "C" void html_view_aa_line(float x0, float y0, float x1, float y1, float wd,
                                  int r, int g, int b, int a)
{
    float hw = wd / 2.0f;
    int bx0 = (int)std::floor(std::min(x0, x1) - hw - 1), bx1 = (int)std::ceil(std::max(x0, x1) + hw + 1);
    int by0 = (int)std::floor(std::min(y0, y1) - hw - 1), by1 = (int)std::ceil(std::max(y0, y1) + hw + 1);
    float vx = x1 - x0, vy = y1 - y0, l2 = vx * vx + vy * vy;
    for (int py = by0; py <= by1; py++)
        for (int px = bx0; px <= bx1; px++) {
            float cx = px + 0.5f, cy = py + 0.5f;
            float t = l2 > 0 ? ((cx - x0) * vx + (cy - y0) * vy) / l2 : 0;
            t = t < 0 ? 0 : t > 1 ? 1 : t;
            float dx = cx - (x0 + t * vx), dy = cy - (y0 + t * vy);
            float cov = hw + 0.5f - std::sqrt(dx * dx + dy * dy);
            if (cov <= 0) continue;
            if (cov > 1) cov = 1;
            put_px(px, py, r, g, b, (int)(a * cov));
        }
}

/* Anti-aliased filled circle. */
extern "C" void html_view_aa_disc(float cx, float cy, float rad, int r, int g, int b, int a)
{
    for (int py = (int)(cy - rad - 1); py <= (int)(cy + rad + 1); py++)
        for (int px = (int)(cx - rad - 1); px <= (int)(cx + rad + 1); px++) {
            float dx = px + 0.5f - cx, dy = py + 0.5f - cy;
            float cov = rad + 0.5f - std::sqrt(dx * dx + dy * dy);
            if (cov <= 0) continue;
            put_px(px, py, r, g, b, (int)(a * (cov > 1 ? 1 : cov)));
        }
}

__attribute__((unused)) static void chart_line(int x0, int y0, int x1, int y1,
                       int rx, int ry, int rw, int rh, int r, int g, int b, int thick)
{
    int dx = std::abs(x1 - x0), sx = x0 < x1 ? 1 : -1;
    int dy = -std::abs(y1 - y0), sy = y0 < y1 ? 1 : -1;
    int err = dx + dy;
    for (;;) {
        for (int ty = 0; ty < thick; ty++)
            for (int tx = 0; tx < thick; tx++) {
                int px = x0 + tx, py = y0 + ty;
                if (px >= rx && px < rx + rw && py >= ry && py < ry + rh)
                    put_px(px, py, r, g, b, 255);
            }
        if (x0 == x1 && y0 == y1) break;
        int e2 = 2 * err;
        if (e2 >= dy) { err += dy; x0 += sx; }
        if (e2 <= dx) { err += dx; y0 += sy; }
    }
}

/* Find an element by CSS selector and return its laid-out box. 1 if found. */
extern "C" int html_view_rect(const char *sel, int *x, int *y, int *w, int *h)
{
    if (!g_doc) return 0;
    element::ptr root = g_doc->root();
    if (!root) return 0;
    element::ptr el = root->select_one(sel);
    if (!el) return 0;
    position p = el->get_placement();
    int sy = g_doc_overlay ? 0 : g_scroll_y;
    *x = (int)p.x; *y = (int)p.y - sy; *w = (int)p.width; *h = (int)p.height;
    return (*w > 1 && *h > 1);
}

/* Draw a value series as a polyline inside the rect. vals normalized by
 * [vmin,vmax]; top = vmax. fill_a>0 fills the area under the line at that alpha. */
extern "C" void html_view_polyline(int x, int y, int w, int h,
                                   const int *vals, int n, int vmin, int vmax,
                                   int r, int g, int b, int thick, int fill_a)
{
    if (n <= 0 || w <= 1 || h <= 1) return;
    if (vmax <= vmin) vmax = vmin + 1;

    /* area under the line: vertical gradient, fill_a at the line fading to 0 */
    if (fill_a > 0) {
        for (int col = 0; col < w; col++) {
            double t = (n > 1) ? (double)col / (w - 1) * (n - 1) : 0.0;
            int i0 = (int)t; double fr = t - i0;
            int v0 = vals[i0], v1 = (i0 + 1 < n) ? vals[i0 + 1] : v0;
            double v = v0 + (v1 - v0) * fr;
            if (v < vmin) v = vmin; if (v > vmax) v = vmax;
            int py = y + (h - 1) - (int)((v - vmin) * (h - 1) / (vmax - vmin));
            int span = y + h - py;
            for (int yy = py; yy < y + h; yy++)
                put_px(x + col, yy, r, g, b, fill_a * (span - (yy - py)) / (span > 0 ? span : 1));
        }
    }

    float px = 0, py = 0;
    for (int i = 0; i < n; i++) {
        int v = vals[i]; if (v < vmin) v = vmin; if (v > vmax) v = vmax;
        float cx = x + (n > 1 ? (float)i * (w - 1) / (n - 1) : 0);
        float cy = y + (h - 1) - (float)((long)(v - vmin) * (h - 1)) / (vmax - vmin);
        if (i > 0) html_view_aa_line(px, py, cx, cy, thick > 1 ? thick - 0.2f : 1.2f, r, g, b, 255);
        px = cx; py = cy;
    }
}

/* Rounded outline (native widgets like the battery icon). */
extern "C" void html_view_stroke_round_rect(int x, int y, int w, int h, int rad, int t, int r, int g, int b, int a)
{
    if (!g_container) return;
    g_container->stroke_rounded(x, y, w, h, rad, rad, rad, rad, t, web_color(r, g, b, a));
}

/* Wallpaper thumbnail: decode once, cover-scale to w x h, cache, blit with
 * anti-aliased rounded corners (settings wallpaper chooser). */
extern "C" void html_view_draw_thumb(const char *path, int x, int y, int w, int h, int rad)
{
    struct thumb { std::string path; int w, h; std::vector<uint16_t> px; };
    static std::vector<thumb> cache;
    if (!path || w <= 0 || h <= 0) return;
    thumb *t = nullptr;
    for (auto &c : cache) if (c.path == path && c.w == w && c.h == h) t = &c;
    if (!t) {
        int iw = 0, ih = 0, comp = 0;
        unsigned char *img = stbi_load(path, &iw, &ih, &comp, 3);
        if (!img) return;
        thumb n; n.path = path; n.w = w; n.h = h; n.px.resize((size_t)w * h);
        float sc = std::max((float)w / iw, (float)h / ih);
        float ox = (iw * sc - w) / 2, oy = (ih * sc - h) / 2;
        for (int yy = 0; yy < h; yy++)
            for (int xx = 0; xx < w; xx++) {
                /* box-average the source area for a smooth downscale */
                int sx0 = (int)((xx + ox) / sc), sy0 = (int)((yy + oy) / sc);
                int sx1 = std::max(sx0 + 1, (int)((xx + 1 + ox) / sc)), sy1 = std::max(sy0 + 1, (int)((yy + 1 + oy) / sc));
                long r = 0, g = 0, b = 0, cnt = 0;
                for (int sy = sy0; sy < sy1 && sy < ih; sy++)
                    for (int sx = sx0; sx < sx1 && sx < iw; sx++) {
                        const unsigned char *p = img + (sy * iw + sx) * 3;
                        r += p[0]; g += p[1]; b += p[2]; cnt++;
                    }
                if (!cnt) cnt = 1;
                n.px[(size_t)yy * w + xx] = (uint16_t)((((r / cnt) & 0xF8) << 8) | (((g / cnt) & 0xFC) << 3) | ((b / cnt) >> 3));
            }
        stbi_image_free(img);
        if (cache.size() > 8) cache.erase(cache.begin());
        cache.push_back(std::move(n));
        t = &cache.back();
    }
    for (int yy = 0; yy < h; yy++)
        for (int xx = 0; xx < w; xx++) {
            int cov = rr_cov_fast(x + xx, y + yy, x, y, w, h, rad, rad, rad, rad);
            if (!cov) continue;
            uint16_t c = t->px[(size_t)yy * w + xx];
            put_px(x + xx, y + yy, ((c >> 11) & 0x1F) * 255 / 31, ((c >> 5) & 0x3F) * 255 / 63, (c & 0x1F) * 255 / 31, 255 * cov / 16);
        }
}


/* Native clip rect for marquee text; reset with w <= 0. */
extern "C" void html_view_clip_rect(int x, int y, int w, int h)
{
    if (w <= 0 || h <= 0) { g_cl = g_ct = -100000; g_cr = g_cb = 100000; return; }
    g_cl = x; g_cr = x + w; g_ct = y; g_cb = y + h;
}

/* Copy a logical rect of the framebuffer out / back (marquee backgrounds). */
extern "C" void html_view_save_rect(int x, int y, int w, int h, uint16_t *buf)
{
    for (int yy = 0; yy < h; yy++)
        for (int xx = 0; xx < w; xx++)
            buf[yy * w + xx] = get_px565(x + xx, y + yy);
}
extern "C" void html_view_restore_rect(int x, int y, int w, int h, const uint16_t *buf)
{
    for (int yy = 0; yy < h; yy++)
        for (int xx = 0; xx < w; xx++) {
            int px = x + xx, py = y + yy;
            if (px < 0 || py < 0 || px >= g_w || py >= g_h) continue;
            int dx = g_rotate ? (g_w - 1 - px) : px, dy = g_rotate ? (g_h - 1 - py) : py;
            g_fb[dy * g_pitch_px + dx] = buf[yy * w + xx];
        }
}
