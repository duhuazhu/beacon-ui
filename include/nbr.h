/*
 * nbr.h - "附近基站" page: neighbouring cells ranked by RSRP.
 *
 * Two sources:
 *  - live:    zwrt-datad's passive neighbour collector (QTrace over diag_mdlog).
 *             Switched on only while the page is visible, off again shortly
 *             after leaving it or when the screen goes dark.
 *  - scan:    the firmware's own neighbour search (zte_nwinfo_api), which drops
 *             the data connection for a few seconds; only on an explicit
 *             double tap.
 * All device I/O runs as background shell jobs writing /tmp files; the render
 * path only parses those files, so nothing here blocks the UI.
 *
 * SPDX-License-Identifier: MIT
 */
#ifndef U60_NBR_H
#define U60_NBR_H

#include <stddef.h>
#include <stdint.h>

typedef struct {
    int  nr;              /* serving RAT is NR (SA/NSA anchor on NR) */
    int  pci;
    long arfcn;
    char band[16];        /* "78" (digits only) */
    char lock[64];        /* lock_nr_cell "pci,arfcn,band" while a 5G cell lock is set, else "" */
    char rsrp[24];        /* preformatted, e.g. "-98" */
    char sinr[24];
    char nrca[256];       /* datad nrca: idx,pci,?,band,arfcn,...; (carriers in use) */
} nbr_serving_t;

/* Main loop, every iteration (cheap; time-gated inside). The live collector
 * runs only while on_page; screen_on = 0 stops it at once. */
void nbr_tick(int on_page, int screen_on, uint32_t now_ms);

/* HTML for {{NBRBODY}}. lock_armed is the cell-lock key armed by a first tap
 * ("lock:pci:arfcn:band") so its button can read "再点一次". */
const char *nbr_body_html(const nbr_serving_t *sv, const char *lock_armed);

/* Actions starting with "nbr:" (prefix "act:" stripped). Returns 1 if handled;
 * a short message for the toast may be written to toast. */
int nbr_handle_action(const char *a, uint32_t now_ms, char *toast, size_t tcap);

#endif /* U60_NBR_H */
