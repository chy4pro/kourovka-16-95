/* ROUND 6-AV (registry R6.124): clean-room exhaustive verification of Conjecture J over small prime fields,
 * directly from the definition (no lemmas, no restricted witness set):
 *   configuration: m >= 1, columns c_0 = x, c_k = e_k + y_k x (k = 1..m), x, y in F_p^m.
 *   witness: choose an omitted column j in {0..m} and an arrangement tau (bijection from matrix positions
 *   1..m to the remaining column labels); M has column r = c_{tau(r)}, b = c_j;
 *   D_{j,tau} = det [ b, Mb, ..., M^{m-1} b ]  over F_p.
 *   J holds at (x, y) iff some D_{j,tau} != 0.  This program checks EVERY (x, y) in F_p^m x F_p^m and reports
 *   any point with no witness (exhaustive over all (m+1)! candidates, with early exit on the first witness).
 * Usage: round6_r1alln_exhaust p m
 * Output: "p=<p> m=<m> points=<N> all_witnessed=1 max_candidates_scanned=<k> avg=<a>" or the counterexample.
 * Plain C99, no dependencies.  Memory: O(m^2). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int P, M;
typedef unsigned char u8;

/* determinant of an M x M matrix over F_p (Gaussian elimination), a is row-major, destroyed */
static int det_mod(u8 *a) {
    int det = 1;
    for (int col = 0; col < M; col++) {
        int piv = -1;
        for (int r = col; r < M; r++) if (a[r * M + col]) { piv = r; break; }
        if (piv < 0) return 0;
        if (piv != col) {
            for (int c = col; c < M; c++) { u8 t = a[piv * M + c]; a[piv * M + c] = a[col * M + c]; a[col * M + c] = t; }
            det = (P - det) % P;
        }
        int pv = a[col * M + col];
        det = (det * pv) % P;
        /* normalise pivot row to 1 (multiply by inverse) */
        int inv = 1; for (int e = 1; e < P - 1; e++) { inv = (inv * pv) % P; } /* pv^(p-2) mod p */
        for (int c = col; c < M; c++) a[col * M + c] = (u8)((a[col * M + c] * inv) % P);
        for (int r = col + 1; r < M; r++) {
            int f = a[r * M + col];
            if (f) for (int c = col; c < M; c++) a[r * M + c] = (u8)((a[r * M + c] + P * P - f * a[col * M + c]) % P);
        }
    }
    return det;
}

static u8 cols[9][8];       /* c_0..c_m, each an M-vector */
static u8 Mat[8][8];        /* matrix columns (index [col][row]) */
static u8 kry[8 * 8];       /* Krylov row-major for det */

static int try_candidate(const int *labels, int j) {
    /* labels: array of M column labels for matrix positions; b = c_j */
    u8 b[8], v[8], w[8];
    for (int r = 0; r < M; r++) for (int c = 0; c < M; c++) Mat[c][r] = cols[labels[c]][r];
    memcpy(b, cols[j], M);
    memcpy(v, b, M);
    for (int k = 0; k < M; k++) {
        for (int r = 0; r < M; r++) kry[r * M + k] = v[r];
        if (k + 1 < M) {
            for (int r = 0; r < M; r++) { int s = 0; for (int c = 0; c < M; c++) s += Mat[c][r] * v[c]; w[r] = (u8)(s % P); }
            memcpy(v, w, M);
        }
    }
    return det_mod(kry);
}

static int perm_labels[9], perm_used[9];
static int found;
static long scanned;

static void search_perms(int pos, const int *avail, int navail, int j) {
    if (found) return;
    if (pos == M) { scanned++; if (try_candidate(perm_labels, j)) found = 1; return; }
    for (int i = 0; i < navail; i++) {
        if (perm_used[i]) continue;
        perm_used[i] = 1; perm_labels[pos] = avail[i];
        search_perms(pos + 1, avail, navail, j);
        perm_used[i] = 0;
        if (found) return;
    }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s p m\n", argv[0]); return 2; }
    P = atoi(argv[1]); M = atoi(argv[2]);
    if (M < 1 || M > 8 || P < 2 || P > 13) { fprintf(stderr, "bad p/m\n"); return 2; }
    long npts = 1; for (int i = 0; i < 2 * M; i++) npts *= P;
    long maxscan = 0, totalscan = 0; long bad = 0;
    u8 x[8], y[8];
    for (long pt = 0; pt < npts; pt++) {
        long v = pt;
        for (int i = 0; i < M; i++) { x[i] = v % P; v /= P; }
        for (int i = 0; i < M; i++) { y[i] = v % P; v /= P; }
        /* columns */
        for (int r = 0; r < M; r++) cols[0][r] = x[r];
        for (int k = 1; k <= M; k++) for (int r = 0; r < M; r++) cols[k][r] = (u8)((((r == k - 1) ? 1 : 0) + y[k - 1] * x[r]) % P);
        found = 0; scanned = 0;
        for (int j = 0; j <= M && !found; j++) {
            int avail[9]; int na = 0;
            for (int k = 0; k <= M; k++) if (k != j) avail[na++] = k;
            memset(perm_used, 0, sizeof perm_used);
            search_perms(0, avail, na, j);
        }
        totalscan += scanned; if (scanned > maxscan) maxscan = scanned;
        if (!found) {
            bad++;
            printf("COUNTEREXAMPLE p=%d m=%d x=", P, M);
            for (int i = 0; i < M; i++) printf("%d,", x[i]);
            printf(" y=");
            for (int i = 0; i < M; i++) printf("%d,", y[i]);
            printf("\n");
        }
    }
    printf("p=%d m=%d points=%ld all_witnessed=%d bad=%ld max_candidates_scanned=%ld avg=%.2f\n",
           P, M, npts, bad == 0, bad, maxscan, (double)totalscan / (double)npts);
    return bad == 0 ? 0 : 1;
}
