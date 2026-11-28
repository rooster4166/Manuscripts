/* gen.c -- graphs up to isomorphism by vertex addition and canonical forms (individualisation-
   refinement, no automorphism pruning), for n <= 11.  Written for the conj-r session.

   gen N        : all graphs on 1..N vertices are built level by level; prints the counts per
                  level on stderr, and the graphs of order N in graph6 on stdout.
   gen N odd    : as above for levels < N; at level N prints only the graphs with all degrees odd
                  (each all-odd graph of order N arises from a graph of order N-1 by adding a
                  vertex joined exactly to its even-degree vertices).
   gen N oddc   : the same, connected only.
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 12
typedef uint16_t row;

static int n;
static row g[MAXN];

/* canonical form: adjacency matrix upper triangle as a 64-bit word (n <= 11 -> 55 bits) */
static uint64_t best; static int have_best;

static uint64_t code_of(const int *perm /* perm[pos] = vertex */) {
    uint64_t c = 0; int k = 0;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
        if (g[perm[i]] >> perm[j] & 1) c |= (uint64_t)1 << (63 - k);
        k++;
    }
    return c;
}

/* partition as an ordered list of cells: cellof[v], and cells in order */
static void refine(int *cell, int ncell, int *ncell_out) {
    /* cell[v] in 0..ncell-1, ordered.  Equitable refinement: split cells by the multiset of
       neighbour counts into each cell, repeat until stable.  Cell order: by old cell, then by
       signature (lexicographic), which is isomorphism-invariant. */
    for (;;) {
        int sig[MAXN][MAXN];
        for (int v = 0; v < n; v++) {
            for (int c = 0; c < ncell; c++) sig[v][c] = 0;
            for (int w = 0; w < n; w++) if (g[v] >> w & 1) sig[v][cell[w]]++;
        }
        /* new key: (cell[v], sig[v][0..ncell-1]) ; sort vertices by key */
        int ord[MAXN];
        for (int v = 0; v < n; v++) ord[v] = v;
        for (int a = 1; a < n; a++) {     /* insertion sort */
            int x = ord[a], b = a - 1;
            while (b >= 0) {
                int y = ord[b], cmp = 0;
                if (cell[y] != cell[x]) cmp = cell[y] > cell[x] ? 1 : -1;
                else for (int c = 0; c < ncell && !cmp; c++)
                    if (sig[y][c] != sig[x][c]) cmp = sig[y][c] > sig[x][c] ? 1 : -1;
                if (cmp <= 0) break;
                ord[b + 1] = y; b--;
            }
            ord[b + 1] = x;
        }
        int nc[MAXN], k = 0;
        for (int a = 0; a < n; a++) {
            if (a > 0) {
                int x = ord[a], y = ord[a - 1], same = cell[x] == cell[y];
                for (int c = 0; c < ncell && same; c++) if (sig[x][c] != sig[y][c]) same = 0;
                if (!same) k++;
            }
            nc[ord[a]] = k;
        }
        k++;
        if (k == ncell) { *ncell_out = ncell; return; }
        for (int v = 0; v < n; v++) cell[v] = nc[v];
        ncell = k;
    }
}

static void search(int *cell, int ncell) {
    int nc2;
    refine(cell, ncell, &nc2); ncell = nc2;
    if (ncell == n) {
        int perm[MAXN];
        for (int v = 0; v < n; v++) perm[cell[v]] = v;
        uint64_t c = code_of(perm);
        if (!have_best || c < best) { best = c; have_best = 1; }
        return;
    }
    /* first non-singleton cell */
    int cnt[MAXN] = {0};
    for (int v = 0; v < n; v++) cnt[cell[v]]++;
    int t = 0; while (cnt[t] == 1) t++;
    for (int v = 0; v < n; v++) if (cell[v] == t) {
        int c2[MAXN];
        for (int w = 0; w < n; w++) c2[w] = cell[w] > t ? cell[w] + 1 : cell[w];
        for (int w = 0; w < n; w++) if (w != v && cell[w] == t) c2[w] = t + 1;
        search(c2, ncell + 1);
    }
}

static uint64_t canon(void) {
    int cell[MAXN];
    for (int v = 0; v < n; v++) cell[v] = 0;
    have_best = 0;
    search(cell, 1);
    return best;
}

/* hash set of uint64 */
typedef struct { uint64_t *t; size_t cap, cnt; } hset;
static void hs_init(hset *h, size_t cap) { h->cap = cap; h->cnt = 0; h->t = calloc(cap, 8); }
static int hs_add(hset *h, uint64_t x) {
    x |= 1;  /* avoid 0: codes have bit 0 unused for n <= 11 (55 bits from the top) */
    size_t i = (x * 0x9E3779B97F4A7C15ULL) % h->cap;
    while (h->t[i]) { if (h->t[i] == x) return 0; i = (i + 1) % h->cap; }
    h->t[i] = x; h->cnt++;
    if (h->cnt * 2 > h->cap) { fprintf(stderr, "hash full\n"); exit(1); }
    return 1;
}

static void decode(uint64_t c, int nn) {
    n = nn; for (int v = 0; v < n; v++) g[v] = 0;
    int k = 0;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
        if (c >> (63 - k) & 1) { g[i] |= 1 << j; g[j] |= 1 << i; }
        k++;
    }
}

static void print_g6(void) {
    char s[64]; int p = 0; s[p++] = 63 + n;
    int bits = 0, acc = 0;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
        acc = acc << 1 | (g[i] >> j & 1); bits++;
        if (bits == 6) { s[p++] = 63 + acc; bits = 0; acc = 0; }
    }
    if (bits) { acc <<= 6 - bits; s[p++] = 63 + acc; }
    s[p] = 0; puts(s);
}

static int connected(void) {
    row seen = 1, fr = 1;
    while (fr) { row nf = 0; for (int v = 0; v < n; v++) if (fr >> v & 1) nf |= g[v]; fr = nf & ~seen; seen |= nf; }
    return seen == (row)((1u << n) - 1);
}

int main(int argc, char **argv) {
    int N = atoi(argv[1]);
    int mode = argc > 2 ? (!strcmp(argv[2], "odd") ? 1 : !strcmp(argv[2], "oddc") ? 2 : 0) : 0;
    /* level lists */
    uint64_t *cur = malloc(8); size_t ncur = 1; cur[0] = 0; /* n = 1: one graph, code 0 */
    fprintf(stderr, "n=1: 1\n");
    for (int lev = 2; lev <= N; lev++) {
        int last = lev == N && mode;
        hset h; hs_init(&h, last ? (size_t)4 * ncur + 16 : (size_t)64 * ncur * 4 + 1024);
        uint64_t *nxt = NULL; size_t nnxt = 0, capn = 0;
        for (size_t a = 0; a < ncur; a++) {
            decode(cur[a], lev - 1);
            row base[MAXN]; memcpy(base, g, sizeof g);
            int lo = 0, hi = (1 << (lev - 1)) - 1;
            row S0 = 0;
            if (last) {
                for (int v = 0; v < lev - 1; v++) {
                    int d = __builtin_popcount(base[v]);
                    if (d % 2 == 0) S0 |= 1 << v;
                }
                if (__builtin_popcount(S0) % 2 == 0) continue;
                lo = hi = S0;
            }
            for (int S = lo; S <= hi; S++) {
                n = lev; memcpy(g, base, sizeof g); g[lev - 1] = 0;
                for (int v = 0; v < lev - 1; v++) if (S >> v & 1) { g[v] |= 1 << (lev - 1); g[lev - 1] |= 1 << v; }
                if (last && mode == 2 && !connected()) continue;
                uint64_t c = canon();
                if (hs_add(&h, c)) {
                    if (nnxt == capn) { capn = capn ? 2 * capn : 1024; nxt = realloc(nxt, capn * 8); }
                    nxt[nnxt++] = c;
                }
            }
        }
        free(h.t); free(cur); cur = nxt; ncur = nnxt;
        fprintf(stderr, "n=%d: %zu\n", lev, ncur);
    }
    for (size_t a = 0; a < ncur; a++) { decode(cur[a], N); print_g6(); }
    return 0;
}
