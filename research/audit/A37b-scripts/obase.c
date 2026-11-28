/* obase.c -- audit A37b: independent exact decider for constrained Lovasz decompositions.
   Written from scratch for the audit (shares no code with allodd_dl.c or route_ext.c).

   Query (stdin, one per line):
     n m u1 v1 ... um vm b0 .. b_{n-1} X0 .. X_{n-1} k s1 t1 ... sk tk
   b_v in {0,1}: the number of path ends required at v (a vertex with b_v = 0 must have even
   degree, with b_v = 1 odd degree).  X_v: vertex bit mask; the path ending at v must avoid X_v.
   (s_i, t_i): forbidden end pairs -- no path may have ends s_i and t_i.
   Answer: "1 | v0 v1 ... | ... |" (a witness), "0", or "2" (unknown: node budget OBASE_BUDGET hit;
   no budget unless that environment variable is set).
   Since every constraint concerns a single path (its two ends and its vertex set), whether the
   remaining edge set R can be completed depends only on (R, set of vertices already ended):
   the failure memo is keyed on exactly that pair.
   Pruning (necessary conditions): parity of every vertex in R; every component of R with an edge
   contains an unended vertex; per component C with q = (#unended in C)/2 paths: d <= 2q at a
   vertex with no end left, d <= 2q - 1 at an unended vertex, e(C) <= q(|C| - 1).  Nothing else.
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 20
#define MAXM 64
static int n, m, eu[MAXM], ev[MAXM], b[MAXN], X[MAXN];
static int adjv[MAXN][MAXN], adje[MAXN][MAXN], adeg[MAXN];
static uint64_t inc[MAXN];
static int forb[MAXN];            /* forb[s] bit t: (s,t) forbidden end pair */

/* paths of the current partial solution */
static int pv[MAXN][MAXN + 1], plen[MAXN], np;

/* failure memo */
#define HB 22
#define HS (1u << HB)
typedef struct { uint64_t R; uint32_t e; uint32_t st; } hent;
static hent *ht; static uint32_t stamp = 1; static unsigned hcnt;
static unsigned hix(uint64_t R, uint32_t e) {
    uint64_t h = (R ^ ((uint64_t)e << 40)) * 0x9E3779B97F4A7C15ULL;
    h ^= h >> 29; h *= 0xBF58476D1CE4E5B9ULL; h ^= h >> 32;
    return (unsigned)(h & (HS - 1));
}
static int mhas(uint64_t R, uint32_t e) {
    for (unsigned i = hix(R, e);; i = (i + 1) & (HS - 1)) {
        if (ht[i].st != stamp) return 0;
        if (ht[i].R == R && ht[i].e == e) return 1;
    }
}
static void mput(uint64_t R, uint32_t e) {
    if (hcnt > HS / 2) return;
    for (unsigned i = hix(R, e);; i = (i + 1) & (HS - 1)) {
        if (ht[i].st != stamp) { ht[i].R = R; ht[i].e = e; ht[i].st = stamp; hcnt++; return; }
        if (ht[i].R == R && ht[i].e == e) return;
    }
}

static long long nodes, budget; static int aborted;
static int ok_state(uint64_t R, int ended) {
    int need = 0;
    for (int v = 0; v < n; v++) {
        int d = __builtin_popcountll(R & inc[v]);
        int want = (b[v] && !(ended >> v & 1)) ? 1 : 0;
        if ((d & 1) != want) return 0;
        if (want) need |= 1 << v;
    }
    /* every component with an edge has an unended vertex */
    int seen = 0;
    for (int v0 = 0; v0 < n; v0++) {
        if ((seen >> v0 & 1) || !(R & inc[v0])) continue;
        int C = 1 << v0, fr = 1 << v0;
        while (fr) {
            int v = __builtin_ctz(fr); fr &= fr - 1;
            for (int i = 0; i < adeg[v]; i++) if (R >> adje[v][i] & 1) {
                int y = adjv[v][i];
                if (!(C >> y & 1)) { C |= 1 << y; fr |= 1 << y; }
            }
        }
        seen |= C;
        if (!(C & need)) return 0;
        /* degree bounds: q = (#vertices of C still needing an end)/2 paths lie in C, each
           visits a vertex at most once: d <= 2q at a vertex with no end left, d <= 2q - 1 at a
           vertex still needing its end; and e(C) <= q(|C| - 1). */
        int q = __builtin_popcount(C & need) / 2, ec = 0;
        for (int cm = C; cm; cm &= cm - 1) {
            int v = __builtin_ctz(cm);
            int d = __builtin_popcountll(R & inc[v]);
            ec += d;
            if (need >> v & 1) { if (d > 2 * q - 1) return 0; }
            else if (d > 2 * q) return 0;
        }
        if (ec / 2 > q * (__builtin_popcount(C) - 1)) return 0;
    }
    return 1;
}

static int solve(uint64_t R, int ended);

/* cur[0..clen-1] is the path being grown (a buffer local to the calling solve) */
static int grow(uint64_t R, int ended, int x, int u, int vm, uint64_t pm, int *cur, int clen) {
    for (int i = 0; i < adeg[u]; i++) {
        int y = adjv[u][i], e = adje[u][i];
        if (!(R >> e & 1) || (vm >> y & 1) || (X[x] >> y & 1)) continue;
        cur[clen] = y;
        int vm2 = vm | (1 << y); uint64_t pm2 = pm | (1ULL << e);
        if (b[y] && !(ended >> y & 1) && !(forb[x] >> y & 1) && !(X[y] & vm2)) {
            memcpy(pv[np], cur, (clen + 1) * sizeof(int)); plen[np] = clen + 1; np++;
            if (solve(R & ~pm2, ended | (1 << x) | (1 << y))) return 1;
            np--;
        }
        if (grow(R, ended, x, y, vm2, pm2, cur, clen + 1)) return 1;
    }
    return 0;
}

static int solve(uint64_t R, int ended) {
    if (aborted) return 0;
    if (budget && ++nodes > budget) { aborted = 1; return 0; }
    int x = -1;
    /* any unended vertex ends exactly one remaining path, so the start may be chosen freely:
       prefer a constrained vertex (nonempty X or a forbidden partner) */
    for (int v = 0; v < n; v++) if (b[v] && !(ended >> v & 1) && (X[v] || forb[v])) { x = v; break; }
    if (x < 0) for (int v = 0; v < n; v++) if (b[v] && !(ended >> v & 1)) { x = v; break; }
    if (x < 0) return R == 0;
    if (!ok_state(R, ended)) return 0;
    if (mhas(R, (uint32_t)ended)) return 0;
    int cur[MAXN + 1];
    cur[0] = x;
    int r = grow(R, ended, x, x, 1 << x, 0, cur, 1);
    if (!r && !aborted) mput(R, (uint32_t)ended);
    return r;
}

int main(void) {
    ht = calloc(HS, sizeof(hent));
    if (getenv("OBASE_BUDGET")) budget = atoll(getenv("OBASE_BUDGET"));   /* 0 = none */
    static char line[1 << 16];
    while (fgets(line, sizeof line, stdin)) {
        char *p = line; int k;
        #define RD() (int)strtol(p, &p, 10)
        n = RD(); if (n <= 0) continue; m = RD();
        if (n > MAXN || m > MAXM) { printf("-1\n"); fflush(stdout); continue; }
        for (int v = 0; v < n; v++) { adeg[v] = 0; inc[v] = 0; forb[v] = 0; }
        for (int e = 0; e < m; e++) {
            int a = RD(), c = RD(); eu[e] = a; ev[e] = c;
            adjv[a][adeg[a]] = c; adje[a][adeg[a]++] = e;
            adjv[c][adeg[c]] = a; adje[c][adeg[c]++] = e;
            inc[a] |= 1ULL << e; inc[c] |= 1ULL << e;
        }
        for (int v = 0; v < n; v++) b[v] = RD();
        for (int v = 0; v < n; v++) X[v] = RD() & ~(1 << v);
        k = RD();
        for (int i = 0; i < k; i++) { int s = RD(), t = RD(); forb[s] |= 1 << t; forb[t] |= 1 << s; }
        stamp++; hcnt = 0; if (stamp == 0) { memset(ht, 0, HS * sizeof(hent)); stamp = 1; }
        np = 0; nodes = 0; aborted = 0;
        uint64_t R = (m == 64) ? ~0ULL : ((1ULL << m) - 1);
        int r = ok_state(R, 0) ? solve(R, 0) : 0;
        if (r) {
            printf("1 |");
            for (int i = 0; i < np; i++) { for (int j = 0; j < plen[i]; j++) printf(" %d", pv[i][j]); printf(" |"); }
            printf("\n");
        } else printf(aborted ? "2\n" : "0\n");
        fflush(stdout);
    }
    return 0;
}
