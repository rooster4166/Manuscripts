/* lnsolve.c -- exact search for constrained parity path decompositions (ln session).

   A parity decomposition of a graph K is a decomposition of E(K) into paths with
   b(v) = r(v) ends at every vertex v, where by default r(v) = d(v) mod 2 (a Lovasz
   decomposition when K has at most one vertex of positive even degree).
   Constraints:
     A t a   : the path ending at t does not contain a        (t must have r(t) = 1)
     S p q   : no path contains both p and q                    (separation)
     R v k   : set r(v) = k  (k in {0,1,2})
     J p q   : p and q are the two ends of one path (r(p) = r(q) = 1)
   Input: one instance per line:  <graph6> [A t a] [S p q] [R v k] ...
   Output per line: "SAT <g6> :: path ; path ; ..." or "UNSAT <g6>" or "UNDEC <g6>".
   Method: depth-first search; at each node a vertex v with an unspent end is chosen
   (tails first, then fewest remaining edges), and every path from v to another vertex with an
   unspent end is tried.  Pruning: a vertex with an unspent end needs a remaining edge; every
   component of remaining edges needs a vertex with an unspent end; edge-count bound; failed
   states (remaining edges, unspent ends) are memoised.  The answer is exact unless the node
   budget (-b) is exhausted, in which case UNDEC is printed.
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 24
#define MAXM 128
typedef struct { uint64_t w[2]; } eset;   /* edge set, up to 128 edges */

static int n, m;
static int eu[MAXM], ev[MAXM];
static int eid[MAXN][MAXN];
static uint32_t adj0[MAXN];
static int deg0[MAXN];
static int req[MAXN];
static uint32_t avoid[MAXN];      /* avoid[t]: vertices the path ending at t must miss */
static uint32_t sepw[MAXN];       /* sepw[p]: vertices that must not share a path with p */
static int istail[MAXN];
static int mate[MAXN];           /* J p q: p and q are the two ends of one path (-1: none) */

static uint32_t radj[MAXN];       /* remaining adjacency */
static int rdeg[MAXN];
static int rem[MAXN];
static int remtot;
static long long nodes, budget;
static int aborted;

/* witness stack */
static int pathbuf[MAXN * MAXN * 4];
static int pathlen[MAXN * MAXN];
static int npaths, pbtop;

/* failure memo */
#define HBITS 22
#define HSIZE (1u << HBITS)
typedef struct { uint64_t a, b, c; } hkey;
static hkey *htab;
static unsigned char *hused;
static long long hcount;

static void edges_of(eset *E) {
    E->w[0] = E->w[1] = 0;
    for (int u = 0; u < n; u++) {
        uint32_t x = radj[u];
        while (x) { int v = __builtin_ctz(x); x &= x - 1; if (u < v) { int e = eid[u][v]; E->w[e >> 6] |= 1ULL << (e & 63); } }
    }
}
static uint64_t remcode(void) {
    uint64_t c = 0;
    for (int v = 0; v < n; v++) c = c * 3 + rem[v];
    return c;
}
static uint64_t mix(uint64_t x) { x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33; return x; }
static int memo_has(hkey k) {
    uint64_t h = mix(k.a ^ mix(k.b ^ mix(k.c))) & (HSIZE - 1);
    for (int i = 0; i < 64; i++) {
        uint64_t j = (h + i) & (HSIZE - 1);
        if (!hused[j]) return 0;
        if (htab[j].a == k.a && htab[j].b == k.b && htab[j].c == k.c) return 1;
    }
    return 0;
}
static void memo_add(hkey k) {
    if (hcount > (long long)(HSIZE * 0.7)) return;
    uint64_t h = mix(k.a ^ mix(k.b ^ mix(k.c))) & (HSIZE - 1);
    for (int i = 0; i < 64; i++) {
        uint64_t j = (h + i) & (HSIZE - 1);
        if (!hused[j]) { hused[j] = 1; htab[j] = k; hcount++; return; }
    }
}
static void memo_clear(void) { memset(hused, 0, HSIZE); hcount = 0; }

static int feasible(void) {
    /* vertex with unspent end needs an edge; components need ends; edge bound */
    int E = 0, act = 0;
    for (int v = 0; v < n; v++) {
        if (rem[v] > rdeg[v]) return 0;
        E += rdeg[v];
        if (rdeg[v]) act++;
    }
    E /= 2;
    if (E == 0) return remtot == 0;
    if (remtot == 0) return 0;
    if ((long long)E > (long long)(remtot / 2) * (act - 1)) return 0;
    uint32_t seen = 0;
    for (int v = 0; v < n; v++) {
        if (!rdeg[v] || (seen >> v & 1)) continue;
        uint32_t comp = 1u << v, fr = 1u << v;
        while (fr) { int x = __builtin_ctz(fr); fr &= fr - 1; uint32_t nb = radj[x] & ~comp; comp |= nb; fr |= nb; }
        seen |= comp;
        int ends = 0, ce = 0, cv = 0;
        uint32_t c2 = comp;
        while (c2) { int x = __builtin_ctz(c2); c2 &= c2 - 1; ends += rem[x]; ce += rdeg[x]; cv++; }
        ce /= 2;
        if (ends < 2) return 0;
        if ((long long)ce > (long long)(ends / 2) * (cv - 1)) return 0;
    }
    /* each unspent tail must reach another unspent vertex avoiding its avoid set */
    for (int t = 0; t < n; t++) {
        if (!rem[t] || !avoid[t]) continue;
        uint32_t ok = ~avoid[t];
        uint32_t comp = 1u << t, fr = 1u << t; int found = 0;
        while (fr && !found) {
            int x = __builtin_ctz(fr); fr &= fr - 1;
            uint32_t nb = radj[x] & ok & ~comp;
            uint32_t y = nb;
            while (y) { int z = __builtin_ctz(y); y &= y - 1; if (rem[z]) { found = 1; break; } }
            comp |= nb; fr |= nb;
        }
        if (!found) return 0;
    }
    return 1;
}

static int search(void);

/* path extension: current path vertices in stack cur[0..len-1], vset mask */
static int extend(int *cur, int len, uint32_t vset, int start) {
    int x = cur[len - 1];
    uint32_t cand = radj[x] & ~vset;
    while (cand) {
        int y = __builtin_ctz(cand); cand &= cand - 1;
        uint32_t nv = vset | (1u << y);
        /* constraint pruning: if start is a tail, path must avoid avoid[start] */
        if (avoid[start] >> y & 1) continue;
        /* separation pruning */
        int bad = 0;
        for (int i = 0; i < len && !bad; i++) if (sepw[cur[i]] >> y & 1) bad = 1;
        if (bad) continue;
        radj[x] &= ~(1u << y); radj[y] &= ~(1u << x); rdeg[x]--; rdeg[y]--;
        cur[len] = y;
        if (rem[y] && !(avoid[y] & nv) && (mate[start] < 0 || mate[start] == y) && (mate[y] < 0 || mate[y] == start)) {
            /* end here */
            rem[start]--; rem[y]--; remtot -= 2;
            for (int i = 0; i <= len; i++) pathbuf[pbtop + i] = cur[i];
            pathlen[npaths++] = len + 1; pbtop += len + 1;
            int r = feasible() ? search() : 0;
            if (r) return 1;
            npaths--; pbtop -= len + 1;
            rem[start]++; rem[y]++; remtot += 2;
            if (aborted) { radj[x] |= 1u << y; radj[y] |= 1u << x; rdeg[x]++; rdeg[y]++; return 0; }
        }
        /* continue through y */
        if (rdeg[y] > 0) {
            if (extend(cur, len + 1, nv, start)) return 1;
            if (aborted) { radj[x] |= 1u << y; radj[y] |= 1u << x; rdeg[x]++; rdeg[y]++; return 0; }
        }
        radj[x] |= 1u << y; radj[y] |= 1u << x; rdeg[x]++; rdeg[y]++;
    }
    return 0;
}

static int search(void) {
    if (++nodes > budget) { aborted = 1; return 0; }
    if (remtot == 0) {
        for (int v = 0; v < n; v++) if (rdeg[v]) return 0;
        return 1;
    }
    hkey k; eset E; edges_of(&E); k.a = E.w[0]; k.b = E.w[1]; k.c = remcode();
    if (memo_has(k)) return 0;
    /* choose start: an unspent tail with an avoid set first, then fewest remaining edges */
    int best = -1, bs = 1 << 30;
    for (int v = 0; v < n; v++) {
        if (!rem[v]) continue;
        int s = rdeg[v] + ((avoid[v] || sepw[v]) ? -1000 : 0);
        if (s < bs) { bs = s; best = v; }
    }
    int v = best;
    int cur[MAXN + 1];
    cur[0] = v;
    int r = extend(cur, 1, 1u << v, v);
    if (!r && !aborted) memo_add(k);
    return r;
}

static int read_g6(const char *s) {
    const unsigned char *p = (const unsigned char *)s;
    n = p[0] - 63;
    if (n < 1 || n > MAXN) return 0;
    p++;
    int bit = 0, curb = 0, k = 0;
    m = 0;
    for (int v = 0; v < n; v++) { adj0[v] = 0; deg0[v] = 0; }
    for (int j = 1; j < n; j++)
        for (int i = 0; i < j; i++) {
            if (bit == 0) { curb = p[k++] - 63; bit = 6; }
            bit--;
            if (curb >> bit & 1) {
                if (m >= MAXM) return 0;
                eu[m] = i; ev[m] = j; eid[i][j] = eid[j][i] = m;
                adj0[i] |= 1u << j; adj0[j] |= 1u << i; deg0[i]++; deg0[j]++;
                m++;
            }
        }
    return 1;
}

int main(int argc, char **argv) {
    budget = 50000000LL;
    for (int i = 1; i < argc; i++) if (!strcmp(argv[i], "-b") && i + 1 < argc) budget = atoll(argv[++i]);
    htab = malloc(sizeof(hkey) * HSIZE); hused = malloc(HSIZE);
    static char line[1 << 16];
    setvbuf(stdout, NULL, _IOLBF, 0);
    while (fgets(line, sizeof line, stdin)) {
        char *tok = strtok(line, " \t\n");
        if (!tok) continue;
        char g6[256]; strncpy(g6, tok, 255); g6[255] = 0;
        if (!read_g6(g6)) { printf("BAD %s\n", g6); continue; }
        for (int v = 0; v < n; v++) { req[v] = deg0[v] & 1; avoid[v] = 0; sepw[v] = 0; istail[v] = 0; mate[v] = -1; }
        int bad = 0;
        while ((tok = strtok(NULL, " \t\n"))) {
            if (!strcmp(tok, "A")) { int t = atoi(strtok(NULL, " \t\n")); int a = atoi(strtok(NULL, " \t\n")); avoid[t] |= 1u << a; istail[t] = 1; }
            else if (!strcmp(tok, "S")) { int p = atoi(strtok(NULL, " \t\n")); int q = atoi(strtok(NULL, " \t\n")); sepw[p] |= 1u << q; sepw[q] |= 1u << p; }
            else if (!strcmp(tok, "J")) { int p = atoi(strtok(NULL, " \t\n")); int q = atoi(strtok(NULL, " \t\n")); mate[p] = q; mate[q] = p; }
            else if (!strcmp(tok, "R")) { int v = atoi(strtok(NULL, " \t\n")); int k = atoi(strtok(NULL, " \t\n")); req[v] = k; }
            else bad = 1;
        }
        if (bad) { printf("BAD %s\n", g6); continue; }
        for (int v = 0; v < n; v++) if (avoid[v] && req[v] != 1) bad = 1;
        if (bad) { printf("BADTAIL %s\n", g6); continue; }
        remtot = 0;
        for (int v = 0; v < n; v++) { radj[v] = adj0[v]; rdeg[v] = deg0[v]; rem[v] = req[v]; remtot += req[v]; }
        nodes = 0; aborted = 0; npaths = 0; pbtop = 0;
        memo_clear();
        int ok = 0;
        if ((remtot & 1) == 0) {
            int par = 1;
            for (int v = 0; v < n; v++) if (((deg0[v] - req[v]) & 1)) par = 0;
            if (par && feasible()) ok = search();
        }
        if (ok) {
            printf("SAT %s ::", g6);
            int o = 0;
            for (int i = 0; i < npaths; i++) {
                printf(" ");
                for (int j = 0; j < pathlen[i]; j++) printf(j ? "-%d" : "%d", pathbuf[o + j]);
                o += pathlen[i];
                if (i + 1 < npaths) printf(" ;");
            }
            printf("\n");
        } else if (aborted) printf("UNDEC %s\n", g6);
        else printf("UNSAT %s\n", g6);
    }
    return 0;
}
