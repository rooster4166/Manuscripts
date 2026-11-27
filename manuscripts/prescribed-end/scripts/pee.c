/* pee.c: exact oracle for prescribed end edges in Lovász decompositions.

   A Lovász decomposition of a graph G with at most one vertex of positive even degree is a
   path decomposition in which every vertex v is the end of exactly (deg v mod 2) paths.  For
   an edge xy with deg x odd, xy is *terminal at x* in D if the path of D ending at x has xy as
   its last edge.  Conjecture PEE: every such edge is terminal at x in some Lovász decomposition.

   Search.  The path ending at x is built first: it starts x, y, ... and ends at a vertex t != x
   with b(t) = 1.  The rest is an exact search for a decomposition of the remaining edges with
   prescribed end counts (b in {0,1}), branching on the paths starting at a vertex with b = 1 of
   least remaining degree, with memoised failures keyed by (remaining edges, remaining b) and
   necessary conditions: every non-trivial component carries an end; deg(v) <= 2P - b(v) and
   |E| <= P (#active - 1), where P is the number of paths still to be chosen (parity is automatic).
   Further modes: z (EE only), edq (generic PEE / avoidance / separation queries), l1p, l1s2, sepee.

   Modes (argv[1]):
     g6   [flags]   read graph6 lines on stdin (e.g. from nauty-geng); test every graph with at
                    most one vertex of positive even degree, every ordered edge (x, y) with
                    deg x odd and deg x >= 3 (deg x = 1 is trivial).  Prints failures and a
                    summary.  flag "w": also print, for every graph, the per-edge verdicts.
     ed             read lines "n m u1 v1 ... um vm x y" and print 1/0 (or 2 if the node budget
                    in argv[2] was exceeded) for the single query (x, y).
   The graph has at most 32 vertices and 128 edges.
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 32
#define MAXM 128
typedef unsigned __int128 u128;

static int n, m;
static int eu[MAXM], ev[MAXM];
static int eid[MAXN][MAXN];
static u128 inc[MAXN];
static int dg0[MAXN];

/* ---------- failure memo ---------- */
typedef struct { u128 mask; uint32_t b; } key_t2;
static key_t2 *tab; static unsigned char *used; static size_t cap, cnt;
static void hreset(void) {
  if (!tab) { cap = 1u << 16; tab = malloc(cap * sizeof(key_t2)); used = calloc(cap, 1); }
  else if (cnt) memset(used, 0, cap);
  cnt = 0;
}
static size_t hh(u128 a, uint32_t b) {
  uint64_t lo = (uint64_t)a, hi = (uint64_t)(a >> 64);
  uint64_t x = lo * 0x9E3779B97F4A7C15ULL ^ (hi * 0xC2B2AE3D27D4EB4FULL) ^ ((uint64_t)b * 0x632BE59BD9B4E019ULL);
  x ^= x >> 31; x *= 0xBF58476D1CE4E5B9ULL; x ^= x >> 29;
  return (size_t)x;
}
static int hfind(u128 a, uint32_t b) {
  size_t i = hh(a, b) & (cap - 1);
  while (used[i]) { if (tab[i].mask == a && tab[i].b == b) return 1; i = (i + 1) & (cap - 1); }
  return 0;
}
static void hadd(u128 a, uint32_t b);
static void hgrow(void) {
  size_t oc = cap; key_t2 *ot = tab; unsigned char *ou = used;
  cap *= 2; tab = malloc(cap * sizeof(key_t2)); used = calloc(cap, 1); cnt = 0;
  for (size_t i = 0; i < oc; i++) if (ou[i]) hadd(ot[i].mask, ot[i].b);
  free(ot); free(ou);
}
static void hadd(u128 a, uint32_t b) {
  if (cnt * 2 > cap) hgrow();
  size_t i = hh(a, b) & (cap - 1);
  while (used[i]) i = (i + 1) & (cap - 1);
  used[i] = 1; tab[i].mask = a; tab[i].b = b; cnt++;
}

/* ---------- search ---------- */
static u128 rem;          /* remaining edges */
static uint32_t bm;       /* vertices that still need an end */
static unsigned long long budget, nodes;
static int aborted;
static uint32_t sepmask;  /* if nonzero (two bits): no path may contain both vertices */
static uint32_t sepmask2; /* a second forbidden pair */

static int popc(u128 x) { return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64)); }
static int ctz128(u128 x) { uint64_t lo = (uint64_t)x; return lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll((uint64_t)(x >> 64)); }
static int deg(int v) { return popc(rem & inc[v]); }

static int solve(void);

/* grow a path from a (current end c, visited vis); it may stop at any w in bm, w != a */
static int extend(int a, int c, uint32_t vis) {
  if (aborted) return 0;
  if (budget && ++nodes > budget) { aborted = 1; return 0; }
  u128 ex = rem & inc[c];
  while (ex) {
    int e = ctz128(ex); ex &= ex - 1;
    int w = eu[e] == c ? ev[e] : eu[e];
    if (vis >> w & 1) continue;
    if (sepmask && ((vis | (1u << w)) & sepmask) == sepmask) continue;
    if (sepmask2 && ((vis | (1u << w)) & sepmask2) == sepmask2) continue;
    rem &= ~((u128)1 << e);
    if (bm >> w & 1) {
      uint32_t sb = bm;
      bm &= ~((1u << a) | (1u << w));
      int ok = solve();
      bm = sb;
      if (ok) { rem |= (u128)1 << e; return 1; }
    }
    if (rem & inc[w]) {
      if (extend(a, w, vis | (1u << w))) { rem |= (u128)1 << e; return 1; }
    }
    rem |= (u128)1 << e;
  }
  return 0;
}

static int prune_ok(int *bestp) {
  int best = -1, bd = 999;
  int P = __builtin_popcount(bm) / 2, act = 0;   /* P = number of paths still to be chosen */
  for (int v = 0; v < n; v++) {
    int d = deg(v);
    if (d) act++;
    int bv = bm >> v & 1;
    if (d > 2 * P - bv) return 0;                 /* each path uses at most two edges at v */
    if (bv && d < bd) { bd = d; best = v; }
  }
  if (popc(rem) > P * (act - 1)) return 0;         /* a path has at most act - 1 edges */
  uint32_t seen = 0;
  for (int v = 0; v < n; v++) {
    if ((seen >> v & 1) || !(rem & inc[v])) continue;
    uint32_t comp = 1u << v, frontier = 1u << v;
    while (frontier) {
      int x = __builtin_ctz(frontier); frontier &= frontier - 1;
      u128 ex = rem & inc[x];
      while (ex) {
        int e = ctz128(ex); ex &= ex - 1;
        int y = eu[e] == x ? ev[e] : eu[e];
        if (!(comp >> y & 1)) { comp |= 1u << y; frontier |= 1u << y; }
      }
    }
    seen |= comp;
    if (!(comp & bm)) return 0;   /* an Eulerian component cannot be decomposed with no ends */
  }
  if (bestp) *bestp = best;
  return 1;
}

static int solve(void) {
  if (rem == 0) return bm == 0;
  if (bm == 0) return 0;
  int best;
  if (!prune_ok(&best)) return 0;
  if (hfind(rem, bm)) return 0;
  int r = extend(best, best, 1u << best);
  if (!r && !aborted) hadd(rem, bm);
  return r;
}

/* the path ending at x starts with the edge xy */
static int pee_query(int x, int y) {
  int e = eid[x][y];
  if (e < 0) return -1;
  hreset(); nodes = 0; aborted = 0;
  rem = (m == 128) ? ~(u128)0 : (((u128)1 << m) - 1);
  bm = 0;
  for (int v = 0; v < n; v++) if (dg0[v] & 1) bm |= 1u << v;
  if (!(bm >> x & 1)) return -1;
  rem &= ~((u128)1 << e);
  int ok = 0;
  if (bm >> y & 1) {   /* the path may be the single edge xy */
    uint32_t sb = bm; bm &= ~((1u << x) | (1u << y));
    ok = solve(); bm = sb;
  }
  if (!ok && (rem & inc[y])) ok = extend(x, y, (1u << x) | (1u << y));
  rem |= (u128)1 << e;
  if (aborted) return 2;
  return ok;
}

/* Lovász decomposition of the current graph with no path containing both s and t */
static int sep_query(int s1, int t1) {
  hreset(); nodes = 0; aborted = 0;
  rem = (m == 128) ? ~(u128)0 : (((u128)1 << m) - 1);
  bm = 0;
  for (int v = 0; v < n; v++) if (dg0[v] & 1) bm |= 1u << v;
  sepmask = (1u << s1) | (1u << t1);
  int ok = solve();
  sepmask = 0;
  if (aborted) return 2;
  return ok;
}

/* Lovász decomposition whose path ending at c avoids every vertex of mask f */
static int avoid_query(int c, uint32_t f) {
  hreset(); nodes = 0; aborted = 0;
  rem = (m == 128) ? ~(u128)0 : (((u128)1 << m) - 1);
  bm = 0;
  for (int v = 0; v < n; v++) if (dg0[v] & 1) bm |= 1u << v;
  if (!(bm >> c & 1)) return -1;
  int best;
  if (!prune_ok(&best)) return 0;
  int ok = extend(c, c, (1u << c) | f);
  if (aborted) return 2;
  return ok;
}

/* ---------- input ---------- */
static void setup_edges(void) {
  for (int i = 0; i < n; i++) { inc[i] = 0; dg0[i] = 0; for (int j = 0; j < n; j++) eid[i][j] = -1; }
  for (int e = 0; e < m; e++) {
    int u = eu[e], v = ev[e];
    eid[u][v] = eid[v][u] = e;
    inc[u] |= (u128)1 << e; inc[v] |= (u128)1 << e;
    dg0[u]++; dg0[v]++;
  }
}

static int parse_g6(const char *s) {
  int len = (int)strlen(s);
  while (len && (s[len - 1] == '\n' || s[len - 1] == '\r')) len--;
  if (len == 0) return 0;
  int p = 0;
  n = s[p++] - 63;
  if (n > MAXN || n < 0) return 0;
  int bit = 0, k = 0; m = 0;
  int val = 0;
  for (int j = 1; j < n; j++)
    for (int i = 0; i < j; i++) {
      if (bit == 0) { if (p >= len) return 0; val = s[p++] - 63; bit = 6; }
      bit--;
      if (val >> bit & 1) {
        if (m >= MAXM) return 0;
        eu[m] = i; ev[m] = j; m++;
      }
      k++;
    }
  setup_edges();
  return 1;
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: pee g6 [w] | pee ed [budget]\n"); return 1; }
  if (!strcmp(argv[1], "ed")) {
    budget = argc > 2 ? strtoull(argv[2], 0, 10) : 0;
    while (scanf("%d %d", &n, &m) == 2) {
      for (int e = 0; e < m; e++) if (scanf("%d %d", &eu[e], &ev[e]) != 2) return 1;
      int x, y; if (scanf("%d %d", &x, &y) != 2) return 1;
      setup_edges();
      printf("%d\n", pee_query(x, y)); fflush(stdout);
    }
    return 0;
  }
  if (!strcmp(argv[1], "edq")) {
    /* lines: n m u1 v1 ... um vm T a b ; T=0: PEE(x=a,y=b); T=1: path ending at a avoids mask b;
       T=2: separation of a and b.  argv[2] = node budget (0 = none).  prints 1/0/2 */
    budget = argc > 2 ? strtoull(argv[2], 0, 10) : 0;
    while (scanf("%d %d", &n, &m) == 2) {
      for (int e = 0; e < m; e++) if (scanf("%d %d", &eu[e], &ev[e]) != 2) return 1;
      int T; unsigned long long a, b; if (scanf("%d %llu %llu", &T, &a, &b) != 3) return 1;
      setup_edges();
      int r;
      if (T == 3) { /* separate vertex a from both vertices of mask b (two bits) */
        int b1 = __builtin_ctzll(b), b2 = 63 - __builtin_clzll(b);
        sepmask2 = (1u << a) | (1u << b2);
        r = sep_query((int)a, b1);
        sepmask2 = 0;
      } else
      r = T == 0 ? pee_query((int)a, (int)b) : T == 1 ? avoid_query((int)a, (uint32_t)b) : sep_query((int)a, (int)b);
      printf("%d\n", r); fflush(stdout);
    }
    return 0;
  }
  if (!strcmp(argv[1], "l1p")) {
    /* L1': one even vertex g; c, a odd, c !~ a, g !~ a: Q_c avoids a.  flag argv[2]="all": drop g !~ a */
    int all = argc > 2 && !strcmp(argv[2], "all");
    char line[512]; long long tot = 0, fail = 0, fga = 0, tga = 0;
    while (fgets(line, sizeof line, stdin)) {
      if (!parse_g6(line)) continue;
      int g = -1, ne = 0;
      for (int v = 0; v < n; v++) if (dg0[v] > 0 && !(dg0[v] & 1)) { g = v; ne++; }
      if (ne != 1) continue;
      for (int c = 0; c < n; c++) {
        if (!(dg0[c] & 1)) continue;
        for (int a = 0; a < n; a++) {
          if (a == c || !(dg0[a] & 1) || eid[c][a] >= 0) continue;
          int ga = eid[g][a] >= 0;
          if (ga && !all) continue;
          int r = avoid_query(c, 1u << a);
          tot++; if (ga) tga++;
          if (r == 0) { fail++; if (ga) fga++; if (!ga) { char *nl = strchr(line, '\n'); if (nl) *nl = 0; printf("L1PFAIL %s g=%d c=%d a=%d\n", line, g, c, a); } }
        }
      }
    }
    printf("SUMMARY l1p tests=%lld fail=%lld (of which g~a: tests=%lld fail=%lld)\n", tot, fail, tga, fga);
    return 0;
  }
  if (!strcmp(argv[1], "l1s2")) {
    /* L1S: <=1 even vertex g; c odd; A={a1,a2}, a_i not in N[c] u N(g): Q_c avoids A.
       Also the triangle-lemma condition: one even z, u in N(z), w in N(u)&N(z): K-{uz,uw,zw}, Q_w avoids {u,z} */
    char line[512]; long long tot = 0, fail = 0, ttot = 0, tfail = 0, eeres = 0, eeres_ok = 0;
    while (fgets(line, sizeof line, stdin)) {
      if (!parse_g6(line)) continue;
      int g = -1, ne = 0;
      for (int v = 0; v < n; v++) if (dg0[v] > 0 && !(dg0[v] & 1)) { g = v; ne++; }
      if (ne > 1) continue;
      for (int c = 0; c < n; c++) {
        if (!(dg0[c] & 1)) continue;
        uint32_t bad = 1u << c;
        for (int v = 0; v < n; v++) if (eid[c][v] >= 0 || (g >= 0 && eid[g][v] >= 0)) bad |= 1u << v;
        for (int a1 = 0; a1 < n; a1++) for (int a2 = a1 + 1; a2 < n; a2++) {
          if ((bad >> a1 & 1) || (bad >> a2 & 1) || !dg0[a1] || !dg0[a2]) continue;
          int r = avoid_query(c, (1u << a1) | (1u << a2));
          tot++;
          if (r == 0) { fail++; if (fail <= 20) { char *nl = strchr(line, '\n'); if (nl) *nl = 0; printf("L1S2FAIL %s g=%d c=%d a=%d,%d\n", line, g, c, a1, a2); } }
        }
      }
      if (ne != 1) continue;
      int z = g, M0 = m; int EU[MAXM], EV[MAXM]; memcpy(EU, eu, sizeof(int) * m); memcpy(EV, ev, sizeof(int) * m);
      for (int u = 0; u < n; u++) {
        if (eid[z][u] < 0) continue;
        int any = 0, okany = 0;
        for (int w = 0; w < n; w++) {
          if (eid[z][w] < 0 || eid[u][w] < 0) continue;
          int e1 = eid[z][u], e2 = eid[u][w], e3 = eid[z][w];
          int k = 0;
          for (int e = 0; e < M0; e++) if (e != e1 && e != e2 && e != e3) { eu[k] = EU[e]; ev[k] = EV[e]; k++; }
          m = k; setup_edges();
          int r = avoid_query(w, (1u << u) | (1u << z));
          ttot++; any = 1; if (r == 1) okany = 1; else tfail++;
          m = M0; memcpy(eu, EU, sizeof(int) * m); memcpy(ev, EV, sizeof(int) * m); setup_edges();
        }
        if (any) { eeres++; if (okany) eeres_ok++; else { char *nl = strchr(line, '\n'); if (nl) *nl = 0; printf("TRINOWORK %s z=%d u=%d\n", line, z, u); } }
      }
    }
    printf("SUMMARY l1s2 tests=%lld fail=%lld | triangle-lemma (z,u,w) tests=%lld fail=%lld ; (z,u) with a triangle: %lld, some w works: %lld\n", tot, fail, ttot, tfail, eeres, eeres_ok);
    return 0;
  }
  if (!strcmp(argv[1], "sepee")) {
    char line[512]; long long tot = 0, fail = 0; long long byT[8][2] = {{0}};
    while (fgets(line, sizeof line, stdin)) {
      if (!parse_g6(line)) continue;
      int z = -1, ne = 0;
      for (int v = 0; v < n; v++) if (dg0[v] > 0 && !(dg0[v] & 1)) { z = v; ne++; }
      if (ne != 1) continue;
      int M0 = m; int EU[MAXM], EV[MAXM]; memcpy(EU, eu, sizeof(int) * m); memcpy(EV, ev, sizeof(int) * m);
      for (int u = 0; u < n; u++) {
        if (eid[z][u] < 0) continue;
        int T = 0; for (int w = 0; w < n; w++) if (eid[z][w] >= 0 && eid[u][w] >= 0) T++;
        /* build K - uz */
        int k = 0; int ez = eid[z][u];
        for (int e = 0; e < M0; e++) if (e != ez) { eu[k] = EU[e]; ev[k] = EV[e]; k++; }
        m = k; setup_edges();
        int r = sep_query(u, z);
        tot++; byT[T < 7 ? T : 7][0]++;
        if (r == 0) { fail++; byT[T < 7 ? T : 7][1]++; char *nl = strchr(line, '\n'); if (nl) *nl = 0; printf("SEPFAIL %s z=%d u=%d T=%d\n", line, z, u, T); }
        m = M0; memcpy(eu, EU, sizeof(int) * m); memcpy(ev, EV, sizeof(int) * m); setup_edges();
      }
    }
    printf("SUMMARY sepee tests=%lld fail=%lld\n", tot, fail);
    for (int t = 0; t < 8; t++) if (byT[t][0]) printf("  |T|=%d tests=%lld fail=%lld\n", t, byT[t][0], byT[t][1]);
    return 0;
  }
  int verbose = argc > 2 && strchr(argv[2], 'w');
  int zonly = argc > 2 && strchr(argv[2], 'z');   /* only edges at the even vertex (EE) */
  char line[512];
  long long graphs = 0, tests_z = 0, tests_away = 0, fail_z = 0, fail_away = 0;
  long long graphs_fail = 0, zcount_fail_all = 0, graphs_with_z = 0;
  while (fgets(line, sizeof line, stdin)) {
    if (!parse_g6(line)) continue;
    int z = -1, ne = 0;
    for (int v = 0; v < n; v++) if (dg0[v] > 0 && !(dg0[v] & 1)) { z = v; ne++; }
    if (ne > 1) continue;
    graphs++;
    if (z >= 0) graphs_with_z++;
    int gfail = 0, zfails = 0, zdeg = 0;
    char buf[4096]; int bl = 0; buf[0] = 0;
    for (int x = 0; x < n; x++) {
      if (!(dg0[x] & 1) || dg0[x] < 3) continue;
      for (int y = 0; y < n; y++) {
        if (eid[x][y] < 0) continue;
        if (zonly && y != z) continue;
        int r = pee_query(x, y);
        int atz = (y == z);
        if (atz) { tests_z++; zdeg++; } else tests_away++;
        if (verbose && bl < 4000) bl += snprintf(buf + bl, sizeof buf - bl, " %d%c%d:%d", x, atz ? '*' : '-', y, r);
        if (r == 0) {
          gfail = 1;
          if (atz) { fail_z++; zfails++; } else fail_away++;
          char *nl = strchr(line, '\n'); if (nl) *nl = 0;
          printf("FAIL %s x=%d y=%d z=%d %s\n", line, x, y, z, atz ? "at-z" : "away");
          fflush(stdout);
        }
      }
    }
    if (z >= 0 && zdeg > 0 && zfails == zdeg) zcount_fail_all++;
    if (gfail) graphs_fail++;
    if (verbose) { char *nl = strchr(line, '\n'); if (nl) *nl = 0; printf("G %s z=%d%s\n", line, z, buf); }
    if (graphs % 200000 == 0) { printf("PARTIAL graphs=%lld tests_at_z=%lld fail_at_z=%lld tests_away=%lld fail_away=%lld\n", graphs, tests_z, fail_z, tests_away, fail_away); fflush(stdout); }
  }
  printf("SUMMARY graphs=%lld with_even=%lld tests_at_z=%lld fail_at_z=%lld tests_away=%lld fail_away=%lld graphs_failing=%lld graphs_all_z_edges_fail=%lld\n",
         graphs, graphs_with_z, tests_z, fail_z, tests_away, fail_away, graphs_fail, zcount_fail_all);
  return 0;
}
