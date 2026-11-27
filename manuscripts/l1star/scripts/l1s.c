/* l1s.c: exact oracle for one-sided avoidance in Lovász decompositions (Conjecture L1*).

   A Lovász decomposition of a graph G with at most one vertex g of positive even degree is a path
   decomposition in which every vertex v ends exactly (deg v mod 2) paths.  For an odd vertex c,
   Q_c is the path ending at c.  Conjecture L1*: if |A| <= 2 and A misses N[c] and N(g), some Lovász
   decomposition has Q_c disjoint from A.

   The search core is the oracle of manuscripts/prescribed-end/scripts/pee.c (validated there
   against brute force and tools/route_ext.c): Q_c is grown first from c, never entering the
   forbidden set; the rest is an exact search with prescribed end counts and a failure memo.

   Modes (argv[1]):
     max K [flags]  read graph6 on stdin.  For each graph with <= 1 vertex of positive even degree and
                    each odd c: let Amax = vertices of positive degree outside N[c] and N(g) (g itself
                    allowed).  Test Amax.  If it fails, list the inclusion-minimal failing subsets of
                    Amax of size <= K.  Prints MINFAIL lines and a summary.
                    flags: "n" = also test A inside N(g) (drop the N(g) condition: diagnostic),
                           "q" = quiet (no MINFAIL lines).
     ed [budget]    lines "n m u1 v1 ... um vm c mask"; prints 1 (avoidable), 0 (not), 2 (budget hit),
                    -1 (c not odd).
     sep [budget]   lines "n m u1 v1 ... um vm c mask"; prints 1 if some Lovász decomposition has
                    Q_c disjoint from mask AND no path containing c and a vertex of mask... (unused)
   At most 32 vertices and 128 edges.
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
static uint32_t nbr[MAXN];

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

static int popc(u128 x) { return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64)); }
static int ctz128(u128 x) { uint64_t lo = (uint64_t)x; return lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll((uint64_t)(x >> 64)); }
static int deg(int v) { return popc(rem & inc[v]); }

static int solve(void);

/* grow a path from a (current end cur, visited vis); it may stop at any w in bm, w != a */
static int extend(int a, int cur, uint32_t vis) {
  if (aborted) return 0;
  if (budget && ++nodes > budget) { aborted = 1; return 0; }
  u128 ex = rem & inc[cur];
  while (ex) {
    int e = ctz128(ex); ex &= ex - 1;
    int w = eu[e] == cur ? ev[e] : eu[e];
    if (vis >> w & 1) continue;
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
  int P = __builtin_popcount(bm) / 2, act = 0;
  for (int v = 0; v < n; v++) {
    int d = deg(v);
    if (d) act++;
    int bv = bm >> v & 1;
    if (d > 2 * P - bv) return 0;
    if (bv && d < bd) { bd = d; best = v; }
  }
  if (popc(rem) > P * (act - 1)) return 0;
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
    if (!(comp & bm)) return 0;
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

/* Lovász decomposition whose path ending at c avoids every vertex of mask f */
static int avoid_query(int c, uint32_t f) {
  hreset(); nodes = 0; aborted = 0;
  rem = (m == 128) ? ~(u128)0 : (((u128)1 << m) - 1);
  bm = 0;
  for (int v = 0; v < n; v++) if (dg0[v] & 1) bm |= 1u << v;
  if (!(bm >> c & 1)) return -1;
  if (!prune_ok(NULL)) return 0;
  int ok = extend(c, c, (1u << c) | f);
  if (aborted) return 2;
  return ok;
}


/* Q_c search with limits: path from c (current end cur, visited vis, length len, outside-count oc);
   at most qmaxlen edges, at most qmaxout vertices outside region qreg; never enters forbidden mask */
static int qmaxlen = 1000, qmaxout = 1000; static uint32_t qreg = 0xffffffffu;
static int extendQ(int a, int cur, uint32_t vis, int len, int oc) {
  if (aborted) return 0;
  if (budget && ++nodes > budget) { aborted = 1; return 0; }
  if (len >= qmaxlen) return 0;
  u128 ex = rem & inc[cur];
  while (ex) {
    int e = ctz128(ex); ex &= ex - 1;
    int w = eu[e] == cur ? ev[e] : eu[e];
    if (vis >> w & 1) continue;
    int oc2 = oc + !(qreg >> w & 1);
    if (oc2 > qmaxout) continue;
    rem &= ~((u128)1 << e);
    if (bm >> w & 1) {
      uint32_t sb = bm;
      bm &= ~((1u << a) | (1u << w));
      int ok = solve();
      bm = sb;
      if (ok) { rem |= (u128)1 << e; return 1; }
    }
    if (rem & inc[w]) {
      if (extendQ(a, w, vis | (1u << w), len + 1, oc2)) { rem |= (u128)1 << e; return 1; }
    }
    rem |= (u128)1 << e;
  }
  return 0;
}
static int avoid_query_lim(int c, uint32_t f, int maxlen, uint32_t reg, int maxout) {
  hreset(); nodes = 0; aborted = 0;
  rem = (m == 128) ? ~(u128)0 : (((u128)1 << m) - 1);
  bm = 0;
  for (int v = 0; v < n; v++) if (dg0[v] & 1) bm |= 1u << v;
  if (!(bm >> c & 1)) return -1;
  if (!prune_ok(NULL)) return 0;
  qmaxlen = maxlen; qreg = reg; qmaxout = maxout;
  int ok = extendQ(c, c, (1u << c) | f, 0, 0);
  qmaxlen = 1000; qreg = 0xffffffffu; qmaxout = 1000;
  if (aborted) return 2;
  return ok;
}

/* ---------- input ---------- */
static void setup_edges(void) {
  for (int i = 0; i < n; i++) { inc[i] = 0; dg0[i] = 0; nbr[i] = 0; for (int j = 0; j < n; j++) eid[i][j] = -1; }
  for (int e = 0; e < m; e++) {
    int u = eu[e], v = ev[e];
    eid[u][v] = eid[v][u] = e;
    inc[u] |= (u128)1 << e; inc[v] |= (u128)1 << e;
    nbr[u] |= 1u << v; nbr[v] |= 1u << u;
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
  int bit = 0; m = 0;
  int val = 0;
  for (int j = 1; j < n; j++)
    for (int i = 0; i < j; i++) {
      if (bit == 0) { if (p >= len) return 0; val = s[p++] - 63; bit = 6; }
      bit--;
      if (val >> bit & 1) {
        if (m >= MAXM) return 0;
        eu[m] = i; ev[m] = j; m++;
      }
    }
  setup_edges();
  return 1;
}

/* distance-2 closure: vertices within distance <= 2 of v */
static uint32_t ball2(int v) {
  uint32_t b = (1u << v) | nbr[v], r = b;
  for (int x = 0; x < n; x++) if (b >> x & 1) r |= nbr[x];
  return r;
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: l1s max K [flags] | l1s ed [budget]\n"); return 1; }
  if (!strcmp(argv[1], "ed")) {
    budget = argc > 2 ? strtoull(argv[2], 0, 10) : 0;
    while (scanf("%d %d", &n, &m) == 2) {
      for (int e = 0; e < m; e++) if (scanf("%d %d", &eu[e], &ev[e]) != 2) return 1;
      int c; unsigned long long f; if (scanf("%d %llu", &c, &f) != 2) return 1;
      setup_edges();
      printf("%d\n", avoid_query(c, (uint32_t)f)); fflush(stdout);
    }
    return 0;
  }

  if (!strcmp(argv[1], "stats")) {
    /* per (G, c): minimum length of Q_c (free, and inside N[c] u N(g)); is Q_c inside N[c] possible;
       minimum number of vertices of Q_c outside N[c] (within N[c] u N(g)) */
    budget = 0;
    char line[512]; long long pairs = 0, inNc = 0, hist_free[40] = {0}, hist_loc[40] = {0}, hist_out[40] = {0};
    long long pairsG = 0, inNcG = 0, hist_locG[40] = {0}, hist_outG[40] = {0};
    while (fgets(line, sizeof line, stdin)) {
      if (!parse_g6(line)) continue;
      char *nl = strchr(line, '\n'); if (nl) *nl = 0;
      int g = -1, ne = 0;
      for (int v = 0; v < n; v++) if (dg0[v] > 0 && !(dg0[v] & 1)) { g = v; ne++; }
      if (ne > 1) continue;
      for (int c = 0; c < n; c++) {
        if (!(dg0[c] & 1)) continue;
        uint32_t Nc = (1u << c) | nbr[c];
        uint32_t loc = Nc | (g >= 0 ? nbr[g] : 0);
        uint32_t Amax = 0; for (int v = 0; v < n; v++) if (!(loc >> v & 1)) Amax |= 1u << v;
        int lf = 0; for (lf = 1; lf < n; lf++) if (avoid_query_lim(c, 0, lf, 0xffffffffu, 1000) == 1) break;
        int ll = 0; for (ll = 1; ll < n; ll++) if (avoid_query_lim(c, Amax, ll, 0xffffffffu, 1000) == 1) break;
        int oo = 0; for (oo = 0; oo < n; oo++) if (avoid_query_lim(c, Amax, 1000, Nc, oo) == 1) break;
        pairs++; hist_free[lf]++; hist_loc[ll]++; hist_out[oo]++; if (oo == 0) inNc++;
        if (g >= 0 && !(nbr[g] >> c & 1)) { pairsG++; hist_locG[ll]++; hist_outG[oo]++; if (oo == 0) inNcG++; }
        if (ll >= 4 || oo >= 2) printf("EXTREME %s g=%d c=%d minlen_free=%d minlen_local=%d minout=%d\n", line, g, c, lf, ll, oo);
      }
    }
    printf("SUMMARY stats pairs=%lld Q_c-inside-N[c]-possible=%lld\n", pairs, inNc);
    for (int i = 0; i < 40; i++) if (hist_free[i] || hist_loc[i] || hist_out[i])
      printf("  %d: minlen_free=%lld minlen_local=%lld minout=%lld\n", i, hist_free[i], hist_loc[i], hist_out[i]);
    printf("  [g exists, c not in N(g)] pairs=%lld inside-N[c]=%lld\n", pairsG, inNcG);
    for (int i = 0; i < 40; i++) if (hist_locG[i] || hist_outG[i])
      printf("    %d: minlen_local=%lld minout=%lld\n", i, hist_locG[i], hist_outG[i]);
    return 0;
  }

  if (!strcmp(argv[1], "gen")) {
    /* all A subset of V - N[c] (positive degree), |A| <= K; classify and test */
    int K = argc > 2 ? atoi(argv[2]) : 3;
    budget = 0;
    char line[512];
    long long cnt[2][2][2][2] = {{{{0}}}};  /* [hypL1][sep][gin][fail] */
    while (fgets(line, sizeof line, stdin)) {
      if (!parse_g6(line)) continue;
      char *nl = strchr(line, '\n'); if (nl) *nl = 0;
      int g = -1, ne = 0;
      for (int v = 0; v < n; v++) if (dg0[v] > 0 && !(dg0[v] & 1)) { g = v; ne++; }
      if (ne != 1) continue;
      for (int c = 0; c < n; c++) {
        if (!(dg0[c] & 1)) continue;
        uint32_t bad = (1u << c) | nbr[c];
        int idx[32], k = 0;
        for (int v = 0; v < n; v++) if (dg0[v] > 0 && !(bad >> v & 1)) idx[k++] = v;
        for (uint32_t sub = 1; sub < (1u << k); sub++) {
          if (__builtin_popcount(sub) > K) continue;
          uint32_t A = 0; for (int i = 0; i < k; i++) if (sub >> i & 1) A |= 1u << idx[i];
          int hyp = !(A & nbr[g]);
          int gin = A >> g & 1;
          /* is g reachable from c in G - A? */
          uint32_t comp = 1u << c, fr = 1u << c;
          while (fr) { int x = __builtin_ctz(fr); fr &= fr - 1; uint32_t nx = nbr[x] & ~A & ~comp; comp |= nx; fr |= nx; }
          int sep = !gin && !(comp >> g & 1);
          int r = avoid_query(c, A);
          int fail = (r == 0);
          cnt[hyp][sep][gin][fail]++;
          if (fail && (hyp || sep)) {
            printf("GENFAIL %s g=%d c=%d A=", line, g, c);
            for (int x = 0; x < n; x++) if (A >> x & 1) printf("%d,", x);
            printf(" hyp=%d sep=%d gin=%d\n", hyp, sep, gin);
          }
        }
      }
    }
    for (int h = 0; h < 2; h++) for (int s = 0; s < 2; s++) for (int gi = 0; gi < 2; gi++)
      if (cnt[h][s][gi][0] + cnt[h][s][gi][1])
        printf("  hypL1=%d sep=%d g_in_A=%d : tests=%lld fail=%lld\n", h, s, gi, cnt[h][s][gi][0] + cnt[h][s][gi][1], cnt[h][s][gi][1]);
    return 0;
  }

  if (!strcmp(argv[1], "two")) {
    /* graphs with exactly two vertices x, y of positive even degree: does a decomposition with
       b = deg mod 2 exist?  classified by dist(x, y) (1, 2, >=3) */
    budget = 0;
    char line[512]; long long tot[4] = {0}, ok[4] = {0};
    while (fgets(line, sizeof line, stdin)) {
      if (!parse_g6(line)) continue;
      char *nl = strchr(line, '\n'); if (nl) *nl = 0;
      int ev[32], ne = 0;
      for (int v = 0; v < n; v++) if (dg0[v] > 0 && !(dg0[v] & 1)) ev[ne++] = v;
      if (ne != 2) continue;
      int x = ev[0], y = ev[1];
      int d = (nbr[x] >> y & 1) ? 1 : ((nbr[x] & nbr[y]) ? 2 : 3);
      hreset(); nodes = 0; aborted = 0;
      rem = (m == 128) ? ~(u128)0 : (((u128)1 << m) - 1);
      bm = 0; for (int v = 0; v < n; v++) if (dg0[v] & 1) bm |= 1u << v;
      int r = solve();
      tot[d]++; ok[d] += r;
      if (!r) printf("TWOFAIL %s x=%d y=%d dist=%d dx=%d dy=%d\n", line, x, y, d, dg0[x], dg0[y]);
    }
    for (int d = 1; d <= 3; d++) printf("  dist %s%d: graphs=%lld decomposable=%lld\n", d == 3 ? ">=" : "", d, tot[d], ok[d]);
    return 0;
  }

  if (!strcmp(argv[1], "packedev")) {
    /* graphs whose vertices of positive even degree are pairwise at distance >= 3 (packed):
       does a decomposition with b = deg mod 2 exist?  by number of even vertices */
    budget = 0;
    char line[512]; long long tot[40] = {0}, ok[40] = {0};
    while (fgets(line, sizeof line, stdin)) {
      if (!parse_g6(line)) continue;
      char *nl = strchr(line, '\n'); if (nl) *nl = 0;
      uint32_t E = 0; int ne = 0;
      for (int v = 0; v < n; v++) if (dg0[v] > 0 && !(dg0[v] & 1)) { E |= 1u << v; ne++; }
      if (ne < 2) continue;
      int pk = 1;
      for (int v = 0; v < n && pk; v++) if (E >> v & 1) if (ball2(v) & E & ~(1u << v)) pk = 0;
      if (!pk) continue;
      hreset(); nodes = 0; aborted = 0;
      rem = (m == 128) ? ~(u128)0 : (((u128)1 << m) - 1);
      bm = 0; for (int v = 0; v < n; v++) if (dg0[v] & 1) bm |= 1u << v;
      int r = solve();
      tot[ne]++; ok[ne] += r;
      if (!r) printf("PKFAIL %s evens=%d\n", line, ne);
    }
    for (int d = 2; d < 40; d++) if (tot[d]) printf("  even vertices %d: graphs=%lld decomposable=%lld\n", d, tot[d], ok[d]);
    return 0;
  }

  if (!strcmp(argv[1], "peloc")) {
    /* even vertices packed (>= 2 of them): for each odd c, is Q_c inside N[c] u N(Ev) possible? */
    budget = 0;
    char line[512]; long long tot = 0, ok = 0, gr = 0;
    while (fgets(line, sizeof line, stdin)) {
      if (!parse_g6(line)) continue;
      char *nl = strchr(line, '\n'); if (nl) *nl = 0;
      uint32_t E = 0, NE = 0; int ne = 0;
      for (int v = 0; v < n; v++) if (dg0[v] > 0 && !(dg0[v] & 1)) { E |= 1u << v; NE |= nbr[v]; ne++; }
      if (ne < 2) continue;
      int pk = 1;
      for (int v = 0; v < n && pk; v++) if (E >> v & 1) if (ball2(v) & E & ~(1u << v)) pk = 0;
      if (!pk) continue;
      gr++;
      for (int c = 0; c < n; c++) {
        if (!(dg0[c] & 1)) continue;
        uint32_t reg = (1u << c) | nbr[c] | NE;
        uint32_t A = 0; for (int v = 0; v < n; v++) if (dg0[v] > 0 && !(reg >> v & 1)) A |= 1u << v;
        int r = avoid_query(c, A);
        tot++; ok += (r == 1);
        if (r != 1) printf("PELOCFAIL %s c=%d\n", line, c);
      }
    }
    printf("SUMMARY peloc graphs=%lld pairs=%lld ok=%lld\n", gr, tot, ok);
    return 0;
  }
  if (!strcmp(argv[1], "max")) {
    int K = argc > 2 ? atoi(argv[2]) : 3;
    const char *fl = argc > 3 ? argv[3] : "";
    int dropNg = strchr(fl, 'n') != NULL, quiet = strchr(fl, 'q') != NULL;
    budget = 0;
    char line[512];
    long long graphs = 0, pairs = 0, maxok = 0, bysize[40] = {0}, minsets[40] = {0};
    long long feat_g[40] = {0}, feat_packed[40] = {0}, feat_indep[40] = {0};
    long long beyondK = 0, trivialA = 0;
    while (fgets(line, sizeof line, stdin)) {
      if (!parse_g6(line)) continue;
      char *nl = strchr(line, '\n'); if (nl) *nl = 0;
      int g = -1, ne = 0;
      for (int v = 0; v < n; v++) if (dg0[v] > 0 && !(dg0[v] & 1)) { g = v; ne++; }
      if (ne > 1) continue;
      graphs++;
      for (int c = 0; c < n; c++) {
        if (!(dg0[c] & 1)) continue;
        uint32_t bad = (1u << c) | nbr[c];
        if (g >= 0 && !dropNg) bad |= nbr[g];
        uint32_t Amax = 0;
        for (int v = 0; v < n; v++) if (dg0[v] > 0 && !(bad >> v & 1)) Amax |= 1u << v;
        pairs++;
        if (!Amax) { trivialA++; maxok++; continue; }
        int r = avoid_query(c, Amax);
        if (r == 1) { maxok++; continue; }
        /* enumerate subsets of Amax by size; keep the minimal failing ones */
        int idx[32], k = 0;
        for (int v = 0; v < n; v++) if (Amax >> v & 1) idx[k++] = v;
        uint32_t fails[4096]; int nf = 0; int minsz = 0;
        for (int s = 1; s <= K && s <= k; s++) {
          /* iterate combinations of size s */
          int comb[32];
          for (int i = 0; i < s; i++) comb[i] = i;
          while (1) {
            uint32_t S = 0;
            for (int i = 0; i < s; i++) S |= 1u << idx[comb[i]];
            int sup = 0;
            for (int i = 0; i < nf; i++) if ((fails[i] & S) == fails[i]) { sup = 1; break; }
            if (!sup) {
              int rr = avoid_query(c, S);
              if (rr == 0 && nf < 4096) {
                fails[nf++] = S;
                if (!minsz) minsz = s;
                minsets[s]++;
                int hasg = g >= 0 && (S >> g & 1);
                int packed = 1, indep = 1;
                for (int x = 0; x < n; x++) if (S >> x & 1) {
                  if (nbr[x] & S) indep = 0;
                  if (ball2(x) & S & ~(1u << x)) packed = 0;
                }
                feat_g[s] += hasg; feat_packed[s] += packed; feat_indep[s] += indep;
                if (!quiet) {
                  printf("MINFAIL %s g=%d c=%d dc=%d A=", line, g, c, dg0[c]);
                  for (int x = 0; x < n; x++) if (S >> x & 1) printf("%d,", x);
                  printf(" size=%d hasg=%d packed=%d indep=%d\n", s, hasg, packed, indep);
                }
              }
            }
            int i = s - 1;
            while (i >= 0 && comb[i] == k - s + i) i--;
            if (i < 0) break;
            comb[i]++;
            for (int j = i + 1; j < s; j++) comb[j] = comb[j - 1] + 1;
          }
        }
        if (minsz) bysize[minsz]++; else beyondK++;
      }
      if (graphs % 100000 == 0) {
        fprintf(stderr, "PARTIAL graphs=%lld pairs=%lld maxok=%lld\n", graphs, pairs, maxok);
      }
    }
    printf("SUMMARY max K=%d dropNg=%d graphs=%lld pairs(G,c)=%lld Amax_ok=%lld trivial(Amax empty)=%lld minfail_size>K=%lld\n",
           K, dropNg, graphs, pairs, maxok, trivialA, beyondK);
    for (int s = 1; s < 40; s++) if (bysize[s] || minsets[s])
      printf("  smallest failing size %d: pairs=%lld ; minimal failing sets of size %d: %lld (contain g: %lld, packed: %lld, independent: %lld)\n",
             s, bysize[s], s, minsets[s], feat_g[s], feat_packed[s], feat_indep[s]);
    return 0;
  }
  fprintf(stderr, "unknown mode\n");
  return 1;
}
