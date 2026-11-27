/* walk3p.c: walk3 with a parallel first edge allowed (session claude/ptm).  The pair x1y1 may be
   an edge of G' = J - z ("parallel"); it must then take the role e1 (the leafed edge), and its
   G'-edge stays in the base graph M = G' + l1 y1 - E(P1) - E(P2).  The other two pairs must be
   non-adjacent in G'.  This is the J-form of the chained walk theorem (merge l_i through z).
   usage: walk3p EXTRA [ALL [BUDGET]]: BUDGET = node budget per base search (0 = exact); cut-off
   searches count as no base and are reported as sep_und.
   Derived from walk3.c:
   Input lines: g6(G-F) a1 b1 a2 b2 a3 b3 (F simple, i.e. no F-edge parallel to a G-edge).
   usage: walk3 EXTRA [ALL] ; EXTRA = allowed excess over the shortest constrained length of each walk;
   ALL = 1: try all 48 configurations and print "BASE g6 F x1 x2 x3" for each one with a base. */
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

typedef struct { u128 mask; u128 prof; int extra; } key_t2;
static key_t2 *tab; static uint32_t *used; static uint32_t stamp = 1; static size_t cap, cnt;
/* (ptm.c change: generation stamps instead of clearing the table on every query) */

static void hreset(void) {
  if (!tab) { cap = 1u << 16; tab = malloc(cap * sizeof(key_t2)); used = calloc(cap, sizeof(uint32_t)); }
  stamp++;
  if (stamp == 0) { memset(used, 0, cap * sizeof(uint32_t)); stamp = 1; }
  cnt = 0;
}
static size_t hh(u128 a, u128 bb, int x0) {
  uint64_t lo = (uint64_t)a, hi = (uint64_t)(a >> 64);
  uint64_t b = (uint64_t)bb ^ ((uint64_t)(bb >> 64) * 0x94D049BB133111EBULL);
  uint64_t x = lo * 0x9E3779B97F4A7C15ULL ^ (hi * 0xC2B2AE3D27D4EB4FULL) ^ (b + 0x632BE59BD9B4E019ULL + (lo << 6))
               ^ ((uint64_t)(x0 + 1000) * 0xD6E8FEB86659FD93ULL);
  x ^= x >> 31; x *= 0xBF58476D1CE4E5B9ULL; x ^= x >> 29;
  return (size_t)x;
}
static int hfind(u128 a, u128 b, int x0) {
  size_t i = hh(a, b, x0) & (cap - 1);
  while (used[i] == stamp) { if (tab[i].mask == a && tab[i].prof == b && tab[i].extra == x0) return 1; i = (i + 1) & (cap - 1); }
  return 0;
}
static void hgrow(void);
static void hadd(u128 a, u128 b, int x0) {
  if (cnt * 2 > cap) hgrow();
  size_t i = hh(a, b, x0) & (cap - 1);
  while (used[i] == stamp) i = (i + 1) & (cap - 1);
  used[i] = stamp; tab[i].mask = a; tab[i].prof = b; tab[i].extra = x0; cnt++;
}
static void hgrow(void) {
  size_t oc = cap; key_t2 *ot = tab; uint32_t *ou = used;
  cap *= 2; tab = malloc(cap * sizeof(key_t2)); used = calloc(cap, sizeof(uint32_t)); cnt = 0;
  for (size_t i = 0; i < oc; i++) if (ou[i] == stamp) hadd(ot[i].mask, ot[i].prof, ot[i].extra);
  free(ot); free(ou);
}

static int b[MAXN];
static u128 rem;
static int Z, R, STAR, THR;
static int bal;      /* #LL - #SS so far */
static int use_t, use_m;
static int req[MAXN], forb[MAXN];   /* terminal-edge constraints: a path ending at v must have
                                       terminal neighbour req[v] (if >= 0), never forb[v] (if >= 0) */
static uint32_t pmask[MAXN];        /* allowed transitions c - Z - w : (pmask[c] >> w) & 1 */
static int rshort;   /* r short so far */
static int use_sep; static uint32_t sepm[MAXN];   /* (walk.c) separation: no path contains v and a vertex of sepm[v] */

static int ord[MAXN];
static unsigned long long budget, nodes;
static int aborted;
static uint64_t rng_state;
static uint64_t rnd(void) { rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17; return rng_state; }

static int popc(u128 x) { return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64)); }
static int ctz128(u128 x) { uint64_t lo = (uint64_t)x; return lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll((uint64_t)(x >> 64)); }
static int deg(int v) { return popc(rem & inc[v]); }
static u128 packb(void) { u128 p = 0; for (int v = 0; v < n; v++) p |= (u128)b[v] << (4 * v); return p; }

static int want_witness;
static int pbuf[MAXM][MAXN + 1];
static int plens[MAXM], pd;
#define pathbuf pbuf[pd]
#define plen plens[pd]
static int wit[MAXM][MAXN + 1], witlen[MAXM], nwit;

static int solve(void);

/* classify the just-closed path pathbuf[0..plen-1] (plen vertices); zp = index of Z or -1.
   returns delta bal, sets *rs = 1 if r is short on it */
static int classify(int zp, int *rs) {
  *rs = 0;
  if (zp < 0) return 0;
  int L = plen - 1;               /* edges */
  int sa = (zp == 1), sb = (L - zp == 1);
  if (R >= 0) {
    if (sa && pathbuf[0] == R) *rs = 1;
    if (sb && pathbuf[L] == R) *rs = 1;
  }
  if (sa && sb) return -1;
  if (!sa && !sb) return 1;
  return 0;
}

static int term_ok(int v, int nb) {
  if (!use_t) return 1;
  if (req[v] >= 0 && nb != req[v]) return 0;
  if (forb[v] >= 0 && nb == forb[v]) return 0;
  return 1;
}

/* a = start vertex, c = current vertex, vis = visited mask, zp = index of Z in path or -1 */
static int extend(int a, int c, uint32_t vis, int zp) {
  if (aborted) return 0;
  if (budget && ++nodes > budget) { aborted = 1; return 0; }
  /* star: if Z was entered at index >= 2, the vertex after Z must close the path */
  int mustclose = (STAR && zp >= 2 && c != Z);  /* we are past z: should have closed already */
  if (mustclose) return 0;
  int closeonly = (STAR && zp >= 2 && c == Z);
  for (int iw = 0; iw < n; iw++) {
    int w = ord[iw];
    if (vis >> w & 1) continue;
    if (use_sep && (sepm[w] & vis)) continue;
    int e = eid[c][w];
    if (e < 0 || !((rem >> e) & 1)) continue;
    if (use_m && c == Z && plen >= 2 && !((pmask[pathbuf[plen - 2]] >> w) & 1)) continue;
    if (use_t && plen == 1 && !term_ok(a, w)) continue;   /* first edge = terminal edge at a */
    rem &= ~((u128)1 << e);
    pathbuf[plen++] = w;
    int zp2 = (w == Z) ? plen - 1 : zp;
    if (b[w] > 0 && term_ok(w, c)) {
      int rs; int dbal = classify(zp2, &rs);
      int ok_close = 1;
      if (STAR && dbal > 0) ok_close = 0;
      if (ok_close) {
        int obal = bal, ors = rshort;
        bal += dbal; rshort |= rs;
        b[a]--; b[w]--;
        if (want_witness) { memcpy(wit[nwit], pathbuf, plen * sizeof(int)); witlen[nwit] = plen; nwit++; }
        pd++;
        int ok = solve();
        pd--;
        b[a]++; b[w]++;
        bal = obal; rshort = ors;
        if (ok) { rem |= (u128)1 << e; plen--; return 1; }
        if (want_witness) nwit--;
      }
    }
    if (!closeonly && (rem & inc[w])) {
      /* star pruning: entering Z at index >= 2 is fine only if we can close right after; checked inside */
      if (extend(a, w, vis | (1u << w), zp2)) { rem |= (u128)1 << e; plen--; return 1; }
    }
    plen--;
    rem |= (u128)1 << e;
  }
  return 0;
}

static int prune_ok(int *bestp) {
  int S = 0;
  for (int v = 0; v < n; v++) S += b[v];
  if (S & 1) return 0;
  int P = S / 2;
  int best = -1, bd = 999;
  for (int v = 0; v < n; v++) {
    int d = deg(v);
    if (b[v] > P || b[v] > d || d > 2 * P - b[v] || ((d - b[v]) & 1)) return 0;
    if (b[v] > 0 && d < bd) { bd = d; best = v; }
  }
  /* transition bound: each remaining pair of z-edges lowers bal by at most 1 */
  if (Z >= 0) {
    int rz = deg(Z) / 2;
    if (bal - rz + rshort > THR) return 0;
  }
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
    int s = 0;
    for (int x = 0; x < n; x++) if (comp >> x & 1) s += b[x];
    if (s < 2) return 0;
  }
  if (bestp) *bestp = best;
  return 1;
}

static int solve(void) {
  int S = 0;
  for (int v = 0; v < n; v++) S += b[v];
  if (rem == 0) return S == 0 && bal + rshort <= THR;
  if (S == 0) return 0;
  int best;
  if (!prune_ok(&best)) return 0;
  u128 pk = packb();
  int ex = (bal + 64) * 2 + rshort;
  if (hfind(rem, pk, ex)) return 0;
  plen = 1; pathbuf[0] = best;
  int r = extend(best, best, 1u << best, best == Z ? 0 : -1);
  if (!r && !aborted) hadd(rem, pk, ex);
  return r;
}

/* ===================== walk.c driver ===================== */
static unsigned long long sep_budget; static long long n_sep_und; static long long adj_pruned;   /* walk3p: node budget per base search */
static u128 fullmask(void) { return m == 128 ? ~(u128)0 : (((u128)1 << m) - 1); }
static int GA[MAXN][MAXN], gn;
/* Lovasz decomposition of graph A (order N, profile = degree parity) with separated pairs */
static int sepq(int N, int A[MAXN][MAXN], int np, const int *pu, const int *pv) {
  n = N; m = 0;
  for (int i = 0; i < n; i++) { inc[i] = 0; for (int j = 0; j < n; j++) eid[i][j] = -1; }
  for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++) if (A[u][v]) {
    if (m >= MAXM) return -1;
    eu[m] = u; ev[m] = v; eid[u][v] = eid[v][u] = m; inc[u] |= (u128)1 << m; inc[v] |= (u128)1 << m; m++; }
  Z = -1; R = -1; STAR = 0; THR = 0; use_m = 0; use_t = 0;
  use_sep = 1; for (int v = 0; v < n; v++) sepm[v] = 0;
  for (int i = 0; i < np; i++) { sepm[pu[i]] |= 1u << pv[i]; sepm[pv[i]] |= 1u << pu[i]; }
  for (int v = 0; v < n; v++) { int d = 0; for (int w = 0; w < n; w++) d += A[v][w]; b[v] = d & 1; }
  want_witness = 0; nwit = 0; pd = 0; plens[0] = 0; hreset();
  for (int v = 0; v < n; v++) ord[v] = v;
  budget = sep_budget; nodes = 0; aborted = 0; rem = fullmask(); bal = 0; rshort = 0;
  int res = solve();
  if (!res && aborted) { n_sep_und++; return 2; }
  return res;
}
static int parse_g6(const char *s, int A[MAXN][MAXN]) {
  int N = s[0] - 63; if (N < 1 || N > MAXN - 2) return -1;
  int k = 0, bit = 0; const char *p = s + 1;
  for (int i = 0; i < MAXN; i++) for (int j = 0; j < MAXN; j++) A[i][j] = 0;
  for (int j = 1; j < N; j++) for (int i = 0; i < j; i++) {
    if (bit == 0) { if (!*p) return -1; k = *p++ - 63; bit = 6; }
    bit--; if ((k >> bit) & 1) A[i][j] = A[j][i] = 1;
  }
  return N;
}
/* enumerate simple paths a1 -> y2 of length <= maxlen avoiding forbidden set, interior avoiding N(x2) */
/* ---- walk3: chained walks ----
   Labels after choosing the order of the edges and their orientations: e_i = x_i y_i, x_i short.
   Walks: P2 from y3 to x2, P1 from y2 to x1 (edge-disjoint, in G - F).
   Constraints (see manuscript, chained walk theorem):
     P2: vertices avoid x1, y1, y2, x3; x2 only as last vertex; vertices other than x2 not in N(x3).
     P1: vertices avoid y1, x2, x3; x1 only as last; vertices other than x1 not in N(x2) u N(x3).
   Base: M = G - e1 + l1 y1 - e2 - e3 - E(P1) - E(P2), l1 = gn; x3 its only even vertex.
   Separations: {x1,l1} {x2,y2} {x3,y3} {l1,y2} {l1,y3} {y2,y3}. */
static int MA[MAXN][MAXN];
static int BA[MAXN][MAXN];   /* walk3p: adjacency of G' = J - z */
static int X[3], Y[3];
static int P1[MAXN], n1, P2[MAXN], n2;
static int used2[MAXN][MAXN];
static long long tried, parity_bad;
static int found, maxlen1, maxlen2;
static int try_base(void) {
  for (int u = 0; u <= gn; u++) for (int v = 0; v <= gn; v++) MA[u][v] = (u < gn && v < gn) ? BA[u][v] : 0;
  for (int i = 0; i + 1 < n1; i++) MA[P1[i]][P1[i + 1]] = MA[P1[i + 1]][P1[i]] = 0;
  for (int i = 0; i + 1 < n2; i++) MA[P2[i]][P2[i + 1]] = MA[P2[i + 1]][P2[i]] = 0;
  int l1 = gn; MA[l1][Y[0]] = MA[Y[0]][l1] = 1;
  /* parity: x3 the only vertex of positive even degree */
  for (int v = 0; v <= gn; v++) { int d = 0; for (int w = 0; w <= gn; w++) d += MA[v][w];
    if (d > 0 && d % 2 == 0 && v != X[2]) { parity_bad++; return 0; } }
  int pu[6] = {X[0], X[1], X[2], l1, l1, Y[1]}, pv[6] = {l1, Y[1], Y[2], Y[1], Y[2], Y[2]};
  /* a separated pair adjacent in M can never be separated (its edge lies on some path) */
  for (int i = 0; i < 6; i++) if (MA[pu[i]][pv[i]]) { adj_pruned++; return 0; }
  tried++;
  return sepq(gn + 1, MA, 6, pu, pv);
}
static int ok1(int w) {   /* vertex allowed on P1 (not the last) */
  if (w == Y[0] || w == X[1] || w == X[2] || w == X[0]) return 0;
  if (GA[w][X[1]] && !(w == Y[1])) return 0;     /* y2 x2 is the F-edge e2, removed */
  if (GA[w][X[2]]) return 0;
  return 1;
}
static int ok2(int w) {   /* vertex allowed on P2 (not the last) */
  if (w == X[0] || w == Y[0] || w == Y[1] || w == X[2] || w == X[1]) return 0;
  if (GA[w][X[2]] && w != Y[2]) return 0;        /* y3 x3 is the F-edge e3, removed */
  return 1;
}
static int ue(int u, int v) { return used2[u][v]; }
static void dfs1(int v, uint32_t vis) {
  if (found) return;
  if (v == X[0]) { if (try_base() == 1) found = 1; return; }
  if (n1 > maxlen1) return;
  for (int w = 0; w < gn && !found; w++) if (GA[v][w] && !(vis >> w & 1) && !ue(v, w)) {
    if (w != X[0] && !ok1(w)) continue;
    int isF = 0; for (int i = 0; i < 3; i++) if ((v == X[i] && w == Y[i]) || (v == Y[i] && w == X[i])) isF = 1;
    if (isF) continue;
    P1[n1++] = w; dfs1(w, vis | 1u << w); n1--;
  }
}
static int bfs_dist(int s, int t, int which) {
  int dist[MAXN]; for (int v = 0; v < gn; v++) dist[v] = -1;
  int q[MAXN], h = 0, tt = 0; dist[s] = 0; q[tt++] = s;
  while (h < tt) { int v = q[h++]; if (v == t) continue;
    for (int w = 0; w < gn; w++) if (GA[v][w] && dist[w] < 0) {
      if (w != t && !(which == 1 ? ok1(w) : ok2(w))) continue;
      int isF = 0; for (int i = 0; i < 3; i++) if ((v == X[i] && w == Y[i]) || (v == Y[i] && w == X[i])) isF = 1;
      if (isF) continue;
      dist[w] = dist[v] + 1; q[tt++] = w; } }
  return dist[t];
}
static int extra;
static void dfs2(int v, uint32_t vis) {
  if (found) return;
  if (v == X[1]) {
    for (int i = 0; i + 1 < n2; i++) used2[P2[i]][P2[i + 1]] = used2[P2[i + 1]][P2[i]] = 1;
    n1 = 1; P1[0] = Y[1]; dfs1(Y[1], 1u << Y[1]);
    for (int i = 0; i + 1 < n2; i++) used2[P2[i]][P2[i + 1]] = used2[P2[i + 1]][P2[i]] = 0;
    return;
  }
  if (n2 > maxlen2) return;
  for (int w = 0; w < gn && !found; w++) if (GA[v][w] && !(vis >> w & 1)) {
    if (w != X[1] && !ok2(w)) continue;
    int isF = 0; for (int i = 0; i < 3; i++) if ((v == X[i] && w == Y[i]) || (v == Y[i] && w == X[i])) isF = 1;
    if (isF) continue;
    P2[n2++] = w; dfs2(w, vis | 1u << w); n2--;
  }
}
int main(int argc, char **argv) {
  extra = argc > 1 ? atoi(argv[1]) : 0;
  int all = argc > 2 ? atoi(argv[2]) : 0;
  sep_budget = argc > 3 ? strtoull(argv[3], 0, 10) : 0;
  char line[1024]; long long inst = 0, okc = 0, nopath = 0;
  static const int perm[6][3] = {{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
  while (fgets(line, sizeof line, stdin)) {
    char *tok = strtok(line, " \t\n"); if (!tok) continue;
    char g6[256]; snprintf(g6, sizeof g6, "%s", tok);
    gn = parse_g6(tok, GA); if (gn < 0 || gn + 1 > 32) continue;
    int fa_[3], fb_[3]; for (int i = 0; i < 3; i++) { fa_[i] = atoi(strtok(NULL, " \t\n")); fb_[i] = atoi(strtok(NULL, " \t\n")); }
    int par[3], npar = 0; for (int i = 0; i < 3; i++) { par[i] = GA[fa_[i]][fb_[i]]; npar += par[i]; }
    if (npar > 1) continue;
    for (int u = 0; u < gn; u++) for (int v = 0; v < gn; v++) BA[u][v] = GA[u][v];
    for (int i = 0; i < 3; i++) GA[fa_[i]][fb_[i]] = GA[fb_[i]][fa_[i]] = 1;
    inst++; found = 0; int anypath = 0, any = 0;
    for (int cfg = 0; cfg < 48 && !(found && !all); cfg++) {
      found = 0;
      const int *pr = perm[cfg / 8]; int o = cfg % 8;
      for (int i = 0; i < 3; i++) { int e = pr[i]; int fl = (o >> i) & 1; X[i] = fl ? fb_[e] : fa_[e]; Y[i] = fl ? fa_[e] : fb_[e]; }
      if (par[pr[1]] || par[pr[2]]) continue;    /* a parallel pair only as e1 */
      if (GA[Y[1]][X[2]]) continue;              /* y2 must not be adjacent to x3 */
      int d2 = bfs_dist(Y[2], X[1], 2), d1 = bfs_dist(Y[1], X[0], 1);
      if (d2 < 0 || d1 < 0) continue;
      anypath = 1;
      maxlen2 = d2 + extra; maxlen1 = d1 + extra;
      memset(used2, 0, sizeof used2);
      n2 = 1; P2[0] = Y[2]; dfs2(Y[2], 1u << Y[2]);
      if (found) { any = 1;
        if (all) printf("BASE %s %d %d %d %d %d %d short %d %d %d\n", g6, fa_[0], fb_[0], fa_[1], fb_[1], fa_[2], fb_[2], X[0], X[1], X[2]); }
    }
    found = any;
    if (!anypath) nopath++;
    if (found) okc++; else printf("NOBASE %s %d %d %d %d %d %d anypath=%d\n", g6, fa_[0], fb_[0], fa_[1], fb_[1], fa_[2], fb_[2], anypath);
    fflush(stdout);
  }
  printf("SUMMARY inst=%lld base_ok=%lld nopath=%lld tried=%lld parity_bad=%lld sep_und=%lld adj_pruned=%lld\n", inst, okc, nopath, tried, parity_bad, n_sep_und, adj_pruned);
  return 0;
}
