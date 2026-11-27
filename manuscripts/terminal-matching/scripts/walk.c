/* walk.c: tests the base hypothesis of the walk theorem (session claude/ptm). Input lines: g6(G-F) a1 b1 a2 b2. */
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
  budget = 0; nodes = 0; aborted = 0; rem = fullmask(); bal = 0; rshort = 0;
  return solve();
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
static int MA[MAXN][MAXN];
static int pathv[MAXN], plen2, found;
static int a1, b1, x2, y2;
static long long tried;
static int try_path(void) {
  /* M = G - e1 - e2 - E(P) + l1@b1 ; l1 = gn */
  for (int u = 0; u <= gn; u++) for (int v = 0; v <= gn; v++) MA[u][v] = (u < gn && v < gn) ? GA[u][v] : 0;
  MA[a1][b1] = MA[b1][a1] = 0; MA[x2][y2] = MA[y2][x2] = 0;
  for (int i = 0; i + 1 < plen2; i++) { MA[pathv[i]][pathv[i + 1]] = MA[pathv[i + 1]][pathv[i]] = 0; }
  int l1 = gn; MA[l1][b1] = MA[b1][l1] = 1;
  int pu[3] = {x2, a1, l1}, pv[3] = {y2, l1, y2};
  tried++;
  return sepq(gn + 1, MA, 3, pu, pv);
}
static int maxlen;
static void dfs(int v, uint32_t vis) {
  if (found) return;
  if (v == y2) { if (try_path() == 1) found = 1; return; }
  if (plen2 > maxlen) return;
  for (int w = 0; w < gn && !found; w++) if (GA[v][w] && !(vis >> w & 1)) {
    if (w == b1 || w == x2) continue;
    if (w != y2 && GA[w][x2]) continue;        /* interior avoids N(x2) */
    if ((v == a1 && w == b1)) continue;
    pathv[plen2++] = w; dfs(w, vis | 1u << w); plen2--;
  }
}
int main(int argc, char **argv) {
  int extra = argc > 1 ? atoi(argv[1]) : 0;   /* allow paths up to shortest + extra */
  char line[1024]; long long inst = 0, okc = 0, nopath = 0;
  while (fgets(line, sizeof line, stdin)) {
    char *tok = strtok(line, " \t\n"); if (!tok) continue;
    char g6[256]; snprintf(g6, sizeof g6, "%s", tok);
    gn = parse_g6(tok, GA); if (gn < 0) continue;
    int fa_[2], fb_[2]; for (int i = 0; i < 2; i++) { fa_[i] = atoi(strtok(NULL, " \t\n")); fb_[i] = atoi(strtok(NULL, " \t\n")); }
    /* G = G' + F (input is G' = G - F as in ptm 'f' mode) */
    for (int i = 0; i < 2; i++) GA[fa_[i]][fb_[i]] = GA[fb_[i]][fa_[i]] = 1;
    inst++; found = 0; int anypath = 0;
    for (int cfg = 0; cfg < 8 && !found; cfg++) {
      int e = cfg >> 2, o1 = (cfg >> 1) & 1, o2 = cfg & 1;
      int A0 = fa_[e], B0 = fb_[e], X0 = fa_[1 - e], Y0 = fb_[1 - e];
      a1 = o1 ? B0 : A0; b1 = o1 ? A0 : B0; x2 = o2 ? Y0 : X0; y2 = o2 ? X0 : Y0;
      /* BFS distance from a1 to y2 under the walk constraints */
      int dist[MAXN]; for (int v = 0; v < gn; v++) dist[v] = -1;
      int q[MAXN], h = 0, t = 0; dist[a1] = 0; q[t++] = a1;
      while (h < t) { int v = q[h++]; if (v == y2) continue;
        for (int w = 0; w < gn; w++) if (GA[v][w] && dist[w] < 0) {
          if (w == b1 || w == x2) continue; if (w != y2 && GA[w][x2]) continue;
          dist[w] = dist[v] + 1; q[t++] = w; } }
      if (dist[y2] < 0) continue;
      anypath = 1;
      maxlen = dist[y2] + extra;
      plen2 = 1; pathv[0] = a1; dfs(a1, 1u << a1);
    }
    if (!anypath) nopath++;
    if (found) okc++; else printf("NOBASE %s %d %d %d %d anypath=%d\n", g6, fa_[0], fb_[0], fa_[1], fb_[1], anypath);
    fflush(stdout);
  }
  printf("SUMMARY inst=%lld base_ok=%lld nopath=%lld tried=%lld\n", inst, okc, nopath, tried);
  return 0;
}
