/* lsearch.c: constrained path-decomposition search (session claude/t6-dense).
   Engine: the depth-first search of tools/stl.c / terminal-matching walk3p.c (paths grown from a
   vertex with an end, memoised failures keyed by remaining edges and end profile), with
   constraints that depend only on the path being closed, so the memo stays exact:
     sep  a b      : no path contains both a and b;
     ef   v S      : a path with an end at v avoids every vertex of S (end-path avoidance);
     ep   a b      : no path has ends exactly a and b;
     es   p q S    : the path containing the edge pq has its end on p's side outside S.
   Input: blocks of 6 lines
     n m seed budget
     u1 v1 ... um vm
     b_0 ... b_{n-1}                      (required end counts)
     nsep a1 b1 ...
     nef  v1 k1 s... v2 k2 s...
     nep  a1 b1 ...
     nes  p1 q1 k1 s... ...
   (the last four lines start with their count). Output per block: "OK k" and k path lines
   (vertex lists), or "NONE", or "UND" (node budget exhausted; budget 0 = exact).
   Limits: n <= 32, m <= 128. */
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

typedef struct { u128 mask; u128 prof; } key_t2;
static key_t2 *tab; static uint32_t *used; static uint32_t stamp = 1; static size_t cap, cnt;
static void hreset(void) {
  if (!tab) { cap = 1u << 16; tab = malloc(cap * sizeof(key_t2)); used = calloc(cap, sizeof(uint32_t)); }
  stamp++;
  if (stamp == 0) { memset(used, 0, cap * sizeof(uint32_t)); stamp = 1; }
  cnt = 0;
}
static size_t hh(u128 a, u128 bb) {
  uint64_t lo = (uint64_t)a, hi = (uint64_t)(a >> 64);
  uint64_t b = (uint64_t)bb ^ ((uint64_t)(bb >> 64) * 0x94D049BB133111EBULL);
  uint64_t x = lo * 0x9E3779B97F4A7C15ULL ^ (hi * 0xC2B2AE3D27D4EB4FULL) ^ (b + 0x632BE59BD9B4E019ULL + (lo << 6));
  x ^= x >> 31; x *= 0xBF58476D1CE4E5B9ULL; x ^= x >> 29;
  return (size_t)x;
}
static int hfind(u128 a, u128 b) {
  size_t i = hh(a, b) & (cap - 1);
  while (used[i] == stamp) { if (tab[i].mask == a && tab[i].prof == b) return 1; i = (i + 1) & (cap - 1); }
  return 0;
}
static void hgrow(void);
static void hadd(u128 a, u128 b) {
  if (cnt * 2 > cap) hgrow();
  size_t i = hh(a, b) & (cap - 1);
  while (used[i] == stamp) i = (i + 1) & (cap - 1);
  used[i] = stamp; tab[i].mask = a; tab[i].prof = b; cnt++;
}
static void hgrow(void) {
  size_t oc = cap; key_t2 *ot = tab; uint32_t *ou = used;
  cap *= 2; tab = malloc(cap * sizeof(key_t2)); used = calloc(cap, sizeof(uint32_t)); cnt = 0;
  for (size_t i = 0; i < oc; i++) if (ou[i] == stamp) hadd(ot[i].mask, ot[i].prof);
  free(ot); free(ou);
}

static int b[MAXN];
static u128 rem;
static uint32_t sepm[MAXN], efm[MAXN], epm[MAXN];
#define MAXES 16
static int nes, esp[MAXES], esq[MAXES]; static uint32_t esm[MAXES];
static int ord[MAXN];
static unsigned long long budget, nodes;
static int aborted;
static uint64_t rng_state;
static uint64_t rnd(void) { rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17; return rng_state; }

static int popc(u128 x) { return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64)); }
static int ctz128(u128 x) { uint64_t lo = (uint64_t)x; return lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll((uint64_t)(x >> 64)); }
static int deg(int v) { return popc(rem & inc[v]); }
static u128 packb(void) { u128 p = 0; for (int v = 0; v < n; v++) p |= (u128)b[v] << (4 * v); return p; }

static int pbuf[MAXM][MAXN + 1];
static int plens[MAXM], pd;
#define pathbuf pbuf[pd]
#define plen plens[pd]
static int wit[MAXM][MAXN + 1], witlen[MAXM], nwit;

static int solve(void);

/* constraints on the closed path pathbuf[0..plen-1] with vertex mask vis */
static int close_ok(int a, int w, uint32_t vis) {
  if (efm[a] & vis) return 0;
  if (efm[w] & vis) return 0;
  if ((epm[a] >> w) & 1) return 0;
  for (int i = 0; i < nes; i++) {
    int p = esp[i], q = esq[i];
    if (!((vis >> p) & 1) || !((vis >> q) & 1)) continue;
    for (int j = 0; j + 1 < plen; j++) {
      int s = pathbuf[j], t = pathbuf[j + 1];
      if (s == p && t == q) { if ((esm[i] >> pathbuf[0]) & 1) return 0; }
      else if (s == q && t == p) { if ((esm[i] >> pathbuf[plen - 1]) & 1) return 0; }
    }
  }
  return 1;
}

static int extend(int a, int c, uint32_t vis) {
  if (aborted) return 0;
  if (budget && ++nodes > budget) { aborted = 1; return 0; }
  for (int iw = 0; iw < n; iw++) {
    int w = ord[iw];
    if (vis >> w & 1) continue;
    if (sepm[w] & vis) continue;
    int e = eid[c][w];
    if (e < 0 || !((rem >> e) & 1)) continue;
    uint32_t vis2 = vis | (1u << w);
    if (efm[a] & vis2) continue;          /* a is an end of this path: it can never close */
    rem &= ~((u128)1 << e);
    pathbuf[plen++] = w;
    if (b[w] > 0 && close_ok(a, w, vis2)) {
      b[a]--; b[w]--;
      memcpy(wit[nwit], pathbuf, plen * sizeof(int)); witlen[nwit] = plen; nwit++;
      pd++;
      int ok = solve();
      pd--;
      b[a]++; b[w]++;
      if (ok) { rem |= (u128)1 << e; plen--; return 1; }
      nwit--;
    }
    if (rem & inc[w]) {
      if (extend(a, w, vis2)) { rem |= (u128)1 << e; plen--; return 1; }
    }
    plen--;
    rem |= (u128)1 << e;
  }
  return 0;
}

static uint32_t prio;   /* vertices whose end paths are constrained: grow their paths first */
static int prune_ok(int *bestp) {
  int S = 0;
  for (int v = 0; v < n; v++) S += b[v];
  if (S & 1) return 0;
  int P = S / 2;
  int best = -1, bd = 999, pbest = -1, pbd = 999;
  for (int iv = 0; iv < n; iv++) {
    int v = ord[iv];
    int d = deg(v);
    if (b[v] > P || b[v] > d || d > 2 * P - b[v] || ((d - b[v]) & 1)) return 0;
    if (b[v] > 0 && d < bd) { bd = d; best = v; }
    if (b[v] > 0 && ((prio >> v) & 1) && d < pbd) { pbd = d; pbest = v; }
  }
  if (pbest >= 0) best = pbest;
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
  if (rem == 0) return S == 0;
  if (S == 0) return 0;
  int best;
  if (!prune_ok(&best)) return 0;
  u128 pk = packb();
  if (hfind(rem, pk)) return 0;
  plen = 1; pathbuf[0] = best;
  int r = extend(best, best, 1u << best);
  if (!r && !aborted) hadd(rem, pk);
  return r;
}

static int rdint(int *x) { return scanf("%d", x) == 1; }

int main(void) {
  int seed; unsigned long long bud;
  while (scanf("%d %d %d %llu", &n, &m, &seed, &bud) == 4) {
    if (n > MAXN || m > MAXM) { fprintf(stderr, "too large\n"); return 1; }
    for (int i = 0; i < n; i++) { inc[i] = 0; for (int j = 0; j < n; j++) eid[i][j] = -1; sepm[i] = efm[i] = epm[i] = 0; }
    for (int i = 0; i < m; i++) {
      int u, v; rdint(&u); rdint(&v);
      eu[i] = u; ev[i] = v; eid[u][v] = eid[v][u] = i; inc[u] |= (u128)1 << i; inc[v] |= (u128)1 << i;
    }
    for (int v = 0; v < n; v++) rdint(&b[v]);
    int k; rdint(&k);
    for (int i = 0; i < k; i++) { int x, y; rdint(&x); rdint(&y); sepm[x] |= 1u << y; sepm[y] |= 1u << x; }
    rdint(&k);
    for (int i = 0; i < k; i++) { int v, c; rdint(&v); rdint(&c); for (int j = 0; j < c; j++) { int s; rdint(&s); efm[v] |= 1u << s; } }
    rdint(&k);
    for (int i = 0; i < k; i++) { int x, y; rdint(&x); rdint(&y); epm[x] |= 1u << y; epm[y] |= 1u << x; }
    rdint(&nes);
    for (int i = 0; i < nes; i++) { int c; rdint(&esp[i]); rdint(&esq[i]); rdint(&c); esm[i] = 0; for (int j = 0; j < c; j++) { int s; rdint(&s); esm[i] |= 1u << s; } }
    prio = 0;
    for (int v = 0; v < n; v++) if (efm[v] || epm[v]) prio |= 1u << v;
    if (getenv("LS_NOPRIO")) prio = 0;
    rng_state = 0x9E3779B97F4A7C15ULL ^ ((uint64_t)(seed + 1) * 0xD6E8FEB86659FD93ULL);
    for (int i = 0; i < 4; i++) rnd();
    for (int v = 0; v < n; v++) ord[v] = v;
    if (seed) for (int v = n - 1; v > 0; v--) { int j = (int)(rnd() % (uint64_t)(v + 1)); int t = ord[v]; ord[v] = ord[j]; ord[j] = t; }
    nwit = 0; pd = 0; plens[0] = 0; hreset();
    budget = bud; nodes = 0; aborted = 0;
    rem = (m == 128) ? ~(u128)0 : (((u128)1 << m) - 1);
    int res = solve();
    if (res) {
      printf("OK %d\n", nwit);
      for (int i = 0; i < nwit; i++) { for (int j = 0; j < witlen[i]; j++) printf("%d%c", wit[i][j], j + 1 < witlen[i] ? ' ' : '\n'); }
    } else if (aborted) printf("UND\n");
    else printf("NONE\n");
    fflush(stdout);
  }
  return 0;
}
