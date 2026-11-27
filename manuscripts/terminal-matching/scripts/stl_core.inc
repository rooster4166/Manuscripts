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

