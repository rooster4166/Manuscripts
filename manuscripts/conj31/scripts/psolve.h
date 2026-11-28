/* psolve.h -- exact solver: path decomposition with a prescribed end profile.
 *
 * Given a simple graph on n <= 16 vertices (adjacency bitmasks) and a target
 * b : V -> N, decide whether E(G) can be partitioned into paths such that every
 * vertex x is an end of exactly b(x) paths (a path with ends s != t counts once
 * at s and once at t).  The number of paths is then sum(b)/2.
 *
 * Search.  Between paths: pick a vertex s with remaining ends (fewest remaining
 * edges first) and enumerate every path that ends at s (this path must exist in
 * any completion, so the branching is complete).  Pruning (all sound):
 *   (P1) re(x) <= rd(x) and rd(x)+re(x) <= 2*(sum_{y in C} re(y))/2 for every x in a
 *        component C of the remaining edge graph (a path through x uses <= 2 edges
 *        at x, one fewer for each end at x; paths stay inside one component);
 *   (P2) a component with an edge has remaining ends;
 *   (P3) failed between-path states are memoised (key = remaining edges + re).
 * No pruning removes a solution, so "no solution" answers are exact.
 */
#include <stdint.h>
#include <string.h>
#include <stdlib.h>

#define PS_MAXN 16
typedef struct {
  int n;
  uint32_t adj[PS_MAXN];   /* remaining edges */
  int re[PS_MAXN];         /* remaining ends */
  /* witness */
  int npaths;
  int plen[64];
  int pv[64][PS_MAXN + 1];
  long nodes;
  long node_limit;         /* 0 = unlimited; if exceeded, ps_solve returns -1 */
  int aborted;
} PS;

/* ---------------- memo of failed states ---------------- */
#define PS_HBITS 22
#define PS_HSIZE (1u << PS_HBITS)
typedef struct { uint64_t a, b, c; } PSKey;
static PSKey *ps_tab = NULL;
static uint32_t *ps_gen = NULL;
static uint32_t ps_curgen = 1;

static void ps_memo_init(void) {
  if (!ps_tab) {
    ps_tab = (PSKey *)calloc(PS_HSIZE, sizeof(PSKey));
    ps_gen = (uint32_t *)calloc(PS_HSIZE, sizeof(uint32_t));
  }
  ps_curgen++;
  if (ps_curgen == 0) { memset(ps_gen, 0, PS_HSIZE * sizeof(uint32_t)); ps_curgen = 1; }
}

static PSKey ps_key(PS *P) {
  PSKey k = {0, 0, 0};
  int n = P->n, bit = 0;
  for (int x = 0; x < n; x++)
    for (int y = x + 1; y < n; y++) {
      if (P->adj[x] >> y & 1) {
        if (bit < 64) k.a |= 1ull << bit; else k.b |= 1ull << (bit - 64);
      }
      bit++;
    }
  for (int x = 0; x < n; x++) k.c |= (uint64_t)(P->re[x] & 15) << (4 * x);
  return k;
}
static uint32_t ps_hash(PSKey k) {
  uint64_t h = k.a * 0x9E3779B97F4A7C15ull ^ (k.b + 0x632BE59BD9B4E019ull) * 0xC2B2AE3D27D4EB4Full ^ k.c * 0x165667B19E3779F9ull;
  h ^= h >> 29; h *= 0xBF58476D1CE4E5B9ull; h ^= h >> 32;
  return (uint32_t)h & (PS_HSIZE - 1);
}
static int ps_memo_has(PSKey k) {
  uint32_t h = ps_hash(k);
  for (int i = 0; i < 8; i++) {
    uint32_t j = (h + i) & (PS_HSIZE - 1);
    if (ps_gen[j] != ps_curgen) return 0;
    if (ps_tab[j].a == k.a && ps_tab[j].b == k.b && ps_tab[j].c == k.c) return 1;
  }
  return 0;
}
static void ps_memo_add(PSKey k) {
  uint32_t h = ps_hash(k);
  for (int i = 0; i < 8; i++) {
    uint32_t j = (h + i) & (PS_HSIZE - 1);
    if (ps_gen[j] != ps_curgen) { ps_gen[j] = ps_curgen; ps_tab[j] = k; return; }
  }
  /* table neighbourhood full: overwrite the home slot (memo is only a cache) */
  ps_tab[h] = k; ps_gen[h] = ps_curgen;
}

/* ---------------- feasibility ---------------- */
static int ps_feasible(PS *P) {
  int n = P->n;
  uint32_t seen = 0;
  for (int x = 0; x < n; x++) {
    int rd = __builtin_popcount(P->adj[x]);
    if (P->re[x] > rd) return 0;
    if (((rd - P->re[x]) & 1)) return 0;
  }
  for (int x = 0; x < n; x++) {
    if ((seen >> x & 1) || P->adj[x] == 0) continue;
    uint32_t comp = 1u << x, fr = 1u << x;
    while (fr) {
      int y = __builtin_ctz(fr); fr &= fr - 1;
      uint32_t nb = P->adj[y] & ~comp;
      comp |= nb; fr |= nb;
    }
    seen |= comp;
    int sre = 0;
    for (uint32_t c = comp; c; c &= c - 1) sre += P->re[__builtin_ctz(c)];
    if (sre < 2) return 0;
    for (uint32_t c = comp; c; c &= c - 1) {
      int y = __builtin_ctz(c);
      if (__builtin_popcount(P->adj[y]) + P->re[y] > sre) return 0;
    }
  }
  return 1;
}

static int ps_next(PS *P);

static int ps_extend(PS *P, int s, int t, uint32_t vis, int len) {
  if (P->aborted) return 0;
  P->nodes++;
  if (P->node_limit && P->nodes > P->node_limit) { P->aborted = 1; return 0; }
  int pi = P->npaths;
  P->pv[pi][len] = t;
  /* option 1: continue */
  uint32_t nb = P->adj[t] & ~vis;
  while (nb) {
    int y = __builtin_ctz(nb); nb &= nb - 1;
    P->adj[t] &= ~(1u << y); P->adj[y] &= ~(1u << t);
    int r = ps_extend(P, s, y, vis | (1u << y), len + 1);
    P->adj[t] |= 1u << y; P->adj[y] |= 1u << t;
    if (r) return 1;
    if (P->aborted) return 0;
  }
  /* option 2: stop at t */
  if (len > 0 && P->re[t] > 0) {
    P->re[t]--;
    P->plen[pi] = len + 1;
    P->npaths++;
    int r = ps_next(P);
    if (r) return 1;
    P->npaths--;
    P->re[t]++;
  }
  return 0;
}

static int ps_next(PS *P) {
  int n = P->n;
  int any = 0;
  for (int x = 0; x < n; x++) if (P->adj[x]) { any = 1; break; }
  if (!any) {
    for (int x = 0; x < n; x++) if (P->re[x]) return 0;
    return 1;
  }
  if (!ps_feasible(P)) return 0;
  PSKey k = ps_key(P);
  if (ps_memo_has(k)) return 0;
  int s = -1, best = 1 << 30;
  for (int x = 0; x < n; x++)
    if (P->re[x] > 0) {
      int rd = __builtin_popcount(P->adj[x]);
      if (rd < best) { best = rd; s = x; }
    }
  if (s < 0) return 0;
  P->re[s]--;
  int r = ps_extend(P, s, s, 1u << s, 0);
  P->re[s]++;
  if (!r && !P->aborted) ps_memo_add(k);
  return r;
}

/* returns 1 (solution in P->pv/plen/npaths), 0 (none), -1 (node limit hit) */
static int ps_solve(PS *P, int n, const uint32_t *adj, const int *b, long node_limit) {
  P->n = n;
  for (int x = 0; x < n; x++) { P->adj[x] = adj[x]; P->re[x] = b[x]; }
  P->npaths = 0; P->nodes = 0; P->node_limit = node_limit; P->aborted = 0;
  ps_memo_init();
  int r = ps_next(P);
  if (P->aborted) return -1;
  return r;
}

/* ---------------- graph6 ---------------- */
static int g6_decode(const char *s, int *n, uint32_t *adj) {
  int N = s[0] - 63;
  if (N < 1 || N > PS_MAXN) return 0;
  *n = N;
  for (int i = 0; i < N; i++) adj[i] = 0;
  int bit = 0; const char *p = s + 1; int cur = 0, left = 0;
  for (int j = 1; j < N; j++)
    for (int i = 0; i < j; i++) {
      if (left == 0) { cur = *p++ - 63; left = 6; }
      left--;
      if (cur >> left & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
      bit++;
    }
  return 1;
}
