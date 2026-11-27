/* realis_wide.c: tools/realis.c for profiles with b <= 3 (e.g. simple profiles) on up to 30
   vertices.  Identical search; the memo key packs b in 2 bits per vertex (b only decreases
   during the search, so b <= 3 throughout).  Only "P" queries; prints 1 or 0, or -1 if some
   b(v) > 3 or n > 30.  The comment of realis.c follows; its limit n <= 16 is lifted here. */

/* Exact realisability oracle for small graphs (n <= 16, m <= 64).

   A profile b : V -> N is *realisable* in G if E(G) has a partition into simple paths
   with exactly b(v) path ends at v (a path of length >= 1 has two distinct ends).

   Input (stdin), one query per line:
       F n m u1 v1 ... um vm          family query: print the realisable sets S of even
                                      vertices (simple profile: 1 on odd, 2 on S, 0 on
                                      the other even vertices), one bitmask over V per set
       P n m u1 v1 ... um vm b0 .. b_{n-1}
                                      profile query: print 1 or 0
   Output: one line per query.  Families are printed as space-separated decimal masks,
   in increasing order of mask; the line starts with the count.

   Method: depth-first search for the paths one at a time.  The next path starts at a
   fixed vertex a with b(a) > 0 (every path decomposition has a path ending at a), and is
   grown edge by edge; it may stop at any vertex w != a with b(w) > 0.  Pruning (all are
   necessary conditions, so the search is exact):
     b(v) <= P, b(v) <= d(v), d(v) <= 2P - b(v), d(v) = b(v) mod 2,
   where P = sum b / 2 is the number of remaining paths and d is the remaining degree; and
   every component of the remaining graph carries at least two ends.  Failed states are
   memoised (edge mask + profile).
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 30
#define MAXM 64

static int n, m;
static int eu[MAXM], ev[MAXM];
static int eid[MAXN][MAXN];
static uint64_t inc[MAXN]; /* edges incident to v */

/* failed-state hash set */
typedef struct { uint64_t mask; uint64_t prof; } key_t2;
static key_t2 *tab; static unsigned char *used; static size_t cap, cnt;

static void hreset(void) {
  if (!tab) { cap = 1u << 20; tab = malloc(cap * sizeof(key_t2)); used = calloc(cap, 1); }
  else memset(used, 0, cap);
  cnt = 0;
}
static size_t hh(uint64_t a, uint64_t b) {
  uint64_t x = a * 0x9E3779B97F4A7C15ULL ^ (b + 0x632BE59BD9B4E019ULL + (a << 6));
  x ^= x >> 31; x *= 0xBF58476D1CE4E5B9ULL; x ^= x >> 29;
  return (size_t)x;
}
static int hfind(uint64_t a, uint64_t b) {
  size_t i = hh(a, b) & (cap - 1);
  while (used[i]) { if (tab[i].mask == a && tab[i].prof == b) return 1; i = (i + 1) & (cap - 1); }
  return 0;
}
static void hgrow(void);
static void hadd(uint64_t a, uint64_t b) {
  if (cnt * 2 > cap) hgrow();
  size_t i = hh(a, b) & (cap - 1);
  while (used[i]) i = (i + 1) & (cap - 1);
  used[i] = 1; tab[i].mask = a; tab[i].prof = b; cnt++;
}
static void hgrow(void) {
  size_t oc = cap; key_t2 *ot = tab; unsigned char *ou = used;
  cap *= 2; tab = malloc(cap * sizeof(key_t2)); used = calloc(cap, 1); cnt = 0;
  for (size_t i = 0; i < oc; i++) if (ou[i]) hadd(ot[i].mask, ot[i].prof);
  free(ot); free(ou);
}

static int b[MAXN];
static uint64_t rem; /* remaining edges */

static int deg(int v) { return __builtin_popcountll(rem & inc[v]); }
static uint64_t packb(void) { uint64_t p = 0; for (int v = 0; v < n; v++) p |= (uint64_t)b[v] << (2 * v); return p; }

static int solve(void);

/* extend the current path, which started at a and is now at c; vis = vertices on it */
static int extend(int a, int c, unsigned vis) {
  for (int w = 0; w < n; w++) {
    if (vis >> w & 1) continue;
    int e = eid[c][w];
    if (e < 0 || !(rem >> e & 1)) continue;
    rem &= ~(1ULL << e);
    if (b[w] > 0) {
      b[a]--; b[w]--;
      if (solve()) { b[a]++; b[w]++; rem |= 1ULL << e; return 1; }
      b[a]++; b[w]++;
    }
    if (rem & inc[w]) {
      if (extend(a, w, vis | (1u << w))) { rem |= 1ULL << e; return 1; }
    }
    rem |= 1ULL << e;
  }
  return 0;
}

static int solve(void) {
  int S = 0;
  for (int v = 0; v < n; v++) S += b[v];
  if (rem == 0) return S == 0;
  if (S & 1) return 0;
  int P = S / 2;
  if (P == 0) return 0;
  int best = -1, bd = 99;
  for (int v = 0; v < n; v++) {
    int d = deg(v);
    if (b[v] > P || b[v] > d || d > 2 * P - b[v] || ((d - b[v]) & 1)) return 0;
    if (b[v] > 0 && d < bd) { bd = d; best = v; }
  }
  /* components carry >= 2 ends */
  unsigned seen = 0;
  for (int v = 0; v < n; v++) {
    if ((seen >> v & 1) || !(rem & inc[v])) continue;
    unsigned comp = 1u << v, frontier = 1u << v;
    while (frontier) {
      int x = __builtin_ctz(frontier); frontier &= frontier - 1;
      uint64_t ex = rem & inc[x];
      while (ex) {
        int e = __builtin_ctzll(ex); ex &= ex - 1;
        int y = eu[e] == x ? ev[e] : eu[e];
        if (!(comp >> y & 1)) { comp |= 1u << y; frontier |= 1u << y; }
      }
    }
    seen |= comp;
    int s = 0;
    for (int x = 0; x < n; x++) if (comp >> x & 1) s += b[x];
    if (s < 2) return 0;
  }
  uint64_t pk = packb();
  if (hfind(rem, pk)) return 0;
  int r = extend(best, best, 1u << best);
  if (!r) hadd(rem, pk);
  return r;
}

static int realisable(const int *prof) {
  for (int v = 0; v < n; v++) b[v] = prof[v];
  rem = (m == 64) ? ~0ULL : ((1ULL << m) - 1);
  return solve();
}

int main(void) {
  char tag[4];
  while (scanf("%3s", tag) == 1) {
    if (scanf("%d %d", &n, &m) != 2) return 1;
    for (int i = 0; i < n; i++) { inc[i] = 0; for (int j = 0; j < n; j++) eid[i][j] = -1; }
    int dg[MAXN] = {0};
    for (int e = 0; e < m; e++) {
      if (scanf("%d %d", &eu[e], &ev[e]) != 2) return 1;
      eid[eu[e]][ev[e]] = eid[ev[e]][eu[e]] = e;
      inc[eu[e]] |= 1ULL << e; inc[ev[e]] |= 1ULL << e;
      dg[eu[e]]++; dg[ev[e]]++;
    }
    hreset();
    if (tag[0] != 'P') { printf("-1\n"); fflush(stdout); continue; }
    {
      int prof[MAXN], bad = n > MAXN;
      for (int v = 0; v < n; v++) { if (scanf("%d", &prof[v]) != 1) return 1; if (prof[v] > 3) bad = 1; }
      printf("%d\n", bad ? -1 : realisable(prof));
    }
    fflush(stdout);
  }
  return 0;
}
