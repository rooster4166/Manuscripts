/* Forcing gadgets for EMM_3 (endpoint-min-max, Section "Gadgets").

   A *port gadget* is a graph D with two port vertices x1, x2 (possibly equal).  In a host graph G,
   D is attached by two cut edges at x1 and x2.  Every partition of G restricts to a partition of
   the graph D^+ = D + l1 x1 + l2 x2 (two temporary leaves, one end at each).  The restriction is
   *joined* if l1 and l2 lie on one path, and *separated* otherwise.  D is *joined-forcing* for a
   profile b of D if D^+ has a realisation and every realisation is joined.

   Input (stdin): graph6 lines (the graphs D), e.g. from nauty-geng.
   For every port pair x1 <= x2 such that every vertex of D^+ other than l1, l2 has degree >= MIND
   (default 3; argv[1]), and every simple profile b of D^+ (1 on odd vertices, 0 or 2 on even
   ones), compute
       tot = D^+ realisable with b,
       sep = D^+ has a realisation with b in which the path from l1 does not end at l2.
   Print every (D, x1, x2, S) with tot = 1, sep = 0, where S is the set of even vertices with
   b = 2 (as a bitmask over V(D)), and a tally on stderr.

   The search is the exact depth-first search of tools/realis.c (same pruning, memoised failed
   states).  The first path is forced to start at l1 and, for sep, may not stop at l2.  Both tot
   and sep are up-closed in S (split a path at an even vertex with no end; splitting never joins
   l1 to l2), which is used to skip supersets.

   Options: argv[2] = "all" also prints every port pair's (tot, sep) counts.  */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 16
#define MAXM 64

static int n, m;
static int eu[MAXM], ev[MAXM];
static int eid[MAXN][MAXN];
static uint64_t inc[MAXN];

typedef struct { uint64_t mask; uint64_t prof; } key_t2;
static key_t2 *tab; static unsigned char *used; static size_t cap, cnt;
static void hgrow(void);
static void hreset(void) {
  if (!tab) { cap = 1u << 16; tab = malloc(cap * sizeof(key_t2)); used = calloc(cap, 1); }
  else if (cnt) memset(used, 0, cap);
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
static uint64_t rem;
static int forbid_a = -1, forbid_w = -1; /* the path started at forbid_a may not stop at forbid_w */

static int deg(int v) { return __builtin_popcountll(rem & inc[v]); }
static uint64_t packb(void) { uint64_t p = 0; for (int v = 0; v < n; v++) p |= (uint64_t)b[v] << (4 * v); return p; }

static int solve(void);

static int extend(int a, int c, int vis, int restricted) {
  for (int w = 0; w < n; w++) {
    if (vis >> w & 1) continue;
    int e = eid[c][w];
    if (e < 0 || !(rem >> e & 1)) continue;
    rem &= ~(1ULL << e);
    if (b[w] > 0 && !(restricted && w == forbid_w)) {
      b[a]--; b[w]--;
      if (solve()) { b[a]++; b[w]++; rem |= 1ULL << e; return 1; }
      b[a]++; b[w]++;
    }
    if (rem & inc[w]) {
      if (extend(a, w, vis | (1 << w), restricted)) { rem |= 1ULL << e; return 1; }
    }
    rem |= 1ULL << e;
  }
  return 0;
}

/* necessary conditions; returns 0 if the state is dead */
static int prune(void) {
  int S = 0;
  for (int v = 0; v < n; v++) S += b[v];
  if (S & 1) return 0;
  int P = S / 2;
  if (P == 0) return 0;
  for (int v = 0; v < n; v++) {
    int d = deg(v);
    if (b[v] > P || b[v] > d || d > 2 * P - b[v] || ((d - b[v]) & 1)) return 0;
  }
  int seen = 0;
  for (int v = 0; v < n; v++) {
    if ((seen >> v & 1) || !(rem & inc[v])) continue;
    int comp = 1 << v, frontier = 1 << v;
    while (frontier) {
      int x = __builtin_ctz(frontier); frontier &= frontier - 1;
      uint64_t ex = rem & inc[x];
      while (ex) {
        int e = __builtin_ctzll(ex); ex &= ex - 1;
        int y = eu[e] == x ? ev[e] : eu[e];
        if (!(comp >> y & 1)) { comp |= 1 << y; frontier |= 1 << y; }
      }
    }
    seen |= comp;
    int s = 0;
    for (int x = 0; x < n; x++) if (comp >> x & 1) s += b[x];
    if (s < 2) return 0;
  }
  return 1;
}

static int solve(void) {
  if (rem == 0) { for (int v = 0; v < n; v++) if (b[v]) return 0; return 1; }
  if (!prune()) return 0;
  int best = -1, bd = 99;
  for (int v = 0; v < n; v++) { int d = deg(v); if (b[v] > 0 && d < bd) { bd = d; best = v; } }
  uint64_t pk = packb();
  if (hfind(rem, pk)) return 0;
  int r = extend(best, best, 1 << best, 0);
  if (!r) hadd(rem, pk);
  return r;
}

/* realisable with b; if sep, the first path starts at l1 and does not stop at l2 */
static int query(const int *prof, int l1, int l2, int sep) {
  for (int v = 0; v < n; v++) b[v] = prof[v];
  rem = (m == 64) ? ~0ULL : ((1ULL << m) - 1);
  hreset();
  if (!prune()) return 0;
  forbid_a = l1; forbid_w = sep ? l2 : -1;
  return extend(l1, l1, 1 << l1, sep);
}

static int read_g6(const char *s, int *N, unsigned *adj) {
  int k = 0;
  if (s[0] == '>') return 0;
  *N = s[k++] - 63;
  if (*N > MAXN - 2) return 0;
  for (int i = 0; i < *N; i++) adj[i] = 0;
  int bit = 0, val = 0, have = 0;
  for (int j = 1; j < *N; j++)
    for (int i = 0; i < j; i++) {
      if (have == 0) { val = s[k++] - 63; have = 6; }
      have--;
      if (val >> have & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
      bit++;
    }
  return 1;
}

int main(int argc, char **argv) {
  int mind = argc > 1 ? atoi(argv[1]) : 3;
  int all = argc > 2 && strcmp(argv[2], "all") == 0;
  char line[256];
  long graphs = 0, pairs = 0, profiles = 0, nontrivial = 0, forcing = 0, forcing_pairs = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0;
    int N; unsigned adj[MAXN];
    if (!read_g6(line, &N, adj)) continue;
    graphs++;
    int dD[MAXN];
    for (int v = 0; v < N; v++) dD[v] = __builtin_popcount(adj[v]);
    for (int x1 = 0; x1 < N; x1++)
      for (int x2 = x1; x2 < N; x2++) {
        int dG[MAXN], ok = 1;
        for (int v = 0; v < N; v++) dG[v] = dD[v] + (v == x1) + (v == x2);
        for (int v = 0; v < N; v++) if (dG[v] < mind) ok = 0;
        if (!ok) continue;
        pairs++;
        /* build D^+ : vertices 0..N-1, l1 = N, l2 = N+1 */
        n = N + 2; m = 0;
        for (int i = 0; i < n; i++) { inc[i] = 0; for (int j = 0; j < n; j++) eid[i][j] = -1; }
        for (int i = 0; i < N; i++) for (int j = i + 1; j < N; j++) if (adj[i] >> j & 1) {
          eu[m] = i; ev[m] = j; m++;
        }
        eu[m] = x1; ev[m] = N; m++;
        eu[m] = x2; ev[m] = N + 1; m++;
        if (m > MAXM) continue;
        for (int e = 0; e < m; e++) {
          eid[eu[e]][ev[e]] = eid[ev[e]][eu[e]] = e;
          inc[eu[e]] |= 1ULL << e; inc[ev[e]] |= 1ULL << e;
        }
        int E[MAXN], ne = 0;
        for (int v = 0; v < N; v++) if (dG[v] % 2 == 0) E[ne++] = v;
        int NS = 1 << ne;
        char *tot = calloc(NS, 1), *sep = calloc(NS, 1);
        int prof[MAXN], ctot = 0, csep = 0, cf = 0;
        for (int sz = 0; sz <= ne; sz++)
          for (int s = 0; s < NS; s++) {
            if (__builtin_popcount(s) != sz) continue;
            for (int i = 0; i < ne; i++) if (s >> i & 1) {
              if (tot[s & ~(1 << i)]) tot[s] = 1;
              if (sep[s & ~(1 << i)]) sep[s] = 1;
            }
            for (int v = 0; v < N; v++) prof[v] = dG[v] % 2;
            for (int i = 0; i < ne; i++) prof[E[i]] = (s >> i & 1) ? 2 : 0;
            prof[N] = prof[N + 1] = 1;
            profiles++;
            if (!sep[s]) sep[s] = (char)query(prof, N, N + 1, 1);
            if (!tot[s]) tot[s] = sep[s] ? 1 : (char)query(prof, N, N + 1, 0);
            ctot += tot[s]; csep += sep[s];
            if (tot[s] && !sep[s]) {
              int mask = 0;
              for (int i = 0; i < ne; i++) if (s >> i & 1) mask |= 1 << E[i];
              printf("FORCING %s x1=%d x2=%d S=%d b=", line, x1, x2, mask);
              for (int v = 0; v < N; v++) printf("%d", prof[v]);
              printf("\n");
              cf++;
            }
          }
        if (ctot) nontrivial++;
        forcing += cf; forcing_pairs += cf > 0;
        if (all) printf("PAIR %s x1=%d x2=%d tot=%d sep=%d\n", line, x1, x2, ctot, csep);
        free(tot); free(sep);
        fflush(stdout);
      }
  }
  fprintf(stderr, "graphs %ld port-pairs %ld profiles %ld realisable-pairs %ld forcing-profiles %ld forcing-pairs %ld\n",
          graphs, pairs, profiles, nontrivial, forcing, forcing_pairs);
  return 0;
}
