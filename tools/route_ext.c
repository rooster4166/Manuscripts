/* route_ext.c: exact realisability oracle with a constrained first path (route-descent session).

   Same search as tools/realis.c (depth-first search for the paths one at a time, exact
   necessary-condition pruning, memoised failures), extended to n <= 32 vertices and m <= 128
   edges (edge masks are 128-bit; profiles are packed 2 bits per vertex, so b <= 3).

   Input (stdin), one query per line:
     P n m u1 v1 ... um vm b0 .. b_{n-1}
          print 1 if the profile b is realisable (E(G) partitions into paths with exactly
          b(v) ends at v), else 0.
     X n m u1 v1 ... um vm b0 .. b_{n-1} c f
          constrained query: print 1 if there is a realisation of b in which some path Q with
          an end at c avoids every vertex of the bit mask f (f must not contain c).  When
          b(c) = 1, Q is the unique path ending at c.
     C n m u1 v1 ... um vm b0 .. b_{n-1} r0 .. r_{n-1}
          route-respecting query: r_v is a vertex bit mask (v is added to it).  Print 1 if b is
          realisable by paths each of which, with ends s and w, meets r_s only in s, meets r_w
          only in w, and has r_s, r_w disjoint.  (With r_c = V(R) for the tail c of each route R
          and r_v = {v} otherwise, on G - J: the routes can all be appended.)
     A n m u1 v1 ... um vm b0 .. b_{n-1} x0 .. x_{n-1}
          avoidance query: print 1 if b is realisable by paths each of which avoids x_s and x_w,
          where s, w are its ends (x_v is a vertex bit mask; v itself is removed from x_v).
     W... (WP / WX / WC / WA): as P / X / C / A, but on success also print the paths of one realisation on the
          same line after the 1, as  "| v0 v1 ... | w0 w1 ... |".
     Flag B (e.g. PB, XB, CB, WPB): two more numbers follow the query, a seed and a node budget;
          the neighbour order is shuffled by the seed and the search stops after `budget` calls
          of the path-growing step, printing 2 (unknown) if it was cut off.  Budget 0 = none.
   Output: one line per query.  Prints -1 for unsupported input (n > 32, m > 128, b > 3).

   The extension step of route descent: for a route R from c to a in G, with G' = G - E(R),
   "G' has a realisation of b' whose path at c avoids V(R) - c" is query X on G' with
   f = V(R) - c.  It is equivalent to "G has a realisation of b in which R is a terminal
   segment, ending at a, of some path".
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

typedef struct { u128 mask; uint64_t prof; } key_t2;
static key_t2 *tab; static unsigned char *used; static size_t cap, cnt;

static void hreset(void) {
  if (!tab) { cap = 1u << 20; tab = malloc(cap * sizeof(key_t2)); used = calloc(cap, 1); }
  else memset(used, 0, cap);
  cnt = 0;
}
static size_t hh(u128 a, uint64_t b) {
  uint64_t lo = (uint64_t)a, hi = (uint64_t)(a >> 64);
  uint64_t x = lo * 0x9E3779B97F4A7C15ULL ^ (hi * 0xC2B2AE3D27D4EB4FULL) ^ (b + 0x632BE59BD9B4E019ULL + (lo << 6));
  x ^= x >> 31; x *= 0xBF58476D1CE4E5B9ULL; x ^= x >> 29;
  return (size_t)x;
}
static int hfind(u128 a, uint64_t b) {
  size_t i = hh(a, b) & (cap - 1);
  while (used[i]) { if (tab[i].mask == a && tab[i].prof == b) return 1; i = (i + 1) & (cap - 1); }
  return 0;
}
static void hgrow(void);
static void hadd(u128 a, uint64_t b) {
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
static u128 rem;

/* budgeted randomised search (flag B): vertex order ord[], node budget; aborted => answer 2 */
static int ord[MAXN];
static unsigned long long budget, nodes;
static int aborted;
static uint64_t rng_state;
static uint64_t rnd(void) { rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17; return rng_state; }

static int popc(u128 x) { return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64)); }
static int ctz128(u128 x) { uint64_t lo = (uint64_t)x; return lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll((uint64_t)(x >> 64)); }
static int deg(int v) { return popc(rem & inc[v]); }
static uint64_t packb(void) { uint64_t p = 0; for (int v = 0; v < n; v++) p |= (uint64_t)b[v] << (2 * v); return p; }

/* witness recording */
static int want_witness;
static int pbuf[MAXM][MAXN + 1];      /* vertices of the path under construction, per depth */
static int plens[MAXM], pd;           /* pd = index of the path under construction */
#define pathbuf pbuf[pd]
#define plen plens[pd]
static int wit[MAXM][MAXN + 1], witlen[MAXM], nwit; /* stack of completed paths */

static int solve(void);

/* route-respecting constraint (query C): a path with ends s, w must satisfy
   V(path) & crv[s] = {s}, V(path) & crv[w] = {w} and crv[s] & crv[w] = 0 */
static int use_c, use_a;
static uint32_t crv[MAXN];      /* query C: route vertex sets */
static uint32_t avd[MAXN];      /* query A: a path ending at v avoids avd[v] */

static int extend(int a, int c, uint32_t vis, uint32_t pm) {
  if (aborted) return 0;
  if (budget && ++nodes > budget) { aborted = 1; return 0; }
  for (int iw = 0; iw < n; iw++) {
    int w = ord[iw];
    if (vis >> w & 1) continue;
    int e = eid[c][w];
    if (e < 0 || !((rem >> e) & 1)) continue;
    rem &= ~((u128)1 << e);
    pathbuf[plen++] = w;
    uint32_t pm2 = pm | (1u << w);
    if (b[w] > 0 && (!use_c || ((pm2 & crv[w]) == (1u << w) && (crv[a] & crv[w]) == 0))
        && (!use_a || (pm2 & avd[w]) == 0)) {
      b[a]--; b[w]--;
      if (want_witness) { memcpy(wit[nwit], pathbuf, plen * sizeof(int)); witlen[nwit] = plen; nwit++; }
      pd++;
      int ok = solve();
      pd--;
      if (ok) { b[a]++; b[w]++; rem |= (u128)1 << e; plen--; return 1; }
      if (want_witness) nwit--;
      b[a]++; b[w]++;
    }
    if (rem & inc[w]) {
      if (extend(a, w, vis | (1u << w), pm2)) { rem |= (u128)1 << e; plen--; return 1; }
    }
    plen--;
    rem |= (u128)1 << e;
  }
  return 0;
}

/* necessary conditions; returns 0 if violated */
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
  uint64_t pk = packb();
  if (hfind(rem, pk)) return 0;
  plen = 1; pathbuf[0] = best;
  int r = extend(best, best, (1u << best) | (use_c ? crv[best] : 0) | (use_a ? avd[best] : 0), 1u << best);
  if (!r && !aborted) hadd(rem, pk);
  return r;
}

/* first path forced to start at c and avoid the vertices of f */
static int solve_first(int c, uint32_t f) {
  if (b[c] <= 0) return 0;
  if (rem == 0) return 0;
  if (!prune_ok(NULL)) return 0;
  plen = 1; pathbuf[0] = c;
  return extend(c, c, (1u << c) | f, 1u << c);
}

static u128 fullmask(void) { return m == 128 ? ~(u128)0 : (((u128)1 << m) - 1); }

int main(void) {
  char tag[8];
  while (scanf("%7s", tag) == 1) {
    if (scanf("%d %d", &n, &m) != 2) return 1;
    int bad = (n > MAXN || m > MAXM);
    int nn = n > MAXN ? MAXN : n;
    for (int i = 0; i < nn; i++) { inc[i] = 0; for (int j = 0; j < nn; j++) eid[i][j] = -1; }
    for (int e = 0; e < m; e++) {
      int u, v;
      if (scanf("%d %d", &u, &v) != 2) return 1;
      if (bad || e >= MAXM) continue;
      eu[e] = u; ev[e] = v;
      eid[u][v] = eid[v][u] = e;
      inc[u] |= (u128)1 << e; inc[v] |= (u128)1 << e;
    }
    int prof[64];
    for (int v = 0; v < n; v++) if (scanf("%d", &prof[v]) != 1) return 1;
    int isX = (strchr(tag, 'X') != NULL);
    int c = -1; unsigned long long f = 0;
    if (isX && scanf("%d %llu", &c, &f) != 2) return 1;
    use_c = (strchr(tag, 'C') != NULL);
    use_a = (strchr(tag, 'A') != NULL);
    if (use_a) for (int v = 0; v < n; v++) { unsigned long long x; if (scanf("%llu", &x) != 1) return 1; avd[v] = (uint32_t)x & ~(1u << v); }
    int useB = (strchr(tag, 'B') != NULL);
    if (use_c) for (int v = 0; v < n; v++) { unsigned long long x; if (scanf("%llu", &x) != 1) return 1; crv[v] = (uint32_t)x | (1u << v); }
    unsigned long long seed = 0, bud = 0;
    if (useB && scanf("%llu %llu", &seed, &bud) != 2) return 1;
    for (int v = 0; v < n && !bad; v++) if (prof[v] > 3 || prof[v] < 0) bad = 1;
    if (bad) { printf("-1\n"); fflush(stdout); continue; }
    want_witness = (tag[0] == 'W');
    nwit = 0; pd = 0; plens[0] = 0;
    hreset();
    for (int v = 0; v < n; v++) ord[v] = v;
    budget = bud; nodes = 0; aborted = 0;
    if (useB) {
      rng_state = seed * 0x9E3779B97F4A7C15ULL + 12345;
      for (int v = n - 1; v > 0; v--) { int j = (int)(rnd() % (unsigned)(v + 1)); int t = ord[v]; ord[v] = ord[j]; ord[j] = t; }
    }
    for (int v = 0; v < n; v++) b[v] = prof[v];
    rem = fullmask();
    int r = isX ? solve_first(c, (uint32_t)f) : solve();
    if (aborted) r = 2;
    printf("%d", r);
    if (r == 1 && want_witness) {
      printf(" |");
      for (int i = 0; i < nwit; i++) {
        for (int j = 0; j < witlen[i]; j++) printf(" %d", wit[i][j]);
        printf(" |");
      }
    }
    printf("\n");
    fflush(stdout);
  }
  return 0;
}
