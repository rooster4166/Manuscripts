/* cubsep.c: multi-pair separation (MSEP) for cubic graphs.

   A Lovasz decomposition of a cubic graph is a choice, at every vertex v, of one incident edge
   e(v) (the end edge; v is an end of the path containing it), the other two edges at v being
   consecutive on a path.  We search such choices by depth-first search, maintaining the path
   components with union-find and vertex masks:
     - linking two edges at v is allowed iff they lie in different components whose vertex sets
       meet only in v, and the end edge of v lies in neither (so every component stays a path);
     - a merged component must not contain both vertices of any pair (separation).
   Input (stdin): lines "graph6 [k s1 t1 ... sk tk]".  Without pairs, mode is chosen by argv:
     cubsep all  [cap]   : for each graph enumerate perfect pairings at distance >= 3 (up to cap
                            per graph, 0 = all) and test each.
     cubsep rand N seed  : N random perfect pairings at distance >= 3 per graph.
   Output: one summary line per graph; "FAIL graph6 pairs" lines for failures.
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 32
static int n, m;
static int adj[MAXN][3], eidx[MAXN][3];
static int eu[3 * MAXN / 2 + 2], ev_[3 * MAXN / 2 + 2];
static int partner[MAXN];
static int order[MAXN];
static int dist[MAXN][MAXN];

/* union-find with undo */
static int par[64], rnk[64];
static uint32_t msk[64];
typedef struct { int a, b, ra; uint32_t ma; } undo_t;
static undo_t ustack[4096]; static int usp;
static int find(int x) { while (par[x] != x) x = par[x]; return x; }

static uint32_t pmap(uint32_t M) {
  uint32_t r = 0;
  while (M) { int v = __builtin_ctz(M); M &= M - 1; if (partner[v] >= 0 && partner[v] != v) r |= 1u << partner[v]; }
  return r;
}

static int link(int e1, int e2, int v) {
  int a = find(e1), b = find(e2);
  if (a == b) return 0;
  if ((msk[a] & msk[b]) != (1u << v)) return 0;
  uint32_t M = msk[a] | msk[b];
  if (M & pmap(M)) return 0;
  if (rnk[a] < rnk[b]) { int t = a; a = b; b = t; }
  ustack[usp].a = a; ustack[usp].b = b; ustack[usp].ra = rnk[a]; ustack[usp].ma = msk[a]; usp++;
  par[b] = a; msk[a] = M; if (rnk[a] == rnk[b]) rnk[a]++;
  return 1;
}
static void unlink1(void) {
  usp--; int a = ustack[usp].a, b = ustack[usp].b;
  par[b] = b; rnk[a] = ustack[usp].ra; msk[a] = ustack[usp].ma;
}

static long long nodes; static long long budget;
static int choice[MAXN];

static int dfs(int i) {
  if (budget && ++nodes > budget) return -1;
  if (i == n) return 1;
  int v = order[i];
  for (int c = 0; c < 3; c++) {
    int e3 = eidx[v][c], e1 = eidx[v][(c + 1) % 3], e2 = eidx[v][(c + 2) % 3];
    int r3 = find(e3);
    if (r3 == find(e1) || r3 == find(e2)) continue;
    if (!link(e1, e2, v)) continue;
    /* after linking, e3's component must still differ from the merged one */
    if (find(e3) == find(e1)) { unlink1(); continue; }
    choice[v] = c;
    int r = dfs(i + 1);
    if (r != 0) { if (r == 1) return 1; unlink1(); return r; }
    unlink1();
  }
  return 0;
}

static int solve(void) {
  for (int e = 0; e < m; e++) { par[e] = e; rnk[e] = 0; msk[e] = (1u << eu[e]) | (1u << ev_[e]); }
  usp = 0; nodes = 0;
  return dfs(0);
}

static int parse_g6(const char *s) {
  int N = s[0] - 63; if (N > MAXN || N < 1) return 0;
  n = N;
  int deg[MAXN] = {0};
  m = 0;
  int bit = 0; const char *p = s + 1;
  for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
    int byte = bit / 6, off = 5 - bit % 6; bit++;
    if (((p[byte] - 63) >> off) & 1) {
      if (deg[i] >= 3 || deg[j] >= 3) return 0;
      adj[i][deg[i]] = j; eidx[i][deg[i]++] = m;
      adj[j][deg[j]] = i; eidx[j][deg[j]++] = m;
      eu[m] = i; ev_[m] = j; m++;
    }
  }
  for (int v = 0; v < n; v++) if (deg[v] != 3) return 0;
  /* BFS order and distances */
  for (int s0 = 0; s0 < n; s0++) {
    for (int v = 0; v < n; v++) dist[s0][v] = 99;
    int q[MAXN], h = 0, t = 0; q[t++] = s0; dist[s0][s0] = 0;
    while (h < t) { int x = q[h++]; for (int k = 0; k < 3; k++) { int y = adj[x][k]; if (dist[s0][y] == 99) { dist[s0][y] = dist[s0][x] + 1; q[t++] = y; } } }
    if (s0 == 0) for (int k = 0; k < n; k++) order[k] = q[k];
  }
  return 1;
}

/* pairing enumeration */
static int pm[MAXN];
static long long cap, tested, failed, undecided;
static char g6[256];
static int mindist = 3;

static void test_current(void) {
  for (int v = 0; v < n; v++) partner[v] = pm[v];
  int r = solve();
  tested++;
  if (r == 0) {
    failed++;
    printf("FAIL %s", g6);
    for (int v = 0; v < n; v++) if (v < pm[v]) printf(" %d-%d", v, pm[v]);
    printf("\n"); fflush(stdout);
  } else if (r < 0) undecided++;
}

static int enum_pm(void) {
  if (cap && tested >= cap) return 1;
  int v = -1;
  for (int x = 0; x < n; x++) if (pm[x] < 0) { v = x; break; }
  if (v < 0) { test_current(); return 0; }
  for (int w = v + 1; w < n; w++) if (pm[w] < 0 && dist[v][w] >= mindist) {
    pm[v] = w; pm[w] = v;
    if (enum_pm()) { pm[v] = pm[w] = -1; return 1; }
    pm[v] = pm[w] = -1;
  }
  return 0;
}

static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rand_pm(void) {
  for (int tr = 0; tr < 200; tr++) {
    for (int v = 0; v < n; v++) pm[v] = -1;
    int ok = 1;
    int perm[MAXN]; for (int i = 0; i < n; i++) perm[i] = i;
    for (int i = n - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    for (int i = 0; i < n && ok; i++) {
      int v = perm[i]; if (pm[v] >= 0) continue;
      int cand[MAXN], c = 0;
      for (int w = 0; w < n; w++) if (w != v && pm[w] < 0 && dist[v][w] >= mindist) cand[c++] = w;
      if (!c) { ok = 0; break; }
      int w = cand[rnd() % c]; pm[v] = w; pm[w] = v;
    }
    if (ok) return 1;
  }
  return 0;
}

int main(int argc, char **argv) {
  const char *mode = argc > 1 ? argv[1] : "all";
  long long N = argc > 2 ? atoll(argv[2]) : 0;
  rs = argc > 3 ? atoll(argv[3]) * 2654435761ULL + 1 : 88172645463325252ULL;
  budget = argc > 4 ? atoll(argv[4]) : 0;
  if (argc > 5) mindist = atoi(argv[5]);
  long long G = 0, Ttot = 0, Ftot = 0, Utot = 0;
  while (scanf("%255s", g6) == 1) {
    if (!parse_g6(g6)) { fprintf(stderr, "bad graph %s\n", g6); continue; }
    G++;
    tested = failed = undecided = 0;
    for (int v = 0; v < n; v++) pm[v] = -1;
    if (!strcmp(mode, "given")) {
      int k; if (scanf("%d", &k) != 1) return 1;
      for (int v = 0; v < n; v++) pm[v] = v;
      for (int i = 0; i < k; i++) { int s, t; if (scanf("%d %d", &s, &t) != 2) return 1; pm[s] = t; pm[t] = s; }
      for (int v = 0; v < n; v++) partner[v] = pm[v];
      int r = solve(); printf("%d\n", r); fflush(stdout); continue;
    }
    if (!strcmp(mode, "all")) { cap = N; enum_pm(); }
    else { for (long long k = 0; k < N; k++) if (rand_pm()) test_current(); }
    Ttot += tested; Ftot += failed; Utot += undecided;
  }
  printf("graphs %lld pairings %lld failures %lld undecided %lld\n", G, Ttot, Ftot, Utot);
  return 0;
}
