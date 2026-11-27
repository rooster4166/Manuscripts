/* ts.c -- audit A21: independent exact solver over transition systems.
 *
 * A path decomposition of G with end counts b(v) = d(v) mod 2 (a Lovasz decomposition) is the
 * same thing as a choice, at every vertex v, of a pairing of the edges at v that leaves exactly
 * d(v) mod 2 edges unpaired, such that the trails obtained by following the pairings are paths
 * (no closed trail, no repeated vertex).  We search these choices vertex by vertex, keeping the
 * partial trails ("chains") in a union-find over edges with the vertex set of each chain, and
 * reject a pairing at v of e1,e2 unless chain(e1) != chain(e2) and V(chain e1) & V(chain e2) = {v}.
 * This invariant keeps every chain a path at all times, so a complete assignment is exactly a
 * Lovasz decomposition.  Written from scratch for the audit; it shares no code with pee.c.
 *
 * Input (stdin), one query per line:
 *   n m u1 v1 ... um vm  T x y            -> 1 iff some Lovasz decomposition has xy terminal at x
 *   n m u1 v1 ... um vm  A c k a1 .. ak   -> 1 iff some Lovasz decomposition has Q_c disjoint from {a_i}
 *   n m u1 v1 ... um vm  S k p1 q1 .. pk qk -> 1 iff some Lovasz decomposition has no path
 *                                            containing both p_i and q_i, for every i
 *   n m u1 v1 ... um vm  L                -> 1 iff a Lovasz decomposition exists
 * Output: one line "0" or "1" per query.  Optional argv[1] = node budget: if the search exceeds
 * it, the answer is "2" (undecided); "0" and "1" remain exact.  Without argv[1] there is no budget.
 * Optional argv[2] = R: up to R attempts per query, attempt 0 in the default order and attempts
 * 1..R-1 with the incidence lists shuffled (fixed seed).  An attempt that finishes within the
 * budget is exact in any order (1 = decomposition found, 0 = search exhausted), so the first
 * finished attempt is the answer; "2" only if every attempt hits the budget.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 40
#define MAXM 200
typedef uint64_t u64;

static int n, m, eu[MAXM], ev[MAXM], deg[MAXN], inc[MAXN][MAXN], order[MAXN];
static int par[MAXM], sz[MAXM];
static u64 msk[MAXM];
static int used[MAXM][2];            /* end of edge e at eu (0) / ev (1) assigned */
/* query */
static char qt;
static int qx = -1, qe = -1;          /* T: vertex x and forced end edge */
static int qc = -1, qce = -1;         /* A: vertex c and its end edge (once chosen) */
static u64 qA = 0;
static int nsp, sp[64][2];
/* undo stack */
static int ustk_child[MAXM * 2], ustk_root[MAXM * 2], usp;
static long long budget = -1, nodes = 0;
static int shuffle_round = 0, rounds = 1;
static u64 rng_state = 88172645463325252ULL;
static int aborted = 0;
static u64 ustk_mask[MAXM * 2];

static int find(int e) { while (par[e] != e) e = par[e]; return e; }

static int chain_ok(u64 M) {
  for (int i = 0; i < nsp; i++)
    if ((M >> sp[i][0] & 1) && (M >> sp[i][1] & 1)) return 0;
  if (qce >= 0 && (msk[find(qce)] & qA)) return 0;
  return 1;
}

/* try to pair e1,e2 at v; on success push undo record and return 1 */
static int merge(int e1, int e2, int v) {
  int r1 = find(e1), r2 = find(e2);
  if (r1 == r2) return 0;
  if ((msk[r1] & msk[r2]) != ((u64)1 << v)) return 0;
  if (sz[r1] < sz[r2]) { int t = r1; r1 = r2; r2 = t; }
  ustk_child[usp] = r2; ustk_root[usp] = r1; ustk_mask[usp] = msk[r1]; usp++;
  par[r2] = r1; sz[r1] += sz[r2]; msk[r1] |= msk[r2];
  if (!chain_ok(msk[r1])) {
    usp--; par[r2] = r2; sz[r1] -= sz[r2]; msk[r1] = ustk_mask[usp];
    return 0;
  }
  return 1;
}
static void unmerge(void) {
  usp--;
  int c = ustk_child[usp], r = ustk_root[usp];
  par[c] = c; sz[r] -= sz[c]; msk[r] = ustk_mask[usp];
}

static int side(int e, int v) { return eu[e] == v ? 0 : 1; }

static int solve(int vi);

static int at_vertex(int vi, int need) {
  if (aborted) return 0;
  if (budget >= 0 && ++nodes > budget) { aborted = 1; return 0; }
  int v = order[vi];
  int i, e = -1;
  for (i = 0; i < deg[v]; i++) { int f = inc[v][i]; if (!used[f][side(f, v)]) { e = f; break; } }
  if (e < 0) return need == 0 ? solve(vi + 1) : 0;
  used[e][side(e, v)] = 1;
  /* option 1: e is the unpaired (end) edge at v */
  if (need > 0 && (v != qx || e == qe)) {
    int setc = 0;
    if (v == qc) { qce = e; setc = 1; }
    if (!setc || chain_ok(msk[find(e)]))
      if (at_vertex(vi, need - 1)) { used[e][side(e, v)] = 0; if (setc) qce = -1; return 1; }
    if (setc) qce = -1;
  }
  /* option 2: pair e with a later unused edge f at v */
  if (!(v == qx && e == qe)) {
    for (int j = i + 1; j < deg[v]; j++) {
      int f = inc[v][j];
      if (used[f][side(f, v)]) continue;
      if (v == qx && f == qe) continue;
      used[f][side(f, v)] = 1;
      if (merge(e, f, v)) {
        int r = at_vertex(vi, need);
        unmerge();
        if (r) { used[f][side(f, v)] = 0; used[e][side(e, v)] = 0; return 1; }
      }
      used[f][side(f, v)] = 0;
    }
  }
  used[e][side(e, v)] = 0;
  return 0;
}

static int solve(int vi) {
  if (vi == n) return 1;
  return at_vertex(vi, deg[order[vi]] & 1);
}

static int run(void) {
  for (int v = 0; v < n; v++) deg[v] = 0;
  for (int e = 0; e < m; e++) {
    inc[eu[e]][deg[eu[e]]++] = e; inc[ev[e]][deg[ev[e]]++] = e;
    par[e] = e; sz[e] = 1; msk[e] = ((u64)1 << eu[e]) | ((u64)1 << ev[e]);
    used[e][0] = used[e][1] = 0;
  }
  usp = 0;
  for (int e = 0; e < m; e++) if (!chain_ok(msk[e])) return 0;
  if (shuffle_round > 0)
    for (int v = 0; v < n; v++)
      for (int i = deg[v] - 1; i > 0; i--) {
        rng_state = rng_state * 6364136223846793005ULL + 1442695040888963407ULL;
        int j = (int)((rng_state >> 33) % (u64)(i + 1));
        int t = inc[v][i]; inc[v][i] = inc[v][j]; inc[v][j] = t;
      }
  /* BFS order, starting at the constrained vertex of the query (x, c, or the first separated
     vertex), otherwise at a vertex of maximum degree, so that chains grow locally and local
     obstructions are met near the root of the search */
  int seen[MAXN] = {0}, k = 0;
  int start = qx >= 0 ? qx : qc >= 0 ? qc : nsp > 0 ? sp[0][0] : -1;
  while (k < n) {
    int s = -1;
    if (start >= 0 && !seen[start]) s = start;
    else for (int v = 0; v < n; v++) if (!seen[v] && (s < 0 || deg[v] > deg[s])) s = v;
    int q[MAXN], h = 0, t = 0; q[t++] = s; seen[s] = 1;
    while (h < t) {
      int v = q[h++]; order[k++] = v;
      for (int i = 0; i < deg[v]; i++) {
        int f = inc[v][i], w = eu[f] == v ? ev[f] : eu[f];
        if (!seen[w]) { seen[w] = 1; q[t++] = w; }
      }
    }
  }
  nodes = 0; aborted = 0;
  int r = solve(0);
  return aborted ? 2 : r;
}

int main(int argc, char **argv) {
  if (argc > 1) budget = atoll(argv[1]);
  if (argc > 2) rounds = atoi(argv[2]);
  while (scanf("%d %d", &n, &m) == 2) {
    for (int e = 0; e < m; e++) if (scanf("%d %d", &eu[e], &ev[e]) != 2) return 1;
    char buf[8];
    if (scanf("%7s", buf) != 1) return 1;
    qt = buf[0]; qx = qe = qc = qce = -1; qA = 0; nsp = 0;
    if (qt == 'T') {
      int x, y; if (scanf("%d %d", &x, &y) != 2) return 1;
      qx = x;
      for (int e = 0; e < m; e++) if ((eu[e] == x && ev[e] == y) || (eu[e] == y && ev[e] == x)) qe = e;
      if (qe < 0) { fprintf(stderr, "no edge %d %d\n", x, y); return 1; }
    } else if (qt == 'A') {
      int c, k; if (scanf("%d %d", &c, &k) != 2) return 1;
      qc = c;
      for (int i = 0; i < k; i++) { int a; if (scanf("%d", &a) != 1) return 1; qA |= (u64)1 << a; }
    } else if (qt == 'S') {
      if (scanf("%d", &nsp) != 1) return 1;
      for (int i = 0; i < nsp; i++) if (scanf("%d %d", &sp[i][0], &sp[i][1]) != 2) return 1;
    } else if (qt != 'L') { fprintf(stderr, "bad query\n"); return 1; }
    int res = 2;
    for (shuffle_round = 0; shuffle_round < rounds; shuffle_round++) {
      res = run();
      if (res != 2) break;
    }
    printf("%d\n", res);
    fflush(stdout);
  }
  return 0;
}
