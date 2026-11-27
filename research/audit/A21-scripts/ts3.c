/* ts3.c -- audit A21: ts.c plus forward checking (function fc below).
 * ts.c -- audit A21: independent exact solver over transition systems.
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
 * Output: one line "0" or "1" per query.
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

/* ---- forward checking (ts3 only) ----
   Two unassigned ends e1, e2 at an unprocessed vertex v are mergeable now if their chains differ,
   meet only in v, and the union passes chain_ok.  Chains only grow, so mergeability only
   decreases; and an end may stay unpaired at v only if d(v) is odd and (v != x or it is xy) and
   (v != c or its chain avoids A).  Hence if, at some unprocessed vertex, the unassigned ends admit
   no pairing of the required shape in the current mergeability graph, no completion exists. */
static int merge_ok_now(int e1, int e2, int v) {
  int r1 = find(e1), r2 = find(e2);
  if (r1 == r2) return 0;
  if ((msk[r1] & msk[r2]) != ((u64)1 << v)) return 0;
  u64 M = msk[r1] | msk[r2];
  for (int i = 0; i < nsp; i++) if ((M >> sp[i][0] & 1) && (M >> sp[i][1] & 1)) return 0;
  if (qce >= 0) { int rc = find(qce); if ((rc == r1 || rc == r2) && (M & qA)) return 0; }
  return 1;
}
static int adjm[MAXN], unp_ok;
static signed char dpm[1 << 12][2];
static int ends_k;
static int match_dp(int S, int need) {
  if (!S) return need == 0;
  if (dpm[S][need] >= 0) return dpm[S][need];
  int i = __builtin_ctz(S), r = 0, S1 = S & ~(1 << i);
  if (need && (unp_ok >> i & 1) && match_dp(S1, 0)) r = 1;
  for (int j = i + 1; !r && j < ends_k; j++)
    if ((S1 >> j & 1) && (adjm[i] >> j & 1) && match_dp(S1 & ~(1 << j), need)) r = 1;
  dpm[S][need] = (signed char)r;
  return r;
}
static int fc_vertex(int v, int need) {
  int E[MAXN], k = 0;
  for (int i = 0; i < deg[v]; i++) { int f = inc[v][i]; if (!used[f][side(f, v)]) E[k++] = f; }
  if (k == 0) return need == 0;
  if (k > 12) return 1;                     /* too large to check: no pruning */
  ends_k = k; unp_ok = 0;
  for (int i = 0; i < k; i++) {
    adjm[i] = 0;
    for (int j = 0; j < k; j++) if (j != i && merge_ok_now(E[i], E[j], v)) adjm[i] |= 1 << j;
    int ok = (v != qx || E[i] == qe);
    if (ok && v == qc && (msk[find(E[i])] & qA)) ok = 0;
    if (ok) unp_ok |= 1 << i;
  }
  for (int S = 0; S < (1 << k); S++) dpm[S][0] = dpm[S][1] = -1;
  return match_dp((1 << k) - 1, need);
}
static int fc(int from) {
  for (int j = from; j < n; j++) if (!fc_vertex(order[j], deg[order[j]] & 1)) return 0;
  return 1;
}

static int at_vertex(int vi, int need) {
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
        int r = fc(vi + 1) ? at_vertex(vi, need) : 0;
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
  if (!fc(vi)) return 0;
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
  return solve(0);
}

int main(void) {
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
    printf("%d\n", run());
    fflush(stdout);
  }
  return 0;
}
