/* Transitions of Hamiltonian decompositions of 4-regular graphs (endpoint-min-max, gadgets).

   A Hamiltonian decomposition of a 4-regular graph G is a partition of E(G) into two
   Hamiltonian cycles.  At a vertex w with neighbours a < b < c < d it induces a *transition*,
   the pairing of the four edges at w into the two cycles:  0 = {ab|cd}, 1 = {ac|bd}, 2 = {ad|bc}.

   Why: if every Hamiltonian decomposition of G uses the same transition {x1 x2 | o1 o2} at w, then
   D = G - w with ports x1, x2 is a joined-forcing gadget for the profile b = 1 on o1, o2 and 0
   elsewhere (both paths of a realisation of D + l1 x1 + l2 x2 are Hamiltonian in D, and closing
   them through w gives a Hamiltonian decomposition of G).

   Input: graph6 lines (4-regular graphs, e.g. nauty-geng -c -d4 -D4 n).
   Output: for every graph with at least one Hamiltonian decomposition, the number of
   decompositions and, for each vertex, the set of transitions used (bit mask over 0,1,2).
   Lines start with FORCED if some vertex uses exactly one transition.  With argv[1] = "forced"
   only those lines are printed.  Tally on stderr: graphs, decomposable, with a forced vertex. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 24

static int n;
static unsigned adj[MAXN];
static int nb[MAXN][4];
static unsigned onC[MAXN];   /* onC[v]: neighbours joined to v by an edge of the current cycle */
static int path[MAXN];
static long ndec;
static int seen[MAXN];        /* transition bit masks */

static int tr_of(int v, int p, int q) {
  /* index of the transition at v whose one class is {p, q} */
  int i = -1, j = -1;
  for (int t = 0; t < 4; t++) { if (nb[v][t] == p) i = t; if (nb[v][t] == q) j = t; }
  if (i > j) { int s = i; i = j; j = s; }
  /* pairs: (0,1)|(2,3) -> 0 ; (0,2)|(1,3) -> 1 ; (0,3)|(1,2) -> 2 */
  static const int T[4][4] = {{-1, 0, 1, 2}, {0, -1, 2, 1}, {1, 2, -1, 0}, {2, 1, 0, -1}};
  return T[i][j];
}

static void check_cycle(void) {
  /* the complement of the current Hamiltonian cycle is 2-regular; is it one cycle? */
  int start = 0, prev = -1, cur = 0, len = 0;
  do {
    unsigned rest = adj[cur] & ~onC[cur];
    int nxt = -1;
    while (rest) {
      int y = __builtin_ctz(rest); rest &= rest - 1;
      if (y != prev) { nxt = y; break; }
    }
    if (nxt < 0) return;
    prev = cur; cur = nxt; len++;
    if (len > n) return;
  } while (cur != start);
  if (len != n) return;
  ndec++;
  for (int v = 0; v < n; v++) {
    unsigned c = onC[v];
    int p = __builtin_ctz(c); c &= c - 1; int q = __builtin_ctz(c);
    seen[v] |= 1 << tr_of(v, p, q);
  }
}

static void dfs(int len, unsigned vis) {
  int c = path[len - 1];
  if (len == n) {
    if (adj[c] >> 0 & 1 && path[1] != c) {
      onC[c] |= 1u; onC[0] |= 1u << c;
      check_cycle();
      onC[c] &= ~1u; onC[0] &= ~(1u << c);
    }
    return;
  }
  unsigned cand = adj[c] & ~vis;
  while (cand) {
    int y = __builtin_ctz(cand); cand &= cand - 1;
    path[len] = y;
    onC[c] |= 1u << y; onC[y] |= 1u << c;
    dfs(len + 1, vis | (1u << y));
    onC[c] &= ~(1u << y); onC[y] &= ~(1u << c);
  }
}

int main(int argc, char **argv) {
  int only = argc > 1 && strcmp(argv[1], "forced") == 0;
  char line[256];
  long graphs = 0, dec = 0, forced = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0;
    if (line[0] < 63) continue;
    n = line[0] - 63;
    if (n > MAXN) continue;
    for (int i = 0; i < n; i++) adj[i] = 0;
    int k = 1, have = 0, val = 0;
    for (int j = 1; j < n; j++)
      for (int i = 0; i < j; i++) {
        if (!have) { val = line[k++] - 63; have = 6; }
        have--;
        if (val >> have & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
      }
    int bad = 0;
    for (int v = 0; v < n; v++) {
      if (__builtin_popcount(adj[v]) != 4) bad = 1;
      unsigned a = adj[v];
      for (int t = 0; t < 4 && a; t++) { nb[v][t] = __builtin_ctz(a); a &= a - 1; }
    }
    if (bad) continue;
    graphs++;
    ndec = 0;
    memset(seen, 0, sizeof seen);
    memset(onC, 0, sizeof onC);
    /* Hamiltonian cycles through the edge 0 - nb[0][0], traversed from 0 to nb[0][0]:
       each decomposition is counted once (its cycle through that edge). */
    path[0] = 0; path[1] = nb[0][0];
    onC[0] |= 1u << nb[0][0]; onC[nb[0][0]] |= 1u;
    dfs(2, 1u | (1u << nb[0][0]));
    onC[0] = 0; onC[nb[0][0]] = 0;
    if (!ndec) continue;
    dec++;
    int f = 0;
    for (int v = 0; v < n; v++) if (__builtin_popcount(seen[v]) == 1) f = 1;
    forced += f;
    if (only && !f) continue;
    printf("%s %s decs=%ld trans=", f ? "FORCED" : "free", line, ndec);
    for (int v = 0; v < n; v++) printf("%d", seen[v]);
    printf("\n");
  }
  fprintf(stderr, "graphs %ld decomposable %ld forced %ld\n", graphs, dec, forced);
  return 0;
}
