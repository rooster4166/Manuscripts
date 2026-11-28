/* t31.c -- Conjecture 31 (two-even tightness) over a graph6 stream.
 *
 *   t31 MODE [witness_file] < graphs.g6
 *
 * For every graph with exactly two vertices of positive even degree and no
 * isolated vertex, decide tightness: a partition of E into paths with one end
 * at each odd vertex and none at the two even vertices.
 *   MODE census : solve every such graph; classify the non-tight ones as
 *                 O1 (odd vertex of degree n-1), and otherwise by 2-connectivity.
 *   MODE c31    : skip graphs with an odd vertex of degree n-1 (proved obstruction)
 *                 and solve the rest; report every non-tight one.
 * Witnesses (one line per tight graph: g6 then paths "a-b-c ...") go to
 * witness_file when given.  Exit summary on stderr and stdout.
 */
#include <stdio.h>
#include "psolve.h"

static int is2conn(int n, const uint32_t *adj) {
  /* n >= 3, connected and no cut vertex */
  for (int c = -1; c < n; c++) {
    uint32_t all = ((n == 32) ? 0xffffffffu : ((1u << n) - 1));
    if (c >= 0) all &= ~(1u << c);
    int st = (c == 0) ? 1 : 0;
    uint32_t comp = 1u << st, fr = comp;
    while (fr) {
      int y = __builtin_ctz(fr); fr &= fr - 1;
      uint32_t nb = adj[y] & all & ~comp;
      comp |= nb; fr |= nb;
    }
    if (comp != all) return 0;
  }
  return 1;
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: t31 census|c31 [witness]\n"); return 1; }
  int census = (argv[1][0] == 'c' && argv[1][1] == 'e');
  FILE *W = (argc > 2) ? fopen(argv[2], "w") : NULL;
  char line[512];
  long tot = 0, twoeven = 0, o1 = 0, solved = 0, tight = 0, nt_o1 = 0, nt_2c = 0, nt_cut = 0, und = 0;
  long maxnodes = 0;
  static PS P;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0;
    if (!line[0]) continue;
    int n; uint32_t adj[PS_MAXN];
    if (!g6_decode(line, &n, adj)) continue;
    tot++;
    int b[PS_MAXN], ne = 0, iso = 0, univ = 0;
    for (int x = 0; x < n; x++) {
      int d = __builtin_popcount(adj[x]);
      if (d == 0) iso = 1;
      if (d > 0 && d % 2 == 0) ne++;
      b[x] = d & 1;
      if ((d & 1) && d == n - 1) univ = 1;
    }
    if (iso || ne != 2) continue;
    twoeven++;
    if (univ) o1++;
    if (univ && !census) continue;
    solved++;
    int r = ps_solve(&P, n, adj, b, 0);
    if (P.nodes > maxnodes) maxnodes = P.nodes;
    if (r == 1) {
      tight++;
      if (W) {
        fprintf(W, "%s", line);
        for (int i = 0; i < P.npaths; i++) {
          fputc(' ', W);
          for (int j = 0; j < P.plen[i]; j++) fprintf(W, j ? "-%d" : "%d", P.pv[i][j]);
        }
        fputc('\n', W);
      }
    } else if (r == 0) {
      int c2 = is2conn(n, adj);
      if (univ) nt_o1++;
      else if (c2) { nt_2c++; printf("NONTIGHT_2CONN %s\n", line); fflush(stdout); }
      else { nt_cut++; if (!census) printf("NONTIGHT_CUT %s\n", line); }
      if (census && !univ) printf("NONTIGHT %s %s\n", c2 ? "2conn" : "cut", line);
    } else und++;
  }
  if (W) fclose(W);
  printf("graphs %ld two-even %ld O1 %ld solved %ld tight %ld nontight: O1 %ld 2conn-nonO1 %ld cut-nonO1 %ld undecided %ld maxnodes %ld\n",
         tot, twoeven, o1, solved, tight, nt_o1, nt_2c, nt_cut, und, maxnodes);
  return 0;
}
