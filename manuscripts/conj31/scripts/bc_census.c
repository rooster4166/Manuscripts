/* bc_census.c -- block criterion (BC) against exact tightness, connected two-even graphs.
 *   bc_census < connected.g6
 * For each connected graph with exactly two vertices of positive even degree:
 * exact tightness (psolve.h) and BC (blockcrit.h, target t = d mod 2).  BC => tight
 * follows from PC; tight => BC is the content tested.  Disagreements are printed.
 */
#include <stdio.h>
#include "psolve.h"
#include "blockcrit.h"
int main(void) {
  char line[256]; long tot = 0, agree = 0, tb = 0, tnb = 0, ntb = 0, ntnb = 0;
  static PS P;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0;
    int n; uint32_t a[PS_MAXN];
    if (!line[0] || !g6_decode(line, &n, a)) continue;
    int t[PS_MAXN], ne = 0;
    for (int x = 0; x < n; x++) { int d = __builtin_popcount(a[x]); t[x] = d & 1; if (d && !(d & 1)) ne++; }
    if (ne != 2) continue;
    tot++;
    int r = ps_solve(&P, n, a, t, 0);
    int c = bc_check(n, a, t);
    if (r == 1 && c) tb++; else if (r == 1) { tnb++; printf("TIGHT_NOT_BC %s\n", line); }
    else if (c) { ntb++; printf("BC_NOT_TIGHT %s\n", line); } else ntnb++;
  }
  printf("two-even %ld: tight&BC %ld tight&notBC %ld nottight&BC %ld nottight&notBC %ld\n", tot, tb, tnb, ntb, ntnb);
  return 0;
}
