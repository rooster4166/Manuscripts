/* ndq.c -- line interface to ndsolve.h, in the format of route_ext query C (for cross-checks):
   C n m u1 v1 ... um vm b0 .. b_{n-1} r0 .. r_{n-1}   with b_v in {0,1}; prints 1 or 0. */
#include <stdio.h>
#include "ndsolve.h"
int main(void) {
  char tag[8];
  while (scanf("%7s", tag) == 1) {
    int n, m; if (scanf("%d %d", &n, &m) != 2) return 1;
    sinit(n);
    for (int e = 0; e < m; e++) { int u, v; if (scanf("%d %d", &u, &v) != 2) return 1; sadd(u, v); }
    for (int v = 0; v < n; v++) { int b; if (scanf("%d", &b) != 1) return 1; if (b) sneed |= 1u << v; }
    for (int v = 0; v < n; v++) { unsigned long long x; if (scanf("%llu", &x) != 1) return 1; crv[v] = (u32)x | (1u << v); }
    printf("%d\n", srun());
    fflush(stdout);
  }
  return 0;
}
