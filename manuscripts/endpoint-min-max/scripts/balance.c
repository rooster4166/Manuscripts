/* Balance filter (connections §T.result-4).  Input: "n m u1 v1 ... um vm" then the output of tools/cutfeas.c.
   For a graph (n <= 24) and a list of half-set masks, print those M with
   | |M cap X| - |(Ev - M) cap X| | <= |delta(X)| for every X (the balance condition). */
#include <stdio.h>
#include <stdlib.h>
int main(void) {
  int n, m; if (scanf("%d %d", &n, &m) != 2) return 1;
  unsigned nbr[32] = {0}; int deg[32] = {0};
  for (int i = 0; i < m; i++) { int a, b; scanf("%d %d", &a, &b); nbr[a] |= 1u << b; nbr[b] |= 1u << a; deg[a]++; deg[b]++; }
  unsigned N = 1u << n, Ev = 0;
  for (int v = 0; v < n; v++) if (deg[v] % 2 == 0) Ev |= 1u << v;
  int *cut = malloc(sizeof(int) * N); cut[0] = 0;
  for (unsigned W = 1; W < N; W++) { int low = __builtin_ctz(W); unsigned Wp = W & (W - 1);
    cut[W] = cut[Wp] + deg[low] - 2 * __builtin_popcount(nbr[low] & Wp); }
  int k; long tot = 0, bal = 0;
  while (scanf("%d", &k) == 1) {
    for (int i = 0; i < k; i++) { unsigned M; scanf("%u", &M); tot++;
      unsigned U = Ev & ~M; int ok = 1;
      for (unsigned X = 1; ok && X < N - 1; X++) {
        int d = __builtin_popcount(X & M) - __builtin_popcount(X & U);
        if (d < 0) d = -d;
        if (d > cut[X]) ok = 0;
      }
      if (ok) { bal++; printf("%u\n", M); }
    }
  }
  fprintf(stderr, "half-sets %ld balanced %ld\n", tot, bal);
  return 0;
}
