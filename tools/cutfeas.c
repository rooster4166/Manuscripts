/* Cut-feasible half-sets (endpoint min-max programme; even-degrees.pdf §12.4, inequality (1)).

   Input (stdin), one graph per line:  n m u1 v1 ... um vm      (n <= 20, n even)
   Output, one line per graph: the number of cut-feasible half-sets, then their bitmasks over V.

   A half-set M (|M| = e/2 of the e even vertices of positive degree) gives the simple profile
   b = 1 on odd vertices, 2 on M, 0 on the other even vertices.  It is cut-feasible if
       b(W) <= |delta(W)| + 2k - d(v) - b(v)   for every v and every W subset of V - v,
   with 2k = n.  For each W we only need the smallest slack s(v) = 2k - d(v) - b(v) over v not in
   W, so the test costs O(2^n) per half-set after an O(2^n n) precomputation. */
#include <stdio.h>
#include <stdlib.h>

int main(void) {
  int n, m;
  while (scanf("%d %d", &n, &m) == 2) {
    int deg[32] = {0};
    unsigned nbr[32] = {0};
    for (int i = 0; i < m; i++) {
      int a, b;
      if (scanf("%d %d", &a, &b) != 2) return 1;
      nbr[a] |= 1u << b; nbr[b] |= 1u << a; deg[a]++; deg[b]++;
    }
    int k = n / 2;
    unsigned N = 1u << n;
    int *cut = malloc(sizeof(int) * N);
    int *oddc = malloc(sizeof(int) * N);
    cut[0] = 0; oddc[0] = 0;
    for (unsigned W = 1; W < N; W++) {
      int low = __builtin_ctz(W);
      unsigned Wp = W & (W - 1);
      int inside = __builtin_popcount(nbr[low] & Wp);
      cut[W] = cut[Wp] + deg[low] - 2 * inside;
      oddc[W] = oddc[Wp] + (deg[low] & 1);
    }
    int ev[32], e = 0;
    for (int v = 0; v < n; v++) if (deg[v] > 0 && deg[v] % 2 == 0) ev[e++] = v;
    int cnt = 0;
    unsigned *out = malloc(sizeof(unsigned) * (1u << (e > 0 ? e : 1)));
    for (unsigned s = 0; s < (1u << e); s++) {
      if (__builtin_popcount(s) != e / 2) continue;
      unsigned M = 0;
      for (int i = 0; i < e; i++) if (s >> i & 1) M |= 1u << ev[i];
      int slack[32], ok = 1;
      for (int v = 0; v < n; v++) {
        int bv = (deg[v] & 1) ? 1 : ((M >> v & 1) ? 2 : 0);
        slack[v] = 2 * k - deg[v] - bv;
        if (slack[v] < 0 || bv > deg[v]) ok = 0;
      }
      for (unsigned W = 1; ok && W < N - 1; W++) {
        int bW = oddc[W] + 2 * __builtin_popcount(W & M);
        int ex = bW - cut[W];
        if (ex <= 0) continue;
        int mn = 1 << 30;
        for (int v = 0; v < n; v++) if (!(W >> v & 1) && slack[v] < mn) mn = slack[v];
        if (ex > mn) ok = 0;
      }
      if (ok) out[cnt++] = M;
    }
    printf("%d", cnt);
    for (int i = 0; i < cnt; i++) printf(" %u", out[i]);
    printf("\n");
    fflush(stdout);
    free(cut); free(oddc); free(out);
  }
  return 0;
}
