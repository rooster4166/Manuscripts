/* Cap functions of the cut inequalities (endpoint min-max programme).

   Input: lines "n m u1 v1 ... um vm" (n even, n <= 20).  Even vertices are indexed 0..e-1.
   Every inequality (1), b(W) <= |delta(W)| + 2k - d(v) - b(v) with v outside W, is an upper bound
   on the number of marks in X = (W u {v}) n Ev:
       v even:  2|M n X| <= |delta(W)| + 2k - d(v) - odd(W)
       v odd:   2|M n X| <= |delta(W)| + 2k - d(v) - 1 - odd(W)        (here X = W n Ev)
   Let f(X) be the least such bound (and at most |X|).  A half-set is cut-feasible iff it is
   independent for these caps.  Output per graph, space separated:
       e  rawSub  famMatroid  rank  nviol  witness
   rawSub = 1 if f is submodular (local test f(X+a)+f(X+b) >= f(X+a+b)+f(X)),
   famMatroid = 1 if the independent sets {I : |I n X| <= f(X) for all X} form a matroid
   (rank function submodular), rank = the largest independent set. */
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
    int *cut = malloc(sizeof(int) * N), *oddc = malloc(sizeof(int) * N);
    cut[0] = 0; oddc[0] = 0;
    for (unsigned W = 1; W < N; W++) {
      int low = __builtin_ctz(W);
      unsigned Wp = W & (W - 1);
      int inside = __builtin_popcount(nbr[low] & Wp);
      cut[W] = cut[Wp] + deg[low] - 2 * inside;
      oddc[W] = oddc[Wp] + (deg[low] & 1);
    }
    int ev[32], idx[32], e = 0;
    for (int v = 0; v < n; v++) { idx[v] = -1; if (deg[v] > 0 && deg[v] % 2 == 0) { idx[v] = e; ev[e++] = v; } }
    unsigned E = 1u << e;
    int *f = malloc(sizeof(int) * E);
    for (unsigned X = 0; X < E; X++) f[X] = __builtin_popcount(X);
    for (int v = 0; v < n; v++) {
      for (unsigned W = 0; W < N; W++) {
        if (W >> v & 1) continue;
        int rhs = cut[W] + 2 * k - deg[v] - oddc[W] - (deg[v] & 1);
        unsigned X = 0;
        for (int i = 0; i < e; i++) if (W >> ev[i] & 1) X |= 1u << i;
        if (idx[v] >= 0) X |= 1u << idx[v];
        int bound = rhs >= 0 ? rhs / 2 : -1;   /* rhs < 0 means infeasible for any marks */
        if (bound < f[X]) f[X] = bound;
      }
    }
    /* raw submodularity */
    int rawSub = 1, nviol = 0; unsigned wit = 0;
    for (unsigned X = 0; X < E && rawSub >= 0; X++)
      for (int a = 0; a < e; a++) {
        if (X >> a & 1) continue;
        for (int b = a + 1; b < e; b++) {
          if (X >> b & 1) continue;
          unsigned A = X | 1u << a, B = X | 1u << b;
          if (f[A] + f[B] < f[A | B] + f[X]) { rawSub = 0; nviol++; wit = X; }
        }
      }
    /* independent sets and rank */
    char *ind = malloc(E);
    for (unsigned I = 0; I < E; I++) {
      ind[I] = 1;
      /* I is independent iff |I n X| <= f(X) for every X (f need not be monotone: test all X) */
      for (unsigned X = 0; X < E && ind[I]; X++)
        if (__builtin_popcount(I & X) > f[X]) ind[I] = 0;
    }
    int *r = malloc(sizeof(int) * E);
    for (unsigned X = 0; X < E; X++) {
      int best = 0;
      for (unsigned I = X;; I = (I - 1) & X) {
        if (ind[I] && __builtin_popcount(I) > best) best = __builtin_popcount(I);
        if (I == 0) break;
      }
      r[X] = best;
    }
    int famMat = 1;
    for (unsigned X = 0; X < E && famMat; X++)
      for (int a = 0; a < e && famMat; a++) {
        if (X >> a & 1) continue;
        for (int b = a + 1; b < e; b++) {
          if (X >> b & 1) continue;
          unsigned A = X | 1u << a, B = X | 1u << b;
          if (r[A] + r[B] < r[A | B] + r[X]) { famMat = 0; break; }
        }
      }
    int pure = 1; unsigned pwit = 0;
    for (unsigned I = 0; I < E; I++) {
      if (!ind[I]) continue;
      int maximal = 1;
      for (int a = 0; a < e; a++) if (!(I >> a & 1) && ind[I | 1u << a]) { maximal = 0; break; }
      if (maximal && __builtin_popcount(I) < r[E - 1]) { pure = 0; pwit = I; }
    }
    /* is every singleton independent? */
    int single = 1;
    for (int a = 0; a < e; a++) if (!ind[1u << a]) single = 0;
    printf("%d %d %d %d %d %u %d %u %d\n", e, rawSub, famMat, r[E - 1], nviol, wit, pure, pwit, single);
    fflush(stdout);
    free(cut); free(oddc); free(f); free(ind); free(r);
  }
  return 0;
}
