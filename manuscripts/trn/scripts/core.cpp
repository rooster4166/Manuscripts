// core.cpp: count TRN tests (child good) at the instances reached by N's induction (the core of
// manuscript Definition 5.1): all-tight, child witness w in N(y)\N(x), w != u, x,y with a common
// neighbour, N(g) not an independent pair.  Also reports y~g / y!~g and d(g) in the core.
#include "lind.h"
int main() {
  char line[256]; long long tot[2] = {0,0}, core[2] = {0,0}, byd[2][20]; memset(byd, 0, sizeof byd);
  long long excl_tight = 0, excl_wit = 0, excl_far = 0, excl_ind = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    if (__builtin_popcount(G.evens()) != 1) continue;
    int g = even_vertex(G);
    bool ind = false;
    if (G.deg(g) == 2) { int a = __builtin_ctz(G.adj[g]), b = 31 - __builtin_clz(G.adj[g]); ind = !G.has(a, b); }
    for (int y = 0; y < G.N; y++) { if (G.deg(y) % 2 == 0) continue;
      for (int x = 0; x < G.N; x++) {
        if (x == y || G.deg(x) % 2 == 0 || G.has(x, y)) continue;
        bool tight = true;
        for (int v = 0; v < G.N; v++) if (G.has(g, v) && v != x && v != y && !G.has(y, v)) tight = false;
        bool cn = (G.adj[x] & G.adj[y]) != 0;
        for (int u = 0; u < G.N; u++) {
          if (u == x || !G.has(g, u) || !G.has(y, u)) continue;
          Gr H = G; H.del(g, u);
          if (orc::avoid(H, y, 1u << x) != 1) continue;
          int a = G.has(g, y); tot[a]++;
          bool wit = (G.adj[y] & ~G.adj[x] & ~(1u << u)) != 0;
          if (!tight) { excl_tight++; continue; }
          if (!wit) { excl_wit++; continue; }
          if (!cn) { excl_far++; continue; }
          if (ind) { excl_ind++; continue; }
          core[a]++; byd[a][G.deg(g)]++;
        }
      }
    }
  }
  printf("TRN tests y!~g=%lld y~g=%lld; core y!~g=%lld y~g=%lld; excluded: not all-tight %lld, no child witness %lld, distance>=3 %lld, d(g)=2 independent %lld\n",
         tot[0], tot[1], core[0], core[1], excl_tight, excl_wit, excl_far, excl_ind);
  for (int a = 0; a < 2; a++) { printf("core y%sg by d(g):", a ? "~" : "!~"); for (int d = 0; d < 20; d++) if (byd[a][d]) printf(" %d:%lld", d, byd[a][d]); printf("\n"); }
}
