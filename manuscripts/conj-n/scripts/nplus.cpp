// nplus.cpp: for N instances, is (G, y, {x}, N(x)) good (Q_y avoids x and does not end next to x)?
#include "orcb.h"
int main() {
  char line[256]; long long tot = 0, ok = 0, okg = 0, totg = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    if (__builtin_popcount(G.evens()) > 1) continue;
    int g = even_vertex(G);
    for (int y = 0; y < G.N; y++) { if (G.deg(y) % 2 == 0) continue;
      for (int x = 0; x < G.N; x++) {
        if (x == y || G.deg(x) % 2 == 0 || G.has(x, y)) continue;
        uint32_t W = G.adj[y] & ~G.adj[x]; if (g >= 0) W &= ~(1u << g);
        if (!W) continue;
        tot++; bool xg = g >= 0 && G.has(g, x); totg += xg;
        int r = orcb::avoidB(G, y, 1u << x, G.adj[x]);
        if (r == 1) { ok++; okg += xg; } else if (tot - ok < 20) printf("NPFAIL %s g=%d y=%d x=%d r=%d\n", line, g, y, x, r);
      }
    }
  }
  printf("NPLUS total=%lld ok=%lld  (x~g: %lld ok %lld)\n", tot, ok, totg, okg);
}
