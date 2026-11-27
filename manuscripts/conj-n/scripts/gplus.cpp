// gplus.cpp: is (G, c, {g}, N(g)) good for every odd c not in N[g]?  (Q_c avoids g, far end not next to g)
#include "orcb.h"
int main() {
  char line[256]; long long tot = 0, ok = 0, ok0 = 0; int pr = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    if (__builtin_popcount(G.evens()) != 1) continue;
    int g = even_vertex(G);
    for (int c = 0; c < G.N; c++) { if (G.deg(c) % 2 == 0 || c == g || G.has(c, g)) continue;
      tot++;
      int r = orcb::avoidB(G, c, 1u << g, G.adj[g]);
      int r0 = orcb::avoidB(G, c, 1u << g, 0);
      ok += r == 1; ok0 += r0 == 1;
      if (r != 1 && pr++ < 10) printf("GPFAIL %s g=%d c=%d plain=%d\n", line, g, c, r0);
    }
  }
  printf("GPLUS total=%lld far_ok=%lld plain_ok=%lld\n", tot, ok, ok0);
}
