// nadj.cpp: all-odd graphs: x ~ y, y has a neighbour w != x with w !~ x.  Is (G, y, {x}) good?
#include "orcb.h"
int main() {
  char line[256]; long long tot = 0, ok = 0; int pr = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    if (__builtin_popcount(G.evens()) != 0) continue;
    for (int y = 0; y < G.N; y++) for (int x = 0; x < G.N; x++) {
      if (x == y || !G.has(x, y)) continue;
      uint32_t W = G.adj[y] & ~G.adj[x] & ~(1u << x); if (!W) continue;
      tot++;
      int r = orc::avoid(G, y, 1u << x);
      if (r == 1) ok++; else if (pr++ < 10) printf("NADJFAIL %s y=%d x=%d r=%d\n", line, y, x, r);
    }
  }
  printf("NADJ total=%lld ok=%lld\n", tot, ok);
}
