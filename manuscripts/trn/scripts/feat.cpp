// feat.cpp: per TRN instance: features and whether every good D' succeeds (plain Fan image good).
#include "dec.h"
using namespace dec;
int main() {
  char line[256];
  printf("g6 g y x u adj dg du dy dx xu xg ngu nxy nD nGood nAv\n");
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    if (__builtin_popcount(G.evens()) != 1) continue;
    int g = even_vertex(G), n = G.N;
    for (int u = 0; u < n; u++) { if (!G.has(g, u)) continue;
      Gr H = G; H.del(g, u);
      for (int y = 0; y < n; y++) { if (G.deg(y) % 2 == 0 || !G.has(y, u)) continue;
        for (int x = 0; x < n; x++) {
          if (x == y || x == u || G.deg(x) % 2 == 0 || G.has(x, y)) continue;
          long long nD = 0, nG = 0, nA = 0;
          enumerate(H, y, 1u << x, 0, [&](const Decomp& D) {
            nD++; std::vector<int> ch; Decomp R = fan_forced(D, g, u, ch);
            if (std::find(ch.begin(), ch.end(), y) == ch.end()) nA++;
            if (path_avoids(R[path_end_at(R, y)], 1u << x)) nG++; return false; });
          if (!nD) continue;
          printf("%s %d %d %d %d %d %d %d %d %d %d %d %d %d %lld %lld %lld\n", line, g, y, x, u, (int)G.has(g, y), G.deg(g), G.deg(u), G.deg(y), G.deg(x),
                 (int)G.has(x, u), (int)G.has(x, g), __builtin_popcount(G.adj[g] & G.adj[u]), __builtin_popcount(G.adj[x] & G.adj[y]), nD, nG, nA);
        }
      }
    }
  }
}
