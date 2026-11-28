// chainlist.cpp: same as chain.cpp but prints one line per instance: g6 g y x u nD nAvoid nGood
#include "dec.h"
using namespace dec;
int main() {
  char line[256];
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    if (__builtin_popcount(G.evens()) != 1) continue;
    int g = even_vertex(G);
    for (int u = 0; u < G.N; u++) { if (!G.has(g, u)) continue;
      for (int y = 0; y < G.N; y++) { if (G.deg(y) % 2 == 0 || !G.has(y, u)) continue;
        for (int x = 0; x < G.N; x++) {
          if (x == y || x == u || G.deg(x) % 2 == 0 || G.has(x, y)) continue;
          Gr H = G; H.del(g, u);
          long long nD = 0, nAv = 0, nGood = 0;
          enumerate(H, y, 1u << x, 0, [&](const Decomp& D) {
            nD++; std::vector<int> ch; Decomp R = fan_forced(D, g, u, ch);
            if (std::find(ch.begin(), ch.end(), y) == ch.end()) nAv++;
            if (path_avoids(R[path_end_at(R, y)], 1u << x)) nGood++;
            return false; });
          if (nD) printf("%s %d %d %d %d %lld %lld %lld\n", line, g, y, x, u, nD, nAv, nGood);
        }
      }
    }
  }
}
