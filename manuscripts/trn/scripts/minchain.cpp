// minchain.cpp: distribution of the minimum forced-chain length over good D', and of the chain
// length of D' whose chain hits y.
#include "dec.h"
using namespace dec;
int main(int argc, char** argv) {
  char line[256]; long long dist[2][20]; memset(dist, 0, sizeof dist); long long hitlen[2][20]; memset(hitlen, 0, sizeof hitlen);
  int pr = argc > 1 ? atoi(argv[1]) : 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    if (__builtin_popcount(G.evens()) != 1) continue;
    int g = even_vertex(G);
    for (int u = 0; u < G.N; u++) { if (!G.has(g, u)) continue;
      Gr H = G; H.del(g, u);
      for (int y = 0; y < G.N; y++) { if (G.deg(y) % 2 == 0 || !G.has(y, u)) continue;
        for (int x = 0; x < G.N; x++) {
          if (x == y || x == u || G.deg(x) % 2 == 0 || G.has(x, y)) continue;
          int mn = 99; long long nD = 0;
          enumerate(H, y, 1u << x, 0, [&](const Decomp& D) {
            nD++; std::vector<int> ch; fan_forced(D, g, u, ch);
            mn = std::min(mn, (int)ch.size());
            int adj = G.has(g, y);
            if (std::find(ch.begin(), ch.end(), y) != ch.end()) hitlen[adj][ch.size()]++;
            return false; });
          if (!nD) continue;
          dist[G.has(g, y)][mn]++;
          if (pr && mn >= pr) printf("MIN %d %s g=%d y=%d x=%d u=%d\n", mn, line, g, y, x, u);
        }
      }
    }
  }
  for (int a = 0; a < 2; a++) { printf("y%sg min chain len:", a ? "~" : "!~"); for (int k = 1; k < 20; k++) if (dist[a][k]) printf(" %d:%lld", k, dist[a][k]); printf("\n"); }
  for (int a = 0; a < 2; a++) { printf("y%sg hitting chain len:", a ? "~" : "!~"); for (int k = 1; k < 20; k++) if (hitlen[a][k]) printf(" %d:%lld", k, hitlen[a][k]); printf("\n"); }
}
