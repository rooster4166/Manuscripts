// clean.cpp: does every TRN instance have a good D' that is y-clean (x notin P_y, the path through yu)?
#include "dec.h"
using namespace dec;
int main(int argc, char** argv) {
  char line[256]; long long inst[2] = {0,0}, cl[2] = {0,0}; int pr = argc > 1 ? atoi(argv[1]) : 0;
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
          long long nD = 0; bool c = false;
          enumerate(H, y, 1u << x, 0, [&](const Decomp& D) {
            nD++;
            for (auto& p : D) for (size_t j = 0; j + 1 < p.size(); j++)
              if ((p[j] == y && p[j+1] == u) || (p[j] == u && p[j+1] == y)) { if (path_avoids(p, 1u << x)) c = true; }
            return c; });
          if (!nD) continue;
          int a = G.has(g, y); inst[a]++; cl[a] += c;
          if (!c && pr) printf("NOCLEAN %s g=%d y=%d x=%d u=%d\n", line, g, y, x, u);
        }
      }
    }
  }
  printf("instances y!~g %lld (y-clean %lld)  y~g %lld (y-clean %lld)\n", inst[0], cl[0], inst[1], cl[1]);
}
