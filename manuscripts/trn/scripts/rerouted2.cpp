// rerouted2.cpp: count good D' (over all TRN tests) in which the forced chain re-routes some path at
// both of its ends, i.e. some path of D' has both ends among the re-routed chain vertices x_0..x_{k-1}
// (Section 2, the remark after the re-routing rule).
#include "dec.h"
using namespace dec;
int main() {
  char line[256]; long long tot = 0, twice = 0;
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
          enumerate(H, y, 1u << x, 0, [&](const Decomp& D) {
            tot++; std::vector<int> ch; fan_forced(D, g, u, ch);
            uint32_t re = 0; for (size_t j = 0; j + 1 < ch.size(); j++) re |= 1u << ch[j];   // x_0..x_{k-1}
            for (auto& p : D) if (p.size() >= 2 && (re >> p.front() & 1) && (re >> p.back() & 1)) { twice++; break; }
            return false; });
        }
      }
    }
  }
  printf("good D' %lld, with a path re-routed at both ends %lld\n", tot, twice);
}
