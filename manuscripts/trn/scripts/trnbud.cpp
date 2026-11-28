// trnbud.cpp: TRN and TRN-E with a node budget (for larger random graphs).
#include "orc2.h"
int main(int argc, char** argv) {
  unsigned long long bud = argc > 1 ? atoll(argv[1]) : 2000000;
  char line[512]; long long t = 0, viol = 0, und = 0, e1 = 0, eund = 0, skip = 0;
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
          orc::budget = bud; int h = orc::avoid(H, y, 1u << x);
          if (h == 2) { skip++; continue; } if (h != 1) continue;
          t++;
          int s2[2] = {y, g}; uint32_t f2[2] = {1u << x, 1u << u};
          int r = orc2::query(H, 2, s2, f2);
          if (r == 1) { e1++; continue; } if (r == 2) eund++;
          int w = orc::avoid(G, y, 1u << x);
          if (w == 2) und++; else if (w != 1) { viol++; printf("TRN_VIOL %s g=%d y=%d x=%d u=%d\n", line, g, y, x, u); fflush(stdout); }
          if (r == 0) { printf("NOTRNE %s g=%d y=%d x=%d u=%d trn=%d\n", line, g, y, x, u, w); fflush(stdout); }
        }
      }
    }
  }
  printf("SUMMARY TRN tests=%lld viol=%lld undecided=%lld (child undecided %lld); TRN-E holds %lld, undecided %lld\n", t, viol, und, skip, e1, eund);
}
