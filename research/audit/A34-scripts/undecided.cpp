// undecided.cpp (audit A34): find the TRN tests of a graph6 list where the authors' orc2 TRN_E query
// hits the node budget (as in trnbud.cpp), and re-decide them with a larger budget.  Uses the
// authors' oracle headers (identification only).  Also lists the child-undecided candidates.
#include "orc2.h"
int main(int argc, char** argv) {
  unsigned long long bud = argc > 1 ? atoll(argv[1]) : 2000000, big = argc > 2 ? atoll(argv[2]) : 0; bool redecideChild = argc > 3 ? atoi(argv[3]) : 1;
  char line[512]; long long childUnd = 0, childUndBig = 0, childUndGood = 0;
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
          if (h == 2) { childUnd++; if (redecideChild) { orc::budget = big; int h2 = orc::avoid(H, y, 1u << x); if (h2 == 2) childUndBig++; else if (h2 == 1) { childUndGood++;
                  int s2[2] = {y, g}; uint32_t f2[2] = {1u << x, 1u << u}; orc::budget = big; int r = orc2::query(H, 2, s2, f2);
                  printf("CHILDUND %s g=%d y=%d x=%d u=%d -> child good, TRN_E=%d\n", line, g, y, x, u, r); }
                else printf("CHILDUND %s g=%d y=%d x=%d u=%d -> child not good\n", line, g, y, x, u); fflush(stdout); } continue; }
          if (h != 1) continue;
          int s2[2] = {y, g}; uint32_t f2[2] = {1u << x, 1u << u};
          orc::budget = bud; int r = orc2::query(H, 2, s2, f2);
          if (r == 2) { orc::budget = big; int r2 = orc2::query(H, 2, s2, f2); orc::budget = big; int w = orc::avoid(G, y, 1u << x);
            printf("TRNE_UNDECIDED %s g=%d y=%d x=%d u=%d m=%d -> budget %llu: TRN_E=%d TRN=%d\n", line, g, y, x, u, G.nedges(), big, r2, w); fflush(stdout); }
        }
      }
    }
  }
  printf("child undecided %lld; with the larger budget: still undecided %lld, child good %lld\n", childUnd, childUndBig, childUndGood);
}
