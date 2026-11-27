// rechoice.cpp: tight re-choice.  For every instance (G, c, Amax) with one even vertex g, c notin N(g),
// and every tight target u in N(g) cap N(c) such that (G - gu, c, A) is good: is there a good D' of
// G - gu whose forced Fan chain g -> u avoids c?  (And: is there one whose transfer is good at all?)
#include "dec.h"
int main(int argc, char** argv) {
  long long cap = argc > 1 ? atoll(argv[1]) : 2000000;
  char line[256]; long long pairs = 0, avoidOK = 0, anyOK = 0, capped = 0, inst = 0, instOK = 0;
  while (fgets(line, sizeof line, stdin)) {
    Gr G; if (!parse_g6(line, G)) continue; char* nl = strchr(line, '\n'); if (nl) *nl = 0;
    if (__builtin_popcount(G.evens()) != 1) continue; int g = even_vertex(G);
    for (int c = 0; c < G.N; c++) { if (!(G.deg(c) & 1) || G.has(g, c)) continue;
      uint32_t A = amax_of(G, c);
      for (int u = 0; u < G.N; u++) if (G.has(g, u) && G.has(c, u)) {
        Gr H = G; H.del(g, u);
        if (orc::avoid(H, c, A) != 1) continue;
        pairs++;
        bool fa = false, fo = false; long long nd = 0;
        dec::enumerate(H, c, A, cap, [&](const dec::Decomp& D) {
          nd++;
          std::vector<int> ch; dec::Decomp D2 = dec::fan_forced(D, g, u, ch);
          bool thru = std::find(ch.begin(), ch.end(), c) != ch.end();
          int qi = dec::path_end_at(D2, c); bool ok = qi >= 0 && dec::path_avoids(D2[qi], A);
          if (!thru) fa = true; if (ok) fo = true;
          return fa;  // stop once a chain avoiding c is found
        });
        if (nd >= cap && !fa) capped++;
        avoidOK += fa; anyOK += fo;
        if (!fa) { printf("NOAVOID %s c=%d g=%d u=%d A=", line, c, g, u); print_set(stdout, A); printf(" anyTransferOK=%d enumerated=%lld%s\n", (int)fo, nd, nd >= cap ? "(cap)" : ""); fflush(stdout); }
      }
    }
  }
  printf("SUMMARY tight pairs with (G-gu,c,A) good=%lld  some D' with chain avoiding c=%lld  some D' with good transfer=%lld  capped=%lld\n", pairs, avoidOK, anyOK, capped);
}
