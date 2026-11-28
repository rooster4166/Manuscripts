// trne.cpp: for each TRN test (G, g, y, x, u) with (G-gu, y, {x}) good, decide TRN-E: is there a good
// D' of G-gu whose path ending at g avoids u (trivial forced chain)?  Equivalently, a Lovász
// decomposition of G with x notin Q(y) in which gu is the terminal edge at u.
// For instances where TRN-E fails, optionally enumerate D' (cap) to decide re-choice (chain avoiding y)
// and plain-image goodness.
#include "orc2.h"
#include "dec.h"
int main(int argc, char** argv) {
  long long cap = argc > 1 ? atoll(argv[1]) : 0;   // 0: do not enumerate
  char line[256]; long long t[2] = {0, 0}, e1[2] = {0, 0}, und = 0, rech[2] = {0, 0}, img[2] = {0, 0}, capd = 0;
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
          if (orc::avoid(H, y, 1u << x) != 1) continue;
          int adj = G.has(g, y); t[adj]++;
          int s2[2] = {y, g}; uint32_t f2[2] = {1u << x, 1u << u};
          int r = orc2::query(H, 2, s2, f2);
          if (r == 2) und++;
          if (r == 1) { e1[adj]++; continue; }
          printf("NOTRNE %s g=%d y=%d x=%d u=%d adj=%d", line, g, y, x, u, adj);
          if (cap) {
            bool fa = false, fo = false; long long nd = 0;
            dec::enumerate(H, y, 1u << x, cap, [&](const dec::Decomp& D) {
              nd++; std::vector<int> ch; dec::Decomp R = dec::fan_forced(D, g, u, ch);
              if (std::find(ch.begin(), ch.end(), y) == ch.end()) fa = true;
              if (dec::path_avoids(R[dec::path_end_at(R, y)], 1u << x)) fo = true;
              return fa; });
            if (nd >= cap && !fa) capd++;
            rech[adj] += fa; img[adj] += fo;
            printf(" rechoice=%d image=%d nD=%lld", (int)fa, (int)fo, nd);
          }
          printf("\n"); fflush(stdout);
        }
      }
    }
  }
  printf("SUMMARY tests y!~g=%lld y~g=%lld; TRN-E holds y!~g=%lld y~g=%lld; undecided=%lld; among TRN-E failures: rechoice %lld/%lld image %lld/%lld capped=%lld\n",
         t[0], t[1], e1[0], e1[1], und, rech[0], rech[1], img[0], img[1], capd);
}
