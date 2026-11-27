// tr2.cpp: TR with A cap N[c] = empty.  Tight targets only (u in N(g) cap N(c)); all A subset of
// V - N[c] - {u}.  Violations: (G - gu, c, A) good but (G, c, A) not.
#include "lind.h"
int main() {
  char line[256]; long long tests = 0, viol = 0;
  while (fgets(line, sizeof line, stdin)) {
    Gr G; if (!parse_g6(line, G)) continue; char* nl = strchr(line, '\n'); if (nl) *nl = 0;
    if (__builtin_popcount(G.evens()) != 1) continue; int g = even_vertex(G);
    for (int c = 0; c < G.N; c++) { if (!(G.deg(c) & 1) || G.has(g, c)) continue;
      for (int u = 0; u < G.N; u++) if (G.has(g, u) && G.has(c, u)) {
        Gr H = G; H.del(g, u);
        uint32_t bad = closed_nbhd(G, c) | (1u << u);
        int idx[32], k = 0; for (int v = 0; v < G.N; v++) if (!(bad >> v & 1)) idx[k++] = v;
        // only maximal-by-inclusion tests are not enough (not monotone), so test all subsets
        for (uint32_t s = 0; s < (1u << k); s++) {
          uint32_t A = 0; for (int i = 0; i < k; i++) if (s >> i & 1) A |= 1u << idx[i];
          if (orc::avoid(H, c, A) != 1) continue;
          tests++;
          if (orc::avoid(G, c, A) != 1) { viol++; printf("TRVIOL %s c=%d g=%d u=%d A=", line, c, g, u); print_set(stdout, A); printf(" adm=%d\n", (int)admissible(G, c, A)); fflush(stdout); }
        }
      }
    }
  }
  printf("SUMMARY TR (A cap N[c] empty, tight u): tests %lld violations %lld\n", tests, viol);
}
