// tradj.cpp: TR with c ~ g.  For c in N(g) odd, A & N[c] = 0, tight u in N(g)&N(c)-A:
// if (G - gu, c, A) good then is (G, c, A) good?  Also restricted to |A| = 1 (N-type).
#include "orcb.h"
int main(int argc, char** argv) {
  int maxA = argc > 1 ? atoi(argv[1]) : 99;
  char line[256]; long long tests = 0, viol = 0; int pr = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    if (__builtin_popcount(G.evens()) != 1) continue;
    int g = even_vertex(G);
    for (int c = 0; c < G.N; c++) { if (!G.has(g, c) || G.deg(c) % 2 == 0) continue;
      uint32_t U = ((1u << G.N) - 1) & ~closed_nbhd(G, c);
      for (uint32_t A = U; A; A = (A - 1) & U) { if (__builtin_popcount(A) > maxA) continue;
        int whole = -1;
        for (int u = 0; u < G.N; u++) { if (!G.has(g, u) || !G.has(c, u) || (A >> u & 1)) continue;
          Gr H = G; H.del(g, u);
          if (orc::avoid(H, c, A) != 1) continue;
          tests++;
          if (whole < 0) whole = orc::avoid(G, c, A);
          if (whole != 1) { viol++; if (pr++ < 10) { printf("TRADJ_VIOL %s g=%d c=%d u=%d A=", line, g, c, u); print_set(stdout, A); printf("\n"); } }
        }
      }
    }
  }
  printf("TRADJ tests=%lld violations=%lld\n", tests, viol);
}
