// t_trsplit.cpp: the TR test of tr2.cpp (same loop, the authors' lind.h oracle included unmodified),
// with each test classified by whether A is admissible for G (A cap N(g) empty: then the conclusion
// "(G,c,A) good" is an instance of L1* itself) or meets N(g) (TR beyond L1*).  Also counts A = empty.
// build: g++ -O2 -I<snapshot>/manuscripts/l1-induction/scripts t_trsplit.cpp
#include "lind.h"
int main() {
  char line[256]; long long tests = 0, viol = 0, adm = 0, inadm = 0, empty = 0;
  while (fgets(line, sizeof line, stdin)) {
    Gr G; if (!parse_g6(line, G)) continue;
    if (__builtin_popcount(G.evens()) != 1) continue; int g = even_vertex(G);
    for (int c = 0; c < G.N; c++) { if (!(G.deg(c) & 1) || G.has(g, c)) continue;
      for (int u = 0; u < G.N; u++) if (G.has(g, u) && G.has(c, u)) {
        Gr H = G; H.del(g, u);
        uint32_t bad = closed_nbhd(G, c) | (1u << u);
        int idx[32], k = 0; for (int v = 0; v < G.N; v++) if (!(bad >> v & 1)) idx[k++] = v;
        for (uint32_t s = 0; s < (1u << k); s++) {
          uint32_t A = 0; for (int i = 0; i < k; i++) if (s >> i & 1) A |= 1u << idx[i];
          if (orc::avoid(H, c, A) != 1) continue;
          tests++; if (!A) empty++;
          if (A & G.adj[g]) inadm++; else adm++;
          if (orc::avoid(G, c, A) != 1) viol++;
        }
      }
    }
  }
  printf("SUMMARY TR tests %lld violations %lld; A admissible for G %lld (of which A empty %lld); A meets N(g) %lld\n", tests, viol, adm, empty, inadm);
}
