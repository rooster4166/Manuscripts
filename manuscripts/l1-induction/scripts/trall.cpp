// trall.cpp: the transfer lemma TR for arbitrary A.  G with one even vertex g, c odd, c notin N(g),
// u in N(g) (in N(c) or not), A any set with c, u notin A (g may be in A).  If (G - gu, c, A) is good, is (G, c, A) good?
// Counts violations; for tight u also checks the forced-chain re-choice.
#include "lind.h"
int main() {
  char line[256]; long long tests[2] = {0}, viol[2] = {0};
  while (fgets(line, sizeof line, stdin)) {
    Gr G; if (!parse_g6(line, G)) continue; char* nl = strchr(line, '\n'); if (nl) *nl = 0;
    if (__builtin_popcount(G.evens()) != 1) continue; int g = even_vertex(G);
    for (int c = 0; c < G.N; c++) { if (!(G.deg(c) & 1) || G.has(g, c)) continue;
      for (int u = 0; u < G.N; u++) if (G.has(g, u)) {
        Gr H = G; H.del(g, u);
        int idx[32], k = 0; for (int v = 0; v < G.N; v++) if (v != c && v != u) idx[k++] = v;
        for (uint32_t s = 0; s < (1u << k); s++) {
          uint32_t A = 0; for (int i = 0; i < k; i++) if (s >> i & 1) A |= 1u << idx[i];
          if (orc::avoid(H, c, A) != 1) continue;
          int t = G.has(c, u);
          tests[t]++;
          if (orc::avoid(G, c, A) != 1) { viol[t]++; printf("TRVIOL %s c=%d g=%d u=%d inNc=%d adm=%d AmeetsNc=%d A=", line, c, g, u, t, (int)admissible(G, c, A), (int)((A & G.adj[c]) != 0)); print_set(stdout, A); printf("\n"); }
        }
      }
    }
  }
  printf("SUMMARY TR: u notin N(c): tests %lld violations %lld;  u in N(c): tests %lld violations %lld\n", tests[0], viol[0], tests[1], viol[1]);
}
