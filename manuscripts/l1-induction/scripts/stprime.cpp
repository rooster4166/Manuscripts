// stprime.cpp: the instance-level some-target statement ST'.  For a blocked admissible instance
// (G, c, A) [g even, c notin N(g), every u in N(g) has a neighbour in A - g]:
//   ST'(G,c,A):  exists u in N(g):  u notin N(c) and (G - gu, c, A) good,
//                               or  u in N(c)  and (G - gu - cu, u, A + c) good.
//   ST (G,c,A):  exists u in N(g): (G - gu, c, A) good.
// All admissible A (every subset of Amax), A nonempty.
#include "lind.h"
int main() {
  char line[256]; long long inst = 0, stp = 0, st = 0, nontight_avail = 0, stout = 0, tightonly = 0, tight_st = 0;
  while (fgets(line, sizeof line, stdin)) {
    Gr G; if (!parse_g6(line, G)) continue; char* nl = strchr(line, '\n'); if (nl) *nl = 0;
    if (__builtin_popcount(G.evens()) != 1) continue; int g = even_vertex(G);
    for (int c = 0; c < G.N; c++) { if (!(G.deg(c) & 1) || G.has(g, c)) continue;
      uint32_t Am = amax_of(G, c);
      int idx[32], k = 0; for (int v = 0; v < G.N; v++) if (Am >> v & 1) idx[k++] = v;
      for (uint32_t s = 1; s < (1u << k); s++) {
        uint32_t A = 0; for (int i = 0; i < k; i++) if (s >> i & 1) A |= 1u << idx[i];
        bool isb = true; for (int u = 0; u < G.N; u++) if (G.has(g, u) && !(G.adj[u] & A & ~(1u << g))) isb = false;
        if (!isb) continue; inst++;
        bool a = false, b = false, bo = false;
        for (int u = 0; u < G.N; u++) if (G.has(g, u)) {
          Gr H = G; H.del(g, u);
          bool gd = orc::avoid(H, c, A) == 1; b |= gd;
          if (!G.has(c, u)) { a |= gd; bo |= gd; }
          else { Gr K = H; K.del(c, u); a |= (orc::avoid(K, u, A | (1u << c)) == 1); }
        }
        stp += a; st += b;
        bool avail = (G.adj[g] & ~G.adj[c]) != 0;
        if (avail) { nontight_avail++; stout += bo; if (!bo) { printf("STOUTFAIL %s g=%d c=%d A=", line, g, c); print_set(stdout, A); printf("\n"); } }
        else { tightonly++; tight_st += b; }
        if (!a) { printf("STPFAIL %s g=%d c=%d A=", line, g, c); print_set(stdout, A); printf(" |A|=%d ST=%d N(g)=", __builtin_popcount(A), (int)b); print_set(stdout, G.adj[g]); printf(" N(c)="); print_set(stdout, G.adj[c]); printf("\n"); }
        if (!b) { printf("STFAIL %s g=%d c=%d A=", line, g, c); print_set(stdout, A); printf("\n"); }
      }
    }
  }
  printf("SUMMARY blocked instances (all admissible A)=%lld  ST'=%lld  ST=%lld | N(g) not in N(c): %lld, with a good non-tight target: %lld | N(g) in N(c): %lld, ST: %lld\n", inst, stp, st, nontight_avail, stout, tightonly, tight_st);
}
