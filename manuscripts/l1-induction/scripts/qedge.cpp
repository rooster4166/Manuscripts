// for given instances "g6 c": which x in N(c) admit a Lovász decomposition with Q_c = cx?
#include "lind.h"
int main() { char g6[256]; int c; while (scanf("%255s %d %*s", g6, &c) == 2) { Gr G; parse_g6(g6, G);
  int g = even_vertex(G); printf("%s c=%d g=%d N(g)=", g6, c, g); print_set(stdout, G.adj[g]); printf(" N(c)="); print_set(stdout, G.adj[c]); printf(" Q_c=cx possible for x in ");
  uint32_t ok = 0; for (int x = 0; x < G.N; x++) if (G.has(c, x)) { uint32_t f = ((1u << G.N) - 1) & ~(1u << c) & ~(1u << x); if (orc::avoid(G, c, f) == 1) ok |= 1u << x; }
  print_set(stdout, ok); printf("\n"); } }
