// l1e1.cpp: per-target L1E check for one instance "g6 c" (A = Amax), unlimited budget, with progress.
#include "orc2.h"
int main() { char g6[256]; int c; while (scanf("%255s %d", g6, &c) == 2) { Gr G; parse_g6(g6, G); int g = even_vertex(G); uint32_t A = amax_of(G, c);
  printf("%s c=%d g=%d A=", g6, c, g); print_set(stdout, A); printf(" N(g)="); print_set(stdout, G.adj[g]); printf(" N(c)="); print_set(stdout, G.adj[c]); printf("\n"); fflush(stdout);
  for (int u = 0; u < G.N; u++) if (G.has(g, u)) { Gr H = G; H.del(g, u); int r = orc::avoid(H, c, A); int q = -9;
    if (r == 1) { int s2[2] = {c, g}; uint32_t f2[2] = {A, 1u << u}; q = orc2::query(H, 2, s2, f2); }
    printf("  u=%d inNc=%d ST-child-good=%d L1E=%d\n", u, (int)G.has(c, u), r, q); fflush(stdout); } } }
