// move (s): u in N(g) cap N(c).  Q_c = cu is possible if G'' = G - cu - gu has a Lovász decomposition
// with Q_g and Q_u vertex-disjoint (join them through gu).  Tests which targets u admit it.
#include "orc2.h"
static int sq(const Gr& G, int g, int c, int u) {
  Gr H = G; H.del(c, u); H.del(g, u);
  if (!(H.deg(u) & 1) || !(H.deg(g) & 1)) return -1;
  int s[2] = {g, u}; uint32_t f[2] = {1u << u, 0};
  orc2::DISJ = 1; int r = orc2::query(H, 2, s, f); orc2::DISJ = 0; return r;
}
int main(int argc, char** argv) {
  std::string mode = argc > 1 ? argv[1] : "list";
  char line[256];
  if (mode == "list") { char g6[256]; int c;
    while (scanf("%255s %d %*s", g6, &c) == 2) { Gr G; parse_g6(g6, G); int g = even_vertex(G);
      printf("%s c=%d g=%d s-move ok for u in ", g6, c, g); uint32_t ok = 0;
      for (int u = 0; u < G.N; u++) if (G.has(g, u) && G.has(c, u) && sq(G, g, c, u) == 1) ok |= 1u << u;
      print_set(stdout, ok); printf("\n"); } return 0; }
  // census: blocked Amax instances with c notin N(g) and N(g) cap N(c) nonempty: how often does (s) apply?
  long long inst = 0, common = 0, sok = 0, tight_all = 0, tight_sok = 0;
  while (fgets(line, sizeof line, stdin)) {
    Gr G; if (!parse_g6(line, G)) continue; char* nl = strchr(line, '\n'); if (nl) *nl = 0;
    if (__builtin_popcount(G.evens()) != 1) continue; int g = even_vertex(G);
    for (int c = 0; c < G.N; c++) { if (!(G.deg(c) & 1) || G.has(g, c)) continue;
      inst++; if (!(G.adj[g] & G.adj[c])) continue; common++;
      bool any = false; for (int u = 0; u < G.N; u++) if (G.has(g, u) && G.has(c, u) && sq(G, g, c, u) == 1) { any = true; break; }
      sok += any;
      bool allin = !(G.adj[g] & ~G.adj[c]);
      if (allin) { tight_all++; tight_sok += any; if (!any) { printf("NOS %s c=%d g=%d\n", line, c, g); } }
    }
  }
  printf("SUMMARY inst=%lld withCommonNbr=%lld sMoveApplies=%lld  N(g)inN(c)=%lld of which sMove=%lld\n", inst, common, sok, tight_all, tight_sok);
}
