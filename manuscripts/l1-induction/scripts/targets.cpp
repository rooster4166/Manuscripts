// targets.cpp: for each blocked instance (A = Amax, c notin N(g)), and each target u in N(g), record
// whether (G - gu, c, A) is good, with local features of u.  Tests simple selection rules.
#include "lind.h"
#include <functional>
int main() {
  char line[256]; long long inst = 0;
  // rules: R1 min |N(u) cap A - g|; R2 max |N(u) cap N(g)|; R3 u notin N(c) first, then R1; R4 min d(u); R5 max |N(u) cap N(c)|
  long long ruleok[8] = {0};
  long long feat[2][16] = {{0}};  // good/bad by |N(u)∩A-g|
  while (fgets(line, sizeof line, stdin)) {
    Gr G; if (!parse_g6(line, G)) continue; char* nl = strchr(line, '\n'); if (nl) *nl = 0;
    if (__builtin_popcount(G.evens()) != 1) continue; int g = even_vertex(G);
    for (int c = 0; c < G.N; c++) { if (!(G.deg(c) & 1) || G.has(g, c)) continue;
      uint32_t A = amax_of(G, c);
      bool isb = true; for (int u = 0; u < G.N; u++) if (G.has(g, u) && !(G.adj[u] & A & ~(1u << g))) isb = false;
      if (!isb) continue; inst++;
      int good[32], fa[32], fg[32], fc[32], du[32]; std::vector<int> T;
      for (int u = 0; u < G.N; u++) if (G.has(g, u)) { Gr H = G; H.del(g, u); good[u] = orc::avoid(H, c, A) == 1;
        fa[u] = __builtin_popcount(G.adj[u] & A & ~(1u << g)); fg[u] = __builtin_popcount(G.adj[u] & G.adj[g]); fc[u] = __builtin_popcount(G.adj[u] & G.adj[c]); du[u] = G.deg(u); T.push_back(u);
        feat[good[u]][fa[u]]++; if (!good[u] && getenv("DUMP")) { printf("BADT %s g=%d c=%d u=%d A=", line, g, c, u); print_set(stdout, A); printf(" d(u)=%d |N(u)∩A|=%d uInNc=%d N(u)=", du[u], fa[u], (int)G.has(c,u)); print_set(stdout, G.adj[u]); printf(" N(g)="); print_set(stdout, G.adj[g]); printf(" N(c)="); print_set(stdout, G.adj[c]); printf("\n"); } }
      auto rule = [&](std::function<long(int)> key) { long best = 1L << 60; for (int u : T) best = std::min(best, key(u)); bool allok = true; for (int u : T) if (key(u) == best && !good[u]) allok = false; return allok; };
      ruleok[0] += rule([&](int u) { return (long)fa[u]; });
      ruleok[1] += rule([&](int u) { return -(long)fg[u]; });
      ruleok[2] += rule([&](int u) { return (long)(G.has(c, u) ? 100 : 0) + fa[u]; });
      ruleok[3] += rule([&](int u) { return (long)du[u]; });
      ruleok[4] += rule([&](int u) { return -(long)fc[u]; });
      ruleok[5] += rule([&](int u) { return (long)fa[u] * 100 - fg[u]; });
      bool any = false; for (int u : T) any |= good[u]; ruleok[6] += any;
    }
  }
  printf("blocked instances=%lld someGoodTarget=%lld\n", inst, ruleok[6]);
  const char* nm[] = {"min|N(u)∩A|", "max|N(u)∩N(g)|", "outsideN(c) then min|N(u)∩A|", "min d(u)", "max|N(u)∩N(c)|", "min|N(u)∩A| then max|N(u)∩N(g)|"};
  for (int r = 0; r < 6; r++) printf("  rule %-40s all minimisers good in %lld\n", nm[r], ruleok[r]);
  printf("  by |N(u)∩A-g|: "); for (int k = 0; k < 10; k++) if (feat[0][k] + feat[1][k]) printf("%d: good %lld bad %lld; ", k, feat[1][k], feat[0][k]); printf("\n");
}
