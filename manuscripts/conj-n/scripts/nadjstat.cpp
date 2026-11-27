// nadjstat.cpp: NA instances by the cases settled on paper (d(y)=3 via the split (g); d(x)=1 via
// Lemma NP; no common neighbour via dl-one Thm 6.1) and the rest.
#include "orcb.h"
int main() {
  char line[256]; long long tot = 0, d3 = 0, dx1 = 0, nocn = 0, rest = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    if (__builtin_popcount(G.evens()) != 0) continue;
    for (int y = 0; y < G.N; y++) for (int x = 0; x < G.N; x++) {
      if (x == y || !G.has(x, y)) continue;
      uint32_t W = G.adj[y] & ~G.adj[x] & ~(1u << x); if (!W) continue;
      tot++;
      if (G.deg(y) == 3) d3++; else if (G.deg(x) == 1) dx1++; else if (!(G.adj[x] & G.adj[y])) nocn++; else rest++;
    }
  }
  printf("NA total=%lld d(y)=3:%lld d(x)=1:%lld no-common-nbr:%lld rest:%lld\n", tot, d3, dx1, nocn, rest);
}
