// tx.cpp: the target-in-A child.  For every N instance (G, y, {x}) with x ~ g, test whether
// (G - gx, y, {x}, B = N_G(x)) is good (Q_y avoids x and does not end in N_G(x)).
#include "orcb.h"
int main() {
  char line[256]; long long tot = 0, core = 0, ok = 0, okcore = 0, sanity = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    if (__builtin_popcount(G.evens()) != 1) continue;
    int g = even_vertex(G);
    for (int y = 0; y < G.N; y++) { if (G.deg(y) % 2 == 0) continue;
      for (int x = 0; x < G.N; x++) {
        if (x == y || G.deg(x) % 2 == 0 || G.has(x, y) || !G.has(x, g)) continue;
        uint32_t W = G.adj[y] & ~G.adj[x] & ~(1u << g); if (!W) continue;
        tot++;
        uint32_t T = G.adj[g] & ~(1u << x) & ~(1u << y);
        bool isc = (T & ~G.adj[x]) == 0; core += isc;
        Gr H = G; H.del(g, x);
        int r = orcb::avoidB(H, y, 1u << x, G.adj[x]);
        if (r == 1) { ok++; okcore += isc; }
        else printf("TXFAIL %s g=%d y=%d x=%d core=%d r=%d\n", line, g, y, x, (int)isc, r);
        if (orcb::avoidB(H, y, 1u << x, 0) != orc::avoid(H, y, 1u << x)) sanity++;
      }
    }
  }
  printf("TX total=%lld ok=%lld core=%lld okcore=%lld sanity_mismatch=%lld\n", tot, ok, core, okcore, sanity);
}
