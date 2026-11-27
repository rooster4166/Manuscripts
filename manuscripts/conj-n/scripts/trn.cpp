// trn.cpp: exhaustive test of TRN (manuscript Conjecture 4.1): g even, x, y odd, x !~ y,
// u in N(g) & N(y), u != x.  If (G - gu, y, {x}) is good, is (G, y, {x}) good?
// Counts tests separately for y ~ g and y !~ g; prints violations.
#include "orcb.h"
int main() {
  char line[256]; long long t[2] = {0, 0}, v[2] = {0, 0}, inst = 0; int pr = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    if (__builtin_popcount(G.evens()) != 1) continue;
    int g = even_vertex(G);
    for (int y = 0; y < G.N; y++) { if (G.deg(y) % 2 == 0) continue;
      for (int x = 0; x < G.N; x++) {
        if (x == y || G.deg(x) % 2 == 0 || G.has(x, y)) continue;
        int whole = -1, adj = G.has(g, y);
        for (int u = 0; u < G.N; u++) {
          if (u == x || !G.has(g, u) || !G.has(y, u)) continue;
          Gr H = G; H.del(g, u);
          if (orc::avoid(H, y, 1u << x) != 1) continue;
          t[adj]++;
          if (whole < 0) whole = orc::avoid(G, y, 1u << x);
          if (whole != 1) { v[adj]++; if (pr++ < 20) printf("TRN_VIOL %s g=%d y=%d x=%d u=%d\n", line, g, y, x, u); }
        }
      }
    }
  }
  printf("TRN tests y!~g=%lld (viol %lld)  y~g=%lld (viol %lld)\n", t[0], v[0], t[1], v[1]);
}
