#include "dec.h"
static void pd(const dec::Decomp& D) { for (auto& p : D) { printf(" "); for (size_t i = 0; i < p.size(); i++) printf("%d", p[i]); } }
int main(int argc, char** argv) {
  Gr G; parse_g6(argv[1], G); int c = atoi(argv[2]); uint32_t A = 0; for (char* p = argv[3]; *p;) { if (*p == ',') { p++; continue; } A |= 1u << strtol(p, &p, 10); }
  int g = even_vertex(G);
  printf("good D of G:"); dec::enumerate(G, c, A, 3, [&](const dec::Decomp& D) { printf(" {"); pd(D); printf(" }"); return false; }); printf("\n");
  for (int u = 0; u < G.N; u++) if (G.has(g, u)) { Gr H = G; H.del(g, u);
    int shown[2] = {0, 0};
    dec::enumerate(H, c, A, 0, [&](const dec::Decomp& D) { std::vector<int> ch; auto D2 = dec::fan_forced(D, g, u, ch); bool thru = std::find(ch.begin(), ch.end(), c) != ch.end();
      int qi = dec::path_end_at(D2, c); bool ok = dec::path_avoids(D2[qi], A);
      if (shown[thru] < 1) { shown[thru]++; printf("u=%d D':", u); pd(D); printf("  chain:"); for (int x : ch) printf(" %d", x); printf("  -> D:"); pd(D2); printf("  Q_c ok=%d\n", (int)ok); }
      return false; }); }
}
