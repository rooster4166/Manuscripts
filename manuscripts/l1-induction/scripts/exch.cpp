// exch.cpp: coverage of TR by the proved lemmas, per decomposition.  For every tight pair (G, c, u)
// with A = Amax and every good D' of G - gu, classify:
//   AV  forced chain avoids c (tight-fan Lemma 3.2: transfer good);
//   EX  chain first meets c at step i, Q'_c avoids u (chain stops at c), V(P_{x_{i-1}}) ∩ V(Q'_c) = {c}
//       (exchange lemma: a decomposition with Q_c = cu);
//   REST otherwise (then record whether the Fan image happens to be good).
#include "dec.h"
int main(int argc, char** argv) {
  long long cap = argc > 1 ? atoll(argv[1]) : 200000;
  char line[256]; long long nAV = 0, nEX = 0, nREST = 0, nRESTgood = 0, pairs = 0, pairsAllCovered = 0;
  while (fgets(line, sizeof line, stdin)) {
    Gr G; if (!parse_g6(line, G)) continue; char* nl = strchr(line, '\n'); if (nl) *nl = 0;
    if (__builtin_popcount(G.evens()) != 1) continue; int g = even_vertex(G);
    for (int c = 0; c < G.N; c++) { if (!(G.deg(c) & 1) || G.has(g, c)) continue;
      uint32_t A = amax_of(G, c);
      for (int u = 0; u < G.N; u++) if (G.has(g, u) && G.has(c, u)) {
        Gr H = G; H.del(g, u); bool any = false, allcov = true;
        dec::enumerate(H, c, A, cap, [&](const dec::Decomp& D) {
          any = true;
          std::vector<int> ch; dec::Decomp D2 = dec::fan_forced(D, g, u, ch);
          auto it = std::find(ch.begin(), ch.end(), c);
          if (it == ch.end()) { nAV++; return false; }
          int i = (int)(it - ch.begin()); int xprev = ch[i - 1];
          int qc = dec::path_end_at(D, c); int pp = dec::path_end_at(D, xprev);
          bool qcu = std::find(D[qc].begin(), D[qc].end(), u) != D[qc].end();
          uint32_t vp = 0, vq = 0; for (int x : D[pp]) vp |= 1u << x; for (int x : D[qc]) vq |= 1u << x;
          if (!qcu && pp != qc && (vp & vq) == (1u << c)) { nEX++; return false; }
          nREST++; allcov = false;
          int qi = dec::path_end_at(D2, c); if (dec::path_avoids(D2[qi], A)) nRESTgood++;
          return false; });
        if (any) { pairs++; pairsAllCovered += allcov; }
      }
    }
  }
  printf("SUMMARY tight pairs=%lld (every good D' covered by AV or EX: %lld)  D': AV=%lld EX=%lld REST=%lld (REST with good Fan image %lld)\n", pairs, pairsAllCovered, nAV, nEX, nREST, nRESTgood);
}
