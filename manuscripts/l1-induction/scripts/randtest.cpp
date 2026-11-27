// randtest.cpp: ST, TR, L1E on given graphs (A = Amax, c notin N(g)), with a node budget.
//   ST : some u in N(g): (G - gu, c, A) good.          [blocked instances]
//   TR : tight u with (G - gu, c, A) good  =>  (G, c, A) good.   [all instances, tight targets]
//   L1E: some u in N(g): G - gu has D' with Q'_c avoiding A and Q'_g avoiding u.   [blocked]
#include "orc2.h"
int main(int argc, char** argv) {
  orc::budget = argc > 1 ? strtoull(argv[1], 0, 10) : 2000000;
  char line[512]; long long binst = 0, stok = 0, stund = 0, trt = 0, trv = 0, trund = 0, l1eok = 0, l1eund = 0, graphs = 0;
  while (fgets(line, sizeof line, stdin)) {
    Gr G; if (!parse_g6(line, G)) continue; char* nl = strchr(line, '\n'); if (nl) *nl = 0;
    if (__builtin_popcount(G.evens()) != 1) continue; int g = even_vertex(G); graphs++;
    for (int c = 0; c < G.N; c++) { if (!(G.deg(c) & 1) || G.has(g, c)) continue;
      uint32_t A = amax_of(G, c);
      bool isb = true; for (int u = 0; u < G.N; u++) if (G.has(g, u) && !(G.adj[u] & A & ~(1u << g))) isb = false;
      int whole = -1;  // goodness of (G, c, A), computed lazily
      bool st = false, stu = false, le = false, leu = false;
      for (int u = 0; u < G.N; u++) if (G.has(g, u)) {
        Gr H = G; H.del(g, u);
        int r = orc::avoid(H, c, A);
        if (r == 2) { stu = true; if (G.has(c, u)) trund++; continue; }
        if (r == 1) st = true;
        if (r == 1 && G.has(c, u)) { trt++; if (whole < 0) whole = orc::avoid(G, c, A);
          if (whole == 2) trund++; else if (whole != 1) { trv++; printf("TRVIOL %s c=%d g=%d u=%d\n", line, c, g, u); } }
        if (isb && r == 1 && !le) { int s2[2] = {c, g}; uint32_t f2[2] = {A, 1u << u}; int q = orc2::query(H, 2, s2, f2); if (q == 1) le = true; else if (q == 2) leu = true; }
      }
      if (isb) { binst++; if (st) stok++; else if (stu) stund++; else printf("STFAIL %s c=%d g=%d\n", line, c, g);
        if (le) l1eok++; else if (leu) l1eund++; else printf("L1EFAIL %s c=%d g=%d\n", line, c, g); }
      fflush(stdout);
    }
  }
  printf("SUMMARY graphs=%lld blocked=%lld ST ok=%lld undecided=%lld | L1E ok=%lld undecided=%lld | TR tight tests=%lld violations=%lld undecided=%lld\n", graphs, binst, stok, stund, l1eok, l1eund, trt, trv, trund);
}
