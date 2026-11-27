// alltarget.cpp: the "every target" form.  For G with one even vertex g, c odd, c notin N(g),
// A = Amax(G, c): for each u in N(g), is (G - gu, c, A) good?  Tabulated by (d(g), d(c)) classes.
// Prints ATFAIL for failures with d(g) >= 4 and d(c) >= 3.
#include "lind.h"
int main(int argc, char** argv) {
  char line[256]; long long tot[3][3] = {{0}}, fail[3][3] = {{0}}, inst[3][3] = {{0}}, instfail[3][3] = {{0}}, und = 0;
  unsigned long long bud = argc > 1 ? strtoull(argv[1], 0, 10) : 0;
  orc::budget = bud;
  while (fgets(line, sizeof line, stdin)) {
    Gr G; if (!parse_g6(line, G)) continue; char* nl = strchr(line, '\n'); if (nl) *nl = 0;
    if (__builtin_popcount(G.evens()) != 1) continue; int g = even_vertex(G);
    int ig = G.deg(g) == 2 ? 0 : (G.deg(g) == 4 ? 1 : 2);
    for (int c = 0; c < G.N; c++) { if (!(G.deg(c) & 1) || G.has(g, c)) continue;
      int ic = G.deg(c) == 1 ? 0 : (G.deg(c) == 3 ? 1 : 2);
      uint32_t A = amax_of(G, c); bool anyf = false;
      for (int u = 0; u < G.N; u++) if (G.has(g, u)) {
        Gr H = G; H.del(g, u); int r = orc::avoid(H, c, A);
        if (r == 2) { und++; continue; }
        tot[ig][ic]++; if (r != 1) { fail[ig][ic]++; anyf = true;
          if (ig >= 1 && ic >= 1) { printf("ATFAIL %s g=%d c=%d u=%d A=", line, g, c, u); print_set(stdout, A); printf("\n"); fflush(stdout); } }
      }
      inst[ig][ic]++; instfail[ig][ic] += anyf;
    }
  }
  const char* gn[] = {"d(g)=2", "d(g)=4", "d(g)>=6"}; const char* cn[] = {"d(c)=1", "d(c)=3", "d(c)>=5"};
  for (int a = 0; a < 3; a++) for (int b = 0; b < 3; b++) if (tot[a][b]) printf("  %s %s: instances %lld (some bad target %lld), targets %lld bad %lld\n", gn[a], cn[b], inst[a][b], instfail[a][b], tot[a][b], fail[a][b]);
  printf("SUMMARY undecided=%lld\n", und);
}
