// tt.cpp: the D-level Case I step.  For an instance (G, c, A) with even vertex g and a target
// u in N(g), enumerate the Lovász decompositions D' of G - gu with Q'_c avoiding A (up to a cap), run
// Fan's forced chain g -> u, and record whether the result has Q_c avoiding A.
// input lines: "graph6 c A" with A a comma list (or '-' for Amax).  Output per target.
#include "dec.h"

int main(int argc, char** argv) {
  long long cap = argc > 1 ? atoll(argv[1]) : 200000;
  char g6[256], As[256]; int c;
  while (scanf("%255s %d %255s", g6, &c, As) == 3) {
    Gr G; if (!parse_g6(g6, G)) continue;
    uint32_t A = 0;
    if (!strcmp(As, "-")) A = amax_of(G, c);
    else { char* p = As; while (*p) { if (*p == '{' || *p == '}' || *p == ',') { p++; continue; } A |= 1u << strtol(p, &p, 10); } }
    int g = even_vertex(G);
    printf("INST %s c=%d A=", g6, c); print_set(stdout, A); printf(" g=%d\n", g);
    bool anyok = false;
    for (int u = 0; u < G.N; u++) if (G.has(g, u) && !(A >> u & 1)) {
      Gr H = G; H.del(g, u);
      long long nd = 0, nok = 0, navoid = 0, navoid_ok = 0, nthru = 0, nthru_ok = 0;
      dec::enumerate(H, c, A, cap, [&](const dec::Decomp& D) {
        nd++;
        if (!dec::check_decomp(H, D)) { fprintf(stderr, "BAD DECOMP\n"); exit(1); }
        std::vector<int> ch;
        dec::Decomp D2 = dec::fan_forced(D, g, u, ch);
        if (!dec::check_decomp(G, D2)) { fprintf(stderr, "BAD FAN RESULT\n"); exit(1); }
        int qi = dec::path_end_at(D2, c);
        bool ok = qi >= 0 && dec::path_avoids(D2[qi], A);
        bool thru = std::find(ch.begin(), ch.end(), c) != ch.end();
        nok += ok;
        if (thru) { nthru++; nthru_ok += ok; } else { navoid++; navoid_ok += ok; }
        return false;
      });
      printf("  u=%d inNc=%d goodD'=%lld%s transferOK=%lld chainAvoidsC=%lld(ok %lld) chainThruC=%lld(ok %lld)\n", u, (int)G.has(c, u), nd,
             nd >= cap ? "(cap)" : "", nok, navoid, navoid_ok, nthru, nthru_ok);
      if (nok) anyok = true;
    }
    printf("  RESULT %s\n", anyok ? "CaseI-OK" : "CaseI-FAIL");
    fflush(stdout);
  }
  return 0;
}
