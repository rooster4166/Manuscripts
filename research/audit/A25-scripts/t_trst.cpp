// t_trst.cpp: independent re-derivation of TR, TR with A arbitrary (trall), ST and ST' with the a25
// library (all Lovász decompositions of G and of every G - gx enumerated once; goodness of every
// (graph, c, A) read off the minimal V(Q_c) sets).
//   TR : g the only even vertex, c odd, c notin N(g), x in N(g) cap N(c), every A subset of
//        V - (N[c] + x) with (G-gx,c,A) good: is (G,c,A) good?   Tests are split by whether A is
//        admissible for G (then the conclusion is an instance of L1* itself) or meets N(g).
//   TRALL: every u in N(g) (tight or not), every A with c, u notin A.
//   ST, ST': every blocked admissible (G,c,A) (A nonempty subset of Amax).
// usage: t_trst [SAMPLE_MOD [SAMPLE_REM]] < graph6     (sampling of the input lines)
#include "a25.h"
#include <iostream>
using namespace a25;
int main(int argc, char** argv) {
  int mod = argc > 1 ? atoi(argv[1]) : 1, remd = argc > 2 ? atoi(argv[2]) : 0;
  long long tr_tests = 0, tr_viol = 0, tr_adm = 0, tr_inadm = 0, tr_inadm_gA = 0;
  long long ta_tests[2] = {0, 0}, ta_viol[2] = {0, 0}, ta_viol_meetNc[2] = {0, 0};
  long long st_inst = 0, st_ok = 0, stp_ok = 0, graphs = 0, lineno = 0;
  long long stp_fail_NgNc = 0, stp_fail_dg2 = 0, stp_fail_dg4dc5 = 0, stp_fail_dg2_gA_uvnonadj = 0;
  std::string line;
  while (std::getline(std::cin, line)) {
    if ((lineno++ % mod) != remd) continue;
    Graph G; if (!decode_g6(line, G)) continue;
    if (__builtin_popcount(G.evenset()) != 1) continue;
    int g = theeven(G), n = G.n; graphs++;
    std::vector<std::vector<uint32_t>> SG; qc_sets(G, SG);
    std::vector<std::vector<std::vector<uint32_t>>> SC(n);
    for (int x = 0; x < n; x++) if (G.has(g, x)) { Graph H = G; H.rem(g, x); qc_sets(H, SC[x]); }
    for (int c = 0; c < n; c++) {
      if (G.deg(c) % 2 == 0 || G.has(g, c)) continue;
      // TR
      for (int x = 0; x < n; x++) if (G.has(g, x) && G.has(c, x)) {
        uint32_t bad = closedN(G, c) | (1u << x);
        for (uint32_t A = 0; A < (1u << n); A++) {
          if (A & bad) continue;
          if (!good_from_sets(SC[x][c], A)) continue;
          tr_tests++;
          bool adm = !(A & G.adj[g]);
          if (adm) tr_adm++; else { tr_inadm++; }
          if (!adm && (A >> g & 1u)) tr_inadm_gA++;
          if (!good_from_sets(SG[c], A)) { tr_viol++; printf("TRVIOL %s c=%d g=%d x=%d A=%s\n", line.c_str(), c, g, x, sstr(A).c_str()); }
        }
      }
      // TRALL
      for (int u = 0; u < n; u++) if (G.has(g, u)) {
        int t = G.has(c, u);
        for (uint32_t A = 0; A < (1u << n); A++) {
          if (A & ((1u << c) | (1u << u))) continue;
          if (!good_from_sets(SC[u][c], A)) continue;
          ta_tests[t]++;
          if (!good_from_sets(SG[c], A)) { ta_viol[t]++; if (A & G.adj[c]) ta_viol_meetNc[t]++; }
        }
      }
      // ST, ST'
      uint32_t Am = amax(G, c);
      for (uint32_t A = Am; A; A = (A - 1) & Am) {
        if (!blocked(G, c, A)) continue;
        st_inst++;
        bool st = false, stp = false;
        for (int x = 0; x < n; x++) if (G.has(g, x)) {
          bool gd = good_from_sets(SC[x][c], A);
          st |= gd;
          if (!G.has(c, x)) stp |= gd;
          else { Graph K = G; K.rem(g, x); K.rem(x, c); stp |= (good(K, x, A | (1u << c)) == 1); }
        }
        st_ok += st; stp_ok += stp;
        if (!st) printf("STFAIL %s c=%d A=%s\n", line.c_str(), c, sstr(A).c_str());
        if (!stp) {
          bool ngnc = !(G.adj[g] & ~G.adj[c]);
          stp_fail_NgNc += ngnc;
          if (G.deg(g) == 2) { stp_fail_dg2++; int u = __builtin_ctz(G.adj[g]), v = 31 - __builtin_clz(G.adj[g]); if ((A >> g & 1u) && !G.has(u, v)) stp_fail_dg2_gA_uvnonadj++; }
          if (G.deg(g) == 4 && G.deg(c) == 5) stp_fail_dg4dc5++;
          if (getenv("PRINT")) printf("STPFAIL %s g=%d c=%d A=%s\n", line.c_str(), g, c, sstr(A).c_str());
        }
      }
    }
  }
  printf("graphs (one even vertex) = %lld\n", graphs);
  printf("TR: tests %lld, violations %lld; A admissible for G (conclusion = L1*) %lld, A meets N(g) %lld (of which g in A %lld)\n", tr_tests, tr_viol, tr_adm, tr_inadm, tr_inadm_gA);
  printf("TRALL: non-tight tests %lld viol %lld; tight tests %lld viol %lld (meeting N(c): %lld)\n", ta_tests[0], ta_viol[0], ta_tests[1], ta_viol[1], ta_viol_meetNc[1]);
  printf("ST/ST': blocked admissible instances %lld, ST holds %lld, ST' holds %lld\n", st_inst, st_ok, stp_ok);
  printf("ST' failures: %lld; with N(g) in N(c) %lld; d(g)=2 %lld (of which g in A and N(g) non-adjacent %lld); d(g)=4,d(c)=5 %lld\n", st_inst - stp_ok, stp_fail_NgNc, stp_fail_dg2, stp_fail_dg2_gA_uvnonadj, stp_fail_dg4dc5);
}
