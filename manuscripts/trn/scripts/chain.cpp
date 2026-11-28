// chain.cpp: for every TRN instance (G, g, y, x, u) with (G-gu, y, {x}) good, enumerate all good
// Lovász decompositions D' of G-gu (Q'(y) avoids x), run Fan's forced chain g -> u, and classify.
//   avoid  : chain avoids y (Lemma avoidc => image good)
//   good   : plain Fan image has x notin Q(y)
// Instance classes:  A = some D' with chain avoiding y;  B = some D' with good image;  C = neither.
#include "dec.h"
using namespace dec;
static int findQ(const Decomp& D, int c) { return path_end_at(D, c); }
int main(int argc, char** argv) {
  long long cap = argc > 1 ? atoll(argv[1]) : 2000000;
  int verbose = argc > 2 ? atoi(argv[2]) : 0;
  char line[256];
  long long inst[2] = {0, 0}, clsA[2] = {0, 0}, clsB[2] = {0, 0}, clsC[2] = {0, 0}, capped = 0;
  long long totD[2] = {0, 0}, totAv[2] = {0, 0}, totGood[2] = {0, 0}, allGood[2] = {0, 0};
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    if (__builtin_popcount(G.evens()) != 1) continue;
    int g = even_vertex(G);
    for (int y = 0; y < G.N; y++) { if (G.deg(y) % 2 == 0) continue;
      for (int x = 0; x < G.N; x++) {
        if (x == y || G.deg(x) % 2 == 0 || G.has(x, y)) continue;
        int adj = G.has(g, y);
        for (int u = 0; u < G.N; u++) {
          if (u == x || !G.has(g, u) || !G.has(y, u)) continue;
          Gr H = G; H.del(g, u);
          long long nD = 0, nAv = 0, nGood = 0;
          enumerate(H, y, 1u << x, cap, [&](const Decomp& D) {
            nD++;
            std::vector<int> ch; Decomp R = fan_forced(D, g, u, ch);
            if (!check_decomp(G, R)) { fprintf(stderr, "bad image\n"); exit(1); }
            bool hit = std::find(ch.begin(), ch.end(), y) != ch.end();
            if (!hit) nAv++;
            int qi = findQ(R, y);
            bool ok = path_avoids(R[qi], 1u << x);
            if (ok) nGood++;
            if (!hit && !ok) { fprintf(stderr, "avoid but bad?! %s\n", line); exit(1); }
            return false; });
          if (nD == 0) continue;
          if (nD >= cap) capped++;
          inst[adj]++; totD[adj] += nD; totAv[adj] += nAv; totGood[adj] += nGood;
          if (nGood == nD) allGood[adj]++;
          if (nAv) clsA[adj]++; else if (nGood) clsB[adj]++; else clsC[adj]++;
          if (verbose && (nAv == 0)) printf("%s %s g=%d y=%d x=%d u=%d nD=%lld nAv=%lld nGood=%lld\n", nGood ? "CLS_B" : "CLS_C", line, g, y, x, u, nD, nAv, nGood);
        }
      }
    }
  }
  for (int a = 0; a < 2; a++)
    printf("y%sg: inst=%lld  A(chain avoids y)=%lld  B(only image good)=%lld  C(no good image)=%lld  allD'good=%lld  D'=%lld avoid=%lld good=%lld\n",
           a ? "~" : "!~", inst[a], clsA[a], clsB[a], clsC[a], allGood[a], totD[a], totAv[a], totGood[a]);
  printf("capped=%lld\n", capped);
}
