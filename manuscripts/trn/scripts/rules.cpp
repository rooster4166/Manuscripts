// rules.cpp: test extremal-choice rules for TRN.  For each instance, among all good D' of G-gu
// (Q'(y) avoids x), a rule picks the D' minimising a key; the rule "holds" on the instance if every
// minimiser has its forced chain avoiding y (AV) / has a good Fan image (GD).
#include "dec.h"
using namespace dec;
static const int NR = 12;
static const char* rname[NR] = {
  "min|Q'y|", "max|Q'y|", "yu-first,then min|Q'y|", "min chain len", "max chain len",
  "min|P0|", "max|P0|", "Q'y ends at g first", "min |Q'y cap N(u)|", "max |Q'y cap N(u)|",
  "min #paths thru u", "max |P_yu|"};
int main(int argc, char** argv) {
  char line[256];
  long long inst[2] = {0, 0}, failAV[NR][2], failGD[NR][2];
  memset(failAV, 0, sizeof failAV); memset(failGD, 0, sizeof failGD);
  int pr = argc > 1 ? atoi(argv[1]) : 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    if (__builtin_popcount(G.evens()) != 1) continue;
    int g = even_vertex(G);
    for (int u = 0; u < G.N; u++) { if (!G.has(g, u)) continue;
      Gr H = G; H.del(g, u);
      for (int y = 0; y < G.N; y++) { if (G.deg(y) % 2 == 0 || !G.has(y, u)) continue;
        for (int x = 0; x < G.N; x++) {
          if (x == y || x == u || G.deg(x) % 2 == 0 || G.has(x, y)) continue;
          long long best[NR]; bool allAV[NR], allGD[NR];
          for (int r = 0; r < NR; r++) { best[r] = (1LL << 60); allAV[r] = allGD[r] = true; }
          long long nD = 0;
          enumerate(H, y, 1u << x, 0, [&](const Decomp& D) {
            nD++;
            std::vector<int> ch; Decomp R = fan_forced(D, g, u, ch);
            bool av = std::find(ch.begin(), ch.end(), y) == ch.end();
            bool gd = path_avoids(R[path_end_at(R, y)], 1u << x);
            int qi = path_end_at(D, y); const Path& Q = D[qi];
            int p0 = path_end_at(D, g);
            long long lq = Q.size();
            bool yufirst = Q.size() >= 2 && Q[1] == u;
            bool endsg = (Q.front() == g || Q.back() == g);
            int qnu = 0; for (int v : Q) if (H.has(v, u)) qnu++;
            int thru = 0; size_t lyu = 0;
            for (auto& p : D) { bool has = false; for (size_t i = 0; i < p.size(); i++) { if (p[i] == u) has = true;
                if (i + 1 < p.size() && ((p[i] == y && p[i + 1] == u) || (p[i] == u && p[i + 1] == y))) lyu = p.size(); }
              if (has) thru++; }
            long long key[NR] = { lq, -lq, (yufirst ? 0 : 100) + lq, (long long)ch.size(), -(long long)ch.size(),
              (long long)D[p0].size(), -(long long)D[p0].size(), endsg ? 0 : 1, qnu, -qnu, thru, -(long long)lyu };
            for (int r = 0; r < NR; r++) {
              if (key[r] < best[r]) { best[r] = key[r]; allAV[r] = av; allGD[r] = gd; }
              else if (key[r] == best[r]) { allAV[r] = allAV[r] && av; allGD[r] = allGD[r] && gd; }
            }
            return false; });
          if (!nD) continue;
          int adj = G.has(g, y); inst[adj]++;
          for (int r = 0; r < NR; r++) { if (!allAV[r]) failAV[r][adj]++; if (!allGD[r]) { failGD[r][adj]++;
              if (pr) printf("RULEFAIL %d %s g=%d y=%d x=%d u=%d\n", r, line, g, y, x, u); } }
        }
      }
    }
  }
  printf("instances y!~g=%lld y~g=%lld\n", inst[0], inst[1]);
  for (int r = 0; r < NR; r++) printf("%-26s failAV %lld/%lld  failGD %lld/%lld\n", rname[r], failAV[r][0], failAV[r][1], failGD[r][0], failGD[r][1]);
}
