// repair.cpp: for each TRN instance and each good D' whose plain Fan image is bad, find the good D''
// whose chain avoids y and whose transition system differs from D' at the fewest vertices.  Report
// the distribution of that distance and the roles of the changed vertices.
#include "dec.h"
#include <map>
using namespace dec;
typedef std::vector<uint64_t> Trans;  // per vertex: encoded pairing
// encode transition at v: for each pair (a,b) a<b set bit a*32+b in a small sorted list; use a hash
static Trans trans_of(const Decomp& D, int n) {
  // exact encoding: for each vertex v, partner[w] (4 bits) = neighbour paired with w at v, 15 if w is
  // the terminal edge at v or not a neighbour.  Requires n <= 15.
  std::vector<std::vector<int>> part(n, std::vector<int>(n, 15));
  for (auto& p : D)
    for (size_t i = 1; i + 1 < p.size(); i++) { int v = p[i]; part[v][p[i - 1]] = p[i + 1]; part[v][p[i + 1]] = p[i - 1]; }
  Trans T(n);
  for (int v = 0; v < n; v++) { uint64_t h = 0; for (int w = 0; w < n; w++) h = h * 16 + part[v][w]; T[v] = h; }
  return T;
}
int main(int argc, char** argv) {
  char line[256]; long long hist[20]; memset(hist, 0, sizeof hist);
  long long roleCnt[8]; memset(roleCnt, 0, sizeof roleCnt); long long nfail = 0; std::map<std::string,long long> combo;
  const char* rn[8] = {"y", "u", "g", "e", "chain(other)", "x", "N(y) other", "other"};
  int pr = argc > 1 ? atoi(argv[1]) : 0; int printed = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    if (__builtin_popcount(G.evens()) != 1) continue;
    int g = even_vertex(G), n = G.N;
    for (int u = 0; u < n; u++) { if (!G.has(g, u)) continue;
      Gr H = G; H.del(g, u);
      for (int y = 0; y < n; y++) { if (G.deg(y) % 2 == 0 || !G.has(y, u)) continue;
        for (int x = 0; x < n; x++) {
          if (x == y || x == u || G.deg(x) % 2 == 0 || G.has(x, y)) continue;
          std::vector<Trans> goodT; std::vector<Decomp> goodD;
          std::vector<Trans> badT; std::vector<Decomp> badD; std::vector<std::vector<int>> badCh;
          enumerate(H, y, 1u << x, 0, [&](const Decomp& D) {
            std::vector<int> ch; Decomp R = fan_forced(D, g, u, ch);
            bool av = std::find(ch.begin(), ch.end(), y) == ch.end();
            bool gd = path_avoids(R[path_end_at(R, y)], 1u << x);
            if (av) { goodT.push_back(trans_of(D, n)); goodD.push_back(D); }
            else if (!gd) { badT.push_back(trans_of(D, n)); badD.push_back(D); badCh.push_back(ch); }
            return false; });
          for (size_t b = 0; b < badT.size(); b++) {
            nfail++;
            int best = 99; size_t bi = 0;
            for (size_t j = 0; j < goodT.size(); j++) {
              int d = 0; for (int v = 0; v < n; v++) if (goodT[j][v] != badT[b][v]) d++;
              if (d < best) { best = d; bi = j; }
            }
            hist[std::min(best, 19)]++;
            if (best < 99) {
              // roles of changed vertices
              const std::vector<int>& ch = badCh[b];
              int ei = (int)(std::find(ch.begin(), ch.end(), y) - ch.begin()) - 1; int e = ch[ei];
              // all nearest repairs: union of role-sets
              std::string best_key = "~";
              for (size_t j = 0; j < goodT.size(); j++) {
                int d = 0; for (int v = 0; v < n; v++) if (goodT[j][v] != badT[b][v]) d++;
                if (d != best) continue;
                std::string key;
                for (int v = 0; v < n; v++) if (goodT[j][v] != badT[b][v]) {
                  char c; if (v == y) c = 'y'; else if (v == u) c = 'u'; else if (v == g) c = 'g'; else if (v == e) c = 'e';
                  else if (std::find(ch.begin(), ch.end(), v) != ch.end()) c = 'c'; else if (v == x) c = 'x';
                  else if (G.has(y, v)) c = 'n'; else c = 'o';
                  key += c; }
                std::sort(key.begin(), key.end());
                if (key < best_key) best_key = key;
              }
              combo[std::to_string(best) + ":" + best_key]++;
              for (int v = 0; v < n; v++) if (goodT[bi][v] != badT[b][v]) {
                int r;
                if (v == y) r = 0; else if (v == u) r = 1; else if (v == g) r = 2; else if (v == e) r = 3;
                else if (std::find(ch.begin(), ch.end(), v) != ch.end()) r = 4; else if (v == x) r = 5;
                else if (G.has(y, v)) r = 6; else r = 7;
                roleCnt[r]++;
              }
              if (pr && printed < pr) { printed++;
                printf("%s g=%d y=%d x=%d u=%d dist=%d\n  bad : ", line, g, y, x, u, best);
                for (auto& p : badD[b]) { for (int v : p) printf("%d", v); printf(" "); }
                printf(" chain="); for (int v : ch) printf("%d", v);
                printf("\n  good: "); for (auto& p : goodD[bi]) { for (int v : p) printf("%d", v); printf(" "); }
                printf(" changed="); for (int v = 0; v < n; v++) if (goodT[bi][v] != badT[b][v]) printf("%d", v); printf("\n"); }
            }
          }
        }
      }
    }
  }
  printf("bad D' = %lld; nearest chain-avoiding good D'' distance histogram:", nfail);
  for (int k = 0; k < 20; k++) if (hist[k]) printf(" %d:%lld", k, hist[k]); printf("\n roles of changed vertices:");
  for (int r = 0; r < 8; r++) printf(" %s=%lld", rn[r], roleCnt[r]); printf("\n");
  for (auto& kv : combo) printf("  %s %lld\n", kv.first.c_str(), kv.second);
}
