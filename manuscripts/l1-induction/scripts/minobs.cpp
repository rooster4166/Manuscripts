// minobs.cpp: smallest obstructions to the class C1 (c-admissible: A cap N[c] empty) under Case I.
// From every admissible instance (G, c, A) with c notin N(g) and every A subset of Amax, follow Case I
// steps (targets u in N(g) - A - {c}, keep c) through GOOD instances only (TR / Lemma 2.4 make each
// step goodness-preserving upward).  A DEAD END is a good instance reached this way, not admissible,
// none of whose Case I children is good.  (Then Case I alone, with any target, cannot continue.)
#include "lind.h"
#include <set>
static std::unordered_map<std::string, int> gm;
static int good(const Gr& G, int c, uint32_t A) { std::string k = G.key(); k.push_back((char)G.N); k.push_back((char)c); k.append((const char*)&A, 4);
  auto it = gm.find(k); if (it != gm.end()) return it->second; int r = orc::avoid(G, c, A) == 1; gm[k] = r; return r; }
int main(int argc, char** argv) {
  int maxprint = argc > 1 ? atoi(argv[1]) : 20; int depthmax = argc > 2 ? atoi(argv[2]) : 3;
  char line[256]; long long dead = 0, roots = 0;
  while (fgets(line, sizeof line, stdin)) {
    Gr G; if (!parse_g6(line, G)) continue; char* nl = strchr(line, '\n'); if (nl) *nl = 0;
    if (__builtin_popcount(G.evens()) != 1) continue; int g0 = even_vertex(G);
    for (int c = 0; c < G.N; c++) { if (!(G.deg(c) & 1) || G.has(g0, c)) continue;
      uint32_t A = amax_of(G, c); roots++;
      // BFS over Case I descendants (depth-limited)
      std::vector<std::pair<Gr, int>> frontier{{G, 0}};
      std::set<std::string> seen;
      while (!frontier.empty()) {
        auto [H, d] = frontier.back(); frontier.pop_back();
        std::string k = H.key(); if (seen.count(k)) continue; seen.insert(k);
        int g = even_vertex(H); if (g < 0) continue;
        if (admissible(H, c, A) && d > 0) continue;   // back in C0: the IH applies
        bool anyg = false; int nch = 0;
        for (int u = 0; u < H.N; u++) if (H.has(g, u) && u != c && !(A >> u & 1)) {
          Gr K = H; K.del(g, u); nch++;
          if (good(K, c, A)) { anyg = true; if (d + 1 <= depthmax) frontier.push_back({K, d + 1}); }
        }
        if (!anyg && d > 0) { dead++; if (maxprint-- > 0) { printf("DEADEND root=%s c=%d depth=%d g=%d d(g)=%d nch=%d A=", line, c, d, g, H.deg(g), nch); print_set(stdout, A);
          printf(" N(g)="); print_set(stdout, H.adj[g]); printf(" E: "); print_edges(stdout, H); printf("\n"); } }
      }
    }
  }
  printf("SUMMARY roots=%lld deadends=%lld\n", roots, dead);
}
