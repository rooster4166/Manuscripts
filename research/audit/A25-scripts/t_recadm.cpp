// t_recadm.cpp: Rec (the authors' moves.h, included unmodified from the audited snapshot) with and
// without the restriction that every intermediate (non-base) instance be admissible.  Tests the
// claim of section 3 that cert.py failed on 35 of the 1,868 order-7 instances with |A| <= 2 BECAUSE
// it required admissible intermediates.  Also checks every Rec-certified instance with the a25
// oracle (soundness of the implementation) on all A (admissible or not) with c notin A.
// build: g++ -O2 -std=c++17 -I<snapshot>/manuscripts/l1-induction/scripts t_recadm.cpp
// usage: t_recadm MODE < graph6    MODE = k2 (|A| <= 2, admissible) | all (every A with c notin A)
#include "moves.h"
#include "a25.h"
#include <unordered_map>
static std::unordered_map<std::string, char> memo[2];
static std::string ikey(const Gr& G, int c, uint32_t A) { std::string k = G.key(); k.push_back((char)G.N); k.push_back((char)c); k.append((const char*)&A, 4); return k; }
static bool rec(const Gr& G0, int c0, uint32_t A0, int admOnly) {
  Gr G; int c; uint32_t A; compact_inst(G0, c0, A0, G, c, A);
  if (A >> c & 1) return false;
  std::string k = ikey(G, c, A);
  auto it = memo[admOnly].find(k); if (it != memo[admOnly].end()) return it->second;
  memo[admOnly][k] = 0;
  bool r = base_case(G, c, A, false);
  if (!r && (!admOnly || admissible(G, c, A))) { std::vector<Inst> ch; children(G, c, A, true, true, ch); for (auto& x : ch) if (rec(x.G, x.c, x.A, admOnly)) { r = true; break; } }
  memo[admOnly][k] = r; return r;
}
static a25::Graph conv(const Gr& G) { a25::Graph H; H.n = G.N; for (int v = 0; v < G.N; v++) H.adj[v] = G.adj[v]; return H; }
int main(int argc, char** argv) {
  std::string mode = argc > 1 ? argv[1] : "k2"; MV_TR = getenv("TR") != nullptr;
  char line[256]; long long inst = 0, inRec = 0, inRecAdm = 0, soundTests = 0, unsound = 0;
  while (fgets(line, sizeof line, stdin)) {
    Gr G; if (!parse_g6(line, G)) continue; char* nl = strchr(line, '\n'); if (nl) *nl = 0;
    if (__builtin_popcount(G.evens()) > 1) continue;
    a25::Graph H = conv(G);
    for (int c = 0; c < G.N; c++) { if (!(G.deg(c) & 1)) continue;
      if (mode == "k2") {
        uint32_t Am = amax_of(G, c);
        for (uint32_t A = Am; A; A = (A - 1) & Am) { if (__builtin_popcount(A) > 2) continue;
          inst++; bool r = rec(G, c, A, 0), ra = rec(G, c, A, 1); inRec += r; inRecAdm += ra;
          if (!ra) printf("NOT-IN-REC-ADM %s c=%d A=", line, c), print_set(stdout, A), printf(" inRec=%d\n", (int)r); }
      } else {
        for (uint32_t A = 0; A < (1u << G.N); A++) { if (A >> c & 1) continue;
          if (rec(G, c, A, 0)) { soundTests++; if (a25::good(H, c, A) != 1) { unsound++; printf("UNSOUND %s c=%d A=", line, c); print_set(stdout, A); printf("\n"); } } }
      }
    }
  }
  if (mode == "k2") printf("SUMMARY |A|<=2 instances=%lld inRec=%lld inRec_admissible_intermediates=%lld\n", inst, inRec, inRecAdm);
  else printf("SUMMARY Rec-certified (G,c,A) with c notin A, any A: %lld; not good by a25 oracle: %lld\n", soundTests, unsound);
}
