// t_gaproute.cpp: least certificate gap (longest run of consecutive inadmissible intermediate
// instances) for A = Amax, with the authors' moves.h (included unmodified) but move (h) over ALL
// simple g--c routes (MV_ROUTE_ALL = 1, ROUTE_MAXLEN = 64), as Definition 3.2 allows.  Same
// bookkeeping as gap.cpp (a run counter reset at admissible instances).
// usage: [TR=1] t_gaproute KMAX < graph6
#include "moves.h"
#include <unordered_map>
static std::unordered_map<std::string, char> memo[8];
static std::string ikey(const Gr& G, int c, uint32_t A, int r) { std::string k = G.key(); k.push_back((char)G.N); k.push_back((char)c); k.append((const char*)&A, 4); k.push_back((char)r); return k; }
static bool rec(const Gr& G0, int c0, uint32_t A0, int r, int K) {
  Gr G; int c; uint32_t A; compact_inst(G0, c0, A0, G, c, A);
  if (A >> c & 1) return false;
  if (admissible(G, c, A)) r = 0;
  if (r > K) return false;
  std::string k = ikey(G, c, A, r); auto it = memo[K].find(k); if (it != memo[K].end()) return it->second;
  memo[K][k] = 0; bool res = base_case(G, c, A, false);
  if (!res) { std::vector<Inst> ch; children(G, c, A, true, true, ch); for (auto& x : ch) if (rec(x.G, x.c, x.A, r + 1, K)) { res = true; break; } }
  memo[K][k] = res; return res;
}
int main(int argc, char** argv) {
  int KMAX = argc > 1 ? atoi(argv[1]) : 6; MV_TR = getenv("TR") != nullptr; MV_ROUTE_ALL = 1; ROUTE_MAXLEN = 64;
  char line[256]; long long hist[10] = {0}, inst = 0;
  while (fgets(line, sizeof line, stdin)) {
    Gr G; if (!parse_g6(line, G)) continue; char* nl = strchr(line, '\n'); if (nl) *nl = 0;
    if (__builtin_popcount(G.evens()) > 1) continue;
    for (int K = 0; K <= KMAX; K++) if (memo[K].size() > 2000000) memo[K].clear();
    for (int c = 0; c < G.N; c++) { if (!(G.deg(c) & 1)) continue; uint32_t A = amax_of(G, c); inst++;
      int K = 0; while (K <= KMAX && !rec(G, c, A, 0, K)) K++; hist[K]++;
      if (K >= 4) printf("GAP%d %s c=%d\n", K, line, c); }
  }
  printf("SUMMARY (all routes) inst=%lld least-gap histogram:", inst); for (int K = 0; K <= KMAX + 1; K++) printf(" %d:%lld", K, hist[K]); printf("\n");
}
