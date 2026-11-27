// t_recroute.cpp: does the restriction of move (h) in moves.h (at most 8 SHORTEST g--c paths in G - A)
// change the Rec counts, compared with Definition 3.2, where (h) allows ANY path g r1..r_{k-1} c with
// interior outside A?  Includes the authors' moves.h unmodified and sets its globals
// MV_ROUTE_ALL = 1, ROUTE_MAXLEN = 64 (all simple routes).  A = Amax for every (G, c).
// build: g++ -O2 -std=c++17 -I<snapshot>/manuscripts/l1-induction/scripts t_recroute.cpp
// usage: t_recroute [T][S] < graph6      (T: also the TR move (t); S: every admissible A, not only Amax)
#include "moves.h"
#include <unordered_map>
static std::unordered_map<std::string, char> memo; static bool SUB = false;
static std::string ikey(const Gr& G, int c, uint32_t A) { std::string k = G.key(); k.push_back((char)G.N); k.push_back((char)c); k.append((const char*)&A, 4); return k; }
static bool rec(const Gr& G0, int c0, uint32_t A0) {
  Gr G; int c; uint32_t A; compact_inst(G0, c0, A0, G, c, A);
  if (A >> c & 1) return false;
  std::string k = ikey(G, c, A); auto it = memo.find(k); if (it != memo.end()) return it->second;
  memo[k] = 0; bool r = base_case(G, c, A, false);
  if (!r) { std::vector<Inst> ch; children(G, c, A, true, true, ch); for (auto& x : ch) if (rec(x.G, x.c, x.A)) { r = true; break; } }
  memo[k] = r; return r;
}
int main(int argc, char** argv) {
  MV_TR = argc > 1 && strchr(argv[1], 'T'); MV_ROUTE_ALL = 1; ROUTE_MAXLEN = 64; SUB = argc > 1 && strchr(argv[1], 'S');
  char line[256]; long long inst = 0, norec = 0, norecb = 0;
  while (fgets(line, sizeof line, stdin)) {
    Gr G; if (!parse_g6(line, G)) continue; char* nl = strchr(line, '\n'); if (nl) *nl = 0;
    if (__builtin_popcount(G.evens()) > 1) continue; int g = even_vertex(G);
    if (memo.size() > 3000000) memo.clear();
    for (int c = 0; c < G.N; c++) { if (!(G.deg(c) & 1)) continue; uint32_t Am = amax_of(G, c);
     for (uint32_t A = Am; A; A = (A - 1) & Am) { if (!SUB && A != Am) continue; inst++;
      bool isb = false; if (g >= 0 && !G.has(g, c)) { isb = true; for (int u = 0; u < G.N; u++) if (G.has(g, u) && !(G.adj[u] & A & ~(1u << g))) isb = false; }
      if (!rec(G, c, A)) { norec++; norecb += isb; printf("NOREC %s g=%d c=%d A=", line, g, c); print_set(stdout, A); printf(" blocked=%d\n", (int)isb); } } }
  }
  printf("SUMMARY (all routes) instances=%lld notRec=%lld notRec_blocked=%lld TR=%d\n", inst, norec, norecb, MV_TR);
}
