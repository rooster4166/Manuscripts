// gap.cpp: certificates of Rec (moves.h) in which every run of consecutive inadmissible intermediate
// instances has length <= K.  For each admissible instance (A = Amax) report the least such K (<= KMAX).
#include "moves.h"
static bool fB = true, fM = true;
static int KMAX;
static std::unordered_map<std::string, char> memo[8];
static std::string ikey(const Gr& G, int c, uint32_t A, int r) { std::string k = G.key(); k.push_back((char)G.N); k.push_back((char)c); k.append((const char*)&A, 4); k.push_back((char)r); return k; }
static bool rec(const Gr& G0, int c0, uint32_t A0, int r, int K) {
  Gr G; int c; uint32_t A; compact_inst(G0, c0, A0, G, c, A);
  if (A >> c & 1) return false;
  if (admissible(G, c, A)) r = 0;
  if (r > K) return false;
  std::string k = ikey(G, c, A, r);
  auto it = memo[K].find(k); if (it != memo[K].end()) return it->second;
  memo[K][k] = 0;
  bool res = base_case(G, c, A, false);
  if (!res) { std::vector<Inst> ch; children(G, c, A, fB, fM, ch); for (auto& x : ch) if (rec(x.G, x.c, x.A, r + 1, K)) { res = true; break; } }
  memo[K][k] = res; return res;
}
static void pc(const Gr& G0, int c0, uint32_t A0, int r, int K, int depth) {
  Gr G; int c; uint32_t A; compact_inst(G0, c0, A0, G, c, A);
  if (admissible(G, c, A)) r = 0;
  int g = even_vertex(G);
  printf("  %*s[N=%d m=%d g=%d d(g)=%d c=%d d(c)=%d A=", depth, "", G.N, G.nedges(), g, g >= 0 ? G.deg(g) : 0, c, G.deg(c)); print_set(stdout, A); printf(" adm=%d]", (int)admissible(G, c, A));
  if (base_case(G, c, A, false)) { printf(" BASE\n"); return; }
  std::vector<Inst> ch; children(G, c, A, fB, fM, ch);
  for (auto& x : ch) if (rec(x.G, x.c, x.A, r + 1, K)) { printf(" --%c-->\n", x.mv); pc(x.G, x.c, x.A, r + 1, K, depth + 1); return; }
  printf(" ???\n");
}
int main(int argc, char** argv) {
  KMAX = argc > 1 ? atoi(argv[1]) : 4;
  char line[256]; long long hist[10] = {0}, bhist[10] = {0}, inst = 0;
  while (fgets(line, sizeof line, stdin)) {
    Gr G; if (!parse_g6(line, G)) continue; char* nl = strchr(line, '\n'); if (nl) *nl = 0;
    if (__builtin_popcount(G.evens()) > 1) continue; int g = even_vertex(G);
    for (int K = 0; K <= KMAX; K++) if (memo[K].size() > 2000000) memo[K].clear();
    for (int c = 0; c < G.N; c++) { if (!(G.deg(c) & 1)) continue;
      uint32_t A = amax_of(G, c); inst++;
      bool isb = false;
      if (g >= 0 && !G.has(g, c)) { isb = true; for (int u = 0; u < G.N; u++) if (G.has(g, u) && !(G.adj[u] & A & ~(1u << g))) isb = false; }
      int K = 0; while (K <= KMAX && !rec(G, c, A, 0, K)) K++;
      hist[K]++; if (isb) bhist[K]++;
      if (K >= 2) { printf("GAP%d %s c=%d g=%d blocked=%d\n", K, line, c, g, (int)isb); if (argc > 2 && K >= atoi(argv[2])) pc(G, c, A, 0, K, 0); fflush(stdout); }
    }
  }
  printf("SUMMARY inst=%lld least-gap histogram (all / blocked):", inst);
  for (int K = 0; K <= KMAX + 1; K++) printf(" %d:%lld/%lld", K, hist[K], bhist[K]);
  printf("  (%d = none within KMAX)\n", KMAX + 1);
}
