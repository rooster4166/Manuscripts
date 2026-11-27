// ncert.cpp: are the Conjecture-N instances certified by the proved transfer calculus?
// (session claude/conj-n).  Instance (G, y, {x}): G at most one even vertex g, x, y odd, x !~ y,
// y has a neighbour w != g with w !~ x.  Certified = in Rec (moves.h of l1-induction, flags BMS,
// plus the L1 set-form base of dlrec.cpp).
// usage: ncert [FLAGS] < graph6   FLAGS default BMS; add R for all routes in (h)  (prints UNCERT lines, then a summary)
#include "moves.h"
#include <unordered_map>
static bool fB = true, fM = true, fS = true;
static std::unordered_map<std::string, char> memo;
static std::string ikey(const Gr& G, int c, uint32_t A) {
  std::string k = G.key(); k.push_back((char)G.N); k.push_back((char)c); k.append((const char*)&A, 4); return k;
}
static bool base2(const Gr& G, int c, uint32_t A) {
  if (base_case(G, c, A, fS)) return true;
  if (even_vertex(G) < 0 && packed_set(G, A) && !(A & closed_nbhd(G, c))) return true;
  return false;
}
static bool rec(const Gr& G0, int c0, uint32_t A0) {
  Gr G; int c; uint32_t A; compact_inst(G0, c0, A0, G, c, A);
  if (A >> c & 1) return false;
  std::string k = ikey(G, c, A);
  auto it = memo.find(k); if (it != memo.end()) return it->second;
  memo[k] = 0;
  bool r = base2(G, c, A);
  if (!r) { std::vector<Inst> ch; children(G, c, A, fB, fM, ch); for (auto& x : ch) if (rec(x.G, x.c, x.A)) { r = true; break; } }
  memo[k] = r; return r;
}
int main(int argc, char** argv) {
  if (argc > 1) { fB = strchr(argv[1], 'B'); fM = strchr(argv[1], 'M'); fS = strchr(argv[1], 'S');
    if (strchr(argv[1], 'R')) { MV_ROUTE_ALL = 1; ROUTE_MAXLEN = 64; } }  // R: all g--c routes for (h)
  char line[256]; long long inst = 0, cert = 0, unc = 0, good = 0, bad = 0, xg = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    if (__builtin_popcount(G.evens()) > 1) continue;
    int g = even_vertex(G);
    if (memo.size() > 4000000) memo.clear();
    for (int y = 0; y < G.N; y++) {
      if (G.deg(y) % 2 == 0) continue;
      for (int x = 0; x < G.N; x++) {
        if (x == y || G.deg(x) % 2 == 0 || G.has(x, y)) continue;
        uint32_t W = G.adj[y] & ~G.adj[x]; if (g >= 0) W &= ~(1u << g);
        if (!W) continue;
        inst++;
        if (g >= 0 && G.has(g, x)) xg++;
        if (rec(G, y, 1u << x)) { cert++; continue; }
        unc++;
        int o = orc::avoid(G, y, 1u << x);
        if (o == 1) good++; else bad++;
        printf("UNCERT %s g=%d y=%d x=%d good=%d\n", line, g, y, x, o);
      }
    }
  }
  printf("NCERT instances=%lld (x~g %lld) certified=%lld uncertified=%lld (good %lld, not good %lld)\n", inst, xg, cert, unc, good, bad);
}
