// rec2.cpp: certificate class Rec built from moves.h, with exploration of failures.
// usage: rec2 MODE FLAGS < graph6
//   FLAGS: B boundary, M section-5 moves, S separation base, R all routes (length <= 4)
//   MODE adm     : every (G, c) with <= 1 even vertex, A = Amax.  NOREC lines + summary.
//   MODE explore : as adm, and for each NOREC instance search the good-but-not-Rec part of the move
//                  tree for STUCK instances (good, not a base case, every child bad).
#include "moves.h"

static bool fB, fM, fS;
static std::unordered_map<std::string, char> memo;
static long long nstates;

static std::string ikey(const Gr& G, int c, uint32_t A) {
  std::string k = G.key(); k.push_back((char)G.N); k.push_back((char)c); k.append((const char*)&A, 4); return k;
}

static bool rec(const Gr& G0, int c0, uint32_t A0) {
  Gr G; int c; uint32_t A; compact_inst(G0, c0, A0, G, c, A);
  if (A >> c & 1) return false;
  std::string k = ikey(G, c, A);
  auto it = memo.find(k); if (it != memo.end()) return it->second;
  nstates++; memo[k] = 0;
  bool r = base_case(G, c, A, fS);
  if (!r) { std::vector<Inst> ch; children(G, c, A, fB, fM, ch); for (auto& x : ch) if (rec(x.G, x.c, x.A)) { r = true; break; } }
  memo[k] = r; return r;
}

static std::unordered_map<std::string, int> goodmemo;
static int good(const Gr& G0, int c0, uint32_t A0) {
  Gr G; int c; uint32_t A; compact_inst(G0, c0, A0, G, c, A);
  std::string k = ikey(G, c, A);
  auto it = goodmemo.find(k); if (it != goodmemo.end()) return it->second;
  int r = orc::avoid(G, c, A) == 1; goodmemo[k] = r; return r;
}

static long long nstuck = 0;
static void explore(const Gr& G0, int c0, uint32_t A0, int depth, std::unordered_set<std::string>& seen, const char* root, int maxprint) {
  Gr G; int c; uint32_t A; compact_inst(G0, c0, A0, G, c, A);
  std::string k = ikey(G, c, A);
  if (seen.count(k)) return; seen.insert(k);
  std::vector<Inst> ch; children(G, c, A, fB, fM, ch);
  bool anygood = false;
  for (auto& x : ch) if (good(x.G, x.c, x.A)) { anygood = true; if (!rec(x.G, x.c, x.A)) explore(x.G, x.c, x.A, depth + 1, seen, root, maxprint); }
  if (!anygood) {
    nstuck++;
    if (maxprint-- > 0) {
      int g = even_vertex(G);
      printf("STUCK root=%s depth=%d N=%d g=%d c=%d A=", root, depth, G.N, g, c); print_set(stdout, A);
      printf(" degs:"); for (int v = 0; v < G.N; v++) printf("%d", G.deg(v) > 9 ? 9 : G.deg(v));
      printf(" adm=%d nch=%zu E: ", (int)admissible(G, c, A), ch.size()); print_edges(stdout, G); printf("\n");
    }
  }
}


static void print_cert(const Gr& G0, int c0, uint32_t A0, int depth) {
  Gr G; int c; uint32_t A; compact_inst(G0, c0, A0, G, c, A);
  int g = even_vertex(G);
  printf("  %*s[N=%d g=%d c=%d A=", depth, "", G.N, g, c); print_set(stdout, A);
  printf(" adm=%d]", (int)admissible(G, c, A));
  if (base_case(G, c, A, fS)) { printf(" BASE\n"); return; }
  std::vector<Inst> ch; children(G, c, A, fB, fM, ch);
  for (auto& x : ch) if (rec(x.G, x.c, x.A)) { printf(" --%c-->\n", x.mv); print_cert(x.G, x.c, x.A, depth + 1); return; }
  printf(" ???\n");
}
int main(int argc, char** argv) {
  if (argc < 2) { fprintf(stderr, "usage\n"); return 1; }
  std::string mode = argv[1];
  const char* fl = argc > 2 ? argv[2] : "";
  fB = strchr(fl, 'B'); fM = strchr(fl, 'M'); fS = strchr(fl, 'S'); MV_ROUTE_ALL = strchr(fl, 'R') != nullptr;
  char line[256];
  long long inst = 0, norec = 0, blocked = 0, norec_blocked = 0;
  while (fgets(line, sizeof line, stdin)) {
    Gr G; if (!parse_g6(line, G)) continue;
    char* nl = strchr(line, '\n'); if (nl) *nl = 0;
    if (__builtin_popcount(G.evens()) > 1) continue;
    int g = even_vertex(G);
    if (memo.size() > 3000000) memo.clear();
    if (goodmemo.size() > 3000000) goodmemo.clear();
    for (int c = 0; c < G.N; c++) {
      if (!(G.deg(c) & 1)) continue;
      uint32_t A = amax_of(G, c);
      inst++;
      bool isb = false;
      if (g >= 0 && !G.has(g, c)) { isb = true; for (int u = 0; u < G.N; u++) if (G.has(g, u) && !(G.adj[u] & A & ~(1u << g))) isb = false; }
      blocked += isb;
      if (mode == "stuck0") {
        if (base_case(G, c, A, fS)) continue;
        std::vector<Inst> ch; children(G, c, A, fB, fM, ch);
        bool anyg = false; for (auto& x : ch) if (good(x.G, x.c, x.A)) { anyg = true; break; }
        if (!anyg) { nstuck++; printf("STUCK0 %s %d ", line, c); print_set(stdout, A); printf(" g=%d blocked=%d nch=%zu\n", g, (int)isb, ch.size()); fflush(stdout); }
        continue;
      }
      if (mode == "cert" && isb) { if (rec(G, c, A)) { printf("CERT %s g=%d c=%d\n", line, g, c); print_cert(G, c, A, 0); } }
      if (!rec(G, c, A)) {
        norec++; norec_blocked += isb;
        printf("NOREC %s g=%d c=%d A=", line, g, c); print_set(stdout, A); printf(" blocked=%d\n", (int)isb); fflush(stdout);
        if (mode == "explore") { std::unordered_set<std::string> seen; explore(G, c, A, 0, seen, line, 3); fflush(stdout); }
      }
    }
  }
  printf("SUMMARY instances=%lld blocked=%lld notRec=%lld notRec_blocked=%lld stuck=%lld flags=%s\n", inst, blocked, norec, norec_blocked, nstuck, fl);
  return 0;
}
