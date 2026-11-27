// xcert.cpp: certificates for Conjecture N from the extended move calculus (ext.h).
// usage: xcert [movelist-excluded] < graph6
#include "ext.h"
static std::unordered_map<std::string, char> memo;
static std::string excl;
static bool xrec(const Gr& G0, int c0, uint32_t A0, uint32_t B0) {
  Gr G; int c; uint32_t A, B; xcompact(G0, c0, A0, B0, G, c, A, B);
  if (A >> c & 1) return false;
  std::string k = xkey(G, c, A, B);
  auto it = memo.find(k); if (it != memo.end()) return it->second;
  memo[k] = 0;
  bool r = xbase(G, c, A, B);
  if (!r) { std::vector<XInst> ch; xchildren(G, c, A, B, ch);
    for (auto& x : ch) { if (excl.find(x.mv) != std::string::npos) continue; if (xrec(x.G, x.c, x.A, x.B)) { r = true; break; } } }
  memo[k] = r; return r;
}
static void pcert(const Gr& G0, int c0, uint32_t A0, uint32_t B0, int depth) {
  Gr G; int c; uint32_t A, B; xcompact(G0, c0, A0, B0, G, c, A, B);
  printf("  %*s[", depth * 2, ""); xpr(stdout, G, c, A, B); printf("]");
  if (xbase(G, c, A, B)) { printf(" BASE\n"); return; }
  std::vector<XInst> ch; xchildren(G, c, A, B, ch);
  for (auto& x : ch) { if (excl.find(x.mv) != std::string::npos) continue; if (xrec(x.G, x.c, x.A, x.B)) { printf(" --%c-->\n", x.mv); pcert(x.G, x.c, x.A, x.B, depth + 1); return; } }
  printf(" ???\n");
}
static int showcore = 0;
int main(int argc, char** argv) {
  if (argc > 2) showcore = atoi(argv[2]);
  if (argc > 1) excl = argv[1];
  char line[256]; long long inst = 0, cert = 0, unc = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    if (__builtin_popcount(G.evens()) > 1) continue;
    int g = even_vertex(G);
    if (memo.size() > 6000000) memo.clear();
    for (int y = 0; y < G.N; y++) { if (G.deg(y) % 2 == 0) continue;
      for (int x = 0; x < G.N; x++) {
        if (x == y || G.deg(x) % 2 == 0 || G.has(x, y)) continue;
        uint32_t W = G.adj[y] & ~G.adj[x]; if (g >= 0) W &= ~(1u << g);
        if (!W) continue;
        inst++;
        if (xrec(G, y, 1u << x, 0)) { cert++;
          bool core = g >= 0 && G.has(g, x) && !((G.adj[g] & ~(1u << x) & ~(1u << y)) & ~G.adj[x]);
          if (core && showcore > 0) { showcore--; printf("CORE %s g=%d y=%d x=%d\n", line, g, y, x); pcert(G, y, 1u << x, 0, 0); } }
        else { unc++; printf("UNCERT %s g=%d y=%d x=%d\n", line, g, y, x); }
      }
    }
  }
  printf("XCERT instances=%lld certified=%lld uncertified=%lld\n", inst, cert, unc);
}
