// walk2.cpp: census of Proposition (walk to a degree-two vertex).  Blocked instances, A = Amax.
// Trail g = w0, w1, ..., wk (k >= 1), edge-distinct, w_i notin A + N[c] (mode 0) or w_i notin A + c
// (mode 1, using TR at tight targets); success if in G - E(W) the end wk has degree 2 with
// non-adjacent neighbours x, y (then split off wk: an admissible all-odd instance), or wk has no
// neighbour in A (Fan route, l1star Prop. 5.3).
#include "lind.h"
static uint32_t AA, FORB; static int maxlen; static int split_found, route_found;
static void dfs(Gr& H, int w, int len) {
  if (split_found && route_found) return;
  if (len >= 1) {
    if (!(H.adj[w] & AA)) route_found = 1;
    if (H.deg(w) == 2) { int x = __builtin_ctz(H.adj[w]), y = 31 - __builtin_clz(H.adj[w]); if (!H.has(x, y)) split_found = 1; }
  }
  if (len >= maxlen) return;
  uint32_t nb = H.adj[w] & ~AA & ~FORB;
  while (nb) { int v = __builtin_ctz(nb); nb &= nb - 1; H.del(w, v); dfs(H, v, len + 1); H.add(w, v); }
}
int main(int argc, char** argv) {
  int mode = argc > 1 ? atoi(argv[1]) : 0; maxlen = argc > 2 ? atoi(argv[2]) : 10;
  char line[256]; long long inst = 0, sp = 0, ro = 0, either = 0, sponly = 0;
  while (fgets(line, sizeof line, stdin)) {
    Gr G; if (!parse_g6(line, G)) continue; if (__builtin_popcount(G.evens()) != 1) continue; int g = even_vertex(G);
    for (int c = 0; c < G.N; c++) { if (!(G.deg(c) & 1) || G.has(g, c)) continue;
      uint32_t A = amax_of(G, c);
      bool isb = true; for (int u = 0; u < G.N; u++) if (G.has(g, u) && !(G.adj[u] & A & ~(1u << g))) isb = false;
      if (!isb) continue; inst++;
      AA = A; FORB = mode == 0 ? closed_nbhd(G, c) : (1u << c); split_found = route_found = 0;
      Gr H = G; dfs(H, g, 0);
      sp += split_found; ro += route_found; either += (split_found || route_found); sponly += (split_found && !route_found);
    }
  }
  printf("SUMMARY mode=%d blocked=%lld  walk-to-degree-two=%lld  Fan-route=%lld  either=%lld  (degree-two only=%lld)\n", mode, inst, sp, ro, either, sponly);
}
