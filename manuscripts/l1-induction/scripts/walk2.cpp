// walk2.cpp: census of Proposition 3.3 (walk to a degree-two vertex) and of Fan trails.
// Blocked instances, A = Amax.  Trail g = w0, w1, ..., wk (k >= 1), edge-distinct, w_i notin A + {c}.
//   mode 0: w_i notin N[c] (Proposition 3.3 as proved; Fan trail = trail form of l1star Prop 5.3
//           without its d(c) = 1 clause);
//   mode 1: tight w_i (in N(c)) allowed, restricted to what TR licenses (audit A25, F3):
//           a tight w_i only after a non-tight w_{i-1} (TR needs the source not adjacent to c), and
//           a split at a tight end w_k only if its remaining neighbour other than c is not in A
//           (G* gains the edge from c to that neighbour);
//   mode 3: l1star Proposition 5.3 exactly as stated: simple paths g e1 ... ek avoiding A + {c},
//           with e_i notin N(c) for all i, or d(c) = 1; success = Fan route (ek has no A-neighbour
//           in G - E(R)).  Reported as Fan-trail; the split count is not meaningful in this mode;
//   mode 2: the unrestricted trails of the first version (w_i notin A + {c} only), kept for
//           reference; these are NOT all licensed by TR.
// Success: in G - E(W), the end wk has degree 2 with non-adjacent neighbours x, y (split off wk:
// an admissible all-odd instance), or wk has no neighbour in A (Fan trail to an admissible instance).
#include "lind.h"
static uint32_t AA, NC; static int C, MODE, maxlen; static int split_found, route_found;
static uint32_t VIS;
static void dfs(Gr& H, int w, int len) {
  if (split_found && route_found) return;
  if (len >= 1) {
    if (!(H.adj[w] & AA)) route_found = 1;
    if (H.deg(w) == 2) {
      int x = __builtin_ctz(H.adj[w]), y = 31 - __builtin_clz(H.adj[w]);
      bool ok = !H.has(x, y);
      if (ok && MODE == 1 && (NC >> w & 1)) { int other = (x == C) ? y : x; if (AA >> other & 1) ok = false; }
      if (ok) split_found = 1;
    }
  }
  if (len >= maxlen) return;
  uint32_t nb = H.adj[w] & ~AA & ~(1u << C);
  if (MODE == 0) nb &= ~NC;
  if (MODE == 1 && (NC >> w & 1)) nb &= ~NC;   // no tight step out of a tight vertex
  if (MODE == 3) { nb &= ~VIS; if (__builtin_popcount(NC) != 1) nb &= ~NC; }
  if (MODE == 3) { while (nb) { int v = __builtin_ctz(nb); nb &= nb - 1; H.del(w, v); VIS |= 1u << v; dfs(H, v, len + 1); VIS &= ~(1u << v); H.add(w, v); } return; }
  while (nb) { int v = __builtin_ctz(nb); nb &= nb - 1; H.del(w, v); dfs(H, v, len + 1); H.add(w, v); }
}
int main(int argc, char** argv) {
  MODE = argc > 1 ? atoi(argv[1]) : 0; maxlen = argc > 2 ? atoi(argv[2]) : 10;
  char line[256]; long long inst = 0, sp = 0, ro = 0, either = 0, sponly = 0;
  while (fgets(line, sizeof line, stdin)) {
    Gr G; if (!parse_g6(line, G)) continue; if (__builtin_popcount(G.evens()) != 1) continue; int g = even_vertex(G);
    for (int c = 0; c < G.N; c++) { if (!(G.deg(c) & 1) || G.has(g, c)) continue;
      uint32_t A = amax_of(G, c);
      bool isb = true; for (int u = 0; u < G.N; u++) if (G.has(g, u) && !(G.adj[u] & A & ~(1u << g))) isb = false;
      if (!isb) continue; inst++;
      AA = A; NC = G.adj[c]; C = c; split_found = route_found = 0; VIS = 1u << g;
      Gr H = G; dfs(H, g, 0);
      sp += split_found; ro += route_found; either += (split_found || route_found); sponly += (split_found && !route_found);
    }
  }
  printf("SUMMARY mode=%d maxlen=%d blocked=%lld  walk-to-degree-two=%lld  Fan-trail=%lld  either=%lld  (degree-two only=%lld)\n", MODE, maxlen, inst, sp, ro, either, sponly);
}
