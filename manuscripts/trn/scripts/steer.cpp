// steer.cpp: the tail-steering move (T).  For an instance (G, g, y, x) (g the even vertex, x, y odd,
// non-adjacent), is there a trail y = y_0, y_1, ..., y_k (k >= 1, distinct edges of G) with every
// y_i (i >= 1) outside N[g] u {x}, such that y_k has no edge outside the trail?  If so, (G, y, {x})
// is good (leaf at y, steered Fan steps, leaf-tail lemma at the bottom).
// Modes: count over all N-instances / TRN tests / the TRN core; report instances without (T).
#include "lind.h"
static int n; static uint32_t adjm[MAXV]; static uint32_t allowed;  // allowed targets
static long long nodes, budget;
// used[v] = mask of used neighbours of v
static bool dfs(int c, uint32_t* used) {
  if (budget && ++nodes > budget) return false;
  uint32_t nb = adjm[c] & ~used[c] & allowed;
  while (nb) {
    int v = __builtin_ctz(nb); nb &= nb - 1;
    used[c] |= 1u << v; used[v] |= 1u << c;
    if ((adjm[v] & ~used[v]) == 0) { used[c] &= ~(1u << v); used[v] &= ~(1u << c); return true; }
    bool ok = dfs(v, used);
    used[c] &= ~(1u << v); used[v] &= ~(1u << c);
    if (ok) return true;
  }
  return false;
}
static int steerable(const Gr& G, int g, int y, int x) {
  n = G.N; for (int v = 0; v < n; v++) adjm[v] = G.adj[v];
  allowed = 0; for (int v = 0; v < n; v++) if (G.deg(v) > 0) allowed |= 1u << v;
  allowed &= ~(G.adj[g] | (1u << g) | (1u << x));
  uint32_t used[MAXV]; memset(used, 0, sizeof used); nodes = 0;
  bool r = dfs(y, used);
  if (budget && nodes > budget) return 2;
  return r ? 1 : 0;
}
int main(int argc, char** argv) {
  const char* mode = argc > 1 ? argv[1] : "N";   // N, TRN, CORE
  budget = argc > 2 ? atoll(argv[2]) : 0;
  int pr = argc > 3 ? atoi(argv[3]) : 0, printed = 0;
  char line[256]; long long inst = 0, ok = 0, und = 0, tight = 0, tightok = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    if (__builtin_popcount(G.evens()) != 1) continue;
    int g = even_vertex(G);
    bool ind = false;
    if (G.deg(g) == 2) { int a = __builtin_ctz(G.adj[g]), b = 31 - __builtin_clz(G.adj[g]); ind = !G.has(a, b); }
    for (int y = 0; y < G.N; y++) { if (G.deg(y) % 2 == 0) continue;
      for (int x = 0; x < G.N; x++) {
        if (x == y || G.deg(x) % 2 == 0 || G.has(x, y)) continue;
        uint32_t W = G.adj[y] & ~G.adj[x] & ~(1u << g);   // N-witnesses
        bool alltight = true;
        for (int v = 0; v < G.N; v++) if (G.has(g, v) && v != x && v != y && !G.has(y, v)) alltight = false;
        bool cn = (G.adj[x] & G.adj[y]) != 0;
        if (!strcmp(mode, "N")) { if (!W) continue; }
        else {
          // TRN core: all-tight, a tight target u with a child witness, common neighbour, not ind.
          bool anyu = false;
          for (int u = 0; u < G.N; u++) if (u != x && G.has(g, u) && G.has(y, u) && (G.adj[y] & ~G.adj[x] & ~(1u << u))) anyu = true;
          if (!anyu || !alltight || !cn || ind) continue;
          if (!W) continue;  // an N-instance as well
        }
        inst++;
        int r = steerable(G, g, y, x);
        if (r == 2) und++; else if (r == 1) ok++;
        if (alltight) { tight++; if (r == 1) tightok++; }
        if (r == 0 && pr && printed < pr) { printed++; printf("NOSTEER %s g=%d y=%d x=%d alltight=%d\n", line, g, y, x, (int)alltight); }
      }
    }
  }
  printf("mode %s: instances %lld, move (T) available %lld, undecided %lld; all-tight %lld, of which (T) %lld\n", mode, inst, ok, und, tight, tightok);
}
