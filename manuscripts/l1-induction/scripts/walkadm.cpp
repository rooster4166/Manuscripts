// walkadm.cpp: (corrected after audit A25, F3: only trails that TR licenses, i.e. no tight w_i
// directly after a tight w_{i-1}.)  Assuming TR, a trail g = w0, w1, ..., wk (k >= 1, edge-distinct, w_i not in A + c for
// i >= 1) whose end wk has no neighbour in A in G - E(W) reduces (G, c, A) to an admissible smaller
// instance.  For every blocked admissible instance (A = Amax), search for such a trail (DFS over trails,
// bounded length).  Also reports the simpler reachability criterion for Amax.
#include "lind.h"
static Gr G0; static int C; static uint32_t AA, NCC; static int maxlen;
static bool dfs(Gr& H, int w, int len) {
  if (len >= 1 && !(H.adj[w] & AA)) return true;
  if (len >= maxlen) return false;
  uint32_t nb = H.adj[w] & ~AA & ~(1u << C);
  if (NCC >> w & 1) nb &= ~NCC;   // TR needs the source of a tight step to be non-tight
  while (nb) { int v = __builtin_ctz(nb); nb &= nb - 1;
    H.del(w, v); bool r = dfs(H, v, len + 1); H.add(w, v); if (r) return true; }
  return false;
}
int main(int argc, char** argv) {
  maxlen = argc > 1 ? atoi(argv[1]) : 12;
  char line[256]; long long inst = 0, ok = 0;
  while (fgets(line, sizeof line, stdin)) {
    Gr G; if (!parse_g6(line, G)) continue; char* nl = strchr(line, '\n'); if (nl) *nl = 0;
    if (__builtin_popcount(G.evens()) != 1) continue; int g = even_vertex(G);
    for (int c = 0; c < G.N; c++) { if (!(G.deg(c) & 1) || G.has(g, c)) continue;
      uint32_t A = amax_of(G, c);
      bool isb = true; for (int u = 0; u < G.N; u++) if (G.has(g, u) && !(G.adj[u] & A & ~(1u << g))) isb = false;
      if (!isb) continue; inst++;
      C = c; AA = A; NCC = G.adj[c]; Gr H = G;
      bool r = dfs(H, g, 0); ok += r;
      if (!r && getenv("DUMP")) { printf("NOWALK %s c=%d g=%d A=", line, c, g); print_set(stdout, A); printf("\n"); }
    }
  }
  printf("SUMMARY blocked=%lld with TR-walk to admissible=%lld (maxlen %d)\n", inst, ok, maxlen);
}
