// t_walk.cpp: independent census for Proposition 3.3 (walk to a degree-two vertex) and the Fan route,
// at blocked instances with A = Amax (c notin N(g)), with UNBOUNDED trails.
//   W0  : trail g w1..wk, w_i notin A + N[c]; end of remaining degree 2 with non-adjacent neighbours.
//         For every such trail found, the structural claims of Prop 3.3 are checked: G* has no even
//         vertex, (G*, c, A) is admissible, nu(G*) = 2|E| - 2k - 1.
//   FR  : l1star Prop 5.3 as stated: a PATH g e1..ek, c notin V(R), e_i notin A, N(e_k) cap A within
//         {e_{k-1}}, and (e_i notin N(c) for all i, or d(c) = 1).  Reported separately for d(c) = 1.
//   W1  : the authors' "tight targets allowed" walk (w_i notin A + c), as in walk2.cpp mode 1.
//   W1v : W1 restricted to what TR actually licenses: no two consecutive tight vertices on the trail
//         (TR needs c notin N(even vertex) at each tight step), and, for a split at a tight end w_k
//         (then c is one of its two remaining neighbours), the other neighbour must not be in A
//         (otherwise G* is not admissible).
//   R1, R1v: the same for the TR Fan trail (end with no A-neighbour in G - E(W)), as in walkadm.cpp.
#include "a25.h"
#include <iostream>
using namespace a25;
static Graph G0; static int C, Gv; static uint32_t AA, NC;
static bool w0, w1, w1v, r1, r1v, frpath;
static long long structural_bad = 0;
static int edgesG; static int MAXK = 1000;
static void check_star(const Graph& H, int w, int k) {  // H = G - E(W), w = end with degree 2
  int x = __builtin_ctz(H.adj[w]), y = 31 - __builtin_clz(H.adj[w]);
  Graph S = H; S.rem(w, x); S.rem(w, y); S.add(x, y);
  bool ok = S.evenset() == 0 && admissible(S, C, AA) && S.deg(C) % 2 == 1;
  long long nuS = 0; for (int v = 0; v < S.n; v++) nuS += S.deg(v); nuS += 1;
  if (nuS != 2LL * edgesG - 2 * k - 1) ok = false;
  if (!ok) structural_bad++;
}
// mode 0: forbidden A + N[c]
static void dfs0(Graph& H, int w, int k) {
  if (w0) return;
  if (k >= 1 && H.deg(w) == 2) { int x = __builtin_ctz(H.adj[w]), y = 31 - __builtin_clz(H.adj[w]); if (!H.has(x, y)) { check_star(H, w, k); w0 = true; return; } }
  uint32_t nb = H.adj[w] & ~AA & ~(NC | (1u << C));
  while (nb) { int v = __builtin_ctz(nb); nb &= nb - 1; H.rem(w, v); dfs0(H, v, k + 1); H.add(w, v); if (w0) return; }
}
// mode 1: forbidden A + c; track validity
static void dfs1(Graph& H, int w, int k, bool valid, bool prevTight) {
  if (w1 && w1v && r1 && r1v) return;
  if (k >= 1) {
    bool tight = NC >> w & 1u;
    if (!(H.adj[w] & AA)) { r1 = true; if (valid) r1v = true; }
    if (H.deg(w) == 2) { int x = __builtin_ctz(H.adj[w]), y = 31 - __builtin_clz(H.adj[w]);
      if (!H.has(x, y)) { w1 = true; bool v2 = valid; if (tight) { int other = (x == C) ? y : x; if (AA >> other & 1u) v2 = false; } if (v2) w1v = true; } }
    (void)prevTight;
  }
  if (k >= MAXK) return;
  uint32_t nb = H.adj[w] & ~AA & ~(1u << C);
  bool wt = (k >= 1) && (NC >> w & 1u);
  while (nb) { int v = __builtin_ctz(nb); nb &= nb - 1; bool vt = NC >> v & 1u;
    H.rem(w, v); dfs1(H, v, k + 1, valid && !(wt && vt), vt); H.add(w, v); if (w1 && w1v && r1 && r1v) return; }
}
// Fan route, paths only (l1star Prop 5.3)
static void dfsfr(int x, uint32_t vis, int prev, bool allOutNc) {
  if (frpath) return;
  if (x != Gv) { uint32_t bad = G0.adj[x] & AA & ~(prev >= 0 ? (1u << prev) : 0); if (!bad && (allOutNc || G0.deg(C) == 1)) { frpath = true; return; } }
  for (int y = 0; y < G0.n; y++) if (G0.has(x, y) && !(vis >> y & 1u) && y != C && !(AA >> y & 1u)) dfsfr(y, vis | (1u << y), x, allOutNc && !(NC >> y & 1u));
}
int main() {
  if (getenv("MAXK")) MAXK = atoi(getenv("MAXK"));
  long long inst = 0, n0 = 0, nfr = 0, nfr_dc1 = 0, nfr_dc3 = 0, nw1 = 0, nw1v = 0, nr1 = 0, nr1v = 0, either = 0, eitherv = 0, dc1inst = 0;
  std::string line;
  while (std::getline(std::cin, line)) {
    Graph G; if (!decode_g6(line, G)) continue;
    if (__builtin_popcount(G.evenset()) != 1) continue;
    int g = theeven(G);
    for (int c = 0; c < G.n; c++) {
      if (G.deg(c) % 2 == 0 || G.has(g, c)) continue;
      uint32_t A = amax(G, c);
      if (!blocked(G, c, A)) continue;
      inst++; dc1inst += G.deg(c) == 1;
      G0 = G; C = c; Gv = g; AA = A; NC = G.adj[c]; edgesG = G.m();
      w0 = w1 = w1v = r1 = r1v = frpath = false;
      Graph H = G; dfs0(H, g, 0);
      Graph H1 = G; dfs1(H1, g, 0, true, false);
      dfsfr(g, 1u << g, -1, true);
      n0 += w0; nfr += frpath; if (frpath) { if (G.deg(c) == 1) nfr_dc1++; else nfr_dc3++; }
      nw1 += w1; nw1v += w1v; nr1 += r1; nr1v += r1v; either += (w1 || r1); eitherv += (w1v || r1v);
      if (frpath && getenv("PRINT")) printf("FANROUTE %s c=%d g=%d d(c)=%d prop33walk=%d\n", line.c_str(), c, g, G.deg(c), (int)w0);
    }
  }
  printf("blocked Amax instances %lld (d(c)=1: %lld)\n", inst, dc1inst);
  printf("Prop 3.3 walk (w_i notin A+N[c], unbounded): %lld; structural check failures %lld\n", n0, structural_bad);
  printf("l1star Prop 5.3 Fan route (paths): %lld (d(c)=1: %lld, d(c)>=3: %lld)\n", nfr, nfr_dc1, nfr_dc3);
  printf("tight allowed (walk2 mode 1 / walkadm): split %lld, Fan trail %lld, either %lld\n", nw1, nr1, either);
  printf("tight allowed, TR-valid only: split %lld, Fan trail %lld, either %lld\n", nw1v, nr1v, eitherv);
}
