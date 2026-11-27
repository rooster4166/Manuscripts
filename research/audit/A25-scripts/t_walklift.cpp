// t_walklift.cpp: direct test of the PROOF of Proposition 3.3 (walk to a degree-two vertex).
// For every connected G with one even vertex g, odd c notin N(g), every admissible A (all subsets of
// Amax, including the empty set) and every trail W = g w1 .. wk (edge-distinct, w_i notin A + N[c],
// trails may revisit vertices and g) whose end has degree 2 in G - E(W) with non-adjacent
// neighbours x, y: build G*, check the structural claims, take good decompositions D* of (G*, c, A)
// (up to CAP), and execute the proof: subdivide xy by w_k, then for i = k..1 restore w_{i-1}w_i by the
// forced Fan chain from w_{i-1} to w_i.  The final decomposition must be a Lovász decomposition of G
// whose path ending at c avoids A.  (The forced chain in the plain graph equals the chain of the
// protected transfer, since c is not adjacent to the target and so is never a chain vertex.)
// usage: t_walklift [CAP_DSTAR] [MAX_TRAILS_PER_INSTANCE] [MODE]   MODE = all (every admissible A) | amax
#include "a25.h"
#include <iostream>
using namespace a25;
static long long trails = 0, lifts = 0, liftbad = 0, structbad = 0, revisit = 0, backtog = 0, nostar = 0;
int main(int argc, char** argv) {
  long long CAP = argc > 1 ? atoll(argv[1]) : 20; long long MAXT = argc > 2 ? atoll(argv[2]) : 50;
  std::string mode = argc > 3 ? argv[3] : "all";
  std::string line;
  while (std::getline(std::cin, line)) {
    Graph G; if (!decode_g6(line, G)) continue;
    if (__builtin_popcount(G.evenset()) != 1) continue;
    int g = theeven(G);
    for (int c = 0; c < G.n; c++) {
      if (G.deg(c) % 2 == 0 || G.has(g, c)) continue;
      uint32_t Am = amax(G, c);
      std::vector<uint32_t> As;
      if (mode == "amax") As.push_back(Am); else { for (uint32_t A = Am;; A = (A - 1) & Am) { As.push_back(A); if (!A) break; } }
      for (uint32_t A : As) {
        if (mode == "amax" && !blocked(G, c, A)) continue;
        uint32_t forb = A | closedN(G, c);
        long long tcount = 0;
        std::vector<int> W{g};
        Graph H = G;
        std::function<void()> dfs = [&]() {
          if (tcount >= MAXT) return;
          int w = W.back(); int k = (int)W.size() - 1;
          if (k >= 1 && H.deg(w) == 2) {
            int x = __builtin_ctz(H.adj[w]), y = 31 - __builtin_clz(H.adj[w]);
            if (!H.has(x, y)) {
              tcount++; trails++;
              bool rv = false; for (int i = 1; i <= k; i++) for (int j = 0; j < i; j++) if (W[i] == W[j]) { rv = true; if (W[j] == g) backtog++; }
              revisit += rv;
              Graph S = H; S.rem(w, x); S.rem(w, y); S.add(x, y);
              if (S.evenset() != 0 || !admissible(S, c, A) || S.deg(c) % 2 != 1) structbad++;
              long long got = 0;
              enumerate(S, nullptr, [&](const Dec& Ds) {
                int qc = path_ending_at(Ds, c); if (qc < 0 || (vset(Ds[qc]) & A)) return false;
                got++;
                // subdivide xy by w
                Dec D = Ds; bool done = false;
                for (auto& P : D) for (size_t j = 0; j + 1 < P.size() && !done; j++)
                  if ((P[j] == x && P[j + 1] == y) || (P[j] == y && P[j + 1] == x)) { P.insert(P.begin() + j + 1, w); done = true; }
                if (!done || !check(H, D)) { liftbad++; return got >= CAP; }
                // restore the trail edges, last first
                Graph K = H; bool ok = true;
                for (int i = k; i >= 1 && ok; i--) {
                  int t = W[i - 1], u = W[i];
                  Dec D2; std::vector<int> ch;
                  if (!forced_chain(D, t, u, D2, ch)) { ok = false; break; }
                  K.add(t, u);
                  if (!check(K, D2)) { ok = false; break; }
                  int q = path_ending_at(D2, c); if (q < 0 || (vset(D2[q]) & A)) { ok = false; break; }
                  D = D2;
                }
                lifts++; if (!ok || !check(G, D)) { liftbad++; printf("LIFTFAIL %s c=%d A=%s trail", line.c_str(), c, sstr(A).c_str()); for (int z : W) printf(" %d", z); printf("\n"); }
                return got >= CAP; }, c, A);
              if (!got) nostar++;
            }
          }
          uint32_t nb = H.adj[w] & ~forb;
          while (nb) { int v = __builtin_ctz(nb); nb &= nb - 1; H.rem(w, v); W.push_back(v); dfs(); W.pop_back(); H.add(w, v); if (tcount >= MAXT) return; }
        };
        dfs();
      }
    }
  }
  printf("trails %lld (revisiting a vertex %lld, returning to g %lld); structural failures %lld; G* not good %lld\n", trails, revisit, backtog, structbad, nostar);
  printf("lifts executed %lld, failures %lld\n", lifts, liftbad);
}
