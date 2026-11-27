// t_trst9.cpp: TR, ST and ST' at order 9 with the a25 avoidance oracle (pruned transition-system
// search, node budget per query; no full enumeration, which is infeasible for the densest graphs).
// Goodness is antitone in A, so for each (graph, terminal) known-good and known-bad sets are kept and
// used to infer answers (A within a good set is good; A containing a bad set is bad).
// usage: t_trst9 MOD REM BUDGET < graph6    (processes the graphs with exactly one even vertex whose
//        index among those graphs is REM mod MOD)
#include "a25.h"
#include <iostream>
#include <map>
using namespace a25;
struct Know { std::vector<uint32_t> goodS, badS; };
static std::map<std::string, Know> know;
static long long queries = 0, inferred = 0, undecided = 0;
static long long BUD;
static int q(const Graph& H, int c, uint32_t A) {
  std::string k((const char*)H.adj, 4 * H.n); k.push_back((char)c);
  Know& K = know[k];
  for (uint32_t s : K.goodS) if ((A & s) == A) { inferred++; return 1; }
  for (uint32_t s : K.badS) if ((A & s) == s) { inferred++; return 0; }
  queries++;
  int r = good(H, c, A, BUD);
  if (r == 1) K.goodS.push_back(A); else if (r == 0) K.badS.push_back(A); else undecided++;
  return r;
}
int main(int argc, char** argv) {
  int mod = argc > 1 ? atoi(argv[1]) : 1, rem = argc > 2 ? atoi(argv[2]) : 0; BUD = argc > 3 ? atoll(argv[3]) : 20000000;
  long long idx = 0, graphs = 0, trT = 0, trV = 0, trU = 0, trAdm = 0, trIn = 0, stI = 0, stOK = 0, stU = 0, stpOK = 0, stpU = 0;
  std::string line;
  while (std::getline(std::cin, line)) {
    Graph G; if (!decode_g6(line, G)) continue;
    if (__builtin_popcount(G.evenset()) != 1) continue;
    if ((idx++ % mod) != rem) continue;
    graphs++; know.clear();
    int g = theeven(G), n = G.n;
    std::vector<Graph> Hx(n); for (int x = 0; x < n; x++) if (G.has(g, x)) { Hx[x] = G; Hx[x].rem(g, x); }
    for (int c = 0; c < n; c++) {
      if (G.deg(c) % 2 == 0 || G.has(g, c)) continue;
      for (int x = 0; x < n; x++) if (G.has(g, x) && G.has(c, x)) {
        uint32_t free = ((1u << n) - 1) & ~(closedN(G, c) | (1u << x));
        std::vector<uint32_t> As; for (uint32_t A = free;; A = (A - 1) & free) { As.push_back(A); if (!A) break; }
        std::sort(As.begin(), As.end(), [](uint32_t a, uint32_t b) { return __builtin_popcount(a) < __builtin_popcount(b); });
        for (uint32_t A : As) {
          int ch = q(Hx[x], c, A); if (ch == 2) { trU++; continue; } if (ch != 1) continue;
          trT++; if (A & G.adj[g]) trIn++; else trAdm++;
          int pa = q(G, c, A); if (pa == 2) trU++; else if (pa != 1) { trV++; printf("TRVIOL %s c=%d x=%d A=%s\n", line.c_str(), c, x, sstr(A).c_str()); }
        }
      }
      uint32_t Am = amax(G, c);
      for (uint32_t A = Am; A; A = (A - 1) & Am) {
        if (!blocked(G, c, A)) continue;
        stI++; bool st = false, stu = false, sp = false, spu = false;
        for (int x = 0; x < n; x++) if (G.has(g, x)) {
          int r = q(Hx[x], c, A); if (r == 1) st = true; if (r == 2) stu = true;
          if (!G.has(c, x)) { if (r == 1) sp = true; if (r == 2) spu = true; }
          else { Graph K = Hx[x]; K.rem(x, c); int r2 = q(K, x, A | (1u << c)); if (r2 == 1) sp = true; if (r2 == 2) spu = true; }
        }
        if (st) stOK++; else if (stu) stU++; else printf("STFAIL %s c=%d A=%s\n", line.c_str(), c, sstr(A).c_str());
        if (sp) stpOK++; else if (spu) stpU++;
      }
    }
    fflush(stdout);
  }
  printf("SUMMARY graphs=%lld | TR tests=%lld (A admissible for G %lld, A meets N(g) %lld) violations=%lld undecided=%lld | ST blocked=%lld ok=%lld undecided=%lld | ST' ok=%lld undecided=%lld | oracle queries=%lld inferred=%lld undecided=%lld\n",
         graphs, trT, trAdm, trIn, trV, trU, stI, stOK, stU, stpOK, stpU, queries, inferred, undecided);
}
