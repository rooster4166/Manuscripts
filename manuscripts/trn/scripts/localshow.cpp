// local.cpp: for every bad D' (plain Fan image has x in Q(y)), let S = chain paths P_0..P_k plus
// Q'(y) (and optionally P_y).  Can E(S) + gu be re-decomposed into paths with end multiset
// ends(S) - g + u, such that the path ending at y avoids x?  (Other paths of D' kept.)
#include "dec.h"
using namespace dec;
// enumerate path decompositions of edge set given by adjacency adjL with prescribed end counts need[]
static int Ln; static uint32_t radj[MAXV]; static int need[MAXV]; static int Ly, Lx; static bool lfound; static std::vector<std::vector<int>> lsol, lcur;
static int remE;
static void lgrow(int a, int cur, uint32_t vis, bool isY, int depth);
static void lsolve() {
  if (lfound) return;
  if (remE == 0) { for (int v = 0; v < Ln; v++) if (need[v]) return; lfound = true; lsol = lcur; return; }
  int a = -1;
  for (int v = 0; v < Ln; v++) if (need[v] > 0) { if (!radj[v]) return; if (a < 0) a = v; }
  if (a < 0) return;
  // prefer starting at y so that its constraint prunes early
  if (need[Ly] > 0) a = Ly;
  need[a]--; lcur.push_back({a});
  lgrow(a, a, 1u << a, a == Ly, 0);
  lcur.pop_back(); need[a]++;
}
static void lgrow(int a, int cur, uint32_t vis, bool isY, int depth) {
  uint32_t nb = radj[cur] & ~vis;
  if (isY) nb &= ~(1u << Lx);
  while (nb && !lfound) {
    int w = __builtin_ctz(nb); nb &= nb - 1;
    radj[cur] &= ~(1u << w); radj[w] &= ~(1u << cur); remE--; lcur.back().push_back(w);
    uint32_t nv = vis | (1u << w);
    bool canClose = need[w] > 0 && !(w == Ly && (nv >> Lx & 1));
    if (canClose) { need[w]--; lsolve(); need[w]++; }
    if (!lfound) lgrow(a, w, nv, isY, depth + 1);
    lcur.back().pop_back();
    radj[cur] |= 1u << w; radj[w] |= 1u << cur; remE++;
  }
}
int main(int argc, char** argv) {
  int withPy = argc > 1 ? atoi(argv[1]) : 0; int onlyDu = argc > 3 ? atoi(argv[3]) : 0;
  char line[256]; long long nbad = 0, fixed = 0; int pr = argc > 2 ? atoi(argv[2]) : 0, printed = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    if (__builtin_popcount(G.evens()) != 1) continue;
    int g = even_vertex(G), n = G.N;
    for (int u = 0; u < n; u++) { if (!G.has(g, u)) continue; if (onlyDu && G.deg(u) != onlyDu) continue;
      Gr H = G; H.del(g, u);
      for (int y = 0; y < n; y++) { if (G.deg(y) % 2 == 0 || !G.has(y, u)) continue;
        for (int x = 0; x < n; x++) {
          if (x == y || x == u || G.deg(x) % 2 == 0 || G.has(x, y)) continue;
          if (getenv("WIT")) { uint32_t W = G.adj[y] & ~G.adj[x] & ~(1u << u); if (!W) continue; }
          enumerate(H, y, 1u << x, 0, [&](const Decomp& D) {
            std::vector<int> ch; Decomp R = fan_forced(D, g, u, ch);
            if (path_avoids(R[path_end_at(R, y)], 1u << x)) return false;
            nbad++;
            std::vector<int> sel;
            for (int v : ch) { int pi = path_end_at(D, v); if (std::find(sel.begin(), sel.end(), pi) == sel.end()) sel.push_back(pi); }
            int qy = path_end_at(D, y); if (std::find(sel.begin(), sel.end(), qy) == sel.end()) sel.push_back(qy);
            if (withPy) for (size_t pi = 0; pi < D.size(); pi++) { const Path& p = D[pi];
                for (size_t j = 0; j + 1 < p.size(); j++) if ((p[j] == y && p[j + 1] == u) || (p[j] == u && p[j + 1] == y))
                  if (std::find(sel.begin(), sel.end(), (int)pi) == sel.end()) sel.push_back(pi); }
            Ln = n; memset(radj, 0, sizeof radj); memset(need, 0, sizeof need); remE = 0;
            for (int pi : sel) { const Path& p = D[pi]; need[p.front()]++; need[p.back()]++;
              for (size_t j = 0; j + 1 < p.size(); j++) { radj[p[j]] |= 1u << p[j + 1]; radj[p[j + 1]] |= 1u << p[j]; remE++; } }
            radj[g] |= 1u << u; radj[u] |= 1u << g; remE++; need[g]--; need[u]++;
            Ly = y; Lx = x; lfound = false;
            lsolve();
            if (lfound) { fixed++; if (getenv("SHOWFIX") && printed < pr) { printed++; printf("FIX %s g=%d y=%d x=%d u=%d D'=", line, g, y, x, u);
              for (auto& p : D) { for (int v : p) printf("%d", v); printf(" "); } printf(" chain="); for (int v : ch) printf("%d", v); printf("  ->  ");
              for (auto& p : lsol) { for (int v : p) printf("%d", v); printf(" "); } printf("\n"); } }
            else if (pr && printed < pr) { printed++; printf("NOLOCAL %s g=%d y=%d x=%d u=%d D'=", line, g, y, x, u);
              for (auto& p : D) { for (int v : p) printf("%d", v); printf(" "); } printf(" chain="); for (int v : ch) printf("%d", v); printf("\n"); }
            return false; });
        }
      }
    }
  }
  printf("bad D'=%lld, locally re-decomposable (chain paths + Q'(y)%s + gu): %lld\n", nbad, withPy ? " + P_y" : "", fixed);
}
