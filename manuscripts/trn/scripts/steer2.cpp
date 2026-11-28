// steer2.cpp: the two-token steering move (T2).  Hang a leaf l at y: the even vertices of G+yl are
// g and y.  A token sits on each.  A step moves one token from p along an unused edge pq to q, where
// q is not x, not the other token's position, and not adjacent (in the current graph, after removing
// pq) to the other token's position.  The token is done when q becomes isolated.  If both tokens can
// be made done, (G, y, {x}) is good: L1 at the all-odd bottom (tail l), then Fan steps back up, each
// with no blank (Z = empty) and a target outside {x, l}.
// Mode 1 (y-token only, never move g) reproduces move (T).
#include "lind.h"
#include <unordered_set>
#include <array>
static int n; static uint32_t A0[MAXV]; static int X;
static long long nodes, budget;
static std::unordered_set<std::string> failset;
static int onlyY; static int Y; static std::vector<std::array<int,3>> mv, best;
static std::string key(int pg, int py, const uint32_t* adj) {
  std::string k((const char*)adj, n * 4); k.push_back((char)(pg + 1)); k.push_back((char)(py + 1)); return k;
}
// adj: current adjacency; pg, py: token positions (-1 = done)
static bool search(int pg, int py, uint32_t* adj) {
  if (pg < 0 || py < 0) { best = mv; return true; }   // at most one even vertex left: leaf-tail lemma or L1 at the bottom
  if (budget && ++nodes > budget) return false;
  std::string k = key(pg, py, adj);
  if (failset.count(k)) return false;
  for (int tok = 0; tok < 2; tok++) {
    if (onlyY && tok == 0) continue;
    int p = tok == 0 ? pg : py, o = tok == 0 ? py : pg;
    if (p < 0) continue;
    uint32_t nb = adj[p];
    while (nb) {
      int q = __builtin_ctz(nb); nb &= nb - 1;
      if (q == X || q == o) continue;
      adj[p] &= ~(1u << q); adj[q] &= ~(1u << p);
      bool okq = (o < 0) || !(adj[q] >> o & 1);
      bool res = false;
      if (okq) {
        int nq = (adj[q] || q == Y) ? q : -1;   // y keeps its leaf, so it is never isolated
        mv.push_back({tok, p, q});
        res = tok == 0 ? search(nq, py, adj) : search(pg, nq, adj);
        mv.pop_back();
      }
      adj[p] |= 1u << q; adj[q] |= 1u << p;
      if (res) return true;
    }
  }
  if (!(budget && nodes > budget)) failset.insert(k);
  return false;
}
static int schedulable(const Gr& G, int g, int y, int x) {
  // The leaf l at y is not stored: it is never a target (it is in X) and its edge is never removed,
  // so it only keeps y from becoming isolated (see the isolation test in search()).
  n = G.N; X = x; Y = y; uint32_t adj[MAXV]; memset(adj, 0, sizeof adj);
  for (int v = 0; v < n; v++) adj[v] = G.adj[v];
  failset.clear(); nodes = 0; mv.clear(); best.clear();
  bool r = search(g, y, adj);
  return (budget && nodes > budget) ? 2 : (r ? 1 : 0);
}
int main(int argc, char** argv) {
  const char* mode = argc > 1 ? argv[1] : "N";
  budget = argc > 2 ? atoll(argv[2]) : 2000000;
  onlyY = argc > 3 ? atoi(argv[3]) : 0;
  int pr = argc > 4 ? atoi(argv[4]) : 0, printed = 0;
  char line[256]; long long inst = 0, ok = 0, und = 0, tight = 0, tightok = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    if (__builtin_popcount(G.evens()) != 1) continue;
    int g = even_vertex(G);
    for (int y = 0; y < G.N; y++) { if (G.deg(y) % 2 == 0) continue;
      for (int x = 0; x < G.N; x++) {
        if (x == y || G.deg(x) % 2 == 0 || G.has(x, y)) continue;
        uint32_t W = G.adj[y] & ~G.adj[x] & ~(1u << g);
        if (!strcmp(mode, "N") && !W) continue;
        if (!strcmp(mode, "CORETESTS")) {
          // per TRN test (G, y, x, u) in the core of Definition 5.1, exactly as core.cpp:
          // child good, all-tight, child witness, common neighbour, N(g) not an independent pair
          bool alltight2 = true;
          for (int v = 0; v < G.N; v++) if (G.has(g, v) && v != x && v != y && !G.has(y, v)) alltight2 = false;
          bool ind2 = false;
          if (G.deg(g) == 2) { int a = __builtin_ctz(G.adj[g]), b = 31 - __builtin_clz(G.adj[g]); ind2 = !G.has(a, b); }
          if (!alltight2 || (G.adj[x] & G.adj[y]) == 0 || ind2 || !W) continue;   // W != 0 is (C0)
          int sched = -1;
          for (int u = 0; u < G.N; u++) {
            if (u == x || !G.has(g, u) || !G.has(y, u)) continue;
            if (!(G.adj[y] & ~G.adj[x] & ~(1u << u))) continue;
            Gr H = G; H.del(g, u);
            if (orc::avoid(H, y, 1u << x) != 1) continue;
            if (sched < 0) { sched = schedulable(G, g, y, x);
              if (getenv("SHOWCORE")) { printf("CORE %s g=%d y=%d x=%d sched=%d m=%d", line, g, y, x, sched, G.nedges());
                if (sched == 1) for (auto& m : best) printf(" %d:%d-%d", m[0], m[1], m[2]); printf("\n"); } }
            inst++; if (sched == 1) ok++; else if (sched == 2) und++;
            tight++; if (sched == 1) tightok++;
          }
          continue;
        }
        bool alltight = true;
        for (int v = 0; v < G.N; v++) if (G.has(g, v) && v != x && v != y && !G.has(y, v)) alltight = false;
        if (!strcmp(mode, "TIGHT") && (!W || !alltight)) continue;
        // RESID: all-tight N-instances not settled by a proved base case (x a leaf at g; distance >= 3;
        // N(g) an independent pair; N(g) = {x, y} is NA, now proved)
        bool ind = false;
        if (G.deg(g) == 2) { int a = __builtin_ctz(G.adj[g]), b = 31 - __builtin_clz(G.adj[g]); ind = !G.has(a, b); }
        bool leafg = G.adj[x] == (1u << g);
        bool far = (G.adj[x] & G.adj[y]) == 0;
        bool degxy = G.adj[g] == ((1u << x) | (1u << y));
        if (!strcmp(mode, "RESID") && (!W || !alltight || ind || leafg || far || degxy)) continue;
        // TRNCORE: TRN core tests (some tight target u with child witness), counted per (G, y, x)
        if (!strcmp(mode, "TRNCORE")) {
          bool anyu = false;
          for (int u = 0; u < G.N; u++) if (u != x && G.has(g, u) && G.has(y, u) && (G.adj[y] & ~G.adj[x] & ~(1u << u))) anyu = true;
          if (!anyu || !alltight || far || ind) continue;
        }
        inst++;
        int r = schedulable(G, g, y, x);
        if (r == 2) und++; else if (r == 1) ok++;
        if (alltight) { tight++; if (r == 1) tightok++; }
        if (r == 1 && getenv("SCHED")) { printf("SCHED %s %d %d %d", line, g, y, x); for (auto& m : best) printf(" %d:%d-%d", m[0], m[1], m[2]); printf("\n"); }
        if (r == 0 && pr && printed < pr) { printed++; printf("NOSCHED %s g=%d y=%d x=%d alltight=%d\n", line, g, y, x, (int)alltight); }
      }
    }
  }
  printf("mode %s onlyY=%d: instances %lld, schedule %lld, undecided %lld; all-tight %lld, of which schedule %lld\n", mode, onlyY, inst, ok, und, tight, tightok);
}
