// dec.h: enumeration of Lovász decompositions (b = deg mod 2) whose path ending at c avoids a mask,
// with the paths recorded, and exact simulation of Fan's forced chain (tight-fan Prop. 2.1).
#pragma once
#include "lind.h"
#include <functional>

namespace dec {
typedef std::vector<int> Path;
typedef std::vector<Path> Decomp;

static int n;
static uint32_t adj0[MAXV];
static uint32_t rem[MAXV];    // remaining adjacency
static uint32_t bm;           // vertices still needing an end
static Decomp cur;
static std::function<bool(const Decomp&)> cb;  // return true to stop
static long long found, cap_found;
static bool stop;
static int remEdges;

static bool remaining_ok() {
  // every component of the remaining edges must contain a vertex of bm; degree bound
  int P = __builtin_popcount(bm) / 2;
  for (int v = 0; v < n; v++) { int d = __builtin_popcount(rem[v]); if (d > 2 * P - (int)(bm >> v & 1)) return false; }
  uint32_t seen = 0;
  for (int v = 0; v < n; v++) {
    if ((seen >> v & 1) || !rem[v]) continue;
    uint32_t comp = 1u << v, f = comp;
    while (f) { int x = __builtin_ctz(f); f &= f - 1; uint32_t nx = rem[x] & ~comp; comp |= nx; f |= nx; }
    seen |= comp;
    if (!(comp & bm)) return false;
  }
  return true;
}

static void solve_rest();
// grow path from start a, current end x, visited vis
static void grow(int a, int x, uint32_t vis, uint32_t forbid) {
  if (stop) return;
  uint32_t nb = rem[x] & ~vis & ~forbid;
  while (nb) {
    int w = __builtin_ctz(nb); nb &= nb - 1;
    rem[x] &= ~(1u << w); rem[w] &= ~(1u << x); remEdges--;
    cur.back().push_back(w);
    if (bm >> w & 1 && w != a) {
      uint32_t sb = bm; bm &= ~((1u << a) | (1u << w));
      solve_rest();
      bm = sb;
      if (stop) return;
    }
    if (rem[w] & ~(vis | (1u << w)) & ~forbid) grow(a, w, vis | (1u << w), forbid);
    if (stop) return;
    cur.back().pop_back();
    rem[x] |= 1u << w; rem[w] |= 1u << x; remEdges++;
  }
}
static void solve_rest() {
  if (stop) return;
  if (remEdges == 0) { if (bm == 0) { found++; if (cb(cur) || (cap_found && found >= cap_found)) stop = true; } return; }
  if (bm == 0) return;
  if (!remaining_ok()) return;
  // start a new path at the lowest-degree vertex needing an end, to cut symmetry: paths are
  // generated starting from the smallest vertex of bm (each path has both ends in bm; start = min end)
  int a = __builtin_ctz(bm);
  if (!rem[a]) return;
  cur.push_back(Path{a});
  grow(a, a, 1u << a, 0);
  if (!stop) cur.pop_back();
}
// enumerate all Lovász decompositions with Q_c avoiding mask f.  Each decomposition is produced
// exactly once up to the orientation of paths (paths are grown from their smaller end, except Q_c,
// grown from c).  Returns number found (capped).
static long long enumerate(const Gr& G, int c, uint32_t f, long long capn, std::function<bool(const Decomp&)> callback) {
  n = G.N; for (int v = 0; v < n; v++) { adj0[v] = G.adj[v]; rem[v] = G.adj[v]; }
  remEdges = G.nedges();
  bm = 0; for (int v = 0; v < n; v++) if (G.deg(v) & 1) bm |= 1u << v;
  cur.clear(); found = 0; cap_found = capn; stop = false; cb = callback;
  if (!(bm >> c & 1)) return 0;
  cur.push_back(Path{c});
  grow(c, c, 1u << c, f);
  return found;
}

// Fan's forced chain on a decomposition with b <= 1: add edge t-w (t, w non-adjacent in the
// decomposed graph).  Returns the new decomposition; chainv receives the chain vertices.
static Decomp fan_forced(const Decomp& D, int t, int w, std::vector<int>& chainv) {
  Decomp P = D;
  int nv = 0; for (auto& p : P) for (int x : p) nv = std::max(nv, x + 1);
  nv = std::max(nv, std::max(t, w) + 1);
  std::vector<int> orig(nv, -1);  // path index ending at x in D
  for (size_t i = 0; i < P.size(); i++) { orig[P[i].front()] = (int)i; orig[P[i].back()] = (int)i; }
  chainv.clear();
  int x = t;
  for (int step = 0; step < 64; step++) {
    chainv.push_back(x);
    int pi = orig[x];
    if (pi < 0) { fprintf(stderr, "fan: no path ends at %d\n", x); exit(1); }
    Path& p = P[pi];
    if (p.back() == x) std::reverse(p.begin(), p.end());
    if (p.front() != x) { fprintf(stderr, "fan: path %d does not end at %d\n", pi, x); exit(1); }
    auto it = std::find(p.begin(), p.end(), w);
    if (it == p.end()) { p.insert(p.begin(), w); return P; }
    int k = (int)(it - p.begin());
    int y = p[k - 1];
    Path np(p.begin(), p.begin() + k); std::reverse(np.begin(), np.end());
    np.insert(np.end(), p.begin() + k, p.end());
    p = np;  // y ... x w ... ; now x-w used, y-w freed
    x = y;
  }
  fprintf(stderr, "fan: chain too long\n"); exit(1);
}

static int path_end_at(const Decomp& D, int c) {
  int idx = -1, cnt = 0;
  for (size_t i = 0; i < D.size(); i++) { if (D[i].front() == c) { idx = (int)i; cnt++; } if (D[i].back() == c) { idx = (int)i; cnt++; } }
  return cnt == 1 ? idx : -1;
}
static bool path_avoids(const Path& p, uint32_t A) { for (int x : p) if (A >> x & 1) return false; return true; }

// check D is a Lovász decomposition of G
static bool check_decomp(const Gr& G, const Decomp& D) {
  uint32_t used[MAXV]; memset(used, 0, sizeof used);
  int ends[MAXV]; memset(ends, 0, sizeof ends);
  for (auto& p : D) {
    if (p.size() < 2) return false;
    uint32_t vs = 0;
    for (int x : p) { if (vs >> x & 1) return false; vs |= 1u << x; }
    for (size_t i = 0; i + 1 < p.size(); i++) {
      int a = p[i], b = p[i + 1];
      if (!G.has(a, b) || (used[a] >> b & 1)) return false;
      used[a] |= 1u << b; used[b] |= 1u << a;
    }
    ends[p.front()]++; ends[p.back()]++;
  }
  for (int v = 0; v < G.N; v++) { if (used[v] != G.adj[v]) return false; if (ends[v] != (G.deg(v) & 1)) return false; }
  return true;
}
}  // namespace dec
