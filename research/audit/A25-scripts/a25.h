// a25.h -- independent library for audit A25 (l1-induction).  Written for the audit; it does not
// include or copy any of the authors' code (lind.h, orc2.h, dec.h, moves.h).
//
// * own graph6 decoder;
// * path decompositions with prescribed end counts by TRANSITION SYSTEMS: at every vertex v choose
//   b(v) of the incident edges as path ends and pair the others (transitions); a choice is valid iff
//   every resulting trail is open and visits no vertex twice.  Components are kept in a union-find
//   with undo, together with their vertex mask and edge count; a merge is allowed only if the two
//   chains share exactly the junction vertex, so every component is always a path.
// * an avoidance oracle (exists a decomposition whose path ending at c avoids A), pruned on the
//   component that carries c's end;
// * the forced Fan chain on a decomposition with b <= 1 (tight-fan Prop. 2.1), implemented here.
#pragma once
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#include <functional>
#include <algorithm>

namespace a25 {

static const int MV = 32;

struct Graph {
  int n = 0;
  uint32_t adj[MV];
  Graph() { memset(adj, 0, sizeof adj); }
  int deg(int v) const { return __builtin_popcount(adj[v]); }
  bool has(int a, int b) const { return (adj[a] >> b) & 1u; }
  void add(int a, int b) { adj[a] |= 1u << b; adj[b] |= 1u << a; }
  void rem(int a, int b) { adj[a] &= ~(1u << b); adj[b] &= ~(1u << a); }
  int m() const { int s = 0; for (int v = 0; v < n; v++) s += deg(v); return s / 2; }
  uint32_t evenset() const { uint32_t e = 0; for (int v = 0; v < n; v++) { int d = deg(v); if (d > 0 && d % 2 == 0) e |= 1u << v; } return e; }
  uint32_t component(int v) const { uint32_t s = 1u << v; bool ch = true; while (ch) { ch = false; for (int x = 0; x < n; x++) if ((s >> x & 1u) && (adj[x] & ~s)) { s |= adj[x]; ch = true; } } return s; }
};

// graph6, written from the format description (n <= 62): bits of the upper triangle in column order
// (0,1),(0,2),(1,2),(0,3),..., six bits per byte, most significant first, each byte offset by 63.
static bool decode_g6(const std::string& s0, Graph& G) {
  std::string s = s0;
  while (!s.empty() && (s.back() == '\n' || s.back() == '\r' || s.back() == ' ')) s.pop_back();
  if (s.empty()) return false;
  int n = (unsigned char)s[0] - 63;
  if (n < 0 || n > MV) return false;
  std::vector<int> bits;
  for (size_t i = 1; i < s.size(); i++) { int x = (unsigned char)s[i] - 63; for (int k = 5; k >= 0; k--) bits.push_back((x >> k) & 1); }
  G = Graph(); G.n = n;
  size_t p = 0;
  for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) { if (p >= bits.size()) return false; if (bits[p++]) G.add(i, j); }
  return true;
}

typedef std::vector<int> Path;
typedef std::vector<Path> Dec;

// ---------- transition-system enumerator ----------
struct TS {
  int n, m;
  int eu[256], ev[256];
  std::vector<int> inc[MV];
  int b[MV];
  int order[MV];
  // slot (e, side): side 0 = endpoint eu[e], 1 = endpoint ev[e]; partner = -1 unassigned, -2 end, else slot id
  std::vector<int> partner;
  // union-find over edges with undo
  std::vector<int> par, ecount; std::vector<uint32_t> vmask; std::vector<char> hasC;
  struct Undo { int a, b; int ea; uint32_t ma; char ca; };
  std::vector<Undo> stk;
  int C = -1; uint32_t AV = 0;   // avoidance: the component with c's end must avoid AV
  bool stop = false;
  long long nodes = 0, budget = 0; bool aborted = false;
  std::function<bool(TS&)> cb;   // called on a complete system; return true to stop

  int find(int x) const { while (par[x] != x) x = par[x]; return x; }
  void init(const Graph& G, const int* bb) {
    n = G.n; m = 0;
    for (int v = 0; v < n; v++) inc[v].clear();
    for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++) if (G.has(u, v)) { eu[m] = u; ev[m] = v; inc[u].push_back(2 * m); inc[v].push_back(2 * m + 1); m++; }
    for (int v = 0; v < n; v++) b[v] = bb[v];
    partner.assign(2 * m, -1); par.resize(m); ecount.assign(m, 1); vmask.resize(m); hasC.assign(m, 0);
    for (int e = 0; e < m; e++) { par[e] = e; vmask[e] = (1u << eu[e]) | (1u << ev[e]); }
    stk.clear();
    // vertex order: BFS from C if given, else from 0, then the rest
    bool seen[MV] = {false}; int k = 0;
    auto bfs = [&](int s) { int q[MV], h = 0, t = 0; q[t++] = s; seen[s] = true; while (h < t) { int x = q[h++]; order[k++] = x; for (int y = 0; y < n; y++) if (G.has(x, y) && !seen[y]) { seen[y] = true; q[t++] = y; } } };
    if (C >= 0) bfs(C);
    for (int v = 0; v < n; v++) if (!seen[v]) bfs(v);
  }
  int vert(int slot) const { return (slot & 1) ? ev[slot >> 1] : eu[slot >> 1]; }
  bool merge(int e1, int e2, int junction) {
    int r1 = find(e1), r2 = find(e2);
    if (r1 == r2) return false;  // would close a cycle
    if ((vmask[r1] & vmask[r2]) != (1u << junction)) return false;
    uint32_t nm = vmask[r1] | vmask[r2]; char nc = hasC[r1] | hasC[r2];
    if (nc && (nm & AV)) return false;
    if (ecount[r1] < ecount[r2]) std::swap(r1, r2);
    stk.push_back({r1, r2, ecount[r1], vmask[r1], hasC[r1]});
    par[r2] = r1; ecount[r1] += ecount[r2]; vmask[r1] = nm; hasC[r1] = nc;
    return true;
  }
  void unmerge() { Undo u = stk.back(); stk.pop_back(); par[u.b] = u.b; ecount[u.a] = u.ea; vmask[u.a] = u.ma; hasC[u.a] = u.ca; }
  bool markC(int e) {  // the end at C is on edge e
    int r = find(e);
    if (vmask[r] & AV) return false;
    stk.push_back({r, r, ecount[r], vmask[r], hasC[r]}); hasC[r] = 1; return true;
  }
  void unmarkC() { Undo u = stk.back(); stk.pop_back(); hasC[u.a] = u.ca; }
  // assign slots at vertex order[k]; ends_left ends still to place there
  void at_vertex(int k, int ends_left) {
    if (stop || aborted) return;
    if (budget && ++nodes > budget) { aborted = true; return; }
    if (k == n) { if (cb(*this)) stop = true; return; }
    int v = order[k];
    int first = -1;
    for (int s : inc[v]) if (partner[s] == -1) { first = s; break; }
    if (first < 0) { if (ends_left == 0) at_vertex(k + 1, k + 1 < n ? b[order[k + 1]] : 0); return; }
    // count unassigned
    int un = 0; for (int s : inc[v]) if (partner[s] == -1) un++;
    if (ends_left > un) return;
    if ((un - ends_left) % 2) return;
    // option 1: first is an end
    if (ends_left > 0) {
      partner[first] = -2;
      bool ok = true;
      if (v == C) ok = markC(first >> 1);
      if (ok) { at_vertex(k, ends_left - 1); if (v == C) unmarkC(); }
      partner[first] = -1;
      if (stop || aborted) return;
    }
    // option 2: pair first with another unassigned slot
    for (int s : inc[v]) if (s != first && partner[s] == -1) {
      if (!merge(first >> 1, s >> 1, v)) continue;
      partner[first] = s; partner[s] = first;
      at_vertex(k, ends_left);
      partner[first] = -1; partner[s] = -1;
      unmerge();
      if (stop || aborted) return;
    }
  }
  void run() { stop = false; aborted = false; nodes = 0; if (n == 0) { cb(*this); return; } at_vertex(0, b[order[0]]); }
  // extract the paths of a complete system
  Dec paths() const {
    Dec D; std::vector<char> used(m, 0);
    for (int e = 0; e < m; e++) if (!used[e]) {
      // walk to one end of the trail containing e
      int cur = e, side = 0;  // leave edge cur through side 'side'
      // go towards side 0 until an end
      int s = 2 * cur + 0; int guard = 0;
      while (partner[s] >= 0 && guard++ < 1000) { int t = partner[s]; cur = t >> 1; s = 2 * cur + (1 - (t & 1)); }
      // now s is an end slot of edge cur; walk forward
      Path P; P.push_back(vert(s));
      int x = s; (void)side;
      while (true) {
        int e2 = x >> 1; used[e2] = 1; int other = 2 * e2 + (1 - (x & 1)); P.push_back(vert(other));
        if (partner[other] < 0) break;
        x = partner[other];
      }
      D.push_back(P);
    }
    return D;
  }
};

static void lovasz_b(const Graph& G, int* b) { for (int v = 0; v < G.n; v++) b[v] = G.deg(v) % 2; }

// enumerate all decompositions with end counts b (default: Lovász); callback gets the paths
static long long enumerate(const Graph& G, const int* bb, std::function<bool(const Dec&)> f, int C = -1, uint32_t AV = 0) {
  TS T; T.C = C; T.AV = AV;
  int b[MV]; if (bb) memcpy(b, bb, sizeof(int) * G.n); else lovasz_b(G, b);
  T.init(G, b);
  long long cnt = 0;
  T.cb = [&](TS& t) { cnt++; return f(t.paths()); };
  T.run();
  return cnt;
}

// 1 good, 0 not good, 2 budget exhausted.  Lovász end counts; requires c odd.
static int good(const Graph& G, int c, uint32_t A, long long budget = 0) {
  if (G.deg(c) % 2 == 0) return 0;
  if ((A >> c) & 1u) return 0;
  TS T; T.C = c; T.AV = A; T.budget = budget;
  int b[MV]; lovasz_b(G, b); T.init(G, b);
  bool found = false; T.cb = [&](TS&) { found = true; return true; };
  T.run();
  if (found) return 1;
  if (T.aborted) return 2;
  return 0;
}

// all distinct vertex sets V(Q_c) over all Lovász decompositions, for every odd c (antichain of
// inclusion-minimal sets per c).  Goodness of (G,c,A) = some minimal set misses A.
static void qc_sets(const Graph& G, std::vector<std::vector<uint32_t>>& out) {
  out.assign(G.n, {});
  std::vector<std::vector<uint32_t>> raw(G.n);
  enumerate(G, nullptr, [&](const Dec& D) {
    for (auto& P : D) { uint32_t mk = 0; for (int x : P) mk |= 1u << x; raw[P.front()].push_back(mk); raw[P.back()].push_back(mk); }
    return false; });
  for (int c = 0; c < G.n; c++) {
    auto& r = raw[c]; std::sort(r.begin(), r.end()); r.erase(std::unique(r.begin(), r.end()), r.end());
    std::sort(r.begin(), r.end(), [](uint32_t a, uint32_t b) { return __builtin_popcount(a) < __builtin_popcount(b); });
    std::vector<uint32_t> mn;
    for (uint32_t x : r) { bool dom = false; for (uint32_t y : mn) if ((y & x) == y) { dom = true; break; } if (!dom) mn.push_back(x); }
    out[c] = mn;
  }
}
static bool good_from_sets(const std::vector<uint32_t>& S, uint32_t A) { for (uint32_t x : S) if (!(x & A)) return true; return false; }

// check a decomposition of G with end counts b (default Lovász)
static bool check(const Graph& G, const Dec& D, const int* bb = nullptr) {
  int b[MV]; if (bb) memcpy(b, bb, sizeof(int) * G.n); else lovasz_b(G, b);
  uint32_t used[MV] = {0}; int ends[MV] = {0};
  for (auto& P : D) {
    if (P.size() < 2) return false;
    uint32_t vs = 0; for (int x : P) { if (vs >> x & 1u) return false; vs |= 1u << x; }
    for (size_t i = 0; i + 1 < P.size(); i++) { int a = P[i], c = P[i + 1]; if (!G.has(a, c) || (used[a] >> c & 1u)) return false; used[a] |= 1u << c; used[c] |= 1u << a; }
    ends[P.front()]++; ends[P.back()]++;
  }
  for (int v = 0; v < G.n; v++) { if (used[v] != G.adj[v]) return false; if (ends[v] != b[v]) return false; }
  return true;
}

static int path_ending_at(const Dec& D, int c) { int idx = -1, k = 0; for (size_t i = 0; i < D.size(); i++) { if (D[i].front() == c) { idx = (int)i; k++; } if (D[i].back() == c) { idx = (int)i; k++; } } return k == 1 ? idx : -1; }
static uint32_t vset(const Path& P) { uint32_t s = 0; for (int x : P) s |= 1u << x; return s; }

// Forced Fan chain: D decomposes K with b <= 1, t and w non-adjacent in K, every neighbour of w has
// an end.  x_0 = t; x_{i+1} = vertex before w on the ORIGINAL path of D with an end at x_i, read from
// x_i; stop at the first x_k whose path avoids w.  Execution: re-route the paths of x_0..x_{k-1}
// (reverse the segment x_i..x_{i+1} and join x_i to w), then append w to the path of x_k.
// Returns false if the chain is stuck (some x_{i+1} has no end).
static bool forced_chain(const Dec& D, int t, int w, Dec& out, std::vector<int>& chain) {
  out = D; chain.clear();
  int nv = 0; for (auto& P : D) for (int x : P) nv = std::max(nv, x + 1);
  nv = std::max(nv, std::max(t, w) + 1);
  std::vector<int> who(nv, -1);
  for (size_t i = 0; i < D.size(); i++) { who[D[i].front()] = (int)i; who[D[i].back()] = (int)i; }
  int x = t;
  for (int guard = 0; guard < 100; guard++) {
    chain.push_back(x);
    int pi = who[x]; if (pi < 0) return false;
    Path& P = out[pi];
    if (P.front() != x) std::reverse(P.begin(), P.end());
    if (P.front() != x) return false;
    int k = -1; for (size_t j = 0; j < P.size(); j++) if (P[j] == w) { k = (int)j; break; }
    if (k < 0) { P.insert(P.begin(), w); return true; }
    int y = P[k - 1];
    Path NP; for (int j = k - 1; j >= 0; j--) NP.push_back(P[j]); for (size_t j = k; j < P.size(); j++) NP.push_back(P[j]);
    P = NP; x = y;
    for (int z : chain) if (z == x) return false;  // chain must be injective
  }
  return false;
}

static std::string dstr(const Dec& D) { std::string s = "{"; for (size_t i = 0; i < D.size(); i++) { if (i) s += ", "; for (int x : D[i]) s += std::to_string(x); } return s + "}"; }
static std::string sstr(uint32_t S) { std::string s = "{"; bool f = true; for (int v = 0; v < 32; v++) if (S >> v & 1u) { if (!f) s += ","; s += std::to_string(v); f = false; } return s + "}"; }
static uint32_t closedN(const Graph& G, int v) { return G.adj[v] | (1u << v); }
static int theeven(const Graph& G) { uint32_t e = G.evenset(); return e ? __builtin_ctz(e) : -1; }
static uint32_t amax(const Graph& G, int c) { int g = theeven(G); uint32_t loc = closedN(G, c) | (g >= 0 ? G.adj[g] : 0); uint32_t A = 0; for (int v = 0; v < G.n; v++) if (G.deg(v) > 0 && !(loc >> v & 1u)) A |= 1u << v; return A; }
static bool admissible(const Graph& G, int c, uint32_t A) { int g = theeven(G); uint32_t bad = closedN(G, c) | (g >= 0 ? G.adj[g] : 0); return !(A & bad); }
static bool blocked(const Graph& G, int c, uint32_t A) { int g = theeven(G); if (g < 0 || G.has(g, c)) return false; for (int u = 0; u < G.n; u++) if (G.has(g, u) && !(G.adj[u] & A & ~(1u << g))) return false; return true; }
}  // namespace a25
