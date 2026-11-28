// a41.cpp -- independent re-derivation for audit A41 (nodata).  Written from the manuscript's
// definitions only; it shares no code with nd.c / ndsolve.h / fl.c / route_ext.c.
//
// Solver: does a graph H with every degree odd (isolated vertices allowed: need 0) have a Lovasz
// decomposition (paths, exactly deg mod 2 ends per vertex) such that
//   (A) for every v: V(Q(v)) cap avoid[v] = empty      (Q(v) the path ending at v), and
//   (S) no path has two ends x, y with sibpair[x] containing y?
// Search: pick an unended vertex s of least remaining degree; enumerate every simple path from s
// in the remaining graph that never enters avoid[s]; close it at any unended vertex w with
// avoid[w] cap V(P) = empty and (s, w) not a sibling pair; recurse.  Failures are memoised under
// (remaining edge set, ended set).  Only pruning: an unended vertex must have an edge; every
// component of the remaining graph that has an edge contains an unended vertex.  Every solution
// found is re-verified by verify().
//
// Modes:
//   a41 tiers      < graph6   : (T1) instances (3-connected, delta>=3, one even vertex), every root
//                               without matching data: tier 1..5, least excess at tier 3/4, twins,
//                               deficiency, linkage existence.  One line per root.
//   a41 univ       < graph6   : universality counts over every structure (as nodata Obs. 2.1(b)).
//   a41 fam F      < graph6   : abstract families on connected all-odd graphs; F in
//                               k kp kk kpp c cp r l lk ss.
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;
typedef unsigned int u32;

// ------------------------------------------------------------------ solver
static bool getenv_prune = getenv("A41_PRUNE") != nullptr;   // optional extra (sound) pruning
struct Solver {
  int n, m;
  int eu[64], ev[64];
  u64 inc[16];
  u32 avoid[16];
  u32 sib[16];      // sib[x] bit y: x, y siblings (Q(x) != Q(y))
  u32 need;         // vertices that need an end (odd degree)
  unordered_set<unsigned __int128> fail;
  vector<vector<int>> sol, cur;
  long long nodes;
  void init(int n_) { n = n_; m = 0; for (int v = 0; v < n; v++) { inc[v] = 0; avoid[v] = 0; sib[v] = 0; } }
  void add(int a, int b) { eu[m] = a; ev[m] = b; inc[a] |= 1ULL << m; inc[b] |= 1ULL << m; m++; }
  bool comp_ok(u64 rem, u32 ended) {
    u32 seen = 0;
    for (int v = 0; v < n; v++) {
      if ((seen >> v & 1) || !(rem & inc[v])) continue;
      u32 c = 1u << v, fr = c;
      while (fr) {
        int x = __builtin_ctz(fr); fr &= fr - 1;
        u64 ex = rem & inc[x];
        while (ex) { int e = __builtin_ctzll(ex); ex &= ex - 1; int y = eu[e] == x ? ev[e] : eu[e];
          if (!(c >> y & 1)) { c |= 1u << y; fr |= 1u << y; } }
      }
      seen |= c;
      if (!(c & need & ~ended)) return false;
      if (getenv_prune) { int t = __builtin_popcount(c & need & ~ended); if (t & 1) return false; }
    }
    return true;
  }
  vector<int> path;
  bool grow(int s, int x, u64 rem, u32 ended, u32 vis) {
    u64 ex = rem & inc[x];
    while (ex) {
      int e = __builtin_ctzll(ex); ex &= ex - 1;
      int w = eu[e] == x ? ev[e] : eu[e];
      if (vis >> w & 1) continue;
      if (avoid[s] >> w & 1) continue;             // Q(s) may not contain avoid[s]
      u64 rem2 = rem & ~(1ULL << e);
      u32 vis2 = vis | (1u << w);
      path.push_back(w);
      if ((need >> w & 1) && !(ended >> w & 1) && !(avoid[w] & vis2) && !(sib[s] >> w & 1)) {
        cur.push_back(path);
        if (rec(rem2, ended | (1u << s) | (1u << w))) return true;
        cur.pop_back();
      }
      if (rem2 & inc[w]) { if (grow(s, w, rem2, ended, vis2)) return true; }
      path.pop_back();
    }
    return false;
  }
  bool rec(u64 rem, u32 ended) {
    nodes++;
    u32 todo = need & ~ended;
    if (!todo) return rem == 0;
    int best = -1, bd = 1 << 20;
    int P = __builtin_popcount(todo) / 2;
    for (int v = 0; v < n; v++) {
      int d = __builtin_popcountll(rem & inc[v]);
      int nd = todo >> v & 1;
      // sound: each remaining path uses <= 2 edges at v, and the one ending at v uses 1
      if (getenv_prune && d > 2 * P - nd) return false;
      if (!nd) continue;
      if (d == 0) return false;
      if (d < bd) { bd = d; best = v; }
    }
    if (!comp_ok(rem, ended)) return false;
    unsigned __int128 key = ((unsigned __int128)rem << 32) | ended;
    if (fail.count(key)) return false;
    vector<int> save = path;
    path.assign(1, best);
    bool ok = grow(best, best, rem, ended, (1u << best));
    path = save;
    if (!ok) fail.insert(key);
    return ok;
  }
  bool solve() {
    need = 0;
    for (int v = 0; v < n; v++) if (__builtin_popcountll(inc[v]) & 1) need |= 1u << v;
    for (int v = 0; v < n; v++) if (__builtin_popcountll(inc[v]) && !(__builtin_popcountll(inc[v]) & 1)) {
      fprintf(stderr, "solver: even vertex\n"); exit(2); }
    fail.clear(); cur.clear(); path.clear(); nodes = 0;
    u64 full = m == 64 ? ~0ULL : ((1ULL << m) - 1);
    bool ok = rec(full, 0);
    if (ok) { sol = cur; verify(); }
    return ok;
  }
  void verify() {
    // the solution is a Lovasz decomposition satisfying (A), (S)
    u64 used = 0; int ends[16] = {0};
    int Q[16]; for (int v = 0; v < n; v++) Q[v] = -1;
    for (size_t i = 0; i < sol.size(); i++) {
      auto &P = sol[i];
      u32 vs = 0;
      for (int x : P) { if (vs >> x & 1) { fprintf(stderr, "verify: not a path\n"); exit(3); } vs |= 1u << x; }
      for (size_t j = 0; j + 1 < P.size(); j++) {
        int e = -1;
        for (int k = 0; k < m; k++) if ((eu[k] == P[j] && ev[k] == P[j + 1]) || (ev[k] == P[j] && eu[k] == P[j + 1])) e = k;
        if (e < 0 || (used >> e & 1)) { fprintf(stderr, "verify: bad edge\n"); exit(3); }
        used |= 1ULL << e;
      }
      ends[P.front()]++; ends[P.back()]++;
      Q[P.front()] = i; Q[P.back()] = i;
    }
    u64 full = m == 64 ? ~0ULL : ((1ULL << m) - 1);
    if (used != full) { fprintf(stderr, "verify: not all edges\n"); exit(3); }
    for (int v = 0; v < n; v++) if (ends[v] != (int)(need >> v & 1)) { fprintf(stderr, "verify: ends\n"); exit(3); }
    for (int v = 0; v < n; v++) if (Q[v] >= 0) {
      u32 vs = 0; for (int x : sol[Q[v]]) vs |= 1u << x;
      if (vs & avoid[v]) { fprintf(stderr, "verify: avoid\n"); exit(3); }
      for (int y = 0; y < n; y++) if ((sib[v] >> y & 1) && Q[y] == Q[v]) { fprintf(stderr, "verify: sib\n"); exit(3); }
    }
  }
};

// ------------------------------------------------------------------ graphs
static int N; static u32 A[16]; static string g6s;
static bool read_g6(const string &s) {
  N = (unsigned char)s[0] - 63; if (N < 1 || N > 16) return false;
  int k = 1, bit = 0, curb = 0;
  for (int v = 0; v < N; v++) A[v] = 0;
  for (int j = 1; j < N; j++) for (int i = 0; i < j; i++) {
    if (bit == 0) { curb = (unsigned char)s[k++] - 63; bit = 6; }
    bit--;
    if (curb >> bit & 1) { A[i] |= 1u << j; A[j] |= 1u << i; }
  }
  return true;
}
static bool conn(u32 S) {
  if (!S) return true;
  u32 c = S & -S, fr = c;
  while (fr) { int x = __builtin_ctz(fr); fr &= fr - 1; u32 nb = A[x] & S & ~c; c |= nb; fr |= nb; }
  return c == S;
}
static bool three_conn() {
  u32 all = (1u << N) - 1;
  if (N < 4 || !conn(all)) return false;
  for (int a = 0; a < N; a++) { if (!conn(all & ~(1u << a))) return false;
    for (int b = a + 1; b < N; b++) if (!conn(all & ~(1u << a) & ~(1u << b))) return false; }
  return true;
}
static bool pm(u32 S) {   // perfect matching of the graph induced on S
  if (!S) return true;
  int a = __builtin_ctz(S); u32 S2 = S & ~(1u << a);
  for (u32 nb = A[a] & S2; nb; nb &= nb - 1) { int b = __builtin_ctz(nb); if (pm(S2 & ~(1u << b))) return true; }
  return false;
}
static int nu(u32 S) {
  if (!S) return 0;
  int a = __builtin_ctz(S); u32 S2 = S & ~(1u << a);
  int best = nu(S2);
  for (u32 nb = A[a] & S2; nb; nb &= nb - 1) { int b = __builtin_ctz(nb); best = max(best, 1 + nu(S2 & ~(1u << b))); }
  return best;
}

// ------------------------------------------------------------------ the (T1) instance
static int Z, R; static u32 T, VB;
// forest given by parent array over vertices (-1 = root or not in Phi), plus edge list of Phi.
// base graph H = (J - z) - Phi; constraints: avoid[v] = {p(v)}, siblings share a parent.
static Solver S;
static bool base_ok(const int *par) {
  if (getenv("A41_COUNTONLY")) return true;   // population counts only (no solving)
  S.init(N);
  for (int u = 0; u < N; u++) for (int v = u + 1; v < N; v++) {
    if (u == Z || v == Z || !(A[u] >> v & 1)) continue;
    if (par[u] == v || par[v] == u) continue;     // a forest edge
    S.add(u, v);
  }
  for (int v = 0; v < N; v++) if (par[v] >= 0) S.avoid[v] = 1u << par[v];
  for (int x = 0; x < N; x++) for (int y = 0; y < N; y++)
    if (x != y && par[x] >= 0 && par[x] == par[y]) S.sib[x] |= 1u << y;
  return S.solve();
}

// linkages: list of T-paths (vertex sequences), interiors outside T, vertex-disjoint, covering T
static vector<vector<int>> curL;
static void linkages(u32 U, u32 used, int maxlen, vector<vector<vector<int>>> &out) {
  if (!U) { out.push_back(curL); return; }
  int a = __builtin_ctz(U);
  vector<int> P = {a};
  // DFS from a through non-T vertices
  function<void(int, u32)> dfs = [&](int x, u32 vis) {
    for (u32 nb = A[x] & VB; nb; nb &= nb - 1) {
      int y = __builtin_ctz(nb);
      if (vis >> y & 1) continue;
      if (T >> y & 1) {
        if ((U >> y & 1) && y != a) {
          P.push_back(y); curL.push_back(P);
          linkages(U & ~(1u << a) & ~(1u << y), used | vis, maxlen, out);
          curL.pop_back(); P.pop_back();
        }
        continue;
      }
      if (used >> y & 1) continue;
      if (maxlen && (int)P.size() >= maxlen) continue;   // P has P.size()-1 edges; one more interior
      P.push_back(y);
      dfs(y, vis | (1u << y));
      P.pop_back();
    }
  };
  dfs(a, 1u << a);
}
// end-rootings of a linkage with r a root: for each path, choose an end (r's path rooted at r)
static void linkage_rootings(const vector<vector<int>> &L, vector<array<int, 16>> &out) {
  int k = L.size(); int ri = -1;
  for (int i = 0; i < k; i++) if (L[i].front() == R || L[i].back() == R) ri = i;
  for (int mask = 0; mask < (1 << k); mask++) {
    array<int, 16> par; par.fill(-1);
    bool ok = true;
    for (int i = 0; i < k; i++) {
      vector<int> P = L[i];
      if (mask >> i & 1) reverse(P.begin(), P.end());
      if (i == ri && P.front() != R) { ok = false; break; }
      for (size_t j = 0; j + 1 < P.size(); j++) par[P[j + 1]] = P[j];
    }
    if (ok) out.push_back(par);
  }
}
// all forest T-joins of B = J - z, by the cycle space (T-join J0 xor fundamental cycles)
static vector<u64> forestTJoins(vector<pair<int,int>> &E) {
  E.clear();
  for (int u = 0; u < N; u++) for (int v = u + 1; v < N; v++)
    if (u != Z && v != Z && (A[u] >> v & 1)) E.push_back({u, v});
  int m = E.size();
  // spanning tree by BFS from the smallest vertex of B
  int root = __builtin_ctz(VB);
  int tpar[16], tpe[16], depth[16]; for (int v = 0; v < 16; v++) { tpar[v] = -1; tpe[v] = -1; depth[v] = 0; }
  u32 seen = 1u << root; vector<int> q = {root}; u64 tree = 0;
  for (size_t h = 0; h < q.size(); h++) { int x = q[h];
    for (int e = 0; e < m; e++) { int a = E[e].first, b = E[e].second; int y = a == x ? b : (b == x ? a : -1);
      if (y < 0 || (seen >> y & 1)) continue; seen |= 1u << y; tpar[y] = x; tpe[y] = e; depth[y] = depth[x] + 1; tree |= 1ULL << e; q.push_back(y); } }
  if (seen != VB) { fprintf(stderr, "B disconnected\n"); exit(4); }
  auto tpath = [&](int a, int b) { u64 s = 0; while (a != b) { if (depth[a] >= depth[b]) { s ^= 1ULL << tpe[a]; a = tpar[a]; } else { s ^= 1ULL << tpe[b]; b = tpar[b]; } } return s; };
  // J0: pair the T vertices in order
  vector<int> tv; for (int v = 0; v < N; v++) if (T >> v & 1) tv.push_back(v);
  u64 J0 = 0; for (size_t i = 0; i + 1 < tv.size(); i += 2) J0 ^= tpath(tv[i], tv[i + 1]);
  vector<u64> cyc;
  for (int e = 0; e < m; e++) if (!(tree >> e & 1)) cyc.push_back((1ULL << e) ^ tpath(E[e].first, E[e].second));
  int c = cyc.size();
  vector<u64> res;
  u64 X = J0;
  for (u64 g = 0; g < (1ULL << c); g++) {
    if (g) { int b = __builtin_ctzll(g); X ^= cyc[b]; }
    // acyclic?  union-find
    int uf[16]; for (int v = 0; v < 16; v++) uf[v] = v;
    function<int(int)> fd = [&](int x) { while (uf[x] != x) x = uf[x] = uf[uf[x]]; return x; };
    bool ok = true;
    for (u64 y = X; y && ok; y &= y - 1) { int e = __builtin_ctzll(y); int a = fd(E[e].first), b = fd(E[e].second); if (a == b) ok = false; else uf[a] = b; }
    if (ok) res.push_back(X);
  }
  // sanity: parity
  for (u64 F : res) { u32 odd = 0; for (u64 y = F; y; y &= y - 1) { int e = __builtin_ctzll(y); odd ^= (1u << E[e].first) ^ (1u << E[e].second); } if (odd != T) { fprintf(stderr, "parity bug\n"); exit(5); } }
  return res;
}
// every rooting of forest F: lev 3 = r a root; lev 4 = r a child with c(r) >= 2
static void forest_rootings(u64 F, const vector<pair<int,int>> &E, int lev, vector<array<int,16>> &out) {
  u32 fa[16] = {0};
  for (u64 y = F; y; y &= y - 1) { int e = __builtin_ctzll(y); fa[E[e].first] |= 1u << E[e].second; fa[E[e].second] |= 1u << E[e].first; }
  vector<u32> comps; u32 seen = 0;
  for (int v = 0; v < N; v++) if (fa[v] && !(seen >> v & 1)) { u32 c = 1u << v, fr = c; while (fr) { int x = __builtin_ctz(fr); fr &= fr - 1; u32 nb = fa[x] & ~c; c |= nb; fr |= nb; } seen |= c; comps.push_back(c); }
  if (lev == 4 && __builtin_popcount(fa[R]) < 3) return;
  vector<vector<int>> choices;
  for (u32 c : comps) {
    vector<int> ch;
    for (u32 x = c; x; x &= x - 1) { int v = __builtin_ctz(x);
      if (c >> R & 1) { if (lev == 3 && v != R) continue; if (lev == 4 && v == R) continue; }
      ch.push_back(v); }
    choices.push_back(ch);
  }
  vector<size_t> idx(comps.size(), 0);
  while (true) {
    array<int,16> par; par.fill(-1);
    for (size_t i = 0; i < comps.size(); i++) {
      int rt = choices[i][idx[i]];
      vector<int> q = {rt}; u32 vis = 1u << rt;
      for (size_t h = 0; h < q.size(); h++) { int x = q[h]; for (u32 nb = fa[x] & ~vis; nb; nb &= nb - 1) { int y = __builtin_ctz(nb); vis |= 1u << y; par[y] = x; q.push_back(y); } }
    }
    out.push_back(par);
    size_t i = 0;
    while (i < comps.size()) { if (++idx[i] < choices[i].size()) break; idx[i] = 0; i++; }
    if (i == comps.size()) break;
  }
}
static int excess(const array<int,16> &par) {
  int ch[16] = {0}; for (int v = 0; v < N; v++) if (par[v] >= 0) ch[par[v]]++;
  int e = 0; for (int v = 0; v < N; v++) if (ch[v] > 1) e += ch[v] - 1; return e;
}
static bool is_claw_base(const array<int,16> &par) {
  // the unique vertex with two children is a child itself
  int ch[16] = {0}; for (int v = 0; v < N; v++) if (par[v] >= 0) ch[par[v]]++;
  for (int v = 0; v < N; v++) if (ch[v] >= 2 && par[v] < 0) return false;
  return true;
}

int main(int argc, char **argv) {
  string mode = argc > 1 ? argv[1] : "tiers";
  string fam = argc > 2 ? argv[2] : "k";
  string line;
  long long ug[6] = {0}, uf[6] = {0};
  long long graphs = 0, roots = 0, nodata = 0, lev[7] = {0};
  map<string, long long> famstat;
  while (getline(cin, line)) {
    if (line.empty() || !read_g6(line)) continue;
    g6s = line;
    if (mode == "fam") {
      // connected, every degree odd
      bool odd = true; for (int v = 0; v < N; v++) if (!(__builtin_popcount(A[v]) & 1)) odd = false;
      if (!odd || !conn((1u << N) - 1)) continue;
      famstat["graphs"]++;
      auto nonadj = [&](int a, int b) { return a != b && !(A[a] >> b & 1); };
      // units as (vertex list, avoid edges (v, w): w notin Q(v), sibling pairs)
      struct Unit { vector<int> vs; vector<pair<int,int>> av; vector<pair<int,int>> sb; char t; };
      auto gen = [&](char t) {
        vector<Unit> out;
        for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) {
          if (t == 'P') { if (nonadj(a, b)) out.push_back({{a, b}, {{a, b}}, {}, 'P'}); continue; }   // child a, parent b
          for (int c = 0; c < N; c++) {
            if (a == b || b == c || a == c) continue;
            if (t == 'K' && nonadj(a, b) && nonadj(b, c)) out.push_back({{a, b, c}, {{b, a}, {c, b}}, {}, 'K'});   // a <- b <- c
            if (t == 'R' && nonadj(a, b) && nonadj(b, c)) out.push_back({{a, b, c}, {{a, b}, {a, c}}, {}, 'R'});   // route a b c at a
            if (t == 'S' && b < c && nonadj(a, b) && nonadj(a, c)) out.push_back({{a, b, c}, {{b, a}, {c, a}}, {{b, c}}, 'S'});  // a <- {b, c}
            if (t == 'C' || t == 'L') for (int d = 0; d < N; d++) {
              if (d == a || d == b || d == c) continue;
              if (t == 'C' && nonadj(a, b) && nonadj(b, c) && nonadj(c, d)) out.push_back({{a, b, c, d}, {{b, a}, {c, b}, {d, c}}, {}, 'C'});
              if (t == 'L' && c < d && nonadj(a, b) && nonadj(b, c) && nonadj(b, d)) out.push_back({{a, b, c, d}, {{b, a}, {c, b}, {d, b}}, {{c, d}}, 'L'});  // a <- b <- {c, d}
            }
          }
        }
        return out;
      };
      vector<string> spec;
      if (fam == "k") spec = {"K"}; else if (fam == "kp") spec = {"K", "P"}; else if (fam == "kk") spec = {"K", "K"};
      else if (fam == "kpp") spec = {"K", "P", "P"}; else if (fam == "c") spec = {"C"}; else if (fam == "cp") spec = {"C", "P"};
      else if (fam == "r") spec = {"R"}; else if (fam == "l") spec = {"L"}; else if (fam == "lk") spec = {"L", "K"};
      else if (fam == "ss") spec = {"S", "S"}; else if (fam == "s") spec = {"S"}; else if (fam == "sp") spec = {"S", "P"};
      else if (fam == "sk") spec = {"S", "K"}; else if (fam == "lp") spec = {"L", "P"};
      else { fprintf(stderr, "family?\n"); return 1; }
      vector<vector<Unit>> lists; for (auto &s : spec) lists.push_back(gen(s[0]));
      auto mask = [&](const Unit &u) { u32 mk = 0; for (int v : u.vs) mk |= 1u << v; return mk; };
      // H1 at a vertex with two children
      auto h1 = [&](const Unit &u) -> int {
        int c0, c1, c2;
        if (u.t == 'S') { c0 = u.vs[0]; c1 = u.vs[1]; c2 = u.vs[2]; }
        else if (u.t == 'L') { c0 = u.vs[1]; c1 = u.vs[2]; c2 = u.vs[3]; }
        else return -1;
        u32 all = ((1u << N) - 1) & ~(1u << c0), seen = 0;
        for (int v = 0; v < N; v++) { if (!(all >> v & 1) || (seen >> v & 1)) continue;
          u32 c = 1u << v, fr = c; while (fr) { int x = __builtin_ctz(fr); fr &= fr - 1; u32 nb = A[x] & all & ~c; c |= nb; fr |= nb; }
          seen |= c; int k = (c >> c1 & 1) + (c >> c2 & 1); int e = __builtin_popcount(A[c0] & c);
          if (2 * k > __builtin_popcount(c) - e) return 0; }
        return 1;
      };
      auto runset = [&](vector<const Unit*> us) {
        if (getenv("A41_SKIP_H1")) {   // sets in which some star/claw violates (H1) fail by Lemma 5.5: count, do not search
          bool viol = false; for (auto *u : us) if (h1(*u) == 0) viol = true;
          if (viol) { famstat["skipped_H1_violated"]++; famstat["sets"]++; return; }
        }
        S.init(N);
        for (int u = 0; u < N; u++) for (int v = u + 1; v < N; v++) if (A[u] >> v & 1) S.add(u, v);
        for (auto *u : us) { for (auto &p : u->av) S.avoid[p.first] |= 1u << p.second; for (auto &p : u->sb) { S.sib[p.first] |= 1u << p.second; S.sib[p.second] |= 1u << p.first; } }
        famstat["sets"]++;
        bool ok = S.solve();
        if (!ok) {
          famstat["fail"]++;
          famstat["fail_n" + to_string(N)]++;
          int hv = 1; bool any = false;
          for (auto *u : us) { int h = h1(*u); if (h >= 0) { any = true; if (h == 0) hv = 0; } }
          if (any) famstat[hv ? "fail_all_H1_hold" : "fail_some_H1_violated"]++;
          if (fam == "r") { const Unit *u = us[0]; if (A[u->vs[0]] >> u->vs[2] & 1) famstat["fail_route_cb_edge"]++; }
          printf("FAIL %s", g6s.c_str());
          for (auto *u : us) { printf(" %c", u->t); for (int v : u->vs) printf(" %d", v); }
          if (any) printf(" allH1=%d", hv);
          printf("\n");
        }
      };
      if (spec.size() == 1) for (auto &u : lists[0]) runset({&u});
      else if (spec.size() == 2) {
        for (size_t i = 0; i < lists[0].size(); i++) for (size_t j = 0; j < lists[1].size(); j++) {
          if (spec[0] == spec[1] && j <= i) continue;
          if (mask(lists[0][i]) & mask(lists[1][j])) continue;
          runset({&lists[0][i], &lists[1][j]});
        }
      } else {
        for (size_t i = 0; i < lists[0].size(); i++) for (size_t j = 0; j < lists[1].size(); j++) for (size_t k = j + 1; k < lists[2].size(); k++) {
          u32 a = mask(lists[0][i]), b = mask(lists[1][j]), c = mask(lists[2][k]);
          if ((a & b) || (a & c) || (b & c)) continue;
          runset({&lists[0][i], &lists[1][j], &lists[2][k]});
        }
      }
      continue;
    }
    // (T1) instances
    int mind = 99; u32 ev = 0;
    for (int v = 0; v < N; v++) { int d = __builtin_popcount(A[v]); mind = min(mind, d); if (!(d & 1)) ev |= 1u << v; }
    if (mind < 3 || __builtin_popcount(ev) != 1 || !three_conn()) continue;
    graphs++;
    Z = __builtin_ctz(ev); T = A[Z]; VB = ((1u << N) - 1) & ~(1u << Z);
    bool hasdata = pm(T);
    int dz = __builtin_popcount(T);
    int deficiency = dz - 2 * nu(T);
    // forest T-joins are computed lazily, once per (J, z)
    vector<pair<int,int>> E; vector<u64> forests; bool fdone = false;
    vector<vector<vector<int>>> L1, L2;
    linkages(T, 0, 2, L1);
    bool l2done = false;
    if (mode == "univ" && !hasdata) { linkages(T, 0, 0, L2); l2done = true; }
    for (u32 rl = T; rl; rl &= rl - 1) {
      R = __builtin_ctz(rl); roots++;
      if (hasdata) continue;
      nodata++;
      // twins in T: J-degree 3, equal neighbourhoods
      int twinR = 0, twinO = 0;
      for (int a = 0; a < N; a++) for (int b = a + 1; b < N; b++)
        if ((T >> a & 1) && (T >> b & 1) && __builtin_popcount(A[a]) == 3 && A[a] == A[b]) { if (a == R || b == R) twinR = 1; else twinO = 1; }
      if (mode == "univ") {
        // tier 1: linkages with paths <= 2 edges; tier 2: linkages with a path of >= 3 edges
        for (auto &L : L1) { vector<array<int,16>> rs; linkage_rootings(L, rs); for (auto &p : rs) { ug[1]++; if (!base_ok(p.data())) uf[1]++; } }
        for (auto &L : L2) { bool lng = false; for (auto &P : L) if (P.size() > 3) lng = true; if (!lng) continue;
          vector<array<int,16>> rs; linkage_rootings(L, rs); for (auto &p : rs) { ug[2]++; if (!base_ok(p.data())) uf[2]++; } }
        if (!fdone) { forests = forestTJoins(E); fdone = true; }
        for (u64 F : forests) for (int lv = 3; lv <= 4; lv++) {
          vector<array<int,16>> rs; forest_rootings(F, E, lv, rs);
          for (auto &p : rs) { if (lv == 3 && excess(p) == 0) continue; ug[lv]++;
            bool okb = base_ok(p.data());
            if (!okb) uf[lv]++;
            if (lv == 3) { printf("U3 %s %s %d %d exc %d par", okb ? "SUCC" : "FAIL", g6s.c_str(), Z, R, excess(p)); for (int v = 0; v < N; v++) printf(" %d", p[v]); printf("\n"); } }
        }
        continue;
      }
      int level = 0, exc = -1; int claw = -1;
      for (auto &L : L1) { vector<array<int,16>> rs; linkage_rootings(L, rs); for (auto &p : rs) if (base_ok(p.data())) { level = 1; exc = 0; break; } if (level) break; }
      if (!level && !l2done) { linkages(T, 0, 0, L2); l2done = true; }
      if (!level) for (auto &L : L2) { vector<array<int,16>> rs; linkage_rootings(L, rs); for (auto &p : rs) if (base_ok(p.data())) { level = 2; exc = 0; break; } if (level) break; }
      int nlink = l2done ? (int)L2.size() : -1;   // -1: not enumerated (a tier-1 base was found)
      long long n3 = 0, n4 = 0, ok3 = 0;
      if (!level && getenv("A41_MAXTIER") && atoi(getenv("A41_MAXTIER")) == 2) level = 3;   // report "tier >= 3" without searching forests
      if (!level) {
        if (!fdone) { forests = forestTJoins(E); fdone = true; }
        for (int lv = 3; lv <= 4 && !level; lv++) {
          vector<array<int,16>> all;
          for (u64 F : forests) forest_rootings(F, E, lv, all);
          if (lv == 3) n3 = all.size(); else n4 = all.size();
          // least excess with a base
          int best = 1 << 20;
          for (auto &p : all) { int e = excess(p); if (e >= best) continue; if (base_ok(p.data())) { best = e; if (lv == 3) claw = is_claw_base(p) ? 1 : 0; } }
          if (best < (1 << 20)) { level = lv; exc = best; }
        }
        if (!level) level = 5;
      }
      lev[level]++;
      printf("T1 %s %d %d dz %d def %d tier %d exc %d twinR %d twinO %d linkages %d n3 %lld n4 %lld claw %d nforests %zu\n",
             g6s.c_str(), Z, R, dz, deficiency, level, exc, twinR, twinO, nlink, n3, n4, claw, fdone ? forests.size() : (size_t)0);
    }
  }
  if (mode == "fam") { for (auto &kv : famstat) fprintf(stderr, "%s=%lld ", kv.first.c_str(), kv.second); fprintf(stderr, "\n"); return 0; }
  if (mode == "univ") fprintf(stderr, "UNIV tier1 %lld/%lld tier2 %lld/%lld tier3 %lld/%lld tier4 %lld/%lld (failures/structures)\n", uf[1], ug[1], uf[2], ug[2], uf[3], ug[3], uf[4], ug[4]);
  fprintf(stderr, "SUMMARY graphs=%lld roots=%lld nodata=%lld tiers %lld %lld %lld %lld %lld\n", graphs, roots, nodata, lev[1], lev[2], lev[3], lev[4], lev[5]);
  return 0;
}
