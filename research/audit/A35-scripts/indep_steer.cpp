// indep_steer.cpp (audit A35).  Independent recomputation of Table 1 (with (C0)) and Table 2 of
// manuscripts/trn/trn.tex.  It shares no code with the authors' tools (no lind.h, orc2.h, dec.h,
// steer*.cpp): its own graph6 parser, its own goodness oracle, its own schedule search.
//
// Goodness oracle.  (H, y, {x}) is good iff some simple path P from y to an odd vertex z != y with
// x notin V(P) leaves H - E(P) with a "parity decomposition" (every vertex an end of exactly
// deg mod 2 paths).  PD(H) holds iff H has no edge, or, for the least odd vertex w of H, some simple
// path from w to another odd vertex z leaves a graph with PD.  (In H - E(P) the required end counts
// are again the degree parities, so the recursion is exact.)  Memoised on the edge mask of G.
//
// Schedule search (Definition 6.3).  G+ = G + y l with l = n an explicit new vertex, X = {l, x}.
// A state is (edge mask of the current graph, position of the g-token, position of the y-token).
// A move of the token at p to q: pq present, q != x, q != l, q != the other token's position, and
// after deleting pq the vertex q is not adjacent to the other token.  The move retires the token
// if q is isolated after the deletion (the edge y l is counted).  A schedule exists iff some state
// reachable from (E(G+), g, y) has a retiring move.  Forward BFS over all reachable states.
//
// Pruning (exact): Lovasz's theorem (every component with at most one even vertex has a parity
// decomposition); a vertex lies on at most P = #odd/2 paths, so d(v) <= 2P - (d(v) mod 2); every
// component with an edge needs an odd vertex.
// build: g++ -O2 -std=c++17 -o indep_steer indep_steer.cpp
// usage: indep_steer [full] < graphs.g6       (full: also the whole Table 1, every TRN test)
//        SKIPSCHED=1 skips the schedule searches (oracle timing only)
// Output: summary lines, and per-triple lines "T g6 g y x isN tight sched schedY schedFirstY nCore"
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;

static int n, m;
static int A[20][20];
static vector<pair<int, int>> E;
static u64 inc[20];

static bool parse(const string& s) {
  if (s.empty()) return false;
  n = s[0] - 63;
  if (n < 1 || n > 15) return false;
  vector<int> bits;
  for (size_t i = 1; i < s.size(); i++) {
    int v = s[i] - 63;
    for (int k = 5; k >= 0; k--) bits.push_back((v >> k) & 1);
  }
  memset(A, 0, sizeof A);
  size_t p = 0;
  for (int j = 1; j < n; j++)
    for (int i = 0; i < j; i++) {
      if (p < bits.size() && bits[p]) A[i][j] = A[j][i] = 1;
      p++;
    }
  E.clear();
  for (int i = 0; i < n; i++)
    for (int j = i + 1; j < n; j++)
      if (A[i][j]) E.push_back({i, j});
  m = E.size();
  for (int v = 0; v < 20; v++) inc[v] = 0;
  for (int e = 0; e < m; e++) { inc[E[e].first] |= 1ULL << e; inc[E[e].second] |= 1ULL << e; }
  return true;
}
static inline int dg(u64 mask, int v) { return __builtin_popcountll(mask & inc[v]); }
static inline int other(int e, int v) { return E[e].first == v ? E[e].second : E[e].first; }

// ---------- parity decompositions ----------
static unordered_map<u64, char> memo;
static bool PD(u64 mask);
static bool growPD(u64 mask, int c, int start, int vis, u64 path) {
  u64 cand = mask & inc[c] & ~path;
  while (cand) {
    int e = __builtin_ctzll(cand); cand &= cand - 1;
    int z = other(e, c);
    if (vis >> z & 1) continue;
    u64 np = path | (1ULL << e);
    if ((dg(mask, z) & 1) && PD(mask & ~np)) return true;
    if (growPD(mask, z, start, vis | (1 << z), np)) return true;
  }
  return false;
}
// Lovasz's theorem: if every component of the graph has at most one vertex of positive even
// degree, a parity decomposition exists.  Used only to cut the search short.
static bool lovaszShortcut(u64 mask) {
  int comp[20]; for (int v = 0; v < n; v++) comp[v] = -1;
  int nc = 0, evens[20] = {0};
  for (int s = 0; s < n; s++) {
    if (comp[s] >= 0 || !(mask & inc[s])) continue;
    vector<int> st = {s}; comp[s] = nc;
    while (!st.empty()) {
      int v = st.back(); st.pop_back();
      int d = dg(mask, v);
      if (d > 0 && d % 2 == 0) evens[nc]++;
      u64 c = mask & inc[v];
      while (c) { int e = __builtin_ctzll(c); c &= c - 1; int z = other(e, v); if (comp[z] < 0) { comp[z] = nc; st.push_back(z); } }
    }
    if (evens[nc] > 1) return false;
    nc++;
  }
  return true;
}
static bool PD(u64 mask) {
  if (!mask) return true;
  auto it = memo.find(mask);
  if (it != memo.end()) return it->second;
  if (lovaszShortcut(mask)) { memo[mask] = 1; return true; }
  // necessary conditions: with P = (#odd)/2 paths, a vertex lies on at most P of them, so
  // d(v) <= 2P - (d(v) mod 2); and every component with an edge contains an odd vertex.
  int nodd = 0, w = -1, wd = 99;
  for (int v = 0; v < n; v++) { int d = dg(mask, v); if (d & 1) { nodd++; if (d < wd) { wd = d; w = v; } } }
  int P = nodd / 2;
  bool r = false;
  bool ok = nodd > 0;
  for (int v = 0; ok && v < n; v++) { int d = dg(mask, v); if (d > 2 * P - (d & 1)) ok = false; }
  if (ok) {
    int seen = 0;
    for (int s = 0; ok && s < n; s++) {
      if ((seen >> s & 1) || !(mask & inc[s])) continue;
      int comp = 1 << s, fr = comp; bool hasOdd = false;
      while (fr) { int v = __builtin_ctz(fr); fr &= fr - 1; if (dg(mask, v) & 1) hasOdd = true;
        u64 c = mask & inc[v]; while (c) { int e = __builtin_ctzll(c); c &= c - 1; int z = other(e, v); if (!(comp >> z & 1)) { comp |= 1 << z; fr |= 1 << z; } } }
      seen |= comp; if (!hasOdd) ok = false;
    }
  }
  if (ok) r = growPD(mask, w, w, 1 << w, 0);   // the path ending at the odd vertex w of least degree
  memo[mask] = r;
  return r;
}
// good(mask, y, x): some path from y to an odd z avoiding x, rest PD
static bool growQ(u64 mask, int c, int x, int vis, u64 path) {
  u64 cand = mask & inc[c] & ~path;
  while (cand) {
    int e = __builtin_ctzll(cand); cand &= cand - 1;
    int z = other(e, c);
    if (z == x || (vis >> z & 1)) continue;
    u64 np = path | (1ULL << e);
    if ((dg(mask, z) & 1) && PD(mask & ~np)) return true;
    if (growQ(mask, z, x, vis | (1 << z), np)) return true;
  }
  return false;
}
static bool good(u64 mask, int y, int x) { return growQ(mask, y, x, 1 << y, 0); }

// ---------- schedules ----------
static int L, Xv, Yv;
static vector<pair<int, int>> EP;   // edges of G+
static u64 incP[20];
static int adjP(u64 mask, int a, int b) {
  for (int e = 0; e < (int)EP.size(); e++)
    if ((mask >> e & 1) && ((EP[e].first == a && EP[e].second == b) || (EP[e].first == b && EP[e].second == a))) return 1;
  return 0;
}
// mode 0: both tokens; mode 1: y-token only; mode 2: both tokens, first move by the y-token
static bool schedule(int g, int y, int x, int mode) {
  L = n; Xv = x; Yv = y;
  EP = E; EP.push_back({y, L});
  for (int v = 0; v < 20; v++) incP[v] = 0;
  for (int e = 0; e < (int)EP.size(); e++) { incP[EP[e].first] |= 1ULL << e; incP[EP[e].second] |= 1ULL << e; }
  u64 full = (EP.size() == 64) ? ~0ULL : ((1ULL << EP.size()) - 1);
  auto key = [](u64 mask, int a, int b) { return mask | ((u64)a << 40) | ((u64)b << 48); };
  unordered_set<u64> seen;
  deque<tuple<u64, int, int, int>> dq;   // mask, pos g-token, pos y-token, depth
  dq.push_back({full, g, y, 0});
  seen.insert(key(full, g, y));
  while (!dq.empty()) {
    auto [mask, a, b, d] = dq.front(); dq.pop_front();
    for (int t = 0; t < 2; t++) {
      if (mode == 1 && t == 0) continue;
      if (mode == 2 && d == 0 && t == 0) continue;
      int p = t == 0 ? a : b, o = t == 0 ? b : a;
      u64 cand = mask & incP[p];
      while (cand) {
        int e = __builtin_ctzll(cand); cand &= cand - 1;
        int q = EP[e].first == p ? EP[e].second : EP[e].first;
        if (q == Xv || q == L || q == o) continue;
        u64 nm = mask & ~(1ULL << e);
        if (adjP(nm, q, o)) continue;
        if (__builtin_popcountll(nm & incP[q]) == 0) return true;   // retires
        int na = t == 0 ? q : a, nb = t == 0 ? b : q;
        u64 k = key(nm, na, nb);
        if (seen.insert(k).second) dq.push_back({nm, na, nb, d + 1});
      }
    }
  }
  return false;
}

int main(int argc, char** argv) {
  bool full = argc > 1 && !strcmp(argv[1], "full");
  string line;
  long long graphs = 0;
  long long Ninst = 0, Nsch = 0, NschY = 0, Ntight = 0, NtightSch = 0, NschNoFirstY = 0;
  long long coreTests = 0, coreTestsSch = 0, coreTriples = 0, coreTriplesSch = 0, unschStuck = 0, schStuck = 0;
  long long tests[2] = {0, 0}, core[2] = {0, 0}, ex[5] = {0, 0, 0, 0, 0};
  map<int, long long> byd[2];
  while (getline(cin, line)) {
    while (!line.empty() && (line.back() == '\r' || line.back() == '\n')) line.pop_back();
    if (!parse(line)) continue;
    int deg[20];
    for (int v = 0; v < n; v++) { deg[v] = 0; for (int w = 0; w < n; w++) deg[v] += A[v][w]; }
    int ne = 0, g = -1;
    for (int v = 0; v < n; v++) if (deg[v] > 0 && deg[v] % 2 == 0) { ne++; g = v; }
    if (ne != 1) continue;
    graphs++;
    memo.clear();
    u64 all = (m == 64) ? ~0ULL : ((1ULL << m) - 1);
    for (int y = 0; y < n; y++) {
      if (deg[y] % 2 == 0) continue;
      for (int x = 0; x < n; x++) {
        if (x == y || deg[x] % 2 == 0 || A[x][y]) continue;
        bool isN = false;
        for (int w = 0; w < n; w++) if (A[y][w] && w != g && !A[x][w]) isN = true;
        bool tight = true;
        for (int v = 0; v < n; v++) if (A[g][v] && v != x && v != y && !A[y][v]) tight = false;
        bool cn = false;
        for (int c = 0; c < n; c++) if (A[y][c] && A[c][x]) cn = true;
        bool indep = false;
        if (deg[g] == 2) {
          int a = -1, b = -1;
          for (int v = 0; v < n; v++) if (A[g][v]) { if (a < 0) a = v; else b = v; }
          indep = !A[a][b];
        }
        // TRN tests of the triple
        int nCore = 0;
        for (int u = 0; u < n; u++) {
          if (u == x || !A[g][u] || !A[y][u]) continue;
          bool wit = false;
          for (int w = 0; w < n; w++) if (A[y][w] && w != u && !A[x][w]) wit = true;
          bool candCore = isN && tight && wit && cn && !indep;
          if (!full && !candCore) continue;
          u64 K = all & ~(1ULL << [&] { for (int e = 0; e < m; e++) if ((E[e].first == g && E[e].second == u) || (E[e].first == u && E[e].second == g)) return e; return -1; }());
          if (!good(K, y, x)) continue;
          int a = A[g][y];
          tests[a]++;
          if (!tight) { ex[0]++; continue; }
          if (!wit) { ex[1]++; continue; }
          if (!cn) { ex[2]++; continue; }
          if (indep) { ex[3]++; continue; }
          if (!isN) { ex[4]++; continue; }
          core[a]++; byd[a][deg[g]]++; nCore++;
        }
        if (!isN) continue;
        Ninst++;
        static bool skipS = getenv("SKIPSCHED") != nullptr;
        if (skipS) { printf("T %s %d %d %d %d %d - - - %d\n", line.c_str(), g, y, x, (int)isN, (int)tight, nCore); continue; }
        bool s = schedule(g, y, x, 0);
        bool sY = schedule(g, y, x, 1);
        bool sF = s ? schedule(g, y, x, 2) : false;
        Nsch += s; NschY += sY; if (s && !sF) NschNoFirstY++;
        if (tight) { Ntight++; NtightSch += s; }
        if (nCore) {
          coreTriples++; coreTriplesSch += s; coreTests += nCore; if (s) coreTestsSch += nCore;
          bool stuck = true;
          for (int q = 0; q < n; q++) if (A[y][q] && q != g && !A[g][q]) stuck = false;
          if (s) schStuck += stuck; else unschStuck += stuck;
        }
        printf("T %s %d %d %d %d %d %d %d %d %d\n", line.c_str(), g, y, x, (int)isN, (int)tight, (int)s, (int)sY, (int)sF, nCore);
      }
    }
  }
  printf("SUMMARY graphs %lld\n", graphs);
  printf("SUMMARY instances of N %lld: schedule %lld, move (T) %lld, schedule but none starting with the y-token %lld\n", Ninst, Nsch, NschY, NschNoFirstY);
  printf("SUMMARY all-tight instances of N %lld: schedule %lld\n", Ntight, NtightSch);
  printf("SUMMARY core tests %lld: schedule %lld; core triples %lld: schedule %lld; N(y) in N[g]: unscheduled %lld, scheduled %lld\n",
         coreTests, coreTestsSch, coreTriples, coreTriplesSch, unschStuck, schStuck);
  if (full) {
    printf("SUMMARY TRN tests y!~g %lld y~g %lld; core y!~g %lld y~g %lld; excluded (C2) %lld (C3) %lld (C4) %lld (C5) %lld (C0) %lld\n",
           tests[0], tests[1], core[0], core[1], ex[0], ex[1], ex[2], ex[3], ex[4]);
    for (int a = 0; a < 2; a++) {
      printf("SUMMARY core %s by d(g):", a ? "y~g" : "y!~g");
      for (auto& kv : byd[a]) printf(" %d:%lld", kv.first, kv.second);
      printf("\n");
    }
  }
}
