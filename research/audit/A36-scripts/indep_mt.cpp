// indep_mt.cpp -- A36 auditor.  An independent k-token schedule search for multi-token.tex.
// Shares no code with mtok.cpp / mt_verify.py.  Implements Definition 2.2 literally:
//   tokens tau(K) = vertices of positive even degree; a tail i = (c_i, s_i, x_i) is live iff c_i s_i in K;
//   X(K) = union of {c_i, x_i} over live tails.
//   (M) token p, edge pu, u odd, u not in X(K), no neighbour of u in K - pu is a token other than p.
//   (D) live tail i with s_i odd: K - c_i s_i.
//   (S) token p with N(p) = {a, b}, a !~ b, neither a nor b the leaf of ANY tail (live or dead),
//       {a, b} != {x_i, s_i} for every live tail: K - pa - pb + ab.
//   end: |tau| <= 1 and #live <= 1   (TERM=1: |tau| <= 1 only).
// Exhaustive DFS over the reachable states with an EXACT visited set (the full edge set is the key;
// no hashing shortcut).  Every move lowers |E| by one, so the state graph is acyclic and marking a
// state visited on entry is sound.  For an instance with no schedule all reachable states are
// visited, and the least potential Phi = |tau| + #live over them is reported.
//
// usage: indep_mt MODE CAP < lines "g6 [r1,r2,..]"
//   MODE g6 | resid (resid: g6 of B = J - z, z new vertex joined to 0..5)
//   CAP: max visited states per instance (0 = none); hitting it makes the instance undecided.
// env: SUPP=0/1 (default 1), DROP=0/1 (default 1), TERM=0/1 (default 0), PRINT=0/1/2
//   (1: one SCHED line per scheduled root; 2: one per scheduled instance), STOPDATA=1: stop the
//   orientations of a data choice once one is scheduled (root verdicts only).
// Output: per root "R g6 r deg nonnbrs verdict data datasched inst instsched minphi" and a summary.
#include <bits/stdc++.h>
using namespace std;
typedef uint64_t u64;
static const int MAXN = 30;

static int N, KT;                 // vertices of M+, number of tails
static int Cc[8], Ss[8], Xx[8];   // tails
static u64 A[MAXN];
static int SUPP = 1, DROP = 1, TERM = 0;
static long long CAP = 0, visitedCount = 0;
static bool capHit = false;
static int minPhi;
static u64 allLeaves;

static const int KW = 4;   // 256 bits: enough for N <= 23 vertices (N(N-1)/2 <= 253)
struct Key { u64 w[KW]; bool operator==(const Key& o) const { for (int i = 0; i < KW; i++) if (w[i] != o.w[i]) return false; return true; } };
struct KH { size_t operator()(const Key& k) const { u64 h = 0x12345; for (int i = 0; i < KW; i++) { h ^= k.w[i] + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2); } return h; } };
static unordered_set<Key, KH> visited;

static Key enc() {  // exact: upper-triangular adjacency bits
  Key k; memset(k.w, 0, sizeof k.w);
  int pos = 0;
  for (int i = 0; i + 1 < N; i++) {          // row i, columns i+1..N-1, packed (exact, injective)
    int len = N - i - 1;
    u64 bits = (A[i] >> (i + 1)) & (len >= 64 ? ~0ULL : ((1ULL << len) - 1));
    int w = pos >> 6, o = pos & 63;
    k.w[w] |= bits << o;
    if (o && o + len > 64) k.w[w + 1] |= bits >> (64 - o);
    pos += len;
  }
  return k;
}
static inline int dg(int v) { return __builtin_popcountll(A[v]); }
static inline void delE(int a, int b) { A[a] &= ~(1ULL << b); A[b] &= ~(1ULL << a); }
static inline void addE(int a, int b) { A[a] |= 1ULL << b; A[b] |= 1ULL << a; }

struct Mv { char t; int p, q, r; };
static vector<Mv> path, found;

static bool dfs() {
  u64 tok = 0;
  for (int v = 0; v < N; v++) { int d = dg(v); if (d > 0 && d % 2 == 0) tok |= 1ULL << v; }
  int nlive = 0; u64 X = 0; bool live[8];
  for (int i = 0; i < KT; i++) { live[i] = A[Cc[i]] >> Ss[i] & 1; if (live[i]) { nlive++; X |= (1ULL << Cc[i]) | (1ULL << Xx[i]); } }
  int ntok = __builtin_popcountll(tok);
  minPhi = min(minPhi, ntok + nlive);
  if (ntok <= 1 && (TERM == 1 || nlive <= 1)) { found = path; return true; }
  if (ntok <= 1 && TERM == 2) {   // sparse family (separation_sparse): every vertex has <= 1 neighbour in X
    bool sp = true;
    for (int v = 0; v < N; v++) if (__builtin_popcountll(A[v] & X) > 1) sp = false;
    if (sp) { found = path; return true; }
  }
  Key key = enc();
  if (visited.count(key)) return false;
  if (CAP && (long long)visited.size() >= CAP) { capHit = true; return false; }
  visited.insert(key);
  // (M)
  for (int p = 0; p < N; p++) if (tok >> p & 1) {
    u64 nb = A[p];
    for (int u = 0; u < N; u++) if (nb >> u & 1) {
      if (dg(u) % 2 == 0) continue;           // u odd
      if (X >> u & 1) continue;               // u not in X(K)
      u64 nu = A[u] & ~(1ULL << p);           // neighbours of u in K - pu
      if (nu & tok & ~(1ULL << p)) continue;  // no other token among them
      delE(p, u); path.push_back({'M', p, u, 0});
      bool ok = dfs();
      path.pop_back(); addE(p, u);
      if (ok) return true;
      if (capHit) return false;
    }
  }
  // (D)
  if (DROP) for (int i = 0; i < KT; i++) if (live[i] && dg(Ss[i]) % 2 == 1) {
    delE(Cc[i], Ss[i]); path.push_back({'D', i, 0, 0});
    bool ok = dfs();
    path.pop_back(); addE(Cc[i], Ss[i]);
    if (ok) return true;
    if (capHit) return false;
  }
  // (S)
  if (SUPP) for (int p = 0; p < N; p++) if ((tok >> p & 1) && dg(p) == 2) {
    int a = -1, b = -1;
    for (int v = 0; v < N; v++) if (A[p] >> v & 1) { if (a < 0) a = v; else b = v; }
    if (A[a] >> b & 1) continue;
    if ((allLeaves >> a & 1) || (allLeaves >> b & 1)) continue;
    bool bad = false;
    for (int i = 0; i < KT; i++) if (live[i]) {
      if ((a == Xx[i] && b == Ss[i]) || (a == Ss[i] && b == Xx[i])) bad = true;
    }
    if (bad) continue;
    delE(p, a); delE(p, b); addE(a, b); path.push_back({'S', p, a, b});
    bool ok = dfs();
    path.pop_back(); delE(a, b); addE(p, a); addE(p, b);
    if (ok) return true;
    if (capHit) return false;
  }
  return false;
}

static bool g6parse(const string& s, int& n, vector<u64>& J) {
  if (s.empty()) return false;
  int c0 = (unsigned char)s[0];
  if (c0 < 63 || c0 > 126) return false;
  n = c0 - 63;
  J.assign(n + 1, 0);
  size_t idx = 1; int have = 0, cur = 0;
  for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
    if (have == 0) { if (idx >= s.size()) return false; cur = (unsigned char)s[idx++] - 63; have = 6; }
    have--;
    if ((cur >> have) & 1) { J[i] |= 1ULL << j; J[j] |= 1ULL << i; }
  }
  return true;
}

static void pmatch(vector<int> vs, const vector<u64>& J, vector<pair<int,int>>& cur, vector<vector<pair<int,int>>>& out) {
  if (vs.empty()) { out.push_back(cur); return; }
  int a = vs.back(); vs.pop_back();   // different recursion order from mtok (last vertex first)
  for (size_t j = 0; j < vs.size(); j++) {
    int b = vs[j];
    if (!(J[a] >> b & 1)) continue;
    vector<int> rest; for (size_t t = 0; t < vs.size(); t++) if (t != j) rest.push_back(vs[t]);
    cur.push_back({min(a, b), max(a, b)}); pmatch(rest, J, cur, out); cur.pop_back();
  }
}

int main(int argc, char** argv) {
  string mode = argc > 1 ? argv[1] : "g6";
  CAP = argc > 2 ? atoll(argv[2]) : 0;
  if (getenv("SUPP")) SUPP = atoi(getenv("SUPP"));
  if (getenv("DROP")) DROP = atoi(getenv("DROP"));
  if (getenv("TERM")) TERM = atoi(getenv("TERM"));
  int PRINT = getenv("PRINT") ? atoi(getenv("PRINT")) : 0;
  int STOPDATA = getenv("STOPDATA") ? atoi(getenv("STOPDATA")) : 0;
  long long roots = 0, rsched = 0, rund = 0, datas = 0, dsched = 0, insts = 0, isched = 0, iund = 0;
  string line;
  while (getline(cin, line)) {
    stringstream ss(line); string g6, rl; ss >> g6; if (g6.empty()) continue; ss >> rl;
    set<int> rset; if (!rl.empty()) { stringstream rs(rl); string t; while (getline(rs, t, ',')) rset.insert(stoi(t)); }
    int n; vector<u64> J;
    if (!g6parse(g6, n, J)) { fprintf(stderr, "bad g6 %s\n", g6.c_str()); continue; }
    int z = -1;
    if (mode == "resid") { z = n; J.resize(n + 1); J[z] = 0; for (int u = 0; u < 6; u++) { J[z] |= 1ULL << u; J[u] |= 1ULL << z; } n++; }
    vector<int> ev; for (int v = 0; v < n; v++) if (__builtin_popcountll(J[v]) % 2 == 0) ev.push_back(v);
    if (ev.size() != 1) { fprintf(stderr, "skip %s: %zu even\n", g6.c_str(), ev.size()); continue; }
    if (z < 0) z = ev[0];
    if (z != ev[0]) { fprintf(stderr, "skip %s: z not even\n", g6.c_str()); continue; }
    int dz = __builtin_popcountll(J[z]);
    if (dz < 4 || dz % 2) continue;
    int k = dz / 2 - 1;
    vector<int> Nz; for (int v = 0; v < n; v++) if (J[z] >> v & 1) Nz.push_back(v);
    for (int r : Nz) {
      if (!rset.empty() && !rset.count(r)) continue;
      int dr = __builtin_popcountll(J[r]);
      if (dr < 3) continue;
      int nonnb = 0; for (int v = 0; v < n; v++) if (v != r && !(J[r] >> v & 1)) nonnb++;
      int rdata = 0, rdsched = 0, rinst = 0, risched = 0; bool rund_ = false; int rminphi = 99;
      bool printed = false;
      for (int w : Nz) if (w != r) {
        vector<int> rest; for (int u : Nz) if (u != r && u != w) rest.push_back(u);
        vector<vector<pair<int,int>>> pms; vector<pair<int,int>> cur;
        pmatch(rest, J, cur, pms);
        for (auto& pm : pms) {
          rdata++;
          bool ds = false;
          for (int o = 0; o < (1 << k); o++) {
            if (STOPDATA && ds) break;
            // M+ : vertices 0..n-1 of J, leaf of pair i is n+i
            N = n + k; KT = k; allLeaves = 0;
            if (N * (N - 1) / 2 > 64 * KW) { fprintf(stderr, "too many vertices\n"); return 1; }
            for (int v = 0; v < N; v++) A[v] = v < n ? J[v] : 0;
            delE(z, w);
            for (int i = 0; i < k; i++) {
              int a = pm[i].first, b = pm[i].second;
              delE(z, a); delE(z, b); delE(a, b);
              int y = (o >> i & 1) ? b : a, x = (o >> i & 1) ? a : b;
              Ss[i] = y; Xx[i] = x; Cc[i] = n + i; addE(y, n + i); allLeaves |= 1ULL << (n + i);
            }
            visited.clear(); if (CAP) visited.reserve(CAP + 16); capHit = false; minPhi = 99; path.clear(); found.clear();
            bool ok = dfs();
            rinst++;
            if (ok) {
              risched++; ds = true;
              if (PRINT == 2 || (PRINT == 1 && !printed)) {
                printed = true;
                printf("SCHED %s %d %d %d %d", g6.c_str(), mode == "resid" ? 1 : 0, z, r, w);
                for (int i = 0; i < k; i++) printf(" %d,%d", Ss[i], Xx[i]);
                printf(" |");
                for (auto& m : found) {
                  if (m.t == 'M') printf(" M%d-%d", m.p, m.q);
                  else if (m.t == 'D') printf(" D%d", m.p);
                  else printf(" S%d:%d-%d", m.p, m.q, m.r);
                }
                printf("\n");
              }
            } else if (capHit) { rund_ = true; iund++; }
            else rminphi = min(rminphi, minPhi);
          }
          if (ds) rdsched++;
        }
      }
      if (rdata == 0) continue;
      roots++; datas += rdata; dsched += rdsched; insts += rinst; isched += risched;
      int verdict = risched > 0 ? 1 : (rund_ ? 2 : 0);
      if (verdict == 1) rsched++; else if (verdict == 2) rund++;
      printf("R %s %d %d %d %d %d %d %d %d %d\n", g6.c_str(), r, dr, nonnb, verdict, rdata, rdsched, rinst, risched,
             verdict == 0 ? rminphi : -1);
      fflush(stdout);
    }
  }
  printf("TOTAL roots %lld scheduled %lld undecided %lld | data %lld scheduled %lld | instances %lld scheduled %lld undecided %lld\n",
         roots, rsched, rund, datas, dsched, insts, isched, iund);
}
