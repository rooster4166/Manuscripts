// mt_indep.cpp -- A36 auditor: an independent test of Conjecture 6.2 (MT) of multi-token.tex.
// Own exact solver (no route_ext): a parity decomposition of H (b(v) = d(v) mod 2, so every path joins
// two odd vertices) in which no path contains both c_i and x_i.  Backtracking: take the least odd
// vertex with an unused end, enumerate simple paths from it in the remaining edges to another
// unused odd end, subject to the constraint; memoise failed (edge set, used ends); prune when a
// component of the remaining edges has fewer than two unused ends.  The solution found is
// re-checked independently (cover, ends, constraint) before an instance counts as passed.
//
// Instances: H = G + leaves c_i at stems s_i, k tails (c_i, s_i, x_i), G connected (graph6 on stdin),
// (TS) and (TI) of Definition 2.1: x_i != s_j for all i, j; x_i odd in H; x_i !~ s_i; at most one even
// vertex of H.  MODE: 'distinct' (stems distinct, x_i distinct: the class of mt_conj.py) or 'all'
// (stems may coincide, x_i may coincide: everything (TS) allows).  Tails are unordered.
// usage: mt_indep K MODE < graphs.g6     prints instance counts and any failure.
#include <bits/stdc++.h>
using namespace std;
typedef uint64_t u64;
static int NV, NE;
static int eu[64], ev[64];
static int eid[32][32];
static u64 incid[32];
static int deg[32];
static int TK; static int tc[4], tx[4];
static vector<vector<int>> sol, cur;
static unordered_set<u64> fail;   // key: edges mask (<= 40 bits) | used-ends mask << 40 (NV <= 24)

static bool okPath(const vector<int>& P) {
  for (int i = 0; i < TK; i++) {
    bool a = false, b = false;
    for (int v : P) { if (v == tc[i]) a = true; if (v == tx[i]) b = true; }
    if (a && b) return false;
  }
  return true;
}
static bool compOK(u64 E, u64 freeEnds) {   // every component of E has >= 2 free ends
  u64 seenE = 0;
  for (int e = 0; e < NE; e++) if ((E >> e & 1) && !(seenE >> e & 1)) {
    u64 vs = (1ULL << eu[e]) | (1ULL << ev[e]), fr = 0;
    bool grow = true;
    while (grow) { grow = false;
      for (int f = 0; f < NE; f++) if ((E >> f & 1) && !(fr >> f & 1) && ((vs >> eu[f] & 1) || (vs >> ev[f] & 1))) {
        fr |= 1ULL << f; u64 nv = vs | (1ULL << eu[f]) | (1ULL << ev[f]); if (nv != vs) { vs = nv; } grow = true; }
    }
    seenE |= fr;
    if (__builtin_popcountll(vs & freeEnds) < 2) return false;
  }
  return true;
}
static bool solve(u64 E, u64 freeEnds);
static bool grow(int v, u64 E, u64 freeEnds, vector<int>& P, u64 inP) {
  // P ends at v; try to stop at v (if v is a free end other than the start) or extend
  int s = P[0];
  if (P.size() >= 2 && v != s && (freeEnds >> v & 1)) {
    if (okPath(P)) {
      cur.push_back(P);
      if (solve(E, freeEnds & ~(1ULL << v) & ~(1ULL << s))) return true;
      cur.pop_back();
    }
  }
  for (int w = 0; w < NV; w++) {
    int e = eid[v][w]; if (e < 0 || !(E >> e & 1) || (inP >> w & 1)) continue;
    P.push_back(w);
    if (okPath(P) && grow(w, E & ~(1ULL << e), freeEnds, P, inP | (1ULL << w))) return true;
    P.pop_back();
  }
  return false;
}
static bool solve(u64 E, u64 freeEnds) {
  if (!E) { if (!freeEnds) { sol = cur; return true; } return false; }
  if (!freeEnds) return false;
  u64 key = E | (freeEnds << 40);
  if (fail.count(key)) return false;
  if (!compOK(E, freeEnds)) { fail.insert(key); return false; }
  int s = __builtin_ctzll(freeEnds);
  vector<int> P{s};
  if (grow(s, E, freeEnds, P, 1ULL << s)) return true;
  fail.insert(key);
  return false;
}
static bool checkSol() {
  set<int> used; vector<int> ends(NV, 0);
  for (auto& P : sol) {
    set<int> vs(P.begin(), P.end()); if ((int)vs.size() != (int)P.size() || P.size() < 2) return false;
    for (size_t i = 0; i + 1 < P.size(); i++) { int e = eid[P[i]][P[i + 1]]; if (e < 0 || used.count(e)) return false; used.insert(e); }
    ends[P[0]]++; ends[P.back()]++;
    if (!okPath(P)) return false;
  }
  if ((int)used.size() != NE) return false;
  for (int v = 0; v < NV; v++) if (ends[v] != deg[v] % 2) return false;
  return true;
}
int main(int argc, char** argv) {
  int K = atoi(argv[1]); string mode = argv[2];
  long long inst = 0, fails = 0, shared = 0;
  string g6;
  while (cin >> g6) {
    int n = g6[0] - 63; vector<u64> A(n, 0);
    size_t idx = 1; int have = 0, c = 0;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) { if (!have) { c = g6[idx++] - 63; have = 6; } have--; if (c >> have & 1) { A[i] |= 1ULL << j; A[j] |= 1ULL << i; } }
    vector<int> dG(n); for (int v = 0; v < n; v++) dG[v] = __builtin_popcountll(A[v]);
    // stems: nondecreasing tuples (multisets) of length K
    vector<int> st(K, 0);
    function<void(int,int)> recS = [&](int i, int from) {
      if (i == K) {
        if (mode == "distinct") for (int a = 0; a < K; a++) for (int b = a + 1; b < K; b++) if (st[a] == st[b]) return;
        vector<int> dH(n + K); for (int v = 0; v < n; v++) dH[v] = dG[v]; for (int a = 0; a < K; a++) { dH[st[a]]++; dH[n + a] = 1; }
        int nev = 0; for (int v = 0; v < n + K; v++) if (dH[v] > 0 && dH[v] % 2 == 0) nev++;
        if (nev > 1) return;
        u64 stemMask = 0; for (int a = 0; a < K; a++) stemMask |= 1ULL << st[a];
        vector<vector<int>> cand(K);
        for (int a = 0; a < K; a++) for (int x = 0; x < n; x++)
          if (!(stemMask >> x & 1) && dH[x] % 2 == 1 && !(A[st[a]] >> x & 1)) cand[a].push_back(x);
        vector<int> xs(K);
        function<void(int)> recX = [&](int a) {
          if (a == K) {
            // unordered tails: among equal stems require nondecreasing x
            for (int p = 0; p + 1 < K; p++) if (st[p] == st[p + 1] && xs[p] > xs[p + 1]) return;
            bool shr = false;
            for (int p = 0; p < K; p++) for (int q = p + 1; q < K; q++) {
              if (xs[p] == xs[q]) { if (mode == "distinct") return; shr = true; }
              if (st[p] == st[q]) shr = true;
            }
            // build H
            NV = n + K; NE = 0; memset(eid, -1, sizeof eid);
            for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++) if (A[u] >> v & 1) { eu[NE] = u; ev[NE] = v; eid[u][v] = eid[v][u] = NE++; }
            for (int t = 0; t < K; t++) { int cc = n + t; eu[NE] = st[t]; ev[NE] = cc; eid[st[t]][cc] = eid[cc][st[t]] = NE++; tc[t] = cc; tx[t] = xs[t]; }
            TK = K; for (int v = 0; v < NV; v++) deg[v] = dH[v];
            u64 odd = 0; for (int v = 0; v < NV; v++) if (deg[v] % 2) odd |= 1ULL << v;
            fail.clear(); cur.clear(); sol.clear();
            bool ok = solve((NE == 64 ? ~0ULL : ((1ULL << NE) - 1)), odd) && checkSol();
            inst++; if (shr) shared++;
            if (!ok) { fails++; printf("FAIL %s stems", g6.c_str()); for (int t = 0; t < K; t++) printf(" %d", st[t]); printf(" x"); for (int t = 0; t < K; t++) printf(" %d", xs[t]); printf("\n"); }
            return;
          }
          for (int x : cand[a]) { xs[a] = x; recX(a + 1); }
        };
        recX(0);
        return;
      }
      for (int s = from; s < n; s++) { st[i] = s; recS(i + 1, s); }
    };
    recS(0, 0);
  }
  printf("K %d mode %s instances %lld (with a shared stem or avoided vertex %lld) failures %lld\n", K, mode.c_str(), inst, shared, fails);
}
