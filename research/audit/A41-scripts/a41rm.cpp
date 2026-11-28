// a41rm.cpp -- independent root-move closure for audit A41 (nodata Theorem 4.2, Corollary 4.3).
// Written from the manuscript's statement of M1, M2; shares no code with rootmove2.py / rm.c.
//   state (J', rho), z fixed, T' = N_{J'}(z):
//   M1: |N(rho) cap T'| <= 1; for each w in N(rho) - T' - z: J'' = J' - rho w - z rho + z w, root w
//   M2: N(rho) cap T' = {u, v}, u != v; for each choice of u: J'' = J' - rho u - z rho - z u, root v
// Breadth-first to depth <= D (default 6), exact visited set (full adjacency + root), no cap.
// Each state is also checked: z is the only even vertex of J'' (the parity claim of Thm 4.2),
// J'' - z = (J' - z) minus the one edge, and N(z) changes as stated.
// Input: lines "ND g6 z r ..." (nd.c format) or "T1 g6 z r ..." (a41 format); the tier is read
// from the nd.c field when present.  Output: one line per root and a summary.
#include <bits/stdc++.h>
using namespace std;
typedef unsigned int u32;
static int N;
static bool read_g6(const string &s, vector<u32> &A) {
  N = (unsigned char)s[0] - 63; A.assign(N, 0);
  int k = 1, bit = 0, cur = 0;
  for (int j = 1; j < N; j++) for (int i = 0; i < j; i++) {
    if (bit == 0) { cur = (unsigned char)s[k++] - 63; bit = 6; }
    bit--;
    if (cur >> bit & 1) { A[i] |= 1u << j; A[j] |= 1u << i; }
  }
  return true;
}
static bool pm(const vector<u32> &A, u32 S) {
  if (!S) return true;
  int a = __builtin_ctz(S); u32 S2 = S & ~(1u << a);
  for (u32 nb = A[a] & S2; nb; nb &= nb - 1) { int b = __builtin_ctz(nb); if (pm(A, S2 & ~(1u << b))) return true; }
  return false;
}
static int Z;
static void check_parity(const vector<u32> &A) {
  for (int v = 0; v < N; v++) { bool even = !(__builtin_popcount(A[v]) & 1); if (even != (v == Z)) { fprintf(stderr, "parity claim fails\n"); exit(7); } }
}
int main(int argc, char **argv) {
  int D = argc > 1 ? atoi(argv[1]) : 6;
  string line;
  map<string, long long> st;
  while (getline(cin, line)) {
    istringstream is(line); string tag, g; int z, r;
    if (!(is >> tag >> g >> z >> r)) continue;
    if (tag != "ND" && tag != "T1") continue;
    int tier = -1, twins = -1;
    if (tag == "ND") {
      // nd.c: z r dz nu def |D| |A| |C| ncomp rclass twinR twinO tri level excess
      vector<string> f; string x; while (is >> x && x != "|") f.push_back(x);
      tier = stoi(f[11]); twins = (f[8] == "1" || f[9] == "1");
    } else {
      // a41 formats: key value pairs (tier, twins, twinR, twinO)
      string k, v; int tR = -1, tO = -1;
      while (is >> k >> v) {
        if (k == "tier") tier = stoi(v);
        if (k == "twins") twins = stoi(v);
        if (k == "twinR") tR = stoi(v);
        if (k == "twinO") tO = stoi(v);
      }
      if (tR >= 0 && tO >= 0) twins = (tR || tO);
    }
    vector<u32> A0; read_g6(g, A0); Z = z;
    check_parity(A0);
    // BFS
    set<pair<vector<u32>, int>> seen;
    deque<tuple<vector<u32>, int, int, string>> q;
    q.push_back({A0, r, 0, ""}); seen.insert({A0, r});
    string found = "";
    bool single_M1 = false;
    while (!q.empty() && found.empty()) {
      auto [A, rho, d, hist] = q.front(); q.pop_front();
      if (d > 0 && pm(A, A[z])) { found = hist; break; }
      if (d >= D) continue;
      u32 T = A[z];
      if (!(T >> rho & 1)) { fprintf(stderr, "root not in N(z)\n"); exit(8); }
      u32 tn = A[rho] & T;
      vector<tuple<vector<u32>, int, string>> nxt;
      if (__builtin_popcount(tn) <= 1) {
        for (u32 ws = A[rho] & ~T & ~(1u << z); ws; ws &= ws - 1) {
          int w = __builtin_ctz(ws);
          vector<u32> B = A;
          B[rho] &= ~(1u << w); B[w] &= ~(1u << rho);
          B[z] &= ~(1u << rho); B[rho] &= ~(1u << z);
          B[z] |= 1u << w; B[w] |= 1u << z;
          check_parity(B);
          if (B[z] != ((T & ~(1u << rho)) | (1u << w))) { fprintf(stderr, "N(z) claim M1\n"); exit(9); }
          nxt.push_back({B, w, "M1"});
        }
      }
      if (__builtin_popcount(tn) == 2) {
        int a = __builtin_ctz(tn), b = 31 - __builtin_clz(tn);
        for (int k = 0; k < 2; k++) {
          int u = k ? b : a, v = k ? a : b;
          vector<u32> B = A;
          B[rho] &= ~(1u << u); B[u] &= ~(1u << rho);
          B[z] &= ~(1u << rho); B[rho] &= ~(1u << z);
          B[z] &= ~(1u << u); B[u] &= ~(1u << z);
          check_parity(B);
          if (B[z] != (T & ~(1u << rho) & ~(1u << u))) { fprintf(stderr, "N(z) claim M2\n"); exit(9); }
          nxt.push_back({B, v, "M2"});
        }
      }
      for (auto &[B, w, nm] : nxt) {
        if (d == 0 && nm == "M1" && pm(B, B[z])) single_M1 = true;
        if (seen.insert({B, w}).second) q.push_back({B, w, d + 1, hist + nm});
      }
    }
    bool reached = !found.empty();
    printf("RM %s %d %d tier %d twins %d reached %d single_M1 %d path %s states %zu\n", g.c_str(), z, r, tier, twins, reached, single_M1, reached ? found.c_str() : "-", seen.size());
    st["total"]++; if (reached) st["reached"]++; if (single_M1) st["single_M1"]++;
    st["tier" + to_string(tier) + (reached ? "_reached" : "_not")]++;
    st["tier" + to_string(tier) + "_twins" + to_string(twins) + (reached ? "_reached" : "_not")]++;
  }
  for (auto &kv : st) fprintf(stderr, "%s=%lld\n", kv.first.c_str(), kv.second);
}
