// t_rec.cpp: an independent implementation of the certificate class Rec of Definition 3.2 (own move
// generator from the text of Theorem 3.1, with c notin A enforced as F1 requires; no authors' code).
// Moves: (a)-(i) as stated (route move (h) over ALL simple g--c paths with interior outside A).
// Options (letters in argv[1]):
//   T  add the move (t) of Rec_T (tight x, A cap N[c] empty, x notin A, c notin N(g));
//   C  allow (b), (c) also when c in N(g) (as moves.h does);
//   S  restrict (h) to at most 8 shortest g--c paths in G - A, and to c notin N(g) (as moves.h does);
//   D  moves (a)-(d) only (no (e)-(i));
//   E  drop the split (e) only;
//   X  every admissible A (nonempty subsets of Amax) instead of Amax only.
// Base cases: no even vertex, d(c) = 1, neighbour not in A; A misses the component of c.
#include "a25.h"
#include <iostream>
#include <unordered_map>
using namespace a25;
static bool OT, OC, OS, OD, OE;
static std::unordered_map<std::string, char> memo;
static void compact(const Graph& G, int c, uint32_t A, Graph& H, int& c2, uint32_t& A2) {
  uint32_t S = G.component(c); int mp[MV]; int k = 0;
  for (int v = 0; v < G.n; v++) mp[v] = (S >> v & 1u) ? k++ : -1;
  H = Graph(); H.n = k;
  for (int v = 0; v < G.n; v++) if (mp[v] >= 0) for (int w = v + 1; w < G.n; w++) if (mp[w] >= 0 && G.has(v, w)) H.add(mp[v], mp[w]);
  c2 = mp[c]; A2 = 0; for (int v = 0; v < G.n; v++) if ((A >> v & 1u) && mp[v] >= 0) A2 |= 1u << mp[v];
}
static bool rec(const Graph& G0, int c0, uint32_t A0);
static bool tryc(const Graph& H, int c, uint32_t A) { return rec(H, c, A); }
static bool rec(const Graph& G0, int c0, uint32_t A0) {
  Graph G; int c; uint32_t A; compact(G0, c0, A0, G, c, A);
  if (A >> c & 1u) return false;
  std::string key((const char*)G.adj, 4 * G.n); key.push_back((char)G.n); key.push_back((char)c); key.append((const char*)&A, 4);
  auto it = memo.find(key); if (it != memo.end()) return it->second;
  memo[key] = 0;
  int n = G.n; int g = theeven(G);
  bool r = false;
  // base cases
  if (g < 0 && G.deg(c) == 1 && !(A & G.adj[c])) r = true;
  if (!(A & G.component(c))) r = true;
  auto done = [&](bool x) { if (x) r = true; return r; };
  if (!r && !OD) {  // (i)
    uint32_t C = 1u << c; bool ch = true;
    while (ch) { ch = false; for (int x = 0; x < n; x++) if ((C >> x & 1u) && (G.adj[x] & ~A & ~C)) { C |= G.adj[x] & ~A; ch = true; } }
    uint32_t bd = 0; for (int x = 0; x < n; x++) if (!(C >> x & 1u) && (G.adj[x] & C)) bd |= 1u << x;
    if (bd != A) done(tryc(G, c, bd));
  }
  if (!r && !OD && G.deg(c) == 3) {  // (g)
    int ys[3], t = 0; for (int y = 0; y < n; y++) if (G.has(c, y)) ys[t++] = y;
    for (int i = 0; i < 3 && !r; i++) for (int j = 0; j < 3 && !r; j++) if (i != j && !G.has(ys[i], ys[j])) { Graph H = G; H.rem(c, ys[i]); H.rem(c, ys[j]); H.add(ys[i], ys[j]); done(tryc(H, c, A | (1u << ys[i]))); }
  }
  if (!r && g < 0 && G.deg(c) >= 3) {  // (d)
    for (int y = 0; y < n && !r; y++) if (G.has(c, y) && !(A >> y & 1u)) { Graph H = G; int l = H.n++; H.adj[l] = 0; H.rem(c, y); H.add(y, l); done(tryc(H, l, A | (1u << c))); }
  }
  if (!r && g >= 0) {
    if (G.has(g, c)) { Graph H = G; H.rem(g, c); done(tryc(H, g, A | (1u << c))); }  // (a)
    for (int x = 0; x < n && !r; x++) if (G.has(g, x) && x != c && !(A >> x & 1u) && (OC || !G.has(g, c))) {
      Graph H = G; H.rem(g, x);
      if (!G.has(c, x)) done(tryc(H, c, A));                                              // (b)
      else { Graph K = H; K.rem(x, c); done(tryc(K, x, A | (1u << c)));                    // (c)
        if (!r && OT && !(A & closedN(G, c)) && !G.has(g, c)) done(tryc(H, c, A)); }       // (t)
    }
    if (!r && !OD && G.deg(g) == 2) {
      int u = __builtin_ctz(G.adj[g]), v = 31 - __builtin_clz(G.adj[g]);
      if (!G.has(u, v)) { if (OE) goto noe; { Graph H = G; H.rem(g, u); H.rem(g, v); H.add(u, v);            // (e)
        if (!(A >> g & 1u)) done(tryc(H, c, A)); else for (int w : {u, v}) if (!r && w != c) done(tryc(H, c, (A & ~(1u << g)) | (1u << w))); } noe:; }
      else if ((A >> g & 1u) && !G.has(g, c)) done(tryc(G, c, A & ~(1u << g)));           // (f)
    }
    if (!r && !OD && !(A >> g & 1u) && !(OS && G.has(g, c))) {                             // (h)
      std::vector<std::vector<int>> paths;
      if (OS) {
        int dist[MV]; for (int x = 0; x < n; x++) dist[x] = -1; int q[MV], qh = 0, qt = 0; dist[c] = 0; q[qt++] = c;
        while (qh < qt) { int x = q[qh++]; for (int y = 0; y < n; y++) if (G.has(x, y) && dist[y] < 0 && !(A >> y & 1u)) { dist[y] = dist[x] + 1; q[qt++] = y; } }
        if (dist[g] >= 2) { std::vector<int> P{g}; std::function<void(int)> go = [&](int x) { if (paths.size() >= 8) return; if (x == c) { paths.push_back(P); return; }
            for (int y = 0; y < n; y++) if (G.has(x, y) && dist[y] == dist[x] - 1) { P.push_back(y); go(y); P.pop_back(); } }; go(g); }
      } else {
        std::vector<int> P{g}; uint32_t vis = 1u << g;
        std::function<void(int)> go = [&](int x) { for (int y = 0; y < n; y++) if (G.has(x, y) && !(vis >> y & 1u)) {
            if (y == c) { if (P.size() >= 2) { auto R = P; R.push_back(c); paths.push_back(R); } continue; }
            if (A >> y & 1u) continue; vis |= 1u << y; P.push_back(y); go(y); P.pop_back(); vis &= ~(1u << y); } };
        go(g);
      }
      for (auto& R : paths) { if (r) break; Graph H = G; uint32_t B = A; for (size_t i = 0; i + 1 < R.size(); i++) H.rem(R[i], R[i + 1]); for (size_t i = 1; i < R.size(); i++) B |= 1u << R[i]; done(tryc(H, g, B)); }
    }
  }
  memo[key] = r; return r;
}
int main(int argc, char** argv) {
  const char* f = argc > 1 ? argv[1] : ""; OT = strchr(f, 'T'); OC = strchr(f, 'C'); OS = strchr(f, 'S'); OD = strchr(f, 'D'); OE = strchr(f, 'E'); bool X = strchr(f, 'X');
  long long inst = 0, no = 0, nob = 0; std::string line;
  while (std::getline(std::cin, line)) {
    Graph G; if (!decode_g6(line, G)) continue; if (__builtin_popcount(G.evenset()) > 1) continue;
    if (memo.size() > 4000000) memo.clear();
    for (int c = 0; c < G.n; c++) { if (G.deg(c) % 2 == 0) continue; uint32_t Am = amax(G, c);
      for (uint32_t A = Am;; A = (A - 1) & Am) {
        if (X ? A != 0 : A == Am) { inst++; bool b = blocked(G, c, A);
          if (!rec(G, c, A)) { no++; nob += b; if (getenv("PRINT")) printf("NOREC %s c=%d A=%s blocked=%d\n", line.c_str(), c, sstr(A).c_str(), (int)b); } }
        if (!A) break; } }
  }
  printf("SUMMARY flags=%s instances=%lld notRec=%lld notRec_blocked=%lld\n", f, inst, no, nob);
}
