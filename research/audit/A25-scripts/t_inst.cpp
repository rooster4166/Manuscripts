// t_inst.cpp: independent checks of the explicit instances of the manuscript, with the a25 library
// only (own oracle, own enumerator, own forced chain, own move generator).
//   Prop 4.7   FEhv?  g=4 c=6 A={3,5} and {3,4,5}
//   Ex 4.3     FCZ~o  g=4 c=0 x=6 A={1,2,3,4}
//   Sec 5      DEk    g=0 c=1 A={0,2} (the dead end G-04)
//   Ex 5.1     the six stuck instances of out/stuck0_9.txt
#include "a25.h"
#include <iostream>
#include <map>
using namespace a25;

static Dec parse_dec(const std::string& s) {  // "61 260315 3524"
  Dec D; Path P;
  for (char ch : s) { if (ch == ' ') { if (!P.empty()) D.push_back(P); P.clear(); } else P.push_back(ch - '0'); }
  if (!P.empty()) D.push_back(P); return D;
}
static uint32_t S(std::initializer_list<int> l) { uint32_t s = 0; for (int x : l) s |= 1u << x; return s; }
static void edges(const Graph& G) { for (int u = 0; u < G.n; u++) for (int v = u + 1; v < G.n; v++) if (G.has(u, v)) printf("%d%d ", u, v); printf("\n"); }
static Graph del(Graph G, int a, int b) { G.rem(a, b); return G; }

// all instance-level children of Theorem 3.1 (as stated) plus the moves.h variants; returns label list
struct Child { std::string mv; Graph H; int c; uint32_t A; };
static std::vector<Child> children(const Graph& G, int c, uint32_t A) {
  std::vector<Child> out; int n = G.n; int g = theeven(G);
  // (i)
  { uint32_t C = 1u << c; bool ch = true; while (ch) { ch = false; for (int x = 0; x < n; x++) if ((C >> x & 1u) && (G.adj[x] & ~A & ~C)) { C |= G.adj[x] & ~A; ch = true; } }
    uint32_t bd = 0; for (int x = 0; x < n; x++) if (!(C >> x & 1u) && (G.adj[x] & C)) bd |= 1u << x;
    if (bd != A) out.push_back({"i", G, c, bd}); }
  if (G.deg(c) == 3) { int ys[3], t = 0; for (int y = 0; y < n; y++) if (G.has(c, y)) ys[t++] = y;
    for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) if (i != j && !G.has(ys[i], ys[j])) { Graph H = G; H.rem(c, ys[i]); H.rem(c, ys[j]); H.add(ys[i], ys[j]); out.push_back({"g", H, c, A | (1u << ys[i])}); } }
  if (g < 0) {
    if (G.deg(c) >= 3) for (int y = 0; y < n; y++) if (G.has(c, y) && !(A >> y & 1u)) { Graph H = G; int l = H.n++; H.adj[l] = 0; H.rem(c, y); H.add(y, l); out.push_back({"d", H, l, A | (1u << c)}); }
    return out;
  }
  if (G.has(g, c) && !(A >> g & 1u)) out.push_back({"a", del(G, g, c), g, A | (1u << c)});
  for (int x = 0; x < n; x++) if (G.has(g, x) && x != c && !(A >> x & 1u)) {
    if (!G.has(c, x)) out.push_back({"b", del(G, g, x), c, A});
    else out.push_back({"c", del(del(G, g, x), x, c), x, A | (1u << c)});
  }
  if (G.deg(g) == 2) { int u = __builtin_ctz(G.adj[g]), v = 31 - __builtin_clz(G.adj[g]);
    if (!G.has(u, v)) { Graph H = G; H.rem(g, u); H.rem(g, v); H.add(u, v);
      if (!(A >> g & 1u)) out.push_back({"e", H, c, A}); else for (int w : {u, v}) if (w != c) out.push_back({"e", H, c, (A & ~(1u << g)) | (1u << w)}); }
    else if (A >> g & 1u) out.push_back({"f", G, c, A & ~(1u << g)}); }
  if (!(A >> g & 1u)) { std::vector<int> P{g}; uint32_t vis = 1u << g;
    std::function<void(int)> go = [&](int x) { for (int y = 0; y < n; y++) if (G.has(x, y) && !(vis >> y & 1u)) {
      if (y == c) { if (P.size() >= 2) { Graph H = G; uint32_t B = A; std::vector<int> R = P; R.push_back(c); for (size_t i = 0; i + 1 < R.size(); i++) H.rem(R[i], R[i + 1]); for (size_t i = 1; i < R.size(); i++) B |= 1u << R[i]; out.push_back({"h", H, g, B}); } continue; }
      if (A >> y & 1u) continue; vis |= 1u << y; P.push_back(y); go(y); P.pop_back(); vis &= ~(1u << y); } };
    go(g); }
  return out;
}

// D-level Case I census at target u: all good D' of G-gu, chain through c?, transfer good?
static void dlevel(const Graph& G, int c, uint32_t A, int g, int u, long long& nd, long long& nav, long long& navok, long long& nthru, long long& nthruok) {
  Graph H = del(G, g, u); nd = nav = navok = nthru = nthruok = 0;
  enumerate(H, nullptr, [&](const Dec& D) {
    int qi = path_ending_at(D, c); if (qi < 0 || (vset(D[qi]) & A)) return false;
    nd++; Dec D2; std::vector<int> ch;
    if (!forced_chain(D, g, u, D2, ch)) { printf("  STUCK CHAIN\n"); return false; }
    if (!check(G, D2)) { printf("  BAD FAN IMAGE\n"); exit(1); }
    int q2 = path_ending_at(D2, c); bool ok = q2 >= 0 && !(vset(D2[q2]) & A);
    bool thru = std::find(ch.begin(), ch.end(), c) != ch.end();
    if (thru) { nthru++; nthruok += ok; } else { nav++; navok += ok; }
    return false; }, c, A);
}

int main() {
  Graph G;
  // ---------------- Proposition 4.7 ----------------
  printf("=== Proposition 4.7: FEhv?\n");
  decode_g6("FEhv?", G); printf("edges: "); edges(G);
  printf("even set %s, degrees:", sstr(G.evenset()).c_str()); for (int v = 0; v < G.n; v++) printf(" %d", G.deg(v)); printf("\n");
  for (uint32_t A : {S({3, 5}), S({3, 4, 5})}) {
    int g = 4, c = 6;
    printf("A=%s admissible=%d blocked=%d c notin N(g)=%d good(G)=%d\n", sstr(A).c_str(), (int)admissible(G, c, A), (int)blocked(G, c, A), (int)!G.has(g, c), good(G, c, A));
    for (int x = 0; x < G.n; x++) if (G.has(g, x)) {
      Graph H = del(G, g, x);
      printf("  target %d tight=%d  (G-gx,c,A) good=%d", x, (int)G.has(c, x), good(H, c, A));
      if (G.has(c, x)) { Graph K = del(H, x, c); printf("  (c)-child (G-xc-gx,x,A+c) good=%d  N_K(x)=%s", good(K, x, A | (1u << c)), sstr(K.adj[x]).c_str()); }
      printf("\n");
    }
    // every instance-level child
    auto ch = children(G, c, A); printf("  instance-level children:"); for (auto& k : ch) printf(" %s:%d", k.mv.c_str(), good(k.H, k.c, k.A)); printf("\n");
  }
  {
    Graph H = del(G, 4, 0); Dec D = parse_dec("61 260315 3524"); Dec D2; std::vector<int> chv;
    printf("D'={61,260315,3524} valid for G-40: %d, Q_6=%s\n", (int)check(H, D), sstr(vset(D[path_ending_at(D, 6)])).c_str());
    forced_chain(D, 4, 0, D2, chv); printf("  chain:"); for (int x : chv) printf(" %d", x); printf("  image %s valid=%d Q_6=%s\n", dstr(D2).c_str(), (int)check(G, D2), sstr(vset(D2[path_ending_at(D2, 6)])).c_str());
    Dec E = parse_dec("61 2513 426035"); printf("D''={61,2513,426035} valid: %d\n", (int)check(H, E));
    forced_chain(E, 4, 0, D2, chv); printf("  chain:"); for (int x : chv) printf(" %d", x); printf("  image %s valid=%d Q_6=", dstr(D2).c_str(), (int)check(G, D2)); for (int x : D2[path_ending_at(D2, 6)]) printf("%d", x); printf("\n");
    long long nd, nav, navok, nthru, nthruok;
    for (uint32_t A : {S({3, 5}), S({3, 4, 5})}) for (int x : {0, 2}) { dlevel(G, 6, A, 4, x, nd, nav, navok, nthru, nthruok);
      printf("  A=%s target %d: good D'=%lld, chain avoids c %lld (transfer ok %lld), chain through c %lld (ok %lld)\n", sstr(A).c_str(), x, nd, nav, navok, nthru, nthruok); }
  }
  // ---------------- Example 4.3 ----------------
  printf("\n=== Example 4.3: FCZ~o\n");
  decode_g6("FCZ~o", G); printf("edges: "); edges(G); printf("even set %s\n", sstr(G.evenset()).c_str());
  {
    int g = 4, c = 0, x = 6; uint32_t A = S({1, 2, 3, 4});
    Graph H = del(G, g, x);
    printf("x in N(g) cap N(c): %d, c notin N(g): %d, A cap N(c)=%s\n", (int)(G.has(g, x) && G.has(c, x)), (int)!G.has(g, c), sstr(A & G.adj[c]).c_str());
    printf("(G-46,0,A) good=%d  (G,0,A) good=%d\n", good(H, c, A), good(G, c, A));
    Dec D = parse_dec("05 1453062 361524"); Dec D2; std::vector<int> chv;
    printf("D' valid=%d", (int)check(H, D)); forced_chain(D, g, x, D2, chv); printf(" chain:"); for (int z : chv) printf(" %d", z); printf(" image valid=%d Q_0=", (int)check(G, D2)); for (int z : D2[path_ending_at(D2, 0)]) printf("%d", z); printf("\n");
    long long nd, nav, navok, nthru, nthruok; dlevel(G, c, A, g, x, nd, nav, navok, nthru, nthruok);
    printf("all good D' of G-46: %lld; chain avoids c in %lld; chain through c in %lld (good image %lld)\n", nd, nav, nthru, nthruok);
  }
  // ---------------- DEk ----------------
  printf("\n=== Section 5 dead end: DEk\n");
  decode_g6("DEk", G); printf("edges: "); edges(G); printf("even set %s\n", sstr(G.evenset()).c_str());
  {
    int c = 1; uint32_t A = S({0, 2});
    printf("(G,1,A): admissible=%d c-admissible=%d blocked=%d good=%d\n", (int)admissible(G, c, A), (int)!(A & closedN(G, c)), (int)blocked(G, c, A), good(G, c, A));
    for (int x : {3, 4}) { Graph H = del(G, 0, x); printf("  Case I child G-0%d (target %d, tight=%d): good=%d admissible=%d\n", x, x, (int)G.has(c, x), good(H, c, A), (int)admissible(H, c, A)); }
    Graph H = del(G, 0, 4); printf("  {13, 0342} valid for G-04: %d\n", (int)check(H, parse_dec("13 0342")));
    printf("  G-04: even set %s, N(4)=%s\n", sstr(H.evenset()).c_str(), sstr(H.adj[4]).c_str());
    printf("  (G-04-43,1,A) good=%d   (G-04-42,1,A) good=%d (target 2 in A)\n", good(del(H, 4, 3), c, A), good(del(H, 4, 2), c, A));
    auto ch = children(H, c, A); printf("  all instance-level children of (G-04,1,A):"); for (auto& k : ch) printf(" %s:%d", k.mv.c_str(), good(k.H, k.c, k.A)); printf("\n");
  }
  // ---------------- the six stuck instances ----------------
  printf("\n=== Example 5.1: the stuck instances (out/stuck0_9.txt)\n");
  const char* st[6][2] = {{"H?ABfbw", "8"}, {"H?ABvrw", "7"}, {"H?ABvrw", "8"}, {"H?B@nbw", "8"}, {"H?BDvp{", "7"}, {"H?Bcrrw", "8"}};
  for (auto& s : st) {
    decode_g6(s[0], G); int c = atoi(s[1]); int g = theeven(G); uint32_t A = amax(G, c);
    bool indep = true; for (int a = 0; a < G.n; a++) for (int b = 0; b < G.n; b++) if (G.has(c, a) && G.has(c, b) && G.has(a, b)) indep = false;
    bool mech = G.deg(g) == 4 && G.deg(c) == 5 && indep && !(G.adj[g] & ~G.adj[c]);
    for (int u = 0; u < G.n; u++) if (G.has(g, u)) { uint32_t r = G.adj[u] & ~(1u << g) & ~(1u << c); if (G.deg(u) != 3 || __builtin_popcount(r) != 1 || !(r & A)) mech = false; }
    printf("%s c=%d g=%d A=%s adm=%d blocked=%d good=%d mechanism=%d edges: ", s[0], c, g, sstr(A).c_str(), (int)admissible(G, c, A), (int)blocked(G, c, A), good(G, c, A), (int)mech); edges(G);
    auto ch = children(G, c, A); int ng = 0; printf("  children:"); for (auto& k : ch) { int r = good(k.H, k.c, k.A); ng += r; printf(" %s:%d", k.mv.c_str(), r); } printf("  -> %s\n", ng ? "NOT stuck" : "stuck");
    printf("  Q_c = cx possible for x in {"); for (int x = 0; x < G.n; x++) if (G.has(c, x)) { uint32_t f = ((1u << G.n) - 1) & ~(1u << c) & ~(1u << x); if (good(G, c, f) == 1) printf("%d ", x); } printf("}\n");
    for (int u = 0; u < G.n; u++) if (G.has(g, u)) { long long nd, nav, navok, nthru, nthruok; dlevel(G, c, A, g, u, nd, nav, navok, nthru, nthruok);
      printf("  u=%d: good D'=%lld, chain avoids c %lld (%.1f%%, transfer ok %lld), through c %lld (ok %lld)\n", u, nd, nav, 100.0 * nav / nd, navok, nthru, nthruok); }
  }
}
