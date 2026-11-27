// t_calc.cpp: exhaustive test of the transfer calculus (manuscript Theorem 3.1) exactly as stated,
// with NO admissibility and with every A subset of V (c in A allowed, as the definition of instance
// allows).  For every connected graph on stdin with at most one even vertex, every odd c, every A and
// every applicable move, test "child good => parent good" with the a25 oracle (all Lovász
// decompositions enumerated once per graph; goodness read off the minimal V(Q_c) sets).
// Also tests the variants that moves.h actually uses ((b) and (c) without c notin N(g)), and the
// measure claim.  Output: per move, tests (child good), violations, measure failures; first examples.
#include "a25.h"
#include <map>
#include <iostream>
using namespace a25;

static std::map<std::string, std::vector<std::vector<uint32_t>>> memo;
static std::string gkey(const Graph& G) { std::string k((const char*)G.adj, 4 * G.n); k.push_back((char)G.n); return k; }
static const std::vector<std::vector<uint32_t>>& sets(const Graph& G) {
  std::string k = gkey(G); auto it = memo.find(k); if (it != memo.end()) return it->second;
  std::vector<std::vector<uint32_t>> s; qc_sets(G, s); return memo[k] = s;
}
static bool isgood(const Graph& G, int c, uint32_t A) {
  if (G.deg(c) % 2 == 0) return false; if (A >> c & 1u) return false;
  if (__builtin_popcount(G.evenset()) > 1) { fprintf(stderr, "two even vertices in a child\n"); exit(1); }
  return good_from_sets(sets(G)[c], A);
}
static long long nu(const Graph& G) { long long s = 0; for (int v = 0; v < G.n; v++) s += G.deg(v); return s + (G.evenset() ? 0 : 1); }

struct Stat { long long app = 0, tests = 0, tests_cnotA = 0, viol = 0, viol_cnotA = 0, measure = 0; int shown = 0; };
static std::map<std::string, Stat> st;
static void report(const std::string& mv, const std::string& g6, const Graph& G, int c, uint32_t A, const Graph& H, int c2, uint32_t A2) {
  Stat& s = st[mv]; s.app++;
  long long n1 = nu(G), n2 = nu(H);
  bool dec = n2 < n1 || (n2 == n1 && __builtin_popcount(A2) < __builtin_popcount(A));
  if (!dec) s.measure++;
  if (!isgood(H, c2, A2)) return;
  s.tests++; if (!(A >> c & 1u)) s.tests_cnotA++;
  if (!isgood(G, c, A)) {
    s.viol++; if (!(A >> c & 1u)) s.viol_cnotA++;
    if (s.shown++ < 3) printf("VIOL %s %s c=%d A=%s  child c=%d A=%s (cInA=%d adm=%d)\n", mv.c_str(), g6.c_str(), c, sstr(A).c_str(), c2, sstr(A2).c_str(), (int)(A >> c & 1u), (int)admissible(G, c, A));
  }
}

int main() {
  std::string line;
  while (std::getline(std::cin, line)) {
    Graph G; if (!decode_g6(line, G)) continue;
    uint32_t E = G.evenset(); if (__builtin_popcount(E) > 1) continue;
    int g = E ? __builtin_ctz(E) : -1;
    int n = G.n;
    for (int c = 0; c < n; c++) {
      if (G.deg(c) % 2 == 0) continue;
      for (uint32_t A = 0; A < (1u << n); A++) {
        bool cA = A >> c & 1u;
        if (g >= 0) {
          // (a)
          if (G.has(g, c) && !cA) { Graph H = G; H.rem(g, c); report("a", line, G, c, A, H, g, A | (1u << c)); }
          for (int x = 0; x < n; x++) if (G.has(g, x) && x != c) {
            bool xA = A >> x & 1u;
            if (!G.has(c, x) && !xA) {  // (b)
              Graph H = G; H.rem(g, x);
              report(G.has(g, c) ? "b'(c in N(g), moves.h)" : "b", line, G, c, A, H, c, A);
            }
            if (G.has(c, x) && !xA && !cA) {  // (c)
              Graph H = G; H.rem(g, x); H.rem(x, c);
              report(G.has(g, c) ? "c'(c in N(g), moves.h)" : "c", line, G, c, A, H, x, A | (1u << c));
            }
          }
          if (G.deg(g) == 2) {
            int u = __builtin_ctz(G.adj[g]), v = 31 - __builtin_clz(G.adj[g]);
            if (!G.has(u, v)) {  // (e)
              Graph H = G; H.rem(g, u); H.rem(g, v); H.add(u, v);
              if (!(A >> g & 1u)) report("e", line, G, c, A, H, c, A);
              else { for (int w : {u, v}) if (w != c) report("e", line, G, c, A, H, c, (A & ~(1u << g)) | (1u << w)); }
            } else if ((A >> g & 1u) && !G.has(g, c)) report("f", line, G, c, A, G, c, A & ~(1u << g));  // (f)
            if (G.has(u, v) && (A >> g & 1u) && G.has(g, c)) report("f'(c in N(g))", line, G, c, A, G, c, A & ~(1u << g));
          }
          // (h): every path g r1 .. r_{k-1} c, k >= 2, interior outside A, g notin A
          if (!(A >> g & 1u)) {
            std::vector<int> P{g}; uint32_t vis = 1u << g;
            std::function<void(int)> go = [&](int x) {
              for (int y = 0; y < n; y++) if (G.has(x, y) && !(vis >> y & 1u)) {
                if (y == c) { if (P.size() >= 2) { Graph H = G; uint32_t B = A; std::vector<int> R = P; R.push_back(c);
                    for (size_t i = 0; i + 1 < R.size(); i++) H.rem(R[i], R[i + 1]); for (size_t i = 1; i < R.size(); i++) B |= 1u << R[i];
                    report(G.has(g, c) ? "h(c in N(g))" : "h", line, G, c, A, H, g, B); } continue; }
                if (A >> y & 1u) continue;
                vis |= 1u << y; P.push_back(y); go(y); P.pop_back(); vis &= ~(1u << y);
              }
            };
            go(g);
          }
        } else {
          // (d)
          if (G.deg(c) >= 3) for (int y = 0; y < n; y++) if (G.has(c, y) && !(A >> y & 1u)) {
            Graph H = G; int l = H.n++; H.adj[l] = 0; H.rem(c, y); H.add(y, l);
            report("d", line, G, c, A, H, l, A | (1u << c));
          }
        }
        // (g)
        if (G.deg(c) == 3) {
          int ys[3], t = 0; for (int y = 0; y < n; y++) if (G.has(c, y)) ys[t++] = y;
          for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) if (i != j && !G.has(ys[i], ys[j])) {
            Graph H = G; H.rem(c, ys[i]); H.rem(c, ys[j]); H.add(ys[i], ys[j]);
            report(g >= 0 && G.has(g, c) ? "g(c in N(g))" : "g", line, G, c, A, H, c, A | (1u << ys[i]));
          }
        }
        // (i)
        if (!cA) {
          uint32_t C = 1u << c; bool ch = true;
          while (ch) { ch = false; for (int x = 0; x < n; x++) if ((C >> x & 1u) && (G.adj[x] & ~A & ~C)) { C |= G.adj[x] & ~A; ch = true; } }
          uint32_t bd = 0; for (int x = 0; x < n; x++) if (!(C >> x & 1u) && (G.adj[x] & C)) bd |= 1u << x;
          if (bd != A) report("i", line, G, c, A, G, c, bd);
        }
      }
    }
  }
  printf("move  applications  tests(child good)  tests-with-c-notin-A  violations  violations-with-c-notin-A  measure-not-decreasing\n");
  for (auto& kv : st) printf("%-24s %10lld %10lld %10lld %8lld %8lld %8lld\n", kv.first.c_str(), kv.second.app, kv.second.tests, kv.second.tests_cnotA, kv.second.viol, kv.second.viol_cnotA, kv.second.measure);
}
