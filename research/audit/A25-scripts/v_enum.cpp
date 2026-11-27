// v_enum.cpp: validation of the transition-system enumerator of a25.h.
// For every graph6 line on stdin and several end-count vectors b (Lovász, and random feasible ones
// seeded by the line number), print "g6 b-vector count hash" where hash is an order-independent
// hash of the canonical decompositions (each path written from its smaller end, paths sorted).
// Every enumerated decomposition is checked; duplicates are detected.
#include "a25.h"
#include <set>
#include <iostream>
using namespace a25;
static unsigned long long hstr(const std::string& s) { unsigned long long h = 1469598103934665603ULL; for (char ch : s) { h ^= (unsigned char)ch; h *= 1099511628211ULL; } return h; }
int main(int argc, char** argv) {
  int nrand = argc > 1 ? atoi(argv[1]) : 2;
  std::string line; unsigned seed = 12345; long long bad = 0, dup = 0;
  while (std::getline(std::cin, line)) {
    Graph G; if (!decode_g6(line, G)) continue;
    std::vector<std::vector<int>> bs;
    std::vector<int> b0(G.n); for (int v = 0; v < G.n; v++) b0[v] = G.deg(v) % 2; bs.push_back(b0);
    for (int r = 0; r < nrand; r++) {
      std::vector<int> b(G.n);
      for (int v = 0; v < G.n; v++) { seed = seed * 1103515245u + 12345u; int d = G.deg(v); int k = (seed >> 16) % (d / 2 + 1); b[v] = (d % 2) + 2 * k; if (b[v] > d) b[v] = d % 2; }
      bs.push_back(b);
    }
    for (auto& b : bs) {
      std::set<std::string> seen; unsigned long long H = 0; long long cnt = 0;
      enumerate(G, b.data(), [&](const Dec& D) {
        if (!check(G, D, b.data())) bad++;
        std::vector<std::string> ps;
        for (auto P : D) { if (P.front() > P.back()) std::reverse(P.begin(), P.end()); std::string s; for (int x : P) s += char('a' + x); ps.push_back(s); }
        std::sort(ps.begin(), ps.end()); std::string key; for (auto& s : ps) key += s + "|";
        if (!seen.insert(key).second) dup++;
        H += hstr(key); cnt++; return false; });
      std::cout << line << " "; for (int x : b) std::cout << x; std::cout << " " << cnt << " " << H << "\n";
    }
  }
  std::cerr << "bad=" << bad << " dup=" << dup << "\n";
}
