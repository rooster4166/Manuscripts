// rot.cpp: for each bad D' (plain Fan image has x in Q(y)), try every "rotation" at y: pick a path P
// through y (y interior) and a side; the edge from y to that side becomes the new terminal edge
// (new Q''(y) = that half of P), and Q'(y) is joined with the other half of P at y.  Valid if the
// joined trail is a path.  Count bad D' that have a rotation giving D'' with x notin Q''(y) and
// (a) chain avoiding y, (b) good image, (c) at least valid & good D''.
#include "dec.h"
using namespace dec;
int main(int argc, char** argv) {
  char line[256]; long long nbad = 0, ra = 0, rb = 0, rc = 0, rPy = 0, rPyB = 0; int pr = argc > 1 ? atoi(argv[1]) : 0, printed = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    if (__builtin_popcount(G.evens()) != 1) continue;
    int g = even_vertex(G), n = G.N;
    for (int u = 0; u < n; u++) { if (!G.has(g, u)) continue;
      Gr H = G; H.del(g, u);
      for (int y = 0; y < n; y++) { if (G.deg(y) % 2 == 0 || !G.has(y, u)) continue;
        for (int x = 0; x < n; x++) {
          if (x == y || x == u || G.deg(x) % 2 == 0 || G.has(x, y)) continue;
          if (getenv("WIT")) { uint32_t W = G.adj[y] & ~G.adj[x] & ~(1u << u); if (!W) continue; }
          enumerate(H, y, 1u << x, 0, [&](const Decomp& D) {
            std::vector<int> ch; Decomp R = fan_forced(D, g, u, ch);
            if (path_avoids(R[path_end_at(R, y)], 1u << x)) return false;
            nbad++;
            int qi = path_end_at(D, y); Path Q = D[qi]; if (Q.front() != y) std::reverse(Q.begin(), Q.end());
            bool A = false, B = false, C = false, Apy = false, Bpy = false;
            for (size_t pi = 0; pi < D.size(); pi++) { if ((int)pi == qi) continue;
              const Path& P = D[pi]; auto it = std::find(P.begin(), P.end(), y); if (it == P.end()) continue;
              size_t k = it - P.begin(); if (k == 0 || k + 1 == P.size()) continue;
              bool isPy = (P[k - 1] == u || P[k + 1] == u);
              for (int side = 0; side < 2; side++) {
                Path half, other;  // half: y -> one side (new Q''), other: other side ... y
                if (side == 0) { for (size_t j = k; j < P.size(); j++) half.push_back(P[j]); for (size_t j = 0; j <= k; j++) other.push_back(P[j]); }
                else { for (size_t j = k + 1; j-- > 0;) half.push_back(P[j]); for (size_t j = P.size(); j-- > k;) other.push_back(P[j]); }
                // other ends at y; join with Q (starts at y)
                Path J = other; for (size_t j = 1; j < Q.size(); j++) J.push_back(Q[j]);
                uint32_t vs = 0; bool okp = true; for (int v : J) { if (vs >> v & 1) { okp = false; break; } vs |= 1u << v; }
                if (!okp) continue;
                if (!path_avoids(half, 1u << x)) continue;
                Decomp D2; for (size_t j = 0; j < D.size(); j++) if ((int)j != qi && j != pi) D2.push_back(D[j]);
                D2.push_back(half); D2.push_back(J);
                if (!check_decomp(H, D2)) { fprintf(stderr, "bad rot\n"); exit(1); }
                C = true;
                std::vector<int> ch2; Decomp R2 = fan_forced(D2, g, u, ch2);
                bool av = std::find(ch2.begin(), ch2.end(), y) == ch2.end();
                bool gd = path_avoids(R2[path_end_at(R2, y)], 1u << x);
                if (av) { A = true; if (isPy) Apy = true; }
                if (gd) { B = true; if (isPy) Bpy = true; }
              }
            }
            ra += A; rb += B; rc += C; rPy += Apy; rPyB += Bpy;
            if (pr && !B && printed < pr) { printed++; printf("NOROT %s g=%d y=%d x=%d u=%d D'=", line, g, y, x, u);
              for (auto& p : D) { for (int v : p) printf("%d", v); printf(" "); } printf(" chain="); for (int v : ch) printf("%d", v); printf("\n"); }
            return false; });
        }
      }
    }
  }
  printf("bad D'=%lld  rotation at y gives: valid good D''=%lld  chain-avoiding=%lld (via P_y %lld)  good image=%lld (via P_y %lld)\n", nbad, rc, ra, rPy, rb, rPyB);
}
