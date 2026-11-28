// halves.cpp: for bad D', locate x on P_y: on the e-half (e..y->u) or on the partner half (u->..f).
// For partner-side failures, test whether some re-pairing of the halves at u (all perfect matchings
// of halves into vertex-disjoint pairs) keeps x notin Q'(y) and gives a good Fan image.
#include "dec.h"
using namespace dec;
struct Half { std::vector<int> v; int end; };  // v: from end to u (inclusive)
static std::vector<Half> hs; static std::vector<int> mate; static bool ok;
static int Hy = -1, Hey = -1; static int X; static int Np;
static std::vector<uint32_t> hm;
static void match(int i, std::function<bool()> chk) {
  if (ok) return;
  while (i < (int)hs.size() && mate[i] >= 0) i++;
  if (i == (int)hs.size()) { if (chk()) ok = true; return; }
  for (int j = i + 1; j < (int)hs.size() && !ok; j++) if (mate[j] < 0 && !(hm[i] & hm[j])) {
    mate[i] = j; mate[j] = i; match(i + 1, chk); mate[i] = mate[j] = -1; }
}
int main(int argc, char** argv) {
  char line[256]; long long nbad = 0, onE = 0, onP = 0, fixP = 0;
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
            // build halves
            hs.clear(); std::vector<Path> full;
            for (auto& p : D) { auto it = std::find(p.begin(), p.end(), u);
              if (it == p.end()) { full.push_back(p); continue; }
              size_t k = it - p.begin();
              Half a; for (size_t j = 0; j <= k; j++) a.v.push_back(p[j]); a.end = p.front();
              Half b; for (size_t j = p.size(); j-- > k;) b.v.push_back(p[j]); b.end = p.back();
              hs.push_back(a); hs.push_back(b); }
            hm.assign(hs.size(), 0);
            for (size_t i = 0; i < hs.size(); i++) for (int v : hs[i].v) if (v != u) hm[i] |= 1u << v;
            // the e-half: half whose vertex before u is y
            int he = -1; for (size_t i = 0; i < hs.size(); i++) if (hs[i].v[hs[i].v.size() - 2] == y) he = (int)i;
            bool xe = hm[he] >> x & 1;
            if (xe) { onE++; return false; }
            onP++;
            // y's half (if Q'(y) passes through u)
            int hy = -1; for (size_t i = 0; i < hs.size(); i++) if (hs[i].end == y) hy = (int)i;
            mate.assign(hs.size(), -1); ok = false;
            match(0, [&]() {
              if (hm[mate[he]] >> x & 1) return false;
              if (hy >= 0 && (hm[mate[hy]] >> x & 1)) return false;
              return true; });
            if (ok) fixP++;
            return false; });
        }
      }
    }
  }
  printf("bad D'=%lld: x on e-half %lld, x on partner half %lld (fixed by re-pairing at u: %lld)\n", nbad, onE, onP, fixP);
}
