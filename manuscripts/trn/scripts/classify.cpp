// classify.cpp: exhaustive classification of TRN failures over (G, D') pairs.
// For every TRN test (G,g,y,x,u) and every good D' of K=G-gu (x notin Q'(y)) whose plain Fan image
// is bad, record: adj (y~g), i (step at which the chain meets y; i=1 means e=g), side (x on the e-half
// E or on the partner half P of P_y), qu (u in Q'(y)), wit (child has a witness), tri2 (d(g)=2 and
// N(g) spans an edge), and which repairs succeed: exch (exchange lemma), rot (a rotation at y followed
// by plain Fan), rep (re-pairing of halves at u), loc (re-decomposition of chain paths + Q'(y) + gu).
// Prints aggregated counts and the first examples where every repair fails.
#include "dec.h"
#include <map>
using namespace dec;
// ---------- local re-decomposition search ----------
static int Ln; static uint32_t radj[MAXV]; static int need[MAXV]; static int Ly, Lx; static bool lfound; static int remE;
static void lgrow(int a, int cur, uint32_t vis, bool isY);
static void lsolve() {
  if (lfound) return;
  if (remE == 0) { for (int v = 0; v < Ln; v++) if (need[v]) return; lfound = true; return; }
  int a = -1;
  for (int v = 0; v < Ln; v++) if (need[v] > 0) { if (!radj[v]) return; if (a < 0) a = v; }
  if (a < 0) return;
  if (need[Ly] > 0) a = Ly;
  need[a]--; lgrow(a, a, 1u << a, a == Ly); need[a]++;
}
static void lgrow(int a, int cur, uint32_t vis, bool isY) {
  uint32_t nb = radj[cur] & ~vis; if (isY) nb &= ~(1u << Lx);
  while (nb && !lfound) {
    int w = __builtin_ctz(nb); nb &= nb - 1;
    radj[cur] &= ~(1u << w); radj[w] &= ~(1u << cur); remE--;
    uint32_t nv = vis | (1u << w);
    if (need[w] > 0 && !(w == Ly && (nv >> Lx & 1))) { need[w]--; lsolve(); need[w]++; }
    if (!lfound) lgrow(a, w, nv, isY);
    radj[cur] |= 1u << w; radj[w] |= 1u << cur; remE++;
  }
}
// ---------- halves matching ----------
static std::vector<uint32_t> hm; static std::vector<int> hend, mate; static bool mok;
static void hmatch(int i, const std::function<bool()>& chk) {
  if (mok) return;
  while (i < (int)hm.size() && mate[i] >= 0) i++;
  if (i == (int)hm.size()) { if (chk()) mok = true; return; }
  for (int j = i + 1; j < (int)hm.size() && !mok; j++) if (mate[j] < 0 && !(hm[i] & hm[j])) { mate[i] = j; mate[j] = i; hmatch(i + 1, chk); mate[i] = mate[j] = -1; }
}
static bool goodImage(const Decomp& D, int g, int u, int y, int x) {
  std::vector<int> ch; Decomp R = fan_forced(D, g, u, ch); return path_avoids(R[path_end_at(R, y)], 1u << x);
}
int main(int argc, char** argv) {
  int nprint = argc > 1 ? atoi(argv[1]) : 5;
  long long maxD = argc > 2 ? atoll(argv[2]) : 0;   // skip instances with more good D' than this (0: no limit)
  std::map<std::string, long long> agg; long long nbad = 0, nallfail = 0, skipped = 0, tests = 0, badinst = 0; int printed = 0;
  char line[256];
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    if (__builtin_popcount(G.evens()) != 1) continue;
    int g = even_vertex(G), n = G.N;
    bool tri2 = G.deg(g) == 2 && G.has(__builtin_ctz(G.adj[g]), 31 - __builtin_clz(G.adj[g]));
    for (int u = 0; u < n; u++) { if (!G.has(g, u)) continue;
      Gr H = G; H.del(g, u);
      for (int y = 0; y < n; y++) { if (G.deg(y) % 2 == 0 || !G.has(y, u)) continue;
        for (int x = 0; x < n; x++) {
          if (x == y || x == u || G.deg(x) % 2 == 0 || G.has(x, y)) continue;
          bool wit = (G.adj[y] & ~G.adj[x] & ~(1u << u)) != 0;
          if (getenv("CORE")) {
            bool tight = true; for (int v = 0; v < n; v++) if (G.has(g, v) && v != x && v != y && !G.has(y, v)) tight = false;
            bool cn = (G.adj[x] & G.adj[y]) != 0;
            bool ind = G.deg(g) == 2 && !tri2;
            bool nw = (G.adj[y] & ~G.adj[x] & ~(1u << g)) != 0;   // (C0)
            if (!tight || !wit || !cn || ind || !nw) continue;
          }
          std::vector<Decomp> bad;
          long long nD = enumerate(H, y, 1u << x, maxD ? maxD + 1 : 0, [&](const Decomp& D) {
            if (!goodImage(D, g, u, y, x)) bad.push_back(D); return false; });
          if (!nD) continue;
          if (maxD && nD > maxD) { skipped++; continue; }
          tests++; if (!bad.empty()) badinst++;
          for (auto& D : bad) {
            nbad++;
            std::vector<int> ch; fan_forced(D, g, u, ch);
            int i = (int)(std::find(ch.begin(), ch.end(), y) - ch.begin());
            int qi = path_end_at(D, y); Path Q = D[qi]; if (Q.front() != y) std::reverse(Q.begin(), Q.end());
            bool qu = std::find(Q.begin(), Q.end(), u) != Q.end();
            // P_y and halves
            int py = -1; size_t ky = 0;
            for (size_t pi = 0; pi < D.size(); pi++) { const Path& p = D[pi];
              for (size_t j = 0; j + 1 < p.size(); j++) if ((p[j] == y && p[j+1] == u) || (p[j] == u && p[j+1] == y)) { py = (int)pi; ky = j; } }
            Path P = D[py]; if (!(P[ky] == y)) { std::reverse(P.begin(), P.end()); }
            // now P = e ... y u ... f with y at some index
            size_t yi = std::find(P.begin(), P.end(), y) - P.begin();
            if (!(yi + 1 < P.size() && P[yi + 1] == u)) { std::reverse(P.begin(), P.end()); yi = std::find(P.begin(), P.end(), y) - P.begin(); }
            bool sideE = false; for (size_t j = 0; j < yi; j++) if (P[j] == x) sideE = true;
            uint32_t vP = 0, vQ = 0; for (int v : P) vP |= 1u << v; for (int v : Q) vQ |= 1u << v;
            bool exch = !qu && (vP & vQ) == (1u << y);
            // rotations at y
            bool rot = false;
            for (size_t pi = 0; pi < D.size() && !rot; pi++) { if ((int)pi == qi) continue;
              const Path& R = D[pi]; auto it = std::find(R.begin(), R.end(), y); if (it == R.end()) continue;
              size_t k = it - R.begin(); if (k == 0 || k + 1 == R.size()) continue;
              for (int side = 0; side < 2 && !rot; side++) {
                Path half, other;
                if (side == 0) { for (size_t j = k; j < R.size(); j++) half.push_back(R[j]); for (size_t j = 0; j <= k; j++) other.push_back(R[j]); }
                else { for (size_t j = k + 1; j-- > 0;) half.push_back(R[j]); for (size_t j = R.size(); j-- > k;) other.push_back(R[j]); }
                Path J = other; for (size_t j = 1; j < Q.size(); j++) J.push_back(Q[j]);
                uint32_t vs = 0; bool okp = true; for (int v : J) { if (vs >> v & 1) { okp = false; break; } vs |= 1u << v; }
                if (!okp || !path_avoids(half, 1u << x)) continue;
                Decomp D2; for (size_t j = 0; j < D.size(); j++) if ((int)j != qi && j != pi) D2.push_back(D[j]);
                D2.push_back(half); D2.push_back(J);
                if (goodImage(D2, g, u, y, x)) rot = true;
              } }
            // re-pairing of halves at u
            bool rep = false;
            if (!sideE) {
              hm.clear(); hend.clear();
              for (auto& p : D) { auto it = std::find(p.begin(), p.end(), u); if (it == p.end()) continue; size_t k = it - p.begin();
                uint32_t a = 0, b = 0; for (size_t j = 0; j < k; j++) a |= 1u << p[j]; for (size_t j = k + 1; j < p.size(); j++) b |= 1u << p[j];
                hm.push_back(a); hend.push_back(p.front()); hm.push_back(b); hend.push_back(p.back()); }
              int he = -1, hy = -1; for (size_t j = 0; j < hm.size(); j++) { if ((hm[j] >> y & 1) && hend[j] == P.front()) he = (int)j; if (hend[j] == y) hy = (int)j; }
              mate.assign(hm.size(), -1); mok = false;
              if (he >= 0) hmatch(0, [&]() { if (hm[mate[he]] >> x & 1) return false; if (hy >= 0 && (hm[mate[hy]] >> x & 1)) return false; return true; });
              rep = mok;
            }
            // local re-decomposition
            std::vector<int> sel;
            for (int v : ch) { int pi = path_end_at(D, v); if (std::find(sel.begin(), sel.end(), pi) == sel.end()) sel.push_back(pi); }
            if (std::find(sel.begin(), sel.end(), qi) == sel.end()) sel.push_back(qi);
            Ln = n; memset(radj, 0, sizeof radj); memset(need, 0, sizeof need); remE = 0;
            for (int pi : sel) { const Path& p = D[pi]; need[p.front()]++; need[p.back()]++;
              for (size_t j = 0; j + 1 < p.size(); j++) { radj[p[j]] |= 1u << p[j+1]; radj[p[j+1]] |= 1u << p[j]; remE++; } }
            radj[g] |= 1u << u; radj[u] |= 1u << g; remE++; need[g]--; need[u]++;
            Ly = y; Lx = x; lfound = false; lsolve();
            bool loc = lfound;
            char key[128];
            snprintf(key, sizeof key, "adj=%d i=%s side=%c qu=%d wit=%d tri2=%d | exch=%d rot=%d rep=%d loc=%d",
                     (int)G.has(g, y), i == 1 ? "1" : ">1", sideE ? 'E' : 'P', (int)qu, (int)wit, (int)tri2, (int)exch, (int)rot, (int)rep, (int)loc);
            agg[key]++;
            if (!exch && !rot && !rep && !loc) { nallfail++;
              if (printed < nprint) { printed++; printf("ALLFAIL %s g=%d y=%d x=%d u=%d wit=%d D'=", line, g, y, x, u, (int)wit);
                for (auto& p : D) { for (int v : p) printf("%d", v); printf(" "); } printf(" chain="); for (int v : ch) printf("%d", v); printf("\n"); } }
          }
        }
      }
    }
  }
  for (auto& kv : agg) printf("  %-80s %lld\n", kv.first.c_str(), kv.second);
  printf("SUMMARY tests=%lld (skipped %lld with > maxD good D') instances-with-bad-D'=%lld bad D'=%lld all-repairs-fail=%lld\n", tests, skipped, badinst, nbad, nallfail);
}
