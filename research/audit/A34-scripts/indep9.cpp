// indep9.cpp (audit A34): independent TRN / TRN_E / core counter for orders up to 9.
// Does not use the authors' headers.  Input: graph6 (e.g. straight from `nauty-geng -c 9`);
// graphs without exactly one even vertex are skipped (and counted).
// For every candidate (g,u,y,x) with u in N(g) cap N(y), y,x odd, x != y, x != u, x !~ y:
//   test   : K = G-gu has a Lovász decomposition with x notin Q(y)         (own search)
//   TRN_E  : K has one with x notin Q(y) and u notin Q(g)                  (own search)
//   TRN    : checked directly on G when TRN_E fails
//   core   : Definition 5.1 (C2)-(C5), first failing condition counted, as in Table 1;
//            plus gwit: G itself has an N-witness w in N(y)\{g}, w !~ x (hypothesis of Conj. N).
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <vector>
#include <unordered_set>
#include <string>
using namespace std;
static int n, m; static int ea[64], eb[64]; static uint64_t inc[16];
struct KH { size_t operator()(const pair<uint64_t,uint32_t>& k) const { uint64_t x = k.first * 0x9E3779B97F4A7C15ULL ^ (k.second * 0xC2B2AE3D27D4EB4FULL); x ^= x >> 31; return x; } };
static unordered_set<pair<uint64_t,uint32_t>, KH> memo;
static int other(int e, int v) { return ea[e] == v ? eb[e] : ea[e]; }
static bool solveRest(uint64_t rem, uint32_t ends);
// grow a path from a (current end cur, visited vis); close at w in ends; constraint callback via mode
static bool growFree(int a, int cur, uint32_t vis, uint64_t rem, uint32_t ends) {
  uint64_t ex = rem & inc[cur];
  while (ex) { int e = __builtin_ctzll(ex); ex &= ex - 1; int w = other(e, cur); if (vis >> w & 1) continue;
    uint64_t r2 = rem & ~(1ULL << e);
    if ((ends >> w & 1) && solveRest(r2, ends & ~((1u << a) | (1u << w)))) return true;
    if ((r2 & inc[w]) && growFree(a, w, vis | (1u << w), r2, ends)) return true; }
  return false;
}
static bool solveRest(uint64_t rem, uint32_t ends) {
  if (!rem) return ends == 0;
  if (!ends) return false;
  pair<uint64_t,uint32_t> key(rem, ends);
  if (memo.count(key)) return false;
  // every component of the remaining edges must contain a vertex that needs an end
  uint32_t act = 0; for (int v = 0; v < n; v++) if (rem & inc[v]) act |= 1u << v;
  if (ends & ~act) { memo.insert(key); return false; }
  uint32_t seen = 0;
  for (int v = 0; v < n; v++) if ((act >> v & 1) && !(seen >> v & 1)) {
    uint32_t comp = 1u << v, fr = comp;
    while (fr) { int x = __builtin_ctz(fr); fr &= fr - 1; uint64_t ex = rem & inc[x];
      while (ex) { int e = __builtin_ctzll(ex); ex &= ex - 1; int w = other(e, x); if (!(comp >> w & 1)) { comp |= 1u << w; fr |= 1u << w; } } }
    seen |= comp; if (!(comp & ends)) { memo.insert(key); return false; }
  }
  // degree bound and start at an end vertex of least remaining degree
  int P = __builtin_popcount(ends) / 2, a = -1, bd = 999;
  for (int v = 0; v < n; v++) { int d = __builtin_popcountll(rem & inc[v]); int bv = ends >> v & 1;
    if (d > 2 * P - bv) { memo.insert(key); return false; }
    if (bv && d < bd) { bd = d; a = v; } }
  bool ok = growFree(a, a, 1u << a, rem, ends);
  if (!ok) memo.insert(key);
  return ok;
}
// path from c avoiding mask F (never enters F)
static bool growAvoid(int c, int cur, uint32_t vis, uint64_t rem, uint32_t ends) {
  uint64_t ex = rem & inc[cur];
  while (ex) { int e = __builtin_ctzll(ex); ex &= ex - 1; int w = other(e, cur); if (vis >> w & 1) continue;
    uint64_t r2 = rem & ~(1ULL << e);
    if ((ends >> w & 1) && solveRest(r2, ends & ~((1u << c) | (1u << w)))) return true;
    if ((r2 & inc[w]) && growAvoid(c, w, vis | (1u << w), r2, ends)) return true; }
  return false;
}
// TRN_E: y's path avoids x; g's path avoids u (if y's path ends at g, it must avoid u)
static int G_, U_;
static bool growG(int cur, uint32_t vis, uint64_t rem, uint32_t ends) {   // g's path, avoiding u
  uint64_t ex = rem & inc[cur];
  while (ex) { int e = __builtin_ctzll(ex); ex &= ex - 1; int w = other(e, cur); if (vis >> w & 1) continue;
    uint64_t r2 = rem & ~(1ULL << e);
    if ((ends >> w & 1) && solveRest(r2, ends & ~((1u << G_) | (1u << w)))) return true;
    if ((r2 & inc[w]) && growG(w, vis | (1u << w), r2, ends)) return true; }
  return false;
}
static bool growY(int y, int cur, uint32_t vis, uint32_t pv, uint64_t rem, uint32_t ends) {
  uint64_t ex = rem & inc[cur];
  while (ex) { int e = __builtin_ctzll(ex); ex &= ex - 1; int w = other(e, cur); if (vis >> w & 1) continue;
    uint64_t r2 = rem & ~(1ULL << e); uint32_t pv2 = pv | (1u << w);
    if (ends >> w & 1) {
      uint32_t e2 = ends & ~((1u << y) | (1u << w));
      if (w == G_) { if (!(pv2 >> U_ & 1) && solveRest(r2, e2)) return true; }
      else if (growG(G_, (1u << G_) | (1u << U_), r2, e2)) return true;
    }
    if ((r2 & inc[w]) && growY(y, w, vis | (1u << w), pv2, r2, ends)) return true; }
  return false;
}
static bool adjm[16][16]; static int deg[16];
static void load(bool a[16][16]) {
  m = 0; for (int v = 0; v < n; v++) inc[v] = 0;
  for (int v = 0; v < n; v++) for (int w = v + 1; w < n; w++) if (a[v][w]) { ea[m] = v; eb[m] = w; inc[v] |= 1ULL << m; inc[w] |= 1ULL << m; m++; }
  memo.clear();
}
static uint32_t oddset(bool a[16][16]) { uint32_t s = 0; for (int v = 0; v < n; v++) { int d = 0; for (int w = 0; w < n; w++) d += a[v][w]; if (d & 1) s |= 1u << v; } return s; }
static bool avoid(bool a[16][16], int c, int x) {
  uint32_t ends = oddset(a); if (!(ends >> c & 1)) return false;
  uint64_t all = (m == 64) ? ~0ULL : ((1ULL << m) - 1);
  return growAvoid(c, c, (1u << c) | (1u << x), all, ends);
}
int main() {
  char line[256]; long long graphs = 0, skipped = 0, cand = 0;
  long long tests[2] = {0, 0}, e1[2] = {0, 0}, trnViol = 0;
  long long core[2] = {0, 0}, exT = 0, exW = 0, exF = 0, exI = 0, coreG[2] = {0, 0}, byd[2][20] = {{0}};
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    n = line[0] - 63; if (n > 16) { skipped++; continue; } memset(adjm, 0, sizeof adjm);
    { int k = 0; for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) { int by = 1 + k / 6, bi = 5 - k % 6; k++; if (((line[by] - 63) >> bi) & 1) adjm[i][j] = adjm[j][i] = true; } }
    int g = -1, nev = 0; for (int v = 0; v < n; v++) { deg[v] = 0; for (int w = 0; w < n; w++) deg[v] += adjm[v][w]; if (deg[v] > 0 && deg[v] % 2 == 0) { g = v; nev++; } }
    if (nev != 1) { skipped++; continue; }
    graphs++; if (graphs % 1000 == 0) { fprintf(stderr, "%lld graphs\n", graphs); }
    bool ind = false; if (deg[g] == 2) { int a = -1, b = -1; for (int w = 0; w < n; w++) if (adjm[g][w]) { if (a < 0) a = w; else b = w; } ind = !adjm[a][b]; }
    for (int u = 0; u < n; u++) { if (!adjm[g][u]) continue;
      bool K[16][16]; memcpy(K, adjm, sizeof K); K[g][u] = K[u][g] = false; load(K);
      G_ = g; U_ = u; uint32_t endsK = oddset(K); uint64_t allK = (m == 64) ? ~0ULL : ((1ULL << m) - 1);
      for (int y = 0; y < n; y++) { if (deg[y] % 2 == 0 || !adjm[y][u]) continue;
        for (int x = 0; x < n; x++) { if (x == y || x == u || deg[x] % 2 == 0 || adjm[x][y]) continue;
          cand++;
          if (!growAvoid(y, y, (1u << y) | (1u << x), allK, endsK)) continue;
          int a = adjm[g][y]; tests[a]++;
          bool te = growY(y, y, (1u << y) | (1u << x), 1u << y, allK, endsK);
          if (te) e1[a]++;
          else { printf("NOTRNE %s g=%d y=%d x=%d u=%d\n", line, g, y, x, u);
            bool sv[16][16]; memcpy(sv, adjm, sizeof sv); load(adjm); bool t = avoid(adjm, y, x); load(K);
            if (!t) { trnViol++; printf("TRN VIOLATION\n"); } }
          bool tight = true; for (int v = 0; v < n; v++) if (adjm[g][v] && v != x && v != y && !adjm[y][v]) tight = false;
          bool cw = false, gw = false; for (int w = 0; w < n; w++) if (adjm[y][w] && !adjm[x][w]) { if (w != u) cw = true; if (w != g) gw = true; }
          bool cn = false; for (int w = 0; w < n; w++) if (adjm[x][w] && adjm[y][w]) cn = true;
          if (!tight) exT++; else if (!cw) exW++; else if (!cn) exF++; else if (ind) exI++;
          else { core[a]++; byd[a][deg[g]]++; if (gw) coreG[a]++; }
        }
      }
    }
  }
  printf("graphs with exactly one even vertex=%lld (skipped %lld); candidates=%lld\n", graphs, skipped, cand);
  printf("TRN tests y!~g=%lld y~g=%lld; TRN_E holds y!~g=%lld y~g=%lld; TRN violations=%lld\n", tests[0], tests[1], e1[0], e1[1], trnViol);
  printf("core y!~g=%lld y~g=%lld; excluded (C2) %lld (C3) %lld (C4) %lld (C5) %lld\n", core[0], core[1], exT, exW, exF, exI);
  printf("core with an N-witness in G itself: y!~g=%lld y~g=%lld\n", coreG[0], coreG[1]);
  for (int a = 0; a < 2; a++) { printf("core y%sg by d(g):", a ? "~" : "!~"); for (int d = 0; d < 20; d++) if (byd[a][d]) printf(" %d:%lld", d, byd[a][d]); printf("\n"); }
}
