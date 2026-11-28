// indep.cpp (audit A34): independent checker for manuscripts/trn, orders 5 and 7.
// Does NOT use the authors' headers (lind.h, orc2.h, dec.h).
//  * Lovász decompositions are enumerated as TRANSITION SYSTEMS: at every vertex v the incident
//    edges are paired, with deg(v) mod 2 of them left as path ends; a pairing is accepted only if
//    it joins two different chains whose vertex sets meet only in v (so every chain stays a path).
//  * Fan's transfer is computed by a closed formula on transitions (not by sequential re-routing):
//    with the chain x_0=g, x_{j+1}=sigma(x_j) (sigma read off D'), phi(x_{j+1})=x_j:
//      at u: each transition {a,b} becomes {phi a, phi b}, and x_k u becomes u's end edge;
//      at x_j (1<=j<=k): the edge x_j p_j paired with x_j u becomes an end, and x_j's old end edge
//      is paired with x_j u;  at g: g's end edge is paired with gu.
//    The result is checked to be a Lovász decomposition of G.
//  * Checks Prop 3.1 (exact iff, and the vertex-set claims), Lemma 2.2(i), Lemma 3.2 (all
//    re-pairings), Lemma 4.2 and 4.3 (constructions verified), Lemma 4.4, and recomputes the
//    classification of Table 3 / Section 8 (exch, rot, rep, loc) and the hard core.
//  * Also records whether G itself has an N-witness (w in N(y), w not even, w !~ x).
// usage: indep [CORE] < graphs.g6
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <vector>
#include <map>
#include <string>
#include <algorithm>
#include <functional>
using namespace std;
typedef vector<int> Path;
typedef vector<Path> Dec;

static int N;                     // order
static bool A[32][32];            // adjacency of the current graph G

static bool parseg6(const char* s, int& n, bool adj[32][32]) {
  int len = strlen(s); while (len && (s[len-1]=='\n'||s[len-1]=='\r'||s[len-1]==' ')) len--;
  if (!len) return false;
  n = s[0] - 63; memset(adj, 0, sizeof(bool)*32*32);
  int k = 0; // bit index
  for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
    int byte = 1 + k / 6, bit = 5 - k % 6; k++;
    if (byte >= len) return false;
    if (((s[byte] - 63) >> bit) & 1) adj[i][j] = adj[j][i] = true;
  }
  return true;
}

// ---------------- transition-system enumerator ----------------
struct TEnum {
  int n, m; int ea[64], eb[64];
  vector<int> inc[32];       // incident edge ids
  int endEdge[32];           // for vertex v: chosen end edge or -1
  int matePos[32][32];       // matePos[v][i] = j (index into inc[v]) or -1 (end) ; -2 unassigned
  int cid[64]; uint32_t cmask[64];
  std::function<bool(const Dec&)> cb; bool stop;
  void build(bool adj[32][32], int nn) {
    n = nn; m = 0; for (int v = 0; v < n; v++) inc[v].clear();
    for (int a = 0; a < n; a++) for (int b = a+1; b < n; b++) if (adj[a][b]) { ea[m]=a; eb[m]=b; inc[a].push_back(m); inc[b].push_back(m); m++; }
  }
  int other(int e, int v) { return ea[e]==v ? eb[e] : ea[e]; }
  Dec extract() {
    Dec D; vector<char> used(m, 0);
    for (int v = 0; v < n; v++) for (int i = 0; i < (int)inc[v].size(); i++) if (matePos[v][i] == -1) {
      int e = inc[v][i]; if (used[e]) continue;
      Path p; p.push_back(v); int cur = v, ce = e;
      while (true) {
        used[ce] = 1; int w = other(ce, cur); p.push_back(w);
        int pos = find(inc[w].begin(), inc[w].end(), ce) - inc[w].begin();
        int mp = matePos[w][pos]; if (mp == -1) break;
        cur = w; ce = inc[w][mp];
      }
      D.push_back(p);
    }
    for (int e = 0; e < m; e++) if (!used[e]) { fprintf(stderr, "extract: cycle\n"); exit(1); }
    return D;
  }
  bool join(int e1, int e2, int v, vector<pair<int,uint32_t>>& undo, vector<int>& relab) {
    int c1 = cid[e1], c2 = cid[e2];
    if (c1 == c2) return false;
    if ((cmask[c1] & cmask[c2]) != (1u << v)) return false;
    undo.push_back({c1, cmask[c1]});
    for (int e = 0; e < m; e++) if (cid[e] == c2) { cid[e] = c1; relab.push_back(e); }
    cmask[c1] |= cmask[c2];
    return true;
  }
  void pairRest(int v, int vi) {
    if (stop) return;
    int d = inc[v].size(); int i = 0; while (i < d && matePos[v][i] != -2) i++;
    if (i == d) { rec(vi + 1); return; }
    for (int j = i + 1; j < d && !stop; j++) if (matePos[v][j] == -2) {
      vector<pair<int,uint32_t>> undo; vector<int> relab;
      int c2 = cid[inc[v][j]];
      if (!join(inc[v][i], inc[v][j], v, undo, relab)) continue;
      matePos[v][i] = j; matePos[v][j] = i;
      pairRest(v, vi);
      matePos[v][i] = matePos[v][j] = -2;
      for (int e : relab) cid[e] = c2; cmask[undo[0].first] = undo[0].second;
    }
  }
  void rec(int v) {
    if (stop) return;
    if (v == n) { Dec D = extract(); if (cb(D)) stop = true; return; }
    int d = inc[v].size();
    if (d == 0) { rec(v + 1); return; }
    for (int i = 0; i < d; i++) matePos[v][i] = -2;
    if (d % 2 == 0) pairRest(v, v);
    else for (int i0 = 0; i0 < d && !stop; i0++) { matePos[v][i0] = -1; pairRest(v, v); matePos[v][i0] = -2; }
  }
  // enumerate all Lovász decompositions (b = deg mod 2) of the graph
  void run(std::function<bool(const Dec&)> f) {
    cb = f; stop = false;
    for (int e = 0; e < m; e++) { cid[e] = e; cmask[e] = (1u << ea[e]) | (1u << eb[e]); }
    rec(0);
  }
};

// ---------------- helpers ----------------
static bool inP(const Path& p, int v) { return find(p.begin(), p.end(), v) != p.end(); }
static uint32_t vmask(const Path& p) { uint32_t s = 0; for (int v : p) s |= 1u << v; return s; }
static int endIdx(const Dec& D, int v) { int r = -1, c = 0; for (int i = 0; i < (int)D.size(); i++) { if (D[i].front()==v) { r=i; c++; } if (D[i].back()==v) { r=i; c++; } } return c == 1 ? r : -1; }
static Path fromEnd(const Path& p, int v) { Path q = p; if (q.front() != v) reverse(q.begin(), q.end()); return q; }

// check D is a Lovász decomposition of graph adj (n vertices)
static bool isLovasz(const Dec& D, bool adj[32][32], int n) {
  static int used[32][32]; memset(used, 0, sizeof used); int ends[32] = {0};
  for (auto& p : D) {
    if (p.size() < 2) return false; uint32_t s = 0;
    for (int v : p) { if (s >> v & 1) return false; s |= 1u << v; }
    for (size_t i = 0; i + 1 < p.size(); i++) { int a = p[i], b = p[i+1]; if (!adj[a][b] || used[a][b]) return false; used[a][b] = used[b][a] = 1; }
    ends[p.front()]++; ends[p.back()]++;
  }
  for (int a = 0; a < n; a++) { int d = 0; for (int b = 0; b < n; b++) { if (adj[a][b] && !used[a][b]) return false; d += adj[a][b]; } if (ends[a] != d % 2) return false; }
  return true;
}

// sigma(v) on D (path ending at v contains u): the vertex before u reading from v; -1 if path avoids u
static int sigma(const Dec& D, int v, int u) {
  int i = endIdx(D, v); if (i < 0) { fprintf(stderr, "sigma: no end at %d\n", v); exit(1); }
  Path p = fromEnd(D[i], v); for (size_t k = 0; k < p.size(); k++) if (p[k] == u) return k == 0 ? -3 : p[k-1];
  return -1;
}
static vector<int> chainOf(const Dec& D, int g, int u) {
  vector<int> ch{g};
  while (true) { int s = sigma(D, ch.back(), u); if (s == -1) break; if (s == -3) { fprintf(stderr, "u is an end?\n"); exit(1); }
    if (find(ch.begin(), ch.end(), s) != ch.end()) { fprintf(stderr, "chain repeats (Lemma 2.2(i) fails)\n"); exit(1); }
    ch.push_back(s); }
  return ch;
}

// Fan's transfer by the transition formula. D: decomposition of K = G - gu. Returns decomposition of G.
static bool isLovasz(const Dec& D, bool adj[32][32], int n);
static Dec transferFormula0(const Dec& D, int g, int u, const vector<int>& ch);
static Dec transferFormula(const Dec& D, int g, int u, const vector<int>& ch) {
  Dec R = transferFormula0(D, g, u, ch);
  if (!isLovasz(R, A, N)) { fprintf(stderr, "transfer formula gave a non-decomposition\n"); exit(1); }
  return R;
}
static Dec transferFormula0(const Dec& D, int g, int u, const vector<int>& ch) {
  // transitions T[v][a] = b (-1 end, -2 none) over neighbours
  static int T[32][32];
  for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) T[a][b] = -2;
  for (auto& p : D) { int L = p.size() - 1;
    T[p[0]][p[1]] = -1; T[p[L]][p[L-1]] = -1;
    for (int i = 1; i < L; i++) { T[p[i]][p[i-1]] = p[i+1]; T[p[i]][p[i+1]] = p[i-1]; } }
  int k = ch.size() - 1;
  int phi[32]; for (int v = 0; v < N; v++) phi[v] = v; for (int j = 0; j < k; j++) phi[ch[j+1]] = ch[j];
  static int T2[32][32]; memcpy(T2, T, sizeof T);
  // at u
  for (int a = 0; a < N; a++) T2[u][a] = -2;
  for (int a = 0; a < N; a++) if (T[u][a] >= 0) T2[u][phi[a]] = phi[T[u][a]];
  T2[u][ch[k]] = -1;
  // at x_j, 1<=j<=k
  for (int j = 1; j <= k; j++) { int xj = ch[j]; int pj = T[xj][u]; int qj = -1;
    for (int b = 0; b < N; b++) if (T[xj][b] == -1) qj = b;
    if (pj < 0 || qj < 0) { fprintf(stderr, "formula: bad x_j\n"); exit(1); }
    T2[xj][pj] = -1; T2[xj][qj] = u; T2[xj][u] = qj; }
  { int q0 = -1; for (int b = 0; b < N; b++) if (T[g][b] == -1) q0 = b; T2[g][q0] = u; T2[g][u] = q0; }
  // extract
  Dec R; static bool usedE[32][32]; memset(usedE, 0, sizeof usedE);
  for (int v = 0; v < N; v++) for (int a = 0; a < N; a++) if (T2[v][a] == -1 && !usedE[v][a]) {
    Path p{v}; int prev = v, cur = a; usedE[v][a] = usedE[a][v] = true;
    for (int guard = 0; guard < 64; guard++) { p.push_back(cur); int nx = T2[cur][prev]; if (nx == -1) break;
      if (nx < 0) { fprintf(stderr, "formula: broken\n"); exit(1); }
      usedE[cur][nx] = usedE[nx][cur] = true; prev = cur; cur = nx; }
    R.push_back(p);
  }
  return R;
}

// existence of a Lovász decomposition of graph adj with the path ending at c avoiding mask F
static bool avoidExists(bool adj[32][32], int n, int c, uint32_t F) {
  TEnum E; E.build(adj, n); bool ok = false;
  E.run([&](const Dec& D) { int i = endIdx(D, c); if (i >= 0 && !(vmask(D[i]) & F)) { ok = true; return true; } return false; });
  return ok;
}

// ---------------- main ----------------
int main(int argc, char** argv) {
  bool coreOnly = argc > 1 && string(argv[1]) == "CORE";
  char line[512];
  long long tests[2] = {0,0}, nDtot = 0, viol31 = 0, violSub = 0, violHalves = 0, viol42 = 0, viol43 = 0, viol44 = 0;
  long long nDouble = 0, n42 = 0, n43a = 0, n43b = 0, n44 = 0, nRepairings = 0;
  map<string, long long> agg;
  long long gwitCoreTests = 0, coreTests = 0;
  vector<string> triples;  // g6 g y x u nD nAv nGood, as chainlist prints
  vector<string> residuals;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    if (!parseg6(line, N, A)) continue;
    int ev = -1, nev = 0; for (int v = 0; v < N; v++) { int d = 0; for (int w = 0; w < N; w++) d += A[v][w]; if (d > 0 && d % 2 == 0) { ev = v; nev++; } }
    if (nev != 1) continue;
    int g = ev; int deg[32]; for (int v = 0; v < N; v++) { deg[v] = 0; for (int w = 0; w < N; w++) deg[v] += A[v][w]; }
    for (int u = 0; u < N; u++) { if (!A[g][u]) continue;
      bool K[32][32]; memcpy(K, A, sizeof K); K[g][u] = K[u][g] = false;
      // all Lovász decompositions of K, once per u
      vector<Dec> all; TEnum E; E.build(K, N); E.run([&](const Dec& D) { all.push_back(D); return false; });
      for (auto& D : all) if (!isLovasz(D, K, N)) { fprintf(stderr, "enumerator produced a non-decomposition\n"); return 1; }
      for (int y = 0; y < N; y++) { if (deg[y] % 2 == 0 || !A[y][u]) continue;
        for (int x = 0; x < N; x++) { if (x == y || x == u || deg[x] % 2 == 0 || A[x][y]) continue;
          // core properties (Definition 5.1), and G-witness (Conjecture N hypothesis on G itself)
          bool tight = true; for (int v = 0; v < N; v++) if (A[g][v] && v != x && v != y && !A[y][v]) tight = false;
          bool cwit = false, gwit = false; for (int w = 0; w < N; w++) if (A[y][w] && !A[x][w]) { if (w != u) cwit = true; if (w != g) gwit = true; }
          bool cn = false; for (int w = 0; w < N; w++) if (A[x][w] && A[y][w]) cn = true;
          bool ind = false; if (deg[g] == 2) { int a = -1, b = -1; for (int w = 0; w < N; w++) if (A[g][w]) { if (a < 0) a = w; else b = w; } ind = !A[a][b]; }
          bool core = tight && cwit && cn && !ind;
          if (coreOnly && !core) continue;
          long long nD = 0, nAv = 0, nGood = 0;
          vector<const Dec*> bads;
          for (auto& D : all) {
            int qi = endIdx(D, y); if (inP(D[qi], x)) continue;   // good D' only
            nD++;
            vector<int> ch = chainOf(D, g, u);
            Dec R = transferFormula(D, g, u, ch);
            if (!isLovasz(R, A, N)) { fprintf(stderr, "transfer formula gave a non-decomposition: %s\n", line); return 1; }
            int ri = endIdx(R, y); bool good = !inP(R[ri], x);
            bool hitY = inP(ch, y); if (!hitY) nAv++; if (good) nGood++;
            { // a path of D' re-routed twice (both ends are chain vertices x_i, x_j with i,j < k)
              int k = ch.size() - 1; bool dbl = false;
              for (int a = 0; a < k && !dbl; a++) for (int b = a + 1; b < k; b++) if (endIdx(D, ch[a]) == endIdx(D, ch[b])) dbl = true;
              if (dbl) nDouble++; }
            // ---- Proposition 3.1 ----
            Path Q = fromEnd(D[qi], y);
            int py = -1; for (int i = 0; i < (int)D.size(); i++) for (size_t j = 0; j + 1 < D[i].size(); j++) if ((D[i][j]==y&&D[i][j+1]==u)||(D[i][j]==u&&D[i][j+1]==y)) py = i;
            bool pred;
            if (py == qi) {
              if (hitY) violSub++;
              pred = true;
              if (vmask(R[ri]) & ~(vmask(Q) | (1u << u))) violSub++;
            } else {
              Path P = D[py]; size_t yi = find(P.begin(), P.end(), y) - P.begin();
              if (!(yi + 1 < P.size() && P[yi+1] == u)) reverse(P.begin(), P.end());
              int e = P.front();
              bool hitE = inP(ch, e);
              if (hitE != hitY) violSub++;
              if (hitE) {
                size_t ie = find(ch.begin(), ch.end(), e) - ch.begin();
                if (!(ie + 1 < ch.size() && ch[ie+1] == y)) violSub++;
                if (vmask(R[ri]) != vmask(P)) violSub++;
                bool eok = (e == g) || K[e][u]; if (!eok) violSub++;
                pred = !inP(P, x);
              } else {
                if (vmask(R[ri]) & ~(vmask(Q) | (1u << u))) violSub++;
                pred = true;
              }
            }
            if (pred != good) viol31++;
            // ---- Lemma 3.2: every re-pairing of the halves at u ----
            {
              vector<Path> halves; vector<int> owner; vector<int> rest;
              for (int i = 0; i < (int)D.size(); i++) { if (!inP(D[i], u)) { rest.push_back(i); continue; }
                const Path& p = D[i]; size_t k = find(p.begin(), p.end(), u) - p.begin();
                Path h1(p.begin(), p.begin() + k + 1); Path h2(p.rbegin(), p.rbegin() + (p.size() - k)); halves.push_back(h1); halves.push_back(h2); }
              int H = halves.size(); vector<int> mate(H, -1);
              std::function<void(int)> rp = [&](int i) {
                while (i < H && mate[i] >= 0) i++;
                if (i == H) {
                  Dec D2; for (int r : rest) D2.push_back(D[r]);
                  for (int a = 0; a < H; a++) if (mate[a] > a) { Path p = halves[a]; for (int t = (int)halves[mate[a]].size() - 2; t >= 0; t--) p.push_back(halves[mate[a]][t]); D2.push_back(p); }
                  nRepairings++;
                  if (!isLovasz(D2, K, N)) { violHalves++; return; }
                  vector<int> ch2 = chainOf(D2, g, u); if (ch2 != ch) violHalves++;
                  int q2 = endIdx(D2, y); if (!inP(D[qi], u) && vmask(D2[q2]) != vmask(D[qi])) violHalves++;
                  if (py != qi && inP(ch, y)) {
                    // e-half and its new partner
                    Path P = D[py]; size_t yi = find(P.begin(), P.end(), y) - P.begin(); if (!(yi + 1 < P.size() && P[yi+1] == u)) reverse(P.begin(), P.end());
                    int he = -1; for (int a = 0; a < H; a++) if (halves[a].front() == P.front() && inP(halves[a], y)) he = a;
                    Dec R2 = transferFormula(D2, g, u, ch2); int r2 = endIdx(R2, y);
                    if (vmask(R2[r2]) != (vmask(halves[he]) | vmask(halves[mate[he]]))) violHalves++;
                  }
                  return;
                }
                for (int j = i + 1; j < H; j++) if (mate[j] < 0 && (vmask(halves[i]) & vmask(halves[j])) == (1u << u)) { mate[i] = j; mate[j] = i; rp(i + 1); mate[i] = mate[j] = -1; }
              };
              rp(0);
            }
            if (!good) bads.push_back(&D);
          }
          if (!nD) continue;
          int adj = A[g][y]; tests[adj]++; nDtot += nD;
          if (core) { coreTests++; if (gwit) gwitCoreTests++; }
          char buf[256]; snprintf(buf, sizeof buf, "%s %d %d %d %d %lld %lld %lld", line, g, y, x, u, nD, nAv, nGood); triples.push_back(buf);
          bool tri2 = deg[g] == 2 && !ind;
          // ---- classification of bad D' ----
          for (const Dec* Dp : bads) {
            const Dec& D = *Dp; vector<int> ch = chainOf(D, g, u);
            int i = find(ch.begin(), ch.end(), y) - ch.begin();
            int qi = endIdx(D, y); Path Q = fromEnd(D[qi], y); bool qu = inP(Q, u);
            int py = -1; for (int t = 0; t < (int)D.size(); t++) for (size_t j = 0; j + 1 < D[t].size(); j++) if ((D[t][j]==y&&D[t][j+1]==u)||(D[t][j]==u&&D[t][j+1]==y)) py = t;
            Path P = D[py]; size_t yi = find(P.begin(), P.end(), y) - P.begin(); if (!(yi + 1 < P.size() && P[yi+1] == u)) { reverse(P.begin(), P.end()); yi = find(P.begin(), P.end(), y) - P.begin(); }
            int e = P.front(), f = P.back();
            bool sideE = false; for (size_t j = 0; j < yi; j++) if (P[j] == x) sideE = true;
            // exchange (Lemma 4.2): hypothesis and construction
            bool exch = !qu && (vmask(P) & vmask(Q)) == (1u << y);
            if (exch) { n42++;
              Dec R = transferFormula(D, g, u, ch);
              // R contains Q'(y)+yu and the re-routed P_y; glue
              int a1 = endIdx(R, u), a2 = endIdx(R, y); if (a1 >= 0 && vmask(R[a1]) != (vmask(Q) | (1u << u))) a1 = -1; if (a2 >= 0 && vmask(R[a2]) != vmask(P)) a2 = -1;
              if (a1 < 0 || a2 < 0) viol42++;
              else { Dec R3; for (int t = 0; t < (int)R.size(); t++) if (t != a1 && t != a2) R3.push_back(R[t]);
                R3.push_back(Path{y, u}); Path pp = fromEnd(R[a2], y); reverse(pp.begin(), pp.end()); for (size_t t = 1; t < Q.size(); t++) pp.push_back(Q[t]); R3.push_back(pp);
                int r3 = endIdx(R3, y); if (!isLovasz(R3, A, N) || R3[r3].size() != 2) viol42++; }
            }
            // rotations (Lemma 4.3) when e = g, u notin Q'(y)
            if (e == g && !qu) {
              Path S(P.begin() + 1, P.begin() + yi); // between g and y (S a)
              Path gSa(P.begin(), P.begin() + yi); Path uRf(P.begin() + yi + 1, P.end()); Path bTq(Q.begin() + 1, Q.end());
              auto mk = [&](const Dec& D, int skip1, int skip2, const Path& p1, const Path& p2) { Dec D2; for (int t = 0; t < (int)D.size(); t++) if (t != skip1 && t != skip2) D2.push_back(D[t]); D2.push_back(p1); D2.push_back(p2); return D2; };
              if (!(vmask(gSa) & vmask(bTq)) && !inP(uRf, x)) { n43a++;
                Path p1 = gSa; p1.push_back(y); for (int v : bTq) p1.push_back(v); Path p2{y}; for (int v : uRf) p2.push_back(v);
                Dec D2 = mk(D, py, qi, p1, p2);
                if (!isLovasz(D2, K, N)) viol43++; else { vector<int> c2 = chainOf(D2, g, u); Dec R2 = transferFormula(D2, g, u, c2); int r = endIdx(R2, y);
                  if (c2.size() != 1 || R2[r] != p2 && R2[r] != Path(p2.rbegin(), p2.rend())) viol43++; } }
              if (!(vmask(uRf) & vmask(bTq)) && !inP(gSa, x)) { n43b++;
                Path p1{y}; for (int t = (int)gSa.size() - 1; t >= 0; t--) p1.push_back(gSa[t]);
                Path p2(uRf.rbegin(), uRf.rend()); p2.push_back(y); for (int v : bTq) p2.push_back(v);
                Dec D2 = mk(D, py, qi, p1, p2);
                if (!isLovasz(D2, K, N)) viol43++; else { vector<int> c2 = chainOf(D2, g, u); Dec R2 = transferFormula(D2, g, u, c2); int r = endIdx(R2, y);
                  Path want = p1; want.push_back(u); if (c2.size() != 1 || (R2[r] != want && R2[r] != Path(want.rbegin(), want.rend()))) viol43++; } }
            }
            // rot: any rotation at y along any path through y (y interior), then plain Fan
            bool rot = false;
            for (int t = 0; t < (int)D.size() && !rot; t++) { if (t == qi) continue; const Path& Rp = D[t]; size_t k = find(Rp.begin(), Rp.end(), y) - Rp.begin();
              if (k == Rp.size() || k == 0 || k + 1 == Rp.size()) continue;
              for (int side = 0; side < 2 && !rot; side++) {
                Path half, oth; if (side == 0) { half.assign(Rp.begin() + k, Rp.end()); oth.assign(Rp.begin(), Rp.begin() + k + 1); }
                else { half.assign(Rp.rbegin() + (Rp.size() - 1 - k), Rp.rend()); oth.assign(Rp.rbegin(), Rp.rbegin() + (Rp.size() - k)); }
                Path J = oth; for (size_t s = 1; s < Q.size(); s++) J.push_back(Q[s]);
                if (__builtin_popcount(vmask(J)) != (int)J.size() || inP(half, x)) continue;
                Dec D2; for (int s = 0; s < (int)D.size(); s++) if (s != t && s != qi) D2.push_back(D[s]); D2.push_back(half); D2.push_back(J);
                if (!isLovasz(D2, K, N)) { fprintf(stderr, "rot invalid\n"); return 1; }
                vector<int> c2 = chainOf(D2, g, u); Dec R2 = transferFormula(D2, g, u, c2); if (!inP(R2[endIdx(R2, y)], x)) rot = true; } }
            // rep: any re-pairing at u giving a good D'' with a good transfer
            bool rep = false;
            { vector<Path> halves; vector<int> rest;
              for (int t = 0; t < (int)D.size(); t++) { if (!inP(D[t], u)) { rest.push_back(t); continue; } const Path& p = D[t]; size_t k = find(p.begin(), p.end(), u) - p.begin();
                halves.push_back(Path(p.begin(), p.begin() + k + 1)); halves.push_back(Path(p.rbegin(), p.rbegin() + (p.size() - k))); }
              int H = halves.size(); vector<int> mate(H, -1);
              std::function<void(int)> rp = [&](int a) { if (rep) return; while (a < H && mate[a] >= 0) a++;
                if (a == H) { Dec D2; for (int r : rest) D2.push_back(D[r]);
                  for (int b = 0; b < H; b++) if (mate[b] > b) { Path p = halves[b]; for (int s = (int)halves[mate[b]].size() - 2; s >= 0; s--) p.push_back(halves[mate[b]][s]); D2.push_back(p); }
                  if (inP(D2[endIdx(D2, y)], x)) return;
                  vector<int> c2 = chainOf(D2, g, u); Dec R2 = transferFormula(D2, g, u, c2); if (!inP(R2[endIdx(R2, y)], x)) rep = true; return; }
                for (int b = a + 1; b < H; b++) if (mate[b] < 0 && (vmask(halves[a]) & vmask(halves[b])) == (1u << u)) { mate[a] = b; mate[b] = a; rp(a + 1); mate[a] = mate[b] = -1; } };
              rp(0);
              // Lemma 4.4 sufficiency: if its hypothesis holds then rep must be true; and rep with x on the e-half is impossible
              if (rep && sideE) viol44++;
            }
            // loc: re-decompose union of chain paths + Q'(y) + gu, y's path avoiding x
            bool U[32][32]; memset(U, 0, sizeof U); vector<int> sel;
            for (int v : ch) { int t = endIdx(D, v); if (find(sel.begin(), sel.end(), t) == sel.end()) sel.push_back(t); }
            if (find(sel.begin(), sel.end(), qi) == sel.end()) sel.push_back(qi);
            for (int t : sel) for (size_t s = 0; s + 1 < D[t].size(); s++) U[D[t][s]][D[t][s+1]] = U[D[t][s+1]][D[t][s]] = true;
            U[g][u] = U[u][g] = true;
            bool loc = avoidExists(U, N, y, 1u << x);
            bool hard = (i == 1) && !qu;
            char key[200]; snprintf(key, sizeof key, "adj=%d i=%s side=%c qu=%d wit=%d tri2=%d gwit=%d hard=%d | exch=%d rot=%d rep=%d loc=%d",
              adj, i == 1 ? "1" : ">1", sideE ? 'E' : 'P', (int)qu, (int)cwit, (int)tri2, (int)gwit, (int)hard, (int)exch, (int)rot, (int)rep, (int)loc);
            agg[key]++;
            if (!exch && !rot && !rep && !loc && core) { string s = string(line) + " g=" + to_string(g) + " y=" + to_string(y) + " x=" + to_string(x) + " u=" + to_string(u) + " gwit=" + to_string(gwit) + " D'=";
              for (auto& p : D) { for (int v : p) s += to_string(v); s += " "; } residuals.push_back(s); }
          }
        }
      }
    }
  }
  FILE* tf = fopen(getenv("TRIPLES") ? getenv("TRIPLES") : "/dev/null", "w"); sort(triples.begin(), triples.end()); for (auto& s : triples) fprintf(tf, "%s\n", s.c_str()); fclose(tf);
  FILE* rf = fopen(getenv("RESID") ? getenv("RESID") : "/dev/null", "w"); for (auto& s : residuals) fprintf(rf, "%s\n", s.c_str()); fclose(rf);
  for (auto& kv : agg) printf("  %-110s %lld\n", kv.first.c_str(), kv.second);
  printf("tests y!~g=%lld y~g=%lld, good D'=%lld; core tests=%lld of which G has an N-witness=%lld\n", tests[0], tests[1], nDtot, coreTests, gwitCoreTests);
  printf("Prop3.1 iff violations=%lld, Prop3.1 sub-claim violations=%lld; Lemma3.2: re-pairings checked=%lld violations=%lld\n", viol31, violSub, nRepairings, violHalves);
  printf("good D' with a path re-routed at both ends: %lld\n", nDouble); printf("Lemma4.2 applications=%lld violations=%lld; Lemma4.3 alpha=%lld beta=%lld violations=%lld; rep with x on e-half=%lld\n", n42, viol42, n43a, n43b, viol43, viol44);
}
