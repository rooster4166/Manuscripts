// mtok.cpp: k-token schedules for the triangle base (session claude/multi-token).
//
// Instance: J with one even vertex z, root r in N(z), w in N(z) - r, a perfect matching
// {a_i b_i} of J[N(z) - {r, w}] (k = d(z)/2 - 1 pairs), and an orientation: y_i in {a_i, b_i}
// gets a leaf l_i, x_i is the other.  M+ = J - zw - {z a_i, z b_i, a_i b_i} + {y_i l_i}.
// Tokens are the even vertices of the current graph K (initially w and the y_i).
// A tail i is live while the leaf edge y_i l_i is present; X(K) = {l_i, x_i : i live}.
// Moves (manuscript Definition 3.1; Lean `SteerK`):
//   (M) a token p moves along an edge pu to u, where u is odd, u not in X(K), and in K - pu the
//       vertex u is adjacent to no token other than p.  (If u is left isolated the token retires.)
//   (D) drop a live tail i whose y_i is odd: delete the leaf edge y_i l_i.
// A schedule ends when at most one token and at most one live tail are left (TERM=0).
// TERM=1: end as soon as at most one token is left (needs the multi-tail conjecture MT).
// TERM=2: as TERM=0, or at most one token and the live sets {l_i, x_i} form a sparse family
//         (every vertex has at most one neighbour in X(K)): separation_sparse.
// NODROP=1 disables (D).
// env SUPP=1 enables (S): a token p of degree 2 whose neighbours a, b are non-adjacent is suppressed
//   (K - pa - pb + ab; p is not y_i of a live tail, and ab is not x_i y_i).
//
// usage: mtok MODE BUDGET [TERM] [NODROP] [PRINT]
//   MODE g6: graph6 of J per line;  resid: graph6 of B = J - z with N(z) = {0..5} (gen_resid.py)
//   output per root: ROOT g6 r verdict (1 schedule found for some data/orientation, 0 none, 2 undecided)
//   with PRINT=1 also SCHED lines (one schedule per root) for mt_verify.py;
//   PRINT=2: SCHED lines for every data choice / orientation that has one.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <vector>
#include <string>
#include <unordered_set>
#include <array>
#include <algorithm>
typedef uint64_t u64;
static const int MAXV = 64;
static int N, K;                  // vertices of M+ (0..n-1 from J, n..n+k-1 leaves), tails
static int Ty[8], Tx[8], Tl[8];   // tails: y_i, x_i, l_i
static u64 adj[MAXV];
static long long nodes, budget; static int TERM, NODROP, SUPP;
struct H2 { size_t operator()(const std::array<u64,2>& a) const { return a[0] ^ (a[1] * 0x9E3779B97F4A7C15ULL); } };
static std::unordered_set<std::array<u64,2>, H2> failset;
struct Mv { int kind, p, u; };   // kind 0 = move p->u, 1 = drop tail p
static std::vector<Mv> mv, best;

static std::array<u64,2> key() {
  u64 h1 = 1469598103934665603ULL, h2 = 0x84222325CBF29CE4ULL;
  for (int v = 0; v < N; v++) { h1 = (h1 ^ adj[v]) * 1099511628211ULL; h2 = (h2 + adj[v]) * 0xC2B2AE3D27D4EB4FULL; h2 ^= h2 >> 29; }
  return {h1, h2};
}
static inline int deg(int v) { return __builtin_popcountll(adj[v]); }
static bool live(int i) { return adj[Ty[i]] >> Tl[i] & 1; }
static u64 Xmask() { u64 m = 0; for (int i = 0; i < K; i++) if (live(i)) m |= (1ULL << Tl[i]) | (1ULL << Tx[i]); return m; }
static u64 evens() { u64 m = 0; for (int v = 0; v < N; v++) { int d = deg(v); if (d > 0 && d % 2 == 0) m |= 1ULL << v; } return m; }
static bool terminal(u64 ev, u64 X) {
  if (__builtin_popcountll(ev) > 1) return false;
  int nl = 0; for (int i = 0; i < K; i++) if (live(i)) nl++;
  if (TERM == 1) return true;
  if (nl <= 1) return true;
  if (TERM == 2) {   // sparse family: every vertex has at most one neighbour in X
    for (int v = 0; v < N; v++) if (__builtin_popcountll(adj[v] & X) > 1) return false;
    return true;
  }
  return false;
}
static bool search() {
  u64 ev = evens(), X = Xmask();
  if (terminal(ev, X)) { best = mv; return true; }
  if (budget && ++nodes > budget) return false;
  std::array<u64,2> k = key();
  if (failset.count(k)) return false;
  // candidate moves, retirements first
  struct C { int kind, p, u, pri; };
  std::vector<C> cs;
  for (int p = 0; p < N; p++) if (ev >> p & 1) {
    u64 nb = adj[p];
    while (nb) {
      int u = __builtin_ctzll(nb); nb &= nb - 1;
      if (X >> u & 1) continue;
      if (deg(u) % 2 == 0) continue;            // u must be odd (u is not a token)
      u64 au = adj[u] & ~(1ULL << p);
      if (au & ev & ~(1ULL << p)) continue;      // u adjacent to another token after deleting pu
      int pri = (au == 0) ? 0 : 2;               // retirement first
      cs.push_back({0, p, u, pri});
    }
  }
  if (SUPP) for (int p = 0; p < N; p++) if ((ev >> p & 1) && deg(p) == 2) {
    // (S) suppress a token of degree 2 with non-adjacent neighbours a, b: K - pa - pb + ab
    int a = __builtin_ctzll(adj[p]), b = 63 - __builtin_clzll(adj[p]);
    if (adj[a] >> b & 1) continue;
    bool ok = true;
    for (int i = 0; i < K; i++) if (live(i)) {
      if (a == Tl[i] || b == Tl[i]) ok = false;                       // p = y_i: would move the tail
      if ((a == Tx[i] && b == Ty[i]) || (b == Tx[i] && a == Ty[i])) ok = false;  // new edge x_i y_i
    }
    if (ok) cs.push_back({2, p, a * 64 + b, 0});
  }
  if (!NODROP) for (int i = 0; i < K; i++) if (live(i) && deg(Ty[i]) % 2 == 1) {
    int pri = (deg(Ty[i]) == 1) ? 1 : 3;          // a drop that creates no token first
    cs.push_back({1, i, -1, pri});
  }
  std::stable_sort(cs.begin(), cs.end(), [](const C& a, const C& b) { return a.pri < b.pri; });
  for (auto& c : cs) {
    if (c.kind == 2) {
      int p = c.p, a = c.u / 64, b = c.u % 64;
      adj[p] = 0; adj[a] &= ~(1ULL << p); adj[b] &= ~(1ULL << p); adj[a] |= 1ULL << b; adj[b] |= 1ULL << a;
      mv.push_back({2, p, c.u});
      bool res = search();
      mv.pop_back();
      adj[a] &= ~(1ULL << b); adj[b] &= ~(1ULL << a); adj[p] = (1ULL << a) | (1ULL << b); adj[a] |= 1ULL << p; adj[b] |= 1ULL << p;
      if (res) return true;
      if (budget && nodes > budget) return false;
      continue;
    }
    int a, b;
    if (c.kind == 0) { a = c.p; b = c.u; } else { a = Ty[c.p]; b = Tl[c.p]; }
    adj[a] &= ~(1ULL << b); adj[b] &= ~(1ULL << a);
    mv.push_back({c.kind, c.kind == 0 ? c.p : c.p, c.u});
    bool res = search();
    mv.pop_back();
    adj[a] |= 1ULL << b; adj[b] |= 1ULL << a;
    if (res) return true;
    if (budget && nodes > budget) return false;
  }
  failset.insert(k);
  return false;
}

static bool parse_g6(const char* s, int& n, u64* A) {
  const unsigned char* p = (const unsigned char*)s;
  if (*p < 63 || *p > 126) return false;
  n = *p++ - 63; if (n > MAXV) return false;
  for (int i = 0; i < n; i++) A[i] = 0;
  int bit = 0, val = 0;
  for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
    if (bit == 0) { if (!*p) return false; val = *p++ - 63; bit = 6; }
    bit--;
    if (val >> bit & 1) { A[i] |= 1ULL << j; A[j] |= 1ULL << i; }
  }
  return true;
}

static void matchings(std::vector<int> vs, const u64* J, std::vector<std::pair<int,int>>& cur,
                      std::vector<std::vector<std::pair<int,int>>>& out) {
  if (vs.empty()) { out.push_back(cur); return; }
  int a = vs[0];
  for (size_t j = 1; j < vs.size(); j++) { int b = vs[j]; if (!(J[a] >> b & 1)) continue;
    std::vector<int> rest; for (size_t t = 1; t < vs.size(); t++) if (t != j) rest.push_back(vs[t]);
    cur.push_back({a, b}); matchings(rest, J, cur, out); cur.pop_back(); }
}

int main(int argc, char** argv) {
  const char* mode = argc > 1 ? argv[1] : "g6";
  budget = argc > 2 ? atoll(argv[2]) : 2000000;
  TERM = argc > 3 ? atoi(argv[3]) : 0;
  NODROP = argc > 4 ? atoi(argv[4]) : 0;
  int PRINT = argc > 5 ? atoi(argv[5]) : 0;
  SUPP = getenv("SUPP") ? atoi(getenv("SUPP")) : 0;
  char line[4096];
  long long roots = 0, rootsok = 0, rootsund = 0, datas = 0, datasok = 0, inst = 0, instok = 0, instund = 0;
  long long totnodes = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    char* tok = strtok(line, " \t"); if (!tok) continue;
    std::string g6 = tok;
    int n; u64 J[MAXV];
    if (!parse_g6(g6.c_str(), n, J)) continue;
    int z = -1;
    if (!strcmp(mode, "resid")) {   // B = J - z, N(z) = {0..5}; z gets index n
      if (n + 1 > MAXV) continue;
      z = n; J[z] = 0; for (int u = 0; u < 6; u++) { J[z] |= 1ULL << u; J[u] |= 1ULL << z; } n++;
    }
    int nev = 0;
    for (int v = 0; v < n; v++) { int d = __builtin_popcountll(J[v]); if (d % 2 == 0) { nev++; if (z < 0 || !strcmp(mode, "g6")) z = v; } }
    if (nev != 1) continue;
    int dz = __builtin_popcountll(J[z]);
    if (dz < 4 || dz % 2) continue;
    std::vector<int> U; for (int v = 0; v < n; v++) if (J[z] >> v & 1) U.push_back(v);
    for (int r : U) {
      if (__builtin_popcountll(J[r]) < 3) continue;
      int rv = 0; bool anydata = false, anyund = false;
      for (int w : U) { if (w == r) continue;
        std::vector<int> rest; for (int u : U) if (u != r && u != w) rest.push_back(u);
        std::vector<std::vector<std::pair<int,int>>> pms; std::vector<std::pair<int,int>> cur;
        matchings(rest, J, cur, pms);
        for (auto& pm : pms) {
          anydata = true; datas++; int dok = 0;
          int k = (int)pm.size();
          for (int o = 0; o < (1 << k); o++) {
            if (dok && PRINT < 2 && !getenv("ALLO")) break;
            // build M+
            N = n + k; K = k;
            for (int v = 0; v < N; v++) adj[v] = v < n ? J[v] : 0;
            auto del = [&](int a, int b) { adj[a] &= ~(1ULL << b); adj[b] &= ~(1ULL << a); };
            del(z, w);
            for (int i = 0; i < k; i++) { int a = pm[i].first, b = pm[i].second; del(z, a); del(z, b); del(a, b);
              Ty[i] = (o >> i & 1) ? a : b; Tx[i] = (o >> i & 1) ? b : a; Tl[i] = n + i;
              adj[Ty[i]] |= 1ULL << Tl[i]; adj[Tl[i]] |= 1ULL << Ty[i]; }
            failset.clear(); nodes = 0; mv.clear(); best.clear();
            bool res = search();
            totnodes += nodes;
            int verdict = res ? 1 : ((budget && nodes > budget) ? 2 : 0);
            inst++; if (verdict == 1) instok++; if (verdict == 2) { instund++; anyund = true; }
            if (verdict == 1) {
              if (!dok) datasok++;
              dok = 1;
              if (PRINT == 2 || (PRINT == 1 && rv != 1)) {
                printf("SCHED %s %d %d %d %d", g6.c_str(), (int)strcmp(mode, "resid") == 0, z, r, w);
                for (int i = 0; i < k; i++) printf(" %d,%d", Ty[i], Tx[i]);
                printf(" |");
                for (auto& m : best) { if (m.kind == 0) printf(" M%d-%d", m.p, m.u); else if (m.kind == 1) printf(" D%d", m.p); else printf(" S%d:%d-%d", m.p, m.u / 64, m.u % 64); }
                printf("\n");
              }
              rv = 1;
            }
          }
        }
      }
      if (!anydata) continue;
      roots++; if (rv == 1) rootsok++; else if (anyund) rootsund++;
      printf("ROOT %s r=%d verdict=%d\n", g6.c_str(), r, rv == 1 ? 1 : (anyund ? 2 : 0));
      fflush(stdout);
    }
  }
  printf("SUMMARY roots %lld scheduled %lld undecided %lld | data %lld with-schedule %lld | instances %lld scheduled %lld undecided %lld | nodes %lld\n",
         roots, rootsok, rootsund, datas, datasok, inst, instok, instund, totnodes);
}
