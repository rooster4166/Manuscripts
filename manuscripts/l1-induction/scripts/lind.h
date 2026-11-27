// lind.h: shared graph utilities and the exact avoidance oracle for the l1-induction experiments.
// The oracle core is a port of manuscripts/l1star/scripts/l1s.c (itself the validated oracle of
// prescribed-end/pee.c): Q_c is grown first from c never entering the forbidden set; the rest is an
// exact search for a path decomposition with prescribed end counts (failure memo, parity, degree and
// component pruning).  End counts are always b(v) = deg(v) mod 2 (Lovász decompositions).
#pragma once
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <string>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <algorithm>

typedef unsigned __int128 u128;
static const int MAXV = 32;

struct Gr {
  int N = 0;
  uint32_t adj[MAXV];
  Gr() { memset(adj, 0, sizeof adj); }
  int deg(int v) const { return __builtin_popcount(adj[v]); }
  bool has(int u, int v) const { return adj[u] >> v & 1; }
  void add(int u, int v) { adj[u] |= 1u << v; adj[v] |= 1u << u; }
  void del(int u, int v) { adj[u] &= ~(1u << v); adj[v] &= ~(1u << u); }
  int nedges() const { int s = 0; for (int v = 0; v < N; v++) s += deg(v); return s / 2; }
  uint32_t evens() const { uint32_t e = 0; for (int v = 0; v < N; v++) { int d = deg(v); if (d > 0 && !(d & 1)) e |= 1u << v; } return e; }
  uint32_t comp(int c) const { uint32_t s = 1u << c, f = s; while (f) { int x = __builtin_ctz(f); f &= f - 1; uint32_t nx = adj[x] & ~s; s |= nx; f |= nx; } return s; }
  void restrict_to(uint32_t S) { for (int v = 0; v < N; v++) { if (!(S >> v & 1)) adj[v] = 0; else adj[v] &= S; } }
  std::string key() const { return std::string((const char*)adj, N * 4); }
};

static bool parse_g6(const char* s, Gr& G) {
  int len = (int)strlen(s);
  while (len && (s[len - 1] == '\n' || s[len - 1] == '\r')) len--;
  if (len == 0) return false;
  int p = 0; int n = s[p++] - 63;
  if (n > MAXV || n < 0) return false;
  G = Gr(); G.N = n;
  int bit = 0, val = 0;
  for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
    if (bit == 0) { if (p >= len) return false; val = s[p++] - 63; bit = 6; }
    bit--;
    if (val >> bit & 1) G.add(i, j);
  }
  return true;
}

// ---------------- exact oracle ----------------
namespace orc {
static int n, m;
static int eu[128], ev[128];
static u128 inc[MAXV];
static int dg0[MAXV];
typedef struct { u128 mask; uint32_t b; } key_t2;
static key_t2* tab; static unsigned char* used; static size_t cap, cnt;
static void hreset() {
  if (!tab) { cap = 1u << 16; tab = (key_t2*)malloc(cap * sizeof(key_t2)); used = (unsigned char*)calloc(cap, 1); }
  else if (cnt) memset(used, 0, cap);
  cnt = 0;
}
static size_t hh(u128 a, uint32_t b) {
  uint64_t lo = (uint64_t)a, hi = (uint64_t)(a >> 64);
  uint64_t x = lo * 0x9E3779B97F4A7C15ULL ^ (hi * 0xC2B2AE3D27D4EB4FULL) ^ ((uint64_t)b * 0x632BE59BD9B4E019ULL);
  x ^= x >> 31; x *= 0xBF58476D1CE4E5B9ULL; x ^= x >> 29;
  return (size_t)x;
}
static int hfind(u128 a, uint32_t b) {
  size_t i = hh(a, b) & (cap - 1);
  while (used[i]) { if (tab[i].mask == a && tab[i].b == b) return 1; i = (i + 1) & (cap - 1); }
  return 0;
}
static void hadd(u128 a, uint32_t b);
static void hgrow() {
  size_t oc = cap; key_t2* ot = tab; unsigned char* ou = used;
  cap *= 2; tab = (key_t2*)malloc(cap * sizeof(key_t2)); used = (unsigned char*)calloc(cap, 1); cnt = 0;
  for (size_t i = 0; i < oc; i++) if (ou[i]) hadd(ot[i].mask, ot[i].b);
  free(ot); free(ou);
}
static void hadd(u128 a, uint32_t b) {
  if (cnt * 2 > cap) hgrow();
  size_t i = hh(a, b) & (cap - 1);
  while (used[i]) i = (i + 1) & (cap - 1);
  used[i] = 1; tab[i].mask = a; tab[i].b = b; cnt++;
}
static u128 rem; static uint32_t bm;
static unsigned long long budget = 0, nodes; static int aborted;
static int popc(u128 x) { return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64)); }
static int ctz128(u128 x) { uint64_t lo = (uint64_t)x; return lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll((uint64_t)(x >> 64)); }
static int degr(int v) { return popc(rem & inc[v]); }
static int solve();
static int extend(int a, int cur, uint32_t vis) {
  if (aborted) return 0;
  if (budget && ++nodes > budget) { aborted = 1; return 0; }
  u128 ex = rem & inc[cur];
  while (ex) {
    int e = ctz128(ex); ex &= ex - 1;
    int w = eu[e] == cur ? ev[e] : eu[e];
    if (vis >> w & 1) continue;
    rem &= ~((u128)1 << e);
    if (bm >> w & 1) {
      uint32_t sb = bm; bm &= ~((1u << a) | (1u << w));
      int ok = solve(); bm = sb;
      if (ok) { rem |= (u128)1 << e; return 1; }
    }
    if (rem & inc[w]) { if (extend(a, w, vis | (1u << w))) { rem |= (u128)1 << e; return 1; } }
    rem |= (u128)1 << e;
  }
  return 0;
}
static int prune_ok(int* bestp) {
  int best = -1, bd = 999;
  int P = __builtin_popcount(bm) / 2, act = 0;
  for (int v = 0; v < n; v++) {
    int d = degr(v); if (d) act++;
    int bv = bm >> v & 1;
    if (d > 2 * P - bv) return 0;
    if (bv && d < bd) { bd = d; best = v; }
  }
  if (popc(rem) > P * (act - 1)) return 0;
  uint32_t seen = 0;
  for (int v = 0; v < n; v++) {
    if ((seen >> v & 1) || !(rem & inc[v])) continue;
    uint32_t comp = 1u << v, frontier = 1u << v;
    while (frontier) {
      int x = __builtin_ctz(frontier); frontier &= frontier - 1;
      u128 ex = rem & inc[x];
      while (ex) { int e = ctz128(ex); ex &= ex - 1; int y = eu[e] == x ? ev[e] : eu[e];
        if (!(comp >> y & 1)) { comp |= 1u << y; frontier |= 1u << y; } }
    }
    seen |= comp;
    if (!(comp & bm)) return 0;
  }
  if (bestp) *bestp = best;
  return 1;
}
static int solve() {
  if (rem == 0) return bm == 0;
  if (bm == 0) return 0;
  int best; if (!prune_ok(&best)) return 0;
  if (hfind(rem, bm)) return 0;
  int r = extend(best, best, 1u << best);
  if (!r && !aborted) hadd(rem, bm);
  return r;
}
static void load(const Gr& G) {
  n = G.N; m = 0;
  for (int v = 0; v < n; v++) { inc[v] = 0; dg0[v] = 0; }
  for (int v = 0; v < n; v++) for (int w = v + 1; w < n; w++) if (G.has(v, w)) {
    eu[m] = v; ev[m] = w; inc[v] |= (u128)1 << m; inc[w] |= (u128)1 << m; dg0[v]++; dg0[w]++; m++;
  }
}
// 1: some Lovász decomposition (b = deg mod 2 everywhere) has Q_c avoiding the mask f; 0: none;
// 2: budget hit; -1: c not odd.
static int avoid(const Gr& G, int c, uint32_t f) {
  load(G);
  hreset(); nodes = 0; aborted = 0;
  rem = (m == 128) ? ~(u128)0 : (((u128)1 << m) - 1);
  bm = 0; for (int v = 0; v < n; v++) if (dg0[v] & 1) bm |= 1u << v;
  if (!(bm >> c & 1)) return -1;
  if (f >> c & 1) return 0;
  if (!prune_ok(NULL)) return 0;
  int ok = extend(c, c, (1u << c) | f);
  if (aborted) return 2;
  return ok;
}
// decomposable with b = deg mod 2 at all vertices (no avoidance)
static int lovasz(const Gr& G) {
  load(G); hreset(); nodes = 0; aborted = 0;
  rem = (m == 128) ? ~(u128)0 : (((u128)1 << m) - 1);
  bm = 0; for (int v = 0; v < n; v++) if (dg0[v] & 1) bm |= 1u << v;
  return solve();
}
}  // namespace orc

static inline uint32_t closed_nbhd(const Gr& G, int v) { return G.adj[v] | (1u << v); }
static inline int even_vertex(const Gr& G) { uint32_t e = G.evens(); return e ? __builtin_ctz(e) : -1; }
static inline uint32_t amax_of(const Gr& G, int c) {
  int g = even_vertex(G);
  uint32_t loc = closed_nbhd(G, c) | (g >= 0 ? G.adj[g] : 0);
  uint32_t A = 0; for (int v = 0; v < G.N; v++) if (G.deg(v) > 0 && !(loc >> v & 1)) A |= 1u << v;
  return A;
}
static inline bool admissible(const Gr& G, int c, uint32_t A) {
  int g = even_vertex(G);
  uint32_t bad = closed_nbhd(G, c) | (g >= 0 ? G.adj[g] : 0);
  return !(A & bad);
}
static void print_set(FILE* f, uint32_t S) { fputc('{', f); bool first = true; for (int v = 0; v < 32; v++) if (S >> v & 1) { fprintf(f, first ? "%d" : ",%d", v); first = false; } fputc('}', f); }
static void print_edges(FILE* f, const Gr& G) { for (int v = 0; v < G.N; v++) for (int w = v + 1; w < G.N; w++) if (G.has(v, w)) fprintf(f, "%d-%d ", v, w); }
