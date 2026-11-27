// moves.h: the moves of the certificate class Rec (l1-induction manuscript, Section 2).
// Each move maps an instance (G, c, A) to a child instance; if the child is good, so is (G, c, A).
// No admissibility is required anywhere.  The measure (nu(G), |A|) decreases lexicographically,
// except for the boundary move (i), which only shrinks A, and (f), which shrinks A.
#pragma once
#include "lind.h"
#include <functional>

struct Inst { Gr G; int c; uint32_t A; char mv; };

static int MV_ROUTE_ALL = 0;  // route move: all g--c paths (not only shortest in G - A), up to length ROUTE_MAXLEN
static int ROUTE_MAXLEN = 4;
static int MV_TR = 0;      // TR moves: tight target u in N(g) cap N(c), keep c as terminal (valid when A cap N[c] empty)

static void compact_inst(const Gr& G, int c, uint32_t A, Gr& H, int& c2, uint32_t& A2) {
  uint32_t S = G.comp(c);
  int map[MAXV]; int k = 0;
  for (int v = 0; v < G.N; v++) map[v] = (S >> v & 1) ? k++ : -1;
  H = Gr(); H.N = k;
  for (int v = 0; v < G.N; v++) if (map[v] >= 0) for (int w = v + 1; w < G.N; w++) if (map[w] >= 0 && G.has(v, w)) H.add(map[v], map[w]);
  c2 = map[c]; A2 = 0;
  for (int v = 0; v < G.N; v++) if ((A >> v & 1) && map[v] >= 0) A2 |= 1u << map[v];
}

static bool packed_set(const Gr& G, uint32_t X) {
  for (int x = 0; x < G.N; x++) if (X >> x & 1) {
    if (G.adj[x] & X) return false;
    for (int y = x + 1; y < G.N; y++) if ((X >> y & 1) && (G.adj[x] & G.adj[y])) return false;
  }
  return true;
}

// base cases: returns 1 (certified), 0 (not a base case)
static int base_case(const Gr& G, int c, uint32_t A, bool sep) {
  if (A >> c & 1) return 0;
  int g = even_vertex(G);
  if (g < 0 && G.deg(c) == 1) { int y = __builtin_ctz(G.adj[c]); return !(A >> y & 1); }
  if (sep && packed_set(G, A | (1u << c))) return 1;
  if (!(A & G.comp(c))) return 1;  // A misses the component of c
  return 0;
}

// flags: 'B' boundary, 'M' section-5 moves
static void children(const Gr& G, int c, uint32_t A, bool fB, bool fM, std::vector<Inst>& out) {
  out.clear();
  int g = even_vertex(G);
  if (fB) {
    uint32_t C = 1u << c, f = C;
    while (f) { int x = __builtin_ctz(f); f &= f - 1; uint32_t nx = G.adj[x] & ~A & ~C; C |= nx; f |= nx; }
    uint32_t bd = 0; for (int x = 0; x < G.N; x++) if (G.adj[x] & C) bd |= 1u << x;
    bd &= A;
    if (bd != A) { out.push_back({G, c, bd, 'i'}); return; }  // canonical: always shrink first
  }
  if (fM && G.deg(c) == 3) {  // (g) split at c
    int ys[3], t = 0; for (int y = 0; y < G.N; y++) if (G.has(c, y)) ys[t++] = y;
    for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) if (i != j) {
      int y1 = ys[i], y2 = ys[j];
      if (G.has(y1, y2)) continue;
      if (i > j && false) continue;
      Gr H = G; H.del(c, y1); H.del(c, y2); H.add(y1, y2);
      out.push_back({H, c, A | (1u << y1), 'g'});
    }
  }
  if (g < 0) {
    if (G.deg(c) >= 3)
      for (int y = 0; y < G.N; y++) if (G.has(c, y) && !(A >> y & 1)) {
        if (G.N >= MAXV) { fprintf(stderr, "too many vertices\n"); exit(1); }
        Gr H = G; int l = H.N++; H.adj[l] = 0; H.del(c, y); H.add(y, l);
        out.push_back({H, l, A | (1u << c), 'd'});
      }
    return;
  }
  if (G.has(g, c) && !(A >> g & 1)) { Gr H = G; H.del(g, c); out.push_back({H, g, A | (1u << c), 'a'}); }
  for (int u = 0; u < G.N; u++) if (G.has(g, u) && u != c && !(A >> u & 1)) {
    Gr H = G; H.del(g, u);
    if (!G.has(c, u)) out.push_back({H, c, A, 'b'});
    else {
      if (MV_TR && !(A & closed_nbhd(G, c)) && !G.has(g, c)) out.push_back({H, c, A, 't'});
      H.del(c, u); out.push_back({H, u, A | (1u << c), 'c'});
    }
  }
  if (!fM) return;
  if (G.deg(g) == 2) {
    int u = __builtin_ctz(G.adj[g]), v = 31 - __builtin_clz(G.adj[g]);
    if (!G.has(u, v)) {
      Gr H = G; H.del(g, u); H.del(g, v); H.add(u, v);
      if (!(A >> g & 1)) out.push_back({H, c, A, 'e'});
      else {
        if (u != c) out.push_back({H, c, (A & ~(1u << g)) | (1u << u), 'e'});
        if (v != c) out.push_back({H, c, (A & ~(1u << g)) | (1u << v), 'e'});
      }
    } else if ((A >> g & 1) && !G.has(g, c)) out.push_back({G, c, A & ~(1u << g), 'f'});
  }
  if (!(A >> g & 1) && !G.has(g, c)) {  // (h) route to c
    std::vector<std::vector<int>> paths;
    std::vector<int> cur{g};
    if (!MV_ROUTE_ALL) {
      int dist[MAXV]; for (int x = 0; x < G.N; x++) dist[x] = -1;
      int q[MAXV], qh = 0, qt = 0; dist[c] = 0; q[qt++] = c;
      while (qh < qt) { int x = q[qh++]; for (int y = 0; y < G.N; y++) if (G.has(x, y) && dist[y] < 0 && !(A >> y & 1)) { dist[y] = dist[x] + 1; q[qt++] = y; } }
      if (dist[g] >= 2) {
        std::function<void(int)> go = [&](int x) {
          if ((int)paths.size() >= 8) return;
          if (x == c) { paths.push_back(cur); return; }
          for (int y = 0; y < G.N; y++) if (G.has(x, y) && dist[y] == dist[x] - 1) { cur.push_back(y); go(y); cur.pop_back(); }
        };
        go(g);
      }
    } else {
      uint32_t vis = 1u << g;
      std::function<void(int)> go = [&](int x) {
        if ((int)cur.size() - 1 >= ROUTE_MAXLEN) return;
        for (int y = 0; y < G.N; y++) if (G.has(x, y) && !(vis >> y & 1) && !(A >> y & 1)) {
          if (y == c) { if (cur.size() >= 2) { cur.push_back(y); paths.push_back(cur); cur.pop_back(); } continue; }
          vis |= 1u << y; cur.push_back(y); go(y); cur.pop_back(); vis &= ~(1u << y);
        }
      };
      go(g);
    }
    for (auto& P : paths) {
      Gr H = G; uint32_t B = A;
      for (size_t i = 0; i + 1 < P.size(); i++) H.del(P[i], P[i + 1]);
      for (size_t i = 1; i < P.size(); i++) B |= 1u << P[i];
      out.push_back({H, g, B, 'h'});
    }
  }
}
