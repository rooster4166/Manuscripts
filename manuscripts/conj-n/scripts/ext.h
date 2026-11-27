// ext.h: extended avoidance instances (G, c, A, B) and their proved moves (session claude/conj-n).
//
// (G, c, A, B): G has at most one vertex g of positive even degree, c is odd, c not in A.
// Good: some Lovasz decomposition has V(Q_c) disjoint from A and the far end of Q_c outside B.
// Normal form: compacted to the component of c; B restricted to odd vertices outside A + c.
//
// Moves (child good => instance good): l1-induction Thm 3.1 and manuscript conj-n Lemma 3.1, Thm 3.3:
//  (a) g even, c ~ g, g notin A:                     (G - gc, g, A+c, B)
//  (b) g even, u in N(g) - (A + N[c] + B), N(u)&B=0: (G - gu, c, A, B)
//  (x) g even, u in N(g) - N[c]:                     (G - gu, c, A, B + N_G(u))   [u may lie in A]
//  (c) g even, u in N(g)&N(c) - A, N(u)&B = 0:        (G - cu - gu, u, A+c, B)
//  (C) g even, u in N(g)&N(c) - A:                   (G - cu - gu, u, A+c, B + N_G(u))
//  (d) no even vertex, d(c)>=3, y in N(c) - A:       (G - cy + y l, l, A+c, B)
//  (e) d(g)=2, N(g)={u,v}, uv notin E:  G' = G-gu-gv+uv; (G',c,A,B) if g notin A, else (G',c,A-g+w,B), w in {u,v}-c
//  (f) d(g)=2, uv in E, g in A:                      (G, c, A-g, B)
//  (g) d(c)=3, y1,y2 in N(c), y1 !~ y2:              (G - cy1 - cy2 + y1y2, c, A+y1, B)
//  (h) g even, g notin A, R = g..c a path, interior outside A: (G - E(R), g, A + V(R)-g, B)
//  (i) C = component of c in G - A:                  (G, c, N(C)&A, B&C)   (only when it shrinks)
//  (k) P a path between two degree-one vertices, c not an end of P: (G - E(P), c, A, B)
// Optional (conjectural, flag XMV_TR): (t) tight target u in N(g)&N(c)-A, A & N[c] = 0, B = 0:
//  (G - gu, c, A, 0); XMV_TR = 1 only for c !~ g (TR of l1-induction), = 2 also for c ~ g (TR*).
// Base cases:
//  A and B miss the component of c; no even vertex, d(c)=1, neighbour not in A+B;
//  and, when B misses the component of c: A+c packed (separation); no even vertex, A packed,
//  A & N[c] = 0 (L1 set form); every vertex has <= 1 neighbour in A+c and A & N[c] = 0
//  (csys_good_of_sparse); |A| = 1 with A = {a}: N(a) = {g} and a, c not universal twins
//  (avoid_leaf), or N(g) = {c, a}, ca notin E, N(c) & N(a) = {g}, d(c) >= 3 (avoid_deg_two).
#pragma once
#include "orcb.h"
#include <functional>
#include <map>

struct XInst { Gr G; int c; uint32_t A, B; char mv; };

static uint32_t odd_mask(const Gr& G) { uint32_t o = 0; for (int v = 0; v < G.N; v++) if (G.deg(v) & 1) o |= 1u << v; return o; }

static void xcompact(const Gr& G, int c, uint32_t A, uint32_t B, Gr& H, int& c2, uint32_t& A2, uint32_t& B2) {
  uint32_t S = G.comp(c);
  int map[MAXV]; int k = 0;
  for (int v = 0; v < G.N; v++) map[v] = (S >> v & 1) ? k++ : -1;
  H = Gr(); H.N = k;
  for (int v = 0; v < G.N; v++) if (map[v] >= 0) for (int w = v + 1; w < G.N; w++) if (map[w] >= 0 && G.has(v, w)) H.add(map[v], map[w]);
  c2 = map[c]; A2 = 0; B2 = 0;
  for (int v = 0; v < G.N; v++) if (map[v] >= 0) { if (A >> v & 1) A2 |= 1u << map[v]; if (B >> v & 1) B2 |= 1u << map[v]; }
  B2 &= odd_mask(H) & ~A2 & ~(1u << c2);
}

static bool xpacked(const Gr& G, uint32_t X) {
  for (int x = 0; x < G.N; x++) if (X >> x & 1) {
    if (G.adj[x] & X) return false;
    for (int y = x + 1; y < G.N; y++) if ((X >> y & 1) && (G.adj[x] & G.adj[y])) return false;
  }
  return true;
}

static int XFLAG_SEP = 1, XFLAG_SPARSE = 1, XFLAG_DL1 = 1;
static bool xbase(const Gr& G, int c, uint32_t A, uint32_t B) {
  if (A >> c & 1) return false;
  int g = even_vertex(G);
  uint32_t C = G.comp(c);
  if (!(A & C) && !(B & C)) return true;
  if (g < 0 && G.deg(c) == 1) { int y = __builtin_ctz(G.adj[c]); if (!((A | B) >> y & 1)) return true; }
  if (B & C) return false;
  if (XFLAG_SEP && xpacked(G, A | (1u << c))) return true;
  if (XFLAG_SPARSE && !(A & closed_nbhd(G, c))) {  // csys_good_of_sparse: every vertex has <= 1 neighbour in A+c
    uint32_t X = A | (1u << c); bool ok = true;
    for (int v = 0; v < G.N && ok; v++) if (__builtin_popcount(G.adj[v] & X) > 1) ok = false;
    if (ok) return true;
  }
  if (XFLAG_DL1 && g >= 0 && __builtin_popcount(A) == 1) {
    int a = __builtin_ctz(A);
    if (G.adj[a] == (1u << g)) {  // avoid_leaf: N(a) = {g}, not universal twins
      uint32_t rest = C & ~(1u << a) & ~(1u << c);
      bool tw = G.adj[a] == rest && G.adj[c] == rest;
      if (!tw) return true;
    }
    // avoid_deg_two: N(g) = {c, a}, ca notin E, N(c) & N(a) = {g}, d(c) >= 3
    if (G.adj[g] == ((1u << c) | (1u << a)) && !G.has(c, a) && (G.adj[c] & G.adj[a]) == (1u << g) && G.deg(c) >= 3) return true;
  }
  if (g < 0 && xpacked(G, A) && !(A & closed_nbhd(G, c))) return true;
  return false;
}

static int XMV_LEAFPATH_MAXLEN = 2;
static int XMV_TR = 0;  // (t): TR move (conjectural, l1-induction Conj 4.1): c !~ g, u in N(g)&N(c)-A, A & N[c] = 0, B = 0: (G - gu, c, A, 0)
static int XMV_ROUTES = 8;

static void xchildren(const Gr& G, int c, uint32_t A, uint32_t B, std::vector<XInst>& out) {
  out.clear();
  int g = even_vertex(G);
  // (i) boundary
  {
    uint32_t C = 1u << c, f = C;
    while (f) { int x = __builtin_ctz(f); f &= f - 1; uint32_t nx = G.adj[x] & ~A & ~C; C |= nx; f |= nx; }
    uint32_t bd = 0; for (int x = 0; x < G.N; x++) if (G.adj[x] & C) bd |= 1u << x;
    bd &= A;
    if (bd != A || (B & ~C)) { out.push_back({G, c, bd, B & C, 'i'}); return; }
  }
  // (g) split at c of degree 3
  if (G.deg(c) == 3) {
    int ys[3], t = 0; for (int y = 0; y < G.N; y++) if (G.has(c, y)) ys[t++] = y;
    for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) if (i != j) {
      int y1 = ys[i], y2 = ys[j];
      if (G.has(y1, y2)) continue;
      Gr H = G; H.del(c, y1); H.del(c, y2); H.add(y1, y2);
      out.push_back({H, c, A | (1u << y1), B, 'g'});
    }
  }
  // (k) leaf paths
  for (int u = 0; u < G.N; u++) if (G.deg(u) == 1 && u != c) {
    std::vector<int> cur{u}; uint32_t vis = 1u << u;
    std::function<void(int)> go = [&](int v) {
      if ((int)cur.size() - 1 >= XMV_LEAFPATH_MAXLEN) return;
      for (int w = 0; w < G.N; w++) if (G.has(v, w) && !(vis >> w & 1)) {
        if (G.deg(w) == 1) {
          if (w != c && w > u) { Gr H = G; H.del(v, w); for (size_t i = 0; i + 1 < cur.size(); i++) H.del(cur[i], cur[i + 1]); out.push_back({H, c, A, B, 'k'}); }
          continue;
        }
        vis |= 1u << w; cur.push_back(w); go(w); cur.pop_back(); vis &= ~(1u << w);
      }
    };
    go(u);
  }
  if (g < 0) {
    if (G.deg(c) >= 3)
      for (int y = 0; y < G.N; y++) if (G.has(c, y) && !(A >> y & 1)) {
        if (G.N >= MAXV) { fprintf(stderr, "too many vertices\n"); exit(1); }
        Gr H = G; int l = H.N++; H.adj[l] = 0; H.del(c, y); H.add(y, l);
        out.push_back({H, l, A | (1u << c), B, 'd'});
      }
    return;
  }
  // (a)
  if (G.has(g, c) && !(A >> g & 1)) { Gr H = G; H.del(g, c); out.push_back({H, g, A | (1u << c), B, 'a'}); }
  for (int u = 0; u < G.N; u++) if (G.has(g, u) && u != c) {
    Gr H = G; H.del(g, u);
    if (!G.has(c, u)) {
      if (!(A >> u & 1) && !(B >> u & 1) && !(G.adj[u] & B)) out.push_back({H, c, A, B, 'b'});
      out.push_back({H, c, A, B | G.adj[u], 'x'});
    } else if (!(A >> u & 1)) {
      if (XMV_TR && !B && (XMV_TR == 2 || !G.has(g, c)) && !(A & closed_nbhd(G, c))) out.push_back({H, c, A, 0, 't'});
      H.del(c, u);
      if (!(G.adj[u] & B)) out.push_back({H, u, A | (1u << c), B, 'c'});
      out.push_back({H, u, A | (1u << c), B | G.adj[u], 'C'});
    }
  }
  // (e), (f)
  if (G.deg(g) == 2) {
    int u = __builtin_ctz(G.adj[g]), v = 31 - __builtin_clz(G.adj[g]);
    if (!G.has(u, v)) {
      Gr H = G; H.del(g, u); H.del(g, v); H.add(u, v);
      if (!(A >> g & 1)) out.push_back({H, c, A, B, 'e'});
      else {
        if (u != c) out.push_back({H, c, (A & ~(1u << g)) | (1u << u), B, 'e'});
        if (v != c) out.push_back({H, c, (A & ~(1u << g)) | (1u << v), B, 'e'});
      }
    } else if (A >> g & 1) out.push_back({G, c, A & ~(1u << g), B, 'f'});
  }
  // (h) routes g -> c: shortest in G - A, at most XMV_ROUTES of them
  if (!(A >> g & 1) && !G.has(g, c)) {
    int dist[MAXV]; for (int x = 0; x < G.N; x++) dist[x] = -1;
    int q[MAXV], qh = 0, qt = 0; dist[c] = 0; q[qt++] = c;
    while (qh < qt) { int x = q[qh++]; for (int y = 0; y < G.N; y++) if (G.has(x, y) && dist[y] < 0 && !(A >> y & 1)) { dist[y] = dist[x] + 1; q[qt++] = y; } }
    std::vector<std::vector<int>> paths; std::vector<int> cur{g};
    if (dist[g] >= 2) {
      std::function<void(int)> go = [&](int x) {
        if ((int)paths.size() >= XMV_ROUTES) return;
        if (x == c) { paths.push_back(cur); return; }
        for (int y = 0; y < G.N; y++) if (G.has(x, y) && dist[y] == dist[x] - 1) { cur.push_back(y); go(y); cur.pop_back(); }
      };
      go(g);
    }
    for (auto& P : paths) {
      Gr H = G; uint32_t A2 = A;
      for (size_t i = 0; i + 1 < P.size(); i++) H.del(P[i], P[i + 1]);
      for (size_t i = 1; i < P.size(); i++) A2 |= 1u << P[i];
      out.push_back({H, g, A2, B, 'h'});
    }
  }
}

// goodness with memo
static std::unordered_map<std::string, char> xgmemo;
static std::string xkey(const Gr& G, int c, uint32_t A, uint32_t B) {
  std::string k = G.key(); k.push_back((char)G.N); k.push_back((char)c); k.append((const char*)&A, 4); k.append((const char*)&B, 4); return k;
}
static int xgood(const Gr& G, int c, uint32_t A, uint32_t B) {
  if (A >> c & 1) return 0;
  std::string k = xkey(G, c, A, B);
  auto it = xgmemo.find(k); if (it != xgmemo.end()) return it->second;
  int r = orcb::avoidB(G, c, A, B);
  if (xgmemo.size() > 8000000) xgmemo.clear();
  xgmemo[k] = (char)r; return r;
}

static void xpr(FILE* f, const Gr& G, int c, uint32_t A, uint32_t B) {
  int g = even_vertex(G);
  fprintf(f, "N=%d g=%d c=%d A=", G.N, g, c); print_set(f, A); fprintf(f, " B="); print_set(f, B);
  fprintf(f, " degs="); for (int v = 0; v < G.N; v++) fprintf(f, "%d", G.deg(v) > 9 ? 9 : G.deg(v));
  fprintf(f, " E: "); print_edges(f, G);
}
