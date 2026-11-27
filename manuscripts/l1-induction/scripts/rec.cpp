// rec.cpp: the certificate class Rec of the l1-induction manuscript.
//
// Rec(G, c, A) holds if (G, c, A) is certified by Lovász steps with the end at c protected, where
// the intermediate instances need NOT be admissible.  Every move transfers goodness from the smaller
// instance to the larger one unconditionally (l1star Thm 4.2 proofs; admissibility is used there only
// to invoke the induction hypothesis):
//   (a)  g even, c in N(g), g not in A:            Rec(G - gc, g, A + c)
//   (b)  g even, u in N(g) - A - N[c]:             Rec(G - gu, c, A)        (protected transfer)
//   (c)  g even, u in N(g) cap N(c), u not in A:   Rec(G - cu - gu, u, A + c)
//   (d)  no even vertex, y in N(c) - A, d(c) >= 3: Rec(H(G; c, y), l, A + c)  (leaf l at y)
//   (d0) no even vertex, d(c) = 1, N(c) = {y}:     true iff y not in A
// Optional base (flag S): A + c packed (route-descent Thm 6.1, Lean separation_set) => true.
//
// Modes:
//   rec adm [S]     : stdin graph6; every (G, c) with <= 1 even vertex, A = Amax(G, c).
//                     Prints NOREC lines for admissible instances not in Rec, and a summary.
//   rec all [S]     : every A subset of V - {c} (vertices of positive degree): compare Rec with Good.
#include "lind.h"
#include <functional>

static int FL_SEP = 0, FL_M = 0, FL_B = 0;
static long long nstates = 0;
static std::unordered_map<std::string, char> memo;

static bool packed(const Gr& G, uint32_t X) {
  for (int x = 0; x < G.N; x++) if (X >> x & 1) {
    if (G.adj[x] & X) return false;
    for (int y = x + 1; y < G.N; y++) if ((X >> y & 1) && (G.adj[x] & G.adj[y])) return false;
  }
  return true;
}

// compact the component of c; returns new c and maps A
static void compact(const Gr& G, int c, uint32_t A, Gr& H, int& c2, uint32_t& A2) {
  uint32_t S = G.comp(c);
  int map[MAXV]; int k = 0;
  for (int v = 0; v < G.N; v++) map[v] = (S >> v & 1) ? k++ : -1;
  H = Gr(); H.N = k;
  for (int v = 0; v < G.N; v++) if (map[v] >= 0) for (int w = v + 1; w < G.N; w++) if (map[w] >= 0 && G.has(v, w)) H.add(map[v], map[w]);
  c2 = map[c]; A2 = 0;
  for (int v = 0; v < G.N; v++) if ((A >> v & 1) && map[v] >= 0) A2 |= 1u << map[v];
}

static bool rec(const Gr& G0, int c0, uint32_t A0) {
  Gr G; int c; uint32_t A;
  compact(G0, c0, A0, G, c, A);
  if (A >> c & 1) return false;
  std::string k = G.key(); k.push_back((char)G.N); k.push_back((char)c); k.append((const char*)&A, 4);
  auto it = memo.find(k);
  if (it != memo.end()) return it->second;
  nstates++;
  memo[k] = 0;  // no cycles possible (measure decreases), but guard anyway
  bool r = false;
  uint32_t E = G.evens();
  if (__builtin_popcount(E) > 1) { fprintf(stderr, "two even vertices?\n"); exit(1); }
  int g = E ? __builtin_ctz(E) : -1;
  if (FL_SEP && packed(G, A | (1u << c))) r = true;
  // (i) boundary: shrink A to the boundary of the component of c in G - A
  if (!r && FL_B) {
    uint32_t C = 1u << c, f = C;
    while (f) { int x = __builtin_ctz(f); f &= f - 1; uint32_t nx = G.adj[x] & ~A & ~C; C |= nx; f |= nx; }
    uint32_t bd = 0; for (int x = 0; x < G.N; x++) if (G.adj[x] & C) bd |= 1u << x;
    bd &= A;
    if (bd != A) { r = rec(G, c, bd); memo[k] = r; return r; }
  }
  // (g) d(c) = 3: split off two non-adjacent neighbours y1, y2 at c; c becomes a leaf
  if (!r && FL_M && G.deg(c) == 3) {
    int ys[3], t = 0; for (int y = 0; y < G.N; y++) if (G.has(c, y)) ys[t++] = y;
    for (int i = 0; i < 3 && !r; i++) for (int j = 0; j < 3 && !r; j++) if (i != j) {
      int y1 = ys[i], y2 = ys[j];
      if (G.has(y1, y2) || (A >> y1 & 1) == 0 && false) continue;
      Gr H = G; H.del(c, y1); H.del(c, y2); H.add(y1, y2);
      r = rec(H, c, A | (1u << y1));
    }
  }
  if (r) {}
  else if (g < 0) {
    if (G.deg(c) == 1) { int y = __builtin_ctz(G.adj[c]); r = !(A >> y & 1); }
    else {
      for (int y = 0; y < G.N && !r; y++) if (G.has(c, y) && !(A >> y & 1)) {
        if (G.N >= MAXV) { fprintf(stderr, "too many vertices\n"); exit(1); }
        Gr H = G; int l = H.N++; H.adj[l] = 0; H.del(c, y); H.add(y, l);
        r = rec(H, l, A | (1u << c));
      }
    }
  } else {
    if (G.has(g, c) && !(A >> g & 1)) { Gr H = G; H.del(g, c); r = rec(H, g, A | (1u << c)); }
    // (e) d(g) = 2, N(g) = {u, v}, uv not an edge: split off g
    if (!r && FL_M && G.deg(g) == 2) {
      int u = __builtin_ctz(G.adj[g]), v = 31 - __builtin_clz(G.adj[g]);
      if (!G.has(u, v)) {
        Gr H = G; H.del(g, u); H.del(g, v); H.add(u, v);
        if (!(A >> g & 1)) r = rec(H, c, A);
        else {
          if (!r && u != c) r = rec(H, c, (A & ~(1u << g)) | (1u << u));
          if (!r && v != c) r = rec(H, c, (A & ~(1u << g)) | (1u << v));
        }
      } else if ((A >> g & 1) && !G.has(g, c)) {
        // (f) triangle swap: drop g from A
        r = rec(G, c, A & ~(1u << g));
      }
    }
    // (h) route to c: a shortest g--c path R in G - A (length >= 2); new terminal g, A + V(R) - g
    if (!r && FL_M && !(A >> g & 1) && !G.has(g, c)) {
      // BFS from c in G - A
      int dist[MAXV]; for (int x = 0; x < G.N; x++) dist[x] = -1;
      int q[MAXV], qh = 0, qt = 0; dist[c] = 0; q[qt++] = c;
      while (qh < qt) { int x = q[qh++]; for (int y = 0; y < G.N; y++) if (G.has(x, y) && dist[y] < 0 && !(A >> y & 1)) { dist[y] = dist[x] + 1; q[qt++] = y; } }
      if (dist[g] >= 2) {
        // enumerate shortest paths g -> c (up to 8)
        int path[MAXV]; int cntp = 0;
        std::vector<std::vector<int>> paths;
        std::vector<int> cur{g};
        std::function<void(int)> go = [&](int x) {
          if ((int)paths.size() >= 8) return;
          if (x == c) { paths.push_back(cur); return; }
          for (int y = 0; y < G.N; y++) if (G.has(x, y) && dist[y] == dist[x] - 1) { cur.push_back(y); go(y); cur.pop_back(); }
        };
        go(g); (void)path; (void)cntp;
        for (auto& P : paths) {
          if (r) break;
          Gr H = G; uint32_t B = A;
          for (size_t i = 0; i + 1 < P.size(); i++) H.del(P[i], P[i + 1]);
          for (size_t i = 1; i < P.size(); i++) B |= 1u << P[i];
          r = rec(H, g, B);
        }
      }
    }
    for (int u = 0; u < G.N && !r; u++) if (G.has(g, u) && u != c && !(A >> u & 1)) {
      Gr H = G; H.del(g, u);
      if (!G.has(c, u)) r = rec(H, c, A);
      else { H.del(c, u); r = rec(H, u, A | (1u << c)); }
    }
  }
  memo[k] = r;
  return r;
}

int main(int argc, char** argv) {
  if (argc < 2) { fprintf(stderr, "usage: rec adm|all [S]\n"); return 1; }
  std::string mode = argv[1];
  FL_SEP = argc > 2 && strchr(argv[2], 'S');
  FL_M = argc > 2 && strchr(argv[2], 'M');
  FL_B = argc > 2 && strchr(argv[2], 'B');
  char line[256];
  long long inst = 0, norec = 0, blocked = 0, norec_blocked = 0, allcnt[2][2] = {{0}};
  while (fgets(line, sizeof line, stdin)) {
    Gr G; if (!parse_g6(line, G)) continue;
    char* nl = strchr(line, '\n'); if (nl) *nl = 0;
    if (__builtin_popcount(G.evens()) > 1) continue;
    int g = even_vertex(G);
    if (memo.size() > 4000000) memo.clear();
    for (int c = 0; c < G.N; c++) {
      if (!(G.deg(c) & 1)) continue;
      if (mode == "adm") {
        uint32_t A = amax_of(G, c);
        inst++;
        bool isb = false;
        if (g >= 0 && !G.has(g, c)) {
          isb = true;
          for (int u = 0; u < G.N; u++) if (G.has(g, u) && !(G.adj[u] & A & ~(1u << g))) isb = false;
        }
        blocked += isb;
        bool r = rec(G, c, A);
        if (!r) { norec++; norec_blocked += isb;
          printf("NOREC %s g=%d c=%d A=", line, g, c); print_set(stdout, A); printf(" blocked=%d\n", (int)isb); fflush(stdout); }
      } else {
        // every A subset of positive-degree vertices other than c
        int idx[32], kk = 0;
        for (int v = 0; v < G.N; v++) if (v != c && G.deg(v) > 0) idx[kk++] = v;
        for (uint32_t sub = 0; sub < (1u << kk); sub++) {
          uint32_t A = 0; for (int i = 0; i < kk; i++) if (sub >> i & 1) A |= 1u << idx[i];
          int good = orc::avoid(G, c, A) == 1;
          bool r = rec(G, c, A);
          allcnt[good][r]++;
          if (good && !r && admissible(G, c, A)) { printf("ADM-NOREC %s c=%d A=", line, c); print_set(stdout, A); printf("\n"); }
          if (!good && r) { printf("BUG rec but not good %s c=%d A=", line, c); print_set(stdout, A); printf("\n"); }
        }
      }
    }
  }
  if (mode == "adm")
    printf("SUMMARY adm instances=%lld blocked=%lld notRec=%lld notRec_blocked=%lld states=%lld sep=%d\n", inst, blocked, norec, norec_blocked, nstates, FL_SEP);
  else
    printf("SUMMARY all good&rec=%lld good&!rec=%lld bad&rec=%lld bad&!rec=%lld sep=%d\n", allcnt[1][1], allcnt[1][0], allcnt[0][1], allcnt[0][0], FL_SEP);
  return 0;
}
