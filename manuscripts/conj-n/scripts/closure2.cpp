// closure2.cpp: closure computation for classes of extended instances (G, c, A, B)
// (session claude/conj-n).  See ext.h for instances, moves and base cases.
//
// For every connected graph on stdin (graph6; at most one even vertex), every odd c, every A, B
// (B a set of odd vertices outside A + c; sizes bounded by -a, -b) in the class:
//   BASE / MOVED (some move leads to a base case or into the class) / STUCK.
//   -s : soundness, every member is good (exact oracle);  -g : print goodness of stuck children.
// usage: closure2 CLASS [-a maxA] [-b maxB] [-s] [-g] [-p maxprint] [-m moveletters] [-x excluded]
#include "ext.h"

static std::string cls, movelist, exclude;
static int maxA = 99, maxB = 99, soundness = 0, showgood = 0, maxprint = 30;
static int popc(uint32_t x) { return __builtin_popcount(x); }

// ---------------- predicates ----------------
static bool hasWitness(const Gr& G, int c, uint32_t A, uint32_t B) {
  int g = even_vertex(G); uint32_t gm = g >= 0 ? 1u << g : 0;
  for (uint32_t W = G.adj[c] & ~gm & ~B & ~A; W; W &= W - 1) { int w = __builtin_ctz(W); if (!(G.adj[w] & A & ~gm)) return true; }
  return false;
}
static bool P_N2B(const Gr& G, int c, uint32_t A, uint32_t B) {
  if (A & closed_nbhd(G, c)) return false;
  return hasWitness(G, c, A, B);
}
static bool P_N2(const Gr& G, int c, uint32_t A, uint32_t B) { return B == 0 && P_N2B(G, c, A, B); }
static bool P_N1(const Gr& G, int c, uint32_t A, uint32_t B) {
  if (B || popc(A) != 1) return false;
  int x = __builtin_ctz(A); if (G.deg(x) % 2 == 0) return false;
  return P_N2B(G, c, A, B);
}
static uint32_t nbrs(const Gr& G, uint32_t S) { uint32_t r = 0; for (int v = 0; v < G.N; v++) if (S >> v & 1) r |= G.adj[v]; return r; }
static bool P_NBA(const Gr& G, int c, uint32_t A, uint32_t B) {  // N2B with B inside N(A)
  if (B & ~nbrs(G, A)) return false;
  return P_N2B(G, c, A, B);
}
// XC: (x)-children of N2 instances.  x = even vertex of G, x in A; some odd h in B, h !~ x, h != c, with
// B = N_G(x) + h (restricted to odd vertices outside A + c), and (G + hx, c, A) in N2.
static bool P_XC(const Gr& G, int c, uint32_t A, uint32_t B) {
  int x = even_vertex(G); if (x < 0 || !(A >> x & 1)) return false;
  for (uint32_t Hs = B & ~G.adj[x]; Hs; Hs &= Hs - 1) {
    int h = __builtin_ctz(Hs); if (h == c || h == x) continue;
    Gr P = G; P.add(h, x);
    if (__builtin_popcount(P.evens()) != 1 || even_vertex(P) != h) continue;
    uint32_t want = (P.adj[x]) & odd_mask(G) & ~A & ~(1u << c);
    if (B != want) continue;
    if (P_N2B(P, c, A, 0)) return true;
  }
  return false;
}
static bool P_V(const Gr& G, int c, uint32_t A, uint32_t B) {  // witness may be g
  if (B || (A & closed_nbhd(G, c))) return false;
  int g = even_vertex(G); uint32_t gm = g >= 0 ? 1u << g : 0;
  for (uint32_t W = G.adj[c]; W; W &= W - 1) { int w = __builtin_ctz(W); if (!(G.adj[w] & A & ~gm)) return true; }
  return false;
}
static bool P_L1(const Gr& G, int c, uint32_t A, uint32_t B) {
  if (B) return false; int g = even_vertex(G);
  return !(A & (closed_nbhd(G, c) | (g >= 0 ? G.adj[g] : 0)));
}
static bool P_NA(const Gr& G, int c, uint32_t A, uint32_t B) {  // all-odd neighbour avoidance
  if (B || even_vertex(G) >= 0 || __builtin_popcount(A) != 1) return false;
  int x = __builtin_ctz(A); if (!G.has(c, x)) return false;
  return (G.adj[c] & ~G.adj[x] & ~(1u << x)) != 0;
}
static bool P_Ngx(const Gr& G, int c, uint32_t A, uint32_t B) {  // N2 with A = {g, x}, x ~ g
  int g = even_vertex(G); if (g < 0 || B || __builtin_popcount(A) != 2 || !(A >> g & 1)) return false;
  int x = __builtin_ctz(A & ~(1u << g)); if (!G.has(g, x)) return false;
  return P_N2B(G, c, A, 0);
}
static bool P_NgA(const Gr& G, int c, uint32_t A, uint32_t B) {  // N2 with A inside N[g]
  int g = even_vertex(G); if (g < 0 || B) return false;
  if (A & ~closed_nbhd(G, g)) return false;
  return P_N2B(G, c, A, 0);
}
static bool P_W(const Gr& G, int c, uint32_t A, uint32_t B) { return B == 0 && hasWitness(G, c, A, B); }
static int maxdeg(const Gr& G) { int m = 0; for (int v = 0; v < G.N; v++) m = std::max(m, G.deg(v)); return m; }
static int maxodd(const Gr& G) { int m = 0; for (int v = 0; v < G.N; v++) if (G.deg(v) & 1) m = std::max(m, G.deg(v)); return m; }
static int DMAX = 3, GMAX = 99;
static bool inclass(const Gr& G, int c, uint32_t A, uint32_t B) {
  if (A >> c & 1) return false;
  if (cls.size() > 2 && cls[0] == 'D') {  // D<k>_<class>: restrict to max odd degree <= k (and even degree <= GMAX)
    if (maxodd(G) > DMAX) return false;
    int g = even_vertex(G); if (g >= 0 && G.deg(g) > GMAX) return false;
  }
  if (G.deg(c) % 2 == 0) return false;
  std::string k = cls; if (k.size() > 2 && k[0] == 'D') k = k.substr(k.find('_') + 1);
  if (k == "N1") return P_N1(G, c, A, B);
  if (k == "N2") return P_N2(G, c, A, B);
  if (k == "N2B") return P_N2B(G, c, A, B);
  if (k == "NBA") return P_NBA(G, c, A, B);
  if (k == "N2XC") return P_N2(G, c, A, B) || P_XC(G, c, A, B);
  if (k == "XC") return P_XC(G, c, A, B);
  if (k == "V") return P_V(G, c, A, B);
  if (k == "L1") return P_L1(G, c, A, B);
  if (k == "U") return P_N2(G, c, A, B) || P_L1(G, c, A, B);
  if (k == "N1NA") return P_N1(G, c, A, B) || P_NA(G, c, A, B);
  if (k == "N1NAgx") return P_N1(G, c, A, B) || P_NA(G, c, A, B) || P_Ngx(G, c, A, B);
  if (k == "C1") return P_N1(G, c, A, B) || P_NA(G, c, A, B) || P_NgA(G, c, A, B);
  if (k == "W") return P_W(G, c, A, B);
  fprintf(stderr, "unknown class %s\n", cls.c_str()); exit(1);
}

int main(int argc, char** argv) {
  if (argc < 2) { fprintf(stderr, "usage\n"); return 1; }
  cls = argv[1];
  for (int i = 2; i < argc; i++) {
    std::string a = argv[i];
    if (a == "-a") maxA = atoi(argv[++i]);
    else if (a == "-b") maxB = atoi(argv[++i]);
    else if (a == "-s") soundness = 1;
    else if (a == "-g") showgood = 1;
    else if (a == "-p") maxprint = atoi(argv[++i]);
    else if (a == "-m") movelist = argv[++i];
    else if (a == "-x") exclude = argv[++i];
    else if (a == "-L") XMV_LEAFPATH_MAXLEN = atoi(argv[++i]);
    else if (a == "-cap") { XMV_LEAFPATH_MAXLEN = 2; XMV_ROUTES_ALL = 0; }  // the capped variant of the first draft
    else if (a == "-T") XMV_TR = 1;
    else if (a == "-T2") XMV_TR = 2;
    else if (a == "-D") DMAX = atoi(argv[++i]);
    else if (a == "-G") GMAX = atoi(argv[++i]);
  }
  std::map<std::string, long long> C;
  char line[256]; int printed = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    if (popc(G.evens()) > 1) continue;
    uint32_t odd = odd_mask(G);
    for (int c = 0; c < G.N; c++) {
      if (!(odd >> c & 1)) continue;
      uint32_t U = ((1u << G.N) - 1) & ~(1u << c);
      for (uint32_t A = U;; A = (A - 1) & U) {
        if (popc(A) <= maxA) {
          uint32_t UB = maxB == 0 ? 0 : (odd & ~A & ~(1u << c));
          for (uint32_t B = UB;; B = (B - 1) & UB) {
            if (popc(B) <= maxB && inclass(G, c, A, B)) {
              C["inclass"]++;
              if (soundness) {
                int o = xgood(G, c, A, B);
                if (o != 1) { C["FALSE"]++; if (printed++ < maxprint) { printf("FALSE %s ", line); xpr(stdout, G, c, A, B); printf(" oracle=%d\n", o); } }
              }
              if (xbase(G, c, A, B)) C["base"]++;
              else {
                std::vector<XInst> ch; xchildren(G, c, A, B, ch);
                char used = 0;
                for (auto& x : ch) {
                  if (!movelist.empty() && movelist.find(x.mv) == std::string::npos) continue;
                  if (!exclude.empty() && exclude.find(x.mv) != std::string::npos) continue;
                  Gr H; int c2; uint32_t A2, B2; xcompact(x.G, x.c, x.A, x.B, H, c2, A2, B2);
                  if (A2 >> c2 & 1) continue;
                  if (xbase(H, c2, A2, B2) || inclass(H, c2, A2, B2)) { used = x.mv; break; }
                }
                if (used) { C["moved"]++; C[std::string("move_") + used]++; }
                else {
                  C["STUCK"]++;
                  if (printed++ < maxprint) {
                    printf("STUCK %s ", line); xpr(stdout, G, c, A, B);
                    if (showgood) printf(" good=%d", xgood(G, c, A, B));
                    printf("\n");
                    for (auto& x : ch) {
                      Gr H; int c2; uint32_t A2, B2; xcompact(x.G, x.c, x.A, x.B, H, c2, A2, B2);
                      printf("    --%c--> ", x.mv); xpr(stdout, H, c2, A2, B2);
                      if (showgood) printf(" good=%d", (A2 >> c2 & 1) ? 0 : xgood(H, c2, A2, B2));
                      printf("\n");
                    }
                  }
                }
              }
            }
            if (B == 0) break;
          }
        }
        if (A == 0) break;
      }
    }
  }
  printf("CLOSURE2 class=%s", cls.c_str());
  for (auto& kv : C) printf(" %s=%lld", kv.first.c_str(), kv.second);
  printf("\n");
}
