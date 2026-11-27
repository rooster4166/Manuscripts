// dlrec.cpp: certificates for DL(1) from the proved transfer calculus (session claude/dl-one).
// Uses moves.h / lind.h of manuscripts/l1-induction/scripts (every move there transfers goodness
// unconditionally, l1-induction Theorem 3.1).  A DL instance (G, a, b) is certified if
// Rec(G, b, {a}) or Rec(G, a, {b}).  Extra proved base cases here: no even vertex and A packed
// with A disjoint from N[c] (lovasz_avoid_set).  Flags as rec2: B boundary, M section-5 moves,
// S separation base.  Prints UNCERT lines for non-twin pairs with no certificate.
// usage: dlrec FLAGS < graph6
#include "moves.h"
#include <unordered_map>
static bool fB, fM, fS;
static int showcn1 = 0;
static std::unordered_map<std::string, char> memo;
static std::string ikey(const Gr& G, int c, uint32_t A) {
  std::string k = G.key(); k.push_back((char)G.N); k.push_back((char)c); k.append((const char*)&A, 4); return k;
}
static bool base2(const Gr& G, int c, uint32_t A) {
  if (base_case(G, c, A, fS)) return true;
  if (even_vertex(G) < 0 && packed_set(G, A) && !(A & closed_nbhd(G, c))) return true;  // L1, set form
  return false;
}
static bool rec(const Gr& G0, int c0, uint32_t A0) {
  Gr G; int c; uint32_t A; compact_inst(G0, c0, A0, G, c, A);
  if (A >> c & 1) return false;
  std::string k = ikey(G, c, A);
  auto it = memo.find(k); if (it != memo.end()) return it->second;
  memo[k] = 0;
  bool r = base2(G, c, A);
  if (!r) { std::vector<Inst> ch; children(G, c, A, fB, fM, ch); for (auto& x : ch) if (rec(x.G, x.c, x.A)) { r = true; break; } }
  memo[k] = r; return r;
}
static void pcert(const Gr& G0, int c0, uint32_t A0, int depth) {
  Gr G; int c; uint32_t A; compact_inst(G0, c0, A0, G, c, A);
  int g = even_vertex(G);
  printf("  %*s[N=%d g=%d c=%d A=", depth * 2, "", G.N, g, c); print_set(stdout, A);
  printf(" E: "); print_edges(stdout, G); printf("]");
  if (base2(G, c, A)) { printf(" BASE\n"); return; }
  std::vector<Inst> ch; children(G, c, A, fB, fM, ch);
  for (auto& x : ch) if (rec(x.G, x.c, x.A)) { printf(" --%c-->\n", x.mv); pcert(x.G, x.c, x.A, depth + 1); return; }
  printf(" ???\n");
}
int main(int argc, char** argv) {
  const char* fl = argc > 1 ? argv[1] : "BMS";
  fB = strchr(fl, 'B'); fM = strchr(fl, 'M'); fS = strchr(fl, 'S');
  if (argc > 2) showcn1 = atoi(argv[2]);
  char line[256]; long long pairs = 0, tw = 0, cert = 0, unc = 0, unc_core = 0, unc_cn1 = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    int g = even_vertex(G);
    int nev = 0; for (int v = 0; v < G.N; v++) if (G.deg(v) > 0 && G.deg(v) % 2 == 0) nev++;
    if (nev > 1) continue;
    if (memo.size() > 4000000) memo.clear();
    for (int a = 0; a < G.N; a++) for (int b = a + 1; b < G.N; b++) {
      if (G.deg(a) % 2 == 0 || G.deg(b) % 2 == 0 || G.has(a, b)) continue;
      pairs++;
      uint32_t C = G.comp(a);
      uint32_t rest = C & ~(1u << a) & ~(1u << b);
      bool twins = (C >> b & 1) && G.adj[a] == rest && G.adj[b] == rest;
      if (twins) { tw++; continue; }
      bool r1 = rec(G, b, 1u << a), r = r1 || rec(G, a, 1u << b);
      if (r) {
        cert++;
        if (showcn1) {
          bool core = g >= 0 && G.has(g, a) && G.has(g, b);
          bool cn1 = core && (G.adj[a] & G.adj[b]) == (1u << g);
          if (cn1 && G.deg(g) >= 4 && G.deg(a) >= 3 && G.deg(b) >= 3 && showcn1-- > 0) {
            printf("CERT %s g=%d a=%d b=%d orient=%s\n", line, g, a, b, r1 ? "Q(b)!a" : "Q(a)!b");
            if (r1) pcert(G, b, 1u << a, 0); else pcert(G, a, 1u << b, 0);
          }
        }
        continue;
      }
      unc++;
      bool core = g >= 0 && G.has(g, a) && G.has(g, b);
      bool cn1 = core && (G.adj[a] & G.adj[b]) == (1u << g);
      if (core) unc_core++;
      if (cn1) unc_cn1++;
      printf("UNCERT %s g=%d a=%d b=%d core=%d cn1=%d da=%d db=%d dg=%d\n", line, g, a, b, (int)core, (int)cn1,
             G.deg(a), G.deg(b), g >= 0 ? G.deg(g) : -1);
      fflush(stdout);
    }
  }
  printf("DLREC pairs=%lld twins=%lld certified=%lld uncertified=%lld (core %lld, cn1 %lld)\n", pairs, tw, cert, unc, unc_core, unc_cn1);
}
