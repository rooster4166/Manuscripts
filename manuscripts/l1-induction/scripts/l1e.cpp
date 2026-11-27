// l1e.cpp: test of L1E.  For each (G, c) with one even vertex g, c not in N(g), A = Amax: is there a
// target u in N(g) and a Lovász decomposition D' of G - gu with Q'_c avoiding A and Q'_g avoiding u?
// (Equivalently: a good Lovász decomposition of G in which gu is the terminal edge of Q_u.)
// Also reports the "some target good" form (Q'_c avoiding A only) and splits targets by N(c).
#include "orc2.h"
int main(int argc, char** argv) {
  char line[256]; long long inst = 0, st = 0, l1e = 0, l1e_out = 0, st_out = 0, blocked = 0, bl1e = 0;
  while (fgets(line, sizeof line, stdin)) {
    Gr G; if (!parse_g6(line, G)) continue;
    char* nl = strchr(line, '\n'); if (nl) *nl = 0;
    if (__builtin_popcount(G.evens()) != 1) continue;
    int g = even_vertex(G);
    for (int c = 0; c < G.N; c++) {
      if (!(G.deg(c) & 1) || G.has(g, c)) continue;
      uint32_t A = amax_of(G, c);
      bool isb = true; for (int u = 0; u < G.N; u++) if (G.has(g, u) && !(G.adj[u] & A & ~(1u << g))) isb = false;
      inst++; blocked += isb;
      bool anyst = false, anyl1e = false, anyst_out = false, anyl1e_out = false;
      for (int u = 0; u < G.N; u++) if (G.has(g, u)) {
        Gr H = G; H.del(g, u);
        int s1[1] = {c}; uint32_t f1[1] = {A};
        int r1 = orc2::query(H, 1, s1, f1) == 1;
        int r2 = 0;
        if (r1) { int s2[2] = {c, g}; uint32_t f2[2] = {A, 1u << u}; r2 = orc2::query(H, 2, s2, f2) == 1; }
        anyst |= r1; anyl1e |= r2;
        if (!G.has(c, u)) { anyst_out |= r1; anyl1e_out |= r2; }
      }
      st += anyst; l1e += anyl1e; st_out += anyst_out; l1e_out += anyl1e_out; bl1e += (isb && anyl1e);
      if (!anyl1e) { printf("NOL1E %s c=%d g=%d A=", line, c, g); print_set(stdout, A); printf(" sometarget=%d blocked=%d\n", (int)anyst, (int)isb); fflush(stdout); }
    }
  }
  printf("SUMMARY inst(c notin N(g), Amax)=%lld blocked=%lld sometarget=%lld sometarget_outNc=%lld L1E=%lld L1E_outNc=%lld L1E_blocked=%lld\n", inst, blocked, st, st_out, l1e, l1e_out, bl1e);
}
