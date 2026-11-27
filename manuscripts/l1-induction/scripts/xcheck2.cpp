// cross-check orc2 (two constrained paths) against full enumeration (dec.h) on random instances
#include "orc2.h"
#include "dec.h"
int main() {
  char line[256]; long long q = 0, bad = 0; unsigned seed = 1;
  while (fgets(line, sizeof line, stdin)) {
    Gr G; if (!parse_g6(line, G)) continue;
    for (int c = 0; c < G.N; c++) if (G.deg(c) & 1) for (int d = 0; d < G.N; d++) if (d != c && (G.deg(d) & 1)) {
      for (int rep = 0; rep < 3; rep++) {
        seed = seed * 1103515245 + 12345; uint32_t A = (seed >> 8) & ((1u << G.N) - 1) & ~(1u << c);
        seed = seed * 1103515245 + 12345; uint32_t B = (seed >> 8) & ((1u << G.N) - 1) & ~(1u << d);
        int s[2] = {c, d}; uint32_t f[2] = {A, B};
        int r = orc2::query(G, 2, s, f) == 1;
        bool e = false;
        dec::enumerate(G, c, A, 0, [&](const dec::Decomp& D) {
          int qi = dec::path_end_at(D, c), qd = dec::path_end_at(D, d);
          if (dec::path_avoids(D[qi], A) && dec::path_avoids(D[qd], B)) { e = true; return true; }
          return false; });
        q++; if (r != (int)e) { bad++; printf("MISMATCH %s c=%d d=%d A=%u B=%u orc2=%d enum=%d\n", line, c, d, A, B, r, (int)e); }
      }
    }
  }
  printf("xcheck2 queries=%lld mismatches=%lld\n", q, bad);
}
