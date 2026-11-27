// orcb.h: exact oracle for extended avoidance instances (session claude/conj-n).
// (G, c, A, B) is good if some Lovasz decomposition of G (b(v) = d(v) mod 2) has
//   V(Q_c) disjoint from A, and the far end of Q_c not in B.
// Reuses the search engine of lind.h (namespace orc): the first path is grown from c, never
// entering A, and may stop only at an odd vertex outside B; the rest is the exact search of lind.h.
#pragma once
#include "lind.h"
namespace orcb {
using namespace orc;
static uint32_t Bmask;
static int extend0(int c, int cur, uint32_t vis) {
  if (aborted) return 0;
  if (budget && ++nodes > budget) { aborted = 1; return 0; }
  u128 ex = rem & inc[cur];
  while (ex) {
    int e = ctz128(ex); ex &= ex - 1;
    int w = eu[e] == cur ? ev[e] : eu[e];
    if (vis >> w & 1) continue;
    rem &= ~((u128)1 << e);
    if ((bm >> w & 1) && !(Bmask >> w & 1)) {
      uint32_t sb = bm; bm &= ~((1u << c) | (1u << w));
      int ok = solve(); bm = sb;
      if (ok) { rem |= (u128)1 << e; return 1; }
    }
    if (rem & inc[w]) { if (extend0(c, w, vis | (1u << w))) { rem |= (u128)1 << e; return 1; } }
    rem |= (u128)1 << e;
  }
  return 0;
}
// 1 good, 0 not, 2 budget, -1 c not odd
static int avoidB(const Gr& G, int c, uint32_t A, uint32_t B) {
  load(G);
  hreset(); nodes = 0; aborted = 0;
  rem = (m == 128) ? ~(u128)0 : (((u128)1 << m) - 1);
  bm = 0; for (int v = 0; v < n; v++) if (dg0[v] & 1) bm |= 1u << v;
  if (!(bm >> c & 1)) return -1;
  if (A >> c & 1) return 0;
  if (!prune_ok(NULL)) return 0;
  Bmask = B;
  int ok = extend0(c, c, (1u << c) | A);
  if (aborted) return 2;
  return ok;
}
}  // namespace orcb
