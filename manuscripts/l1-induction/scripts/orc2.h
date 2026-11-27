// orc2.h: exact oracle with several constrained paths.  Paths are grown in order from given start
// vertices s_1, ..., s_k (each must have odd degree), path i never entering mask F_i; if path i ends
// at a later start s_j, it must also avoid F_j (it is then path j as well).  The rest is decomposed
// with b = deg mod 2 by the memoised exact search of lind.h (orc::solve).
#pragma once
#include "lind.h"

namespace orc2 {
using namespace orc;
static int K; static int S[8]; static uint32_t F[8];
static int stage_grow(int i);
// grow path i from a=S[i], current end cur, visited vis
static int ext2(int i, int a, int cur, uint32_t vis, uint32_t pv) {
  if (aborted) return 0;
  if (budget && ++nodes > budget) { aborted = 1; return 0; }
  u128 ex = rem & inc[cur];
  while (ex) {
    int e = ctz128(ex); ex &= ex - 1;
    int w = eu[e] == cur ? ev[e] : eu[e];
    if (vis >> w & 1) continue;
    rem &= ~((u128)1 << e);
    if (bm >> w & 1) {
      // closing at w: if w is a later start, the path must avoid F of that start too
      bool okc = true;
      for (int j = i + 1; j < K; j++) if (S[j] == w && ((pv | (1u << w)) & F[j] & ~(1u << w))) okc = false;
      if (okc) {
        uint32_t sb = bm; bm &= ~((1u << a) | (1u << w));
        int ok = stage_grow(i + 1);
        bm = sb;
        if (ok) { rem |= (u128)1 << e; return 1; }
      }
    }
    if (rem & inc[w]) { if (ext2(i, a, w, vis | (1u << w), pv | (1u << w))) { rem |= (u128)1 << e; return 1; } }
    rem |= (u128)1 << e;
  }
  return 0;
}
static int stage_grow(int i) {
  while (i < K && !(bm >> S[i] & 1)) i++;   // start already used as an end
  if (i >= K) return solve();
  if (!prune_ok(NULL)) return 0;
  return ext2(i, S[i], S[i], (1u << S[i]) | F[i], 1u << S[i]);
}
static int query(const Gr& G, int k, const int* starts, const uint32_t* forb) {
  load(G); hreset(); nodes = 0; aborted = 0;
  rem = (m == 128) ? ~(u128)0 : (((u128)1 << m) - 1);
  bm = 0; for (int v = 0; v < n; v++) if (dg0[v] & 1) bm |= 1u << v;
  K = k; for (int i = 0; i < k; i++) { S[i] = starts[i]; F[i] = forb[i]; if (!(bm >> S[i] & 1)) return -1; if (F[i] >> S[i] & 1) return 0; }
  // note: the failure memo of solve() is keyed only on the remaining edges and end set, which is
  // valid because solve() has no path constraints.
  int r = stage_grow(0);
  if (aborted) return 2;
  return r;
}
}  // namespace orc2
