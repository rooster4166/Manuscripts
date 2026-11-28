/* blockcrit.h -- the block criterion (BC) for a prescribed end profile.
 *
 * Graph a[] on n vertices (vertices of degree 0 ignored), target t : V -> N with
 * t(x) == d(x) mod 2.  BC holds if there are block profiles b_B (B a block of the
 * graph, x in B) with
 *   b_B(x) = t(x) when x is not a cut vertex;  b_B(c) == d_B(c) mod 2, 0 <= b_B(c) <= d_B(c);
 *   at every cut vertex c (blocks B_1..B_k at c, M = sum_i b_{B_i}(c)):
 *        M >= t(c),  M == t(c) mod 2,  2 max_i b_{B_i}(c) <= M + t(c)       (gluing);
 *   every block B that is a single edge has b_B = (1,1);
 *   every 2-connected block B has at most two zeros (b_B(x) = 0) and satisfies
 *        (DB)  d_B(x) + b_B(x) <= sum_{y in B} b_B(y)  for all x in B.
 * Gluing is exact (paths of different blocks meet only in cut vertices), so if PC holds
 * for every 2-connected block, BC implies that t is realisable.
 */
#include <stdint.h>
#include <string.h>

#define BC_MAXB 32
static int bc_n, bc_nb, bc_bsz[BC_MAXB], bc_bv[BC_MAXB][16];
static uint32_t bc_bmask[BC_MAXB], bc_a[16];
static int bc_t[16], bc_iscut[16];
static int bc_inc_b[64], bc_inc_v[64], bc_ninc;   /* (block, cut vertex) incidences */
static int bc_val[BC_MAXB][16];                    /* current block profile */

/* biconnected components (Tarjan, edge stack) */
static int bc_disc[16], bc_low[16], bc_time, bc_es[256][2], bc_esp;
static void bc_dfs(int u, int p) {
  bc_disc[u] = bc_low[u] = ++bc_time;
  for (uint32_t nb = bc_a[u]; nb; nb &= nb - 1) {
    int v = __builtin_ctz(nb);
    if (!bc_disc[v]) {
      bc_es[bc_esp][0] = u; bc_es[bc_esp][1] = v; bc_esp++;
      bc_dfs(v, u);
      if (bc_low[v] < bc_low[u]) bc_low[u] = bc_low[v];
      if (bc_low[v] >= bc_disc[u]) {
        uint32_t m = 0;
        while (1) {
          bc_esp--; m |= (1u << bc_es[bc_esp][0]) | (1u << bc_es[bc_esp][1]);
          if (bc_es[bc_esp][0] == u && bc_es[bc_esp][1] == v) break;
        }
        bc_bmask[bc_nb++] = m;
      }
    } else if (v != p && bc_disc[v] < bc_disc[u]) {
      bc_es[bc_esp][0] = u; bc_es[bc_esp][1] = v; bc_esp++;
      if (bc_disc[v] < bc_low[u]) bc_low[u] = bc_disc[v];
    }
  }
}

static int bc_dB(int B, int x) { return __builtin_popcount(bc_a[x] & bc_bmask[B]); }

static int bc_block_ok(int B) {
  int sz = bc_bsz[B];
  if (sz == 2) { return bc_val[B][bc_bv[B][0]] == 1 && bc_val[B][bc_bv[B][1]] == 1; }
  int S = 0, z = 0;
  for (int i = 0; i < sz; i++) { int x = bc_bv[B][i]; S += bc_val[B][x]; if (bc_val[B][x] == 0) z++; }
  if (z > 2) return 0;
  for (int i = 0; i < sz; i++) { int x = bc_bv[B][i]; if (bc_dB(B, x) + bc_val[B][x] > S) return 0; }
  return 1;
}

static int bc_glue_ok(int c) {
  int M = 0, mx = 0;
  for (int B = 0; B < bc_nb; B++) if (bc_bmask[B] >> c & 1) { int v = bc_val[B][c]; M += v; if (v > mx) mx = v; }
  return M >= bc_t[c] && ((M - bc_t[c]) % 2 == 0) && 2 * mx <= M + bc_t[c];
}

static int bc_rec(int i) {
  if (i == bc_ninc) {
    for (int B = 0; B < bc_nb; B++) if (!bc_block_ok(B)) return 0;
    for (int c = 0; c < bc_n; c++) if (bc_iscut[c] && !bc_glue_ok(c)) return 0;
    return 1;
  }
  int B = bc_inc_b[i], c = bc_inc_v[i], d = bc_dB(B, c);
  for (int v = d & 1; v <= d; v += 2) {
    bc_val[B][c] = v;
    if (bc_rec(i + 1)) return 1;
  }
  return 0;
}

/* returns 1 if BC holds */
static int bc_check(int n, const uint32_t *a, const int *t) {
  bc_n = n; memcpy(bc_a, a, n * sizeof(uint32_t)); memcpy(bc_t, t, n * sizeof(int));
  memset(bc_disc, 0, sizeof bc_disc); bc_time = 0; bc_esp = 0; bc_nb = 0;
  for (int x = 0; x < n; x++) if (a[x] && !bc_disc[x]) bc_dfs(x, -1);
  int cntB[16] = {0};
  for (int B = 0; B < bc_nb; B++) {
    bc_bsz[B] = 0;
    for (int x = 0; x < n; x++) if (bc_bmask[B] >> x & 1) { bc_bv[B][bc_bsz[B]++] = x; cntB[x]++; }
  }
  bc_ninc = 0;
  for (int x = 0; x < n; x++) bc_iscut[x] = cntB[x] > 1;
  for (int B = 0; B < bc_nb; B++)
    for (int i = 0; i < bc_bsz[B]; i++) {
      int x = bc_bv[B][i];
      if (bc_iscut[x]) { bc_inc_b[bc_ninc] = B; bc_inc_v[bc_ninc] = x; bc_ninc++; }
      else bc_val[B][x] = t[x];
    }
  return bc_rec(0);
}
