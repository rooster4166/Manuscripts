/* jcert.c -- Conjecture J via Conjecture 31: certified joint paths.
 *
 *   jcert [witness_file|- [bc]] < allodd.g6
 *
 * For every connected graph F with all degrees odd, every instance (c1,a1;c2,a2)
 * (four distinct vertices, c1 !~ a1, c2 !~ a2; unordered in the two pairs) in which
 * c1, c2 are joined in F - {a1,a2}, search the c1-c2 paths P of F - {a1,a2} for one with
 *   (L)  c1 or c2 isolated in K0 = F - E(P)   [K0 has <= 1 even vertex: Lovasz], or
 *   (C)  K0 minus isolated vertices is 2-connected and no odd vertex of K0 has degree
 *        |V(K0)| - 1                            [Conjecture 31 applies];
 *   with option "bc", failing (L) and (C) on every P, also
 *   (B)  K0 satisfies the block criterion BC (blockcrit.h)  [PC on the blocks applies].
 * Instances with no such P are printed (UNCERT).  As a check, the first certified P of
 * each instance is also solved exactly (K0 tight) and the decomposition plus P is
 * written as a witness line "g6 P paths... " for wcheck31.py (P is listed first).
 */
#include <stdio.h>
#include "psolve.h"
#include "blockcrit.h"

static int n; static uint32_t adj[PS_MAXN];
static int c1, c2, a1, a2;
static int path[PS_MAXN + 1], plen, found, ftype;
static uint32_t K0[PS_MAXN];
static long nodes;
static int usebc, pass;

static int is2c(const uint32_t *a, uint32_t verts) {
  if (__builtin_popcount(verts) < 3) return 0;
  for (int c = -1; c < n; c++) {
    uint32_t all = verts;
    if (c >= 0) { if (!(verts >> c & 1)) continue; all &= ~(1u << c); }
    uint32_t comp = 1u << __builtin_ctz(all), fr = comp;
    while (fr) { int y = __builtin_ctz(fr); fr &= fr - 1; uint32_t nb = a[y] & all & ~comp; comp |= nb; fr |= nb; }
    if (comp != all) return 0;
  }
  return 1;
}

static void test(void) {
  /* K0 = adj minus path edges */
  memcpy(K0, adj, sizeof K0);
  for (int i = 0; i + 1 < plen; i++) { int x = path[i], y = path[i + 1]; K0[x] &= ~(1u << y); K0[y] &= ~(1u << x); }
  if (!K0[c1] || !K0[c2]) { found = 1; ftype = 0; return; }
  uint32_t verts = 0; int n0 = 0;
  for (int x = 0; x < n; x++) if (K0[x]) { verts |= 1u << x; n0++; }
  if (pass == 1) {
    int t[PS_MAXN];
    for (int x = 0; x < n; x++) t[x] = __builtin_popcount(K0[x]) & 1;
    if (bc_check(n, K0, t)) { found = 1; ftype = 2; }
    return;
  }
  for (int x = 0; x < n; x++) { int d = __builtin_popcount(K0[x]); if ((d & 1) && d == n0 - 1) return; }
  if (is2c(K0, verts)) { found = 1; ftype = 1; }
}

static void dfs(int x, uint32_t vis) {
  if (found) return;
  nodes++;
  if (x == c2) { test(); return; }
  uint32_t nb = adj[x] & ~vis & ~((1u << a1) | (1u << a2));
  while (nb && !found) {
    int y = __builtin_ctz(nb); nb &= nb - 1;
    path[plen++] = y; dfs(y, vis | (1u << y)); if (found) return; plen--;
  }
}

int main(int argc, char **argv) {
  usebc = argc > 2 && !strcmp(argv[2], "bc");
  FILE *W = (argc > 1 && strcmp(argv[1], "-")) ? fopen(argv[1], "w") : NULL;
  char line[256];
  long ngraphs = 0, ninst = 0, njoined = 0, nL = 0, nC = 0, nB = 0, nun = 0, nbad = 0;
  static PS P;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0;
    if (!line[0] || !g6_decode(line, &n, adj)) continue;
    int allodd = 1;
    for (int x = 0; x < n; x++) if (!(__builtin_popcount(adj[x]) & 1)) allodd = 0;
    if (!allodd) continue;
    ngraphs++;
    for (c1 = 0; c1 < n; c1++) for (a1 = 0; a1 < n; a1++) for (c2 = 0; c2 < n; c2++) for (a2 = 0; a2 < n; a2++) {
      if (c1 == a1 || c1 == c2 || c1 == a2 || a1 == c2 || a1 == a2 || c2 == a2) continue;
      if ((adj[c1] >> a1 & 1) || (adj[c2] >> a2 & 1)) continue;
      /* unordered pairs: count each instance once */
      if (c1 > c2) continue;
      ninst++;
      found = 0; plen = 0; path[plen++] = c1;
      /* joined? */
      uint32_t avoid = (1u << a1) | (1u << a2), comp = 1u << c1, fr = comp;
      while (fr) { int y = __builtin_ctz(fr); fr &= fr - 1; uint32_t nb = adj[y] & ~avoid & ~comp; comp |= nb; fr |= nb; }
      if (!(comp >> c2 & 1)) continue;
      njoined++;
      pass = 0; dfs(c1, 1u << c1);
      if (!found && usebc) { pass = 1; plen = 1; dfs(c1, 1u << c1); }
      if (!found) { nun++; printf("UNCERT %s %d %d %d %d\n", line, c1, a1, c2, a2); continue; }
      if (ftype == 0) nL++; else if (ftype == 1) nC++; else nB++;
      /* exact check of the certified P: K0 tight */
      int b[PS_MAXN];
      for (int x = 0; x < n; x++) b[x] = __builtin_popcount(K0[x]) & 1;
      int r = ps_solve(&P, n, K0, b, 0);
      if (r != 1) { nbad++; printf("NOTTIGHT %s %d %d %d %d\n", line, c1, a1, c2, a2); continue; }
      if (W) {
        fprintf(W, "%s ", line);
        for (int i = 0; i < plen; i++) fprintf(W, i ? "-%d" : "%d", path[i]);
        for (int i = 0; i < P.npaths; i++) {
          fputc(' ', W);
          for (int j = 0; j < P.plen[i]; j++) fprintf(W, j ? "-%d" : "%d", P.pv[i][j]);
        }
        fprintf(W, " J=%d,%d,%d,%d\n", c1, a1, c2, a2);
      }
    }
  }
  if (W) fclose(W);
  printf("all-odd graphs %ld instances %ld joined %ld certified: Lovasz %ld Conj31 %ld BC %ld uncertified %ld; certified-but-not-tight %ld\n",
         ngraphs, ninst, njoined, nL, nC, nB, nun, nbad);
  return 0;
}
