/* pc_test.c -- test the profile form (PC) of Conjecture 31.
 *
 *   pc_test MAXZ [bmax [witness_file]] < graphs.g6
 *
 * For every graph read (intended: 2-connected), every set Z of exactly MAXZ
 * vertices of positive even degree (MAXZ = 0, 1 or 2), and every profile b with
 *   b(z) = 0 for z in Z,  b(x) == d(x) mod 2,  1 <= b(x) <= min(d(x), bmax)  otherwise,
 * compare "b is realisable" (exact solver) with the degree bound
 *   (DB)  d(x) + b(x) <= sum_y b(y)  for every x.
 * Prints every disagreement and a summary.  Realisable => (DB) always holds
 * (a path has at most two edges at x, one fewer per end at x), so the only
 * possible disagreement is (DB) true but not realisable.
 */
#include <stdio.h>
#include "psolve.h"

static int n, deg[PS_MAXN], b[PS_MAXN], isz[PS_MAXN], bmax;
static uint32_t adj[PS_MAXN];
static long nprof, ndb, nreal, nbad, nund;
static char g6[256];
static PS P;
static FILE *WF = NULL;

static void rec(int x) {
  if (x == n) {
    int S = 0;
    for (int i = 0; i < n; i++) S += b[i];
    int db = 1;
    for (int i = 0; i < n; i++) if (deg[i] + b[i] > S) db = 0;
    nprof++;
    if (!db) return;      /* (DB) false => not realisable; no need to solve */
    ndb++;
    int r = ps_solve(&P, n, adj, b, 50000000L);
    if (r == 1) {
      nreal++;
      if (WF) {
        fprintf(WF, "%s", g6);
        for (int i = 0; i < P.npaths; i++) {
          fputc(' ', WF);
          for (int j = 0; j < P.plen[i]; j++) fprintf(WF, j ? "-%d" : "%d", P.pv[i][j]);
        }
        fprintf(WF, " b=");
        for (int i = 0; i < n; i++) fprintf(WF, i ? ",%d" : "%d", b[i]);
        fputc('\n', WF);
      }
    }
    else if (r == 0) {
      nbad++;
      printf("BAD %s b=", g6);
      for (int i = 0; i < n; i++) printf(i ? ",%d" : "%d", b[i]);
      printf("\n"); fflush(stdout);
    } else nund++;
    return;
  }
  if (isz[x]) { b[x] = 0; rec(x + 1); return; }
  int lo = (deg[x] & 1) ? 1 : 2;
  for (int v = lo; v <= deg[x] && v <= bmax; v += 2) { b[x] = v; rec(x + 1); }
}

int main(int argc, char **argv) {
  int maxz = argc > 1 ? atoi(argv[1]) : 2;
  bmax = argc > 2 ? atoi(argv[2]) : 99;
  if (argc > 3) WF = fopen(argv[3], "w");
  char line[512];
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0;
    if (!line[0]) continue;
    strcpy(g6, line);
    if (!g6_decode(line, &n, adj)) continue;
    int ev[PS_MAXN], ne = 0;
    for (int x = 0; x < n; x++) {
      deg[x] = __builtin_popcount(adj[x]);
      if (deg[x] > 0 && deg[x] % 2 == 0) ev[ne++] = x;
    }
    if (maxz == 2) {
      for (int i = 0; i < ne; i++)
        for (int j = i + 1; j < ne; j++) {
          memset(isz, 0, sizeof isz);
          isz[ev[i]] = isz[ev[j]] = 1;
          rec(0);
        }
    } else if (maxz == 1) {
      for (int i = 0; i < ne; i++) { memset(isz, 0, sizeof isz); isz[ev[i]] = 1; rec(0); }
    } else { memset(isz, 0, sizeof isz); rec(0); }
  }
  printf("profiles %ld with-DB %ld realisable %ld DB-but-not-realisable %ld undecided %ld\n",
         nprof, ndb, nreal, nbad, nund);
  if (WF) fclose(WF);
  return 0;
}
