/* encode.c (session claude/ptm): for every all-odd graph G (g6, stdin) and every matching F of
   M edges of G, print the graph H = G with each F-edge subdivided by a vertex s_i carrying two
   pendant leaves.  s_i is the only vertex of even degree (4), so isomorphism classes of H are
   isomorphism classes of pairs (G, F).  Pipe through nauty-labelg and sort -u, then decode.py. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MX 64
static int N, A[MX][MX], M;
static int eu[MX * MX], ev[MX * MX], ne;
static int fu[8], fv[8], nf;
static void out(void) {
  int n2 = N + 3 * M, B[MX][MX];
  memset(B, 0, sizeof B);
  for (int i = 0; i < N; i++) for (int j = 0; j < N; j++) B[i][j] = A[i][j];
  for (int k = 0; k < M; k++) {
    int s = N + 3 * k;
    B[fu[k]][fv[k]] = B[fv[k]][fu[k]] = 0;
    B[s][fu[k]] = B[fu[k]][s] = B[s][fv[k]] = B[fv[k]][s] = 1;
    B[s][s + 1] = B[s + 1][s] = B[s][s + 2] = B[s + 2][s] = 1;
  }
  char buf[4096]; int p = 0; buf[p++] = 63 + n2;
  int k = 0, bit = 0;
  for (int j = 1; j < n2; j++) for (int i = 0; i < j; i++) {
    k = (k << 1) | B[i][j]; bit++;
    if (bit == 6) { buf[p++] = 63 + k; k = 0; bit = 0; }
  }
  if (bit) { k <<= (6 - bit); buf[p++] = 63 + k; }
  buf[p] = 0; puts(buf);
}
static void rec(int start, int need, int *used) {
  if (!need) { out(); return; }
  for (int e = start; e < ne; e++) {
    if (used[eu[e]] || used[ev[e]]) continue;
    used[eu[e]] = used[ev[e]] = 1; fu[nf] = eu[e]; fv[nf] = ev[e]; nf++;
    rec(e + 1, need - 1, used);
    nf--; used[eu[e]] = used[ev[e]] = 0;
  }
}
int main(int argc, char **argv) {
  M = atoi(argv[1]);
  char line[1024];
  while (fgets(line, sizeof line, stdin)) {
    char *s = strtok(line, " \t\n"); if (!s) continue;
    N = s[0] - 63; int k = 0, bit = 0; char *q = s + 1;
    memset(A, 0, sizeof A);
    for (int j = 1; j < N; j++) for (int i = 0; i < j; i++) {
      if (!bit) { k = *q++ - 63; bit = 6; }
      bit--; if ((k >> bit) & 1) A[i][j] = A[j][i] = 1;
    }
    int odd = 1; for (int v = 0; v < N; v++) { int d = 0; for (int w = 0; w < N; w++) d += A[v][w]; if (!(d & 1)) odd = 0; }
    if (!odd) continue;
    ne = 0; for (int u = 0; u < N; u++) for (int v = u + 1; v < N; v++) if (A[u][v]) { eu[ne] = u; ev[ne] = v; ne++; }
    int used[MX] = {0}; nf = 0; rec(0, M, used);
  }
  return 0;
}
