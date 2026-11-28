/* rm.c -- root-move closure (moves M1, M2 of nodata Theorem 4.2) in C, for the order-11 data.

   Reads ND lines (as written by nd.c) and, for each (T1) root (J, z, r), searches breadth-first,
   to depth <= 6, the states reachable by
     M1: rho has <= 1 neighbour in T = N(z); w a neighbour of rho outside T + z:
         J' = J - rho w - z rho + z w, root w;
     M2: rho has exactly two neighbours u, v in T: J' = J - rho u - z rho - z u, root v;
   for a state (other than the start) in which J'[N(z)] has a perfect matching.
   Same semantics as rootmove2.py (cross-checked on n <= 9).  Prints a summary: counts by
   (tier, twins, reached).
   usage: rm < ND lines */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint32_t u32;
#define MAXN 16
static int N;
static int has_pm(const u32 *adj, u32 S) {
  if (!S) return 1;
  int a = __builtin_ctz(S); u32 S2 = S & ~(1u << a); u32 nb = adj[a] & S2;
  while (nb) { int b = __builtin_ctz(nb); nb &= nb - 1; if (has_pm(adj, S2 & ~(1u << b))) return 1; }
  return 0;
}
typedef struct { u32 adj[MAXN]; int rho, d; } state;
#define QCAP 200000
static state Q[QCAP];
#define HB 18
static uint64_t hkey[1 << HB]; static u32 hstamp[1 << HB]; static u32 stamp = 1;
static uint64_t hashst(const state *s) {
  uint64_t h = 1469598103934665603ULL ^ (uint64_t)s->rho;
  for (int i = 0; i < N; i++) { h ^= s->adj[i]; h *= 1099511628211ULL; }
  return h | 1;
}
static int seen_insert(uint64_t h) {
  for (u32 i = (u32)(h >> (64 - HB)), t = 0; t < 64; t++, i = (i + 1) & ((1 << HB) - 1)) {
    if (hstamp[i] != stamp) { hstamp[i] = stamp; hkey[i] = h; return 1; }
    if (hkey[i] == h) return 0;
  }
  return 1;
}
static int read_g6(const char *s, u32 *adj) {
  const unsigned char *p = (const unsigned char *)s;
  N = p[0] - 63; if (N < 1 || N > MAXN) return 0; p++;
  int bit = 0, cur = 0, k = 0;
  for (int v = 0; v < N; v++) adj[v] = 0;
  for (int j = 1; j < N; j++) for (int i = 0; i < j; i++) {
    if (bit == 0) { cur = p[k++] - 63; bit = 6; }
    bit--;
    if (cur >> bit & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
  }
  return 1;
}
static void del(u32 *a, int x, int y) { a[x] &= ~(1u << y); a[y] &= ~(1u << x); }
static void add(u32 *a, int x, int y) { a[x] |= 1u << y; a[y] |= 1u << x; }
int main(void) {
  static char line[4096];
  long long cnt[8][2][2]; memset(cnt, 0, sizeof cnt);
  while (fgets(line, sizeof line, stdin)) {
    if (strncmp(line, "ND ", 3)) continue;
    char g6[256]; int z, r, f[16];
    if (sscanf(line + 3, "%255s", g6) != 1) continue;
    char *rest = line + 3 + strlen(g6);
    char rc;
    if (sscanf(rest, "%d %d %d %d %d %d %d %d %d %c %d %d %d %d", &z, &r, &f[0], &f[1], &f[2], &f[3],
               &f[4], &f[5], &f[6], &rc, &f[7], &f[8], &f[9], &f[10]) != 14) continue;
    int twins = f[7] || f[8], level = f[10];
    stamp++;
    int qh = 0, qt = 0, found = 0;
    if (!read_g6(g6, Q[0].adj)) continue;
    Q[0].rho = r; Q[0].d = 0; qt = 1; seen_insert(hashst(&Q[0]));
    while (qh < qt && !found) {
      state *s = &Q[qh++];
      u32 T = s->adj[z];
      if (s->d > 0 && has_pm(s->adj, T)) { found = 1; break; }
      if (s->d >= 6) continue;
      int rho = s->rho;
      u32 tn = s->adj[rho] & T;
      int ntn = __builtin_popcount(tn);
      if (ntn <= 1) {
        u32 ws = s->adj[rho] & ~T & ~(1u << z);
        while (ws) {
          int w = __builtin_ctz(ws); ws &= ws - 1;
          if (qt >= QCAP) break;
          state *t = &Q[qt]; *t = *s;
          del(t->adj, rho, w); del(t->adj, z, rho); add(t->adj, z, w);
          t->rho = w; t->d = s->d + 1;
          if (seen_insert(hashst(t))) qt++;
        }
      }
      if (ntn == 2) {
        int a = __builtin_ctz(tn), b = 31 - __builtin_clz(tn);
        for (int k = 0; k < 2; k++) {
          int u = k ? b : a, v = k ? a : b;
          if (qt >= QCAP) break;
          state *t = &Q[qt]; *t = *s;
          del(t->adj, rho, u); del(t->adj, z, rho); del(t->adj, z, u);
          t->rho = v; t->d = s->d + 1;
          if (seen_insert(hashst(t))) qt++;
        }
      }
    }
    cnt[level][twins][found]++;
  }
  long long tot = 0, reach = 0;
  for (int l = 1; l <= 5; l++) for (int t = 0; t < 2; t++) {
    printf("tier %d twins %d: reached %lld, not %lld\n", l, t, cnt[l][t][1], cnt[l][t][0]);
    tot += cnt[l][t][0] + cnt[l][t][1]; reach += cnt[l][t][1];
  }
  printf("TOTAL %lld reached %lld\n", tot, reach);
  return 0;
}
