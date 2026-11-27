/* enum.c: print every Lovasz decomposition of each input graph (session claude/dl-one).
   Input lines: "n m u1 v1 ... um vm" (edge list).  Output: one line per decomposition, paths
   separated by '|', vertices by spaces; then a line "END count".  Stops after CAP decompositions
   (argv[1], default 200000) and prints "END CAP".  Exhaustive DFS: the path at the odd vertex of
   smallest index, over all its paths, recursively; no shortcut. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static int n, m, eu[128], ev[128], eid[32][32];
static uint32_t adj[32];
static u128 inc[32];
static long long cnt, cap;
static int stk[64][33], slen[64], depth;
static int deg(u128 E, int v) { u128 x = E & inc[v]; return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64)); }
static void rec(u128 E);
static void ext(u128 E, uint32_t need, int *path, int plen, uint32_t vis) {
  int x = path[plen - 1];
  for (int y = 0; y < n && cnt < cap; y++) {
    if (!((adj[x] >> y) & 1) || ((vis >> y) & 1)) continue;
    int e = eid[x][y];
    if (!((E >> e) & 1)) continue;
    u128 E2 = E & ~((u128)1 << e);
    path[plen] = y;
    if ((need >> y) & 1) {
      memcpy(stk[depth], path, (plen + 1) * sizeof(int)); slen[depth] = plen + 1; depth++;
      rec(E2);
      depth--;
    }
    ext(E2, need, path, plen + 1, vis | (1u << y));
  }
}
static void rec(u128 E) {
  if (E == 0) {
    cnt++;
    for (int i = 0; i < depth; i++) {
      for (int j = 0; j < slen[i]; j++) printf("%d%s", stk[i][j], j + 1 < slen[i] ? " " : "");
      printf("%s", i + 1 < depth ? "|" : "\n");
    }
    return;
  }
  uint32_t need = 0;
  for (int v = 0; v < n; v++) if (deg(E, v) & 1) need |= 1u << v;
  if (!need) return;
  int v = __builtin_ctz(need);
  int path[33]; path[0] = v;
  ext(E, need & ~(1u << v), path, 1, 1u << v);
}
int main(int argc, char **argv) {
  cap = argc > 1 ? atoll(argv[1]) : 200000;
  while (scanf("%d %d", &n, &m) == 2) {
    memset(adj, 0, sizeof adj); memset(inc, 0, sizeof inc);
    for (int e = 0; e < m; e++) {
      if (scanf("%d %d", &eu[e], &ev[e]) != 2) return 1;
      eid[eu[e]][ev[e]] = eid[ev[e]][eu[e]] = e;
      adj[eu[e]] |= 1u << ev[e]; adj[ev[e]] |= 1u << eu[e];
      inc[eu[e]] |= (u128)1 << e; inc[ev[e]] |= (u128)1 << e;
    }
    u128 E = 0; for (int e = 0; e < m; e++) E |= (u128)1 << e;
    cnt = 0; depth = 0;
    rec(E);
    if (cnt >= cap) printf("END CAP\n"); else printf("END %lld\n", cnt);
    fflush(stdout);
  }
  return 0;
}
