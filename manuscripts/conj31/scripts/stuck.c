/* stuck.c -- which PC instances admit none of the proved reduction moves?
 *
 *   stuck MAXZ < 2conn.g6      (MAXZ = 2: exactly two zeros; 1: one zero)
 *
 * Instance: 2-connected B, zero set Z (positive even degree), profile b with
 * b = 0 on Z, 1 <= b(x) <= d(x), b(x) == d(x) mod 2 off Z, and (DB).
 * Moves (each reduces to a smaller instance of the same kind; see the manuscript):
 *   CYC  B is a cycle (base case).
 *   EAR  a removable thread (interior vertices of degree 2, B - interior 2-connected)
 *        with a vertex of b = 2 in its interior.
 *   SUP  a thread whose interior lies in Z, with non-adjacent ends (suppress it).
 *   TR   a removable edge xy (B - xy 2-connected), the end moving to y:
 *        b(y) >= 1, b(x) <= d(x) - 2, |Z0| <= 2 where Z0 = (Z - x) + (y if b(y) = 1),
 *        and |N(y) cap Z0| <= b(x)   (Fan's lemma),
 *   NEW  a removable edge xy as a one-edge path: b(x), b(y) >= 1, |Z0| <= 2 where
 *        Z0 = Z + {x : b(x) = 1} + {y : b(y) = 1}, and slack(w) >= 2 for w != x, y.
 *   TRI  a zero u of degree 2 with N(u) = {x,y}, xy an edge, B - u 2-connected, the end
 *        moving to y: x, y not in Z, b(x) <= d(x) - 2, and (y not adjacent to the other
 *        zero, or b(x) >= 2).  (B - u with b + 1_x - 1_y; subdivide xy; Fan at y.)
 *   SPL  a vertex x with b(x) = d(x) and B - x 2-connected: delete x; each neighbour y
 *        gets b(y)+1 (b(y) <= d(y)-2) or b(y)-1 (b(y) = d(y)); zeros of B - x: Z - N(x)
 *        plus new zeros; require |Z'| <= 2 and (DB) for the new profile.
 *   TW2  twin zeros u,v, uv not an edge, N(u) = N(v) = {x,y}, x not adjacent to y:
 *        B - u - v + xy with b - 1_x - 1_y (xy subdivided by u, plus the path x v y);
 *        require B - u - v + xy 2-connected, |Z'| <= 2, (DB).
 * Prints the stuck instances and a summary (with TWIN marking stuck instances whose
 * zeros are twins: N(u) - v = N(v) - u).
 */
#include <stdio.h>
#include "psolve.h"

static int n, deg[PS_MAXN], b[PS_MAXN], isz[PS_MAXN];
static uint32_t adj[PS_MAXN];
static char g6[256];
static long ninst, nstuck, cnt[10];

static int conn2(const uint32_t *a, uint32_t verts) {
  /* is the graph induced... a[] restricted to verts 2-connected (>=3 vertices)? */
  if (__builtin_popcount(verts) < 3) return 0;
  for (int c = -1; c < n; c++) {
    uint32_t all = verts;
    if (c >= 0) { if (!(verts >> c & 1)) continue; all &= ~(1u << c); }
    int st = __builtin_ctz(all);
    uint32_t comp = 1u << st, fr = comp;
    while (fr) {
      int y = __builtin_ctz(fr); fr &= fr - 1;
      uint32_t nb = a[y] & all & ~comp;
      comp |= nb; fr |= nb;
    }
    if (comp != all) return 0;
  }
  return 1;
}

/* threads */
static int nth, thlen[64], thv[64][PS_MAXN + 1], threm[64];
static int iscycle;

static void threads(void) {
  nth = 0; iscycle = 1;
  for (int x = 0; x < n; x++) if (deg[x] != 2) iscycle = 0;
  if (iscycle) return;
  uint32_t full = (1u << n) - 1;
  /* start from each vertex of degree >= 3 along each incident edge */
  static int used[PS_MAXN][PS_MAXN];
  memset(used, 0, sizeof used);
  for (int x = 0; x < n; x++) {
    if (deg[x] < 3) continue;
    for (uint32_t nb = adj[x]; nb; nb &= nb - 1) {
      int y = __builtin_ctz(nb);
      if (used[x][y]) continue;
      int L = 0; thv[nth][L++] = x;
      int prev = x, cur = y;
      while (deg[cur] == 2) {
        thv[nth][L++] = cur;
        uint32_t o = adj[cur] & ~(1u << prev);
        int nx = __builtin_ctz(o);
        prev = cur; cur = nx;
      }
      thv[nth][L++] = cur;
      used[x][thv[nth][1]] = 1; used[thv[nth][1]][x] = 1;
      used[cur][prev] = 1; used[prev][cur] = 1;
      thlen[nth] = L;
      /* removable? */
      uint32_t a2[PS_MAXN]; memcpy(a2, adj, sizeof a2);
      uint32_t verts = full;
      if (L == 2) { a2[x] &= ~(1u << cur); a2[cur] &= ~(1u << x); }
      else for (int i = 1; i < L - 1; i++) {
        int z = thv[nth][i]; verts &= ~(1u << z);
      }
      threm[nth] = conn2(a2, verts);
      nth++;
    }
  }
}

static int nZ(void) { int c = 0; for (int i = 0; i < n; i++) c += isz[i]; return c; }

static int check(void) {
  int S = 0;
  for (int i = 0; i < n; i++) S += b[i];
  if (iscycle) { cnt[0]++; return 1; }
  for (int t = 0; t < nth; t++) {
    int L = thlen[t];
    if (L > 2 && threm[t]) {
      for (int i = 1; i < L - 1; i++) if (!isz[thv[t][i]]) { cnt[1]++; return 1; }
    }
    if (L > 2) {
      int allz = 1;
      for (int i = 1; i < L - 1; i++) if (!isz[thv[t][i]]) allz = 0;
      int x0 = thv[t][0], xm = thv[t][L - 1];
      if (allz && x0 != xm && !(adj[x0] >> xm & 1)) { cnt[2]++; return 1; }
    }
  }
  for (int t = 0; t < nth; t++) {
    if (thlen[t] != 2 || !threm[t]) continue;
    int p = thv[t][0], q = thv[t][1];
    for (int o = 0; o < 2; o++) {
      int x = o ? q : p, y = o ? p : q;
      /* TR: end moves to y */
      if (b[y] >= 1 && b[x] <= deg[x] - 2) {
        uint32_t Z0 = 0;
        for (int i = 0; i < n; i++) if (isz[i]) Z0 |= 1u << i;
        Z0 &= ~(1u << x);
        if (b[y] == 1) Z0 |= 1u << y;
        uint32_t Ny = adj[y] & ~(1u << x);
        if (__builtin_popcount(Z0) <= 2 && __builtin_popcount(Ny & Z0) <= b[x]) { cnt[3]++; return 1; }
      }
    }
    if (b[p] >= 1 && b[q] >= 1) {
      int z = nZ() + (b[p] == 1) + (b[q] == 1);
      int ok = (z <= 2);
      for (int w = 0; w < n && ok; w++) if (w != p && w != q && S - deg[w] - b[w] < 2) ok = 0;
      if (ok) { cnt[4]++; return 1; }
    }
  }
  /* TRI */
  for (int u = 0; u < n; u++) {
    if (!isz[u] || deg[u] != 2) continue;
    int x = __builtin_ctz(adj[u]), y = 31 - __builtin_clz(adj[u]);
    if (!(adj[x] >> y & 1) || isz[x] || isz[y]) continue;
    uint32_t verts = ((1u << n) - 1) & ~(1u << u);
    if (!conn2(adj, verts)) continue;
    int oz = -1;
    for (int i = 0; i < n; i++) if (isz[i] && i != u) oz = i;
    for (int o = 0; o < 2; o++) {
      int a = o ? y : x, c = o ? x : y;   /* end moves to c */
      if (b[a] <= deg[a] - 2 && (oz < 0 || !(adj[c] >> oz & 1) || b[a] >= 2)) { cnt[5]++; return 1; }
    }
  }
  /* SPL */
  for (int x = 0; x < n; x++) {
    if (isz[x] || b[x] != deg[x]) continue;
    uint32_t verts = ((1u << n) - 1) & ~(1u << x);
    uint32_t a2[PS_MAXN]; memcpy(a2, adj, sizeof a2);
    for (int i = 0; i < n; i++) a2[i] &= ~(1u << x);
    a2[x] = 0;
    if (!conn2(a2, verts)) continue;
    int b2[PS_MAXN], S2 = 0, z2 = 0, ok = 1;
    for (int i = 0; i < n; i++) {
      if (i == x) { b2[i] = 0; continue; }
      b2[i] = b[i];
      if (adj[x] >> i & 1) b2[i] = (b[i] <= deg[i] - 2) ? b[i] + 1 : b[i] - 1;
      S2 += b2[i];
      if (b2[i] == 0) z2++;
    }
    if (z2 > 2) ok = 0;
    for (int i = 0; i < n && ok; i++) if (i != x && __builtin_popcount(a2[i]) + b2[i] > S2) ok = 0;
    if (ok) { cnt[6]++; return 1; }
  }
  /* TW2 */
  {
    int zz[2], k = 0;
    for (int i = 0; i < n; i++) if (isz[i] && k < 2) zz[k++] = i;
    if (k == 2) {
      int u = zz[0], v = zz[1];
      if (!(adj[u] >> v & 1) && adj[u] == adj[v] && deg[u] == 2) {
        int x = __builtin_ctz(adj[u]), y = 31 - __builtin_clz(adj[u]);
        if (!(adj[x] >> y & 1)) {
          uint32_t a2[PS_MAXN]; memcpy(a2, adj, sizeof a2);
          for (int i = 0; i < n; i++) a2[i] &= ~((1u << u) | (1u << v));
          a2[u] = a2[v] = 0; a2[x] |= 1u << y; a2[y] |= 1u << x;
          uint32_t verts = ((1u << n) - 1) & ~((1u << u) | (1u << v));
          int b2[PS_MAXN], S2 = 0, z2 = 0, ok = conn2(a2, verts);
          for (int i = 0; i < n; i++) {
            b2[i] = (i == u || i == v) ? 0 : b[i] - (i == x || i == y);
            if (i != u && i != v) { S2 += b2[i]; if (b2[i] == 0) z2++; }
          }
          if (z2 > 2) ok = 0;
          for (int i = 0; i < n && ok; i++)
            if (i != u && i != v && __builtin_popcount(a2[i]) + b2[i] > S2) ok = 0;
          if (ok) { cnt[7]++; return 1; }
        }
      }
    }
  }
  return 0;
}

static int istwin(void) {
  int zz[2], k = 0;
  for (int i = 0; i < n; i++) if (isz[i] && k < 2) zz[k++] = i;
  if (k < 2) return 0;
  uint32_t m = ~((1u << zz[0]) | (1u << zz[1]));
  return (adj[zz[0]] & m) == (adj[zz[1]] & m);
}

static void rec(int x) {
  if (x == n) {
    int S = 0;
    for (int i = 0; i < n; i++) S += b[i];
    for (int i = 0; i < n; i++) if (deg[i] + b[i] > S) return;
    ninst++;
    if (!check()) {
      nstuck++;
      printf("STUCK%s %s b=", istwin() ? "_TWIN" : "", g6);
      for (int i = 0; i < n; i++) printf(i ? ",%d" : "%d", b[i]);
      printf("\n");
    }
    return;
  }
  if (isz[x]) { b[x] = 0; rec(x + 1); return; }
  int lo = (deg[x] & 1) ? 1 : 2;
  for (int v = lo; v <= deg[x]; v += 2) { b[x] = v; rec(x + 1); }
}

int main(int argc, char **argv) {
  int maxz = argc > 1 ? atoi(argv[1]) : 2;
  char line[512];
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0;
    if (!line[0]) continue;
    strcpy(g6, line);
    if (!g6_decode(line, &n, adj)) continue;
    int ev[PS_MAXN], ne = 0;
    for (int x = 0; x < n; x++) {
      deg[x] = __builtin_popcount(adj[x]);
      if (deg[x] % 2 == 0) ev[ne++] = x;
    }
    threads();
    if (maxz == 2) {
      for (int i = 0; i < ne; i++)
        for (int j = i + 1; j < ne; j++) {
          memset(isz, 0, sizeof isz); isz[ev[i]] = isz[ev[j]] = 1; rec(0);
        }
    } else if (maxz == 1) {
      for (int i = 0; i < ne; i++) { memset(isz, 0, sizeof isz); isz[ev[i]] = 1; rec(0); }
    } else { memset(isz, 0, sizeof isz); rec(0); }
  }
  printf("instances %ld stuck %ld  [CYC %ld EAR %ld SUP %ld TR %ld NEW %ld TRI %ld SPL %ld TW2 %ld]\n", ninst, nstuck,
         cnt[0], cnt[1], cnt[2], cnt[3], cnt[4], cnt[5], cnt[6], cnt[7]);
  return 0;
}
