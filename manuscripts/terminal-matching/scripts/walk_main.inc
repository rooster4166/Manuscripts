/* ===================== walk.c driver ===================== */
static u128 fullmask(void) { return m == 128 ? ~(u128)0 : (((u128)1 << m) - 1); }
static int GA[MAXN][MAXN], gn;
/* Lovasz decomposition of graph A (order N, profile = degree parity) with separated pairs */
static int sepq(int N, int A[MAXN][MAXN], int np, const int *pu, const int *pv) {
  n = N; m = 0;
  for (int i = 0; i < n; i++) { inc[i] = 0; for (int j = 0; j < n; j++) eid[i][j] = -1; }
  for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++) if (A[u][v]) {
    if (m >= MAXM) return -1;
    eu[m] = u; ev[m] = v; eid[u][v] = eid[v][u] = m; inc[u] |= (u128)1 << m; inc[v] |= (u128)1 << m; m++; }
  Z = -1; R = -1; STAR = 0; THR = 0; use_m = 0; use_t = 0;
  use_sep = 1; for (int v = 0; v < n; v++) sepm[v] = 0;
  for (int i = 0; i < np; i++) { sepm[pu[i]] |= 1u << pv[i]; sepm[pv[i]] |= 1u << pu[i]; }
  for (int v = 0; v < n; v++) { int d = 0; for (int w = 0; w < n; w++) d += A[v][w]; b[v] = d & 1; }
  want_witness = 0; nwit = 0; pd = 0; plens[0] = 0; hreset();
  for (int v = 0; v < n; v++) ord[v] = v;
  budget = 0; nodes = 0; aborted = 0; rem = fullmask(); bal = 0; rshort = 0;
  return solve();
}
static int parse_g6(const char *s, int A[MAXN][MAXN]) {
  int N = s[0] - 63; if (N < 1 || N > MAXN - 2) return -1;
  int k = 0, bit = 0; const char *p = s + 1;
  for (int i = 0; i < MAXN; i++) for (int j = 0; j < MAXN; j++) A[i][j] = 0;
  for (int j = 1; j < N; j++) for (int i = 0; i < j; i++) {
    if (bit == 0) { if (!*p) return -1; k = *p++ - 63; bit = 6; }
    bit--; if ((k >> bit) & 1) A[i][j] = A[j][i] = 1;
  }
  return N;
}
/* enumerate simple paths a1 -> y2 of length <= maxlen avoiding forbidden set, interior avoiding N(x2) */
static int MA[MAXN][MAXN];
static int pathv[MAXN], plen2, found;
static int a1, b1, x2, y2;
static long long tried;
static int try_path(void) {
  /* M = G - e1 - e2 - E(P) + l1@b1 ; l1 = gn */
  for (int u = 0; u <= gn; u++) for (int v = 0; v <= gn; v++) MA[u][v] = (u < gn && v < gn) ? GA[u][v] : 0;
  MA[a1][b1] = MA[b1][a1] = 0; MA[x2][y2] = MA[y2][x2] = 0;
  for (int i = 0; i + 1 < plen2; i++) { MA[pathv[i]][pathv[i + 1]] = MA[pathv[i + 1]][pathv[i]] = 0; }
  int l1 = gn; MA[l1][b1] = MA[b1][l1] = 1;
  int pu[3] = {x2, a1, l1}, pv[3] = {y2, l1, y2};
  tried++;
  return sepq(gn + 1, MA, 3, pu, pv);
}
static int maxlen;
static void dfs(int v, uint32_t vis) {
  if (found) return;
  if (v == y2) { if (try_path() == 1) found = 1; return; }
  if (plen2 > maxlen) return;
  for (int w = 0; w < gn && !found; w++) if (GA[v][w] && !(vis >> w & 1)) {
    if (w == b1 || w == x2) continue;
    if (w != y2 && GA[w][x2]) continue;        /* interior avoids N(x2) */
    if ((v == a1 && w == b1)) continue;
    pathv[plen2++] = w; dfs(w, vis | 1u << w); plen2--;
  }
}
int main(int argc, char **argv) {
  int extra = argc > 1 ? atoi(argv[1]) : 0;   /* allow paths up to shortest + extra */
  char line[1024]; long long inst = 0, okc = 0, nopath = 0;
  while (fgets(line, sizeof line, stdin)) {
    char *tok = strtok(line, " \t\n"); if (!tok) continue;
    char g6[256]; snprintf(g6, sizeof g6, "%s", tok);
    gn = parse_g6(tok, GA); if (gn < 0) continue;
    int fa_[2], fb_[2]; for (int i = 0; i < 2; i++) { fa_[i] = atoi(strtok(NULL, " \t\n")); fb_[i] = atoi(strtok(NULL, " \t\n")); }
    /* G = G' + F (input is G' = G - F as in ptm 'f' mode) */
    for (int i = 0; i < 2; i++) GA[fa_[i]][fb_[i]] = GA[fb_[i]][fa_[i]] = 1;
    inst++; found = 0; int anypath = 0;
    for (int cfg = 0; cfg < 8 && !found; cfg++) {
      int e = cfg >> 2, o1 = (cfg >> 1) & 1, o2 = cfg & 1;
      int A0 = fa_[e], B0 = fb_[e], X0 = fa_[1 - e], Y0 = fb_[1 - e];
      a1 = o1 ? B0 : A0; b1 = o1 ? A0 : B0; x2 = o2 ? Y0 : X0; y2 = o2 ? X0 : Y0;
      /* BFS distance from a1 to y2 under the walk constraints */
      int dist[MAXN]; for (int v = 0; v < gn; v++) dist[v] = -1;
      int q[MAXN], h = 0, t = 0; dist[a1] = 0; q[t++] = a1;
      while (h < t) { int v = q[h++]; if (v == y2) continue;
        for (int w = 0; w < gn; w++) if (GA[v][w] && dist[w] < 0) {
          if (w == b1 || w == x2) continue; if (w != y2 && GA[w][x2]) continue;
          dist[w] = dist[v] + 1; q[t++] = w; } }
      if (dist[y2] < 0) continue;
      anypath = 1;
      maxlen = dist[y2] + extra;
      plen2 = 1; pathv[0] = a1; dfs(a1, 1u << a1);
    }
    if (!anypath) nopath++;
    if (found) okc++; else printf("NOBASE %s %d %d %d %d anypath=%d\n", g6, fa_[0], fb_[0], fa_[1], fb_[1], anypath);
    fflush(stdout);
  }
  printf("SUMMARY inst=%lld base_ok=%lld nopath=%lld tried=%lld\n", inst, okc, nopath, tried);
  return 0;
}
