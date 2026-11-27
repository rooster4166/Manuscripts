/* ----- enumeration ----- */
static int do_pee = 1;
static long long cnt_inst, cnt_ptm_fail, cnt_ptm_und, cnt_r_tests, cnt_r_fail, cnt_r_und, cnt_pee_tests, cnt_pee_fail;
static long long cnt_par_inst, cnt_par_fail;     /* instances with a pair adjacent in G' */
static char cur_g6[256];

static int parse_g6(const char *s, int A[MAXN][MAXN]) {
  int N = s[0] - 63; if (N < 1 || N > MAXN - 1) return -1;
  int k = 0, bit = 0; const char *p = s + 1;
  for (int i = 0; i < N; i++) for (int j = 0; j < N; j++) A[i][j] = 0;
  for (int j = 1; j < N; j++) for (int i = 0; i < j; i++) {
    if (bit == 0) { if (!*p) return -1; k = *p++ - 63; bit = 6; }
    bit--; if ((k >> bit) & 1) A[i][j] = A[j][i] = 1;
  }
  return N;
}

static int connectedGF(void) {   /* G' + F connected */
  int seen[MAXN] = {0}, st[MAXN], sp = 0; seen[0] = 1; st[sp++] = 0; int c = 1;
  while (sp) { int x = st[--sp];
    for (int y = 0; y < gn; y++) { int adj = gadj[x][y];
      for (int k = 0; k < nf; k++) if ((fa[k] == x && fb[k] == y) || (fb[k] == x && fa[k] == y)) adj = 1;
      if (adj && !seen[y]) { seen[y] = 1; c++; st[sp++] = y; } } }
  return c == gn;
}
static int connectedGp(void) {
  int seen[MAXN] = {0}, st[MAXN], sp = 0; seen[0] = 1; st[sp++] = 0; int c = 1;
  while (sp) { int x = st[--sp]; for (int y = 0; y < gn; y++) if (gadj[x][y] && !seen[y]) { seen[y] = 1; c++; st[sp++] = y; } }
  return c == gn;
}

static void report(const char *kind, int k, int s) {
  printf("%s %s", kind, cur_g6);
  for (int i = 0; i < nf; i++) printf(" %d-%d%s", fa[i], fb[i], gadj[fa[i]][fb[i]] ? "*" : "");
  if (k >= 0) printf(" end=%d", s ? fb[k] : fa[k]);
  printf(" GFconn=%d\n", connectedGp());
  fflush(stdout);
}

static void test_instance(void) {
  buildJ();
  if (Jm > MAXM || gn + 1 > MAXN) return;
  cnt_inst++;
  int par = 0; for (int k = 0; k < nf; k++) if (gadj[fa[k]][fb[k]]) par = 1;
  if (par) cnt_par_inst++;
  int sh[16], known[16];
  int r0 = ptmq(NULL, sh);
  if (r0 == 2) { cnt_ptm_und++; report("UND", -1, 0); return; }
  if (r0 == 0) { cnt_ptm_fail++; if (par) cnt_par_fail++; report("PTMFAIL", -1, 0); return; }
  for (int k = 0; k < nf; k++) known[k] = sh[k];
  int rq[MAXN];
  for (int k = 0; k < nf; k++) for (int s = 0; s < 2; s++) {
    cnt_r_tests++;
    if ((known[k] >> s) & 1) continue;
    for (int v = 0; v <= gn; v++) rq[v] = -1;
    rq[s ? fb[k] : fa[k]] = gn;
    int r = ptmq(rq, sh);
    if (r == 1) { for (int j = 0; j < nf; j++) known[j] |= sh[j]; }
    else if (r == 0) { cnt_r_fail++; report("RFAIL", k, s); }
    else { cnt_r_und++; report("RUND", k, s); }
  }
  if (do_pee && nf <= 6) {
    for (int c = 0; c < (1 << nf); c++) {
      cnt_pee_tests++;
      for (int v = 0; v <= gn; v++) rq[v] = -1;
      for (int k = 0; k < nf; k++) rq[(c >> k) & 1 ? fb[k] : fa[k]] = gn;
      int r = ptmq(rq, sh);
      if (r == 0) cnt_pee_fail++;
    }
  }
}

/* simple mode: G all-odd; F ranges over matchings of size mm in E(G) */
static int GA[MAXN][MAXN];
static int ue[MAXM], ve2[MAXM], ne;
static void rec_match(int start, int need, int *usedv) {
  if (need == 0) {
    for (int u = 0; u < gn; u++) for (int v = 0; v < gn; v++) gadj[u][v] = GA[u][v];
    for (int k = 0; k < nf; k++) gadj[fa[k]][fb[k]] = gadj[fb[k]][fa[k]] = 0;
    test_instance();
    return;
  }
  for (int e = start; e < ne; e++) {
    int u = ue[e], v = ve2[e];
    if (usedv[u] || usedv[v]) continue;
    usedv[u] = usedv[v] = 1; fa[nf] = u; fb[nf] = v; nf++;
    rec_match(e + 1, need - 1, usedv);
    nf--; usedv[u] = usedv[v] = 0;
  }
}

/* pairing mode: G' given; F ranges over perfect matchings of Ev(G') */
static int evs[MAXN], nev;
static void rec_pair(int *usedv) {
  int i = 0; while (i < nev && usedv[evs[i]]) i++;
  if (i == nev) { if (connectedGF()) test_instance(); return; }
  usedv[evs[i]] = 1;
  for (int j = i + 1; j < nev; j++) if (!usedv[evs[j]]) {
    usedv[evs[j]] = 1; fa[nf] = evs[i]; fb[nf] = evs[j]; nf++;
    rec_pair(usedv);
    nf--; usedv[evs[j]] = 0;
  }
  usedv[evs[i]] = 0;
}

int main(int argc, char **argv) {
  char mode = argc > 1 ? argv[1][0] : 's';
  int mm = argc > 2 ? atoi(argv[2]) : 2;
  if (argc > 3) gbudget = strtoull(argv[3], 0, 10);
  if (argc > 4) do_pee = atoi(argv[4]);
  char line[1024];
  while (fgets(line, sizeof line, stdin)) {
    char *tok = strtok(line, " \t\n"); if (!tok) continue;
    if (tok[0] == '>') continue;
    snprintf(cur_g6, sizeof cur_g6, "%s", tok);
    if (mode == 's') {
      gn = parse_g6(tok, GA); if (gn < 0) continue;
      int odd = 1; for (int v = 0; v < gn; v++) { int d = 0; for (int w = 0; w < gn; w++) d += GA[v][w]; if (d % 2 == 0) odd = 0; }
      if (!odd) continue;
      ne = 0; for (int u = 0; u < gn; u++) for (int v = u + 1; v < gn; v++) if (GA[u][v]) { ue[ne] = u; ve2[ne] = v; ne++; }
      int usedv[MAXN] = {0}; nf = 0;
      rec_match(0, mm, usedv);
    } else if (mode == 'p') {
      gn = parse_g6(tok, gadj); if (gn < 0) continue;
      nev = 0; for (int v = 0; v < gn; v++) { int d = 0; for (int w = 0; w < gn; w++) d += gadj[v][w]; if (d % 2 == 0) evs[nev++] = v; }
      if (nev < 2 || (mm > 0 && nev != 2 * mm)) continue;
      int usedv[MAXN] = {0}; nf = 0;
      rec_pair(usedv);
    } else if (mode == 'f') {     /* line: g6(G') a1 b1 a2 b2 ... */
      gn = parse_g6(tok, gadj); if (gn < 0) continue;
      nf = 0; char *t;
      while ((t = strtok(NULL, " \t\n")) && nf < 16) { fa[nf] = atoi(t); t = strtok(NULL, " \t\n"); if (!t) break; fb[nf] = atoi(t); nf++; }
      test_instance();
    }
  }
  printf("SUMMARY inst=%lld ptm_fail=%lld ptm_und=%lld par_inst=%lld par_fail=%lld r_tests=%lld r_fail=%lld r_und=%lld pee_tests=%lld pee_fail=%lld verified=%lld badwit=%lld\n",
         cnt_inst, cnt_ptm_fail, cnt_ptm_und, cnt_par_inst, cnt_par_fail, cnt_r_tests, cnt_r_fail, cnt_r_und, cnt_pee_tests, cnt_pee_fail, nverified, nbadwit);
  return 0;
}
