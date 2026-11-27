/* ===================== PTM driver (session claude/ptm) ===================== */

static u128 fullmask(void) { return m == 128 ? ~(u128)0 : (((u128)1 << m) - 1); }

static int gn;                       /* order of G' = G - F                                   */
static int gadj[MAXN][MAXN];         /* adjacency of G' (simple)                              */
static int nf, fa[16], fb[16];       /* the pairs of F                                        */
static int Jeu[MAXM], Jev[MAXM], Jm; /* edges of J = G' + z V(F), z = gn                      */

static void buildJ(void) {
  Jm = 0;
  for (int u = 0; u < gn; u++) for (int v = u + 1; v < gn; v++) if (gadj[u][v]) { Jeu[Jm] = u; Jev[Jm] = v; Jm++; }
  for (int i = 0; i < nf; i++) { Jeu[Jm] = fa[i]; Jev[Jm] = gn; Jm++; Jeu[Jm] = fb[i]; Jev[Jm] = gn; Jm++; }
}

static long long nverified, nbadwit;

/* independent check of a witness: paths partition E(J), are paths, one end at every v != z, none
   at z, every path through z is x z y ... with x an end and {x, y} a pair of F, and req honoured */
static int verify(const int *rq) {
  static int usedE[MAXM]; int endc[MAXN];
  memset(usedE, 0, sizeof usedE); memset(endc, 0, sizeof endc);
  int Z0 = gn;
  for (int i = 0; i < nwit; i++) {
    int L = witlen[i]; if (L < 2) return 0;
    int seen[MAXN] = {0}, zp = -1;
    for (int j = 0; j < L; j++) { int v = wit[i][j]; if (v < 0 || v >= n || seen[v]) return 0; seen[v] = 1; if (v == Z0) zp = j; }
    for (int j = 0; j + 1 < L; j++) { int e = eid[wit[i][j]][wit[i][j + 1]]; if (e < 0 || usedE[e]) return 0; usedE[e] = 1; }
    endc[wit[i][0]]++; endc[wit[i][L - 1]]++;
    if (zp >= 0) {
      if (zp == 0 || zp == L - 1) return 0;
      int x = wit[i][zp - 1], y = wit[i][zp + 1];
      int ok = 0; for (int k = 0; k < nf; k++) if ((fa[k] == x && fb[k] == y) || (fa[k] == y && fb[k] == x)) ok = 1;
      if (!ok) return 0;
      if (!(zp == 1 || zp == L - 2)) return 0;              /* star-terminal */
    }
    if (rq) for (int s = 0; s < 2; s++) { int v = s ? wit[i][L - 1] : wit[i][0]; int nb = s ? wit[i][L - 2] : wit[i][1];
      if (rq[v] >= 0 && rq[v] != nb) return 0; }
  }
  for (int e = 0; e < m; e++) if (!usedE[e]) return 0;
  for (int v = 0; v < n; v++) if (endc[v] != (v == Z0 ? 0 : 1)) return 0;
  return 1;
}

/* short[i] bit 0: fa[i] short, bit 1: fb[i] short, read off the witness */
static void shortsOf(int *sh) {
  for (int k = 0; k < nf; k++) sh[k] = 0;
  for (int i = 0; i < nwit; i++) {
    int L = witlen[i], zp = -1;
    for (int j = 0; j < L; j++) if (wit[i][j] == gn) zp = j;
    if (zp < 0) continue;
    int x = wit[i][zp - 1], y = wit[i][zp + 1];
    for (int k = 0; k < nf; k++) {
      if (zp == 1) { if (wit[i][0] == fa[k]) sh[k] |= 1; if (wit[i][0] == fb[k]) sh[k] |= 2; }
      if (zp == L - 2) { if (wit[i][L - 1] == fa[k]) sh[k] |= 1; if (wit[i][L - 1] == fb[k]) sh[k] |= 2; }
    }
    (void)x; (void)y;
  }
}

static unsigned long long gbudget = 0; static uint64_t gseed = 1;

/* PTM query with optional prescribed short ends: rq[v] = gn means v must be short.
   Returns 1/0/2 (2 = budget exhausted on every retry). On 1 fills sh[]. */
static int ptmq(const int *rq, int *sh) {
  for (int attempt = 0; attempt < (gbudget ? 6 : 1); attempt++) {
    n = gn + 1; m = Jm;
    for (int i = 0; i < n; i++) { inc[i] = 0; for (int j = 0; j < n; j++) eid[i][j] = -1; }
    for (int e = 0; e < m; e++) { eu[e] = Jeu[e]; ev[e] = Jev[e]; eid[eu[e]][ev[e]] = eid[ev[e]][eu[e]] = e;
      inc[eu[e]] |= (u128)1 << e; inc[ev[e]] |= (u128)1 << e; }
    Z = gn; R = -1; STAR = 1; THR = 99;
    use_m = 1; for (int v = 0; v < n; v++) pmask[v] = 0;
    for (int k = 0; k < nf; k++) { pmask[fa[k]] = 1u << fb[k]; pmask[fb[k]] = 1u << fa[k]; }
    use_t = 1; for (int v = 0; v < n; v++) { req[v] = rq ? rq[v] : -1; forb[v] = -1; }
    for (int v = 0; v < n; v++) b[v] = (v == Z) ? 0 : 1;
    want_witness = 1; nwit = 0; pd = 0; plens[0] = 0;
    hreset();
    for (int v = 0; v < n; v++) ord[v] = v;
    budget = gbudget ? gbudget << (2 * (attempt / 2)) : 0; nodes = 0; aborted = 0;
    if (gbudget) {
      rng_state = (gseed++) * 0x9E3779B97F4A7C15ULL + 12345;
      for (int v = n - 1; v > 0; v--) { int j = (int)(rnd() % (unsigned)(v + 1)); int t = ord[v]; ord[v] = ord[j]; ord[j] = t; }
    }
    rem = fullmask(); bal = 0; rshort = 0;
    int r = solve();
    if (aborted) continue;
    if (r == 1) {
      nverified++;
      if (!verify(rq)) { nbadwit++; fprintf(stderr, "BAD WITNESS\n"); }
      shortsOf(sh);
    }
    return r;
  }
  return 2;
}
