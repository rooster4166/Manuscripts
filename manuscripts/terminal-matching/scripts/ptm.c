/* ptm.c: exhaustive / random tests of the terminal-matching property PTM (session claude/ptm).

   PTM(G, F): G a (multi)graph with all degrees odd, F a matching of G (an F-edge may be parallel
   to an edge of G' = G - F).  Some Lovasz decomposition of G has every F-edge terminal at one of
   its ends and no path with two F-edges.  Tested through J = G' + z V(F) (STL-P, stl.tex Prop. 3.4):
   a star-terminal Lovasz decomposition of J whose transitions at z are exactly the pairs of F.
   The search engine is a verbatim copy of tools/stl.c (session claude/stl, validated there against
   brute force); every positive answer is re-checked here by an independent verifier.

   usage: ptm MODE M [BUDGET [PEE]]  < graphs.g6
     MODE s : input all-odd graphs G; F ranges over all matchings of M edges of G.
     MODE p : input graphs G'; F ranges over all perfect matchings of the even-degree vertices
              of G' (|Ev(G')| = 2M; M = 0: any size), with G' + F connected.  Pairs adjacent in G'
              are F-edges parallel to G'-edges (marked * in the output).
     MODE f : lines "g6(G') a1 b1 a2 b2 ...": one instance per line.
   Tests per instance: PTM (free ends); PTM(r) for every pair and every end x (x short, i.e. the
   F-edge terminal at x); PEE for all 2^M prescribed end choices (if PEE = 1, default).
   BUDGET = 0: exact.  Otherwise node budget per attempt, 6 attempts with growing budget and
   shuffled vertex orders; "UND" if all are cut off.
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 32
#define MAXM 128
typedef unsigned __int128 u128;

static int n, m;
static int eu[MAXM], ev[MAXM];
static int eid[MAXN][MAXN];
static u128 inc[MAXN];

typedef struct { u128 mask; u128 prof; int extra; } key_t2;
static key_t2 *tab; static uint32_t *used; static uint32_t stamp = 1; static size_t cap, cnt;
/* (ptm.c change: generation stamps instead of clearing the table on every query) */

static void hreset(void) {
  if (!tab) { cap = 1u << 16; tab = malloc(cap * sizeof(key_t2)); used = calloc(cap, sizeof(uint32_t)); }
  stamp++;
  if (stamp == 0) { memset(used, 0, cap * sizeof(uint32_t)); stamp = 1; }
  cnt = 0;
}
static size_t hh(u128 a, u128 bb, int x0) {
  uint64_t lo = (uint64_t)a, hi = (uint64_t)(a >> 64);
  uint64_t b = (uint64_t)bb ^ ((uint64_t)(bb >> 64) * 0x94D049BB133111EBULL);
  uint64_t x = lo * 0x9E3779B97F4A7C15ULL ^ (hi * 0xC2B2AE3D27D4EB4FULL) ^ (b + 0x632BE59BD9B4E019ULL + (lo << 6))
               ^ ((uint64_t)(x0 + 1000) * 0xD6E8FEB86659FD93ULL);
  x ^= x >> 31; x *= 0xBF58476D1CE4E5B9ULL; x ^= x >> 29;
  return (size_t)x;
}
static int hfind(u128 a, u128 b, int x0) {
  size_t i = hh(a, b, x0) & (cap - 1);
  while (used[i] == stamp) { if (tab[i].mask == a && tab[i].prof == b && tab[i].extra == x0) return 1; i = (i + 1) & (cap - 1); }
  return 0;
}
static void hgrow(void);
static void hadd(u128 a, u128 b, int x0) {
  if (cnt * 2 > cap) hgrow();
  size_t i = hh(a, b, x0) & (cap - 1);
  while (used[i] == stamp) i = (i + 1) & (cap - 1);
  used[i] = stamp; tab[i].mask = a; tab[i].prof = b; tab[i].extra = x0; cnt++;
}
static void hgrow(void) {
  size_t oc = cap; key_t2 *ot = tab; uint32_t *ou = used;
  cap *= 2; tab = malloc(cap * sizeof(key_t2)); used = calloc(cap, sizeof(uint32_t)); cnt = 0;
  for (size_t i = 0; i < oc; i++) if (ou[i] == stamp) hadd(ot[i].mask, ot[i].prof, ot[i].extra);
  free(ot); free(ou);
}

static int b[MAXN];
static u128 rem;
static int Z, R, STAR, THR;
static int bal;      /* #LL - #SS so far */
static int use_t, use_m;
static int req[MAXN], forb[MAXN];   /* terminal-edge constraints: a path ending at v must have
                                       terminal neighbour req[v] (if >= 0), never forb[v] (if >= 0) */
static uint32_t pmask[MAXN];        /* allowed transitions c - Z - w : (pmask[c] >> w) & 1 */
static int rshort;   /* r short so far */

static int ord[MAXN];
static unsigned long long budget, nodes;
static int aborted;
static uint64_t rng_state;
static uint64_t rnd(void) { rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17; return rng_state; }

static int popc(u128 x) { return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64)); }
static int ctz128(u128 x) { uint64_t lo = (uint64_t)x; return lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll((uint64_t)(x >> 64)); }
static int deg(int v) { return popc(rem & inc[v]); }
static u128 packb(void) { u128 p = 0; for (int v = 0; v < n; v++) p |= (u128)b[v] << (4 * v); return p; }

static int want_witness;
static int pbuf[MAXM][MAXN + 1];
static int plens[MAXM], pd;
#define pathbuf pbuf[pd]
#define plen plens[pd]
static int wit[MAXM][MAXN + 1], witlen[MAXM], nwit;

static int solve(void);

/* classify the just-closed path pathbuf[0..plen-1] (plen vertices); zp = index of Z or -1.
   returns delta bal, sets *rs = 1 if r is short on it */
static int classify(int zp, int *rs) {
  *rs = 0;
  if (zp < 0) return 0;
  int L = plen - 1;               /* edges */
  int sa = (zp == 1), sb = (L - zp == 1);
  if (R >= 0) {
    if (sa && pathbuf[0] == R) *rs = 1;
    if (sb && pathbuf[L] == R) *rs = 1;
  }
  if (sa && sb) return -1;
  if (!sa && !sb) return 1;
  return 0;
}

static int term_ok(int v, int nb) {
  if (!use_t) return 1;
  if (req[v] >= 0 && nb != req[v]) return 0;
  if (forb[v] >= 0 && nb == forb[v]) return 0;
  return 1;
}

/* a = start vertex, c = current vertex, vis = visited mask, zp = index of Z in path or -1 */
static int extend(int a, int c, uint32_t vis, int zp) {
  if (aborted) return 0;
  if (budget && ++nodes > budget) { aborted = 1; return 0; }
  /* star: if Z was entered at index >= 2, the vertex after Z must close the path */
  int mustclose = (STAR && zp >= 2 && c != Z);  /* we are past z: should have closed already */
  if (mustclose) return 0;
  int closeonly = (STAR && zp >= 2 && c == Z);
  for (int iw = 0; iw < n; iw++) {
    int w = ord[iw];
    if (vis >> w & 1) continue;
    int e = eid[c][w];
    if (e < 0 || !((rem >> e) & 1)) continue;
    if (use_m && c == Z && plen >= 2 && !((pmask[pathbuf[plen - 2]] >> w) & 1)) continue;
    if (use_t && plen == 1 && !term_ok(a, w)) continue;   /* first edge = terminal edge at a */
    rem &= ~((u128)1 << e);
    pathbuf[plen++] = w;
    int zp2 = (w == Z) ? plen - 1 : zp;
    if (b[w] > 0 && term_ok(w, c)) {
      int rs; int dbal = classify(zp2, &rs);
      int ok_close = 1;
      if (STAR && dbal > 0) ok_close = 0;
      if (ok_close) {
        int obal = bal, ors = rshort;
        bal += dbal; rshort |= rs;
        b[a]--; b[w]--;
        if (want_witness) { memcpy(wit[nwit], pathbuf, plen * sizeof(int)); witlen[nwit] = plen; nwit++; }
        pd++;
        int ok = solve();
        pd--;
        b[a]++; b[w]++;
        bal = obal; rshort = ors;
        if (ok) { rem |= (u128)1 << e; plen--; return 1; }
        if (want_witness) nwit--;
      }
    }
    if (!closeonly && (rem & inc[w])) {
      /* star pruning: entering Z at index >= 2 is fine only if we can close right after; checked inside */
      if (extend(a, w, vis | (1u << w), zp2)) { rem |= (u128)1 << e; plen--; return 1; }
    }
    plen--;
    rem |= (u128)1 << e;
  }
  return 0;
}

static int prune_ok(int *bestp) {
  int S = 0;
  for (int v = 0; v < n; v++) S += b[v];
  if (S & 1) return 0;
  int P = S / 2;
  int best = -1, bd = 999;
  for (int v = 0; v < n; v++) {
    int d = deg(v);
    if (b[v] > P || b[v] > d || d > 2 * P - b[v] || ((d - b[v]) & 1)) return 0;
    if (b[v] > 0 && d < bd) { bd = d; best = v; }
  }
  /* transition bound: each remaining pair of z-edges lowers bal by at most 1 */
  if (Z >= 0) {
    int rz = deg(Z) / 2;
    if (bal - rz + rshort > THR) return 0;
  }
  uint32_t seen = 0;
  for (int v = 0; v < n; v++) {
    if ((seen >> v & 1) || !(rem & inc[v])) continue;
    uint32_t comp = 1u << v, frontier = 1u << v;
    while (frontier) {
      int x = __builtin_ctz(frontier); frontier &= frontier - 1;
      u128 ex = rem & inc[x];
      while (ex) {
        int e = ctz128(ex); ex &= ex - 1;
        int y = eu[e] == x ? ev[e] : eu[e];
        if (!(comp >> y & 1)) { comp |= 1u << y; frontier |= 1u << y; }
      }
    }
    seen |= comp;
    int s = 0;
    for (int x = 0; x < n; x++) if (comp >> x & 1) s += b[x];
    if (s < 2) return 0;
  }
  if (bestp) *bestp = best;
  return 1;
}

static int solve(void) {
  int S = 0;
  for (int v = 0; v < n; v++) S += b[v];
  if (rem == 0) return S == 0 && bal + rshort <= THR;
  if (S == 0) return 0;
  int best;
  if (!prune_ok(&best)) return 0;
  u128 pk = packb();
  int ex = (bal + 64) * 2 + rshort;
  if (hfind(rem, pk, ex)) return 0;
  plen = 1; pathbuf[0] = best;
  int r = extend(best, best, 1u << best, best == Z ? 0 : -1);
  if (!r && !aborted) hadd(rem, pk, ex);
  return r;
}

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
