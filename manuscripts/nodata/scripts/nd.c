/* nd.c -- roots without matching data (nodata session).

   Reads graph6 (n <= 16).  Mode -t1: keeps the 3-connected J with exactly one even vertex z
   (and delta >= 3); every r in N(z) is an instance of (T1).  Mode -t2: keeps the 3-connected J
   whose only even vertices are an adjacent pair; both orientations (z, r) are instances of (T2).
   An instance has *matching data* if J[N(z)] has a perfect matching (for (T1) and (T2) alike).

   For every instance WITHOUT matching data (or every instance with -a) it prints one line
     ND g6 z r d(z) nu def |D| |A| |C| ncomp rclass twinR twinO tri level excess
   where nu = nu(J[N(z)]), def = d(z) - 2 nu, (D, A, C) is the Gallai-Edmonds decomposition of
   J[N(z)], ncomp the number of (odd) components of J[N(z)][D], rclass in {D,A,C} the class of r,
   twinR = 1 if r has a twin in N(z) (same J-neighbourhood, J-degree 3), twinO = 1 if two vertices
   of N(z) - r are such twins, tri = 1 if (T1) triangle data exist (a perfect matching of
   J[N(z) - {r, w}] for some w), level = the first tier at which an all-odd base exists:
     1  Phi a linear forest with components of length <= 2, rooted at ends (no siblings), r a root
     2  Phi a linear forest (vertex-disjoint T-paths with interiors outside T), rooted at ends
     3  Phi any forest T-join, r a root
     4  Phi any forest T-join, r a child with c(r) >= 2
     5  none (every forest T-join and every rooting tried)
   and excess = sum_v max(0, c(v) - 1) of the base found (tiers 3, 4 are searched by increasing
   excess, so it is the least excess of a base in that tier; tiers 1-2 have excess 0).
   followed by the witness "| par p0 .. p_{n-1} | D0 paths |" (p_v = parent or -1) when found.
   The base graph is H = (J - z) - Phi for (T1) and M = H + zr for (T2); both have no even vertex.
   Tiers 1-2 are enumerated exhaustively (every linkage, every end-rooting); tiers 3-4 enumerate
   every forest T-join of J - z (edge recursion with acyclicity and final-parity pruning) and every
   rooting.  The solver (ndsolve.h) is exact.  Options: -L k = stop after tier k (report k+1 =
   "not within tiers <= k").
   -D file cap every: write every `every`-th solver query (at most cap) to file in route_ext query-C
   format, and our answers to file.ans (for cross-checks).
   -b: (T1) only; the input graphs are B = J - z, and J = B + z (z joined to the even vertices).
   -x: do not require 3-connectivity or minimum degree 3 (the lifts do not use them).
   usage: nd -t1|-t2 [-a] [-b] [-L k] [-D file cap every] < graph6 */
#include <stdio.h>
#include "ndsolve.h"

#define MAXN 16
static int N;
static u32 adj[MAXN];
static char g6line[256];

static int read_g6(const char *s) {
  const unsigned char *p = (const unsigned char *)s;
  N = p[0] - 63;
  if (N < 1 || N > MAXN) return 0;
  p++;
  int bit = 0, cur = 0, k = 0;
  for (int v = 0; v < N; v++) adj[v] = 0;
  for (int j = 1; j < N; j++)
    for (int i = 0; i < j; i++) {
      if (bit == 0) { cur = p[k++] - 63; bit = 6; }
      bit--;
      if (cur >> bit & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
    }
  return 1;
}

static int connected_mask(u32 S) {        /* is J[S] connected (S nonempty)? */
  if (!S) return 1;
  u32 seen = S & -S, fr = seen;
  while (fr) {
    int x = __builtin_ctz(fr); fr &= fr - 1;
    u32 nb = adj[x] & S & ~seen;
    seen |= nb; fr |= nb;
  }
  return seen == S;
}
static int three_connected(void) {
  u32 all = (N == 32) ? ~0u : ((1u << N) - 1);
  if (N < 4 || !connected_mask(all)) return 0;
  for (int a = 0; a < N; a++)
    for (int b = a + 1; b < N; b++)
      if (!connected_mask(all & ~(1u << a) & ~(1u << b))) return 0;
  return 1;
}

/* ---- matchings in J[S] ---- */
static int nu_mask(u32 S) {               /* maximum matching size of J[S] */
  if (!S) return 0;
  int a = __builtin_ctz(S);
  u32 S2 = S & ~(1u << a);
  int best = nu_mask(S2);                 /* a unmatched */
  u32 nb = adj[a] & S2;
  while (nb) {
    int b = __builtin_ctz(nb); nb &= nb - 1;
    int t = 1 + nu_mask(S2 & ~(1u << b));
    if (t > best) best = t;
  }
  return best;
}
static int has_pm(u32 S) {
  if (!S) return 1;
  int a = __builtin_ctz(S);
  u32 S2 = S & ~(1u << a);
  u32 nb = adj[a] & S2;
  while (nb) {
    int b = __builtin_ctz(nb); nb &= nb - 1;
    if (has_pm(S2 & ~(1u << b))) return 1;
  }
  return 0;
}

/* ---- the instance ---- */
static int Z, R, MODE;     /* MODE 1 = (T1), 2 = (T2) */
static u32 T, Vb;          /* T = N(z), Vb = V(J) - z */
static int bu[128], bv[128], bm;    /* edges of B = J - z */
static int lastat[MAXN];

/* solve the base for parent map par[] (-1 = root / not in Phi), forest edge mask phim */
static int par[MAXN];
static long long ncalls;
static FILE *dumpf; static long long dumpcap, ndumped; static int dumpevery = 1;
static int base_ok(u64 phim) {
  ncalls++;
  sinit(N);
  for (int e = 0; e < bm; e++) if (!(phim >> e & 1)) sadd(bu[e], bv[e]);
  if (MODE == 2) sadd(Z, R);
  sneed = Vb | (MODE == 2 ? (1u << Z) : 0);
  for (int v = 0; v < N; v++) if (par[v] >= 0) crv[v] |= 1u << par[v];
  int res = srun();
  if (dumpf && ndumped < dumpcap && ncalls % dumpevery == 0) {
    /* the same query in route_ext query-C format, followed by our answer */
    fprintf(dumpf, "C %d %d", N, sm);
    for (int e = 0; e < sm; e++) fprintf(dumpf, " %d %d", seu[e], sev[e]);
    for (int v = 0; v < N; v++) fprintf(dumpf, " %d", (sneed >> v) & 1);
    for (int v = 0; v < N; v++) fprintf(dumpf, " %u", crv[v]);
    fprintf(dumpf, "\n");
    ndumped++;
    fprintf(stderr, "%s", "");
    extern FILE *ansf; fprintf(ansf, "%d\n", res);
  }
  return res;
}
FILE *ansf;

static int univ;            /* -U: try every structure, count failures, print failing ones */
static long long u_tot[6], u_fail[6]; static int u_tier;
static int found_level;
static int found_par[MAXN];
static int found_np, found_paths[SMAXM][SMAXN + 1], found_len[SMAXM];
static void save_found(int level) {
  found_level = level;
  memcpy(found_par, par, sizeof(par));
  found_np = wn;
  for (int i = 0; i < wn; i++) { found_len[i] = wlen[i]; memcpy(found_paths[i], wpath[i], wlen[i] * sizeof(int)); }
}

/* ---- tiers 1-2: linkages ---- */
static int eidB[MAXN][MAXN];
static int lk_maxlen;      /* max path length (edges); 0 = unbounded */
static int lk_npaths, lk_path[MAXN + 1][MAXN + 1], lk_plen[MAXN + 1];
static int lk_done;

static int u_skip_short;
static int try_linkage_rootings(void) {
  /* each path: root at one end; the path containing R is rooted at R */
  int np = lk_npaths;
  if (u_skip_short) { int lng = 0; for (int i = 0; i < np; i++) if (lk_plen[i] > 3) lng = 1; if (!lng) return 0; }
  for (int mask = 0; mask < (1 << np); mask++) {
    int okm = 1;
    for (int i = 0; i < np; i++) {
      int *P = lk_path[i]; int L = lk_plen[i];
      int rootfirst = !(mask >> i & 1);
      if (P[0] == R && !rootfirst) { okm = 0; break; }
      if (P[L - 1] == R && rootfirst) { okm = 0; break; }
    }
    if (!okm) continue;
    for (int v = 0; v < N; v++) par[v] = -1;
    u64 phim = 0;
    for (int i = 0; i < np; i++) {
      int *P = lk_path[i]; int L = lk_plen[i];
      int rootfirst = !(mask >> i & 1);
      for (int j = 0; j + 1 < L; j++) {
        phim |= 1ULL << eidB[P[j]][P[j + 1]];
        if (rootfirst) par[P[j + 1]] = P[j]; else par[P[j]] = P[j + 1];
      }
    }
    if (univ) {
      u_tot[u_tier]++;
      if (!base_ok(phim)) {
        u_fail[u_tier]++;
        printf("UFAIL %s %d %d tier %d par", g6line, Z, R, u_tier);
        for (int v = 0; v < N; v++) printf(" %d", par[v]);
        printf("\n");
      }
      continue;
    }
    if (base_ok(phim)) return 1;
  }
  return 0;
}

/* the path under construction is lk_path[lk_npaths] (a per-depth buffer), of lk_clen vertices */
static int lk_clen;
static int lk_rec(u32 U, u32 used);
static int lk_dfs(u32 U, u32 used, int a) {
  int *cur = lk_path[lk_npaths];
  int c = cur[lk_clen - 1];
  u32 nb = adj[c] & Vb;
  while (nb) {
    int y = __builtin_ctz(nb); nb &= nb - 1;
    if ((U >> y & 1) && y != a) {
      cur[lk_clen] = y;
      lk_plen[lk_npaths] = lk_clen + 1;
      lk_npaths++;
      int save = lk_clen;
      int r = lk_rec(U & ~(1u << a) & ~(1u << y), used);
      lk_clen = save;
      if (r) return 1;
      lk_npaths--;
    } else if (!(T >> y & 1) && !(used >> y & 1)) {
      if (lk_maxlen && lk_clen >= lk_maxlen) continue;   /* the path would exceed lk_maxlen edges */
      cur[lk_clen++] = y;
      if (lk_dfs(U, used | (1u << y), a)) return 1;
      lk_clen--;
    }
  }
  return 0;
}
static int lk_rec(u32 U, u32 used) {
  if (!U) return try_linkage_rootings();
  int a = __builtin_ctz(U);
  lk_clen = 1; lk_path[lk_npaths][0] = a;
  return lk_dfs(U, used, a);
}
/* note: with lk_maxlen = 2 the interior has at most one vertex: lk_dfs extends only when
   lk_clen < 2, i.e. from the first vertex. */

/* ---- tiers 3-4: all forest T-joins ---- */
static int fe_level;       /* 3 = r root, 4 = r child with c(r) >= 2 */
static int fe_excess;      /* required sibling excess sum_v max(0, c(v) - 1); -1 = any */
static int found_excess;
static long long nforest;
static int uf_find(int *p, int x) { while (p[x] != x) x = p[x]; return x; }
static int forest_rootings(u64 phim) {
  /* components of Phi */
  u32 fadj[MAXN]; for (int v = 0; v < N; v++) fadj[v] = 0;
  for (int e = 0; e < bm; e++) if (phim >> e & 1) { fadj[bu[e]] |= 1u << bv[e]; fadj[bv[e]] |= 1u << bu[e]; }
  u32 comps[MAXN]; int nc = 0; u32 seen = 0;
  for (int v = 0; v < N; v++) {
    if (!fadj[v] || (seen >> v & 1)) continue;
    u32 c = 1u << v, fr = c;
    while (fr) { int x = __builtin_ctz(fr); fr &= fr - 1; u32 nb = fadj[x] & ~c; c |= nb; fr |= nb; }
    seen |= c; comps[nc++] = c;
  }
  int dr = __builtin_popcount(fadj[R]);
  if (fe_level == 4 && dr < 3) return 0;
  /* enumerate root choices */
  int rootsel[MAXN]; u32 rem[MAXN];
  for (int i = 0; i < nc; i++) rem[i] = comps[i];
  int idx[MAXN];
  for (int i = 0; i < nc; i++) idx[i] = 0;
  /* iterate the product by odometer over members */
  int mem[MAXN][MAXN], nmem[MAXN];
  for (int i = 0; i < nc; i++) {
    nmem[i] = 0;
    u32 c = rem[i];
    if ((c >> R & 1)) {
      if (fe_level == 3) { mem[i][nmem[i]++] = R; continue; }
      c &= ~(1u << R);
    }
    while (c) { int x = __builtin_ctz(c); c &= c - 1; mem[i][nmem[i]++] = x; }
  }
  for (;;) {
    for (int i = 0; i < nc; i++) rootsel[i] = mem[i][idx[i]];
    for (int v = 0; v < N; v++) par[v] = -1;
    for (int i = 0; i < nc; i++) {
      int q[MAXN], qh = 0, qt = 0; u32 vis = 1u << rootsel[i];
      q[qt++] = rootsel[i];
      while (qh < qt) {
        int u = q[qh++]; u32 nb = fadj[u] & ~vis;
        while (nb) { int y = __builtin_ctz(nb); nb &= nb - 1; vis |= 1u << y; par[y] = u; q[qt++] = y; }
      }
    }
    int exc = 0;
    if (fe_excess >= 0 || fe_excess == -2) {
      int ch[MAXN]; for (int v = 0; v < N; v++) ch[v] = 0;
      for (int v = 0; v < N; v++) if (par[v] >= 0) ch[par[v]]++;
      for (int v = 0; v < N; v++) if (ch[v] > 1) exc += ch[v] - 1;
    }
    if (univ && (fe_excess == -1 || exc == fe_excess || (fe_excess == -2 && exc >= 1))) {
      int t = fe_level;
      u_tot[t]++;
      int okb = base_ok(phim);
      if (!okb) u_fail[t]++;
      if (!okb || univ == 2) {
        printf("%s %s %d %d tier %d exc %d par", okb ? "USUCC" : "UFAIL", g6line, Z, R, t, exc);
        for (int v = 0; v < N; v++) printf(" %d", par[v]);
        printf("\n");
      }
    } else if ((fe_excess < 0 || exc == fe_excess) && base_ok(phim)) { found_excess = exc; return 1; }
    int i = 0;
    while (i < nc) { if (++idx[i] < nmem[i]) break; idx[i] = 0; i++; }
    if (i == nc) break;
  }
  return 0;
}
static u64 fe_mask;
static int fe_rec(int e, int *uf, u32 parity) {
  if (e == bm) {
    if (parity != T) return 0;
    nforest++;
    return forest_rootings(fe_mask);
  }
  /* exclude e */
  {
    int ok = 1;
    for (int v = 0; v < N; v++) if (lastat[v] == e && ((parity >> v & 1) != (T >> v & 1))) { ok = 0; break; }
    if (ok && fe_rec(e + 1, uf, parity)) return 1;
  }
  /* include e */
  int a = uf_find(uf, bu[e]), b = uf_find(uf, bv[e]);
  if (a != b) {
    int uf2[MAXN]; memcpy(uf2, uf, sizeof(uf2));
    uf2[a] = b;
    u32 p2 = parity ^ (1u << bu[e]) ^ (1u << bv[e]);
    int ok = 1;
    for (int v = 0; v < N; v++) if (lastat[v] == e && ((p2 >> v & 1) != (T >> v & 1))) { ok = 0; break; }
    if (ok) {
      fe_mask |= 1ULL << e;
      if (fe_rec(e + 1, uf2, p2)) return 1;
      fe_mask &= ~(1ULL << e);
    }
  }
  return 0;
}

/* -b: the input graph is B; J = B + z with z joined to the even vertices of B ((T1) instances
   correspond one-to-one to such B, up to isomorphism, since z is the unique even vertex of J) */
static int cone_input, nofilter;
static void make_cone(void) {
  int z = N;
  adj[z] = 0;
  for (int v = 0; v < N; v++) if (!(__builtin_popcount(adj[v]) & 1)) { adj[v] |= 1u << z; adj[z] |= 1u << v; }
  N++;
  /* rewrite g6line for J */
  int k = 0; unsigned char buf[256]; buf[k++] = 63 + N;
  int bit = 0, cur = 0;
  for (int j = 1; j < N; j++) for (int i = 0; i < j; i++) {
    cur = (cur << 1) | (adj[i] >> j & 1); bit++;
    if (bit == 6) { buf[k++] = 63 + cur; bit = 0; cur = 0; }
  }
  if (bit) { cur <<= (6 - bit); buf[k++] = 63 + cur; }
  buf[k] = 0; memcpy(g6line, buf, k + 1);
}

int main(int argc, char **argv) {
  int all = 0, maxtier = 4;
  MODE = 1;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "-t1")) MODE = 1;
    else if (!strcmp(argv[i], "-t2")) MODE = 2;
    else if (!strcmp(argv[i], "-a")) all = 1;
    else if (!strcmp(argv[i], "-b")) cone_input = 1;
    else if (!strcmp(argv[i], "-U")) univ = 1;
    else if (!strcmp(argv[i], "-x")) nofilter = 1;   /* keep instances that are not 3-connected or have delta < 3 */
    else if (!strcmp(argv[i], "-UU")) univ = 2;     /* also print the successes of tiers 3-4 */
    else if (!strcmp(argv[i], "-L") && i + 1 < argc) maxtier = atoi(argv[++i]);
    else if (!strcmp(argv[i], "-D") && i + 3 < argc) {      /* -D file cap every: dump queries */
      dumpf = fopen(argv[++i], "w"); dumpcap = atoll(argv[++i]); dumpevery = atoi(argv[++i]);
      char nm[512]; snprintf(nm, sizeof nm, "%s.ans", argv[i - 2]); ansf = fopen(nm, "w");
    }
  }
  long long ngraphs = 0, ninst = 0, nnodata = 0, lev[7] = {0};
  while (fgets(g6line, sizeof g6line, stdin)) {
    g6line[strcspn(g6line, "\r\n")] = 0;
    if (!g6line[0] || !read_g6(g6line)) continue;
    if (cone_input) { if (N + 1 > MAXN) continue; make_cone(); }
    u32 ev = 0; int mind = 99;
    for (int v = 0; v < N; v++) {
      int d = __builtin_popcount(adj[v]);
      if (d < mind) mind = d;
      if (!(d & 1)) ev |= 1u << v;
    }
    if (mind < 3 && !nofilter) continue;
    int pairs[2][2], np = 0;
    if (MODE == 1) {
      if (__builtin_popcount(ev) != 1) continue;
      pairs[0][0] = __builtin_ctz(ev); pairs[0][1] = -1; np = 1;
    } else {
      if (__builtin_popcount(ev) != 2) continue;
      int a = __builtin_ctz(ev), b = 31 - __builtin_clz(ev);
      if (!(adj[a] >> b & 1)) continue;
      pairs[0][0] = a; pairs[0][1] = b; pairs[1][0] = b; pairs[1][1] = a; np = 2;
    }
    if (!nofilter && !three_connected()) continue;
    ngraphs++;
    for (int pi = 0; pi < np; pi++) {
      Z = pairs[pi][0];
      T = adj[Z];
      Vb = ((1u << N) - 1) & ~(1u << Z);
      bm = 0;
      for (int v = 0; v < N; v++) { lastat[v] = -1; for (int w = 0; w < N; w++) eidB[v][w] = -1; }
      for (int u = 0; u < N; u++) for (int v = u + 1; v < N; v++)
        if (u != Z && v != Z && (adj[u] >> v & 1)) { bu[bm] = u; bv[bm] = v; eidB[u][v] = eidB[v][u] = bm; lastat[u] = bm; lastat[v] = bm; bm++; }
      int dz = __builtin_popcount(T);
      int pm = has_pm(T);
      u32 rlist = (MODE == 1) ? T : (1u << pairs[pi][1]);
      while (rlist) {
        R = __builtin_ctz(rlist); rlist &= rlist - 1;
        ninst++;
        if (pm && !all) continue;
        if (!pm) nnodata++;
        int nu = nu_mask(T);
        u32 D = 0;
        for (int v = 0; v < N; v++) if ((T >> v & 1) && nu_mask(T & ~(1u << v)) == nu) D |= 1u << v;
        u32 A = 0;
        for (int v = 0; v < N; v++) if ((D >> v & 1)) A |= adj[v] & T & ~D;
        u32 C = T & ~D & ~A;
        int ncomp = 0; u32 seen = 0;
        for (int v = 0; v < N; v++) if ((D >> v & 1) && !(seen >> v & 1)) {
          u32 c = 1u << v, fr = c;
          while (fr) { int x = __builtin_ctz(fr); fr &= fr - 1; u32 nb = adj[x] & D & ~c; c |= nb; fr |= nb; }
          seen |= c; ncomp++;
        }
        char rc = (D >> R & 1) ? 'D' : (A >> R & 1) ? 'A' : 'C';
        int twinR = 0, twinO = 0;
        for (int a = 0; a < N; a++) for (int b = a + 1; b < N; b++)
          if ((T >> a & 1) && (T >> b & 1) && __builtin_popcount(adj[a]) == 3 && adj[a] == adj[b]) {
            if (a == R || b == R) twinR = 1; else twinO = 1;
          }
        int tri = 0;
        if (MODE == 1) {
          u32 T2 = T & ~(1u << R);
          for (int w = 0; w < N && !tri; w++) if ((T2 >> w & 1) && has_pm(T2 & ~(1u << w))) tri = 1;
        }
        if (univ) {
          lk_npaths = 0; lk_clen = 0;
          u_tier = 1; lk_maxlen = 2; lk_rec(T, 0);
          /* tier 2 proper: linkages with a path of length >= 3 (those of length <= 2 were tier 1) */
          u_tier = 2; lk_maxlen = 0; lk_npaths = 0; u_skip_short = 1; lk_rec(T, 0); u_skip_short = 0;
          int uf[MAXN];
          for (int lv = 3; lv <= 4; lv++) {
            for (int v = 0; v < N; v++) uf[v] = v;
            fe_level = lv; fe_mask = 0; fe_excess = (lv == 3) ? -2 : -1;
            fe_rec(0, uf, 0);
          }
          continue;
        }
        found_level = 0; ncalls = 0; nforest = -1;
        lk_npaths = 0; lk_clen = 0;
        if (maxtier >= 1) { lk_maxlen = 2; if (lk_rec(T, 0)) save_found(1); }
        if (!found_level && maxtier >= 2) { lk_maxlen = 0; lk_npaths = 0; if (lk_rec(T, 0)) save_found(2); }
        found_excess = 0;
        if (!found_level && maxtier >= 3) {
          /* r a root, by increasing sibling excess (excess 0 = tiers 1-2, already exhausted) */
          for (int k = 1; k <= N && !found_level; k++) {
            int uf[MAXN]; for (int v = 0; v < N; v++) uf[v] = v;
            fe_level = 3; nforest = 0; fe_mask = 0; fe_excess = k;
            if (fe_rec(0, uf, 0)) save_found(3);
          }
        }
        if (!found_level && maxtier >= 4) {
          for (int k = 1; k <= N && !found_level; k++) {
            int uf[MAXN]; for (int v = 0; v < N; v++) uf[v] = v;
            fe_level = 4; nforest = 0; fe_mask = 0; fe_excess = k;
            if (fe_rec(0, uf, 0)) save_found(4);
          }
        }
        int level = found_level ? found_level : maxtier + 1;
        lev[level]++;
        printf("ND %s %d %d %d %d %d %d %d %d %d %c %d %d %d %d %d", g6line, Z, R, dz, nu, dz - 2 * nu,
               __builtin_popcount(D), __builtin_popcount(A), __builtin_popcount(C), ncomp, rc, twinR, twinO, tri,
               level, found_level ? found_excess : -1);
        if (found_level) {
          printf(" | par");
          for (int v = 0; v < N; v++) printf(" %d", found_par[v]);
          printf(" |");
          for (int i = 0; i < found_np; i++) {
            for (int j = 0; j < found_len[i]; j++) printf(" %d", found_paths[i][j]);
            printf(" |");
          }
        }
        printf("\n");
        fflush(stdout);
      }
    }
  }
  if (univ) fprintf(stderr, "UNIV tier1 %lld/%lld tier2 %lld/%lld tier3 %lld/%lld tier4 %lld/%lld (failures/structures)\n",
                    u_fail[1], u_tot[1], u_fail[2], u_tot[2], u_fail[3], u_tot[3], u_fail[4], u_tot[4]);
  fprintf(stderr, "SUMMARY mode=T%d graphs=%lld instances=%lld nodata=%lld level1=%lld level2=%lld level3=%lld level4=%lld level5=%lld\n",
          MODE, ngraphs, ninst, nnodata, lev[1], lev[2], lev[3], lev[4], lev[5]);
  return 0;
}
