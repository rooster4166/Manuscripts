/* dl.c: exact decision of DL(1) queries (session claude/dl-one).

   A Lovasz decomposition of a graph H is a partition of E(H) into paths in which every vertex v
   is an end of exactly d(v) mod 2 paths.  For an odd vertex c, Q(c) is the path ending at c.

   decomposable(E): does the edge set E (a subgraph) have a Lovasz decomposition?
     Exact DFS: pick the odd vertex v of smallest degree, enumerate every path from v to another
     odd vertex, recurse on the rest.  Shortcut (Lovasz's theorem): if at most one vertex has
     positive even degree, the answer is yes.  Results are memoised on the edge mask (the profile
     d mod 2 is a function of the mask).  Option -L disables the shortcut (for validation).

   avoid(E, c, F): is there a Lovasz decomposition of E whose path ending at c (c odd) has no
     vertex in the vertex mask F?

   Input: graph6 lines on stdin.  Modes:
     -m pairs   for every non-adjacent pair a<b of odd vertices print "a b ob oa tw", where
                ob = avoid(E, b, {a}), oa = avoid(E, a, {b}), tw = universal twins of their
                component.  One output line per graph: g6 | g | pairs...
                Graphs with more than one vertex of positive even degree are skipped (printed
                with "skip").
     -m core    as pairs, but only pairs a,b in N(g) (needs exactly one even vertex g).
     -m dec     print 1/0: does the graph have a Lovasz decomposition (any number of even
                vertices allowed).
   Output per pair: ob oa in {0,1}.
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 32
#define MAXM 128
typedef unsigned __int128 u128;

static int n, m;
static int eu[MAXM], ev_[MAXM];
static int eid[MAXN][MAXN];
static u128 inc[MAXN];
static uint32_t adj0[MAXN];
static int noshort = 0, verbose = 0, longfirst = 1, summ = 0;
static uint32_t sepmask = 0;
static int quick = 0, setk = 2, allsets = 0;
static long long tot_okb, tot_graphs, tot_pairs, tot_core, tot_core_cn, tot_both, tot_one, tot_one_core, tot_fail, tot_tw;
static long long nodes = 0;
static int ord_[MAXN];            /* neighbour iteration order */
static long long budget = 0, bstart = 0; static int bhit = 0;
static uint64_t rng = 88172645463325252ULL;
static uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static void shuffle_ord(void) {
  for (int i = 0; i < n; i++) ord_[i] = i;
  for (int i = n - 1; i > 0; i--) { int j = xr() % (i + 1); int t = ord_[i]; ord_[i] = ord_[j]; ord_[j] = t; }
}

/* ---------- memo: open addressing on u128 keys ---------- */
/* slots carry a generation stamp, so a reset is O(1) */
static u128 *hk; static unsigned char *hv; static uint32_t *hg; static size_t hcap, hcnt;
static uint32_t gen = 1;
static void hreset(void) {
  if (!hk) { hcap = 1u << 16; hk = malloc(hcap * sizeof(u128)); hv = calloc(hcap, 1); hg = calloc(hcap, sizeof(uint32_t)); }
  gen++;
  if (gen == 0) { memset(hg, 0, hcap * sizeof(uint32_t)); gen = 1; }
  hcnt = 0;
}
static size_t hh(u128 a) {
  uint64_t lo = (uint64_t)a, hi = (uint64_t)(a >> 64);
  uint64_t x = lo * 0x9E3779B97F4A7C15ULL ^ (hi + 0x632BE59BD9B4E019ULL) * 0xC2B2AE3D27D4EB4FULL;
  x ^= x >> 31; x *= 0xBF58476D1CE4E5B9ULL; x ^= x >> 29;
  return (size_t)x;
}
#define LIVE(i) (hg[i] == gen)
static int hget(u128 a) { /* 0 absent, 1 false, 2 true */
  size_t i = hh(a) & (hcap - 1);
  while (LIVE(i)) { if (hk[i] == a) return hv[i]; i = (i + 1) & (hcap - 1); }
  return 0;
}
static void hput(u128 a, int val) {
  if (hcnt * 2 > hcap) {
    size_t oc = hcap; u128 *ok = hk; unsigned char *ov = hv; uint32_t *og = hg;
    hcap *= 2; hk = malloc(hcap * sizeof(u128)); hv = calloc(hcap, 1); hg = calloc(hcap, sizeof(uint32_t)); hcnt = 0;
    for (size_t i = 0; i < oc; i++) if (og[i] == gen) hput(ok[i], ov[i]);
    free(ok); free(ov); free(og);
  }
  size_t i = hh(a) & (hcap - 1);
  while (LIVE(i)) { if (hk[i] == a) { hv[i] = val; return; } i = (i + 1) & (hcap - 1); }
  hv[i] = val; hk[i] = a; hg[i] = gen; hcnt++;
}

static inline int popc(u128 x) {
  return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64));
}
static inline int deg(u128 E, int v) { return popc(E & inc[v]); }

static int decomposable(u128 E);
static int noprune = 0;

/* necessary condition: in every component C of E, the number of paths is (#odd in C)/2 and each
   path has at most |V(C)|-1 edges, so |E(C)| <= (#odd/2)(|V(C)|-1); also #odd >= 2 if C has edges. */
static int length_ok(u128 E) {
  uint32_t act = 0, nb[MAXN];
  for (int v = 0; v < n; v++) {
    nb[v] = 0;
    u128 iv = E & inc[v];
    if (!iv) continue;
    act |= 1u << v;
    for (int u = 0; u < n; u++) if (((adj0[v] >> u) & 1) && ((iv >> eid[v][u]) & 1)) nb[v] |= 1u << u;
  }
  while (act) {
    int s = __builtin_ctz(act);
    uint32_t C = 1u << s, fr = C;
    while (fr) {
      uint32_t nf = 0;
      for (uint32_t t = fr; t; t &= t - 1) nf |= nb[__builtin_ctz(t)];
      nf &= ~C; C |= nf; fr = nf;
    }
    act &= ~C;
    int nv = __builtin_popcount(C), od = 0, de = 0;
    for (uint32_t t = C; t; t &= t - 1) { int d = deg(E, __builtin_ctz(t)); de += d; if (d & 1) od++; }
    int ne = de / 2;
    if (od < 2) return 0;
    if (ne > (od / 2) * (nv - 1)) return 0;
  }
  return 1;
}

/* path search state */
static u128 pE;          /* the graph in which the path is chosen */
static uint32_t podd;    /* odd vertices of pE (ends allowed) */
static uint32_t pforb;   /* forbidden vertices (only for the constrained top path) */
static int pstart;

static int extend(int x, uint32_t vis, u128 used) {
  /* x current end; try every continuation */
  u128 avail = pE & ~used;
  for (int yi = 0; yi < n; yi++) {
    int y = ord_[yi];
    if (bhit) return 0;
    if (!((adj0[x] >> y) & 1)) continue;
    int e = eid[x][y];
    if (!((avail >> e) & 1)) continue;
    if ((vis >> y) & 1) continue;
    if ((pforb >> y) & 1) continue;
    if (sepmask && (((vis | (1u << y)) & sepmask) == sepmask)) continue;
    u128 u2 = used | ((u128)1 << e);
    if (longfirst && extend(y, vis | (1u << y), u2)) return 1;
    if ((podd >> y) & 1) {
      /* end here */
      u128 savE = pE; uint32_t savO = podd, savF = pforb; int savS = pstart;
      int ok = decomposable(pE & ~u2);
      pE = savE; podd = savO; pforb = savF; pstart = savS;
      if (ok) return 1;
    }
    if (!longfirst && extend(y, vis | (1u << y), u2)) return 1;
  }
  return 0;
}

static int paths_from(u128 E, int v, uint32_t forb) {
  uint32_t odd = 0;
  for (int w = 0; w < n; w++) if (deg(E, w) & 1) odd |= 1u << w;
  pE = E; podd = odd & ~(1u << v); pforb = forb; pstart = v;
  return extend(v, 1u << v, 0);
}

static int decomposable(u128 E) {
  nodes++;
  if (budget && nodes - bstart > budget) bhit = 1;
  if (bhit) return 0;
  if (E == 0) return 1;
  int nev = 0, best = -1, bd = 99;
  for (int v = 0; v < n; v++) {
    int d = deg(E, v);
    if (d == 0) continue;
    if (d % 2 == 0) nev++;
    else if (d < bd) { bd = d; best = v; }
  }
  if (!noshort && !sepmask && nev <= 1) return 1;
  if (best < 0) return 0; /* edges but no odd vertex: impossible */
  int h = hget(E);
  if (h) return h - 1;
  if (!noprune && !length_ok(E)) { hput(E, 1); return 0; }
  int r = paths_from(E, best, 0);
  if (r || !bhit) hput(E, r + 1);
  return r;
}

/* number of paths of a Lovasz decomposition in the component of v, and through v */
static int comp_paths(u128 E, int v) {
  uint32_t C = 1u << v, fr = C;
  while (fr) {
    uint32_t nf = 0;
    for (uint32_t t = fr; t; t &= t - 1) {
      int x = __builtin_ctz(t);
      for (int u = 0; u < n; u++) if (((adj0[x] >> u) & 1) && ((E >> eid[x][u]) & 1)) nf |= 1u << u;
    }
    nf &= ~C; C |= nf; fr = nf;
  }
  int od = 0;
  for (uint32_t t = C; t; t &= t - 1) if (deg(E, __builtin_ctz(t)) & 1) od++;
  return od / 2;
}
static int nrestart = 6; static long long rbudget = 20000;
/* one budgeted attempt: 1 found, 0 proved impossible, 2 budget hit */
static int avoid3(u128 E, int c, uint32_t F, long long B) {
  budget = B; bstart = nodes; bhit = 0;
  int ok = paths_from(E, c, F);
  int hit = bhit;
  budget = 0; bhit = 0;
  if (ok) return 1;
  return hit ? 2 : 0;
}
static int count_blocks(u128 E, int c, uint32_t F);
/* DL for the pair: interleave the two orientations with doubling budgets */
static int dl_pair(u128 E, int a, int b, int *which) {
  if (count_blocks(E, b, 1u << a) && count_blocks(E, a, 1u << b)) { *which = 0; return 0; }
  int db = count_blocks(E, b, 1u << a) ? 0 : 2, da = count_blocks(E, a, 1u << b) ? 0 : 2;
  long long B = 2000;
  while (db == 2 || da == 2) {
    if (db == 2) { shuffle_ord(); db = avoid3(E, b, 1u << a, B); if (db == 1) { *which = 1; return 1; } }
    if (da == 2) { shuffle_ord(); da = avoid3(E, a, 1u << b, B); if (da == 1) { *which = 2; return 1; } }
    B *= 4;
  }
  *which = 0; return 0;
}
/* both_q: exists Lovasz decomposition with a not in Q(b) and b not in Q(a) */
static u128 bqE; static uint32_t bqodd; static int bqa, bqb;
static int bq_ext2(int x, uint32_t vis, u128 used, u128 E2, uint32_t odd2) {
  u128 avail = E2 & ~used;
  for (int y = 0; y < n; y++) {
    if (!((adj0[x] >> y) & 1)) continue;
    int e = eid[x][y];
    if (!((avail >> e) & 1) || ((vis >> y) & 1) || y == bqb) continue;
    u128 u2 = used | ((u128)1 << e);
    if (bq_ext2(y, vis | (1u << y), u2, E2, odd2)) return 1;
    if ((odd2 >> y) & 1) { if (decomposable(E2 & ~u2)) return 1; }
  }
  return 0;
}
static int bq_ext1(int x, uint32_t vis, u128 used) {
  u128 avail = bqE & ~used;
  for (int y = 0; y < n; y++) {
    if (!((adj0[x] >> y) & 1)) continue;
    int e = eid[x][y];
    if (!((avail >> e) & 1) || ((vis >> y) & 1) || y == bqa) continue;
    u128 u2 = used | ((u128)1 << e);
    if (bq_ext1(y, vis | (1u << y), u2)) return 1;
    if ((bqodd >> y) & 1) {
      /* Q(b) ends at y; now Q(a) in the rest, avoiding b */
      u128 E2 = bqE & ~u2;
      uint32_t odd2 = 0;
      for (int w = 0; w < n; w++) if (deg(E2, w) & 1) odd2 |= 1u << w;
      /* a must still need an end: a odd in rest */
      if (!((odd2 >> bqa) & 1)) continue;
      odd2 &= ~(1u << bqa);
      if (bq_ext2(bqa, 1u << bqa, 0, E2, odd2)) return 1;
    }
  }
  return 0;
}
static int both_q(u128 E, int a, int b) {
  bqE = E; bqa = a; bqb = b; bqodd = 0;
  for (int w = 0; w < n; w++) if (deg(E, w) & 1) bqodd |= 1u << w;
  bqodd &= ~(1u << b);
  return bq_ext1(b, 1u << b, 0);
}
static int count_blocks(u128 E, int c, uint32_t F) {
  for (uint32_t t = F; t; t &= t - 1) {
    int f = __builtin_ctz(t);
    int d = deg(E, f);
    if (d == 0) continue;
    int pf = (d + (d & 1)) / 2;
    if (pf >= comp_paths(E, f)) {
      uint32_t C = 1u << f, fr = C;
      while (fr) { uint32_t nf = 0;
        for (uint32_t s = fr; s; s &= s - 1) { int x = __builtin_ctz(s);
          for (int u = 0; u < n; u++) if (((adj0[x] >> u) & 1) && ((E >> eid[x][u]) & 1)) nf |= 1u << u; }
        nf &= ~C; C |= nf; fr = nf; }
      if ((C >> c) & 1) return 1;
    }
  }
  return 0;
}
static int avoid(u128 E, int c, uint32_t F) {
  /* counting: f lies on (d(f)+b(f))/2 paths; if that is every path of its component (which
     contains c), the path at c contains f */
  for (uint32_t t = F; t; t &= t - 1) {
    int f = __builtin_ctz(t);
    int d = deg(E, f);
    if (d == 0) continue;
    int pf = (d + (d & 1)) / 2;
    if (pf >= comp_paths(E, f) && ((comp_paths(E, c) == comp_paths(E, f)))) {
      /* same component? check c reachable: comp_paths equal is not enough; verify */
      uint32_t C = 1u << f, fr = C;
      while (fr) { uint32_t nf = 0;
        for (uint32_t s = fr; s; s &= s - 1) { int x = __builtin_ctz(s);
          for (int u = 0; u < n; u++) if (((adj0[x] >> u) & 1) && ((E >> eid[x][u]) & 1)) nf |= 1u << u; }
        nf &= ~C; C |= nf; fr = nf; }
      if ((C >> c) & 1) return 0;
    }
  }
  for (int r = 0; r < nrestart; r++) {
    shuffle_ord();
    budget = rbudget; bstart = nodes; bhit = 0;
    int ok = paths_from(E, c, F);
    budget = 0; bhit = 0;
    if (ok) return 1;
  }
  for (int i = 0; i < n; i++) ord_[i] = i;
  return paths_from(E, c, F);
}

/* ---------- graph6 ---------- */
static int parse_g6(const char *s) {
  int p = 0;
  if (s[0] == '>') return -1;
  n = s[p++] - 63;
  if (n > MAXN || n < 1) return -1;
  m = 0;
  memset(adj0, 0, sizeof adj0);
  for (int i = 0; i < n; i++) inc[i] = 0;
  int bit = 0; int val = 0; int k = 6;
  for (int j = 1; j < n; j++)
    for (int i = 0; i < j; i++) {
      if (k == 6) { val = s[p++] - 63; k = 0; }
      int b = (val >> (5 - k)) & 1; k++;
      if (b) {
        if (m >= MAXM) return -1;
        eu[m] = i; ev_[m] = j; eid[i][j] = eid[j][i] = m;
        inc[i] |= (u128)1 << m; inc[j] |= (u128)1 << m;
        adj0[i] |= 1u << j; adj0[j] |= 1u << i;
        m++;
      }
    }
  (void)bit;
  return 0;
}

static int comp_of(int a, uint32_t *out) {
  uint32_t seen = 1u << a, fr = 1u << a;
  while (fr) {
    uint32_t nf = 0;
    for (int v = 0; v < n; v++) if ((fr >> v) & 1) nf |= adj0[v];
    nf &= ~seen; seen |= nf; fr = nf;
  }
  *out = seen; return 0;
}

static int univ_twins(int a, int b) {
  uint32_t C; comp_of(a, &C);
  if (!((C >> b) & 1)) return 0;
  uint32_t rest = C & ~(1u << a) & ~(1u << b);
  return (adj0[a] == rest) && (adj0[b] == rest);
}

int main(int argc, char **argv) {
  const char *mode = "pairs";
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "-m") && i + 1 < argc) { mode = argv[++i]; if (!strcmp(mode, "sum")) summ = 1; }
    else if (!strcmp(argv[i], "-L")) noshort = 1;
    else if (!strcmp(argv[i], "-P")) noprune = 1;
    else if (!strcmp(argv[i], "-v")) verbose = 1;
    else if (!strcmp(argv[i], "-S")) longfirst = 0;
    else if (!strcmp(argv[i], "-q")) quick = 1;
    else if (!strcmp(argv[i], "-k") && i + 1 < argc) setk = atoi(argv[++i]);
    else if (!strcmp(argv[i], "-a")) allsets = 1;
    else if (!strcmp(argv[i], "-R") && i + 1 < argc) nrestart = atoi(argv[++i]);
    else if (!strcmp(argv[i], "-B") && i + 1 < argc) rbudget = atoll(argv[++i]);
  }
  char line[4096];
  hreset();
  for (int i = 0; i < MAXN; i++) ord_[i] = i;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n ")] = 0;
    if (!line[0]) continue;
    if (parse_g6(line) < 0) continue;
    u128 E = 0; for (int e = 0; e < m; e++) E |= (u128)1 << e;
    if (!strcmp(mode, "dec")) { hreset(); printf("%s %d\n", line, decomposable(E)); continue; }
    int g = -1, nev = 0;
    for (int v = 0; v < n; v++) { int d = deg(E, v); if (d > 0 && d % 2 == 0) { nev++; g = v; } }
    if (nev > 1) { if (!summ) printf("%s skip\n", line); continue; }
    hreset();
    if (summ) {
      /* summary mode: count, print only exceptions */
      int connected = 1; { uint32_t C; comp_of(0, &C); if (C != (n == 32 ? 0xffffffffu : (1u << n) - 1)) connected = 0; }
      (void)connected;
      tot_graphs++;
      for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) {
        if (!(deg(E, a) & 1) || !(deg(E, b) & 1)) continue;
        if ((adj0[a] >> b) & 1) continue;
        int incore = g >= 0 && ((adj0[g] >> a) & 1) && ((adj0[g] >> b) & 1);
        int cn = (adj0[a] & adj0[b] & ~(g >= 0 ? (1u << g) : 0u)) != 0;
        int ob, oa;
        if (quick) { int wh; int ok = dl_pair(E, a, b, &wh); ob = ok; oa = ok ? -1 : 0; }
        else { ob = avoid(E, b, 1u << a); oa = avoid(E, a, 1u << b); }
        int tw = univ_twins(a, b);
        tot_pairs++;
        if (incore) tot_core++;
        if (incore && cn) tot_core_cn++;
        if (oa == -1) { tot_okb++; oa = 1; }
        else if (ob && oa) tot_both++; else if (ob || oa) { tot_one++; if (incore) tot_one_core++; }
        else tot_fail++;
        if (tw) tot_tw++;
        if ((!(ob || oa)) != tw) { printf("MISMATCH %s g=%d a=%d b=%d ob=%d oa=%d tw=%d\n", line, g, a, b, ob, oa, tw); fflush(stdout); }
      }
      continue;
    }
    if (!strcmp(mode, "sets")) {
      /* every odd c, every A (|A| <= setk) with A disjoint from N[c] (A may contain g):
         hyp1: some w in N(c)-{g} has N(w) & A = {}   ; hyp2: some w in N(c)-{g} has N(w) & (A-{g}) = {}
         print violations (hypothesis holds, avoid fails) */
      for (int c = 0; c < n; c++) {
        if (!(deg(E, c) & 1)) continue;
        uint32_t cand = 0;
        for (int v = 0; v < n; v++) if (v != c && !((adj0[c] >> v) & 1) && deg(E, v) > 0) cand |= 1u << v;
        /* enumerate subsets of cand of size 1..setk */
        int L[32], nl = 0; for (int v = 0; v < n; v++) if ((cand >> v) & 1) L[nl++] = v;
        for (int s1 = 0; s1 < nl; s1++) for (int s2 = s1; s2 < nl; s2++) for (int s3 = s2; s3 < nl; s3++) {
          if (setk < 2 && s2 != s1) continue;
          if (setk < 3 && s3 != s2) continue;
          uint32_t Am = (1u << L[s1]) | (1u << L[s2]) | (1u << L[s3]);
          uint32_t Ang = g >= 0 ? Am & ~(1u << g) : Am;
          int h1 = 0, h2 = 0;
          for (int w = 0; w < n; w++) {
            if (!((adj0[c] >> w) & 1) || w == g) continue;
            if (!(adj0[w] & Am)) h1 = 1;
            if (!(adj0[w] & Ang)) h2 = 1;
          }
          if (!h1 && !h2 && !allsets) continue;
          int ok = avoid(E, c, Am);
          tot_pairs++;
          if (h1) { tot_core++; if (!ok) { tot_fail++; printf("V1 %s g=%d c=%d A=%x\n", line, g, c, Am); } }
          if (h2) { tot_core_cn++; if (!ok) { tot_tw++; printf("V2 %s g=%d c=%d A=%x\n", line, g, c, Am); } }
          if (!ok) tot_one++;
        }
      }
      fflush(stdout);
      continue;
    }
    if (!strcmp(mode, "nmax")) {
      /* for every odd c and every w in N(c)-{g}: A = V - N[c] - N(w), plus g if g not in N[c];
         also w = g when g exists (L1* local form): A = V - N[c] - N(g).  Query avoid. */
      for (int c = 0; c < n; c++) {
        if (!(deg(E, c) & 1)) continue;
        for (int w = 0; w < n; w++) {
          if (!((adj0[c] >> w) & 1) && w != g) continue;
          if (w == g && w < 0) continue;
          uint32_t all = (n == 32 ? 0xffffffffu : (1u << n) - 1);
          uint32_t Am = all & ~adj0[c] & ~(1u << c) & ~(w >= 0 ? adj0[w] : 0);
          if (w != g && g >= 0 && !((adj0[c] >> g) & 1) && g != c) Am |= 1u << g;
          if (w == g) Am &= ~(1u << g);
          /* drop isolated vertices */
          for (int v = 0; v < n; v++) if (deg(E, v) == 0) Am &= ~(1u << v);
          if (!Am) continue;
          int ok = avoid(E, c, Am);
          tot_pairs++;
          if (w == g) { tot_core++; if (!ok) { tot_fail++; printf("LOC %s g=%d c=%d A=%x\n", line, g, c, Am); } }
          else { tot_core_cn++; if (!ok) { tot_tw++; printf("NMAX %s g=%d c=%d w=%d A=%x\n", line, g, c, w, Am); } }
        }
      }
      fflush(stdout);
      continue;
    }
    if (!strcmp(mode, "both")) {
      /* CN1 core pairs: a,b in N(g), N(a)&N(b) = {g}: is there one decomposition with both
         Q(b) avoiding a and Q(a) avoiding b?  Encoded as avoidance system: tails a,b.  Uses the
         'sep' search: path at b avoiding a, then (in the rest) path at a avoiding b. */
      for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) {
        if (g < 0 || !(deg(E, a) & 1) || !(deg(E, b) & 1) || ((adj0[a] >> b) & 1)) continue;
        if (!(((adj0[g] >> a) & 1) && ((adj0[g] >> b) & 1))) continue;
        int cn1 = (adj0[a] & adj0[b]) == (1u << g);
        int r = both_q(E, a, b);
        tot_pairs++;
        if (cn1) { tot_core++; if (!r) { tot_fail++; printf("NOBOTH_CN1 %s g=%d a=%d b=%d da=%d db=%d\n", line, g, a, b, deg(E,a), deg(E,b)); } }
        else { tot_core_cn++; if (!r) tot_tw++; }
      }
      fflush(stdout);
      continue;
    }
    if (!strcmp(mode, "sep1")) {
      for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) {
        if (!(deg(E, a) & 1) || !(deg(E, b) & 1) || ((adj0[a] >> b) & 1)) continue;
        uint32_t cn = adj0[a] & adj0[b];
        if (__builtin_popcount(cn) != 1) continue;
        int w = __builtin_ctz(cn);
        hreset(); sepmask = (1u << a) | (1u << b);
        for (int i = 0; i < n; i++) ord_[i] = i;
        uint32_t odd = 0; for (int v = 0; v < n; v++) if (deg(E, v) & 1) odd |= 1u << v;
        int r = decomposable(E);
        sepmask = 0; hreset();
        printf("SEP1 %s g=%d a=%d b=%d w=%d wg=%d da=%d db=%d dw=%d sep=%d\n", line, g, a, b, w, w == g, deg(E,a), deg(E,b), deg(E,w), r);
      }
      fflush(stdout);
      continue;
    }
    int core = !strcmp(mode, "core");
    if (core && g < 0) { printf("%s skip\n", line); continue; }
    printf("%s ; %d ;", line, g);
    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) {
      if (!(deg(E, a) & 1) || !(deg(E, b) & 1)) continue;
      if ((adj0[a] >> b) & 1) continue;
      if (core && !(((adj0[g] >> a) & 1) && ((adj0[g] >> b) & 1))) continue;
      long long n0 = nodes;
      int ob = avoid(E, b, 1u << a);
      long long n1 = nodes;
      int oa = avoid(E, a, 1u << b);
      if (verbose) fprintf(stderr, "%s a=%d b=%d ob=%d (%lld) oa=%d (%lld) memo=%zu\n", line, a, b, ob, n1 - n0, oa, nodes - n1, hcnt);
      printf(" %d %d %d %d %d,", a, b, ob, oa, univ_twins(a, b));
    }
    printf("\n");
    fflush(stdout);
  }
  if (!strcmp(mode, "both")) printf("BOTH corepairs=%lld cn1=%lld cn1_noboth=%lld other=%lld other_noboth=%lld\n", tot_pairs, tot_core, tot_fail, tot_core_cn, tot_tw);
  if (!strcmp(mode, "nmax")) printf("NMAX queries=%lld local=%lld local_viol=%lld nmax=%lld nmax_viol=%lld\n", tot_pairs, tot_core, tot_fail, tot_core_cn, tot_tw);
  if (!strcmp(mode, "sets")) printf("SETS queries=%lld hyp1=%lld hyp1_viol=%lld hyp2=%lld hyp2_viol=%lld avoid_fail=%lld\n", tot_pairs, tot_core, tot_fail, tot_core_cn, tot_tw, tot_one);
  if (summ) printf("SUMMARY okb_unchecked_oa=%lld graphs=%lld pairs=%lld core=%lld core_cn=%lld both=%lld one=%lld one_core=%lld fail=%lld twins=%lld nodes=%lld\n",
    tot_okb, tot_graphs, tot_pairs, tot_core, tot_core_cn, tot_both, tot_one, tot_one_core, tot_fail, tot_tw, nodes);
  return 0;
}
