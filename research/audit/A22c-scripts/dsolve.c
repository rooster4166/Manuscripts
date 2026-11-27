/* dsolve.c -- audit A22c: an independent path-decomposition solver (written for this audit; it
   shares no code with ptm.c / walk3.c / stl.c).

   Problem: multigraph on n <= 64 vertices, m <= 128 edges (edge list, parallel edges allowed).
   Find a decomposition of E into paths such that every vertex v is an end of exactly B(v) in {0,1}
   paths (B given as a vertex mask), subject to per-path constraints:
     sep   : no path contains both vertices of a listed pair;
     cover : (if nsets > 0) the vertex set of every path lies inside one of the listed vertex sets;
     spec  : special edges (spec[e] != -2): a path contains at most one special edge, and a special
             edge on a path is its first or last edge; if spec[e] = x >= 0 the path must have an end
             at x whose end edge is e ("e terminal at x").
   Search design: pick an edge e at a vertex of least positive remaining degree and enumerate every
   simple path through e (extend on both sides); memoise failed states (remaining edges, end mask).
   Returns 1 (found; paths written to out), 0 (none), 2 (node budget exhausted).
   out format: for each path: L, v0, e1, v1, ..., eL, vL ; then -1.                               */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned __int128 u128;
#define MAXV 64
#define MAXE 128

static int n, m, EU[MAXE], EV[MAXE];
static int adjE[MAXV][MAXE], adjW[MAXV][MAXE], adjN[MAXV];
static uint64_t sepm[MAXV];
static int nsets; static uint64_t sets[64];
static int spec[MAXE];
static u128 rem; static uint64_t bm;
static unsigned long long budget, nodes; static int aborted;
static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

/* memo */
typedef struct { u128 r; uint64_t b; } key_t3;
static key_t3 *tab; static uint32_t *stampv; static uint32_t stamp = 1; static size_t cap, cnt;
static size_t hsh(u128 r, uint64_t b) {
  uint64_t x = (uint64_t)r * 0x9E3779B97F4A7C15ULL ^ (uint64_t)(r >> 64) * 0xC2B2AE3D27D4EB4FULL ^ b * 0x165667B19E3779F9ULL;
  x ^= x >> 29; x *= 0xBF58476D1CE4E5B9ULL; x ^= x >> 32; return (size_t)x;
}
static int hget(u128 r, uint64_t b) {
  size_t i = hsh(r, b) & (cap - 1);
  while (stampv[i] == stamp) { if (tab[i].r == r && tab[i].b == b) return 1; i = (i + 1) & (cap - 1); }
  return 0;
}
static void hput(u128 r, uint64_t b);
static void hgrow(void) {
  size_t oc = cap; key_t3 *ot = tab; uint32_t *os = stampv;
  cap *= 2; tab = malloc(cap * sizeof *tab); stampv = calloc(cap, sizeof *stampv); cnt = 0;
  uint32_t st = stamp;
  for (size_t i = 0; i < oc; i++) if (os[i] == st) hput(ot[i].r, ot[i].b);
  free(ot); free(os);
}
static void hput(u128 r, uint64_t b) {
  if (2 * (cnt + 1) > cap) hgrow();
  size_t i = hsh(r, b) & (cap - 1);
  while (stampv[i] == stamp) i = (i + 1) & (cap - 1);
  stampv[i] = stamp; tab[i].r = r; tab[i].b = b; cnt++;
}
static void hreset(void) {
  if (!tab) { cap = 1 << 16; tab = malloc(cap * sizeof *tab); stampv = calloc(cap, sizeof *stampv); }
  stamp++; if (stamp == 0) { memset(stampv, 0, cap * sizeof *stampv); stamp = 1; }
  cnt = 0;
}

/* path under construction: left side (from u outward) and right side (from v outward) */
static int seedE, seedU, seedV;
static int Lv[MAXV], Le[MAXV], nl;   /* left vertices beyond u, edges */
static int Rv[MAXV], Re[MAXV], nr;
static uint64_t vis; static uint64_t setsok; static int nspec;
/* solution stack */
static int sol[4 * MAXE + 8 * MAXV]; static int solp;

static int solve(void);

static int degrem(int v) { int d = 0; for (int i = 0; i < adjN[v]; i++) if ((rem >> adjE[v][i]) & 1) d++; return d; }

static int complete_ok(void) {
  /* path: L-side reversed, u, v, R-side.  ends: a = (nl ? Lv[nl-1] : u), c = (nr ? Rv[nr-1] : v) */
  int a = nl ? Lv[nl - 1] : seedU, c = nr ? Rv[nr - 1] : seedV;
  if (!((bm >> a) & 1) || !((bm >> c) & 1)) return 0;
  if (nspec > 1) return 0;
  if (nspec == 1) {
    /* first edge (at end a) and last edge (at end c) */
    int ea = nl ? Le[nl - 1] : seedE, ec = nr ? Re[nr - 1] : seedE;
    int sp = -1;
    if (spec[seedE] != -2) sp = seedE;
    for (int i = 0; i < nl; i++) if (spec[Le[i]] != -2) sp = Le[i];
    for (int i = 0; i < nr; i++) if (spec[Re[i]] != -2) sp = Re[i];
    int atA = (sp == ea), atC = (sp == ec);
    if (!atA && !atC) return 0;
    if (spec[sp] >= 0) { int x = spec[sp]; if (!((atA && a == x) || (atC && c == x))) return 0; }
  }
  if (nsets && !setsok) return 0;
  return 1;
}

static int try_path(void) {
  int a = nl ? Lv[nl - 1] : seedU, c = nr ? Rv[nr - 1] : seedV;
  int save = solp;
  int L = 1 + nl + nr;
  sol[solp++] = L;
  /* write v0 e1 v1 ... */
  int seq_v[MAXV + 2], seq_e[MAXV + 2], k = 0;
  for (int i = nl - 1; i >= 0; i--) { seq_v[k] = Lv[i]; seq_e[k] = Le[i]; k++; }
  seq_v[k] = seedU; seq_e[k] = seedE; k++;
  seq_v[k] = seedV; k++;
  for (int i = 0; i < nr; i++) { seq_e[k - 1] = Re[i]; seq_v[k] = Rv[i]; k++; }
  /* now seq_v[0..k-1], seq_e[0..k-2] */
  sol[solp++] = seq_v[0];
  for (int i = 0; i + 1 < k; i++) { sol[solp++] = seq_e[i]; sol[solp++] = seq_v[i + 1]; }
  bm &= ~(1ULL << a); bm &= ~(1ULL << c);
  int ok = solve();
  bm |= (1ULL << a) | (1ULL << c);
  if (!ok) solp = save;
  return ok;
}

static uint64_t sets_containing(uint64_t vs) {
  uint64_t r = 0; for (int i = 0; i < nsets; i++) if ((vs & ~sets[i]) == 0) r |= 1ULL << i; return r;
}

static int ext_left(void);
/* extend right side from current right end; at each stage optionally stop and go to the left side */
static int ext_right(void) {
  if (aborted) return 0;
  if (budget && ++nodes > budget) { aborted = 1; return 0; }
  int c = nr ? Rv[nr - 1] : seedV;
  /* option: stop the right side here */
  if ((bm >> c) & 1) { if (ext_left()) return 1; if (aborted) return 0; }
  /* cannot extend past a special edge on this side; e itself special: extending right is allowed only
     if the left side stays empty -- checked at completion */
  int lastE = nr ? Re[nr - 1] : -1;
  if (lastE >= 0 && spec[lastE] != -2) return 0;
  int deg = adjN[c]; int st = deg ? (int)(rnd() % (unsigned)deg) : 0;
  for (int jj = 0; jj < deg; jj++) {
    int j = (st + jj) % deg; int e = adjE[c][j], w = adjW[c][j];
    if (!((rem >> e) & 1)) continue;
    if ((vis >> w) & 1) continue;
    if (sepm[w] & vis) continue;
    int sp = spec[e] != -2;
    if (sp && nspec >= 1) continue;
    uint64_t so = setsok;
    if (nsets) { setsok &= sets_containing(vis | (1ULL << w)); if (!setsok) { setsok = so; continue; } }
    rem &= ~((u128)1 << e); vis |= 1ULL << w; nspec += sp;
    Rv[nr] = w; Re[nr] = e; nr++;
    int ok = ext_right();
    nr--; nspec -= sp; vis &= ~(1ULL << w); rem |= (u128)1 << e; setsok = so;
    if (ok) return 1;
    if (aborted) return 0;
  }
  return 0;
}
static int ext_left(void) {
  if (aborted) return 0;
  if (budget && ++nodes > budget) { aborted = 1; return 0; }
  int c = nl ? Lv[nl - 1] : seedU;
  if ((bm >> c) & 1) {
    int ok = 1;
    if (spec[seedE] != -2 && nl > 0 && nr > 0) ok = 0;
    if (ok && complete_ok()) { if (try_path()) return 1; if (aborted) return 0; }
  }
  int lastE = nl ? Le[nl - 1] : -1;
  if (lastE >= 0 && spec[lastE] != -2) return 0;
  if (nl == 0 && nr > 0 && spec[seedE] != -2) return 0;   /* seed special and right side used */
  int deg = adjN[c]; int st = deg ? (int)(rnd() % (unsigned)deg) : 0;
  for (int jj = 0; jj < deg; jj++) {
    int j = (st + jj) % deg; int e = adjE[c][j], w = adjW[c][j];
    if (!((rem >> e) & 1)) continue;
    if ((vis >> w) & 1) continue;
    if (sepm[w] & vis) continue;
    int sp = spec[e] != -2;
    if (sp && nspec >= 1) continue;
    uint64_t so = setsok;
    if (nsets) { setsok &= sets_containing(vis | (1ULL << w)); if (!setsok) { setsok = so; continue; } }
    rem &= ~((u128)1 << e); vis |= 1ULL << w; nspec += sp;
    Lv[nl] = w; Le[nl] = e; nl++;
    int ok = ext_left();
    nl--; nspec -= sp; vis &= ~(1ULL << w); rem |= (u128)1 << e; setsok = so;
    if (ok) return 1;
    if (aborted) return 0;
  }
  return 0;
}

static int prune(void) {
  /* special edges: each needs its own path and a terminal end that still needs an end */
  int ns = 0;
  for (int e = 0; e < m; e++) if (spec[e] != -2 && ((rem >> e) & 1)) {
    ns++;
    if (spec[e] >= 0) { if (!((bm >> spec[e]) & 1)) return 0; }
    else if (!((bm >> EU[e]) & 1) && !((bm >> EV[e]) & 1)) return 0;
  }
  if (2 * ns > __builtin_popcountll(bm)) return 0;
  /* parity and capacity at each vertex; every component of the remaining edges has >= 2 ends */
  for (int v = 0; v < n; v++) {
    int d = degrem(v), b = (bm >> v) & 1;
    if (d == 0 && b) return 0;
    if (((d - b) & 1)) return 0;
  }
  uint64_t seen = 0;
  for (int v = 0; v < n; v++) {
    if ((seen >> v) & 1) continue;
    if (degrem(v) == 0) continue;
    uint64_t comp = 1ULL << v; int stack[MAXV], sp = 0; stack[sp++] = v;
    while (sp) { int x = stack[--sp];
      for (int i = 0; i < adjN[x]; i++) { if (!((rem >> adjE[x][i]) & 1)) continue; int y = adjW[x][i];
        if (!((comp >> y) & 1)) { comp |= 1ULL << y; stack[sp++] = y; } } }
    seen |= comp;
    if (__builtin_popcountll(comp & bm) < 2) return 0;
  }
  return 1;
}

static int solve(void) {
  if (rem == 0) return bm == 0;
  if (bm == 0) return 0;
  if (!prune()) return 0;
  if (hget(rem, bm)) return 0;
  /* choose a vertex of least positive remaining degree, and an edge at it */
  int best = -1, bd = 1 << 30;
  for (int v = 0; v < n; v++) { int d = degrem(v); if (d > 0 && d < bd) { bd = d; best = v; } }
  int e = -1;
  for (int i = 0; i < adjN[best]; i++) if ((rem >> adjE[best][i]) & 1) { e = adjE[best][i]; break; }
  int u = EU[e], v = EV[e];
  /* save path state (this is a fresh path) */
  int s_seedE = seedE, s_seedU = seedU, s_seedV = seedV, s_nl = nl, s_nr = nr, s_nspec = nspec;
  uint64_t s_vis = vis, s_setsok = setsok;
  int sLv[MAXV], sLe[MAXV], sRv[MAXV], sRe[MAXV];
  memcpy(sLv, Lv, sizeof(int) * nl); memcpy(sLe, Le, sizeof(int) * nl);
  memcpy(sRv, Rv, sizeof(int) * nr); memcpy(sRe, Re, sizeof(int) * nr);
  int ok = 0;
  if (!(sepm[u] & (1ULL << v))) {
    uint64_t so = nsets ? sets_containing((1ULL << u) | (1ULL << v)) : 0;
    if (!nsets || so) {
      seedE = e; seedU = u; seedV = v; nl = nr = 0; vis = (1ULL << u) | (1ULL << v);
      nspec = spec[e] != -2; setsok = so;
      rem &= ~((u128)1 << e);
      ok = ext_right();
      rem |= (u128)1 << e;
    }
  }
  seedE = s_seedE; seedU = s_seedU; seedV = s_seedV; nl = s_nl; nr = s_nr; nspec = s_nspec;
  vis = s_vis; setsok = s_setsok;
  memcpy(Lv, sLv, sizeof(int) * nl); memcpy(Le, sLe, sizeof(int) * nl);
  memcpy(Rv, sRv, sizeof(int) * nr); memcpy(Re, sRe, sizeof(int) * nr);
  if (!ok && !aborted) hput(rem, bm);
  return ok;
}

int dsolve(int N, int M, const int *eu, const int *ev, uint64_t bmask,
           int nsep, const int *su, const int *sv,
           int nS, const uint64_t *S, const int *specv,
           uint64_t seed, uint64_t bud, int *out, int outcap) {
  if (N > MAXV || M > MAXE || nS > 64) return -1;
  n = N; m = M;
  for (int v = 0; v < n; v++) { adjN[v] = 0; sepm[v] = 0; }
  for (int e = 0; e < m; e++) {
    EU[e] = eu[e]; EV[e] = ev[e];
    adjE[eu[e]][adjN[eu[e]]] = e; adjW[eu[e]][adjN[eu[e]]++] = ev[e];
    adjE[ev[e]][adjN[ev[e]]] = e; adjW[ev[e]][adjN[ev[e]]++] = eu[e];
    spec[e] = specv ? specv[e] : -2;
  }
  for (int i = 0; i < nsep; i++) { sepm[su[i]] |= 1ULL << sv[i]; sepm[sv[i]] |= 1ULL << su[i]; }
  nsets = nS; for (int i = 0; i < nS; i++) sets[i] = S[i];
  rem = 0; for (int e = 0; e < m; e++) rem |= (u128)1 << e;
  bm = bmask; budget = bud; nodes = 0; aborted = 0;
  rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL; if (!rs) rs = 1;
  nl = nr = 0; vis = 0; nspec = 0; setsok = 0; solp = 0;
  hreset();
  int r = solve();
  if (aborted) return 2;
  if (r == 1) {
    if (solp + 1 > outcap) return -2;
    memcpy(out, sol, sizeof(int) * solp); out[solp] = -1;
  }
  return r;
}
