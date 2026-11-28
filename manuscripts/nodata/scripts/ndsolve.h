/* ndsolve.h -- exact constrained Lovasz solver (nodata session).

   Graph H on n <= 16 vertices, m <= 64 edges.  need[v] in {0,1} is the number of path ends wanted
   at v (in an all-odd graph every need is 1; an isolated vertex has need 0).  A solution is a
   decomposition of E(H) into paths with exactly need[v] ends at v, such that every path P with
   ends s, w satisfies the route-respecting conditions of tools/route_ext.c query C:
       V(P) & crv[s] = {s},   V(P) & crv[w] = {w},   crv[s] & crv[w] = 0,
   where crv[v] is a vertex mask containing v.  With crv[v] = {v, p(v)} at the children of a rooted
   forest and crv[v] = {v} elsewhere this is exactly (i) p(v) not on Q(v) and (ii) siblings end
   distinct paths.  An optional extra test (pair_ok) rejects a path by its two ends.

   Search: the unended vertex of least remaining degree is an end of some remaining path; branch
   over every path from it (vertices of crv[s] - s are never entered) to an unended vertex w that
   satisfies the conditions; prune by parity (remaining degree = need mod 2), by "an unended vertex
   has an edge", and per component (an even number >= 2 of unended vertices in every component
   with an edge); memoise failures under (remaining edges, ended set), which determine the
   subproblem.  Exact (no budget). */
#ifndef NDSOLVE_H
#define NDSOLVE_H
#include <stdint.h>
#include <string.h>
#include <stdlib.h>

#define SMAXN 16
#define SMAXM 64
typedef uint64_t u64;
typedef uint32_t u32;

static int sn, sm;
static int seu[SMAXM], sev[SMAXM];
static u64 sinc[SMAXN];
static u32 sneed;              /* bit v: need[v] = 1 */
static u32 crv[SMAXN];
static int (*pair_ok)(int s, int w) = 0;

/* witness */
static int wpath[SMAXM + 1][SMAXN + 1], wlen[SMAXM + 1], wn;   /* wpath[wn] = path being grown */
static int clen;
#define cpath (wpath[wn])

/* memo of failures */
#define MBITS 22
#define MSIZE (1u << MBITS)
typedef struct { u64 rem; u32 ended; u32 stamp; } ment;
static ment *mtab; static u32 mstamp = 1; static u32 mcount;
static long long snodes, sbudget;   /* sbudget > 0: abort after that many nodes (sabort = 1) */
static int sabort;
static inline u32 midx(u64 r, u32 e) {
  u64 h = r * 0x9E3779B97F4A7C15ULL ^ ((u64)e * 0xC2B2AE3D27D4EB4FULL + 0x165667B19E3779F9ULL);
  h ^= h >> 29;
  return (u32)(h >> (64 - MBITS));
}
static int mhas(u64 r, u32 e) {
  for (u32 i = midx(r, e), t = 0; t < 64; t++, i = (i + 1) & (MSIZE - 1)) {
    if (mtab[i].stamp != mstamp) return 0;
    if (mtab[i].rem == r && mtab[i].ended == e) return 1;
  }
  return 0;
}
static void mput(u64 r, u32 e) {
  if (mcount > MSIZE / 2) return;
  for (u32 i = midx(r, e), t = 0; t < 64; t++, i = (i + 1) & (MSIZE - 1))
    if (mtab[i].stamp != mstamp) { mtab[i].rem = r; mtab[i].ended = e; mtab[i].stamp = mstamp; mcount++; return; }
}
static void mreset(void) {
  if (!mtab) mtab = calloc(MSIZE, sizeof(ment));
  mstamp++; mcount = 0;
  if (mstamp == 0) { memset(mtab, 0, MSIZE * sizeof(ment)); mstamp = 1; }
}

static inline int popc64(u64 x) { return __builtin_popcountll(x); }

static int ssolve(u64 rem, u32 ended);

static int sgrow(int s, int cur, u64 rem, u32 ended, u32 pm, u32 block) {
  if (sabort) return 0;
  u64 ex = rem & sinc[cur];
  while (ex) {
    int e = __builtin_ctzll(ex); ex &= ex - 1;
    int w = seu[e] == cur ? sev[e] : seu[e];
    if (block >> w & 1) continue;
    u64 rem2 = rem & ~(1ULL << e);
    u32 pm2 = pm | (1u << w);
    cpath[clen++] = w;
    if ((sneed >> w & 1) && !(ended >> w & 1) && (pm2 & crv[w]) == (1u << w) && !(crv[s] & crv[w])
        && (!pair_ok || pair_ok(s, w))) {
      wlen[wn] = clen; wn++;
      if (ssolve(rem2, ended | (1u << s) | (1u << w))) return 1;
      wn--;
    }
    if (rem2 & sinc[w]) {
      if (sgrow(s, w, rem2, ended, pm2, block | (1u << w))) return 1;
    }
    clen--;
  }
  return 0;
}

static int ssolve(u64 rem, u32 ended) {
  u32 todo = sneed & ~ended;
  if (!todo) return rem == 0;
  if (!rem) return 0;
  snodes++;
  if (sbudget && snodes > sbudget) { sabort = 1; return 0; }
  int best = -1, bd = 999;
  int P = __builtin_popcount(todo) / 2;
  int dg[SMAXN];
  for (int v = 0; v < sn; v++) {
    int d = popc64(rem & sinc[v]);
    dg[v] = d;
    int nd = todo >> v & 1;
    if ((d ^ nd) & 1) return 0;
    if (d > 2 * P - nd) return 0;          /* each remaining path meets v at most once */
    if (nd) {
      if (d == 0) return 0;
      /* fail-first: constrained vertices (crv beyond v itself) first, then least degree */
      int key = d + ((crv[v] != (1u << v)) ? 0 : 64);
      if (key < bd) { bd = key; best = v; }
    }
  }
  /* components: an even number q2 >= 2 of unended vertices; with q = q2/2 paths, every degree is
     at most 2q - need and the component has at most q(|C| - 1) edges */
  u32 seen = 0;
  for (int v = 0; v < sn; v++) {
    if ((seen >> v & 1) || !(rem & sinc[v])) continue;
    u32 comp = 1u << v, fr = 1u << v;
    while (fr) {
      int x = __builtin_ctz(fr); fr &= fr - 1;
      u64 ex = rem & sinc[x];
      while (ex) {
        int e = __builtin_ctzll(ex); ex &= ex - 1;
        int y = seu[e] == x ? sev[e] : seu[e];
        if (!(comp >> y & 1)) { comp |= 1u << y; fr |= 1u << y; }
      }
    }
    seen |= comp;
    int t = __builtin_popcount(comp & todo);
    if (t < 2 || (t & 1)) return 0;
    int q = t / 2, sumd = 0;
    for (u32 c = comp; c; c &= c - 1) {
      int x = __builtin_ctz(c);
      if (dg[x] > 2 * q - (int)(todo >> x & 1)) return 0;
      sumd += dg[x];
    }
    if (sumd / 2 > q * (__builtin_popcount(comp) - 1)) return 0;
  }
  if (mhas(rem, ended)) return 0;
  int savelen = clen;
  clen = 0; cpath[clen++] = best;
  int ok = sgrow(best, best, rem, ended, 1u << best, (1u << best) | crv[best]);
  clen = savelen;
  if (!ok && !sabort) mput(rem, ended);
  return ok;
}

/* set up: edges given as list; need mask; crv default {v} */
static void sinit(int n_) {
  sn = n_; sm = 0;
  for (int v = 0; v < sn; v++) { sinc[v] = 0; crv[v] = 1u << v; }
  sneed = 0;
  pair_ok = 0;
}
static void sadd(int u, int v) {
  seu[sm] = u; sev[sm] = v;
  sinc[u] |= 1ULL << sm; sinc[v] |= 1ULL << sm;
  sm++;
}
/* run: returns 1 if a solution exists; the witness is wpath[0..wn) */
static int srun(void) {
  mreset();
  snodes = 0; sabort = 0;
  wn = 0; clen = 0;
  u64 full = sm == 64 ? ~0ULL : ((1ULL << sm) - 1);
  return ssolve(full, 0);
}
#endif
