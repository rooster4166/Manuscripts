/* fl.c -- exhaustive tests of forest forms of L_N in graphs with no even vertex (nodata session).

   Input: graph6, connected graphs with every degree odd (others are skipped), n <= 12.
   A Lovasz decomposition of such a graph F has n/2 paths and one end at every vertex; Q(v) is the
   path ending at v.  A *unit* is a small rooted forest on non-edges of F, with conditions
   (i) p(v) not on Q(v) for every non-root v and (ii) siblings end distinct paths, or a route:
     P   pair      c <- a        (a parent of c):  a notin Q(c)                         [= L_1]
     K   2-chain   a <- x <- b   (path a x b rooted at a): a notin Q(x), x notin Q(b)
     C3  3-chain   a <- x <- y <- b:  a notin Q(x), x notin Q(y), y notin Q(b)
     S   star      u <- {x, y}   (cherry rooted at its centre): u notin Q(x), Q(y); Q(x) != Q(y)
     R   route     c -> {x, b}   (route c x b appended at c):  x, b notin Q(c)
   (forest edges ax, xb, ... are non-edges of F; the vertices of a unit are distinct).
     L   claw      a <- v <- {b, c} (K_{1,3} rooted at a leaf): a notin Q(v); v notin Q(b), Q(c);
                   Q(b) != Q(c)
   Families (flag -f): k = one K; c = one C3; s = one S; r = one R; l = one L;
                       kp = K + disjoint P; kk = two disjoint K; sp = S + disjoint P;
                       rp = R + disjoint P; kpp = K + two disjoint P; lp = L + P; sk = S + K;
                       lk = L + K; cp = C3 + P; ss = two disjoint S.
   Phase 1: -d random Lovasz decompositions strike the sets they satisfy (coverage bitsets);
   phase 2: every set still standing is decided by the exact solver of ndsolve.h (route-
   respecting masks encode exactly (i), (ii); the route R is encoded as a mask {c, x, b} at c).
   A set left infeasible is a genuine counterexample and is printed (FAIL ...), with, for stars,
   whether the star Hall condition (H1) holds:  every component C of F - u has
   |{x, y} cap C| <= (|C| - e(u, C)) / 2   (u the centre, x, y its two children; for a claw
   the centre is v).  Phase-2 searches first try 12 randomly relabelled budgeted solves (a
   success is a certificate) and then an exhaustive exact search.
   -H: do not search unstruck sets in which a vertex with two children violates (H1) (they fail by
   the Hall lemma); count them instead.
   usage: fl -f FAMILY [-d dives] [-s seed] [-H] < graph6 */
#include <stdio.h>
#include "ndsolve.h"

#define MAXN 12
typedef unsigned __int128 u128;
static int n;
static u32 adj[MAXN];
static char g6[256];
static int read_g6(const char *s) {
  const unsigned char *p = (const unsigned char *)s;
  n = p[0] - 63;
  if (n < 1 || n > MAXN) return 0;
  p++;
  int bit = 0, cur = 0, k = 0;
  for (int v = 0; v < n; v++) adj[v] = 0;
  for (int j = 1; j < n; j++)
    for (int i = 0; i < j; i++) {
      if (bit == 0) { cur = p[k++] - 63; bit = 6; }
      bit--;
      if (cur >> bit & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
    }
  return 1;
}

/* ---------------- random Lovasz decompositions (phase 1) ---------------- */
static int perm[MAXN], iperm[MAXN];
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int E_u[64], E_v[64], m;
static u64 inc[MAXN];
static u32 Qm[MAXN]; static int part[MAXN];   /* result of a dive */
static int dpath[MAXN + 1][MAXN + 1], dlen[MAXN + 1], dnp;
static long long dnodes, dcap;
static int dive(u64 rem, u32 ended);
static int dgrow(int s, int cur, u64 rem, u32 ended, u32 vis) {
  /* random order of incident remaining edges */
  int es[16], ne = 0;
  u64 ex = rem & inc[cur];
  while (ex) { int e = __builtin_ctzll(ex); ex &= ex - 1; es[ne++] = e; }
  for (int i = ne - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = es[i]; es[i] = es[j]; es[j] = t; }
  for (int i = 0; i < ne; i++) {
    int e = es[i];
    int w = E_u[e] == cur ? E_v[e] : E_u[e];
    if (vis >> w & 1) continue;
    u64 rem2 = rem & ~(1ULL << e);
    dpath[dnp][dlen[dnp]++] = w;
    int order = rnd() & 1;    /* randomly try closing first or extending first */
    for (int pass = 0; pass < 2; pass++) {
      int closing = (pass == 0) ? order : !order;
      if (closing) {
        if (!(ended >> w & 1)) {
          dnp++;
          if (dive(rem2, ended | (1u << s) | (1u << w))) return 1;
          dnp--;
        }
      } else if (rem2 & inc[w]) {
        if (dgrow(s, w, rem2, ended, vis | (1u << w))) return 1;
      }
      if (dnodes > dcap) { dlen[dnp]--; return 0; }
    }
    dlen[dnp]--;
  }
  return 0;
}
static int dive(u64 rem, u32 ended) {
  u32 all = (1u << n) - 1, todo = all & ~ended;
  if (!todo) return rem == 0;
  if (!rem) return 0;
  if (++dnodes > dcap) return 0;
  int P = __builtin_popcount(todo) / 2;
  int cand[MAXN], nc = 0, bd = 99;
  for (int v = 0; v < n; v++) {
    int d = __builtin_popcountll(rem & inc[v]), nd = todo >> v & 1;
    if ((d ^ nd) & 1) return 0;
    if (d > 2 * P - nd) return 0;
    if (nd && d == 0) return 0;
    if (nd) { if (d < bd) { bd = d; nc = 0; } if (d == bd) cand[nc++] = v; }
  }
  int s = cand[rnd() % nc];
  dlen[dnp] = 1; dpath[dnp][0] = s;
  return dgrow(s, s, rem, ended, 1u << s);
}
/* a random Lovasz decomposition: solve a randomly relabelled copy exactly (ndsolve.h, which
   returns the first decomposition in its search order) and map it back; with probability 1/2
   use a randomised dive instead (cheap on sparse graphs) */

/* relabel F randomly into the solver (perm: F -> solver labels) */
static void load_relabelled(void) {
  for (int v = 0; v < n; v++) perm[v] = v;
  for (int v = n - 1; v > 0; v--) { int j = rnd() % (v + 1); int t = perm[v]; perm[v] = perm[j]; perm[j] = t; }
  for (int v = 0; v < n; v++) iperm[perm[v]] = v;
  sinit(n);
  int eo[64]; for (int e = 0; e < m; e++) eo[e] = e;
  for (int e = m - 1; e > 0; e--) { int j = rnd() % (e + 1); int t = eo[e]; eo[e] = eo[j]; eo[j] = t; }
  for (int k = 0; k < m; k++) sadd(perm[E_u[eo[k]]], perm[E_v[eo[k]]]);
  sneed = (1u << n) - 1;
}
static void read_solution(void) {
  for (int i = 0; i < wn; i++) {
    u32 mk = 0; for (int j = 0; j < wlen[i]; j++) mk |= 1u << iperm[wpath[i][j]];
    int a = iperm[wpath[i][0]], b = iperm[wpath[i][wlen[i] - 1]];
    Qm[a] = mk; Qm[b] = mk; part[a] = b; part[b] = a;
  }
}
/* a random Lovasz decomposition: a randomised dive; if it fails, an exact solve of a randomly
   relabelled copy with a node budget */
static int random_decomp(void) {
  /* first an exact solve of a randomly relabelled copy with a node budget (strong pruning makes
     this fast on dense graphs); then randomised dives as a fallback */
  for (int tries = 0; tries < 4; tries++) {
    load_relabelled();
    sbudget = 20000;
    int ok = srun();
    sbudget = 0;
    if (ok) { read_solution(); return 1; }
  }
  for (int tries = 0; tries < 20; tries++) {
    dnodes = 0; dcap = 20000; dnp = 0;
    u64 full = m == 64 ? ~0ULL : ((1ULL << m) - 1);
    if (dive(full, 0)) {
      for (int i = 0; i < dnp; i++) {
        u32 mk = 0; for (int j = 0; j < dlen[i]; j++) mk |= 1u << dpath[i][j];
        int a = dpath[i][0], b = dpath[i][dlen[i] - 1];
        Qm[a] = mk; Qm[b] = mk; part[a] = b; part[b] = a;
      }
      return 1;
    }
  }
  return 0;
}

/* ---------------- units ---------------- */
typedef struct { int type; int v[4]; } unit;   /* type: 'P','K','C','S','R' */
static unit U[20000]; static int nu_;
static int nonadj(int a, int b) { return a != b && !(adj[a] >> b & 1); }
static void gen_units(int type) {
  nu_ = 0;
  for (int a = 0; a < n; a++) for (int b = 0; b < n; b++) {
    if (type == 'P') { if (nonadj(a, b)) { unit u = {'P', {a, b, -1, -1}}; U[nu_++] = u; } continue; }
    for (int c = 0; c < n; c++) {
      if (a == b || a == c || b == c) continue;
      if (type == 'K') {             /* a <- x <- b with (a, x, b) = (a, b, c) */
        if (nonadj(a, b) && nonadj(b, c)) { unit u = {'K', {a, b, c, -1}}; U[nu_++] = u; }
      } else if (type == 'S') {      /* u <- {x, y}, x < y */
        if (b < c && nonadj(a, b) && nonadj(a, c)) { unit u = {'S', {a, b, c, -1}}; U[nu_++] = u; }
      } else if (type == 'R') {      /* route c x b at c: (c, x, b) = (a, b, c) */
        if (nonadj(a, b) && nonadj(b, c)) { unit u = {'R', {a, b, c, -1}}; U[nu_++] = u; }
      } else if (type == 'L') {      /* claw rooted at a leaf: (a, v, b, c), v child of a, b, c children of v */
        for (int d = c + 1; d < n; d++) {
          if (d == a || d == b) continue;
          if (nonadj(a, b) && nonadj(b, c) && nonadj(b, d)) { unit u = {'L', {a, b, c, d}}; U[nu_++] = u; }
        }
      } else if (type == 'C') {
        for (int d = 0; d < n; d++) {
          if (d == a || d == b || d == c) continue;
          if (nonadj(a, b) && nonadj(b, c) && nonadj(c, d)) { unit u = {'C', {a, b, c, d}}; U[nu_++] = u; }
        }
      }
    }
  }
}
static u32 umask(const unit *u) {
  u32 mk = 0; for (int i = 0; i < 4; i++) if (u->v[i] >= 0) mk |= 1u << u->v[i]; return mk;
}
static int sat_unit(const unit *u) {
  const int *v = u->v;
  switch (u->type) {
  case 'P': return !(Qm[v[0]] >> v[1] & 1);
  case 'K': return !(Qm[v[1]] >> v[0] & 1) && !(Qm[v[2]] >> v[1] & 1);
  case 'C': return !(Qm[v[1]] >> v[0] & 1) && !(Qm[v[2]] >> v[1] & 1) && !(Qm[v[3]] >> v[2] & 1);
  case 'S': return !(Qm[v[1]] >> v[0] & 1) && !(Qm[v[2]] >> v[0] & 1) && part[v[1]] != v[2];
  case 'R': return !(Qm[v[0]] >> v[1] & 1) && !(Qm[v[0]] >> v[2] & 1);
  case 'L': return !(Qm[v[1]] >> v[0] & 1) && !(Qm[v[2]] >> v[1] & 1) && !(Qm[v[3]] >> v[1] & 1)
                   && part[v[2]] != v[3];
  }
  return 0;
}
/* exact: encode the units as route-respecting masks */
static void encode_unit(const unit *u) {
  const int *v = u->v;
  switch (u->type) {
  case 'P': crv[v[0]] |= 1u << v[1]; break;
  case 'K': crv[v[1]] |= 1u << v[0]; crv[v[2]] |= 1u << v[1]; break;
  case 'C': crv[v[1]] |= 1u << v[0]; crv[v[2]] |= 1u << v[1]; crv[v[3]] |= 1u << v[2]; break;
  case 'S': crv[v[1]] |= 1u << v[0]; crv[v[2]] |= 1u << v[0]; break;
  case 'R': crv[v[0]] |= (1u << v[1]) | (1u << v[2]); break;
  case 'L': crv[v[1]] |= 1u << v[0]; crv[v[2]] |= 1u << v[1]; crv[v[3]] |= 1u << v[1]; break;
  }
}
static void encode_perm(const unit *u) {
  unit w = *u;
  for (int i = 0; i < 4; i++) if (w.v[i] >= 0) w.v[i] = perm[w.v[i]];
  encode_unit(&w);
}
static int exact(const unit *a, const unit *b, const unit *c) {
  /* randomised budgeted attempts (a success is a certificate; failures prove nothing) */
  for (int t = 0; t < 12; t++) {
    load_relabelled();
    if (a) encode_perm(a);
    if (b) encode_perm(b);
    if (c) encode_perm(c);
    sbudget = 20000;
    int ok = srun();
    sbudget = 0;
    if (ok) return 1;
  }
  /* exhaustive exact search, original labels */
  sinit(n);
  for (int e = 0; e < m; e++) sadd(E_u[e], E_v[e]);
  sneed = (1u << n) - 1;
  if (a) encode_unit(a);
  if (b) encode_unit(b);
  if (c) encode_unit(c);
  return srun();
}
/* the masks of different units are disjoint vertex sets, so crv[s] & crv[w] != 0 only inside a
   unit; inside a unit it forbids exactly the pairings that (i) already forbids, or two siblings
   (star), or for a route the pairing of c with x or b (already forbidden by x, b notin Q(c)). */

static int h1_ok(const unit *s) {
  int u = s->v[0];
  int c1 = s->v[1], c2 = s->v[2];
  if (s->type == 'L') { u = s->v[1]; c1 = s->v[2]; c2 = s->v[3]; }
  u32 all = ((1u << n) - 1) & ~(1u << u), seen = 0;
  for (int v = 0; v < n; v++) {
    if (!(all >> v & 1) || (seen >> v & 1)) continue;
    u32 c = 1u << v, fr = c;
    while (fr) { int x = __builtin_ctz(fr); fr &= fr - 1; u32 nb = adj[x] & all & ~c; c |= nb; fr |= nb; }
    seen |= c;
    int k = (c >> c1 & 1) + (c >> c2 & 1);
    int e = __builtin_popcount(adj[u] & c);
    if (2 * k > __builtin_popcount(c) - e) return 0;
  }
  return 1;
}

static void print_unit(const unit *u) {
  printf(" %c", u->type);
  for (int i = 0; i < 4; i++) if (u->v[i] >= 0) printf(" %d", u->v[i]);
}

int main(int argc, char **argv) {
  const char *fam = "k";
  int dives = 600;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "-f") && i + 1 < argc) fam = argv[++i];
    else if (!strcmp(argv[i], "-d") && i + 1 < argc) dives = atoi(argv[++i]);
    else if (!strcmp(argv[i], "-s") && i + 1 < argc) rs = strtoull(argv[++i], 0, 10) * 2654435761ULL + 1;
  }
  int T1 = 0, T2 = 0, T3 = 0;   /* unit types of the family: first, second, third (0 = none) */
  if (!strcmp(fam, "k")) T1 = 'K';
  else if (!strcmp(fam, "c")) T1 = 'C';
  else if (!strcmp(fam, "s")) T1 = 'S';
  else if (!strcmp(fam, "r")) T1 = 'R';
  else if (!strcmp(fam, "kp")) { T1 = 'K'; T2 = 'P'; }
  else if (!strcmp(fam, "kk")) { T1 = 'K'; T2 = 'K'; }
  else if (!strcmp(fam, "sp")) { T1 = 'S'; T2 = 'P'; }
  else if (!strcmp(fam, "rp")) { T1 = 'R'; T2 = 'P'; }
  else if (!strcmp(fam, "kpp")) { T1 = 'K'; T2 = 'P'; T3 = 'P'; }
  else if (!strcmp(fam, "l")) T1 = 'L';
  else if (!strcmp(fam, "lp")) { T1 = 'L'; T2 = 'P'; }
  else if (!strcmp(fam, "sk")) { T1 = 'S'; T2 = 'K'; }
  else if (!strcmp(fam, "lk")) { T1 = 'L'; T2 = 'K'; }
  else if (!strcmp(fam, "cp")) { T1 = 'C'; T2 = 'P'; }
  else if (!strcmp(fam, "ss")) { T1 = 'S'; T2 = 'S'; }
  else { fprintf(stderr, "unknown family\n"); return 1; }
  long long ngraphs = 0, nsets = 0, nfail = 0, nexact = 0, nfail_h1 = 0, nfail_noh1 = 0, nskipH1 = 0;
  int skipH1 = 0;
  for (int i = 1; i < argc; i++) if (!strcmp(argv[i], "-H")) skipH1 = 1;
  static unit A[20000], Bu[20000];
  static u64 cov[20000][160];        /* coverage: per first unit, bitset over second units (or pairs of P) */
  while (fgets(g6, sizeof g6, stdin)) {
    g6[strcspn(g6, "\r\n")] = 0;
    if (!g6[0] || !read_g6(g6)) continue;
    int odd = 1;
    for (int v = 0; v < n; v++) if (!(__builtin_popcount(adj[v]) & 1)) odd = 0;
    if (!odd) continue;
    /* connected? */
    u32 seen = 1, fr = 1;
    while (fr) { int x = __builtin_ctz(fr); fr &= fr - 1; u32 nb = adj[x] & ~seen; seen |= nb; fr |= nb; }
    if (seen != (1u << n) - 1) continue;
    ngraphs++;
    m = 0;
    for (int v = 0; v < n; v++) inc[v] = 0;
    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) if (adj[a] >> b & 1) {
      E_u[m] = a; E_v[m] = b; inc[a] |= 1ULL << m; inc[b] |= 1ULL << m; m++;
    }
    gen_units(T1); int na = nu_; memcpy(A, U, na * sizeof(unit));
    int nb = 0;
    if (T2) { gen_units(T2); nb = nu_; memcpy(Bu, U, nb * sizeof(unit)); }
    /* third unit (kpp): pairs again, the same list as Bu */
    int words = T2 ? (T3 ? ((nb * nb + 63) / 64) : ((nb + 63) / 64)) : 1;
    if (words > 160) {
      /* kpp at n = 10: too many pair-pairs for the bitset; fall back to per-set phase 2 only */
      words = 0;
    }
    for (int i = 0; i < na; i++) for (int w = 0; w < (words ? words : 1); w++) cov[i][w] = 0;
    /* phase 1 */
    for (int d = 0, fails = 0; d < dives && fails < 4 * dives; d++) {
      if (!random_decomp()) { fails++; d--; continue; }
      /* the second-level units satisfied by this decomposition, once */
      static u64 satB[160]; static int sj[20000]; int ns = 0;
      if (T2 && words) {
        for (int w = 0; w < words; w++) satB[w] = 0;
        for (int j = 0; j < nb; j++) if (sat_unit(&Bu[j])) sj[ns++] = j;
        if (!T3) for (int x = 0; x < ns; x++) satB[sj[x] >> 6] |= 1ULL << (sj[x] & 63);
        else for (int x = 0; x < ns; x++) for (int y = 0; y < ns; y++) {
          int idx = sj[x] * nb + sj[y]; satB[idx >> 6] |= 1ULL << (idx & 63);
        }
      }
      for (int i = 0; i < na; i++) {
        if (!sat_unit(&A[i])) continue;
        if (!T2) { cov[i][0] = 1; continue; }
        if (!words) continue;
        for (int w = 0; w < words; w++) cov[i][w] |= satB[w];
      }
    }
    /* phase 2 */
    for (int i = 0; i < na; i++) {
      u32 mi = umask(&A[i]);
      if (!T2) {
        nsets++;
        if (cov[i][0]) continue;
        if (skipH1 && (A[i].type == 'S' || A[i].type == 'L') && !h1_ok(&A[i])) { nskipH1++; continue; }
        nexact++;
        if (!exact(&A[i], 0, 0)) {
          nfail++;
          int h = (A[i].type == 'S' || A[i].type == 'L') ? h1_ok(&A[i]) : -1;
          if (h == 1) nfail_h1++; else if (h == 0) nfail_noh1++;
          printf("FAIL %s", g6); print_unit(&A[i]);
          if (h >= 0) printf(" H1=%d", h);
          printf("\n"); fflush(stdout);
        }
        continue;
      }
      for (int j = 0; j < nb; j++) {
        u32 mj = umask(&Bu[j]);
        if (mi & mj) continue;
        if (T2 == T1 && j <= i) continue;   /* two units of the same type: unordered */
        if (!T3) {
          nsets++;
          if (cov[i][j >> 6] >> (j & 63) & 1) continue;
          if (skipH1 && (((A[i].type == 'S' || A[i].type == 'L') && !h1_ok(&A[i])) ||
                         ((Bu[j].type == 'S' || Bu[j].type == 'L') && !h1_ok(&Bu[j])))) { nskipH1++; continue; }
          nexact++;
          if (!exact(&A[i], &Bu[j], 0)) {
            nfail++;
            int h = (A[i].type == 'S' || A[i].type == 'L') ? h1_ok(&A[i]) : -1;
            if (h == 1) nfail_h1++; else if (h == 0) nfail_noh1++;
            printf("FAIL %s", g6); print_unit(&A[i]); print_unit(&Bu[j]);
            if (h >= 0) printf(" H1=%d", h);
            printf("\n"); fflush(stdout);
          }
        } else {
          for (int k = j + 1; k < nb; k++) {
            u32 mk = umask(&Bu[k]);
            if ((mk & mi) || (mk & mj)) continue;
            nsets++;
            int idx = j * nb + k;
            if (words && (cov[i][idx >> 6] >> (idx & 63) & 1)) continue;
            nexact++;
            if (!exact(&A[i], &Bu[j], &Bu[k])) {
              nfail++;
              printf("FAIL %s", g6); print_unit(&A[i]); print_unit(&Bu[j]); print_unit(&Bu[k]);
              printf("\n"); fflush(stdout);
            }
          }
        }
      }
    }
  }
  fprintf(stderr, "SUMMARY family=%s graphs=%lld sets=%lld exact=%lld failures=%lld", fam, ngraphs, nsets, nexact, nfail);
  if (T1 == 'S' || T1 == 'L') fprintf(stderr, " (H1 holds at %lld of them, fails at %lld)", nfail_h1, nfail_noh1);
  if (skipH1) fprintf(stderr, " unstruck sets violating (H1), not searched (they fail by the Hall lemma): %lld", nskipH1);
  fprintf(stderr, "\n");
  return 0;
}
