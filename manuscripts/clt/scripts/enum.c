/* enum.c: enumerate ALL Lovász decompositions of small graphs (session claude/clt).
   A Lovász decomposition of G (at most one vertex of positive even degree) is a decomposition of
   E(G) into paths in which every vertex v is an end of exactly (deg v mod 2) paths.
   For every decomposition D and every odd vertex v we record the end-path signature
       mask(P_v)   (vertex set of the path ending at v),
       partner(v)  (the other end of P_v),
       term(v)     (the neighbour of v on P_v, so v term(v) is the terminal edge at v).
   Distinct signatures are printed, one per line:  "S m_0 p_0 t_0 m_1 p_1 t_1 ..." over all v
   (entries -1 for even vertices).  Input: graph6 lines on stdin (n <= 12).
   Header per graph: "G <graph6> <number of distinct signatures> <number of decompositions>".
   The DFS is the engine of manuscripts/t6-dense/scripts/lsearch.c (paths grown from a vertex with
   an end, chosen deterministically from the state, so each decomposition is produced once), with a
   memo of dead states (a state with no completion has no completion however it is reached). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 12
#define MAXM 66
typedef uint64_t u64;

static int n, m;
static int eu[MAXM], ev[MAXM];
static int eid[MAXN][MAXN];
static u64 inc[MAXN];
static int b[MAXN];
static u64 rem;

/* dead-state memo */
typedef struct { u64 mask; u64 prof; } key_t2;
static key_t2 *tab; static uint8_t *used; static size_t cap, cnt;
static size_t hh(u64 a, u64 p) { u64 x = a * 0x9E3779B97F4A7C15ULL ^ (p + 0x632BE59BD9B4E019ULL + (a << 6)); x ^= x >> 31; x *= 0xBF58476D1CE4E5B9ULL; x ^= x >> 29; return (size_t)x; }
static void hinit(void) { if (!tab) { cap = 1u << 20; tab = malloc(cap * sizeof(key_t2)); used = calloc(cap, 1); } else memset(used, 0, cap); cnt = 0; }
static int hfind(u64 a, u64 p) { size_t i = hh(a, p) & (cap - 1); while (used[i]) { if (tab[i].mask == a && tab[i].prof == p) return 1; i = (i + 1) & (cap - 1); } return 0; }
static void hadd(u64 a, u64 p) {
  if (cnt * 2 > cap) {
    size_t oc = cap; key_t2 *ot = tab; uint8_t *ou = used;
    cap *= 2; tab = malloc(cap * sizeof(key_t2)); used = calloc(cap, 1); cnt = 0;
    for (size_t i = 0; i < oc; i++) if (ou[i]) hadd(ot[i].mask, ot[i].prof);
    free(ot); free(ou);
  }
  size_t i = hh(a, p) & (cap - 1); while (used[i]) i = (i + 1) & (cap - 1);
  used[i] = 1; tab[i].mask = a; tab[i].prof = p; cnt++;
}

/* signature store */
#define SIGW (3 * MAXN)
typedef struct { int16_t s[SIGW]; } sig_t;
static sig_t *sigs; static size_t nsig, sigcap;
static uint32_t *sh; static size_t shcap;
static size_t sighash(const sig_t *s) { u64 x = 1469598103934665603ULL; for (int i = 0; i < 3 * n; i++) { x ^= (uint16_t)s->s[i]; x *= 1099511628211ULL; } return (size_t)x; }
static void sigreset(void) { nsig = 0; if (!sh) { shcap = 1u << 16; sh = malloc(shcap * sizeof(uint32_t)); } memset(sh, 0xff, shcap * sizeof(uint32_t)); }
static void siginsert(const sig_t *s);
static void sggrow(void) {
  free(sh); shcap *= 2; sh = malloc(shcap * sizeof(uint32_t)); memset(sh, 0xff, shcap * sizeof(uint32_t));
  for (size_t k = 0; k < nsig; k++) { size_t i = sighash(&sigs[k]) & (shcap - 1); while (sh[i] != 0xffffffffu) i = (i + 1) & (shcap - 1); sh[i] = (uint32_t)k; }
}
static void siginsert(const sig_t *s) {
  if (nsig * 2 >= shcap) sggrow();
  size_t i = sighash(s) & (shcap - 1);
  while (sh[i] != 0xffffffffu) { if (!memcmp(sigs[sh[i]].s, s->s, 3 * n * sizeof(int16_t))) return; i = (i + 1) & (shcap - 1); }
  if (nsig == sigcap) { sigcap = sigcap ? 2 * sigcap : 1024; sigs = realloc(sigs, sigcap * sizeof(sig_t)); }
  sigs[nsig] = *s; sh[i] = (uint32_t)nsig; nsig++;
}

static sig_t cur; /* current partial signature */
static int noterm; /* -t: drop the terminal edges from the signature */
static unsigned long long ndec;
/* -v L mode: store distinct violation masks over the atom universe instead of signatures.
   atoms: av(c,a) at bit c*n+a (if allowed by locality L), ne(u,v) (u<v) at bit n*n+u*n+v.
   L = 0: every av atom; L = 1: a not in N[c] u N(g); L = 2: a not in N[c]. */
static int vmode = -1;
static int packedE = 0;   /* -E: accept graphs whose positive-even vertices are pairwise at distance >= 3 */
static int dist[MAXN][MAXN];
static int pathmask[MAXM]; static int npm;
typedef struct { u64 w[4]; } vm_t;
static vm_t *vms; static size_t nvm, vmcap; static uint32_t *vh; static size_t vhcap;
static vm_t allowed;
static size_t vmhash(const vm_t *x) { u64 h = x->w[0] * 0x9E3779B97F4A7C15ULL ^ x->w[1] * 0xC2B2AE3D27D4EB4FULL ^ x->w[2] * 0x165667B19E3779F9ULL ^ x->w[3]; h ^= h >> 31; h *= 0xBF58476D1CE4E5B9ULL; h ^= h >> 29; return (size_t)h; }
static void vmreset(void) { nvm = 0; if (!vh) { vhcap = 1u << 12; vh = malloc(vhcap * sizeof(uint32_t)); } memset(vh, 0xff, vhcap * sizeof(uint32_t)); }
static void vmgrow(void) { free(vh); vhcap *= 2; vh = malloc(vhcap * sizeof(uint32_t)); memset(vh, 0xff, vhcap * sizeof(uint32_t));
  for (size_t k = 0; k < nvm; k++) { size_t i = vmhash(&vms[k]) & (vhcap - 1); while (vh[i] != 0xffffffffu) i = (i + 1) & (vhcap - 1); vh[i] = (uint32_t)k; } }
static void vminsert(const vm_t *x) {
  if (nvm * 2 >= vhcap) vmgrow();
  size_t i = vmhash(x) & (vhcap - 1);
  while (vh[i] != 0xffffffffu) { if (!memcmp(&vms[vh[i]], x, sizeof(vm_t))) return; i = (i + 1) & (vhcap - 1); }
  if (nvm == vmcap) { vmcap = vmcap ? 2 * vmcap : 1024; vms = realloc(vms, vmcap * sizeof(vm_t)); }
  vms[nvm] = *x; vh[i] = (uint32_t)nvm; nvm++;
}
static void setbit(vm_t *x, int i) { x->w[i >> 6] |= (u64)1 << (i & 63); }
static void record(void) {
  if (vmode < 0) { siginsert(&cur); return; }
  vm_t x; memset(&x, 0, sizeof x);
  if (vmode == 5) {   /* sep atoms: pair {p,q} (p<q) at bit p*n+q, violated if a path contains both */
    for (int k = 0; k < npm; k++) { int mk = pathmask[k];
      for (int p = 0; p < n; p++) if (mk >> p & 1) for (int q = p + 1; q < n; q++) if (mk >> q & 1) setbit(&x, p * n + q); }
    for (int k = 0; k < 4; k++) x.w[k] &= allowed.w[k];
    vminsert(&x); return;
  }
  for (int c = 0; c < n; c++) { if (cur.s[3 * c] < 0) continue;
    int mk = cur.s[3 * c], p = cur.s[3 * c + 1];
    for (int a = 0; a < n; a++) if (a != c && ((mk >> a) & 1)) setbit(&x, c * n + a);
    if (c < p) setbit(&x, n * n + c * n + p); }
  for (int k = 0; k < 4; k++) x.w[k] &= allowed.w[k];
  vminsert(&x);
}
static int popv(const vm_t *x) { int s = 0; for (int k = 0; k < 4; k++) s += __builtin_popcountll(x->w[k]); return s; }
static int subv(const vm_t *x, const vm_t *y) { for (int k = 0; k < 4; k++) if (x->w[k] & ~y->w[k]) return 0; return 1; }
static int cmpv(const void *p, const void *q) { return popv(p) - popv(q); }
static int pbuf[MAXM][MAXN + 1], plens[MAXM], pd;
#define pathbuf pbuf[pd]
#define plen plens[pd]

static int deg(int v) { return __builtin_popcountll(rem & inc[v]); }
static u64 packb(void) { u64 p = 0; for (int v = 0; v < n; v++) p |= (u64)b[v] << (2 * v); return p; }

static int prune_ok(int *bestp) {
  int S = 0; for (int v = 0; v < n; v++) S += b[v];
  if (S & 1) return 0;
  int P = S / 2, best = -1, bd = 999;
  for (int v = 0; v < n; v++) {
    int d = deg(v);
    if (b[v] > P || b[v] > d || d > 2 * P - b[v] || ((d - b[v]) & 1)) return 0;
    if (b[v] > 0 && d < bd) { bd = d; best = v; }
  }
  uint32_t seen = 0;
  for (int v = 0; v < n; v++) {
    if ((seen >> v & 1) || !(rem & inc[v])) continue;
    uint32_t comp = 1u << v, fr = 1u << v;
    while (fr) { int x = __builtin_ctz(fr); fr &= fr - 1; u64 ex = rem & inc[x];
      while (ex) { int e = __builtin_ctzll(ex); ex &= ex - 1; int y = eu[e] == x ? ev[e] : eu[e]; if (!(comp >> y & 1)) { comp |= 1u << y; fr |= 1u << y; } } }
    seen |= comp; int s = 0; for (int x = 0; x < n; x++) if (comp >> x & 1) s += b[x];
    if (s < 2) return 0;
  }
  *bestp = best; return 1;
}

static long long solve(void);
static long long extend(int a, int c, uint32_t vis) {
  long long tot = 0;
  for (int w = 0; w < n; w++) {
    if (vis >> w & 1) continue;
    int e = eid[c][w]; if (e < 0 || !((rem >> e) & 1)) continue;
    uint32_t vis2 = vis | (1u << w);
    rem &= ~((u64)1 << e); pathbuf[plen++] = w;
    if (b[w] > 0) {
      b[a]--; b[w]--;
      sig_t save = cur;
      cur.s[3 * a] = (int16_t)vis2; cur.s[3 * a + 1] = (int16_t)w; cur.s[3 * a + 2] = noterm ? -1 : (int16_t)pathbuf[1];
      cur.s[3 * w] = (int16_t)vis2; cur.s[3 * w + 1] = (int16_t)a; cur.s[3 * w + 2] = noterm ? -1 : (int16_t)pathbuf[plen - 2];
      pathmask[npm++] = (int)vis2;
      pd++; plens[pd] = 0;
      tot += solve();
      pd--;
      cur = save; npm--;
      b[a]++; b[w]++;
    }
    if (rem & inc[w]) tot += extend(a, w, vis2);
    plen--; rem |= (u64)1 << e;
  }
  return tot;
}
static long long solve(void) {
  int S = 0; for (int v = 0; v < n; v++) S += b[v];
  if (rem == 0) { if (S == 0) { record(); ndec++; return 1; } return 0; }
  if (S == 0) return 0;
  int best; if (!prune_ok(&best)) return 0;
  u64 pk = packb(); if (hfind(rem, pk)) return 0;
  plen = 1; pathbuf[0] = best;
  long long r = extend(best, best, 1u << best);
  if (r == 0) hadd(rem, pk);
  return r;
}

int main(int argc, char **argv) {
  char line[256];
  int quiet = 0;
  for (int i = 1; i < argc; i++) { if (!strcmp(argv[i], "-q")) quiet = 1; if (!strcmp(argv[i], "-t")) noterm = 1; if (!strcmp(argv[i], "-v") && i + 1 < argc) { vmode = atoi(argv[++i]); noterm = 1; } if (!strcmp(argv[i], "-E")) packedE = 1; }
  while (fgets(line, sizeof line, stdin)) {
    int L = (int)strlen(line); while (L && (line[L - 1] == '\n' || line[L - 1] == '\r')) line[--L] = 0;
    if (!L) continue;
    n = line[0] - 63; if (n > MAXN) { fprintf(stderr, "n too large\n"); return 1; }
    int adj[MAXN][MAXN]; memset(adj, 0, sizeof adj);
    int k = 0, pos = 1, bit = 5;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
      int v = line[pos] - 63; if ((v >> bit) & 1) adj[i][j] = adj[j][i] = 1;
      if (--bit < 0) { bit = 5; pos++; } k++;
    }
    m = 0; for (int i = 0; i < n; i++) { inc[i] = 0; for (int j = 0; j < n; j++) eid[i][j] = -1; }
    for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if (adj[i][j]) { eu[m] = i; ev[m] = j; eid[i][j] = eid[j][i] = m; inc[i] |= (u64)1 << m; inc[j] |= (u64)1 << m; m++; }
    int nev = 0; for (int v = 0; v < n; v++) { int d = __builtin_popcountll(inc[v]); b[v] = d & 1; if (d > 0 && !(d & 1)) nev++; }
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) dist[i][j] = i == j ? 0 : (adj[i][j] ? 1 : 99);
    for (int k2 = 0; k2 < n; k2++) for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (dist[i][k2] + dist[k2][j] < dist[i][j]) dist[i][j] = dist[i][k2] + dist[k2][j];
    if (packedE) {
      int bad = 0;
      for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++) { int du = __builtin_popcountll(inc[u]), dv = __builtin_popcountll(inc[v]);
        if (du > 0 && !(du & 1) && dv > 0 && !(dv & 1) && dist[u][v] < 3) bad = 1; }
      if (bad) continue;
    } else if (nev > 1) continue;
    rem = (m == 64) ? ~(u64)0 : (((u64)1 << m) - 1); npm = 0;
    for (int i = 0; i < SIGW; i++) cur.s[i] = -1;
    hinit(); sigreset(); vmreset(); ndec = 0; pd = 0; plens[0] = 0;
    if (vmode >= 0) {
      int gv = -1; for (int v = 0; v < n; v++) { int d = __builtin_popcountll(inc[v]); if (d > 0 && !(d & 1)) gv = v; }
      memset(&allowed, 0, sizeof allowed);
      for (int c = 0; c < n; c++) if (b[c]) for (int a = 0; a < n; a++) {
        if (a == c || !inc[a]) continue;
        int loc = !adj[c][a] && !(gv >= 0 && adj[gv][a]);
        if (vmode == 0 || (vmode == 1 && loc) || (vmode == 2 && !adj[c][a])) setbit(&allowed, c * n + a);
      }
      for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++) if (b[u] && b[v]) setbit(&allowed, n * n + u * n + v);
      if (vmode == 5) { memset(&allowed, 0, sizeof allowed);
        for (int p = 0; p < n; p++) for (int q = p + 1; q < n; q++) if (inc[p] && inc[q] && dist[p][q] >= 3) setbit(&allowed, p * n + q); }
    }
    solve();
    if (vmode >= 0) {
      qsort(vms, nvm, sizeof(vm_t), cmpv);
      size_t nk = 0;
      for (size_t i = 0; i < nvm; i++) { int dom = 0; for (size_t j = 0; j < nk; j++) if (subv(&vms[j], &vms[i])) { dom = 1; break; } if (!dom) vms[nk++] = vms[i]; }
      printf("G %s %zu %llu\n", line, nk, ndec);
      for (size_t i = 0; i < nk; i++) { printf("V");
        for (int c = 0; c < n; c++) for (int a = 0; a < n; a++) { int bi = c * n + a; if ((vms[i].w[bi >> 6] >> (bi & 63)) & 1) printf(vmode == 5 ? " s%d,%d" : " a%d,%d", c, a); }
        for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++) { int bi = n * n + u * n + v; if ((vms[i].w[bi >> 6] >> (bi & 63)) & 1) printf(" n%d,%d", u, v); }
        printf("\n"); }
      continue;
    }
    printf("G %s %zu %llu\n", line, nsig, ndec);
    if (!quiet) for (size_t s = 0; s < nsig; s++) { printf("S"); for (int i = 0; i < 3 * n; i++) printf(" %d", sigs[s].s[i]); printf("\n"); }
  }
  return 0;
}
