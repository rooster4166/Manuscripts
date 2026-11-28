/* a43.c -- audit A43: independent solver and checks for manuscripts/conj31.
 *
 * Shares no code with manuscripts/conj31/scripts (psolve.h, blockcrit.h, ...).
 *
 * Solver: a path decomposition of G with end profile b is the same as a transition system:
 * at every vertex x, b(x) incident edges are left as path ends and the other d(x)-b(x)
 * are paired (a pair = a pass of a path through x), such that the trails obtained by
 * following the pairs are simple paths (no closed trail, no repeated vertex).  We fix the
 * transitions vertex by vertex and keep the partial trails as fragments in a union-find
 * over edges, each root carrying the vertex set of its fragment.  Pairing two edge ends at
 * the current vertex x is allowed iff the two fragments are different and share only x;
 * this keeps every fragment a simple path, so every completed system is a decomposition.
 * The search is complete (every transition system is enumerated once).  No pruning other
 * than parity/cardinality at a vertex, unless the caller asks for the (DB) pre-check.
 * Every positive answer is re-checked by rebuilding the paths from the transitions.
 *
 * Block decomposition: two edges are in the same block iff for every vertex x their
 * remaining endpoints lie in one component of G - x.  BC as in conj31 Def 7.2 / Thm 7.1.
 *
 * Modes (graph6 on stdin):
 *   census        connected graphs: two-even count, tight, O1, 2-conn, BC agreement
 *   pc MAXZ       2-connected graphs: every zero set of size MAXZ, every profile
 *   j             all-odd connected graphs: Conjecture J instances, (L)/(C)/(B) classification
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 12
#define MAXE 66

/* ------------------------------------------------------------------ graph6 */
static int decode_g6(const char *s, int *n, uint32_t *adj) {
  int nn = s[0] - 63;
  if (nn < 1 || nn > MAXN) return 0;
  for (int i = 0; i < MAXN; i++) adj[i] = 0;
  const char *p = s + 1;
  int bitpos = 0, cur = 0;
  for (int j = 1; j < nn; j++)
    for (int i = 0; i < j; i++) {
      if (bitpos == 0) { if (!*p) return 0; cur = *p++ - 63; bitpos = 6; }
      bitpos--;
      if ((cur >> bitpos) & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
    }
  *n = nn;
  return 1;
}

static int popc(uint32_t x) { return __builtin_popcount(x); }

/* ------------------------------------------------------------------ solver */
static int sN, sm;
static int seu[MAXE], sev[MAXE];
static int sinc[MAXN][MAXN], sdeg[MAXN];
static int sidx[MAXN][MAXN];              /* sidx[x][y] = index of edge xy in x's list */
static int sord[MAXN], sb[MAXN];
static int par[MAXE];
static uint32_t vm[MAXE];
static int ur1[MAXE], ur2[MAXE];
static uint32_t uvm[MAXE];
static int usp;
static int partner[MAXN][MAXN];           /* -1 = end, else paired incident index */
static long snodes;

static int uf_find(int e) { while (par[e] != e) e = par[e]; return e; }
static int try_union(int e1, int e2, int x) {
  int r1 = uf_find(e1), r2 = uf_find(e2);
  if (r1 == r2) return 0;
  if ((vm[r1] & vm[r2]) != (1u << x)) return 0;
  ur1[usp] = r1; ur2[usp] = r2; uvm[usp] = vm[r1]; usp++;
  par[r2] = r1; vm[r1] |= vm[r2];
  return 1;
}
static void undo_union(void) { usp--; par[ur2[usp]] = ur2[usp]; vm[ur1[usp]] = uvm[usp]; }

static int solve_vertex(int i);
static long g_limit = 0, nundecided = 0;   /* optional node limit per solve (0 = none) */
static int s_abort;
static int match_at(int i, int x, int ends_left, int *used, int nfree) {
  snodes++;
  if (g_limit && snodes > g_limit) { s_abort = 1; return 0; }
  if (s_abort) return 0;
  if (nfree < ends_left || ((nfree - ends_left) & 1)) return 0;
  if (nfree == 0) return solve_vertex(i + 1);
  int k = 0;
  while (used[k]) k++;
  if (ends_left > 0) {
    used[k] = 1; partner[x][k] = -1;
    if (match_at(i, x, ends_left - 1, used, nfree - 1)) return 1;
    used[k] = 0;
  }
  for (int t = k + 1; t < sdeg[x]; t++) {
    if (used[t]) continue;
    if (!try_union(sinc[x][k], sinc[x][t], x)) continue;
    used[k] = used[t] = 1; partner[x][k] = t; partner[x][t] = k;
    if (match_at(i, x, ends_left, used, nfree - 2)) return 1;
    used[k] = used[t] = 0;
    undo_union();
  }
  return 0;
}
static int solve_vertex(int i) {
  if (i == sN) return 1;
  int x = sord[i];
  int used[MAXN] = {0};
  return match_at(i, x, sb[x], used, sdeg[x]);
}

/* witness: paths rebuilt from the transitions */
static int wnp, wlen[64], wpath[64][MAXN + 1];
static int rebuild_and_check(int n, const uint32_t *adj, const int *b) {
  int seen[MAXE] = {0};
  int ends[MAXN] = {0};
  wnp = 0;
  for (int x = 0; x < n; x++)
    for (int k = 0; k < sdeg[x]; k++) {
      if (partner[x][k] != -1) continue;
      int e = sinc[x][k];
      if (seen[e]) continue;
      int L = 0; uint32_t vis = 1u << x;
      wpath[wnp][L++] = x;
      int cur = x, ce = e;
      while (1) {
        if (seen[ce]) return 0;
        seen[ce] = 1;
        int y = seu[ce] == cur ? sev[ce] : seu[ce];
        if (vis >> y & 1) return 0;          /* repeated vertex */
        vis |= 1u << y;
        wpath[wnp][L++] = y;
        int kk = sidx[y][cur];
        if (partner[y][kk] == -1) break;
        ce = sinc[y][partner[y][kk]];
        cur = y;
      }
      wlen[wnp] = L;
      ends[wpath[wnp][0]]++; ends[wpath[wnp][L - 1]]++;
      wnp++;
    }
  for (int e = 0; e < sm; e++) if (!seen[e]) return 0;   /* an edge on a closed trail */
  for (int x = 0; x < n; x++) if (ends[x] != b[x]) return 0;
  /* each edge of adj used exactly once */
  int cnt = 0;
  for (int p = 0; p < wnp; p++)
    for (int j = 0; j + 1 < wlen[p]; j++) { if (!(adj[wpath[p][j]] >> wpath[p][j + 1] & 1)) return 0; cnt++; }
  int m = 0;
  for (int x = 0; x < n; x++) m += popc(adj[x]);
  return cnt * 2 == m;
}

static long nwitness_ok, nwitness_bad;
/* returns 1 if b is realisable in the graph adj (n vertices), 0 if not */
static int g_start = -1;   /* forced first vertex of the order (portfolio retries) */
static int realisable1(int n, const uint32_t *adj, const int *b, int dbcheck);
static int realisable(int n, const uint32_t *adj, const int *b, int dbcheck) {
  g_start = -1;
  int r = realisable1(n, adj, b, dbcheck);
  if (r || !s_abort) return r;
  for (int st = 0; st < n; st++) {
    g_start = st;
    r = realisable1(n, adj, b, dbcheck);
    if (r || !s_abort) { g_start = -1; return r; }
  }
  g_start = -1;
  nundecided++; fprintf(stderr, "UNDECIDED (node limit, all starts)\n");
  return 0;
}
static int realisable1(int n, const uint32_t *adj, const int *b, int dbcheck) {
  sN = n; sm = 0;
  for (int x = 0; x < n; x++) { sdeg[x] = 0; }
  for (int x = 0; x < n; x++)
    for (int y = x + 1; y < n; y++)
      if (adj[x] >> y & 1) {
        seu[sm] = x; sev[sm] = y;
        sidx[x][y] = sdeg[x]; sinc[x][sdeg[x]++] = sm;
        sidx[y][x] = sdeg[y]; sinc[y][sdeg[y]++] = sm;
        par[sm] = sm; vm[sm] = (1u << x) | (1u << y);
        sm++;
      }
  int S = 0;
  for (int x = 0; x < n; x++) {
    if (b[x] < 0 || b[x] > sdeg[x] || ((b[x] - sdeg[x]) & 1)) return 0;
    S += b[x];
    sb[x] = b[x];
  }
  if (sm > 0 && S == 0) return 0;
  if (dbcheck) for (int x = 0; x < n; x++) if (sdeg[x] + b[x] > S) return 0;
  /* order: maximum cardinality search (next = most already-ordered neighbours, then degree) */
  int placed[MAXN] = {0};
  for (int k = 0; k < n; k++) {
    int s = -1, sc = -1;
    for (int x = 0; x < n; x++) {
      if (placed[x]) continue;
      int c = 0;
      for (int y = 0; y < n; y++) if (placed[y] && (adj[x] >> y & 1)) c++;
      int score = c * 64 + sdeg[x];
      if (k == 0 && g_start >= 0) score = (x == g_start) ? 1 << 20 : 0;
      if (score > sc) { sc = score; s = x; }
    }
    sord[k] = s; placed[s] = 1;
  }
  usp = 0; snodes = 0; s_abort = 0;
  int r = solve_vertex(0);
  if (s_abort) return 0;
  if (r) { if (rebuild_and_check(n, adj, b)) nwitness_ok++; else { nwitness_bad++; fprintf(stderr, "WITNESS FAILURE\n"); } }
  return r;
}

/* ------------------------------------------------------------------ connectivity, blocks */
static uint32_t comp_of(const uint32_t *adj, uint32_t verts, int s) {
  uint32_t c = 1u << s, fr = c;
  while (fr) { int y = __builtin_ctz(fr); fr &= fr - 1; uint32_t nb = adj[y] & verts & ~c; c |= nb; fr |= nb; }
  return c;
}
/* 2-connected (>= 3 vertices, connected, no cut vertex) on the vertex set verts */
static int twoconn(const uint32_t *adj, uint32_t verts) {
  if (popc(verts) < 3) return 0;
  if (comp_of(adj, verts, __builtin_ctz(verts)) != verts) return 0;
  for (uint32_t v = verts; v; v &= v - 1) {
    int x = __builtin_ctz(v);
    uint32_t rest = verts & ~(1u << x);
    if (comp_of(adj, rest, __builtin_ctz(rest)) != rest) return 0;
  }
  return 1;
}

static int bN, nblk, blk_of_edge[MAXE];
static uint32_t blkV[MAXE];
static int bm, beu[MAXE], bev[MAXE];
static uint32_t badj[MAXN];
static int ncut_inc, inc_blk[4 * MAXE], inc_v[4 * MAXE];
static int iscut[MAXN];
static int bt[MAXN];
static int bval[MAXE][MAXN];

static int ufb[MAXE];
static int ufb_find(int e) { while (ufb[e] != e) e = ufb[e]; return e; }

static void blocks(int n, const uint32_t *adj) {
  bN = n; bm = 0;
  memcpy(badj, adj, sizeof(uint32_t) * MAXN);
  for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (adj[x] >> y & 1) { beu[bm] = x; bev[bm] = y; bm++; }
  uint32_t nonIso = 0;
  for (int x = 0; x < n; x++) if (adj[x]) nonIso |= 1u << x;
  /* component labels of G - x */
  static int lab[MAXN][MAXN];
  for (int x = 0; x < n; x++) {
    uint32_t rest = nonIso & ~(1u << x), done = 0;
    int L = 0;
    for (uint32_t v = rest; v; v &= v - 1) {
      int y = __builtin_ctz(v);
      if (done >> y & 1) continue;
      uint32_t c = comp_of(adj, rest, y);
      for (uint32_t w = c; w; w &= w - 1) lab[x][__builtin_ctz(w)] = L;
      done |= c; L++;
    }
  }
  for (int e = 0; e < bm; e++) ufb[e] = e;
  for (int e = 0; e < bm; e++)
    for (int f = e + 1; f < bm; f++) {
      int same = 1;
      for (int x = 0; x < n && same; x++) {
        if (!(nonIso >> x & 1)) continue;
        int re = beu[e] != x ? beu[e] : bev[e];
        int rf = beu[f] != x ? beu[f] : bev[f];
        if (lab[x][re] != lab[x][rf]) same = 0;
      }
      if (same) { int a = ufb_find(e), c = ufb_find(f); if (a != c) ufb[c] = a; }
    }
  int map[MAXE];
  for (int e = 0; e < bm; e++) map[e] = -1;
  nblk = 0;
  for (int e = 0; e < bm; e++) {
    int r = ufb_find(e);
    if (map[r] < 0) { map[r] = nblk; blkV[nblk] = 0; nblk++; }
    blk_of_edge[e] = map[r];
    blkV[map[r]] |= (1u << beu[e]) | (1u << bev[e]);
  }
  for (int x = 0; x < n; x++) {
    int c = 0;
    for (int B = 0; B < nblk; B++) if (blkV[B] >> x & 1) c++;
    iscut[x] = c >= 2;
  }
}
static int dB(int B, int x) { /* degree of x inside block B */
  int d = 0;
  for (int e = 0; e < bm; e++) if (blk_of_edge[e] == B && (beu[e] == x || bev[e] == x)) d++;
  return d;
}
static int blkdeg[MAXE][MAXN];

static int bc_block_ok(int B) {
  uint32_t V = blkV[B];
  int sz = popc(V);
  if (sz == 2) {
    for (uint32_t v = V; v; v &= v - 1) if (bval[B][__builtin_ctz(v)] != 1) return 0;
    return 1;
  }
  int S = 0, z = 0;
  for (uint32_t v = V; v; v &= v - 1) { int x = __builtin_ctz(v); S += bval[B][x]; if (bval[B][x] == 0) z++; }
  if (z > 2) return 0;
  for (uint32_t v = V; v; v &= v - 1) { int x = __builtin_ctz(v); if (blkdeg[B][x] + bval[B][x] > S) return 0; }
  return 1;
}
static int bc_glue_ok(int c) {
  int M = 0, mx = 0;
  for (int B = 0; B < nblk; B++) if (blkV[B] >> c & 1) { M += bval[B][c]; if (bval[B][c] > mx) mx = bval[B][c]; }
  return M >= bt[c] && 2 * mx <= M + bt[c];
}
static int bc_rec(int i) {
  if (i == ncut_inc) {
    for (int B = 0; B < nblk; B++) if (!bc_block_ok(B)) return 0;
    for (int c = 0; c < bN; c++) if (iscut[c] && !bc_glue_ok(c)) return 0;
    return 1;
  }
  int B = inc_blk[i], c = inc_v[i], d = blkdeg[B][c];
  for (int v = d & 1; v <= d; v += 2) { bval[B][c] = v; if (bc_rec(i + 1)) return 1; }
  return 0;
}
/* BC for (G, t), t == d mod 2 assumed */
static int BC(int n, const uint32_t *adj, const int *t) {
  blocks(n, adj);
  for (int B = 0; B < nblk; B++) for (int x = 0; x < n; x++) blkdeg[B][x] = (blkV[B] >> x & 1) ? dB(B, x) : 0;
  for (int x = 0; x < n; x++) bt[x] = t[x];
  for (int x = 0; x < n; x++) if (!adj[x] && t[x] != 0) return 0;
  ncut_inc = 0;
  for (int B = 0; B < nblk; B++)
    for (int x = 0; x < n; x++) {
      if (!(blkV[B] >> x & 1)) continue;
      if (iscut[x]) { inc_blk[ncut_inc] = B; inc_v[ncut_inc] = x; ncut_inc++; }
      else bval[B][x] = t[x];
    }
  return bc_rec(0);
}

/* ------------------------------------------------------------------ modes */
static int n;
static uint32_t adj[MAXN];
static int deg[MAXN];
static int g_w = 0;    /* 1: print witness lines "W g6 paths..." (for testing the repository's checkers) */
static void print_paths(void) { for (int p = 0; p < wnp; p++) { putchar(' '); for (int j = 0; j < wlen[p]; j++) printf(j ? "-%d" : "%d", wpath[p][j]); } }
static int g_db = 0;   /* 1: use the proved (DB) as a pre-check (Lemma 2.2, Lean degree_add_le_sum_of_realises) */

static void mode_census(void) {
  char line[256];
  long ng = 0, two = 0, tight = 0, o1 = 0, o1tight = 0, c2 = 0, c2nt = 0, c2nt_nonO1 = 0, cutnt = 0;
  long bc_t = 0, bc_tn = 0, bc_nt = 0, bc_ntn = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0;
    if (!line[0] || !decode_g6(line, &n, adj)) continue;
    ng++;
    int ne = 0, t[MAXN];
    for (int x = 0; x < n; x++) { deg[x] = popc(adj[x]); t[x] = deg[x] & 1; if (deg[x] > 0 && !(deg[x] & 1)) ne++; }
    if (ne != 2) continue;
    two++;
    int isO1 = 0;
    for (int x = 0; x < n; x++) if ((deg[x] & 1) && deg[x] == n - 1) isO1 = 1;
    int r = realisable(n, adj, t, g_db);
    int is2c = twoconn(adj, (1u << n) - 1);
    int bc = BC(n, adj, t);
    if (r && g_w) { printf("W %s", line); print_paths(); printf("\n"); }
    tight += r; o1 += isO1; if (isO1 && r) o1tight++;
    if (is2c) { c2++; if (!r) { c2nt++; if (!isO1) { c2nt_nonO1++; printf("NONTIGHT-2CONN-NONO1 %s\n", line); } } }
    else if (!r && !isO1) cutnt++;
    if (r && bc) bc_t++; else if (r && !bc) { bc_tn++; printf("DISAGREE tight-notBC %s\n", line); }
    else if (!r && bc) { bc_nt++; printf("DISAGREE nottight-BC %s\n", line); } else bc_ntn++;
  }
  printf("graphs %ld two-even %ld tight %ld nottight %ld | O1 %ld (O1 tight %ld) | 2-conn %ld 2-conn-nottight %ld 2-conn-nottight-nonO1 %ld | cut-nonO1-nottight %ld\n",
         ng, two, tight, two - tight, o1, o1tight, c2, c2nt, c2nt_nonO1, cutnt);
  if (g_limit) printf("node limit %ld: undecided solves %ld (counted as not tight above)\n", g_limit, nundecided);
  printf("BC: tight&BC %ld tight&notBC %ld nottight&BC %ld nottight&notBC %ld\n", bc_t, bc_tn, bc_nt, bc_ntn);
  printf("witnesses rebuilt and checked %ld, bad %ld\n", nwitness_ok, nwitness_bad);
}

/* PC: every zero set Z of size maxz (positive even degree), every profile */
static int pz[MAXN], pb[MAXN];
static char g6line[256];
static long np, ndb, nreal, ndb_nr, nr_ndb, ndbf_char_bad;
static void pc_rec(int x) {
  if (x == n) {
    int S = 0;
    for (int i = 0; i < n; i++) S += pb[i];
    int db = 1, fail_at = -1;
    for (int i = 0; i < n; i++) if (deg[i] + pb[i] > S) { db = 0; fail_at = i; }
    np++;
    /* Lemma DBfail characterisation: DB fails at x iff |Z| = 2, x ~ all, b = 1 off Z + x */
    for (int xx = 0; xx < n; xx++) {
      int fails = deg[xx] + pb[xx] > S;
      int zc = 0; for (int i = 0; i < n; i++) zc += pz[i];
      int ch = (zc == 2) && !pz[xx] && popc(adj[xx]) == n - 1;
      for (int i = 0; i < n && ch; i++) if (i != xx && !pz[i] && pb[i] != 1) ch = 0;
      if (fails != ch) ndbf_char_bad++;
    }
    (void)fail_at;
    int r = (g_db && !db) ? 0 : realisable(n, adj, pb, 0);
    if (db) ndb++;
    if (r) nreal++;
    if (r && g_w) { printf("W %s", g6line); print_paths(); printf(" b="); for (int i = 0; i < n; i++) printf(i ? ",%d" : "%d", pb[i]); printf("\n"); }
    if (db && !r) { ndb_nr++; printf("DB-NOT-REALISABLE\n"); }
    if (!db && r) nr_ndb++;
    return;
  }
  if (pz[x]) { pb[x] = 0; pc_rec(x + 1); return; }
  for (int v = (deg[x] & 1) ? 1 : 2; v <= deg[x]; v += 2) { pb[x] = v; pc_rec(x + 1); }
}
static void mode_pc(int maxz) {
  char *line = g6line;
  long ng = 0;
  while (fgets(line, sizeof g6line, stdin)) {
    line[strcspn(line, "\r\n")] = 0;
    if (!line[0] || !decode_g6(line, &n, adj)) continue;
    ng++;
    int ev[MAXN], ne = 0;
    for (int x = 0; x < n; x++) { deg[x] = popc(adj[x]); if (deg[x] > 0 && !(deg[x] & 1)) ev[ne++] = x; }
    memset(pz, 0, sizeof pz);
    if (maxz == 0) pc_rec(0);
    else if (maxz == 1) for (int i = 0; i < ne; i++) { memset(pz, 0, sizeof pz); pz[ev[i]] = 1; pc_rec(0); }
    else for (int i = 0; i < ne; i++) for (int j = i + 1; j < ne; j++) { memset(pz, 0, sizeof pz); pz[ev[i]] = pz[ev[j]] = 1; pc_rec(0); }
  }
  printf("Z=%d graphs %ld profiles %ld with-DB %ld realisable %ld DB-not-realisable %ld realisable-not-DB %ld DBfail-characterisation-mismatches %ld\n",
         maxz, ng, np, ndb, nreal, ndb_nr, nr_ndb, ndbf_char_bad);
  printf("witnesses rebuilt and checked %ld, bad %ld\n", nwitness_ok, nwitness_bad);
}

/* Conjecture J */
static int c1, c2, a1, a2, path[MAXN + 1], plen;
static int anyL, anyC, any2c, anyB, anyBCany, firstType, haveFirst, certP[MAXN + 1], certLen, certType;
static uint32_t K0[MAXN];
static long npaths_total, nall_solved, nall_bad;
static int g_all = 0;  /* 1: solve K0 exactly for every joint path with (L) or BC, not only the best one */
static int g_fast = 0, jpass = 0, jstop = 0;  /* fast: pass 0 looks for (L)/(C) only, pass 1 for BC; stop at the first */
static void j_test_fast(void) {
  npaths_total++;
  memcpy(K0, adj, sizeof K0);
  for (int i = 0; i + 1 < plen; i++) { int x = path[i], y = path[i + 1]; K0[x] &= ~(1u << y); K0[y] &= ~(1u << x); }
  int isL = !K0[c1] || !K0[c2];
  int type = -1;
  if (isL) type = 0;
  else if (jpass == 0) {
    uint32_t verts = 0;
    for (int x = 0; x < n; x++) if (K0[x]) verts |= 1u << x;
    int n0 = popc(verts), univ = 0;
    for (int x = 0; x < n; x++) { int d = popc(K0[x]); if ((d & 1) && d == n0 - 1) univ = 1; }
    if (!univ && twoconn(K0, verts)) type = 1;
  } else {
    int t[MAXN];
    for (int x = 0; x < n; x++) t[x] = popc(K0[x]) & 1;
    if (BC(n, K0, t)) type = 2;
  }
  if (type >= 0) { jstop = 1; certType = type; certLen = plen; memcpy(certP, path, sizeof(int) * plen); }
}
static void j_test(void) {
  if (g_fast) { j_test_fast(); return; }
  npaths_total++;
  memcpy(K0, adj, sizeof K0);
  for (int i = 0; i + 1 < plen; i++) { int x = path[i], y = path[i + 1]; K0[x] &= ~(1u << y); K0[y] &= ~(1u << x); }
  int isL = !K0[c1] || !K0[c2];
  uint32_t verts = 0;
  for (int x = 0; x < n; x++) if (K0[x]) verts |= 1u << x;
  int n0 = popc(verts);
  int t[MAXN];
  for (int x = 0; x < n; x++) t[x] = popc(K0[x]) & 1;
  int tc = twoconn(K0, verts);
  int univ = 0;
  for (int x = 0; x < n; x++) { int d = popc(K0[x]); if ((d & 1) && d == n0 - 1) univ = 1; }
  int isC = !isL && tc && !univ;
  int bc = BC(n, K0, t);
  if (isL) anyL = 1;
  if (isC) anyC = 1;
  if (!isL && tc) any2c = 1;
  if (!isL && !isC && bc) anyB = 1;
  if (bc) anyBCany = 1;
  if (g_all && (isL || bc)) {
    int tt[MAXN]; for (int x = 0; x < n; x++) tt[x] = popc(K0[x]) & 1;
    uint32_t KK[MAXN]; memcpy(KK, K0, sizeof KK);
    nall_solved++;
    if (!realisable(n, KK, tt, 0)) { nall_bad++; printf("L-OR-BC-PATH-NOT-TIGHT\n"); }
  }
  if (!haveFirst && (isL || isC)) { haveFirst = 1; firstType = isL ? 0 : 1; }
  int type = isL ? 0 : isC ? 1 : bc ? 2 : -1;
  if (type >= 0 && (certType < 0 || type < certType)) { certType = type; certLen = plen; memcpy(certP, path, sizeof(int) * plen); }
}
static void j_dfs(int x, uint32_t vis) {
  if (jstop) return;
  if (x == c2) { j_test(); return; }
  uint32_t nb = adj[x] & ~vis & ~((1u << a1) | (1u << a2));
  while (nb) {
    int y = __builtin_ctz(nb); nb &= nb - 1;
    path[plen++] = y; j_dfs(y, vis | (1u << y)); plen--;
  }
}
static void mode_j(void) {
  char line[256];
  long ng = 0, ninst = 0, njoined = 0, nLC = 0, nBonly = 0, nnone = 0, nanyL = 0, nC_noL = 0, nL2c = 0;
  long nfirstL = 0, nfirstC = 0, nBCany = 0, ntight_ok = 0, ntight_bad = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0;
    if (!line[0] || !decode_g6(line, &n, adj)) continue;
    int allodd = 1;
    for (int x = 0; x < n; x++) { deg[x] = popc(adj[x]); if (!(deg[x] & 1)) allodd = 0; }
    if (!allodd) continue;
    ng++;
    for (c1 = 0; c1 < n; c1++) for (c2 = c1 + 1; c2 < n; c2++)
      for (a1 = 0; a1 < n; a1++) for (a2 = 0; a2 < n; a2++) {
        if (a1 == c1 || a1 == c2 || a2 == c1 || a2 == c2 || a1 == a2) continue;
        if ((adj[c1] >> a1 & 1) || (adj[c2] >> a2 & 1)) continue;
        ninst++;
        uint32_t rest = ((1u << n) - 1) & ~((1u << a1) | (1u << a2));
        if (!(comp_of(adj, rest, c1) >> c2 & 1)) continue;
        njoined++;
        anyL = anyC = any2c = anyB = anyBCany = haveFirst = 0; firstType = -1; certType = -1;
        plen = 0; path[plen++] = c1;
        jstop = 0; jpass = 0;
        j_dfs(c1, 1u << c1);
        if (g_fast) {
          if (certType == 0) anyL = 1; else if (certType == 1) anyC = 1;
          if (!jstop) { jpass = 1; plen = 1; j_dfs(c1, 1u << c1); if (jstop) anyB = 1; }
          if (jstop) { haveFirst = (certType <= 1); firstType = certType; anyBCany = 1; }
        }
        if (anyL) nanyL++;
        if (anyL || anyC) nLC++;
        else if (anyB) nBonly++;
        else { nnone++; printf("NONE %s %d %d %d %d\n", line, c1, a1, c2, a2); }
        if (!anyL && anyC) nC_noL++;
        if (anyL || any2c) nL2c++;
        if (haveFirst) { if (firstType == 0) nfirstL++; else nfirstC++; }
        if (anyBCany) nBCany++;
        if (certType >= 0) {
          uint32_t K[MAXN]; memcpy(K, adj, sizeof K);
          for (int i = 0; i + 1 < certLen; i++) { int x = certP[i], y = certP[i + 1]; K[x] &= ~(1u << y); K[y] &= ~(1u << x); }
          int t[MAXN]; for (int x = 0; x < n; x++) t[x] = popc(K[x]) & 1;
          if (realisable(n, K, t, g_db)) { ntight_ok++; if (g_w) { printf("W %s ", line); for (int i = 0; i < certLen; i++) printf(i ? "-%d" : "%d", certP[i]); print_paths(); printf(" J=%d,%d,%d,%d\n", c1, a1, c2, a2); } } else { ntight_bad++; printf("CERT-NOT-TIGHT %s\n", line); }
        }
      }
  }
  printf("all-odd graphs %ld instances %ld joined %ld\n", ng, ninst, njoined);
  printf("(L)or(C) %ld  (B)only %ld  none %ld   [some (L) path %ld; (C) but no (L) %ld]\n", nLC, nBonly, nnone, nanyL, nC_noL);
  printf("DFS-first (L)/(C) split: (L) %ld (C) %ld\n", nfirstL, nfirstC);
  printf("instances with some joint path whose K0 is (L) or 2-connected (universal vertex allowed): %ld\n", nL2c);
  printf("instances with some joint path whose K0 satisfies BC (incl. (L) paths): %ld\n", nBCany);
  printf("best certified K0 solved exactly: tight %ld not tight %ld; joint paths examined %ld\n", ntight_ok, ntight_bad, npaths_total);
  if (g_all) printf("all (L)/BC joint paths solved exactly: %ld, not tight %ld\n", nall_solved, nall_bad);
  printf("witnesses rebuilt and checked %ld, bad %ld\n", nwitness_ok, nwitness_bad);
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: a43 census|pc MAXZ|j [db] < g6\n"); return 1; }
  for (int i = 2; i < argc; i++) { if (!strcmp(argv[i], "db")) g_db = 1; if (!strcmp(argv[i], "w")) g_w = 1; if (!strcmp(argv[i], "all")) g_all = 1; if (!strcmp(argv[i], "fast")) g_fast = 1; if (!strncmp(argv[i], "limit=", 6)) g_limit = atol(argv[i] + 6); }
  if (!strcmp(argv[1], "census")) mode_census();
  else if (!strcmp(argv[1], "pc")) mode_pc(argc > 2 ? atoi(argv[2]) : 2);
  else if (!strcmp(argv[1], "j")) mode_j();
  return 0;
}
