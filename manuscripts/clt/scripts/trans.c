/* trans.c: search for unsatisfiable constraint systems of a given shape (session claude/clt).

   Input: output of `enum -v L` (per graph the inclusion-minimal violation sets of all Lovász
   decompositions over the atoms av(c,a) [path ending at c avoids a] and ne(u,v) [paths ending at
   u and v differ]).  A system X of atoms is unsatisfiable iff X meets every violation set, so we
   search for a hitting set X of the family obeying a shape predicate, by the standard branching
   (pick an unhit member with fewest admissible atoms, branch on them), with iterative deepening
   on |X| so that the first system found has minimum size.

   Usage: trans SHAPE K [ne] < input
     SHAPE (constraints on the arc digraph of the av atoms of X; a vertex may be both tail and
     head unless stated):
       any    no condition
       in1    every vertex is avoided by at most one end path (in-degree <= 1)
       func   in-degree <= 1 and out-degree <= 1
       lin    func and acyclic (a disjoint union of directed paths)
       match  every vertex lies in at most one atom (L_N shape)
       out1   out-degree <= 1
       star   all atoms have the same tail (single-vertex constraint, L1* shape)
     K      maximum |X|
     ne     also allow ne atoms (each ne atom counts as an arc in both directions for the shape
            test is NOT done: ne atoms are unrestricted except by K)
   Output per graph with a hit: "H graph6 size atoms..."; final line: counts. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXA 256
#define MAXF 200000
#define W 4000  /* family words: up to 256000 members */
typedef uint64_t u64;

static int n;
static int na; static int at_t[MAXA], at_x[MAXA], at_y[MAXA];
static int nf; static int *fam_atoms[MAXF]; static int fam_len[MAXF];
static int shape, K, allow_ne, tdeg = 0, hdeg = 0, gdeg = 0;
static int degv[16]; static int distv[16][16];
static int indeg[16], outdeg[16], touched[16], netouch[16];
static int ne_tails = 0;  /* ne atoms only between vertices that are not heads */
static int X[64], nx;
static unsigned long long nodes;

static int atom_id(int t, int x, int y) {
  for (int i = 0; i < na; i++) if (at_t[i] == t && at_x[i] == x && at_y[i] == y) return i;
  at_t[na] = t; at_x[na] = x; at_y[na] = y; return na++;
}

/* is there a directed path from s to t among av atoms of X? */
static int reach(int s, int t) {
  int seen = 1 << s, fr = 1 << s;
  while (fr) {
    int v = __builtin_ctz(fr); fr &= fr - 1;
    for (int i = 0; i < nx; i++) { int a = X[i]; if (at_t[a] != 0 || at_x[a] != v) continue;
      int y = at_y[a]; if (y == t) return 1; if (!(seen >> y & 1)) { seen |= 1 << y; fr |= 1 << y; } }
  }
  return 0;
}

static int ok_add(int a) {
  if (at_t[a] == 1) { if (!allow_ne) return 0; if (ne_tails && (indeg[at_x[a]] || indeg[at_y[a]])) return 0; return 1; }
  if (ne_tails && netouch[at_y[a]]) return 0;
  int c = at_x[a], y = at_y[a];
  switch (shape) {
    case 0: return 1;
    case 1: return indeg[y] == 0;
    case 2: return indeg[y] == 0 && outdeg[c] == 0;
    case 3: return indeg[y] == 0 && outdeg[c] == 0 && !reach(y, c);
    case 4: return !touched[c] && !touched[y];
    case 5: return outdeg[c] == 0;
    case 6: for (int i = 0; i < nx; i++) if (at_t[X[i]] == 0 && at_x[X[i]] != c) return 0; return 1;
    case 13: /* in-degree <= 1; every directed 2-path x->y->z is a 2-cycle (z = x) at distance >= 3 */
      if (indeg[y] > 0) return 0;
      for (int i = 0; i < nx; i++) { int a2 = X[i]; if (at_t[a2]) continue;
        int p = at_x[a2], q = at_y[a2];
        if (p == y && !(q == c && distv[c][y] >= 3)) return 0;   /* c -> y -> q */
        if (q == c && !(p == y && distv[c][y] >= 3)) return 0; } /* p -> c -> y */
      return 1;
    case 12: /* bipartite (no tail is a head), in-degree <= 1, no cross-locality */
      return indeg[c] == 0 && outdeg[y] == 0 && indeg[y] == 0;
    case 11: if (indeg[y] > 0) return 0;  /* bip with in-degree <= 1 */
      /* fall through */
    case 10: /* bipartite multi-star with cross-locality: tails never heads, heads outside N[tails] */
      if (indeg[c] > 0 || outdeg[y] > 0) return 0;
      if (distv[c][y] <= 1) return 0;
      for (int i = 0; i < nx; i++) { int a2 = X[i]; if (at_t[a2]) continue;
        if (distv[at_x[a2]][y] <= 1) return 0;      /* new head next to an old tail */
        if (distv[c][at_y[a2]] <= 1) return 0; }    /* old head next to the new tail */
      return 1;
    case 7: return !touched[c] && !touched[y];
    case 8: return touched[c] < 2 && touched[y] < 2;
    case 9: { /* components of the pair graph X + cy must be packed: every two vertices of the new
                 component at distance >= 3 */
      int comp = (1 << c) | (1 << y), grow = 1;
      while (grow) { grow = 0; for (int i = 0; i < nx; i++) { int a2 = X[i]; int p = at_x[a2], q = at_y[a2];
        if (((comp >> p) & 1) != ((comp >> q) & 1)) { comp |= (1 << p) | (1 << q); grow = 1; } } }
      for (int p = 0; p < n; p++) if (comp >> p & 1) for (int q = p + 1; q < n; q++) if (comp >> q & 1) if (distv[p][q] < 3) return 0;
      return 1; }
  }
  return 0;
}
static void push(int a) { X[nx++] = a; if (at_t[a] == 1) { netouch[at_x[a]]++; netouch[at_y[a]]++; } if (at_t[a] == 0) { indeg[at_y[a]]++; outdeg[at_x[a]]++; touched[at_x[a]]++; touched[at_y[a]]++; } }
static void pop(void) { int a = X[--nx]; if (at_t[a] == 1) { netouch[at_x[a]]--; netouch[at_y[a]]--; } if (at_t[a] == 0) { indeg[at_y[a]]--; outdeg[at_x[a]]--; touched[at_x[a]]--; touched[at_y[a]]--; } }

static uint8_t inX[MAXA];
static int hit(int f) { for (int j = 0; j < fam_len[f]; j++) if (inX[fam_atoms[f][j]]) return 1; return 0; }

static int dfs(int depth) {
  nodes++;
  /* find an unhit member with fewest admissible atoms */
  int best = -1, bc = 1 << 30;
  for (int f = 0; f < nf; f++) {
    if (hit(f)) continue;
    int cnt = 0;
    for (int j = 0; j < fam_len[f]; j++) if (ok_add(fam_atoms[f][j])) cnt++;
    if (cnt < bc) { bc = cnt; best = f; if (cnt == 0) break; }
  }
  if (best < 0) return 1;          /* every member hit: unsatisfiable system found */
  if (depth == 0 || bc == 0) return 0;
  for (int j = 0; j < fam_len[best]; j++) {
    int a = fam_atoms[best][j];
    if (!ok_add(a)) continue;
    push(a); inX[a] = 1;
    if (dfs(depth - 1)) return 1;
    pop(); inX[a] = 0;
  }
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: trans SHAPE K [ne]\n"); return 1; }
  const char *names[] = {"any", "in1", "func", "lin", "match", "out1", "star", "pmatch", "pdeg2", "comp", "bip", "bip1", "bipx", "bipx2"};
  shape = -1; for (int i = 0; i < 14; i++) if (!strcmp(argv[1], names[i])) shape = i;
  if (shape < 0) { fprintf(stderr, "bad shape\n"); return 1; }
  K = atoi(argv[2]);
  for (int i = 3; i < argc; i++) {
    if (!strcmp(argv[i], "ne")) allow_ne = 1;
    else if (!strcmp(argv[i], "net")) allow_ne = 1, ne_tails = 1;
    else if (!strncmp(argv[i], "tdeg=", 5)) tdeg = atoi(argv[i] + 5);   /* tails of degree >= tdeg */
    else if (!strncmp(argv[i], "hdeg=", 5)) hdeg = atoi(argv[i] + 5);   /* heads of degree >= hdeg */
    else if (!strncmp(argv[i], "gdeg=", 5)) gdeg = atoi(argv[i] + 5);   /* skip graphs whose even vertex has degree < gdeg */
  }
  static char line[1 << 16], g6[256];
  long ngraphs = 0, nhit = 0, hist[65] = {0};
  int have = 0, skipg = 0;
  int tmp[MAXA];
  for (;;) {
    char *r = fgets(line, sizeof line, stdin);
    if (!r || line[0] == 'G') {
      if (have) {
        ngraphs++;
        memset(indeg, 0, sizeof indeg); memset(outdeg, 0, sizeof outdeg); memset(touched, 0, sizeof touched); memset(netouch, 0, sizeof netouch);
        memset(inX, 0, sizeof inX); nx = 0;
        int found = 0;
        if (nf == 0) { printf("H %s NODECOMP\n", g6); found = 1; }
        else for (int k = 1; k <= K && !found; k++) {
          if (dfs(k)) {
            found = 1; hist[nx]++;
            printf("H %s %d", g6, nx);
            for (int i = 0; i < nx; i++) printf(" %c%d,%d", at_t[X[i]] ? 'n' : (shape >= 7 && shape <= 9 ? 's' : 'a'), at_x[X[i]], at_y[X[i]]);
            printf("\n");
          }
        }
        if (found) nhit++;
        for (int f = 0; f < nf; f++) free(fam_atoms[f]);
        nf = 0; na = 0;
      }
      if (!r) break;
      sscanf(line, "G %255s", g6); n = g6[0] - 63; have = 1;
      { memset(degv, 0, sizeof degv); int pos = 1, bit = 5;
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) distv[i][j] = i == j ? 0 : 99;
        for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) { int v = g6[pos] - 63; if ((v >> bit) & 1) { degv[i]++; degv[j]++; distv[i][j] = distv[j][i] = 1; } if (--bit < 0) { bit = 5; pos++; } }
        for (int k2 = 0; k2 < n; k2++) for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (distv[i][k2] + distv[k2][j] < distv[i][j]) distv[i][j] = distv[i][k2] + distv[k2][j]; }
      { int ge = -1; for (int v = 0; v < n; v++) if (degv[v] > 0 && !(degv[v] & 1)) ge = v; if (ge >= 0 && degv[ge] < gdeg) have = 0, skipg = 1; else skipg = 0; }
      continue;
    }
    if (line[0] != 'V' || skipg) continue;
    int len = 0; char *p = line + 1;
    for (;;) {
      while (*p == ' ') p++;
      if (*p != 'a' && *p != 'n' && *p != 's') break;
      int t = *p == 'n'; int x, y, c; p++;
      if (sscanf(p, "%d,%d%n", &x, &y, &c) != 2) break;
      p += c;
      if (t == 1 && !allow_ne) continue;
      if (t == 0 && (degv[x] < tdeg || degv[y] < hdeg)) continue;
      tmp[len++] = atom_id(t, x, y);
    }
    if (nf >= MAXF) { fprintf(stderr, "family too large\n"); return 1; }
    fam_atoms[nf] = malloc(len * sizeof(int) + 1); memcpy(fam_atoms[nf], tmp, len * sizeof(int)); fam_len[nf] = len; nf++;
  }
  printf("graphs %ld  with an unsatisfiable %s system of size <= %d: %ld   by size:", ngraphs, names[shape], K, nhit);
  for (int k = 1; k <= K; k++) if (hist[k]) printf(" %d:%ld", k, hist[k]);
  printf("   nodes %llu\n", nodes);
  return 0;
}
