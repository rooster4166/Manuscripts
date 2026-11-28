/* allodd_dl.c -- exact test of disjunctive / fixed avoidance in graphs with no even vertex
   (test2 session).

   For every connected graph G on stdin (graph6, n <= 12) whose degrees are all odd, a Lovasz
   decomposition is a decomposition into n/2 paths with exactly one end at every vertex; Q(c) is
   the path ending at c.  For a non-adjacent ordered pair (c, x) write [c|x] for "x not in Q(c)".
   Constraint families (all vertices involved distinct, all pairs non-adjacent):
     F2  two free pairs   ([a|b] or [b|a]) and ([c|d] or [d|c])        (all-odd DL(2))
     F3  three free pairs                                                (all-odd DL(3))
     X2  two fixed        [a|b] and [c|d]
     X3  three fixed
     XF  one fixed + one free     [c|x] and ([a|b] or [b|a])             (Conjecture 7.2)
     XF2 one fixed + two free                                            (the d(z)=6 matching base)
   The program enumerates the Lovasz decompositions by depth-first search (lowest unended vertex
   is an end; branch over all paths from it to an unended vertex; prune by the parity of the
   remaining degrees), records for each decomposition the set of satisfied [c|x], and strikes the
   constraint sets it satisfies.  It stops when every set is struck; a set left after the whole
   enumeration is a genuine failure and is printed.  A node budget (-b) makes the answer
   "undecided" for the sets left.
   Output: FAIL lines, UNDEC lines, and a summary per family on stderr.
   Phase 1 (randomised dives, -d of them) only finds decompositions; every set still standing is
   then decided by a targeted exact search that prunes as soon as one of its clauses is violated,
   so the randomisation affects the running time only, never the answer.
   usage: ./allodd_dl [-b budget] [-f families] [-d dives] < graph6      (families: subset of "23xyuv",
          2=F2 3=F3 x=X2 y=X3 u=XF v=XF2; default all)
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef unsigned __int128 u128;
#define MAXN 12
#define MAXM 66
static int n, m;
static int eu[MAXM], ev[MAXM];
static int adjv[MAXN][MAXN], adje[MAXN][MAXN], adeg[MAXN];
static uint64_t inc[MAXN];
static int A[MAXN];  /* adjacency bitmask */

static int read_g6(const char *s) {
    const unsigned char *p = (const unsigned char *)s;
    n = p[0] - 63;
    if (n < 1 || n > MAXN) return 0;
    p++;
    int bit = 0, cur = 0, k = 0;
    m = 0;
    for (int v = 0; v < n; v++) { adeg[v] = 0; inc[v] = 0; A[v] = 0; }
    for (int j = 1; j < n; j++)
        for (int i = 0; i < j; i++) {
            if (bit == 0) { cur = p[k++] - 63; bit = 6; }
            bit--;
            if (cur >> bit & 1) {
                eu[m] = i; ev[m] = j;
                adjv[i][adeg[i]] = j; adje[i][adeg[i]++] = m;
                adjv[j][adeg[j]] = i; adje[j][adeg[j]++] = m;
                inc[i] |= 1ULL << m; inc[j] |= 1ULL << m;
                A[i] |= 1 << j; A[j] |= 1 << i;
                m++;
            }
        }
    return 1;
}

static inline u128 B(int c, int x) { return ((u128)1) << (c * MAXN + x); }

/* constraint sets: up to 3 clauses; clause = OR-mask */
typedef struct { u128 cl[3]; int k; int fam; signed char v[6]; } cset;
static cset *sets; static int nsets, capsets;
static void add_set(int fam, int k, const u128 *cl, const int *verts, int nv) {
    if (nsets == capsets) { capsets = capsets ? 2 * capsets : 4096; sets = realloc(sets, capsets * sizeof(cset)); }
    cset *s = &sets[nsets++];
    s->k = k; s->fam = fam;
    for (int i = 0; i < k; i++) s->cl[i] = cl[i];
    for (int i = 0; i < 6; i++) s->v[i] = i < nv ? verts[i] : -1;
}

static long long nodes, budget;
static int aborted, ndec;
static long long phase1cap = 300;
static cset *target = NULL;        /* phase 2: the set the search must satisfy */
static int endS[MAXN];             /* vertex set of Q(c) once chosen, else -1 */
static int stopflag;               /* phase 1: stop after phase1cap decompositions */
static int ndives = 2000;
static uint64_t rngstate = 88172645463325252ULL;
static uint64_t rng(void) { rngstate ^= rngstate << 13; rngstate ^= rngstate >> 7; rngstate ^= rngstate << 17; return rngstate; }
static int ended;
static int pathsv[MAXN], pathsu[MAXN], pathsS[MAXN], np;

/* does the partial assignment already violate a clause of the target? */
static int target_violated(void) {
    if (!target) return 0;
    for (int j = 0; j < target->k; j++) {
        int all_viol = 1;
        for (int c = 0; c < n && all_viol; c++) {
            if (endS[c] < 0) {
                /* any condition with this c keeps the clause alive */
                for (int x = 0; x < n; x++) if (target->cl[j] & B(c, x)) { all_viol = 0; break; }
            } else {
                for (int x = 0; x < n; x++) if ((target->cl[j] & B(c, x)) && !(endS[c] >> x & 1)) { all_viol = 0; break; }
            }
        }
        if (all_viol) return 1;
    }
    return 0;
}

static void record(void) {
    u128 sat = 0;
    for (int i = 0; i < np; i++) {
        int S = pathsS[i];
        int ends[2] = {pathsu[i], pathsv[i]};
        for (int e = 0; e < 2; e++) {
            int c = ends[e];
            for (int x = 0; x < n; x++) if (!(S >> x & 1)) sat |= B(c, x);
        }
    }
    ndec++;
    for (int i = 0; i < nsets; ) {
        cset *s = &sets[i];
        int ok = 1;
        for (int j = 0; j < s->k; j++) if (!(s->cl[j] & sat)) { ok = 0; break; }
        if (ok) { if (s == target) target = NULL; sets[i] = sets[--nsets]; }
        else i++;
    }
    if (!target && phase1cap && ndec >= phase1cap) stopflag = 1;
}

static int feasible(uint64_t R, int endedm, int remaining_paths) {
    for (int v = 0; v < n; v++) {
        int d = __builtin_popcountll(R & inc[v]);
        if (endedm >> v & 1) { if (d & 1) return 0; }
        else { if (!(d & 1)) return 0; }
    }
    if (__builtin_popcountll(R) > remaining_paths * (n - 1)) return 0;
    return 1;
}

static void dfs(uint64_t R);

static int done_now(void) { return aborted || nsets == 0 || stopflag || (target == NULL && phase1cap == 0); }

static void extend(uint64_t R, int x, int cur, int vmask, uint64_t pm) {
    if (done_now()) return;
    for (int i = 0; i < adeg[cur]; i++) {
        int y = adjv[cur][i], e = adje[cur][i];
        if (!(R >> e & 1) || (vmask >> y & 1)) continue;
        uint64_t pm2 = pm | (1ULL << e);
        int vm2 = vmask | (1 << y);
        /* close the path at y if y is unended */
        if (!(ended >> y & 1)) {
            uint64_t R2 = R & ~pm2;
            int e2 = ended | (1 << x) | (1 << y);
            int rem = n / 2 - np - 1;
            if (feasible(R2, e2, rem)) {
                pathsu[np] = x; pathsv[np] = y; pathsS[np] = vm2; np++;
                endS[x] = vm2; endS[y] = vm2;
                if (!target_violated()) {
                    int save = ended; ended = e2;
                    dfs(R2);
                    ended = save;
                }
                endS[x] = -1; endS[y] = -1;
                np--;
                if (done_now()) return;
            }
        }
        extend(R, x, y, vm2, pm2);
        if (done_now()) return;
    }
}

static void dfs(uint64_t R) {
    if (done_now()) return;
    if (budget && ++nodes > budget) { aborted = 1; return; }
    if (np == n / 2) { if (R == 0) record(); return; }
    int x = -1;
    for (int v = 0; v < n; v++) if (!(ended >> v & 1)) { x = v; break; }
    if (x < 0) return;
    extend(R, x, x, 1 << x, 0);
}

int main(int argc, char **argv) {
    budget = 0;
    const char *fams = "23xyuv";
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-b") && i + 1 < argc) budget = atoll(argv[++i]);
        else if (!strcmp(argv[i], "-f") && i + 1 < argc) fams = argv[++i];
        else if (!strcmp(argv[i], "-d") && i + 1 < argc) ndives = atoi(argv[++i]);
    }
    int use[6] = {0};
    const char *codes = "23xyuv";
    for (int i = 0; i < 6; i++) use[i] = strchr(fams, codes[i]) != NULL;
    const char *names[6] = {"F2", "F3", "X2", "X3", "XF", "XF2"};
    long long tot[6] = {0}, fail[6] = {0}, und[6] = {0};
    long long ngraphs = 0;
    char line[256];
    while (fgets(line, sizeof line, stdin)) {
        line[strcspn(line, "\r\n")] = 0;
        if (!line[0] || !read_g6(line)) continue;
        int odd = 1;
        for (int v = 0; v < n; v++) if (!(adeg[v] & 1)) odd = 0;
        if (!odd) continue;
        /* connected */
        int seen = 1, fr = 1;
        while (fr) { int v = __builtin_ctz(fr); fr &= fr - 1; int nb = A[v] & ~seen; seen |= nb; fr |= nb; }
        if (seen != (1 << n) - 1) continue;
        ngraphs++;
        /* non-adjacent unordered pairs */
        int pa[80], pb[80], npair = 0;
        for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) if (!(A[a] >> b & 1)) { pa[npair] = a; pb[npair] = b; npair++; }
        nsets = 0;
        u128 cl[3]; int vs[6];
        /* free clause of pair i, fixed clause of pair i in orientation o */
        #define FREE(i) (B(pa[i], pb[i]) | B(pb[i], pa[i]))
        #define FIX(i, o) ((o) ? B(pb[i], pa[i]) : B(pa[i], pb[i]))
        #define DISJ(i, j) (pa[i] != pa[j] && pa[i] != pb[j] && pb[i] != pa[j] && pb[i] != pb[j])
        for (int i = 0; i < npair; i++) for (int j = i + 1; j < npair; j++) {
            if (!DISJ(i, j)) continue;
            vs[0] = pa[i]; vs[1] = pb[i]; vs[2] = pa[j]; vs[3] = pb[j];
            if (use[0]) { cl[0] = FREE(i); cl[1] = FREE(j); add_set(0, 2, cl, vs, 4); }
            if (use[2]) for (int o1 = 0; o1 < 2; o1++) for (int o2 = 0; o2 < 2; o2++) {
                cl[0] = FIX(i, o1); cl[1] = FIX(j, o2); add_set(2, 2, cl, vs, 4); }
            if (use[4]) for (int o1 = 0; o1 < 2; o1++) {
                cl[0] = FIX(i, o1); cl[1] = FREE(j); add_set(4, 2, cl, vs, 4);
                cl[0] = FIX(j, o1); cl[1] = FREE(i); add_set(4, 2, cl, vs, 4); }
            for (int k = j + 1; k < npair; k++) {
                if (!DISJ(i, k) || !DISJ(j, k)) continue;
                vs[4] = pa[k]; vs[5] = pb[k];
                if (use[1]) { cl[0] = FREE(i); cl[1] = FREE(j); cl[2] = FREE(k); add_set(1, 3, cl, vs, 6); }
                if (use[3]) for (int o = 0; o < 8; o++) {
                    cl[0] = FIX(i, o & 1); cl[1] = FIX(j, o >> 1 & 1); cl[2] = FIX(k, o >> 2 & 1);
                    add_set(3, 3, cl, vs, 6); }
                if (use[5]) for (int o = 0; o < 2; o++) {
                    int t[3] = {i, j, k};
                    for (int f = 0; f < 3; f++) {
                        cl[0] = FIX(t[f], o); cl[1] = FREE(t[(f + 1) % 3]); cl[2] = FREE(t[(f + 2) % 3]);
                        add_set(5, 3, cl, vs, 6); } }
            }
        }
        for (int i = 0; i < nsets; i++) tot[sets[i].fam]++;
        if (nsets) {
            uint64_t R = (m == 64) ? ~0ULL : ((1ULL << m) - 1);
            for (int v = 0; v < n; v++) endS[v] = -1;
            /* phase 1: randomised dives, one decomposition each (neighbour order shuffled) */
            long long cap = phase1cap;
            ndec = 0;
            for (int dive = 0; dive < ndives && nsets > 0; dive++) {
                for (int v = 0; v < n; v++)
                    for (int i = adeg[v] - 1; i > 0; i--) {
                        int j = (int)(rng() % (unsigned)(i + 1));
                        int t1 = adjv[v][i]; adjv[v][i] = adjv[v][j]; adjv[v][j] = t1;
                        int t2 = adje[v][i]; adje[v][i] = adje[v][j]; adje[v][j] = t2;
                    }
                nodes = 0; aborted = 0; ended = 0; np = 0; stopflag = 0; target = NULL;
                phase1cap = ndec + 1;
                long long b0 = budget; budget = 2000000;
                dfs(R);
                budget = b0;
            }
            /* phase 2: one targeted search per remaining set */
            phase1cap = 0;
            int nleft = 0;
            static cset left[200000];
            while (nsets > 0) {
                cset cur = sets[0];
                target = &sets[0];
                nodes = 0; aborted = 0; ended = 0; np = 0; stopflag = 0;
                for (int v = 0; v < n; v++) endS[v] = -1;
                dfs(R);
                if (target != NULL) {
                    /* not satisfied: exhaustive (fail) or budget (undecided) */
                    cur.v[5] = cur.v[5]; /* keep */
                    if (nleft < 200000) { left[nleft] = cur; left[nleft].fam = cur.fam + (aborted ? 100 : 0); nleft++; }
                    sets[0] = sets[--nsets];
                    target = NULL;
                }
            }
            phase1cap = cap;
            for (int i = 0; i < nleft; i++) {
                cset *s = &left[i];
                int ab = s->fam >= 100; int fam = s->fam % 100;
                if (ab) und[fam]++; else fail[fam]++;
                printf("%s %s %s", ab ? "UNDEC" : "FAIL", names[fam], line);
                for (int j = 0; j < 6 && s->v[j] >= 0; j++) printf(" %d", s->v[j]);
                /* print the clauses as c|x lists */
                for (int j = 0; j < s->k; j++) {
                    printf(" (");
                    for (int c = 0; c < n; c++) for (int x = 0; x < n; x++) if (s->cl[j] & B(c, x)) printf(" %d|%d", c, x);
                    printf(" )");
                }
                printf("\n");
            }
        }
    }
    fprintf(stderr, "graphs %lld\n", ngraphs);
    for (int f = 0; f < 6; f++) if (use[f]) fprintf(stderr, "%s: sets %lld, fail %lld, undecided %lld\n", names[f], tot[f], fail[f], und[f]);
    return 0;
}
