/* lovcheck.c -- A31 audit: independent re-implementation of the Lovasz-plus-matching tests of
   re-tight (shares no code with ret.c).

   For a graph B (graph6 on stdin) and every root r of degree n - 2 (or only -r R):
     G = B - r, N = N(r).  Enumerate EVERY Lovasz decomposition of G (every x in N is an end of
     exactly one path, no other vertex is an end), each exactly once: the path ending at the
     smallest x in N that is not yet an end is unique, so we branch over all simple paths from x
     in the remaining edge set that end at some other y in N not yet an end.  Pruning is only by
     necessary parity/length conditions (stated at feasible()).
   For every decomposition D:
     muT  = max bipartite matching paths vs trivial ends (P_i ~ b_j iff b_j not on P_i), with
            the orientation of ret.c -T (trivial end = lower end in (degree, label) order);
     muA  = min of the same over ALL orientations with d(b_i) <= d(a_i) (every tie-break);
     Lok  = some orientation (any of the 2^(k-1)) whose general compatibility graph on the 2k-2
            members (paths and trivial ends; compatible = vertex-disjoint) has a matching of size
            k - 2.
   Input lines: g6 [root].  Output: g6 r ndec minmuT minmuA Lyes(0/1) status(DONE/CAP) need=k-3
   Options: -r R (one root), -c CAP (stop after CAP decompositions, status CAP), -l (stop at the
   first Lok success; then ndec/minmu are partial and status is LSTOP), -noL (skip Lok; Lyes = 0).
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 16
static int n, k, r, s;
static int adj[MAXN][MAXN], degB[MAXN];
static int inN[MAXN];
static int rem[MAXN][MAXN], rdeg[MAXN];
static int isend[MAXN];
static int npaths;
static int pv[MAXN][MAXN + 1], plen[MAXN]; /* vertex sequences */
static unsigned pmask[MAXN];
static long long ndec, cap;
static int minT, minA, Lyes, stopL, capped, nrem, noL;

static int bip_match(int m, unsigned *pm, int *triv) {
    /* paths 0..m-1, trivial ends triv[0..m-1]; Kuhn */
    int mt[MAXN], res = 0;
    for (int j = 0; j < m; j++) mt[j] = -1;
    for (int i = 0; i < m; i++) {
        int vis[MAXN] = {0};
        /* recursive helper via explicit function */
        int stackp[MAXN], stackj[MAXN], via[MAXN], d = 0, ok = 0;
        stackp[0] = i; stackj[0] = 0; d = 1;
        while (d > 0 && !ok) {
            int p = stackp[d - 1], j = stackj[d - 1]++;
            if (j >= m) { d--; continue; }
            if (vis[j] || (pm[p] >> triv[j] & 1)) continue;
            vis[j] = 1; via[d - 1] = j;
            if (mt[j] < 0) { for (int t = 0; t < d; t++) mt[via[t]] = stackp[t]; ok = 1; }
            else { stackp[d] = mt[j]; stackj[d] = 0; d++; }
        }
        res += ok;
    }
    return res;
}

static int gen_match(int m, unsigned *vm) {
    /* maximum matching in the general graph on m members (m <= 30), compat = disjoint; DP */
    static int memo[1 << 16];
    if (m > 16) { fprintf(stderr, "too many members\n"); exit(1); }
    int full = (1 << m) - 1;
    for (int S = 0; S <= full; S++) memo[S] = 0;
    for (int S = 1; S <= full; S++) {
        int i = __builtin_ctz(S), T = S & ~(1 << i);
        int best = memo[T];
        for (int j = i + 1; j < m; j++)
            if ((T >> j & 1) && !(vm[i] & vm[j])) {
                int v = 1 + memo[T & ~(1 << j)];
                if (v > best) best = v;
            }
        memo[S] = best;
    }
    return memo[full];
}

static void evaluate(void) {
    int m = npaths;
    ndec++;
    /* ret.c -T orientation */
    int triv[MAXN];
    for (int i = 0; i < m; i++) {
        int a = pv[i][0], b = pv[i][plen[i]];
        int blow = degB[b] < degB[a] || (degB[b] == degB[a] && b < a);
        triv[i] = blow ? b : a;
    }
    int mu = bip_match(m, pmask, triv);
    if (mu < minT) minT = mu;
    /* all orientations */
    for (int o = 0; o < (1 << m); o++) {
        int ok = 1;
        unsigned vm[2 * MAXN];
        for (int i = 0; i < m; i++) {
            int a = pv[i][0], b = pv[i][plen[i]];
            if (o >> i & 1) { int t = a; a = b; b = t; }
            triv[i] = b;
            if (degB[b] > degB[a]) ok = 0;
            vm[i] = pmask[i]; vm[m + i] = 1u << b;
        }
        if (ok) {
            int mm = bip_match(m, pmask, triv);
            if (mm < minA) minA = mm;
        }
        if (!Lyes && !noL) {
            if (gen_match(2 * m, vm) >= k - 2) Lyes = 1;
        }
    }
}

/* necessary conditions on the remaining edges: a vertex of N that is not an end has odd
   remaining degree; every other vertex has even remaining degree; the remaining edges fit into
   (#non-end vertices of N)/2 paths of length <= n - 2 */
static int feasible(void) {
    int open = 0;
    for (int v = 0; v < n; v++) {
        if (v == r) continue;
        int want = inN[v] && !isend[v];
        open += want;
        if ((rdeg[v] & 1) != want) return 0;
    }
    if (nrem > (open / 2) * (n - 2)) return 0;
    return 1;
}

static void search(void);
static int cur[MAXN + 1];
static unsigned curm;

static void extend(int len) {
    if (capped || (stopL && Lyes)) return;
    int c = cur[len];
    if (len >= 1 && inN[c] && !isend[c]) {
        /* close the path here */
        int x = cur[0];
        isend[x] = isend[c] = 1;
        for (int i = 0; i <= len; i++) pv[npaths][i] = cur[i];
        plen[npaths] = len; pmask[npaths] = curm; npaths++;
        for (int i = 0; i < len; i++) { rem[cur[i]][cur[i + 1]] = rem[cur[i + 1]][cur[i]] = 0; rdeg[cur[i]]--; rdeg[cur[i + 1]]--; }
        nrem -= len;
        {
            int savec[MAXN + 1]; unsigned savem = curm;
            memcpy(savec, cur, sizeof savec);
            if (feasible()) search();
            memcpy(cur, savec, sizeof savec); curm = savem;
        }
        nrem += len;
        for (int i = 0; i < len; i++) { rem[cur[i]][cur[i + 1]] = rem[cur[i + 1]][cur[i]] = 1; rdeg[cur[i]]++; rdeg[cur[i + 1]]++; }
        npaths--;
        isend[x] = isend[c] = 0;
    }
    for (int w = 0; w < n; w++) {
        if (!rem[c][w] || (curm >> w & 1)) continue;
        /* the path is still being built: its edges are removed only on closing, but we must not
           reuse an edge -- simple path, so no edge repeats */
        cur[len + 1] = w; curm |= 1u << w;
        extend(len + 1);
        curm &= ~(1u << w);
        if (capped || (stopL && Lyes)) return;
    }
}

static void search(void) {
    if (capped || (stopL && Lyes)) return;
    int x = -1;
    for (int v = 0; v < n; v++) if (inN[v] && !isend[v]) { x = v; break; }
    if (x < 0) {
        if (nrem == 0) {
            evaluate();
            if (cap && ndec >= cap) capped = 1;
        }
        return;
    }
    cur[0] = x; curm = 1u << x;
    extend(0);
}

static int parse(const char *g) {
    int nn = g[0] - 63, p = 1, bit = 0, x = 0;
    if (nn < 1 || nn > MAXN) return -1;
    memset(adj, 0, sizeof adj);
    for (int j = 1; j < nn; j++)
        for (int i = 0; i < j; i++) {
            if (bit == 0) { x = g[p++] - 63; bit = 6; }
            bit--;
            if (x >> bit & 1) adj[i][j] = adj[j][i] = 1;
        }
    return nn;
}

int main(int argc, char **argv) {
    int onlyr = -1;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-r")) onlyr = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-c")) cap = atoll(argv[++i]);
        else if (!strcmp(argv[i], "-l")) stopL = 1;
        else if (!strcmp(argv[i], "-noL")) noL = 1;
    }
    char line[256];
    while (fgets(line, sizeof line, stdin)) {
        int lr = -1;
        {
            char *sp = strchr(line, ' ');
            if (sp) { lr = atoi(sp + 1); }
        }
        line[strcspn(line, "\r\n ")] = 0;
        if (!line[0]) continue;
        n = parse(line);
        if (n < 0 || n % 2) continue;
        k = n / 2;
        for (int v = 0; v < n; v++) { degB[v] = 0; for (int w = 0; w < n; w++) degB[v] += adj[v][w]; }
        for (r = 0; r < n; r++) {
            if (onlyr >= 0 && r != onlyr) continue;
            if (lr >= 0 && r != lr) continue;
            if (degB[r] != n - 2) continue;
            s = -1;
            for (int v = 0; v < n; v++) { inN[v] = adj[r][v]; if (v != r && !adj[r][v]) s = v; isend[v] = 0; }
            nrem = 0;
            for (int v = 0; v < n; v++) { rdeg[v] = 0; for (int w = 0; w < n; w++) { rem[v][w] = adj[v][w] && v != r && w != r; rdeg[v] += rem[v][w]; } nrem += rdeg[v]; }
            nrem /= 2;
            npaths = 0; ndec = 0; minT = minA = 1000; Lyes = 0; capped = 0;
            if (feasible()) search();
            printf("%s %d %lld %d %d %d %s need=%d\n", line, r, ndec, minT, minA, Lyes,
                   capped ? "CAP" : (stopL && Lyes) ? "LSTOP" : "DONE", k - 3);
            fflush(stdout);
        }
    }
    return 0;
}
