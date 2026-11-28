/* t2.c -- exact solver for the spine test (T2) (test2 session).

   Input: graph6 lines of graphs J (n <= 16).  For each J with exactly two even-degree vertices
   z, r, adjacent (and, unless -a, 3-connected), and for each of the two orientations (z, r) and
   (r, z), decide (T2) at (J, z, r):
       B = J - z has a decomposition into at most n/2 paths with at least three ends at r.
   Computed per instance:
     slack : 1 iff p(B) <= n/2 - 1 (then (T2) holds by the splitting lemma, spine Lemma ends(b));
     t2    : 1 iff (T2) holds (decided exactly; a witness is printed);
     emax  : the largest e such that B has a decomposition into <= n/2 paths with >= e ends at r
             (computed only with -e; e is odd since d_B(r) is odd).
   Output (one line per instance):
     g6 z r dz dr n slack t2 emax | witness paths (vertices of J) |
   The witness is a decomposition of B with <= n/2 paths and >= 3 ends at r (or, if t2 = 0, nothing).

   The path search (solve, ext1, the memo, the lower bounds) is copied verbatim from
   manuscripts/eulerian-cone/scripts/re.c (validated in audit A30).  New here: the rooted search
   with e ends at r (solve_rooted_e), the parity and 3-connectivity filters, and the driver.
   Options: -a  do not require 3-connectivity
            -e  compute emax
            -E  compute emax only for instances with slack = 0
            -b N node budget (0 = none; undecided answers print t2 = 2)
            -B N node budget for each emax search (0 = none); if a search is cut off, emax is
                 printed as -e, meaning emax >= e (e the last value proved)
            -q  print only instances with slack = 0
            -s  also print a slack witness: after the (T2) witness, the token S and a decomposition
                of B into <= n/2 - 1 paths (only when slack = 1), each path followed by |
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 16
#define MAXM 64
typedef uint64_t u64;
static inline int pc(u64 x) { return __builtin_popcountll(x); }
static inline int ctz(u64 x) { return __builtin_ctzll(x); }
#define ONE 1ULL

static int n, m;
static int eu[MAXM], ev[MAXM];
static int eid[MAXN][MAXN];
static u64 inc[MAXN];
static int adjv[MAXN][MAXN], adje[MAXN][MAXN], adeg[MAXN];

/* memo */
#define HBITS 22
#define HSIZE (1u << HBITS)
typedef struct { u64 key; uint32_t stamp; int8_t failt; } entry;
static entry *tab;
static uint32_t stamp = 0;

static long long nodes, budget;
static int aborted;

/* witness stack */
static int stk[4 * MAXM][MAXN + 1];
static int stklen[4 * MAXM];
static int sp = 0;

static inline uint32_t hsh(u64 xx) {
    uint64_t x = (uint64_t)xx ^ (uint64_t)(xx >> 32 >> 32) * 0x9e3779b97f4a7c15ULL;
    x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33;
    return (uint32_t)(x & (HSIZE - 1));
}
static int memo_failed(u64 R, int t) {
    uint32_t h = hsh(R);
    for (int i = 0; i < 4; i++) {
        entry *e = &tab[(h + i) & (HSIZE - 1)];
        if (e->stamp != stamp) return 0;
        if (e->key == R) return e->failt >= t;
    }
    return 0;
}
static void memo_store(u64 R, int t) {
    uint32_t h = hsh(R);
    for (int i = 0; i < 4; i++) {
        entry *e = &tab[(h + i) & (HSIZE - 1)];
        if (e->stamp != stamp) { e->stamp = stamp; e->key = R; e->failt = (int8_t)t; return; }
        if (e->key == R) { if (t > e->failt) e->failt = (int8_t)t; return; }
    }
    entry *e = &tab[h];
    e->stamp = stamp; e->key = R; e->failt = (int8_t)t;
}

static inline int degR(u64 R, int v) { return pc(R & inc[v]); }

/* component of edge set R containing edge e0, as an edge mask */
static u64 component(u64 R, int e0) {
    int vm = (1 << eu[e0]) | (1 << ev[e0]);
    u64 C = 0;
    for (;;) {
        u64 add = 0;
        for (int v = 0; v < n; v++) if (vm >> v & 1) add |= inc[v] & R;
        add &= ~C;
        if (!add) break;
        C |= add;
        u64 a = add;
        while (a) { int e = ctz(a); a &= a - 1; vm |= (1 << eu[e]) | (1 << ev[e]); }
    }
    return C;
}

static int lbcomp(u64 C) {
    int odd = 0, mx = 0, nv = 0;
    for (int v = 0; v < n; v++) {
        int d = degR(C, v);
        if (d) nv++;
        if (d & 1) odd++;
        if ((d + 1) / 2 > mx) mx = (d + 1) / 2;
    }
    int lb = odd / 2;
    if (mx > lb) lb = mx;
    /* a path of C has at most nv - 1 edges */
    int me = pc(C);
    int le = (me + nv - 2) / (nv - 1);
    if (le > lb) lb = le;
    if (lb < 1) lb = 1;
    return lb;
}

static int lball(u64 R) {
    int s = 0;
    while (R) {
        int e0 = ctz(R);
        u64 C = component(R, e0);
        s += lbcomp(C);
        R &= ~C;
    }
    return s;
}

static int solve(u64 R, int t);

/* path enumeration ------------------------------------------------------- */
/* current path as a vertex sequence pv[0..pl-1]; edge mask pm; vertex mask vmask */

static void push_path(const int *seq, int len) {
    memcpy(stk[sp], seq, len * sizeof(int));
    stklen[sp] = len;
    sp++;
}

/* one-directional: extend from the last vertex; path seq in buf[0..len-1] */
static int ext1(u64 R, int t, int *buf, int len, u64 pm, int vmask) {
    if (aborted) return 0;
    int x = buf[len - 1];
    for (int i = 0; i < adeg[x]; i++) {
        int y = adjv[x][i], e = adje[x][i];
        if (!(R >> e & 1) || (vmask >> y & 1)) continue;
        buf[len] = y;
        if (ext1(R, t, buf, len + 1, pm | (ONE << e), vmask | (1 << y))) return 1;
        if (aborted) return 0;
    }
    if (len >= 2) {
        int save = sp;
        push_path(buf, len);
        if (solve(R & ~pm, t - 1)) return 1;
        sp = save;
    }
    return 0;
}

/* two-directional through edge e0 = (a, b): tail grows from b, then head grows from a */
static int ext_head(u64 R, int t, int *tail, int tl, int *head, int hl, u64 pm, int vmask) {
    if (aborted) return 0;
    int x = head[hl - 1];
    for (int i = 0; i < adeg[x]; i++) {
        int y = adjv[x][i], e = adje[x][i];
        if (!(R >> e & 1) || (vmask >> y & 1)) continue;
        head[hl] = y;
        if (ext_head(R, t, tail, tl, head, hl + 1, pm | (ONE << e), vmask | (1 << y))) return 1;
        if (aborted) return 0;
    }
    /* path = reverse(head) + tail ; head[0] = a = tail's predecessor */
    int seq[2 * MAXN + 2], L = 0;
    for (int i = hl - 1; i >= 0; i--) seq[L++] = head[i];
    for (int i = 0; i < tl; i++) seq[L++] = tail[i];
    int save = sp;
    push_path(seq, L);
    if (solve(R & ~pm, t - 1)) return 1;
    sp = save;
    return 0;
}
static int ext_tail(u64 R, int t, int a, int *tail, int tl, u64 pm, int vmask) {
    if (aborted) return 0;
    int x = tail[tl - 1];
    for (int i = 0; i < adeg[x]; i++) {
        int y = adjv[x][i], e = adje[x][i];
        if (!(R >> e & 1) || (vmask >> y & 1)) continue;
        tail[tl] = y;
        if (ext_tail(R, t, a, tail, tl + 1, pm | (ONE << e), vmask | (1 << y))) return 1;
        if (aborted) return 0;
    }
    int head[MAXN + 1];
    head[0] = a;
    return ext_head(R, t, tail, tl, head, 1, pm, vmask);
}

static int solve_conn(u64 R, int t) {
    /* R connected, nonempty, lb(R) <= t already checked */
    int x = -1;
    for (int v = 0; v < n; v++) if (degR(R, v) & 1) { x = v; break; }
    if (x >= 0) {
        int buf[MAXN + 1];
        buf[0] = x;
        return ext1(R, t, buf, 1, 0, 1 << x);
    }
    int e0 = ctz(R);
    int a = eu[e0], b = ev[e0];
    int tail[MAXN + 1];
    tail[0] = b;
    return ext_tail(R, t, a, tail, 1, ONE << e0, (1 << a) | (1 << b));
}

static int solve(u64 R, int t) {
    if (R == 0) return 1;
    if (t <= 0) return 0;
    if (aborted) return 0;
    if (budget && ++nodes > budget) { aborted = 1; return 0; }
    if (lball(R) > t) return 0;
    if (memo_failed(R, t)) return 0;
    int save = sp;
    int e0 = ctz(R);
    u64 C = component(R, e0);
    int ok;
    if (C == R) {
        ok = solve_conn(R, t);
    } else {
        u64 rest = R & ~C;
        int lbr = lball(rest);
        ok = 0;
        for (int s = lbcomp(C); s <= t - lbr; s++) {
            if (solve(C, s)) { ok = solve(rest, t - s); break; }
            if (aborted) break;
        }
    }
    if (!ok) {
        sp = save;
        if (!aborted) memo_store(R, t);
    }
    return ok;
}

/* ---- new: rooted search with e ends at r ------------------------------------------------ */
static int solve_rooted_e(u64 R, int t, int e, int r, int minfe);

static int rext(u64 R, int t, int e, int r, int f, int *buf, int len, u64 pm, int vmask) {
    if (aborted) return 0;
    int x = buf[len - 1];
    for (int i = 0; i < adeg[x]; i++) {
        int y = adjv[x][i], g = adje[x][i];
        if (!(R >> g & 1) || (vmask >> y & 1)) continue;
        buf[len] = y;
        if (rext(R, t, e, r, f, buf, len + 1, pm | (ONE << g), vmask | (1 << y))) return 1;
        if (aborted) return 0;
    }
    int save = sp;
    push_path(buf, len);
    if (solve_rooted_e(R & ~pm, t - 1, e - 1, r, f)) return 1;
    sp = save;
    return 0;
}

/* Is there a decomposition of R into <= t paths, e of which start at r with first edges of index
   > minfe, the first edges increasing?  (Complete: order the r-paths by first edge.) */
static int solve_rooted_e(u64 R, int t, int e, int r, int minfe) {
    if (e == 0) return solve(R, t);
    if (t < e) return 0;
    if (aborted) return 0;
    if (budget && ++nodes > budget) { aborted = 1; return 0; }
    if (lball(R) > t) return 0;
    int buf[MAXN + 1];
    for (int i = 0; i < adeg[r]; i++) {
        int y = adjv[r][i], f = adje[r][i];
        if (!(R >> f & 1) || f <= minfe) continue;
        buf[0] = r; buf[1] = y;
        if (rext(R, t, e, r, f, buf, 2, ONE << f, (1 << r) | (1 << y))) return 1;
        if (aborted) return 0;
    }
    return 0;
}

/* ---- J, its filters, and B = J - z ------------------------------------------------------- */
static int Jn, Jadj[MAXN];
static int bmap[MAXN];  /* B index -> J vertex */

static int read_J(const char *s) {
    const unsigned char *p = (const unsigned char *)s;
    Jn = p[0] - 63;
    if (Jn > MAXN || Jn < 1) return 0;
    p++;
    int bit = 0, cur = 0, k = 0;
    for (int v = 0; v < Jn; v++) Jadj[v] = 0;
    for (int j = 1; j < Jn; j++)
        for (int i = 0; i < j; i++) {
            if (bit == 0) { cur = p[k++] - 63; bit = 6; }
            bit--;
            if (cur >> bit & 1) { Jadj[i] |= 1 << j; Jadj[j] |= 1 << i; }
        }
    return 1;
}

static int connected_without(int X) {
    int all = ((1 << Jn) - 1) & ~X;
    if (!all) return 1;
    int seen = all & -all, frontier = seen;
    while (frontier) {
        int v = __builtin_ctz(frontier);
        frontier &= frontier - 1;
        int nb = Jadj[v] & all & ~seen;
        seen |= nb; frontier |= nb;
    }
    return seen == all;
}

static int three_connected(void) {
    if (Jn < 4) return 0;
    if (!connected_without(0)) return 0;
    for (int a = 0; a < Jn; a++) {
        if (!connected_without(1 << a)) return 0;
        for (int b = a + 1; b < Jn; b++) if (!connected_without((1 << a) | (1 << b))) return 0;
    }
    return 1;
}

/* load B = J - z into the solver globals; returns the B index of r */
static int load_B(int z, int r) {
    int idx[MAXN];
    n = 0;
    for (int v = 0; v < Jn; v++) if (v != z) { idx[v] = n; bmap[n] = v; n++; }
    m = 0;
    memset(eid, -1, sizeof eid);
    for (int v = 0; v < n; v++) { inc[v] = 0; adeg[v] = 0; }
    for (int j = 0; j < Jn; j++) for (int i = 0; i < j; i++) {
        if (i == z || j == z || !(Jadj[i] >> j & 1)) continue;
        int a = idx[i], b = idx[j];
        if (m >= MAXM) { fprintf(stderr, "too many edges\n"); exit(1); }
        eu[m] = a; ev[m] = b; eid[a][b] = eid[b][a] = m;
        inc[a] |= ONE << m; inc[b] |= ONE << m;
        adjv[a][adeg[a]] = b; adje[a][adeg[a]++] = m;
        adjv[b][adeg[b]] = a; adje[b][adeg[b]++] = m;
        m++;
    }
    return idx[r];
}

static void print_witness_J(void) {
    printf(" |");
    for (int i = 0; i < sp; i++) {
        for (int j = 0; j < stklen[i]; j++) printf(" %d", bmap[stk[i][j]]);
        printf(" |");
    }
}

int main(int argc, char **argv) {
    budget = 0;
    int any = 0, doemax = 0, quiet = 0, slackwit = 0;
    long long ebudget = 0;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-a")) any = 1;
        else if (!strcmp(argv[i], "-e")) doemax = 1;
        else if (!strcmp(argv[i], "-E")) doemax = 2;
        else if (!strcmp(argv[i], "-q")) quiet = 1;
        else if (!strcmp(argv[i], "-s")) slackwit = 1;
        else if (!strcmp(argv[i], "-b") && i + 1 < argc) budget = atoll(argv[++i]);
        else if (!strcmp(argv[i], "-B") && i + 1 < argc) ebudget = atoll(argv[++i]);
    }
    tab = calloc(HSIZE, sizeof(entry));
    char line[1024];
    long long ngr = 0, ninst = 0, nslack = 0, ntight = 0, nfail = 0, nunk = 0;
    long long emaxc[MAXN * 2] = {0}, emaxtight[MAXN * 2] = {0}, nemaxunk = 0;
    while (fgets(line, sizeof line, stdin)) {
        line[strcspn(line, "\r\n")] = 0;
        if (!line[0]) continue;
        if (!read_J(line)) continue;
        int ev2[2], ne = 0, ok = 1;
        for (int v = 0; v < Jn; v++) if (!(__builtin_popcount(Jadj[v]) & 1)) {
            if (ne < 2) ev2[ne] = v;
            ne++;
        }
        if (ne != 2) continue;
        if (!(Jadj[ev2[0]] >> ev2[1] & 1)) continue;
        if (!any && !three_connected()) continue;
        (void)ok;
        ngr++;
        for (int o = 0; o < 2; o++) {
            int z = ev2[o], r = ev2[1 - o];
            int rb = load_B(z, r);
            stamp++;
            if (stamp == 0) { memset(tab, 0, HSIZE * sizeof(entry)); stamp = 1; }
            int k = Jn / 2;
            u64 E = (m == MAXM) ? ~(u64)0 : ((ONE << m) - 1);
            nodes = 0; aborted = 0; sp = 0;
            int slack = solve(E, k - 1);
            int ab0 = aborted;
            /* save the slack witness */
            static int sst[4 * MAXM][MAXN + 1], sl[4 * MAXM];
            int ssp = slack ? sp : 0;
            for (int i = 0; i < ssp; i++) { sl[i] = stklen[i]; memcpy(sst[i], stk[i], sizeof stk[i]); }
            int t2;
            nodes = 0; aborted = 0; sp = 0;
            if (solve_rooted_e(E, k, 3, rb, -1)) t2 = 1;
            else t2 = aborted ? 2 : 0;
            int wsp = sp, wstk_ok = (t2 == 1);
            /* save witness */
            static int wst[4 * MAXM][MAXN + 1], wl[4 * MAXM];
            for (int i = 0; i < wsp; i++) { wl[i] = stklen[i]; memcpy(wst[i], stk[i], sizeof stk[i]); }
            int emax = -1;
            if (doemax && t2 == 1 && (doemax == 1 || !slack)) {
                emax = 3;
                long long b0 = budget;
                budget = ebudget;
                for (int e = 5; e <= adeg[rb]; e += 2) {
                    nodes = 0; aborted = 0; sp = 0;
                    if (solve_rooted_e(E, k, e, rb, -1)) emax = e;
                    else { if (aborted) emax = -emax; break; }
                }
                budget = b0;
            }
            ninst++;
            if (slack) nslack++; else if (!ab0) ntight++;
            if (t2 == 0) nfail++;
            if (t2 == 2) nunk++;
            if (emax > 0) { emaxc[emax]++; if (!slack) emaxtight[emax]++; }
            if (emax < -1) nemaxunk++;
            if (!quiet || !slack || t2 != 1) {
                printf("%s %d %d %d %d %d %d %d %d", line, z, r, __builtin_popcount(Jadj[z]),
                       __builtin_popcount(Jadj[r]), Jn, slack ? 1 : (ab0 ? 2 : 0), t2, emax);
                sp = wsp;
                for (int i = 0; i < wsp; i++) { stklen[i] = wl[i]; memcpy(stk[i], wst[i], sizeof stk[i]); }
                if (wstk_ok) print_witness_J();
                if (slackwit && slack) {
                    printf(" S");
                    sp = ssp;
                    for (int i = 0; i < ssp; i++) { stklen[i] = sl[i]; memcpy(stk[i], sst[i], sizeof stk[i]); }
                    print_witness_J();
                }
                printf("\n");
            }
        }
    }
    fprintf(stderr, "graphs %lld instances %lld slack %lld tight %lld fail %lld unk %lld\n",
            ngr, ninst, nslack, ntight, nfail, nunk);
    if (doemax) {
        fprintf(stderr, "emax distribution (all / tight):");
        for (int e = 3; e < MAXN * 2; e += 2) if (emaxc[e]) fprintf(stderr, " %d:%lld/%lld", e, emaxc[e], emaxtight[e]);
        fprintf(stderr, " undecided %lld\n", nemaxunk);
    }
    return 0;
}
