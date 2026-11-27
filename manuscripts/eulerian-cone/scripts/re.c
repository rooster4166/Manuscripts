/* re.c -- exact solver for the rooted path number (eulerian-cone session).

   For a graph B and a vertex r, p_r(B) is the least number of paths in a decomposition of E(B)
   in which r is an end of at least one path.  (When every degree of B is even, r is then an
   end of at least two paths.)  RE(B, r) is the statement p_r(B) <= |B|/2.  The program also
   computes the ordinary path number p(B).

   Search.  solve(R, t) decides whether the edge set R splits into at most t paths.
     - Lower bound: for every component C of R,
         p(C) >= max(1, odd(C)/2, max_{v in C} ceil(d_C(v)/2)),
       since every odd vertex is an end of a path and a path uses at most two edges at v.
     - Several components are solved one at a time, the first with the least budget that works.
     - Branching: if R has a vertex x of odd degree, x is an end of some path, so we branch over
       all paths of R that start at x.  Otherwise we branch over all paths of R through the
       lowest edge of R.  Both branchings are complete.  Longer paths are tried first.
     - Failures are memoised: fail[R] = the largest t for which solve(R, t) was false.
   The rooted problem branches first over all paths starting at r, then calls solve on the rest.
   An optional node budget turns the answer into "unknown" (2) when exceeded.

   Input: graph6 lines on stdin.  Output (one line per graph and root, roots 0..n-1 unless -r):
     g6 r p_r k status | v0 v1 ... | w0 w1 ... |
   where k = n/2 (floor), status is OK (p_r <= k), FAIL (p_r > k, proved), UNK (budget), and
   the paths are a witness decomposition with p_r paths and an end at r.  With -p the unrooted
   path number p(B) is printed instead (root field -1).
   Options: -b N  node budget per (graph, root) (0 = none)
            -r R  only root R
            -m    print only p_r (minimum) and skip the witness
            -q    print only lines whose status is not OK, plus a final summary
            -x    compute p_r exactly even when it exceeds k (status OVER)
            -u    UC mode: per root, first decide p_r <= max(CB, ceil(n/2) - 1), where CB is the
                  end-counting bound (see countbound.py); status UC if that holds, else decide
                  p_r <= ceil(n/2) (status OK) or FAIL/UNK
            -d    decide RE only: search with budget exactly k (the printed p_r is then
                  the size of the witness found, an upper bound for p_r)
   Limits: n <= 16, m <= 64.
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#ifdef WIDE
/* compile with -DWIDE for up to 128 edges (edge masks are 128-bit) */
#define MAXN 16
#define MAXM 128
typedef unsigned __int128 u64;
static inline int pc(u64 x) { return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64)); }
static inline int ctz(u64 x) { uint64_t lo = (uint64_t)x; return lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll((uint64_t)(x >> 64)); }
#define ONE ((u64)1)
#else
#define MAXN 16
#define MAXM 64
typedef uint64_t u64;
static inline int pc(u64 x) { return __builtin_popcountll(x); }
static inline int ctz(u64 x) { return __builtin_ctzll(x); }
#define ONE 1ULL
#endif

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

/* rooted: first path starts at r */
static int solve_root(int r, int t) {
    u64 R = (m == MAXM) ? ~(u64)0 : ((ONE << m) - 1);
    int buf[MAXN + 1];
    buf[0] = r;
    sp = 0;
    return ext1(R, t, buf, 1, 0, 1 << r);
}

/* end-counting bound: least p with 2p - d_r >= 2, d_v <= 2p and sum_v min(d_v, 2p - d_v) >= 2p */
static int countbound(int r) {
    for (int p = 1;; p++) {
        if (2 * p - adeg[r] < 2) continue;
        int ok = 1, cap = 0;
        for (int v = 0; v < n; v++) {
            if (adeg[v] > 2 * p) { ok = 0; break; }
            cap += adeg[v] < 2 * p - adeg[v] ? adeg[v] : 2 * p - adeg[v];
        }
        if (ok && cap >= 2 * p) return p;
    }
}

/* graph6 ----------------------------------------------------------------- */
static int read_g6(const char *s) {
    const unsigned char *p = (const unsigned char *)s;
    n = p[0] - 63;
    if (n > MAXN || n < 1) return 0;
    p++;
    int bit = 0, cur = 0, k = 0;
    m = 0;
    memset(eid, -1, sizeof eid);
    for (int v = 0; v < n; v++) { inc[v] = 0; adeg[v] = 0; }
    for (int j = 1; j < n; j++)
        for (int i = 0; i < j; i++) {
            if (bit == 0) { cur = p[k++] - 63; bit = 6; }
            bit--;
            if (cur >> bit & 1) {
                if (m >= MAXM) return 0;
                eu[m] = i; ev[m] = j; eid[i][j] = eid[j][i] = m;
                inc[i] |= ONE << m; inc[j] |= ONE << m;
                adjv[i][adeg[i]] = j; adje[i][adeg[i]++] = m;
                adjv[j][adeg[j]] = i; adje[j][adeg[j]++] = m;
                m++;
            }
        }
    return 1;
}

static void print_witness(void) {
    printf(" |");
    for (int i = 0; i < sp; i++) {
        for (int j = 0; j < stklen[i]; j++) printf(" %d", stk[i][j]);
        printf(" |");
    }
}

int main(int argc, char **argv) {
    budget = 0;
    int onlyroot = -1, minonly = 0, quiet = 0, unrooted = 0, exact = 0, decide = 0, ucmode = 0;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-b") && i + 1 < argc) budget = atoll(argv[++i]);
        else if (!strcmp(argv[i], "-r") && i + 1 < argc) onlyroot = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-m")) minonly = 1;
        else if (!strcmp(argv[i], "-q")) quiet = 1;
        else if (!strcmp(argv[i], "-p")) unrooted = 1;
        else if (!strcmp(argv[i], "-x")) exact = 1;
        else if (!strcmp(argv[i], "-d")) decide = 1;
        else if (!strcmp(argv[i], "-u")) ucmode = 1;
    }
    tab = calloc(HSIZE, sizeof(entry));
    char line[1024];
    long long ngr = 0, nok = 0, nfail = 0, nunk = 0, ntight = 0, nuc = 0;
    while (fgets(line, sizeof line, stdin)) {
        line[strcspn(line, "\r\n")] = 0;
        if (!line[0]) continue;
        if (!read_g6(line)) { printf("%s SKIP\n", line); continue; }
        ngr++;
        stamp++;
        if (stamp == 0) { memset(tab, 0, HSIZE * sizeof(entry)); stamp = 1; }
        int k = n / 2;
        if (unrooted) {
            u64 R = (m == MAXM) ? ~(u64)0 : ((ONE << m) - 1);
            int t, res = 0;
            nodes = 0; aborted = 0;
            for (t = (m ? lball(R) : 0); t <= m; t++) {
                sp = 0;
                if (solve(R, t)) { res = 1; break; }
                if (aborted) break;
            }
            if (!quiet || !res) {
                printf("%s -1 %d %d %s", line, res ? t : -1, k, res ? (t <= k ? "OK" : "OVER") : "UNK");
                if (res && !minonly) print_witness();
                printf("\n");
            }
            continue;
        }
        for (int r = 0; r < n; r++) {
            if (onlyroot >= 0 && r != onlyroot) continue;
            if (adeg[r] == 0) continue;
            if (ucmode) {
                int ce = (n + 1) / 2, cb = countbound(r);
                int t1 = cb > ce - 1 ? cb : ce - 1;
                const char *st = "FAIL";
                int got = -1;
                nodes = 0; aborted = 0;
                if (solve_root(r, t1)) { st = "UC"; got = sp; nuc++; }
                else {
                    int ab1 = aborted;
                    nodes = 0; aborted = 0;
                    if (t1 < ce && solve_root(r, ce)) { st = ab1 ? "OKUNK" : "OK"; got = sp; nok++; }
                    else if (aborted || ab1) { st = "UNK"; nunk++; }
                    else nfail++;
                }
                if (!quiet || strcmp(st, "UC")) {
                    printf("%s %d %d %d %s cb=%d", line, r, got, ce, st, cb);
                    if (got >= 0 && !minonly) print_witness();
                    printf("\n");
                }
                continue;
            }
            nodes = 0; aborted = 0;
            int res = 0, t;
            int lb = (adeg[r] + 2) / 2; /* paths at r: one end plus ceil((d-1)/2) others */
            if (lb < 1) lb = 1;
            int tmax = exact ? m : k;
            if (decide && lb <= k) lb = k;
            for (t = lb; t <= tmax; t++) {
                if (solve_root(r, t)) { res = 1; break; }
                if (aborted) break;
            }
            const char *st;
            if (res && decide) t = sp;
            if (res && t > k) { st = "OVER"; nfail++; }
            else if (res) { st = "OK"; nok++; if (t == k) ntight++; }
            else if (aborted) { st = "UNK"; nunk++; }
            else { st = "FAIL"; nfail++; }
            if (!quiet || !res) {
                printf("%s %d %d %d %s", line, r, res ? t : -1, k, st);
                if (res && !minonly) print_witness();
                printf("\n");
            }
        }
        fflush(stdout);
    }
    if (quiet && !unrooted)
        printf("# graphs %lld roots_uc %lld roots_ok %lld tight %lld fail %lld unknown %lld\n", ngr,
               nuc, nok, ntight, nfail, nunk);
    return 0;
}
