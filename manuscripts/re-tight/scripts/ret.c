/* ret.c -- exact checker for the degree-(n-2) form of RE (re-tight session).

   Setting.  B is a graph of even order n = 2k, r is a vertex of degree n - 2, s is the unique
   vertex other than r not adjacent to r, and G = B - r.  A *family* is (Q_x), x in N(r), where
   each Q_x is a path of G with an end at x (its *attachment*) or the trivial path x, and the
   nontrivial Q_x partition E(G).  Two members are *compatible* if they are vertex-disjoint.
   RE(B, r) holds iff some family admits k - 2 disjoint compatible pairs (eulerian-cone Rem. 7.2):
   the pairs give k - 2 paths Q_x x r y Q_y, the two leftover members give Q_x x r.

   Search.  Pieces are chosen one at a time, each with its attachment.  If the remaining edge set
   R has a vertex v of odd degree, some remaining piece ends at v, so we branch over all paths of
   R starting at v; otherwise we branch over all paths of R through the lowest edge of R.  Both
   branchings are complete.  Each piece gets an attachment among its ends in N(r) that is not yet
   used.  When R is empty, the trivial pieces are added for the unused attachments and a maximum
   matching of the compatibility graph is computed exactly.  Pruning: per component C of R at
   least max(1, odd(C)/2, max_v ceil(d_C(v)/2)) further pieces are needed, and they need distinct
   unused attachments; a piece containing all of N(r) is compatible with nothing ("dead").

   Modes.
     default   RE: at most 2 members unmatched (k - 2 pairs suffice; k - 1 pairs also give RE).
     -z        exactly k - 1 pairs, none unmatched.  This holds iff B has a decomposition into
               k - 1 paths all through r, i.e. iff p(B) <= k - 1 (each of the k - 1 paths uses at
               most two of the 2k - 2 edges at r).  Used to validate negative answers against
               re.c -p.
     -L        Lovasz-restricted: every vertex of N(r) is an end of exactly one piece and s of
               none.  The pieces are then exactly the paths of a Lovasz decomposition of G, each
               with one end chosen as attachment, the other end a trivial member.  This is the
               "Lovasz plus matching" method; the search is over all Lovasz decompositions and
               all orientations, and is complete.
     -q A:B    only families with A <= (number of nontrivial pieces) <= B.
     -S        s is not an end of any piece (e_B(s) = 0).
     -b N      node budget (status UNK when exceeded).
     -r R      only root R (must have degree n - 2).
     -c        count mode: do not stop at the first success; count successful families
               (with the node budget).  Prints the count instead of a witness.
   Input: graph6 on stdin.  Output per (graph, root of degree n - 2):
     g6 r YES q | piece ; piece ; ... | pairs |      piece = att:v0,v1,...  (v0 = att)
     g6 r NO
     g6 r UNK
   Limits: n <= 16; |E(G)| <= 64 (compile with -DWIDE for <= 128).
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#ifdef WIDE
typedef unsigned __int128 em;
#define MAXE 128
#else
typedef uint64_t em;
#define MAXE 64
#endif
#define ONE ((em)1)
#define MAXN 16

static int n, k, r, s;
static int A[MAXN][MAXN];
static int ne, eu[MAXE], ev[MAXE], eid[MAXN][MAXN];
static em inc[MAXN];
static int Nmask; /* N(r) as vertex mask */

static int modeZ = 0, modeL = 0, modeS = 0, countMode = 0, modeT = 0;
static int degB[MAXN];
static int minmu; static long long nlov;
static int qmin = 0, qmax = 1000;
static long long budget = 0, nodes;
static int aborted, found;
static long long nsucc;

/* pieces */
static int np;
static int pvm[2 * MAXN], patt[2 * MAXN], plen[2 * MAXN], pseq[2 * MAXN][MAXN + 1];
static int attm, endm;

/* best witness */
static int wnp, wvm[2 * MAXN], watt[2 * MAXN], wlen[2 * MAXN], wseq[2 * MAXN][MAXN + 1];
static int wmate[2 * MAXN], wtot;

static inline int popc(unsigned x) { return __builtin_popcount(x); }
static inline int epc(em x) {
#ifdef WIDE
    return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64));
#else
    return __builtin_popcountll(x);
#endif
}
static inline int ectz(em x) {
#ifdef WIDE
    uint64_t lo = (uint64_t)x;
    return lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll((uint64_t)(x >> 64));
#else
    return __builtin_ctzll(x);
#endif
}

/* ---- matching on the members ---- */
static int mvm[2 * MAXN], mtot, mate[2 * MAXN];
/* can the members i.. be handled with at most u unmatched? (members < i already decided) */
static int used_m;
static int match_rec(int u) {
    int i = 0;
    while (i < mtot && (used_m >> i & 1)) i++;
    if (i == mtot) return 1;
    used_m |= 1 << i;
    for (int j = i + 1; j < mtot; j++) {
        if ((used_m >> j & 1) || (mvm[i] & mvm[j])) continue;
        used_m |= 1 << j; mate[i] = j; mate[j] = i;
        if (match_rec(u)) return 1;
        used_m &= ~(1 << j);
    }
    if (u > 0) { mate[i] = -1; if (match_rec(u - 1)) return 1; }
    used_m &= ~(1 << i);
    return 0;
}

static int check_leaf(void) {
    if (np < qmin) return 0;
    mtot = 0;
    for (int i = 0; i < np; i++) mvm[mtot++] = pvm[i];
    for (int x = 0; x < n; x++)
        if ((Nmask >> x & 1) && !(attm >> x & 1)) mvm[mtot++] = 1 << x;
    used_m = 0;
    int u = modeZ ? 0 : 2;
    if (!match_rec(u)) return 0;
    /* record witness */
    wnp = np; wtot = mtot;
    for (int i = 0; i < np; i++) {
        wvm[i] = pvm[i]; watt[i] = patt[i]; wlen[i] = plen[i];
        memcpy(wseq[i], pseq[i], sizeof(int) * (plen[i] + 1));
    }
    int t = np;
    for (int x = 0; x < n; x++)
        if ((Nmask >> x & 1) && !(attm >> x & 1)) { watt[t] = x; wlen[t] = 0; wseq[t][0] = x; wvm[t] = 1 << x; t++; }
    for (int i = 0; i < mtot; i++) wmate[i] = mate[i];
    return 1;
}

/* ---- lower bound on further pieces ---- */
static int lower_bound(em R) {
    int deg[MAXN], seen = 0, lb = 0;
    int vm = 0;
    for (int v = 0; v < n; v++) { deg[v] = epc(R & inc[v]); if (deg[v]) vm |= 1 << v; }
    while (vm & ~seen) {
        int st = __builtin_ctz(vm & ~seen), comp = 1 << st, fr = comp;
        while (fr) {
            int v = __builtin_ctz(fr); fr &= fr - 1;
            for (int w = 0; w < n; w++)
                if (A[v][w] && v != r && w != r && (R >> eid[v][w] & 1) && !(comp >> w & 1)) { comp |= 1 << w; fr |= 1 << w; }
        }
        seen |= comp;
        int odd = 0, mx = 0;
        for (int v = 0; v < n; v++) if (comp >> v & 1) { if (deg[v] & 1) odd++; int c = (deg[v] + 1) / 2; if (c > mx) mx = c; }
        int b = odd / 2; if (b < mx) b = mx; if (b < 1) b = 1;
        lb += b;
    }
    return lb;
}

static void solve(em R);

static int curseq[MAXN + 1];
static int lseq[MAXN + 1];

/* try the current path curseq[0..len] (len >= 1) as a piece */
static void try_piece(em R, int len, int vmask, em pe) {
    int v0 = curseq[0], w = curseq[len];
    if (modeL) {
        if (!(Nmask >> v0 & 1) || !(Nmask >> w & 1)) return;
        if ((endm >> v0 & 1) || (endm >> w & 1)) return;
    }
    if (modeS && (v0 == s || w == s)) return;
    /* dead piece: contains all of N(r) -> compatible with nothing */
    int dead = ((vmask & Nmask) == Nmask);
    for (int side = 0; side < 2; side++) {
        int a = side ? w : v0;
        if (modeT) {
            /* the trivial end is the lower end in (degree, label) order; attach at the other */
            int other = side ? v0 : w;
            int alo = degB[a] < degB[other] || (degB[a] == degB[other] && a < other);
            if (alo) continue;
        }
        if (!(Nmask >> a & 1) || (attm >> a & 1)) continue;
        if (found && !countMode) return;
        if (aborted) return;
        /* count dead pieces: compatible with no placed piece and no possible future member
           (every future member contains an attachment outside attm, the new one included) */
        {
            int fut = Nmask & ~(attm | (1 << a));
            int nd = 0, u = modeZ ? 0 : 2;
            if (dead) nd = 1;
            else {
                int ok = (fut & ~vmask) != 0;
                for (int i = 0; i < np && !ok; i++) if (!(pvm[i] & vmask)) ok = 1;
                if (!ok) nd = 1;
            }
            for (int i = 0; i < np && nd <= u; i++) {
                int ok = (fut & ~pvm[i]) != 0 || !(pvm[i] & vmask);
                for (int j = 0; j < np && !ok; j++) if (j != i && !(pvm[i] & pvm[j])) ok = 1;
                if (!ok) nd++;
            }
            if (nd > u && !modeT) continue;
        }
        pvm[np] = vmask; patt[np] = a; plen[np] = len;
        if (side == 0) memcpy(pseq[np], curseq, sizeof(int) * (len + 1));
        else for (int i = 0; i <= len; i++) pseq[np][i] = curseq[len - i];
        np++; attm |= 1 << a;
        int oldend = endm;
        if (modeL) endm |= (1 << v0) | (1 << w);
        int savec[MAXN + 1], savel[MAXN + 1];
        memcpy(savec, curseq, sizeof savec); memcpy(savel, lseq, sizeof savel);
        solve(R & ~pe);
        memcpy(curseq, savec, sizeof savec); memcpy(lseq, savel, sizeof savel);
        endm = oldend;
        np--; attm &= ~(1 << a);
    }
}

/* enumerate paths from curseq[len] extending, avoiding vmask; post-order (longer first) */
static void extend(em R, int len, int vmask, em pe) {
    if ((found && !countMode) || aborted) return;
    int c = curseq[len];
    em avail = R & inc[c] & ~pe;
    while (avail) {
        int e = ectz(avail); avail &= avail - 1;
        int u = eu[e] == c ? ev[e] : eu[e];
        if (vmask >> u & 1) continue;
        curseq[len + 1] = u;
        extend(R, len + 1, vmask | (1 << u), pe | (ONE << e));
        if ((found && !countMode) || aborted) return;
    }
    if (len >= 1) try_piece(R, len, vmask, pe);
}

/* paths through edge e0 = (a,b): left part from a (reversed), then right part from b */
static void extend_right(em R, int llen, int len, int vmask, em pe) {
    if ((found && !countMode) || aborted) return;
    int c = curseq[len];
    em avail = R & inc[c] & ~pe;
    while (avail) {
        int e = ectz(avail); avail &= avail - 1;
        int u = eu[e] == c ? ev[e] : eu[e];
        if (vmask >> u & 1) continue;
        curseq[len + 1] = u;
        extend_right(R, llen, len + 1, vmask | (1 << u), pe | (ONE << e));
        if ((found && !countMode) || aborted) return;
    }
    try_piece(R, len, vmask, pe);
}
static void extend_left(em R, int llen, int vmask, em pe, int b, int e0) {
    if ((found && !countMode) || aborted) return;
    int c = lseq[llen];
    em avail = R & inc[c] & ~pe;
    while (avail) {
        int e = ectz(avail); avail &= avail - 1;
        int u = eu[e] == c ? ev[e] : eu[e];
        if ((vmask >> u & 1)) continue;
        lseq[llen + 1] = u;
        extend_left(R, llen + 1, vmask | (1 << u), pe | (ONE << e), b, e0);
        if ((found && !countMode) || aborted) return;
    }
    /* build curseq = reverse(lseq[0..llen]) + b */
    for (int i = 0; i <= llen; i++) curseq[i] = lseq[llen - i];
    curseq[llen + 1] = b;
    extend_right(R, llen, llen + 1, vmask | (1 << b), pe | (ONE << e0));
}

static void solve(em R) {
    if ((found && !countMode) || aborted) return;
    nodes++;
    if (budget && nodes > budget) { aborted = 1; return; }
    if (R == 0) {
        if (modeT) {
            /* bipartite matching: pieces vs trivial members (unused attachments) */
            int triv[MAXN], nt = 0;
            for (int x = 0; x < n; x++) if ((Nmask >> x & 1) && !(attm >> x & 1)) triv[nt++] = x;
            int matchT[MAXN]; for (int j = 0; j < nt; j++) matchT[j] = -1;
            int mu = 0;
            for (int i = 0; i < np; i++) {
                /* augmenting path search (Kuhn) */
                int seen[MAXN] = {0};
                int stack_i[2 * MAXN], sp2 = 0, par[2 * MAXN];
                (void)stack_i; (void)sp2; (void)par;
                /* simple recursive-free Kuhn via repeated DFS */
                int found_aug = 0;
                int vis[MAXN]; memset(vis, 0, sizeof vis);
                /* iterative DFS over (piece) nodes */
                int qi[2 * MAXN], qj[2 * MAXN], depth = 0;
                qi[0] = i; qj[0] = 0; depth = 1;
                int via[2 * MAXN];
                while (depth > 0 && !found_aug) {
                    int pi = qi[depth - 1];
                    int j = qj[depth - 1]++;
                    if (j >= nt) { depth--; continue; }
                    if (vis[j] || (pvm[pi] >> triv[j] & 1)) continue;
                    vis[j] = 1; via[depth - 1] = j;
                    if (matchT[j] < 0) {
                        for (int d2 = 0; d2 < depth; d2++) matchT[via[d2]] = qi[d2];
                        found_aug = 1;
                    } else { qi[depth] = matchT[j]; qj[depth] = 0; depth++; }
                }
                (void)seen;
                if (found_aug) mu++;
            }
            if (mu < minmu) minmu = mu;
            nlov++;
            return;
        }
        if (check_leaf()) { found = 1; nsucc++; }
        return;
    }
    /* relaxation: future members contain their attachment, so the current pieces plus the
       singletons {x} at the unused attachments must already admit the matching */
    if (np && !modeT) {
        mtot = 0;
        for (int i = 0; i < np; i++) mvm[mtot++] = pvm[i];
        for (int x = 0; x < n; x++)
            if ((Nmask >> x & 1) && !(attm >> x & 1)) mvm[mtot++] = 1 << x;
        used_m = 0;
        if (!match_rec(modeZ ? 0 : 2)) return;
    }
    /* capacity: the members containing v lie in distinct paths of B, so there are at most
       T of them (T = k, or k - 1 with -z); future ones number at least ceil(d_R(v)/2), and at
       least 1 if v is an unused attachment */
    {
        int T = modeZ ? k - 1 : k;
        for (int v = 0; v < n; v++) {
            if (v == r) continue;
            int c = 0;
            for (int i = 0; i < np; i++) c += pvm[i] >> v & 1;
            int f = (epc(R & inc[v]) + 1) / 2;
            if (f == 0 && (Nmask >> v & 1) && !(attm >> v & 1)) f = 1;
            if (c + f > T) return;
        }
    }
    /* end capacity: in the reassembled decomposition into T paths, v != r is an end of
       e_B(v) = (far ends of pieces at v) + [Q_v trivial] paths, and e_B(v) <= min(d_B(v), 2T - d_B(v)).
       Future: an unused attachment v adds >= 1 if d_R(v) is even (attached: an even number >= 2
       of piece ends at v, one of them far; trivial: +1), else >= 0; any other v adds >= 1 far end
       if d_R(v) is odd. */
    {
        int T = modeZ ? k - 1 : k;
        for (int v = 0; v < n; v++) {
            if (v == r) continue;
            int d = 0; for (int x = 0; x < n; x++) d += A[v][x];
            int cap = d < 2 * T - d ? d : 2 * T - d;
            int far = 0;
            for (int i = 0; i < np; i++) if (pseq[i][plen[i]] == v) far++;
            int dr = epc(R & inc[v]) & 1;
            int fut = ((Nmask >> v & 1) && !(attm >> v & 1)) ? !dr : dr;
            if (far + fut > cap) return;
        }
    }
    int freeatt = popc(Nmask & ~attm);
    int lb = lower_bound(R);
    if (lb > freeatt || np + lb > qmax) return;
    /* odd vertex? */
    int v = -1;
    for (int x = 0; x < n; x++) if (x != r && (epc(R & inc[x]) & 1)) { v = x; break; }
    if (v >= 0) {
        curseq[0] = v;
        extend(R, 0, 1 << v, 0);
    } else {
        int e0 = ectz(R);
        int a = eu[e0], b = ev[e0];
        lseq[0] = a;
        extend_left(R, 0, (1 << a) | (1 << b), ONE << e0, b, e0);
    }
}

static int parse_g6(const char *g) {
    int nn = g[0] - 63, p = 1, bit = 0, x = 0;
    memset(A, 0, sizeof A);
    for (int j = 1; j < nn; j++)
        for (int i = 0; i < j; i++) {
            if (bit == 0) { x = g[p++] - 63; bit = 6; }
            bit--;
            if (x >> bit & 1) A[i][j] = A[j][i] = 1;
        }
    return nn;
}

int main(int argc, char **argv) {
    int onlyr = -1;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-z")) modeZ = 1;
        else if (!strcmp(argv[i], "-L")) modeL = 1;
        else if (!strcmp(argv[i], "-S")) modeS = 1;
        else if (!strcmp(argv[i], "-c")) countMode = 1;
        else if (!strcmp(argv[i], "-T")) { modeT = 1; modeL = 1; countMode = 1; }
        else if (!strcmp(argv[i], "-b")) budget = atoll(argv[++i]);
        else if (!strcmp(argv[i], "-r")) onlyr = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-q")) { sscanf(argv[++i], "%d:%d", &qmin, &qmax); }
        else { fprintf(stderr, "unknown option %s\n", argv[i]); return 1; }
    }
    char line[256];
    while (fgets(line, sizeof line, stdin)) {
        line[strcspn(line, "\r\n ")] = 0;
        if (!line[0]) continue;
        n = parse_g6(line);
        if (n % 2 || n > MAXN) continue;
        k = n / 2;
        for (r = 0; r < n; r++) {
            if (onlyr >= 0 && r != onlyr) continue;
            int d = 0; for (int x = 0; x < n; x++) d += A[r][x];
            if (d != n - 2) continue;
            s = -1; Nmask = 0;
            for (int x = 0; x < n; x++) if (x != r) { if (A[r][x]) Nmask |= 1 << x; else s = x; }
            ne = 0; memset(inc, 0, sizeof inc);
            for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++)
                if (A[i][j] && i != r && j != r) {
                    if (ne >= MAXE) { fprintf(stderr, "too many edges\n"); return 1; }
                    eu[ne] = i; ev[ne] = j; eid[i][j] = eid[j][i] = ne;
                    inc[i] |= ONE << ne; inc[j] |= ONE << ne; ne++;
                }
            em all = ne == MAXE ? ~(em)0 : (ONE << ne) - 1;
            for (int v = 0; v < n; v++) { degB[v] = 0; for (int x = 0; x < n; x++) degB[v] += A[v][x]; }
            np = 0; attm = 0; endm = 0; nodes = 0; aborted = 0; found = 0; nsucc = 0;
            minmu = 1000; nlov = 0;
            solve(all);
            if (modeT) {
                printf("%s %d %s lovasz=%lld minmu=%d need=%d nodes=%lld\n", line, r, aborted ? "UNK" : "DONE",
                       nlov, minmu, k - 3, nodes);
                fflush(stdout);
                continue;
            }
            if (countMode) {
                printf("%s %d %s %lld nodes=%lld\n", line, r, aborted ? "UNK" : (nsucc ? "YES" : "NO"), nsucc, nodes);
            } else if (found) {
                printf("%s %d YES %d |", line, r, wnp);
                for (int i = 0; i < wtot; i++) {
                    printf(" %d:", watt[i]);
                    for (int j = 0; j <= wlen[i]; j++) printf("%s%d", j ? "," : "", wseq[i][j]);
                    printf(" ;");
                }
                printf(" |");
                for (int i = 0; i < wtot; i++) if (wmate[i] > i) printf(" %d-%d", watt[i], watt[wmate[i]]);
                printf(" | nodes=%lld\n", nodes);
            } else printf("%s %d %s nodes=%lld\n", line, r, aborted ? "UNK" : "NO", nodes);
            fflush(stdout);
        }
    }
    return 0;
}
