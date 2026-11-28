/* trsolve.c -- A40 audit: independent exact solver for constrained parity path decompositions.

   Method (shares nothing with lnsolve.c or lnlib.py): a path decomposition is encoded by its
   *transition system*: at every vertex v the incident half-edges are split into r(v) path ends
   and a perfect matching of the others (consecutive edges of a path).  Vertices are processed one
   at a time (max-cardinality order); chains of edges are kept in a union-find structure with
   their vertex masks.  Pairing two half-edges at v is allowed only if the two chains meet exactly
   in {v}, which forbids cycles and repeated vertices, so every chain is a path at all times.
   Constraints are checked on the chain masks:
     A t a : the path ending at t avoids a (r(t) = 1)
     S p q : no path contains both p and q
     J p q : p and q are the two ends of one path
     R v k : r(v) = k (default r(v) = d(v) mod 2)
   Input: '<graph6> [A t a] [S p q] [J p q] [R v k] ...' per line.
   Output: 'SAT :: p ; p ; ...', 'UNSAT', or 'UNDEC' (node budget, -b).
   A failure memo at vertex boundaries (128-bit hashed keys) is used unless -nomemo is given or a
   J constraint is present. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 32
#define MAXE 256
static int n, m, eu[MAXE], ev[MAXE];
static int inc[MAXN][MAXN], deg[MAXN];       /* incident edge ids */
static int req[MAXN];
static uint32_t avoidof[MAXN], sepof[MAXN];
static int jmate[MAXN];
static int order[MAXN];
/* union-find over edges */
static int par[MAXE];
static uint32_t cmask[MAXE], cavoid[MAXE];
/* decisions: for each half-edge (edge e, side s) : partner edge id (>=0), -2 end, -1 undecided */
static int hpart[MAXE][2];
static long long nodes, budget; static int aborted;
/* undo log */
typedef struct { int kind, a, b; uint32_t m1, m2; int p1; } logent;
static logent lg[MAXE * 8]; static int lgtop;

static int find(int x) { while (par[x] != x) x = par[x]; return x; }
static int side(int e, int v) { return eu[e] == v ? 0 : 1; }

static int ok_mask(uint32_t mk, uint32_t av) {
    if (mk & av) return 0;
    uint32_t x = mk;
    while (x) { int p = __builtin_ctz(x); x &= x - 1; if (sepof[p] & mk) return 0; }
    return 1;
}
/* union two chains (no path compression, union by attaching b under a), log for undo */
static void unite(int ra, int rb) {
    lg[lgtop].kind = 1; lg[lgtop].a = ra; lg[lgtop].b = rb; lg[lgtop].m1 = cmask[ra]; lg[lgtop].m2 = cavoid[ra]; lgtop++;
    par[rb] = ra; cmask[ra] |= cmask[rb]; cavoid[ra] |= cavoid[rb];
}
static void undo_to(int top) {
    while (lgtop > top) {
        lgtop--;
        logent *L = &lg[lgtop];
        if (L->kind == 1) { par[L->b] = L->b; cmask[L->a] = L->m1; cavoid[L->a] = L->m2; }
        else if (L->kind == 2) { cavoid[L->a] = L->m1; }
    }
}
static int solve_vertex(int k);
/* assign half-edges at vertex v = order[k]; idx scans its incident list; endsleft */
static int assign(int k, int idx, int endsleft) {
    int v = order[k];
    while (idx < deg[v] && hpart[inc[v][idx]][side(inc[v][idx], v)] != -1) idx++;
    if (idx == deg[v]) { if (endsleft) return 0; return solve_vertex(k + 1); }
    if (++nodes > budget) { aborted = 1; return 0; }
    int e = inc[v][idx], s = side(e, v);
    /* option 1: an end */
    if (endsleft > 0) {
        int top = lgtop, r = find(e);
        uint32_t av = avoidof[v];
        int ok = 1;
        if (av) {
            if (!ok_mask(cmask[r], cavoid[r] | av)) ok = 0;
            else { lg[lgtop].kind = 2; lg[lgtop].a = r; lg[lgtop].m1 = cavoid[r]; lgtop++; cavoid[r] |= av; }
        }
        if (ok) {
            hpart[e][s] = -2;
            if (assign(k, idx + 1, endsleft - 1)) return 1;
            hpart[e][s] = -1;
        }
        undo_to(top);
        if (aborted) return 0;
    }
    /* option 2: pair with a later undecided half-edge at v */
    int need = deg[v] - idx; (void)need;
    for (int j = idx + 1; j < deg[v]; j++) {
        int f = inc[v][j], t = side(f, v);
        if (hpart[f][t] != -1) continue;
        int ra = find(e), rb = find(f);
        if (ra == rb) continue;
        if ((cmask[ra] & cmask[rb]) != (1u << v)) continue;
        uint32_t mk = cmask[ra] | cmask[rb];
        if (!ok_mask(mk, cavoid[ra] | cavoid[rb])) continue;
        int top = lgtop;
        unite(ra, rb);
        hpart[e][s] = f; hpart[f][t] = e;
        if (assign(k, idx + 1, endsleft)) return 1;
        hpart[e][s] = -1; hpart[f][t] = -1;
        undo_to(top);
        if (aborted) return 0;
    }
    return 0;
}
static int other_end_ok(void) {
    /* J constraints: walk each path */
    for (int p = 0; p < n; p++) if (jmate[p] >= 0) {
        /* find the end half-edge at p */
        int found = 0;
        for (int i = 0; i < deg[p]; i++) {
            int e = inc[p][i];
            if (hpart[e][side(e, p)] != -2) continue;
            /* walk from p along e */
            int cur = e, at = (eu[e] == p) ? ev[e] : eu[e];
            while (1) {
                int s = side(cur, at), nx = hpart[cur][s];
                if (nx == -2) break;
                cur = nx; at = (eu[cur] == at) ? ev[cur] : eu[cur];
            }
            if (at != jmate[p]) return 0;
            found = 1;
        }
        if (!found) return 0;
    }
    return 1;
}
/* failure memo at vertex boundaries: the future depends only on the chains that still have an
   open half-edge (their open half-edges, vertex masks and avoid masks), and on k.  Keys are
   128-bit hashes of that description (collision probability negligible; disabled with J). */
static int usememo, nomemo, posof[MAXN];
#define MB 22
static uint64_t *mk1, *mk2; static unsigned char *mused; static long long mcount;
static uint64_t hmix(uint64_t x) { x ^= x >> 31; x *= 0x7fb5d329728ea185ULL; x ^= x >> 27; x *= 0x81dadef4bc2dd44dULL; x ^= x >> 33; return x; }
static void state_key(int k, uint64_t *h1, uint64_t *h2) {
    static int minopen[MAXE];
    for (int e = 0; e < m; e++) minopen[e] = 1 << 30;
    for (int e = 0; e < m; e++) {
        int open = (posof[eu[e]] >= k) || (posof[ev[e]] >= k);
        if (!open) continue;
        int r = find(e);
        int hid = 2 * e + ((posof[eu[e]] >= k) ? 0 : 1);
        if (hid < minopen[r]) minopen[r] = hid;
    }
    uint64_t a = 0x9e3779b97f4a7c15ULL ^ (uint64_t)k, b = 0xc2b2ae3d27d4eb4fULL + (uint64_t)k;
    for (int e = 0; e < m; e++) for (int sd = 0; sd < 2; sd++) {
        int v = sd ? ev[e] : eu[e];
        if (posof[v] < k) continue;
        int r = find(e);
        uint64_t x = ((uint64_t)(2 * e + sd) << 40) ^ ((uint64_t)minopen[r] << 20) ^ (uint64_t)cmask[r] * 0x100000001b3ULL ^ ((uint64_t)cavoid[r] << 7);
        a = hmix(a ^ x); b = hmix(b + x * 0x2545f4914f6cdd1dULL + 1);
    }
    *h1 = a; *h2 = b;
}
static int memo_find(uint64_t a, uint64_t b) {
    uint64_t j = a & ((1u << MB) - 1);
    for (int i = 0; i < 64; i++, j = (j + 1) & ((1u << MB) - 1)) {
        if (!mused[j]) return 0;
        if (mk1[j] == a && mk2[j] == b) return 1;
    }
    return 0;
}
static void memo_put(uint64_t a, uint64_t b) {
    if (mcount > (long long)((1u << MB) * 0.7)) return;
    uint64_t j = a & ((1u << MB) - 1);
    for (int i = 0; i < 64; i++, j = (j + 1) & ((1u << MB) - 1))
        if (!mused[j]) { mused[j] = 1; mk1[j] = a; mk2[j] = b; mcount++; return; }
}
static int solve_vertex(int k) {
    if (k == n) return other_end_ok();
    int v = order[k];
    if (!usememo || k == 0) return assign(k, 0, req[v]);
    uint64_t a, b; state_key(k, &a, &b);
    if (memo_find(a, b)) return 0;
    int r = assign(k, 0, req[v]);
    if (!r && !aborted) memo_put(a, b);
    return r;
}
static int read_g6(const char *s) {
    n = s[0] - 63; if (n < 1 || n > MAXN) return 0;
    int k = 1, bit = 0, cur = 0; m = 0;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
        if (bit == 0) { if (!s[k]) return 0; cur = s[k++] - 63; bit = 6; }
        bit--;
        if (cur >> bit & 1) { eu[m] = i; ev[m] = j; inc[i][deg[i]++] = m; inc[j][deg[j]++] = m; m++; }
    }
    return 1;
}
static void print_paths(void) {
    printf("SAT ::");
    int first = 1;
    for (int v = 0; v < n; v++) for (int i = 0; i < deg[v]; i++) {
        int e = inc[v][i];
        if (hpart[e][side(e, v)] != -2) continue;
        int other = (eu[e] == v) ? ev[e] : eu[e];
        /* walk; print each path once, from its smaller end */
        int cur = e, at = other;
        while (1) { int s = side(cur, at), nx = hpart[cur][s]; if (nx == -2) break; cur = nx; at = (eu[cur] == at) ? ev[cur] : eu[cur]; }
        if (at < v) continue;
        printf(first ? " %d" : " ; %d", v); first = 0;
        cur = e; at = other;
        while (1) { printf("-%d", at); int s = side(cur, at), nx = hpart[cur][s]; if (nx == -2) break; cur = nx; at = (eu[cur] == at) ? ev[cur] : eu[cur]; }
    }
    printf("\n");
}
int main(int argc, char **argv) {
    budget = 200000000LL;
    for (int i = 1; i < argc; i++) if (!strcmp(argv[i], "-b") && i + 1 < argc) budget = atoll(argv[++i]);
    for (int i = 1; i < argc; i++) if (!strcmp(argv[i], "-nomemo")) nomemo = 1;
    mk1 = malloc(sizeof(uint64_t) << MB); mk2 = malloc(sizeof(uint64_t) << MB); mused = malloc(1u << MB);
    static char line[1 << 16];
    setvbuf(stdout, NULL, _IOLBF, 0);
    while (fgets(line, sizeof line, stdin)) {
        char *tok = strtok(line, " \t\n");
        if (!tok) continue;
        if (!read_g6(tok)) { printf("BAD\n"); continue; }
        for (int v = 0; v < n; v++) { req[v] = deg[v] & 1; avoidof[v] = 0; sepof[v] = 0; jmate[v] = -1; }
        int bad = 0;
        while ((tok = strtok(NULL, " \t\n"))) {
            char *x = strtok(NULL, " \t\n"), *y = strtok(NULL, " \t\n");
            if (!x || !y) { bad = 1; break; }
            int p = atoi(x), q = atoi(y);
            if (!strcmp(tok, "A")) avoidof[p] |= 1u << q;
            else if (!strcmp(tok, "S")) { sepof[p] |= 1u << q; sepof[q] |= 1u << p; }
            else if (!strcmp(tok, "J")) { jmate[p] = q; jmate[q] = p; }
            else if (!strcmp(tok, "R")) req[p] = q;
            else bad = 1;
        }
        for (int v = 0; v < n; v++) {
            if (avoidof[v] && req[v] != 1) bad = 1;
            if (jmate[v] >= 0 && req[v] != 1) bad = 1;
        }
        if (bad) { printf("BAD\n"); continue; }
        int ok = 1;
        for (int v = 0; v < n; v++) if (req[v] > deg[v] || ((deg[v] - req[v]) & 1)) ok = 0;
        /* restarts: attempt 0 uses the deterministic max-cardinality order; later attempts use a
           random start and random tie-breaks, with doubling node budgets.  An exhaustive (not
           aborted) failure under any order is a proof of UNSAT. */
        int r = 0; long long total = 0, per = 100000; unsigned long long rs = 0x1234567ULL;
        aborted = 0;
        for (int att = 0; ok; att++) {
            int done[MAXN] = {0}, cnt[MAXN] = {0};
            for (int k = 0; k < n; k++) {
                int best = -1; unsigned bkey = 0;
                for (int v = 0; v < n; v++) if (!done[v]) {
                    rs = rs * 6364136223846793005ULL + 1442695040888963407ULL;
                    unsigned tie = att ? (unsigned)(rs >> 40) & 1023 : ((avoidof[v] || sepof[v]) ? 1023 : 0);
                    unsigned key = ((unsigned)cnt[v] << 10) | tie;
                    if (best < 0 || key > bkey) { best = v; bkey = key; }
                }
                order[k] = best; done[best] = 1;
                for (int i = 0; i < deg[best]; i++) { int e = inc[best][i]; int o = eu[e] == best ? ev[e] : eu[e]; cnt[o]++; }
            }
            for (int e = 0; e < m; e++) {
                par[e] = e; cmask[e] = (1u << eu[e]) | (1u << ev[e]); cavoid[e] = 0;
                hpart[e][0] = hpart[e][1] = -1;
                if (!ok_mask(cmask[e], 0)) ok = 0;
            }
            if (!ok) break;
            lgtop = 0; nodes = 0; aborted = 0;
            for (int k = 0; k < n; k++) posof[order[k]] = k;
            usememo = !nomemo;
            for (int v = 0; v < n; v++) if (jmate[v] >= 0) usememo = 0;
            if (usememo) { memset(mused, 0, 1u << MB); mcount = 0; }
            long long saveb = budget;
            budget = (total + per > saveb) ? saveb - total : per;
            r = solve_vertex(0);
            total += nodes; budget = saveb;
            if (r || !aborted) break;           /* SAT, or exhaustive UNSAT */
            if (total >= budget) break;         /* give up: UNDEC */
            per *= 2;
        }
        if (r) print_paths();
        else if (aborted) printf("UNDEC\n");
        else printf("UNSAT\n");
    }
    return 0;
}
