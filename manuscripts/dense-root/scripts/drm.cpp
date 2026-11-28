// drm.cpp -- the Lovasz + Hall + Phi method for Test1 at roots of degree n-2 (dense-root session).
//
// Input lines: graph6 of J [roots].  z = the unique even vertex of J.  B = J - z, r a root with
// d_J(r) = n - 2 (so d_B(r) = |B| - 2), s its non-neighbour in B, G = B - r, N = V(G) - s.
// A *family* (eulerian-cone Rem. 7.2 / re-tight Lemma 2.1, valid for any B): members Q_x (x in N),
// paths of G with an end at x or trivial, nontrivial ones partitioning E(G); Test1 at r iff some
// family has k - 2 disjoint pairs of vertex-disjoint members (k = |B|/2).
//
// The method searched here: choose g (an even vertex of G of positive degree, or none) and a set
// Phi of vertex-disjoint paths of G pairing up T_g = (even vertices of G) - g; D0 = a Lovasz
// decomposition of G - Phi (every odd vertex an end exactly once, none else).  Each Phi-path is
// either a separate member or appended (forest lift) to the D0-path ending at one of its ends.
// Then every member gets an attachment (an end in N, injective), the other vertices of N are
// trivial members, and we ask for a matching of size k - 2 in the compatibility graph.
//
// Options: -m MODE  (0 = Phi-paths separate members only, 1 = separate or appended at a D0-path
//                   end (forest step); default 1)
//          -L len   (max length of a Phi-path; default 3)
//          -b N     node budget per (root, g, Phi)  (0 = none; UNK when exceeded)
//          -P       Phi = empty only when G has <= 1 even vertex; skip other even choices
//          -G       also let g' range over the odd vertices of G (T = E_G xor {g'})
//          -c       count successful D0 (per root, over all g, Phi) instead of stopping
//          -A       "every D0": report ALLD=1 if some (g, Phi) has every Lovasz D0 succeed
//          -s SEED  randomise the neighbour order and the order of Phi-systems
//          -C CAP   at most CAP Phi-systems per g (default 100000)
//          -d D     roots of degree n - D (default 2); every odd root degree is accepted when
//                   roots are listed on the input line.  For d_J(r) < n - 2 a D0-path or
//                   Phi-path may be *free* (no attachment, a whole path of B avoiding r), and the
//                   count is #pairs + #singletons + #free <= k with #singletons >= 2.
//          -v       print a witness line "W g6 r D0: ... PHI: ..." (J labels)
// Output per root: g6 r YES|NO|UNK how nodes=.. sinZ=[s in N(z)] |EG|=#even vertices of G.
// NO is exhaustive only for the (g, Phi) choices enumerated (paths of length <= L).
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>
#include <string>
#include <algorithm>
using namespace std;
typedef unsigned long long u64;
typedef unsigned __int128 u128;

static int n, A[20][20];
static int optDeg = 2; static int optMode = 1, optLen = 3, optP = 0, optC = 0, optV = 0, optG = 0, optA = 0; static long long nleaf;
static long long budget = 0; static unsigned seed = 0; static int capSys = 100000; static int nperm[20];
static unsigned rng_s = 1; static unsigned rnd() { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 17; rng_s ^= rng_s << 5; return rng_s; }

// current instance
static int nb;               // |B| = 2k
static int K;                // k
static int bv[20];           // B vertex -> J vertex
static int BA[20][20];       // adjacency of B
static int R, S;             // root, non-neighbour (B indices)
static int Nmask;            // N as B-vertex mask
static int ne; static int eu[160], ev_[160], eid[20][20];
static u128 inc[20];
static u128 phiE;            // edges of Phi
static int needEnd[20];      // 1 if odd in G - Phi
static long long nodes; static int aborted, found; static long long nsucc;

// Phi paths
struct QP { int len; int seq[20]; int vm; };
static vector<QP> Qs, witQs;

// D0 paths
static int np; static int plen[40]; static int pseq[40][20]; static int pvm[40];
static int endUsed;          // vertices already ends in D0

static inline int popc(unsigned x) { return __builtin_popcount(x); }
static inline int popc128(u128 x) { return __builtin_popcountll((u64)x) + __builtin_popcountll((u64)(x >> 64)); }

// ---------- matching on members ----------
static int mcnt; static int mvm[40];
static int memo_ok;
// maximum matching size >= need ? (exact, small: recursive)
static int best;
static void mm(int i, int used, int cur, int need) {
    if (best >= need) return;
    if (cur > best) best = cur;
    // upper bound
    int rem = 0; for (int j = i; j < mcnt; j++) if (!(used >> j & 1)) rem++;
    if (cur + rem / 2 <= best) return;
    while (i < mcnt && (used >> i & 1)) i++;
    if (i >= mcnt) return;
    used |= 1 << i;
    for (int j = i + 1; j < mcnt; j++) {
        if ((used >> j & 1) || (mvm[i] & mvm[j])) continue;
        mm(i + 1, used | (1 << j), cur + 1, need);
        if (best >= need) return;
    }
    mm(i + 1, used, cur, need);
}
static int matchOK(int need) { best = 0; mm(0, 0, 0, need); return best >= need; }

// ---------- leaf: Phi placement, designation, matching ----------
// members: built paths with vertex masks and their two ends
static int lm; static int lvm[40], le1[40], le2[40];
static int wit_ok; static int witlm, witvm[40], witused, witnp, witplen[40], witpseq[40][20];

static int freeOK = 0; static int pieceFree[40];
static int tryDesignate(int i, int used) {
    if (i == lm) {
        mcnt = 0; int F = 0;
        for (int j = 0; j < lm; j++) { if (pieceFree[j]) F++; else mvm[mcnt++] = lvm[j]; }
        for (int x = 0; x < nb; x++) if ((Nmask >> x & 1) && !(used >> x & 1)) mvm[mcnt++] = 1 << x;
        int nN = popc(Nmask);
        if (mcnt != nN) return 0;
        int need = nN + F - K; if (need < 0) need = 0;
        if (nN - 2 * need < 2) return 0;
        int ok = matchOK(need);
        if (ok && optV && !wit_ok) { wit_ok = 1; witlm = lm; for (int j = 0; j < lm; j++) { witvm[j] = lvm[j]; }
            witused = used; witnp = np; for (int j = 0; j < np; j++) { witplen[j] = plen[j]; memcpy(witpseq[j], pseq[j], sizeof(int) * (plen[j] + 1)); } }
        return ok;
    }
    int e[2] = {le1[i], le2[i]};
    pieceFree[i] = 0;
    for (int t = 0; t < 2; t++) {
        int a = e[t];
        if (t == 1 && le2[i] == le1[i]) break;
        if (!(Nmask >> a & 1) || (used >> a & 1)) continue;
        if (tryDesignate(i + 1, used | (1 << a))) return 1;
    }
    if (freeOK) { pieceFree[i] = 1; int r1 = tryDesignate(i + 1, used); pieceFree[i] = 0; if (r1) return 1; }
    return 0;
}

static int placeQ(int j) {
    // build member list from D0 paths (with appended Q's) and separate Q's
    if (j == (int)Qs.size()) {
        return tryDesignate(0, 0);
    }
    const QP &q = Qs[j];
    int saveLm = lm;
    // option 0: separate member
    lvm[lm] = q.vm; le1[lm] = q.seq[0]; le2[lm] = q.seq[q.len]; lm++;
    if (placeQ(j + 1)) return 1;
    lm = saveLm;
    if (optMode == 0) return 0;
    // option 1/2: append at an end u of q to the D0-member ending at u
    for (int t = 0; t < 2; t++) {
        int u = t ? q.seq[q.len] : q.seq[0];
        int far = t ? q.seq[0] : q.seq[q.len];
        for (int i = 0; i < lm; i++) {
            if (le1[i] != u && le2[i] != u) continue;
            if ((lvm[i] & q.vm) != (1 << u)) continue;
            int s1 = le1[i], s2 = le2[i], sv = lvm[i];
            if (le1[i] == u) le1[i] = far; else le2[i] = far;
            lvm[i] |= q.vm;
            if (placeQ(j + 1)) return 1;
            le1[i] = s1; le2[i] = s2; lvm[i] = sv;
        }
    }
    return 0;
}

static int leaf() {
    lm = 0;
    for (int i = 0; i < np; i++) { lvm[lm] = pvm[i]; le1[lm] = pseq[i][0]; le2[lm] = pseq[i][plen[i]]; lm++; }
    return placeQ(0);
}

// ---------- Lovasz decomposition search on G - Phi ----------
static int curseq[20], curlen;
static void solve(u128 Rm);
static void extend(u128 Rm, int vmask, int len) {
    if (found && !optC) return;
    if (aborted) return;
    int v = curseq[len];
    if (len > 0 && needEnd[v] && !(endUsed >> v & 1) && v != curseq[0]) {
        // close the path here
        np++;
        plen[np - 1] = len; memcpy(pseq[np - 1], curseq, sizeof(int) * (len + 1)); pvm[np - 1] = vmask;
        int su = endUsed; endUsed |= (1 << curseq[0]) | (1 << v);
        int saved[20]; memcpy(saved, curseq, sizeof(int) * (len + 1));
        solve(Rm);
        memcpy(curseq, saved, sizeof(int) * (len + 1));
        endUsed = su; np--;
        if (found && !optC) return;
    }
    for (int wi = 0; wi < nb; wi++) {
        int w = nperm[wi];
        if (w == R || (vmask >> w & 1)) continue;
        if (!BA[v][w]) continue;
        int e = eid[v][w];
        if (!(Rm >> e & 1)) continue;
        curseq[len + 1] = w;
        extend(Rm & ~((u128)1 << e), vmask | (1 << w), len + 1);
        if (found && !optC) return;
    }
}
static void solve(u128 Rm) {
    if (found && !optC) return;
    nodes++;
    if (budget && nodes > budget) { aborted = 1; return; }
    if (Rm == 0) {
        // all required ends used?
        for (int x = 0; x < nb; x++) if (needEnd[x] && !(endUsed >> x & 1)) return;
        nleaf++;
        if (leaf()) { found = 1; nsucc++; }
        return;
    }
    for (int x = 0; x < nb; x++) if (needEnd[x] && !(endUsed >> x & 1) && !(Rm & inc[x])) return;
    // pick an odd-needed vertex not yet an end with remaining edges
    int v = -1;
    for (int x = 0; x < nb; x++) if (needEnd[x] && !(endUsed >> x & 1) && (Rm & inc[x])) { v = x; break; }
    if (v < 0) return; // remaining edges but no ends available
    curseq[0] = v;
    extend(Rm, 1 << v, 0);
}

// ---------- Phi enumeration ----------
static int gG[20];  // degree in G
static vector<vector<QP>> phis;
static int qseq[20];
static void dfsPaths(int v, int b, int mask, int len, int maxl, vector<QP> &out) {
    if (v == b && len > 0) {
        QP q; q.len = len; memcpy(q.seq, qseq, sizeof(int) * (len + 1)); q.vm = mask; out.push_back(q); return;
    }
    if (len == maxl) return;
    for (int w = 0; w < nb; w++) {
        if (w == R || (mask >> w & 1) || !BA[v][w]) continue;
        qseq[len + 1] = w;
        dfsPaths(w, b, mask | (1 << w), len + 1, maxl, out);
    }
}
// enumerate systems of vertex-disjoint paths pairing up the list T
static void pairSystems(vector<int> T, vector<QP> &cur, int usedmask, vector<vector<QP>> &out, size_t cap) {
    if (out.size() >= cap) return;
    if (T.empty()) { out.push_back(cur); return; }
    int a = T[0];
    for (size_t i = 1; i < T.size(); i++) {
        int b = T[i];
        vector<QP> ps;
        qseq[0] = a;
        dfsPaths(a, b, 1 << a, 0, optLen, ps);
        vector<int> T2;
        for (size_t j = 1; j < T.size(); j++) if (j != i) T2.push_back(T[j]);
        for (auto &q : ps) {
            if (q.vm & usedmask) continue;
            // the other T vertices must not be on q (they need odd Phi-degree 1)
            int bad = 0; for (int t : T2) if (q.vm >> t & 1) bad = 1;
            if (bad) continue;
            cur.push_back(q);
            pairSystems(T2, cur, usedmask | q.vm, out, cap);
            cur.pop_back();
            if (out.size() >= cap) return;
        }
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
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-m")) optMode = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-L")) optLen = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-b")) budget = atoll(argv[++i]);
        else if (!strcmp(argv[i], "-P")) optP = 1;
        else if (!strcmp(argv[i], "-c")) optC = 1;
        else if (!strcmp(argv[i], "-v")) optV = 1;
        else if (!strcmp(argv[i], "-G")) optG = 1;
        else if (!strcmp(argv[i], "-d")) optDeg = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-A")) { optA = 1; optC = 1; }
        else if (!strcmp(argv[i], "-s")) seed = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-C")) capSys = atoi(argv[++i]);
    }
    char line[512];
    while (fgets(line, sizeof line, stdin)) {
        char g6[256]; char rest[256] = "";
        if (sscanf(line, "%255s %255[^\n]", g6, rest) < 1) continue;
        n = parse_g6(g6);
        int deg[20]; int z = -1, nev = 0;
        for (int v = 0; v < n; v++) { deg[v] = 0; for (int w = 0; w < n; w++) deg[v] += A[v][w]; if (deg[v] % 2 == 0) { z = v; nev++; } }
        if (nev != 1) continue;
        vector<int> roots;
        if (rest[0]) { char *p = rest; while (*p) { while (*p == ' ' || *p == ',') p++; if (!*p) break; roots.push_back(strtol(p, &p, 10)); } }
        else for (int v = 0; v < n; v++) if (A[z][v] && deg[v] == n - optDeg) roots.push_back(v);
        // B
        nb = 0; int jb[20];
        for (int v = 0; v < n; v++) if (v != z) { jb[v] = nb; bv[nb++] = v; }
        K = nb / 2;
        for (int i = 0; i < nb; i++) for (int j = 0; j < nb; j++) BA[i][j] = A[bv[i]][bv[j]];
        for (int rj : roots) {
            if (!A[z][rj] || deg[rj] % 2 == 0) { printf("%s %d SKIP\n", g6, rj); continue; }
            R = jb[rj]; S = -1; Nmask = 0;
            for (int x = 0; x < nb; x++) if (x != R) { if (BA[R][x]) Nmask |= 1 << x; else if (S < 0) S = x; }
            freeOK = (deg[rj] < n - 2);
            ne = 0; memset(inc, 0, sizeof inc);
            for (int i = 0; i < nb; i++) for (int j = i + 1; j < nb; j++)
                if (BA[i][j] && i != R && j != R) { eu[ne] = i; ev_[ne] = j; eid[i][j] = eid[j][i] = ne; inc[i] |= (u128)1 << ne; inc[j] |= (u128)1 << ne; ne++; }
            for (int x = 0; x < nb; x++) { gG[x] = 0; for (int y = 0; y < nb; y++) if (y != R && x != R) gG[x] += BA[x][y]; }
            vector<int> EG; for (int x = 0; x < nb; x++) if (x != R && gG[x] > 0 && gG[x] % 2 == 0) EG.push_back(x);
            wit_ok = 0; int allD = 0; string allhow; int ok = 0; long long totnodes = 0; int anyAbort = 0; long long succ = 0;
            string how;
            vector<int> gchoices;
            if (EG.size() <= 1) gchoices.push_back(EG.empty() ? -1 : EG[0]);
            else if (!optP) for (int g : EG) gchoices.push_back(g);
            if (optG) for (int x = 0; x < nb; x++) if (x != R && gG[x] > 0 && gG[x] % 2 == 1) gchoices.push_back(x);
            for (int g : gchoices) {
                vector<int> Tg; for (int x : EG) if (x != g) Tg.push_back(x);
                if (g >= 0 && gG[g] % 2 == 1) Tg.push_back(g);
                vector<vector<QP>> systems; vector<QP> cur;
                pairSystems(Tg, cur, 0, systems, seed ? 1000000 : capSys);
                if (seed) { rng_s = seed * 7919u + 17; for (int x = (int)systems.size() - 1; x > 0; x--) { int y = rnd() % (x + 1); swap(systems[x], systems[y]); } if ((int)systems.size() > capSys) systems.resize(capSys); }
                for (auto &sys : systems) {
                    Qs = sys; phiE = 0;
                    for (auto &q : Qs) for (int i = 0; i < q.len; i++) phiE |= (u128)1 << eid[q.seq[i]][q.seq[i + 1]];
                    for (int x = 0; x < nb; x++) {
                        int d = popc128(inc[x] & ~phiE);
                        needEnd[x] = (x != R) && (d % 2 == 1);
                    }
                    u128 all = 0; for (int e = 0; e < ne; e++) all |= (u128)1 << e;
                    for (int x = 0; x < nb; x++) nperm[x] = x;
                    if (seed) { rng_s = seed * 2654435761u + 12345; for (int x = nb - 1; x > 0; x--) { int y = rnd() % (x + 1); int t = nperm[x]; nperm[x] = nperm[y]; nperm[y] = t; } }
                    np = 0; endUsed = 0; nodes = 0; aborted = 0; found = 0; nsucc = 0; nleaf = 0;
                    solve(all & ~phiE);
                    totnodes += nodes; if (aborted) anyAbort = 1; succ += nsucc;
                    if (optA && !aborted && nleaf > 0 && nsucc == nleaf) { allD = 1; char b2[64]; snprintf(b2, sizeof b2, "g=%d,Q0=%d-%d,len=%d,nD=%lld", g < 0 ? -1 : bv[g], Qs.empty() ? -1 : bv[Qs[0].seq[0]], Qs.empty() ? -1 : bv[Qs[0].seq[Qs[0].len]], Qs.empty() ? 0 : Qs[0].len, nleaf); allhow = b2; }
                    if (found) {
                        ok = 1; if (optV) witQs = Qs;
                        char buf[64]; snprintf(buf, sizeof buf, "g=%d|Phi=%d", g < 0 ? -1 : bv[g], (int)Qs.size());
                        how = buf;
                        if (!optC) break;
                    }
                }
                if (ok && !optC) break;
            }
            int sinZ = A[z][bv[S]];
            if (optV && ok && wit_ok) {
                // D0 paths (J labels) and Phi paths of the winning system are printed; the family is
                // re-derived by the verifier.
                printf("W %s %d D0:", g6, rj);
                for (int j = 0; j < witnp; j++) { printf(" "); for (int t = 0; t <= witplen[j]; t++) printf("%s%d", t ? "," : "", bv[witpseq[j][t]]); }
                printf(" PHI:");
                for (auto &q : witQs) { printf(" "); for (int t = 0; t <= q.len; t++) printf("%s%d", t ? "," : "", bv[q.seq[t]]); }
                printf("\n");
            }
            if (optA) printf("%s %d %s ALLD=%d %s sinZ=%d |EG|=%d\n", g6, rj, ok ? "YES" : (anyAbort ? "UNK" : "NO"), allD, allhow.c_str(), sinZ, (int)EG.size());
            else if (optC) printf("%s %d %s succ=%lld nodes=%lld sinZ=%d |EG|=%d\n", g6, rj, ok ? "YES" : (anyAbort ? "UNK" : "NO"), succ, totnodes, sinZ, (int)EG.size());
            else printf("%s %d %s %s nodes=%lld sinZ=%d |EG|=%d\n", g6, rj, ok ? "YES" : (anyAbort ? "UNK" : "NO"), how.c_str(), totnodes, sinZ, (int)EG.size());
            fflush(stdout);
        }
    }
    return 0;
}
