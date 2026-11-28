/* wcheck.c -- independent checker for solver witnesses (conj-r session).  Shares no code with
   lnsolve.  Reads pairs of lines: a query "<g6> [A t a] [S p q] [J p q] [R v k] ..." and the
   solver's answer "SAT <g6> :: p-q-r ; ..." (or UNSAT/UNDEC).  For SAT it checks that the paths
   are simple paths of the graph, use every edge exactly once, give every vertex the required number
   of ends (d(v) mod 2 unless R), that the path ending at t avoids a (A), that no path contains both
   p and q (S), and that p, q are the two ends of one path (J).  Prints counts; any failure is
   printed and makes the exit status 1. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MX 32
static int n, adj[MX][MX], deg[MX], req[MX];
static int nA, At[64], Aa[64], nS, Sp[64], Sq[64], nJ, Jp[64], Jq[64];

static int g6(const char *s) {
    n = s[0] - 63; if (n < 1 || n > MX) return 0;
    memset(adj, 0, sizeof adj); memset(deg, 0, sizeof deg);
    int k = 0, bit = 0, cur = 0; const char *p = s + 1;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
        if (bit == 0) { cur = *p++ - 63; bit = 6; }
        bit--;
        if (cur >> bit & 1) { adj[i][j] = adj[j][i] = 1; deg[i]++; deg[j]++; }
        k++;
    }
    return 1;
}

int main(void) {
    static char q[1 << 16], a[1 << 16];
    long sat = 0, unsat = 0, und = 0, bad = 0;
    while (fgets(q, sizeof q, stdin) && fgets(a, sizeof a, stdin)) {
        char *tok = strtok(q, " \t\n");
        if (!tok || !g6(tok)) { printf("BADQUERY\n"); bad++; continue; }
        char gq[256]; strncpy(gq, tok, 255); gq[255] = 0;
        for (int v = 0; v < n; v++) req[v] = deg[v] % 2;
        nA = nS = nJ = 0; int badtok = 0;
        while ((tok = strtok(NULL, " \t\n"))) {
            int x = atoi(strtok(NULL, " \t\n")), y = atoi(strtok(NULL, " \t\n"));
            if (!strcmp(tok, "A")) { At[nA] = x; Aa[nA++] = y; }
            else if (!strcmp(tok, "S")) { Sp[nS] = x; Sq[nS++] = y; }
            else if (!strcmp(tok, "J")) { Jp[nJ] = x; Jq[nJ++] = y; }
            else if (!strcmp(tok, "R")) req[x] = y;
            else { badtok = 1; }
        }
        if (badtok) { printf("BADQUERYTOKEN %s\n", gq); bad++; continue; }
        if (!strncmp(a, "UNSAT", 5)) { unsat++; continue; }
        if (!strncmp(a, "UNDEC", 5)) { und++; continue; }
        if (strncmp(a, "SAT ", 4)) { printf("BADANSWER %s", a); bad++; continue; }
        char ga[256]; sscanf(a + 4, "%255s", ga);
        if (strcmp(ga, gq)) { printf("MISMATCH %s %s\n", gq, ga); bad++; continue; }
        char *w = strstr(a, "::"); if (!w) { printf("NOWITNESS %s\n", gq); bad++; continue; }
        w += 2;
        /* parse paths */
        static int P[256][MX + 1], L[256]; int np = 0;
        char *save = NULL;
        for (char *ps = strtok_r(w, ";\n", &save); ps; ps = strtok_r(NULL, ";\n", &save)) {
            int len = 0; char *s2 = NULL;
            for (char *vs = strtok_r(ps, "- \t", &s2); vs; vs = strtok_r(NULL, "- \t", &s2)) {
                if (len > MX) break;
                P[np][len++] = atoi(vs);
            }
            if (len) L[np++] = len;
        }
        int used[MX][MX]; memset(used, 0, sizeof used);
        int ends[MX] = {0}, err = 0, ecount = 0, m = 0;
        for (int v = 0; v < n; v++) m += deg[v];
        m /= 2;
        for (int i = 0; i < np && !err; i++) {
            if (L[i] < 2) err = 1;
            int seen[MX] = {0};
            for (int k = 0; k < L[i] && !err; k++) {
                int v = P[i][k];
                if (v < 0 || v >= n || seen[v]) err = 2; else seen[v] = 1;
                if (!err && k > 0) {
                    int u = P[i][k - 1];
                    if (!adj[u][v]) err = 3;
                    else if (used[u][v]) err = 4;
                    else { used[u][v] = used[v][u] = 1; ecount++; }
                }
            }
            if (!err) { ends[P[i][0]]++; ends[P[i][L[i] - 1]]++; }
        }
        if (!err && ecount != m) err = 5;
        for (int v = 0; v < n && !err; v++) if (ends[v] != req[v]) err = 6;
        for (int c = 0; c < nA && !err; c++) {
            for (int i = 0; i < np; i++) {
                if (P[i][0] != At[c] && P[i][L[i] - 1] != At[c]) continue;
                for (int k = 0; k < L[i]; k++) if (P[i][k] == Aa[c]) err = 7;
            }
        }
        for (int c = 0; c < nS && !err; c++) for (int i = 0; i < np; i++) {
            int hp = 0, hq = 0;
            for (int k = 0; k < L[i]; k++) { if (P[i][k] == Sp[c]) hp = 1; if (P[i][k] == Sq[c]) hq = 1; }
            if (hp && hq) err = 8;
        }
        for (int c = 0; c < nJ && !err; c++) {
            int ok = 0;
            for (int i = 0; i < np; i++) {
                int x = P[i][0], y = P[i][L[i] - 1];
                if ((x == Jp[c] && y == Jq[c]) || (x == Jq[c] && y == Jp[c])) ok = 1;
            }
            if (!ok) err = 9;
        }
        if (err) { printf("FAIL %d %s\n", err, gq); bad++; } else sat++;
    }
    printf("witnesses checked %ld, unsat %ld, undecided %ld, failures %ld\n", sat, unsat, und, bad);
    return bad ? 1 : 0;
}
