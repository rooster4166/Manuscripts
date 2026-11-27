/* evenn2.c -- A31 audit: graph6 filter.  Keeps graphs of even order n in which every degree is
   even and some vertex has degree n - 2.  With -n2c keeps only those that are NOT 2-connected
   (disconnected, or with a cut vertex). */
#include <stdio.h>
#include <string.h>

static int n, A[16][16];

static int conn_without(int x) {
    int seen[16] = {0}, st[16], sp = 0, cnt = 0, tot = 0, s = -1;
    for (int v = 0; v < n; v++) if (v != x) { tot++; if (s < 0) s = v; }
    if (s < 0) return 1;
    seen[s] = 1; st[sp++] = s; cnt = 1;
    while (sp) {
        int v = st[--sp];
        for (int w = 0; w < n; w++)
            if (w != x && A[v][w] && !seen[w]) { seen[w] = 1; st[sp++] = w; cnt++; }
    }
    return cnt == tot;
}

int main(int argc, char **argv) {
    int n2c = argc > 1 && !strcmp(argv[1], "-n2c");
    char line[256];
    while (fgets(line, sizeof line, stdin)) {
        line[strcspn(line, "\r\n")] = 0;
        if (!line[0] || line[0] == '>') continue;
        n = line[0] - 63;
        if (n < 2 || n > 16 || n % 2) continue;
        memset(A, 0, sizeof A);
        int p = 1, bit = 0, x = 0;
        for (int j = 1; j < n; j++)
            for (int i = 0; i < j; i++) {
                if (bit == 0) { x = line[p++] - 63; bit = 6; }
                bit--;
                if (x >> bit & 1) A[i][j] = A[j][i] = 1;
            }
        int ok = 1, has = 0;
        for (int v = 0; v < n && ok; v++) {
            int d = 0;
            for (int w = 0; w < n; w++) d += A[v][w];
            if (d & 1) ok = 0;
            if (d == n - 2) has = 1;
        }
        if (!ok || !has) continue;
        if (n2c) {
            int two = conn_without(-1);
            for (int v = 0; v < n && two; v++) if (!conn_without(v)) two = 0;
            if (two) continue;
        }
        puts(line);
    }
    return 0;
}
