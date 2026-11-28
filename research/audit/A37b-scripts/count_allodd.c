/* count_allodd.c -- audit A37b: own filter for connected graphs with all degrees odd (graph6 on
   stdin, n <= 16); writes them to stdout with "m" appended, and counts on stderr, per graph and in
   total, P2 = #unordered pairs of disjoint non-adjacent vertex pairs and P3 = #triples. */
#include <stdio.h>
#include <string.h>
int main(void) {
    char line[256]; long long ng = 0, P2 = 0, P3 = 0;
    while (fgets(line, sizeof line, stdin)) {
        line[strcspn(line, "\r\n")] = 0;
        int n = line[0] - 63, A[16] = {0}, k = 0, bit = 0, cur = 0, m = 0;
        for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
            if (!bit) { cur = line[1 + k++] - 63; bit = 6; }
            bit--;
            if (cur >> bit & 1) { A[i] |= 1 << j; A[j] |= 1 << i; m++; }
        }
        int ok = 1;
        for (int v = 0; v < n; v++) if (!(__builtin_popcount(A[v]) & 1)) ok = 0;
        if (!ok) continue;
        int seen = 1, fr = 1;
        while (fr) { int v = __builtin_ctz(fr); fr &= fr - 1; int nb = A[v] & ~seen; seen |= nb; fr |= nb; }
        if (seen != (1 << n) - 1) continue;
        ng++;
        int pa[128], pb[128], np = 0;
        for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) if (!(A[a] >> b & 1)) { pa[np] = a; pb[np] = b; np++; }
        long long p2 = 0, p3 = 0;
        for (int i = 0; i < np; i++) for (int j = i + 1; j < np; j++) {
            int mi = 1 << pa[i] | 1 << pb[i], mj = 1 << pa[j] | 1 << pb[j];
            if (mi & mj) continue;
            p2++;
            for (int l = j + 1; l < np; l++) {
                int ml = 1 << pa[l] | 1 << pb[l];
                if ((mi | mj) & ml) continue;
                p3++;
            }
        }
        P2 += p2; P3 += p3;
        printf("%s %d %lld %lld\n", line, m, p2, p3);
    }
    fprintf(stderr, "graphs %lld P2 %lld P3 %lld => F2 %lld X2 %lld XF %lld F3 %lld X3 %lld XF2 %lld total %lld\n",
            ng, P2, P3, P2, 4 * P2, 4 * P2, P3, 8 * P3, 6 * P3, 9 * P2 + 15 * P3);
    return 0;
}
