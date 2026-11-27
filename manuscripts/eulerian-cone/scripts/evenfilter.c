/* evenfilter.c: copy the graph6 lines of stdin whose every vertex degree is even (n <= 62). */
#include <stdio.h>
#include <string.h>
int main(void) {
    char line[4096];
    while (fgets(line, sizeof line, stdin)) {
        int n = line[0] - 63, deg[64] = {0}, bit = 0, cur = 0, k = 1;
        if (n < 1 || n > 62) continue;
        for (int j = 1; j < n; j++)
            for (int i = 0; i < j; i++) {
                if (bit == 0) { cur = line[k++] - 63; bit = 6; }
                bit--;
                if (cur >> bit & 1) { deg[i]++; deg[j]++; }
            }
        int ok = 1;
        for (int v = 0; v < n; v++) if (deg[v] & 1) { ok = 0; break; }
        if (ok) fputs(line, stdout);
    }
    return 0;
}
