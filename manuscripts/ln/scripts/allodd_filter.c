/* allodd_filter.c -- pass through graph6 lines whose degrees are all odd (n <= 62). */
#include <stdio.h>
#include <string.h>
int main(void) {
    char s[4096];
    while (fgets(s, sizeof s, stdin)) {
        int n = s[0] - 63, deg[64] = {0}, bit = 0, cur = 0, k = 1;
        for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
            if (bit == 0) { cur = s[k++] - 63; bit = 6; }
            bit--;
            if (cur >> bit & 1) { deg[i]++; deg[j]++; }
        }
        int ok = 1;
        for (int v = 0; v < n; v++) if (!(deg[v] & 1)) { ok = 0; break; }
        if (ok) fputs(s, stdout);
    }
    return 0;
}
