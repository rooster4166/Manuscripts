/* count_odd.c -- A40: pass graph6 lines (n <= 62) whose degrees are all odd; count on stderr. */
#include <stdio.h>
int main(void) {
    static char s[8192]; long tot = 0, kept = 0;
    while (fgets(s, sizeof s, stdin)) {
        int n = s[0] - 63, d[64] = {0}, k = 1, b = 0, x = 0; tot++;
        for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
            if (!b) { x = s[k++] - 63; b = 6; }
            if ((x >> --b) & 1) { d[i]++; d[j]++; }
        }
        int ok = 1; for (int v = 0; v < n; v++) if (d[v] % 2 == 0) ok = 0;
        if (ok) { kept++; fputs(s, stdout); }
    }
    fprintf(stderr, "read %ld all-odd %ld\n", tot, kept);
    return 0;
}
