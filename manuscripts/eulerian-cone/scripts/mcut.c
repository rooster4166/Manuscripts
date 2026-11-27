/* mcut.c: for each graph6 line, print the line followed by 1 if the graph has a matching cut
   (a bipartition (X, V-X), both sides nonempty, every vertex with at most one neighbour on the
   other side), else 0.  n <= 20; exhaustive over X containing vertex 0. */
#include <stdio.h>
#include <string.h>
int main(void) {
    char line[4096];
    while (fgets(line, sizeof line, stdin)) {
        line[strcspn(line, "\r\n")] = 0;
        int n = line[0] - 63, bit = 0, cur = 0, k = 1;
        unsigned adj[32] = {0};
        for (int j = 1; j < n; j++)
            for (int i = 0; i < j; i++) {
                if (bit == 0) { cur = line[k++] - 63; bit = 6; }
                bit--;
                if (cur >> bit & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
            }
        unsigned full = (1u << n) - 1;
        int found = 0;
        for (unsigned X = 1; X < full && !found; X += 2) { /* vertex 0 in X */
            unsigned Y = full & ~X;
            int ok = 1;
            for (int v = 0; v < n && ok; v++) {
                unsigned other = (X >> v & 1) ? Y : X;
                if (__builtin_popcount(adj[v] & other) > 1) ok = 0;
            }
            if (ok) found = 1;
        }
        printf("%s %d\n", line, found);
    }
    return 0;
}
