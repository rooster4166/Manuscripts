/* allodd.c: filter graph6 lines to graphs with every degree odd. */
#include <stdio.h>
#include <string.h>
int main(void) {
  char s[256];
  while (fgets(s, sizeof s, stdin)) {
    int len = strlen(s); while (len && (s[len-1] == '\n' || s[len-1] == '\r')) s[--len] = 0;
    int n = s[0] - 63, deg[64] = {0}, p = 1, bit = 0, val = 0;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
      if (bit == 0) { val = s[p++] - 63; bit = 6; }
      bit--; if (val >> bit & 1) { deg[i]++; deg[j]++; }
    }
    int ok = 1; for (int v = 0; v < n; v++) if (deg[v] % 2 == 0) { ok = 0; break; }
    if (ok) puts(s);
  }
  return 0;
}
