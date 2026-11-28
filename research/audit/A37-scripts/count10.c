/* count10.c (audit A37, item 3c): independent count of the (T2) instances.
   Reads graph6 (n <= 16) on stdin.  Keeps graphs with exactly two even-degree vertices, adjacent,
   that are 3-connected (n >= 4 and no vertex set of size <= 2 disconnects).  Prints the number of
   such graphs and, per d(z), the number of instances (both orientations), and writes the kept
   graph6 lines to stdout if argv[1] == "-p".  Written for the audit; shares no code with t2.c. */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

static int n, adj[16];

static int parse(const char *s) {
  n = s[0] - 63;
  if (n < 1 || n > 16) return 0;
  memset(adj, 0, sizeof adj);
  int k = 0, len = strlen(s);
  for (int j = 1; j < n; j++)
    for (int i = 0; i < j; i++, k++) {
      int byte = 1 + k / 6, bit = 5 - k % 6;
      if (byte >= len) return 0;
      if (((s[byte] - 63) >> bit) & 1) { adj[i] |= 1 << j; adj[j] |= 1 << i; }
    }
  return 1;
}

static int conn_without(int rem) {
  int all = ((1 << n) - 1) & ~rem;
  if (!all) return 1;
  int start = all & -all, seen = start, stack = start;
  while (stack) {
    int v = __builtin_ctz(stack); stack &= stack - 1;
    int nb = adj[v] & all & ~seen;
    seen |= nb; stack |= nb;
  }
  return seen == all;
}

int main(int argc, char **argv) {
  int pr = argc > 1 && !strcmp(argv[1], "-p");
  char line[256];
  long long graphs = 0, inst[17] = {0}, read = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0;
    if (!parse(line)) continue;
    read++;
    int ev[16], ne = 0;
    for (int v = 0; v < n; v++) if (__builtin_popcount(adj[v]) % 2 == 0) ev[ne++] = v;
    if (ne != 2 || !((adj[ev[0]] >> ev[1]) & 1)) continue;
    if (n < 4) continue;
    int ok = conn_without(0);
    for (int a = 0; ok && a < n; a++) {
      if (!conn_without(1 << a)) ok = 0;
      for (int b = a + 1; ok && b < n; b++) if (!conn_without((1 << a) | (1 << b))) ok = 0;
    }
    if (!ok) continue;
    graphs++;
    inst[__builtin_popcount(adj[ev[0]])]++;
    inst[__builtin_popcount(adj[ev[1]])]++;
    if (pr) puts(line);
  }
  fprintf(stderr, "read %lld graphs; kept %lld graphs\n", read, graphs);
  long long tot = 0;
  for (int d = 0; d <= 16; d++) if (inst[d]) { fprintf(stderr, "  d(z)=%d: %lld instances\n", d, inst[d]); tot += inst[d]; }
  fprintf(stderr, "  total instances %lld\n", tot);
  return 0;
}
