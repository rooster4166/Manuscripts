// qb.cpp: batch queries for the far-end oracle: first line graph6, then lines "c A B" (masks).
#include "orcb.h"
int main() { char line[256]; if (!fgets(line, sizeof line, stdin)) return 0; line[strcspn(line, "\r\n")] = 0;
  Gr G; parse_g6(line, G); int c; unsigned A, B;
  while (scanf("%d %u %u", &c, &A, &B) == 3) printf("%d\n", orcb::avoidB(G, c, A, B) == 1); }
