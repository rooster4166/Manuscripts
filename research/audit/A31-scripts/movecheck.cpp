// movecheck.cpp (auditor, conj-n audit): soundness of every move and base case of ext.h.
// For every graph on stdin (graph6, at most one even vertex), every odd c, every A (|A| <= maxA),
// every B (odd, outside A + c, |B| <= maxB):
//   - if xbase(G,c,A,B) then the exact oracle must say good;
//   - for every child of xchildren (all moves, including (t) when -T/-T2 is given):
//     child good (oracle) must imply parent good (oracle).
// Violations are counted per move letter and printed.  The oracle is orcb::avoidB (validated
// against full enumeration by xcheckb.py; re-run in this audit).
// build: g++ -O2 -I <conj-n/scripts> -I <l1-induction/scripts> -o movecheck movecheck.cpp
// usage: movecheck [-a maxA] [-b maxB] [-T|-T2] [-L leafpathlen] < graph6
#include "ext.h"
int main(int argc, char** argv) {
  int maxA = 99, maxB = 99;
  for (int i = 1; i < argc; i++) {
    std::string a = argv[i];
    if (a == "-a") maxA = atoi(argv[++i]);
    else if (a == "-b") maxB = atoi(argv[++i]);
    else if (a == "-T") XMV_TR = 1;
    else if (a == "-T2") XMV_TR = 2;
    else if (a == "-L") XMV_LEAFPATH_MAXLEN = atoi(argv[++i]);
  }
  std::map<char, long long> tested, viol, applied; long long inst = 0, basec = 0, baseviol = 0, good = 0;
  char line[256]; int pr = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0; if (!line[0]) continue;
    Gr G; if (!parse_g6(line, G)) continue;
    if (__builtin_popcount(G.evens()) > 1) continue;
    uint32_t odd = odd_mask(G);
    for (int c = 0; c < G.N; c++) {
      if (!(odd >> c & 1)) continue;
      uint32_t U = ((1u << G.N) - 1) & ~(1u << c);
      for (uint32_t A = U;; A = (A - 1) & U) {
        if (__builtin_popcount(A) <= maxA) {
          uint32_t UB = odd & ~A & ~(1u << c);
          for (uint32_t B = UB;; B = (B - 1) & UB) {
            if (__builtin_popcount(B) <= maxB) {
              inst++;
              int p = xgood(G, c, A, B);
              if (p == 1) good++;
              if (xbase(G, c, A, B)) { basec++; if (p != 1) { baseviol++; if (pr++ < 40) { printf("BASEVIOL %s ", line); xpr(stdout, G, c, A, B); printf(" oracle=%d\n", p); } } }
              std::vector<XInst> ch; xchildren(G, c, A, B, ch);
              for (auto& x : ch) {
                Gr H; int c2; uint32_t A2, B2; xcompact(x.G, x.c, x.A, x.B, H, c2, A2, B2);
                applied[x.mv]++;
                if (A2 >> c2 & 1) continue;
                int q = xgood(H, c2, A2, B2);
                if (q != 1) continue;
                tested[x.mv]++;
                if (p != 1) { viol[x.mv]++; if (pr++ < 40) { printf("VIOL --%c-- %s ", x.mv, line); xpr(stdout, G, c, A, B); printf(" parent=%d child: ", p); xpr(stdout, H, c2, A2, B2); printf("\n"); } }
              }
            }
            if (B == 0) break;
          }
        }
        if (A == 0) break;
      }
    }
  }
  printf("MOVECHECK instances=%lld good=%lld base=%lld baseviol=%lld\n", inst, good, basec, baseviol);
  for (auto& kv : applied) printf("  move %c: applied=%lld child_good=%lld violations=%lld\n", kv.first, kv.second, tested[kv.first], viol[kv.first]);
}
