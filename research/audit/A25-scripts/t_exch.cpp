// t_exch.cpp: independent check of Lemma 4.2 (exchange at c) and of the coverage counts of section 4.
// For every G with one even vertex g, odd c notin N(g), A = Amax, tight x in N(g) cap N(c), and every
// good D' of G - gx (a25 enumerator, pruned on Q'_c avoiding A):
//   AV   : forced chain g -> x avoids c (Lemma 2.2);
//   EX   : chain first meets c at step i >= 1, Q'_c avoids x, V(P) cap V(Q'_c) = {c} for the path P
//          of D' ending at x_{i-1}.  For every EX case the exchange is PERFORMED on the Fan image:
//          the image must contain P' (ends c, f; V(P') = V(P)) and R = Q'_c + cx (ends q, x); replace
//          them by cx and P' u Q'_c and check that the result is a Lovász decomposition of G with
//          Q_c = cx.  Also checks the intermediate claims (chain stops at c, P' has V(P') = V(P)).
//   REST : neither; record whether the Fan image is good.
// Also (static condition (3), TF Thm 3.3) implies (1): checked on every D'.
#include "a25.h"
#include <iostream>
using namespace a25;
int main() {
  long long nAV = 0, nEX = 0, nREST = 0, nRESTgood = 0, exch_ok = 0, exch_bad = 0, claims_bad = 0, static_not_AV = 0, nstatic = 0;
  std::string line;
  while (std::getline(std::cin, line)) {
    Graph G; if (!decode_g6(line, G)) continue;
    if (__builtin_popcount(G.evenset()) != 1) continue;
    int g = theeven(G);
    for (int c = 0; c < G.n; c++) {
      if (G.deg(c) % 2 == 0 || G.has(g, c)) continue;
      uint32_t A = amax(G, c);
      for (int x = 0; x < G.n; x++) if (G.has(g, x) && G.has(c, x)) {
        Graph H = G; H.rem(g, x);
        enumerate(H, nullptr, [&](const Dec& D) {
          int qc = path_ending_at(D, c); if (qc < 0 || (vset(D[qc]) & A)) return false;
          Dec D2; std::vector<int> ch;
          if (!forced_chain(D, g, x, D2, ch)) { claims_bad++; return false; }
          // static condition of TF Thm 3.3 (leaf graph at c): no vertex of {g} + N_H(x) has c as its
          // predecessor of x, read on its path (the leaf path ends at the far end of Q'_c and at l)
          bool stat = true;
          for (int v = 0; v < G.n; v++) if (v == g || H.has(v, x)) {
            int pi = path_ending_at(D, v); if (pi < 0) continue;
            if (v == c) continue;  // in the leaf graph c has no end
            Path P = D[pi]; if (P.front() != v) std::reverse(P.begin(), P.end());
            for (size_t j = 1; j < P.size(); j++) if (P[j] == x && P[j - 1] == c) stat = false;
          }
          auto it = std::find(ch.begin(), ch.end(), c);
          if (stat) { nstatic++; if (it != ch.end()) static_not_AV++; }
          if (it == ch.end()) { nAV++; return false; }
          int i = (int)(it - ch.begin());
          int xp = ch[i - 1];
          int pp = path_ending_at(D, xp);
          bool qcx = (vset(D[qc]) >> x) & 1u;
          if (!qcx && pp != qc && (vset(D[pp]) & vset(D[qc])) == (1u << c)) {
            nEX++;
            // claims: the chain stops at c
            if ((int)ch.size() != i + 1) claims_bad++;
            // locate P' (ends c and f, V = V(P)) and R = Q'_c + cx in the image
            int iP = -1, iR = -1; uint32_t VP = vset(D[pp]), VR = vset(D[qc]) | (1u << x);
            for (size_t j = 0; j < D2.size(); j++) { uint32_t s = vset(D2[j]);
              if (s == VP && (D2[j].front() == c || D2[j].back() == c)) iP = (int)j;
              if (s == VR && (D2[j].front() == x || D2[j].back() == x)) iR = (int)j; }
            if (iP < 0 || iR < 0) { claims_bad++; exch_bad++; return false; }
            Path Pp = D2[iP]; if (Pp.back() != c) std::reverse(Pp.begin(), Pp.end());   // f ... c
            Path Q = D[qc]; if (Q.front() != c) std::reverse(Q.begin(), Q.end());       // c ... q
            Path Sx = Pp; for (size_t j = 1; j < Q.size(); j++) Sx.push_back(Q[j]);
            Dec E; for (size_t j = 0; j < D2.size(); j++) if ((int)j != iP && (int)j != iR) E.push_back(D2[j]);
            E.push_back(Path{c, x}); E.push_back(Sx);
            int q2 = path_ending_at(E, c);
            if (check(G, E) && q2 >= 0 && E[q2].size() == 2) exch_ok++; else { exch_bad++; printf("EXCH-FAIL %s c=%d x=%d D'=%s\n", line.c_str(), c, x, dstr(D).c_str()); }
            return false;
          }
          nREST++;
          int q2 = path_ending_at(D2, c); if (q2 >= 0 && !(vset(D2[q2]) & A)) nRESTgood++;
          return false; }, c, A);
      }
    }
  }
  printf("good D' at tight targets: %lld  AV=%lld EX=%lld REST=%lld (REST with good Fan image %lld)\n", nAV + nEX + nREST, nAV, nEX, nREST, nRESTgood);
  printf("exchange performed: ok %lld, failed %lld; intermediate-claim failures %lld\n", exch_ok, exch_bad, claims_bad);
  printf("static condition (TF Thm 3.3) holds for %lld D'; of these with chain through c: %lld\n", nstatic, static_not_AV);
}
