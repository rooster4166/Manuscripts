"""exp5.py: CN1 instances, d(a) >= 3.  For every separating Lovasz decomposition D' of G - ga
(no path contains both a and b), test the two ways of restoring ga:
  O1: Fan's forced chain g -> a;  good iff the result is DL-good;
  O2: some path R through a (a interior) has a half R_i with V(R_i) & V(Q'(g)) = {} ;
      then R_i + ag + Q'(g) is a path, Q(a) = the other half, which avoids b.
Count separating D' for which neither works."""
import sys
from collections import Counter
import dllib

def o2(Dp, a, g):
    qg = dllib.Q(Dp, g)
    S = set(qg)
    for R in Dp:
        if a in R and R[0] != a and R[-1] != a and R is not qg:
            k = R.index(a)
            if not (set(R[:k + 1]) & S) or not (set(R[k:]) & S):
                return True
    return False

def main():
    cap = int(sys.argv[2]) if len(sys.argv) > 2 else 100000
    C = Counter()
    for line in open(sys.argv[1]):
        s = line.strip()
        if not s:
            continue
        n, E = dllib.g6_decode(s)
        ev = dllib.even_vertices(n, E)
        if len(ev) != 1:
            continue
        g = ev[0]
        A = dllib.adjsets(n, E)
        d = dllib.degrees(n, E)
        for a in sorted(A[g]):
            for b in sorted(A[g]):
                if a == b or not (d[a] % 2 and d[b] % 2) or b in A[a] or (A[a] & A[b]) != {g}:
                    continue
                if d[a] < 3:
                    continue
                K = dllib.remove_edge(E, g, a)
                Ds, comp = dllib.enum_decomps(n, K, cap)
                if not comp:
                    C["undec"] += 1
                    continue
                C["inst"] += 1
                bad = 0
                for Dp in Ds:
                    if any(a in P and b in P for P in Dp):
                        continue
                    C["sepD"] += 1
                    D, chain = dllib.fan_transfer(Dp, g, a)
                    g1 = dllib.dl_good(D, a, b)
                    g2 = o2(Dp, a, g)
                    C["o1"] += g1
                    C["o2"] += g2
                    if not g1 and not g2:
                        bad += 1
                        if bad == 1:
                            print("NEITHER", s, "g=%d a=%d b=%d" % (g, a, b), Dp, flush=True)
                C["inst_bad"] += bad > 0
                C["badD"] += bad
    print(dict(C))

main()
