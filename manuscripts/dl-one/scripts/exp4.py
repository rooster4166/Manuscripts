"""exp4.py: CN1 core instances, target a, child G' = G - ga (a even).  For candidate properties
of D' measure: exists (some D' has it) and sufficient (every D' with it transfers to a good D).
  sep     : no path contains both a and b
  far     : the far end of Q'(b) is not in N_G'(a) + {g}
  gq      : Q'(g) avoids a and Q'(g) != Q'(b)
  ae      : Q'(b) avoids a
"""
import sys
from collections import Counter
import dllib

def main():
    cap = int(sys.argv[2]) if len(sys.argv) > 2 else 100000
    only_cn1 = "--all" not in sys.argv
    C = Counter()
    for line in open(sys.argv[1]):
        g6 = line.strip()
        if not g6:
            continue
        n, E = dllib.g6_decode(g6)
        ev = dllib.even_vertices(n, E)
        if len(ev) != 1:
            continue
        g = ev[0]
        A = dllib.adjsets(n, E)
        d = dllib.degrees(n, E)
        for a in sorted(A[g]):
            for b in sorted(A[g]):
                if a == b or not (d[a] % 2 and d[b] % 2) or b in A[a]:
                    continue
                if only_cn1 and (A[a] & A[b]) != {g}:
                    continue
                if dllib.univ_twins(n, E, a, b) or d[a] == 1 or d[b] == 1:
                    continue
                K = dllib.remove_edge(E, g, a)
                Ka = A[a] - {g}
                Ds, comp = dllib.enum_decomps(n, K, cap)
                if not comp:
                    C["undec"] += 1
                    continue
                C["inst"] += 1
                props = {"sep": [], "far": [], "gq": [], "ae": [], "sep+far": [], "sep+gq": [], "ae+far": []}
                for Dp in Ds:
                    D, chain = dllib.fan_transfer(Dp, g, a)
                    good = dllib.dl_good(D, a, b)
                    qb = dllib.Q(Dp, b)
                    beta = qb[0] if qb[-1] == b else qb[-1]
                    sep = not any(a in P and b in P for P in Dp)
                    far = beta not in Ka and beta != g
                    qg = dllib.Q(Dp, g)
                    gq = a not in qg and qg is not qb
                    ae = a not in qb
                    for k, v in (("sep", sep), ("far", far), ("gq", gq), ("ae", ae), ("sep+far", sep and far),
                                 ("sep+gq", sep and gq), ("ae+far", ae and far)):
                        if v:
                            props[k].append(good)
                for k, L in props.items():
                    if L:
                        C["ex_" + k] += 1
                        if all(L):
                            C["suff_" + k] += 1
                if not props["sep+far"]:
                    print("NO_SEPFAR", g6, "g=%d a=%d b=%d" % (g, a, b), flush=True)
    for k in sorted(C):
        print(k, C[k])

main()
