"""exp2.py: target a (delete ga) for core instances.  Child G' = G - ga, where a is even.
For each D' of G' record:
  AE  : a not in Q'(b)          (b's path avoids the even vertex a)
  NP  : Q'(b) != Q'(x_k)        (the chain from g toward a does not stop at b's partner)
  good: the transfer is DL-good (= (b not in Q'(x_k)) or (AE and NP)).
Statistics per instance: exists AE; every AE D' good; exists good; for the symmetric target b too.
"""
import sys
from collections import Counter
import dllib

def analyse(n, E, g, a, b, cap):
    K = dllib.remove_edge(E, g, a)
    Ds, comp = dllib.enum_decomps(n, K, cap)
    if not comp:
        return None
    st = Counter()
    for Dp in Ds:
        D, chain = dllib.fan_transfer(Dp, g, a)
        xk = chain[-1]
        qb = dllib.Q(Dp, b)
        qx = dllib.Q(Dp, xk)
        ae = a not in qb
        np_ = qb is not qx
        good = dllib.dl_good(D, a, b)
        assert good == ((b not in qx) or (ae and np_)), (Dp, D, chain)
        st["D"] += 1
        st["AE"] += ae
        st["good"] += good
        st["AEbad"] += ae and not good
        st["sep"] += all(not (a in P and b in P) for P in Dp)
        st["sepbad"] += all(not (a in P and b in P) for P in Dp) and not good
    return st

def main():
    cap = int(sys.argv[2]) if len(sys.argv) > 2 else 100000
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
        Nb = sorted(A[g])
        for a in Nb:
            for b in Nb:
                if a == b or not (d[a] % 2 and d[b] % 2) or b in A[a]:
                    continue
                if dllib.univ_twins(n, E, a, b):
                    continue
                st = analyse(n, E, g, a, b, cap)   # ordered: target a, and b's path
                if st is None:
                    C["undec"] += 1
                    continue
                C["ord_inst"] += 1
                C["exAE"] += st["AE"] > 0
                C["exgood"] += st["good"] > 0
                C["AE_all_good"] += st["AE"] > 0 and st["AEbad"] == 0
                cn = A[a] & A[b]
                if cn == {g}:
                    C["cn1"] += 1
                    C["cn1_exsep"] += st["sep"] > 0
                    C["cn1_sep_all_good"] += st["sep"] > 0 and st["sepbad"] == 0
                if st["AE"] == 0:
                    print("NOAE", g6, "g=%d a=%d b=%d" % (g, a, b), "da=%d db=%d" % (d[a], d[b]), "cn", sorted(cn))
    print(dict(C))

main()
