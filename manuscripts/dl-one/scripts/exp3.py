"""exp3.py: CN1 core instances (N(a) & N(b) = {g}).  Target a: for every separating Lovasz
decomposition D' of G - ga (no path contains both a and b), transfer g -> a; if the result D is
bad, try one end exchange at a or at b: for a path R != Q(a) through a, split R at a and join
Q(a) with one half when they meet only in a; the other half becomes Q(a).  Report instances where
some bad D cannot be repaired by one exchange."""
import sys
from collections import Counter
import dllib

def exchanges(D, v):
    """all decompositions obtained by one end exchange at v"""
    qi = dllib.endpath(D, v)
    Pq = D[qi]
    if Pq[-1] != v:
        Pq = Pq[::-1]      # Pq ends at v
    for ri, R in enumerate(D):
        if ri == qi or v not in R or R[0] == v or R[-1] == v:
            continue
        k = R.index(v)
        H1, H2 = R[:k + 1], R[k:]       # H1 ends at v, H2 starts at v
        for keep, join in ((H2, H1), (H1, H2)):
            jn = join if join[0] == v else join[::-1]   # starts at v
            if set(Pq) & set(jn) == {v}:
                newP = Pq + jn[1:]
                D2 = [P for i, P in enumerate(D) if i not in (qi, ri)] + [newP, keep]
                yield D2

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
        for a in sorted(A[g]):
            for b in sorted(A[g]):
                if a == b or not (d[a] % 2 and d[b] % 2) or b in A[a] or (A[a] & A[b]) != {g}:
                    continue
                if d[a] == 1 or d[b] == 1:
                    continue
                K = dllib.remove_edge(E, g, a)
                Ds, comp = dllib.enum_decomps(n, K, cap)
                if not comp:
                    C["undec"] += 1
                    continue
                C["inst"] += 1
                nsep = nbad = nunrep = 0
                for Dp in Ds:
                    if any(a in P and b in P for P in Dp):
                        continue
                    nsep += 1
                    D, chain = dllib.fan_transfer(Dp, g, a)
                    if dllib.dl_good(D, a, b):
                        continue
                    nbad += 1
                    rep = any(dllib.dl_good(D2, a, b) for v in (a, b) for D2 in exchanges(D, v))
                    if not rep:
                        nunrep += 1
                        if nunrep == 1:
                            print("UNREP", g6, "g=%d a=%d b=%d" % (g, a, b), "D'=", Dp, "chain", chain, "D=", D, flush=True)
                C["sep_D"] += nsep
                C["bad_D"] += nbad
                C["unrep_D"] += nunrep
                C["inst_with_unrep"] += nunrep > 0
    print(dict(C))

main()
