"""Independent check of the R2 strengthening (Section 7): some Lovasz decomposition has Q(y) avoiding
x and xy as the terminal edge of Q(x) at x.  All NA instances of the given graphs."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import indep
tot = good = 0
for line in sys.stdin:
    G = indep.read_g6(line)
    if any(len(G[v]) % 2 == 0 for v in G):
        continue
    lds = None
    for y in G:
        for x in G[y]:
            if not any(w != x and w not in G[x] for w in G[y]):
                continue
            if lds is None:
                lds = indep.all_lovasz(G)
            tot += 1
            ok = False
            for D in lds:
                Qy = [P for P in D if y in (P[0], P[-1])][0]
                Qx = [P for P in D if x in (P[0], P[-1])][0]
                Qx = Qx if Qx[0] == x else Qx[::-1]
                if x not in Qy and Qx[1] == y:
                    ok = True
                    break
            good += ok
            if not ok:
                print("R2 fails", line.strip(), y, x)
print("NA instances", tot, "R2-strong good", good)
