"""Check the coordinator's reformulation R2 by brute force (small orders).
R2-good: some Lovasz decomposition has Q(y) avoiding x AND Q(x) with terminal edge xy.
This is what R2 produces; it is stronger than NA."""
import sys
import nalib, exact
tot = good_na = good_r2 = 0
fails = []
for line in sys.stdin:
    G = nalib.g6_decode(line)
    if any(len(G[v]) % 2 == 0 for v in G):
        continue
    try:
        decs = exact.brute_all(G)
    except RuntimeError:
        continue
    for y in G:
        for x in G[y]:
            if not any(w != x and w not in G[x] for w in G[y]):
                continue
            tot += 1
            na = r2 = False
            for dec in decs:
                Qy = next(P for P in dec if P[0] == y or P[-1] == y)
                if x in Qy:
                    continue
                na = True
                Qx = next(P for P in dec if P[0] == x or P[-1] == x)
                Qx = Qx if Qx[0] == x else Qx[::-1]
                if Qx[1] == y:
                    r2 = True
                    break
            good_na += na
            good_r2 += r2
            if not r2:
                fails.append((line.strip(), y, x))
print("NA instances", tot, "NA good", good_na, "R2 good", good_r2)
for f in fails[:10]:
    print("R2 fails:", *f)
