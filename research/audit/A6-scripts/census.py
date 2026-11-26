import itertools
from collections import Counter
V = range(6)
pairs = list(itertools.combinations(V, 2))
def cands(Cedges):
    Cs = set(Cedges)
    D = [p for p in pairs if p not in Cs]
    deg = Counter()
    for x, y in D: deg[x] += 1; deg[y] += 1
    nonis = [v for v in V if deg[v] > 0]
    E = len(D)
    out = []
    for r in V:
        if deg[r] == 5:  # isolated in C
            T = [v for v in V if v != r]
            miss = [p for p in D if r not in p]
            ok = len(miss) <= 1 or (len(miss) == 2 and len(set(miss[0]) | set(miss[1])) == 3)
            if ok: out.append(r)
            continue
        if E == 0 or E == 1: out.append(r)
        elif E == 2 and len(nonis) == 3 and deg[r] == 2: out.append(r)
        elif E == 3 and len(nonis) == 3 and deg[r] == 2: out.append(r)
        elif E == 4 and len(nonis) == 4 and all(deg[v] == 2 for v in nonis) and deg[r] == 2: out.append(r)
    return out
hist = Counter(); fixed0 = 0
for s in range(1 << 15):
    C = [pairs[i] for i in range(15) if s >> i & 1]
    c = cands(C)
    hist[len(c)] += 1
    if 0 in c: fixed0 += 1
print('number of candidate roots histogram:', sorted(hist.items()))
print('cores with vertex 0 a candidate:', fixed0, ' cores where root 0 passes:', 32768 - fixed0)
