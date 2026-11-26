import itertools
from collections import Counter
U = range(6)   # r = 5, V = 0..4
pairs6 = list(itertools.combinations(U, 2))      # omitted pairs index the 15 four-sets
vec = [sum(1 << i for i in U if i not in p) for p in pairs6]   # four-set incidence vectors
def rank(vs):
    basis = []
    for v in vs:
        for bv in basis:
            v = min(v, v ^ bv)
        if v: basis.append(v)
    return len(basis)
indep = []
for s in range(1 << 15):
    idx = [i for i in range(15) if s >> i & 1]
    if rank([vec[i] for i in idx]) == len(idx): indep.append(s)
bysize = Counter(bin(s).count('1') for s in indep)
print('independent subsets', len(indep), sorted(bysize.items()))
# kernel (zero-sum) and circuits
zs = [s for s in range(1, 1 << 15) if __import__('functools').reduce(lambda a, i: a ^ vec[i], [i for i in range(15) if s >> i & 1], 0) == 0]
print('nonempty zero-sum families', len(zs), '(+1 empty =', len(zs) + 1, ')')
zset = set(zs)
circ = [s for s in zs if not any((t & s) == t and t != s for t in zs if bin(t).count('1') < bin(s).count('1'))]
print('inclusion-minimal nonempty zero-sum supports', len(circ))
# two disjoint triangles among circuits
def is_two_tri(s):
    E = [pairs6[i] for i in range(15) if s >> i & 1]
    if len(E) != 6: return False
    deg = Counter(v for e in E for v in e)
    if any(deg[v] != 2 for v in U): return False
    import networkx as nx
    G = nx.Graph(E); return all(len(c) == 3 for c in nx.connected_components(G))
print('circuits that are two disjoint triangles', sum(1 for s in circ if is_two_tri(s)))
# Burnside for rooted classes of (H, I)
V = range(5); pairs5 = list(itertools.combinations(V, 2))
p5i = {p: i for i, p in enumerate(pairs5)}; p6i = {p: i for i, p in enumerate(pairs6)}
from math import factorial
indep_by = {j: [s for s in indep if bin(s).count('1') == j] for j in range(6)}
tot = Counter()
for perm in itertools.permutations(V):
    sg = list(perm) + [5]
    # fixed H: graphs on V invariant: count cycles of the induced perm on pairs5
    pm = [p5i[tuple(sorted((sg[a], sg[b])))] for a, b in pairs5]
    seen = [False] * 10; cyc = 0
    for i in range(10):
        if not seen[i]:
            cyc += 1; j = i
            while not seen[j]: seen[j] = True; j = pm[j]
    fixH = 2 ** cyc
    qm = [p6i[tuple(sorted((sg[a], sg[b])))] for a, b in pairs6]
    for j in range(6):
        f = 0
        for s in indep_by[j]:
            t = 0
            for i in range(15):
                if s >> i & 1: t |= 1 << qm[i]
            if t == s: f += 1
        tot[j] += fixH * f
print('rooted classes by |I|:', {j: tot[j] // 120 for j in range(6)}, 'total', sum(tot[j] // 120 for j in range(6)))
print('labelled pairs by |I|:', {j: 1024 * len(indep_by[j]) for j in range(6)}, 'total', 1024 * len(indep))
