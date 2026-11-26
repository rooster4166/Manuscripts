"""Cross-check exact.py against tools/pathnum.py (CP-SAT) on random graphs and end vectors."""
import random, sys, os
sys.path.insert(0, '/home/user/Manuscripts/tools')
import networkx as nx
from pathnum import solve as psolve
from exact import realise, check_partition, floor_with_end
rng = random.Random(11)
agree = 0
for trial in range(150):
    n = rng.choice([5, 6, 7, 8])
    Gx = nx.gnp_random_graph(n, rng.uniform(0.3, 0.8), seed=rng.randrange(10**9))
    if not nx.is_connected(Gx):
        continue
    G = {v: set(Gx[v]) for v in Gx}
    beta = {v: (len(G[v]) % 2) for v in G}
    for _ in range(rng.randrange(3)):
        w = rng.choice(list(G)); beta[w] += 2
    P = realise(G, beta)
    r = psolve(Gx, exact_ends=beta, workers=1, time_limit=60)
    mine = P is not None
    theirs = r.status in ('OPTIMAL', 'FEASIBLE')
    assert mine == theirs, (nx.to_graph6_bytes(Gx), beta, mine, theirs)
    if mine:
        assert check_partition(G, P, beta)
    y = rng.choice(list(G))
    Q = floor_with_end(G, y)
    r2 = psolve(Gx, budget=n // 2, min_ends={y: 1}, workers=1, time_limit=60)
    assert (Q is not None) == (r2.status in ('OPTIMAL', 'FEASIBLE'))
    if Q is not None:
        assert check_partition(G, Q) and len(Q) <= n // 2 and any(y in (p[0], p[-1]) for p in Q)
    agree += 1
print('exact.py agrees with pathnum on', agree, 'random instances (exact vectors and floor-with-end)')
