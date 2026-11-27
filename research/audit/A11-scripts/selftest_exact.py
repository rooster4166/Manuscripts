"""Cross-check exact.py against tools/pathnum.py (CP-SAT) on random connected graphs of order
5-7: exact end vectors, and 'floor(N/2) paths with an end at y'. Instances on which CP-SAT does
not finish in its time limit are skipped and counted."""
import random, sys
sys.path.insert(0, '/home/user/Manuscripts/tools')
import networkx as nx
from pathnum import solve as psolve
from exact import realise, check_partition, floor_with_end
rng = random.Random(11)
agree = skipped = 0
for trial in range(400):
    n = rng.choice([5, 6, 7])
    Gx = nx.gnp_random_graph(n, rng.uniform(0.3, 0.8), seed=rng.randrange(10**9))
    if not nx.is_connected(Gx):
        continue
    G = {v: set(Gx[v]) for v in Gx}
    beta = {v: (len(G[v]) % 2) for v in G}
    for _ in range(rng.randrange(3)):
        w = rng.choice(list(G)); beta[w] += 2
    P = realise(G, beta)
    r = psolve(Gx, exact_ends=beta, workers=1, time_limit=20)
    y = rng.choice(list(G))
    Q = floor_with_end(G, y)
    r2 = psolve(Gx, budget=n // 2, min_ends={y: 1}, workers=1, time_limit=20)
    if r.status not in ('OPTIMAL', 'FEASIBLE', 'INFEASIBLE') or r2.status not in ('OPTIMAL', 'FEASIBLE', 'INFEASIBLE'):
        skipped += 1
        continue
    assert (P is not None) == (r.status in ('OPTIMAL', 'FEASIBLE')), (nx.to_graph6_bytes(Gx), beta)
    if P is not None:
        assert check_partition(G, P, beta)
    assert (Q is not None) == (r2.status in ('OPTIMAL', 'FEASIBLE')), (nx.to_graph6_bytes(Gx), y)
    if Q is not None:
        assert check_partition(G, Q) and len(Q) <= n // 2 and any(y in (p[0], p[-1]) for p in Q)
    agree += 1
print(f'exact.py agrees with pathnum on {agree} random instances ({skipped} skipped on CP-SAT time limit)')
