"""Random test of EMM_3 (EMM on connected graphs of minimum degree >= 3), and of bridge cores.

mode "emm3": N random connected graphs of order n, minimum degree >= 3, m uniform in [mlo, mhi]
(G(n, m) with rejection); every half-set M of the even vertices is tested, cut-feasibility (L)+(C)
against realisability (tools/realis.c), as in tools/cut_test.py.
mode "cores": N random graphs made of a core of order n - s with minimum degree >= 3 plus s
pendant leaves (s = 1 or 2), all simple profiles; report cut-feasible non-realisable ones (see
tools/emm3_core_search.py for why such cores matter).

Usage: python3 tools/emm3_random.py emm3|cores n N mlo mhi seed
"""
import random
import sys
from itertools import combinations

import networkx as nx

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import realis  # noqa: E402
from gemm_test import prepare, feasible  # noqa: E402

mode, n, N, mlo, mhi, seed = sys.argv[1], *map(int, sys.argv[2:7])
rng = random.Random(seed)


def rand_d3(order, lo, hi):
    while True:
        m = rng.randint(lo, hi)
        G = nx.gnm_random_graph(order, m, seed=rng.randrange(10**9))
        if min(d for _, d in G.degree()) >= 3 and nx.is_connected(G):
            return G


t = dict(graphs=0, profiles=0, feasible=0, failures=0)
for _ in range(N):
    if mode == "emm3":
        G = rand_d3(n, mlo, mhi)
    else:
        s = rng.choice((1, 2))
        G = rand_d3(n - s, mlo, mhi)
        for i in range(s):
            G.add_edge(n - s + i, rng.randrange(n - s))
    t["graphs"] += 1
    d = dict(G.degree())
    nodes = sorted(G)
    Ev = [v for v in G if d[v] % 2 == 0]
    prep = prepare(G)
    if mode == "emm3":
        Evs, fam = realis.family(G)
        fam = set(fam)
        Ms = combinations(Ev, len(Ev) // 2) if len(Ev) % 2 == 0 else []
    else:
        fam = None
        Ms = (M for k in range(len(Ev) + 1) for M in combinations(Ev, k))
    for M in Ms:
        bb = [1 if d[v] % 2 else (2 if v in M else 0) for v in nodes]
        t["profiles"] += 1
        if not feasible(prep, bb)[0]:
            continue
        t["feasible"] += 1
        real = (frozenset(M) in fam) if fam is not None else realis.profile_ok(G, {v: bb[v] for v in G})
        if not real:
            t["failures"] += 1
            print("FAIL", mode, nx.to_graph6_bytes(G, header=False).decode().strip(), sorted(G.edges()),
                  "M", M, "p", sum(bb) // 2, flush=True)
print(t, flush=True)
