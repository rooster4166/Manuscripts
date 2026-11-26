"""Audit A9: exhaustive checks over all graphs with <= 7 vertices and no isolated vertex
(networkx atlas), all orders (odd orders exercise Remark 'at every order'), of:
 R  : Ev and Ev - {u} realisable (Lemmas faithful/minus at every order);
 T2 : non-realisable pairs Ev - {u,v} are E-twins (Thm 'second step' / Cor 'twins');
 L,S,C : Prop 'moves' with X = {x, v} under each local condition at x."""
import sys, itertools
sys.path.insert(0, '/home/user/Manuscripts/tools')
import networkx as nx
from networkx.generators.atlas import graph_atlas_g
from pathnum2 import decompose
from functools import lru_cache

def Ev(G): return [v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0]
def Od(G): return [v for v in G if G.degree(v) % 2 == 1]
cache = {}
def realisable(G, S, key):
    S = frozenset(S)
    if (key, S) in cache: return cache[key, S]
    ex = {v: 1 for v in Od(G)}
    for u in Ev(G): ex[u] = 2 if u in S else 0
    k = len(Od(G)) // 2 + len(S)
    st, P = decompose(G, k, exact_ends=ex, time_limit=60, workers=1)
    assert st in ('OPTIMAL', 'FEASIBLE', 'INFEASIBLE') or P is not None, st
    cache[key, S] = P is not None
    return P is not None

cnt = dict(graphs=0, R=0, T2=0, L=0, S=0, C=0)
bad = []
for i, G in enumerate(graph_atlas_g()):
    if G.number_of_nodes() < 2 or any(d == 0 for _, d in G.degree()): continue
    cnt['graphs'] += 1
    E = Ev(G); Es = set(E)
    if not realisable(G, E, i): bad.append(('R-full', i))
    for u in E:
        cnt['R'] += 1
        if not realisable(G, Es - {u}, i): bad.append(('R-minus', i, u))
    for u, v in itertools.combinations(E, 2):
        ok = realisable(G, Es - {u, v}, i)
        twins = all((G.has_edge(u, w) == G.has_edge(v, w)) for w in E if w not in (u, v))
        cnt['T2'] += 1
        if not ok and not twins: bad.append(('T2', i, u, v))
        for x, vv in ((u, v), (v, u)):
            Nx = set(G[x])
            if any(G.degree(l) == 1 for l in Nx):
                cnt['L'] += 1
                if not ok: bad.append(('L', i, x, vv))
            if G.degree(x) == 2:
                a, b = Nx
                if not G.has_edge(a, b):
                    cnt['S'] += 1
                    if not ok: bad.append(('S', i, x, vv))
            if Nx <= Es - {x, vv}:
                cnt['C'] += 1
                if not ok: bad.append(('C', i, x, vv))
print(cnt)
print("violations:", bad)
