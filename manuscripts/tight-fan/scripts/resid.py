"""Generate L1* blocked residual instances (one level of all reductions, as irred_all.py)."""
import sys, itertools, collections, subprocess
import networkx as nx
import tf

def residuals(n, K=2, amax=False):
    gs = subprocess.run(['nauty-geng', '-cq', str(n)], capture_output=True, text=True).stdout.split()
    for line in gs:
        G = tf.from_g6(line); H = tf.to_nx(G)
        ev = tf.evens(G)
        if len(ev) != 1: continue
        g = ev[0]; Ng = set(G[g])
        for c in G:
            if tf.deg(G, c) % 2 == 0 or c in Ng: continue
            Nc = set(G[c]); NNc = Nc | {c}
            cand = [v for v in G if v not in NNc and v not in Ng]
            sets = [tuple(cand)] if amax else [S for k in range(1, K + 1) for S in itertools.combinations(cand, k)]
            for S in sets:
                A = set(S)
                if not A: continue
                comp = nx.node_connected_component(H.subgraph(set(G) - A), c)
                bd = {a for a in A if set(G[a]) & comp}
                if bd != A: continue
                if any(not ((set(G[u]) & A) - {g}) for u in Ng): continue   # not blocked
                yield line, G, g, c, frozenset(A), irreducible(G, H, g, c, A, comp)

def irreducible(G, H, g, c, A, comp):
    Ng = set(G[g]); Nc = set(G[c])
    if g not in A and g in comp: return False
    allowed = set(G) - A - {c, g}
    if len(G[c]) != 1: allowed -= Nc
    S = H.subgraph(allowed | {g})
    if any(not (set(G[z]) & A) for z in nx.node_connected_component(S, g) - {g}): return False
    if len(G[g]) == 2:
        u, v = sorted(Ng)
        if v in G[u]:
            if g in A: return False
        else:
            if g not in A or u not in Nc or v not in Nc: return False
    if len(G[c]) == 3:
        for y1, y2 in itertools.permutations(sorted(Nc), 2):
            if y2 not in G[y1] and y1 not in Ng: return False
    return True
