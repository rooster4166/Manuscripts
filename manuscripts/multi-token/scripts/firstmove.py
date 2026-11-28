"""firstmove.py: for each triangle-base instance at d(z) = 6, the legal first moves of the k-token game
(Definition 2.2).  Per root: whether some data choice / orientation has a legal first move.
usage: firstmove.py MODE(g6|resid) < g6 ; prints per-root lines and a summary."""
import sys, itertools
import networkx as nx
mode = sys.argv[1]

def matchings(vs, J):
    if not vs: yield []; return
    a = vs[0]
    for b in vs[1:]:
        if J.has_edge(a, b):
            for pm in matchings([v for v in vs[1:] if v != b], J): yield [(a, b)] + pm

def first_moves(K, toks, X, leaves, pairs):
    mv = []
    for p in toks:
        for u in K[p]:
            if u in X or u in toks or len(K[u]) % 2 == 0: continue
            if any(t != p and t in K[u] for t in toks): continue
            mv.append(('M', p, u))
        if len(K[p]) == 2:
            a, b = sorted(K[p])
            if b not in K[a] and a not in leaves and b not in leaves and \
               all({a, b} != {y, x} for (y, x) in pairs):
                mv.append(('S', p))
    return mv

tot = withmove = 0
for line in sys.stdin:
    s = line.split()[0] if line.strip() else ''
    if not s: continue
    J = nx.from_graph6_bytes(s.encode())
    if mode == 'resid':
        z = J.number_of_nodes(); J.add_edges_from((z, u) for u in range(6))
    else:
        z = [v for v in J if J.degree(v) % 2 == 0][0]
    U = sorted(J[z]); n = J.number_of_nodes()
    for r in U:
        anym = False; anydata = False
        for w in U:
            if w == r: continue
            for pm in matchings([u for u in U if u not in (r, w)], J):
                anydata = True
                for o in itertools.product((0, 1), repeat=len(pm)):
                    pairs = [(a, b) if oi else (b, a) for (a, b), oi in zip(pm, o)]   # (y, x)
                    K = {v: set(J[v]) for v in J}
                    def rm(a, b): K[a].discard(b); K[b].discard(a)
                    rm(z, w)
                    for (y, x) in pairs: rm(z, y); rm(z, x); rm(y, x)
                    leaves = []
                    for i, (y, x) in enumerate(pairs):
                        l = n + i; K[l] = {y}; K[y].add(l); leaves.append(l)
                    toks = {v for v in K if K[v] and len(K[v]) % 2 == 0}
                    X = set(leaves) | {x for (y, x) in pairs}
                    if first_moves(K, toks, X, leaves, pairs): anym = True; break
                if anym: break
            if anym: break
        if not anydata: continue
        tot += 1; withmove += anym
        print('ROOT', s, 'r=%d' % r, 'firstmove=%d' % anym)
print('SUMMARY roots', tot, 'with a legal first move', withmove)
