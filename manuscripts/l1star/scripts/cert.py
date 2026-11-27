"""Move certificates for L1*-instances (l1star session, exploratory).

An instance is (G, c, A): G with at most one vertex g of positive even degree, c odd,
A disjoint from N[c] and N(g).  cert(G, c, A) searches for a tree of proved reductions
(moves) ending in proved base cases; every move maps an instance to one smaller instance
(fewer edges, or the same edges and one fewer even... see Lovász's measure).
Base cases: no vertex of A in the component of c; {c} u A packed (separation theorem);
all-odd with A packed (lovasz_avoid_set); all-odd with d(c) = 1.
Moves: M1 (Case I at g with target u, three variants), M2 (route g..c appended), M2' (route
g..y, y in N(c), via Fan transfers), M3 (all-odd leaf graph), M7 (d(g) = 2 splitting at g),
M8 (d(c) = 3 splitting at c), M9 (route from g to a vertex with no neighbour in A, via Fan).
usage: nauty-geng -cq n | python3 cert.py K [moves]
"""
import sys, itertools, collections, functools
import networkx as nx

sys.setrecursionlimit(10000)

def even_vertex(G):
    ev = [v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0]
    assert len(ev) <= 1, ev
    return ev[0] if ev else None

def key(G, c, A):
    return (frozenset(frozenset(e) for e in G.edges()), frozenset(G.nodes()), c, frozenset(A))

def packed(G, X):
    X = list(X)
    for i in range(len(X)):
        for j in range(i + 1, len(X)):
            x, y = X[i], X[j]
            if G.has_edge(x, y) or set(G[x]) & set(G[y]):
                return False
    return True

MOVES = None
memo = {}
stats = collections.Counter()

def valid(G, c, A):
    g = even_vertex(G)
    if G.degree(c) % 2 == 0:
        return False
    bad = set(G[c]) | {c}
    if g is not None:
        bad |= set(G[g])
    return not (A & bad)

def cert(G, c, A, depth=0):
    A = frozenset(a for a in A if G.degree(a) > 0)
    k = key(G, c, A)
    if k in memo:
        return memo[k]
    memo[k] = False  # cycle guard
    r = _cert(G, c, A, depth)
    memo[k] = r
    return r

def _cert(G, c, A, depth):
    assert valid(G, c, A), (sorted(G.edges()), c, A)
    comp = nx.node_connected_component(G, c)
    if not (A & comp):
        return True
    g = even_vertex(G)
    if g is not None and g not in comp:
        g = None  # the even vertex is in another component: c's component is all-odd
    if packed(G, A | {c}):
        return True
    if g is None and packed(G, A):
        return True
    if g is None and G.degree(c) == 1:
        return True
    Nc = set(G[c])
    if g is None:
        if "M3" in MOVES:
            for y in sorted(Nc):
                H = G.copy(); H.remove_edge(c, y); l = max(G.nodes()) + 1; H.add_edge(y, l)
                if cert(H, l, A | {c}, depth + 1):
                    return True
        return False
    Ng = set(G[g])
    # boundary (Lemma 5.1): shrink A to the neighbourhood of the component of c in G - A
    if "B" in MOVES:
        compA = nx.node_connected_component(G.subgraph(set(G) - A), c)
        bd = frozenset(a for a in A if set(G[a]) & compA)
        if bd != A:
            return cert(G, c, bd, depth + 1)
    # M13: d(g) = 2 in a triangle, g in A: drop g from A
    if "M13" in MOVES and G.degree(g) == 2 and g in A:
        u0, v0 = sorted(Ng)
        if G.has_edge(u0, v0) and c not in Ng:
            return cert(G, c, A - {g}, depth + 1)
    # M1
    if "M1" in MOVES:
        for u in sorted(Ng):
            if (set(G[u]) & A) - {g}:
                continue
            H = G.copy(); H.remove_edge(g, u)
            if u == c:
                if cert(H, g, A | {c}, depth + 1): return True
            elif u in Nc:
                H.remove_edge(c, u)
                if cert(H, u, A | {c}, depth + 1): return True
            else:
                if cert(H, c, A, depth + 1): return True
    # M7: d(g) = 2 splitting
    if "M7" in MOVES and G.degree(g) == 2:
        u, v = sorted(Ng)
        if not G.has_edge(u, v):
            H = G.copy(); H.remove_edge(g, u); H.remove_edge(g, v); H.add_edge(u, v)
            if g not in A:
                if cert(H, c, A, depth + 1): return True
            else:
                for w in (u, v):
                    if w not in Nc and w != c:
                        if cert(H, c, (A - {g}) | {w}, depth + 1): return True
    # M8: d(c) = 3 splitting at c
    if "M8" in MOVES and G.degree(c) == 3 and c not in Ng:
        for y1, y2 in itertools.combinations(sorted(Nc), 2):
            if G.has_edge(y1, y2):
                continue
            H = G.copy(); H.remove_edge(c, y1); H.remove_edge(c, y2); H.add_edge(y1, y2)
            for w in (y1, y2):
                if w not in Ng and w not in A:
                    if valid(H, c, A | {w}) and cert(H, c, A | {w}, depth + 1): return True
    # M2: route g..c avoiding A, chordless at both ends (shortest path in G - A)
    if "M2" in MOVES and g not in A and c not in Ng:
        S = G.subgraph(set(G) - A)
        if nx.has_path(S, g, c):
            for R in itertools.islice(nx.all_shortest_paths(S, g, c), 6):
                H = G.copy()
                for i in range(len(R) - 1): H.remove_edge(R[i], R[i + 1])
                B = A | set(R[1:])
                if valid(H, g, B) and cert(H, g, B, depth + 1): return True
    # M2' and M9: Fan routes from g
    if "M9" in MOVES and c not in Ng:
        allowed = set(G) - A - {c, g}
        if G.degree(c) != 1:
            allowed -= Nc
        # simple paths from g inside allowed (bounded length)
        S = G.subgraph(allowed | {g})
        for z in sorted(allowed):
            if z in Ng and ((set(G[z]) & A) - {g}) == set():
                continue  # that is M1
            if set(G[z]) & A:
                continue
            if not nx.has_path(S, g, z):
                continue
            for R in itertools.islice(nx.all_shortest_paths(S, g, z), 4):
                H = G.copy()
                for i in range(len(R) - 1): H.remove_edge(R[i], R[i + 1])
                if valid(H, c, A) and cert(H, c, A, depth + 1): return True
    if "M2p" in MOVES and c not in Ng:
        for y in sorted(Nc):
            if (set(G[y]) | {y}) & A or y == g:
                continue
            S = G.subgraph((set(G) - A - Nc - {c}) | {g, y})
            if not nx.has_path(S, g, y):
                continue
            for R in itertools.islice(nx.all_shortest_paths(S, g, y), 4):
                H = G.copy()
                for i in range(len(R) - 1): H.remove_edge(R[i], R[i + 1])
                H.remove_edge(y, c)
                B = A | {c}
                if valid(H, y, B) and cert(H, y, B, depth + 1): return True
    return False

if __name__ == "__main__":
    K = int(sys.argv[1])
    MOVES = set(sys.argv[2].split(",")) if len(sys.argv) > 2 else {"M1", "M2", "M2p", "M3", "M7", "M8", "M9", "M13", "B"}
    C = collections.Counter(); ex = collections.defaultdict(list)
    for line in sys.stdin:
        line = line.strip()
        G = nx.from_graph6_bytes(line.encode())
        g = even_vertex(G) if len([v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0]) <= 1 else "skip"
        if g == "skip": continue
        Ng = set(G[g]) if g is not None else set()
        for c in G:
            if G.degree(c) % 2 == 0: continue
            Nc = set(G[c]) | {c}
            cand = [v for v in G if v not in Nc and v not in Ng]
            for k in range(1, K + 1):
                for S in itertools.combinations(cand, k):
                    A = frozenset(S)
                    ok = cert(G, c, A)
                    C[("one-even" if g is not None else "all-odd", k, ok)] += 1
                    if not ok and len(ex[k]) < 6:
                        ex[k].append((line, g, c, sorted(A)))
    for kk, v in sorted(C.items(), key=str): print(kk, v)
    for k in ex: print("UNCERT", k, ex[k])
