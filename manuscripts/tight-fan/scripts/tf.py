"""tf.py: small exact library for the tight-Fan experiments (tight-fan session).

Graphs: dict v -> set(neighbours) on vertices 0..n-1 (graph6 via networkx).
A decomposition is a list of paths, each a tuple of vertices (length >= 2).
ends(D, v) = number of path ends at v.

* decomps(G, b, ...)  -- enumerate all path decompositions with end counts b (dict v -> 0/1),
  via transition systems; optional pruning: the path ending at c avoids the set `avoid`,
  or lies in `region`.
* fan_moves(D, t, u)   -- all decompositions of G + tu produced by Fan's chain argument
  (reroutes then one append), with every choice of chain.  Exact, no counting shortcut.
* flower(...)          -- the flower recombination (flower lemma) and receipt-or-flower.
"""
import itertools, collections
import networkx as nx

def from_g6(s):
    G = nx.from_graph6_bytes(s.encode())
    return {v: set(G[v]) for v in G}

def to_nx(G):
    H = nx.Graph(); H.add_nodes_from(G)
    for v in G:
        for w in G[v]:
            if v < w: H.add_edge(v, w)
    return H

def copyg(G): return {v: set(G[v]) for v in G}
def rem(G, *es):
    H = copyg(G)
    for a, b in es:
        assert b in H[a], (a, b)
        H[a].discard(b); H[b].discard(a)
    return H
def add(G, *es):
    H = copyg(G)
    for a, b in es:
        H.setdefault(a, set()); H.setdefault(b, set())
        assert b not in H[a]
        H[a].add(b); H[b].add(a)
    return H
def deg(G, v): return len(G[v])
def edges(G): return sorted((a, b) for a in G for b in G[a] if a < b)
def evens(G): return [v for v in G if deg(G, v) > 0 and deg(G, v) % 2 == 0]
def lovasz_b(G): return {v: deg(G, v) % 2 for v in G}

def ends(D, v):
    return sum((P[0] == v) + (P[-1] == v) for P in D)

def path_at(D, c):
    """the paths with an end at c"""
    return [P for P in D if P[0] == c or P[-1] == c]

def check(G, D, b=None):
    E = collections.Counter()
    for P in D:
        assert len(P) >= 2 and len(set(P)) == len(P), P
        for x, y in zip(P, P[1:]):
            assert y in G[x], (P, x, y)
            E[frozenset((x, y))] += 1
    assert all(k == 1 for k in E.values()) and len(E) == len(edges(G)), "not a decomposition"
    if b is not None:
        for v in G:
            assert ends(D, v) == b[v], (v, ends(D, v), b[v])
    return True

# ---------------------------------------------------------------------------
# enumeration of path decompositions with prescribed ends

def _pairings(es, k):
    """all ways to choose k singletons from list es and pair up the rest"""
    for S in itertools.combinations(range(len(es)), k):
        rest = [es[i] for i in range(len(es)) if i not in S]
        for M in _perfect(rest):
            yield M
def _perfect(xs):
    if not xs:
        yield []; return
    a = xs[0]
    for i in range(1, len(xs)):
        for M in _perfect(xs[1:i] + xs[i + 1:]):
            yield [(a, xs[i])] + M

def decomps(G, b, c=None, avoid=frozenset(), region=None, limit=None, order=None):
    """Yield every path decomposition of G with end counts b.  If c is given (b[c] == 1),
    prune so that the path ending at c avoids `avoid` and lies inside `region` (if given)."""
    E = edges(G)
    eidx = {}
    for i, (x, y) in enumerate(E):
        eidx[(x, y)] = eidx[(y, x)] = i
    verts = [v for v in G if deg(G, v) > 0]
    for v in verts:
        assert b[v] <= deg(G, v) and (deg(G, v) - b[v]) % 2 == 0, (v, b[v], deg(G, v))
    if order is None:
        # BFS from c (or from max degree)
        H = to_nx(G)
        s = c if c is not None else max(verts, key=lambda v: deg(G, v))
        order = list(nx.bfs_tree(H, s)) if s in H else []
        order += [v for v in verts if v not in order]
    # union-find over edges; each component a path: store vertex set and the end-vertices
    parent = list(range(len(E)))
    comp_v = [set(e) for e in E]
    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x
    trans = {}  # v -> list of pairs (i, j)
    count = [0]
    bad = frozenset(avoid)
    def qc_ok(root):
        V = comp_v[root]
        if bad & V: return False
        if region is not None and not V <= region: return False
        return True
    def rec(k):
        if limit is not None and count[0] >= limit: return
        if k == len(order):
            yield build(); return
        v = order[k]
        inc = [eidx[(v, w)] for w in sorted(G[v])]
        for M in _pairings(inc, b[v]):
            # apply merges, with undo log
            log = []; ok = True
            for (i, j) in M:
                ri, rj = find(i), find(j)
                if ri == rj or (comp_v[ri] & comp_v[rj]) != {v}:
                    ok = False; break
                # merge rj into ri
                log.append((ri, rj, set(comp_v[ri])))
                parent[rj] = ri; comp_v[ri] = comp_v[ri] | comp_v[rj]
            if ok and c is not None and v == c and (bad or region is not None):
                single = [e for e in inc if all(e not in p for p in M)]
                assert len(single) == 1
                if not qc_ok(find(single[0])): ok = False
            if ok and c is not None and (bad or region is not None) and c in order[:k]:
                # Q_c is the component containing c's single edge; re-check after merges
                if not qc_ok(find(trans['single'])): ok = False
            if ok:
                trans[v] = M
                if v == c:
                    trans['single'] = [e for e in inc if all(e not in p for p in M)][0]
                yield from rec(k + 1)
                if v == c: trans.pop('single', None)
                trans.pop(v, None)
            for (ri, rj, old) in reversed(log):
                parent[rj] = rj; comp_v[ri] = old
    def build():
        count[0] += 1
        # assemble paths from transitions
        nxt = collections.defaultdict(dict)  # edge i -> {vertex: edge j}
        for v in order:
            for (i, j) in trans[v]:
                nxt[i][v] = j; nxt[j][v] = i
        seen = set(); D = []
        for i, (x, y) in enumerate(E):
            if i in seen: continue
            # find a free end of the trail containing i: walk in one direction
            # walk from edge i towards x until no transition
            cur, at = i, x
            while at in nxt[cur]:
                cur2 = nxt[cur][at]
                a, bb = E[cur2]
                at = bb if a == at else a
                cur = cur2
            # now 'at' is a free end, cur the edge there; walk the whole trail
            a, bb = E[cur]
            P = [at]; v = at; e = cur
            while True:
                seen.add(e)
                a, bb = E[e]
                w = bb if a == v else a
                P.append(w)
                if w in nxt[e]:
                    e = nxt[e][w]; v = w
                else:
                    break
            D.append(tuple(P))
        return D
    yield from rec(0)

def exists(G, b, c=None, avoid=frozenset(), region=None):
    for D in decomps(G, b, c, avoid, region, limit=1):
        return D
    return None

def Qc(D, c):
    Ps = path_at(D, c)
    assert len(Ps) == 1, (c, Ps)
    return Ps[0]

# ---------------------------------------------------------------------------
# Fan's chain, exactly

def _orient(P, x):
    return P if P[0] == x else tuple(reversed(P))

def fan_moves(D, t, u, protect=None):
    """All results of Fan's argument adding the edge tu to the decomposition D (tu not an edge).
    A step at the current vertex x (which holds an end): take a path P with an end at x.
    If u not on P: append xu (P gains u) -> result.  Else read P from x: x .. z u ..;
    reroute to z .. x u .. (vertex set kept, x loses the end, z gains it), and the missing edge
    becomes zu; continue from z.  Returns list of (D', final_path_index_info).
    `protect` is ignored here (filtering is done by the caller)."""
    out = []
    seen = set()
    stack = [(tuple(D), t, ())]
    while stack:
        Dc, x, chain = stack.pop()
        key = (frozenset(Dc), x)
        if key in seen: continue
        seen.add(key)
        for idx, P in enumerate(Dc):
            if P[0] != x and P[-1] != x: continue
            Po = _orient(P, x)
            if u not in Po:
                newP = (u,) + Po          # the new edge ux, P gains u at its end x
                D2 = list(Dc); D2[idx] = newP
                out.append((D2, chain + (x,), newP))
            else:
                k = Po.index(u)
                z = Po[k - 1]
                if k - 1 == 0:
                    continue  # x itself adjacent to u on P: impossible since xu is missing
                newP = tuple(reversed(Po[:k])) + Po[k:]   # z .. x u ..
                # careful: reversed(Po[:k]) = z ... x ; then u ...
                D2 = list(Dc); D2[idx] = newP
                stack.append((tuple(D2), z, chain + (x,)))
    return out

def fan_results(G2, D, t, u):
    """decompositions of G2 = G + tu reachable by Fan's argument from D; checked."""
    res = []
    for D2, chain, P in fan_moves(D, t, u):
        check(G2, D2)
        res.append((D2, chain, P))
    return res

def canon(D):
    return frozenset(P if P[0] < P[-1] else tuple(reversed(P)) for P in D)
