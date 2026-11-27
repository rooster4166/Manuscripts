"""A16 core library: graphs, path partitions, a checker, an exhaustive enumerator, and a direct
implementation of the proof of Lemma 3 (Fan's lemma with vertex sets) of route-descent.tex.

Written for the A16 audit from the text of the manuscript alone. It imports nothing from
manuscripts/route-descent/scripts. The optional oracle wrapper at the end calls
tools/route_ext.c directly; it is used only for instances too large for the enumerator, and it
is cross-checked against the enumerator in a16_enum.py.

Graphs are dicts {v: set(neighbours)}; vertices are hashable (ints, or tuples for new leaves).
A path is a list of distinct vertices; a path partition is a list of paths.
"""
import itertools
import os
import random
import subprocess
import tempfile

# ----------------------------------------------------------------------------------------------
# graphs


def copy(adj):
    return {v: set(N) for v, N in adj.items()}


def edges(adj):
    return {frozenset((u, v)) for u in adj for v in adj[u]}


def add_edge(adj, u, v):
    assert u != v and v not in adj[u]
    adj[u].add(v)
    adj[v].add(u)


def del_edge(adj, u, v):
    assert v in adj[u]
    adj[u].discard(v)
    adj[v].discard(u)


def deg(adj, v):
    return len(adj[v])


def even_set(adj):
    return [v for v in adj if adj[v] and len(adj[v]) % 2 == 0]


def dist_from(adj, s):
    d = {s: 0}
    fr = [s]
    while fr:
        nx_ = []
        for x in fr:
            for y in adj[x]:
                if y not in d:
                    d[y] = d[x] + 1
                    nx_.append(y)
        fr = nx_
    return d


def dist(adj, s, t):
    return dist_from(adj, s).get(t, float("inf"))


def packed(adj, X):
    X = list(X)
    for i in range(len(X)):
        for j in range(i + 1, len(X)):
            if dist(adj, X[i], X[j]) < 3:
                return False
    return True


def random_graph(n, p, rng):
    adj = {v: set() for v in range(n)}
    for u in range(n):
        for v in range(u + 1, n):
            if rng.random() < p:
                add_edge(adj, u, v)
    return adj


def make_odd(adj, rng, allow_isolated=True):
    """Toggle edges to make every vertex of positive degree odd (pairs up even vertices along
    random non-edges / edges). Vertices of degree 0 may remain if allow_isolated."""
    for _ in range(200):
        ev = [v for v in adj if len(adj[v]) % 2 == 0 and (adj[v] or not allow_isolated)]
        if not ev:
            return adj
        if len(ev) == 1:
            # attach a pendant new vertex
            v = ev[0]
            w = max(x for x in adj if isinstance(x, int)) + 1
            adj[w] = set()
            add_edge(adj, v, w)
            continue
        u, v = rng.sample(ev, 2)
        if v in adj[u]:
            del_edge(adj, u, v)
        else:
            add_edge(adj, u, v)
    raise RuntimeError("make_odd failed")


def random_one_even(n, p, rng):
    """A random graph with at most one vertex of positive even degree."""
    adj = make_odd(random_graph(n, p, rng), rng)
    if rng.random() < 0.6:
        # make one vertex even by deleting or adding an edge at it to a new leaf
        cands = [v for v in adj if adj[v]]
        if cands:
            z = rng.choice(cands)
            w = max(x for x in adj if isinstance(x, int)) + 1
            adj[w] = set()
            add_edge(adj, z, w)
            # w is a new leaf (odd), z became even
    return adj


# ----------------------------------------------------------------------------------------------
# path partitions


def ends_count(D, vertices):
    b = {v: 0 for v in vertices}
    for P in D:
        b[P[0]] += 1
        b[P[-1]] += 1
    return b


def check_partition(adj, D, b=None):
    """Independent check that D partitions E(adj) into simple paths (each with >= 1 edge), with
    b(v) ends at every v if b is given. Returns the end-count dict."""
    seen = set()
    for P in D:
        assert len(P) >= 2, "path with no edge"
        assert len(set(P)) == len(P), f"not a simple path: {P}"
        for x, y in zip(P, P[1:]):
            assert y in adj[x], f"non-edge {x}{y}"
            e = frozenset((x, y))
            assert e not in seen, f"edge {x}{y} used twice"
            seen.add(e)
    assert seen == edges(adj), "edges not covered"
    bc = ends_count(D, adj)
    if b is not None:
        for v in adj:
            assert bc[v] == b[v], f"wrong profile at {v}: {bc[v]} != {b[v]}"
    return bc


def lovasz_profile(adj):
    return {v: len(adj[v]) % 2 for v in adj}


def is_lovasz(adj, D):
    try:
        check_partition(adj, D, lovasz_profile(adj))
        return True
    except AssertionError:
        return False


def meets_once(D, X):
    X = set(X)
    return all(len(X & set(P)) <= 1 for P in D)


def random_partition(adj, rng, stop=0.25):
    """A random path partition of adj (arbitrary profile): grow random paths greedily."""
    unused = set(edges(adj))
    D = []
    while unused:
        e = rng.choice(sorted(unused, key=lambda f: tuple(sorted(map(str, f)))))
        x, y = tuple(e)
        unused.discard(e)
        P = [x, y]
        for _ in range(2):
            while rng.random() > stop:
                end = P[-1]
                cand = [w for w in adj[end] if w not in P and frozenset((end, w)) in unused]
                if not cand:
                    break
                w = rng.choice(sorted(cand, key=str))
                unused.discard(frozenset((end, w)))
                P.append(w)
            P.reverse()
        D.append(P)
    return D


# ----------------------------------------------------------------------------------------------
# exhaustive enumeration of path partitions with a prescribed profile (transition systems)


def _matchings(items):
    if not items:
        yield []
        return
    a = items[0]
    for i in range(1, len(items)):
        rest = items[1:i] + items[i + 1:]
        for m in _matchings(rest):
            yield [(a, items[i])] + m


def partitions_with_profile(adj, b):
    """Yield every path partition of adj with exactly b(v) ends at v, each exactly once.

    A path partition is determined by its transition system: at every vertex v, the b(v) edges
    that end a path at v, and a perfect matching of the other edges at v (the passages). Conversely
    a transition system gives a partition into trails and closed trails; it is a path partition
    iff there is no closed trail and no trail repeats a vertex."""
    V = sorted(adj, key=str)
    choices = []
    for v in V:
        N = sorted(adj[v], key=str)
        k = b[v]
        if k > len(N) or (len(N) - k) % 2:
            return
        opts = []
        for E in itertools.combinations(N, k):
            rest = [w for w in N if w not in E]
            for m in _matchings(rest):
                opts.append((set(E), m))
        choices.append(opts)
    for combo in itertools.product(*choices):
        nxt = {}  # (v, w): at v, arriving from w, continue to nxt[(v, w)] (None = end here)
        for v, (E, m) in zip(V, combo):
            for w in E:
                nxt[(v, w)] = None
            for x, y in m:
                nxt[(v, x)] = y
                nxt[(v, y)] = x
        used = set()
        D = []
        ok = True
        # trails start at end-edges
        for v, (E, m) in zip(V, combo):
            for w in E:
                e = frozenset((v, w))
                if e in used:
                    continue
                P = [v]
                prev, cur = v, w
                while True:
                    used.add(frozenset((prev, cur)))
                    P.append(cur)
                    nn = nxt[(cur, prev)]
                    if nn is None:
                        break
                    prev, cur = cur, nn
                if len(set(P)) != len(P):
                    ok = False
                    break
                D.append(P)
            if not ok:
                break
        if not ok or len(used) != len(edges(adj)):
            continue  # repeated vertex, or a closed trail remains
        yield D


def lovasz_decompositions(adj):
    return partitions_with_profile(adj, lovasz_profile(adj))


# ----------------------------------------------------------------------------------------------
# Lemma 3 (Fan's lemma with vertex sets), implemented exactly as in the manuscript's proof


class FanStats:
    def __init__(self):
        self.calls = 0
        self.chain_len = {}
        self.reuse = 0  # chains with Q_i = Q_j for some j < i


FAN_STATS = FanStats()


def Zset(adj, D, u):
    b = ends_count(D, adj)
    return {w for w in adj[u] if b[w] == 0}


def fan(adj, D, t, u, rng=None, check=True, long_chain=False):
    """Lemma 3. adj = K, D a path partition of K, t != u, tu not in E(K), b(t) > |Z(u)|.
    Returns (adj_plus, D_plus, star) where D_plus[i] corresponds to D[i] (the bijection phi) and
    star is the index of the one path that gains u. Asserts every claim of the lemma."""
    assert t != u and u not in adj[t]
    b = ends_count(D, adj)
    assert b[t] > len(Zset(adj, D, u)), "hypothesis b(t) > |Z(u)| fails"
    FAN_STATS.calls += 1

    def pi(x, P):
        # read P from its end x; the vertex just before u
        Q = P if P[0] == x else P[::-1]
        assert Q[0] == x
        i = Q.index(u)
        return Q[i - 1]

    ends_at = {}
    for i, P in enumerate(D):
        ends_at.setdefault(P[0], []).append(i)
        ends_at.setdefault(P[-1], []).append(i)
    # BFS over steps x -> pi(x, Q); stop at a vertex with a path ending there that avoids u
    order = [t]
    parent = {t: None}
    found = None
    head = 0
    while head < len(order) and found is None:
        x = order[head]
        head += 1
        idx = list(ends_at.get(x, []))
        if rng:
            rng.shuffle(idx)
        for i in idx:
            if u not in D[i]:
                found = (x, i)
                break
        if found:
            break
        for i in idx:
            y = pi(x, D[i])
            assert y != u and u in adj[y]
            if y not in parent:
                parent[y] = (x, i)
                order.append(y)
    assert found is not None, "no chain although b(t) > |Z(u)| (counting argument violated)"
    xk, istar = found
    chain = [xk]
    paths = []
    while parent[chain[-1]] is not None:
        x, i = parent[chain[-1]]
        paths.append(i)
        chain.append(x)
    chain.reverse()
    paths.reverse()
    if long_chain and rng:
        # any chain of distinct vertices is allowed by the proof; pick a long random one by a
        # randomised depth-first search in the step digraph (stress test of the execution)
        best = None
        for _ in range(20):
            seq, ps, seen = [t], [], {t}
            while True:
                x = seq[-1]
                idx = list(ends_at.get(x, []))
                rng.shuffle(idx)
                stops = [i for i in idx if u not in D[i]]
                steps = [(pi(x, D[i]), i) for i in idx if u in D[i]]
                steps = [(y, i) for y, i in steps if y not in seen]
                if stops and (not steps or rng.random() < 0.15):
                    if best is None or len(seq) > len(best[0]):
                        best = (list(seq), list(ps), stops[0])
                    break
                if not steps:
                    break
                y, i = rng.choice(steps)
                seq.append(y)
                ps.append(i)
                seen.add(y)
        if best is not None and len(best[0]) > len(chain):
            chain, paths, istar = best
            xk = chain[-1]
    k = len(chain) - 1
    assert chain[0] == t and len(set(chain)) == len(chain)
    FAN_STATS.chain_len[k] = FAN_STATS.chain_len.get(k, 0) + 1
    if len(set(paths)) < len(paths):
        FAN_STATS.reuse += 1
    for i in set(paths):
        assert paths.count(i) <= 2, "a path used three times"
    # execute
    cur = copy(adj)
    Dc = [list(P) for P in D]
    for i in range(k):
        xi, xn = chain[i], chain[i + 1]
        P = Dc[paths[i]]
        if P[0] != xi:
            P = P[::-1]
        assert P[0] == xi, "chain path no longer ends at x_i"
        j = P.index(u)
        assert P[j - 1] == xn, "pi(x_i, current path) != x_{i+1}"
        assert u not in cur[xi], "edge x_i u already present"
        newP = P[:j][::-1] + P[j:]
        del_edge(cur, xn, u)
        add_edge(cur, xi, u)
        assert set(newP) == set(P) and newP[0] == xn and newP[-1] == P[-1]
        Dc[paths[i]] = newP
    # append
    Qs = Dc[istar]
    assert Qs == D[istar] or Qs == D[istar][::-1], "Q* touched before the append"
    if Qs[-1] != xk:
        Qs = Qs[::-1]
    assert Qs[-1] == xk and u not in Qs
    assert u not in cur[xk]
    add_edge(cur, xk, u)
    Dc[istar] = Qs + [u]
    if check:
        target = copy(adj)
        add_edge(target, t, u)
        assert edges(cur) == edges(target), "final graph is not K + tu"
        bb = dict(b)
        bb[t] -= 1
        bb[u] += 1
        check_partition(target, Dc, bb)
        for i in range(len(D)):
            if i == istar:
                assert set(Dc[i]) == set(D[i]) | {u} and u not in D[i]
            else:
                assert set(Dc[i]) == set(D[i]), "a vertex set changed"
    return cur, Dc, istar


# ----------------------------------------------------------------------------------------------
# oracle wrapper (tools/route_ext.c), for larger instances only

_PROC = None
_MAP = None


def _oracle():
    global _PROC
    if _PROC is None:
        here = os.path.dirname(os.path.abspath(__file__))
        src = os.path.normpath(os.path.join(here, "..", "..", "..", "tools", "route_ext.c"))
        d = tempfile.mkdtemp(prefix="a16_oracle_")
        exe = os.path.join(d, "route_ext")
        subprocess.run(["gcc", "-O2", "-o", exe, src], check=True)
        _PROC = subprocess.Popen([exe], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True,
                                 bufsize=1)
    return _PROC


def _encode(adj):
    V = sorted(adj, key=str)
    idx = {v: i for i, v in enumerate(V)}
    E = sorted((idx[u], idx[v]) for u in adj for v in adj[u] if idx[u] < idx[v])
    return V, idx, f"{len(V)} {len(E)} " + " ".join(f"{a} {c}" for a, c in E)


def oracle_sep(adj, b, pairs, witness=False, budget=None, seed=1):
    """Is b realisable with no path containing both vertices of any pair? Returns True/False
    (or None if a budget was given and exhausted); with witness=True returns the partition."""
    V, idx, g = _encode(adj)
    body = g + " " + " ".join(str(b[v]) for v in V) + f" {len(pairs)} " + " ".join(
        f"{idx[x]} {idx[y]}" for x, y in pairs)
    tag = ("W" if witness else "") + "S" + ("B" if budget else "")
    line = tag + " " + body + (f" {seed} {budget}" if budget else "")
    p = _oracle()
    p.stdin.write(line + "\n")
    p.stdin.flush()
    out = p.stdout.readline().strip()
    if out.startswith("-1"):
        raise ValueError("unsupported")
    if out.startswith("2"):
        return None
    if not out.startswith("1"):
        return False
    if not witness:
        return True
    parts = out.split("|")[1:-1]
    D = [[V[int(x)] for x in s.split()] for s in parts]
    check_partition(adj, D, b)
    for x, y in pairs:
        assert not any(x in P and y in P for P in D)
    return D


def oracle_avoid(adj, b, c, forbid, budget=None, seed=1):
    """X query: a realisation of b whose path at c avoids `forbid`."""
    V, idx, g = _encode(adj)
    f = sum(1 << idx[x] for x in forbid)
    body = g + " " + " ".join(str(b[v]) for v in V) + f" {idx[c]} {f}"
    tag = "X" + ("B" if budget else "")
    line = tag + " " + body + (f" {seed} {budget}" if budget else "")
    p = _oracle()
    p.stdin.write(line + "\n")
    p.stdin.flush()
    out = p.stdout.readline().strip()
    if out.startswith("2"):
        return None
    return out.startswith("1")
