"""A38 audit library (independent of manuscripts/overview/scripts).

Exact enumeration of path decompositions, forest T-joins and rootings, and the
predicates of the overview paper (forest stepping, stripping, terminal at parents).

Graphs: vertices 0..n-1, edges as a list of 2-tuples (u, v), u < v.
A path is a tuple of vertices (length >= 2 vertices, i.e. >= 1 edge), all distinct.
"""
import itertools
from collections import defaultdict


def norm(u, v):
    return (u, v) if u < v else (v, u)


class G:
    def __init__(self, n, edges):
        self.n = n
        self.edges = sorted(set(norm(u, v) for (u, v) in edges))
        self.eidx = {e: i for i, e in enumerate(self.edges)}
        self.adj = [[] for _ in range(n)]
        for (u, v) in self.edges:
            self.adj[u].append(v)
            self.adj[v].append(u)
        for a in self.adj:
            a.sort()

    def deg(self, v):
        return len(self.adj[v])

    def m(self):
        return len(self.edges)

    def odd(self):
        return [v for v in range(self.n) if self.deg(v) % 2 == 1]

    def even_pos(self):
        return [v for v in range(self.n) if self.deg(v) > 0 and self.deg(v) % 2 == 0]

    def minus(self, rem):
        rem = set(norm(*e) for e in rem)
        return G(self.n, [e for e in self.edges if e not in rem])

    def plus(self, add):
        return G(self.n, self.edges + [norm(*e) for e in add])

    def delvert(self, z):
        """Delete all edges at z (z stays as an isolated vertex, labels kept)."""
        return G(self.n, [e for e in self.edges if z not in e])

    def components(self, verts=None):
        seen = set()
        comps = []
        vs = range(self.n) if verts is None else verts
        for s in vs:
            if s in seen:
                continue
            comp = [s]
            seen.add(s)
            i = 0
            while i < len(comp):
                u = comp[i]
                i += 1
                for w in self.adj[u]:
                    if w not in seen:
                        seen.add(w)
                        comp.append(w)
            comps.append(comp)
        return comps


def path_edges(P):
    return [norm(P[i], P[i + 1]) for i in range(len(P) - 1)]


# ---------------------------------------------------------------- decompositions

def decomps(g, maxpaths):
    """All path decompositions of g into at most maxpaths paths (each exactly once)."""
    m = g.m()
    adj = g.adj
    eidx = g.eidx

    def odd_count(mask):
        d = [0] * g.n
        for i in range(m):
            if mask >> i & 1:
                u, v = g.edges[i]
                d[u] += 1
                d[v] += 1
        return sum(1 for x in d if x % 2)

    def ext(start, avoid, mask):
        """All simple walks from start (list of vertex lists, starting [start]) using edges of
        mask and avoiding vertices in avoid; includes the trivial one."""
        out = []
        stack = [([start], frozenset([start]) | avoid)]
        while stack:
            seq, used = stack.pop()
            out.append(seq)
            u = seq[-1]
            for w in adj[u]:
                if w in used:
                    continue
                i = eidx[norm(u, w)]
                if not (mask >> i & 1):
                    continue
                stack.append((seq + [w], used | {w}))
        return out

    def rec(mask, left):
        if mask == 0:
            yield []
            return
        if left == 0:
            return
        if (odd_count(mask) + 1) // 2 > left:
            return
        i = (mask & -mask).bit_length() - 1
        u, v = g.edges[i]
        mask1 = mask & ~(1 << i)
        for fwd in ext(v, frozenset([u]), mask1):
            fset = frozenset(fwd)
            mf = mask1
            for j in range(len(fwd) - 1):
                mf &= ~(1 << eidx[norm(fwd[j], fwd[j + 1])])
            for bwd in ext(u, fset, mf):
                mb = mf
                for j in range(len(bwd) - 1):
                    mb &= ~(1 << eidx[norm(bwd[j], bwd[j + 1])])
                P = tuple(list(reversed(bwd)) + fwd)
                for rest in rec(mb, left - 1):
                    yield [P] + rest

    full = (1 << m) - 1
    yield from rec(full, maxpaths)


def ends(D, n):
    b = [0] * n
    for P in D:
        b[P[0]] += 1
        b[P[-1]] += 1
    return b


def is_path_decomp(g, D):
    seen = set()
    for P in D:
        if len(P) < 2 or len(set(P)) != len(P):
            return False
        for e in path_edges(P):
            if e not in g.eidx or e in seen:
                return False
            seen.add(e)
    return len(seen) == g.m()


def is_parity_decomp(g, D):
    b = ends(D, g.n)
    return all(b[v] == g.deg(v) % 2 for v in range(g.n))


# ---------------------------------------------------------------- forests and joins

def tjoins(g, T):
    """All T-joins of g (edge sets whose odd-degree vertex set is exactly T), via a spanning
    forest and the cycle space. Returns list of frozensets of edges."""
    T = set(T)
    n = g.n
    parent = [None] * n
    order = []
    seen = [False] * n
    tree = set()
    for s in range(n):
        if seen[s]:
            continue
        seen[s] = True
        q = [s]
        comp = []
        while q:
            u = q.pop()
            comp.append(u)
            order.append(u)
            for w in g.adj[u]:
                if not seen[w]:
                    seen[w] = True
                    parent[w] = u
                    tree.add(norm(u, w))
                    q.append(w)
        if len(T & set(comp)) % 2:
            return []
    # unique T-join in the forest: process vertices in reverse order
    cnt = [1 if v in T else 0 for v in range(n)]
    phi0 = set()
    for u in reversed(order):
        if parent[u] is not None:
            if cnt[u] % 2:
                phi0.add(norm(u, parent[u]))
                cnt[parent[u]] += 1
    # fundamental cycles
    def tree_path(a):
        p = [a]
        while parent[p[-1]] is not None:
            p.append(parent[p[-1]])
        return p

    cycles = []
    for e in g.edges:
        if e in tree:
            continue
        a, b = e
        pa, pb = tree_path(a), tree_path(b)
        sa = set(pa)
        lca = next(x for x in pb if x in sa)
        cyc = {e}
        for seq in (pa, pb):
            for i in range(len(seq) - 1):
                if seq[i] == lca:
                    break
                cyc.add(norm(seq[i], seq[i + 1]))
        cycles.append(frozenset(cyc))
    out = []
    for bits in itertools.product((0, 1), repeat=len(cycles)):
        s = set(phi0)
        for bt, c in zip(bits, cycles):
            if bt:
                s ^= c
        out.append(frozenset(s))
    return out


def is_forest(n, edges):
    par = list(range(n))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for (u, v) in edges:
        a, b = f(u), f(v)
        if a == b:
            return False
        par[a] = b
    return True


def forest_tjoins(g, T):
    return [phi for phi in tjoins(g, T) if is_forest(g.n, phi)]


def rootings(n, phi):
    """All rootings of the forest phi: yields parent dicts {child: parent}."""
    fg = G(n, list(phi))
    comps = [c for c in fg.components() if len(c) > 1]
    for roots in itertools.product(*comps):
        par = {}
        for root in roots:
            stack = [root]
            seen = {root}
            while stack:
                u = stack.pop()
                for w in fg.adj[u]:
                    if w not in seen:
                        seen.add(w)
                        par[w] = u
                        stack.append(w)
        yield par


def children_count(par):
    c = defaultdict(int)
    for v, p in par.items():
        c[p] += 1
    return c


# ---------------------------------------------------------------- predicates

def end_path(D, v):
    """Paths of D ending at v (list of indices)."""
    return [i for i, P in enumerate(D) if P[0] == v or P[-1] == v]


def base_ok(D, par):
    """(i) p(v) not on the path ending at v (every path ending at v); (ii) siblings end
    different paths. Assumes each child ends exactly one path (checked)."""
    q = {}
    for v, p in par.items():
        idx = end_path(D, v)
        if len(idx) != 1:
            return False
        q[v] = idx[0]
        if p in D[idx[0]]:
            return False
    sib = defaultdict(list)
    for v, p in par.items():
        sib[p].append(q[v])
    for p, lst in sib.items():
        if len(set(lst)) != len(lst):
            return False
    return True


def append_forest(D, par):
    """Lemma 3.1: append p(v)v to the path ending at v, at its end v. Returns new list."""
    out = []
    for P in D:
        P = list(P)
        a, b = P[0], P[-1]
        if a in par:
            P = [par[a]] + P
        if b in par:
            P = P + [par[b]]
        out.append(tuple(P))
    return out


def terminal_mask_set(D):
    """Set of (vertex, edge) terminal incidences of D."""
    s = set()
    for P in D:
        s.add((P[0], norm(P[0], P[1])))
        s.add((P[-1], norm(P[-1], P[-2])))
    return s


def terminal_at_parents(D, par):
    s = terminal_mask_set(D)
    return all((p, norm(p, v)) in s for v, p in par.items())


def strip(D, phi):
    """Lemma 3.2: delete every edge of phi from its path (it must be an end edge), drop empties."""
    phi = set(norm(*e) for e in phi)
    out = []
    for P in D:
        P = list(P)
        if len(P) >= 2 and norm(P[0], P[1]) in phi:
            P = P[1:]
        if len(P) >= 2 and norm(P[-1], P[-2]) in phi:
            P = P[:-1]
        if len(P) >= 2:
            out.append(tuple(P))
    return out


def graph6(s):
    import networkx as nx
    H = nx.from_graph6_bytes(s.encode())
    return G(H.number_of_nodes(), list(H.edges()))


def connectivity(g):
    import networkx as nx
    H = nx.Graph()
    H.add_nodes_from(range(g.n))
    H.add_edges_from(g.edges)
    return nx.node_connectivity(H)


# ---------------------------------------------------------------- constrained search

def find_decomp(g, maxpaths, cap, path_ok=None):
    """First path decomposition of g into at most maxpaths paths in which every vertex v ends at
    most cap[v] paths and every path P satisfies path_ok(P) (if given); None if there is none.
    With cap[v] = deg(v) % 2 and maxpaths = (#odd)/2 this searches parity decompositions."""
    m = g.m()
    adj = g.adj
    eidx = g.eidx
    used_end = [0] * g.n

    def ext(start, avoid, mask):
        out = []
        stack = [([start], frozenset([start]) | avoid)]
        while stack:
            seq, used = stack.pop()
            out.append(seq)
            u = seq[-1]
            for w in adj[u]:
                if w in used:
                    continue
                i = eidx[norm(u, w)]
                if not (mask >> i & 1):
                    continue
                stack.append((seq + [w], used | {w}))
        return out

    def odd_count(mask):
        d = [0] * g.n
        for i in range(m):
            if mask >> i & 1:
                u, v = g.edges[i]
                d[u] += 1
                d[v] += 1
        return sum(1 for x in d if x % 2)

    def rec(mask, left):
        if mask == 0:
            return []
        if left == 0:
            return None
        if (odd_count(mask) + 1) // 2 > left:
            return None
        i = (mask & -mask).bit_length() - 1
        u, v = g.edges[i]
        mask1 = mask & ~(1 << i)
        for fwd in ext(v, frozenset([u]), mask1):
            b_end = fwd[-1]
            fset = frozenset(fwd)
            mf = mask1
            for j in range(len(fwd) - 1):
                mf &= ~(1 << eidx[norm(fwd[j], fwd[j + 1])])
            for bwd in ext(u, fset, mf):
                a_end = bwd[-1]
                if used_end[a_end] >= cap[a_end] or used_end[b_end] >= cap[b_end]:
                    continue
                P = tuple(list(reversed(bwd)) + fwd)
                if path_ok is not None and not path_ok(P):
                    continue
                mb = mf
                for j in range(len(bwd) - 1):
                    mb &= ~(1 << eidx[norm(bwd[j], bwd[j + 1])])
                used_end[a_end] += 1
                used_end[b_end] += 1
                rest = rec(mb, left - 1)
                used_end[a_end] -= 1
                used_end[b_end] -= 1
                if rest is not None:
                    return [P] + rest
        return None

    return rec((1 << m) - 1, maxpaths)


def find_base(g, par):
    """A Lovasz decomposition of g (at most one even vertex) with (i) p(v) not on the path ending
    at the child v and (ii) siblings ending different paths; None if none exists."""
    cap = [g.deg(v) % 2 for v in range(g.n)]
    np_ = sum(cap) // 2

    def ok(P):
        a, b = P[0], P[-1]
        if a in par and par[a] in P:
            return False
        if b in par and par[b] in P:
            return False
        if a in par and b in par and par[a] == par[b]:
            return False
        return True
    return find_decomp(g, np_, cap, ok)
