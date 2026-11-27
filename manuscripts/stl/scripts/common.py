"""Shared helpers for the STL experiments (session claude/stl).

Graphs are networkx graphs on vertices 0..n-1.  The oracle is tools/stl.c (compiled to ./stl).
"""
import os, subprocess, itertools
import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
STL_BIN = os.path.join(HERE, 'stl')
REALIS_BIN = os.path.join(HERE, 'route_ext')


def build():
    src = os.path.join(HERE, '..', '..', '..', 'tools')
    for name, out in (('stl.c', STL_BIN), ('route_ext.c', REALIS_BIN)):
        s = os.path.join(src, name)
        if not os.path.exists(out) or os.path.getmtime(out) < os.path.getmtime(s):
            subprocess.check_call(['gcc', '-O2', '-o', out, s])


class Oracle:
    """Persistent pipe to the stl oracle."""
    def __init__(self, binary=None):
        build()
        self.p = subprocess.Popen([binary or STL_BIN], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  text=True, bufsize=1)

    def query(self, G, prof, z, r, star, thr, witness=False, seed=None, budget=0, req=None, forb=None,
              pairs=None):
        """req/forb: dict v -> neighbour (terminal-edge constraints); pairs: dict c -> set of allowed
        w for transitions c - z - w."""
        n = G.number_of_nodes(); E = list(G.edges())
        useT = req is not None or forb is not None
        tag = ('W' if witness else '') + 'Q' + ('T' if useT else '') + ('M' if pairs is not None else '') + \
              ('B' if seed is not None else '')
        parts = [tag, str(n), str(len(E))]
        for u, v in E:
            parts += [str(u), str(v)]
        parts += [str(prof[v]) for v in range(n)]
        parts += [str(z), str(r), str(star), str(thr)]
        if useT:
            req = req or {}; forb = forb or {}
            parts += [str(req.get(v, -1)) for v in range(n)]
            parts += [str(forb.get(v, -1)) for v in range(n)]
        if pairs is not None:
            parts += [str(sum(1 << w for w in pairs.get(v, ()))) for v in range(n)]
        if seed is not None:
            parts += [str(seed), str(budget)]
        self.p.stdin.write(' '.join(parts) + '\n'); self.p.stdin.flush()
        line = self.p.stdout.readline().strip()
        if witness:
            head, *rest = line.split('|')
            val = int(head)
            paths = [list(map(int, s.split())) for s in rest if s.strip()]
            return val, paths
        return int(line)


class Realis:
    """Persistent pipe to tools/route_ext.c (plain profile realisability, query P)."""
    def __init__(self):
        build()
        self.p = subprocess.Popen([REALIS_BIN], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  text=True, bufsize=1)

    def realisable(self, G, prof, seed=None, budget=0):
        n = G.number_of_nodes(); E = list(G.edges())
        tag = 'P' + ('B' if seed is not None else '')
        parts = [tag, str(n), str(len(E))]
        for u, v in E:
            parts += [str(u), str(v)]
        parts += [str(prof[v]) for v in range(n)]
        if seed is not None:
            parts += [str(seed), str(budget)]
        self.p.stdin.write(' '.join(parts) + '\n'); self.p.stdin.flush()
        return int(self.p.stdout.readline().strip())


def relabel(G):
    return nx.convert_node_labels_to_integers(G, ordering='sorted')


def even_vertices(G):
    return [v for v in G if G.degree(v) % 2 == 0]


def has_matching_cut(G):
    """Brute force over bipartitions (n <= ~20): edges across form a matching."""
    nodes = list(G.nodes()); n = len(nodes)
    if n < 2:
        return False
    idx = {v: i for i, v in enumerate(nodes)}
    adj = [0] * n
    for u, v in G.edges():
        adj[idx[u]] |= 1 << idx[v]; adj[idx[v]] |= 1 << idx[u]
    full = (1 << n) - 1
    # fix vertex 0 on side X
    for mask in range(1, 1 << (n - 1)):
        X = (mask << 1) | 1
        if X == full:
            continue
        Y = full ^ X
        ok = True
        for i in range(n):
            other = Y if (X >> i) & 1 else X
            if bin(adj[i] & other).count('1') > 1:
                ok = False; break
        if ok:
            return True
    return False


def has_matching_cut_fast(G):
    """Matching-cut test by propagation (exact): choose a pair of adjacent... uses simple
    branching: a vertex with >= 2 neighbours on one side must be on that side."""
    nodes = list(G.nodes()); n = len(nodes)
    idx = {v: i for i, v in enumerate(nodes)}
    nb = [[idx[w] for w in G[v]] for v in nodes]

    def propagate(side):
        changed = True
        while changed:
            changed = False
            for v in range(n):
                cnt = [0, 0]
                for w in nb[v]:
                    if side[w] >= 0:
                        cnt[side[w]] += 1
                for s in (0, 1):
                    if cnt[s] >= 2:
                        if side[v] == 1 - s:
                            return False
                        if side[v] < 0:
                            side[v] = s; changed = True
            # a vertex on side s with >= 2 neighbours ... handled above (neighbour count rule):
            for v in range(n):
                if side[v] < 0:
                    continue
                # v has at most one neighbour on the other side
                other = [w for w in nb[v] if side[w] == 1 - side[v]]
                if len(other) > 1:
                    return False
        return True

    def rec(side):
        side = side[:]
        if not propagate(side):
            return False
        free = [v for v in range(n) if side[v] < 0]
        if not free:
            return 0 in side and 1 in side
        v = free[0]
        for s in (0, 1):
            s2 = side[:]; s2[v] = s
            if rec(s2):
                return True
        return False

    # X contains vertex 0, Y contains some vertex u
    for u in range(1, n):
        side = [-1] * n; side[0] = 0; side[u] = 1
        if rec(side):
            return True
    return False
