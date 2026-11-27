#!/usr/bin/env python3
"""Audit A13: independent check of endpoint-min-max Theorem 21 (cut selection).

Written from the text of the manuscript only; it shares no code with
manuscripts/endpoint-min-max/scripts/ or tools/.

For a connected graph G of even order:
  1. J = the T-join (T = Ev) of a random spanning tree; F = G - J.
  2. At every v with d_J(v) > 0 build F^v (F minus the edges at v, plus v joined to every
     non-neighbour of v in G), and pair its odd vertices by edge-disjoint paths. Two pairing
     procedures are used: 'proof' (the proof of Lemma tjoin: delete cycles, then leaf-to-leaf
     paths of the remaining forest) and 'greedy' (repeatedly join an odd vertex to another odd
     vertex of its component by a random path, then delete that path).
  3. Declare transitions and end edges as in Thm 21(2), follow them, and check that the result is
     a set of edge-disjoint paths with union J pairing Ev, whose passages at each v are exactly
     the declared transitions.
  4. Goodness is checked by brute force against the DEFINITION: every transversal half-set M of
     the pairing satisfies ED inequality (1), b(W) <= |delta(W)| + 2k - d(v) - b(v), for every
     vertex v and every W subset of V - v. (No use of Lemmas 1, 6, 13.)
Intermediate claims are also checked: Lemma 19 (free degrees) on every F^v, identity (eq:split)
and Lemma 7 (parity) on every (v, Y), and the edge-disjointness and simplicity of the linking paths.

Usage:
  a13_check.py g6 FILE [trials]       all graphs in a graph6 file
  a13_check.py families [trials]      trees, cycles, K_{a,b}, random graphs, special graphs
  a13_check.py sanity                 checker sanity: count cut-infeasible half-sets at n = 6, 8;
                                      Lemma 13 (pairing criterion) vs the definition at n = 6
"""
import itertools
import random
import sys

import networkx as nx
import numpy as np


# ---------------------------------------------------------------- brute-force cut check (1)

class CutData:
    """Precomputed |delta(W)| for all W subset of V, as numpy arrays indexed by bitmask."""

    def __init__(self, G):
        self.n = n = G.number_of_nodes()
        assert sorted(G.nodes()) == list(range(n))
        self.deg = [G.degree(v) for v in range(n)]
        N = 1 << n
        W = np.arange(N, dtype=np.int64)
        self.bits = [((W >> v) & 1).astype(np.int64) for v in range(n)]
        cut = np.zeros(N, dtype=np.int64)
        for (a, c) in G.edges():
            cut += self.bits[a] ^ self.bits[c]
        self.cut = cut
        self.notv = [self.bits[v] == 0 for v in range(n)]

    def profile_ok(self, b):
        """Inequality (1) for every v and every W subset of V - v. Returns a violation or None."""
        n = self.n
        k2 = n  # 2k = n
        bW = np.zeros(1 << n, dtype=np.int64)
        for v in range(n):
            if b[v]:
                bW += b[v] * self.bits[v]
        slackW = bW - self.cut
        for v in range(n):
            rhs = k2 - self.deg[v] - b[v]
            sel = slackW[self.notv[v]]
            if sel.max() > rhs:
                idx = np.nonzero(self.notv[v])[0][int(np.argmax(sel))]
                return (v, int(idx))
        return None


def simple_profile(deg, M):
    return [1 if deg[v] % 2 else (2 if v in M else 0) for v in range(len(deg))]


def pairing_good_bruteforce(cd, pairs):
    """Every transversal of the pairing satisfies (1) at every v, W. Returns a failure or None."""
    for choice in itertools.product((0, 1), repeat=len(pairs)):
        M = {p[c] for p, c in zip(pairs, choice)}
        viol = cd.profile_ok(simple_profile(cd.deg, M))
        if viol is not None:
            return (sorted(M), viol)
    return None


# ---------------------------------------------------------------- the construction

def edge(a, c):
    return (a, c) if a < c else (c, a)


def random_spanning_tree(G, rng):
    """Random spanning tree: random-weight Kruskal (varied, not uniform)."""
    H = nx.Graph()
    H.add_nodes_from(G.nodes())
    for a, c in G.edges():
        H.add_edge(a, c, weight=rng.random())
    return nx.minimum_spanning_tree(H)


def tree_tjoin(tree, T):
    """The unique T-join inside a tree: edges whose lower side contains an odd number of T."""
    J = set()
    root = min(tree.nodes())
    parent = {root: None}
    order = []
    for v in nx.dfs_preorder_nodes(tree, root):
        order.append(v)
    for a, c in nx.dfs_edges(tree, root):
        parent[c] = a
    cnt = {v: (1 if v in T else 0) for v in tree.nodes()}
    for v in reversed(order):
        p = parent[v]
        if p is None:
            continue
        if cnt[v] % 2:
            J.add(edge(v, p))
        cnt[p] += cnt[v]
    assert cnt[root] % 2 == 0
    return J


def pair_odd_proof(H, rng):
    """Lemma tjoin, following its proof: delete cycles, then leaf-to-leaf paths."""
    H = H.copy()
    pairs, paths = [], []
    while H.number_of_edges():
        try:
            cyc = nx.find_cycle(H)
            H.remove_edges_from(cyc)
            continue
        except nx.NetworkXNoCycle:
            pass
        comps = [c for c in nx.connected_components(H) if len(c) > 1]
        comp = rng.choice(comps)
        leaves = [v for v in comp if H.degree(v) == 1]
        a, c = rng.sample(leaves, 2)
        P = nx.shortest_path(H, a, c)
        H.remove_edges_from(zip(P, P[1:]))
        pairs.append((a, c))
        paths.append(P)
    assert all(H.degree(v) % 2 == 0 for v in H)
    return pairs, paths


def pair_odd_greedy(H, rng):
    """Any odd vertex has another odd vertex in its component (handshake): join them by a random
    path and delete it. Produces arbitrary pairings by edge-disjoint paths."""
    H = H.copy()
    pairs, paths = [], []
    while True:
        odd = [v for v in H if H.degree(v) % 2]
        if not odd:
            break
        a = rng.choice(odd)
        comp = nx.node_connected_component(H, a)
        targets = [c for c in odd if c != a and c in comp]
        c = rng.choice(targets)
        # random simple path: shortest path in randomly reweighted graph
        for x, y in H.edges():
            H[x][y]['w'] = rng.random()
        P = nx.dijkstra_path(H, a, c, weight='w')
        H.remove_edges_from(zip(P, P[1:]))
        pairs.append((a, c))
        paths.append(P)
    return pairs, paths


def construct(G, rng, method):
    n = G.number_of_nodes()
    deg = [G.degree(v) for v in range(n)]
    Ev = {v for v in range(n) if deg[v] % 2 == 0}
    tree = random_spanning_tree(G, rng)
    J = tree_tjoin(tree, Ev)
    Jg = nx.Graph()
    Jg.add_nodes_from(range(n))
    Jg.add_edges_from(J)
    assert nx.is_forest(Jg)
    assert {v for v in range(n) if Jg.degree(v) % 2} == Ev, "J is not a T-join"
    Fedges = [edge(a, c) for a, c in G.edges() if edge(a, c) not in J]
    F = nx.Graph()
    F.add_nodes_from(range(n))
    F.add_edges_from(Fedges)
    assert all(F.degree(v) % 2 == 1 for v in range(n)), "Lemma 19: F not all odd"
    stats = {'Fv_disconnected': 0, 'Fv_odd_component_sizes': 0, 'v_even_paired': 0}
    trans = {}   # trans[v][x] = y (passage partner) or None (end edge vx)
    for v in range(n):
        if Jg.degree(v) == 0:
            assert v not in Ev
            continue
        Fv = nx.Graph()
        Fv.add_nodes_from(range(n))
        Fv.add_edges_from(e for e in Fedges if v not in e)
        Fv.add_edges_from((v, w) for w in range(n) if w != v and not G.has_edge(v, w))
        odd = {w for w in range(n) if Fv.degree(w) % 2}
        expect = set(Jg[v]) | ({v} if v in Ev else set())
        assert odd == expect, ("Lemma 19 fails", v, odd, expect)
        if not nx.is_connected(Fv):
            stats['Fv_disconnected'] += 1
            if any(len(c) % 2 for c in nx.connected_components(Fv)):
                stats['Fv_odd_component_sizes'] += 1
        pairs, paths = (pair_odd_proof if method == 'proof' else pair_odd_greedy)(Fv, rng)
        # verify: pairs partition odd, paths are simple paths of Fv, pairwise edge-disjoint
        seen = [x for p in pairs for x in p]
        assert sorted(seen) == sorted(odd), "pairing does not partition the odd vertices"
        used = set()
        for (a, c), P in zip(pairs, paths):
            assert P[0] == a and P[-1] == c and len(set(P)) == len(P)
            for x, y in zip(P, P[1:]):
                assert Fv.has_edge(x, y)
                assert edge(x, y) not in used, "linking paths not edge-disjoint"
                used.add(edge(x, y))
        t = {}
        for a, c in pairs:
            if a == v:
                t[c] = None
                stats['v_even_paired'] += 1
            elif c == v:
                t[a] = None
                stats['v_even_paired'] += 1
            else:
                t[a] = c
                t[c] = a
        assert set(t) == set(Jg[v])
        assert sum(1 for x in t if t[x] is None) == (1 if v in Ev else 0)
        trans[v] = t
    # follow the transitions
    routes = []
    covered = set()
    for a in sorted(Ev):
        z = [x for x in trans[a] if trans[a][x] is None][0]
        if edge(a, z) in covered:
            continue
        walk = [a, z]
        while True:
            prev, cur = walk[-2], walk[-1]
            nxt = trans[cur][prev]
            if nxt is None:
                break
            walk.append(nxt)
            assert len(walk) <= n + 1
        es = [edge(x, y) for x, y in zip(walk, walk[1:])]
        assert len(set(walk)) == len(walk), ("route repeats a vertex", walk)
        assert not covered & set(es)
        covered |= set(es)
        routes.append(walk)
    assert covered == J, "closed trails left over"
    ends = [x for R in routes for x in (R[0], R[-1])]
    assert sorted(ends) == sorted(Ev)
    # passages equal the declared transitions
    for R in routes:
        for i in range(1, len(R) - 1):
            assert trans[R[i]][R[i - 1]] == R[i + 1]
    pairs = [(R[0], R[-1]) for R in routes]
    return pairs, routes, J, stats


# ---------------------------------------------------------------- intermediate identities

def check_split_and_parity(G, J, pairs):
    """eq:split and Lemma 7 for every v and Y subset of V - v; also the pairing criterion."""
    n = G.number_of_nodes()
    deg = [G.degree(v) for v in range(n)]
    Ev = {v for v in range(n) if deg[v] % 2 == 0}
    adj = [set(G[v]) for v in range(n)]
    Fset = {edge(a, c) for a, c in G.edges()} - J
    worst = None
    for v in range(n):
        others = [w for w in range(n) if w != v]
        for r in range(len(others) + 1):
            for Y in itertools.combinations(others, r):
                Ys = set(Y)
                out = set(range(n)) - Ys - {v}
                dGv = sum(1 for y in Ys for w in adj[y] if w in out) + sum(1 for y in Ys if y not in adj[v])
                dJ = sum(1 for y in Ys for w in adj[y] if w in out and edge(y, w) in J)
                dFv = sum(1 for y in Ys for w in adj[y] if w in out and edge(y, w) in Fset) + \
                    sum(1 for y in Ys if y not in adj[v])
                assert dGv == dJ + dFv, "eq:split"
                assert (dGv - len(Ys & Ev)) % 2 == 0, "Lemma 7 parity"
                sig = sum(1 for a, c in pairs if (a in Ys) != (c in Ys))
                if sig > dGv:
                    return ('sigma', v, Y)
    return None


# ---------------------------------------------------------------- drivers

def check_graph(G, rng, trials, methods=('proof', 'greedy'), deep=False):
    G = nx.convert_node_labels_to_integers(G)
    n = G.number_of_nodes()
    deg = [G.degree(v) for v in range(n)]
    e = sum(1 for d in deg if d % 2 == 0)
    cd = CutData(G)
    agg = {'Fv_disconnected': 0, 'Fv_odd_component_sizes': 0, 'v_even_paired': 0, 'runs': 0}
    for t in range(trials):
        for m in methods:
            pairs, routes, J, st = construct(G, rng, m)
            for kk in st:
                agg[kk] += st[kk]
            agg['runs'] += 1
            fail = pairing_good_bruteforce(cd, pairs)
            if fail is not None:
                return ('FAIL', m, pairs, routes, sorted(J), fail), agg, e
            if deep:
                r = check_split_and_parity(G, J, pairs)
                if r is not None:
                    return ('FAIL-sigma', m, pairs, r), agg, e
    return None, agg, e


def run_g6(path, trials):
    rng = random.Random(20261127)
    tot = {'graphs': 0, 'e0': 0, 'runs': 0, 'Fv_disconnected': 0, 'Fv_odd_component_sizes': 0,
           'v_even_paired': 0}
    fails = []
    with open(path) as fh:
        for line in fh:
            s = line.strip()
            if not s:
                continue
            G = nx.from_graph6_bytes(s.encode())
            if G.number_of_nodes() % 2 or not nx.is_connected(G):
                continue
            deep = G.number_of_nodes() <= 6
            res, agg, e = check_graph(G, rng, trials, deep=deep)
            tot['graphs'] += 1
            tot['e0'] += (e == 0)
            for kk in ('runs', 'Fv_disconnected', 'Fv_odd_component_sizes', 'v_even_paired'):
                tot[kk] += agg[kk]
            if res is not None:
                fails.append((s, res))
                print('FAILURE', s, res, flush=True)
    print(path, tot, 'failures:', len(fails))
    return fails


def families():
    fam = []
    for m in (4, 6, 8, 10, 12):
        fam.append(('C%d' % m, nx.cycle_graph(m)))
    for a in range(1, 7):
        for b in range(a, 11):
            if (a + b) % 2 == 0 and a + b <= 12:
                fam.append(('K%d,%d' % (a, b), nx.complete_bipartite_graph(a, b)))
    for m in (2, 4, 6, 8, 10):
        G = nx.complete_bipartite_graph(2, m)
        G.add_edge(0, 1)
        fam.append(('K2,%d+hub' % m, G))
    for n in (4, 6, 8, 10, 12):
        G = nx.complete_graph(n)
        G.remove_edges_from((2 * i, 2 * i + 1) for i in range(n // 2))
        fam.append(('K%d-PM' % n, G))
        fam.append(('wheel%d' % n, nx.wheel_graph(n)))
        fam.append(('ladder%d' % n, nx.ladder_graph(n // 2)))
        fam.append(('path%d' % n, nx.path_graph(n)))
    fam.append(('petersen', nx.petersen_graph()))
    fam.append(('Q3', nx.hypercube_graph(3)))
    fam.append(('KsOeBW??G`?A (MM Thm 7.5)', nx.from_graph6_bytes(b'KsOeBW??G`?A')))
    # all trees of order 8, 10, 12
    for n in (8, 10, 12):
        for i, T in enumerate(nx.nonisomorphic_trees(n)):
            fam.append(('tree%d_%d' % (n, i), T))
    rng = random.Random(1127)
    for n in (10, 12):
        cnt = 0
        while cnt < (200 if n == 10 else 60):
            p = rng.choice([.15, .2, .25, .3, .4, .5, .6, .7, .8])
            G = nx.gnp_random_graph(n, p, seed=rng.randrange(10 ** 9))
            if nx.is_connected(G):
                fam.append(('gnp%d_%.2f_%d' % (n, p, cnt), G))
                cnt += 1
    # even-degree-heavy random graphs: random 4-regular and graphs with many even vertices
    for n in (10, 12):
        for i in range(20):
            G = nx.random_regular_graph(4, n, seed=rng.randrange(10 ** 9))
            if nx.is_connected(G):
                fam.append(('4reg%d_%d' % (n, i), G))
    return fam


def run_families(trials):
    rng = random.Random(4166)
    fails = []
    counts = {}
    for name, G in families():
        res, agg, e = check_graph(G, rng, trials)
        key = name.split('_')[0].rstrip('0123456789,') if not name.startswith('K') else 'Kab etc'
        counts[key] = counts.get(key, 0) + 1
        if res is not None:
            fails.append((name, res))
            print('FAILURE', name, nx.to_graph6_bytes(nx.convert_node_labels_to_integers(G), header=False).strip(), res, flush=True)
    print('families checked:', sum(counts.values()), counts, 'failures:', len(fails))
    return fails


def sanity():
    """(i) Count cut-infeasible half-sets with the brute-force checker: the manuscript reports
    518/18 at n = 6 and 101,714/2,100 at n = 8 (EMM holds at n <= 8, so non-realisable =
    cut-infeasible). (ii) At n = 6, compare Lemma 13's criterion with the definition on every
    pairing of Ev. (iii) Show that random pairings are often bad, so the check is not vacuous."""
    rng = random.Random(7)
    for path in ('data/conn6.g6', 'data/conn8.g6'):
        hs = bad = graphs = 0
        rnd_pairings = rnd_bad = 0
        lemma13_checked = 0
        with open(path) as fh:
            for line in fh:
                G = nx.from_graph6_bytes(line.strip().encode())
                n = G.number_of_nodes()
                deg = [G.degree(v) for v in range(n)]
                Ev = [v for v in range(n) if deg[v] % 2 == 0]
                if not Ev:
                    continue
                graphs += 1
                cd = CutData(G)
                feas = {}
                for M in itertools.combinations(Ev, len(Ev) // 2):
                    hs += 1
                    ok = cd.profile_ok(simple_profile(deg, set(M))) is None
                    feas[frozenset(M)] = ok
                    bad += (not ok)
                # random pairing
                E2 = Ev[:]
                rng.shuffle(E2)
                pr = [(E2[2 * i], E2[2 * i + 1]) for i in range(len(E2) // 2)]
                rnd_pairings += 1
                good = all(feas[frozenset(p[c] for p, c in zip(pr, ch))]
                           for ch in itertools.product((0, 1), repeat=len(pr)))
                rnd_bad += (not good)
                if n == 6:
                    # Lemma 13 on every pairing of Ev
                    for prs in all_pairings(Ev):
                        good = all(feas[frozenset(p[c] for p, c in zip(prs, ch))]
                                   for ch in itertools.product((0, 1), repeat=len(prs)))
                        crit = sigma_criterion(G, prs)
                        assert good == crit, ('Lemma 13 mismatch', line, prs)
                        lemma13_checked += 1
        print(path, 'graphs(e>=2):', graphs, 'half-sets:', hs, 'cut-infeasible:', bad,
              '| random pairings:', rnd_pairings, 'bad:', rnd_bad,
              '| Lemma 13 pairings checked:', lemma13_checked)


def all_pairings(L):
    if not L:
        yield []
        return
    a = L[0]
    for i in range(1, len(L)):
        rest = L[1:i] + L[i + 1:]
        for p in all_pairings(rest):
            yield [(a, L[i])] + p


def sigma_criterion(G, pairs):
    n = G.number_of_nodes()
    adj = [set(G[v]) for v in range(n)]
    for v in range(n):
        others = [w for w in range(n) if w != v]
        for r in range(len(others) + 1):
            for Y in itertools.combinations(others, r):
                Ys = set(Y)
                out = set(range(n)) - Ys - {v}
                dGv = sum(1 for y in Ys for w in adj[y] if w in out) + sum(1 for y in Ys if y not in adj[v])
                sig = sum(1 for a, c in pairs if (a in Ys) != (c in Ys))
                if sig > dGv:
                    return False
    return True


if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'g6':
        trials = int(sys.argv[3]) if len(sys.argv) > 3 else 3
        f = run_g6(sys.argv[2], trials)
        sys.exit(1 if f else 0)
    elif mode == 'families':
        trials = int(sys.argv[2]) if len(sys.argv) > 2 else 3
        f = run_families(trials)
        sys.exit(1 if f else 0)
    elif mode == 'sanity':
        sanity()
