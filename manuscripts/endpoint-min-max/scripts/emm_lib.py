"""Shared helpers for the endpoint min-max (EMM) scripts.

Graphs are networkx graphs relabelled 0..n-1.  The C helpers in tools/ are compiled on first use
into a temporary directory:
    tools/cutfeas.c  all cut-feasible half-sets of a graph (inequality (1) of ED Section 12.4)
    tools/capsub.c   cap functions of the cut inequalities and their submodularity
    tools/realis.c   the exact realisability oracle (through tools/realis.py)
"""
import itertools
import os
import random
import subprocess
import sys
import tempfile

import warnings

import networkx as nx

warnings.filterwarnings("ignore", category=UserWarning)

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
TOOLS = os.path.join(ROOT, "tools")
DATA = os.path.join(ROOT, "data")
sys.path.insert(0, TOOLS)
import realis  # noqa: E402

_BIN = {}


def binary(name):
    """Compile tools/<name>.c once and return the path of the executable."""
    if name not in _BIN:
        out = os.path.join(tempfile.gettempdir(), f"emm_{name}")
        src = os.path.join(TOOLS, name + ".c")
        if not os.path.exists(out) or os.path.getmtime(out) < os.path.getmtime(src):
            subprocess.check_call(["gcc", "-O2", "-o", out, src])
        _BIN[name] = out
    return _BIN[name]


def encode(G):
    return f"{G.number_of_nodes()} {G.number_of_edges()} " + " ".join(f"{a} {b}" for a, b in G.edges())


def run_lines(name, graphs):
    """Feed every graph to tools/<name> and return one output line per graph."""
    if not graphs:
        return []
    inp = "\n".join(encode(G) for G in graphs) + "\n"
    out = subprocess.run([binary(name)], input=inp, capture_output=True, text=True, check=True).stdout
    lines = out.split("\n")[: len(graphs)]
    assert len(lines) == len(graphs)
    return lines


def even_vertices(G):
    return [v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0]


def cut_feasible(graphs):
    """For each graph, the set of cut-feasible half-sets, as frozensets of vertices."""
    res = []
    for G, line in zip(graphs, run_lines("cutfeas", graphs)):
        masks = list(map(int, line.split()))[1:]
        res.append({frozenset(v for v in G if M >> v & 1) for M in masks})
    return res


def realisable_halfsets(G):
    """Half-sets M of Ev whose simple profile is realised by exactly n/2 paths."""
    Ev, fam = realis.family(G)
    fam = set(fam)
    return {frozenset(M) for M in itertools.combinations(Ev, len(Ev) // 2) if frozenset(M) in fam}


def critical(G):
    """p(G) = n/2, i.e. no realisable set of fewer than e/2 even vertices (connected G)."""
    Ev, fam = realis.family(G)
    return not any(len(S) < len(Ev) // 2 for S in fam)


def relabel(G):
    return nx.convert_node_labels_to_integers(G)


# ----------------------------------------------------------------------------------------------
# graph families

def all_connected(n):
    """All connected graphs of order n (n = 6 or 8) with at least two even vertices."""
    out = []
    for line in open(os.path.join(DATA, f"conn{n}.g6")):
        G = relabel(nx.from_graph6_bytes(line.strip().encode()))
        if len(even_vertices(G)) >= 2:
            out.append(G)
    return out


def random_sample(n=10, count=250, seed=20261127, ps=(0.3, 0.4, 0.5, 0.6, 0.7, 0.8)):
    """Connected G(n, p) graphs with at least two even vertices, deterministic in `seed`."""
    rng = random.Random(seed)
    out = []
    while len(out) < count:
        p = ps[len(out) % len(ps)]
        G = nx.gnp_random_graph(n, p, seed=rng.randrange(2**31))
        if nx.is_connected(G) and len(even_vertices(G)) >= 2:
            out.append(G)
    return out


def _clique_pair(a, b, links):
    G = nx.disjoint_union(nx.complete_graph(a), nx.complete_graph(b))
    G.add_edges_from((x, a + y) for x, y in links)
    return G


def _theta(lengths):
    """Two poles 0, 1 joined by internally disjoint paths with the given numbers of inner vertices."""
    G = nx.Graph()
    G.add_nodes_from([0, 1])
    nxt = 2
    for L in lengths:
        prev = 0
        for _ in range(L):
            G.add_edge(prev, nxt)
            prev = nxt
            nxt += 1
        G.add_edge(prev, 1)
    return G


def _cone_paths(sizes, extra=()):
    """Apex 0 joined to every vertex of a disjoint union of paths of the given orders."""
    G = nx.Graph()
    nxt = 1
    for s in sizes:
        nodes = list(range(nxt, nxt + s))
        nx.add_path(G, nodes)
        G.add_nodes_from(nodes)
        nxt += s
    for v in range(1, nxt):
        G.add_edge(0, v)
    G.add_edges_from(extra)
    return G


def _two_sum(A, B, glue_edge=True):
    """Glue A and B along an edge (kept once) or at two vertices (both edges kept would be a multigraph,
    so for glue_edge=False the edge between the glued vertices is removed from B)."""
    B = nx.relabel_nodes(B, {v: v + A.number_of_nodes() for v in B})
    a0, a1 = 0, 1
    b0, b1 = A.number_of_nodes(), A.number_of_nodes() + 1
    if not glue_edge and B.has_edge(b0, b1):
        B.remove_edge(b0, b1)
    G = nx.union(A, B)
    G = nx.contracted_nodes(G, a0, b0, self_loops=False)
    G = nx.contracted_nodes(G, a1, b1, self_loops=False)
    return nx.Graph(G)


def bottleneck(max_n=10):
    """Small graphs with a sparse cut: cliques joined by 1-3 edges, theta graphs, cones over unions
    of paths (ED Section 12.4), and 2-sums of small dense graphs.  Orders 6..max_n, even only."""
    out = []
    for n in range(6, max_n + 1, 2):
        for a in range(3, n - 2):
            b = n - a
            if a > b:
                continue
            for links in ([(0, 0)], [(0, 0), (1, 1)], [(0, 0), (0, 1)], [(0, 0), (1, 1), (2, 2)],
                          [(0, 0), (0, 1), (0, 2)], [(0, 0), (1, 0), (2, 0)]):
                if max(x for x, _ in links) < a and max(y for _, y in links) < b:
                    out.append(_clique_pair(a, b, links))
        for lengths in itertools.combinations_with_replacement(range(0, n - 1), 3):
            if sum(lengths) == n - 2 and lengths.count(0) <= 1:
                out.append(_theta(lengths))
        for r in range(1, 4):
            for sizes in itertools.combinations_with_replacement(range(1, n), r):
                if sum(sizes) == n - 1:
                    out.append(_cone_paths(sizes))
    # the eight-vertex example of ED Section 12.4: apex over paths (0,1,2), (3,4,5,6) plus edge 14
    E8 = nx.Graph([(0, 1), (1, 2), (3, 4), (4, 5), (5, 6), (1, 4)] + [(7, v) for v in range(7)])
    out.append(E8)
    small = [nx.complete_graph(4), nx.complete_graph(5), nx.wheel_graph(5), nx.complete_graph(6),
             nx.cycle_graph(4), nx.cycle_graph(5)]
    for A, B in itertools.combinations_with_replacement(small, 2):
        for glue in (True, False):
            G = _two_sum(A, B, glue)
            if G.number_of_nodes() % 2 == 0 and G.number_of_nodes() <= max_n:
                out.append(G)
    res, seen = [], set()
    for G in out:
        G = relabel(G)
        if not nx.is_connected(G) or G.number_of_nodes() % 2 or len(even_vertices(G)) < 2:
            continue
        key = nx.weisfeiler_lehman_graph_hash(G, iterations=4)
        if any(nx.is_isomorphic(G, H) for H in [H for k, H in seen if k == key]):
            continue
        seen.add((key, G))
        res.append(G)
    return res
