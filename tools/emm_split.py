"""Splitting off for the EMM cut conditions.

Splitting a pair ux, uy (x, y non-adjacent neighbours of u) replaces them by the edge xy. The
profile b and the number of paths p are unchanged, so the class EMM+ is preserved. A partition of
the split graph G' lifts to G (replace xy by x u y) unless the path through xy also visits u. The
lift is automatic only when u is isolated in G' (d(u) = 2, b(u) = 0: smoothing, Lemma 7.7(b)).

This script tests the cut side, an analogue of Mader's splitting lemma. For every cut-feasible
instance of the class EMM+ (p >= ceil(n/2)) and every vertex u, does some pair at u split off
while keeping (L) and (C)? With option "stuck", it reads the stuck instances of a log of
tools/emm_template.py instead of enumerating.

Usage: python3 tools/emm_split.py FILE.g6            (all EMM+ instances, reduced)
       python3 tools/emm_split.py --stuck LOG          (the stuck instances listed in LOG)
       python3 tools/emm_split.py --lift LOG           (for each cut-preserving split at a vertex
                                                        with b = 0, count the partitions of the
                                                        split graph that do not lift)
"""
import sys
import re
from collections import Counter
from itertools import combinations

import networkx as nx

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from gemm_test import prepare, feasible, profiles  # noqa: E402
from emm_template import reducible  # noqa: E402


def splits(G, bb, u):
    """Pairs {x, y} at u whose splitting keeps cut-feasibility."""
    out = []
    for x, y in combinations(sorted(G[u]), 2):
        if G.has_edge(x, y):
            continue
        H = G.copy(); H.remove_edge(u, x); H.remove_edge(u, y); H.add_edge(x, y)
        if feasible(prepare(H), list(bb))[0]:
            out.append((x, y))
    return out


def classify(G, bb, t):
    anyv = False
    for u in G:
        if G.degree(u) < 3:
            continue
        sp = splits(G, bb, u)
        key = f"d{G.degree(u)}_b{'0' if bb[u] == 0 else '+'}"
        t[key + ("_split" if sp else "_NOSPLIT")] += 1
        anyv |= bool(sp)
    t["instance_has_split" if anyv else "INSTANCE_NO_SPLIT"] += 1


def main():
    t = Counter()
    if sys.argv[1] == "--stuck":
        for line in open(sys.argv[2]):
            if not line.startswith("STUCK"):
                continue
            g6 = line.split()[1]
            bb = tuple(map(int, re.search(r"b \(([^)]*)\)", line).group(1).split(",")))
            G = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(g6.encode()))
            res = {u: splits(G, bb, u) for u in G if G.degree(u) >= 3}
            print(g6, bb, {u: s for u, s in res.items() if s})
            classify(G, bb, t)
    else:
        for G in nx.read_graph6(sys.argv[1]):
            G = nx.convert_node_labels_to_integers(G)
            prep = prepare(G)
            n = G.number_of_nodes()
            for bb in profiles(prep[1]):
                if sum(bb) < n or not feasible(prep, list(bb))[0] or reducible(G, bb):
                    continue
                classify(G, bb, t)
    print(dict(sorted(t.items())))


if __name__ == "__main__" and sys.argv[1] != "--lift":
    main()


def all_partitions(G, bb):
    """All partitions of E(G) into paths with profile bb (small graphs only)."""
    E = {frozenset(e) for e in G.edges()}
    out = []

    def rec(rem, b, acc):
        if not rem:
            if all(v == 0 for v in b.values()):
                out.append(list(acc))
            return
        a = min(v for v in b if b[v] > 0) if any(b.values()) else None
        if a is None:
            return
        # grow a path from a
        def grow(path, used):
            last = path[-1]
            if len(path) >= 2 and b[last] > 0 and last != a:
                b[a] -= 1; b[last] -= 1
                acc.append(list(path))
                rec(rem - used, b, acc)
                acc.pop()
                b[a] += 1; b[last] += 1
            for w in G[last]:
                e = frozenset((last, w))
                if e in rem and e not in used and w not in path:
                    path.append(w); used.add(e)
                    grow(path, used)
                    path.pop(); used.discard(e)
        grow([a], set())
    rec(E, dict(bb), [])
    # remove duplicates arising from symmetric choices
    seen, uniq = set(), []
    for P in out:
        key = frozenset(frozenset(frozenset(e) for e in zip(p, p[1:])) for p in P)
        if key not in seen:
            seen.add(key); uniq.append(P)
    return uniq


def lift_report(G, bb):
    """For each cut-preserving split at a vertex with b = 0: (u, x, y, #partitions, #non-liftable)."""
    rep = []
    for u in G:
        if bb[u] != 0 or G.degree(u) < 4:
            continue
        for x, y in splits(G, [bb[v] for v in sorted(G)], u):
            H = G.copy(); H.remove_edge(u, x); H.remove_edge(u, y); H.add_edge(x, y)
            parts = all_partitions(H, {v: bb[v] for v in H})
            bad = sum(1 for P in parts if any(u in p and any({p[i], p[i + 1]} == {x, y}
                                                             for i in range(len(p) - 1)) for p in P))
            rep.append((u, x, y, len(parts), bad))
    return rep


if __name__ == "__main__" and len(sys.argv) > 2 and sys.argv[1] == "--lift":
    for line in open(sys.argv[2]):
        if not line.startswith("STUCK"):
            continue
        g6 = line.split()[1]
        bb = tuple(map(int, re.search(r"b \(([^)]*)\)", line).group(1).split(",")))
        G = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(g6.encode()))
        rep = lift_report(G, {v: bb[v] for v in G})
        good = [r for r in rep if r[3] > 0 and r[4] == 0]
        print(g6, bb, "splits", len(rep), "always-lifting", len(good), "examples", rep[:3], flush=True)
