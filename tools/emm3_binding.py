"""A binding test of EMM_3: structured graphs of minimum degree >= 3 where inequality (1) excludes
some half-sets.

Families (connected, even order n <= 12, minimum degree >= 3):
  blocks  two cliques K_a, K_c (4 <= a, c <= 6) joined by j = 3, 4, 5 edges (spread or concentrated);
          three cliques in a chain or a triangle, consecutive ones joined by 3 edges
  cones   (ED Thm 46 type) an apex joined to every vertex of two cycles C_a, C_c, which are joined
          by s = 1, 2, 3 matching edges; also with one chord in each cycle
For every half-set M: is it cut-feasible ((L) and (C), as in tools/cut_test.py), and, if so, is it
realisable (tools/realis.c, one profile query per half-set)? Reports the number of cut-infeasible half-sets (so that the test
discriminates) and every EMM failure (cut-feasible, not realisable).
Usage: python3 tools/emm3_binding.py
"""
import sys
from itertools import combinations

import networkx as nx

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import realis  # noqa: E402
from gemm_test import prepare, feasible  # noqa: E402


def cliques_joined(sizes, joins):
    G = nx.Graph(); off = []; o = 0
    for a in sizes:
        off.append(o)
        G.add_edges_from((o + i, o + j) for i in range(a) for j in range(i + 1, a))
        o += a
    for (i, k), pairs in joins.items():
        G.add_edges_from((off[i] + x, off[k] + y) for x, y in pairs)
    return G


def families():
    for a in range(4, 7):
        for c in range(a, 7):
            if (a + c) % 2 or a + c > 12:
                continue
            for j in (3, 4, 5):
                if j > min(a, c) + 2:
                    continue
                spread = [(i % a, i % c) for i in range(j)]
                conc = [(0, i % c) for i in range(j)]
                for name, pairs in (("spread", spread), ("conc", conc)):
                    yield f"K{a}+K{c} j{j} {name}", cliques_joined([a, c], {(0, 1): sorted(set(pairs))})
    for sizes in ((4, 4, 4),):
        yield "K4-K4-K4 chain", cliques_joined(sizes, {(0, 1): [(0, 0), (1, 1), (2, 2)],
                                                       (1, 2): [(3, 0), (2, 1), (1, 3)]})
        yield "K4 triangle", cliques_joined(sizes, {(0, 1): [(0, 0), (1, 1), (2, 2)],
                                                    (1, 2): [(3, 0), (2, 1), (1, 3)],
                                                    (0, 2): [(3, 2), (0, 3), (1, 0)]})
    for a in range(3, 9):
        for c in range(a, 9):
            if (a + c + 1) % 2 or a + c + 1 > 12:
                continue
            for s in (1, 2, 3):
                if s > min(a, c):
                    continue
                for chord in (False, True):
                    G = nx.Graph()
                    G.add_edges_from((i, (i + 1) % a) for i in range(a))
                    G.add_edges_from((a + i, a + (i + 1) % c) for i in range(c))
                    if chord and a >= 5 and c >= 5:
                        G.add_edges_from([(0, 2), (a, a + 2)])
                    elif chord:
                        continue
                    step_a, step_c = max(1, a // s), max(1, c // s)
                    G.add_edges_from((i * step_a % a, a + i * step_c % c) for i in range(s))
                    G.add_edges_from((a + c, v) for v in range(a + c))
                    yield f"cone C{a}+C{c} s{s}{' chord' if chord else ''}", G


tot = dict(graphs=0, halfsets=0, cut_infeasible=0, feasible_realisable=0, failures=0)
for name, G in families():
    if not nx.is_connected(G) or min(d for _, d in G.degree()) < 3 or G.number_of_nodes() % 2:
        continue
    G = nx.convert_node_labels_to_integers(G)
    prep = prepare(G); nodes = sorted(G); d = dict(G.degree())
    Ev = [v for v in nodes if d[v] % 2 == 0]
    row = dict(halfsets=0, infeasible=0, fail=0)
    for M in combinations(Ev, len(Ev) // 2):
        bb = [1 if d[v] % 2 else (2 if v in M else 0) for v in nodes]
        row["halfsets"] += 1
        ok = feasible(prep, bb)[0]
        if not ok:
            row["infeasible"] += 1
            continue
        real = realis.profile_ok(G, {v: bb[v] for v in nodes})
        if not real:
            row["fail"] += 1
            print("EMM3 FAIL", name, nx.to_graph6_bytes(G, header=False).decode().strip(), "M", M,
                  flush=True)
        else:
            tot["feasible_realisable"] += 1
    tot["graphs"] += 1
    tot["halfsets"] += row["halfsets"]; tot["cut_infeasible"] += row["infeasible"]
    tot["failures"] += row["fail"]
    print(f"{name}: n={G.number_of_nodes()} m={G.number_of_edges()} half-sets {row['halfsets']}, "
          f"cut-infeasible {row['infeasible']}, failures {row['fail']}", flush=True)
print(tot)
