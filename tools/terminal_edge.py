"""Test terminal-edge prescriptions in Lovasz's theorem for all-odd graphs.

TEL1: all-odd connected H, vertex u, edge uy: some decomposition into |H|/2 paths
      (necessarily one end per vertex) has the end at u on the edge uy.
TEL2: same with two prescriptions (u via uy, v via vx), u != v.
"""
import itertools
import sys
import networkx as nx
from ortools.sat.python import cp_model
from pathnum import enumerate_paths, edge_index


def feasible(H, prescriptions):
    paths = enumerate_paths(H)
    eidx = edge_index(H)
    model = cp_model.CpModel()
    x = [model.NewBoolVar("") for _ in paths]
    by_edge = [[] for _ in eidx]
    for i, P in enumerate(paths):
        for a, b in zip(P.verts, P.verts[1:]):
            by_edge[eidx[frozenset((a, b))]].append(i)
    for lst in by_edge:
        model.AddExactlyOne(x[i] for i in lst)
    model.Add(sum(x) == H.number_of_nodes() // 2)
    for (u, y) in prescriptions:
        # some chosen path starts at u with first edge uy (in either orientation)
        lits = [x[i] for i, P in enumerate(paths)
                if (P.verts[0] == u and P.verts[1] == y) or (P.verts[-1] == u and P.verts[-2] == y)]
        model.AddBoolOr(lits)
    s = cp_model.CpSolver(); s.parameters.num_workers = 1; s.parameters.max_time_in_seconds = 60
    return s.Solve(model) in (cp_model.OPTIMAL, cp_model.FEASIBLE)


if __name__ == "__main__":
    two = "--two" in sys.argv
    tot = f1 = f2 = 0
    for line in open(sys.argv[1]):
        H = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(line.strip().encode()))
        if any(H.degree(v) % 2 == 0 for v in H):
            continue
        tot += 1
        for u in H:
            for y in H[u]:
                if not feasible(H, [(u, y)]):
                    f1 += 1
                    print("TEL1-FAIL", line.strip(), u, y, flush=True)
        if two:
            for u, v in itertools.combinations(H, 2):
                for y in H[u]:
                    for x_ in H[v]:
                        if not feasible(H, [(u, y), (v, x_)]):
                            f2 += 1
                            print("TEL2-FAIL", line.strip(), (u, y), (v, x_), flush=True)
                            break
    print(f"all-odd graphs {tot}; TEL1 failures {f1}; TEL2 failures {f2}", flush=True)
