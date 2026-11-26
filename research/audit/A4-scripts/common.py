import sys, itertools
sys.path.insert(0, '/home/user/Manuscripts/tools')
import networkx as nx
from ortools.sat.python import cp_model
from pathnum import enumerate_paths, solve, verify_partition, Path, edge_index

def iso_classes_edge_sets(n, m):
    """All m-edge graphs on vertex set range(n) (isolated vertices allowed), up to isomorphism."""
    E = list(itertools.combinations(range(n), 2))
    buckets = {}
    out = []
    for es in itertools.combinations(E, m):
        H = nx.Graph(); H.add_nodes_from(range(n)); H.add_edges_from(es)
        key = nx.weisfeiler_lehman_graph_hash(H, iterations=3) + str(sorted(d for _, d in H.degree()))
        lst = buckets.setdefault(key, [])
        if any(nx.is_isomorphic(H, K) for K in lst):
            continue
        lst.append(H); out.append(H)
    return out

def complement_of(n, H):
    G = nx.complete_graph(n)
    G.remove_edges_from(H.edges())
    return G

def solve_pairs(G, budget, exact_ends=None, pair_counts=None, paths=None, time_limit=120, workers=4, exact_count=None):
    """Feasibility: <= budget paths (or == exact_count), exact end counts, exact end-pair multiplicities."""
    if paths is None:
        paths = enumerate_paths(G)
    eidx = edge_index(G)
    model = cp_model.CpModel()
    x = [model.NewBoolVar(f"x{i}") for i in range(len(paths))]
    by_edge = [[] for _ in range(len(eidx))]
    for i, P in enumerate(paths):
        mk = P.mask
        while mk:
            low = mk & -mk
            by_edge[low.bit_length() - 1].append(i)
            mk ^= low
    for e in range(len(eidx)):
        model.AddExactlyOne(x[i] for i in by_edge[e])
    if exact_ends is not None:
        at = {v: [] for v in G.nodes()}
        for i, P in enumerate(paths):
            a, b = P.ends; at[a].append(i); at[b].append(i)
        for v, c in exact_ends.items():
            model.Add(sum(x[i] for i in at[v]) == c)
    if pair_counts is not None:
        byp = {}
        for i, P in enumerate(paths):
            byp.setdefault(frozenset(P.ends), []).append(i)
        allpairs = set(byp) | set(pair_counts)
        for pr in allpairs:
            c = pair_counts.get(pr, 0)
            model.Add(sum(x[i] for i in byp.get(pr, [])) == c)
    if exact_count is not None:
        model.Add(sum(x) == exact_count)
    elif budget is not None:
        model.Add(sum(x) <= budget)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_workers = workers
    st = solver.Solve(model)
    name = solver.StatusName(st)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return name, [paths[i].verts for i in range(len(paths)) if solver.Value(x[i])]
    return name, None
