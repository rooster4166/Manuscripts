"""Compact CP-SAT model for path partitions: K path slots, each a circuit through
a dummy node (AddCircuit with optional nodes).  Supports exact/min/max end counts."""
from ortools.sat.python import cp_model
import networkx as nx
def solve_circ(G, K, exact=None, mins=None, maxs=None, time_limit=600, workers=2, allow_empty=True):
    nodes = list(G.nodes()); idx = {v: i for i, v in enumerate(nodes)}; n = len(nodes)
    E = [tuple(e) for e in G.edges()]
    m = cp_model.CpModel()
    xe = {}
    endlits = {v: [] for v in nodes}
    for p in range(K):
        arcs = []
        d = n  # dummy index
        inpath = {}
        for v in nodes:
            lit = m.NewBoolVar(f'in{p}_{v}')
            inpath[v] = lit
            arcs.append((idx[v], idx[v], lit.Not()))
            s = m.NewBoolVar(f's{p}_{v}'); t = m.NewBoolVar(f't{p}_{v}')
            arcs.append((d, idx[v], s)); arcs.append((idx[v], d, t))
            endlits[v] += [s, t]
        empty = m.NewBoolVar(f'empty{p}')
        if allow_empty:
            arcs.append((d, d, empty))
            for v in nodes:
                m.AddImplication(inpath[v], empty.Not())
        else:
            m.Add(empty == 0)
        for (u, v) in E:
            a1 = m.NewBoolVar(''); a2 = m.NewBoolVar('')
            arcs.append((idx[u], idx[v], a1)); arcs.append((idx[v], idx[u], a2))
            xe[(p, u, v)] = (a1, a2)
        m.AddCircuit(arcs)
        # a nonempty path must have >= 1 edge: forbid single-vertex circuit d->v->d
        for v in nodes:
            # if v in path and it is both start and end then path is trivial -> forbid
            s, t = endlits[v][-2], endlits[v][-1]
            m.AddBoolOr([s.Not(), t.Not()])
    for (u, v) in E:
        m.Add(sum(xe[(p, u, v)][0] + xe[(p, u, v)][1] for p in range(K)) == 1)
    for d_, op in ((exact, '=='), (mins, '>='), (maxs, '<=')):
        if not d_: continue
        for v, c in d_.items():
            s = sum(endlits[v])
            if op == '==': m.Add(s == c)
            elif op == '>=': m.Add(s >= c)
            else: m.Add(s <= c)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_workers = workers
    st = solver.Solve(m)
    name = solver.StatusName(st)
    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return name, None
    # extract paths
    paths = []
    for p in range(K):
        used = [(u, v) for (u, v) in E if solver.Value(xe[(p, u, v)][0]) or solver.Value(xe[(p, u, v)][1])]
        if not used: continue
        H = nx.Graph(used)
        assert nx.is_connected(H) and max(dict(H.degree()).values()) <= 2 and H.number_of_edges() == H.number_of_nodes() - 1
        ends = [v for v in H if H.degree(v) == 1]
        paths.append(tuple(nx.shortest_path(H, ends[0], ends[1])))
    return name, paths
if __name__ == '__main__':
    import sys
    sys.path.insert(0, '/home/user/Manuscripts/tools')
    from pathnum import verify_partition
    for n in range(3, 9):
        G = nx.complete_graph(n); want = (n + 1) // 2 if n % 2 else n // 2
        st, P = solve_circ(G, want)
        st2, _ = solve_circ(G, want - 1)
        print(n, st, len(P), verify_partition(G, P), 'K-1:', st2)
