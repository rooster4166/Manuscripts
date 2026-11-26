"""Exact path numbers and endpoint-constrained path partitions for small graphs.

A path is a nonempty vertex-simple path; a path partition uses every edge exactly
once.  We enumerate all simple paths (identified with their reversals) and solve a
minimum exact cover with OR-Tools CP-SAT, optionally with endpoint constraints.

Intended for independent checking of statements in the Gallai manuscripts on
small graphs (roughly n <= 9 for dense graphs, larger for sparse ones).
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass
from typing import Callable, Dict, Iterable, List, Optional, Sequence, Tuple

import networkx as nx
from ortools.sat.python import cp_model


@dataclass(frozen=True)
class Path:
    verts: Tuple[int, ...]
    mask: int  # bitmask over edge indices

    @property
    def ends(self) -> Tuple[int, int]:
        return self.verts[0], self.verts[-1]


def edge_index(G: nx.Graph) -> Dict[frozenset, int]:
    return {frozenset(e): i for i, e in enumerate(G.edges())}


def enumerate_paths(G: nx.Graph, max_len: Optional[int] = None) -> List[Path]:
    """All simple paths with >= 1 edge, each once (start label < end label)."""
    eidx = edge_index(G)
    nodes = list(G.nodes())
    order = {v: i for i, v in enumerate(nodes)}
    adj = {v: list(G.neighbors(v)) for v in nodes}
    out: List[Path] = []

    def dfs(start, path, visited, mask):
        u = path[-1]
        for w in adj[u]:
            if w in visited:
                continue
            m2 = mask | (1 << eidx[frozenset((u, w))])
            path.append(w)
            visited.add(w)
            if order[w] > order[start]:
                out.append(Path(tuple(path), m2))
            if max_len is None or len(path) - 1 < max_len:
                dfs(start, path, visited, m2)
            visited.remove(w)
            path.pop()

    for s in nodes:
        dfs(s, [s], {s}, 0)
    return out


@dataclass
class Result:
    status: str
    value: Optional[int]
    paths: Optional[List[Tuple[int, ...]]]


def solve(
    G: nx.Graph,
    *,
    budget: Optional[int] = None,
    min_ends: Optional[Dict[int, int]] = None,
    exact_ends: Optional[Dict[int, int]] = None,
    max_ends: Optional[Dict[int, int]] = None,
    paths: Optional[List[Path]] = None,
    time_limit: float = 120.0,
    workers: int = 4,
) -> Result:
    """Minimise the number of paths subject to endpoint constraints.

    If ``budget`` is given, the solve is a feasibility check for <= budget paths
    (still minimising inside it).  Endpoint counts b(v) count path ends at v with
    multiplicity (a path contributes one end to each of its two distinct ends).
    """
    if G.number_of_edges() == 0:
        return Result("OPTIMAL", 0, [])
    if paths is None:
        paths = enumerate_paths(G)
    eidx = edge_index(G)
    m = len(eidx)
    model = cp_model.CpModel()
    x = [model.NewBoolVar(f"x{i}") for i in range(len(paths))]
    by_edge: List[List[int]] = [[] for _ in range(m)]
    for i, P in enumerate(paths):
        mk = P.mask
        while mk:
            low = mk & -mk
            by_edge[low.bit_length() - 1].append(i)
            mk ^= low
    for e in range(m):
        model.AddExactlyOne(x[i] for i in by_edge[e])
    ends_at: Dict[int, List[int]] = {v: [] for v in G.nodes()}
    for i, P in enumerate(paths):
        a, b = P.ends
        ends_at[a].append(i)
        ends_at[b].append(i)
    for d, op in ((min_ends, ">="), (exact_ends, "=="), (max_ends, "<=")):
        if not d:
            continue
        for v, c in d.items():
            s = sum(x[i] for i in ends_at[v])
            if op == ">=":
                model.Add(s >= c)
            elif op == "==":
                model.Add(s == c)
            else:
                model.Add(s <= c)
    total = sum(x)
    if budget is not None:
        model.Add(total <= budget)
    model.Minimize(total)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_workers = workers
    st = solver.Solve(model)
    name = solver.StatusName(st)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        chosen = [paths[i].verts for i in range(len(paths)) if solver.Value(x[i])]
        return Result(name, len(chosen), chosen)
    return Result(name, None, None)


def path_number(G: nx.Graph, **kw) -> int:
    r = solve(G, **kw)
    if r.status != "OPTIMAL":
        raise RuntimeError(f"solver status {r.status}")
    return r.value


def lower_bound(G: nx.Graph) -> int:
    n = G.number_of_nodes()
    if G.number_of_edges() == 0:
        return 0
    odd = sum(1 for v in G if G.degree(v) % 2)
    delta = max(d for _, d in G.degree())
    return max(odd // 2, (delta + 1) // 2, -(-G.number_of_edges() // max(1, n - 1)))


def with_private_leaf(G: nx.Graph, r) -> Tuple[nx.Graph, object]:
    H = G.copy()
    leaf = ("leaf", r)
    H.add_edge(r, leaf)
    return H, leaf


def is_odd_semi_clique(G: nx.Graph) -> bool:
    n = G.number_of_nodes()
    if n % 2 == 0:
        return False
    k = n // 2
    missing = n * (n - 1) // 2 - G.number_of_edges()
    return missing <= k - 1


def verify_partition(G: nx.Graph, plist: Sequence[Tuple[int, ...]]) -> bool:
    seen = set()
    for P in plist:
        if len(set(P)) != len(P) or len(P) < 2:
            return False
        for a, b in zip(P, P[1:]):
            e = frozenset((a, b))
            if not G.has_edge(a, b) or e in seen:
                return False
            seen.add(e)
    return len(seen) == G.number_of_edges()


if __name__ == "__main__":
    # Self-tests against known values.
    tests = []
    for n in range(2, 9):
        tests.append((f"K{n}", nx.complete_graph(n), (n + 1) // 2 if n % 2 else n // 2))
    for n in range(3, 9):
        tests.append((f"C{n}", nx.cycle_graph(n), 2))
    tests.append(("Petersen", nx.petersen_graph(), 5))
    K5e = nx.complete_graph(5)
    K5e.remove_edge(0, 1)
    tests.append(("K5-e", K5e, 3))
    tests.append(("K3,3", nx.complete_bipartite_graph(3, 3), 3))
    tests.append(("K4,4", nx.complete_bipartite_graph(4, 4), 3))  # 16 edges, paths <= 7 edges
    ok = True
    for name, G, want in tests:
        r = solve(G)
        good = r.status == "OPTIMAL" and r.value == want and verify_partition(G, r.paths)
        ok &= good
        print(f"{name:10s} p={r.value} want={want} {'ok' if good else 'FAIL'}")
    print("ALL OK" if ok else "SOME FAILED")
