"""Sanity check for endpoint-structure Cor. 20 / Thm 21 (four even vertices).

For every connected graph of even order with exactly four even vertices in a graph6 file:
criticality (p = n/2) and the realisable pairs. Reports any vertex lying in fewer than two
realisable pairs (strong form: non-realisable pairs pairwise disjoint), and every critical graph
with a non-realisable pair. Usage: python3 tools/emc_four.py data/conn8.g6 [workers]
"""
import sys, itertools
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import networkx as nx
from multiprocessing import Pool
from pathnum import enumerate_paths, solve

def work(line):
    G = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(line.encode()))
    n = G.number_of_nodes()
    E = [v for v in G if G.degree(v) % 2 == 0]
    O = [v for v in G if G.degree(v) % 2 == 1]
    paths = enumerate_paths(G)
    crit = solve(G, budget=n // 2 - 1, paths=paths, time_limit=120, workers=1).status not in ("OPTIMAL", "FEASIBLE")
    real = {}
    for S in itertools.combinations(E, 2):
        exact = {v: 1 for v in O}
        for v in E: exact[v] = 2 if v in S else 0
        r = solve(G, exact_ends=exact, paths=paths, time_limit=120, workers=1)
        assert r.status in ("OPTIMAL", "FEASIBLE", "INFEASIBLE"), r.status
        real[frozenset(S)] = r.status in ("OPTIMAL", "FEASIBLE")
    nonreal = sorted(tuple(sorted(S)) for S in real if not real[S])
    strong = all(not (set(a) & set(b)) for a, b in itertools.combinations(nonreal, 2))
    return line, crit, nonreal, strong

if __name__ == '__main__':
    from collections import Counter
    lines = []
    for line in open(sys.argv[1]):
        line = line.strip()
        G = nx.from_graph6_bytes(line.encode())
        if G.number_of_nodes() % 2 == 0 and sum(1 for v in G if G.degree(v) % 2 == 0) == 4:
            lines.append(line)
    print('graphs with e=4:', len(lines), flush=True)
    st = Counter(); k = 0
    with Pool(int(sys.argv[2]) if len(sys.argv) > 2 else 3) as pool:
        for line, crit, nonreal, strong in pool.imap_unordered(work, lines, chunksize=4):
            k += 1
            st[('critical' if crit else 'noncritical', len(nonreal), 'strong' if strong else 'FAIL')] += 1
            if not strong or (crit and nonreal):
                print(line, 'crit' if crit else 'noncrit', 'nonreal=', nonreal, 'strong=', strong, flush=True)
            if k % 500 == 0:
                print('progress', k, dict(st), flush=True)
    print('FINAL', dict(st), flush=True)
