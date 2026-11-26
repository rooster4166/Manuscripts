"""Rooted test on all connected 8-vertex graphs with exactly six even vertices,
feasibility per even root with the compact circuit CP-SAT model; every found
partition is verified independently.  INFEASIBLE results are re-checked with the
path-enumeration model."""
import sys
from common import *
from circ import solve_circ
def work(line):
    G = nx.from_graph6_bytes(line.encode()); n = G.number_of_nodes(); k = n // 2
    U = [v for v in G if G.degree(v) % 2 == 0]
    if len(U) != 6: return None
    out = []
    for r in U:
        st, P = solve_circ(G, k, mins={r: 2}, workers=1, time_limit=600)
        if P is not None:
            assert verify_partition(G, P) and len(P) <= k
            assert sum((p[0] == r) + (p[-1] == r) for p in P) >= 2
            status = 'pass'
        elif st == 'INFEASIBLE':
            res = solve(G, budget=k, min_ends={r: 2}, workers=1, time_limit=3000)
            status = 'FAIL' if res.status == 'INFEASIBLE' else 'pass*'
        else:
            status = 'unknown'
        shp, cand = dshape(G, U, r)
        # also record whether p2 = k exactly (tight): is there a partition with <= k-1 paths and 2 ends at r?
        st2, P2 = solve_circ(G, k - 1, mins={r: 2}, workers=1, time_limit=600)
        tight = 'tight' if st2 == 'INFEASIBLE' else ('slack' if P2 is not None else 'tight?')
        out.append((line, r, status, shp, cand, tight, G.degree(r)))
    return out
if __name__ == '__main__':
    start, step = int(sys.argv[1]), int(sys.argv[2])
    lines = [l.strip() for l in open('/home/user/Manuscripts/data/conn8.g6') if l.strip()][start::step]
    with open(f'c1d_{start}.txt', 'w') as f:
        for line in lines:
            r = work(line)
            if r:
                for row in r: f.write(' '.join(map(str, row)) + '\n')
            else:
                f.write(f'# skip {line}\n')
            f.flush()
    open(f'c1d_{start}.done', 'w').write('done\n')
