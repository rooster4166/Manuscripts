import sys, random, itertools
from common import *
from gen import random_host, U
def thm6_ok(G, r):
    k = G.number_of_nodes() // 2
    ex = {v: 1 for v in G if v >= 6}; ex[r] = 2
    mx = {u: 2 for u in U if u != r}
    from circ import solve_circ
    st, P = solve_circ(G, k, exact=ex, maxs=mx, workers=2, time_limit=900)
    if P is not None: assert verify_partition(G, P)
    class R: pass
    res = R(); res.status = st
    return st in ('OPTIMAL', 'FEASIBLE'), res
if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'n8':
        n = bad = 0
        for sx in range(0, 6):
            for Sx in itertools.combinations(U, sx):
                Sy = [u for u in U if u not in Sx]
                if len(Sy) > 5: continue
                for xy in (0, 1):
                    if (sx + xy) % 2 == 0 or (len(Sy) + xy) % 2 == 0: continue
                    G = nx.complete_graph(6); G.add_nodes_from([6, 7])
                    G.add_edges_from((6, u) for u in Sx); G.add_edges_from((7, u) for u in Sy)
                    if xy: G.add_edge(6, 7)
                    if not nx.is_connected(G) or any(G.degree(v) == 0 for v in G): continue
                    for r in U:
                        n += 1
                        ok, res = thm6_ok(G, r)
                        if not ok: bad += 1; print('FAIL', Sx, Sy, xy, r, flush=True)
        print('Thm 6 n=8: instances', n, 'failures', bad, flush=True)
    else:
        rng = random.Random(int(sys.argv[2])); N = int(sys.argv[3]); nX = int(sys.argv[4])
        n = bad = 0
        while n < N:
            G = random_host(rng, [], nX, maxS=5)
            if G is None: continue
            r = rng.choice(U); n += 1
            ok, res = thm6_ok(G, r)
            if not ok: bad += 1; print('FAIL', sorted(G.edges()), r, res.status, flush=True)
        print('Thm 6 random nX=%d: instances' % nX, n, 'failures', bad, flush=True)
