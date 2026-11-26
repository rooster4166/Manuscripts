import sys, pickle, random, itertools
from common import *
from gen import ROOTED, random_host, U
def lemma2_ok(G, Uset, r):
    k = G.number_of_nodes() // 2
    ex = {v: 1 for v in G if v not in Uset}; ex[r] = 2
    mx = {u: 2 for u in Uset if u != r}
    from circ import solve_circ
    st, P = solve_circ(G, k, exact=ex, maxs=mx, workers=2, time_limit=900)
    if P is not None: assert verify_partition(G, P)
    class R: pass
    res = R(); res.status = st
    return st in ('OPTIMAL', 'FEASIBLE'), res
if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'conn8':
        rows = pickle.load(open('c1_rows.pkl', 'rb'))
        n = bad = 0
        for (line, r, p2, k, shp, cand, dr) in rows:
            if not cand or 'isolated' in shp: continue
            G = nx.from_graph6_bytes(line.encode())
            Uset = [v for v in G if G.degree(v) % 2 == 0]
            if not any(1 <= len([u for u in Uset if G.has_edge(x, u)]) <= 2 for x in G if x not in Uset): continue
            n += 1
            ok, res = lemma2_ok(G, Uset, r)
            if not ok:
                bad += 1; print('FAIL', line, r, shp, flush=True)
        print('Lemma 2 on conn8: instances', n, 'failures', bad, flush=True)
    else:
        rng = random.Random(int(sys.argv[2])); N = int(sys.argv[3]); nX = int(sys.argv[4])
        n = bad = 0
        while n < N:
            name = rng.choice(list(ROOTED))
            G = random_host(rng, ROOTED[name], nX)
            if G is None: continue
            if not any(1 <= len([u for u in U if G.has_edge(x, u)]) <= 2 for x in G if x >= 6): continue
            n += 1
            ok, res = lemma2_ok(G, U, 0)
            if not ok:
                bad += 1; print('FAIL', name, sorted(G.edges()), res.status, flush=True)
        print('Lemma 2 random nX=%d: instances' % nX, n, 'failures', bad, flush=True)
