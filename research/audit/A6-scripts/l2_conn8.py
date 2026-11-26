import sys
from common import *
from t_inc_lemma2 import lemma2_ok
n = bad = 0; seen_shapes = {}
for line in open('/home/user/Manuscripts/data/conn8.g6'):
    line = line.strip()
    if not line: continue
    G = nx.from_graph6_bytes(line.encode())
    Uset = [v for v in G if G.degree(v) % 2 == 0]
    if len(Uset) != 6: continue
    if not any(1 <= len([u for u in Uset if G.has_edge(x, u)]) <= 2 for x in G if x not in Uset): continue
    for r in Uset:
        shp, cand = dshape(G, Uset, r)
        if not cand or 'isolated' in shp: continue
        n += 1; seen_shapes[shp] = seen_shapes.get(shp, 0) + 1
        ok, res = lemma2_ok(G, Uset, r)
        if not ok:
            bad += 1; print('FAIL', line, r, shp, res.status, flush=True)
print('Lemma 2 on conn8: instances', n, 'by shape', seen_shapes, 'failures', bad, flush=True)
