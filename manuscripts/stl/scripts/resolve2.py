"""Re-decide undecided STL2 entries of mode-2 sample_run outputs (fresh seeds, growing budgets).
usage: resolve2.py in.jsonl out.jsonl"""
import sys, json
import networkx as nx
from common import Oracle
from stl2_run import test2

orc = Oracle()
fout = open(sys.argv[2], 'w'); left = 0
for line in open(sys.argv[1]):
    rec = json.loads(line)
    J = nx.from_graph6_bytes(rec['g6'].encode())
    for key, (s0, s2, stl2, bal2, t2, mc, dz) in list(rec['res'].items()):
        if stl2 == 1:
            continue
        z, r = map(int, key.split('-'))
        p0 = {v: J.degree(v) % 2 for v in J}; p2 = dict(p0); p2[r] = 2
        res = 2
        for k, bud in enumerate([16_000_000, 64_000_000, 256_000_000]):
            for s in range(3):
                for prof in (p0, p2):
                    v = orc.query(J, prof, z, r, 1, 0, seed=100 * k + s + 3, budget=bud)
                    if v == 1:
                        res = 1; break
                if res == 1: break
            if res == 1: break
        if res != 1:
            v0 = orc.query(J, p0, z, r, 1, 0); v2 = orc.query(J, p2, z, r, 1, 0)
            res = 1 if 1 in (v0, v2) else 0
            if res == 0:
                t2 = test2(J, z, r)
        rec['res'][key] = (s0, s2, res, bal2, t2, mc, dz)
        print('resolved', rec['g6'], key, res, flush=True)
        left += (res != 1)
    fout.write(json.dumps(rec) + '\n'); fout.flush()
print('not STL2 after resolution:', left)
