"""Exactly decide undecided (2) STL entries of a families.py output (unbudgeted oracle, after more
seeded retries), and compute Test1 for every pair that is not STL.  usage: resolve_fam.py in out"""
import sys, json, collections
import networkx as nx
from common import Oracle
from stl_run import test1
orc = Oracle(); c = collections.Counter()
fout = open(sys.argv[2], 'w')
for line in open(sys.argv[1]):
    d = json.loads(line)
    J = nx.from_graph6_bytes(d['g6'].encode()); prof = {v: J.degree(v) % 2 for v in J}
    for r, (v, t1) in list(d['res'].items()):
        if v == 2:
            for k, bud in enumerate([512_000_000, 2_000_000_000]):
                for s in range(2):
                    v = orc.query(J, prof, 0, int(r), 1, 0, seed=77 * k + s, budget=bud)
                    if v != 2: break
                if v != 2: break
            if v == 2:
                v = orc.query(J, prof, 0, int(r), 1, 0)
            t1 = test1(J, 0, int(r)) if v == 0 else None
            print('resolved', d['g6'], r, v, t1, flush=True)
        d['res'][r] = (v, t1)
        c[(v, t1)] += 1
    fout.write(json.dumps(d) + '\n'); fout.flush()
print('FINAL', dict(c), flush=True)
