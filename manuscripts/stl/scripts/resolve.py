"""Re-decide undecided (2) entries of sample_run outputs: retry the budgeted oracle with fresh
seeds and growing budgets; finally run the unbudgeted exact search (budget 0) if asked.
usage: resolve.py in.jsonl out.jsonl [exact]
"""
import sys, json
import networkx as nx
from common import Oracle
from stl_run import test1

orc = Oracle()
exact = len(sys.argv) > 3
fout = open(sys.argv[2], 'w')
left = 0
for line in open(sys.argv[1]):
    rec = json.loads(line)
    if 'dz' not in rec:  # mode 2 records are handled by resolve2
        fout.write(line); continue
    J = nx.from_graph6_bytes(rec['g6'].encode())
    prof = {v: J.degree(v) % 2 for v in J}
    for r, (stl, bal, t1) in list(rec['res'].items()):
        r = int(r)
        if stl == 1:
            continue
        for k, bud in enumerate([4_000_000, 16_000_000, 64_000_000, 256_000_000]):
            for s in range(3):
                stl = orc.query(J, prof, 0, r, 1, 0, seed=1000 * k + s + 17, budget=bud)
                if stl != 2:
                    break
            if stl != 2:
                break
        if stl == 2 and exact:
            stl = orc.query(J, prof, 0, r, 1, 0)
        if stl == 0:
            bal = orc.query(J, prof, 0, r, 0, 0, seed=5, budget=256_000_000)
            t1 = test1(J, 0, r)
        if stl == 2:
            left += 1
        rec['res'][str(r)] = (stl, bal if stl != 1 else 1, t1)
        print('resolved', rec['g6'], r, stl, flush=True)
    fout.write(json.dumps(rec) + '\n'); fout.flush()
print('undecided left', left)
