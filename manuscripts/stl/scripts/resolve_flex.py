"""Re-decide undecided (2) EE / STS / PAIR entries of a flex_run output with fresh seeds and growing
budgets (HALF entries are left as they are).  usage: resolve_flex.py in.jsonl out.jsonl"""
import sys, json, collections
import networkx as nx
from common import Oracle, relabel, even_vertices

orc = Oracle()
fout = open(sys.argv[2], 'w'); c = collections.Counter()


def retry(fn):
    for k, bud in enumerate([32_000_000, 128_000_000, 512_000_000]):
        for s in range(3):
            v = fn(seed=1000 * k + s + 11, budget=bud)
            if v != 2:
                return v
    return 2


for line in open(sys.argv[1]):
    d = json.loads(line)
    J = relabel(nx.from_graph6_bytes(d['g6'].encode()))
    z = even_vertices(J)[0]
    prof = {v: J.degree(v) % 2 for v in J}
    for u, v in list(d['EE'].items()):
        if v == 2:
            d['EE'][u] = retry(lambda **kw: orc.query(J, prof, z, -1, 0, 99, req={int(u): z}, **kw))
    for u, v in list(d['STS'].items()):
        if v == 2:
            d['STS'][u] = retry(lambda **kw: orc.query(J, prof, z, -1, 1, 99, req={int(u): z}, **kw))
    for key, v in list(d['PAIR'].items()):
        if v == 2:
            pairs = {}
            for ab in key.split():
                a, b = map(int, ab.split('-')); pairs[a] = {b}; pairs[b] = {a}
            d['PAIR'][key] = retry(lambda **kw: orc.query(J, prof, z, -1, 1, 99, pairs=pairs, **kw))
    for k in ('EE', 'STS', 'HALF', 'PAIR'):
        for v in d[k].values():
            c[(k, v)] += 1
    fout.write(json.dumps(d) + '\n'); fout.flush()
print('RESOLVED', sorted(c.items()), flush=True)
