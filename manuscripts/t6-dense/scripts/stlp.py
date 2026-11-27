"""E28(B′); usage: python3 stlp.py < out/d6_9_dense.g6.  For every labelling with x1y2, x2y3 in B (order-9 dense cores): does an (E7)-base exist, and does
STL-P hold for the oriented pairing (star-terminal Lovasz decomposition of J with transitions
x_i z y_i, x_i an end)?  Exact search (budget 0)."""
import sys, itertools, collections
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import networkx as nx
from dense import base_query, ENG
from equiv import labs, jsharp_query

cnt = collections.Counter()
for line in sys.stdin:
    B = nx.from_graph6_bytes(line.strip().encode())
    Ls = list(labs(B))
    qa = [base_query(B, L, 'endT', 0, 0) for L in Ls]
    qe6 = [base_query(B, L, 'leanE6', 0, 0) for L in Ls]
    qp = []
    for L in Ls:
        q = jsharp_query(B, L); q['es'] = q['es'][:3]; qp.append(q)
    a = ENG.run(qa); e = ENG.run(qe6); p = ENG.run(qp)
    for L, (sa, _), (se, _), (sp, _) in zip(Ls, a, e, p):
        cnt[(sa, se, sp)] += 1
        if sa != 'OK':
            print(line.strip(), L, sa, se, sp, flush=True)
print(dict(cnt))
