"""Prop 2.6 check (audit A26; usage: python3 equiv.py < out/d6_9_dense.g6): (E7)-base of M exists  <=>  J has a star-terminal Lovasz decomposition with
transitions x_i z y_i (x_i an end) in which x1y2 is terminal at y2 and x2y3 is terminal at y3.
Both sides are decided by exact lsearch (budget 0) for every labelling with x1y2, x2y3 in B."""
import sys, itertools, collections
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import networkx as nx
from dense import base_query, ENG

def labs(B):
    for p in itertools.permutations(range(6)):
        x1, y1, x2, y2, x3, y3 = p
        if B.has_edge(x1, y2) and B.has_edge(x2, y3):
            yield dict(x1=x1, y1=y1, x2=x2, y2=y2, x3=x3, y3=y3)

def jsharp_query(B, L):
    nB = B.number_of_nodes(); z, l2, l3 = nB, nB + 1, nB + 2; n = nB + 3
    x1, y1, x2, y2, x3, y3 = (L[k] for k in ('x1', 'y1', 'x2', 'y2', 'x3', 'y3'))
    E = list(B.edges()) + [(z, x1), (z, y1), (l2, x2), (l2, y2), (l3, x3), (l3, y3)]
    deg = [0] * n
    for u, v in E: deg[u] += 1; deg[v] += 1
    allv = set(range(n))
    es = [(x1, z, sorted(allv - {x1})), (x2, l2, sorted(allv - {x2})), (x3, l3, sorted(allv - {x3})),
          (y2, x1, sorted(allv - {y2})), (y3, x2, sorted(allv - {y3}))]
    return dict(n=n, edges=E, b=[d % 2 for d in deg], sep=[(z, l2), (z, l3), (l2, l3)], es=es,
                seed=0, budget=0)

if __name__ == "__main__":
  cnt = collections.Counter()
  for line in sys.stdin:
      B = nx.from_graph6_bytes(line.strip().encode())
      Ls = list(labs(B))
      a = ENG.run([base_query(B, L, 'endT', 0, 0) for L in Ls])
      b = ENG.run([jsharp_query(B, L) for L in Ls])
      for (sa, _), (sb, _) in zip(a, b):
          cnt[(sa, sb)] += 1
  print(dict(cnt))
