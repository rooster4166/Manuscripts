"""A42: K0 = F - E(P) over all order-8 joint paths with both ends of positive degree: tightness
(a42solve answers, K0_8ln.txt.ans) against: universal odd vertex (O1), disconnected active part,
cut vertex, 2-connected."""
import sys, collections
sys.path.insert(0, __import__('os').path.dirname(__file__))
from a42lib import g6dec, comp_of
K = [l.rstrip('\n') for l in open('K0_8ln.txt') if l.strip()]
A = open('K0_8ln.txt.ans').read().split()
C = collections.Counter()
for l, a in zip(K, A):
    f = l.split(' | ')[0].split()
    if f[3] != 'act': continue
    n, adj = g6dec(f[0]); act = [v for v in range(n) if adj[v]]
    o1 = any(len(adj[v]) % 2 == 1 and len(adj[v]) == len(act) - 1 for v in act)
    conn = comp_of(adj, act[0]) >= set(act)
    cut = conn and any(len(comp_of(adj, next(u for u in act if u != x), {x})) < len(act) - 1 for x in act)
    struct = 'disconnected' if not conn else ('cut vertex' if cut else '2-connected')
    C[(struct, 'O1' if o1 else 'no O1', 'tight' if a == 'SAT' else 'NOT tight')] += 1
for k in sorted(C): print(k, C[k])
