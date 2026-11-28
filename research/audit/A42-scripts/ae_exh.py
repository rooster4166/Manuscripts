"""A42: Conjecture AE exhaustively: every graph of order n (graph6 on stdin: all graphs of order n
from gen.c, whose completeness is checked by the OEIS counts) with exactly one even vertex g, every
odd c in the component of g with c != g, c !~ g; query 'A c g', solved by a42solve, checked by a42lib."""
import sys, subprocess, collections
from multiprocessing import Pool
sys.path.insert(0, __import__('os').path.dirname(__file__))
from a42lib import g6dec, comp_of, check_qa
Q = []
for g in sys.stdin:
    g = g.strip(); n, adj = g6dec(g)
    ev = [v for v in range(n) if adj[v] and len(adj[v]) % 2 == 0]
    if len(ev) != 1: continue
    gv = ev[0]
    for c in sorted(comp_of(adj, gv)):
        if c != gv and c not in adj[gv] and len(adj[c]) % 2 == 1: Q.append('%s A %d %d' % (g, c, gv))
def solve(Q):
    r = subprocess.run(['./a42solve', '-b', '50000000'], input='\n'.join(Q) + '\n', capture_output=True, text=True).stdout.split('\n')
    return r[:len(Q)]
ch = [Q[i:i + 2000] for i in range(0, len(Q), 2000)]
with Pool(4) as p: A = [a for r in p.map(solve, ch) for a in r] if Q else []
C = collections.Counter(check_qa(q, a) for q, a in zip(Q, A))
print('n =', sys.argv[1], 'queries', len(Q), dict(C))
