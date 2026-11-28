"""simple rescues of L_N(2) instances: Q(c1) = Q(c2) = P for a short path P from c1 to c2 avoiding
a1, a2, and F - E(P) has a parity decomposition (two even vertices c1, c2).  Paths of length <= 3."""
import sys, subprocess, itertools
from lnlib import g6_decode, g6_encode
lines = [l.split()[1:] for l in open(sys.argv[1]) if l.startswith('NOSCHED')]
queries = []; idx = []
for k, (g, c1, a1, c2, a2) in enumerate(lines):
    c1, a1, c2, a2 = map(int, (c1, a1, c2, a2))
    n, adj = g6_decode(g)
    paths = []
    def ext(P):
        if P[-1] == c2: paths.append(list(P)); return
        if len(P) > 4: return
        for y in adj[P[-1]]:
            if y not in P and y not in (a1, a2): ext(P + [y])
    ext([c1])
    for P in paths:
        A = [set(a) for a in adj]
        for u, v in zip(P, P[1:]): A[u].discard(v); A[v].discard(u)
        queries.append(g6_encode(n, A)); idx.append(k)
out = subprocess.run(['/tmp/claude-0/lnsolve'], input='\n'.join(queries) + '\n', capture_output=True, text=True).stdout.split('\n')
ok = set(idx[i] for i, o in enumerate(out[:len(idx)]) if o.startswith('SAT'))
print('unscheduled', len(lines), 'rescued by a short c1-c2 path', len(ok))
