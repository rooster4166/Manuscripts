"""cfgen.py -- AE instances (stdin: graph6) and the coordinator's form CF (ae session).

An AE instance: K with exactly one vertex g of positive even degree, c odd, c != g, c not adjacent
to g, c in the component of g.  Modes (argv[1]):
  ae   : 'A c g'                        (Conjecture AE)
  cf   : 'A c g' + 'T w g' for every neighbour w of g with d(w) >= 3
         (in H = K - g: profile b(w) = 2 at every non-leaf neighbour w of g, b = 1 at odd vertices)
  cf1  : one line per (instance, w0): as cf but without 'T w0 g' (one zero allowed at w0);
         the line carries a tag '# id' so that instances can be regrouped.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
from lnlib import g6_decode
mode = sys.argv[1]
idx = 0
for line in sys.stdin:
    g6 = line.strip()
    if not g6: continue
    n, adj = g6_decode(g6)
    ev = [v for v in range(n) if adj[v] and len(adj[v]) % 2 == 0]
    if len(ev) != 1: continue
    g = ev[0]
    seen = {g}; st = [g]
    while st:
        u = st.pop()
        for v in adj[u]:
            if v not in seen: seen.add(v); st.append(v)
    W = sorted(w for w in adj[g] if len(adj[w]) >= 3)
    for c in sorted(seen):
        if c != g and c not in adj[g] and len(adj[c]) % 2 == 1:
            base = f'{g6} A {c} {g}'
            if mode == 'ae': print(base)
            elif mode == 'cf': print(base + ''.join(f' T {w} {g}' for w in W))
            elif mode == 'cf1':
                for w0 in W:
                    print(base + ''.join(f' T {w} {g}' for w in W if w != w0))
            idx += 1
