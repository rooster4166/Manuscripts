"""mkJ.py -- solver queries for Conjecture J (joint decomposition: c1, c2 ends of one path that
avoids a1 and a2) on the instances whose c1, c2 are joined in F - {a1, a2}; the other instances
are written to a separate file (separated case)."""
import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lnlib import g6_decode
sep = open(sys.argv[1], 'w')
for line in sys.stdin:
    t = line.split()
    if not t: continue
    g = t[0]; c1, a1, c2, a2 = map(int, t[1:5])
    n, adj = g6_decode(g)
    seen = {c1}; st = [c1]
    while st:
        u = st.pop()
        for v in adj[u]:
            if v not in seen and v not in (a1, a2): seen.add(v); st.append(v)
    if c2 in seen: print(g, 'J', c1, c2, 'A', c1, a1, 'A', c2, a2)
    else: sep.write(line)
