"""classify failures of MTL2 with x_i ~ w_i allowed (singletons, x_i not a tail leaf)."""
import sys, subprocess, collections
from lnlib import g6_decode
inst = []
for line in sys.stdin:
    gs = line.strip()
    n, adj = g6_decode(gs)
    deg = [len(a) for a in adj]
    ev = [v for v in range(n) if deg[v] > 0 and deg[v] % 2 == 0]
    if len(ev) > 1: continue
    g = ev[0] if ev else -1
    leaves = [v for v in range(n) if deg[v] == 1]
    for i1, c1 in enumerate(leaves):
        w1 = next(iter(adj[c1]))
        for c2 in leaves[i1+1:]:
            w2 = next(iter(adj[c2]))
            if w1 == c2: continue
            for x1 in range(n):
                if x1 in (c1, w1, c2): continue
                for x2 in range(n):
                    if x2 in (c1, c2, w2): continue
                    if x1 not in adj[w1] and x2 not in adj[w2]: continue  # only instances using adjacency
                    inst.append((gs, g, c1, w1, x1, c2, w2, x2))
out = subprocess.run(['/tmp/claude-0/lnsolve'], input='\n'.join('%s S %d %d S %d %d' % (t[0], t[2], t[4], t[5], t[7]) for t in inst) + '\n', capture_output=True, text=True).stdout.split('\n')
st = collections.Counter()
for t, o in zip(inst, out):
    gs, g, c1, w1, x1, c2, w2, x2 = t
    n, adj = g6_decode(gs)
    feats = []
    for (c, w, x) in ((c1, w1, x1), (c2, w2, x2)):
        if x in adj[w]:
            feats.append('adj:w=%s,d(w)=%d' % ('g' if w == g else 'odd', len(adj[w])))
    st[(o.split()[0] if o else '?', tuple(sorted(feats)))] += 1
for k, v in sorted(st.items()): print(v, k)
