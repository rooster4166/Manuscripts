"""cov2.py -- union coverage of the proved sufficient conditions on an instance list
('g6 c1 a1 c2 a2'), with the polynomial T-join test for Lemma S (validated against the trail
search at order 8) and at most MAXP joint paths per instance (shortest first).
  B  Corollary B (ln, Lean); C1 joint + leaf; C2 joint + suppression; C3 joint + Lemma S;
  G  cut-vertex gluing (G1-G3).  Prints counts and writes the residual."""
import sys, collections
from multiprocessing import Pool
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lnlib import g6_decode
from cov import ekey
from tjoin import tjoin_ok
from allcov import comp, gluing, corB
MAXP = int(sys.argv[3]) if len(sys.argv) > 3 else 3000
def joint_paths(adj, c1, a1, c2, a2):
    out = []
    def ext(P, S):
        if len(out) >= 200000: return
        if P[-1] == c2: out.append(tuple(P)); return
        for y in sorted(adj[P[-1]]):
            if y not in S and y not in (a1, a2):
                S.add(y); P.append(y); ext(P, S); P.pop(); S.discard(y)
    ext([c1], {c1})
    out.sort(key=len)
    return out
def work(line):
    t = line.split(); n, adj = g6_decode(t[0]); c1, a1, c2, a2 = map(int, t[1:5])
    seen = comp(adj, c1, {a1, a2}); joint = c2 in seen
    f = {'B': corB(adj, c1, a1, c2, a2), 'C1': False, 'C2': False, 'C3': False,
         'G': (not joint) and (gluing(adj, c1, a1, c2, a2) or gluing(adj, c2, a2, c1, a1))}
    capped = False
    if joint:
        f['C1'] = len(adj[c1]) == 1 or len(adj[c2]) == 1
        if not (f['C1'] or f['B']):
            E0 = frozenset(ekey(u, v) for u in range(n) for v in adj[u])
            Ps = joint_paths(adj, c1, a1, c2, a2)
            if len(Ps) > MAXP: capped = True; Ps = Ps[:MAXP]
            for P in Ps:
                E = E0 - set(ekey(p, q) for p, q in zip(P, P[1:]))
                Ad = [set() for _ in range(n)]
                for u, v in E: Ad[u].add(v); Ad[v].add(u)
                for c in (c1, c2):
                    if len(Ad[c]) == 2:
                        y, z = sorted(Ad[c])
                        if z not in Ad[y]: f['C2'] = True
                if f['C2']: break
                if tjoin_ok(n, E, c1, c2) or tjoin_ok(n, E, c2, c1): f['C3'] = True; break
    return line.strip(), joint, f, capped
if __name__ == '__main__':
    C = collections.Counter(); resid = []
    lines = [l for l in open(sys.argv[1]) if l.strip()]
    with Pool(4) as pool:
        for inst, joint, f, capped in pool.imap_unordered(work, lines, chunksize=10):
            C['inst'] += 1; C['joint' if joint else 'sep'] += 1
            for k in f: C[k] += f[k]
            u = any(f.values()); C['union'] += u
            if not u: resid.append(inst + (' J' if joint else ' S') + (' capped' if capped else ''))
            C['capped_resid'] += (not u) and capped
    for k in sorted(C): print(k, C[k])
    open(sys.argv[2], 'w').write('\n'.join(sorted(resid)) + '\n')
