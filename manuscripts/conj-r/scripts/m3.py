"""m3.py -- L_N(3) at order 8: for every connected all-odd graph and every unordered triple of
disjoint ordered non-adjacent pairs, test
  J3 (exact): for some choice {i,j} of two pairs with c_i, c_j joined in F - {a_i, a_j}, a Lovasz
     decomposition with c_i, c_j the ends of one path avoiding a_i, a_j and Q(c_k) avoiding a_k;
  LN3 (exact): Q(c_t) avoids a_t for t = 1, 2, 3 (baseline).
Witnesses are checked by wcheck.  Output: counts; instances failing J3."""
import sys, subprocess, itertools, collections
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lnlib import g6_decode
def comp(adj, s, banned):
    seen = {s}; st = [s]
    while st:
        u = st.pop()
        for v in adj[u]:
            if v not in seen and v not in banned: seen.add(v); st.append(v)
    return seen
Q = []; meta = []
for g in open(sys.argv[1]):
    g = g.strip(); n, adj = g6_decode(g)
    P = [(c, a) for c in range(n) for a in range(n) if c != a and a not in adj[c]]
    for T in itertools.combinations(P, 3):
        vs = [x for p in T for x in p]
        if len(set(vs)) < 6: continue
        q0 = g + ''.join(' A %d %d' % p for p in T)
        Q.append(q0); meta.append((len(meta), 'LN3'))
        idx = len(meta) - 1
        for (i, j) in ((0, 1), (0, 2), (1, 2)):
            (ci, ai), (cj, aj) = T[i], T[j]
            k = 3 - i - j; ck, ak = T[k]
            if cj in comp(adj, ci, {ai, aj}):
                Q.append('%s J %d %d A %d %d A %d %d A %d %d' % (g, ci, cj, ci, ai, cj, aj, ck, ak))
                meta.append((idx, 'J3'))
out = subprocess.run(['./lnsolve3', '-b', '20000000'], input='\n'.join(Q) + '\n', capture_output=True, text=True).stdout.split('\n')
chk = subprocess.run(['./wcheck'], input=''.join(q + '\n' + a + '\n' for q, a in zip(Q, out)), capture_output=True, text=True).stdout
print(chk.strip().split('\n')[-1])
inst = collections.defaultdict(dict)
for (idx, kind), a in zip(meta, out):
    r = a.split()[0]
    d = inst[idx]
    if kind == 'LN3': d['LN3'] = r
    else: d['J3'] = d.get('J3', False) or r == 'SAT'; d['J3any'] = True
C = collections.Counter()
for idx, d in inst.items():
    C['inst'] += 1
    C['LN3_' + d['LN3']] += 1
    C['has_joint_choice'] += d.get('J3any', False)
    C['J3'] += d.get('J3', False)
print(dict(C))
bad = [idx for idx, d in inst.items() if d.get('J3any') and not d.get('J3')]
qs = {idx: q for (idx, kind), q in zip(meta, Q) if kind == 'LN3'}
with open(sys.argv[2], 'w') as f:
    for idx in bad: f.write(qs[idx] + '\n')
