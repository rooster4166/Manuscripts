"""A42: three-way cross-validation a42solve / lnsolve3 / lnsolve on random queries of the kinds
the manuscript uses: J+A+A (Conjecture J), K0 = F - E(P) for a joint path (two-even tightness),
K0 + c_j l with S l a_j (Lemma R(b)), A+A (L_N(2)), AE (F - c_i, one even vertex, A c g),
J+A+A+A (m = 3 joint extension).  Every SAT witness of every solver is checked by a42lib.check.
usage: xval.py SEED N ORDERS(e.g. 8,10) BUDGET"""
import sys, random, subprocess
sys.path.insert(0, __import__('os').path.dirname(__file__))
from a42lib import g6dec, g6enc, comp_of, check_qa
random.seed(int(sys.argv[1])); N = int(sys.argv[2]); ORD = [int(x) for x in sys.argv[3].split(',')]
B = sys.argv[4]
G = {k: [l.strip() for l in open('odd%dc.g6' % k)] for k in ORD}
def rand_joint_path(n, adj, c1, a1, c2, a2):
    # random simple path c1 -> c2 avoiding a1, a2 (random DFS)
    for _ in range(50):
        P = [c1]; S = {c1}
        while P[-1] != c2:
            nx = [y for y in adj[P[-1]] if y not in S and y not in (a1, a2)]
            if not nx: break
            y = random.choice(nx); P.append(y); S.add(y)
        if P[-1] == c2: return P
    return None
Q = []; kinds = []
while len(Q) < N:
    k = random.choice(ORD); g = random.choice(G[k]); n, adj = g6dec(g)
    c1, a1, c2, a2 = random.sample(range(n), 4)
    if a1 in adj[c1] or a2 in adj[c2]: continue
    typ = random.randrange(6)
    if typ == 0:
        if c2 not in comp_of(adj, c1, {a1, a2}): continue
        q = '%s J %d %d A %d %d A %d %d' % (g, c1, c2, c1, a1, c2, a2)
    elif typ in (1, 2):
        if c2 not in comp_of(adj, c1, {a1, a2}): continue
        P = rand_joint_path(n, adj, c1, a1, c2, a2)
        if P is None: continue
        A = [set(x) for x in adj]
        if typ == 2: P = P[:random.randint(2, len(P))]
        for p, r in zip(P, P[1:]): A[p].discard(r); A[r].discard(p)
        if typ == 1: q = g6enc(n, A)
        else:
            if P[-1] in (c2, a2): continue
            A.append({c2}); A[c2].add(n); q = g6enc(n + 1, A) + ' S %d %d' % (n, a2)
    elif typ == 3:
        q = '%s A %d %d A %d %d' % (g, c1, a1, c2, a2)
    elif typ == 4:
        # AE: c_i a leaf at a_j needed; otherwise make one by deleting a random edge at a vertex
        x = random.randrange(n); y = random.choice(sorted(adj[x]))
        A = [set(z) for z in adj]; A[x].discard(y); A[y].discard(x)
        # now x, y even (or isolated); keep only if exactly one even vertex: need d(x)=1
        ev = [v for v in range(n) if A[v] and len(A[v]) % 2 == 0]
        if len(ev) != 1: continue
        gv = ev[0]; cs = [c for c in comp_of(A, gv) if c != gv and c not in A[gv] and len(A[c]) % 2 == 1]
        if not cs: continue
        q = g6enc(n, A) + ' A %d %d' % (random.choice(cs), gv)
    else:
        if n < 8: continue
        rest = [v for v in range(n) if v not in (c1, a1, c2, a2)]
        c3, a3 = random.sample(rest, 2)
        if a3 in adj[c3] or c2 not in comp_of(adj, c1, {a1, a2}): continue
        q = '%s J %d %d A %d %d A %d %d A %d %d' % (g, c1, c2, c1, a1, c2, a2, c3, a3)
    Q.append(q); kinds.append(typ)
inp = '\n'.join(Q) + '\n'
R = {}
for name in ('a42solve', 'lnsolve3', 'lnsolve'):
    R[name] = subprocess.run(['./' + name, '-b', B], input=inp, capture_output=True, text=True).stdout.split('\n')[:len(Q)]
import collections
C = collections.Counter(); dis = 0; und = 0; wit = 0
for i, q in enumerate(Q):
    st = {nm: R[nm][i].split()[0] for nm in R}
    for nm in R:
        if st[nm] == 'SAT':
            r = check_qa(q, R[nm][i]); wit += 1
            if r != 'OK': print('BADWITNESS', nm, q, r)
    dec = [s for s in st.values() if s != 'UNDEC']
    if len(dec) < 3: und += 1
    if len(set(dec)) > 1: dis += 1; print('DISAGREE', q, st)
    C[(kinds[i], st['a42solve'])] += 1
print('queries', len(Q), 'disagreements', dis, 'with some UNDEC', und, 'witnesses checked', wit)
print('by (kind, a42solve answer):', dict(sorted(C.items())))
