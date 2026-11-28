"""A39: the smaller checks, in one place.
  1. J9_d6: 1,819 graphs, all 3-connected, unique even vertex; triangle data at 10,118 roots, at
     1,597 of the 1,756 degree-7 roots, and these are exactly the unscheduled degree-7 roots.
  2. The 52 no-connector roots: distance of q1, q2 in G (49 at 3, 3 at 4).
  3. MR Prop 139 hypotheses at the 1,756 order-9 roots; Cor 138 / Thm 140 conditions in the
     residual families.
  4. Frozen roots: 113 = 23 + 90 from J9_explore.txt (min_phi = 5, degree < n - 2).
  5. Residual ret.c witnesses: number of nontrivial members by order; Lovasz end type.
"""
import sys, itertools
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from g6 import parse_g6, J_from_resid

M = '/home/user/Manuscripts/manuscripts'


def conn_wo(n, adj, rem):
    vs = [v for v in range(n) if v not in rem]
    seen = {vs[0]}; st = [vs[0]]
    while st:
        v = st.pop()
        for w in adj[v]:
            if w not in rem and w not in seen:
                seen.add(w); st.append(w)
    return len(seen) == len(vs)


def has_pm(vs, adj):
    if not vs:
        return True
    a = vs[0]
    return any(b in adj[a] and has_pm([x for x in vs[1:] if x != b], adj) for b in vs[1:])


def dist(G, a, b):
    d = {a: 0}; fr = [a]
    while fr:
        nf = []
        for v in fr:
            for w in G[v]:
                if w not in d:
                    d[w] = d[v] + 1; nf.append(w)
        fr = nf
    return d.get(b)


uns = {}
for l in open(M + '/multi-token/data/runs/J9_none.txt'):
    f = l.split(); uns[f[0]] = set(map(int, f[1].split(',')))
C = Counter()
for l in open(M + '/multi-token/data/J9_d6.g6'):
    g = l.split()[0]; n, adj = parse_g6(g)
    ev = [v for v in range(n) if len(adj[v]) % 2 == 0]
    C['graphs'] += 1; C['unique even'] += len(ev) == 1
    C['3-connected'] += all(conn_wo(n, adj, set(S)) for t in range(3) for S in itertools.combinations(range(n), t))
    z = ev[0]; Z = sorted(adj[z]); VB = [v for v in range(n) if v != z]
    adjB = {v: adj[v] - {z} for v in VB}
    evB = {v for v in VB if len(adjB[v]) % 2 == 0}
    for r in Z:
        data = any(has_pm([x for x in Z if x not in (r, w)], adj) for w in Z if w != r)
        C['roots with data'] += data
        if len(adj[r]) != n - 2:
            continue
        C['deg7'] += 1; C['deg7 with data'] += data
        u = g in uns and r in uns[g]
        C['deg7 unscheduled'] += u; C['deg7 data != unscheduled'] += data != u
        s = [v for v in VB if v != r and v not in adjB[r]][0]
        # Prop 139: B 2-connected (J 3-connected), six even vertices, d_B(r) = 6, an even neighbour
        C['Prop139 hypotheses'] += (len(evB) == 6 and len(adjB[r]) == 6 and r in evB
                                    and any(w in evB for w in adjB[r]))
        if s in adj[z]:
            T = [v for v in VB if v not in adj[z]]
            G = {v: adjB[v] - {r} for v in VB if v != r}
            q1, q2 = T
            if q2 not in G[q1] and not (G[q1] & G[q2]):
                C['no connector, dist_G(q1,q2)=%s' % dist(G, q1, q2)] += 1
print('1-3 (order 9):', dict(C))

for f in ['resid_O8', 'resid_O10', 'e28_hard', 'clt_hard']:
    D = Counter()
    for l in open(M + '/multi-token/data/%s.g6' % f):
        n, adj = J_from_resid(l.split()[0]); z = n - 1
        VB = [v for v in range(n) if v != z]; adjB = {v: adj[v] - {z} for v in VB}
        Z = set(adj[z])
        D['min deg B=%d' % min(len(adjB[v]) for v in VB)] += 1
        D['min even deg B=%d' % min(len(adjB[v]) for v in Z)] += 1
        for r in sorted(Z):
            if len(adj[r]) != n - 2:
                continue
            T = Z - {r}
            D['roots'] += 1
            D['Thm140'] += any(w not in Z and len(adjB[w]) == 5 and len(adjB[w] & T) >= 3 for w in VB)
            D['Prop139 (d_B(r)=6)'] += len(adjB[r]) == 6
    print('3 (%s):' % f, dict(sorted(D.items())))

F = Counter(); fro = []
for l in open(M + '/multi-token/data/runs/J9_explore.txt'):
    f = l.split()
    if f[0] != 'ROOT':
        continue
    g = f[1]; r = int(f[2].split('=')[1]); mp = int(f[-1].split('=')[1])
    n, adj = parse_g6(g)
    if mp == 5 and len(adj[r]) < n - 2:
        fro.append((g, r)); F['deg %d' % len(adj[r])] += 1
ship = [tuple(l.split()[:2]) for l in open(M + '/dense-root/data/frozen9.txt')]
print('4 frozen:', len(fro), dict(F), 'same as frozen9.txt:', set((g, str(r)) for g, r in fro) == set(ship))

P = Counter()
for fn in ['ret_resid_O8.out', 'ret_resid_O10.out', 'ret_e28_hard.out', 'ret_clt_hard.out']:
    for l in open(M + '/dense-root/data/' + fn):
        x = l.split()
        if x[2] != 'YES':
            continue
        g = x[0]; r = int(x[1]); n, adj = parse_g6(g)
        pieces = [p.strip() for p in l.split(' | ')[1].split(';') if p.strip()]
        nt = [list(map(int, p.split(':')[1].split(','))) for p in pieces]
        nt = [q for q in nt if len(q) > 1]
        N = adj[r]; s = [v for v in range(n) if v != r and v not in adj[r]][0]
        e = Counter()
        for q in nt:
            e[q[0]] += 1; e[q[-1]] += 1
        lov = all(e[x] == 1 for x in N) and e[s] == 0
        P[('|B|=%d' % n, 'k-1=%d' % (n // 2 - 1), 'nontrivial=%d' % len(nt))] += 1
        P['Lovasz end type'] += lov
print('5 residual ret.c witnesses:', sorted(P.items(), key=str))
