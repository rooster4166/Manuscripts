"""A42: the 1,692 Criterion R3 certificates (data/m3_R3_certificates.txt): static conditions of
Definition 9.1, and an exact completion: K0 = F - E(pre-committed paths), with a new leaf l at c_k,
'S l a_k' solved by a42solve; the final decomposition (D0 minus l, plus the paths) is checked by
a42lib.check for all three avoidances (Proposition 9.2's construction)."""
import sys, subprocess, collections, itertools
sys.path.insert(0, __import__('os').path.dirname(__file__))
from a42lib import g6dec, g6enc, check, parse_answer
C = collections.Counter(); jobs = []
for l in open(sys.argv[1]):
    t = l.split()
    if not t or t[0] != 'OK': C['not OK line'] += 1; continue
    form = t[1]; g = t[2]; n, adj = g6dec(g)
    nums = [int(x) for x in t[3:12] if x != 'A']; T = [(nums[0], nums[1]), (nums[2], nums[3]), (nums[4], nums[5])]
    rest = ' '.join(t[12:]); Ps = [[int(x) for x in p.split('-')] for p in rest.split('P=')[1].split(' moves')[0].split()]
    ok = all(len(set(P)) == len(P) >= 2 and all(b in adj[a] for a, b in zip(P, P[1:])) for P in Ps)
    E = [frozenset(e) for P in Ps for e in zip(P, P[1:])]; ok = ok and len(E) == len(set(E))
    k = None
    if form == 'A' and len(Ps) == 1:
        P = Ps[0]
        for i, j in itertools.permutations(range(3), 2):
            if P[0] == T[i][0] and P[-1] == T[j][0] and T[i][1] not in P and T[j][1] not in P: k = 3 - i - j
    elif form == 'B' and len(Ps) == 2:
        P1, P2 = Ps
        for i, j in itertools.permutations(range(3), 2):
            if P1[0] == T[i][0] and P2[0] == T[j][0] and T[i][1] not in P1 and T[j][1] not in P2:
                kk = 3 - i - j; ends = [P1[0], P1[-1], P2[0], P2[-1]]
                if len(set(ends)) == 4 and T[kk][0] not in ends and T[kk][1] not in ends: k = kk
    if not ok or k is None: C['static FAIL'] += 1; print('STATIC FAIL', l.strip()); continue
    C['static OK ' + form] += 1
    ck, ak = T[k]; A = [set(s) for s in adj]
    for P in Ps:
        for a, b in zip(P, P[1:]): A[a].discard(b); A[b].discard(a)
    A.append({ck}); A[ck].add(n)
    jobs.append((l, n, adj, T, Ps, g6enc(n + 1, A) + ' S %d %d' % (n, ak)))
out = subprocess.run(['./a42solve', '-b', '100000000'], input='\n'.join(j[-1] for j in jobs) + '\n', capture_output=True, text=True).stdout.split('\n')
for (l, n, adj, T, Ps, q), a in zip(jobs, out):
    st, D = parse_answer(a)
    if st != 'SAT': C['completion ' + st] += 1; print('NO COMPLETION', st, l.strip()); continue
    D = [[v for v in Q if v != n] for Q in D]; D = [Q for Q in D if len(Q) >= 2] + Ps
    err = check(n, adj, D, avoid=T)
    C['final OK' if err is None else 'final FAIL ' + err] += 1
print(dict(C))
