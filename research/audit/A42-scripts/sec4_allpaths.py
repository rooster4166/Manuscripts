"""A42: Section 4 'all paths' (pall.py -int semantics): every path P from c_i avoiding a_i, both
orientations, c_j allowed interior; paths ending at c_j through a_j are skipped.  (1) exact record
counts by (length, kind); (2) exact least length of a working P not ending at a_j (lengths tried in
increasing order, solved with a42solve); (3) all records of a random sample of instances solved."""
import sys, subprocess, collections, random
from multiprocessing import Pool
sys.path.insert(0, __import__('os').path.dirname(__file__))
from a42lib import g6dec, g6enc
def recs(line):
    t = line.split(); g = t[0]; n, adj = g6dec(g); c1, a1, c2, a2 = map(int, t[1:5]); out = []
    for o, (ci, ai, cj, aj) in enumerate(((c1, a1, c2, a2), (c2, a2, c1, a1))):
        def ext(P, S):
            if len(P) >= 2:
                kind = 'a' if P[-1] == cj else ('z' if P[-1] == aj else 'b')
                if not (kind == 'a' and aj in P): out.append((o, tuple(P), kind))
            for y in sorted(adj[P[-1]]):
                if y not in S and y != ai: S.add(y); P.append(y); ext(P, S); P.pop(); S.discard(y)
        ext([ci], {ci})
    return out
def query(line, r):
    t = line.split(); n, adj = g6dec(t[0]); c1, a1, c2, a2 = map(int, t[1:5])
    o, P, kind = r; cj, aj = (c2, a2) if o == 0 else (c1, a1)
    A = [set(s) for s in adj]
    for p, q in zip(P, P[1:]): A[p].discard(q); A[q].discard(p)
    if kind == 'a': return g6enc(n, A)
    A.append({cj}); A[cj].add(n); return g6enc(n + 1, A) + ' S %d %d' % (n, aj)
def solve(Q):
    if not Q: return []
    r = subprocess.run(['./a42solve', '-b', '50000000'], input='\n'.join(Q) + '\n', capture_output=True, text=True).stdout.split('\n')
    return [x.split()[0] for x in r[:len(Q)]]
def psolve(Q, k=4):
    ch = [Q[i:i + 3000] for i in range(0, len(Q), 3000)]
    with Pool(k) as p: return [a for r in p.map(solve, ch) for a in r]
if __name__ == '__main__':
    L = [l.strip() for l in open(sys.argv[1]) if l.strip()]
    R = {l: recs(l) for l in L}
    cnt = collections.Counter((len(P) - 1, kind) for l in L for (_, P, kind) in R[l])
    print('records', sum(cnt.values())); print('by (length, kind):', sorted(cnt.items()))
    # (2) least working length (non-z)
    todo = list(L); minw = collections.Counter(); length = 1
    while todo:
        Q = []; idx = []
        for l in todo:
            for r in R[l]:
                if len(r[1]) - 1 == length and r[2] != 'z': Q.append(query(l, r)); idx.append(l)
        ans = psolve(Q); ok = set(l for l, a in zip(idx, ans) if a == 'SAT')
        und = sum(a == 'UNDEC' for a in ans)
        minw[length] = len(ok); print('length', length, 'queries', len(Q), 'instances first working here', len(ok), 'UNDEC', und, flush=True)
        todo = [l for l in todo if l not in ok]; length += 1
        if length > 8: break
    print('least working length (non-z):', sorted(minw.items()), 'none:', len(todo))
    # (3) random sample of instances, all records
    random.seed(int(sys.argv[2])); S = random.sample(L, int(sys.argv[3]))
    Q = []; meta = []
    for l in S:
        for r in R[l]: Q.append(query(l, r)); meta.append((l, len(r[1]) - 1, r[2]))
    ans = psolve(Q); tab = collections.defaultdict(lambda: [0, 0]); per = collections.defaultdict(lambda: [0, 0])
    for (l, ln, kind), a in zip(meta, ans):
        tab[(ln, kind)][0] += 1; tab[(ln, kind)][1] += a == 'SAT'
        if kind != 'z': per[l][0] += 1; per[l][1] += a == 'SAT'
    print('sample of', len(S), 'instances,', len(Q), 'records; fraction working by (length, kind):')
    for k in sorted(tab): print('  ', k, tab[k], '%.3f' % (tab[k][1] / tab[k][0]))
    fr = [w / t for t, w in per.values()]
    print('sample mean fraction working (non-z) %.4f, min %.4f' % (sum(fr) / len(fr), min(fr)))
