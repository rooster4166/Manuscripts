"""A42: Section 4 'single edges' recomputed with a42solve (own solver) and own code.
Records (instance, i, x) for every neighbour x of c_i; exact Lemma R hypothesis:
  x = c_j (kind a): F - c_i c_j has a parity decomposition;
  else (kind b, or z if x = a_j): F - c_i x + c_j l has a parity decomposition with l, a_j on no common path."""
import sys, subprocess, collections
from multiprocessing import Pool
sys.path.insert(0, __import__('os').path.dirname(__file__))
from a42lib import g6dec, g6enc
def queries(line):
    t = line.split(); g = t[0]; n, adj = g6dec(g); c1, a1, c2, a2 = map(int, t[1:5]); out = []
    for o, (ci, ai, cj, aj) in enumerate(((c1, a1, c2, a2), (c2, a2, c1, a1))):
        for x in sorted(adj[ci]):
            A = [set(s) for s in adj]; A[ci].discard(x); A[x].discard(ci)
            if x == cj: out.append((o, x, 'a', g6enc(n, A)))
            else:
                A.append({cj}); A[cj].add(n)
                out.append((o, x, 'z' if x == aj else 'b', g6enc(n + 1, A) + ' S %d %d' % (n, aj)))
    return out
def solve(chunk):
    Q = [q for _, recs in chunk for (_, _, _, q) in recs]
    r = subprocess.run(['./a42solve', '-b', '50000000'], input='\n'.join(Q) + '\n', capture_output=True, text=True).stdout.split('\n')
    return [x.split()[0] for x in r[:len(Q)]]
if __name__ == '__main__':
    L = [l.strip() for l in open(sys.argv[1]) if l.strip()]
    data = [(l, queries(l)) for l in L]
    chunks = [data[i:i + 500] for i in range(0, len(data), 500)]
    with Pool(int(sys.argv[2])) as p: res = p.map(solve, chunks)
    C = collections.Counter(); byE = collections.Counter(); allE = collections.Counter(); leafclaim = collections.Counter()
    k = 0; ans = [a for r in res for a in r]
    for l, recs in data:
        t = l.split(); n, adj = g6dec(t[0]); c1, a1, c2, a2 = map(int, t[1:5]); m = sum(map(len, adj)) // 2
        rr = []
        for (o, x, kind, q) in recs:
            a = ans[k]; k += 1; rr.append((o, x, kind, a)); C['P'] += 1; C['P_%s_%s' % (kind, a)] += 1
            if a == 'UNDEC': C['UNDEC'] += 1
            ci, ai, cj, aj = (c1, a1, c2, a2) if o == 0 else (c2, a2, c1, a1)
            if len(adj[ci]) == 1 and x not in (cj, aj) and aj not in adj[x]:
                leafclaim[a] += 1
        C['inst'] += 1; allE[m] += 1
        if any(a == 'SAT' for *_, a in rr): C['anyexact'] += 1
        else: byE[m] += 1
        if any(a == 'SAT' and kind != 'z' for _, _, kind, a in rr): C['anyexact_noz'] += 1
    print(dict(sorted(C.items())))
    print('no single-edge exact, by |E|:', sorted(byE.items()))
    print('instances by |E|:', sorted(allE.items()))
    print('records with d(c_i)=1, stem x not in {c_j,a_j}, x !~ a_j:', dict(leafclaim))
