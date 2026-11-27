"""walkcheck.py N EXTRA [SAMPLE SEED]: independent re-implementation of the walk-theorem reach table.

For every connected all-odd G of order N and every 2-matching {e1, e2}: for each of the 8 choices
(which edge is ab, which end is a, which end of the other edge is x), enumerate the admissible walks
P (Definition 4.1: y -> a, avoiding b and x, interior avoiding N(x)) of length <= least + EXTRA,
build the base graph M = (G - ab + l1 b) - xy - E(P), and test
  BASE   : a Lovasz decomposition of M separating {x,y}, {a,l1}, {l1,y}   (bf.py search)
  SPARSE : the hypotheses of Theorem 5.2 (X = {x,y,a,l1} sparse and the pairs packed, in M or in
           M - xv for one neighbour v of x outside X).
Consistency checks (theorems 4.2 / 5.2): BASE or SPARSE for (a,b,x,y) implies PTM(G,F) with short
ends a and x (bf.py ptm_assign); SPARSE implies BASE (Theorem 3.2 / Lemma 5.1).
Prints the counts: instances, no admissible walk, BASE for some choice, SPARSE for some choice."""
import sys, itertools, subprocess, random
from bf import parse_g6, lovasz, ptm_assign

N, EXTRA = int(sys.argv[1]), int(sys.argv[2])
SAMPLE = int(sys.argv[3]) if len(sys.argv) > 3 else 0
SEED = int(sys.argv[4]) if len(sys.argv) > 4 else 1
DO_BASE = EXTRA == 0


def adm_walks(n, A, a, b, x, y):
    """all admissible y->a paths, grouped by length"""
    res = []

    def dfs(c, path, vis):
        if c == a:
            res.append(list(path))
            return
        for w in range(n):
            if A[c][w] and not vis >> w & 1 and w not in (b, x):
                if w != a and A[w][x]:
                    continue
                path.append(w)
                dfs(w, path, vis | 1 << w)
                path.pop()
    dfs(y, [y], 1 << y)
    return res


def base_graph(n, A, a, b, x, y, P):
    B = [row[:] + [0] for row in A] + [[0] * (n + 1)]
    for u, v in ((a, b), (x, y)) + tuple(zip(P, P[1:])):
        B[u][v] = B[v][u] = 0
    B[n][b] = B[b][n] = 1
    return B


def packed(B, u, v):
    return not B[u][v] and not any(B[u][w] and B[w][v] for w in range(len(B)))


def sparse_ok_in(B, X):
    if any(sum(B[v][p] for p in X) > 1 for v in range(len(B))):
        return False
    x, y, a, l1 = X
    return packed(B, x, y) and packed(B, a, l1) and packed(B, l1, y)


def sparse_hyp(B, X):
    if sparse_ok_in(B, X):
        return True
    x = X[0]
    for v in range(len(B)):
        if B[x][v] and v not in X:
            B[x][v] = B[v][x] = 0
            ok = sparse_ok_in(B, X)
            B[x][v] = B[v][x] = 1
            if ok:
                return True
    return False


g6s = subprocess.run(['nauty-geng', '-cq', str(N)], capture_output=True, text=True).stdout.split()
inst = []
for s in g6s:
    n, A = parse_g6(s)
    if any(sum(A[v]) % 2 == 0 for v in range(n)):
        continue
    E = [(u, v) for u in range(n) for v in range(u + 1, n) if A[u][v]]
    for e, f in itertools.combinations(E, 2):
        if set(e) & set(f):
            continue
        inst.append((s, n, A, e, f))
total = len(inst)
if SAMPLE:
    rnd = random.Random(SEED)
    inst = rnd.sample(inst, min(SAMPLE, total))

cnt = dict(inst=0, nowalk=0, base=0, sparse=0, bad=0)
for (s, n, A, e, f) in inst:
    cnt['inst'] += 1
    anyw = base_any = sp_any = False
    for (E1, E2) in ((e, f), (f, e)):
        for a, b in (E1, E1[::-1]):
            for x, y in (E2, E2[::-1]):
                W = adm_walks(n, A, a, b, x, y)
                if not W:
                    continue
                anyw = True
                L = min(len(P) for P in W)
                W = [P for P in W if len(P) <= L + EXTRA]
                for P in W:
                    B = base_graph(n, A, a, b, x, y, P)
                    X = (x, y, a, n)
                    sp = sparse_hyp(B, X)
                    bs = None
                    if DO_BASE and (not base_any or sp):
                        bs = lovasz(n + 1, B, sep=[(x, y), (a, n), (n, y)])[0]
                    if sp and bs is False:
                        cnt['bad'] += 1
                        print('SPARSE-BUT-NOT-BASE', s, a, b, x, y, P)
                    if sp or bs:
                        if not ptm_assign(n, A, [(a, b), (x, y)], [a, x]):
                            cnt['bad'] += 1
                            print('THEOREM VIOLATED', s, a, b, x, y, P)
                    base_any |= bool(bs)
                    sp_any |= sp
    cnt['nowalk'] += not anyw
    cnt['base'] += base_any
    cnt['sparse'] += sp_any
print('N=%d EXTRA=%d class size=%d' % (N, EXTRA, total), cnt)
