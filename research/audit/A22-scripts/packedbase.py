"""packedbase.py N [EXTRA]: for every instance / orientation / admissible walk of least length (+EXTRA),
test whether the three base pairs {x,y}, {a,l1}, {l1,y} are packed in the base graph M (pairwise
distance >= 3 per pair) and whether M has a Lovasz decomposition separating them.  A base graph with
packed pairs and no separating decomposition is a counterexample to separating a path of three
packed pairs (union of two matchings) with one even vertex."""
import sys, itertools, subprocess
from bf import parse_g6, lovasz
from walkcheck_lib import adm_walks, base_graph, packed
N = int(sys.argv[1]); EXTRA = int(sys.argv[2]) if len(sys.argv) > 2 else 0
g6s = subprocess.run(['nauty-geng', '-cq', str(N)], capture_output=True, text=True).stdout.split()
tot = pk = pk_fail = 0
for s in g6s:
    n, A = parse_g6(s)
    if any(sum(A[v]) % 2 == 0 for v in range(n)):
        continue
    E = [(u, v) for u in range(n) for v in range(u + 1, n) if A[u][v]]
    for e, f in itertools.combinations(E, 2):
        if set(e) & set(f):
            continue
        for (E1, E2) in ((e, f), (f, e)):
            for a, b in (E1, E1[::-1]):
                for x, y in (E2, E2[::-1]):
                    W = adm_walks(n, A, a, b, x, y)
                    if not W:
                        continue
                    L = min(len(P) for P in W)
                    for P in W:
                        if len(P) > L + EXTRA:
                            continue
                        tot += 1
                        B = base_graph(n, A, a, b, x, y, P)
                        if packed(B, x, y) and packed(B, a, n) and packed(B, n, y):
                            pk += 1
                            if not lovasz(n + 1, B, sep=[(x, y), (a, n), (n, y)])[0]:
                                pk_fail += 1
                                print('PACKED-BASE-FAIL', s, 'ab=%d%d xy=%d%d P=%s' % (a, b, x, y, P))
print('N=%d base graphs=%d packed=%d packed-but-no-separation=%d' % (N, tot, pk, pk_fail))
