"""A24 (b), per-target variant (b_linf_peru.py): additionally counts, per (instance, u), the
number of D', of failing D', and of D' with y in N(u) (tight), to test Conjecture 3.5 per target.

A24 (b): independent re-derivation of E26(B), the L-infinity (GL) residual.
K connected of order n, exactly one even vertex z, a leaf l with neighbour c (c odd), d(c,z) = 3,
every neighbour of z at distance 2 from c, and d(z) >= 4 or z on a triangle.  B = {l} + N[c].
For every u in N(z) and every Lovász decomposition D' of K - zu whose l-path lies in B: the forced
Fan chain z -> u (own code), the result, and (y in N(u), chain reaches y, result l-path in B),
y = far end of the l-path.  Only mylib.py is used.
usage: python3 b_linf.py n [stride offset]
"""
import sys, subprocess, collections
import mylib as M

n = int(sys.argv[1])
stride = int(sys.argv[2]) if len(sys.argv) > 2 else 1
off = int(sys.argv[3]) if len(sys.argv) > 3 else 0
gs = subprocess.run(['nauty-geng', '-cq', str(n)], capture_output=True, text=True).stdout.split()
C = collections.Counter(); ninst = 0; nsel = 0; Iset = []
for s in gs:
    K = M.g6(s)
    ev = M.evens(K)
    if len(ev) != 1:
        continue
    z = ev[0]
    for l in sorted(K):
        if len(K[l]) != 1:
            continue
        c = next(iter(K[l]))
        if len(K[c]) % 2 == 0:
            continue
        d = M.bfs_dist(K, c)
        if d.get(z) != 3 or any(d[u] != 2 for u in K[z]):
            continue
        tri = any(b in K[a] for a in K[z] for b in K[z])
        if not (len(K[z]) >= 4 or tri):
            continue
        ninst += 1
        if (ninst - 1) % stride != off:
            continue
        nsel += 1
        B = {l, c} | set(K[c])
        okf = (lambda P, B=B, l=l: (l not in P) or set(P) <= B)
        # GL for K itself
        gl = any(True for _ in M.decomps_pg(K, M.lov(K), first_edges=[(l, c)], path_ok=okf))
        C['GL holds' if gl else 'GL FAILS'] += 1
        closes = False; good_u = []
        for u in sorted(K[z]):
            K1 = M.deledge(K, (z, u)); b1 = M.lov(K1)
            allok = True; cnt = 0; nfail = 0; ntight = 0
            for D1 in M.decomps_pg(K1, b1, first_edges=[(l, c)], path_ok=okf):
                P = M.path_with_end(D1, l)
                assert set(P) <= B
                y = P[-1] if P[0] == l else P[0]
                st, ch, ix = M.forced_chain(D1, z, u)
                assert st == 'ok'
                D2 = M.exec_chain(D1, ch, ix, u)
                assert M.verify(K, D2, M.lov(K))
                ok = set(M.path_with_end(D2, l)) <= B
                hit = y in ch
                C[(y in K[u], hit, ok)] += 1
                if hit and ch[-1] != y:
                    C['REACHES-y-BUT-DOES-NOT-STOP'] += 1
                cnt += 1; closes |= ok; allok &= ok; nfail += (not ok); ntight += (y in K[u])
            if cnt and allok:
                good_u.append(u)
            if cnt == 0:
                C['target with no D\''] += 1
            C[('per-u', 'has tight D\'' if ntight else 'no tight D\'', 'all D\' fail' if cnt and nfail == cnt else ('some D\' succeeds' if cnt else 'no D\''))] += 1
        C['instance closes' if closes else 'instance DOES NOT close'] += 1
        C['some u: every D\' succeeds' if good_u else 'every u has a failing D\''] += 1
        Iset.append((s, l, c, z, bool(good_u)))
print("order", n, "instances", ninst, "selected", nsel)
print("key = (y in N(u), chain reaches y, result in B)")
for k, v in sorted(C.items(), key=str):
    print(k, v)
for t in Iset:
    print("I", *t)
