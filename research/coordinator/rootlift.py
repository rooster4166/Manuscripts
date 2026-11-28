"""Root-even lift for Test1 (coordinator idea, unverified): J with unique even vertex z, root r in N(z).
T = N(z) (includes r, |T| = d(z) even); Phi = perfect matching of J[N(z)] with r matched to a0, rooted at r
(and one root per other pair); M = J - {zv : v in N(z)-r} - Phi. Then M has exactly one even vertex r.
Lovasz D0 of M with (i) for each non-root v, p(v) not in Q0(v)  =>  delete z (trim Q0(z)), append Phi edges
=> Test1 at r. This script: (a) checks parity; (b) searches D0 exhaustively (capped) with verify3.predicate;
(c) executes the lift and verifies Test1 independently."""
import itertools, random, sys
sys.path.insert(0, sys.argv[1])
import networkx as nx
from verify3 import lovasz_decomps, predicate, append_and_check, gen_J
def pms(vs, J):
    if not vs: yield []; return
    a=vs[0]
    for b in vs[1:]:
        if J.has_edge(a,b):
            for pm in pms([v for v in vs[1:] if v!=b], J): yield [(a,b)]+pm
rng=random.Random(int(sys.argv[2])); trials=int(sys.argv[3]); Dz=int(sys.argv[4])
stats=dict(roots=0, data=0, ok=0, parity_bad=0, lift_fail=0)
for t in range(trials):
    n=rng.choice([7,9]); J=gen_J(n, Dz, rng); z=0; U=sorted(J.neighbors(z)); k=(n-1)//2
    for r in U:
        stats['roots']+=1; found=False; had=False
        for pm in pms(U, J):
            had=True
            M=J.copy(); M.remove_edges_from([(z,v) for v in U if v!=r]+pm)
            ev=[v for v in M if M.degree(v)%2==0 and M.degree(v)>0]
            if ev!=[r] and not (ev==[] and M.degree(r)==0): stats['parity_bad']+=1; print("PARITY",ev,r); continue
            decs=lovasz_decomps(M, cap=3000)
            for orient in itertools.product([0,1], repeat=len(pm)):
                par={}
                ok_orient=True
                for (a,b),o in zip(pm,orient):
                    if r in (a,b):
                        c = b if a==r else a; par[c]=r   # r is the root of its pair
                        if o==1: ok_orient=False
                    else:
                        if o==0: par[b]=a
                        else: par[a]=b
                if not ok_orient: continue
                for D in decs:
                    if not predicate(D, par): continue
                    paths=[list(p) for p in D]
                    iz=[i for i,p in enumerate(paths) if p[0]==z or p[-1]==z]; P=paths[iz[0]]
                    if P[-1]==z: P.reverse()
                    assert P[1]==r and len(P)>=3, P
                    paths[iz[0]]=P[1:]
                    B=J.copy(); B.remove_node(z)
                    if append_and_check(B, paths, par, k, r=r, need_r=2): found=True; break
                    else: stats['lift_fail']+=1; print("LIFT FAIL", sorted(J.edges()), r, pm, D, par)
                if found: break
            if found: break
        stats['data']+=had; stats['ok']+=found
        if had and not found: print("NO ROOT-EVEN BASE", sorted(J.edges()), "r", r, flush=True)
    print(t, stats, flush=True)
print("FINAL", stats)
