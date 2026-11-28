"""All-odd lift for Test1 (coordinator idea): J with unique even vertex z, r in N(z), Phi a perfect matching
of J[N(z)] with r matched to a0. H = (J - z) - Phi is ALL-ODD. A Lovasz decomposition of H with
r not in Q(a0) and, for each other pair, a_i not in Q(b_i) or b_i not in Q(a_i), lifts (append Phi edges at the
child ends) to a decomposition of J - z into k paths with >= 2 ends at r (Test1)."""
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
st=dict(roots=0, data=0, ok=0, parity_bad=0, lift_fail=0, pm_tested=0, pm_ok=0)
for t in range(trials):
    n=rng.choice([7,9,11]) if Dz<=6 else 11
    J=gen_J(n, Dz, rng); z=0; U=sorted(J.neighbors(z)); k=(n-1)//2
    B=J.copy(); B.remove_node(z)
    for r in U:
        st['roots']+=1; found=False; had=False
        for pm in pms(U, J):
            had=True; st['pm_tested']+=1; pm_ok=False
            H=B.copy(); H.remove_edges_from(pm)
            if any(H.degree(v)%2==0 for v in H if H.degree(v)>0) : st['parity_bad']+=1; print("PARITY"); continue
            Hh=H.copy(); Hh.remove_nodes_from([v for v in list(Hh) if Hh.degree(v)==0])
            decs=lovasz_decomps(Hh, cap=4000)
            for orient in itertools.product([0,1], repeat=len(pm)):
                par={}; skip=False
                for (a,b),o in zip(pm,orient):
                    if r in (a,b):
                        if o==1: skip=True
                        par[b if a==r else a]=r
                    else:
                        if o==0: par[b]=a
                        else: par[a]=b
                if skip: continue
                for D in decs:
                    if predicate(D, par):
                        if append_and_check(B, [list(p) for p in D], par, k, r=r, need_r=2): pm_ok=True; break
                        else: st['lift_fail']+=1; print("LIFT FAIL", sorted(J.edges()), r, pm, D)
                if pm_ok: break
            st['pm_ok']+=pm_ok; found = found or pm_ok
        st['data']+=had; st['ok']+=found
        if had and not found: print("NO ALL-ODD BASE", sorted(J.edges()), "r", r, flush=True)
    print(t, st, flush=True)
print("FINAL", st)
