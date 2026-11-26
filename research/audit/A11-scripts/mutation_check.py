"""Mutation test for cert_check.py Part B: weakening any one hypothesis of Lemmas 6-8 must produce
(graph, labelling) pairs on which the lemma's certificate is illegal; otherwise the hypothesis is
superfluous (or the checker is vacuous). Also checks the A = T supplies 4 and 3."""
import itertools
import cert_check as C

def adj(K, p, q):
    return frozenset((p, q)) in K

weak = {
 'match': [
   ('drop p~z', lambda K,p,q,p2,q2,z: adj(K,p,q) and adj(K,p2,q2) and not adj(K,p2,z) and not adj(K,p2,q)),
   ("drop p'~z", lambda K,p,q,p2,q2,z: adj(K,p,q) and adj(K,p2,q2) and not adj(K,p,z) and not adj(K,p2,q)),
   ("drop p'~q", lambda K,p,q,p2,q2,z: adj(K,p,q) and adj(K,p2,q2) and not adj(K,p,z) and not adj(K,p2,z)),
 ],
 'oddstar': [
   ('drop p-condition', lambda K,a,w,p,q,z: {t for t in C.T5 if t!=a and adj(K,a,t)}=={w,p,q} and not all(adj(K,q,s) for s in (w,p,z))),
 ],
 'unistar': [
   ('drop c isolated', lambda K,x,a,b,c,d: adj(K,x,a) and adj(K,x,b) and adj(K,x,c) and not(adj(K,a,b) and adj(K,a,d)) and not(adj(K,b,a) and adj(K,b,d))),
   ('drop a-condition', lambda K,x,a,b,c,d: adj(K,x,a) and adj(K,x,b) and adj(K,x,c) and not any(adj(K,c,t) for t in (a,b,d)) and not(adj(K,b,a) and adj(K,b,d))),
 ],
}
gens = {n: g for n, g, h in C.LEMMAS}
for name, lst in weak.items():
    for label, hyp in lst:
        bad = 0
        for K in C.all_graphs():
            for lab in itertools.permutations(C.T5):
                if not hyp(K, *lab):
                    continue
                H, prog, _ = gens[name](K, *lab)
                try:
                    C.run(C.five_model(K), H, prog)
                except C.Fail:
                    bad += 1
        print(f'{name:8s} {label:18s}: {bad} illegal certificates (must be > 0)')
        assert bad > 0
# A = T supplies
for prog in C.xabcd_progs():
    log = []
    C.run(C.bowtie_model(C.BOWTIE, 'xabcd'), [frozenset(h) for h in ['xu','au','bu','cu','du','uv']], prog, log=log)
    outs = [(s, b) for d, r, s, b in log if d == ('u',) and r in 'abcd']
    assert all(s in (4, 3) and b <= 2 for s, b in outs), outs
print('A = T: outward moves have supply 4 then 3 and at most 2 blanks, in both orders')
