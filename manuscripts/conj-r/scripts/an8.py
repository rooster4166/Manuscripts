"""an8.py -- case (a) at order 8: classify non-tight K0 = F - E(P) by two-even obstructions."""
import sys, collections
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lnlib import g6_decode
def ekey(a, b): return (a, b) if a < b else (b, a)
def comps(n, A, vs):
    seen=set(); out=[]
    for s in vs:
        if s in seen: continue
        c={s}; st=[s]; seen.add(s)
        while st:
            u=st.pop()
            for v in A[u]:
                if v in vs and v not in seen: seen.add(v); c.add(v); st.append(v)
        out.append(c)
    return out
def twoconn(n, A):
    act=[v for v in range(n) if A[v]]
    if len(comps(n,A,set(act)))!=1: return False
    for x in act:
        rest=set(act)-{x}
        if rest and len(comps(n,A,rest))>1: return False
    return True
C=collections.Counter()
for line in open('pall8.out'):
    inst, rest = line.split(' | ')
    t = inst.split(); n, adj = g6_decode(t[0]); c1,a1,c2,a2 = map(int,t[1:5])
    for r in rest.split():
        o, P, kind, res = r.split(':')
        if kind != 'a' or o != '0': continue
        P = tuple(map(int,P.split('-')))
        A=[set(a) for a in adj]
        for p,q in zip(P,P[1:]): A[p].discard(q); A[q].discard(p)
        d=[len(a) for a in A]
        act=[v for v in range(n) if d[v]]
        na=len(act)
        o1 = any(d[v]%2==1 and d[v]==na-1 for v in act)
        tc = twoconn(n,A)
        both = d[c1] > 0 and d[c2] > 0
        key=('tight' if res=='S' else 'NOT')+(' O1' if o1 else '')+(' 2conn' if tc else ' not2conn')+(' both-ends-active' if both else ' an-end-isolated')
        C[key]+=1
for k in sorted(C): print(k, C[k])
