import sys, collections
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lnlib import g6_decode
C = collections.defaultdict(lambda: [0,0,0])
for line in open('scan8.out'):
    inst, rest = line.split(' | ')
    t = inst.split(); n, adj = g6_decode(t[0]); c1,a1,c2,a2 = map(int,t[1:5])
    recs = [r.split(':') for r in rest.split()]
    for r in recs:
        o, x, kind, sch, ex = int(r[0]), int(r[1]), r[2], r[3], r[4]
        ci,ai,cj,aj = (c1,a1,c2,a2) if o==0 else (c2,a2,c1,a1)
        if kind != 'b': continue
        f = (len(adj[ci]), len(adj[x]), x in adj[aj], x in adj[cj], x in adj[ai], cj in adj[ci])
        f = ('dci=%d'%len(adj[ci]), 'x~aj' if x in adj[aj] else '-', 'x~cj' if x in adj[cj] else '-', 'x~ai' if x in adj[ai] else '-', 'ci~cj' if cj in adj[ci] else '-', 'dcj=%d'%len(adj[cj]))
        C[f][0]+=1; C[f][1]+= sch=='Y'; C[f][2]+= ex=='S'
for f in sorted(C): 
    a,b,c = C[f]
    print(f, a, 'sched %.3f'%(b/a), 'exact %.3f'%(c/a))
