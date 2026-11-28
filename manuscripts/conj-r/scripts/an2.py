import sys, collections
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
from lnlib import g6_decode
C = collections.Counter(); D = collections.Counter(); G=set(); Gall=set()
for line in open('scan8.out'):
    inst, rest = line.split(' | ')
    t = inst.split(); n, adj = g6_decode(t[0]); m = sum(len(a) for a in adj)//2
    recs = [r.split(':') for r in rest.split()]
    D[m] += 1
    Gall.add(t[0])
    if not any(r[4]=='S' for r in recs):
        C[m] += 1; G.add(t[0])
print('no single-edge exact, by edge count:', sorted(C.items()))
print('all instances by edge count:', sorted(D.items()))
print('graphs', len(G), 'of', len(Gall))
