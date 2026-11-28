import sys, collections
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lnlib import g6_decode
C = collections.Counter(); L = collections.defaultdict(lambda:[0,0])
minw = collections.Counter(); fracs=[]
rules = collections.Counter()
for line in open('pall8.out'):
    inst, rest = line.split(' | ')
    t = inst.split(); n, adj = g6_decode(t[0]); c1,a1,c2,a2 = map(int,t[1:5])
    recs = []
    for r in rest.split():
        o, P, kind, res = r.split(':'); P = tuple(map(int,P.split('-')))
        recs.append((int(o), P, kind, res))
    C['inst'] += 1
    work = [r for r in recs if r[3]=='S']
    work_nz = [r for r in work if r[2]!='z']
    C['any'] += bool(work); C['any_nz'] += bool(work_nz)
    for r in recs:
        L[(len(r[1])-1, r[2])][0]+=1; L[(len(r[1])-1, r[2])][1]+= r[3]=='S'
    if work_nz: minw[min(len(r[1])-1 for r in work_nz)] += 1
    fracs.append(len(work_nz)/max(1,len([r for r in recs if r[2]!='z'])))
    # rule: all longest P (non-z) work
    nz = [r for r in recs if r[2]!='z']
    mx = max(len(r[1]) for r in nz)
    rules['all_longest_work'] += all(r[3]=='S' for r in nz if len(r[1])==mx)
    rules['some_longest_work'] += any(r[3]=='S' for r in nz if len(r[1])==mx)
    # rule: shortest c1-c2 path avoiding a1,a2 (case a)
    A = [r for r in recs if r[2]=='a']
    if A:
        mn = min(len(r[1]) for r in A)
        rules['has_a'] += 1
        rules['all_shortest_a_work'] += all(r[3]=='S' for r in A if len(r[1])==mn)
        rules['some_a_work'] += any(r[3]=='S' for r in A)
        mxa = max(len(r[1]) for r in A)
        rules['all_longest_a_work'] += all(r[3]=='S' for r in A if len(r[1])==mxa)
    # interior cj
    rules['interior_needed'] += bool(work_nz) and all((r[0]==0 and c2 in r[1][1:-1]) or (r[0]==1 and c1 in r[1][1:-1]) for r in work_nz)
print(C); print('min working length', sorted(minw.items()))
for k in sorted(L): print('len,kind', k, L[k], '%.3f'%(L[k][1]/L[k][0]))
print(rules)
import statistics
print('mean frac working', statistics.mean(fracs), 'min', min(fracs))
