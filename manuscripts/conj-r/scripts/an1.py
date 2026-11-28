import sys, collections
C = collections.Counter()
for line in open('scan8.out'):
    inst, rest = line.split(' | ')
    recs = [r.split(':') for r in rest.split()]
    anysched = any(r[3]=='Y' for r in recs)
    anyexact = any(r[4]=='S' for r in recs)
    C['inst'] += 1
    C['anysched'] += anysched
    C['anyexact'] += anyexact
    C['anyexact_noz'] += any(r[4]=='S' and r[2]!='z' for r in recs)
    for r in recs:
        C['P'] += 1
        C['P_'+r[2]+'_sched'+r[3]+'_exact'+r[4]] += 1
    # all P exact?
    C['allexact'] += all(r[4]=='S' for r in recs)
    # does some orientation have every x exact
    for o in '01':
        rr = [r for r in recs if r[0]==o]
        if rr and all(r[4]=='S' for r in rr): C['orient_allexact'] += 1; break
    for o in '01':
        rr = [r for r in recs if r[0]==o and r[2]!='z']
        if rr and all(r[3]=='Y' for r in rr): C['orient_allsched'] += 1; break
for k in sorted(C): print(k, C[k])
