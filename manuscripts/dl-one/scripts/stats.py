"""A29: compute the Sec. 8 structure statistics of dl-one from `dl -m pairs` output.
usage: python3 stats.py pairs579.txt   (needs dllib.py on sys.path)"""
import sys
sys.path.insert(0,'.')
from dllib import g6_decode, adjsets, degrees
tot_or=0; fail_or=0; cond_viol=0; cond_hold_ok=0; cn1_both=0; cn1_both_bad=0
one_cn_db3=0; one_cn_db3_bad=0; N_hyp=0; N_bad=0; nontwin=0; core=0; core57=0
near_twin_fail=0
for line in open(sys.argv[1]):
    p=line.split(';'); g6=p[0].strip(); g=int(p[1])
    n,E=g6_decode(g6); A=adjsets(n,E); d=degrees(n,E)
    for item in p[2].split(','):
        f=item.split()
        if len(f)<5: continue
        a,b,ob,oa,tw=map(int,f[:5])
        if tw: continue
        nontwin+=1
        if g>=0 and a in A[g] and b in A[g]:
            core+=1
            if n<=7: core57+=1
        # orientations: (y,x,ok): S_y means Q(y) avoids x
        for (y,x,ok) in ((b,a,ob),(a,b,oa)):
            tot_or+=1
            Ny=A[y]-{g}; Ng=A[g] if g>=0 else set()
            c1 = g>=0 and x in A[g]
            c2 = Ny <= A[x]
            c3 = Ng <= (A[x]|{x}|A[y]|{y})
            conds = c1 and c2 and c3
            if not ok:
                fail_or+=1
                if not conds: cond_viol+=1
            elif conds: cond_hold_ok+=1
            cn=A[a]&A[b]
            if len(cn)==1 and d[y]>=3:
                one_cn_db3+=1
                if not ok: one_cn_db3_bad+=1
            # Conjecture N hypothesis: y has neighbour w != g with w not in N(x)
            if any(w!=g and w not in A[x] for w in A[y]):
                N_hyp+=1
                if not ok: N_bad+=1
        if not ob and not oa: near_twin_fail+=1
print("nontwin pairs",nontwin,"orientations",tot_or,"failing",fail_or,"failures violating 3 conds",cond_viol,"conds hold but S_y ok",cond_hold_ok)
print("one common nbr & d(y)>=3:",one_cn_db3,"bad",one_cn_db3_bad)
print("Conj N hyp orientations",N_hyp,"bad",N_bad)
print("core nontwin pairs",core,"of which order<=7:",core57)
print("nontwin pairs failing both",near_twin_fail)
