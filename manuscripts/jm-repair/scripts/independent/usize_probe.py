# Written by an independent internal referee agent (Nov 2026); copied here for reproducibility.
import itertools, sys
sys.path.insert(0, '.')
from thmB_exhaustive import decomps, extension_exists
from cuts_vs_direct import cuts_ok
n, m = int(sys.argv[1]), int(sys.argv[2]); k = 2*n+1-m
E, D = decomps(m, n)
res = {}
seen=set()
for colv in D:
    p = [m - sum(1 for j in colv if j == i) for i in range(n)]
    if max(p) > k: continue
    for usz in range(1, n+1):
        for U in itertools.combinations(range(n), usz):
            if any(p[i] > k-1 for i in U): continue
            for c in U:
                T = [i for i in range(n) if i not in U]
                key = tuple(sorted((('T' if i in T else ('c' if i == c else 'S')), tuple(sorted(e for e, j in zip(E, colv) if j == i))) for i in range(n)))
                if key in seen: continue
                seen.add(key)
                delta = [max(0, p[i]+(4 if i in T else (3 if i==c else 5))-k) for i in range(n)]
                d = extension_exists(m, n, E, colv, c, delta)
                r = res.setdefault(usz, [0,0]); r[0]+=1; r[1]+= (not d)
                if not d and usz <= (k-1)//2 + 0 and len(res.get('ex',[]))<3: res.setdefault('ex',[]).append((colv,U,c,p,delta))
print(n,m,k,res)
