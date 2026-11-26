from fractions import Fraction as Fr
def cd(a,b): return -((-a)//b)
bad = []; bcases = set(); cnt = 0
for k in range(130, 1500):
    for g in range(1, k):
        l, D = (3, 2) if g == 1 else (g, g*(g+1)//2)
        if l + D > k: continue
        rmax = (3*k - l + 2*g + 2 - 3*D)//2
        for r in range(k+2, rmax+1):
            cnt += 1
            u = r-k; d = cd(r,2); v = k-d; M = r-2+(1 if r%2==0 else 0); E = k+g-d
            if not (k >= 12*g+3 and k >= 10*g+40): bad.append(("kg",k,g,r))
            if not (cd(2*r+l-5*g-2+3*D,3) >= d): bad.append(("singletons",k,g,r))
            if not (M-E >= 2*u-1): bad.append(("ME",k,g,r))
            if r <= (4*k)//3 - 1:
                # need >= v forests of size >= 4u: else (2d-k+1) forests lost >= M-(4u-1)
                if not ((2*d-k+1)*(M-4*u+1) > E): bad.append(("R1",k,g,r))
            elif Fr(r) <= Fr(7*k,5):
                b = max(0, 1-3*d+2*k)
                if b > 0:
                    bcases.add((k%3, r-(4*(k//3)), b))
                    if not (2*d-k-g >= b and M >= 4*u-1 and r%2==0): bad.append(("R2b",k,g,r))
                if not (d - b >= 2*(v-b) + 1): bad.append(("R2count",k,g,r))
                if not (M - Fr(E,2) >= 3*u): bad.append(("R2size",k,g,r))
            else:
                if not (d - Fr(E,4) >= 2*v): bad.append(("R3count",k,g,r))
                if not (M - 3 >= 3*u): bad.append(("R3size",k,g,r))
print("cases", cnt, "bad", len(bad), bad[:10]); print("b>0 patterns (k mod 3, r-4*floor(k/3), b):", sorted(bcases))
