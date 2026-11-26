# Written by an independent internal referee agent (Nov 2026); copied here for reproducibility.
"""Abstract check of the aggregation steps in Prop UH and Prop LH.
Only per-colour profiles (type, p, n0, n1, n2) and the slot identities
sum f_i(B) = k b, sum f_i(A) = k a are used, exactly as in the proofs.
UH: is there a multiset (one c-colour, any number of T/S colours) with
    sum f_B == 0 mod k and sum u < 0 ?
LH: is there a multiset (one c, any number of T, at most floor((k-4)/2) S colours)
    with sum f_A == 0 mod k and sum s < 0 ?"""
import sys

def profiles(k, typ):
    pmax = k if typ == 'T' else k - 1
    eps = {'T': 4, 'c': 3, 'S': 5}[typ]
    kap = 2 if typ == 'c' else 4
    out = set()
    for p in range(1, pmax + 1):
        for n0 in range(p + 1):
            for n1 in range(p - n0 + 1):
                n2 = p - n0 - n1
                fA, fB = 2*n0 + n1, n1 + 2*n2
                psi = n1 + n2 + (1 if (n2 >= 1 and typ != 'c') else 0)
                delta = max(0, p + eps - k)
                D = max(0, delta - psi)
                s = 2*fA - k*D
                u = k*min(kap, psi) - 2*fB
                out.add((fA, fB, s, u))
    return out

def check(k):
    T = profiles(k, 'T'); S = profiles(k, 'S'); C = profiles(k, 'c')
    # ---- UH: non-c colours all have u >= 0; bound total u by 2k
    BOUND = 2*k
    reach = {(0, 0)}
    frontier = [(0, 0)]
    nonc = [(fB % k, u) for (fA, fB, s, u) in T | S]
    assert all(u >= 0 for _, u in nonc)
    while frontier:
        nf = []
        for (r, U) in frontier:
            for (df, du) in nonc:
                st = ((r + df) % k, U + du)
                if st[1] < BOUND and st not in reach:
                    reach.add(st); nf.append(st)
        frontier = nf
    uh_bad = []
    for (fA, fB, s, u) in C:
        for (r, U) in reach:
            if (r + fB) % k == 0 and U + u < 0:
                uh_bad.append(((fA, fB, s, u), r, U))
    # ---- LH
    smax = (k - 4)//2
    Tn = [(fA % k, s) for (fA, fB, s, u) in T]
    assert all(s >= 0 for _, s in Tn)
    Sn = [(fA % k, s) for (fA, fB, s, u) in S]
    Cn = [(fA % k, s) for (fA, fB, s, u) in C]
    assert all(s >= 0 for _, s in Cn)
    B2 = 4*smax + 1  # positive part never needs to exceed total negativity
    # T-closure
    reachT = {(0, 0)}; frontier = [(0, 0)]
    while frontier:
        nf = []
        for (r, s0) in frontier:
            for (df, ds) in Tn:
                st = ((r + df) % k, s0 + ds)
                if st[1] < B2 and st not in reachT:
                    reachT.add(st); nf.append(st)
        frontier = nf
    # add exactly one c
    cur = set()
    for (r, s0) in reachT:
        for (df, ds) in Cn:
            if s0 + ds < B2: cur.add(((r + df) % k, s0 + ds))
    lh_bad = []
    allst = set(cur)
    for j in range(smax):
        nxt = set()
        for (r, s0) in cur:
            for (df, ds) in Sn:
                if s0 + ds < B2: nxt.add(((r + df) % k, s0 + ds))
        cur = nxt; allst |= cur
    for (r, s0) in allst:
        if r == 0 and s0 < 0: lh_bad.append((r, s0))
    return uh_bad, lh_bad

for k in range(4, int(sys.argv[1]) if len(sys.argv) > 1 else 31):
    uh, lh = check(k)
    print(k, 'UH-bad', len(uh), 'LH-bad', len(lh), uh[:2], lh[:2])
