"""Sanity check (small): do the elementary moves of the conceptual proof
always apply to the common-vertex (4,3) configuration?
P=(0,1,2,3); three edge-disjoint cycles through x; moves never use L6.
"""
import random, itertools, sys

def nbrs(C, v):
    i = C.index(v); L = len(C)
    return {C[(i-1) % L], C[(i+1) % L]}

def L1ok(Rverts, C):
    """L1 (CFL): path R and cycle C meeting; 2 paths if contacts<=4, or <=5 and C has outside vertex."""
    c = len(set(C) & set(Rverts))
    if c == 0: return False
    if c <= 4: return True
    if c == 5 and not set(C) <= set(Rverts): return True
    return False

def exchange_pair(C, D):
    for v in set(C) & set(D):
        if (nbrs(C, v) - set(D)) and (nbrs(D, v) - set(C)):
            return True
    return False

def circ3(Cs):
    common = set(Cs[0]) & set(Cs[1]) & set(Cs[2])
    for v in common:
        arc = lambda i, j: bool(nbrs(Cs[i], v) - set(Cs[j]))
        for (i, j, k) in [(0, 1, 2), (0, 2, 1)]:
            if arc(i, j) and arc(j, k) and arc(k, i):
                return True
    return False

def moves(P, Cs):
    p1, p4 = P[0], P[-1]
    # M1
    for C in Cs:
        if p1 not in C or p4 not in C: return 'M1'
    # M2, M3
    for a, b in itertools.combinations(range(3), 2):
        if exchange_pair(Cs[a], Cs[b]): return 'M2'
    if circ3(Cs): return 'M3'
    for Pdir in (P, P[::-1]):
        e = Pdir[0]
        # M4
        for i, j in itertools.permutations(range(3), 2):
            k = 3 - i - j
            if not (nbrs(Cs[i], e) - set(Cs[j])): continue
            for z in nbrs(Cs[j], e) - set(P):
                if L1ok([z] + list(Pdir), Cs[k]): return 'M4'
        # M5: open X at e
        for xi in range(3):
            X = Cs[xi]; others = [Cs[j] for j in range(3) if j != xi]
            for t in nbrs(X, e) - set(P):
                R1 = [t] + list(Pdir)
                for (Y, Z) in (others, others[::-1]):
                    for R in (R1, R1[::-1]):
                        u = R[-1]
                        if u not in Y or u not in Z:
                            continue
                        # M5a: (d) at u
                        if (nbrs(Y, u) - set(Z)) and (nbrs(Z, u) - set(R)): return 'M5a'
                        # open Y at u
                        for y in nbrs(Y, u) - set(R):
                            R2 = R + [y]
                            for R2d in (R2, R2[::-1]):
                                w = R2d[-1]
                                if w in Z and (nbrs(Z, w) - set(R2)): return 'M5b'
                            if L1ok(R2, Z): return 'M5c'
                    # first-contact variants for Y from the t end when t not in Y
                    if t not in Y:
                        for s in nbrs(Y, e) - set(Pdir[2:]):
                            R2 = [s] + list(Pdir)
                            if L1ok(R2, Z): return 'M5d'
    return None

def rand_instance(N, xpos, maxlen, rng, ham=False):
    P = [0, 1, 2, 3]
    used = {frozenset((P[i], P[i+1])) for i in range(3)}
    Cs = []
    for _ in range(3):
        for att in range(500):
            L = N if ham else rng.randint(3, min(maxlen, N))
            others = [v for v in range(N) if v != xpos]
            rng.shuffle(others)
            C = [xpos] + others[:L-1]
            es = {frozenset((C[i], C[(i+1) % L])) for i in range(L)}
            if es & used: continue
            used |= es; Cs.append(C); break
        else:
            return None
    return P, Cs

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    stats = {}
    fails = []
    for trial in range(int(sys.argv[2]) if len(sys.argv) > 2 else 20000):
        N = rng.choice([6, 7, 8, 9, 10, 12, 15])
        ham = rng.random() < 0.3
        xpos = rng.choice([0, 1])
        inst = rand_instance(N, xpos, rng.choice([5, 6, 8, 12]), rng, ham)
        if inst is None: continue
        P, Cs = inst
        r = moves(P, Cs)
        stats[r] = stats.get(r, 0) + 1
        if r is None: fails.append((xpos, Cs))
    print(stats)
    for f in fails[:10]: print(f)
