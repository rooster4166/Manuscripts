"""Stress the moves on nested configurations: three cycles through p1,p4,x,
including three Hamilton cycles of K_N taken from a Walecki decomposition,
with P a 3-edge subpath of a fourth Hamilton cycle (all relabelled randomly)."""
import random, sys
from moves43 import moves

def walecki(N):
    # Hamilton decomposition of K_N, N odd: vertices inf=N-1, 0..N-2
    m = N - 1
    cycles = []
    for i in range((N - 1) // 2):
        seq = [i]
        for k in range(1, m):
            seq.append((i + (k + 1) // 2 * (1 if k % 2 else -1)) % m)
        cycles.append([N - 1] + seq)
    return cycles

def ham_instance(N, rng):
    cyc = walecki(N)
    rng.shuffle(cyc)
    perm = list(range(N)); rng.shuffle(perm)
    cyc = [[perm[v] for v in C] for C in cyc]
    D = cyc[3]; L = len(D); s = rng.randrange(L)
    Pv = [D[(s + i) % L] for i in range(4)]
    relabel = {v: i for i, v in enumerate(Pv)}
    nxt = 4
    for v in range(N):
        if v not in relabel: relabel[v] = nxt; nxt += 1
    Cs = [[relabel[v] for v in C] for C in cyc[:3]]
    return [0, 1, 2, 3], Cs

def nested_instance(N, rng):
    # cycles through 0 and 3 (=p1,p4) and x, random extra vertices, retry until edge-disjoint
    P = [0, 1, 2, 3]
    used = {frozenset((P[i], P[i+1])) for i in range(3)}
    Cs = []
    for _ in range(3):
        for att in range(2000):
            k = rng.randint(0, N - 4)
            extra = rng.sample(range(4, N), k)
            core = [0, 3] + [v for v in (1, 2) if rng.random() < 0.7]
            vs = core + extra
            rng.shuffle(vs)
            if len(vs) < 3: continue
            es = {frozenset((vs[i], vs[(i+1) % len(vs)])) for i in range(len(vs))}
            if es & used: continue
            used |= es; Cs.append(vs); break
        else:
            return None
    return P, Cs

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1]))
    T = int(sys.argv[2])
    stats = {}; fails = []
    for _ in range(T):
        if rng.random() < 0.5:
            P, Cs = ham_instance(rng.choice([9, 11, 13, 15]), rng)
        else:
            inst = nested_instance(rng.choice([6, 7, 8, 9, 10]), rng)
            if inst is None: continue
            P, Cs = inst
        r = moves(P, Cs)
        stats[r] = stats.get(r, 0) + 1
        if r is None: fails.append(Cs)
    print(stats)
    for f in fails[:8]: print(f)
