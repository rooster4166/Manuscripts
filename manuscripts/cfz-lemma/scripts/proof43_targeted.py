"""Targeted sanity check for the special branches (F1) and (F3): cycle A is
forced to contain the cross p3-p1-p4-p2 or the twisted pattern; the other two
cycles are random through p1, p4 on a small vertex pool (to force nesting)."""
import random, sys
from proof43_check import prove

def build(rng, N, kind):
    P = [0, 1, 2, 3]
    used = {frozenset((0, 1)), frozenset((1, 2)), frozenset((2, 3))}
    ext = list(range(4, N))
    if kind == 'cross':
        k = rng.randint(1, len(ext))
        W = rng.sample(ext, k)
        A = [2, 0, 3, 1] + W            # p3 p1 p4 p2 W (closes W[-1]-p3)
    else:
        v, vp = rng.sample(ext, 2)
        others = [w for w in ext if w not in (v, vp)]
        mid = rng.sample(others, rng.randint(0, len(others)))
        A = [v, 0, 3, vp] + mid          # v p1 p4 v' ... (twisted: A contains v-p1-p4-v')
    es = {frozenset((A[i], A[(i+1) % len(A)])) for i in range(len(A))}
    if es & used: return None
    used |= es
    Cs = [A]
    for _ in range(2):
        for att in range(3000):
            extra = rng.sample(ext, rng.randint(1, len(ext)))
            core = [0, 3] + [w for w in (1, 2) if rng.random() < 0.8]
            vs = core + extra; rng.shuffle(vs)
            e2 = {frozenset((vs[i], vs[(i+1) % len(vs)])) for i in range(len(vs))}
            if e2 & used: continue
            used |= e2; Cs.append(vs); break
        else:
            return None
    rng.shuffle(Cs)
    return P, Cs

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); T = int(sys.argv[2])
    stats = {}
    for _ in range(T):
        inst = build(rng, rng.choice([7, 8, 9, 10]), rng.choice(['cross', 'twist']))
        if inst is None: continue
        tag, n = prove(*inst); assert n == 4
        stats[tag] = stats.get(tag, 0) + 1
    print(stats)
