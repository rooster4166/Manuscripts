import sys, itertools, random
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import indep_cuts as ic
def first_fail(m, n, cls, c, delta):
    kap = [2 if i == c else 4 for i in range(n)]
    C = [ic.comps(m, cls[i]) for i in range(n)]
    fails = []
    for bm in range(1 << m):
        B = {v for v in range(m) if bm >> v & 1}
        up = low = 0
        for i in range(n):
            N = 0; two = False
            for comp in C[i]:
                sl = 2*(comp[0] in B) if len(comp) == 1 else (comp[0] in B) + (comp[1] in B)
                if sl >= 1: N += 1
                if sl == 2: two = True
            psi = N + (1 if (two and i != c) else 0)
            up += min(kap[i], psi); low += max(0, delta[i] - psi)
        if 2*len(B) > up: fails.append(('UH', len(B)))
        if low > 2*(m - len(B)): fails.append(('LH', len(B)))
    return fails
rng = random.Random(11); stats = {}
for tr in range(60):
    n = rng.randint(2, 4); m = rng.randint(1, 4)
    if m > 2*n - 1: continue
    cls = ic.random_decomp(m, n, rng); c = rng.randrange(n)
    for delta in itertools.product(*[range(3) if i == c else range(5) for i in range(n)]):
        f = first_fail(m, n, cls, c, delta)
        if not f: continue
        key = 'only B nonempty' if all(b > 0 for _, b in f) else 'B=empty among failures'
        stats[key] = stats.get(key, 0) + 1
        for t, b in f: stats[(t, 'b>0' if b else 'b=0')] = stats.get((t, 'b>0' if b else 'b=0'), 0) + 1
print(stats)
