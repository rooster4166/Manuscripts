import random, sys
from common import *
def rand_cycle(rng, w, pool, used, maxlen):
    for _ in range(200):
        L = rng.randint(3, maxlen)
        vs = rng.sample([v for v in pool if v != w], L - 1)
        cyc = [w] + vs
        E = [frozenset((cyc[i], cyc[(i + 1) % L])) for i in range(L)]
        if any(e in used for e in E): continue
        return cyc, E
    return None, None
def trial(rng, kind):
    w = 0
    if kind == 'five':      # P on 6 vertices, w third or fourth
        pos = rng.choice([2, 3]); nP = 6; ncyc = 2
    elif kind == 'four':    # P on 5 vertices, w internal
        pos = rng.choice([1, 2, 3]); nP = 5; ncyc = 2
    else:                   # short path (t', t, w, e), j cycles
        pos = 2; nP = 4; ncyc = rng.choice([1, 2])
    others = list(range(1, nP))
    rng.shuffle(others)
    P = others[:pos] + [w] + others[pos:]
    extra = rng.randint(0, 6)
    pool = list(range(nP + extra))
    used = set(frozenset((P[i], P[i + 1])) for i in range(nP - 1))
    cycles = []
    for _ in range(ncyc):
        # bias towards P vertices
        sub = pool if rng.random() < 0.5 else list(range(nP)) + list(range(nP, nP + min(extra, 2)))
        cyc, E = rand_cycle(rng, w, sub, used, min(len(sub), 9))
        if cyc is None: return None
        used |= set(E); cycles.append(cyc)
    if kind == 'five':
        nbrs = [c[1] for c in cycles] + [c[-1] for c in cycles]
        if sum(1 for x in nbrs if x not in P) < 2: return None
    G = nx.Graph([tuple(e) for e in used])
    target = ncyc + 1
    res = solve(G, budget=target, workers=1, time_limit=60)
    if res.status == 'UNKNOWN':
        res = solve(G, budget=target, workers=2, time_limit=900)
    ok = res.status in ('OPTIMAL', 'FEASIBLE')
    if res.status == 'UNKNOWN': ok = 'timeout'
    return ok, P, cycles
if __name__ == '__main__':
    kind = sys.argv[1]; N = int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
    done = bad = 0
    while done < N:
        r = trial(rng, kind)
        if r is None: continue
        done += 1
        if r[0] is not True:
            bad += 1; print('FAIL', kind, 'P=', r[1], 'cycles=', r[2], flush=True)
    print(kind, 'tested', N, 'failures', bad, flush=True)
