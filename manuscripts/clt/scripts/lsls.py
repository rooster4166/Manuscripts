"""lsls.py: local search for constrained Lovász decompositions in dense graphs (session claude/clt).

The exact DFS (lsearch.c) decides small or sparse instances but stalls on dense ones (thousands of
edges' worth of choices even when the constraints are easy).  This heuristic only ever answers
'found' (with a checked witness) or 'not found'; it never claims non-existence.

Move: choose k paths of the current decomposition, at least one of them violating a constraint
(when there is one), delete them, and re-decompose the union H of their edges exactly (lsearch on
H) into k paths with the same multiset of end vertices, imposing every constraint whose end
vertex lies in H's end set.  If that sub-instance is infeasible, re-decompose H with no
constraints (a random step, seed varied) with probability p_walk.  Repeat.
"""
import random
from clt_lib import solve_many, check


def endpath_violations(paths, sysd):
    endp = {}
    for i, P in enumerate(paths):
        endp.setdefault(P[0], []).append(i)
        endp.setdefault(P[-1], []).append(i)
    bad = set()
    for v, S in sysd.get('ef', {}).items():
        for i in endp.get(v, []):
            if set(paths[i]) & set(S):
                bad.add(i)
    for u, v in sysd.get('ep', []):
        for i in endp.get(u, []):
            if i in endp.get(v, []):
                bad.add(i)
    for p, q, S in sysd.get('es', []):
        for i, P in enumerate(paths):
            for j in range(len(P) - 1):
                if (P[j], P[j + 1]) == (p, q) and P[0] in S:
                    bad.add(i)
                if (P[j], P[j + 1]) == (q, p) and P[-1] in S:
                    bad.add(i)
    for a, c in sysd.get('sep', []):
        for i, P in enumerate(paths):
            if a in P and c in P:
                bad.add(i)
    return bad


def restrict(sysd, ends, vset):
    """constraints that can be imposed on a sub-instance whose paths have end set `ends`."""
    out = {}
    ef = {v: set(S) & vset for v, S in sysd.get('ef', {}).items() if v in ends}
    out['ef'] = {v: S for v, S in ef.items() if S}
    out['ep'] = [(u, v) for u, v in sysd.get('ep', []) if u in ends and v in ends]
    out['es'] = [(p, q, set(S)) for p, q, S in sysd.get('es', []) if p in vset and q in vset]
    out['sep'] = [(a, c) for a, c in sysd.get('sep', []) if a in vset and c in vset]
    return out


def search(n, adj, sysd, steps=3000, k=3, seed=0, p_walk=0.7, budget=20000):
    rng = random.Random(seed)
    st, paths = solve_many([(n, adj, {})], budget=0, seed=seed + 1)[0]
    if st != 'OK':
        return None
    for step in range(steps):
        bad = endpath_violations(paths, sysd)
        if not bad:
            assert check(n, adj, paths, sysd)
            return paths
        first = rng.choice(sorted(bad))
        others = [i for i in range(len(paths)) if i != first]
        pick = [first] + rng.sample(others, min(k - 1, len(others)))
        sub = [paths[i] for i in pick]
        vs = sorted({v for P in sub for v in P})
        idx = {v: j for j, v in enumerate(vs)}
        hadj = [set() for _ in vs]
        for P in sub:
            for a, b in zip(P, P[1:]):
                hadj[idx[a]].add(idx[b])
                hadj[idx[b]].add(idx[a])
        bprof = [0] * len(vs)
        for P in sub:
            bprof[idx[P[0]]] += 1
            bprof[idx[P[-1]]] += 1
        ends = {P[0] for P in sub} | {P[-1] for P in sub}
        rs = restrict(sysd, ends, set(vs))
        rs_loc = {'ef': {idx[v]: {idx[s] for s in S} for v, S in rs['ef'].items()},
                  'ep': [(idx[u], idx[v]) for u, v in rs['ep']],
                  'es': [(idx[p], idx[q], {idx[s] for s in S if s in idx}) for p, q, S in rs['es']],
                  'sep': [(idx[a], idx[c]) for a, c in rs['sep']]}
        from clt_lib import block, LSEARCH
        import subprocess
        def run(sd, sseed):
            inp = block(len(vs), hadj, sd, seed=sseed, budget=budget, b=bprof)
            out = subprocess.run([LSEARCH], input=inp, capture_output=True, text=True).stdout.split('\n')
            if out[0].startswith('OK'):
                kk = int(out[0].split()[1])
                return [[vs[x] for x in map(int, out[1 + j].split())] for j in range(kk)]
            return None
        new = run(rs_loc, rng.randrange(1, 10 ** 6))
        if new is None and rng.random() < p_walk:
            new = run({}, rng.randrange(1, 10 ** 6))
        if new is not None and len(new) == len(sub):
            paths = [P for i, P in enumerate(paths) if i not in pick] + new
    return None
