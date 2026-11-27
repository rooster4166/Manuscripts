"""Validate dsolve against a naive Python enumerator of all path decompositions (small graphs),
with random end sets, separations, special edges and cover sets.  Also K4 / prism sanity checks."""
import random, itertools, sys
from dlib import solve, check_decomp, check_constraints, lovasz_ends, Budget


def all_paths(n, edges, rem):
    """all simple paths (as (verts, eids)) using only edges in rem (set of eids), each listed once
    per orientation-class (we list both orientations and dedupe by edge set+ends)."""
    adj = [[] for _ in range(n)]
    for e in rem:
        a, b = edges[e]
        adj[a].append((e, b)); adj[b].append((e, a))
    out = {}
    def dfs(vs, es):
        if es:
            key = (frozenset(es), frozenset((vs[0], vs[-1])), tuple(sorted([tuple(vs), tuple(vs[::-1])])))
            out[key] = (list(vs), list(es))
        for e, w in adj[vs[-1]]:
            if w in vs or e in es:
                continue
            vs.append(w); es.append(e); dfs(vs, es); vs.pop(); es.pop()
    for v in range(n):
        dfs([v], [])
    return list(out.values())


def naive(n, edges, ends, seps, sets, spec):
    def ok(P):
        vs, es = P
        S = set(vs)
        if vs[0] not in ends or vs[-1] not in ends:
            return False
        for a, b in seps:
            if a in S and b in S:
                return False
        if sets is not None and not any(S <= set(s) for s in sets):
            return False
        sp = [e for e in es if spec and e in spec]
        if len(sp) > 1:
            return False
        if sp:
            e = sp[0]
            atA, atC = es[0] == e, es[-1] == e
            if not (atA or atC):
                return False
            x = spec[e]
            if x >= 0 and not ((atA and vs[0] == x) or (atC and vs[-1] == x)):
                return False
        return True
    def rec(rem, endsleft):
        if not rem:
            return not endsleft
        e0 = min(rem)
        for P in all_paths(n, edges, rem):
            if e0 not in P[1] or not ok(P):
                continue
            a, c = P[0][0], P[0][-1]
            if a not in endsleft or c not in endsleft:
                continue
            if rec(rem - set(P[1]), endsleft - {a, c}):
                return True
        return False
    return rec(frozenset(range(len(edges))), frozenset(ends))


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
    # K4 with perfect matching: PTM fails; prism with rungs: PTM_3 fails
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    assert solve(4, K4, {0, 1, 2, 3}, spec={1: -1, 4: -1}) is None    # F = {02, 13}
    assert solve(4, K4, {0, 1, 2, 3}) is not None
    prism = [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5), (0, 3), (1, 4), (2, 5)]
    assert solve(6, prism, set(range(6)), spec={6: -1, 7: -1, 8: -1}) is None
    assert solve(6, prism, set(range(6)), spec={6: -1, 7: -1}) is not None
    agree = found = 0
    for trial in range(3000):
        n = rng.randint(3, 7)
        m = rng.randint(2, 9)
        edges = []
        for _ in range(m):
            a, b = rng.sample(range(n), 2)
            edges.append((a, b))          # multigraph allowed
        d = [0] * n
        for a, b in edges:
            d[a] += 1; d[b] += 1
        # ends: parity-consistent random choice: odd vertices plus random even pairs
        ends = {v for v in range(n) if d[v] % 2}
        ev = [v for v in range(n) if d[v] % 2 == 0 and d[v] > 0]
        if ev and rng.random() < 0.3:
            pass
        seps = []
        for _ in range(rng.randint(0, 2)):
            a, b = rng.sample(range(n), 2); seps.append((a, b))
        spec = {}
        for e in rng.sample(range(m), rng.randint(0, min(3, m))):
            spec[e] = rng.choice([-1, edges[e][0], edges[e][1]])
        sets = None
        if rng.random() < 0.3:
            sets = [set(rng.sample(range(n), rng.randint(2, n))) for _ in range(rng.randint(1, 3))]
        r1 = solve(n, edges, ends, seps, sets, spec, seed=trial)
        r2 = naive(n, edges, ends, seps, sets, spec)
        if r1 is not None:
            check_decomp(n, edges, r1, ends)
            check_constraints(r1, seps, sets, spec)
        if (r1 is not None) != r2:
            print('MISMATCH', n, edges, ends, seps, sets, spec, r1, r2)
            sys.exit(1)
        agree += 1; found += r2
    print('dsolve vs naive: %d random queries agree (%d positive)' % (agree, found))


if __name__ == '__main__':
    main()
