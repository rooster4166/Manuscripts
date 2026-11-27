#!/usr/bin/env python3
"""A17: Lemma 3.1 (membership matrix), Lemma 4.1 (counting identity) and
Lemma 5.1 (standard profiles) of manuscripts/near-dirac/near-dirac.tex.

Lemma 3.1: r x q array, forbidden <= 0.03q per row and <= 0.03r per column,
integer row sums in [0.4q,0.6q], column sums in [0.4r,0.6r], equal totals.
We stress it with forbidden patterns at the limits (a dense block, a diagonal
band, random) and margins pushed to the extremes in correlated ways, and check
by max-flow that the margins are always met.

Lemma 4.1: for random graphs with a partition (m, m+rho) and D, b' := D - d_R,
b'(B) - b'(A) = 2(e(A) - e(B)) + rho D.

Lemma 5.1: for random graphs on shores (m, m+rho), the constructed profile b has
the degree parity, b(V) = 2m, |b(A)-b(B)| <= 2, and b(t) >= 1 (rho = 0).
"""
import random
import networkx as nx


def flow_ok(r, q, forb, rs, cs):
    F = nx.DiGraph()
    for i in range(r):
        F.add_edge('s', ('r', i), capacity=rs[i])
    for j in range(q):
        F.add_edge(('c', j), 't', capacity=cs[j])
    for i in range(r):
        for j in range(q):
            if (i, j) not in forb:
                F.add_edge(('r', i), ('c', j), capacity=1)
    val = nx.maximum_flow_value(F, 's', 't', flow_func=nx.algorithms.flow.preflow_push)
    return val == sum(rs)


def margins(n, tot, lo, hi, rnd, mode):
    """n integers in [ceil(lo), floor(hi)] summing to tot (None if impossible)."""
    import math
    a, b = math.ceil(lo), math.floor(hi)
    if not (n * a <= tot <= n * b):
        return None
    if mode == 'extreme':
        # as many at the top as possible, the rest at the bottom
        xs = [a] * n
        rest = tot - n * a
        idx = list(range(n))
        rnd.shuffle(idx)
        for i in idx:
            add = min(b - a, rest)
            xs[i] += add
            rest -= add
        return xs
    xs = [a] * n
    rest = tot - n * a
    while rest:
        i = rnd.randrange(n)
        if xs[i] < b:
            xs[i] += 1
            rest -= 1
    return xs


def forb_pattern(r, q, rnd, kind):
    import math
    fr, fc = math.floor(0.03 * q), math.floor(0.03 * r)
    forb = set()
    if kind == 'block':
        R0 = rnd.sample(range(r), fc)
        C0 = rnd.sample(range(q), fr)
        forb = {(i, j) for i in R0 for j in C0}
    elif kind == 'band':
        colc = [0] * q
        for i in range(r):
            for t in range(fr):
                j = (i * q // r + t) % q
                if colc[j] < fc:
                    forb.add((i, j))
                    colc[j] += 1
    else:
        rowc = [0] * r
        colc = [0] * q
        for _ in range(r * fr * 2):
            i, j = rnd.randrange(r), rnd.randrange(q)
            if (i, j) not in forb and rowc[i] < fr and colc[j] < fc:
                forb.add((i, j))
                rowc[i] += 1
                colc[j] += 1
    # sanity: limits
    rc = {}
    cc = {}
    for i, j in forb:
        rc[i] = rc.get(i, 0) + 1
        cc[j] = cc.get(j, 0) + 1
    assert max(rc.values(), default=0) <= 0.03 * q and max(cc.values(), default=0) <= 0.03 * r
    return forb


def test_matrix(rnd, trials=400):
    bad = 0
    done = 0
    for t in range(trials):
        r = rnd.choice([40, 67, 100, 150])
        q = rnd.choice([34, 50, 67, 100])
        kind = ['block', 'band', 'random'][t % 3]
        forb = forb_pattern(r, q, rnd, kind)
        # correlate: rows/cols hit by the forbidden block demand the most
        import math
        lo_tot = max(math.ceil(0.4 * q) * r, math.ceil(0.4 * r) * q)
        hi_tot = min(math.floor(0.6 * q) * r, math.floor(0.6 * r) * q)
        if lo_tot > hi_tot:
            continue
        tot = rnd.choice([lo_tot, hi_tot, rnd.randint(lo_tot, hi_tot)])
        mode = rnd.choice(['extreme', 'random'])
        rs = margins(r, tot, 0.4 * q, 0.6 * q, rnd, mode)
        cs = margins(q, tot, 0.4 * r, 0.6 * r, rnd, mode)
        if rs is None or cs is None:
            continue
        if kind == 'block' and mode == 'extreme':
            # put the largest row sums on rows with forbidden entries, same for columns
            frows = sorted({i for i, j in forb})
            fcols = sorted({j for i, j in forb})
            rs.sort(reverse=True)
            cs.sort(reverse=True)
            order_r = frows + [i for i in range(r) if i not in set(frows)]
            order_c = fcols + [j for j in range(q) if j not in set(fcols)]
            rs2 = [0] * r
            cs2 = [0] * q
            for k, i in enumerate(order_r):
                rs2[i] = rs[k]
            for k, j in enumerate(order_c):
                cs2[j] = cs[k]
            rs, cs = rs2, cs2
        done += 1
        if not flow_ok(r, q, forb, rs, cs):
            bad += 1
            print('Lemma 3.1 FAILURE', r, q, kind, mode)
    return done, bad


def rand_graph(n, p, rnd):
    return {(i, j) for i in range(n) for j in range(i + 1, n) if rnd.random() < p}


def test_identity(rnd, trials=2000):
    for _ in range(trials):
        m = rnd.randint(2, 12)
        rho = rnd.randint(0, 1)
        n = 2 * m + rho
        E = rand_graph(n, rnd.random(), rnd)
        A = set(range(m))
        D = rnd.randint(-5, 30)
        d = [0] * n
        for a, b in E:
            d[a] += 1
            d[b] += 1
        bp = [D - d[v] for v in range(n)]
        eA = sum(1 for a, b in E if a in A and b in A)
        eB = sum(1 for a, b in E if a not in A and b not in A)
        assert sum(bp[v] for v in range(n) if v not in A) - sum(bp[v] for v in A) == 2 * (eA - eB) + rho * D
    return trials


def profile(m, rho, d, t):
    """construction of Lemma 5.1 (rho=0: rooted at t)."""
    n = 2 * m + rho
    A = list(range(m))
    B = list(range(m, n))
    b = [1 if d[v] % 2 else 0 for v in range(n)]
    evA = [v for v in A if d[v] % 2 == 0]
    evB = [v for v in B if d[v] % 2 == 0]
    eA, eB = len(evA), len(evB)

    def dbl(lst, k, prefer=None):
        lst = lst[:]
        if prefer is not None and prefer in lst:
            lst.remove(prefer)
            lst = [prefer] + lst
        for v in lst[:k]:
            b[v] = 2

    if rho == 0:
        assert eA % 2 == eB % 2, 'parity claim e_A = e_B mod 2 fails'
        tp = t if d[t] % 2 == 0 else None
        if eA % 2 == 0:
            dbl(evA, eA // 2, tp)
            dbl(evB, eB // 2, tp)
        else:
            S, S2 = (evA, evB) if t < m else (evB, evA)
            dbl(S, (len(S) + 1) // 2, tp)
            dbl(S2, len(S2) // 2, tp)
    else:
        assert (eA + eB) % 2 == 1
        if eA % 2 == 0:
            dbl(evA, eA // 2)
            dbl(evB, (eB - 1) // 2)
        else:
            dbl(evA, (eA - 1) // 2)
            dbl(evB, eB // 2)
    return b


def test_profiles(rnd, trials=4000):
    for _ in range(trials):
        m = rnd.randint(1, 10)
        rho = rnd.randint(0, 1)
        n = 2 * m + rho
        E = rand_graph(n, rnd.random(), rnd)
        d = [0] * n
        for a, c in E:
            d[a] += 1
            d[c] += 1
        for t in range(n):
            b = profile(m, rho, d, t)
            assert all(b[v] % 2 == d[v] % 2 and 0 <= b[v] <= 2 for v in range(n))
            assert sum(b) == 2 * m
            bA = sum(b[:m])
            bB = sum(b[m:])
            assert abs(bA - bB) <= 2
            if rho == 0:
                assert b[t] >= 1
            if rho == 1:
                break
    return trials


if __name__ == '__main__':
    rnd = random.Random(17)
    done, bad = test_matrix(rnd)
    print(f'Lemma 3.1: {done} stressed instances (block/band/random forbidden sets at the limits,'
          f' extreme and random margins): {bad} failures')
    print(f'Lemma 4.1: identity holds on {test_identity(rnd)} random (graph, partition, D)')
    print(f'Lemma 5.1: profile construction valid on {test_profiles(rnd)} random graphs (every root t when rho=0)')
