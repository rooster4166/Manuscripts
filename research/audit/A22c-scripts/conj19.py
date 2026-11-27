"""Audit A22c: Conjecture 8.5 on an exhaustive family at the least possible order.
Far-apart N(z) with every neighbour of degree 3 needs 6 + 12 + 1 = 19 vertices; at order 19 with all
twelve private vertices of degree 3, J = z + v_1..v_6 + private pairs {a_i, b_i} + a 2-regular graph
R on the twelve private vertices.  We take every 2-regular R up to isomorphism (cycle types), every
pairing of its vertices into the six private pairs, keep J 3-connected, dedupe J with nauty-labelg,
and check the conjecture (relaxed = as stated, strict = Lean AdmChain) exactly for each J.
usage: conj19.py [start step]"""
import sys, itertools, subprocess
from far_check import three_conn
from conj_check import coverage, far
from count_J import g6_encode


def partitions(n, m=3):
    if n == 0:
        yield []
        return
    for k in range(m, n + 1):
        for p in partitions(n - k, k):
            yield [k] + p


def pairings(xs):
    if not xs:
        yield []
        return
    for i in range(1, len(xs)):
        for p in pairings(xs[1:i] + xs[i + 1:]):
            yield [(xs[0], xs[i])] + p


def main():
    nums = [int(a) for a in sys.argv[1:] if a.isdigit()]
    start, step = (nums[0], nums[1]) if nums else (0, 1)
    lines = []
    for part in partitions(12):
        R = []
        base = 0
        for k in part:
            for j in range(k):
                R.append((base + j, base + (j + 1) % k))
            base += k
        for P in pairings(list(range(12))):
            n = 19
            adj = [set() for _ in range(n)]
            def add(u, w):
                adj[u].add(w); adj[w].add(u)
            for i, (a, b) in enumerate(P):
                v = 1 + i
                add(0, v); add(v, 7 + a); add(v, 7 + b)
            for a, b in R:
                add(7 + a, 7 + b)
            if any(len(adj[v]) % 2 == 0 for v in range(1, n)):
                continue
            if not three_conn(n, adj):
                continue
            A = [[1 if w in adj[u] else 0 for w in range(n)] for u in range(n)]
            lines.append(g6_encode(n, A))
    p = subprocess.run(['nauty-labelg', '-q'], input='\n'.join(lines) + '\n', capture_output=True, text=True, check=True)
    canon = sorted(set(l for l in p.stdout.split('\n') if l.strip()))
    print(f'order-19 family: {len(lines)} labelled 3-connected J, {len(canon)} up to isomorphism', flush=True)
    open('conj19_canon.txt', 'w').write('\n'.join(canon) + '\n')
    if 'dump' in sys.argv:
        return
    from count_J import g6_decode
    bad = {False: 0, True: 0}; not_y1 = {False: 0, True: 0}; checked = 0
    for idx in range(start, len(canon), step):
        n, A = g6_decode(canon[idx])
        adj = [set(w for w in range(n) if A[u][w]) for u in range(n)]
        z = [v for v in range(n) if len(adj[v]) == 6][0]
        if z != 0:   # relabel z to 0
            perm = [z] + [v for v in range(n) if v != z]
            inv = {v: i for i, v in enumerate(perm)}
            adj = [set(inv[w] for w in adj[perm[i]]) for i in range(n)]
        assert far(adj)
        checked += 1
        for strict in (False, True):
            cov, y1 = coverage(adj, strict)
            if len(cov) < 6:
                bad[strict] += 1
                print('UNCOVERED', 'strict' if strict else 'relaxed', canon[idx], 'missing', sorted(set(adj[0]) - cov), flush=True)
            elif len(y1) < 6:
                not_y1[strict] += 1
    print(f'checked {checked}: relaxed uncovered {bad[False]} (some r only as y2/y3: {not_y1[False]}); '
          f'strict uncovered {bad[True]} (some r only as y2/y3: {not_y1[True]})', flush=True)


if __name__ == '__main__':
    main()
