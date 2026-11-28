"""A41: order-10 set counts of nodata Section 5.1 (no solving): one 2-chain, one 3-chain, one star,
and the number of star sets violating (H1) (which fail by Lemma 5.5).  Own graph6 reader.
usage: python3 -I count10.py < odd10.g6   (connected graphs with every degree odd)"""
import sys
from itertools import combinations


def g6adj(s):
    n = ord(s[0]) - 63
    A = [set() for _ in range(n)]
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        bits += [(v >> (5 - i)) & 1 for i in range(6)]
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                A[i].add(j)
                A[j].add(i)
            k += 1
    return n, A


def h1_ok(n, A, u, X):
    rest = set(range(n)) - {u}
    while rest:
        v = rest.pop()
        c = {v}
        fr = [v]
        while fr:
            x = fr.pop()
            for y in A[x]:
                if y in rest:
                    rest.discard(y)
                    c.add(y)
                    fr.append(y)
        k = len(set(X) & c)
        e = len(A[u] & c)
        if 2 * k > len(c) - e:
            return False
    return True


k2 = c3 = st = stbad = graphs = 0
for line in sys.stdin:
    s = line.strip()
    if not s:
        continue
    n, A = g6adj(s)
    graphs += 1
    na = [[u != v and v not in A[u] for v in range(n)] for u in range(n)]
    for x in range(n):
        nn = [v for v in range(n) if na[x][v]]
        k2 += len(nn) * (len(nn) - 1)                       # a <- x <- b, a != b
    for a in range(n):
        for x in range(n):
            if not na[a][x]:
                continue
            for y in range(n):
                if y in (a, x) or not na[x][y]:
                    continue
                for b in range(n):
                    if b in (a, x, y) or not na[y][b]:
                        continue
                    c3 += 1                                  # a <- x <- y <- b
    for u in range(n):
        nn = [v for v in range(n) if na[u][v]]
        for x, y in combinations(nn, 2):
            st += 1
            if not h1_ok(n, A, u, [x, y]):
                stbad += 1
print(f"graphs {graphs}: one 2-chain {k2} sets; one 3-chain {c3}; one star {st}, of which {stbad} violate (H1)")
