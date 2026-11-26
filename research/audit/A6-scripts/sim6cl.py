import itertools
# vertices: clique 0..5, reps 6+i omits i
R = lambda i: 6 + i
present = set()
def add(a, b):
    e = frozenset((a, b)); assert e not in present, (a, b); present.add(e)
for e in [(2, 3), (4, 5)]: add(*e)
spokes = {0: [1, 2, 3, 4, 5], 1: [0, 2, 3, 4, 5], 2: [1, 4, 5], 3: [1, 4, 5], 5: [1, 2, 3], 4: [0, 2, 3]}
for i, L in spokes.items():
    for u in L: add(R(i), u)
assert len(present) == 24
paths = [(2, 11, 1, 9, 4, 8, 5, 6, 3, 10, 0, 7), (8, 1, 6, 4, 5, 7, 3, 2, 10), (4, 7, 2, 6), (3, 11), (5, 9)]
used = []
for P in paths:
    assert len(set(P)) == len(P)
    for a, b in zip(P, P[1:]): used.append(frozenset((a, b)))
assert len(used) == len(set(used)) == 24 and set(used) == present, 'display mismatch'
b = {v: 0 for v in range(12)}
for P in paths: b[P[0]] += 1; b[P[-1]] += 1
print('initial ends', b)
# include all possible rep-rep edges as potential neighbours (worst case)
def blanks(v):
    nb = [u for u in range(12) if frozenset((u, v)) in present]
    if v >= 6: nb += [u for u in range(6, 12) if u != v and u not in nb]
    return sum(1 for u in nb if b[u] == 0)
def T(d, r):
    if isinstance(d, str): d = R(int(d[0]))
    if isinstance(r, str): r = R(int(r[0]))
    assert frozenset((d, r)) not in present, ('edge present', d, r)
    sup, bl = b[d], blanks(r)
    assert sup > bl, ('inequality fails', d, r, sup, bl)
    add(d, r); b[d] -= 1; b[r] += 1
    return (sup, bl)
seq1 = [(2, 0), (3, 1)]
seq2 = [(0, "2'"), ("2'", 3), (4, 1), (1, 0), ("3'", 2), (3, 0), (0, "3'"), (5, 3)]
seq3 = [("5'", 0), (0, 4), (4, "5'"), (1, "4'"), ("4'", 5), (5, 2)]
def nocommon(bl):
    N = {x: {y for y in range(6) if frozenset((x, y)) in present} for x in bl}
    return not (N[bl[0]] & N[bl[1]])
print('D0 blanks 0,1 no common nbr:', nocommon((0, 1)))
print('stage1', [T(*x) for x in seq1]); print('D1 blanks 2,3 no common:', nocommon((2, 3)), {v: b[v] for v in range(6)})
print('stage2', [T(*x) for x in seq2]); print('D2 blanks 4,5 no common:', nocommon((4, 5)), {v: b[v] for v in range(12)})
print('stage3', [T(*x) for x in seq3])
rest = [frozenset((x, y)) for x, y in itertools.combinations(range(6), 2) if frozenset((x, y)) not in present]
print('unused clique edges', sorted(tuple(sorted(e)) for e in rest))
final = (0, 5, 1, 2, 4, 3)
assert set(frozenset(e) for e in zip(final, final[1:])) == set(rest)
b[0] += 1; b[3] += 1
print('final ends', b)
allsp = all(frozenset((R(i), u)) in present for i in range(6) for u in range(6) if u != i)
print('all 30 spokes present:', allsp, 'total edges', len(present) + 5)
