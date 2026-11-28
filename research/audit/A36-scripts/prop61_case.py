"""prop61_case.py (A36): look for the case that the proof of Proposition 6.1 mis-handles: before any
token enters r, a legal suppression of a token p in A (p not adjacent to r in J) that is adjacent
to r at that moment (an earlier suppression added the edge rp).  The proof's split 'p in A /
otherwise p ~ r' then counts p as newly used up although it is already adjacent to r.
usage: prop61_case.py < J.g6   (d(z) = 6; stops at the first example)"""
import sys, itertools
import networkx as nx
sys.path.insert(0, __import__('os').path.dirname(__file__))
from thm42 import pms

def moves(K, pairs, r):
    tok = {v for v in K if K[v] and len(K[v]) % 2 == 0}
    live = [i for i, (y, x) in enumerate(pairs) if ('L', i) in K[y]]
    X = set()
    for i in live: X |= {('L', i), pairs[i][1]}
    leaves = {('L', i) for i in range(len(pairs))}
    for p in tok:
        for u in K[p]:
            if u == r or len(K[u]) % 2 == 0 or u in X: continue      # no entry into r
            if (K[u] - {p}) & (tok - {p}): continue
            yield ('M', p, u)
        if len(K[p]) == 2:
            a, b = sorted(K[p], key=str)
            if b in K[a] or a in leaves or b in leaves: continue
            if any({a, b} == {pairs[i][0], pairs[i][1]} for i in live): continue
            yield ('S', p, a, b)
    for i in live:
        if len(K[pairs[i][0]]) % 2 == 1: yield ('D', i)

def apply(K, m, pairs):
    K = {v: set(s) for v, s in K.items()}
    if m[0] == 'M': K[m[1]].discard(m[2]); K[m[2]].discard(m[1])
    elif m[0] == 'D':
        y = pairs[m[1]][0]; K[y].discard(('L', m[1])); K[('L', m[1])].discard(y)
    else:
        _, p, a, b = m
        K[p] = set(); K[a].discard(p); K[b].discard(p); K[a].add(b); K[b].add(a)
    return K

for line in sys.stdin:
    J = nx.from_graph6_bytes(line.split()[0].encode())
    z = [v for v in J if J.degree(v) % 2 == 0][0]
    U = sorted(J[z])
    for r in U:
        A = {v for v in J if v != r and not J.has_edge(r, v)}
        for w in U:
            if w == r: continue
            for pm in pms([u for u in U if u not in (r, w)], J):
                for o in itertools.product((0, 1), repeat=2):
                    pairs = [(a, b) if oi else (b, a) for (a, b), oi in zip(pm, o)]
                    K = {v: set(J[v]) for v in J}
                    for (a, b) in [(z, w)] + [e for (y, x) in pairs for e in ((z, y), (z, x), (y, x))]:
                        K[a].discard(b); K[b].discard(a)
                    for i, (y, x) in enumerate(pairs): K[('L', i)] = {y}; K[y].add(('L', i))
                    stack = [(K, [])]; seen = set()
                    while stack:
                        K, hist = stack.pop()
                        key = frozenset((str(v), str(u)) for v in K for u in K[v])
                        if key in seen: continue
                        seen.add(key)
                        for m in moves(K, pairs, r):
                            if m[0] == 'S' and m[1] in A and r in (m[2], m[3]):
                                print('EXAMPLE', line.split()[0], 'z', z, 'r', r, 'w', w, 'pairs(y,x)', pairs,
                                      'A', sorted(A), 'history', hist, 'then', m)
                                sys.exit(0)
                            stack.append((apply(K, m, pairs), hist + [m]))
print('no example')
