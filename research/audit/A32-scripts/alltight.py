"""alltight.py (auditor, conj-n audit): count the instances of Conjecture N that are all-tight
(every neighbour of g other than x is y or a neighbour of y), and compare with the STUCK lines of
`closure2 N1 -b 0 -p 1000000` (file given as argv[2]).
usage: python3 -I alltight.py one_even_9.g6 closure2_N1_output.txt"""
import sys, re, collections

def g6(s):
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        bits += [(v >> k) & 1 for k in range(5, -1, -1)]
    A = {i: set() for i in range(n)}
    p = 0
    for j in range(1, n):
        for i in range(j):
            if bits[p]:
                A[i].add(j); A[j].add(i)
            p += 1
    return n, A

stuck = set()
for l in open(sys.argv[2]):
    if l.startswith('STUCK'):
        f = l.split()
        g6s = f[1]
        m = re.search(r' c=(\d+) A=\{(\d+)\}', l)
        stuck.add((g6s, int(m.group(1)), int(m.group(2))))
tot = at = at_stuck = notat_stuck = 0
feat = collections.Counter()
for line in open(sys.argv[1]):
    s = line.strip()
    if not s: continue
    n, A = g6(s)
    ev = [v for v in range(n) if len(A[v]) > 0 and len(A[v]) % 2 == 0]
    if len(ev) != 1: continue
    g = ev[0]
    for y in range(n):
        if len(A[y]) % 2 == 0: continue
        for x in range(n):
            if x == y or len(A[x]) % 2 == 0 or x in A[y]: continue
            W = A[y] - A[x] - {g}
            if not W: continue
            tot += 1
            alltight = all(u == y or u in A[y] for u in A[g] - {x})
            st = (s, y, x) in stuck
            if alltight:
                at += 1; at_stuck += st
                if not st: feat[('dg=%d' % len(A[g]), 'Ng=' + ('{x,w}' if A[g] - {x} <= W and len(A[g]) == 2 and x in A[g] else 'other'))] += 1
            else:
                notat_stuck += st
print('instances', tot, 'all-tight', at, 'all-tight stuck', at_stuck, 'all-tight not stuck', at - at_stuck,
      'stuck but not all-tight', notat_stuck)
for k, v in sorted(feat.items()): print('  not stuck, all-tight:', v, k)
