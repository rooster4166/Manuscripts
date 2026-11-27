"""n1stuck.py: classify the STUCK lines of `closure2 N1 -b 0 -p 1000000` (stdin) by the position of
the targets, and, if a graph6 list is given, count the all-tight instances of N in it (every
neighbour of g other than x is y or a neighbour of y) and check that every stuck instance is all-tight.
usage: closure2 N1 -b 0 -p 1000000 < G.g6 | python3 n1stuck.py [G.g6]"""
import re, sys, collections
pat = re.compile(r'N=(\d+) g=(-?\d+) c=(\d+) A=\{([\d,]*)\} B=\{([\d,]*)\} degs=(\d+) E: (.*?)( +good=\d)?$')
cnt = collections.Counter(); stuck = set()
for l in sys.stdin:
    if not l.startswith('STUCK'): continue
    m = pat.search(l.rstrip()); n, g, c, A, B, degs, E, _ = m.groups(); g = int(g); c = int(c); x = int(A)
    stuck.add((l.split()[1], c, x))
    adj = collections.defaultdict(set)
    for e in E.split():
        u, v = map(int, e.split('-')); adj[u].add(v); adj[v].add(u)
    T = adj[g] - {x, c}
    nontight = [u for u in T if u not in adj[c]]
    twit = [u for u in T if (adj[c] - adj[x] - {u})]
    cnt[('y~g' if c in adj[g] else 'y!~g', 'x~g' if x in adj[g] else 'x!~g', 'nontight=%d' % len(nontight), 'tight-with-witness=%d' % (len(twit) > 0), 'dg=%d' % len(adj[g]))] += 1
for k, v in sorted(cnt.items()): print(v, k)
print('stuck', sum(cnt.values()))

def g6(s):
    n = ord(s[0]) - 63; bits = []
    for ch in s[1:]:
        v = ord(ch) - 63; bits += [(v >> k) & 1 for k in range(5, -1, -1)]
    A = {i: set() for i in range(n)}; p = 0
    for j in range(1, n):
        for i in range(j):
            if bits[p]: A[i].add(j); A[j].add(i)
            p += 1
    return n, A
if len(sys.argv) > 1:
    tot = at = at_stuck = 0; stuck_not_at = 0
    for s in open(sys.argv[1]).read().split():
        n, A = g6(s)
        ev = [v for v in range(n) if A[v] and len(A[v]) % 2 == 0]
        if len(ev) != 1: continue
        g = ev[0]
        for y in range(n):
            if len(A[y]) % 2 == 0: continue
            for x in range(n):
                if x == y or len(A[x]) % 2 == 0 or x in A[y]: continue
                if not (A[y] - A[x] - {g}): continue
                tot += 1
                alltight = all(u == y or u in A[y] for u in A[g] - {x})
                at += alltight
                st = (s, y, x) in stuck
                at_stuck += alltight and st; stuck_not_at += st and not alltight
    print('instances %d all-tight %d stuck-and-all-tight %d stuck-not-all-tight %d' % (tot, at, at_stuck, stuck_not_at))
