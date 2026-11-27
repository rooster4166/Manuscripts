import sys
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
    return A
for line in sys.stdin:
    f = line.split()
    if not f or f[0] != 'UNCERT': continue
    G = g6(f[1]); kv = dict(t.split('=') for t in f[2:])
    g, y, x = int(kv['g']), int(kv['y']), int(kv['x'])
    deg = {v: len(G[v]) for v in G}
    print(f[1], 'g=%d y=%d x=%d' % (g, y, x), 'm=%d' % (sum(deg.values())//2),
          'N(g)=%s N(y)=%s N(x)=%s' % (sorted(G[g]), sorted(G[y]), sorted(G[x])),
          'x~g=%d y~g=%d dg=%d' % (x in G[g], y in G[g], deg[g]),
          'degs=' + ''.join(str(deg[v]) for v in range(len(G))))
