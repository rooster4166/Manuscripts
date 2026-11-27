import re, sys, collections
pat = re.compile(r'N=(\d+) g=(-?\d+) c=(\d+) A=\{([\d,]*)\} B=\{([\d,]*)\} degs=(\d+) E: (.*?)( +good=\d)?$')
cnt = collections.Counter()
for l in sys.stdin:
    if not l.startswith('STUCK'): continue
    m = pat.search(l.rstrip()); n, g, c, A, B, degs, E, _ = m.groups(); g = int(g); c = int(c); x = int(A)
    adj = collections.defaultdict(set)
    for e in E.split():
        u, v = map(int, e.split('-')); adj[u].add(v); adj[v].add(u)
    T = adj[g] - {x, c}
    nontight = [u for u in T if u not in adj[c]]
    W = adj[c] - adj[x] - {g}
    twit = [u for u in T if (adj[c] - adj[x] - {u})]
    cnt[('y~g' if c in adj[g] else 'y!~g', 'x~g' if x in adj[g] else 'x!~g', 'nontight=%d' % len(nontight), 'tight-with-witness=%d' % (len(twit) > 0), 'dg=%d' % len(adj[g]))] += 1
for k, v in sorted(cnt.items()): print(v, k)
print('total', sum(cnt.values()))
