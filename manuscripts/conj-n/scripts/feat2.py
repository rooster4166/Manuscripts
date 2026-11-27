import re, sys, collections
L = open(sys.argv[1]).read().splitlines()
cnt = collections.Counter(); ex = {}
i = 0
pat = re.compile(r'N=(\d+) g=(-?\d+) c=(\d+) A=\{([\d,]*)\} B=\{([\d,]*)\} degs=(\d+) E: (.*?) +good=(\d)')
while i < len(L):
    if L[i].startswith('STUCK'):
        m = pat.search(L[i])
        n, g, c, A, B, degs, E, gd = m.groups()
        g, c = int(g), int(c); A = set(map(int, A.split(','))) if A else set()
        adj = collections.defaultdict(set)
        for e in E.split():
            u, v = map(int, e.split('-')); adj[u].add(v); adj[v].add(u)
        ch = []; i += 1
        while i < len(L) and L[i].startswith('    --'):
            ch.append((L[i][6], int(L[i].rsplit('good=', 1)[1]))); i += 1
        gm = {m for m, gg in ch if gg}
        feat = ('dg=%d' % (len(adj[g]) if g >= 0 else -1), 'ginA' if g in A else '-', 'c~g' if c in adj[g] else '-',
                '|A|=%d' % len(A), 'AmeetsNg' if adj[g] & A else '-', 'good=' + gd, 'goodch=' + ''.join(sorted(gm)))
        cnt[feat] += 1; ex.setdefault(feat, L[i - len(ch) - 1])
    else: i += 1
for k, v in sorted(cnt.items(), key=lambda t: -t[1]): print(v, ' '.join(k), '\n     ', ex[k][:220])
