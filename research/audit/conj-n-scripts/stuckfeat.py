"""stuckfeat.py (auditor, conj-n audit): features of STUCK / FALSE lines of closure2 output (run
with -g to get child goodness).  Prints, over the selected lines: count, g in A, every witness
adjacent to g, g on a triangle (N(g) contains an edge), d(g)=2, some good child (needs -g).
usage: python3 -I stuckfeat.py [STUCK|FALSE] < closure2_output"""
import sys, re, collections
kind = sys.argv[1] if len(sys.argv) > 1 else 'STUCK'
pat = re.compile(r'N=(\d+) g=(-?\d+) c=(\d+) A=\{([\d,]*)\} B=\{([\d,]*)\} degs=(\d+) E: (.*?)( +good=\d| +oracle=-?\d)?$')
L = sys.stdin.read().splitlines()
cnt = collections.Counter(); graphs = collections.Counter(); ex = []
i = 0
while i < len(L):
    l = L[i]
    if not l.startswith(kind):
        i += 1; continue
    m = pat.search(l.rstrip())
    n, g, c, A, B, degs, E, _ = m.groups()
    g, c = int(g), int(c)
    A = set(map(int, A.split(','))) if A else set()
    B = set(map(int, B.split(','))) if B else set()
    adj = collections.defaultdict(set); ne = 0
    for e in E.split():
        u, v = map(int, e.split('-')); adj[u].add(v); adj[v].add(u); ne += 1
    W = [w for w in adj[c] if w != g and w not in A and w not in B and not ((adj[w] & A) - {g})]
    goodch = False; j = i + 1
    while j < len(L) and L[j].startswith('    --'):
        if L[j].rstrip().endswith('good=1'): goodch = True
        j += 1
    cnt['total'] += 1
    if g >= 0 and g in A: cnt['g in A'] += 1
    if g >= 0 and W and all(w in adj[g] for w in W): cnt['every witness ~ g'] += 1
    if g >= 0 and any(adj[a] & adj[g] for a in adj[g]): cnt['g on a triangle'] += 1
    if g >= 0 and len(adj[g]) == 2: cnt['d(g)=2'] += 1
    if goodch: cnt['has a good child'] += 1
    if l.rstrip().endswith('good=1'): cnt['good'] += 1
    graphs[(l.split()[1], ne)] += 1
    ex.append((ne, l[:160]))
    i = j
for k, v in sorted(cnt.items()): print(v, k)
ex.sort()
print('fewest edges:', ex[0] if ex else None)
print('distinct graphs:', len(graphs), 'min edges:', min((e for (_, e) in graphs), default=None))
