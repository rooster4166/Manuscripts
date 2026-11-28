"""allodd_xcheck.py: cross-check allodd_dl -A FAIL lines for fixed families (X2, X3) against route_ext query A.
usage: python3 allodd_xcheck.py X2|X3 graphs.g6 allodd_dl_output (run from a directory with ./route_ext)"""
import itertools, subprocess, sys
import networkx as nx
fam, g6file, failfile = sys.argv[1], sys.argv[2], sys.argv[3]
k = {'X2': 2, 'X3': 3}[fam]
fails = set()
for line in open(failfile):
    t = line.split()
    if t[0] != 'FAIL' or t[1] != fam: continue
    g6 = t[2]
    lits = tuple(sorted(tuple(map(int, x.split('|'))) for x in t[3:] if '|' in x))
    fails.add((g6, lits))
p = subprocess.Popen(['stdbuf', '-oL', './route_ext'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
nq = nf = mism = 0
for g6 in open(g6file):
    g6 = g6.strip()
    G = nx.from_graph6_bytes(g6.encode())
    n = G.number_of_nodes(); E = list(G.edges())
    pairs = [(a, b) for a in range(n) for b in range(a + 1, n)]
    for combo in itertools.combinations(range(len(pairs)), k):
        vs = [v for i in combo for v in pairs[i]]
        if len(set(vs)) != 2 * k: continue
        for o in itertools.product((0, 1), repeat=k):
            lits = []
            for i, oo in zip(combo, o):
                a, b = pairs[i]
                lits.append((b, a) if oo else (a, b))
            x = [0] * n
            for c, xx in lits: x[c] |= 1 << xx
            q = 'A %d %d %s %s %s' % (n, len(E), ' '.join('%d %d' % e for e in E), ' '.join(['1'] * n), ' '.join(map(str, x)))
            p.stdin.write(q + '\n'); p.stdin.flush()
            ans = p.stdout.readline().strip()
            nq += 1
            f = ans == '0'
            nf += f
            if f != ((g6, tuple(sorted(lits))) in fails): mism += 1
print(fam, 'queries', nq, 'route_ext failures', nf, 'allodd_dl failures', len(fails), 'mismatches', mism)
