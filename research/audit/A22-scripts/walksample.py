"""walksample.py N SAMPLE SEED TLIM: per-instance comparison of the base hypothesis (shortest admissible
walks, all 8 orientations) with the NOBASE lines of scripts/out/walk_N_0.txt, on a random sample;
TLIM seconds per instance."""
import sys, itertools, subprocess, random, signal
from bf import parse_g6, lovasz
from walkcheck_lib import adm_walks, base_graph
class TO(Exception): pass
def h(*a): raise TO()
signal.signal(signal.SIGALRM, h)
N, K, SEED, T = map(int, sys.argv[1:5])
nob = set()
for l in open('/home/user/Manuscripts/manuscripts/terminal-matching/scripts/out/walk_%d_0.txt' % N):
    t = l.split()
    if t[0] == 'NOBASE': nob.add((t[1], frozenset([frozenset(map(int, t[2:4])), frozenset(map(int, t[4:6]))])))
# instances as in gen_pairs.py: g6(G - F) a1 b1 a2 b2
lines = open('/home/user/Manuscripts/manuscripts/terminal-matching/scripts/out/pairs_%d.txt' % N).read().split('\n')
lines = [l for l in lines if l.strip()]
S = random.Random(SEED).sample(lines, K)
c = dict(checked=0, base=0, agree=0, disagree=0, timeout=0)
for l in S:
    t = l.split(); n, A = parse_g6(t[0]); v = list(map(int, t[1:])); e, f = (v[0], v[1]), (v[2], v[3])
    for a, b in (e, f): A[a][b] = A[b][a] = 1
    found = False
    signal.alarm(T)
    try:
        for (E1, E2) in ((e, f), (f, e)):
            for a, b in (E1, E1[::-1]):
                for x, y in (E2, E2[::-1]):
                    W = adm_walks(n, A, a, b, x, y)
                    if not W: continue
                    L = min(len(P) for P in W)
                    for P in W:
                        if len(P) == L and not found:
                            found = lovasz(n + 1, base_graph(n, A, a, b, x, y, P), sep=[(x, y), (a, n), (n, y)])[0]
        signal.alarm(0)
    except TO:
        c['timeout'] += 1; continue
    c['checked'] += 1; c['base'] += found
    key = (t[0], frozenset([frozenset(e), frozenset(f)]))
    if found == (key in nob): c['disagree'] += 1; print('DISAGREE', l, found)
    else: c['agree'] += 1
print(c, 'NOBASE in sample by file:', sum((l.split()[0], frozenset([frozenset(map(int, l.split()[1:3])), frozenset(map(int, l.split()[3:5]))])) in nob for l in S))
