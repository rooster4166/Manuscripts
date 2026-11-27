"""cmp_multi.py N OUTFILE [SAMPLE SEED]: multigraph case.  For every connected G' of order N and every
perfect matching F of the even-degree vertices of G' (G' + F connected), recompute PTM and PTM(e@x)
with bf.ptm_multi and compare with ptm's 'p 0' output file (scripts/out/pc_N.txt).  Also reports,
independently with networkx, whether each failure has a cut vertex in G'."""
import sys, itertools, subprocess, random
import networkx as nx
from bf import parse_g6, ptm_multi

N, OUT = int(sys.argv[1]), sys.argv[2]
SAMPLE = int(sys.argv[3]) if len(sys.argv) > 3 else 0
SEED = int(sys.argv[4]) if len(sys.argv) > 4 else 1
fails_ptm, fails_r, summ = set(), set(), {}
for line in open(OUT):
    t = line.split()
    if t[0] == 'SUMMARY':
        summ = dict(kv.split('=') for kv in t[1:]); continue
    pairs = frozenset(frozenset(map(int, x.rstrip('*').split('-'))) for x in t[2:] if '-' in x and not x.startswith(('end', 'GF')))
    if t[0] == 'PTMFAIL': fails_ptm.add((t[1], pairs))
    elif t[0] == 'RFAIL': fails_r.add((t[1], pairs, int([x for x in t if x.startswith('end=')][0][4:])))


def pairings(L):
    if not L:
        yield []
        return
    a = L[0]
    for i in range(1, len(L)):
        for rest in pairings(L[1:i] + L[i + 1:]):
            yield [(a, L[i])] + rest


g6s = subprocess.run(['nauty-geng', '-cq', str(N)], capture_output=True, text=True).stdout.split()
inst = []
for s in g6s:
    n, A = parse_g6(s)
    ev = [v for v in range(n) if sum(A[v]) % 2 == 0]
    if len(ev) < 2:
        continue
    E = [(u, v) for u in range(n) for v in range(u + 1, n) if A[u][v]]
    for F in pairings(ev):
        inst.append((s, n, A, E, F))   # G' connected (geng -c), so G' + F connected
total = len(inst)
if SAMPLE:
    rnd = random.Random(SEED)
    keep = set(rnd.sample(range(total), min(SAMPLE, total)))
    flagged = {(f[0], f[1]) for f in fails_ptm} | {(f[0], f[1]) for f in fails_r}
    inst = [I for k, I in enumerate(inst) if k in keep or (I[0], frozenset(frozenset(e) for e in I[4])) in flagged]
c = dict(inst=0, par_inst=0, ptm_fail=0, r_fail=0, fail_no_cut=0)
mp, mr = set(), set()
for (s, n, A, E, F) in inst:
    c['inst'] += 1
    c['par_inst'] += any(A[u][v] for u, v in F)
    feas = {sh: ptm_multi(n, E, F, list(sh)) for sh in itertools.product(*F)}
    key = frozenset(frozenset(e) for e in F)
    failed = False
    if not any(feas.values()):
        c['ptm_fail'] += 1; mp.add((s, key)); failed = True
    else:
        for i, e in enumerate(F):
            for x in e:
                if not any(ok for sh, ok in feas.items() if sh[i] == x):
                    c['r_fail'] += 1; mr.add((s, key, x)); failed = True
    if failed:
        Gp = nx.Graph(); Gp.add_nodes_from(range(n)); Gp.add_edges_from(E)
        if not list(nx.articulation_points(Gp)):
            c['fail_no_cut'] += 1
            print('FAILURE WITHOUT CUT VERTEX', s, F)
print('N=%d class size=%d' % (N, total), 'bf:', c)
print('ptm:', {k: summ.get(k) for k in ('inst', 'par_inst', 'ptm_fail', 'r_fail')})
if SAMPLE:
    mp_f = {f for f in fails_ptm}; mr_f = {f for f in fails_r}
print('PTMFAIL agree:', mp == fails_ptm, len(mp), len(fails_ptm), ' RFAIL agree:', mr == fails_r, len(mr), len(fails_r))
