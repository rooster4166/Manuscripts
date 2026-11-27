"""und_bf.py FILE TLIM: ptm-undecided instances ('g6(G-F) a1 b1 ...'); decide PTM and every PTM(e@x)
with bf.py (lazy), at most TLIM seconds per assignment query.  Prints one line per instance."""
import sys, itertools, signal
from bf import parse_g6, ptm_assign
class TO(Exception): pass
def h(*a): raise TO()
signal.signal(signal.SIGALRM, h)
T = int(sys.argv[2])
for l in open(sys.argv[1]):
    t = l.split()
    if not t: continue
    n, A = parse_g6(t[0]); v = list(map(int, t[1:])); F = [(v[2*i], v[2*i+1]) for i in range(len(v)//2)]
    for a, b in F: A[a][b] = A[b][a] = 1
    need = {(i, x) for i, e in enumerate(F) for x in e}; got = set(); unknown = set(); infeas = set()
    for sh in itertools.product(*F):
        S = {(i, s) for i, s in enumerate(sh)}
        if not (S - got): continue
        signal.alarm(T)
        try:
            ok = ptm_assign(n, A, F, list(sh)); signal.alarm(0)
        except TO:
            ok = None
        if ok: got |= S
        elif ok is None: unknown.add(sh)
        else: infeas.add(sh)
        if got == need: break
    status = 'ALLOK' if got == need else ('PTMFAIL' if not got and not unknown else 'OPEN')
    print(status, l.strip(), 'feasible-pairs=%d/%d timeouts=%d infeasible=%d' % (len(got), len(need), len(unknown), len(infeas)), flush=True)
