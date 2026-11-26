"""Seven-site bank in W = B + leaf: T = 0..4 (even in W), u = 5 (odd), v = 6 (odd),
uv an edge, N_T(u) = A, N_T(v) = empty.  Seed: hold H so exactly one local vertex
is even; Lovasz gives k paths with exact ends.  Success = all held edges restored
(gives floor partition of W)."""
import itertools, sys
from fancert import search
a, b, c, d, e = range(5)
def book():
    return [(a, b)] + [(x, y) for x in (a, b) for y in (c, d, e)]
CORES = {
    'K0': book(),
    'K1': book() + [(c, d)],
    'K2': book() + [(c, d), (d, e)],
    'K3': book() + [(c, d), (d, e), (c, e)],
    # one universal vertex a, rim on b,c,d,e with max degree <= 2
    'U_E0': [(a, x) for x in (b, c, d, e)],
    'U_K2': [(a, x) for x in (b, c, d, e)] + [(b, c)],
    'U_M': [(a, x) for x in (b, c, d, e)] + [(b, c), (d, e)],
    'U_P3': [(a, x) for x in (b, c, d, e)] + [(b, c), (c, d)],
    'U_K3': [(a, x) for x in (b, c, d, e)] + [(b, c), (c, d), (b, d)],
    'U_P4': [(a, x) for x in (b, c, d, e)] + [(b, c), (c, d), (d, e)],
    'U_C4': [(a, x) for x in (b, c, d, e)] + [(b, c), (c, d), (d, e), (e, b)],
}
NAMES = 'abcde'
def run(core, A, maxH=None):
    E = CORES[core] + [(5, t) for t in A] + [(5, 6)]
    par = [0, 0, 0, 0, 0, 1, 1]
    m = len(E)
    best = None
    order = sorted(range(1 << m), key=lambda s: bin(s).count('1'))
    for s in order:
        if maxH is not None and bin(s).count('1') > maxH:
            break
        H = [E[i] for i in range(m) if s >> i & 1]
        p = list(par)
        for x, y in H:
            p[x] ^= 1; p[y] ^= 1
        if sum(1 for q in p if q == 0) != 1:
            continue
        b0 = tuple(1 if q else 0 for q in p)
        cert = search(7, E, H, b0)
        if cert is not None:
            return H, b0, cert
    return None
if __name__ == '__main__':
    core = sys.argv[1]
    maxH = int(sys.argv[2]) if len(sys.argv) > 2 else None
    T = list(range(5))
    surv = []
    for size in range(1, 6):
        for A in itertools.combinations(T, size):
            r = run(core, A, maxH)
            tag = ''.join(NAMES[t] for t in A)
            if r is None:
                surv.append(tag)
            else:
                print(core, tag, 'CERT held=', [(NAMES[x] if x < 5 else 'uv'[x-5], NAMES[y] if y < 5 else 'uv'[y-5]) for x, y in r[0]], flush=True)
    print(core, 'certified', 31 - len(surv), 'surviving', surv, flush=True)
