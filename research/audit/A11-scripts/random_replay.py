"""A11: end-to-end replay of the certificates on random concrete hosts (own code).

For a random host W meeting the hypotheses of Theorem 1 (bowtie: odd u ~ v, N(u) & T = A != {},
N(v) & T = {}; other one-universal cores: nothing outside T), we
  1. recompute every move's blank count in the WHOLE host (all vertices, actual adjacency, end
     count 1 outside the local set) and check it equals the local count used by the certificate;
  2. check with the exact solver (exact.realise) that at every node of the certificate tree the
     predicted end vector is realised by some partition of the current concrete graph
     W - (held edges not yet restored), along at least one branch of every grouped move
     (Fan's lemma guarantees one); at the leaves this is a realisable pair of W.
Hosts are adversarial: dense exterior, exterior vertices adjacent to T, u and v; v a leaf in a
quarter of the bowtie trials; W possibly disconnected.
"""
import itertools
import random
import sys

import cert_check as C
from exact import realise

T5 = C.T5


def fix_parity(adj, T, protected, rng, X):
    """Make T even and all other vertices odd by toggling allowed edges."""
    def tog(a, b):
        if b in adj[a]:
            adj[a].discard(b); adj[b].discard(a)
        else:
            adj[a].add(b); adj[b].add(a)
    for t in T:
        if len(adj[t]) % 2:
            tog(t, rng.choice(X))
    non = [w for w in adj if w not in T]
    bad = [w for w in non if len(adj[w]) % 2 == 0]
    rng.shuffle(bad)
    for p, q in zip(bad[::2], bad[1::2]):
        if frozenset((p, q)) in protected:
            w = rng.choice([z for z in X if z not in (p, q)])
            tog(p, w); tog(w, q)
        else:
            tog(p, q)


def bowtie_host(rng, N, A, vleaf):
    X = ['e%d' % i for i in range(N - 7)]
    V = list(T5) + ['u', 'v'] + X
    adj = {w: set() for w in V}

    def add(a, b):
        adj[a].add(b); adj[b].add(a)
    for e in C.BOWTIE:
        add(*tuple(e))
    for t in A:
        add('u', t)
    add('u', 'v')
    p = rng.uniform(0.25, 0.7)
    for a, b in itertools.combinations(X, 2):
        if rng.random() < p:
            add(a, b)
    for w in X:
        for t in T5:
            if rng.random() < p:
                add(w, t)
        if rng.random() < p:
            add(w, 'u')
        if not vleaf and rng.random() < p:
            add(w, 'v')
    protected = {frozenset(('u', 'v'))} | {frozenset(('u', t)) for t in T5} | {frozenset(('v', t)) for t in T5}
    protected |= {frozenset(e) for e in itertools.combinations(T5, 2)}
    if vleaf:
        protected |= {frozenset(('v', w)) for w in X}
    fix_parity(adj, set(T5), protected, rng, X)
    # verify hypotheses
    if any(len(adj[t]) % 2 for t in T5) or any(len(adj[w]) % 2 == 0 for w in V if w not in T5):
        return None
    if adj['u'] & set(T5) != set(A) or adj['v'] & set(T5) or 'v' not in adj['u']:
        return None
    if {frozenset((a, b)) for a in T5 for b in adj[a] if b in T5} != set(C.BOWTIE):
        return None
    if vleaf and adj['v'] != {'u'}:
        return None
    return adj


def core_host(rng, N, K):
    X = ['e%d' % i for i in range(N - 5)]
    V = list(T5) + X
    adj = {w: set() for w in V}

    def add(a, b):
        adj[a].add(b); adj[b].add(a)
    for e in K:
        add(*tuple(e))
    p = rng.uniform(0.25, 0.7)
    for a, b in itertools.combinations(X, 2):
        if rng.random() < p:
            add(a, b)
    for w in X:
        for t in T5:
            if rng.random() < p:
                add(w, t)
    protected = {frozenset(e) for e in itertools.combinations(T5, 2)}
    fix_parity(adj, set(T5), protected, rng, X)
    if any(len(adj[t]) % 2 for t in T5) or any(len(adj[w]) % 2 == 0 for w in V if w not in T5):
        return None
    if {frozenset((a, b)) for a in T5 for b in adj[a] if b in T5} != set(K):
        return None
    return adj


def replay(adj, M, H, prog):
    """Walk the certificate on the concrete host. Returns the number of leaves reached with every
    node realised (>= 1 required)."""
    H = [frozenset(h) for h in H]
    V = list(adj)

    def graph(restored):
        g = {w: set(adj[w]) for w in V}
        for h in H:
            if h not in restored:
                a, b = tuple(h)
                g[a].discard(b); g[b].discard(a)
        return g

    g0 = graph(frozenset())
    b = {w: len(g0[w]) % 2 for w in V}
    assert sum(1 for w in V if b[w] == 0) == 1
    assert all(b[w] == 1 for w in V if w not in M)
    reached = [0]

    def go(steps, restored, b):
        g = graph(restored)
        if realise(g, b) is None:
            return False
        if not steps:
            assert set(restored) == set(H)
            reached[0] += 1
            return True
        donors, r, printed, branches = steps[0]
        blk_global = sum(1 for w in g[r] if b[w] == 0)
        blk_local = sum(1 for w in g[r] if w in M and b[w] == 0)
        assert blk_global == blk_local
        assert sum(b[d] for d in donors) > blk_global
        any_ok = False
        for d in donors:
            if b[d] == 0:
                continue
            nb = dict(b); nb[d] -= 1; nb[r] += 1
            rest = branches[d] if branches is not None else steps[1:]
            if go(rest, restored | {frozenset((d, r))}, nb):
                any_ok = True
        return any_ok

    ok = go(list(prog), frozenset(), b)
    return reached[0] if ok else 0


def bowtie_cert(A):
    t = C.table()
    for p in C.bowtie_autos(C.BOWTIE):
        inv = {v: k for k, v in p.items()}
        Arep = ''.join(sorted(C.perm_apply(inv, A), key=T5.index))
        if Arep in t:
            H, z, prog, Sp = t[Arep]
            return [C.perm_apply(p, h) for h in H], C.transport_prog(prog, p)
        if Arep == 'xabcd':
            return ['xu', 'au', 'bu', 'cu', 'du', 'uv'], C.xabcd_progs()[0]
    raise AssertionError(A)


def local_cert(K):
    R = {e for e in K if 'x' not in e}
    for lab in itertools.permutations('abcd'):
        A_, B_, C_, D_ = lab
        e = lambda s, t: frozenset((s, t)) in R
        if len(R) == 0:
            c = ('unistar', ('x', A_, B_, C_, D_))
        elif len(R) == 1 and e(A_, B_):
            c = ('match', (A_, B_, C_, 'x', D_))
        elif len(R) == 2 and e(A_, B_) and e(B_, C_):
            c = ('match', (B_, C_, A_, 'x', D_))
        elif len(R) == 3 and e(A_, B_) and e(B_, C_) and e(C_, D_):
            c = ('match', (B_, C_, A_, 'x', D_))
        elif len(R) == 3 and e(A_, B_) and e(B_, C_) and e(A_, C_):
            c = ('oddstar', (A_, 'x', B_, C_, D_))
        elif len(R) == 4 and e(A_, B_) and e(B_, C_) and e(C_, D_) and e(D_, A_):
            c = ('oddstar', (A_, 'x', B_, D_, C_))
        else:
            continue
        gen, hyp = {n: (g, h) for n, g, h in C.LEMMAS}[c[0]]
        if hyp(K, *c[1]):
            H, prog, _ = gen(K, *c[1])
            return H, prog
    raise AssertionError


def main():
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    rng = random.Random(20261126)
    subsets = [''.join(c) for k in range(1, 6) for c in itertools.combinations(T5, k)]
    nb = nl = 0
    while nb < trials:
        A = rng.choice(subsets)
        N = rng.choice([9, 9, 11, 11, 13])
        vleaf = rng.random() < 0.25
        adj = bowtie_host(rng, N, A, vleaf)
        if adj is None:
            continue
        H, prog = bowtie_cert(A)
        k = replay(adj, set(T5) | {'u', 'v'}, [frozenset(h) for h in H], prog)
        assert k >= 1, (A, adj)
        nb += 1
    print(f'bowtie: {nb} random hosts (orders 9-13), every certificate node realised on the host, '
          f'global blank counts = local ones')
    rims = []
    RIMP = [frozenset(e) for e in itertools.combinations('abcd', 2)]
    for mask in range(64):
        R = {RIMP[i] for i in range(6) if mask >> i & 1}
        deg = {w: sum(1 for e in R if w in e) for w in 'abcd'}
        if max(deg.values()) <= 2 and not (len(R) == 2 and len(set().union(*R)) == 4):
            rims.append(R)
    while nl < trials:
        R = rng.choice(rims)
        K = R | C.mk_edges(['xa', 'xb', 'xc', 'xd'])
        N = rng.choice([7, 9, 9, 11, 11])
        adj = core_host(rng, N, K)
        if adj is None:
            continue
        H, prog = local_cert(K)
        k = replay(adj, set(T5), H, prog)
        assert k >= 1
        nl += 1
    print(f'six cores: {nl} random hosts (orders 7-11), every certificate node realised on the host')


if __name__ == '__main__':
    main()
