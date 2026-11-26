"""End-to-end replay of seven-site certificates on concrete random hosts W:
Lovasz-type seed obtained by CP-SAT with the exact end vector, then Fan's own
construction (fan_proc.fan_transfer) follows the certificate tree; the final
decomposition is verified as a k-path partition of W."""
import random, sys, itertools
from common import *
from sevensite import CORES, run, NAMES
from fan_proc import fan_transfer
from fan_test import ends
from circ import solve_circ
def host(rng, core, A, m):
    for _ in range(500):
        W = nx.Graph(); W.add_nodes_from(range(7 + m))
        W.add_edges_from(CORES[core]); W.add_edges_from((5, t) for t in A); W.add_edge(5, 6)
        X = list(range(7, 7 + m))
        for a, b in itertools.combinations(X, 2):
            if rng.random() < 0.5: W.add_edge(a, b)
        for x in X:
            for y in list(range(5)) + [5, 6]:
                if rng.random() < 0.4: W.add_edge(x, y)
        want = {v: (0 if v < 5 else 1) for v in W}
        wrong = [v for v in W if W.degree(v) % 2 != want[v]]
        rng.shuffle(wrong)
        okp = True
        for p, q in zip(wrong[::2], wrong[1::2]):
            if p >= 7 or q >= 7:
                if W.has_edge(p, q): W.remove_edge(p, q)
                else: W.add_edge(p, q)
            else:
                x = rng.choice(X)
                for y in (p, q):
                    if W.has_edge(x, y): W.remove_edge(x, y)
                    else: W.add_edge(x, y)
        if len(wrong) % 2 or any(W.degree(v) % 2 != want[v] for v in W): continue
        if not nx.is_connected(W): continue
        return W
    return None
def replay(W, H, b0, cert):
    k = (W.number_of_nodes() - 1) // 2
    G = W.copy(); G.remove_edges_from(H)
    exact = {v: (b0[v] if v < 7 else 1) for v in G}
    st, D = solve_circ(G, k, exact=exact, workers=2, time_limit=600)
    assert D is not None, ('seed failed', st)
    node = cert
    while node != 'leaf':
        _, x, donors, Z, kids = node
        r = fan_transfer(G, D, x, list(donors))
        assert r is not None, 'Fan construction failed'
        y, D = r
        G.add_edge(y, x)
        node = dict((yy, sub) for (yy, xx), sub in kids)[y]
    assert verify_partition(W, D) and len(D) == k
    return len(D)
if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1]))
    cases = [('U_M', (0,)), ('U_C4', (0, 1, 2, 3, 4)), ('U_P4', (1, 3)), ('K0', (0, 2)), ('K1', (0, 1, 2, 3, 4)), ('K2', (0, 1, 2)), ('K3', (0, 1)), ('K3', (2,))]
    for core, A in cases:
        res = run(core, A)
        H, b0, cert = res
        for m in (4, 6):
            W = host(rng, core, A, m)
            if W is None: print(core, A, m, 'no host'); continue
            kk = replay(W, H, b0, cert)
            print(core, ''.join(NAMES[t] for t in A), 'm=%d' % m, 'replayed OK, paths =', kk, '= floor', flush=True)
