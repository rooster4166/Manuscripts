"""e_tb2.py (audit A37, item 3e): re-run the session's tb2.py search (its function `process`, with
the route_ext oracle) on a seeded sample of order-10 instances, and check every returned base and
lift with MY OWN code:
  * Phi is a forest of E(B) whose odd-degree set is exactly N(z);
  * the parent map is a rooting of Phi (one root per component, every Phi-edge is (v, p(v)) once),
    with r a root or a non-root with >= 2 children;
  * D0 is a Lovasz decomposition of my own M (one end at every vertex), with (i) and (ii);
  * tb2's lifted paths are a (T2) decomposition (own checker); my own lift (d_theta.my_lift) also.
Also reports the tier distribution (M / S / X / N) of the sample.
usage: python3 e_tb2.py ORACLE SAMPLE SEED
"""
import gzip
import random
import sys
from collections import Counter

HERE = __file__.rsplit("/", 1)[0]
sys.path.insert(0, HERE)
sys.path.insert(1, "/home/user/Manuscripts/manuscripts/test2/scripts")
import networkx as nx  # noqa: E402

import tb2  # noqa: E402  (the session's code, used only to PRODUCE the bases)
from a37lib import adjacency, check_decomp, delete_vertex, g6_decode  # noqa: E402
from d_theta import is_base, my_lift  # noqa: E402

F = "/home/user/Manuscripts/manuscripts/test2/data/t2_order10_fields.txt.gz"


def own_check(g6, z, r, phi, par, D0, paths):
    n, E = g6_decode(g6)
    A = adjacency(n, E)
    B = delete_vertex(E, z)
    Phi = {frozenset(e) for e in phi}
    assert len(Phi) == len(phi) and Phi <= B
    deg = Counter(v for e in Phi for v in e)
    assert {v for v, d in deg.items() if d % 2} == set(A[z]), "not an N(z)-join"
    # rooting
    assert {frozenset((v, p)) for v, p in par.items()} == Phi and len(par) == len(Phi)
    G = nx.Graph([tuple(e) for e in Phi])
    assert nx.is_forest(G)
    for comp in nx.connected_components(G):
        roots = [v for v in comp if v not in par]
        assert len(roots) == 1
    kids_r = sum(1 for v in par if par[v] == r)
    mode = "root" if r not in par else "child"
    if mode == "child":
        assert kids_r >= 2
    # base
    M = {e for e in E if not (z in e and (set(e) - {z}).pop() != r)} - Phi
    ends = check_decomp(M, D0)
    Vm = {v for e in M for v in e}
    assert all(ends.get(v, 0) == 1 for v in Vm) and len(D0) == n // 2
    assert all(len(adjacency(n, M)[v]) % 2 == 1 for v in range(n))
    assert is_base(D0, par)
    # lifts
    check_decomp(B, paths, maxpaths=n // 2, r=r, minends=3)
    order = []
    seen = set()
    # parents-first order of my own (BFS from the roots)
    for comp in nx.connected_components(G):
        ro = [v for v in comp if v not in par][0]
        q = [ro]
        seen.add(ro)
        for u in q:
            for w in sorted(G[u]):
                if w not in seen:
                    seen.add(w)
                    order.append(w)
                    q.append(w)
    mine = my_lift(E, z, r, par, order, D0, n)
    check_decomp(B, mine, maxpaths=n // 2, r=r, minends=3)
    return mode


def main():
    oracle = tb2.Oracle(sys.argv[1])
    N, seed = int(sys.argv[2]), int(sys.argv[3])
    with gzip.open(F, "rt") as fh:
        lines = fh.read().splitlines()
    rng = random.Random(seed)
    sample = rng.sample(lines, N)
    st = Counter()
    trng = random.Random(1)
    for line in sample:
        g6, z, r = line.split()[:3]
        z, r = int(z), int(r)
        J = nx.from_graph6_bytes(g6.encode())
        tier, wit, nq, und = tb2.process(oracle, J, z, r, 0, tb2.XDIM, trng)
        st[("tier", tier)] += 1
        if wit is None:
            print("NO BASE", line[:40], tier, flush=True)
            continue
        phi, par, D0, paths = wit
        mode = own_check(g6, z, r, phi, par, D0, paths)
        st[("own check ok", mode)] += 1
    for k in sorted(st, key=str):
        print(k, st[k])


if __name__ == "__main__":
    main()
