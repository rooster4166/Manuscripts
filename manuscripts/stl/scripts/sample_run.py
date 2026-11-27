"""E22 (C): random 3-connected samples.

mode 1 : J has exactly one even vertex z (n odd); test ST, STL(r), BAL(r) for every r in N(z).
mode 2 : J has exactly two even vertices z, r, adjacent (n even); test STL2/BAL2 for (z,r),(r,z).
Families: 'sparse' (degree sequence: z of degree 2k, others 3 or 5) and 'gnp' (G(n,p), parity
fixed by toggling a random pairing of the wrong-parity vertices).  Only 3-connected J are kept;
J - z with / without matching cut is recorded.  Oracle runs with a node budget; undecided -> 2.

usage: sample_run.py mode n count seed family budget out.jsonl
"""
import sys, json, random, collections
import networkx as nx
from common import Oracle, has_matching_cut_fast
from stl_run import test1
from stl2_run import test2

mode, n, count, seed, fam, budget, outfn = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5], int(sys.argv[6]), sys.argv[7]
rng = random.Random(seed)
orc = Oracle()


def fix_parity(G, want_even):
    """toggle edges along a random pairing of the vertices with wrong parity"""
    bad = [v for v in G if (G.degree(v) % 2 == 0) != (v in want_even)]
    rng.shuffle(bad)
    for i in range(0, len(bad) - 1, 2):
        u, v = bad[i], bad[i + 1]
        if G.has_edge(u, v): G.remove_edge(u, v)
        else: G.add_edge(u, v)
    return G


def gen():
    while True:
        if fam == 'sparse':
            k = rng.choice([2, 2, 3, 3, 4])
            ds = [2 * k] + [rng.choice([3, 3, 3, 5]) for _ in range(n - 1)]
            if mode == 2:
                ds[1] = rng.choice([4, 4, 6])
            if sum(ds) % 2:
                ds[-1] += 2 if ds[-1] == 3 else -2
            try:
                G = nx.random_degree_sequence_graph(ds, seed=rng.randrange(1 << 30), tries=20)
            except Exception:
                continue
            want = {0} if mode == 1 else {0, 1}
            if mode == 2 and not G.has_edge(0, 1):
                continue
        else:
            p = rng.uniform(0.25, 0.6)
            G = nx.gnp_random_graph(n, p, seed=rng.randrange(1 << 30))
            want = {0} if mode == 1 else {0, 1}
            if mode == 2:
                G.add_edge(0, 1)
            fix_parity(G, want)
            if mode == 2 and not G.has_edge(0, 1):
                continue
        ev = [v for v in G if G.degree(v) % 2 == 0]
        if sorted(ev) != sorted(want):
            continue
        if G.number_of_edges() > 128 or nx.node_connectivity(G) < 3:
            continue
        return G


stats = collections.Counter()
out = open(outfn, 'w')
for it in range(count):
    J = gen()
    if mode == 1:
        z = 0
        mc = has_matching_cut_fast(J.subgraph(set(J) - {z}))
        prof = {v: J.degree(v) % 2 for v in J}
        rec = dict(g6=nx.to_graph6_bytes(J, header=False).decode().strip(), n=n, m=J.number_of_edges(),
                   dz=J.degree(z), mc=mc, res={})
        for r in sorted(J[z]):
            stl = orc.query(J, prof, z, r, 1, 0, seed=it, budget=budget)
            if stl == 2:
                stl = orc.query(J, prof, z, r, 1, 0, seed=it + 7777, budget=4 * budget)
            bal = stl if stl == 1 else orc.query(J, prof, z, r, 0, 0, seed=it, budget=budget)
            t1 = None
            if stl != 1 and bal != 1:
                t1 = test1(J, z, r)
            rec['res'][r] = (stl, bal, t1)
            stats['pairs'] += 1; stats[('STL', stl)] += 1; stats[('BAL', bal)] += 1
            if mc: stats['pairs_mc'] += 1; stats[('STL_mc', stl)] += 1
        stats['graphs'] += 1
    else:
        ev = [0, 1]
        rec = dict(g6=nx.to_graph6_bytes(J, header=False).decode().strip(), n=n, m=J.number_of_edges(), res={})
        for z, r in ((0, 1), (1, 0)):
            mc = has_matching_cut_fast(J.subgraph(set(J) - {z}))
            p0 = {v: J.degree(v) % 2 for v in J}
            p2 = dict(p0); p2[r] = 2
            s0 = orc.query(J, p0, z, r, 1, 0, seed=it, budget=budget)
            s2 = 1 if s0 == 1 else orc.query(J, p2, z, r, 1, 0, seed=it, budget=budget)
            stl2 = 1 if 1 in (s0, s2) else (2 if 2 in (s0, s2) else 0)
            bal2 = None; t2 = None
            if stl2 != 1:
                b0 = orc.query(J, p0, z, r, 0, 0, seed=it, budget=budget)
                b2 = orc.query(J, p2, z, r, 0, 0, seed=it, budget=budget)
                bal2 = 1 if 1 in (b0, b2) else (2 if 2 in (b0, b2) else 0)
                if bal2 != 1:
                    t2 = test2(J, z, r)
            rec['res'][f'{z}-{r}'] = (s0, s2, stl2, bal2, t2, mc, J.degree(z))
            stats['inst'] += 1; stats[('STL2', stl2)] += 1; stats[('S0', s0)] += 1
        stats['graphs'] += 1
    out.write(json.dumps(rec) + '\n'); out.flush()
    if (it + 1) % 50 == 0:
        print(it + 1, dict(stats), flush=True)
print('FINAL', mode, n, fam, dict(stats), flush=True)
