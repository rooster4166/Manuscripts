"""E22 (E): structured and adversarial families.
  wheel k        : W_{2k} (hub z, rim C_{2k}), k = 2..maxk
  univ nH count  : J = H + universal z, H random 4-regular of order nH (Eulerian H; d(z) = nH)
  zconn n count  : random J with one even vertex z, J - z connected but J NOT 3-connected
Each instance: STL(r) for every r in N(z) (budgeted, retried), then Test1(r) on failure.
usage: families.py fam arg count seed out.jsonl
"""
import sys, json, random, collections
import networkx as nx
from common import Oracle
from stl_run import test1

fam, arg, count, seed, outfn = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
rng = random.Random(seed)
orc = Oracle()
out = open(outfn, 'w')
stats = collections.Counter()


def decide(J, z, r):
    prof = {v: J.degree(v) % 2 for v in J}
    for k, bud in enumerate([2_000_000, 8_000_000, 32_000_000, 128_000_000]):
        for s in range(2):
            v = orc.query(J, prof, z, r, 1, 0, seed=rng.randrange(1 << 30), budget=bud)
            if v != 2:
                return v
    return 2


def instances():
    if fam == 'wheel':
        for k in range(2, arg + 1):
            J = nx.wheel_graph(2 * k + 1)  # hub 0
            yield J, 0, [1]
    elif fam == 'univ':
        for _ in range(count):
            H = nx.random_regular_graph(4, arg, seed=rng.randrange(1 << 30))
            if not nx.is_connected(H):
                continue
            J = nx.relabel_nodes(H, {v: v + 1 for v in H}); J.add_edges_from((0, v) for v in range(1, arg + 1))
            yield J, 0, sorted(J[0])
    elif fam == 'zconn':
        made = 0
        while made < count:
            n = arg
            p = rng.uniform(0.15, 0.45)
            G = nx.gnp_random_graph(n, p, seed=rng.randrange(1 << 30))
            bad = [v for v in G if (G.degree(v) % 2 == 0) != (v == 0)]
            rng.shuffle(bad)
            for i in range(0, len(bad) - 1, 2):
                u, v = bad[i], bad[i + 1]
                if G.has_edge(u, v): G.remove_edge(u, v)
                else: G.add_edge(u, v)
            if [v for v in G if G.degree(v) % 2 == 0] != [0] or G.degree(0) == 0:
                continue
            H = G.subgraph(set(G) - {0})
            if not nx.is_connected(H) or nx.node_connectivity(G) >= 3:
                continue
            made += 1
            yield G, 0, [r for r in sorted(G[0]) if G.degree(r) >= 3]


for J, z, rs in instances():
    rec = dict(g6=nx.to_graph6_bytes(J, header=False).decode().strip(), n=J.number_of_nodes(),
               dz=J.degree(z), conn=nx.node_connectivity(J), res={})
    for r in rs:
        v = decide(J, z, r)
        t1 = test1(J, z, r) if v == 0 else None
        rec['res'][r] = (v, t1)
        stats[('STL', v)] += 1
        if v == 0:
            stats[('T1', t1)] += 1
    stats['graphs'] += 1
    out.write(json.dumps(rec) + '\n'); out.flush()
print('FINAL', fam, arg, dict(stats), flush=True)
