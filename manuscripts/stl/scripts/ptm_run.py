"""E22 (F): the terminal-matching property PTM(G, F) and its prescribed-end form PEE_m.

G: random connected all-odd graph of order n; F: random matching of m edges of G.
  PTM(G,F) : some Lovasz decomposition of G has every F-edge terminal (at either end) and no path
             with two F-edges   (= STL-P(J, F) for J = (G - F) + z(V(F)), Prop. "pairings")
  PEE(G,F,ends): ... with each F-edge terminal at a prescribed end x_i (random)
Records whether G - F is connected and whether G is 3-connected.
usage: ptm_run.py n m count seed budget out.jsonl
"""
import sys, json, random, collections
import networkx as nx
from common import Oracle

n, m, count, seed, budget, outfn = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
rng = random.Random(seed)
orc = Oracle(); out = open(outfn, 'w'); st = collections.Counter()


def rand_allodd():
    while True:
        p = rng.uniform(0.2, 0.55)
        G = nx.gnp_random_graph(n, p, seed=rng.randrange(1 << 30))
        bad = [v for v in G if G.degree(v) % 2 == 0]
        rng.shuffle(bad)
        for i in range(0, len(bad) - 1, 2):
            u, v = bad[i], bad[i + 1]
            if G.has_edge(u, v): G.remove_edge(u, v)
            else: G.add_edge(u, v)
        if all(G.degree(v) % 2 == 1 for v in G) and nx.is_connected(G):
            return G


def q(J, prof, **kw):
    for k, bud in enumerate([budget, 4 * budget, 16 * budget]):
        for s in range(2):
            v = orc.query(J, prof, n, -1, 1, 99, seed=rng.randrange(1 << 30), budget=bud, **kw)
            if v != 2:
                return v
    return 2


for it in range(count):
    G = rand_allodd()
    E = list(G.edges()); rng.shuffle(E)
    F = []; used = set()
    for u, v in E:
        if u not in used and v not in used:
            F.append((u, v)); used |= {u, v}
        if len(F) == m:
            break
    if len(F) < m:
        continue
    H = G.copy(); H.remove_edges_from(F)
    J = H.copy(); J.add_node(n); J.add_edges_from((n, x) for e in F for x in e)
    prof = {v: J.degree(v) % 2 for v in J}
    pairs = {}
    for a, b in F:
        pairs[a] = {b}; pairs[b] = {a}
    ptm = q(J, prof, pairs=pairs)
    ends = [(a, b) if rng.random() < 0.5 else (b, a) for a, b in F]
    pee = q(J, prof, pairs=pairs, req={x: n for x, _ in ends}) if ptm == 1 else 0
    rec = dict(g6=nx.to_graph6_bytes(G, header=False).decode().strip(), F=F, ends=ends, PTM=ptm, PEE=pee,
               GFconn=nx.is_connected(H), G3c=nx.node_connectivity(G) >= 3)
    out.write(json.dumps(rec) + '\n'); out.flush()
    key = ('GFconn' if rec['GFconn'] else 'GFdisc')
    st[(key, 'n')] += 1; st[(key, 'PTM', ptm)] += 1; st[(key, 'PEE', pee)] += 1
print('FINAL', n, m, dict(sorted(st.items(), key=str)), flush=True)
