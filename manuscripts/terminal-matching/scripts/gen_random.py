"""Random instances for ptm mode f: connected all-odd G(n,p) graphs (parities repaired) and a
matching F of m edges, chosen by MODE:
  rand  : random matching;
  close : each new F-edge has an end adjacent to an end of an earlier F-edge;
  share : each new F-edge has an end with a common neighbour with an earlier F-edge's end
          (distance exactly two), often several.
Prints 'g6(G - F) a1 b1 ...' lines.  usage: gen_random.py n m count seed mode [pmin pmax]"""
import sys, random
import networkx as nx
n, m, count, seed, mode = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
pmin = float(sys.argv[6]) if len(sys.argv) > 6 else 0.15
pmax = float(sys.argv[7]) if len(sys.argv) > 7 else 0.5
rng = random.Random(seed)

def rand_allodd():
    while True:
        G = nx.gnp_random_graph(n, rng.uniform(pmin, pmax), seed=rng.randrange(1 << 30))
        bad = [v for v in G if G.degree(v) % 2 == 0]
        rng.shuffle(bad)
        for i in range(0, len(bad) - 1, 2):
            u, v = bad[i], bad[i + 1]
            if G.has_edge(u, v): G.remove_edge(u, v)
            else: G.add_edge(u, v)
        if all(G.degree(v) % 2 == 1 for v in G) and nx.is_connected(G):
            return G

def pick(G):
    E = list(G.edges()); rng.shuffle(E)
    F, used = [], set()
    for _ in range(200):
        if len(F) == m: break
        if not F or mode == 'rand':
            cand = [e for e in E if not (set(e) & used)]
        else:
            Fv = list(used)
            if mode == 'close':
                near = {w for v in Fv for w in G[v]} - used
            else:
                near = {x for v in Fv for w in G[v] for x in G[w]} - used - {w for v in Fv for w in G[v]}
            cand = [e for e in E if not (set(e) & used) and (set(e) & near)]
        if not cand: return None
        e = rng.choice(cand); F.append(e); used |= set(e)
    return F if len(F) == m else None

made = 0
while made < count:
    G = rand_allodd()
    F = pick(G)
    if F is None: continue
    H = G.copy(); H.remove_edges_from(F)
    print(nx.to_graph6_bytes(H, header=False).decode().strip(), ' '.join(f'{a} {b}' for a, b in F))
    made += 1
