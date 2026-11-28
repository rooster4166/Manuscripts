"""mt_conj.py: test of Conjecture MT (manuscript Conjecture 6.2, the multi-tail lemma): H = G + k leaves
c_i at distinct stems w_i of a connected G, with <= 1 even vertex, avoided vertices x_i distinct, odd,
outside the stems and non-adjacent to their own stem.  Is there a parity decomposition with no path
containing c_i and x_i (all i)?  usage: mt_conj.py ROUTE_EXT k FILE.g6 (connected graphs, e.g. geng -c)
"""
import sys, itertools, subprocess
import networkx as nx
ORA = sys.argv[1]; k = int(sys.argv[2]); fn = sys.argv[3]
queries = []; meta = []
for line in open(fn):
    G = nx.from_graph6_bytes(line.strip().encode())
    n = G.number_of_nodes()
    for W in itertools.permutations(range(n), k):
        if list(W[:1]) and False: pass
        deg = {v: G.degree(v) + (1 if v in W else 0) for v in range(n)}
        ev = [v for v in range(n) if deg[v] > 0 and deg[v] % 2 == 0]
        if len(ev) > 1: continue
        # canonical: require W sorted? no: pairs (w_i,x_i) are ordered by i; avoid double count by W[0]<W[1]
        if k == 2 and W[0] > W[1]: continue
        cands = [[x for x in range(n) if x not in W and deg[x] % 2 == 1 and not G.has_edge(x, W[i])] for i in range(k)]
        for X in itertools.product(*cands):
            if len(set(X)) < k: continue
            H = G.copy(); cs = []
            for i in range(k):
                c = n + i; H.add_edge(c, W[i]); cs.append(c)
            N = n + k; E = list(H.edges())
            b = [H.degree(v) % 2 for v in range(N)]
            q = "S %d %d %s %s %d %s" % (N, len(E), " ".join("%d %d" % e for e in E), " ".join(map(str, b)), k,
                                        " ".join("%d %d" % (cs[i], X[i]) for i in range(k)))
            queries.append(q); meta.append((line.strip(), W, X))
p = subprocess.run([ORA], input="\n".join(queries) + "\n", capture_output=True, text=True)
out = p.stdout.split()
fails = [meta[i] for i in range(len(out)) if out[i] != '1']
print("instances", len(queries), "fail", len(fails))
for f in fails[:20]: print("FAIL", f)
