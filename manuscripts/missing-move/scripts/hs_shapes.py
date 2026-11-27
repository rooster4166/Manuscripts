"""Shapes of the extra held edges in a hubroot log of hs_test.py.
Usage: python3 hs_shapes.py LOG
For each line "g6 root y k=K extra [...]" the K extra edges X (edges of F not at y) are classified
by the graph they form (matching, path, star, triangle, ...) and by where their ends lie:
N = a neighbour of y, O = a vertex outside N[y]; a lower-case letter marks an odd vertex of G
(n, o), an upper-case one an even vertex (N, O). A path is written as its vertex sequence. The solver returns the first winning F in
lexicographic order, so a shape is one winning shape, not a canonical one."""
import sys
from collections import Counter
import ast
import networkx as nx


def shape(X):
    H = nx.Graph(); H.add_edges_from(X)
    comps = sorted((c.number_of_nodes(), c.number_of_edges()) for c in
                   (H.subgraph(c) for c in nx.connected_components(H)))
    if all(e == 1 for _, e in comps):
        return "matching" if len(X) > 1 else "edge"
    if len(comps) == 1:
        v, e = comps[0]
        if e == v:
            return "triangle" if v == 3 else f"cycle{v}"
        degs = sorted(d for _, d in H.degree())
        if degs[-1] == 2:
            return f"path{e}"
        return f"star{e}" if degs[-1] == e else f"tree{e}"
    return "+".join(f"P{e}" if e < v else f"C{v}" for v, e in comps)


def ends(G, y, X):
    d = dict(G.degree())

    def t(v):
        c = "N" if G.has_edge(y, v) else "O"
        return c if d[v] % 2 == 0 else c.lower()
    H = nx.Graph(); H.add_edges_from(X)
    if nx.is_connected(H) and max(dd for _, dd in H.degree()) <= 2 and H.number_of_edges() < H.number_of_nodes():
        a = [v for v in H if H.degree(v) == 1][0]
        seq = "-".join(t(v) for v in nx.shortest_path(H, a, [v for v in H if H.degree(v) == 1 and v != a][0]))
        return min(seq, "-".join(reversed(seq.split("-"))))
    lab = []
    for a, b in X:
        t = ""
        for v in (a, b):
            c = "N" if G.has_edge(y, v) else "O"
            t += c if d[v] % 2 == 0 else c.lower()
        lab.append("".join(sorted(t)))
    return ",".join(sorted(lab))


if __name__ == "__main__":
    byk = {}
    for line in open(sys.argv[1]):
        if " extra " not in line:
            continue
        head, ex = line.split(" extra ")
        g6, _, y, k = head.split()
        G = nx.from_graph6_bytes(g6.encode())
        X = [tuple(e) for e in ast.literal_eval(ex.strip())]
        byk.setdefault(k, Counter())[(shape(X), ends(G, int(y), X))] += 1
    for k in sorted(byk):
        print(k, sum(byk[k].values()))
        for (s, e), c in byk[k].most_common():
            print(f"  {c:5d}  {s:10s} {e}")
