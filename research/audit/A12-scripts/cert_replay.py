"""Replay the printed strategy trees of missing-move/scripts/outputs/certificate*.txt (audit A12).

Independent of the author's scripts: the tree is parsed from the text, and at every node the
current graph H = G - held, the supply and the number of blank neighbours Z_H(u) are recomputed
from scratch and compared with the printed numbers. Checked:
  * the held set is a set of edges of G, and the seed is a Lovasz seed (b = d_K mod 2, at most one
    vertex of positive even degree in K) or the Lemma-4 seed;
  * every single transfer is legal (b(t) > Z(u)) and the printed numbers are the true ones;
  * every grouped transfer is legal (sum_T b > Z(u)), and the printed donors are exactly the
    t in T with b(t) >= 1 (adversarial donor: every branch present);
  * every new path consists of held edges, is a simple path, and stays within the budget;
  * every printed profile equals the recomputed one; at END no edge is held, sum b <= n and
    b(root) >= 1.
Usage: python3 cert_replay.py GRAPH6 ROOT FILE [header-substring]"""
import re
import sys
import networkx as nx


def parse_tree(lines):
    """lines: list of (indent, text). Returns nested nodes."""
    pos = 0

    def node(ind):
        nonlocal pos
        ind0, txt = lines[pos]
        pos += 1
        if txt == "END":
            return ("END",)
        m = re.match(r"single (\d+)->(\d+)\s+\(b\(t\)=(\d+) > Z\(u\)=(\d+)\)\s+b=\(([\d, ]+)\)", txt)
        if m:
            t, u, bt, z = map(int, m.groups()[:4])
            b = tuple(int(x) for x in m.group(5).split(","))
            return ("single", t, u, bt, z, b, node(ind0))
        m = re.match(r"new path \(([\d, ]+)\)\s+b=\(([\d, ]+)\)", txt)
        if m:
            p = tuple(int(x) for x in m.group(1).split(","))
            b = tuple(int(x) for x in m.group(2).split(","))
            return ("path", p, b, node(ind0))
        m = re.match(r"grouped at (\d+), T=\(([\d, ]+)\) \(sum=(\d+) > Z=(\d+)\); adversary picks:", txt)
        if m:
            u = int(m.group(1)); T = tuple(int(x) for x in m.group(2).split(",") if x.strip())
            sm, z = int(m.group(3)), int(m.group(4))
            br = []
            while pos < len(lines) and lines[pos][0] > ind0 and lines[pos][1].startswith("donor"):
                dind, dtxt = lines[pos]
                mm = re.match(r"donor (\d+): b=\(([\d, ]+)\)", dtxt)
                pos += 1
                t = int(mm.group(1)); b = tuple(int(x) for x in mm.group(2).split(","))
                br.append((t, b, node(dind + 2)))
            return ("grouped", u, T, sm, z, br)
        raise ValueError("cannot parse: " + txt)

    return node(lines[0][0])


def check(G, r, F, b0, tree, log):
    n = G.number_of_nodes()
    E = set(tuple(sorted(e)) for e in G.edges())
    held = set(tuple(sorted(e)) for e in F)
    assert held <= E, "held edge not in G"
    # seed
    K = nx.Graph(); K.add_nodes_from(range(n)); K.add_edges_from(E - held)
    d = [K.degree(v) for v in range(n)]
    pe = [v for v in range(n) if d[v] > 0 and d[v] % 2 == 0]
    ok_seeds = []
    if len(pe) <= 1:
        ok_seeds.append(tuple(x % 2 for x in d))
    if all(x > 0 for x in d) and len(pe) == 2:
        for u, v in (pe, pe[::-1]):
            bb = [x % 2 for x in d]; bb[v] = 2; bb[u] = 0; ok_seeds.append(tuple(bb))
    assert tuple(b0) in ok_seeds, ("bad seed", b0, ok_seeds)
    log.append(f"seed {b0} valid; Ev(K) = {pe}; 2|D| = {sum(b0)} (n = {n})")
    nleaves = [0]

    def Z(H, b, u):
        return sum(1 for w in H[u] if b[w] == 0)

    def rec(held, b, nd, depth):
        H = nx.Graph(); H.add_nodes_from(range(n)); H.add_edges_from(E - held)
        pad = "  " * depth
        if nd[0] == "END":
            assert not held and sum(b) <= n and b[r] >= 1, ("bad END", held, b)
            nleaves[0] += 1
            log.append(pad + f"END: sum b = {sum(b)} <= {n}, b({r}) = {b[r]}")
            return
        if nd[0] == "single":
            _, t, u, bt, z, nb, sub = nd
            e = tuple(sorted((t, u)))
            assert e in held
            zz = Z(H, b, u)
            assert b[t] == bt and zz == z and b[t] > zz, ("single", t, u, b[t], zz, bt, z)
            c = list(b); c[u] += 1; c[t] -= 1
            assert tuple(c) == nb
            log.append(pad + f"single {t}->{u}: b(t) = {b[t]} > Z(u) = {zz} "
                       f"(blank nbrs {sorted(w for w in H[u] if b[w] == 0)})")
            rec(held - {e}, tuple(c), sub, depth)
            return
        if nd[0] == "path":
            _, p, nb, sub = nd
            es = [tuple(sorted((p[i], p[i + 1]))) for i in range(len(p) - 1)]
            assert len(set(p)) == len(p) and all(e in held for e in es)
            assert sum(b) + 2 <= n
            c = list(b); c[p[0]] += 1; c[p[-1]] += 1
            assert tuple(c) == nb
            log.append(pad + f"new path {p}: sum b {sum(b)} -> {sum(c)}")
            rec(held - set(es), tuple(c), sub, depth)
            return
        if nd[0] == "grouped":
            _, u, T, sm, z, br = nd
            for t in T:
                assert tuple(sorted((t, u))) in held
            zz = Z(H, b, u); s2 = sum(b[t] for t in T)
            assert s2 == sm and zz == z and s2 > zz, ("grouped", u, T, s2, zz)
            donors = sorted(t for t in T if b[t] >= 1)
            assert sorted(t for t, _, _ in br) == donors, ("donor branches", donors, br)
            log.append(pad + f"grouped at {u}, T = {T}: supply {s2} > Z(u) = {zz} "
                       f"(blank nbrs {sorted(w for w in H[u] if b[w] == 0)}); donors {donors}")
            for t, nb, sub in br:
                c = list(b); c[u] += 1; c[t] -= 1
                assert tuple(c) == nb
                log.append(pad + f"  [donor {t}]")
                rec(held - {tuple(sorted((t, u)))}, tuple(c), sub, depth + 2)
            return

    rec(frozenset(held), tuple(b0), tree, 0)
    return nleaves[0]


def load(path, header=None):
    txt = open(path).read().splitlines()
    if header is not None:
        i = next(k for k, l in enumerate(txt) if l.startswith("===") and header in l)
        j = next((k for k in range(i + 1, len(txt)) if txt[k].startswith("===")), len(txt))
        txt = txt[i + 1:j]
    k = next(k for k, l in enumerate(txt) if l.startswith("held F ="))
    m = re.match(r"held F = (\(.*\)) seed (\w+) \(([\d, ]+)\)", txt[k])
    F = eval(m.group(1)); b0 = tuple(int(x) for x in m.group(3).split(","))
    body = [(len(l) - len(l.lstrip(" ")), l.strip()) for l in txt[k + 1:] if l.strip()]
    return F, b0, parse_tree(body)


if __name__ == "__main__":
    g6, r, path = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    header = sys.argv[4] if len(sys.argv) > 4 else None
    G = nx.from_graph6_bytes(g6.encode())
    F, b0, tree = load(path, header)
    log = []
    nl = check(G, r, F, b0, tree, log)
    print(f"== {g6} root {r}: |F| = {len(F)}, F = {F}")
    print("\n".join(log))
    print(f"OK: {nl} leaves, every move legal, every donor branch present")
