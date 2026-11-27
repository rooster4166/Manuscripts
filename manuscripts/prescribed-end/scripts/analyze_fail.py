"""Classify the PEE failures printed by `pee g6` (lines 'FAIL g6 x=.. y=.. z=.. away').

For each failing (x, y) away from z it records local features and whether the reverse
prescription (xy terminal at y) and a few weakenings hold."""
import sys, subprocess, os, collections
import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
P = subprocess.Popen([os.path.join(HERE, "pee"), "ed"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)


def q(G, x, y):
    E = list(G.edges())
    P.stdin.write(f"{G.number_of_nodes()} {len(E)} " + " ".join(f"{a} {b}" for a, b in E) + f" {x} {y}\n")
    P.stdin.flush()
    return int(P.stdout.readline())


def main(path):
    feats = collections.Counter()
    rev = collections.Counter()
    graphs = set()
    examples = []
    for line in open(path):
        if not line.startswith("FAIL"):
            continue
        parts = line.split()
        g6 = parts[1]
        x = int(parts[2][2:]); y = int(parts[3][2:]); z = int(parts[4][2:])
        G = nx.from_graph6_bytes(g6.encode())
        graphs.add(g6)
        xz = G.has_edge(x, z); yz = G.has_edge(y, z)
        dx, dy, dz = G.degree(x), G.degree(y), G.degree(z)
        common = len(set(G[x]) & set(G[y]))
        f = (f"x~z={int(xz)}", f"y~z={int(yz)}", f"dz={dz}")
        feats[f] += 1
        r = q(G, y, x) if dy >= 3 else 1
        rev[r] += 1
        if len(examples) < 5:
            examples.append((g6, x, y, z, sorted(G.edges())))
    print("failing graphs:", len(graphs))
    print("features (x~z, y~z, d(z)):")
    for k, v in sorted(feats.items(), key=lambda t: -t[1]):
        print("  ", k, v)
    print("reverse (xy terminal at y) holds:", rev)
    for e in examples:
        print(e)


if __name__ == "__main__":
    main(sys.argv[1])
