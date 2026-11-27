"""revcheck.py -- audit A21: for every FAIL line of an authors' exhaustive list, is xy terminal at y?

usage: python3 revcheck.py FAILFILE
ts runs with node budget 3e5 and 100 shuffled attempts, then one attempt of budget 2e9; d(y) = 1
is trivially terminal.  Prints counts of 1 (terminal at y), 0 (not), 2 (undecided)."""
import sys, os, subprocess, collections
import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
P = subprocess.Popen([os.path.join(HERE, "ts"), "300000", "100"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
P2 = subprocess.Popen([os.path.join(HERE, "ts"), "2000000000", "1"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
C = collections.Counter()
for line in open(sys.argv[1]):
    if not line.startswith("FAIL"):
        continue
    p = line.split()
    kv = dict(t.split("=") for t in p[2:5])
    G = nx.from_graph6_bytes(p[1].encode())
    x, y = int(kv["x"]), int(kv["y"])
    if G.degree(y) < 3:
        C["terminal_at_y=1 (d(y)=1)"] += 1
        continue
    E = list(G.edges())
    q = f"{G.number_of_nodes()} {len(E)} " + " ".join(f"{a} {b}" for a, b in E) + f" T {y} {x}\n"
    P.stdin.write(q); P.stdin.flush(); r = int(P.stdout.readline())
    if r == 2:
        P2.stdin.write(q); P2.stdin.flush(); r = int(P2.stdout.readline())
    C[f"terminal_at_y={r}"] += 1
    if r != 1:
        print("REV", r, line.strip(), flush=True)
print(dict(C))
