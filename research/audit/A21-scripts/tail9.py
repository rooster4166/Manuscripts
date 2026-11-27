"""tail9.py -- audit A21: finish the order-9 exhaustive run on the dense tail with a node budget.

usage: python3 tail9.py SLICE START WORKER NWORKERS BUDGET ROUNDS BUDGET2

Processes the graphs with exactly one positive even vertex in `nauty-geng -cq 9 SLICE`, numbered
1, 2, ... in geng order, from number START on, taking those with (number - START) % NWORKERS ==
WORKER.  Same EE and away queries as exhaust.py; ts runs with node budget BUDGET per attempt and up
to ROUNDS attempts with shuffled incidence orders; a query still undecided is asked again with one
attempt of node budget BUDGET2.  So each answer is
1 (exact success), 0 (exact failure) or 2 (undecided).  Prints counts and one line per failure or
undecided query."""
import sys, os, subprocess, collections
import networkx as nx
from exhaust import reachable

HERE = os.path.dirname(os.path.abspath(__file__))
sl, start, wk, nw = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
budget, rounds, budget2 = sys.argv[5], sys.argv[6], sys.argv[7]
P = subprocess.Popen([os.path.join(HERE, "ts"), budget, rounds], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
P2 = subprocess.Popen([os.path.join(HERE, "ts"), budget2, "1"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)


def ask(G, q):
    E = list(G.edges())
    line = f"{G.number_of_nodes()} {len(E)} " + " ".join(f"{a} {b}" for a, b in E) + " " + q + "\n"
    P.stdin.write(line); P.stdin.flush()
    r = int(P.stdout.readline())
    if r == 2:
        P2.stdin.write(line); P2.stdin.flush()
        r = int(P2.stdout.readline())
    return r


C = collections.Counter()
num = 0
geng = subprocess.Popen(["nauty-geng", "-cq", "9", sl], stdout=subprocess.PIPE, text=True)
for line in geng.stdout:
    g6 = line.strip()
    G = nx.from_graph6_bytes(g6.encode())
    ev = [v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0]
    if len(ev) != 1:
        continue
    num += 1
    if num < start or (num - start) % nw != wk:
        continue
    z = ev[0]
    C["graphs"] += 1
    d = dict(G.degree())
    for u in sorted(G[z]):
        if d[u] < 3:
            continue
        C["EE:tests"] += 1
        r = ask(G, f"T {u} {z}")
        if r != 1:
            C[f"EE:{r}"] += 1
            print("EE", r, g6, z, u, flush=True)
    for x in sorted(G):
        if x == z or d[x] < 3:
            continue
        for y in sorted(G[x]):
            if y == z:
                continue
            C["away:tests"] += 1
            rc = reachable(G, z, x, y)
            C["away:reachable" if rc else "away:unreachable"] += 1
            r = ask(G, f"T {x} {y}")
            if r == 1:
                continue
            C[f"away:{'fail' if r == 0 else 'undecided'}"] += 1
            C[f"away:{'fail' if r == 0 else 'undecided'}_{'reachable' if rc else 'unreachable'}"] += 1
            print("AWAY", r, g6, z, x, y, "reach" if rc else "unreach", flush=True)
print("TAILDONE", dict(C), flush=True)
