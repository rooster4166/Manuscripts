"""Exhaustive recheck of 'NO BASE' roots: for every data choice and orientation, run the exact
per-end avoidance query (no budget) and report found / proved-absent / undecided."""
import ast
import itertools
import subprocess
import sys

import networkx as nx

ORACLE = sys.argv[1]
BUDGET = int(sys.argv[3]) if len(sys.argv) > 3 else 0


def pms(vs, J):
    if not vs:
        yield []
        return
    a = vs[0]
    for b in vs[1:]:
        if J.has_edge(a, b):
            for pm in pms([v for v in vs[1:] if v != b], J):
                yield [(a, b)] + pm


def run(lines):
    p = subprocess.run([ORACLE], input="\n".join(lines) + "\n", capture_output=True, text=True)
    return p.stdout.strip().split("\n")


for line in open(sys.argv[2]):
    if not line.startswith("NO BASE"):
        continue
    head, rest = line.split("[", 1)
    edges = ast.literal_eval("[" + rest.rsplit("]", 1)[0] + "]")
    r = int(line.rsplit("r", 1)[1])
    J = nx.Graph(edges)
    n = J.number_of_nodes()
    U = sorted(J.neighbors(0))
    verdict = "ABSENT"
    for w in U:
        if w == r:
            continue
        restU = [u for u in U if u not in (r, w)]
        for pairs in pms(restU, J):
            M = J.copy()
            M.remove_edges_from([(0, w)] + [(0, x) for p in pairs for x in p] + pairs)
            E = list(M.edges())
            b = [M.degree(v) % 2 for v in range(n)]
            qs = []
            for cb in itertools.product([0, 1], repeat=len(pairs)):
                xs = [0] * n
                for (a, bb), o in zip(pairs, cb):
                    if o == 0:
                        xs[bb] |= 1 << a
                    else:
                        xs[a] |= 1 << bb
                q = "AB %d %d %s %s %s 3 %d" % (n, len(E), " ".join("%d %d" % e for e in E),
                                              " ".join(map(str, b)), " ".join(map(str, xs)), BUDGET)
                qs.append(q)
            out = run(qs)
            if any(o.strip() == "1" for o in out):
                verdict = "FOUND w=%d pairs=%s" % (w, pairs)
                break
            if any(o.strip() == "2" for o in out):
                verdict = "UNDECIDED"
        if verdict.startswith("FOUND"):
            break
    print("n=%d r=%d m=%d: %s" % (n, r, J.number_of_edges(), verdict), flush=True)
