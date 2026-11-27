"""cpsat_check.py FILE: independent CP-SAT check (tools/pathnum2.py, circuit model) of rooted
path numbers.  Each input line is 'g6 r p'.  For each, CP-SAT must find a decomposition into p
paths with at least two ends at r (FEASIBLE/OPTIMAL) and prove that p - 1 paths are impossible
(INFEASIBLE).  Prints one line per instance and a summary.
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..",
                                "tools"))
import networkx as nx  # noqa: E402
from pathnum2 import decompose  # noqa: E402

agree = disagree = 0
for line in open(sys.argv[1]):
    g6, r, p = line.split()
    r, p = int(r), int(p)
    G = nx.from_graph6_bytes(g6.encode())
    st_hi, _ = decompose(G, p, min_ends={r: 2}, time_limit=600, workers=1)
    st_lo, _ = decompose(G, p - 1, min_ends={r: 2}, time_limit=600, workers=1)
    ok = st_hi in ("OPTIMAL", "FEASIBLE") and st_lo == "INFEASIBLE"
    agree += ok
    disagree += not ok
    print(g6, r, p, st_hi, st_lo, "AGREE" if ok else "DISAGREE", flush=True)
print("# agree", agree, "disagree", disagree)
