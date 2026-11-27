"""cpsat_decide.py FILE TIMELIMIT: lines 'g6 r t'; decide with CP-SAT (tools/pathnum2.py) whether
the graph has a decomposition into at most t paths with at least two ends at r.  Prints the status
and, if feasible, the witness in the verify_witness.py format (with k = t)."""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..",
                                "tools"))
import networkx as nx  # noqa: E402
from pathnum2 import decompose  # noqa: E402

tl = float(sys.argv[2])
for line in open(sys.argv[1]):
    g6, r, t = line.split()
    r, t = int(r), int(t)
    G = nx.from_graph6_bytes(g6.encode())
    st, P = decompose(G, t, min_ends={r: 2}, time_limit=tl, workers=2)
    if P is not None:
        print(g6, r, len(P), t, "OK |", " | ".join(" ".join(map(str, p)) for p in P), "|",
              flush=True)
    else:
        print(g6, r, -1, t, st, flush=True)
