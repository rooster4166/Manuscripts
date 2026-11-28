"""h_2conn8.py (audit A37): forest base at the 126 order-8 instances with delta >= 3 that are
2- but not 3-connected (generated here), via tb2.process, every witness re-checked by e_tb2.own_check."""
import subprocess, sys, random
from collections import Counter
sys.path.insert(0, "."); sys.path.insert(1, "/home/user/Manuscripts/manuscripts/test2/scripts")
import networkx as nx, tb2
from a37lib import adjacency, g6_decode, kconn, t2_instances
from e_tb2 import own_check
o = tb2.Oracle("/tmp/claude-0/-home-user-Manuscripts/35215522-7df9-5b9a-9b8c-701ec9122b7b/scratchpad/route_ext"); st = Counter()
for g6 in subprocess.run(["nauty-geng", "-q", "-c", "-d3", "8"], capture_output=True, text=True).stdout.split():
    n, E = g6_decode(g6); A = adjacency(n, E)
    if not t2_instances(n, E) or kconn(n, A, 3) or not kconn(n, A, 2): continue
    for z, r in t2_instances(n, E):
        tier, wit, nq, und = tb2.process(o, nx.from_graph6_bytes(g6.encode()), z, r, 0, tb2.XDIM, random.Random(1))
        st[("tier", tier)] += 1
        if wit: st[("own check", own_check(g6, z, r, *wit))] += 1
print(dict(st))
