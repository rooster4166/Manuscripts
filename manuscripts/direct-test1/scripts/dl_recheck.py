"""dl_recheck.py: exact (budget 0) recheck of the UNDEC lines of dl_rand.py, with a time limit
per instance (session claude/triangle-base).  usage: dl_recheck.py ORACLE LOG [TIMEOUT_S]"""
import ast
import itertools
import subprocess
import sys

import networkx as nx

from tb import avoid_query

oracle, log = sys.argv[1], sys.argv[2]
tmo = int(sys.argv[3]) if len(sys.argv) > 3 else 1800
for line in open(log):
    if not line.startswith("UNDEC"):
        continue
    _, g6, g, rest = line.split(" ", 3)
    pairs = ast.literal_eval(rest.strip())
    G = nx.from_graph6_bytes(g6.encode())
    n = G.number_of_nodes()
    verdict = "ABSENT"
    for cb in itertools.product([0, 1], repeat=len(pairs)):
        av = {}
        for (a, b), o in zip(pairs, cb):
            av.setdefault(b if o == 0 else a, set()).add(a if o == 0 else b)
        try:
            p = subprocess.run([oracle], input=avoid_query(G, n, av, 0, witness=False) + "\n",
                               capture_output=True, text=True, timeout=tmo)
            o = p.stdout.strip()
        except subprocess.TimeoutExpired:
            o = "T"
        if o == "1":
            verdict = "FOUND"
            break
        if o == "T":
            verdict = "TIMEOUT"
    print(verdict, g6, g, pairs, flush=True)
