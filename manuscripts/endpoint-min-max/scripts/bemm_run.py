"""Realisability of the balanced cut-feasible half-sets of G_18 (connections §T.result-4).
Usage: python3 bemm_run.py REALIS_WIDE_BIN MASK_FILE   (masks from balance.c; 4 threads, 120 s per query)
"""
import sys, subprocess, networkx as nx
from concurrent.futures import ThreadPoolExecutor
BIN = sys.argv[1]; masks = [int(x) for x in open(sys.argv[2])]
G = nx.from_graph6_bytes(b"Q~?GW\\cCoP?@?A?A?@??N?@w?F_"); n = G.number_of_nodes(); E = list(G.edges())
enc = f"{n} {len(E)} " + " ".join(f"{a} {c}" for a, c in E)
def q(M):
    b = [1 if G.degree(v) % 2 else (2 if M >> v & 1 else 0) for v in range(n)]
    try:
        return M, subprocess.run([BIN], input="P " + enc + " " + " ".join(map(str, b)) + "\n", capture_output=True, text=True, timeout=120).stdout.strip()
    except subprocess.TimeoutExpired:
        return M, "timeout"
res = {}
with ThreadPoolExecutor(4) as ex:
    for i, (M, r) in enumerate(ex.map(q, masks)):
        res[r] = res.get(r, 0) + 1
        if r != "1": print("NOT-REALISED", M, r, flush=True)
        if i % 1000 == 999: print("progress", i + 1, res, flush=True)
print("FINAL", len(masks), res, flush=True)
