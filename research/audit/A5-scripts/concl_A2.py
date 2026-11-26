import sys, time, networkx as nx
from marked2 import q_all
n = int(sys.argv[1]); start = int(sys.argv[2]) if len(sys.argv) > 2 else 0
t = time.time(); cnt = 0; viol = []
lines = [l.strip() for l in open(f'/home/user/Manuscripts/data/conn{n}.g6') if l.strip()]
for j, line in enumerate(lines[start:], start):
    G = nx.from_graph6_bytes(line.encode())
    res = q_all(G)
    for S, v in res.items():
        if v > (n - len(S)) // 2: viol.append((line, sorted(S), v))
    cnt += 1
    if cnt % 50 == 0: print(f"  {j+1}/{len(lines)} viol={len(viol)} ({time.time()-t:.0f}s)", flush=True)
print(f"n={n}: graphs={cnt} violations={len(viol)} {viol[:3]} ({time.time()-t:.0f}s)", flush=True)
