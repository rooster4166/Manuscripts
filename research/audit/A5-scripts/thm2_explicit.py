# Explicit Theorem-2 construction for the CP-SAT timeout instance J=K7, P=1-100-6
import sys, itertools
sys.path.insert(0, '/home/user/Manuscripts/tools')
import networkx as nx
from pathnum import verify_partition
from rainbow import ham_cycles
n = 7
allE = frozenset(frozenset(e) for e in itertools.combinations(range(n), 2))
marks = [frozenset((1, 6)), frozenset((6, 0)), frozenset((0, 2))]
def find(i, rem, acc):
    if i == 3: return acc if not rem else None
    for H in ham_cycles(n, rem):
        if marks[i] in H and all(marks[j] not in H for j in range(3) if j != i):
            r = find(i + 1, rem - H, acc + [H])
            if r: return r
    return None
cyc = find(0, allE, [])
def open_at(H, e):
    a, b = tuple(e); adj = {}
    for f in H:
        if f == e: continue
        x, y = tuple(f); adj.setdefault(x, []).append(y); adj.setdefault(y, []).append(x)
    path = [a]; prev = None
    while len(path) < n:
        nxt = [w for w in adj[path[-1]] if w != prev][0] if prev is not None else adj[a][0]
        prev = path[-1]; path.append(nxt)
    assert path[-1] == b; return path
r16 = open_at(cyc[0], marks[0]); r60 = open_at(cyc[1], marks[1]); r02 = open_at(cyc[2], marks[2])
R = [100, 1, 6, 0, 2]                 # R = 1-6-0-2 with half 100-1 attached at 1
row16 = r16 + [100] if r16[-1] == 6 else [100] + r16   # half 6-100 attached at 6
paths = [tuple(R), tuple(row16), tuple(r60), tuple(r02)]
G = nx.complete_graph(7); G.add_edges_from([(1, 100), (100, 6)])
ends = [v for p in paths for v in (p[0], p[-1])]
print(paths); print("valid partition:", verify_partition(G, paths), "ends include 1 and 6:", 1 in ends and 6 in ends, "count:", len(paths))
