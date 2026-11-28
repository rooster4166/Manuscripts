"""Example 5.2 (the wheel EUZw): independent check of every claim."""
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import indep

G0 = indep.read_g6("EUZw")
hub = [v for v in G0 if len(G0[v]) == 5]
assert len(hub) == 1, G0
h = hub[0]
rim = [v for v in G0 if v != h]
assert all(len(G0[v]) == 3 for v in rim)
# order the rim cyclically starting from some rim vertex
start = rim[0]
order = [start]
while len(order) < 5:
    cur = order[-1]
    nxt = [v for v in G0[cur] if v != h and v not in order]
    order.append(sorted(nxt)[0])
lab = {h: "y"}
for i, v in enumerate(order):
    lab[v] = i + 1
G = {lab[v]: {lab[w] for w in G0[v]} for v in G0}
print("wheel:", {k: sorted(map(str, v)) for k, v in G.items()})
x, y, l = 1, "y", "l"
K = {v: set(N) for v, N in G.items()}
K[y].add(l)
K[l] = {y}
X = {x, l}
H = {v: ({w for w in K[v] if w not in X} if v not in X else set()) for v in K}
oddH = sorted(str(v) for v in H if len(H[v]) % 2 == 1)
print("odd in H:", oddH, " d_H(y) =", len(H[y]))
assert oddH == ["3", "4"] and len(H[y]) == 4


def is_steer(K, X, W):
    es = [frozenset(p) for p in zip(W, W[1:])]
    if len(set(es)) != len(es):
        return False
    if any(g in X for g in W[1:]):
        return False
    if any(b not in K[a] for a, b in zip(W, W[1:])):
        return False
    rem = {v: set(N) for v, N in K.items()}
    for a, b in zip(W, W[1:]):
        rem[a].discard(b)
        rem[b].discard(a)
    return len(rem[W[-1]]) == 0, rem


W = ["y", 2, 3, 4, "y", 3]
ok, rem = is_steer(K, X, W)
assert ok
E5 = sorted(sorted(map(str, e)) for e in {frozenset((a, b)) for a in rem for b in rem[a]})
print("K_5 edges:", E5)
degs = {str(v): len(rem[v]) for v in rem}
print("K_5 degrees:", degs, "(vertex 3 has degree 0, so 'all degrees odd' is inaccurate)")

# all steering sequences from y avoiding X
seqs = []


def dfs(W, rem):
    cur = W[-1]
    if len(W) >= 2 and not rem[cur]:
        seqs.append(list(W))
        return  # g_k isolated: the sequence must stop here (no edge left at g_k)
    for c in sorted(rem[cur], key=str):
        if c in X:
            continue
        rem[cur].discard(c)
        rem[c].discard(cur)
        W.append(c)
        dfs(W, rem)
        W.pop()
        rem[cur].add(c)
        rem[c].add(cur)


dfs(["y"], {v: set(N) for v, N in K.items()})
print("number of steering sequences:", len(seqs))
print("ends:", sorted(set(str(s[-1]) for s in seqs)))
print("all return to y:", all("y" in s[1:] for s in seqs))
assert all("y" in s[1:] for s in seqs)
# the NA instance is good and the general claim
print("NA instance good (independent solver):", indep.good(G, y, {x}))
# the hub as x: Theorem 1.4 example
print("x = hub, y = rim 1: good?", indep.good(G, 1, {"y"}), "weak?", indep.weak(G, 1, {"y"}))
