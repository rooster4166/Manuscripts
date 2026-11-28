"""randae.py -- random AE instances of order N with t = |N(g) ∩ N(c)| >= 2 (ae session).
H = G(N-1, p) with p uniform in [0.25, 0.6]; K = H + g joined to the even-degree vertices of H
(so g is the only even vertex of K); keep K connected with d(g) >= 2; c odd, c not adjacent to g,
t >= 2.  Prints graph6 lines (one per distinct sampled graph) to stdout; cfrun.py then treats every
admissible c of each graph.  usage: randae.py N COUNT SEED"""
import sys, random
N, cnt, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed)
def g6(n, adj):
    bits = []
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if j in adj[i] else 0)
    while len(bits) % 6: bits.append(0)
    s = chr(63 + n)
    for k in range(0, len(bits), 6):
        v = 0
        for b in bits[k:k + 6]: v = 2 * v + b
        s += chr(63 + v)
    return s
out = 0
while out < cnt:
    p = rng.uniform(0.25, 0.6)
    n = N; adj = [set() for _ in range(n)]
    for i in range(N - 1):
        for j in range(i + 1, N - 1):
            if rng.random() < p: adj[i].add(j); adj[j].add(i)
    ev = [v for v in range(N - 1) if len(adj[v]) % 2 == 0]
    if len(ev) < 2: continue
    for v in ev: adj[N - 1].add(v); adj[v].add(N - 1)
    seen = {0}; st = [0]
    while st:
        u = st.pop()
        for v in adj[u]:
            if v not in seen: seen.add(v); st.append(v)
    if len(seen) < n: continue
    g = N - 1
    if not any(c != g and c not in adj[g] and len(adj[c]) % 2 == 1 and len(adj[g] & adj[c]) >= 2 for c in range(n)):
        continue
    print(g6(n, adj)); out += 1
