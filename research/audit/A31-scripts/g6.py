"""Minimal graph6 helpers for the A31 audit (independent of the re-tight scripts)."""


def parse_g6(s):
    s = s.strip()
    n = ord(s[0]) - 63
    assert 0 <= n < 63
    adj = [set() for _ in range(n)]
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        for b in range(5, -1, -1):
            bits.append((v >> b) & 1)
    p = 0
    for j in range(1, n):
        for i in range(j):
            if bits[p]:
                adj[i].add(j)
                adj[j].add(i)
            p += 1
    return n, adj


def to_g6(n, adj):
    bits = []
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if j in adj[i] else 0)
    while len(bits) % 6:
        bits.append(0)
    out = chr(n + 63)
    for p in range(0, len(bits), 6):
        v = 0
        for b in bits[p:p + 6]:
            v = 2 * v + b
        out += chr(v + 63)
    return out


def edges(n, adj):
    return [(i, j) for i in range(n) for j in adj[i] if i < j]


def connected_without(n, adj, removed):
    vs = [v for v in range(n) if v not in removed]
    if not vs:
        return True
    seen = {vs[0]}
    st = [vs[0]]
    while st:
        v = st.pop()
        for w in adj[v]:
            if w not in removed and w not in seen:
                seen.add(w)
                st.append(w)
    return len(seen) == len(vs)


def two_connected(n, adj):
    if n < 3 or not connected_without(n, adj, set()):
        return False
    return all(connected_without(n, adj, {v}) for v in range(n))


def degenerate_at_most(n, adj, d):
    deg = [len(a) for a in adj]
    alive = set(range(n))
    changed = True
    while alive and changed:
        changed = False
        for v in list(alive):
            if deg[v] <= d:
                alive.discard(v)
                for w in adj[v]:
                    if w in alive:
                        deg[w] -= 1
                changed = True
    return not alive


def is_forest(vs, adj):
    """vs: vertex set; induced subgraph."""
    vs = set(vs)
    m = sum(1 for v in vs for w in adj[v] if w in vs) // 2
    comp = 0
    seen = set()
    for v in vs:
        if v in seen:
            continue
        comp += 1
        seen.add(v)
        st = [v]
        while st:
            x = st.pop()
            for y in adj[x]:
                if y in vs and y not in seen:
                    seen.add(y)
                    st.append(y)
    return m == len(vs) - comp
