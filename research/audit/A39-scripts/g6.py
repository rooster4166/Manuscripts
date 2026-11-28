"""Own graph6 parser (no networkx). Returns (n, adjacency as list of sets)."""


def parse_g6(s):
    s = s.strip()
    data = [ord(c) - 63 for c in s]
    if data[0] == 63:  # long form (n >= 63)
        n = (data[1] << 12) | (data[2] << 6) | data[3]
        bits = data[4:]
    else:
        n = data[0]
        bits = data[1:]
    adj = [set() for _ in range(n)]
    k = 0
    for j in range(1, n):
        for i in range(j):
            byte, off = divmod(k, 6)
            if (bits[byte] >> (5 - off)) & 1:
                adj[i].add(j)
                adj[j].add(i)
            k += 1
    return n, adj


def J_from_resid(s):
    """residual format: graph6 of B with N(z) = {0..5}; J = B + z (z = new last vertex)."""
    n, adj = parse_g6(s)
    adj = [set(a) for a in adj] + [set(range(6))]
    for u in range(6):
        adj[u].add(n)
    return n + 1, adj
