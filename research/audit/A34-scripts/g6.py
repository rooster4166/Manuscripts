"""g6.py: tiny graph6 helper (audit A34)."""
def parse(s):
    s = s.strip(); n = ord(s[0]) - 63; bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        bits += [(v >> k) & 1 for k in range(5, -1, -1)]
    adj = [set() for _ in range(n)]; p = 0
    for j in range(1, n):
        for i in range(j):
            if bits[p]: adj[i].add(j); adj[j].add(i)
            p += 1
    return n, adj
def edges(adj):
    return sorted((a, b) for a in range(len(adj)) for b in adj[a] if a < b)
