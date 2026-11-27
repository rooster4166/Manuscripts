"""(*) and (**) of re-tight Theorem 3.1, from the definitions (adjacency-list input)."""


def h(adj, r, t):
    return sum(1 for x in adj[r] if len(adj[x]) >= 2 * t)


def star(n, adj, r):
    k = n // 2
    return all(h(adj, r, t) // 2 <= k + 1 - t for t in range(3, k))


def star2(n, adj, r):
    k = n // 2
    for t in range(3, k):
        if not (h(adj, r, t) // 2 <= k + 1 - t or h(adj, r, t + 1) // 2 <= k + 1 - 2 * t):
            return False
    return True
