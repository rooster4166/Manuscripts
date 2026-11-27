"""helpers copied from walkcheck.py"""
def adm_walks(n, A, a, b, x, y):
    """all admissible y->a paths, grouped by length"""
    res = []

    def dfs(c, path, vis):
        if c == a:
            res.append(list(path))
            return
        for w in range(n):
            if A[c][w] and not vis >> w & 1 and w not in (b, x):
                if w != a and A[w][x]:
                    continue
                path.append(w)
                dfs(w, path, vis | 1 << w)
                path.pop()
    dfs(y, [y], 1 << y)
    return res


def base_graph(n, A, a, b, x, y, P):
    B = [row[:] + [0] for row in A] + [[0] * (n + 1)]
    for u, v in ((a, b), (x, y)) + tuple(zip(P, P[1:])):
        B[u][v] = B[v][u] = 0
    B[n][b] = B[b][n] = 1
    return B


def packed(B, u, v):
    return not B[u][v] and not any(B[u][w] and B[w][v] for w in range(len(B)))


def sparse_ok_in(B, X):
    if any(sum(B[v][p] for p in X) > 1 for v in range(len(B))):
        return False
    x, y, a, l1 = X
    return packed(B, x, y) and packed(B, a, l1) and packed(B, l1, y)


def sparse_hyp(B, X):
    if sparse_ok_in(B, X):
        return True
    x = X[0]
    for v in range(len(B)):
        if B[x][v] and v not in X:
            B[x][v] = B[v][x] = 0
            ok = sparse_ok_in(B, X)
            B[x][v] = B[v][x] = 1
            if ok:
                return True
    return False


