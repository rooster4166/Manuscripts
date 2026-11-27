"""brute.py: independent brute force for DL(1) (session claude/dl-one).

Enumerates every Lovasz decomposition of a small graph through transition systems: at each vertex
v the incident edges are split into pairs (passages) and d(v) mod 2 singletons (ends).  A
transition system determines a set of trails and closed trails; it is a path decomposition iff
every piece is an open trail with no repeated vertex.  This is independent of dl.c (which grows
paths by depth-first search with memoisation and Lovasz's theorem as a shortcut).

usage: python3 brute.py FILE.g6 [maxprod]   -> prints per graph: g6 | g | a b ob oa ,...
"""
import sys
import itertools


def g6_decode(s):
    s = s.strip()
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        for k in range(5, -1, -1):
            bits.append((v >> k) & 1)
    edges = []
    p = 0
    for j in range(1, n):
        for i in range(j):
            if bits[p]:
                edges.append((i, j))
            p += 1
    return n, edges


def pairings(items, nsing):
    """all ways to split items into pairs and exactly nsing singletons"""
    items = list(items)
    if not items:
        if nsing == 0:
            yield [], []
        return
    first, rest = items[0], items[1:]
    if nsing > 0:
        for pr, sg in pairings(rest, nsing - 1):
            yield pr, [first] + sg
    for i in range(len(rest)):
        other = rest[i]
        rest2 = rest[:i] + rest[i + 1:]
        for pr, sg in pairings(rest2, nsing):
            yield [(first, other)] + pr, sg


def decomps(n, edges):
    inc = [[] for _ in range(n)]
    for k, (u, v) in enumerate(edges):
        inc[u].append(k)
        inc[v].append(k)
    choices = []
    for v in range(n):
        d = len(inc[v])
        choices.append(list(pairings(inc[v], d % 2)))
    for combo in itertools.product(*choices):
        # partner[(v, e)] = the other edge at v paired with e, or None (end)
        partner = {}
        for v in range(n):
            pr, sg = combo[v]
            for e1, e2 in pr:
                partner[(v, e1)] = e2
                partner[(v, e2)] = e1
            for e in sg:
                partner[(v, e)] = None
        seen = set()
        paths = []
        ok = True
        for v in range(n):
            pr, sg = combo[v]
            for e0 in sg:
                if e0 in seen:
                    continue
                # walk from v along e0
                verts = [v]
                cur, e = v, e0
                while True:
                    seen.add(e)
                    a, b = edges[e]
                    nxt = b if a == cur else a
                    verts.append(nxt)
                    pe = partner[(nxt, e)]
                    if pe is None:
                        break
                    cur, e = nxt, pe
                paths.append(verts)
        if len(seen) != len(edges):
            continue  # some closed trail
        for P in paths:
            if len(set(P)) != len(P):
                ok = False
                break
        if ok:
            yield paths


def main():
    maxprod = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 7
    for line in open(sys.argv[1]):
        line = line.strip()
        if not line:
            continue
        n, edges = g6_decode(line)
        deg = [0] * n
        for u, v in edges:
            deg[u] += 1
            deg[v] += 1
        ev = [v for v in range(n) if deg[v] > 0 and deg[v] % 2 == 0]
        if len(ev) > 1:
            print(line, "skip")
            continue
        prod = 1
        for d in deg:
            for k in range(d - 1 if d % 2 == 0 else d, 0, -2):
                prod *= k
        if prod > maxprod:
            print(line, "toolarge")
            continue
        adj = set()
        for u, v in edges:
            adj.add((u, v))
            adj.add((v, u))
        odd = [v for v in range(n) if deg[v] % 2 == 1]
        pairs = [(a, b) for a, b in itertools.combinations(odd, 2) if (a, b) not in adj]
        res = {p: [0, 0] for p in pairs}
        nd = 0
        for paths in decomps(n, edges):
            nd += 1
            Q = {}
            for P in paths:
                Q[P[0]] = set(P)
                Q[P[-1]] = set(P)
            for (a, b) in pairs:
                if a not in Q[b]:
                    res[(a, b)][0] = 1
                if b not in Q[a]:
                    res[(a, b)][1] = 1
        out = "%s ; %d ;" % (line, ev[0] if ev else -1)
        for (a, b) in pairs:
            out += " %d %d %d %d," % (a, b, res[(a, b)][0], res[(a, b)][1])
        print(out, "ndec=%d" % nd, flush=True)


if __name__ == "__main__":
    main()
