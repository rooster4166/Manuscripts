"""Adversarial search for far-apart instances at d(z) = 6 without admissible chains.

J: z joined to v_1..v_6; each v_i has private neighbours (pairwise distinct, so N(z) is pairwise
at distance >= 3 in H = J - z); the outer vertices are wired at random (configuration model)
with all degrees of J odd except z, and J 3-connected.  For each r in N(z) we look for a labelling
with r = y_1 (y_1 carries no walk condition) -- and, failing that, r = y_2 or y_3 -- and an
admissible chain, searched exactly: every simple path P2 (y3 -> x2 in H - N[x3] - {x1, y2}, other
vertices off N(x3)), then a BFS for P1 (y2 -> x1 in H - N[x2] - N[x3]) avoiding the edges of P2.

usage: chain_search.py COUNT SEED EXTRA [DEG_PRIVATE [BRIDGES]]
  EXTRA: number of extra outer vertices of degree 3; DEG_PRIVATE: degree of the private
  neighbours (default 3).  BRIDGES > 0: two halves (three neighbours of z each) wired separately
  and joined by BRIDGES edges, so that J - z has a small edge cut while J may be 3-connected.
Prints a summary and every instance (graph6 of J, z = 0) with some r uncovered.
"""
import sys, random, itertools
from collections import deque
import networkx as nx


def simple_paths(H, s, t, allowed, limit=200000):
    """all simple paths s -> t with inner vertices and s satisfying allowed (t exempt)."""
    out = []
    stack = [(s, [s])]
    while stack and len(out) < limit:
        v, path = stack.pop()
        for w in H[v]:
            if w in path:
                continue
            if w == t:
                out.append(path + [t])
                continue
            if not allowed(w):
                continue
            stack.append((w, path + [w]))
    return out


def bfs(H, s, t, allowed, banned):
    prev = {s: None}
    q = deque([s])
    while q:
        v = q.popleft()
        if v == t:
            return True
        for w in H[v]:
            if w in prev or frozenset((v, w)) in banned:
                continue
            if w != t and not allowed(w):
                continue
            prev[w] = v
            q.append(w)
    return False


def has_chain(H, X, Y):
    x1, x2, x3 = X
    y1, y2, y3 = Y
    N2 = set(H[x2]) | {x2}
    N3 = set(H[x3]) | {x3}
    if y2 in N3 or y3 in N3 or x2 in N3:
        return False
    for P2 in simple_paths(H, y3, x2, lambda w: w not in N3 and w not in (x1, y2, x2)):
        used = {frozenset(e) for e in zip(P2, P2[1:])}
        if bfs(H, y2, x1, lambda w: w not in N2 and w not in N3 and w != x1, used):
            return True
    return False


FALLBACK = [0]


def covered(H, Nz):
    cov = set()
    for r in Nz:
        rest = [v for v in Nz if v != r]
        done = False
        # r = y1 first: x1 any other, then pair the remaining four
        for x1 in rest:
            four = [v for v in rest if v != x1]
            for a, b, c, d in itertools.permutations(four):
                if not (a < c or True):
                    continue
                X, Y = [x1, a, c], [r, b, d]
                if has_chain(H, X, Y):
                    done = True
                    break
            if done:
                break
        if not done:
            FALLBACK[0] += 1
            # r as y2 or y3
            for perm in itertools.permutations(rest):
                x1, y1, x2, x3, y3 = perm
                if has_chain(H, [x1, x2, x3], [y1, r, y3]):
                    done = True
                    break
                x1, y1, x2, y2, x3 = perm
                if has_chain(H, [x1, x2, x3], [y1, y2, r]):
                    done = True
                    break
        if done:
            cov.add(r)
    return cov


def build(rng, extra, dpriv):
    # vertices: 0 = z, 1..6 = v_i, then 12 private (two per v_i), then extra
    n = 7 + 12 + extra
    G = nx.Graph()
    G.add_nodes_from(range(n))
    for i in range(1, 7):
        G.add_edge(0, i)
    priv = {}
    k = 7
    for i in range(1, 7):
        priv[i] = [k, k + 1]
        for p in priv[i]:
            G.add_edge(i, p)
        k += 2
    stubs = []
    for p in range(7, 19):
        stubs += [p] * (dpriv - 1)
    for e in range(19, n):
        stubs += [e] * 3
    if len(stubs) % 2:
        return None
    rng.shuffle(stubs)
    for u, v in zip(stubs[::2], stubs[1::2]):
        if u == v or G.has_edge(u, v):
            return None
        G.add_edge(u, v)
    if any(G.degree(v) % 2 == 0 for v in G if v != 0):
        return None
    if nx.node_connectivity(G) < 3:
        return None
    return G


def build_halves(rng, extra, bridges):
    """Two halves, each with three neighbours of z, their private pairs and extra/2 extra
    vertices, wired at random inside the half; `bridges` edges between the halves."""
    G = build_parts(rng, extra, bridges)
    return G


def build_parts(rng, extra, bridges):
    n = 7 + 12 + extra
    G = nx.Graph()
    G.add_nodes_from(range(n))
    for i in range(1, 7):
        G.add_edge(0, i)
    k = 7
    side = {}
    for i in range(1, 7):
        for p in (k, k + 1):
            G.add_edge(i, p)
            side[p] = 0 if i <= 3 else 1
        k += 2
    for j, e in enumerate(range(19, n)):
        side[e] = j % 2
    stubs = {0: [], 1: []}
    for p in range(7, 19):
        stubs[side[p]] += [p, p]
    for e in range(19, n):
        stubs[side[e]] += [e] * 3
    # bridges: take one stub from each side per bridge
    for _ in range(bridges):
        if not stubs[0] or not stubs[1]:
            return None
        u = stubs[0].pop(rng.randrange(len(stubs[0])))
        v = stubs[1].pop(rng.randrange(len(stubs[1])))
        if G.has_edge(u, v):
            return None
        G.add_edge(u, v)
    for sd in (0, 1):
        st = stubs[sd]
        if len(st) % 2:
            return None
        rng.shuffle(st)
        for u, v in zip(st[::2], st[1::2]):
            if u == v or G.has_edge(u, v):
                return None
            G.add_edge(u, v)
    if any(G.degree(v) % 2 == 0 for v in G if v != 0):
        return None
    if nx.node_connectivity(G) < 3:
        return None
    return G


def main():
    count, seed, extra = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    dpriv = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    halves = int(sys.argv[5]) if len(sys.argv) > 5 else 0   # > 0: two halves, this many bridges
    rng = random.Random(seed)
    made = bad = 0
    tries = 0
    while made < count and tries < 1000 * count:
        tries += 1
        G = build_parts(rng, extra, halves) if halves else build(rng, extra, dpriv)
        if G is None:
            continue
        made += 1
        H = G.copy()
        H.remove_node(0)
        Nz = list(range(1, 7))
        cov = covered(H, Nz)
        if len(cov) < 6:
            bad += 1
            print('UNCOVERED', nx.to_graph6_bytes(G, header=False).decode().strip(),
                  'missing', sorted(set(Nz) - cov), flush=True)
    print(f'SUMMARY extra={extra} dpriv={dpriv} graphs={made} uncovered={bad} '
          f'r_needing_y2_or_y3={FALLBACK[0]} tries={tries}', flush=True)


if __name__ == '__main__':
    main()
