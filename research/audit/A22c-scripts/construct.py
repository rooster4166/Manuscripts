"""Audit A22c: execute the proof of Theorem 8.2 step by step on concrete instances.

Each Fan step (Lemma 3.1, target g, source t) is realised by brute force: dsolve finds a
decomposition of the larger graph with end counts b + 1_g - 1_t in which every path lies inside
V(Q) + g for some path Q of the current decomposition (this is exactly what Lemma 3.1 promises and
all that the proof uses).  Before every Fan step we check the hypothesis the proof claims
(Z(g) empty and b(t) >= 1, computed in the current graph), and after each step of the proof we check
every vertex-set claim made in the text.  At the end we merge the leaves and verify the final
decomposition of G independently (Lovasz, x_i y_i terminal at x_i, three different paths).
Random seeds vary the base decomposition and every Fan step.

Vertices: G = 0..n-1, l1 = n, l2 = n+1, l3 = n+2 (a leaf is isolated until attached)."""
import random
from dlib import solve, check_decomp, check_constraints, endcount
from chain import base_graph, six_pairs, pedges


class ClaimFailed(Exception):
    pass


def claim(c, msg):
    if not c:
        raise ClaimFailed(msg)


def ends_of(D, N):
    return {v for v in range(N) if endcount(D, v) == 1}


def fan_step(N, edges, D, g, t, seed, log):
    """edges: current edge list (without gt).  D: decomposition of it.  Restore gt."""
    adj = {v: set() for v in range(N)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    b = {v: endcount(D, v) for v in range(N)}
    claim(all(x <= 1 for x in b.values()), 'end count > 1 before Fan step')
    Z = {w for w in adj[g] if b[w] == 0}
    claim(b[t] >= 1, f'Fan source {t} has no end')
    claim(not Z, f'Z({g}) = {sorted(Z)} nonempty (proof claims every neighbour of the target has an end)')
    claim(b[t] > len(Z), 'Fan hypothesis b(t) > |Z(g)| fails')
    new_edges = edges + [(g, t)]
    ends = {v for v in range(N) if b[v] + (v == g) - (v == t) == 1}
    claim(all(b[v] + (v == g) - (v == t) in (0, 1) for v in range(N)), 'end counts leave {0,1}')
    sets = [set(P[0]) | {g} for P in D]
    D2 = solve(N, new_edges, ends, sets=sets, seed=seed)
    claim(D2 is not None, f'no decomposition realising Lemma 3.1 at target {g}, source {t} (lemma or code wrong)')
    check_decomp(N, new_edges, D2, ends)
    check_constraints(D2, sets=sets)
    log.append(('fan', g, t))
    return new_edges, D2


def walk_back(N, edges, D, W, seed, log):
    """Lemma 3.4 along W = w0 .. wk; edges excludes E(W)."""
    rng = random.Random(seed)
    for i in range(len(W) - 1):
        edges, D = fan_step(N, edges, D, W[i], W[i + 1], rng.randrange(1 << 30), log)
    return edges, D


def path_with(D, v):
    c = [P for P in D if v in P[0]]
    return c


def leaf_extend(D, y, l):
    """extend the path ending at y by the leaf edge y-l"""
    out, done = [], False
    for vs, es in D:
        if not done and vs[-1] == y:
            out.append((vs + [l], es + [None])); done = True
        elif not done and vs[0] == y:
            out.append(([l] + vs, [None] + es)); done = True
        else:
            out.append((vs, es))
    claim(done, f'no path ends at {y}')
    return out


def renumber(N, edges, D):
    """re-attach edge ids of D (vertex sequences) to the edge list"""
    idx = {}
    for i, (a, b) in enumerate(edges):
        idx.setdefault(frozenset((a, b)), []).append(i)
    out = []
    for vs, _ in D:
        es = []
        for i in range(len(vs) - 1):
            k = frozenset((vs[i], vs[i + 1]))
            es.append(idx[k][0])
        out.append((vs, es))
    return out


def run(n, E, X, Y, P2, P1, seed=1):
    """execute the proof; returns the log, raises ClaimFailed on the first false claim"""
    rng = random.Random(seed)
    x1, x2, x3 = X; y1, y2, y3 = Y
    l1, l2, l3 = n, n + 1, n + 2
    N = n + 3
    T2 = set(P2[:-1]); T1 = set(P1[:-1])
    log = []
    # base decomposition
    el = base_graph(n, E, X, Y, P2, P1)
    deg = [0] * N
    for a, b in el:
        deg[a] += 1; deg[b] += 1
    ends0 = {v for v in range(N) if deg[v] % 2 == 1}
    claim(all(deg[v] % 2 == 1 or deg[v] == 0 or v == x3 for v in range(N)), 'parity claim after Def 8.1')
    D0 = solve(N, el, ends0, seps=six_pairs(X, Y, l1), seed=rng.randrange(1 << 30))
    if D0 is None:
        return None
    check_decomp(N, el, D0, ends0)
    claim(endcount(D0, x3) == 0, 'x3 has an end in D0')
    Q1 = path_with(D0, l1)[0]
    # Step 1
    Q3 = [P for P in D0 if P[0][0] == y3 or P[0][-1] == y3]
    claim(len(Q3) == 1, 'y3 has not exactly one end in D0')
    Q3 = Q3[0]
    claim(x3 not in Q3[0] and l1 not in Q3[0] and y2 not in Q3[0], 'Step 1: Q3 meets x3, l1 or y2')
    claim(Q3 is not Q1, 'Step 1: Q3 = Q1')
    V_Q3, V_Q1 = set(Q3[0]), set(Q1[0])
    D1 = leaf_extend(D0, y3, l3)
    edges = el + [(y3, l3)]
    D1 = renumber(N, edges, D1)
    check_decomp(N, edges, D1)
    claim(endcount(D1, y3) == 0 and endcount(D1, l3) == 1, 'Step 1 end counts')
    # Step 2: endless vertices claim
    endless = {v for v in range(N) if endcount(D1, v) == 0}
    isolated = {v for v in range(N) if not any(v in e for e in edges + [tuple(e) for e in pedges(P2)])}
    claim(endless <= {x3, y3} | isolated | {l2}, f'Step 2: unexpected endless vertices {endless - {x3, y3} - isolated}')
    edges, D2 = walk_back(N, edges, D1, P2, rng.randrange(1 << 30), log)
    claim(endcount(D2, x2) == 0 and endcount(D2, y3) == 1, 'Step 2 end counts')
    L3 = path_with(D2, l3); L1 = path_with(D2, l1)
    claim(len(L3) == 1 and len(L1) == 1 and L3[0] is not L1[0], 'Step 2: leaf paths')
    claim(set(L3[0][0]) <= V_Q3 | {l3} | T2, 'Step 2: l3-path not inside V(Q3)+l3+T2')
    claim(set(L1[0][0]) <= V_Q1 | T2, 'Step 2: l1-path not inside V(Q1)+T2')
    # Step 3
    claim(y2 not in T2, 'y2 in T2')
    claim(endcount(D2, y2) == 1, 'Step 3: y2 has no end')
    Q2 = [P for P in D2 if P[0][0] == y2 or P[0][-1] == y2][0]
    claim(Q2 is not L3[0] and Q2 is not L1[0], 'Step 3: Q2 is a leaf path')
    claim(x2 not in Q2[0] and l1 not in Q2[0] and l3 not in Q2[0], 'Step 3: Q2 meets x2, l1 or l3')
    V_Q2 = set(Q2[0])
    D3 = leaf_extend(D2, y2, l2)
    edges = edges + [(y2, l2)]
    D3 = renumber(N, edges, D3)
    check_decomp(N, edges, D3)
    V_L3_before = set(path_with(D3, l3)[0][0])
    claim(l2 not in V_L3_before, 'Step 3: l2 on the l3-path')
    # Step 4
    endless = {v for v in range(N) if endcount(D3, v) == 0}
    isolated = {v for v in range(N) if not any(v in e for e in edges + [tuple(e) for e in pedges(P1)])}
    claim(endless <= {x3, x2, y2} | isolated, f'Step 4: unexpected endless vertices {endless - {x3, x2, y2} - isolated}')
    edges, D4 = walk_back(N, edges, D3, P1, rng.randrange(1 << 30), log)
    claim(endcount(D4, x1) == 0 and endcount(D4, y2) == 1, 'Step 4 end counts')
    L = {}
    for l in (l1, l2, l3):
        c = path_with(D4, l)
        claim(len(c) == 1, 'leaf on two paths')
        L[l] = c[0]
    S3, S2, S1 = set(L[l3][0]), set(L[l2][0]), set(L[l1][0])
    claim(S3 <= V_Q3 | {l3} | T2 | T1, 'Step 4: l3-path containment')
    claim(not (S3 & {x3, l1, l2}), f'Step 4: l3-path meets {S3 & {x3, l1, l2}}')
    claim(S2 <= V_Q2 | {l2} | T1, 'Step 4: l2-path containment')
    claim(not (S2 & {x2, l1}), f'Step 4: l2-path meets {S2 & {x2, l1}}')
    claim(S1 <= V_Q1 | T2 | T1, 'Step 4: l1-path containment')
    claim(x1 not in S1, 'Step 4: l1-path contains x1')
    # Step 5: merges l3 -> x3, l2 -> x2, l1 -> x1
    D = [(list(vs), list(es)) for vs, es in D4]
    for l, x in ((l3, x3), (l2, x2), (l1, x1)):
        for vs, es in D:
            claim(not (l in vs and x in vs), f'merge {l}->{x}: a path contains both')
        D = [([x if v == l else v for v in vs], es) for vs, es in D]
    # final decomposition of G
    GE = [tuple(sorted(e)) for e in E]
    D = renumber(n, GE, [(vs, None) for vs, es in D])
    ends = {v for v in range(n) if sum(1 for e in E if v in e) % 2 == 1}
    check_decomp(n, GE, D, ends)
    fin = []
    for i in range(3):
        f = GE.index(tuple(sorted((X[i], Y[i]))))
        P = [P for P in D if (P[0][0] == X[i] and P[1][0] == f) or (P[0][-1] == X[i] and P[1][-1] == f)]
        claim(len(P) == 1, f'x{i+1}y{i+1} not terminal at x{i+1}')
        fin.append(id(P[0]))
    claim(len(set(fin)) == 3, 'final paths not different')
    return log
