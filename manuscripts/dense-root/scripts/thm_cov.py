# Coverage of Theorem A (G = B - r has <= 1 even vertex) and Theorem B (one connector, g = s)
# at degree-(n-2) roots.  Conditions as in the manuscript (h_t over N, d_B degrees).
import sys, networkx as nx
from collections import Counter
def thmA(B, r, s, k):
    G = B.copy(); G.remove_node(r)
    ev = [v for v in G if G.degree(v) % 2 == 0 and G.degree(v) > 0]
    if len(ev) > 1: return None
    eps = 1 if G.degree(s) % 2 == 1 else 0
    N = [x for x in B if x != r and x != s]
    h = lambda t: sum(1 for x in N if B.degree(x) >= 2 * t)
    for t in range(3, k):
        if not ((h(t) + eps) // 2 + t <= k + 1 or h(t + 1) // 2 + eps + 2 * t <= k + 1): return False
    return True
def thmB(B, r, s, k, Z):
    # s even in G, T = V(B) - Z = {q1, q2} subset N; Q = q1q2 (adjacent) or q1 s q2
    G = B.copy(); G.remove_node(r)
    T = [v for v in B if v not in Z]
    if s not in Z or len(T) != 2: return None
    q1, q2 = T
    best = False
    opts = []
    if B.has_edge(q1, q2): opts.append([q1, q2])
    if B.has_edge(q1, s) and B.has_edge(s, q2): opts.append([q1, s, q2])
    if not opts: return 'noQ'
    for Q in opts:
        Gp = G.copy(); Gp.remove_edges_from(zip(Q, Q[1:]))
        ell = lambda v: (Gp.degree(v) + (Gp.degree(v) % 2)) // 2
        lam = sum(ell(v) for v in Q)
        Nt = [x for x in B if x not in (r, s, q1, q2)]
        h = lambda t: sum(1 for x in Nt if B.degree(x) >= 2 * t)
        ok = True
        for t in range(3, k):
            q = 1 if lam >= t else 0
            if not (h(t) // 2 + q + t <= k + 1 or h(t + 1) // 2 + q + 2 * t <= k + 1): ok = False
        if ok: best = True
    return best
C = Counter()
for fn in sys.argv[1:]:
    resid = 'resid' in fn or 'e28' in fn or 'clt' in fn
    for line in open(fn):
        g6 = line.split()[0]
        J = nx.from_graph6_bytes(g6.encode()); n = J.number_of_nodes(); k = (n - 1) // 2
        z = [v for v in J if J.degree(v) % 2 == 0][0]
        Z = set(J[z]); B = J.copy(); B.remove_node(z)
        for r in sorted(Z):
            if J.degree(r) != n - 2: continue
            s = [v for v in B if v != r and not B.has_edge(r, v)][0]
            a = thmA(B, r, s, k); b = thmB(B, r, s, k, Z)
            C[(fn.split('/')[-1], 'sinZ' if s in Z else 'snotZ', 'A=' + str(a), 'B=' + str(b))] += 1
for key, v in sorted(C.items()): print(key, v)

# ---- extended: Theorem B with Q = q1 y q2 (y in N, forced: +1), and MR theorems' hypotheses ----
def thmB2(B, r, s, k, Z):
    G = B.copy(); G.remove_node(r)
    T = [v for v in B if v not in Z]
    if s not in Z or len(T) != 2: return None
    q1, q2 = T
    opts = []
    if B.has_edge(q1, q2): opts.append(([q1, q2], 0))
    for y in G:
        if y in (q1, q2): continue
        if B.has_edge(q1, y) and B.has_edge(y, q2): opts.append(([q1, y, q2], 0 if y == s else 1))
    # length 3 through s and one neighbour y of r (delta = 1): q1 y s q2 and q1 s y q2
    for y in G:
        if y in (q1, q2, s): continue
        if B.has_edge(q1, y) and B.has_edge(y, s) and B.has_edge(s, q2): opts.append(([q1, y, s, q2], 1))
        if B.has_edge(q1, s) and B.has_edge(s, y) and B.has_edge(y, q2): opts.append(([q1, s, y, q2], 1))
    for Q, extra in opts:
        Gp = G.copy(); Gp.remove_edges_from(zip(Q, Q[1:]))
        ell = lambda v: (Gp.degree(v) + (Gp.degree(v) % 2)) // 2
        lam = sum(ell(v) for v in Q)
        Nt = [x for x in B if x not in (r, s) and x not in Q]
        h = lambda t: sum(1 for x in Nt if B.degree(x) >= 2 * t)
        ok = True
        for t in range(3, k):
            q = 1 if lam >= t else 0
            if not ((h(t) + extra) // 2 + q + t <= k + 1 or (h(t + 1) + extra) // 2 + q + 2 * t <= k + 1): ok = False
        if ok: return True
    return False if opts else 'noQ'
def mr47(B, k):   # >= k-1 universal vertices of B
    return sum(1 for v in B if B.degree(v) == 2 * k - 1) >= k - 1
def mr74(B, k):   # complement of B has max degree <= 2
    return min(dict(B.degree()).values()) >= 2 * k - 3
def mr166(B, r, k, Z):
    # R: k vertices of degree >= 2k-2 containing r, u = #universal in R, need sum_{y notin R} b_y = u with
    # b_y = d_B(y) mod 2 baseline (odd vertices outside R need 1) and extra ends in pairs within capacity.
    H = [v for v in B if B.degree(v) >= 2 * k - 2]
    if len(H) < k or r not in H: return False
    import itertools
    others = [v for v in H if v != r]
    for Rr in itertools.combinations(others, k - 1):
        R = set(Rr) | {r}
        u = sum(1 for v in R if B.degree(v) == 2 * k - 1)
        X = [v for v in B if v not in R]
        base = sum(B.degree(v) % 2 for v in X)
        if base > u or (u - base) % 2: continue
        cap = sum((min(B.degree(v), 2 * k - B.degree(v)) - B.degree(v) % 2) // 2 for v in X)
        if (u - base) // 2 <= cap: return True
    return False
C2 = Counter()
for fn in sys.argv[1:]:
    for line in open(fn):
        g6 = line.split()[0]
        J = nx.from_graph6_bytes(g6.encode()); n = J.number_of_nodes(); k = (n - 1) // 2
        z = [v for v in J if J.degree(v) % 2 == 0][0]
        Z = set(J[z]); B = J.copy(); B.remove_node(z)
        for r in sorted(Z):
            if J.degree(r) != n - 2: continue
            s = [v for v in B if v != r and not B.has_edge(r, v)][0]
            a = thmA(B, r, s, k); b = thmB2(B, r, s, k, Z)
            thm = (a is True) or (b is True)
            mr = mr47(B, k) or mr74(B, k) or mr166(B, r, k, Z)
            C2[(fn.split('/')[-1], 'sinZ' if s in Z else 'snotZ', 'A=' + str(a), 'B2=' + str(b), 'MR=' + str(mr))] += 1
print('--- extended')
for key, v in sorted(C2.items()): print(key, v)
