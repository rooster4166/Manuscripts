"""E-C: the tight walk theorem on PTM's NOBASE instances (n = 8).

Walk theorem (terminal-matching Thm 3.2): G all-odd, ab, xy disjoint edges; walk P = y .. a avoiding
b, x; base graph M = ((G - ab) + l1 b) - xy - E(P); a Lovász decomposition of M separating
{x,y}, {a,l1}, {l1,y}; then hang l2 at y, walk back along P by Fan transfers (target p_i, source
p_{i+1}), merge l2 -> x and l1 -> a.  Admissibility (p_i not in N(x), 0<i<k) keeps the endless
short end x out of Z(p_i).  TIGHT version: allow p_i in N(x).  Then Z(p_i) = {x} and Fan's
inequality is an equality, b(p_{i+1}) = 1 = |Z(p_i)|: the forced chain either avoids x (success)
or is stuck at x.  We run the chains exactly and verify the final decomposition of G.

usage: python3 ptmwalk.py FILE [maxlen]   (FILE: lines 'NOBASE g6(G-F) a1 b1 a2 b2 ...')
"""
import sys, itertools, collections
import networkx as nx
import tf

L1, L2 = 100, 101

def sep_ok(D, pairs):
    for P in D:
        S = set(P)
        for p, q in pairs:
            if p in S and q in S: return False
    return True

def walk_back(G2, D, P):
    """walk back along P = p0..pk in graph G2 (contains E(P)); D decomposes G2 - E(P).
    Returns list of results (each a decomposition of G2) over all chain choices."""
    states = [D]
    cur = tf.copyg(G2)
    for i in range(len(P) - 1):
        cur = tf.rem(cur, *[(P[j], P[j + 1]) for j in range(i, len(P) - 1)]) if False else None
    # rebuild graphs stepwise: K_i = G2 - {p_i p_{i+1}, ..., p_{k-1} p_k}
    res = [D]
    for i in range(len(P) - 1):
        Ki = tf.rem(G2, *[(P[j], P[j + 1]) for j in range(i + 1, len(P) - 1)])
        new = []
        seen = set()
        for Dc in res:
            for D2, chain, Q in tf.fan_moves(Dc, P[i + 1], P[i]):
                k = tf.canon(D2)
                if k in seen: continue
                seen.add(k); new.append(D2)
        res = new
        if not res: return []
    return res

def merge(D, leaf, x):
    out = []
    for P in D:
        out.append(tuple(x if v == leaf else v for v in P))
    return out

def try_instance(G, a, b, x, y, maxlen, stats):
    """returns a verified PTM2 decomposition (ab terminal at a, xy terminal at x, different paths) or None"""
    H = tf.to_nx(G)
    Hb = H.copy(); Hb.remove_nodes_from([b, x])
    if y not in Hb or a not in Hb or not nx.has_path(Hb, y, a): return None, 'nopath'
    any_base = False
    for P in nx.all_simple_paths(Hb, y, a, cutoff=maxlen):
        P = tuple(P)
        tight = any(P[i] in G[x] for i in range(1, len(P) - 1))
        # base graph
        K = tf.rem(G, (a, b)); K = tf.add(K, (L1, b))          # leaf graph at ab: l1 stands for a
        M = tf.rem(K, (x, y), *[(P[i], P[i + 1]) for i in range(len(P) - 1)])
        bM = tf.lovasz_b(M)
        assert tf.evens(M) in ([x], []) or tf.evens(M) == [x], tf.evens(M)
        pairs = [(x, y), (a, L1), (L1, y)]
        for D0 in tf.decomps(M, bM):
            if not sep_ok(D0, pairs): continue
            any_base = True
            # step 1: extend Q_y by l2
            Qy = tf.Qc(D0, y)
            D1 = [Pq for Pq in D0 if Pq is not Qy] + [tf._orient(Qy, y)[::-1] + (L2,)]
            H2 = tf.add(tf.rem(K, (x, y)), (L2, y))              # two-leaf graph
            for D2 in walk_back(H2, D1, P):
                # merge l2 -> x, then l1 -> a
                D3 = merge(D2, L2, x); D4 = merge(D3, L1, a)
                try:
                    tf.check(G, D4, tf.lovasz_b(G))
                except AssertionError:
                    continue
                Pa = [Q for Q in D4 if (Q[0] == a and Q[1] == b) or (Q[-1] == a and Q[-2] == b)]
                Px = [Q for Q in D4 if (Q[0] == x and Q[1] == y) or (Q[-1] == x and Q[-2] == y)]
                if Pa and Px and Pa[0] != Px[0]:
                    stats['tight' if tight else 'admissible'] += 1
                    return D4, ('tight' if tight else 'admissible', len(P) - 1)
    return None, ('nobase' if not any_base else 'walkback-failed')

if __name__ == '__main__':
    fn = sys.argv[1]; maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 7
    C = collections.Counter(); ex = []
    for line in open(fn):
        w = line.split()
        if not w or w[0] != 'NOBASE': continue
        g6 = w[1]; a1, b1, a2, b2 = map(int, w[2:6]); anyp = w[6]
        Gm = tf.from_g6(g6)
        G = tf.add(Gm, (a1, b1), (a2, b2))
        stats = collections.Counter()
        found = None; why = collections.Counter()
        for (e, f) in (((a1, b1), (a2, b2)), ((a2, b2), (a1, b1))):
            for a, b in (e, e[::-1]):
                for x, y in (f, f[::-1]):
                    D, info = try_instance(G, a, b, x, y, maxlen, stats)
                    if D is not None:
                        found = info; break
                    why[info] += 1
                if found: break
            if found: break
        key = anyp
        C[(key, found[0] if found else 'NONE')] += 1
        if not found and len(ex) < 8: ex.append((g6, a1, b1, a2, b2, dict(why)))
        if found: C[(key, found[0], 'len', found[1])] += 1
    for k, v in sorted(C.items(), key=str): print(k, v)
    for e in ex: print("UNSOLVED", e)
