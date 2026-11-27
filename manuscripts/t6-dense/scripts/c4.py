"""c4.py: the protected chained walk on the C4 residual shape of T(6)-i (session claude/t6-dense).

Input: g6 lines of B = J - z with U = N(z) = {0..5} (as printed by gen_core.py / gen_resid.py).
For each root r on the C4 of D = K6 - B[U] and each of the 8 labellings with the path
x2 y2 y3 x3 along the cycle, r in {y2, y3}, and {x1, y1} the two universal vertices:

  chains  P2 = y3 x2 (a diagonal), P1 = y2 x1 (x1 universal): both edges of B;
  base    M = (B - x1y2 - x2y3) + l1 y1, whose only even vertex is x3;
  walk    leaf l3 at y3; Fan y3 <- x2; leaf l2 at y2; protected Fan y2 <- x1 (blank x3);
  un-lift l_i -> z, append x_i: a star-terminal Lovasz decomposition of J with transitions
          x_i z y_i, verified edge by edge (so STL(J, z, y_i) for i = 1, 2, 3).

Base modes (constraints on the Lovasz decomposition D0 of M):
  sep   : the six separations of the chained walk theorem (Thm 8.2);
  end   : end-path form: path ending at l1 avoids x1 and does not end at y2, y3; the path ending
          at y2 avoids x2, the one at y3 avoids x3; y2, y3 not the two ends of one path;
  endA  : end + the path ending at x2 avoids y3 (the first walk is a plain append) + the static
          predecessor condition at the protected step, read on D0: the x3y2-path's end on x3's
          side is not a B-neighbour of y2.  (Theorem C4-walk, Lean `c4_walk`.)
For every (root, labelling) up to SEEDS random search orders are tried; for each base found the
whole construction is executed and the final decomposition of J checked.

usage: c4.py MODE SEEDS BUDGET < graphs.g6
"""
import sys
import os
import networkx as nx
from walksim import Engine, leaf, fan, static_pred_ok, check_decomp, unlift_J, star_ok, ends_count

HERE = os.path.dirname(os.path.abspath(__file__))
ENG = Engine(os.path.join(HERE, 'lsearch'))


def core(B):
    U = list(range(6))
    D = [(a, c) for a in U for c in U if a < c and not B.has_edge(a, c)]
    return D


def c4_order(D):
    """cyclic order of the C4 (list of 4 vertices) or None"""
    if len(D) != 4:
        return None
    H = nx.Graph(D)
    if any(d != 2 for _, d in H.degree()) or not nx.is_connected(H):
        return None
    c = nx.cycle_basis(H)[0]
    return c


def labellings(cyc, univ, r):
    out = []
    for i in range(4):
        for s in (1, -1):
            x2, y2, y3, x3 = (cyc[(i + s * j) % 4] for j in range(4))
            if r not in (y2, y3):
                continue
            for x1, y1 in (univ, univ[::-1]):
                out.append(dict(x1=x1, y1=y1, x2=x2, y2=y2, x3=x3, y3=y3))
    return out


def base_query(B, L, mode, seed, budget):
    nB = B.number_of_nodes()
    l1 = nB
    x1, y1, x2, y2, x3, y3 = (L[k] for k in ('x1', 'y1', 'x2', 'y2', 'x3', 'y3'))
    assert B.has_edge(x1, y2) and B.has_edge(x2, y3)
    E = [(u, v) for u, v in B.edges() if {u, v} not in ({x1, y2}, {x2, y3})]
    E.append((y1, l1))
    deg = [0] * (nB + 1)
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    b = [d % 2 for d in deg]
    evens = [v for v in range(nB + 1) if deg[v] > 0 and deg[v] % 2 == 0]
    assert evens == [x3], evens
    q = dict(n=nB + 1, edges=E, b=b, seed=seed, budget=budget)
    if mode == 'sep':
        q['sep'] = [(x1, l1), (x2, y2), (x3, y3), (l1, y2), (l1, y3), (y2, y3)]
    else:
        ef = {l1: [x1], y2: [x2], y3: [x3]}
        q['ep'] = [(l1, y2), (l1, y3), (y2, y3)]
        if mode == 'endA':
            ef[x2] = [y3]
            q['es'] = [(x3, y2, sorted(B.neighbors(y2)))]
        q['ef'] = ef
    return q, E


def run_walk(B, L, D0, E):
    """execute the construction; returns (status, details)"""
    nB = B.number_of_nodes()
    l1, l3, l2 = nB, nB + 1, nB + 2
    x1, y1, x2, y2, x3, y3 = (L[k] for k in ('x1', 'y1', 'x2', 'y2', 'x3', 'y3'))
    info = {}
    D1 = leaf(D0, y3, l3)
    D2, f1 = fan(D1, y3, x2)
    info['w1_trivial'] = len(f1['chain']) == 1
    if not f1['ok']:
        return 'W1FAIL', info
    D3 = leaf(D2, y2, l2)
    # the protected step: target y2, source x1, protected blank x3
    nbrs = [v for v in B.neighbors(y2) if v != x1] + [l2]
    info['static'] = static_pred_ok(D3, y2, x1, nbrs, {x3})
    D4, f2 = fan(D3, y2, x1)
    info['w2_chain'] = f2['chain']
    if not f2['ok']:
        info['hit'] = f2['hit']
        return 'W2FAIL', info
    # final separations
    for li, xi in ((l1, x1), (l2, x2), (l3, x3)):
        P = [P for P in D4 if li in P]
        if len(P) != 1 or xi in P[0]:
            return 'SEPFAIL', info
    # J-form un-lift and verification
    z = nB + 3
    DJ = unlift_J(D4, [l1, l2, l3], [x1, x2, x3], z)
    EJ = set(frozenset(e) for e in B.edges()) | set(frozenset((z, u)) for u in range(6))
    prof = {v: 1 for v in range(nB)}
    prof[z] = 0
    err = check_decomp(DJ, EJ, prof)
    if err:
        return 'BAD:' + err, info
    if not star_ok(DJ, z):
        return 'BAD:star', info
    return 'OK', info


def main():
    mode = sys.argv[1]
    seeds = int(sys.argv[2])
    budget = int(sys.argv[3])
    stats = dict(graphs=0, roots=0, roots_ok=0, cfg=0, cfg_base=0, cfg_ok=0, bases=0,
                 base_ok=0, w2fail=0, static=0, und=0, bad=0, w1triv=0)
    for line in sys.stdin:
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        B = nx.from_graph6_bytes(line.encode())
        D = core(B)
        cyc = c4_order(D)
        if cyc is None:
            continue
        univ = [u for u in range(6) if u not in cyc]
        stats['graphs'] += 1
        gl = []
        for r in cyc:
            stats['roots'] += 1
            rok = False
            for L in labellings(cyc, univ, r):
                stats['cfg'] += 1
                qs = []
                for s in range(seeds):
                    q, E = base_query(B, L, mode, s, budget)
                    qs.append(q)
                res = ENG.run(qs)
                got = False
                cok = False
                seen = set()
                for st, D0 in res:
                    if st == 'UND':
                        stats['und'] += 1
                    if st != 'OK':
                        continue
                    key = tuple(sorted(tuple(P) if P[0] < P[-1] else tuple(P[::-1]) for P in D0))
                    if key in seen:
                        continue
                    seen.add(key)
                    got = True
                    stats['bases'] += 1
                    status, info = run_walk(B, L, D0, E)
                    stats['w1triv'] += info.get('w1_trivial', False)
                    stats['static'] += info.get('static', False)
                    if status == 'OK':
                        stats['base_ok'] += 1
                        cok = True
                    elif status == 'W2FAIL':
                        stats['w2fail'] += 1
                    elif status.startswith('BAD'):
                        stats['bad'] += 1
                        print('BAD', line, L, status, file=sys.stderr)
                    if mode == 'endA' and status != 'OK':
                        print('ENDA-NOT-OK', line, L, status, info, file=sys.stderr)
                stats['cfg_base'] += got
                stats['cfg_ok'] += cok
                rok = rok or cok
            stats['roots_ok'] += rok
            gl.append(int(rok))
        print(line, 'roots_ok', ''.join(map(str, gl)), flush=True)
    print('SUMMARY', mode, ' '.join('%s=%d' % kv for kv in stats.items()), flush=True)


if __name__ == '__main__':
    main()
