"""dense.py: the append chain with one protected step, on all residual shapes of T(6)-i
(session claude/t6-dense).

Input: g6 lines of B = J - z with U = N(z) = {0..5}.  For every root r in U and the labellings
(x1, y1, x2, y2, x3, y3) of U with r in {y1, y2, y3}, x1y2 in E(B) and x2y3 in E(B):

  base    M = (B - x1y2 - x2y3) + l1 y1 (only even vertex x3), a Lovasz decomposition D0 with
          (E1) the l1-path avoids x1 and does not end at y2, y3;
          (E2) the path ending at y2 avoids x2;   (E3) the path ending at y3 avoids x3;
          (E4) y2, y3 are not the two ends of one path;
          (E5) the path ending at x2 avoids y3;
          (E6) for p in {x2, x3} cap N_B(y2): the path through p y2 has its end e on p's side
               with phi(e) not in N_B(y2), where phi(x2) = y3, phi(y3) = l3, phi(v) = v else;
  walk    leaf l3 at y3; append x2 -> y3; leaf l2 at y2; protected Fan y2 <- x1 (blanks
          {x2, x3} cap N(y2));
  un-lift l_i -> z, append x_i, and verify the star-terminal Lovasz decomposition of J.

This is Theorem 3.1 of manuscripts/t6-dense (Lean `stl_of_appendBase`).  Mode `end` drops (E5)
and (E6) and runs the first walk as a Fan transfer (forced chain) and the protected step with
the forced chain (Theorem 3.3 / Remark).  Mode `endZ` is the form proved in Lean, with every
leaf identified with z: in (E6) the end e must moreover not be l1 (= z) or y3.  Mode `endT`
replaces (E6) by (E7) the path ending at x1 avoids y2, so that the protected step is an append
as well (Theorem 2.1, Lean `stl_of_appendBase`).  Roots are tried in all labellings in a fixed random
order; per root the search stops at the first labelling whose base executes.

usage: dense.py MODE SEEDS BUDGET [MAXLAB] < graphs.g6
"""
import sys
import os
import random
import itertools
import networkx as nx
from walksim import Engine, leaf, fan, static_pred_ok, check_decomp, unlift_J, star_ok

HERE = os.path.dirname(os.path.abspath(__file__))
ENG = Engine(os.path.join(HERE, 'lsearch'))


def shape(B):
    U = range(6)
    D = nx.Graph()
    D.add_nodes_from(U)
    D.add_edges_from((a, c) for a in U for c in U if a < c and not B.has_edge(a, c))
    E = sorted(d for _, d in D.degree() if d > 0)
    m = D.number_of_edges()
    if m == 0:
        return 'empty', D
    if m == 1:
        return 'K2', D
    if m == 2 and E == [1, 1, 2]:
        return 'P3', D
    if m == 3 and E == [2, 2, 2]:
        return 'K3', D
    if m == 4 and E == [2, 2, 2, 2] and nx.is_connected(D.subgraph([v for v in U if D.degree(v)])):
        return 'C4', D
    return 'other', D


def labellings(B, r):
    out = []
    for p in itertools.permutations(range(6)):
        x1, y1, x2, y2, x3, y3 = p
        if r not in (y1, y2, y3):
            continue
        if not (B.has_edge(x1, y2) and B.has_edge(x2, y3)):
            continue
        out.append(dict(x1=x1, y1=y1, x2=x2, y2=y2, x3=x3, y3=y3))
    return out


def base_query(B, L, mode, seed, budget):
    nB = B.number_of_nodes()
    l1 = nB
    x1, y1, x2, y2, x3, y3 = (L[k] for k in ('x1', 'y1', 'x2', 'y2', 'x3', 'y3'))
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
    ef = {l1: [x1], y2: [x2], y3: [x3]}
    q['ep'] = [(l1, y2), (l1, y3), (y2, y3)]
    if mode in ('endA', 'endZ'):
        ef.setdefault(x2, []).append(y3)
        Ny2 = set(B.neighbors(y2))
        mask = (Ny2 - {y3, x2}) | ({x2} if y3 in Ny2 else set())
        if mode == 'endZ':      # all leaves are z: z (= l1) and y3 (-> z) are neighbours of y2
            mask |= {l1, y3}
        q['es'] = [(p, y2, sorted(mask)) for p in (x2, x3) if p in Ny2]
    if mode == 'endT':          # all seven steps are appends: (E1)-(E5) and (E7) P_x1 avoids y2
        ef.setdefault(x2, []).append(y3)
        ef.setdefault(x1, []).append(y2)
    q['ef'] = ef
    return q


def run_walk(B, L, D0, mode):
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
    prot = {p for p in (x2, x3) if B.has_edge(p, y2)}
    nbrs = [v for v in B.neighbors(y2) if v != x1] + [l2]
    info['static'] = static_pred_ok(D3, y2, x1, nbrs, prot)
    D4, f2 = fan(D3, y2, x1)
    if not f2['ok']:
        return 'W2FAIL', info
    for li, xi in ((l1, x1), (l2, x2), (l3, x3)):
        P = [P for P in D4 if li in P]
        if len(P) != 1 or xi in P[0]:
            return 'SEPFAIL', info
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


def run_walk_z(B, L, D0, mode='endZ'):
    """the Lean sequence (`stl_of_appendBase`) on subgraphs of J, z = l1 = l2 = l3:
    append y3->z, append x2->y3, append y2->z, protected Fan y2 <- x1 (static condition checked
    with z in N(y2)), append z->x1, z->x2, z->x3; verify the decomposition of J"""
    nB = B.number_of_nodes()
    z = nB                      # l1 is z
    x1, y1, x2, y2, x3, y3 = (L[k] for k in ('x1', 'y1', 'x2', 'y2', 'x3', 'y3'))

    def app(D, t, u):           # append_move: a path ending at t, avoiding u, absorbs tu
        D = [list(P) for P in D]
        for P in D:
            if (P[0] == t or P[-1] == t) and u not in P:
                if P[-1] != t:
                    P.reverse()
                P.append(u)
                return D
        raise ValueError('no append %s->%s' % (t, u))
    D = app(D0, y3, z)
    D = app(D, x2, y3)
    D = app(D, y2, z)
    if mode == 'endT':           # the fourth step is an append as well
        D = app(D, x1, y2)
    else:
        prot = {p for p in (x2, x3) if B.has_edge(p, y2)}
        nbrs = [v for v in B.neighbors(y2) if v != x1] + [z]
        if not static_pred_ok(D, y2, x1, nbrs, prot):
            return 'STATIC_FAIL'
        D, f = fan(D, y2, x1)
        if not f['ok']:
            return 'W2FAIL'
    for yi, xi in ((y1, x1), (y2, x2), (y3, x3)):
        P = [P for P in D if (P[0] == z and P[1] == yi) or (P[-1] == z and P[-2] == yi)]
        if len(P) != 1 or xi in P[0]:
            return 'SEPFAIL'
        P = P[0]
        if P[-1] != z:
            P.reverse()
        P.append(xi)
    EJ = set(frozenset(e) for e in B.edges()) | set(frozenset((z, u)) for u in range(6))
    prof = {v: 1 for v in range(nB)}
    prof[z] = 0
    err = check_decomp(D, EJ, prof)
    if err:
        return 'BAD:' + err
    if not star_ok(D, z):
        return 'BAD:star'
    return 'OK'


def main():
    mode = sys.argv[1]
    seeds = int(sys.argv[2])
    budget = int(sys.argv[3])
    maxlab = int(sys.argv[4]) if len(sys.argv) > 4 else 10 ** 9
    rng = random.Random(1)
    tot = {}
    for line in sys.stdin:
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        B = nx.from_graph6_bytes(line.encode())
        sh, _ = shape(B)
        st = tot.setdefault(sh, dict(graphs=0, roots=0, roots_ok=0, labs_tried=0, bases=0,
                                     base_ok=0, und=0, bad=0, notok=0, nolab=0))
        st['graphs'] += 1
        flags = []
        for r in range(6):
            st['roots'] += 1
            labs = labellings(B, r)
            if not labs:
                st['nolab'] += 1
            rng.shuffle(labs)
            ok = False
            for L in labs[:maxlab]:
                st['labs_tried'] += 1
                res = ENG.run([base_query(B, L, mode, s, budget) for s in range(seeds)])
                for status, D0 in res:
                    if status == 'UND':
                        st['und'] += 1
                    if status != 'OK':
                        continue
                    st['bases'] += 1
                    out, info = run_walk(B, L, D0, mode)
                    if mode in ('endZ', 'endT'):
                        outz = run_walk_z(B, L, D0, mode)
                        if outz != 'OK':
                            st['zfail'] = st.get('zfail', 0) + 1
                            print('Z-NOT-OK', line, L, outz, file=sys.stderr)
                            out = 'Z:' + outz
                    if out == 'OK':
                        st['base_ok'] += 1
                        ok = True
                        break
                    if out.startswith('BAD'):
                        st['bad'] += 1
                        print('BAD', line, L, out, file=sys.stderr)
                    if mode in ('endA', 'endZ', 'endT'):
                        st['notok'] += 1
                        print('ENDA-NOT-OK', line, L, out, info, file=sys.stderr)
                if ok:
                    break
            st['roots_ok'] += ok
            flags.append(str(int(ok)))
        print(line, sh, ''.join(flags), flush=True)
    for sh, st in tot.items():
        print('SUMMARY', mode, sh, ' '.join('%s=%d' % kv for kv in st.items()), flush=True)


if __name__ == '__main__':
    main()
