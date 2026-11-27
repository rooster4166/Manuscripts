"""gen_resid.py: random J in a dense residual shape of T(6)-i, with the residual conditions of a
smallest failure imposed (session claude/t6-dense).

B = J - z, U = N(z) = {0..5}, B[U] = K6 - D for D in {empty, K2, P3, K3, C4} (D on 0, 1, ...;
the C4 is 0-1-2-3-0, K3 is 0-1-2, P3 is 0-1-2 with middle 1, K2 is 01); O = exterior (odd)
vertices.  Imposed (research/notes/reader-six-even-program.md, STATUS 3.5):
  * d_B(u) even for u in U, odd for x in O; J 3-connected; z the only even vertex of J;
  * delta(B) >= 6 and delta(B[O]) >= 4 (4EX Part IV Cor 2);
  * every u in U has >= 3 odd neighbours, a C-universal one >= 5 (RS, apex failures);
  * |S(x)| = |N(x) cap U| in {0, 3, 4, 5, 6} for x in O (INC Thm 1);
  * C4 twins: the cycle neighbours of a failing root are adjacent twins throughout B (RS): with
    TW = 1 the pair {1, 3} are closed twins (roots 0 and 2 qualify), with TW = 2 also {0, 2}
    (all four cycle vertices qualify); TW is ignored for the other shapes;
  * D = empty: some exterior vertex is full, |S(x)| = 6 (6CL Thm 6).
Prints g6(B), U = 0..5, one graph per line.

usage: gen_resid.py COUNT NO TW SEED [SHAPE]     (NO = |O|, even; SHAPE default C4)
"""
import sys
import random
import networkx as nx


SHAPES = {'empty': set(), 'K2': {(0, 1)}, 'P3': {(0, 1), (1, 2)}, 'K3': {(0, 1), (1, 2), (0, 2)},
          'C4': {(0, 1), (1, 2), (2, 3), (0, 3)}}


def build(rng, no, tw, sh='C4'):
    U = list(range(6))
    O = list(range(6, 6 + no))
    B = nx.Graph()
    B.add_nodes_from(U + O)
    Dset = SHAPES[sh]
    for i in U:
        for j in U:
            if i < j and (i, j) not in Dset:
                B.add_edge(i, j)
    if sh != 'C4':
        tw = 0
    # classes of U that must be treated together (twins)
    if tw:
        classes = [[1, 3]] + ([[0, 2]] if tw >= 2 else [[0], [2]]) + [[4], [5]]
    else:
        classes = [[u] for u in U]
    for x in O:
        while True:
            s = rng.choice((0, 3, 3, 4, 4, 5, 5, 6))
            if s == 0:
                S = []
                break
            cl = classes[:]
            rng.shuffle(cl)
            S = []
            for c in cl:
                if len(S) + len(c) <= s:
                    S += c
            if len(S) == s:
                break
        for u in S:
            B.add_edge(x, u)
    if sh == 'empty' and not any(sum(1 for u in U if B.has_edge(x, u)) == 6 for x in O):
        return None
    for u in U:
        e = sum(1 for x in O if B.has_edge(u, x))
        need = 5 if all(B.has_edge(u, w) for w in U if w != u) else 3
        if e < need or B.degree(u) % 2 or B.degree(u) < 6:
            return None
    # exterior degrees: d_O(x) >= 4, total odd >= 7
    target = {}
    for x in O:
        s = B.degree(x)
        d = max(4, 7 - s)
        if (d + s) % 2 == 0:
            d += 1
        d += 2 * rng.choice((0, 0, 0, 1))
        if d > no - 1:
            return None
        target[x] = d
    if sum(target.values()) % 2:
        return None
    seq = [target[x] for x in O]
    if not nx.is_graphical(seq):
        return None
    H = nx.havel_hakimi_graph(seq)
    try:
        nx.double_edge_swap(H, nswap=4 * H.number_of_edges(), max_tries=10 ** 5,
                            seed=rng.randrange(10 ** 9))
    except nx.NetworkXException:
        pass
    for a, c in H.edges():
        B.add_edge(O[a], O[c])
    # twins: closed neighbourhoods equal
    for p, q in (([(1, 3)] + ([(0, 2)] if tw >= 2 else [])) if tw else []):
        if set(B[p]) | {p} != set(B[q]) | {q}:
            return None
    if min(d for _, d in B.degree()) < 6:
        return None
    if any(B.degree(v) % 2 != (0 if v in U else 1) for v in B):
        return None
    J = B.copy()
    J.add_node('z')
    for u in U:
        J.add_edge('z', u)
    if nx.node_connectivity(J) < 3:
        return None
    return B


def main():
    count, no, tw, seed = (int(a) for a in sys.argv[1:5])
    sh = sys.argv[5] if len(sys.argv) > 5 else 'C4'
    rng = random.Random(seed)
    made = tries = 0
    while made < count and tries < 100000 * count:
        tries += 1
        B = build(rng, no, tw, sh)
        if B is None:
            continue
        made += 1
        print(nx.to_graph6_bytes(B, header=False).decode().strip(), flush=True)
    print('# made=%d tries=%d' % (made, tries), file=sys.stderr)


if __name__ == '__main__':
    main()
