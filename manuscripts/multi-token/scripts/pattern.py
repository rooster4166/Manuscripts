#!/usr/bin/env python3
"""pattern.py: the coverage theorem (manuscript Theorem 4.2), checked from its hypotheses.

For every root r with d_J(r) >= 3 of every input J (z the only even vertex, d(z) = 6) and every data choice
(w, {x1 y1, x2 y2}) with both labellings of the pairs and both orientations, test the hypotheses of
Theorem 4.2 directly on J:
  (A) w can be removed:  (A1) d(w) = 3, N(w) - z = {p, q}, pq not an edge, {p, q} not a pair;
                         or (A2) wr is an edge and r is adjacent to neither y1 nor y2;
  (B) d(y1) = 3 with N(y1) = {z, x1, v}, v not in {w, x2, y2}, v not adjacent to y2, and under (A1)
      {p, q} != {v, y2}; and the token arriving at v can be removed:
      (B1) v = r and (A1) holds (then r -> z);
      (B2) v is outside N[z], d(v) = 3, and the two neighbours s, t of v other than y1 (in the graph
           after step (A1), if used) are non-adjacent there and {s, t} is not {x2, y2};
and print the certificate schedule as a SCHED line for mt_verify.py:
      (A1) S w:p-q | (A2) M w-r, M r-z ;  M y1-v ;  (B1) M r-z | (B2) S v:s-t ;  D (tail of y1).
usage: pattern.py < g6  > sched.txt     (summary on stderr)
"""
import sys
import itertools
import networkx as nx


def matchings(vs, J):
    if not vs:
        yield []
        return
    a = vs[0]
    for b in vs[1:]:
        if J.has_edge(a, b):
            for pm in matchings([v for v in vs[1:] if v != b], J):
                yield [(a, b)] + pm


def certificate(J, z, r, w, pairs):
    """pairs = [(y1, x1), (y2, x2)]; the tail of pair index 0 is dropped.  Tries (A1), then (A2)."""
    for A in ('A1', 'A2'):
        mv = certificate_with(J, z, r, w, pairs, A)
        if mv is not None:
            return mv
    return None


def certificate_with(J, z, r, w, pairs, A):
    (y1, x1), (y2, x2) = pairs
    pairsets = [{y1, x1}, {y2, x2}]
    K = nx.Graph(J)                      # the current graph (M is J minus the z-edges and pairs)
    K.remove_edges_from([(z, w), (z, y1), (z, x1), (z, y2), (z, x2), (y1, x1), (y2, x2)])
    moves = []
    p = q = None
    if A == 'A1':
        if J.degree(w) != 3:
            return None
        p, q = sorted(set(J[w]) - {z})
        if J.has_edge(p, q) or {p, q} in pairsets:
            return None
        moves.append('S%d:%d-%d' % (w, p, q))
        K.remove_edges_from([(w, p), (w, q)])
        K.add_edge(p, q)
    else:
        if not J.has_edge(w, r) or J.has_edge(r, y1) or J.has_edge(r, y2):
            return None
        moves += ['M%d-%d' % (w, r), 'M%d-%d' % (r, z)]
        K.remove_edges_from([(w, r), (r, z)])
    if J.degree(y1) != 3:
        return None
    rest = set(J[y1]) - {z, x1}
    if len(rest) != 1:
        return None
    v = rest.pop()
    if v in (w, x2, y2) or J.has_edge(v, y2):
        return None
    if A == 'A1' and {p, q} == {v, y2}:
        return None
    moves.append('M%d-%d' % (y1, v))
    K.remove_edge(y1, v)
    if v == r:
        if A != 'A1':
            return None
        moves.append('M%d-%d' % (r, z))
    else:
        if v == z or v in J[z] or J.degree(v) != 3:
            return None
        st = sorted(K[v])
        if len(st) != 2:
            return None
        s, t = st
        if K.has_edge(s, t) or {s, t} == {x2, y2}:
            return None
        moves.append('S%d:%d-%d' % (v, s, t))
    moves.append('D0')
    return moves


def main():
    roots = covered = certs = 0
    for line in sys.stdin:
        g6 = line.split()[0] if line.strip() else ''
        if not g6:
            continue
        J = nx.from_graph6_bytes(g6.encode())
        ev = [v for v in J if J.degree(v) % 2 == 0]
        if len(ev) != 1 or J.degree(ev[0]) != 6:
            continue
        z = ev[0]
        U = sorted(J[z])
        for r in U:
            if J.degree(r) < 3:          # Test1 needs d_J(r) >= 3 (Corollary 3.2; audit A36, M2)
                continue
            found = None
            anydata = False
            for w in U:
                if w == r:
                    continue
                for pm in matchings([u for u in U if u not in (r, w)], J):
                    anydata = True
                    for (P1, P2) in (tuple(pm), tuple(pm[::-1])):
                        for o1, o2 in itertools.product((0, 1), repeat=2):
                            y1, x1 = (P1[0], P1[1]) if o1 else (P1[1], P1[0])
                            y2, x2 = (P2[0], P2[1]) if o2 else (P2[1], P2[0])
                            mv = certificate(J, z, r, w, [(y1, x1), (y2, x2)])
                            if mv is not None:
                                certs += 1
                                if found is None:
                                    found = (w, [(y1, x1), (y2, x2)], mv)
            if not anydata:
                continue
            roots += 1
            if found:
                covered += 1
                w, prs, mv = found
                print('SCHED %s 0 %d %d %d %s | %s' % (g6, z, r, w, ' '.join('%d,%d' % pr for pr in prs),
                                                      ' '.join(mv)))
    print('pattern: roots %d covered by Theorem 4.2 %d (certificates %d)' % (roots, covered, certs),
          file=sys.stderr)


if __name__ == '__main__':
    main()
