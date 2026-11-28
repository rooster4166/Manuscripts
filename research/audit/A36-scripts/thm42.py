#!/usr/bin/env python3
"""thm42.py (A36 auditor): Theorem 4.2 of multi-token.tex from its hypotheses, written from the
manuscript text (not from pattern.py), plus an own replayer of Definition 2.2 that checks the
certificate schedule of the proof move by move.

For every root r of J (z the only even vertex, d(z) = 6), every w in N(z) - r, every perfect
matching of J[N(z) - {r, w}], every labelling (which pair is pair 1) and orientation, test
  (A1) d(w) = 3, N(w) = {z, p, q}, p !~ q, {p, q} not a pair;  or  (A2) wr in E, r !~ y1, y2;
  (B)  N(y1) = {z, x1, v}, v not in {w, x2, y2}, v !~ y2, and {p, q} != {v, y2} under (A1); and
       (B1) v = r and (A1) holds;  or  (B2) v not in N[z], d(v) = 3, and the two neighbours s, t of
       v other than y1 in the graph after step 1 are non-adjacent there with {s, t} != {x2, y2}.
Every (A, B) combination is tried.  The proof's schedule is then replayed with replay() and must
be legal and end at <= 1 token and <= 1 live tail.
usage: thm42.py < J.g6      prints per-root lines 'T g6 r covered' and a summary."""
import sys
import itertools
import networkx as nx


def pms(vs, J):
    if not vs:
        return [[]]
    out = []
    a = vs[-1]
    for b in vs[:-1]:
        if J.has_edge(a, b):
            rest = [u for u in vs[:-1] if u != b]
            out += [[(a, b)] + m for m in pms(rest, J)]
    return out


def replay(J, z, w, pairs, moves):
    """pairs = [(y, x)]; leaf of pair i is ('L', i).  Checks Definition 2.2 literally."""
    K = {v: set(J[v]) for v in J}

    def rm(a, b):
        assert b in K[a], ('missing edge', a, b)
        K[a].discard(b); K[b].discard(a)
    rm(z, w)
    for (y, x) in pairs:
        rm(z, y); rm(z, x); rm(y, x)
    for i, (y, x) in enumerate(pairs):
        K[('L', i)] = {y}; K[y].add(('L', i))
    leaves = {('L', i) for i in range(len(pairs))}
    for mv in moves:
        tok = {v for v in K if K[v] and len(K[v]) % 2 == 0}
        live = [i for i, (y, x) in enumerate(pairs) if ('L', i) in K[y]]
        X = set()
        for i in live:
            X |= {('L', i), pairs[i][1]}
        if mv[0] == 'M':
            _, p, u = mv
            assert p in tok and u in K[p] and len(K[u]) % 2 == 1 and u not in X, mv
            rm(p, u)
            assert not ((K[u] - {p}) & (tok - {p})), mv
        elif mv[0] == 'D':
            i = mv[1]
            assert i in live and len(K[pairs[i][0]]) % 2 == 1, mv
            rm(pairs[i][0], ('L', i))
        else:
            p = mv[1]
            assert p in tok and len(K[p]) == 2, mv
            if len(mv) == 4:                      # the move names a, b: they must be N(p)
                assert K[p] == {mv[2], mv[3]}, mv
            a, b = sorted(K[p], key=str)
            assert b not in K[a] and a not in leaves and b not in leaves, mv
            for i in live:
                assert {a, b} != {pairs[i][0], pairs[i][1]}, mv
            rm(p, a); rm(p, b); K[a].add(b); K[b].add(a)
    tok = {v for v in K if K[v] and len(K[v]) % 2 == 0}
    live = [i for i, (y, x) in enumerate(pairs) if ('L', i) in K[y]]
    assert len(tok) <= 1 and len(live) <= 1, ('not terminal', tok, live)
    return True


def certificates(J, z, r, w, P1, P2):
    """yield the certificate schedules of every (A, B) combination that applies."""
    (y1, x1), (y2, x2) = P1, P2
    pairset = [{y1, x1}, {y2, x2}]
    Nz = set(J[z])
    for A in ('A1', 'A2'):
        if A == 'A1':
            if J.degree(w) != 3:
                continue
            p, q = sorted(set(J[w]) - {z})
            if J.has_edge(p, q) or {p, q} in pairset:
                continue
            step1 = [('S', w)]
        else:
            if not J.has_edge(w, r) or J.has_edge(r, y1) or J.has_edge(r, y2):
                continue
            p = q = None
            step1 = [('M', w, r), ('M', r, z)]
        if J.degree(y1) != 3:
            continue
        rest = set(J[y1]) - {z, x1}
        if len(rest) != 1:
            continue
        v = rest.pop()
        if v in (w, x2, y2) or J.has_edge(v, y2):
            continue
        if A == 'A1' and {p, q} == {v, y2}:
            continue
        # B1
        if v == r and A == 'A1':
            yield A + 'B1', step1 + [('M', y1, v), ('M', r, z), ('D', 0)]
        # B2: v outside N[z], d(v) = 3, neighbours of v other than y1 after step 1
        if v != z and v not in Nz and J.degree(v) == 3:
            # graph after step 1 restricted to what matters: neighbourhood of v and adjacency of s, t
            nb = set(J[v])
            if A == 'A1' and v in (p, q):
                nb = (nb - {w}) | ({p, q} - {v})
            st = nb - {y1}
            if len(st) == 2:
                s, t = sorted(st)
                # adjacency of s, t in the graph after step 1.  z is not among them (v !~ z), the pair
                # edge x1y1 cannot be {s, t} (y1 is excluded), x2y2 is excluded below; step 1 adds
                # pq under (A1) and deletes wr under (A2).
                adj_st = J.has_edge(s, t)
                if A == 'A1' and {s, t} == {p, q}:
                    adj_st = True
                if A == 'A2' and {s, t} == {w, r}:
                    adj_st = False
                if not adj_st and {s, t} != {x2, y2}:
                    yield A + 'B2', step1 + [('M', y1, v), ('S', v), ('D', 0)]


def main():
    roots = covered = 0
    kinds = {}
    for line in sys.stdin:
        g = line.split()[0] if line.strip() else ''
        if not g:
            continue
        J = nx.from_graph6_bytes(g.encode())
        ev = [v for v in J if J.degree(v) % 2 == 0]
        if len(ev) != 1 or J.degree(ev[0]) != 6:
            continue
        z = ev[0]
        U = sorted(J[z])
        for r in U:
            if J.degree(r) < 3:
                continue
            anyd = False
            cov = None
            for w in U:
                if w == r:
                    continue
                for pm in pms([u for u in U if u not in (r, w)], J):
                    anyd = True
                    for lab in (pm, pm[::-1]):
                        for o in itertools.product((0, 1), repeat=2):
                            prs = [(a, b) if oi else (b, a) for (a, b), oi in zip(lab, o)]
                            for kind, mv in certificates(J, z, r, w, prs[0], prs[1]):
                                replay(J, z, w, prs, mv)
                                kinds[kind] = kinds.get(kind, 0) + 1
                                if cov is None:
                                    cov = (w, prs, mv)
            if not anyd:
                continue
            roots += 1
            covered += cov is not None
            print('T', g, r, int(cov is not None))
    print('SUMMARY roots %d covered %d certificates %s' % (roots, covered, kinds))


if __name__ == '__main__':
    main()
