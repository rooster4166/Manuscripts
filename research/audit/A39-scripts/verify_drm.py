"""A39: verify drm -v witnesses from scratch (no code shared with drm.cpp).

Each line 'W g6 r D0: p p ... PHI: p ...' (J labels) is checked as follows.
  1. Phi: vertex-disjoint paths of G = J - z - r, pairing T = (even vertices of G) xor {g} for a
     single vertex g (inferred); lengths reported.
  2. D0: a decomposition of G - E(Phi) with e(v) = d(v) mod 2 at every vertex (Lovasz).
  3. A family is rebuilt by our own exhaustive search over Phi placements (separate member, or
     appended to the D0 path ending at one of its ends, meeting it only there), attachments (an end
     in N, injective), free pieces (only when d_J(r) < n - 2) and pairings (exact).  Success needs
     #pairs + #singletons + #free <= k and #singletons >= 2.
  4. The resulting paths of B = J - z are checked from scratch: simple paths of B, edge-disjoint,
     covering E(B), at most k of them, at least two ends at r.
usage: verify_drm.py FILE [-L maxlen]
"""
import sys, itertools
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from g6 import parse_g6


def parse_paths(tokens):
    return [[int(v) for v in t.split(',')] for t in tokens]


def is_path_in(adjset, p):
    return len(p) >= 2 and len(set(p)) == len(p) and all(b in adjset[a] for a, b in zip(p, p[1:]))


def edges_of(p):
    return [frozenset(e) for e in zip(p, p[1:])]


def max_pairs(members, keys):
    """maximum number of disjoint pairs of vertex-disjoint members (exact, brute force)."""
    best = 0
    keys = list(keys)

    def rec(i, used, cur):
        nonlocal best
        best = max(best, cur)
        if cur + (len(keys) - i) // 2 <= best:
            return
        while i < len(keys) and keys[i] in used:
            i += 1
        if i >= len(keys):
            return
        a = keys[i]
        for j in range(i + 1, len(keys)):
            b = keys[j]
            if b in used or members[a] & members[b]:
                continue
            rec(i + 1, used | {a, b}, cur + 1)
        rec(i + 1, used | {a}, cur)

    rec(0, frozenset(), 0)
    return best


def find_pairs(members, keys, need):
    keys = list(keys)

    def rec(rest, acc):
        if len(acc) == need:
            return list(acc)
        if len(rest) < 2 * (need - len(acc)):
            return None
        a = rest[0]
        for b in rest[1:]:
            if not (members[a] & members[b]):
                r_ = [x for x in rest[1:] if x != b]
                res = rec(r_, acc + [(a, b)])
                if res is not None:
                    return res
        return rec(rest[1:], acc)

    return rec(keys, [])


def verify_line(line, Lmax=None):
    f = line.split()
    assert f[0] == 'W'
    g6, r = f[1], int(f[2])
    i0 = f.index('D0:'); i1 = f.index('PHI:')
    D0 = parse_paths(f[i0 + 1:i1])
    PHI = parse_paths(f[i1 + 1:])
    n, adj = parse_g6(g6)
    z = [v for v in range(n) if len(adj[v]) % 2 == 0]
    if len(z) != 1:
        return 'z not unique'
    z = z[0]
    k = (n - 1) // 2
    B = {v: set(adj[v]) - {z} for v in range(n) if v != z}
    if r not in adj[z]:
        return 'r not in N(z)'
    N = set(B[r])
    G = {v: set(B[v]) - {r} for v in B if v != r}
    EG = {v for v in G if G[v] and len(G[v]) % 2 == 0}
    # 1. Phi
    phiE = []
    for p in PHI:
        if not is_path_in(G, p):
            return 'Phi path not a path of G: %s' % p
        if Lmax and len(p) - 1 > Lmax:
            return 'Phi path too long'
        phiE += edges_of(p)
    for p, q in itertools.combinations(PHI, 2):
        if set(p) & set(q):
            return 'Phi paths not disjoint'
    T = set()
    for p in PHI:
        T |= {p[0], p[-1]}
    gset = EG ^ T
    if len(gset) > 1:
        return 'Phi does not pair (even vertices) xor {g}: %s' % sorted(gset)
    # 2. D0 is a Lovasz decomposition of G - Phi
    Gm = {v: set(G[v]) for v in G}
    for e in phiE:
        a, b = tuple(e)
        Gm[a].discard(b); Gm[b].discard(a)
    used = Counter()
    ends = Counter()
    for p in D0:
        if not is_path_in(Gm, p):
            return 'D0 path not a path of G - Phi: %s' % p
        for e in edges_of(p):
            used[e] += 1
        ends[p[0]] += 1; ends[p[-1]] += 1
    allE = {frozenset((a, b)) for a in Gm for b in Gm[a]}
    if set(used) != allE or any(c != 1 for c in used.values()):
        return 'D0 does not partition E(G - Phi)'
    for v in Gm:
        if ends[v] != len(Gm[v]) % 2:
            return 'D0 not Lovasz at %d' % v
    # 3. rebuild a family
    freeOK = len(adj[r]) < n - 2
    pieces0 = [list(p) for p in D0]
    sols = []

    def place(j, pieces):
        if j == len(PHI):
            yield [list(p) for p in pieces]
            return
        q = PHI[j]
        yield from place(j + 1, pieces + [list(q)])
        for t in (0, 1):
            u = q[0] if t == 0 else q[-1]
            qq = q if t == 1 else q[::-1]          # qq ends at u ... wait: orient qq to START at u
            qs = q if q[0] == u else q[::-1]       # starts at u
            for i, p in enumerate(pieces):
                if u not in (p[0], p[-1]):
                    continue
                if set(p) & set(qs) != {u}:
                    continue
                pp = p if p[-1] == u else p[::-1]  # ends at u
                newp = pp + qs[1:]
                yield from place(j + 1, pieces[:i] + [newp] + pieces[i + 1:])

    for pieces in place(0, pieces0):
        opts = []
        for p in pieces:
            o = []
            for e in {p[0], p[-1]}:
                if e in N:
                    o.append(e)
            if freeOK:
                o.append(None)
            opts.append(o)
        for choice in itertools.product(*opts):
            atts = [c for c in choice if c is not None]
            if len(set(atts)) != len(atts):
                continue
            F = sum(1 for c in choice if c is None)
            members = {}
            orient = {}
            for p, c in zip(pieces, choice):
                if c is not None:
                    pp = p if p[-1] == c else p[::-1]
                    members[c] = set(pp); orient[c] = pp
            for x in N:
                if x not in members:
                    members[x] = {x}; orient[x] = [x]
            need = max(0, len(N) + F - k)
            if len(N) - 2 * need < 2:
                continue
            pr = find_pairs(members, sorted(N), need)
            if pr is None:
                continue
            # 4. build and verify
            inpair = {v for a, b in pr for v in (a, b)}
            paths = [orient[a] + [r] + orient[b][::-1] for a, b in pr]
            paths += [orient[x] + [r] for x in sorted(N) if x not in inpair]
            paths += [p for p, c in zip(pieces, choice) if c is None]
            err = check_B(B, paths, r, k)
            return err if err else None
    return 'no family found from this witness'


def check_B(B, paths, r, k):
    EB = {frozenset((a, b)) for a in B for b in B[a]}
    seen = set()
    er = 0
    for p in paths:
        if not is_path_in(B, p):
            return 'not a path of B'
        for e in edges_of(p):
            if e in seen:
                return 'edge twice'
            seen.add(e)
        er += (p[0] == r) + (p[-1] == r)
    if seen != EB:
        return 'edges of B not covered'
    if len(paths) > k:
        return 'too many paths %d > %d' % (len(paths), k)
    if er < 2:
        return 'ends at r = %d' % er
    return None


if __name__ == '__main__':
    fn = sys.argv[1]
    Lmax = int(sys.argv[3]) if len(sys.argv) > 3 else None
    C = Counter()
    maxlen = Counter()
    for line in open(fn):
        if not line.startswith('W '):
            continue
        err = verify_line(line, Lmax)
        C['ok' if err is None else 'FAIL'] += 1
        if err:
            print('FAIL', line.strip()[:80], err)
        f = line.split(); i1 = f.index('PHI:')
        for t in f[i1 + 1:]:
            maxlen[len(t.split(',')) - 1] += 1
        maxlen['#Phi=%d' % len(f[i1 + 1:])] += 1
    print(dict(C), 'Phi path lengths / counts:', dict(sorted(maxlen.items(), key=str)))
