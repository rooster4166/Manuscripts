"""Generate the certificate tables used by the manuscript and by lean/GallaiLean/FiveEven.lean.

Labelled setting.  Model vertices 0..4 are the five even vertices T, with 0 = x adjacent to
1..4.  The rim is a graph on {1,2,3,4} given by a 6-bit code over the pairs
  RIM = [(1,2), (1,3), (1,4), (2,3), (2,4), (3,4)]
with maximum degree <= 2 (41 labelled rims).  For the 38 rims that are not perfect matchings
(bowties) we search a *local* certificate (model = T only, held edges inside K).  For the 3
bowtie rims we search, for each of the 31 nonempty contact sets A of u, a certificate on the
seven-site model (5 = u, 6 = v; edges u-A and u-v).  Output: certs_local.json, certs_bowtie.json.
"""
import itertools
import json
import os
from functools import lru_cache

RIM = [(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]
HERE = os.path.dirname(os.path.abspath(__file__))


def rim_edges(code):
    return [RIM[i] for i in range(6) if code >> i & 1]


def rim_ok(code):
    deg = [0] * 5
    for a, b in rim_edges(code):
        deg[a] += 1
        deg[b] += 1
    return max(deg) <= 2


def is_bowtie(code):
    E = rim_edges(code)
    return len(E) == 2 and len({v for e in E for v in e}) == 4


def search(n, E, H, par):
    held = list(H)
    present0 = [e for e in E if e not in H]
    p = list(par)
    for a, b in H:
        p[a] ^= 1
        p[b] ^= 1
    if sum(1 for q in p if q == 0) != 1:
        return None
    c0 = tuple(p)

    @lru_cache(maxsize=None)
    def rec(mask, c):
        if mask == (1 << len(held)) - 1:
            return ['done']
        adj = set(present0) | {held[i] for i in range(len(held)) if mask >> i & 1}
        for r in range(n):
            cand = [(held[i][0] if held[i][1] == r else held[i][1], i)
                    for i in range(len(held)) if not (mask >> i & 1) and r in held[i]]
            if not cand:
                continue
            blank = sum(1 for a in range(n) if a != r and tuple(sorted((a, r))) in adj and c[a] == 0)
            sat = []
            for k in range(1, len(cand) + 1):
                for S in itertools.combinations(cand, k):
                    if sum(c[t] for t, _ in S) <= blank:
                        continue
                    if any(set(T) <= set(S) for T in sat):
                        continue
                    sat.append(S)
                    kids = {}
                    ok = True
                    for t, i in S:
                        if c[t] == 0:
                            continue
                        nc = list(c); nc[t] -= 1; nc[r] += 1
                        sub = rec(mask | (1 << i), tuple(nc))
                        if sub is None:
                            ok = False
                            break
                        kids[t] = sub
                    if ok:
                        return ['offer', [t for t, _ in S], r, kids]
        return None

    t = rec(0, c0)
    return None if t is None else (list(c0), t)


def best(n, E, par):
    for k in range(0, len(E) + 1):
        for H in itertools.combinations(E, k):
            out = search(n, E, list(H), par)
            if out:
                return {'E': E, 'H': [list(h) for h in H], 'c0': out[0], 'tree': out[1]}
    return None


def main():
    local, bow = [], []
    for code in range(64):
        if not rim_ok(code):
            continue
        K = [(0, t) for t in (1, 2, 3, 4)] + rim_edges(code)
        if not is_bowtie(code):
            c = best(5, K, [0] * 5)
            assert c is not None, code
            c['code'] = code
            local.append(c)
        else:
            for Acode in range(1, 32):
                A = [i for i in range(5) if Acode >> i & 1]
                E = K + [(i, 5) for i in A] + [(5, 6)]
                c = best(7, [tuple(sorted(e)) for e in E], [0, 0, 0, 0, 0, 1, 1])
                assert c is not None, (code, Acode)
                c['code'] = code
                c['Acode'] = Acode
                bow.append(c)
    json.dump(local, open(os.path.join(HERE, 'certs_local.json'), 'w'))
    json.dump(bow, open(os.path.join(HERE, 'certs_bowtie.json'), 'w'))
    print(len(local), 'local certificates;', len(bow), 'bowtie certificates')


if __name__ == '__main__':
    main()
