"""Independent checker for certs_local.json and certs_bowtie.json (semantics of Prog.ok).

Checks for every certificate: the model edge set is the one prescribed by the rim code (and the
contact set), the held set H consists of model edges, exactly one model vertex is even after
holding H (seed parity, with T even and u, v odd in W), and the program tree is legal: at every
offer the receiver is not a donor, donors are distinct, each donor edge is held and not yet
restored, and the number of present model neighbours of the receiver with no end is smaller than
the total supply; every branch with a positive donor is checked; at every leaf all of H has been
restored and the end sum on the model equals (number of model vertices) - 1.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
RIM = [(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]


def check(c, n):
    E = {tuple(sorted(e)) for e in c['E']}
    want = {(0, t) for t in (1, 2, 3, 4)} | {RIM[i] for i in range(6) if c['code'] >> i & 1}
    if n == 7:
        want |= {(i, 5) for i in range(5) if c['Acode'] >> i & 1} | {(5, 6)}
    assert E == want, 'edge set'
    H = [tuple(sorted(h)) for h in c['H']]
    assert len(set(H)) == len(H) and set(H) <= E, 'held set'
    par = [0] * 5 + [1, 1][: n - 5]
    for a, b in H:
        par[a] ^= 1
        par[b] ^= 1
    assert par.count(0) == 1 and list(c['c0']) == par, 'seed'
    leaves = 0

    def walk(t, ins, cv):
        nonlocal leaves
        present = (E - set(H)) | ins
        if t[0] == 'done':
            assert ins == set(H), 'not all restored'
            assert sum(cv) == n - 1, 'sum'
            leaves += 1
            return
        _, ds, r, kids = t
        ds = list(ds)
        assert r not in ds and len(set(ds)) == len(ds)
        for d in ds:
            e = tuple(sorted((d, r)))
            assert e in H and e not in ins, 'donor edge'
        blank = sum(1 for a in range(n) if a != r and tuple(sorted((a, r))) in present and cv[a] == 0)
        assert blank < sum(cv[d] for d in ds), 'inequality'
        for d in ds:
            if cv[d] == 0:
                continue
            sub = kids[str(d)] if str(d) in kids else kids[d]
            nc = list(cv); nc[d] -= 1; nc[r] += 1
            walk(sub, ins | {tuple(sorted((d, r)))}, nc)

    walk(c['tree'], set(), list(c['c0']))
    return leaves


def main():
    loc = json.load(open(os.path.join(HERE, 'certs_local.json')))
    bow = json.load(open(os.path.join(HERE, 'certs_bowtie.json')))
    codes = sorted(c['code'] for c in loc)
    lv = sum(check(c, 5) for c in loc)
    bv = sum(check(c, 7) for c in bow)
    bcodes = sorted({c['code'] for c in bow})
    assert len(loc) == 38 and len(bow) == 93 and len(bcodes) == 3
    assert all(sorted(c['Acode'] for c in bow if c['code'] == k) == list(range(1, 32)) for k in bcodes)
    print(f'OK: {len(loc)} local certificates ({lv} leaves), {len(bow)} bowtie certificates '
          f'({bv} leaves) on rims {bcodes}')


if __name__ == '__main__':
    main()
