"""A39: verify ret.c YES witnesses from scratch: the members form a family at r (each x in N(r)
has one member, a path of B - r ending at x or trivial; nontrivial members partition E(B - r)),
the listed pairs are disjoint and vertex-disjoint, and Lemma 2.1 gives a decomposition of B into
at most k paths with >= 2 ends at r (checked as a decomposition of B).
usage: verify_ret.py FILE...   (lines: g6-of-B r YES q | att:v0,..,vl ; ... | a-b ... | nodes=..)"""
import sys
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from g6 import parse_g6
from verify_drm import check_B


def verify(line):
    parts = line.rstrip('\n').split(' | ')
    head = parts[0].split()
    g6, r = head[0], int(head[1])
    n, adj = parse_g6(g6)
    B = {v: set(adj[v]) for v in range(n)}
    k = n // 2
    N = set(B[r])
    mem = {}
    for tok in parts[1].split(';'):
        tok = tok.strip()
        if not tok:
            continue
        a, seq = tok.split(':')
        a = int(a); seq = [int(x) for x in seq.split(',')]
        if seq[0] != a or a not in N or a in mem:
            return 'bad attachment'
        mem[a] = seq
    if set(mem) != N:
        return 'members != N(r)'
    G = {v: B[v] - {r} for v in B if v != r}
    used = Counter()
    for a, seq in mem.items():
        if len(set(seq)) != len(seq) or r in seq:
            return 'member not a path of G'
        for x, y in zip(seq, seq[1:]):
            if y not in G[x]:
                return 'non-edge in member'
            used[frozenset((x, y))] += 1
    EG = {frozenset((a, b)) for a in G for b in G[a]}
    if set(used) != EG or any(c != 1 for c in used.values()):
        return 'members do not partition E(G)'
    pairs = []
    for tok in parts[2].split():
        a, b = map(int, tok.split('-'))
        pairs.append((a, b))
    flat = [v for p in pairs for v in p]
    if len(set(flat)) != len(flat):
        return 'pairs not disjoint'
    for a, b in pairs:
        if set(mem[a]) & set(mem[b]):
            return 'paired members meet'
    if len(pairs) == k - 1:          # k - 1 pairs: unpair one (Lemma 2.1 with k - 2 pairs)
        pairs = pairs[:-1]
        flat = [v for p in pairs for v in p]
    singles = [x for x in N if x not in flat]
    paths = [mem[a][::-1] + [r] + mem[b] for a, b in pairs] + [mem[x][::-1] + [r] for x in singles]
    return check_B(B, paths, r, k)


if __name__ == '__main__':
    for fn in sys.argv[1:]:
        C = Counter()
        for line in open(fn):
            f = line.split()
            if len(f) < 3:
                continue
            if f[2] != 'YES':
                C[f[2]] += 1
                continue
            err = verify(line)
            C['ok' if err is None else 'FAIL'] += 1
            if err:
                print('FAIL', line[:60], err)
        print(fn.rsplit('/', 1)[-1], dict(C))
