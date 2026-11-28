"""A39: the two-connector extension of Theorem B (dense-root §8, item 1: "extends verbatim").

Search for a graph B (order 2k, d_B(r) = 2k - 2) with two vertex-disjoint connectors
Q1 = q1 y q2, Q2 = q3 y' q4 (interiors y, y' in N, ends in N) such that every vertex of N is odd in
G' = G - E(Q1) - E(Q2), and a Lovasz decomposition of G' containing an L-path with ends y and y'.
Then y and y' must both be attachments of L-paths (else a trivial member lies on a connector, and
the C-members are not pairwise compatible), but they are the two ends of ONE L-path: the attachment
scheme of Theorem B cannot be applied verbatim.
"""
import sys, itertools, random
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from literal_AB import lovasz_decomps


def search(k, seed, tries=20000):
    rng = random.Random(seed)
    n = 2 * k
    r, s = 0, n - 1
    N = list(range(1, n - 1))
    for it in range(tries):
        q1, y, q2, q3, y2, q4 = rng.sample(N, 6)
        G = {v: set() for v in range(1, n)}
        for a, b in itertools.combinations(range(1, n), 2):
            if rng.random() < 0.45:
                G[a].add(b); G[b].add(a)
        for a, b in ((q1, y), (y, q2), (q3, y2), (y2, q4)):
            G[a].add(b); G[b].add(a)
        Gp = {v: set(G[v]) for v in G}
        for a, b in ((q1, y), (y, q2), (q3, y2), (y2, q4)):
            Gp[a].discard(b); Gp[b].discard(a)
        # fix parities in G' : all of N odd (toggle edges not on the connectors)
        wrong = [x for x in N if len(Gp[x]) % 2 == 0]
        if len(wrong) % 2:
            wrong.append(s)
        rng.shuffle(wrong)
        for a, b in zip(wrong[::2], wrong[1::2]):
            if b in Gp[a]:
                Gp[a].discard(b); Gp[b].discard(a)
            else:
                Gp[a].add(b); Gp[b].add(a)
        if any(len(Gp[x]) % 2 == 0 for x in N):
            continue
        if any(b in Gp[a] for a, b in ((q1, y), (y, q2), (q3, y2), (y2, q4))):
            continue          # a toggle re-added a connector edge: G' and E(Q) must be disjoint
        Ds = lovasz_decomps(Gp, cap=200, nodecap=20000)
        for D in Ds:
            for p in D:
                if {p[0], p[-1]} == {y, y2}:
                    return dict(k=k, Q1=(q1, y, q2), Q2=(q3, y2, q4), s=s, r=r,
                                Gprime={v: sorted(Gp[v]) for v in Gp}, D=D, Lpath=p)
    return None


if __name__ == '__main__':
    res = search(int(sys.argv[1]) if len(sys.argv) > 1 else 5, 1)
    if res is None:
        print('not found')
    else:
        for kk, v in res.items():
            print(kk, v)
        print('=> the L-path', res['Lpath'], 'joins the interior vertices', res['Q1'][1], 'and',
              res['Q2'][1], 'of the two connectors; one of them must be its far end, hence a',
              'trivial member on a connector (C-members not pairwise compatible).')
