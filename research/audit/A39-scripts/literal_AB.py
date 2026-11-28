"""A39: run the proofs of Theorems A and B literally and check every claim they make.

For a root r of B (|B| = 2k, d_B(r) = 2k - 2, non-neighbour s), and
  Theorem A: G = B - r with <= 1 vertex of positive even degree;
  Theorem B: a connector Q (length 1 or 2, ends in N, all of N odd in G' = G - E(Q)),
we enumerate EVERY Lovasz decomposition (every odd vertex an end exactly once, even vertices none)
of G (resp. G'), apply the paper's attachment rules with EVERY tie-break, and check
  (A1/B1) attachments distinct and in N; no trivial member on V(Q) (B);
  (B2)    exactly one L-path has its far end at q_Q;
  (B3)    the designated pairs (trivial, heavier attachment) are disjoint, inside N - V(Q), and at
          most delta trivial members are unpaired;
  (B4)    at most lambda L-paths meet V(Q);
  (A5/B5) for EVERY set S of t >= 3 A-paths: both upper bounds on |J_S| of the proof
          (these must hold whether or not the degree condition holds);
  (H)     if t + |J_S| <= k + 1 for all S (in particular when the degree condition holds),
          a matching of defect <= 2 exists, and the Lemma 2.1 / Thm 2.3 reassembly yields a
          decomposition of B into k paths with exactly two ends at r (verified from scratch).
A violation of any of these is printed.  The degree condition implying (H) is also checked.

usage: literal_AB.py J9                 all order-9 degree-7 roots (all connectors)
       literal_AB.py rand K COUNT SEED [CAP NODECAP]  random B of order 2K (both theorems)
"""
import sys, itertools, random
from collections import Counter, defaultdict
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from g6 import parse_g6

STATS = Counter()
VIOL = []


def viol(msg):
    VIOL.append(msg)
    if len(VIOL) <= 30:
        print('VIOLATION', msg)


# ---------------- Lovasz decompositions ----------------
def lovasz_decomps(Gadj, cap=10 ** 6, nodecap=None):
    """All path decompositions of the graph Gadj (dict v -> set) with e(v) = d(v) mod 2
    (the first `cap` found, within `nodecap` search nodes if given)."""
    verts = sorted(Gadj)
    odd = {v for v in verts if len(Gadj[v]) % 2 == 1}
    rem = {v: set(Gadj[v]) for v in verts}
    used_end = set()
    paths = []
    out = []
    nodes = [0]

    def solve():
        nodes[0] += 1
        if len(out) >= cap or (nodecap and nodes[0] > nodecap):
            return
        if all(not rem[v] for v in verts):
            if used_end == odd:
                out.append([list(p) for p in paths])
            return
        for x in odd:
            if x not in used_end and not rem[x]:
                return
        cand = [x for x in verts if x in odd and x not in used_end and rem[x]]
        if not cand:
            return
        v = cand[0]
        used_end.add(v)
        seq = [v]
        extend(seq, {v})
        used_end.discard(v)

    def extend(seq, onpath):
        nodes[0] += 1
        if len(out) >= cap or (nodecap and nodes[0] > nodecap):
            return
        v = seq[-1]
        if len(seq) > 1 and v in odd and v not in used_end:
            used_end.add(v)
            paths.append(list(seq))
            solve()
            paths.pop()
            used_end.discard(v)
        for w in sorted(rem[v]):
            if w in onpath:
                continue
            rem[v].discard(w); rem[w].discard(v)
            seq.append(w); onpath.add(w)
            extend(seq, onpath)
            seq.pop(); onpath.discard(w)
            rem[v].add(w); rem[w].add(v)

    solve()
    return out


# ---------------- matching / reassembly / verification ----------------
def max_matching(left, right, compat):
    """left, right: lists of ids; compat(l, r) -> bool.  Kuhn's algorithm."""
    match_r = {}

    def aug(l, seen):
        for rr in right:
            if rr in seen or not compat(l, rr):
                continue
            seen.add(rr)
            if rr not in match_r or aug(match_r[rr], seen):
                match_r[rr] = l
                return True
        return False

    for l in left:
        aug(l, set())
    return {l: rr for rr, l in match_r.items()}


def verify_decomp(Badj, paths, r, k):
    E = set()
    for v in Badj:
        for w in Badj[v]:
            E.add(frozenset((v, w)))
    seen = set()
    ends_r = 0
    for p in paths:
        if len(p) < 2 or len(set(p)) != len(p):
            return 'not a path %s' % p
        for a, b in zip(p, p[1:]):
            e = frozenset((a, b))
            if e not in E:
                return 'non-edge %s' % (e,)
            if e in seen:
                return 'edge twice %s' % (e,)
            seen.add(e)
        ends_r += (p[0] == r) + (p[-1] == r)
    if seen != E:
        return 'edges missing'
    if len(paths) != k:
        return 'size %d != k' % len(paths)
    if ends_r != 2:
        return 'ends at r = %d' % ends_r
    return None


def reassemble(member, Aids, Cids, M, r, k):
    """member[x] = path list ending at x (attachment x), [x] if trivial.  Aids: attachments of
    A-paths; Cids: C-member vertices.  M: matching dict A-attachment -> C-vertex (|M| >= k-3).
    Returns list of paths of B per Theorem 2.3 / Lemma 2.1."""
    M = dict(M)
    if len(M) == k - 1:
        M.pop(next(iter(M)))
    unA = [a for a in Aids if a not in M]
    unC = [c for c in Cids if c not in M.values()]
    assert len(unA) == len(unC) and 1 <= len(unA) <= 2
    pairs = list(M.items())
    singles = list(unA)
    if len(unC) == 2:
        pairs.append((unC[0], unC[1]))
    else:
        singles.append(unC[0])
    paths = []
    for x, y in pairs:
        px = member[x]          # far ... x
        py = member[y]
        paths.append(px + [r] + py[::-1])
    for x in singles:
        paths.append(member[x] + [r])
    return paths


def oriented(p, att):
    """path p as a list ending at att."""
    if p[-1] == att:
        return list(p)
    assert p[0] == att
    return p[::-1]


# ---------------- common data ----------------
class Root:
    def __init__(self, Badj, r):
        self.B = Badj
        self.r = r
        V = sorted(Badj)
        self.k = len(V) // 2
        self.N = sorted(Badj[r])
        non = [v for v in V if v != r and v not in Badj[r]]
        assert len(non) == 1 and len(self.N) == 2 * self.k - 2
        self.s = non[0]
        self.G = {v: set(Badj[v]) - {r} for v in V if v != r}
        self.dB = {v: len(Badj[v]) for v in V}


def condA(R):
    k, N, G, dB = R.k, R.N, R.G, R.dB
    if any(dB[x] < 2 for x in N):
        return None
    pe = [v for v in G if len(G[v]) > 0 and len(G[v]) % 2 == 0]
    if len(pe) > 1:
        return None
    eps = 1 if any(len(G[x]) % 2 == 0 for x in N) else 0
    h = lambda t: sum(1 for x in N if dB[x] >= 2 * t)
    ok = all((h(t) + eps) // 2 + t <= k + 1 or h(t + 1) // 2 + eps + 2 * t <= k + 1
             for t in range(3, k))
    return ok, eps, h


def tie_options(cands_by_path):
    return itertools.product(*cands_by_path)


def check_S_bounds_and_hall(R, Apaths, member_vs, Cvs, bound1, bound2, tag):
    """Apaths: list of vertex sets of A-paths; member_vs: dict C-vertex -> vertex set of its member;
    Cvs: list of C-vertices.  bound1(t), bound2(t): the proof's two upper bounds on |J_S|.
    Returns True iff the Hall condition holds for all S with t >= 3."""
    k = R.k
    hall = True
    m = len(Apaths)
    for t in range(3, m + 1):
        for S in itertools.combinations(range(m), t):
            JS = [c for c in Cvs if all(member_vs[c] & Apaths[i] for i in S)]
            if len(JS) > bound1(t):
                viol('%s bound1 t=%d |J_S|=%d > %d' % (tag, t, len(JS), bound1(t)))
            if len(JS) > bound2(t):
                viol('%s bound2 t=%d |J_S|=%d > %d' % (tag, t, len(JS), bound2(t)))
            if t + len(JS) > k + 1:
                hall = False
    return hall


def do_hall_and_reassemble(R, members, Aatt, Cvs, tag):
    k, r = R.k, R.r
    vs = {x: set(members[x]) for x in members}
    M = max_matching(Aatt, Cvs, lambda a, c: not (vs[a] & vs[c]))
    if len(M) < k - 3:
        viol('%s Hall holds but matching %d < k-3' % (tag, len(M)))
        return
    paths = reassemble(members, Aatt, Cvs, M, r, k)
    err = verify_decomp(R.B, paths, r, k)
    if err:
        viol('%s reassembly: %s' % (tag, err))
    else:
        STATS['reassembled'] += 1


# ---------------- Theorem A, literally ----------------
def run_A(R, tag, cap=10 ** 6, nodecap=None):
    c = condA(R)
    if c is None:
        return None
    ok, eps, h = c
    k, N, G, dB, s = R.k, R.N, R.G, R.dB, R.s
    Nset = set(N)
    g = [x for x in N if len(G[x]) % 2 == 0]
    g = g[0] if g else None
    Ds = lovasz_decomps(G, cap, nodecap)
    STATS['A:decomps'] += len(Ds)
    for D in Ds:
        if len(D) != k - 1:
            viol('%s A: |D| = %d != k-1' % (tag, len(D)))
            continue
        # attachment candidates per path
        cands = []
        for p in D:
            a, b = p[0], p[-1]
            if a == s or b == s:
                if a == s and b == s:
                    viol('%s A: both ends s' % tag)
                cands.append([b if a == s else a])
            elif a not in Nset or b not in Nset:
                viol('%s A: end outside N u {s}' % tag)
                cands.append([a])
            elif dB[a] > dB[b]:
                cands.append([a])
            elif dB[b] > dB[a]:
                cands.append([b])
            else:
                cands.append([a, b])
        for atts in tie_options(cands):
            STATS['A:plans'] += 1
            if len(set(atts)) != len(atts):
                viol('%s A: attachments not distinct' % tag)
                continue
            members = {}
            far = {}
            for p, a in zip(D, atts):
                members[a] = oriented(p, a)
                far[a] = members[a][0]
            triv = [x for x in N if x not in members]
            if len(triv) != k - 1:
                viol('%s A: #trivial %d' % (tag, len(triv)))
            for x in triv:
                members[x] = [x]
            exp_triv = set([g] if g is not None else []) | {far[a] for a in far if far[a] in Nset}
            if set(triv) != exp_triv:
                viol('%s A: trivial members != g + far ends in N' % tag)
            # paths through x: (d_G + e)/2 = floor(d_B/2)
            for x in N:
                on = sum(1 for p in D if x in p)
                if on != dB[x] // 2:
                    viol('%s A: x on %d paths, floor(dB/2)=%d' % (tag, on, dB[x] // 2))
            Apaths = [set(p) for p in D]
            vs = {x: set(members[x]) for x in triv}
            b1 = lambda t: (h(t) + eps) // 2
            b2 = lambda t: t + h(t + 1) // 2 + eps
            hall = check_S_bounds_and_hall(R, Apaths, vs, triv, b1, b2, tag + ' A')
            if ok and not hall:
                viol('%s A: degree condition holds but Hall fails' % tag)
            if hall:
                do_hall_and_reassemble(R, members, list(atts), triv, tag + ' A')
    return ok


# ---------------- Theorem B, literally ----------------
def connectors(R):
    N, G = R.N, R.G
    Nset = set(N)
    out = []
    for a, b in itertools.combinations(N, 2):
        if b in G[a]:
            out.append((a, b))
        for y in G:
            if y not in (a, b) and y in G[a] and y in G[b]:
                out.append((a, y, b))
    good = []
    for Q in out:
        loss = Counter()
        for u, v in zip(Q, Q[1:]):
            loss[u] += 1; loss[v] += 1
        if all((len(G[x]) - loss[x]) % 2 == 1 for x in N):
            good.append(Q)
    return good


def condB(R, Q, Gp):
    k, N, dB = R.k, R.N, R.dB
    Nset = set(N)
    delta = 1 if len(Q) == 3 and Q[1] in Nset else 0
    lam = sum(-(-len(Gp[v]) // 2) for v in Q)
    Nt = [x for x in N if x not in Q]
    ht = lambda t: sum(1 for x in Nt if dB[x] >= 2 * t)
    ok = all((ht(t) + delta) // 2 + (lam >= t) + t <= k + 1 or
             (ht(t + 1) + delta) // 2 + (lam >= t) + 2 * t <= k + 1 for t in range(3, k))
    return ok, delta, lam, ht


def run_B(R, Q, tag, cap=10 ** 6, nodecap=None):
    k, N, G, dB, s = R.k, R.N, R.G, R.dB, R.s
    if any(dB[x] < 2 for x in N):
        return None
    Nset = set(N)
    Gp = {v: set(G[v]) for v in G}
    for u, v in zip(Q, Q[1:]):
        Gp[u].discard(v); Gp[v].discard(u)
    ok, delta, lam, ht = condB(R, Q, Gp)
    q1, q2 = Q[0], Q[-1]
    VQ = set(Q)
    if len(Gp[s]) % 2 != 0:
        viol('%s B: s odd in G\'' % tag)
    Ds = lovasz_decomps(Gp, cap, nodecap)
    STATS['B:decomps'] += len(Ds)
    for D in Ds:
        if len(D) != k - 1:
            viol('%s B: |D| = %d' % (tag, len(D)))
            continue
        P = {}
        for i, p in enumerate(D):
            for e in (p[0], p[-1]):
                if e not in Nset:
                    viol('%s B: L-path end outside N' % tag)
                P[e] = i
        o = {}
        for p in D:
            o[p[0]] = p[-1]; o[p[-1]] = p[0]
        # enumerate the plans the proof allows (all tie-breaks / symmetric choices)
        plans = []   # (qQ, forced: dict pathindex -> attachment, pairs: list (triv, att), unpaired)

        def case1(qa, qb, forced, extra_unpaired):
            # Q = q1 q2 or q1 s q2 (or the q1,q2 part of case 2)
            res = []
            if P[qa] == P[qb]:
                for (x, y) in ((qa, qb), (qb, qa)):     # attach path at y, Q at x (symmetric)
                    f = dict(forced); f[P[qa]] = y
                    res.append((x, f, [], list(extra_unpaired)))
            else:
                a, b = o[qa], o[qb]
                opts = []
                if dB[b] <= dB[a]:
                    opts.append((qa, a, qb, b))   # Q at qa, P(qa) at a, P(qb) at qb, b trivial
                if dB[a] <= dB[b]:
                    opts.append((qb, b, qa, a))   # symmetric
                for (x, attx, yy, trivv) in opts:
                    f = dict(forced); f[P[x]] = attx; f[P[yy]] = yy
                    res.append((x, f, [(trivv, attx)], list(extra_unpaired)))
            return res

        if delta == 0:
            plans += case1(q1, q2, {}, [])
        else:
            y = Q[1]
            if o[y] in (q1, q2):
                qq = o[y]                     # o(y) = qq: P(y) at y, Q at qq, P(other) at other
                other = q1 if qq == q2 else q2
                f = {P[y]: y, P[other]: other}
                plans.append((qq, f, [], [o[other]]))
            else:
                plans += case1(q1, q2, {P[y]: y}, [o[y]])
        for (qQ, forced, pairs0, unpaired) in plans:
            # other paths: larger d_B, all tie-breaks
            free = [i for i in range(len(D)) if i not in forced]
            cands = []
            for i in free:
                a, b = D[i][0], D[i][-1]
                if dB[a] > dB[b]:
                    cands.append([a])
                elif dB[b] > dB[a]:
                    cands.append([b])
                else:
                    cands.append([a, b])
            for choice in tie_options(cands):
                STATS['B:plans'] += 1
                att = dict(forced)
                for i, a in zip(free, choice):
                    att[i] = a
                atts = [att[i] for i in range(len(D))]
                allatt = atts + [qQ]
                if len(set(allatt)) != len(allatt) or not set(allatt) <= Nset:
                    viol('%s B: attachments not distinct / not in N: %s' % (tag, allatt))
                    continue
                members = {}
                for i, a in enumerate(atts):
                    members[a] = oriented(D[i], a)
                members[qQ] = oriented(list(Q), qQ)
                triv = [x for x in N if x not in members]
                for x in triv:
                    members[x] = [x]
                # (B1) no trivial member on Q
                if any(x in VQ for x in triv):
                    viol('%s B1: trivial member on Q' % tag)
                if len(triv) != k - 2:
                    viol('%s B: #trivial = %d' % (tag, len(triv)))
                # (B2) exactly one L-path has far end q_Q
                nfar = sum(1 for i, a in enumerate(atts) if members[a][0] == qQ)
                if nfar != 1:
                    viol('%s B2: %d L-paths with far end q_Q' % (tag, nfar))
                # (B3) pairs
                pairs = list(pairs0)
                for i in free:
                    a = att[i]
                    pairs.append((members[a][0], a))
                paired_triv = [p[0] for p in pairs]
                if sorted(paired_triv + unpaired) != sorted(triv):
                    viol('%s B3: pairs+unpaired != trivial members (%s, %s, %s)' %
                         (tag, pairs, unpaired, triv))
                flat = [v for p in pairs for v in p]
                if len(set(flat)) != len(flat):
                    viol('%s B3: pairs not disjoint' % tag)
                if any(v in VQ or v not in Nset for v in flat):
                    viol('%s B3: pair vertex not in N - V(Q)' % tag)
                if any(dB[t_] > dB[a_] for t_, a_ in pairs):
                    viol('%s B3: attachment lighter than its trivial partner' % tag)
                if len(unpaired) > delta:
                    viol('%s B3: %d unpaired > delta' % (tag, len(unpaired)))
                if any(u_ in VQ for u_ in unpaired):
                    viol('%s B3: unpaired trivial on Q' % tag)
                # own path: every trivial member is the far end of exactly one L-path
                for x in triv:
                    nown = sum(1 for a in atts if members[a][0] == x)
                    if nown != 1:
                        viol('%s B: trivial %s has %d own paths' % (tag, x, nown))
                # (B4) lambda
                meet = sum(1 for p in D if VQ & set(p))
                if meet > lam:
                    viol('%s B4: %d L-paths meet V(Q) > lambda=%d' % (tag, meet, lam))
                # x in N - V(Q) on d_B/2 L-paths
                for x in N:
                    if x in VQ:
                        continue
                    on = sum(1 for p in D if x in p)
                    if 2 * on != dB[x]:
                        viol('%s B: x on %d L-paths, dB=%d' % (tag, on, dB[x]))
                Apaths = [set(p) for p in D]
                Cvs = triv + [qQ]
                vs = {c: set(members[c]) for c in Cvs}
                b1 = lambda t: (ht(t) + delta) // 2 + (lam >= t)
                b2 = lambda t: t + (ht(t + 1) + delta) // 2 + (lam >= t)
                hall = check_S_bounds_and_hall(R, Apaths, vs, Cvs, b1, b2, tag + ' B%d' % delta)
                if ok and not hall:
                    viol('%s B: degree condition holds but Hall fails' % tag)
                if hall:
                    do_hall_and_reassemble(R, members, atts, Cvs, tag + ' B')
    return ok


# ---------------- drivers ----------------
def run_J9():
    ROOT = '/home/user/Manuscripts/manuscripts'
    C = Counter()
    for l in open(ROOT + '/multi-token/data/J9_d6.g6'):
        g = l.split()[0]
        n, adj = parse_g6(g)
        z = [v for v in range(n) if len(adj[v]) % 2 == 0][0]
        Badj = {v: set(adj[v]) - {z} for v in range(n) if v != z}
        for r in sorted(adj[z]):
            if len(adj[r]) != n - 2:
                continue
            R = Root(Badj, r)
            tag = '%s r=%d' % (g, r)
            a = run_A(R, tag)
            if a is not None:
                C['A applicable'] += 1; C['A cond'] += a
            Bok = False
            for Q in connectors(R):
                b = run_B(R, Q, tag + ' Q=%s' % (Q,))
                C['B connectors'] += 1
                C['B connectors, delta=%d' % (1 if len(Q) == 3 and Q[1] in set(R.N) else 0)] += 1
                Bok = Bok or b
            C['B cond (some Q)'] += Bok
            C['roots'] += 1
    print(dict(C))


def random_B(k, p, rng, mode):
    """mode 'A': N all odd in G except at most one; mode 'B': exactly two even vertices of N."""
    n = 2 * k
    V = list(range(n))
    r, s = 0, n - 1
    N = list(range(1, n - 1))
    Gadj = {v: set() for v in V if v != r}
    W = [v for v in V if v != r]
    for a, b in itertools.combinations(W, 2):
        if rng.random() < p:
            Gadj[a].add(b); Gadj[b].add(a)
    if mode == 'A':
        target_even = set(rng.sample(N, 1)) if rng.random() < 0.5 else set()
    else:
        target_even = set(rng.sample(N, 2))
    wrong = [x for x in N if (len(Gadj[x]) % 2 == 0) != (x in target_even)]
    rng.shuffle(wrong)
    if len(wrong) % 2:
        wrong.append(s)
    for a, b in zip(wrong[::2], wrong[1::2]):
        if b in Gadj[a]:
            Gadj[a].discard(b); Gadj[b].discard(a)
        else:
            Gadj[a].add(b); Gadj[b].add(a)
    Badj = {v: set(Gadj.get(v, set())) for v in V}
    for x in N:
        Badj[r].add(x); Badj[x].add(r)
    return Badj, r


def run_rand(k, count, seed, cap=300, nodecap=20000):
    rng = random.Random(seed)
    C = Counter()
    for it in range(count):
        p = rng.choice([0.4, 0.55, 0.7, 0.85])
        mode = 'A' if it % 2 == 0 else 'B'
        Badj, r = random_B(k, p, rng, mode)
        R = Root(Badj, r)
        tag = 'rand k=%d it=%d' % (k, it)
        if mode == 'A':
            a = run_A(R, tag, cap=cap, nodecap=nodecap)
            if a is not None:
                C['A instances'] += 1; C['A cond'] += a
        else:
            for Q in connectors(R):
                b = run_B(R, Q, tag + ' Q=%s' % (Q,), cap=cap, nodecap=nodecap)
                if b is None:
                    continue
                d = 1 if len(Q) == 3 and Q[1] in set(R.N) else 0
                C['B instances d=%d' % d] += 1
                C['B cond d=%d' % d] += b
    print('k=%d' % k, dict(C))


if __name__ == '__main__':
    if sys.argv[1] == 'J9':
        run_J9()
    else:
        run_rand(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]),
                 int(sys.argv[5]) if len(sys.argv) > 5 else 300,
                 int(sys.argv[6]) if len(sys.argv) > 6 else 20000)
    print(dict(STATS))
    print('violations:', len(VIOL))
