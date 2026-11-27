"""A11 independent checker for bs-prescribed (written for the audit; shares no code with
manuscripts/bs-prescribed/scripts).

Semantics (the paper's Lemma 3 (Lovasz) + Lemma 4 (Fan) + Definition 5 + Lemma 6 + the
localisation paragraph after Lemma 6):
  * a model is a vertex set M, the edges of W inside M, and the parity of every M-vertex in W;
  * hold H (edges inside M); the seed end vector on M is (d_{W-H} mod 2), which must have exactly
    one 0 (Lovasz, exact form); every vertex outside M has one end throughout and is never blank;
  * a move (D -> r) needs: r not in D, every rd (d in D) held and not yet restored,
    sum_{d in D} b(d) > #{w in M : rw currently present, b(w) = 0};
    it branches on every d in D with b(d) >= 1 (adversarial donor), moving one end from d to r.
  * at a leaf all of H is restored.

Parts
  A. the eleven bowtie certificates, transcribed by hand from Table 2 and the A = T paragraph,
     checked at their representative and transported by explicit automorphisms to all 31 contact
     sets of all 3 labelled bowties (93 cases); every printed (supply > blanks) pair is compared,
     and every leaf must end with b = 1 at u, v and b = (2,2,0,0,0) on T with the printed S.
  B. Lemmas 10, 11, 12 (match, odd star, universal star) as certificate generators, tested on EVERY
     graph on five labelled even vertices (2^10) and every assignment of the lemma's letters that
     satisfies its hypotheses; then Proposition 13's explicit assignments on all 38 labelled rims.
  C. an exhaustive AND-OR search of our own: (i) bowtie with M = T (paper, end of Sec. 5: no certificate);
     (ii) M = T + u (paper: 25 of 31, exceptions ab, xab, cd, xcd, abcd, xabcd);
     (iii) M = T + u + v (all 31); (iv) the 38 non-bowtie rims with M = T (all certified);
     (v) all 41 one-universal cores x 31 contact sets with M = T + u + v (A6's bank).
"""
import itertools
import sys
from functools import lru_cache

T5 = 'xabcd'


def E(s):
    return frozenset(s)


def mk_edges(pairs):
    return {frozenset(p) for p in pairs}


# ---------------------------------------------------------------------------- engine

class Model:
    def __init__(self, verts, edges, odd):
        self.V = list(verts)
        self.E = set(edges)
        self.odd = set(odd)          # parity in W

    def seed(self, H):
        b = {}
        for w in self.V:
            p = 1 if w in self.odd else 0
            for h in H:
                if w in h:
                    p ^= 1
            b[w] = p
        return b


class Fail(Exception):
    pass


def run(model, H, prog, expect_seed=None, final_check=None, log=None):
    """prog: list of steps; a step is (donors, r, (sup, blk) or None, branches or None);
    branches: dict donor -> list of further steps (only for grouped steps, as the last step)."""
    H = {frozenset(h) for h in H}
    if not H <= model.E:
        raise Fail('held edge not in model: %s' % (H - model.E))
    b = model.seed(H)
    zeros = [w for w in model.V if b[w] == 0]
    if len(zeros) != 1:
        raise Fail('seed has %d even vertices %s' % (len(zeros), zeros))
    if expect_seed is not None and zeros != [expect_seed]:
        raise Fail('seed even vertex %s, printed %s' % (zeros, expect_seed))
    leaves = []

    def go(steps, restored, b):
        if not steps:
            if restored != H:
                raise Fail('not all held edges restored: %s' % (H - restored))
            leaves.append(dict(b))
            if final_check:
                final_check(b)
            return
        donors, r, printed, branches = steps[0]
        if r in donors or len(set(donors)) != len(donors):
            raise Fail('bad donor set')
        for d in donors:
            e = frozenset((d, r))
            if e not in H or e in restored:
                raise Fail('donor edge %s%s not held/unrestored' % (d, r))
        present = (model.E - H) | restored
        blk = sum(1 for w in model.V if w != r and frozenset((w, r)) in present and b[w] == 0)
        sup = sum(b[d] for d in donors)
        if not sup > blk:
            raise Fail('illegal move %s->%s: supply %d, blanks %d' % (donors, r, sup, blk))
        if printed is not None and printed != (sup, blk):
            raise Fail('printed %s but computed %s at %s->%s' % (printed, (sup, blk), donors, r))
        if log is not None:
            log.append((tuple(donors), r, sup, blk))
        for d in donors:
            if b[d] == 0:
                continue
            nb = dict(b); nb[d] -= 1; nb[r] += 1
            rest = branches[d] if branches is not None else steps[1:]
            if branches is not None and len(steps) != 1:
                raise Fail('grouped step with branches must be last in its list')
            go(rest, restored | {frozenset((d, r))}, nb)

    go(list(prog), frozenset(), b)
    return leaves


def S(d, r, sup=None, blk=None):
    return ((d,), r, None if sup is None else (sup, blk), None)


def G(ds, r, sup, blk, branches):
    return (tuple(ds), r, (sup, blk), branches)


# ---------------------------------------------------------------------------- Part A

BOWTIE = mk_edges(['xa', 'xb', 'xc', 'xd', 'ab', 'cd'])


def bowtie_model(K, A):
    edges = set(K) | {frozenset(('u', t)) for t in A} | {frozenset('uv')}
    return Model(list(T5) + ['u', 'v'], edges, odd={'u', 'v'})


def table():
    """Table 2 of the paper, transcribed from the .tex by hand: A -> (held, seed, prog, S)."""
    t = {}
    t['x'] = (['ab', 'cd', 'xu'], 'u', [S('b', 'a', 1, 0), S('d', 'c', 1, 0), S('x', 'u', 1, 0)], {'ac'})
    t['a'] = (['xb', 'cd', 'au'], 'u', [S('b', 'x', 1, 0), S('d', 'c', 1, 0), S('a', 'u', 1, 0)], {'xc'})
    t['ac'] = (['xb', 'cd', 'au'], 'u', [S('b', 'x', 1, 0), S('a', 'u', 1, 0), S('d', 'c', 1, 0)], {'xc'})
    t['ab'] = (['xa', 'cd', 'bu', 'uv'], 'v',
               [S('d', 'c', 1, 0), S('x', 'a', 1, 0), S('b', 'u', 1, 0), S('u', 'v', 2, 0)], {'ac'})
    t['abc'] = (['xa', 'bu', 'cu'], 'd', [S('x', 'a', 1, 0), S('c', 'u', 1, 0), S('u', 'b', 2, 1)], {'ab'})
    t['xac'] = (['xb', 'au', 'cu'], 'd', [S('u', 'a', 1, 0), S('c', 'u', 1, 0), S('x', 'b', 1, 0)], {'ab'})
    t['xabc'] = (['xa', 'bu', 'cu'], 'd', [S('u', 'b', 1, 0), S('c', 'u', 1, 0), S('x', 'a', 1, 0)], {'ab'})
    t['xa'] = (['xb', 'xc', 'xu', 'au'], 'd',
               [S('u', 'a', 1, 0),
                G('bc', 'x', 2, 1, {'b': [S('x', 'c', 2, 1), S('x', 'u', 1, 0)],
                                    'c': [S('x', 'b', 2, 0), S('x', 'u', 1, 0)]})], {'ac', 'ab'})
    t['abcd'] = (['xa', 'bu', 'cu', 'du', 'uv'], 'v',
                 [S('x', 'a', 1, 0), S('b', 'u', 1, 0),
                  G('cd', 'u', 2, 1, {'c': [S('u', 'd', 3, 2), S('u', 'v', 2, 0)],
                                      'd': [S('u', 'c', 3, 2), S('u', 'v', 2, 0)]})], {'ad', 'ac'})
    t['xab'] = (['cd', 'xu', 'au', 'bu', 'uv'], 'v',
                [S('d', 'c', 1, 0), S('x', 'u', 1, 0),
                 G('ab', 'u', 2, 1, {'a': [S('u', 'b', 3, 2), S('u', 'v', 2, 0)],
                                     'b': [S('u', 'a', 3, 2), S('u', 'v', 2, 0)]})], {'bc', 'ac'})
    return t


def xabcd_progs():
    """The A = T paragraph: x->u; {a,b}->u (t1); remaining three ->u (t2); u->s1; u->s2; u->v.
    Both orders of s1, s2 are generated (the text allows either). Printed: (1>0), (2>1), (3>2),
    supply 4 then 3 at the outward moves, (2>0) at u->v."""
    out = []
    for order in (0, 1):
        br1 = {}
        for t1 in 'ab':
            rest = [w for w in 'abcd' if w != t1]
            br2 = {}
            for t2 in rest:
                s = [w for w in rest if w != t2]
                if order:
                    s = s[::-1]
                br2[t2] = [S('u', s[0]), S('u', s[1]), S('u', 'v', 2, 0)]
            br1[t1] = [G(rest, 'u', 3, 2, br2)]
        out.append([S('x', 'u', 1, 0), G('ab', 'u', 2, 1, br1)])
    return out


def perm_apply(p, s):
    return ''.join(p.get(ch, ch) for ch in s)


def transport_prog(prog, p):
    out = []
    for donors, r, printed, branches in prog:
        nd = tuple(p.get(d, d) for d in donors)
        nb = None if branches is None else {p.get(k, k): transport_prog(v, p) for k, v in branches.items()}
        out.append((nd, p.get(r, r), printed, nb))
    return out


def bowtie_autos(K):
    """All permutations of T fixing nothing a priori that map BOWTIE onto K (x must go to the
    centre of K)."""
    res = []
    for perm in itertools.permutations(T5):
        p = dict(zip(T5, perm))
        img = {frozenset(p[c] for c in e) for e in BOWTIE}
        if img == set(K):
            res.append(p)
    return res


def final_checker(Sset, which):
    def chk(b):
        if b['u'] != 1 or b['v'] != 1:
            raise Fail('final b(u), b(v) = %d, %d' % (b['u'], b['v']))
        two = ''.join(sorted(w for w in T5 if b[w] == 2))
        rest = [b[w] for w in T5 if b[w] != 2]
        if len(two) != 2 or any(r != 0 for r in rest):
            raise Fail('final vector on T not (2,2,0,0,0): %s' % b)
        which.add(two)
        if Sset is not None and frozenset(two) not in Sset:
            raise Fail('final pair %s not among printed %s' % (two, Sset))
    return chk


def part_A():
    print('Part A: eleven bowtie certificates')
    t = table()
    # orbit structure: group of the bowtie and the 31 contact sets
    autos = bowtie_autos(BOWTIE)
    assert len(autos) == 8 and all(p['x'] == 'x' for p in autos)
    subsets = [''.join(c) for k in range(1, 6) for c in itertools.combinations(T5, k)]
    orbits = {frozenset(frozenset(perm_apply(p, A)) for p in autos) for A in subsets}
    reps = list(t) + ['xabcd']
    rep_orbits = [frozenset(frozenset(perm_apply(p, A)) for p in autos) for A in reps]
    assert len(orbits) == 11 and set(rep_orbits) == orbits, 'representatives do not hit 11 orbits'
    print('  group order 8, 31 contact sets in 11 orbits, the 11 printed representatives hit all 11')
    # representatives with the printed numbers
    nleaves = 0
    for A, (H, z, prog, Sp) in t.items():
        which = set()
        lv = run(bowtie_model(BOWTIE, A), [E(h) for h in H], prog, expect_seed=z,
                 final_check=final_checker({frozenset(s) for s in Sp}, which))
        nleaves += len(lv)
        assert which == set(''.join(sorted(s)) for s in Sp), (A, which, Sp)
    for prog in xabcd_progs():
        which = set()
        lv = run(bowtie_model(BOWTIE, 'xabcd'), [E(h) for h in ['xu', 'au', 'bu', 'cu', 'du', 'uv']],
                 prog, expect_seed='v', final_check=final_checker(None, which))
        nleaves += len(lv)
    print('  all 11 representatives legal with the printed (supply>blanks), seeds and pairs; '
          '%d leaves (A=T counted in both orders of s1,s2)' % nleaves)
    # transport to all 3 labelled bowties x 31 contact sets
    labelled = []
    for rim in [('ab', 'cd'), ('ac', 'bd'), ('ad', 'bc')]:
        labelled.append(mk_edges(['xa', 'xb', 'xc', 'xd'] + list(rim)))
    done = 0
    for K in labelled:
        maps = bowtie_autos(K)
        for A in subsets:
            ok = False
            for p in maps:
                inv = {v: k for k, v in p.items()}
                Arep = ''.join(sorted(perm_apply(inv, A), key=T5.index))
                if Arep in t:
                    H, z, prog, Sp = t[Arep]
                    progs = [prog]
                    Hs = H
                elif Arep == 'xabcd':
                    progs = xabcd_progs()
                    Hs = ['xu', 'au', 'bu', 'cu', 'du', 'uv']
                    z = 'v'
                else:
                    continue
                for pr in progs:
                    run(bowtie_model(K, A), [E(perm_apply(p, h)) for h in Hs], transport_prog(pr, p),
                        expect_seed=p.get(z, z), final_check=final_checker(None, set()))
                ok = True
                break
            assert ok, (K, A)
            done += 1
    print('  transported certificates verified on %d labelled cases (3 bowties x 31 contact sets)' % done)


# ---------------------------------------------------------------------------- Part B

def five_model(K):
    return Model(list(T5), K, odd=set())


def adj(K, p, q):
    return frozenset((p, q)) in K


def lemma_match(K, p, q, p2, q2, z):
    H = [E(p + q), E(p2 + q2)]
    prog = [S(q, p), S(q2, p2)]
    return H, prog, {frozenset(p + p2)}


def hyp_match(K, p, q, p2, q2, z):
    return adj(K, p, q) and adj(K, p2, q2) and not adj(K, p, z) and not adj(K, p2, z) and not adj(K, p2, q)


def lemma_oddstar(K, a, w, p, q, z):
    H = [E(a + w), E(a + p), E(a + q)]
    prog = [S(w, a), G(p + q, a, None, None, {p: [S(a, q)], q: [S(a, p)]})]
    prog[1] = (tuple(p + q), a, None, {p: [S(a, q)], q: [S(a, p)]})
    return H, prog, {frozenset(a + p), frozenset(a + q)}


def hyp_oddstar(K, a, w, p, q, z):
    nb = {t for t in T5 if t != a and adj(K, a, t)}
    if nb != {w, p, q}:
        return False
    return (not all(adj(K, p, s) for s in (w, q, z))) and (not all(adj(K, q, s) for s in (w, p, z)))


def lemma_unistar(K, x, a, b, c, d):
    H = [E(x + a), E(x + b), E(x + c)]
    prog = [(tuple(a + b), x, None, {a: [S(x, b), S(x, c)], b: [S(x, a), S(x, c)]})]
    return H, prog, {frozenset(a + c), frozenset(b + c)}


def hyp_unistar(K, x, a, b, c, d):
    if not (adj(K, x, a) and adj(K, x, b) and adj(K, x, c)):
        return False
    if any(adj(K, c, t) for t in (a, b, d)):
        return False
    return (not (adj(K, a, b) and adj(K, a, d))) and (not (adj(K, b, a) and adj(K, b, d)))


LEMMAS = [('match', lemma_match, hyp_match), ('oddstar', lemma_oddstar, hyp_oddstar),
          ('unistar', lemma_unistar, hyp_unistar)]
PAIRS = [frozenset(e) for e in itertools.combinations(T5, 2)]


def all_graphs():
    for mask in range(1 << 10):
        yield {PAIRS[i] for i in range(10) if mask >> i & 1}


def part_B():
    print('Part B: Lemmas 10-12 on every graph on five labelled even vertices')
    for name, gen, hyp in LEMMAS:
        tested = 0
        for K in all_graphs():
            for lab in itertools.permutations(T5):
                if not hyp(K, *lab):
                    continue
                H, prog, Sset = gen(K, *lab)
                which = set()

                def fc(b, which=which):
                    two = frozenset(w for w in T5 if b[w] == 2)
                    if len(two) != 2 or any(b[w] not in (0, 2) for w in T5):
                        raise Fail('final vector %s' % b)
                    which.add(two)
                run(five_model(K), H, prog, final_check=fc)
                assert which <= Sset, (name, which, Sset)
                tested += 1
        print('  Lemma %-8s sound on all %d (graph, labelling) pairs meeting its hypotheses' % (name, tested))
    # Proposition 9 assignments on the 38 labelled rims
    rims = []
    RIMP = [frozenset(e) for e in itertools.combinations('abcd', 2)]
    for mask in range(64):
        R = {RIMP[i] for i in range(6) if mask >> i & 1}
        deg = {w: sum(1 for e in R if w in e) for w in 'abcd'}
        if max(deg.values()) <= 2:
            rims.append(R)
    assert len(rims) == 41
    nonbow = 0
    shapes = {}
    for R in rims:
        K = R | mk_edges(['xa', 'xb', 'xc', 'xd'])
        bow = len(R) == 2 and len(set().union(*R)) == 4
        if bow:
            continue
        nonbow += 1
        # classify the rim and build the paper's assignment
        degs = sorted(sum(1 for e in R if w in e) for w in 'abcd')
        found = None
        for lab in itertools.permutations('abcd'):
            A_, B_, C_, D_ = lab
            e = lambda s, t: frozenset((s, t)) in R
            if len(R) == 0:
                cand = ('unistar', ('x', A_, B_, C_, D_), '4K1')
            elif len(R) == 1 and e(A_, B_):
                cand = ('match', (A_, B_, C_, 'x', D_), 'K2+2K1')
            elif len(R) == 2 and e(A_, B_) and e(B_, C_):
                cand = ('match', (B_, C_, A_, 'x', D_), 'P3+K1')
            elif len(R) == 3 and e(A_, B_) and e(B_, C_) and e(C_, D_):
                cand = ('match', (B_, C_, A_, 'x', D_), 'P4')
            elif len(R) == 3 and e(A_, B_) and e(B_, C_) and e(A_, C_):
                cand = ('oddstar', (A_, 'x', B_, C_, D_), 'K3+K1')
            elif len(R) == 4 and e(A_, B_) and e(B_, C_) and e(C_, D_) and e(D_, A_):
                cand = ('oddstar', (A_, 'x', B_, D_, C_), 'C4')
            else:
                continue
            name, args, shape = cand
            gen, hyp = {n: (g, h) for n, g, h in LEMMAS}[name]
            if hyp(K, *args):
                H, prog, Sset = gen(K, *args)
                run(five_model(K), H, prog)
                found = shape
                break
        assert found, R
        shapes[found] = shapes.get(found, 0) + 1
    print('  Proposition 13 assignments valid on all %d labelled non-bowtie rims: %s' % (nonbow, shapes))


# ---------------------------------------------------------------------------- Part C

def search(model, allowed=None, maxheld=None):
    """Exhaustive: is there a certificate on the model? Returns (H, number of leaves) or None."""
    Eall = sorted((tuple(sorted(e)) for e in model.E))
    if allowed is not None:
        Eall = [e for e in Eall if frozenset(e) in allowed]
    V = model.V
    idx = {w: i for i, w in enumerate(V)}
    adjm = [[False] * len(V) for _ in V]
    for e in model.E:
        a, b = tuple(e)
        adjm[idx[a]][idx[b]] = adjm[idx[b]][idx[a]] = True
    rng = range(0, len(Eall) + 1) if maxheld is None else range(0, maxheld + 1)
    for k in rng:
        for H in itertools.combinations(Eall, k):
            Hs = [frozenset(h) for h in H]
            b0 = model.seed(Hs)
            if sum(1 for w in V if b0[w] == 0) != 1:
                continue
            Hi = [(idx[a], idx[c]) for a, c in H]

            @lru_cache(maxsize=None)
            def win(mask, bv):
                if mask == (1 << len(Hi)) - 1:
                    return True
                for r in range(len(V)):
                    cand = [(j, (Hi[j][0] if Hi[j][1] == r else Hi[j][1])) for j in range(len(Hi))
                            if not mask >> j & 1 and r in Hi[j]]
                    if not cand:
                        continue
                    blk = 0
                    for w in range(len(V)):
                        if w == r or bv[w] != 0 or not adjm[r][w]:
                            continue
                        held_unrest = any((not mask >> j & 1) and set(Hi[j]) == {r, w} for j in range(len(Hi)))
                        if not held_unrest:
                            blk += 1
                    for m in range(1, len(cand) + 1):
                        for D in itertools.combinations(cand, m):
                            if sum(bv[t] for _, t in D) <= blk:
                                continue
                            ok = True
                            for j, t in D:
                                if bv[t] == 0:
                                    continue
                                nb = list(bv); nb[t] -= 1; nb[r] += 1
                                if not win(mask | 1 << j, tuple(nb)):
                                    ok = False
                                    break
                            if ok:
                                return True
                return False

            if win(0, tuple(b0[w] for w in V)):
                return H
    return None


def part_C():
    print('Part C: exhaustive certificate search (own engine)')
    # (i) bowtie, M = T
    r = search(Model(list(T5), BOWTIE, odd=set()))
    print('  (i)   bowtie, local set T: %s' % ('certificate found %s' % (r,) if r else 'no certificate (agrees with the end of Sec. 5)'))
    # (ii) M = T + u, (iii) M = T + u + v
    subsets = [''.join(c) for k in range(1, 6) for c in itertools.combinations(T5, k)]
    fail_u = []
    for A in subsets:
        m = Model(list(T5) + ['u'], set(BOWTIE) | {frozenset(('u', t)) for t in A}, odd={'u'})
        if not search(m):
            fail_u.append(A)
    print('  (ii)  bowtie, local set T+u: %d of 31 certified; uncertified: %s' % (31 - len(fail_u), fail_u))
    fail_uv = [A for A in subsets if not search(bowtie_model(BOWTIE, A))]
    print('  (iii) bowtie, local set T+u+v: %d of 31 certified; uncertified: %s' % (31 - len(fail_uv), fail_uv))
    # (iv) the 38 labelled non-bowtie rims with M = T, and (v) all 41 rims with M = T+u+v
    RIMP = [frozenset(e) for e in itertools.combinations('abcd', 2)]
    n_loc = n_bank = 0
    for mask in range(64):
        R = {RIMP[i] for i in range(6) if mask >> i & 1}
        if max(sum(1 for e in R if w in e) for w in 'abcd') > 2:
            continue
        K = R | mk_edges(['xa', 'xb', 'xc', 'xd'])
        bow = len(R) == 2 and len(set().union(*R)) == 4
        if not bow:
            assert search(Model(list(T5), K, odd=set())) is not None, R
            n_loc += 1
        for A in subsets:
            assert search(bowtie_model(K, A)) is not None, (R, A)
            n_bank += 1
    print('  (iv)  all %d labelled non-bowtie rims certified with local set T' % n_loc)
    print('  (v)   all 41 labelled one-universal cores x 31 contact sets (%d cases) certified with T+u+v' % n_bank)


if __name__ == '__main__':
    parts = sys.argv[1:] or ['A', 'B', 'C']
    if 'A' in parts:
        part_A()
    if 'B' in parts:
        part_B()
    if 'C' in parts:
        part_C()
