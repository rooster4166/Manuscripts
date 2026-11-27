#!/usr/bin/env python3
"""A19 audit of near-dirac Section 8 (balancing for the one-apex route).

Written from the text of near-dirac.tex alone.  Checks:

  A. Lemma 8.1 (exact) and Lemma 8.2 (robust): run the constructions of the
     proofs on random and extremal abstract instances; assert validity.
     Also test the robust construction at tolerance mu = D/4 (the proof's
     case analysis allows it) and confirm it fails beyond that on some input.
  B. Graph-level instances (healthy shores A_H, B_H, exceptional set X with
     explicit neighbourhoods, edges inside X).  Healthy internal edges are
     taken as cleared, as in the route of Section 8.
       B1. The exact identity for e_X(I) - e_X(K minus W), compared with the
           paper's formula in Problem 8.5.
       B2. Prop 8.3(i): the monotone sweep of the proof, with exact F(r);
           record the step bound "F(r)-F(r-1) <= d_{x_r}" (claimed) and the
           conclusion.
       B3. Prop 8.3(ii): Lemma 8.2's configuration with an adversarial W.
       B4. Problem 8.5 regime: Lemma 8.2 + adversarial W fails, while the
           two-sided sweep (A19 Prop. P) always returns an exactly valid
           configuration.
       B5. H2 with full neighbourhoods: placements produced by the proof can
           give |N(x) cap I| = D + 1 although every healthy degree is <= D.

Output: out/balance.txt (also printed).
"""
import itertools
import random
import sys

OUT = []


def log(*a):
    s = " ".join(str(x) for x in a)
    OUT.append(s)
    print(s)


# ---------------------------------------------------------------------------
# A. Abstract problem
# ---------------------------------------------------------------------------

def abstract_vals(D, Delta, al, be, nu, M):
    """Imbalance S and slack Gamma of configuration (nu, M) (M a set of indices)."""
    s = len(al)
    if nu == 'B':
        S = sum(al[i] for i in M) - sum(be[i] for i in range(s) if i not in M)
        G = Delta + (s - len(M)) - len(M)
    else:
        S = sum(be[i] for i in M) - sum(al[i] for i in range(s) if i not in M)
        G = -Delta + (s - len(M)) - len(M)
    return S, G


def window(D, t):
    return (D * (t - 1) / 2, D * (t + 1) / 2)


def lemma81(D, Delta, al, be):
    """Construction of the proof of Lemma 8.1.  Returns (nu, M, t)."""
    s = len(al)
    Ss = [sum(al[:r]) - sum(be[r:]) for r in range(s + 1)]
    r = min(i for i in range(s + 1) if Ss[i] >= -D)
    Sr = Ss[r]
    Gr = Delta + s - 2 * r
    Mr = set(range(r))
    comp = set(range(r, s))
    assert -D <= Sr < D
    if Sr <= 0:
        return ('B', Mr, -1) if Gr >= 1 else ('A', comp, 1)
    return ('B', Mr, 1) if Gr >= -1 else ('A', comp, -1)


def lemma82(D, Delta, al, be, mu):
    """Construction of the proof of Lemma 8.2.  Returns (nu, M, t)."""
    s = len(al)
    Ss = [sum(al[:r]) - sum(be[r:]) for r in range(s + 1)]
    r = min(i for i in range(s + 1) if Ss[i] >= -3 * D / 4)
    Sr = Ss[r]
    Gr = Delta + s - 2 * r
    Mr, comp = set(range(r)), set(range(r, s))
    Sp, Gp = -Sr, -Gr
    if Sr <= 0 and Gr >= 1:
        return ('B', Mr, -1) if Sr <= -mu else ('B', Mr, 0)
    if Sr <= 0 and Gr <= 0:
        return ('A', comp, 1) if Sp >= mu else ('A', comp, 0)
    if Sr > 0 and Gr >= 0:
        return ('B', Mr, 1) if Sr >= mu else ('B', Mr, 0)
    if Sr > 0 and Gr == -1:
        return ('B', Mr, 1) if Sr >= mu else ('A', comp, 0)
    # Sr > 0 and Gr <= -2
    return ('A', comp, -1) if Sp <= -mu else ('A', comp, 0)


def check_abstract(rng, trials=20000):
    bad81 = bad82 = bad82q = 0
    worst_margin_q = None
    for _ in range(trials):
        D = rng.choice([2, 4, 8, 16, 40, 100, 400, 1000])
        s = rng.randint(0, 25)
        Delta = rng.randint(-3 * s - 3, 3 * s + 3)
        mode = rng.random()
        al, be = [], []
        for _ in range(s):
            if mode < 0.3:  # extremal: steps exactly D or 2D
                d = rng.choice([D, 2 * D])
                a = rng.randint(max(0, d - D), min(D, d))
            else:
                d = rng.randint(D, 2 * D)
                a = rng.randint(max(0, d - D), min(D, d))
            al.append(a)
            be.append(d - a)
        nu, M, t = lemma81(D, Delta, al, be)
        S, G = abstract_vals(D, Delta, al, be, nu, M)
        lo, hi = window(D, t)
        if not (G + t >= 0 and lo <= S <= hi):
            bad81 += 1
        # Lemma 8.2 needs d <= 5D/4
        al2, be2 = [], []
        for _ in range(s):
            d = rng.choice([D, (5 * D) // 4, rng.randint(D, (5 * D) // 4)])
            a = rng.randint(max(0, d - D), min(D, d))
            al2.append(a)
            be2.append(d - a)
        for mu, tag in ((D / 8, 'D/8'), (D / 4, 'D/4')):
            nu, M, t = lemma82(D, Delta, al2, be2, mu)
            S, G = abstract_vals(D, Delta, al2, be2, nu, M)
            lo, hi = window(D, t)
            ok = G + t >= 0 and lo <= S - mu and S + mu <= hi
            if not ok:
                if tag == 'D/8':
                    bad82 += 1
                else:
                    bad82q += 1
    log(f"[A] Lemma 8.1 construction: {trials} random/extremal instances, failures = {bad81}")
    log(f"[A] Lemma 8.2 construction, mu = D/8: failures = {bad82}")
    log(f"[A] Lemma 8.2 construction, mu = D/4 (not claimed; case analysis allows it): failures = {bad82q}")
    # beyond D/4: a single instance where the construction breaks
    D = 400
    al, be = [0], [3 * D // 4]  # s=1: S_0 = -3D/4, r = 0
    for mu in (D / 4, D / 4 + 1):
        nu, M, t = lemma82(D, 5, al, be, mu)
        S, G = abstract_vals(D, 5, al, be, nu, M)
        lo, hi = window(D, t)
        log(f"[A]   instance D=400, s=1, alpha=0, beta=300, Delta=5, mu={mu}: config {nu},{sorted(M)},t={t}, "
            f"S={S}, window=[{lo},{hi}], robust={lo <= S - mu and S + mu <= hi}")


# ---------------------------------------------------------------------------
# B. Graph-level instances
# ---------------------------------------------------------------------------

class Inst:
    """Healthy shores A_H = range(nA), B_H = range(nB); exceptional X = range(s).
    NA[x], NB[x]: healthy neighbours of x;  EX: edges inside X."""

    def __init__(self, D, nA, nB, NA, NB, EX):
        self.D, self.nA, self.nB = D, nA, nB
        self.NA, self.NB, self.EX = NA, NB, EX
        self.s = len(NA)
        self.adjX = [set() for _ in range(self.s)]
        for (u, v) in EX:
            self.adjX[u].add(v)
            self.adjX[v].add(u)
        self.Delta = nB - nA

    def al(self, x):
        return len(self.NA[x])

    def be(self, x):
        return len(self.NB[x])

    def eX(self, Y):
        Y = set(Y)
        return sum(1 for (u, v) in self.EX if u in Y and v in Y)

    def S(self, nu, M):
        X = range(self.s)
        if nu == 'B':
            return sum(self.al(x) for x in M) - sum(self.be(x) for x in X if x not in M)
        return sum(self.be(x) for x in M) - sum(self.al(x) for x in X if x not in M)

    def Gamma(self, nu, M):
        Dn = self.Delta if nu == 'B' else -self.Delta
        return Dn + (self.s - len(M)) - len(M)

    def exact(self, nu, M, W):
        """e_X(I) - e_X(K minus W), healthy internal edges cleared."""
        M = set(M)
        XK = [x for x in range(self.s) if x not in M]
        W = set(W)
        if nu == 'B':   # I = A, K = B
            eI = sum(len(self.NA[x]) for x in M) + self.eX(M)
            eK = sum(len(self.NB[x] - W) for x in XK) + self.eX(XK)
        else:           # I = B, K = A
            eI = sum(len(self.NB[x]) for x in M) + self.eX(M)
            eK = sum(len(self.NA[x] - W) for x in XK) + self.eX(XK)
        return eI - eK

    def eXK_W(self, nu, M, W):
        W = set(W)
        XK = [x for x in range(self.s) if x not in set(M)]
        if nu == 'B':
            return sum(len(self.NB[x] & W) for x in XK)
        return sum(len(self.NA[x] & W) for x in XK)

    def binsize(self, nu):
        return self.nB if nu == 'B' else self.nA

    def binN(self, nu, x):
        return self.NB[x] if nu == 'B' else self.NA[x]

    def full_internal_degrees(self, nu, M):
        """|N(x) cap I| for x in M and |N(x) cap K| for x not in M (K including W)."""
        M = set(M)
        out = {}
        for x in range(self.s):
            if x in M:
                h = len(self.NA[x]) if nu == 'B' else len(self.NB[x])
                out[x] = h + len(self.adjX[x] & M)
            else:
                h = len(self.NB[x]) if nu == 'B' else len(self.NA[x])
                out[x] = h + len(self.adjX[x] - M - {x})
        return out


def valid(inst, nu, M, t, W):
    G = inst.Gamma(nu, M)
    if len(W) != G + t or G + t < 0:
        return False, None
    F = inst.exact(nu, M, W)
    lo, hi = window(inst.D, t)
    return lo <= F <= hi, F


def worst_W_order(inst, nu, M):
    """Healthy bin-shore vertices sorted by decreasing number of X_K neighbours
    (adversarial: removing them raises e(X_K, W) as fast as possible)."""
    XK = [x for x in range(inst.s) if x not in set(M)]
    cnt = [0] * inst.binsize(nu)
    for x in XK:
        for w in inst.binN(nu, x):
            cnt[w] += 1
    return sorted(range(inst.binsize(nu)), key=lambda w: (-cnt[w], w))


def paper_identity(inst, nu, M, W):
    """Problem 8.5 as printed: S - e(X_I) + e(X_K) + e(X_K, W)."""
    M = set(M)
    XK = [x for x in range(inst.s) if x not in M]
    return inst.S(nu, M) - inst.eX(M) + inst.eX(XK) + inst.eXK_W(nu, M, W)


def corrected_identity(inst, nu, M, W):
    M = set(M)
    XK = [x for x in range(inst.s) if x not in M]
    return inst.S(nu, M) + inst.eX(M) - inst.eX(XK) + inst.eXK_W(nu, M, W)


def make_instance(rng, D, s, Delta, adversarial, pXX, dmode='range'):
    """Exceptional degrees into healthy vertices satisfy (B1) and
    D + |Delta| + 2s + 2 <= d_x <= 5D/4 (the hypotheses of Prop 8.3)."""
    lo = D + abs(Delta) + 2 * s + 2
    hi = (5 * D) // 4
    assert lo <= hi
    nA = D + 3 * s + abs(Delta) + 10
    nB = nA + Delta
    if nB < D + 3 * s + 10:
        nB = D + 3 * s + 10
        nA = nB - Delta
    NA, NB = [], []
    for _ in range(s):
        if dmode == 'top':
            d = hi
        elif dmode == 'bottom':
            d = lo
        else:
            d = rng.randint(lo, hi)
        a = rng.randint(max(0, d - D), min(D, d))
        b = d - a
        if adversarial:  # every x adjacent to the same initial segments
            NA.append(set(range(a)))
            NB.append(set(range(b)))
        else:
            NA.append(set(rng.sample(range(nA), a)))
            NB.append(set(rng.sample(range(nB), b)))
    EX = [(u, v) for u, v in itertools.combinations(range(s), 2) if rng.random() < pXX]
    return Inst(D, nA, nB, NA, NB, EX)


def prop83_i(inst, rng, adversarialW=True):
    """Proof of Prop 8.3(i).  Requires |Delta| >= s+1.  Returns dict of observations."""
    s, D = inst.s, inst.D
    nu = 'B' if inst.Delta >= 0 else 'A'   # healthy bin shore is the larger
    order = list(range(s))
    rng.shuffle(order)
    # W_0 of size Gamma_0 - 1, nested decreasing: W_r = first (Gamma_r - 1) of a fixed list
    base = worst_W_order(inst, nu, set()) if adversarialW else rng.sample(range(inst.binsize(nu)), inst.binsize(nu))
    F, Wsz = [], []
    for r in range(s + 1):
        M = set(order[:r])
        G = inst.Gamma(nu, M)
        assert G >= 1
        W = base[:G - 1]
        F.append(inst.exact(nu, M, W))
        Wsz.append(G - 1)
    obs = {'step_gt_d': 0, 'step_gt_5D4': 0, 'step_le_0': 0, 'max_excess_over_d': 0}
    dH = lambda x: len(inst.NA[x]) + len(inst.NB[x])
    for r in range(1, s + 1):
        step = F[r] - F[r - 1]
        x = order[r - 1]
        if step > dH(x):
            obs['step_gt_d'] += 1
            obs['max_excess_over_d'] = max(obs['max_excess_over_d'], step - dH(x))
        if step > 5 * D / 4:
            obs['step_gt_5D4'] += 1
        if step <= 0:
            obs['step_le_0'] += 1
    assert F[0] <= 0 and F[s] >= 0
    r = min(i for i in range(s + 1) if F[i] >= -D)
    M = set(order[:r])
    G = inst.Gamma(nu, M)
    obs['Fr_ge_D4'] = F[r] >= D / 4
    if F[r] <= 0:
        ok, val = valid(inst, nu, M, -1, base[:G - 1])
    else:
        ok, val = valid(inst, nu, M, 1, base[:G + 1])
    obs['ok'] = ok
    return obs


def two_sided_sweep(inst, rng, adversarialW=True):
    """A19 Proposition P: exact balancing without hypotheses (i)/(ii).
    Physical placement M_r = first r exceptional vertices on A, rest on B.
    For each r, both namings are available.  Returns (nu, M, t, W) or None."""
    s, D = inst.s, inst.D
    order = list(range(s))
    rng.shuffle(order)
    Gam = [inst.Delta + s - 2 * r for r in range(s + 1)]   # = |B| - |A| at stage r
    # Part 1: bin B, t=-1, nested W in B_H, r increasing over R_B = {Gamma_r >= 1}
    RB = [r for r in range(s + 1) if Gam[r] >= 1]
    if RB:
        baseB = worst_W_order(inst, 'B', set()) if adversarialW else rng.sample(range(inst.nB), inst.nB)
        for r in RB:
            M = set(order[:r])
            W = baseB[:Gam[r] - 1]
            F = inst.exact('B', M, W)
            if F >= -D:
                if F <= 0:
                    return ('B', M, -1, W, 'sweepB')
                W1 = baseB[:Gam[r] + 1]
                return ('B', M, 1, W1, 'sweepB')
    # Part 2: bin A (interval B holds X minus M_r), r decreasing over R_A = {Gamma_r <= -1}
    RA = [r for r in range(s, -1, -1) if Gam[r] <= -1]
    if RA:
        baseA = worst_W_order(inst, 'A', set()) if adversarialW else rng.sample(range(inst.nA), inst.nA)
        for r in RA:
            Mi = set(order[r:])          # on the interval shore B
            W = baseA[:-Gam[r] - 1]
            F = inst.exact('A', Mi, W)
            if F >= -D:
                if F <= 0:
                    return ('A', Mi, -1, W, 'sweepA')
                W1 = baseA[:-Gam[r] + 1]
                return ('A', Mi, 1, W1, 'sweepA')
    # Part 3: zero stage, W empty, t = 0
    Z = [r for r in range(s + 1) if Gam[r] == 0]
    if Z:
        r = Z[0]
        return ('B', set(order[:r]), 0, [], 'zero')
    return None


def run_graph_checks(rng):
    # ---- B1 identity ----
    mism = 0
    tot = 0
    for _ in range(300):
        D = rng.choice([40, 80, 200])
        s = rng.randint(2, 6)
        Delta = rng.randint(-s, s)
        lo = D + abs(Delta) + 2 * s + 2
        if lo > (5 * D) // 4:
            continue
        inst = make_instance(rng, D, s, Delta, adversarial=False, pXX=0.6)
        for nu in 'AB':
            for k in range(s + 1):
                for M in itertools.combinations(range(s), k):
                    G = inst.Gamma(nu, set(M))
                    for t in (-1, 0, 1):
                        if G + t < 0:
                            continue
                        W = rng.sample(range(inst.binsize(nu)), G + t)
                        ex = inst.exact(nu, M, W)
                        assert ex == corrected_identity(inst, nu, M, W)
                        tot += 1
                        if ex != paper_identity(inst, nu, M, W):
                            mism += 1
    log(f"[B1] exact e_X(I)-e_X(K\\W) = S + e(X_I) - e(X_K) + e(X_K,W): holds in all {tot} configurations")
    log(f"[B1] Problem 8.5 as printed (S - e(X_I) + e(X_K) + e(X_K,W)) disagrees in {mism}/{tot}")
    # a 2-vertex example
    inst = Inst(40, 60, 60, [set(range(10)), set(range(10, 20))], [set(range(30)), set(range(30))], [(0, 1)])
    M, W = {0, 1}, []
    log(f"[B1] example: X={{x,y}}, xy an edge, both on I=A, alpha=(10,10): exact={inst.exact('B', M, W)}, "
        f"S={inst.S('B', M)}, printed formula={paper_identity(inst, 'B', M, W)}")

    # ---- B2 Prop 8.3(i) ----
    agg = {'n': 0, 'step_gt_d': 0, 'step_gt_5D4': 0, 'step_le_0': 0, 'Fr_ge_D4': 0, 'ok': 0, 'max_excess': 0}
    for it in range(1500):
        D = rng.choice([200, 400, 800, 2000])
        s = rng.randint(1, 25)
        sign = rng.choice([1, -1])
        Delta = sign * rng.randint(s + 1, 2 * s + 6)
        if D + abs(Delta) + 2 * s + 2 > (5 * D) // 4 or abs(Delta) + 5 * s + 1 >= D:
            continue
        inst = make_instance(rng, D, s, Delta, adversarial=rng.random() < 0.5,
                             pXX=rng.choice([0, 0.5, 1.0]), dmode=rng.choice(['range', 'top']))
        o = prop83_i(inst, rng, adversarialW=rng.random() < 0.5)
        agg['n'] += 1
        for k in ('step_gt_d', 'step_gt_5D4', 'step_le_0'):
            agg[k] += o[k]
        agg['Fr_ge_D4'] += o['Fr_ge_D4']
        agg['ok'] += o['ok']
        agg['max_excess'] = max(agg['max_excess'], o['max_excess_over_d'])
    log(f"[B2] Prop 8.3(i) sweep on {agg['n']} instances (|Delta|>=s+1):")
    log(f"[B2]   steps with F(r)-F(r-1) > d_(x_r) [claimed impossible]: {agg['step_gt_d']} "
        f"(max excess {agg['max_excess']}, bound s-1)")
    log(f"[B2]   steps > 5D/4 [claimed impossible]: {agg['step_gt_5D4']};  steps <= 0: {agg['step_le_0']}")
    log(f"[B2]   least r with F(r) >= -D has F(r) >= D/4 [claimed impossible]: {agg['Fr_ge_D4']}")
    log(f"[B2]   conclusion (window met exactly): {agg['ok']}/{agg['n']}")
    # B2b: an explicit instance where the least r has F(r) >= D/4 (the proof claims F(r) < D/4)
    D, s, Delta, a = 400, 20, 21, 204
    nA = D + 3 * s + Delta + 10
    inst = Inst(D, nA, nA + Delta, [set(range(a)) for _ in range(s)], [set(range(500 - a)) for _ in range(s)],
                list(itertools.combinations(range(s), 2)))
    WB = list(range(inst.nB - 1, -1, -1))   # removed vertices taken from the top: no edges to X
    Fs = [inst.exact('B', set(range(r)), WB[:inst.Gamma('B', set(range(r))) - 1]) for r in range(s + 1)]
    r = min(i for i in range(s + 1) if Fs[i] >= -D)
    M = set(range(r))
    ok, val = valid(inst, 'B', M, 1, WB[:inst.Gamma('B', M) + 1])
    log(f"[B2b] D=400, s=20, Delta=21, X complete, alpha=204, beta=296 (d=500=5D/4): F({r-1})={Fs[r-1]}, "
        f"F({r})={Fs[r]} >= D/4={D/4}; step = {Fs[r]-Fs[r-1]} > 5D/4; t=1 config valid: {ok} (value {val})")

    # ---- B3 Prop 8.3(ii) and B4 Problem 8.5 regime ----
    for regime in ('ii', '8.5'):
        n = fail_robust = ok_sweep = 0
        how = {}
        maxerr = 0
        for it in range(1500 if regime == '8.5' else 800):
            D = rng.choice([400, 800, 1600, 3200])
            if regime == 'ii':
                smax = int((D ** 0.5) / 6)
                s = rng.randint(1, max(1, smax))
            else:
                smin = int((D ** 0.5) / 6) + 1
                smax = (D // 4 - 2) // 3
                s = rng.randint(smin, smax)
            Delta = rng.randint(-s, s)
            if D + abs(Delta) + 2 * s + 2 > (5 * D) // 4 or abs(Delta) + 5 * s + 1 >= D:
                continue
            adv = rng.random() < 0.7
            inst = make_instance(rng, D, s, Delta, adversarial=adv, pXX=rng.choice([0, 0.5, 1.0]),
                                 dmode=rng.choice(['range', 'top', 'bottom']))
            n += 1
            # paper: Lemma 8.2 config, W adversarial
            al = [inst.al(x) for x in range(s)]
            be = [inst.be(x) for x in range(s)]
            nu, M, t = lemma82(D, inst.Delta, al, be, D / 8)
            G = inst.Gamma(nu, M)
            W = worst_W_order(inst, nu, M)[:G + t]
            ok, F = valid(inst, nu, M, t, W)
            maxerr = max(maxerr, abs(F - inst.S(nu, M)))
            if not ok:
                fail_robust += 1
            res = two_sided_sweep(inst, rng, adversarialW=adv)
            assert res is not None
            nu2, M2, t2, W2, tag = res
            ok2, F2 = valid(inst, nu2, M2, t2, W2)
            # cross-edge condition and |W| bound
            assert len(W2) <= abs(inst.Delta) + s + 1
            if ok2:
                ok_sweep += 1
                how[tag] = how.get(tag, 0) + 1
        label = "Prop 8.3(ii) regime (|Delta|<=s<=sqrt(D)/6)" if regime == 'ii' else \
            "Problem 8.5 regime (|Delta|<=s, s>sqrt(D)/6)"
        log(f"[B3/4] {label}: {n} instances")
        log(f"[B3/4]   Lemma 8.2 config + adversarial W: window violated in {fail_robust}; "
            f"max |exact - S| = {maxerr}")
        log(f"[B3/4]   two-sided sweep (A19 Prop P): exactly valid in {ok_sweep}/{n}; branch counts {how}")

    # ---- B4b brute force: every instance small enough, sweep vs exhaustive ----
    agree = cnt = 0
    for it in range(150):
        D = rng.choice([200, 400])
        s = rng.randint(3, 8)
        Delta = rng.randint(-s, s)
        if D + abs(Delta) + 2 * s + 2 > (5 * D) // 4:
            continue
        inst = make_instance(rng, D, s, Delta, adversarial=True, pXX=1.0, dmode='top')
        exists = False
        for nu in 'AB':
            for k in range(s + 1):
                for M in itertools.combinations(range(s), k):
                    G = inst.Gamma(nu, set(M))
                    for t in (-1, 0, 1):
                        if G + t < 0:
                            continue
                        W = worst_W_order(inst, nu, M)[:G + t]
                        if valid(inst, nu, set(M), t, W)[0]:
                            exists = True
        res = two_sided_sweep(inst, rng)
        ok2 = valid(inst, res[0], res[1], res[2], res[3])[0]
        cnt += 1
        agree += (ok2 and exists)
    log(f"[B4b] small adversarial instances: exhaustive search finds a valid config and the sweep returns one: {agree}/{cnt}")

    # ---- B5 H2 with full neighbourhoods ----
    D = 400
    # x0, x1: alpha = D (all healthy A-neighbours), beta = 60, x0x1 an edge.
    # x2..x5: alpha = 30, beta = D.  s = 6, Delta = 10 >= s+1 (case (i), naming B, I = A).
    NA = [set(range(D)), set(range(D))] + [set(range(30)) for _ in range(4)]
    NB = [set(range(60)), set(range(60))] + [set(range(D)) for _ in range(4)]
    inst = Inst(D, D + 100, D + 110, NA, NB, [(0, 1)])
    s = inst.s
    for x in range(s):
        d = inst.al(x) + inst.be(x)
        assert inst.al(x) <= D and inst.be(x) <= D and D + inst.Delta + 2 * s + 2 <= d <= 5 * D / 4
    Fs = [inst.exact('B', set(range(r)), list(range(inst.Gamma('B', set(range(r))) - 1))) for r in range(s + 1)]
    r = min(i for i in range(s + 1) if Fs[i] >= -D)
    M = set(range(r))
    deg = inst.full_internal_degrees('B', M)
    log(f"[B5] D={D}, s=6, Delta=10; x0,x1 have alpha=D, beta=60 and are adjacent; x2..x5 have alpha=30, beta=D.")
    log(f"[B5]   Prop 8.3(i) sweep in the order x0,...,x5: F = {Fs}; least r with F(r) >= -D is r = {r}")
    log(f"[B5]   output places M = {sorted(M)} on I = A; full |N(x0) cap I| = {deg[0]}, |N(x1) cap I| = {deg[1]} "
        f"> D = {D}: (H2) fails, and x0 cannot have R-degree D while keeping all internal edges")


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 20261127)
    check_abstract(rng)
    run_graph_checks(rng)
    with open(__file__.rsplit('/', 1)[0] + '/out/balance.txt', 'w') as f:
        f.write("\n".join(OUT) + "\n")


if __name__ == '__main__':
    main()
