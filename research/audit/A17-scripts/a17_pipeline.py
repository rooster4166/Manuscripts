#!/usr/bin/env python3
"""A17: end-to-end implementation of Steps 0-9 of the proof of Theorem 1.1
(manuscripts/near-dirac/near-dirac.tex, section 4), written from the text alone.

The asymptotic constants of the paper (c = theta/1000, q = theta*m, cm <= q/1000)
force m in the hundreds of thousands. Here the construction is run at m of a few
hundred with q ~ 0.05 m, healthy own-shore degree <= 2 + |X|, a handful of
exceptional vertices of own-shore degree up to ~0.6 m, and rho in {0,1}. The
numerical *sufficient* conditions of Lemmas 3.1 and 3.2 are therefore replaced by
the actual max-flow (Lemma 3.1) and the actual Hall matching (Lemma 3.2); the
script records whether the paper's inequality hypotheses happened to hold.

What is tested is the exact bookkeeping, which is what the manuscript must get
right independently of the constants:
  * Step 1: Lambda takes a value in [-0.6q, 0.6q];
  * Step 6 Claim: sum_i h^B_i = P_B (exact identity);
  * Step 7: a_i - b_i = tau_i in every slot;
  * Step 8: each P_i is a simple path with the two prescribed end-sites;
  * Step 9: paths edge-disjoint, v on exactly p_v paths, l_v ends, X interior,
    no kept edge used, d_R(v) = D - b'(v), e_R(S) = |R_S| + I_X(S),
    Lemma 4.1 identity, and the two-apex graph J is simple, D-regular, has a part
    of size floor(N/2) and e_J(A') <= e_R(A)+D, e_J(B') <= e_R(B)+D;
  * q + D = m.
CKLOT Theorem 1.3.5 itself is not simulated (see a17_apex.py for Lemma 4.2's
conversion of a Hamilton decomposition into D paths).
"""
import random
import sys
import networkx as nx
from networkx.algorithms import bipartite


class Fail(Exception):
    pass


def ekey(u, v):
    return (u, v) if u < v else (v, u)


def make_instance(m, rho, nXA, nXB, own_x, mis_h, seed, extra_A=0, extra_B=0):
    rnd = random.Random(seed)
    A = list(range(m))
    B = list(range(m, 2 * m + rho))
    side = {v: 'A' for v in A}
    side.update({v: 'B' for v in B})
    XA = set(rnd.sample(A, nXA))
    XB = set(rnd.sample(B, nXB))
    X = XA | XB
    HA = [v for v in A if v not in X]
    HB = [v for v in B if v not in X]
    E = set(ekey(a, b) for a in A for b in B)
    # healthy missing cross edges: mis_h random partial matchings between H_A and H_B
    for _ in range(mis_h):
        hb = HB[:]
        rnd.shuffle(hb)
        for a, b in zip(HA, hb):
            if rnd.random() < 0.7:
                E.discard(ekey(a, b))
    # exceptional vertices: own-shore neighbours, then drop cross edges to keep d(x) ~ m
    for x in X:
        own_side = A if side[x] == 'A' else B
        cr_side = B if side[x] == 'A' else A
        k = own_x(rnd)
        nb = rnd.sample([v for v in own_side if v != x], k)
        for v in nb:
            E.add(ekey(x, v))
        target_d = m + rnd.randint(-2, 2)
        cur_cr = [v for v in cr_side if ekey(x, v) in E]
        drop = len(cur_cr) + k - target_d
        if drop > 0:
            # drop only cross edges to healthy vertices
            hc = [v for v in cur_cr if v not in X]
            for v in rnd.sample(hc, min(drop, len(hc))):
                E.discard(ekey(x, v))
    G = {'m': m, 'rho': rho, 'A': A, 'B': B, 'side': side, 'X': X, 'XA': XA,
         'XB': XB, 'HA': HA, 'HB': HB, 'E': E, 'rnd': rnd}
    add_healthy_internal(G, 'A', extra_A)
    add_healthy_internal(G, 'B', extra_B)
    return G


def add_healthy_internal(G, S, k):
    """add k new healthy internal edges on shore S (healthy internal degree <= 2)."""
    rnd = G['rnd']
    H = G['HA'] if S == 'A' else G['HB']
    side, X = G['side'], G['X']
    hd = {v: 0 for v in H}
    for (a, b) in G['E']:
        if side[a] == side[b] == S and a not in X and b not in X:
            hd[a] += 1
            hd[b] += 1
    added = 0
    tries = 0
    while added < k and tries < 50 * (k + 1):
        tries += 1
        u, v = rnd.sample(H, 2)
        e = ekey(u, v)
        if e in G['E'] or hd[u] >= 2 or hd[v] >= 2:
            continue
        G['E'].add(e)
        hd[u] += 1
        hd[v] += 1
        added += 1
    return added


def stats(G):
    adj = {v: set() for v in G['side']}
    for a, b in G['E']:
        adj[a].add(b)
        adj[b].add(a)
    side = G['side']
    own = {v: sum(1 for w in adj[v] if side[w] == side[v]) for v in adj}
    deg = {v: len(adj[v]) for v in adj}
    other = {'A': len(G['B']), 'B': len(G['A'])}
    mis = {v: other[side[v]] - (deg[v] - own[v]) for v in adj}
    return adj, deg, own, mis


def internal_counts(G):
    side, X = G['side'], G['X']
    eH = {'A': [], 'B': []}
    IX = {'A': 0, 'B': 0}
    for a, b in G['E']:
        if side[a] == side[b]:
            if a in X or b in X:
                IX[side[a]] += 1
            else:
                eH[side[a]].append((a, b))
    return eH, IX


def choose_q(m, theta):
    q = int(-(-theta * m // 1))
    if (q - m) % 2:
        q += 1
    return q


def balance_instance(G, q):
    """Make Step 1 solvable with margin: add healthy internal edges on the light
    shore; if the healthy own-degree cap (2) prevents that, trade internal edges at
    X on the heavy shore for cross edges at the same exceptional vertex."""
    m, rho, side, X = G['m'], G['rho'], G['side'], G['X']
    rnd = G['rnd']
    D = m - q
    for _ in range(60):
        eH, IX = internal_counts(G)
        base = IX['A'] - IX['B'] + rho * D / 2  # Lambda_0 without the b-term
        mg = min(0.45 * q, 0.6 * q - 5)
        needB = base - mg - len(eH['B'])
        needA = -base - mg - len(eH['A'])
        if needA <= 0 and needB <= 0:
            return True
        light = 'B' if needB > 0 else 'A'
        need = needB if needB > 0 else needA
        got = add_healthy_internal(G, light, int(need) + 3)
        if got >= int(need) + 1:
            continue
        heavy = 'A' if light == 'B' else 'B'
        xe = [e for e in G['E'] if side[e[0]] == side[e[1]] == heavy and (e[0] in X or e[1] in X)]
        rnd.shuffle(xe)
        for (a, c) in xe[:max(1, int(need) // 2)]:
            G['E'].discard((a, c))
            x = a if a in X else c
            cr = [v for v in (G['B'] if side[x] == 'A' else G['A']) if v not in X and ekey(x, v) not in G['E']]
            if cr:
                G['E'].add(ekey(x, rnd.choice(cr)))
    return False


def make_profile(G, deg, imbalance, rnd):
    m = G['m']
    b = {}
    even = {'A': [], 'B': []}
    for v, d in deg.items():
        if d % 2:
            b[v] = 1
        else:
            b[v] = 0
            even[G['side'][v]].append(v)
    nodd = sum(b.values())
    ndouble = (2 * m - nodd) // 2
    assert (2 * m - nodd) % 2 == 0 and 0 <= ndouble <= len(even['A']) + len(even['B'])
    pool = even['A'] + even['B']
    rnd.shuffle(pool)
    for v in pool[:ndouble]:
        b[v] = 2
    # rebalance towards target imbalance by swapping doubled vertices across shores
    def bA():
        return sum(b[v] for v in G['A'])
    target = imbalance
    for _ in range(10 * m):
        dlt = bA() - (2 * m - bA()) - target  # b(A)-b(B)-target
        if abs(dlt) <= 1:
            break
        src, dst = ('A', 'B') if dlt > 0 else ('B', 'A')
        s2 = [v for v in even[src] if b[v] == 2]
        d0 = [v for v in even[dst] if b[v] == 0]
        if not s2 or not d0:
            break
        b[rnd.choice(s2)] = 0
        b[rnd.choice(d0)] = 2
    return b


def maxflow_matrix(rows, cols, rowsum, colsum, forbidden):
    """0/1 matrix with given margins avoiding forbidden (set of (r,c)). Returns set of (r,c) or None."""
    F = nx.DiGraph()
    for r in rows:
        F.add_edge('s', ('r', r), capacity=rowsum[r])
    for c in cols:
        F.add_edge(('c', c), 't', capacity=colsum[c])
    for r in rows:
        for c in cols:
            if (r, c) not in forbidden:
                F.add_edge(('r', r), ('c', c), capacity=1)
    T = sum(rowsum.values())
    assert T == sum(colsum.values())
    val, flow = nx.maximum_flow(F, 's', 't', flow_func=nx.algorithms.flow.preflow_push)
    if val != T:
        return None
    sel = set()
    for r in rows:
        for (_, c), f in flow[('r', r)].items():
            if f > 0:
                sel.add((r, c))
    return sel


def weave(B1, B2, kind, adjF, s_first, s_last, rnd, stats_out):
    """Lemma 3.2. B1, B2 lists of blocks (vertex lists, entry first, exit last).
    kind 'i': |B1|=|B2|=k, s_first in B1, s_last in B2 single blocks.
    kind 'ii': |B1|=k+1, |B2|=k, s_first, s_last distinct single blocks of B1."""
    def ent(b):
        return b[0]

    def ex(b):
        return b[-1]

    # nonadjacency M actually present
    E1 = set(ent(b) for b in B1) | set(ex(b) for b in B1)
    E2 = set(ent(b) for b in B2) | set(ex(b) for b in B2)
    M = 0
    for w in E1:
        M = max(M, sum(1 for z in E2 if z not in adjF[w]))
    for z in E2:
        M = max(M, sum(1 for w in E1 if w not in adjF[z]))
    k = len(B2)
    stats_out.append((k, M, k >= (4 * M + 2 if kind == 'i' else 4 * M + 1)))
    if kind == 'ii':
        assert len(B1) == k + 1
        mid = [b for b in B1 if b != [s_first] and b != [s_last]]
        rnd.shuffle(mid)
        order = [[s_first]] + mid + [[s_last]]
        gaps_blocks = B2[:]
        tail = None
    else:
        assert len(B1) == k
        others = [b for b in B1 if b != [s_first]]
        cand = [b for b in others if s_last in adjF[ex(b)]]
        if not cand:
            raise Fail('weave(i): no last block adjacent to s2')
        last = rnd.choice(cand)
        mid = [b for b in others if b is not last]
        rnd.shuffle(mid)
        order = [[s_first]] + mid + [last]
        gaps_blocks = [b for b in B2 if b != [s_last]]
        tail = [s_last]
    ng = len(order) - 1
    assert ng == len(gaps_blocks)
    # acceptance graph
    BG = nx.Graph()
    gl = [('g', j) for j in range(1, ng + 1)]
    bl = [('b', t) for t in range(len(gaps_blocks))]
    BG.add_nodes_from(gl, bipartite=0)
    BG.add_nodes_from(bl, bipartite=1)
    for j in range(1, ng + 1):
        L = ex(order[j - 1])
        Rr = ent(order[j])
        for t, gb in enumerate(gaps_blocks):
            if ent(gb) in adjF[L] and Rr in adjF[ex(gb)]:
                BG.add_edge(('g', j), ('b', t))
    mt = bipartite.hopcroft_karp_matching(BG, top_nodes=gl)
    if any(g not in mt for g in gl):
        raise Fail('weave: no perfect gap matching')
    path = list(order[0])
    for j in range(1, ng + 1):
        gb = gaps_blocks[mt[('g', j)][1]]
        path += gb
        path += order[j]
    if tail:
        path += tail
    return path


def run(G, q, imbalance, lam_mode='random'):
    rnd = G['rnd']
    m, rho, side, X, XA, XB = G['m'], G['rho'], G['side'], G['X'], G['XA'], G['XB']
    A, B, HA, HB = G['A'], G['B'], G['HA'], G['HB']
    H = set(HA) | set(HB)
    adj, deg, own, mis = stats(G)
    D = m - q
    assert D % 2 == 0
    b = make_profile(G, deg, imbalance, rnd)
    bA = sum(b[v] for v in A)
    bB = sum(b[v] for v in B)
    assert bA + bB == 2 * m
    info = {'m': m, 'rho': rho, 'q': q, 'D': D, '|X|': len(X), 'b(A)-b(B)': bA - bB,
            'max own healthy': max(own[v] for v in H), 'max mis healthy': max(mis[v] for v in H),
            'max own X': max([own[x] for x in X], default=0),
            'min cr X': min([deg[x] - own[x] for x in X], default=None)}
    # Step 0
    p = {}
    for v in side:
        t = deg[v] + b[v] - D
        assert t % 2 == 0
        p[v] = t // 2
    # Step 1
    eH, IX = internal_counts(G)
    assert (bA - bB + rho * D) % 2 == 0
    beta = (bA - bB + rho * D) // 2
    L0 = IX['A'] - IX['B'] + beta
    lo, hi = L0 - len(eH['B']), L0 + len(eH['A'])
    feas = [L for L in range(max(lo, -int(0.6 * q)), min(hi, int(0.6 * q)) + 1)]
    if not feas:
        raise Fail(f'Step 1: no Lambda in [-0.6q,0.6q] (range [{lo},{hi}])')
    Lam = {'random': rnd.choice(feas), 'max': max(feas), 'min': min(feas)}[lam_mode]
    # |R_A| - |R_B| = Lam - L0, with 0<=|R_A|<=eH(A), 0<=|R_B|<=eH(B); pick |F| moderate
    dlt = Lam - L0
    choices = [(ra, ra - dlt) for ra in range(0, len(eH['A']) + 1) if 0 <= ra - dlt <= len(eH['B'])]
    # prefer leaving some F edges on both sides (exercise Step 3) but not too many
    cap3 = max(1, m // 100)
    goodc = [(ra, rb) for ra, rb in choices
             if (len(eH['A']) - ra) + (len(eH['B']) - rb) <= cap3 * q // 3]
    ra, rb = rnd.choice(goodc if goodc else choices)
    nF = (len(eH['A']) - ra) + (len(eH['B']) - rb)
    # Step 3 slot capacity: the paper's m/100, relaxed when the small-m run needs more
    # (in the paper's regime |F| <= 1.01cm^2 is ~1/100 of the total capacity q*m/100).
    cap3 = max(cap3, 3 * (-(-nF // q)))
    info['Step 3 cap (paper m/100)'] = (cap3, m // 100)
    eA, eB = eH['A'][:], eH['B'][:]
    rnd.shuffle(eA)
    rnd.shuffle(eB)
    RA, FA = set(eA[:ra]), eA[ra:]
    RB, FB = set(eB[:rb]), eB[rb:]
    assert Lam == L0 + len(RA) - len(RB)
    info['Lambda'] = Lam
    info['|F_A|,|F_B|'] = (len(FA), len(FB))
    info['|R_A|,|R_B|'] = (len(RA), len(RB))
    info['I_X(A),I_X(B)'] = (IX['A'], IX['B'])
    # Step 2
    lA, lB = q + Lam, q - Lam
    candA = [v for v in HA if b[v] >= 1]
    candB = [v for v in HB if b[v] >= 1]
    if len(candA) < lA or len(candB) < lB:
        raise Fail('Step 2: not enough end candidates')
    LA = rnd.sample(candA, lA)
    LB = rnd.sample(candB, lB)
    l = {v: 0 for v in side}
    for v in LA + LB:
        l[v] = 1
    tau = []
    for i in range(q):
        if Lam >= 0:
            tau.append(1 if i < Lam else 0)
        else:
            tau.append(-1 if i < -Lam else 0)
    assert sum(tau) == Lam
    posA, posB = [], []
    for i in range(q):
        if tau[i] == 1:
            posA += [i, i]
        elif tau[i] == 0:
            posA.append(i)
            posB.append(i)
        else:
            posB += [i, i]
    assert len(posA) == lA and len(posB) == lB
    rnd.shuffle(LA)
    rnd.shuffle(LB)
    ends = [[] for _ in range(q)]  # list of (vertex) end-sites per slot
    endslot = {}
    for v, i in zip(LA, posA):
        ends[i].append(v)
        endslot[v] = i
    for v, i in zip(LB, posB):
        ends[i].append(v)
        endslot[v] = i
    # Step 3: assign F edges greedily
    slotF = [[] for _ in range(q)]
    covered = [set() for _ in range(q)]
    for (u, v) in FA + FB:
        ok = [i for i in range(q) if len(slotF[i]) < cap3 and u not in covered[i] and v not in covered[i]
              and endslot.get(u) != i and endslot.get(v) != i]
        if not ok:
            raise Fail('Step 3: no slot for F edge')
        i = rnd.choice(ok)
        if rnd.random() < 0.5:
            u, v = v, u
        slotF[i].append((u, v))  # oriented entry u -> exit v
        covered[i] |= {u, v}
    kA = [sum(1 for (u, v) in slotF[i] if side[u] == 'A') for i in range(q)]
    kB = [sum(1 for (u, v) in slotF[i] if side[u] == 'B') for i in range(q)]
    # Step 4: partners
    cap4 = max(1, q // 100)
    partner_count = {v: 0 for v in H}
    spokes_used = set()
    T = {}
    partners = [dict() for _ in range(q)]  # slot -> x -> (u,u')
    partner_of = [dict() for _ in range(q)]  # slot -> healthy v -> x
    for x in X:
        T[x] = sorted(rnd.sample(range(q), p[x]))
    pairs = [(x, i) for x in X for i in T[x]]
    rnd.shuffle(pairs)
    for (x, i) in pairs:
        cands = [u for u in adj[x] if u in H and side[u] != side[x]
                 and ekey(x, u) not in spokes_used
                 and endslot.get(u) != i and u not in covered[i] and u not in partner_of[i]
                 and partner_count[u] < cap4]
        if len(cands) < 2:
            raise Fail('Step 4: not enough partners')
        u, u2 = rnd.sample(cands, 2)
        partners[i][x] = (u, u2)
        for w in (u, u2):
            partner_of[i][w] = x
            partner_count[w] += 1
            spokes_used.add(ekey(x, w))
    xA = [sum(1 for x in XA if x in partners[i]) for i in range(q)]
    xB = [sum(1 for x in XB if x in partners[i]) for i in range(q)]
    # Step 5: forced
    forced = set()
    for i in range(q):
        roles = {}
        for v in ends[i]:
            roles[v] = roles.get(v, 0) + 1
        for (u, v) in slotF[i]:
            for w in (u, v):
                roles[w] = roles.get(w, 0) + 1
        for w in partner_of[i]:
            roles[w] = roles.get(w, 0) + 1
        assert all(r == 1 for r in roles.values()), 'Step 5: a forced vertex has two roles'
        for w in roles:
            forced.add((w, i))
    rowforced = {v: 0 for v in H}
    colforcedA = [0] * q
    colforcedB = [0] * q
    for (w, i) in forced:
        rowforced[w] += 1
        if side[w] == 'A':
            colforcedA[i] += 1
        else:
            colforcedB[i] += 1
    info['max row forced / q'] = round(max(rowforced.values()) / q, 3)
    info['max col forced / |H_A|'] = round(max(colforcedA) / len(HA), 3)
    # Step 6
    PA = sum(p[v] for v in HA)
    PB = sum(p[v] for v in HB)
    base, rem = divmod(PA, q)
    hA = [base + (1 if i < rem else 0) for i in range(q)]
    rnd.shuffle(hA)
    hB = [hA[i] - kA[i] - xB[i] + kB[i] + xA[i] - tau[i] for i in range(q)]
    claim = (sum(hB) == PB)
    info['Step 6 claim sum h^B = P_B'] = claim
    if not claim:
        raise Fail('Step 6 claim fails: sum h^B = %d, P_B = %d' % (sum(hB), PB))
    S = {}
    for (Hs, hs, colf, nm) in ((HA, hA, colforcedA, 'A'), (HB, hB, colforcedB, 'B')):
        rows = Hs
        cols = list(range(q))
        rs = {v: p[v] - rowforced[v] for v in rows}
        cs = {i: hs[i] - colf[i] for i in cols}
        if min(rs.values()) < 0 or min(cs.values()) < 0:
            raise Fail('Step 6: negative margin')
        # Lemma 3.1 hypotheses as stated (for the record)
        info[f'L3.1 hyps hold ({nm})'] = (
            all(0.4 * q <= rs[v] <= 0.6 * q for v in rows) and
            all(0.4 * len(rows) <= cs[i] <= 0.6 * len(rows) for i in cols) and
            max(rowforced[v] for v in rows) <= 0.03 * q and
            max(colf) <= 0.03 * len(rows))
        fb = set((w, i) for (w, i) in forced if side[w] == nm)
        sel = maxflow_matrix(rows, cols, rs, cs, fb)
        if sel is None:
            raise Fail('Step 6: max-flow did not saturate (' + nm + ')')
        for i in cols:
            S[(nm, i)] = set(w for (w, j) in fb if j == i) | set(r for (r, j) in sel if j == i)
            assert len(S[(nm, i)]) == hs[i]
    for v in H:
        cnt = sum(1 for i in range(q) if v in S[(side[v], i)])
        assert cnt == p[v]
    # Step 7 + 8
    usedE = set()
    paths = []
    wstats = []
    adjH = {v: set(w for w in adj[v] if w in H and side[w] != side[v]) for v in H}
    for i in range(q):
        blk = {'A': [], 'B': []}
        for nm in ('A', 'B'):
            SS = S[(nm, i)]
            inblk = set()
            for v in ends[i]:
                if side[v] == nm:
                    blk[nm].append([v])
                    inblk.add(v)
            for (u, v) in slotF[i]:
                if side[u] == nm:
                    blk[nm].append([u, v])
                    inblk |= {u, v}
            for x, (u, u2) in partners[i].items():
                if side[u] == nm:
                    blk[nm].append([u, x, u2])
                    inblk |= {u, u2}
            assert inblk <= SS
            for v in SS - inblk:
                blk[nm].append([v])
        ai, bi = len(blk['A']), len(blk['B'])
        assert ai == hA[i] - kA[i] - xB[i] and bi == hB[i] - kB[i] - xA[i]
        assert ai - bi == tau[i], 'Step 7: a_i - b_i != tau_i'
        # vertex-disjointness of blocks
        allv = [w for nm in ('A', 'B') for bl in blk[nm] for w in bl]
        assert len(allv) == len(set(allv)), 'Step 7: blocks not vertex-disjoint'
        # F_i adjacency: unused healthy cross edges
        adjF = {v: set(w for w in adjH[v] if ekey(v, w) not in usedE) for v in H}
        eA_ = [v for v in ends[i] if side[v] == 'A']
        eB_ = [v for v in ends[i] if side[v] == 'B']
        if tau[i] == 0:
            P = weave(blk['A'], blk['B'], 'i', adjF, eA_[0], eB_[0], rnd, wstats)
        elif tau[i] == 1:
            P = weave(blk['A'], blk['B'], 'ii', adjF, eA_[0], eA_[1], rnd, wstats)
        else:
            P = weave(blk['B'], blk['A'], 'ii', adjF, eB_[0], eB_[1], rnd, wstats)
        # record joining edges as used, block edges as well
        for a, c in zip(P, P[1:]):
            e = ekey(a, c)
            if e in usedE:
                raise Fail('edge reused')
            usedE.add(e)
        paths.append(P)
    info['weave: min k, max M, all k>=4M+2'] = (min(k for k, M, ok in wstats), max(M for k, M, ok in wstats),
                                               all(ok for k, M, ok in wstats))
    # Step 9 verification
    allE = G['E']
    on = {v: 0 for v in side}
    endc = {v: 0 for v in side}
    pe = set()
    for P in paths:
        assert len(P) == len(set(P)), 'path not simple'
        for a, c in zip(P, P[1:]):
            e = ekey(a, c)
            assert e in allE, 'non-edge in path'
            assert e not in pe, 'edge in two paths'
            pe.add(e)
        for v in P:
            on[v] += 1
        endc[P[0]] += 1
        endc[P[-1]] += 1
        assert P[0] != P[-1]
    for v in side:
        assert on[v] == p[v], f'v={v} on {on[v]} paths, p_v={p[v]}'
        assert endc[v] == l[v], 'wrong number of ends'
        if v in X:
            assert endc[v] == 0
    for e in RA | RB:
        assert e not in pe
    for (a, c) in pe:
        if side[a] == side[c]:
            assert a not in X and c not in X, 'internal edge at X used'
    assert set(FA) | set(FB) <= pe, 'some F edge unused'
    R = allE - pe
    dR = {v: 0 for v in side}
    eR = {'A': 0, 'B': 0}
    for a, c in R:
        dR[a] += 1
        dR[c] += 1
        if side[a] == side[c]:
            eR[side[a]] += 1
    bp = {v: b[v] - l[v] for v in side}
    for v in side:
        assert bp[v] in (0, 1, 2)
        assert dR[v] == D - bp[v], 'residual degree'
    assert sum(bp.values()) == 2 * D
    assert eR['A'] == len(RA) + IX['A'] and eR['B'] == len(RB) + IX['B']
    # Lemma 4.1 identity
    bpA = sum(bp[v] for v in A)
    bpB = sum(bp[v] for v in B)
    assert bpB - bpA == 2 * (eR['A'] - eR['B']) + rho * D
    # two-apex J
    Z2 = [v for v in side if bp[v] == 2]
    Z1 = [v for v in side if bp[v] == 1]
    assert len(Z1) % 2 == 0
    h = len(Z1) // 2
    a1, a2 = 'a1', 'a2'
    JE = set(R)
    for v in Z2 + Z1[:h]:
        JE.add((a1, v) if isinstance(v, str) else ('a1', v))
    for v in Z2 + Z1[h:]:
        JE.add(('a2', v))
    dJ = {}
    for (u, v) in JE:
        dJ[u] = dJ.get(u, 0) + 1
        dJ[v] = dJ.get(v, 0) + 1
    N = 2 * m + 2 + rho
    assert len(dJ) == N and all(d == D for d in dJ.values()), 'J not D-regular'
    Ap = set(A) | {'a1'}
    assert len(Ap) == N // 2
    eJA = sum(1 for (u, v) in JE if u in Ap and v in Ap)
    eJB = sum(1 for (u, v) in JE if u not in Ap and v not in Ap)
    assert eJA <= eR['A'] + D and eJB <= eR['B'] + D
    info['e_J(A\'),e_J(B\') / N^2'] = (round(eJA / N ** 2, 4), round(eJB / N ** 2, 4))
    info['D >= (1/2 - eps)N needs eps >='] = round(0.5 - D / N, 4)
    assert len(paths) + D == m
    info['paths q + D'] = len(paths) + D
    return info


def main():
    seeds = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    ok = 0
    tot = 0
    for s in range(seeds):
        rho = s % 2
        m = [240, 320, 400, 480][s % 4]
        nXA = [0, 1, 2, 4, 6][s % 5]
        nXB = [0, 3, 1, 5, 2][(s // 2) % 5]
        lo, hi = [(0.25, 0.6), (0.5, 0.74), (0.05, 0.3)][s % 3]
        own_x = (lambda r, lo=lo, hi=hi, m=m: r.randint(int(lo * m), int(hi * m)))
        G = make_instance(m, rho, nXA, nXB, own_x, mis_h=2 + s % 3, seed=1000 + s,
                          extra_A=5 + s % 20, extra_B=5 + (3 * s) % 20)
        q = choose_q(m, [0.05, 0.06, 0.04][s % 3])
        if not balance_instance(G, q):
            print(f'seed {s}: could not balance instance; skipped')
            continue
        imb = G['rnd'].choice([-6, -4, -2, 0, 2, 4, 6])
        mode = ['random', 'max', 'min'][s % 3]
        tot += 1
        try:
            info = run(G, q, imb, mode)
            ok += 1
            print(f'seed {s} [{mode}]: OK  ' + '; '.join(f'{k}={v}' for k, v in info.items()))
        except Fail as e:
            print(f'seed {s} [{mode}]: FAIL {e}')
    print(f'{ok}/{tot} instances: every check passed')


if __name__ == '__main__':
    main()
