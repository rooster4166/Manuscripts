"""Independent check (A10 referee) of Sections 5-6 of jm-repair.tex.

For random decompositions Q of K_m into n linear forests and a colour c, and for EVERY
demand vector delta with 0 <= delta_i <= kappa_i (kappa = 4, kappa_c = 2), compare
  (1) brute force over all colourings chi of the 2m edges xv, yv (xy gets colour c):
      exists chi with every Q'_i a linear forest (graph-level check) and a_i(chi) >= delta_i;
  (2) the cut conditions (UH) and (LH) of Prop. 'cuts' over all B subset V
      (psi computed from scratch here);
  (3) for tiny networks, Hoffman's condition over ALL node subsets X of the network D
      (this checks the derivation of (UH)/(LH) from Hoffman, i.e. no missing cut type).
No code from manuscripts/jm-repair/scripts is used."""
import itertools, random, sys

def lf_ok(nv, edges):
    deg = [0] * nv; par = list(range(nv))
    def f(a):
        while par[a] != a:
            par[a] = par[par[a]]; a = par[a]
        return a
    for u, v in edges:
        deg[u] += 1; deg[v] += 1
        if deg[u] > 2 or deg[v] > 2: return False
        a, b = f(u), f(v)
        if a == b: return False
        par[a] = b
    return True

def random_decomp(m, n, rng):
    while True:
        E = [(u, v) for u in range(m) for v in range(u + 1, m)]
        rng.shuffle(E); cls = [[] for _ in range(n)]; ok = True
        for e in E:
            opts = [i for i in range(n) if lf_ok(m, cls[i] + [e])]
            if not opts: ok = False; break
            cls[rng.choice(opts)].append(e)
        if ok: return cls

def comps(m, F):
    """components of linear forest F on range(m) as tuples of end vertices ((v,) if trivial)"""
    adj = {v: [] for v in range(m)}
    for u, v in F: adj[u].append(v); adj[v].append(u)
    seen = set(); out = []
    for v in range(m):
        if v in seen or len(adj[v]) == 2: continue
        prev, cur = None, v; seen.add(v)
        while True:
            nx_ = [w for w in adj[cur] if w != prev]
            if not nx_: break
            prev, cur = cur, nx_[0]; seen.add(cur)
        out.append((v,) if cur == v else (v, cur))
    assert len(seen) == m
    return out

def achievable(m, n, cls, c):
    """set of Pareto-maximal attachment vectors a(chi) over valid chi (brute force)."""
    x, y = m, m + 1
    vecs = set()
    # pre-filter x-colourings that are valid on their own
    goodx = []
    for cx in itertools.product(range(n), repeat=m):
        okk = True
        for i in range(n):
            F = cls[i] + [(v, x) for v in range(m) if cx[v] == i] + ([(x, y)] if i == c else [])
            if not lf_ok(m + 2, F): okk = False; break
        if okk: goodx.append(cx)
    for cx in goodx:
        for cy in goodx:  # same constraint set for y alone (symmetric)
            okk = True
            for i in range(n):
                F = cls[i] + [(v, x) for v in range(m) if cx[v] == i] + \
                    [(v, y) for v in range(m) if cy[v] == i] + ([(x, y)] if i == c else [])
                if not lf_ok(m + 2, F): okk = False; break
            if okk:
                vecs.add(tuple(sum(cx[v] == i for v in range(m)) + sum(cy[v] == i for v in range(m)) for i in range(n)))
    return vecs

def cut_ok(m, n, cls, c, delta):
    kap = [2 if i == c else 4 for i in range(n)]
    C = [comps(m, cls[i]) for i in range(n)]
    for bm in range(1 << m):
        B = {v for v in range(m) if bm >> v & 1}
        up = 0; low = 0
        for i in range(n):
            N = 0; two = False
            for comp in C[i]:
                # slots in B: trivial comp has 2 slots at its vertex
                sl = 2 * (comp[0] in B) if len(comp) == 1 else (comp[0] in B) + (comp[1] in B)
                if sl >= 1: N += 1
                if sl == 2: two = True
            psi = N + (1 if (two and i != c) else 0)
            up += min(kap[i], psi); low += max(0, delta[i] - psi)
        if 2 * len(B) > up or low > 2 * (m - len(B)): return False
    return True

def hoffman_table(m, n, cls, c):
    """Enumerate all node subsets X of D; return dict I -> min over X of (rhs - const),
    where Hoffman's inequality for X reads const_X + sum_{i in I_X} delta_i <= rhs_X."""
    INF = 10 ** 9
    nodes = ["s", "t"] + [("v", v) for v in range(m)]
    arcs = [("t", "s", 0, INF, None)]
    for v in range(m): arcs.append(("s", ("v", v), 2, 2, None))
    for i in range(n):
        for k, comp in enumerate(comps(m, cls[i])):
            Cn = ("C", i, k); nodes.append(Cn)
            if len(comp) == 1: arcs.append((("v", comp[0]), Cn, 0, 2, None))
            else:
                for v in comp: arcs.append((("v", v), Cn, 0, 1, None))
            arcs.append((Cn, ("g", i), 0, 1, None)); arcs.append((Cn, ("h", i), 0, 1, None))
        nodes += [("h", i), ("g", i)]
        arcs.append((("h", i), ("g", i), 0, 0 if i == c else 1, None))
        arcs.append((("g", i), "t", 0, 2 if i == c else 4, i))   # lower bound = delta_i (symbolic)
    idx = {v: j for j, v in enumerate(nodes)}
    A = [(idx[a], idx[b], lo, hi, sym) for a, b, lo, hi, sym in arcs]
    best = {}
    N = len(nodes)
    for X in range(1 << N):
        const = 0; rhs = 0; I = 0
        for a, b, lo, hi, sym in A:
            ina, inb = X >> a & 1, X >> b & 1
            if inb and not ina:          # entering
                if sym is None: const += lo
                else: I |= 1 << sym
            elif ina and not inb:        # leaving
                rhs += hi
        val = rhs - const
        if val < best.get(I, INF): best[I] = val
    return best

def hoffman_ok(best, delta):
    for I, val in best.items():
        if sum(delta[i] for i in range(len(delta)) if I >> i & 1) > val: return False
    return True

def main(seed, trials, mmax, nmax, hoff_nodes):
    rng = random.Random(seed)
    tot = mism = feas = hoff_checked = 0
    for tr in range(trials):
        n = rng.randint(2, nmax); m = rng.randint(1, mmax)
        if m > 2 * n - 1: continue          # need K_m to decompose into n linear forests
        cls = random_decomp(m, n, rng); c = rng.randrange(n)
        vecs = achievable(m, n, cls, c)
        nnodes = 2 + m + sum(len(comps(m, cls[i])) for i in range(n)) + 2 * n
        best = hoffman_table(m, n, cls, c) if nnodes <= hoff_nodes else None
        if best is not None: hoff_checked += 1
        ranges = [range(3) if i == c else range(5) for i in range(n)]
        for delta in itertools.product(*ranges):
            b1 = any(all(a[i] >= delta[i] for i in range(n)) for a in vecs)
            b2 = cut_ok(m, n, cls, c, delta)
            b3 = hoffman_ok(best, delta) if best is not None else b2
            tot += 1; feas += b1
            if not (b1 == b2 == b3):
                mism += 1; print("MISMATCH", m, n, c, cls, delta, b1, b2, b3)
    print("seed", seed, "instances-x-demands", tot, "feasible", feas, "mismatches", mism,
          "instances with full Hoffman enumeration", hoff_checked)

if __name__ == "__main__":
    a = [int(z) for z in sys.argv[1:]]
    main(*a)
