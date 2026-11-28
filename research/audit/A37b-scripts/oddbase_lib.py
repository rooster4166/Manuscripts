"""oddbase_lib.py -- audit A37b: exhaustive all-odd base search (own code).

For a (T1) instance (J, z, r) (z the only even vertex of J, r in N(z)), B = J - z, T = N(z):
  * every forest T-join of B is enumerated through the cycle space (one T-join XOR every
    element of the cycle space, keep the acyclic ones);
  * every rooting with r a root, or r a child with c(r) >= 2;
  * each (Phi, rooting) is decided exactly by ./obase (own C decider): a Lovasz decomposition of
    H = B - Phi with X_v = {p(v)} at every child v (condition (i)) and every sibling pair a
    forbidden end pair (condition (ii)).
Witnesses are lifted (forest appended, parents first) and checked as (T1) decompositions with
a37lib.check_decomp (the A37 auditor's checker).
"""
import itertools
import os
import subprocess
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "A37-scripts"))
from a37lib import adjacency, check_decomp, g6_decode, kconn  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))


class Obase:
    def __init__(self, budget=None):
        env = dict(os.environ)
        if budget is not None:
            env["OBASE_BUDGET"] = str(budget)
        self.p = subprocess.Popen([os.path.join(HERE, "obase")], stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, text=True, bufsize=1, env=env)
        self.last = None
        self.unknown = 0

    def query(self, n, E, b, X, forb):
        E = [tuple(e) for e in E]
        q = [n, len(E)] + [v for e in E for v in e] + list(b) + list(X) + [len(forb)] + \
            [v for p in forb for v in p]
        self.p.stdin.write(" ".join(map(str, q)) + "\n")
        self.p.stdin.flush()
        out = self.p.stdout.readline().strip()
        self.last = out[:1]
        if out.startswith("1"):
            return [list(map(int, s.split())) for s in out.split("|")[1:] if s.strip()]
        if out == "2":
            self.unknown += 1
            return None
        assert out == "0", out
        return None


def components(vs, edges):
    A = {v: set() for v in vs}
    for a, b in edges:
        A[a].add(b)
        A[b].add(a)
    seen, comps = set(), []
    for v in vs:
        if v in seen:
            continue
        C, st = {v}, [v]
        while st:
            u = st.pop()
            for w in A[u]:
                if w not in C:
                    C.add(w)
                    st.append(w)
        seen |= C
        comps.append(C)
    return comps, A


def is_forest(edges):
    vs = sorted({v for e in edges for v in e})
    comps, _ = components(vs, edges)
    return len(edges) == len(vs) - len(comps)


def tjoins(Bverts, Bedges, T):
    """All T-joins of the connected graph (Bverts, Bedges), as frozensets of edges."""
    Bedges = [tuple(sorted(e)) for e in Bedges]
    # spanning tree by BFS
    A = {v: [] for v in Bverts}
    for a, b in Bedges:
        A[a].append(b)
        A[b].append(a)
    root = Bverts[0]
    par = {root: None}
    order = [root]
    for u in order:
        for w in sorted(A[u]):
            if w not in par:
                par[w] = u
                order.append(w)
    assert len(par) == len(Bverts), "B disconnected"
    tree = {tuple(sorted((v, par[v]))) for v in Bverts if par[v] is not None}
    # one T-join inside the tree
    cnt = {v: int(v in T) for v in Bverts}
    phi0 = set()
    for u in reversed(order):
        if par[u] is not None and cnt[u] % 2:
            phi0.add(tuple(sorted((u, par[u]))))
        if par[u] is not None:
            cnt[par[u]] += cnt[u]
    # fundamental cycles

    def tree_path(a, b):
        pa, x = [], a
        anc = []
        while x is not None:
            anc.append(x)
            x = par[x]
        ancset = set(anc)
        y, pb = b, []
        while y not in ancset:
            pb.append(y)
            y = par[y]
        lca = y
        edges = set()
        x = a
        while x != lca:
            edges.add(tuple(sorted((x, par[x]))))
            x = par[x]
        for y in pb:
            edges.add(tuple(sorted((y, par[y]))))
        return edges
    cycles = []
    for a, b in Bedges:
        if (a, b) not in tree:
            cycles.append(tree_path(a, b) | {(a, b)})
    out = []
    for mask in range(1 << len(cycles)):
        S = set(phi0)
        for i, C in enumerate(cycles):
            if mask >> i & 1:
                S ^= C
        out.append(frozenset(S))
    return out


def rootings(phi, r):
    """(par, order) for every rooting of the forest phi with r a root or a child with >= 2
    children.  order lists the children parents-first (BFS)."""
    vs = sorted({v for e in phi for v in e})
    comps, A = components(vs, list(phi))
    choices = []
    for C in comps:
        if r in C:
            ch = [u for u in sorted(C) if u == r or len(A[r]) >= 3]
        else:
            ch = sorted(C)
        choices.append(ch)
    for roots in itertools.product(*choices):
        par, order = {}, []
        for C, ro in zip(comps, roots):
            seen, q = {ro}, [ro]
            for u in q:
                for w in sorted(A[u]):
                    if w not in seen:
                        seen.add(w)
                        par[w] = u
                        order.append(w)
                        q.append(w)
        # the rooting rule
        if r in par:
            assert sum(1 for v in par if par[v] == r) >= 2
        yield par, order


def decide_base(ob, n, Bverts, Bedges, phi, par):
    """Exact: does H = B - phi have a Lovasz decomposition with (i) and (ii)?"""
    H = [e for e in Bedges if tuple(sorted(e)) not in phi]
    deg = {v: 0 for v in Bverts}
    for a, b in H:
        deg[a] += 1
        deg[b] += 1
    assert all(deg[v] % 2 == 1 for v in Bverts), "H not all-odd"
    b = [1 if v in deg else 0 for v in range(n)]
    X = [0] * n
    for v, p in par.items():
        X[v] |= 1 << p
    forb = []
    kids = {}
    for v, p in par.items():
        kids.setdefault(p, []).append(v)
    for p, ks in kids.items():
        for x, y in itertools.combinations(ks, 2):
            forb.append((x, y))
    return H, ob.query(n, H, b, X, forb)


def lift_and_check(J_E, z, r, n, H, par, order, D0):
    """Append the forest to D0 (parents first) and check (T1)."""
    Q = {}
    paths = [list(P) for P in D0]
    # (i)/(ii) checked independently of obase
    for P in paths:
        Q[P[0]] = P
        Q[P[-1]] = P
    for v, p in par.items():
        assert p not in Q[v], "(i)"
    for x in par:
        for y in par:
            if x < y and par[x] == par[y]:
                assert Q[x] is not Q[y], "(ii)"
    check_decomp({frozenset(e) for e in H}, paths)
    for v in order:
        p = par[v]
        idx = [i for i, P in enumerate(paths) if P[0] == v or P[-1] == v]
        assert len(idx) == 1
        P = paths[idx[0]]
        if P[0] == v:
            P.insert(0, p)
        else:
            P.append(p)
    BE = {e for e in J_E if z not in e}
    ends = check_decomp(BE, paths, maxpaths=(n - 1) // 2, r=r, minends=2)
    return ends.get(r, 0)


def t1_instances(n, E):
    A = adjacency(n, E)
    ev = [v for v in range(n) if len(A[v]) % 2 == 0]
    if len(ev) != 1 or min(len(a) for a in A) < 3 or not kconn(n, A, 3):
        return None, []
    z = ev[0]
    return z, sorted(A[z])
