"""ao_xcheck.py -- audit A37b item 6: independent re-decision of allodd_dl constraint sets.

Own enumeration of the constraint families (from the manuscript's definitions, not from the C
code), own exact decider ./obase (a set of clauses holds iff some choice of one literal per clause,
a conjunction of per-path avoidances, is realisable), optional CP-SAT (own model, with the
disjunctions as clauses) as a second method.  Every witness is checked independently.

modes:
  compare FAMS G6FILE ALLODD_OUT [adj]  -- decide EVERY set of the families and compare the set of
        failures with the FAIL lines of allodd_dl (run with -A when 'adj' is given)
  sample FAMS G6FILE NSETS SEED [cpsat] -- decide NSETS random sets per graph (non-adjacent pairs);
        expected: all hold
families: F2 F3 X2 X3 XF XF2
"""
import itertools
import os
import random
import sys

from ortools.sat.python import cp_model

from oddbase_lib import Obase
from a37lib import adjacency, check_decomp, g6_decode


def lit(c, x):
    return (c, x)


def families(n, A, adj_ok, fams):
    """Yield (fam, clauses) with clauses a tuple of frozensets of literals (c, x) = 'x not on Q(c)'."""
    pairs = [(a, b) for a in range(n) for b in range(a + 1, n) if adj_ok or b not in A[a]]
    FREE = lambda p: frozenset({(p[0], p[1]), (p[1], p[0])})
    FIX = lambda p, o: frozenset({(p[1], p[0])} if o else {(p[0], p[1])})
    for i, j in itertools.combinations(range(len(pairs)), 2):
        P, Q = pairs[i], pairs[j]
        if set(P) & set(Q):
            continue
        if "F2" in fams:
            yield "F2", (FREE(P), FREE(Q))
        if "X2" in fams:
            for o1, o2 in itertools.product((0, 1), repeat=2):
                yield "X2", (FIX(P, o1), FIX(Q, o2))
        if "XF" in fams:
            for o in (0, 1):
                yield "XF", (FIX(P, o), FREE(Q))
                yield "XF", (FIX(Q, o), FREE(P))
    for i, j, k in itertools.combinations(range(len(pairs)), 3):
        P, Q, R = pairs[i], pairs[j], pairs[k]
        if len(set(P) | set(Q) | set(R)) != 6:
            continue
        if "F3" in fams:
            yield "F3", (FREE(P), FREE(Q), FREE(R))
        if "X3" in fams:
            for o in itertools.product((0, 1), repeat=3):
                yield "X3", (FIX(P, o[0]), FIX(Q, o[1]), FIX(R, o[2]))
        if "XF2" in fams:
            for o in (0, 1):
                t = (P, Q, R)
                for f in range(3):
                    yield "XF2", (FIX(t[f], o), FREE(t[(f + 1) % 3]), FREE(t[(f + 2) % 3]))


def satisfied(paths, clauses):
    Q = {}
    for P in paths:
        Q[P[0]] = set(P)
        Q[P[-1]] = set(P)
    return all(any(x not in Q[c] for (c, x) in cl) for cl in clauses)


def decide_obase(ob, n, E, clauses):
    """Exact unless both budgeted passes are cut off: pass 1 tries every orientation (one literal
    per clause) with the small-budget process OB_SMALL, pass 2 the rest with `ob` (its own budget,
    none by default).  A 0 answer of either process is exact."""
    choices = list(itertools.product(*[sorted(cl) for cl in clauses]))
    if OB_SMALL[0] is not None and len(choices) > 1:
        rest = []
        for choice in choices:
            D = _try(OB_SMALL[0], n, E, clauses, choice)
            if D is not None:
                return D
            if OB_SMALL[0].last == "2":
                rest.append(choice)
        choices = rest
    for choice in choices:
        D = _try(ob, n, E, clauses, choice)
        if D is not None:
            return D
    return None


OB_SMALL = [None]


def _try(ob, n, E, clauses, choice):
    if True:
        X = [0] * n
        for c, x in choice:
            X[c] |= 1 << x
        D = ob.query(n, E, [1] * n, X, [])
        if D is not None:
            ends = check_decomp({frozenset(e) for e in E}, D, maxpaths=n // 2)
            assert all(ends.get(v, 0) == 1 for v in range(n)), "not Lovasz"
            assert satisfied(D, clauses), "witness violates"
            return D
        return None


def decide_cpsat(n, E, clauses, time_limit=60.0):
    """Own CP-SAT model: n/2 path slots, every vertex exactly one end; clause literals as
    booleans: lit(c,x) -> for every slot, end(c) in slot -> x not in slot."""
    E = [tuple(sorted(e)) for e in E]
    P = n // 2
    m = cp_model.CpModel()
    x = {(e, s): m.NewBoolVar("") for e in E for s in range(P)}
    f = {}
    for (a, b) in E:
        for s in range(P):
            f[(a, b, s)] = m.NewBoolVar("")
            f[(b, a, s)] = m.NewBoolVar("")
            m.Add(f[(a, b, s)] + f[(b, a, s)] == x[((a, b), s)])
    for e in E:
        m.AddExactlyOne(x[(e, s)] for s in range(P))
    nb = {v: [] for v in range(n)}
    inc = {v: [] for v in range(n)}
    for (a, b) in E:
        nb[a].append(b)
        nb[b].append(a)
        inc[a].append((a, b))
        inc[b].append((a, b))
    st, fi, on = {}, {}, {}
    for s in range(P):
        pos = {v: m.NewIntVar(0, n, "") for v in range(n)}
        for v in range(n):
            ins = [f[(u, v, s)] for u in nb[v]]
            outs = [f[(v, u, s)] for u in nb[v]]
            m.Add(sum(ins) <= 1)
            m.Add(sum(outs) <= 1)
            st[(v, s)] = m.NewBoolVar("")
            fi[(v, s)] = m.NewBoolVar("")
            m.Add(st[(v, s)] - fi[(v, s)] == sum(outs) - sum(ins))
            m.Add(st[(v, s)] + fi[(v, s)] <= 1)
            on[(v, s)] = m.NewBoolVar("")
            for e in inc[v]:
                m.AddImplication(x[(e, s)], on[(v, s)])
            m.AddBoolOr([x[(e, s)] for e in inc[v]]).OnlyEnforceIf(on[(v, s)])
        m.Add(sum(st[(v, s)] for v in range(n)) == 1)
        m.Add(sum(fi[(v, s)] for v in range(n)) == 1)
        for (a, b) in E:
            m.Add(pos[b] == pos[a] + 1).OnlyEnforceIf(f[(a, b, s)])
            m.Add(pos[a] == pos[b] + 1).OnlyEnforceIf(f[(b, a, s)])
    for v in range(n):
        m.Add(sum(st[(v, s)] + fi[(v, s)] for s in range(P)) == 1)
    for cl in clauses:
        ls = []
        for (c, xx) in cl:
            L = m.NewBoolVar("")
            for s in range(P):
                # L and c ends in slot s  ->  xx not on slot s
                endc = m.NewBoolVar("")
                m.Add(st[(c, s)] + fi[(c, s)] == 1).OnlyEnforceIf(endc)
                m.Add(st[(c, s)] + fi[(c, s)] == 0).OnlyEnforceIf(endc.Not())
                m.AddBoolOr([L.Not(), endc.Not(), on[(xx, s)].Not()])
            ls.append(L)
        m.AddBoolOr(ls)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_search_workers = 1
    res = solver.Solve(m)
    if res in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        paths = []
        for s in range(P):
            nxt = {}
            start = None
            for (a, b) in E:
                if solver.Value(f[(a, b, s)]):
                    nxt[a] = b
                if solver.Value(f[(b, a, s)]):
                    nxt[b] = a
            for v in range(n):
                if solver.Value(st[(v, s)]):
                    start = v
            path = [start]
            while path[-1] in nxt:
                path.append(nxt[path[-1]])
            paths.append(path)
        ends = check_decomp(set(frozenset(e) for e in E), paths, maxpaths=P)
        assert all(ends.get(v, 0) == 1 for v in range(n))
        assert satisfied(paths, clauses), "cpsat witness violates"
        return "FEAS"
    return "INFEAS" if res == cp_model.INFEASIBLE else "UNKNOWN"


def parse_fail(path):
    out = set()
    for line in open(path):
        t = line.split()
        if not t or t[0] not in ("FAIL", "UNDEC"):
            continue
        assert t[0] == "FAIL", line
        fam, g6 = t[1], t[2]
        cls, cur = [], None
        for tok in t[3:]:
            if tok == "(":
                cur = set()
            elif tok == ")":
                cls.append(frozenset(cur))
                cur = None
            elif cur is not None:
                c, xx = map(int, tok.split("|"))
                cur.add((c, xx))
        out.add((g6, fam, frozenset(cls)))
    return out


def main():
    mode = sys.argv[1]
    fams = sys.argv[2].split(",")
    g6s = [l.split()[0] for l in open(sys.argv[3]) if l.strip()]
    ob = Obase()
    if os.environ.get("OB_SMALL"):
        OB_SMALL[0] = Obase(budget=int(os.environ["OB_SMALL"]))
    if mode == "compare":
        theirs = parse_fail(sys.argv[4])
        adj_ok = len(sys.argv) > 5 and sys.argv[5] == "adj"
        mine = set()
        tot = {}
        for g6 in g6s:
            n, E = g6_decode(g6)
            A = adjacency(n, E)
            El = [tuple(sorted(e)) for e in E]
            for fam, cls in families(n, A, adj_ok, fams):
                tot[fam] = tot.get(fam, 0) + 1
                if decide_obase(ob, n, El, cls) is None:
                    mine.add((g6, fam, frozenset(cls)))
        th = {k for k in theirs if k[1] in fams}
        for fam in fams:
            a = {k for k in mine if k[1] == fam}
            b = {k for k in th if k[1] == fam}
            print(f"{fam}: sets {tot.get(fam, 0)}, obase failures {len(a)}, allodd_dl failures {len(b)}, "
                  f"only obase {len(a - b)}, only allodd_dl {len(b - a)}")
    else:
        nsets, seed = int(sys.argv[4]), int(sys.argv[5])
        use_cp = len(sys.argv) > 6 and sys.argv[6] == "cpsat"
        rng = random.Random(seed)
        cnt = {}
        for g6 in g6s:
            n, E = g6_decode(g6)
            A = adjacency(n, E)
            El = [tuple(sorted(e)) for e in E]
            allsets = list(families(n, A, False, fams))
            print("GRAPH", g6, len(allsets), flush=True)
            for fam, cls in rng.sample(allsets, min(nsets, len(allsets))):
                c = cnt.setdefault(fam, [0, 0, 0, 0])
                c[0] += 1
                u0 = ob.unknown
                if decide_obase(ob, n, El, cls) is not None:
                    c[1] += 1
                else:
                    tag = "OBASE-UNKNOWN" if ob.unknown > u0 else "OBASE-FAIL"
                    print(tag, g6, fam, sorted(map(sorted, cls)), flush=True)
                if use_cp:
                    r = decide_cpsat(n, El, cls)
                    c[2 if r == "FEAS" else 3] += 1
                    if r != "FEAS":
                        print("CPSAT", r, g6, fam, sorted(map(sorted, cls)), flush=True)
        for fam, c in sorted(cnt.items()):
            print(f"{fam}: sampled {c[0]}, hold by obase {c[1]}" +
                  (f", hold by CP-SAT {c[2]}, not by CP-SAT {c[3]}" if use_cp else ""))


if __name__ == "__main__":
    main()
