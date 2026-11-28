"""cp_validate6.py -- audit A37b: the own CP-SAT model (ao_xcheck.decide_cpsat) against allodd_dl -A
on every order-6 X2 and XF set with adjacent pairs admitted (so that the model must also refute)."""
from ao_xcheck import decide_cpsat, families, parse_fail
from a37lib import adjacency, g6_decode
theirs = parse_fail("ao6_A.out")
cnt = {}
for g6 in [l.strip() for l in open("ao6.g6") if l.strip()]:
    n, E = g6_decode(g6)
    A = adjacency(n, E)
    El = [tuple(sorted(e)) for e in E]
    for fam, cls in families(n, A, True, ["X2", "XF"]):
        r = decide_cpsat(n, El, cls)
        assert r in ("FEAS", "INFEAS"), r
        bad = (g6, fam, frozenset(cls)) in theirs
        c = cnt.setdefault(fam, [0, 0, 0])
        c[0] += 1
        c[1] += (r == "INFEAS")
        c[2] += ((r == "INFEAS") != bad)
for fam, c in sorted(cnt.items()):
    print(f"{fam}: sets {c[0]}, CP-SAT infeasible {c[1]}, disagreements with allodd_dl -A {c[2]}")
