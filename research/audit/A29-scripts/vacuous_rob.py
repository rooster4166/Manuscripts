"""A29: does exp1.py's robustness (needs a good child) differ from the paper's literal definition?
usage: python3 exp1.py oe57.g6 > exp1.out ; python3 vacuous_rob.py exp1.out"""
import sys
import dllib
inst = vac = 0
for line in open(sys.argv[1]):
    if not line.startswith('NOROB'):
        continue
    f = line.split(); g6 = f[1]; g, a, b = (int(x[2:]) for x in f[2:5])
    n, E = dllib.g6_decode(g6); A = dllib.adjsets(n, E); hit = False
    for u in sorted(A[g] - {a, b}):
        Ds, c = dllib.enum_decomps(n, dllib.remove_edge(E, g, u))
        if not any(dllib.dl_good(D, a, b) for D in Ds):
            hit = True
    inst += 1; vac += hit
print("NOROB instances", inst, "with a target that has no good child", vac)
