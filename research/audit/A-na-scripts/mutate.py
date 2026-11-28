"""Mutation test of the manuscript's verifier (nalib.check_lovasz / check_na_output).

For every weak pair of order 6, take the constructed decomposition and apply corrupting mutations;
a sound verifier must reject every mutant that my independent verifier rejects, and the two must
agree on every mutant.  Also feed the verifier decompositions in which Q(y) contains x (taken
from the full list of Lovasz decompositions), which must be rejected."""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(1, os.path.abspath(os.path.join(HERE, "..", "..", "..", "manuscripts", "na", "scripts")))
import indep  # noqa: E402
import nalib  # noqa: E402

rng = random.Random(1)
stats = dict(mutants=0, agree=0, disagree=0, mine_rejects=0, theirs_rejects=0, bad_lds=0,
             bad_lds_rejected=0)


def mutants(D):
    D = [list(P) for P in D]
    out = []
    if len(D) >= 1:
        out.append(D[1:])                                  # drop a path
        P = D[0]
        out.append([P[:-1]] + D[1:] if len(P) > 2 else D)  # drop last edge of a path
        out.append([P[::-1]] + D[1:])                      # reverse (harmless)
        out.append(D + [P])                                # duplicate a path
    if len(D) >= 2:
        P, Q = D[0], D[1]
        if P[-1] == Q[0]:
            out.append([P + Q[1:]] + D[2:])
        out.append([P + [Q[0]]] + D[1:])                   # append a (maybe non-)edge
        # swap one interior vertex
    for i, P in enumerate(D):
        if len(P) >= 3:
            Q = P[:]
            j = rng.randrange(1, len(P) - 1)
            Q[j], Q[j - 1] = Q[j - 1], Q[j]
            out.append(D[:i] + [Q] + D[i + 1:])
            break
    return out


for line in sys.stdin:
    G = indep.read_g6(line)
    if any(len(G[v]) % 2 == 0 for v in G):
        continue
    lds = indep.all_lovasz(G)
    for y in G:
        for x in sorted(G[y]):
            for D in lds:
                Q = [P for P in D if y in (P[0], P[-1])][0]
                if x in Q:
                    stats["bad_lds"] += 1
                    ok, _ = nalib.check_na_output(G, D, y, {x})
                    stats["bad_lds_rejected"] += (not ok)
            if not indep.weak(G, y, {x}):
                continue
            D, W = nalib.na_construct(G, y, {x})
            for M in mutants(D):
                stats["mutants"] += 1
                try:
                    a, _ = nalib.check_na_output(G, M, y, {x})
                except AssertionError:
                    a = False  # path_ending_at asserts uniqueness
                b, _ = indep.verify(G, M, y, {x})
                stats["mine_rejects"] += (not b)
                stats["theirs_rejects"] += (not a)
                if a == b:
                    stats["agree"] += 1
                else:
                    stats["disagree"] += 1
                    print("DISAGREE", line.strip(), y, x, M, a, b)
print(" ".join("%s=%d" % kv for kv in stats.items()))
