"""A41: an explicit order-8 counterexample to the 'star version' of CL stated in nodata Section 5.2
("pairs, 2-chains and stars, every star satisfying (H1)"): it arises at the real (T1) instance
J = H?bc~f{, z = 8, r = 0.  All Lovasz decompositions are enumerated (examples_bruteforce.py)."""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from examples_bruteforce import lovasz_decomps, satisfies, hall_H1, check_decomp

E = [(0, 5), (0, 6), (0, 7), (1, 5), (2, 5), (3, 7), (4, 6), (6, 7)]
# pair 4 <- 0 (0 notin Q(4)); star 7 <- {1, 2}; 2-chain 5 <- 6 <- 3
avoid = {4: {0}, 1: {7}, 2: {7}, 6: {5}, 3: {6}}
sibs = [(1, 2)]
nonedges = [(4, 0), (1, 7), (2, 7), (6, 5), (3, 6)]
Es = {frozenset(e) for e in E}
assert all(frozenset(p) not in Es for p in nonedges)
deg = [sum(v in e for e in E) for v in range(8)]
assert all(d % 2 == 1 for d in deg), deg
allD = list(lovasz_decomps(8, E))
for D in allD:
    check_decomp(8, E, D)
good = [D for D in allD if satisfies(D, avoid, sibs)]
print("degrees", deg, "Lovasz decompositions", len(allD), "satisfying", len(good))
print("(H1) at 7, X = {1, 2}:", hall_H1(8, E, 7, [1, 2]))
for name, av, sb in [("star alone", {1: {7}, 2: {7}}, [(1, 2)]), ("2-chain alone", {6: {5}, 3: {6}}, []),
                     ("pair alone", {4: {0}}, []), ("star + 2-chain", {1: {7}, 2: {7}, 6: {5}, 3: {6}}, [(1, 2)]),
                     ("star + pair", {1: {7}, 2: {7}, 4: {0}}, [(1, 2)]), ("2-chain + pair", {6: {5}, 3: {6}, 4: {0}}, [])]:
    print(" ", name, sum(1 for D in allD if satisfies(D, av, sb)))
assert not good
