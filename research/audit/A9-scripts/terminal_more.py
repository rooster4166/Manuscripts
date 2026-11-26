import sys, itertools
sys.path.insert(0, '/home/user/Manuscripts/manuscripts/d6-frontier/scripts')
import importlib.util
spec = importlib.util.spec_from_file_location('tc', '/home/user/Manuscripts/manuscripts/d6-frontier/scripts/terminal_check.py')
src = open(spec.origin).read().split("U = list(range(6))\nshow(")[0]   # library part only
ns = {}; exec(src, ns)
survivors, classify = ns['survivors'], ns['classify']
def summary(name, S, Uset, Fset):
    profs = {(p, e) for p, e, _ in S}
    types = {}
    for p, e in profs:
        types.setdefault(classify(p, e, Uset, Fset), []).append(p)
    print(name, {t: len(v) for t, v in sorted(types.items())})
    assert 'other' not in types
U = list(range(6))
for nf in (3, 4):
    F = [f'f{i}' for i in range(nf)]
    summary(f"B-form, |F| = {nf}, F independent", survivors(U, F, [], 6, set(F), True), set(U), set(F))
    summary(f"B-form, |F| = {nf}, F clique", survivors(U, F, list(itertools.combinations(F, 2)), 6, set(F), True), set(U), set(F))
T = list(range(5))
for nf in (0, 2, 3):
    F = ['r'] + [f'f{i}' for i in range(nf)]
    summary(f"W-form, |F| = {nf}", survivors(T, F, [], 4, set(F), False), set(T), set(F))
print("ok")
