"""Independent replay of block-degree Sec. 8 (three paths on a nine-cycle)."""
import itertools
from seglib import dihedral
N = 9
Ecore = (0, 3, 4, 7, 6, 1, 2, 5)   # exceptional order on cyclic core 0..7
# doubled links of E: P-links that are C8-edges
def links(o): return [frozenset((o[i], o[i+1])) for i in range(len(o)-1)]
C8 = {frozenset((i, (i+1) % 8)) for i in range(8)}
dbl = [l for l in links(Ecore) if l in C8]
print("E doubled links:", [tuple(sorted(l)) for l in dbl])
# dihedral images of E onto the 8-core {1..8} of a 9-cycle with omitted site 0;
# the 8-core cyclic order is 1,2,...,8 (gap 8-1 passes through 0)
orders = set()
for g in dihedral(8):
    img = tuple(g[v] + 1 for v in Ecore)        # core label i -> site g(i)+1
    dimg = [frozenset(g[a] + 1 for a in l) for l in dbl]
    if frozenset((8, 1)) in dimg:
        orders.add(min(img, img[::-1]))
orders = sorted(orders)
print("orders with omitted site 0:", ["".join(map(str, o)) for o in orders])
claimed = {"25618347", "27634185", "41856327"}
print("match claimed set (up to reversal):",
      {min(s, s[::-1]) for s in claimed} == {min("".join(map(str,o)), "".join(map(str,o))[::-1]) for o in orders})
ends0 = [frozenset((o[0], o[-1])) for o in orders]
print("end pairs:", [tuple(sorted(e)) for e in ends0])
def shift(o, m): return tuple((v + m) % N for v in o)
# omitted triples: 84 labelled, 7 dihedral classes
D9 = dihedral(N)
def canon_triple(T):
    return min(tuple(sorted(g[v] for v in T)) for g in D9)
classes = {}
for T in itertools.combinations(range(N), 3):
    classes.setdefault(canon_triple(T), []).append(T)
print("triple classes:", sorted(classes))
counts = {}
configs = []
for rep in sorted(classes):
    for T in classes[rep]:
        comp = set(range(N)) - set(T)
        c = 0
        for choice in itertools.product(range(3), repeat=3):
            ps = [shift(orders[choice[i]], T[i]) for i in range(3)]
            ends = [x for p in ps for x in (p[0], p[-1])]
            if len(set(ends)) == 6 and set(ends) == comp:
                c += 1
                if T == rep: pass
                configs.append((T, tuple(ps)))
        if T == rep: counts[rep] = c
print("choices per representative triple:", counts)
print("labelled configurations total:", len(configs))
# orbits of configurations under D9 (as sets of unoriented orders)
def norm(p): return min(p, p[::-1])
def canon_conf(ps):
    best = None
    for g in D9:
        s = tuple(sorted(norm(tuple(g[v] for v in p)) for p in ps))
        if best is None or s < best: best = s
    return best
orb = {}
for T, ps in configs:
    orb.setdefault(canon_conf(ps), []).append(ps)
print("orbits:", [(k, len(v)) for k, v in orb.items()])
C9 = {frozenset((i, (i+1) % N)) for i in range(N)}
def compulsory(p):  # 1st,3rd,5th,7th links are forced direct chords
    L = links(p); return {L[i] for i in (0, 2, 4, 6)}
for k, v in orb.items():
    ps = v[0]
    rep = [compulsory(p) for p in ps]
    rept = set()
    for i in range(3):
        for j in range(i+1, 3):
            rept |= rep[i] & rep[j]
    # also: no compulsory chord may be a C9 edge
    onC = [l for r in rep for l in r if l in C9]
    print("orbit rep", ["".join(map(str, p)) for p in ps], "repeated compulsory chords:",
          sorted(tuple(sorted(l)) for l in rept), "compulsory on C9:", onC)
# check the paper's table entries belong to the orbits
tab = {1: ("03486125", "28735106", "36720458"), 2: ("03486125", "26710358", "38745206")}
for key, t in tab.items():
    ps = [tuple(int(c) for c in s) for s in t]
    print("table row", key, "canon in orbits:", canon_conf(ps) in orb,
          "omitted:", [ (set(range(9)) - set(p)).pop() for p in ps])
# verify the replacement rows for orbit 1
A = tuple(int(c) for c in "03486125"); B = tuple(int(c) for c in "28735106")
rows = [("0C1A2C3A4A8A6C5"), ("2C1A6C7C8C0A3B5C4"), ("4C3B7B8B2A5B1B0B6")]
labelled = []
for r in rows:
    verts = [int(c) for c in r[0::2]]; labs = r[1::2]
    assert len(set(verts)) == len(verts), r
    labelled.append(list(zip(zip(verts, verts[1:]), labs)))
need = {('C', frozenset((i, (i+1) % 9))) for i in range(9)} | \
       {('A', l) for l in links(A)} | {('B', l) for l in links(B)}
got = [(lab, frozenset(e)) for row in labelled for e, lab in row]
print("rows partition C,A,B labelled links:", sorted(map(str,got)) == sorted(map(str,need)) and len(got) == len(set(got)) == 23)
var = lambda p: {links(p)[i] for i in (1, 3, 5)}
for idx, row in enumerate(labelled):
    print(" row", idx+1, "variable A links:", sum(1 for e, lab in row if lab == 'A' and frozenset(e) in var(A)),
          "variable B links:", sum(1 for e, lab in row if lab == 'B' and frozenset(e) in var(B)),
          "ends:", row[0][0][0], row[-1][0][1])
