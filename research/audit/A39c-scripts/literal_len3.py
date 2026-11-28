"""A39c: run the proof of Theorem 4.1 literally for connectors of LENGTH 3 (q1 y s q2, q1 s y q2),
the case added in 2660c7e.  Reuses audit A39's checker `A39-scripts/literal_AB.py` (every Lovasz
decomposition of G', every tie-break of the attachment plan, every set S; the claims B1-B5 of the
proof, the bounds on |J_S|, Hall, and the final reassembly verified from scratch), with three textual
patches: connectors() enumerates only length-3 paths with ends in N, at most one interior vertex in
N and every vertex of N odd in G'; delta = number of interior N-vertices (not `len(Q) == 3`); and
the delta = 1 plan takes y = the interior N-vertex (not Q[1], which is s for q1 s y q2).
usage: literal_len3.py J9 | literal_len3.py rand K COUNT SEED [CAP NODECAP]"""
import sys, types
A39 = __file__.rsplit('/', 2)[0] + '/A39-scripts'
sys.path.insert(0, A39)
src = open(A39 + '/literal_AB.py').read()
patches = [
    ("    for a, b in itertools.combinations(N, 2):\n        if b in G[a]:\n            out.append((a, b))\n"
     "        for y in G:\n            if y not in (a, b) and y in G[a] and y in G[b]:\n                out.append((a, y, b))\n",
     "    for a, b in itertools.combinations(N, 2):\n        for u in G[a]:\n            for v in G[u]:\n"
     "                if len({a, u, v, b}) == 4 and b in G[v] and (u in Nset) + (v in Nset) <= 1:\n"
     "                    out.append((a, u, v, b))\n"),
    ("    delta = 1 if len(Q) == 3 and Q[1] in Nset else 0\n",
     "    delta = sum(1 for v in Q[1:-1] if v in Nset)\n"),
    ("            y = Q[1]\n", "            y = [v for v in Q[1:-1] if v in Nset][0]\n"),
    ("1 if len(Q) == 3 and Q[1] in set(R.N) else 0", "sum(1 for v in Q[1:-1] if v in set(R.N))"),
]
for old, new in patches:
    cnt = src.count(old)
    assert cnt >= 1, old
    src = src.replace(old, new)
src = src.replace("if __name__ == '__main__':", "if False:")
mod = types.ModuleType('literal_len3_patched'); mod.__file__ = A39 + '/literal_AB.py'
exec(compile(src, 'literal_AB(patched)', 'exec'), mod.__dict__)
if sys.argv[1] == 'J9':
    mod.run_J9()
else:
    mod.run_rand(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]),
                 int(sys.argv[5]) if len(sys.argv) > 5 else 300,
                 int(sys.argv[6]) if len(sys.argv) > 6 else 20000)
print(dict(mod.STATS))
print('violations:', len(mod.VIOL))
