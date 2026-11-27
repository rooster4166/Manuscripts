"""E-E: candidate weakenings of admissibility for L1* (mechanism (B)).
All connected graphs of order n with exactly one even vertex g, every odd c, every A subset of
V - N[c] with 1 <= |A| <= K.  Goodness via l1s 'ed'.  For each candidate condition, count the
instances that satisfy it and the failures among them.
  ADM : A cap N(g) = {}                       (L1*, the known admissibility)
  W1  : N(g) not inside A                      (g keeps a neighbour outside A)
  W2  : some neighbour of g outside A + N[c]
  W3  : g not in A and N(g) not inside A
  W4  : W2 and g not in A
  DER : the shape of the derived instances (G - gu, c, A) of blocked steps: some neighbour of g in N(c)
        (the tight case) and N(g) not inside A
Also: the derived instances themselves (from blocked residuals) are recorded separately by exp1c."""
import sys, subprocess, itertools, collections
import tf
n = int(sys.argv[1]); K = int(sys.argv[2])
gs = subprocess.run(['nauty-geng', '-cq', str(n)], capture_output=True, text=True).stdout.split()
inst = []; lines = []
for s in gs:
    G = tf.from_g6(s); ev = tf.evens(G)
    if len(ev) != 1: continue
    g = ev[0]; E = tf.edges(G)
    for c in G:
        if tf.deg(G, c) % 2 == 0: continue
        cand = [v for v in G if v != c and v not in G[c] and tf.deg(G, v) > 0]
        for k in range(1, K + 1):
            for S in itertools.combinations(cand, k):
                A = frozenset(S)
                inst.append((s, g, c, A, G))
                mask = sum(1 << a for a in A)
                lines.append(f"{n} {len(E)} " + " ".join(f"{a} {b}" for a, b in E) + f" {c} {mask}")
out = subprocess.run(['./l1s', 'ed', '20000000'], input="\n".join(lines) + "\n", capture_output=True, text=True).stdout.split()
assert len(out) == len(inst)
C = collections.Counter(); ex = collections.defaultdict(list)
for (s, g, c, A, G), o in zip(inst, out):
    o = int(o); good = (o == 1)
    if o == 2: C["budget"] += 1
    Ng = set(G[g]); Nc = set(G[c]) | {c}
    conds = {
        "ADM": not (A & Ng),
        "W1": not Ng <= A,
        "W2": bool(Ng - A - Nc),
        "W3": g not in A and not Ng <= A,
        "W4": bool(Ng - A - Nc) and g not in A,
        "DER": bool(Ng & Nc) and not Ng <= A,
        "W5": g in G[c],
        "W5+": g in G[c] and not (A & Ng) - set(),
        "DER2": g in G[c] and not Ng <= A,
    }
    for name, val in conds.items():
        if val:
            C[(name, "inst")] += 1
            if not good:
                C[(name, "FAIL")] += 1
                if len(ex[name]) < 3: ex[name].append((s, g, c, sorted(A)))
    if not conds["ADM"]:
        C[("inadmissible", "inst")] += 1
        if not good: C[("inadmissible", "FAIL")] += 1
for k, v in sorted(C.items(), key=str): print(k, v)
for k, v in ex.items(): print("EX", k, v)
