# The avoidance conjecture L1* — cloud session `claude/l1star`

Manuscript: `l1star.tex` (compile with `pdflatex` twice). Lean: `lean/GallaiLean/L1Star.lean`.
Experiment log: `research/experiments.md`, E25. Conclusions: `research/connections.md`, §AA.
Audit: `research/audit/A23-l1star.md`.

## Status
- **Local form (Conjecture 1.4): no counterexample.** Some Lovász decomposition has V(Q_c) ⊆ N[c] ∪ N(g). This is L1* for every admissible A at once, of any size.
  - Exhaustive for all connected graphs of order ≤ 10, and order 11 (see the table in the manuscript).
  - 38,896 random pairs (G, c) at orders 11–16.
  - In all-odd graphs it says V(Q_c) ⊆ N[c].
- **Two even vertices at distance ≥ 3 have a Lovász decomposition** (Conjecture 3.2; exhaustive to order 10). This follows from the local form.
  - At distance 1 or 2 such decompositions fail in about 4% of graphs.
  - The local form itself fails for two even vertices (61 of 404,488 pairs at order 10).
- **Proved and formalised:** `l1starGen_of_blocked : L1Blocked → L1StarGen` and `ee_of_l1Blocked : L1Blocked → EE`. A smallest counterexample to general L1* is *blocked*: G has an even vertex g, c ∉ N(g), and every neighbour of g has a neighbour in A ∖ {g}.
- **Proved, paper only:** five more reductions (boundary, route to c, Fan route, degree 2 at g, degree 3 at c). They give the structure of a smallest counterexample (Corollary 5.6).
  - At order 9, 13.9% of the |A| ≤ 2 instances are blocked, and 0.59% survive every reduction one level deep.
- **Open:** the blocked case. Both remaining shapes still occur (g ∈ A; A separates c from g). EE is certified by the reductions at every pair of order ≤ 7 except CP(3) + apex.

## Reproduction (scripts/)
Requirements: gcc, Python 3 with networkx, nauty (`nauty-geng`).
```
cd scripts
./regen.sh            # every quoted output except the long runs below
./run_n11.sh          # exhaustive order 11, local form (three slices, hours)
python3 rand_max.py 3000 7 5000000 11 12 13 14 15 16 > out/rand_max_11_16.txt
nauty-geng -cq 7 | python3 xcheck_brute.py > out/xcheck_7.txt    # brute-force cross-check (30 min)
nauty-geng -cq 7 | python3 cert.py 2 ; nauty-geng -cq 7 | python3 cert_ee.py   # certificate searches
```

| File | Content |
|---|---|
| `l1s.c` | exact oracle. Modes: `max K [n,q]` (local form; minimal failing subsets), `ed` (single queries), `gen K` (all A ⊆ V − N[c], classified), `stats` (lengths of Q_c), `two` (two even vertices), `packedev` (packed even vertices), `peloc` (local form with packed even vertices) |
| `brute.py`, `xcheck_brute.py` | independent brute force over transition systems; cross-check of `l1s ed` |
| `rand_max.py` | random graphs, orders 11–16 |
| `blocked_count.py` | census by the first applicable case of Theorem 4.2 |
| `irred_all.py` | instances surviving all reductions, one level deep |
| `cert.py`, `cert_ee.py` | recursive certificate search from the reductions (generic instances; EE instances) |
| `moves.py`, `irred.py`, `irred2.py` | earlier, smaller move sets (exploratory) |
| `te3walk.py` | Lovász Case I walks for two even vertices |
| `out/` | outputs |
