# Test1 at roots of degree n − 2 (session `claude/dense-root`)

Work in progress. Lean: `lean/GallaiLean/DenseRoot.lean`.

## Status (milestone 1)
- **Proved and formalised** (no `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`;
  full `lake build` green, 18,434 jobs):
  - `famReassemble` (Lemma 2.1): any family (members at the neighbours of r, nontrivial ones a
    decomposition of B − r) with a set of disjoint compatible pairs and the remaining singletons
    gives a decomposition of B with one path per pair/singleton and one end at r per singleton.
    No parity hypothesis on B.
  - `hall_defect_two`, `hallReassemble` (Theorem 2.3): A-paths matched into k − 1 pairwise
    disjoint C-members with defect 2 (Hall: |S| + #{C-members meeting all of S} ≤ k + 1 for
    |S| ≥ 3) ⇒ k paths with exactly two ends at r.
  - `exists_decomp_of_oneEven` (Theorem A): d(r) = 2k − 2, B − r has at most one vertex of
    positive even degree, every neighbour of r has degree ≥ 2, and for 3 ≤ t ≤ k − 1:
    ⌊(h_t + ε)/2⌋ + t ≤ k + 1 or ⌊h_{t+1}/2⌋ + ε + 2t ≤ k + 1 (ε = 1 if some neighbour of r is
    even in B − r). This contains re-tight Theorem 3.1 (ε = 0) without the Eulerian hypothesis.
  - `test1At_of_oneEven`: the spine form, Test1At J z r.
- **Computed** (order 9, d(z) = 6, all 1,756 roots of degree n − 2 of the 1,819 3-connected J):
  - exact family check (`ret.c` of re-tight, default mode): Test1 holds at all 1,756;
  - the method (Lovász of (B − r) − Φ, Φ ≤ one path of length ≤ 3, free choice of the Lovász even
    vertex): succeeds at all 1,756 (`data/drm9.out`, 6 roots need `-G`);
  - "every Lovász decomposition works" for some (g, Φ) with Φ as separate members: 1,742 / 1,756
    (`data/drmA9_m0.out`);
  - frozen roots (multi-token explore, least potential 5, degree < n − 2): the method extended
    by one free path succeeds at 112 / 113 (`data/frz9.out`).
- **Theorem B** (`lean/GallaiLean/DenseRootB.lean`, no `sorry`, standard axioms): s ∈ N(z),
  d(z) = n − 3, one connector path Q between the two vertices of V(B) ∖ N(z), kept as a member:
  `exists_decomp_of_connector` (no other vertex of Q adjacent to r, δ = 0),
  `exists_decomp_of_connector_mid` (one such vertex y, δ = 1), spine forms `test1At_of_connector`,
  `test1At_of_connector_mid`; machinery `consPath`, `exists_lovasz_connector`, `connector_core`.
- Coverage (order 9, `scripts/coverage.py`): Theorem A 459, Theorem B 1,143, A ∪ B 1,602 of 1,756;
  with the hypotheses of MR Thms 74/166 1,658. On multi-token's 1,597 unscheduled roots: 1,445 and
  1,501 (`scripts/cov1597.py`). Residual families: 0 (Theorems A, B need |V(B) ∖ N(z)| = 2).
- Manuscript `dense-root.tex` (compile with pdflatex twice).

## Scripts
- `scripts/drm.cpp`: the method checker (options in the header).
- `scripts/thm_cov.py`: the degree conditions (Theorem A, Theorem B with connectors of length ≤ 2)
  and the hypotheses of MR Thms 47, 74, 166; `scripts/coverage.py` (per data set, also MR 50),
  `scripts/cov1597.py`, `scripts/crosscheck.py` (certified roots have every-D success),
  `scripts/look.py` (the uncovered roots by kind).
- `scripts/mkJ.py` (residual format B with N(z) = {0..5} → J), `scripts/mkB.py` (J → B for ret.c).
