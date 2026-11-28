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
- Theorem B (one connector), coverage tables, MR comparison, manuscript: in progress.

## Scripts
- `scripts/drm.cpp`: the method checker (options in the header).
- `scripts/thm_cov.py`: coverage of the degree conditions (Theorem A, Theorem B with connectors of
  length ≤ 2) and of the hypotheses of MR Thms 47, 74, 166.
- `scripts/mkJ.py` (residual format B with N(z) = {0..5} → J), `scripts/mkB.py` (J → B for ret.c).
