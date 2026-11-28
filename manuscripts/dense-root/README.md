# Test1 at roots of degree n − 2 (session `claude/dense-root`)

Manuscript `dense-root.tex` (compile with `pdflatex` twice). Lean: `lean/GallaiLean/DenseRoot.lean`,
`lean/GallaiLean/DenseRootB.lean`. Audits: `research/audit/A39-dense-root.md` (paper, `DenseRoot.lean`,
scripts, data; all findings applied), `research/audit/A39b-dense-root-lean.md` (`DenseRootB.lean`; F1–F4 applied, F5–F6 are Lean hygiene).

## Status
- **Proved and formalised** (no `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`; full
  `lake build` green, 18,436 jobs):
  - `famReassemble` (Lemma 2.2, forward direction): any family (members at the neighbours of r,
    nontrivial ones a decomposition of B − r) with disjoint compatible pairs and the remaining
    singletons gives a decomposition of B with one path per pair/singleton and one end at r per
    singleton. No parity hypothesis on B.
  - `hall_defect_two`, `hallReassemble` (Theorem 2.3): k − 1 A-paths matched into k − 1 pairwise
    disjoint C-members with defect 2 (|S| + #{C-members meeting all of S} ≤ k + 1 for |S| ≥ 3)
    ⇒ k paths with exactly two ends at r.
  - `exists_decomp_of_oneEven` (Theorem A): d(r) = 2k − 2, B − r has at most one vertex of positive
    even degree, every neighbour of r has degree ≥ 2, and for 3 ≤ t ≤ k − 1:
    ⌊(h_t + ε)/2⌋ + t ≤ k + 1 or ⌊h_{t+1}/2⌋ + ε + 2t ≤ k + 1 (ε = 1 if some neighbour of r is
    even in B − r). Contains re-tight Theorem 3.1 (ε = 0) without the Eulerian hypothesis.
    `test1At_of_oneEven`: the spine form, Test1At J z r.
  - Theorem B (`DenseRootB.lean`): the even vertices of B − r are q₁, q₂, s; a connector path Q from
    q₁ to q₂ is kept as a member. `exists_decomp_of_connector` (no other vertex of Q adjacent to r,
    δ = 0; Q = q₁q₂ or q₁sq₂), `exists_decomp_of_connector_mid` (one such vertex y, δ = 1;
    Q = q₁yq₂, q₁ysq₂ or q₁syq₂); conclusions existential (the proofs start from an arbitrary
    Lovász decomposition of B − r − E(Q)); spine forms
    `test1At_of_connector`, `test1At_of_connector_mid`; machinery `consPath`,
    `exists_lovasz_connector`, `connector_core`.
- **Proved on paper**: Lemma 1.1 (tightness, parity: when Theorems A and B apply in terms of J),
  Corollaries 3.2 and 4.2, the converse of Lemma 2.2.
- **Computed** (order 9, d(z) = 6, all 1,756 roots of degree n − 2 of the 1,819 3-connected J;
  scope in the manuscript, §5):
  - exact family check (`ret.c` of re-tight, default mode): Test1 at all 1,756;
  - Theorem A 459, Theorem B 1,171 (1,143 with connectors of length ≤ 2), A ∪ B 1,630 (on
    multi-token's 1,597 unscheduled roots: 1,472); with MR Thms 47/50/74/166 also 1,686 (1,528).
    The 28 roots needing a length-3 connector are also Lean instances of `test1At_of_connector_mid`
    (`research/audit/A39b-scripts/len3_instances.lean`). Outside A ∪ B: 126 = 24 with no connector
    + 102 where the degree condition fails;
  - **marked-reduction Prop. 139 (unrefereed) already claims Test1 at all 1,756** (root degree 6 at
    d(z) = 6), so the order-9 numbers measure the reach of Theorems A and B, which hold for every n;
  - the method (Lovász of (B − r) − Φ, Φ empty or one path of length ≤ 3, free choice of the Lovász
    even vertex): all 1,756 (`data/drm9G.out`; 1,750 without `-G`, `data/drm9.out`); every Lovász
    decomposition works for some (g, Φ) at 1,742 (`data/drmA9_m0.out`);
  - frozen roots (113): with free paths (one at degree n − 4, two at degree n − 6) the method
    succeeds at 112 (`data/frz9.out`); 105 with at most one free path (audit A39). At the exception
    (B − r = K₇) Test1 holds by a Hamilton decomposition (audit A39).
  - Residual families (resid_O8, resid_O10, E28, clt; 88 roots): no theorem here or in the
    collection applies; `ret.c` gives Test1 at 84 (4 undecided); the method is undecided at all 88
    and at the 42 residual frozen roots.
- **Open**: several connectors (an L-path joining two connector interiors breaks the argument;
  audit A39, F4), no connector (24 order-9 roots), the dense middle.

## Scripts (`scripts/`; `run_all.sh` regenerates every file in `data/` with the shipped budgets)
- `drm.cpp`: the method checker (options in the header).
- `thm_cov.py`: the degree conditions (Theorem A, Theorem B with all connectors, lengths 1–3) and the
  hypotheses of MR Thms 47, 74, 166; `coverage.py` (per data set, also MR 50), `cov1597.py`,
  `crosscheck.py` (certified roots have every-D success), `look.py` (the uncovered roots by kind).
- `mkJ.py` (residual format B with N(z) = {0..5} → J), `mkB.py` (J → B for `ret.c`), `frozen.py`
  (frozen roots from multi-token's `*_explore.txt`), `profile.py`, `profile2.py` (degree profiles),
  `run_resid.sh` (the first residual run, superseded by `run_all.sh`).
