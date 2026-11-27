# Architectural synthesis after the full archive pass (2026-11-27)

This document reads the 31-paper archive together with this project's own results. It sets out what we actually have and chooses the architecture for reaching unrestricted Gallai. It supersedes the "Current strategy" paragraph of `ROADMAP.md`.

Abbreviations:

| Code | Paper |
|---|---|
| MR | marked-reduction |
| SP | separating-pairs |
| RE | root-endpoint-costs |
| OSB | odd-semi-clique-boundary |
| ED | even-degrees |
| DP | degree-preserving-decompositions |
| TVS | two-vertex-separators |
| CC | cycle-and-contact |
| NH | near-half-mixed-vertices |
| DEC | dense-exact-counts |
| ES | endpoint-structure (this project) |
| MM | missing-move (this project) |

## 1. One picture: an endpoint economy

Every reduction in the portfolio converts Gallai into the question of where path ends can be placed. Examples are the rooted private leaf, the marked bound, the two-end and three-end deletion tests, faithful descent (`BranchBase3`), and separator records. Every construction engine is a way of supplying, moving or gluing ends within the budget.

| Role | Engines (sources) |
|---|---|
| **Supply ends** | Lovász seeds (parity ends); Lemma 3 (ES, Ev − u); the spare path of a seed with an isolated vertex (MM); odd-order floor slack |
| **Move ends** | Fan single and grouped transfers. RE Thm 13.1 shows that rotation restorability at a vertex is exactly a **Hall matching condition**. Also relays (MM, d6-frontier) and Fan's alternative (MM) |
| **Open cycles (flowers)** | MR Thm 38 (≤ 7 cycles through x give j+1 paths with 2 ends at x); MR Thm 175 (8 cycles give 9, and m cycles give m + ⌈m/8⌉; K17 is sharp); MR Cor 39 (vertex insertion, cost ⌈q/8⌉ for Hall deficiency q); CC Thm 1 (12 nearly spanning cycles); DP Cor 7 (dense cycle supports, explicit N(c)); SP Thm 10.21 (CP(m), explicit Walecki flower); ES flower lemma / `hub_cycles` / receipt-or-flower |
| **Glue** | TVS Thm 1/7 (exact endpoint records across a 2-separator); SP §2 (cut vertices); MR Thm 113 (separator; Lean); matching-cut and small-edge-cut exclusions (SP §§8–13) |
| **Dense realisation** | SP Thm 14.1 (δ ≥ (1/2+ε)n: *every* locally feasible bounded profile is realised); robust expanders (SP §14); DEC (exact path numbers above Dirac); OSB (semi-cliques, with endpoint vectors prescribable); SP Cor 14.24/14.26 (near-half failures lie near K_{n/2,n/2}); Thm 14.37 (bipartite-like graphs give the floor); Cor 14.39 (an o(n) exceptional set X remains); NH (returns ≤ 2 exceptional vertices via Hamilton decompositions) |
| **Exact algebra** | Walecki; JM rainbow decompositions (repaired, audited); Hilton extension; Hoffman circulations; DP (determinant counts, ≥ 2^{C(r,2)} rearrangements, signed trades) |
| **Barriers** | **ED §12.4 cut inequality and Thm 46**: half-set prescriptions can cost arbitrarily many paths at every connectivity. SP 10.21 and our `cocktail_fan_barrier` / `cocktail_insertion_barrier`: the last step cannot be a Fan move on CP(m). MR 175: K17 sharpness. TVS Thm 2: local optimality can cost t − 1 paths. RE §2: exposure costs a path. DP §5: individually feasible paths that cannot coexist |

## 2. The least counterexample, assembled from all papers

Let (F, r) be a least even-order failure of the rooted test (R). It is equivalent to Gallai (Lean `gallai_iff_rootedTest`). From SP §§2–13, RE §§8–21 and MR:

- **Connectivity.** F is 2-connected, or an odd 2-connected block plus a leaf. It is 6-edge-connected, has no matching cut, and has no proper 4- or 5-edge cuts.
- **Degrees.** δ ≥ 6. If F is Eulerian, δ ≥ 10. Every degree-6 vertex has an odd neighbour.
- **Criticality.** p(F) = n/2. **Every failing root is an even vertex of degree ≥ 6 that is internal or absent on every path of every optimum** (SP Cor 10.17). In the endpoint-matroid language of ES, r is a **loop**.
- **Odd alternative.** Otherwise there is a smaller BP floor witness: 2-connected, no matching cut, ≥ h+1 missing edges, p > h.
- **Not dense.** δ < (1/2 + ε)n (SP 14.1). If δ is near n/2, F is o(n²)-close to K_{n/2,n/2}, with an o(n) exceptional set X (Cor 14.39).
- **Formal spine.** Gallai follows from `BranchBase3` (Lean). Gallai ⇔ marked tests (MR Thm 1, Lean). The 3-connected deletion tests (MR 113 in Lean; 114 modulo Thm 59).

## 3. Every route stalls at the same place

- **Local routes** (Fan, hub, flower, game). They close a root whenever enough ends can be delivered to its neighbourhood:
  - `hub_general` needs Σ_N b ≥ 2d − 5;
  - MR Cor 39 with Thm 175 needs Hall deficiency q ≤ 8;
  - RE 13.1 needs a Hall matching.
  
  They stall exactly when the seed cannot route ends into N(r). Examples are CP(m), Inv~|~zbw and A_{6,2} core roots, which needed symmetry or edge counts.
- **Dense routes.** They need n ≥ n0 and δ ≈ n/2. They stall at exceptional sets whose spokes must be assigned to compatible ends: NH "four squares", a unicyclic assignment, Hall type.
- **Matroid route (EMC).** It holds at n ≤ 8, where all 476 3-connected critical graphs are uniform. But **uniformity is false in general**: ED Thm 46 gives critical graphs of any connectivity s+1 whose half-set on one shore costs k + (h−s)/2 paths. The non-bases are forced by the **cut inequality** (ED (1)).

**Common denominator: routing ends through cuts.** Each stall is the failure of a supply-and-demand condition across a cut: Hall deficiency, Fan's numerical test, ED's inequality, NH's assignment, JM-repair's Hoffman cuts. This suggests that the right parameter-free object is a **min-max theorem for endpoint prescriptions**.

## 4. Candidate architectures

| | Architecture | Parameter-free? | Assessment |
|---|---|---|---|
| A | Sparse/dense split: uniform Fan + hub + flower for sparse cores; close Cor 14.39 to bank δ ≥ (1/2 − γ)n | **No**: dense engines need n ≥ n0 (astronomical) | Banks a major theorem (exact Gallai below Dirac, "Target D"). Cannot reach full Gallai |
| B | Uniform endpoint matroid on 3-connected critical graphs | — | **Refuted in general** by ED Thm 46 (cut obstruction at every connectivity). EMC (non-uniform) remains open |
| C | **Endpoint min-max (EMM)**: a half-set is realisable in n/2 paths iff it meets the local conditions and every cut inequality ED (1) | **Yes** | Unifies SP 14.1 (dense: cuts never bind), ED Prop 45 / Thm 46 (cut inequality necessary and tight), TVS (exact gluing), RE 13.1 and MR Cor 39 (Hall conditions), and JM-repair (Hoffman cuts). Under EMM, Gallai becomes a pure **cut-selection** statement |

## 5. Decision

(Filled in after the n = 8 test of EMM; see §6.)

## 6. Test of EMM

`tools/cut_test.py`, using the exact oracle `tools/realis.c`. For every connected even-order graph and every half-set M of Ev, the test compares realisability with (L) b(v) ≤ d(v), d(v) + b(v) ≤ 2k and (C) ED inequality (1) over all v and W ⊆ V − v.

| Order | Graphs | Half-sets | EMM failures | Unsound |
|---|---|---|---|---|
| 6 | 99 | 518 | **0** | 0 |
| 8 | (running) | | | |
