# Reader notes: the deletion-degree-six rooted test (six even vertices)

These are a reader's notes on the Nov 26 research studies and technical notes, plus the related parts of marked-reduction (MR). They have not been verified independently.

**Abbreviations.**

| Short | Paper |
|---|---|
| MR | marked-reduction |
| RS | six-even-root-shapes |
| INC | six-even-incidence |
| 4EX | four-exterior-neighbors (Part IV, from p.23, is "Odd vertices of small exterior degree") |
| 5ODD | five-odd-neighbors |
| 6CL | six-clique-prescribed-ends |

**Notation.** U = the six even vertices; T = U − r; O = the odd vertices; C = B[U]; D = K6 − C; S(x) = N(x) ∩ U; e(x) = d_O(x). "2c" means two-connected; "3c" means J is three-connected.

## Target and reductions in force

**The target.** B is connected, |B| = 2k, with exactly six even vertices, and r ∈ U. We need at most k paths with at least two ends at r. Equivalently, the floor bound k holds for B with a private leaf at r.

The apex class comes from MR Thm 114(1): B = J − z, J is 3-connected, z is the unique even vertex, d(z) = 6. No matching cut may be assumed.

**Already closed or reduced:**

- The three-end test (ii) is closed at deletion degree ≤ 8 (MR Thms 123, 128). Only the two-end test (i) is open at degree 6.
- B[T] has at least two universal vertices and is not the book K2∨K3 (MR Lemma 133 and §19).
- **Thm 144.** It suffices to test roots with d(r) ≥ 8 and at least 3 neighbours in T. This is equivalent to the floor bound for connected odd-order graphs with a leaf and five even vertices. Its proof uses Shaik's unrefereed 2026 preprint; Botler–Sambinelli probably suffices instead.
- In a failure, δ(B) ≥ 5 and even vertices have degree ≥ 6 (MR Cor 138). 4EX Part IV Cor 2 (3c) strengthens this to δ(B) ≥ 6 and δ(B[O]) ≥ 4, with O nonempty.
- 4EX Prop 16: every even-order graph occurs as B[O], so no structure is forced on O.
- MR Props 139, 140, 142, 143, 149 and Cor 146 are further single-witness closures.

**RS shape theorem.** This holds for any connected host. If r has a core neighbour and the test fails, D is one of:

| D | Candidate roots |
|---|---|
| ∅ | any |
| K2 | any |
| P3 | the middle vertex only |
| K3 | a triangle vertex |
| C4 | a cycle vertex, whose cycle-neighbours are adjacent twins throughout B |

With r fixed this gives 66 patterns (396 labelled).

- **Isolated root.** Failure requires C − r ∈ {K5, K5 − e, K5 − P3}. It descends to a nonisolated failure with fewer edges, but the descent does not preserve 2-connectivity, minimum degree or the matching-cut condition.
- **C4 case.** The exterior T-profiles lie in {∅, abe, abcd, acde, bcde, abcde}.
- **Odd neighbours of even sites.** In apex failures, every even site has at least 3 odd neighbours, and a C-universal site has at least 5.
- **Pendant identity.** p2(A + xry, r) = 1 + p2(A, x).

## Closures, paper by paper

**INC Thm 1 (connected B).**
- If r has a core neighbour and some odd x has |S(x)| ∈ {1, 2}, the root passes.
- If every |S(x)| ≤ 2, every root passes.
- So in a failure, |S(x)| ∈ {0, 3, 4, 5, 6}.

**4EX Part IV.** Single-witness closures:
- every odd vertex of degree ≤ 5;
- e ≤ 3;
- degree-2 vertices;
- degree-4 roots and degree-4 vertices of T;
- an odd vertex with exactly one T-neighbour (Prop 9, 2c).

Props 7, 8, 12, 13, 15 and §5.1 need 3c.

**4EX Part II.** (|S|, e) = (3, 4) is closed unless B[N] ∈ {∅, 2K2}, which leaves 4 of 64 masks.

**4EX Part III.** (|S|, e) = (5, 4) is closed unless B[N] = K4 and the clique-boundary conditions hold.

**4EX Part I.** A 4-regular odd-induced graph is closed at all orders.

**5ODD.**
- Degree 7 with five odd neighbours: 60 of 64 masks.
- Degree 11 with bridge witnesses.
- Independent P4-anchor triples.
- Clique ports with ≥ 119 exterior neighbours.
- The paper says "arbitrary five-neighbor instances remain open."

**6CL.**
- Thm 1: U = K6 and each odd vertex sees exactly 5 core vertices. Then any prescribed triple of core sites gets doubled.
- Thm 6: U = K6 and each odd vertex sees at most 5. Then every r passes.
- **So D = ∅ is closed unless some exterior vertex is full (sees all six).**

**degree-ten-marked-root.** A C-universal root with exactly five odd neighbours passes. So a C-universal root in a failure has at least 7 odd neighbours and degree at least 12.

**false-twin-return.** A lift for false-twin classes. The full-contact problem is stated as open.

**Twin results (C4 pattern).**
- adjacent-twin-insertion closes C4 with degree-6 twins.
- degree-eight-twins is partial at degree 8.
- four-class-twins is an example family on which the local procedures fail but p is still small.

**Structured large families** (short-faithful, two-exterior-contacts, ordered-even-clique, star-deletion): mostly subsumed at six sites.

No closure is a near-miss bound: "m/2 + 3" is exactly k.

## What a failure must look like (synthesis)

Every odd vertex is "bad": e ≥ 4 and one of the following.

| (|S|, e) | Extra condition |
|---|---|
| (3, 4) | B[N] ∈ {∅, 2K2} |
| (5, 4) | B[N] = K4 surviving the boundary conditions |
| (4, 5) | no witnesses |
| (6, 5) | no bridge witness |
| (0, ≥ 7) | — |
| (any, ≥ 6) | — |

Some odd vertex must have e ≥ 5.

## Open

- D = ∅ with full exterior vertices.
- D ∈ {K2, P3, K3}: no shape-specific results.
- C4 with twins of degree ≥ 8 (beyond the partial result) or ≥ 10.
- Generic exterior degree ≥ 5.
- Higher deletion degrees (8, 10, …) of the two-end test.
- The three-end test beyond deletion degree 8, apart from special cases.

**Gap between pieces.** The 3c-dependent closures do not apply to RS's merely connected descent; the route through Thm 144 avoids this.

## Code status

**None of the code is in the collection.** Referenced but absent:

- RS: `verify.sh`, the Lean model, JSON banks, a 13,452-input checker.
- INC: two computations and a Lean certificate.
- 4EX: `four-prefix.py`, `catalogue.cpp`, the `checks/*` directories, Lean for Props 8 and 13.
- 5ODD: the scripts listed in its §6 review. That review replayed the supplied banks but did not regenerate them.
- 6CL: Lean covers only the odd-type portion; the full proper-neighbourhood case (31,442 classes) rests on two executable enumerations.
- degree-ten-marked-root: `referee/verify.sh`.
- degree-eight-twins: `check.py` with unit-propagation clause proofs.
- adjacent-twin-insertion: Lean `PortDeficit`.
- two-exterior-contacts: `certificates.json`.

## Inconsistencies

1. INC's "open" circulant family is already covered by 6CL Thm 1, and the two papers don't cite each other.
2. INC's "separate argument" for separating clique edges is not in the collection.
3. Several results are redundant with later ones: 5ODD §4.3 versus 6CL Thm 6, and two-exterior-contacts versus INC Thm 1(2).
4. 4EX contains superseded drafts and three different results each numbered "Theorem 1".
