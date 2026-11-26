# Roadmap to unrestricted Gallai

This is the single source of truth for the proof architecture. Every node is a statement with a source, a status, an audit result and a formalization status. Update it after every finding.

**Status values:**

| Status | Meaning |
|---|---|
| `PROVED-EXT` | published external result |
| `CLAIMED` | proved in a collection manuscript, not yet audited |
| `AUDITED` | passed an adversarial audit (`research/audit/`) |
| `GAP` | the audit found a fixable gap |
| `ERROR` | the audit found a false step |
| `OPEN` | not proved |
| `CONJ` | conjecture with computational evidence |
| `REFUTED` | counterexample known |

**Verification values:**

| Value | Meaning |
|---|---|
| `lean` | formalized in `lean/` |
| `lean-ext` | the author's external Lean repository (not here) |
| `comp(n≤N)` | exhaustive computation in `tools/` |
| `—` | none |

## The formal target (2026-11-26, night)

**`Gallai.gallai_of_branching : (∀ j ≥ 3, BStmt j) → GallaiConjecture`** (lean/GallaiLean/Bridge.lean). No other hypotheses; Lovász's theorem is proved in the library. Standard axioms only.

`BStmt j` says: in every connected graph H of even order with at least 2j even vertices, for every two distinct even vertices y, w such that y has two even neighbours, some j-set R ⊆ Ev with w ∈ R and y ∉ R has Ev ∖ R realisable (`Desc H j y {w}`). `rooted_six_of_bstmt3 : BStmt 3 → (R) for every connected even-order graph with 6 even vertices`, which is T(6)-i / BP₅.

**Weaker single hypothesis (BranchBase.lean): `gallai_of_branchBase_three : (∀ k ≥ 3, BranchBase k) → GallaiConjecture`.** `BranchBase k`: in every connected even-order H with ≥ 2k even vertices, every even y that has two even neighbours, and every bridge at which leads to a leaf, lies in a realisable (e − k)-set (`Desc H k y ∅`). There is no prescribed removed vertex. `branchBase_of_bstmt` shows it is weaker than `BStmt`. Gqz~vw at y = 3 is an instance of `BranchBase 3`.

**Three even neighbours (FanBarrier.lean): `gallai_of_branchBase3 : (∀ k ≥ 3, BranchBase3 k) → GallaiConjecture`.** The case of exactly two even neighbours reduces by a rooted transfer (`branchBase_of_three`), so `BranchBase3` asks for descent keeping y only when y has ≥ 3 even neighbours.

**The flower move (Flower.lean; endpoint-structure §7).**
- `flower_decomp` and `hub_cycles`: at Fan's equality the hub's paths close into cycles, and a transversal path recombines them into one more path with b(s) = 2.
- `cocktail_passes_of_rt`: CP(m) passes the rooted test for every m ≥ 4, given `RainbowTransversal (m − 1)` (open; E16 finds no failure for m ≤ 10).
- `cocktail_passes_four`, `cocktail_passes_five`: unconditional.

**Route (H) verdict (endpoint-structure §7, connections §N follow-up 4, E15).**
- A stronger induction hypothesis cannot close `BranchBase3` through Fan moves.
- At n ≤ 8, oracle seeds (any realisable profile of G − e) win every even root of every connected graph except K8 − perfect matching.
- For CP(m) = K_{2m} − PM with m ≥ 4, no Fan transfer and no new path of < m − 1 held edges can be the last move (`cocktail_fan_barrier`, `cocktail_insertion_barrier`, Lean, no hypotheses).
- The missing ingredient is a spare-path move at Fan's equality: the flower, missing-move Prop 5.5.

**Everything now hinges on proving `BranchBase k` (equivalently, it suffices to prove `BStmt j`).** Lovász + Fan certificates cannot do it in general: Gqz~vw at y = 3 is an instance of `BStmt 3` with no certificate using ≤ 8 held edges (E13). So the missing-move lemma is the decisive target.

## Top-level chain

```
GALLAI (every connected G: p(G) ≤ ⌈n/2⌉)
 ⇔ [N1] rooted private-leaf test R: ∀ connected H, |H| = 2k, ∀ r: p(H + leaf at r) ≤ k
 ⇔ [N2] marked bound on 2-connected graphs ∧ three-end test on tight odd 2-connected graphs   (MR Thm 1)
 ⇔ [N3] pair of tests F₂ / F₃ on 2-connected graphs without a matching cut                       (MR Thms 7, 57, 59)
 ⇔ [N4] two rooted deletion tests on 3-connected J                                               (MR Thms 113, 114)
      (i)  z the unique even vertex, d(z) = d: J − z has ≤ (|J|−1)/2 paths with ≥ 2 ends at r ∈ N(z)
      (ii) z, r the only even vertices, adjacent: J − z has ≤ |J|/2 paths with ≥ 3 ends at r
 ⇐ [T(d)] test (i) at deletion degree d, together with test (ii) at deletion degree d, for every even d ≥ 4
```

## Node table

| Node | Statement | Source | Status | Verification |
|---|---|---|---|---|
| N1 | Gallai ⇔ R (doubling identity p(double) = 2p(H^r) − 1) | REC §1, SP §1 | **AUDITED** (A3) | **lean** (`gallai_iff_rootedTest`) |
| N2 | MR Thm 1 | MR §1–2 | **AUDITED** (A1); wording gaps G1–G4 | **lean** (`gallai_iff_tests`: Gallai ⇔ MarkedTwoConnTest ∧ ThreeEndsTest; MarkedSurgery/MarkedBlocks.lean). The bridge formula is not formalized and is not needed |
| N3 | MR Thms 7, 57, 59 | MR | **AUDITED** (A1); gaps G6–G9 (wording) | comp (bridge/diamond doubles: 210) |
| N4 | MR Thms 113, 114 | MR §18–19 | **AUDITED** (A2): no errors | **lean (partial)**: Thm 114 setup, Gallai ⇒ both tests, apex 3-connectivity, and the converse modulo Thm 59 and Thm 113 (`ThreeConnected.lean`) |
| T(4) | both tests at d = 4 | MR p.129 | **AUDITED** (A8); Botler–Sambinelli Thm 13 suffices | comp (exhaustive \|J\| ≤ 9) |
| T(6)-ii | three-end test, d = 6 | MR Thm 123 | **AUDITED** (A8) | comp (exhaustive \|J\| ≤ 10) |
| T(8)-ii | three-end test, d = 8 | MR Thm 128 (computer: Thm 124) | **AUDITED** (A8): **Thm 124 certificate independently replayed**. Conditional on Fan–Hou–Zhou (two seven-site shapes) and Chu–Fan–Zhou Lemma 2.1 (star lemma, unquoted) | comp |
| T(6)-i | two-end test, d = 6 (= floor for odd W with a leaf and 5 even vertices, MR Thm 144) | Nov 26 studies | **OPEN**, heavily reduced. **A6: no errors; shape-theorem banks independently re-derived; Thm 144 can be made Shaik-free (BS Thm 13 + Lemma 133).** Unreplayed inputs remain: Thm 135, Thm 137, Lemma 121, the INC trees, 6CL's 31,442 records, D10's tables | comp (n = 8 all instances) |
| T(8)-i | two-end test, d = 8 | MR Thm 130 (only root degree 2) | **OPEN** | — |
| T(≥10) | both tests | partial (hubs) | **OPEN** | — |
| U | a uniform-in-d mechanism closing T(d) for every d | this project: FD / EMC (`research/connections.md` B, C) | **CONJ**. **Descent steps 1 and 2 PROVED** for all even-order graphs (Lemma 3; `two_step_descent`). **Step 3 reduced in Lean** (`desc_three_of_unique`, `desc_three_reduction`, KStep.lean) to two base cases: y has ≥ 2 even neighbours, or y has no even neighbour and every edge at y is a bridge. Sound move systems in Lean: Fan schedules, the Fan calculus `FanCert` (`realisable_of_fanCert`). FanCert is not complete (6 failures at n = 6); see the Fan game (connections §R). **With path insertion the game is complete at n = 8** (connections §S); its first gap is the degree-six hub at n = 10 | **lean** (steps 1–2, step-3 reduction) |
| T(4)-i via descent | two-end test with 4 even vertices: every even r lies in a realisable half-set | `two_step_descent` with y = r | **PROVED** (Lovász + Fan only, no Botler–Sambinelli) | **lean** |
| EMC(e=4) | realisable pairs form a rank-2 matroid | every even vertex has ≥ 2 realisable partners (two-step) ⇒ the partner graph has min degree 2 on 4 vertices ⇒ C4, K4−e or K4 | **PROVED** | **lean** (`endpoint_matroid_four`) |
| BP_3 | floor bound for odd order with a pendant leaf and 3 even vertices | `rooted_four` | **PROVED** by Lovász + Fan (no Botler–Sambinelli) | **lean** |
| U | a uniform-in-d mechanism closing T(d) for every d | this project: FD / EMC (`research/connections.md` B, C) | **CONJ** | comp(n ≤ 6) |
| FD2 | second step of faithful descent: for every root r some Ev − {u, v} (u, v ≠ r) is realisable | endpoint-structure §5, Thm 28 (connections §P); in full: `two_step_descent` (EMCFour.lean, base branch) | **proved in full by `two_step_descent`** (lean, rebuilt and axiom-checked by this session). This session's Thm 28 proves it except for e = 4 with G[Ev] = K_3 + r; non-realisable pairs are E-twins (Thm 20/Cor 22); the step with a prescribed u (Cor 27) is proved unless G[Ev] is edgeless with private odd neighbourhoods | **lean** (Thm 20, Cor 22, pair step Thm 26, Fan certificates Thm 24, path step); comp (n ≤ 8) |
| U-Fan | uniform-in-d sufficient condition for (R): a semi-induced matching of size e/2 − 1 in G[Ev] avoiding r (Cor 25); in MR Thm 114(i) a condition on J[N(z)] alone | endpoint-structure Cor 25 | **CLAIMED** | **lean** (`realisable_of_fanSchedule`) |
| HUB4 | degree-four hubs: d(s) = 4, N(s) ⊆ Ev, ≤ 1 even vertex outside N[s] ⇒ (R) at s and at N(s) | `manuscripts/missing-move` Thm 2.2 (hub lemma 2.1: Lovász's spare path, two Fan receipts and one new path through s) | **PROVED** | **lean** (`Ach.hub_four`, `hub_four_ends`, `hub_four_rooted`; unconditional) |
| FG8 | the Fan game with path insertion (new paths of any length) wins every root of every connected graph of order 8 | missing-move Thm 3.1; E14 | **comp(n = 8)**, \|F\| ≤ 6. Pósa moves at the profile level (rotation, Fan's alternative) repair none of the §R losers. First loser of the extended game: A_{6,2} (n = 10), a degree-six hub one receipt short, where the receipt is forced by an edge count at Fan's equality (missing-move Prop 5.2) | comp |

## Side chains that also reach Gallai

| Node | Statement | Source | Status |
|---|---|---|---|
| S1 | Bonamy–Perrett floor for 2-connected odd graphs, plus N2's marked bound, implies Gallai | MR Thm 1 + semi-clique Thm 4 | CLAIMED |
| S2 | first failure: either a 2-connected odd floor witness, or failing hosts are 6-edge-connected with δ ≥ 6 | SP Thm 10.16, Cor 13.5 | **AUDITED** (A3) modulo JM; citation gaps G1 and G2 in §12 |
| S3 | odd semi-cliques: p = k + 1 exactly | OSB Thm 4 (Javadi–Miralaei) | **AUDITED modulo JM** (A4). **JM's proof has a substantive gap (Thm 8, Claim 12)**; JM verified computationally for k ≤ 7; repair in progress |
| S4 | dense: exact at δ ≥ (1/2+ε)n, large n | SP Thm 14.1 | CLAIMED |
| S5 | blocks with Δ ≤ 7 satisfy the floor | block-degree Thm 3 | **AUDITED + all enumerations independently replayed** (A5). Cited ≤ 5-contact lemmas re-proved exhaustively. JM needed only for k ≤ 3, which Liu–Chen covers. |

## External dependencies

| Result | Used by | Status |
|---|---|---|
| Lovász mixed theorem | everything | classical. **The ≤ 1 even vertex form is proved in Lean** (`lovasz_ends`, by an original induction from Fan's lemma; manuscript `manuscripts/lovasz-fan`) |
| **Javadi–Miralaei (Wu's conjecture)** | OSB Thm 4 / Thm 11; SP Thm 10.16 equality case; block-degree Thm 2 | **REPAIRED and AUDITED** (`manuscripts/jm-repair`; audit A10: no error, no substantive gap). New proof of JM Thm 8 under r ≤ 2t − 1, which covers both OSB uses (Thms 9 and 11). Corrected Thm 7 transfers. Wu's conjecture is proved, assuming Hilton 1984, Hoffman 1960 and Liu–Chen 2023 (Liu–Chen not re-checked). Corrigenda updated. |
| Fan addible-edge lemmas | six-even program; MR | **Both proved in Lean** (`fan_single`, `fan_grouped`; sorry-free). Lemma 3.4 also matches its published quotation (A7). |
| Fan–Hou–Zhou | T(4); MR p.129 | **matches** (A7): no triangle pair, and each block has Δ ≤ 3; ceiling conclusion |
| Chu–Fan–Zhou Lemma 2.4 | MR (≈5 places), even-degrees, SP | **RESOLVED** (`manuscripts/cfz-lemma`): the common-vertex form with \|V(P)\| + q ≤ 7 is proved, and every sum-7 use satisfies its hypothesis. The one finite ingredient is a 1,257-case six-contact lemma, which agrees with MR §6. The general form is unproved but not needed. |
| Shaik (Hexagon preprint, unrefereed) | MR Thm 144, Cor 106 | A7: Botler–Sambinelli replaces it at the Thm 144 r ∈ T step and in the zero-exception case of Cor 106. **The one-exception case of Cor 106 still needs Shaik**, so Thm 144 remains conditional. | **Being attacked** (jm-repair session, `manuscripts/bs-prescribed`): Botler–Sambinelli Thm 13 with a prescribed end (connections §L). At n = 8, Lovász–Fan certificates win every root whenever Δ(EV) ≤ 3 (E13).

**The MR equivalence spine (N2–N4) does not depend on JM** (A1, A2).
### Contingency if the Javadi–Miralaei repair fails

| Result | Effect |
|---|---|
| SP Thm 10.16, alternative 1 | "≥ h+1 missing edges" weakens to "≥ h, and exactly h only when the hole graph is JM-residual (h ≥ 6, not a linear forest, support ≥ h+2)" |
| OSB Thm 4 | the lower bound p ≥ k+1 is elementary; the upper bound loses only the residual family (k ≥ 6, ⌈(k+4)/2⌉ ≤ m ≤ k−1, sparse non-linear-forest H) and its m = k analogue |
| MR equivalence spine (N2–N4) | unaffected |
| block-degree Thm 3 | unaffected |



## Final assembly target (after the audits)

**Floor form of the two tests.** Using MR Thm 114 (audited) and the private-leaf trick:

- **Test (i) at degree d** is the floor bound for W = (J − z) plus one leaf at r. W has odd order and exactly d − 1 even vertices, namely N(z) − r.
- **Test (ii) at degree d** is the floor bound for (J − z) plus two leaves at r. This graph also has odd order and d − 1 even vertices.

So **Gallai ⇔ BP_t for every odd t** (restricted to the apex class), where:

> **BP_t:** connected, odd order, at least one pendant leaf, exactly t even vertices ⇒ p ≤ ⌊n/2⌋.

| t | Status | Source |
|---|---|---|
| 1 | proved | Lovász |
| 3 | proved; **now also in Lean** by Lovász + Fan (`rooted_four`) | Fan–Hou–Zhou / Botler–Sambinelli; `two_step_descent` |
| 5 | **open** | test (i) at d = 6, i.e. MR Thm 144, which is conditional on Shaik; test (ii) at d = 6 is closed (MR Thm 123) |
| 7 | **open** | test (i) at d = 8; test (ii) at d = 8 is closed (MR Thm 128, computer, audit A8) |
| ≥ 9 | **open** | — |

For t = 5, Botler–Sambinelli leaves only E-subgraphs that contain a bowtie or a block with a degree-4 vertex, i.e. dense E-subgraphs on five vertices.

**What a complete proof needs:** an argument for BP_t that is uniform in t, or an induction BP_t ⇒ BP_{t+2}.

Candidate uniform mechanisms (`research/connections.md`):

- the endpoint matroid conjecture (EMC); **proved for e = 4, and its first two descent steps are proved for every e** (connections §N);
- faithful descent (FD);
- a theorem on cliques of even vertices.

## Current strategy

1. **Robustness first.** Audit N1–N4, S2, S3 and S5. Fix every gap in the manuscripts. Formalize the elementary nodes (N1, the parity lemmas, the W(F,S) identity) in Lean.
2. **Uniform mechanism.** Test FD and EMC further: n = 8 exhaustive and random n = 10, 12. Then try to prove the single-descent lemma, which would give T(d) for all d. This is the only route found so far that does not grow with d.
3. **Close T(6)-i** using the shape reductions as a testbed for the uniform mechanism.



## Active workstreams (2026-11-26, evening)

**Direction from the project lead:** concept-level theorems, each formalized in Lean. Computation only as small sanity checks.

**Cloud sessions** (separate compute; each pushes to its own branch, which is then merged here):

| Session | Branch | Target |
|---|---|---|
| session_01FxXpVf7LprJAyrCeEgPQZp | `claude/lean-spine-113-114` | Lean: MR Thm 113 (separator; odd component case done) and Thm 114 |
| session_01FxXpVg1tRbERYwJkzvwvow | `claude/emc-four-even` | delivered KStep, bridge gluing, Thm 29 / Cor 30 and BranchBase (Lean). **Route (H) done** (endpoint-structure §7): two even neighbours reduce (`gallai_of_branchBase3`); oracle-seeded Fan game; last-edge barrier for CP(m), m ≥ 4 (Lean `FanBarrier.lean`); EMC at n = 8 complete |
| session_01FxXpVe2jUooDSPpWwsw7gq | `claude/two-even-lovasz` | delivered the Fan calculus, E-twins and the pair step. **Now:** the base case "y has ≥ 2 even neighbours" of three-step descent, which closes T(6)-i |
| session_01FxXpVhJQ8wYEAygbxxgUKY | `claude/lean-six-clique` | **done**: six-clique Thm 1 in Lean. Idle; it took no new assignment without the owner's go-ahead |
| session_01FxXpViBmJMBd6Z1TwXR2yw | `claude/jm-repair` | **done**: JM Thm 8 repair (16 pp.). Its own referee pass on §§5–8 is running. Idle otherwise; it took no new assignment without the owner's go-ahead |
| session_01FxXpVhzpjnfPb4S9qT66Vk | `claude/bs-prescribed` | **remove Shaik**: Botler–Sambinelli Thm 13 with a prescribed end, then the corrected MR Cor 106 one-exception case (connections §L) |
| session_01FxXpViByhUwk1GmmqirzRR | `claude/lean-d6-frontier` | Lean for d6-frontier: relay/carry, root hub, full hub, and the all-d versions (Thm 6.1) |
| session_01FxXpVhnjxm4QuHi67Kwvfz | `claude/missing-move` | **the move beyond Fan's inequality** (connections §R, E13). Lovász + Fan certificates are incomplete at n = 8 (full-vertex obstruction). Candidates: rotation at equality, a stronger induction hypothesis, certified joins. Target: a lemma with manuscript and Lean, which makes the n = 8 losers winnable |
| session_01FxXpVf7LprJAyrCeEgPQZp | `claude/lean-spine-113-114` | Lean: MR Thm 113 (separator) and Thm 114 (3-connected reduction) |
| session_01FxXpVg1tRbERYwJkzvwvow | `claude/emc-four-even` | conceptual proof and Lean of EMC for four even vertices (non-realisable pairs form parallel classes) |
| session_01FxXpVhJQ8wYEAygbxxgUKY | `claude/lean-six-clique` | Lean: six-clique Thm 1 via fan_grouped, plus a reusable insertion-schedule lemma |
| session_01FxXpVe2jUooDSPpWwsw7gq | `claude/two-even-lovasz` | Q6, two-even problem / second descent step: **done** (connections §P; `lean/GallaiLean/TwoEven.lean`) |
| session_01FxXpVg1tRbERYwJkzvwvow | `claude/emc-four-even` | **delivered** `two_step_descent`, EMC(e=4), `rooted_le_four`, and the write-up (merged). **Now:** general k-step infrastructure (transfer and lift with arbitrary W; the path induction reduces k-step descent to the base case; the one-even-neighbour case) |
| session_01FxXpVhJQ8wYEAygbxxgUKY | `claude/lean-six-clique` | Lean: six-clique Thm 1 via fan_grouped, plus a reusable insertion-schedule lemma. **Done**: `six_clique_prescribed_ends` is sorry-free with standard axioms; `Prog.sound` is the insertion-schedule lemma; `Ach.insert_even` is Lemma 3 |
| session_01FxXpVe2jUooDSPpWwsw7gq | `claude/two-even-lovasz` | redirected to the **third descent step**, since step 2 is proved; this would close T(6)-i |
| session_01FxXpViBmJMBd6Z1TwXR2yw | `claude/jm-repair` | conceptual repair of Javadi–Miralaei Thm 8 / Claim 12 |
| session_01FxXpVhnjxm4QuHi67Kwvfz | `claude/missing-move` | **delivered**: the missing move of the Fan game is path insertion funded by Lovász's spare path (hub lemma, degree-four hubs; Lean `MissingMove.lean`); completeness at n = 8; Pósa moves negative; the degree-six hub gap at n = 10 (manuscript `missing-move`, connections §S, E14) |

**Local agents:** all finished. They delivered MR Thm 1 (Lean), Pyber (Lean), the hypothesis-free EMCFour corollaries, and the d6-frontier manuscript.

## Work queue (next wave)

| # | Item | Purpose |
|---|---|---|
| Q1 | Shaik [25, Cor 1.2]: there is a **public Lean formalization**, github.com/shaikidris/gallai-two-exception (488 files, 79k lines, Lean v4.35.0-rc3). Its statement file `Challenge.lean` was inspected and is faithful: `ceiling_bound` is exactly Cor 1.2, with decompositions as genuine edge partitions into nonempty simple paths. A grep finds no sorry, axioms or IO. Building it here was **blocked by the session's permission policy** (third-party code). To verify: `lake exe cache get && lake build Solution`, then `#print axioms Gallai.Submission.ceiling_bound`. If clean, Cor 106 and Thm 144 become machine-verified. Fallback: prove the one-exception odd-order case directly. The gadget attempts (edge xx′; path x–y–x′) each lose one unit of budget (connections §L). | makes MR Thm 144 unconditional |
| Q2 | Close D = ∅ at d = 6: clique core B[U] = K6 with full exterior vertices (six-clique Thm 6 covers ≤ 5 core neighbours; false-twin-return covers some full cases) | the largest residual d = 6 shape |
| Q3 | EMC for structured classes: cones K1 ∨ H (arm-pairing reformulation) and thread graphs (all even vertices of degree 2). **Done for e = 4 in general (Thm 21).** Next: the third descent step for e = 6, i.e. Thm 19 with the second deleted vertex avoiding N(y) (connections §N) | provable special cases of the uniform conjecture |
| Q4 | Lean: Prop "critical ≠ forced" lower bound; the d = 4 test from Botler–Sambinelli as an explicit hypothesis | pair the manuscript propositions with formal proofs |
| Q5 | Audit SP §14 (dense exact theorem) | off the Gallai-critical path; lower priority |
| Q6 | **Two-even-vertex Lovász problem** (connections §O, §P): when does a graph with exactly two even vertices meet the parity bound |odd|/2? **Mostly done** (§P): exact dictionary with G^{Ev−{u,v}}; Fan descent; second step except twins; pair step; goal (b) except K_3 + r. Open: the two residual configurations of §P.4, and deeper FD steps with the Fan calculus | equivalent to the second faithful-descent step |

## Log

- 2026-11-26: collection pushed; orientation `STATUS.md`; tools built.
- FD and EMC hold on all critical graphs with n ≤ 6.
- CP refuted at n = 7.
- Audits A1–A6 launched.
- Lean project created (`lean/`).
- **Audits A1–A8 complete: no false step in any audited result.** Remaining items are wording fixes, citation fixes and absent finite data (see the corrigenda).
- Lean: N1 (`gallai_iff_rootedTest`), parity, the private-leaf formula, and the endpoint-structure Lemmas 1–4 are all formalized.
- Corrigenda document written (`manuscripts/corrigenda`).
- New manuscript draft `manuscripts/endpoint-structure`.
- **Lovász's theorem proved in Lean** (an original proof from Fan's lemma; `manuscripts/lovasz-fan`).
- **Two-step faithful descent proved in Lean** (cloud session). Consequences: the two-end test at d = 4 holds by Lovász + Fan alone, EMC holds for e = 4, and T(6)-i reduces to the third descent step.
- **CFZ Lemma 2.4 resolved.**
- 2026-11-26 (cloud session, branch `claude/emc-four-even`): **two-step faithful descent** (Thm 19) and **EMC for e = 4** (Thm 21), both from Lovász + Fan's transfers. Formalized in `lean/GallaiLean/EMCFour.lean` (no sorry). Corollary: BP_3 / T(4) without Fan–Hou–Zhou or Botler–Sambinelli. Next target: a third descent step with the second deleted vertex avoiding N(y) (connections §N).
- **MR Thm 1 in Lean** (local agent): `gallai_iff_tests`, with standard axioms only. Includes the cut-vertex step (all five cases), the leaf steps, and the pendant step (the only place the three-end test is used). Also `pathNumber_gt_of_low_degree` (Critical.lean).
- **TwoEven.lean merged** (cloud session two-even): Fan descent, Fan transfer, the second descent step for any pair a, b with a witness w (`realisable_evenSet_erase_pair`), **non-realisable pairs are E-twins** (`etwin_of_not_realisable`), and iterated Fan descent along Fan schedules (`realisable_of_fanSchedule`). The session is now on the third step, split three ways: G[Ev] = K6; some even vertex has ≥ 2 even non-neighbours; the complement of G[Ev] is a matching.
- **Six-clique Thm 1 in Lean** (`six_clique_prescribed_ends`, sorry-free, kernel `decide` for the finite core). Hypotheses: U is a 6-clique of even vertices, every other vertex is odd with exactly 5 neighbours in U. Conclusion: every 3-set T ⊆ U is realisable.
- **Pyber's theorem in Lean from Lovász + Fan** (`pyber`, `pyber_claim`, local agent). If every cycle meets an odd vertex, a set of ≤ ⌊e/2⌋ even vertices is realisable. Fan's 2005 theorem is not formalized: it needs a stronger inductive hypothesis and block decompositions.
- **KStep.lean** (emc-four session): general transfer, `desc_reduction` for every k, `desc_three_of_unique`, `desc_three_reduction`.
- **Thm 113 separator setup** (spine session): PathSurgery.lean, SmallBounds.lean, sides A and E, graft/cut surgery.
- 2026-11-26 (same session, follow-up): **k-step infrastructure** (`lean/GallaiLean/KStep.lean`, manuscript Lemma 24–Cor 27):
  - general transfer;
  - connected reduction of k-step descent to "y has an even neighbour" or "all edges at y are bridges";
  - the one-even-neighbour case of (k+1)-step descent from k-step descent;
  - **three-step descent at vertices with exactly one even neighbour**, hence test (i) at d = 6 at every r ∈ N(z) with exactly one neighbour in N(z).

  Three-step descent is reduced to: y has ≥ 2 even neighbours, or y is an all-bridge vertex with no even neighbour.
- Lean (cloud session, branch `claude/lean-six-clique`): **six-clique Theorem 1 formalized**
  (`six_clique_prescribed_ends`, `lean/GallaiLean/SixClique.lean`). It is sorry-free with
  standard axioms only, and the Section 4 bookkeeping is checked by kernel `decide`.
  - Reusable tools: the insertion-schedule lemma `Prog.sound` (finite transfer programs checked on
    a model and replayed on any graph), `Ach.grouped` / `Ach.addPath`, and Lemma 3
    (`Ach.insert_even`: insert an even graph by chordless cycles).
  - The audit's requested expansions (A6 F10: Lemma 2's chain step; F11: Cor 5's triple rectangle)
    are written out in the `SixClique.lean` docstring.
  - Not formalized: Cor 5 and Thm 6. `Prog` is the format for replaying Thm 6's certificate
    records once they are in the repository.
- 2026-11-26 (same session, follow-up 2): **bridge gluing and the reduction to the branching case**, proved and formalized without hypotheses (`lean/GallaiLean/Bridge.lean`; manuscript Lemma 28, Thm 29, Cor 30).
  - **`gallai_of_branching`: if B_k holds for every k ≥ 3, Gallai's conjecture holds.** B_k is k-step descent at even vertices with ≥ 2 even neighbours.
  - **`rooted_six_of_bstmt3`: B_3 implies (R) for six even vertices, i.e. T(6)-i.**
  - The all-bridges case is closed. The only open input is "y has ≥ 2 even neighbours" at each level.
  - **`gallai_of_branchBase : (∀ k, BranchBase k) → GallaiConjecture`** (`lean/GallaiLean/BranchBase.lean`). BranchBase k asks for descent keeping y, with no prescribed removed vertex, only at y with ≥ 2 even neighbours and no bridge to a vertex of degree ≥ 2. It is proved for k ≤ 2, so **full Gallai is now reduced to the single named statement BranchBase k for k ≥ 3**.
- **MR Thm 1 in Lean** (local agent): `gallai_iff_tests`, with standard axioms only. Includes the cut-vertex step (all five cases), the leaf steps, and the pendant step (the only place the three-end test is used). Also `pathNumber_gt_of_low_degree` (Critical.lean).
- **TwoEven.lean merged** (cloud session two-even): Fan descent, Fan transfer, the second descent step for any pair a, b with a witness w (`realisable_evenSet_erase_pair`), **non-realisable pairs are E-twins** (`etwin_of_not_realisable`), and iterated Fan descent along Fan schedules (`realisable_of_fanSchedule`). The session is now on the third step, split three ways: G[Ev] = K6; some even vertex has ≥ 2 even non-neighbours; the complement of G[Ev] is a matching.
- **Six-clique Thm 1 in Lean** (`six_clique_prescribed_ends`, sorry-free, kernel `decide` for the finite core). Hypotheses: U is a 6-clique of even vertices, every other vertex is odd with exactly 5 neighbours in U. Conclusion: every 3-set T ⊆ U is realisable.
- **Pyber's theorem in Lean from Lovász + Fan** (`pyber`, `pyber_claim`, local agent). If every cycle meets an odd vertex, a set of ≤ ⌊e/2⌋ even vertices is realisable. Fan's 2005 theorem is not formalized: it needs a stronger inductive hypothesis and block decompositions.
- **KStep.lean** (emc-four session): general transfer, `desc_reduction` for every k, `desc_three_of_unique`, `desc_three_reduction`.
- **Thm 113 separator setup** (spine session): PathSurgery.lean, SmallBounds.lean, sides A and E, graft/cut surgery.
- 2026-11-26 (cloud session `claude/emc-four-even`, route (H)): **stronger induction hypotheses tested; the last-edge barrier.**
  - Prescribed transfer (Lemma 51). The two-even-neighbour case reduces (Cor 52, Lean `gallai_of_branchBase3`), so the open base case is m ≥ 3 even neighbours.
  - Gqz~vw at root 3: certified from G − 31, where the pair {5, 7} is realisable, and from G − 01 with a new path.
  - Prescribed descent D^{(j)} does not propagate: branching raises j by m − 2, and j ≥ 2 is false at the critical level. The matroid-qualified form fails in 22 of 275 critical e = 6, m = 3 instances at n = 8.
  - Oracle-seeded Fan game (`tools/fan_oracle.py`, exact oracle `tools/realis.c`): with general seeds and one held edge it wins all even roots at n ≤ 8 except K8 − PM.
  - **Barrier theorem** (Lean `FanBarrier.lean`): Fan's condition forces b(u) + 2|N^ev(u)| + 2 ≤ 3|D|. For CP(m), m ≥ 4, every certificate ends with a new path of ≥ m − 1 edges; the flower attains this.
  - **EMC holds on all 1,082 connected critical graphs at n = 8**: 1,030 are uniform, including all 476 three-connected ones.
- 2026-11-26 (cloud session `claude/emc-four-even`, follow-up 5): **the flower move as a theorem** (Lean `Flower.lean`, no sorry, standard axioms).
  - At Fan's equality the receipts' paths close into cycles (`hub_cycles`), and a transversal recombines them (`flower_decomp`).
  - CP(m): Lovász, then m − 1 receipts, then Hamiltonian cycles by the edge count, then a transversal. **So the rooted test for CP(m) follows from the rainbow-transversal lemma**, which is proved for ≤ 4 cycles. That makes CP(4) (= missing-move Prop 5.5) and CP(5) unconditional.
  - The general case is endpoint-structure Question 66; E16 finds no failure for m ≤ 10.
- 2026-11-26 (cloud session `claude/emc-four-even`, follow-up 6): **rainbow transversals and receipt-or-flower.**
  - The literature does not cover our case (Chen–Li, Andersen, Gyárfás–Mhalla, Maamoun–Meyniel, Joos–Kim). The general lemma stays open; endpoint-structure Question 66 now has the exact known statements.
  - New evidence: the lemma holds also for 2-factorisations, and segment transversals are easy in practice.
  - **Receipt or flower** (endpoint-structure Thm 67; Lean `flower_decomp_rest`).
  - **B′ (n = 10, Q2) closes by hand**, by receipt or flower (Prop 68), giving (R) at every vertex.
  - A_{6,2}: the core roots follow from missing-move Prop 5.2 by symmetry.
- 2026-11-26 (cloud, `claude/two-even-lovasz`): second descent step. Descent = Lemma 4 on G − uw + Fan's lemma restoring uw. Non-realisable pairs are E-twins (Lean). Pair step via Fan's grouped lemma (Lean). Goal (b) proved except e = 4, G[Ev] = K_3 + r. Fan certificates (sound, Lean) give a d-uniform sufficient condition for (R) (semi-induced matchings in G[Ev]). Obstructions (O1)–(O3) and a cut-vertex gluing rule for two-even graphs. Prop 13's e = 4 proof shows (R) only, not a realisable 2-set; Thm 28 supplies the latter except K_3 + r.
- **Fan game (E13, connections §R):** Lovász seeds + Fan transfers win every root at n = 6. At n = 8, every losing graph has Δ(EV) ≥ 4, and all losers but one are non-critical, where splitting at the root suffices. **The critical loser is Gqz~vw** (K8 minus {03,12,23,34,56,67}, 4-connected) at root 3. This is the test case for the missing-move session.
- **JM repair delivered** (16 pp.); audits A9 (d6-frontier and the new descent sections) and A10 (JM repair) are running.
- **Gallai reduced to one family of base cases** (endpoint-structure Thm 29, Cor 30; emc-four session). B_k for all k ≥ 3 implies Gallai, where B_k is k-step descent at an even y with ≥ 2 even neighbours. B_3 is equivalent to T(6)-i. Gqz~vw shows that B_3 is not provable by Lovász + Fan certificates with ≤ 8 held edges.
- **`gallai_of_branching` in Lean** (emc-four session; Bridge.lean, about 2000 lines). Full Gallai follows from `∀ j ≥ 3, BStmt j`. Definitions checked faithful: `GallaiConjecture` is ⌈n/2⌉ for connected finite G, and `PathDecomp` is an exact partition into simple paths of positive length.
- **`gallai_of_branchBase_three` in Lean** (BranchBase.lean): Gallai follows from the single named hypothesis `∀ k ≥ 3, BranchBase k`, which is weaker than BStmt (no prescribed w; y has no bridge to a vertex of degree ≥ 2).
- **Audit A9** (d6-frontier and endpoint-structure §§5–6): **no error in any theorem or proof**. Every d6-frontier certificate was re-run with adversarial grouped donors; each bound is attained exactly in the worst case, with supply exceeding it by 1. Thm 29 / Cor 30 / BranchBase are sound and match Lean. 13 GAPs fixed in the text. One ERROR, in the endpoint-structure abstract, is now fixed. Thm 45 is redundant given Thm 19.
- **Path insertion (missing-move session; `manuscripts/missing-move`, MissingMove.lean).** A Lovász seed with an isolated hub leaves a spare path, and that path pays for a new path of ≥ 2 held edges (hub lemma `Ach.hub_four`, `hub_four_rooted`, Lean). It closes the five non-critical n = 8 losers and the critical Gqz~vw (independently verified). **Correction (independent re-check of all 50 kmax-4 losers with `6 np`):** 6 graphs still lose, **all critical**. They are Guv]}{ (K7 + leaf), Guv]z{, Guv]~{, Gut~~w, Gu^v~w, and Gr~v~w = K8 minus a perfect matching (K_{2,2,2,2}, 6-connected, every vertex a degree-6 hub). So the degree-six "one receipt short" obstruction already occurs at n = 8. A test of K_{2,2,2,2} with |F| ≤ 8 is running. Pósa rotations do not help.
- Relay.lean (d6-frontier Lemma 2.3, forward relay and carry) merged.
- **Audit A10: JM repair SOUND.** Every flagged point checked, with independent brute force (78,360 cases) and enumeration of Hoffman's condition (98 networks): 0 mismatches. The JM dependency is discharged; corrigenda updated.
- 2026-11-26 (cloud session, branch `claude/missing-move`): **the Fan game's missing move found.** It is path insertion (a new path of length ≥ 2 made of held edges), paid for by Lovász's spare path when G − F has an isolated vertex. It is not a move beyond Fan's inequality.
  - **Hub lemma** (`Ach.hub_four`) and **degree-four hubs** (`hub_four_ends`, `hub_four_rooted`, Lean, unconditional, standard axioms): if d(s) = 4, N(s) ⊆ Ev, and at most one even vertex lies outside N[s], then (R) holds at s and at N(s). This closes GsRvnk.
  - **With path insertion the game wins every root of every connected graph of order 8** (\|F\| ≤ 6; E14).
  - Rotation at equality and **Fan's alternative** (new lemma: either the transfer succeeds, or ≥ Σ_T b blank neighbours can each be activated) are sound but repair none of the losers (E14).
  - First gap of the extended game: A_{6,2} at n = 10, a degree-six hub one receipt short. The receipt sits at Fan's equality and is forced by an edge count (manuscript Prop 5.2). This is the d6 frontier's "short by one".
  - `tools/fan_game.py` gains the options `np`, `rotR`, `altR` and `hubs`. Manuscript `manuscripts/missing-move`; connections §S (and a correction note in §R).
- **n = 8 status after path insertion (reconciled).** With \|F\| ≤ 6 and `np`, 6 critical graphs lose (independent run). The missing-move session (E14, orbit runs, \|F\| ≤ 8) reports wins for five of them at \|F\| = 7–8: Gut~~w, Gu^v~w, Guv]}{, Guv]z{ at 7, and Guv]~{ at 8. **Independently confirmed** for Guv]}{ root 0 at \|F\| = 7: F = {01,02,03,04,15,56,57}, with the leaf 2 isolated, which supplies the spare path. **K8 − perfect matching is settled by hand** (missing-move Prop 5.5, **flower lemma**). Lovász on G − s and three Fan receipts give b(s) = 3. The fourth receipt fails at equality, which forces the three paths to close into three Hamiltonian cycles through s. Cutting one edge per cycle along a transversal path gives 4 paths with b(s) = 2. This is the first concrete **two-end move at Fan's equality**. It uses an edge count that the profile cannot see. Checked by hand here.
