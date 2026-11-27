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

## PIVOT (2026-11-27, later): EMM is false at n = 28, and characterising all realisable half-sets is NP-hard (Kotzig); synthesis §§12–13

EMM sufficiency work is **stopped**.

**Sessions, re-assigned 2026-11-27 02:25.** Sessions that finished their task do not take large follow-ups from a peer session, so new tasks go to fresh sessions.
- **lean-thm59** (session_01FxXpVfLDxpMYxUsRi7svQy): **DONE** at 81dbc63. `thm59 : Thm59Statement` and `gallai_iff_spineTests'` are proved, with standard axioms (audit A14: no gap in MR).
- **route-descent** (session_01FxXpViNYwgYUE2BTWtj3X9): **finished** at 60adf00.
  - Proved (paper and Lean): separation (pair and set forms), Fan's lemma with vertex sets, L1 (leaf trick), route_append, Gallai ⇐ RR (`gallai_of_routeRR`), min-T-join heredity.
  - Open items it leaves:
    - the L∞ residual (z at distance 3; 1,531 tests, 0 failures). L∞ would give RR1 for any single route of a min T-join, since routes are geodesics and the first edge lies in J.
    - L_N for 2+ pairs (owned by multi-sep);
    - S1 at distance 2;
    - RR for star forests.
  - **Audit A16: every result correct as stated** (Fan's lemma with vertex sets was executed on 115k transfers, and separation was run as an algorithm). Wording and evidence fixes were sent to the author.
  - Original brief: the main line, synthesis §17. It reduces TRC to an extension lemma by route deletion, with Lovász's odd theorem as the base case. Plan: falsification tests first, then the extension invariant, then the existential version, then banked special classes in a manuscript plus Lean. It replaces two-even's pairing-guided descent follow-up, which was never started.
- **dense-near-dirac** (session_01FxXpVhsyyw9pbAoqda1H6h): **finished** at 413233e.
  - **Unconditional:** Thm 1.1 (balanced return), Cors 1.2/1.3, and Prop 8.3 = A19 Prop P (the counting half of Problem 7.1 under (B1)).
  - **Under SH:** Thm 9.3 — Target D reduces to SH + Problem 9.4 (intermediate vertices).
  - **Open:** SH (re-derive SP 14.31/14.33 with weak sites), 9.4 and 7.2.
  - The session saw no concrete route to SH or 9.4.
  - Original brief: Target D, the exact Gallai bound below Dirac.
  - **Delivered:** the *balanced return theorem* (`manuscripts/near-dirac/`, 15 pp.). It returns a linear-size exceptional set X under a balance condition; it contains SP Thm 14.27, and its Corollary 1.2 is an exact class.
  - **Lean:** `NearDirac.lean` (two finite lemmas).
  - **Remaining for full Target D:** Problem 7.1 (two-sided removal) and Problem 7.2 (exceptional vertices of high degree). **AUDITED (A17): Theorem 1.1 correct.** All CKLOT hypotheses are verified and the constants are consistent; there are wording gaps (N10, N29, N30, N26, N36, N24, N32, N33) and one statement gap (N25, already fixed). The author is fixing the wording.
- **audit-a17**: DONE (7593f1a). Theorem 1.1 is sound; wording fixes were sent to near-dirac.
- **near-dirac §§8–9** (Problem 7.1 attempt):
  - Proved: the balancing lemma (Lemmas 8.1–8.2, Prop 8.3, in regimes (i) and (ii)).
  - Open regime: Problem 8.5, with |X| ≳ √D and an explicit |X|² error.
  - Theorem 9.3, assuming the explicit Scheduling Hypothesis SH: a failure sequence must contain intermediate vertices (new obstruction, Problem 9.4) or lie in the 8.5 regime.
  - What remains for Target D on this route: SH, 7.2, 8.5 and 9.4.
- **audit-a19**: DONE (dc79e9f).
  - Sound: Lemmas 8.1–8.2 and SH as stated.
  - Fixes: a GAP in Prop 8.3(i)'s proof (the conclusion survives) and a sign ERROR in Problem 8.5's identity.
  - **The auditor solved Problem 8.5** with Proposition P (a two-sided exact sweep). So, under SH, a near-regular failure sequence must contain intermediate vertices (Problem 9.4); alternative (b) of Thm 9.3 goes.
  - The fixes were sent to near-dirac and applied in 8535af5.
  - **Re-audit §R: Prop 8.3 (= Prop P) and Thm 9.3 are SOUND as stated**; only wording nits remain.
- **multi-sep** (session_01FxXpVgYWAz7871pVVEKwNF, branch `claude/multi-sep`, new): conjecture MSEP. Lovász decompositions of an all-odd F can separate any disjoint pairs at distance ≥ 3. MSEP would give Gallai whenever G[Ev] has a perfect matching with no edge in a triangle, which includes triangle-free Eulerian graphs with a perfect matching. Evidence: 2,892 instances, 0 failures. route-descent keeps L1 at distance 2 and RR.
- **emc-four**: the endpoint-prescription paper. It still has to make the B-proof the main proof of Thm 21 (citing `cs_all`) and make TRC the main open problem.
- **emm3-gadgets**: done. §6 (forcing gadgets, Thm 45: hardness at even degrees ≥ 4) is merged at 5771c65. TRC survives every gadget construction (connections §T.result-3).
- **spine-paper** (session_01FxXpVgukMvgum4ucV8zWfX, branch `claude/spine-paper`, new): a standalone, audited paper `manuscripts/spine/` presenting the machine-checked reduction (MR Thms 1, 7, 59, 113, 114) along the Lean proof, with audit A15.
- **stl** (session_01FxXpVdsDUXK6XVuG52iCDL, branch `claude/stl`, new): star-terminal Lovász decompositions ⇒ spine Test1 (synthesis §19). It looks for a Test2 analogue, runs exhaustive tests, and attempts a proof via Lovász's induction at the even vertex.
- **Queued, not assigned:** Lean for MR Thms 38/175 and Cor 39 (flowers). This is a banking task, not on the critical path.
- **Finished:** two-even, spine (113/114), missing-move, bs-prescribed, jm-repair, six-clique, lean-d6-frontier.

The main line is **existential descent** (FD / `BranchBase3`), now in its route-deletion form (synthesis §17).

## Architecture (2026-11-27, after the full archive pass): see `research/synthesis.md`

**Main line: the endpoint min-max programme (EMM).** Conjecture: a half-set of even vertices is realisable in n/2 paths iff it satisfies the cut inequality of even-degrees §12.4 for every vertex v and every W ⊆ V − v. It is **exact on every connected graph of order ≤ 8 and on n = 10 samples** (2,368 non-realisable half-sets, all cut-excluded). Gallai ⇐ EMM + **CS (cut selection)**, where CS is a pure cut/flow statement that the T-join lemma already settles for cones. Tracks:
- C1: manuscript and Lean framework. **Draft done**: `manuscripts/endpoint-min-max/` (10 pp.; scripts reproduce the evidence table). EMM has four equivalent forms, the most useful being the **arm form** e(v,Y) ≤ b(Y) + |δ_{G−v}(Y)|. **EMM does not formally imply EMC**: each vertex's inequalities define a matroid (Prop. 11 there), but the global cap is not submodular (1,063 graphs at n = 8). EMC holds for all 1,082 critical graphs at n = 8 anyway;
- C2: prove CS. **DONE: CS (indeed PS) holds for every connected graph of even order** (endpoint-min-max Thm 21). The proof:
  - Take the T-join J (T = Ev) of a spanning tree. F = G − J has all degrees odd, so the odd vertices of F^v are exactly v's J-neighbours (plus v if even).
  - At each v, choose J's transitions by a T-join pairing in F^v. J is a forest, so any transitions give paths pairing Ev.
  - Every bad split at v is paid by its own edge of δ_{F^v}(Y).
  - **EMM itself is false** (missing-move Thm 7.5, n = 12, saturated degree-2 vertices). The corrected EMM₃ needs δ ≥ 3.
  - The earlier Cor 22 (a conditional reduction of Gallai) is **removed**. Thm 21 now stands alone; its use in the descent route is synthesis §13.
  - Checked against enumeration on all n ≤ 8 and samples. Lean definitions: connections §U;
- C3: EMM in classes (e ≤ 4, cones, κ-connected with e ≤ 2κ, 2-separator gluing, dense);
- C4: EMM sufficiency through tight cuts.

The dense track D (close Cor 14.39) is deprioritised. The formal targets below (`gallai_of_branchBase3`) remain valid and are compatible with this programme.

## The formal target (2026-11-26, night)

**`Gallai.gallai_of_branching : (∀ j ≥ 3, BStmt j) → GallaiConjecture`** (lean/GallaiLean/Bridge.lean). No other hypotheses; Lovász's theorem is proved in the library. Standard axioms only.

`BStmt j` says: in every connected graph H of even order with at least 2j even vertices, for every two distinct even vertices y, w such that y has two even neighbours, some j-set R ⊆ Ev with w ∈ R and y ∉ R has Ev ∖ R realisable (`Desc H j y {w}`). `rooted_six_of_bstmt3 : BStmt 3 → (R) for every connected even-order graph with 6 even vertices`, which is T(6)-i / BP₅.

**Weaker single hypothesis (BranchBase.lean): `gallai_of_branchBase_three : (∀ k ≥ 3, BranchBase k) → GallaiConjecture`.** `BranchBase k`: in every connected even-order H with ≥ 2k even vertices, every even y that has two even neighbours, and every bridge at which leads to a leaf, lies in a realisable (e − k)-set (`Desc H k y ∅`). There is no prescribed removed vertex. `branchBase_of_bstmt` shows it is weaker than `BStmt`. Gqz~vw at y = 3 is an instance of `BranchBase 3`.

**Sharper still (FanBarrier.lean): `gallai_of_branchBase3 : (∀ k ≥ 3, BranchBase3 k) → GallaiConjecture`.** It suffices to treat even y with **three** even neighbours, because the two-neighbour case reduces (`desc_succ_of_transfer_two`).

**Barrier theorem (Lean, `cocktail_fan_barrier`).** For the cocktail party graph CP(m) = K_{2m} − perfect matching, m ≥ 4, every decomposition of CP(m) − ut has ≥ m paths, and > m if Fan's condition for a transfer towards u holds. So **no certificate whose last step is a Fan transfer or a new one-edge path proves Gallai for CP(m)**, whatever the seed or induction hypothesis. Any proof of `BranchBase3` must end with a different kind of move, such as path insertion or the flower recombination (missing-move Prop 5.5), at least on these graphs.

**Everything now hinges on proving `BranchBase3 k`.** Lovász + Fan certificates cannot do it in general: Gqz~vw at y = 3 is an instance of `BStmt 3` with no certificate using ≤ 8 held edges (E13). So the missing-move lemma is the decisive target.
**Three even neighbours (FanBarrier.lean): `gallai_of_branchBase3 : (∀ k ≥ 3, BranchBase3 k) → GallaiConjecture`.** The case of exactly two even neighbours reduces by a rooted transfer (`branchBase_of_three`), so `BranchBase3` asks for descent keeping y only when y has ≥ 3 even neighbours.

**Credit: CP(m) rooted test and the failure of Fan's test there are separating-pairs Thm 10.21** (explicit Walecki construction opened along Q = (t, 1, …, h)). The flower work below re-derives it by the receipt route. Question 66 is moot for CP(m). MR Thm 38 closes ≤ 7 cycles through a vertex without transversals.

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
| N3 | MR Thms 7, 57, 59 | MR | **AUDITED** (A1); gaps G6–G9 (wording); A14: no gap | **lean**: `thm59 : Thm59Statement` (Thm59*.lean, 1,933 lines); comp (bridge/diamond doubles: 210) |
| N4 | MR Thms 113, 114 | MR §18–19 | **AUDITED** (A2): no errors | **lean**: Thm 113 proved (`separatorStatement`); **Thm 114 proved unconditionally** (`gallai_iff_spineTests'`); comp (n ≤ 8) |
| T(4) | both tests at d = 4 | MR p.129 | **AUDITED** (A8); Botler–Sambinelli Thm 13 suffices | comp (exhaustive \|J\| ≤ 9) |
| T(6)-ii | three-end test, d = 6 | MR Thm 123 | **AUDITED** (A8) | comp (exhaustive \|J\| ≤ 10) |
| T(8)-ii | three-end test, d = 8 | MR Thm 128 (computer: Thm 124) | **AUDITED** (A8): **Thm 124 certificate independently replayed**. Conditional on Fan–Hou–Zhou (two seven-site shapes) and Chu–Fan–Zhou Lemma 2.1 (star lemma, unquoted) | comp |
| T(6)-i | two-end test, d = 6 (= floor for odd W with a leaf and 5 even vertices, MR Thm 144) | Nov 26 studies | **OPEN**, heavily reduced. **A6: no errors; shape-theorem banks independently re-derived.** **MR Thm 144 is now Shaik-free** (bs-prescribed: its ≤ 1-universal case is proved, Lean). Unreplayed inputs remain: Thm 135, Thm 137, Lemma 121, the INC trees, 6CL's 31,442 records, D10's tables | comp (n = 8 all instances); **lean** (≤ 1 universal: `five_even_local`/`five_even_bowtie`) |
| T(8)-i | two-end test, d = 8 | MR Thm 130 (only root degree 2) | **OPEN** | — |
| T(≥10) | both tests | partial (hubs) | **OPEN** | — |
| U | a uniform-in-d mechanism closing T(d) for every d | this project: FD / EMC (`research/connections.md` B, C) | **CONJ**. **Descent steps 1 and 2 PROVED** for all even-order graphs (Lemma 3; `two_step_descent`). **Step 3 reduced in Lean** (`desc_three_of_unique`, `desc_three_reduction`, KStep.lean) to two base cases: y has ≥ 2 even neighbours, or y has no even neighbour and every edge at y is a bridge. Sound move systems in Lean: Fan schedules, the Fan calculus `FanCert` (`realisable_of_fanCert`). FanCert is not complete (6 failures at n = 6); see the Fan game (connections §R). **With path insertion the game is complete at n = 8** (connections §S); its first gap is the degree-six hub at n = 10 | **lean** (steps 1–2, step-3 reduction) |
| T(8)-i | two-end test, d = 8 | MR Thm 130 (only root degree 2); d6-frontier Thm 6.1 (hub closures at roots adjacent to all other even vertices) | **OPEN** | **lean (partial)**: hub closures for every d (`root_hub_uniform`, `full_hub_uniform`, `full_hub_pendant_uniform`) |
| T(≥10) | both tests | partial (hubs; d6-frontier Thm 6.1) | **OPEN** | **lean (partial)**: the hub closures of Thm 6.1, uniform in d |
| U | a uniform-in-d mechanism closing T(d) for every d | this project: FD / EMC (`research/connections.md` B, C) | **CONJ**. **Descent steps 1 and 2 PROVED** for all even-order graphs (Lemma 3; `two_step_descent`). **Step 3 reduced in Lean** (`desc_three_of_unique`, `desc_three_reduction`, KStep.lean) to two base cases: y has ≥ 2 even neighbours, or y has no even neighbour and every edge at y is a bridge. Sound move systems in Lean: Fan schedules, the Fan calculus `FanCert` (`realisable_of_fanCert`). FanCert is not complete (6 failures at n = 6); see the Fan game (connections §R) | **lean** (steps 1–2, step-3 reduction) |
| T(4)-i via descent | two-end test with 4 even vertices: every even r lies in a realisable half-set | `two_step_descent` with y = r | **PROVED** (Lovász + Fan only, no Botler–Sambinelli) | **lean** |
| EMC(e=4) | realisable pairs form a rank-2 matroid | every even vertex has ≥ 2 realisable partners (two-step) ⇒ the partner graph has min degree 2 on 4 vertices ⇒ C4, K4−e or K4 | **PROVED** | **lean** (`endpoint_matroid_four`) |
| BP_3 | floor bound for odd order with a pendant leaf and 3 even vertices | `rooted_four` | **PROVED** by Lovász + Fan (no Botler–Sambinelli) | **lean** |
| U | a uniform-in-d mechanism closing T(d) for every d | this project: FD / EMC (`research/connections.md` B, C) | **CONJ** | comp(n ≤ 6) |
| FD2 | second step of faithful descent: for every root r some Ev − {u, v} (u, v ≠ r) is realisable | endpoint-structure §5, Thm 28 (connections §P); in full: `two_step_descent` (EMCFour.lean, base branch) | **proved in full by `two_step_descent`** (lean, rebuilt and axiom-checked by this session). This session's Thm 28 proves it except for e = 4 with G[Ev] = K_3 + r; non-realisable pairs are E-twins (Thm 20/Cor 22); the step with a prescribed u (Cor 27) is proved unless G[Ev] is edgeless with private odd neighbourhoods | **lean** (Thm 20, Cor 22, pair step Thm 26, Fan certificates Thm 24, path step); comp (n ≤ 8) |
| U-Fan | uniform-in-d sufficient condition for (R): a semi-induced matching of size e/2 − 1 in G[Ev] avoiding r (Cor 25); in MR Thm 114(i) a condition on J[N(z)] alone | endpoint-structure Cor 25 | **CLAIMED** | **lean** (`realisable_of_fanSchedule`) |
| HUB4 | degree-four hubs: d(s) = 4, N(s) ⊆ Ev, ≤ 1 even vertex outside N[s] ⇒ (R) at s and at N(s) | `manuscripts/missing-move` Thm 2.2 (hub lemma 2.1: Lovász's spare path, two Fan receipts and one new path through s) | **PROVED** | **lean** (`Ach.hub_four`, `hub_four_ends`, `hub_four_rooted`; unconditional) |
| HUBd | hubs of any degree: Σ_{N(s)} b ≥ 2d − 5 ⇒ the star costs one path; relays; two hubs share one path | missing-move Lemmas 6.1–6.5, Thm 6.4, Cor 6.6 | **PROVED** | **lean** (`Ach.hub_general`, `Ach.relays`, `Ach.relay_hub`, `Ach.two_hub`; profile level; the Lovász wrappers are paper only) |
| HS | hub-strategy conjecture: at a BranchBase3 root, star(y) + ≤ lb(y) + c edges wins the game | missing-move Conj 6.7, Prop 6.8; E14 addendum 3 | **comp(n = 8)** with c = 2; n = 10 sample needs **c ≥ 3** (Inv~|~zbw roots 7, 9), so c = 2 is false. Proved theorems cover 2757/9268 root orbits (n = 8), 0/108 (n = 10) | open |
| EMM+ | cut-feasible ⇔ realisable for p ≥ ⌈n/2⌉ (general profiles) | missing-move Def 7.3, Ex 7.4; E17 | **FALSE** (padding: n = 10, p = 5). It holds at n ≤ 7, at p = 4 for n = 8, and on the n = 8 sample | Lean: `CutOK`, `leaf_step` |
| EMM | half-set cut criterion (synthesis Architecture C) | missing-move **Thm 7.5**; E17 addendum | **FALSE at n = 12**: 12 counterexample graphs (gluing through a saturated degree-2 cut vertex), confirmed by `tools/cut_test.py`. Exact at n ≤ 8. Open repairs: Rem 7.6 | – |
| C4-tmpl | inductive template (delete an edge, adjust, re-insert by profile-level moves) | missing-move Prop 7.5, Rem 7.6 | **fails as stated**: stuck instances at n = 6, all at Fan's equality; needs an equality lemma | – |
| FG8 | the Fan game with path insertion (new paths of any length) wins every root of every connected graph of order 8 | missing-move Thm 3.1; E14 | **comp(n = 8)**, \|F\| ≤ 9 (9 needed for K8 − perfect matching). Pósa moves at the profile level (rotation, Fan's alternative) repair none of the §R losers. Degree-six hubs: the pure star is one receipt short at Fan's equality (missing-move §5: edge count, flower). A_{6,2} and B′ (n = 10) are closed by hand and by the receipt-or-flower count (Lemma 5.9); a random n = 10 sample is won with star + ≤ 3 | comp |

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
| Shaik (Hexagon preprint, unrefereed) | MR Thm 144, Cor 106, Thm 114 remark | **REMOVED, AUDITED (A11: sound)** (`manuscripts/bs-prescribed`, corrigenda §Shaik). Every use of Cor 106 in MR has ≤ 5 unmarked even vertices. That case is BP_5 with one universal vertex, now proved from Lovász + Fan alone: six of the seven cores by three local lemmas, which need no leaf; the bowtie by 11 certificates, which need a leaf at an odd support. **Lean** (`FiveEven.lean`, `FiveEvenCerts.lean`: `five_even_local`, `five_even_bowtie`; 131 kernel-checked certificates). The prescribed-end version of BS Thm 13 is **false** (counterexample family G_{t,t'} at every odd N ≥ 5; the x–y–x′ gadget fails on an order-9 bowtie instance). Open without Shaik: Cor 106 one-exception odd case with ≥ 7 unmarked even vertices, which MR does not use. |
| Shaik (Hexagon preprint, unrefereed) | MR Thm 144, Cor 106, Thm 114 remark | **REMOVED (no longer needed by MR)** (`manuscripts/bs-prescribed`, corrigenda §Shaik). Every use of Cor 106 in MR has ≤ 5 unmarked even vertices. That case is BP_5 with one universal vertex, now proved from Lovász + Fan alone: six of the seven cores by three local lemmas, which need no leaf; the bowtie by 11 certificates, which need a leaf at an odd support. **Lean** (`FiveEven.lean`, `FiveEvenCerts.lean`: end-to-end `five_even_floor` (connected, five even vertices, one universal vertex, leaf at an odd support ⇒ floor), via `five_even_local`, `five_even_bowtie` and `exists_uv`; 131 kernel-checked certificates). The prescribed-end version of BS Thm 13 is **false** (counterexample family G_{t,t'} at every odd N ≥ 5; the x–y–x′ gadget fails on an order-9 bowtie instance). Open without Shaik: Cor 106 one-exception odd case with ≥ 7 unmarked even vertices, which MR does not use. |

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
| 5 | **open** for ≥ 2 universal vertices (cores K0–K3); **proved for ≤ 1 universal vertex** (BS Thm 13; bs-prescribed Thm 1, Lovász + Fan, Lean) | test (i) at d = 6, i.e. MR Thm 144, now Shaik-free; test (ii) at d = 6 is closed (MR Thm 123) |
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
| session_01FxXpViBXRQG6c4V7bSYHsM | `claude/emm3-gadgets` | **forcing gadgets**: δ ≥ 3 blocks that simulate degree-2 behaviour (pass-through or double end). They either refute EMM₃ by gluing a below-budget core, or show by a structural lemma that no such gadget exists |
| session_01FxXpVf7LprJAyrCeEgPQZp | `claude/lean-spine-113-114` | Lean: MR Thm 113 (separator) and Thm 114 (3-connected reduction) |
| session_01FxXpVg1tRbERYwJkzvwvow | `claude/emc-four-even` | conceptual proof and Lean of EMC for four even vertices (non-realisable pairs form parallel classes) |
| session_01FxXpVhJQ8wYEAygbxxgUKY | `claude/lean-six-clique` | Lean: six-clique Thm 1 via fan_grouped, plus a reusable insertion-schedule lemma |
| session_01FxXpVe2jUooDSPpWwsw7gq | `claude/two-even-lovasz` | Q6, two-even problem / second descent step: **done** (connections §P; `lean/GallaiLean/TwoEven.lean`) |
| session_01FxXpVg1tRbERYwJkzvwvow | `claude/emc-four-even` | **delivered** `two_step_descent`, EMC(e=4), `rooted_le_four`, and the write-up (merged). **Now:** general k-step infrastructure (transfer and lift with arbitrary W; the path induction reduces k-step descent to the base case; the one-even-neighbour case) |
| session_01FxXpVhJQ8wYEAygbxxgUKY | `claude/lean-six-clique` | Lean: six-clique Thm 1 via fan_grouped, plus a reusable insertion-schedule lemma. **Done**: `six_clique_prescribed_ends` is sorry-free with standard axioms; `Prog.sound` is the insertion-schedule lemma; `Ach.insert_even` is Lemma 3 |
| session_01FxXpVe2jUooDSPpWwsw7gq | `claude/two-even-lovasz` | redirected to the **third descent step**, since step 2 is proved; this would close T(6)-i |
| session_01FxXpViBmJMBd6Z1TwXR2yw | `claude/jm-repair` | conceptual repair of Javadi–Miralaei Thm 8 / Claim 12 |
| session_01FxXpVhnjxm4QuHi67Kwvfz | `claude/missing-move` | **delivered**: the missing move of the Fan game is path insertion funded by Lovász's spare path (hub lemma, degree-four hubs; Lean `MissingMove.lean`); completeness at n = 8; Pósa moves negative (Fan's alternative in Lean); degree-six hubs and the resistant A_{6,2} at n = 10 (manuscript `missing-move`, connections §S, E14) |

**Local agents:** all finished. They delivered MR Thm 1 (Lean), Pyber (Lean), the hypothesis-free EMCFour corollaries, and the d6-frontier manuscript.

## Work queue (next wave)

| # | Item | Purpose |
|---|---|---|
| Q1 | ~~Shaik [25, Cor 1.2]~~ **Done** (bs-prescribed): the one-exception odd case of Cor 106 is proved where MR uses it (five unmarked even vertices); see the Shaik row. Building Shaik's Lean repository is no longer needed for MR. | makes MR Thm 144 unconditional |
| Q2 | Close D = ∅ at d = 6: clique core B[U] = K6 with full exterior vertices (six-clique Thm 6 covers ≤ 5 core neighbours; false-twin-return covers some full cases) | the largest residual d = 6 shape |
| Q3 | EMC for structured classes: cones K1 ∨ H (arm-pairing reformulation) and thread graphs (all even vertices of degree 2). **Done for e = 4 in general (Thm 21).** Next: the third descent step for e = 6, i.e. Thm 19 with the second deleted vertex avoiding N(y) (connections §N) | provable special cases of the uniform conjecture |
| Q4 | Lean: Prop "critical ≠ forced" lower bound; the d = 4 test from Botler–Sambinelli as an explicit hypothesis | pair the manuscript propositions with formal proofs |
| Q5 | Audit SP §14 (dense exact theorem) | off the Gallai-critical path; lower priority |
| Q6 | **Two-even-vertex Lovász problem** (connections §O, §P): when does a graph with exactly two even vertices meet the parity bound |odd|/2? **Mostly done** (§P): exact dictionary with G^{Ev−{u,v}}; Fan descent; second step except twins; pair step; goal (b) except K_3 + r. Open: the two residual configurations of §P.4, and deeper FD steps with the Fan calculus | equivalent to the second faithful-descent step |

## Log

- 2026-11-27 (cloud, `claude/emc-four-even`): **Lean: cut selection formalised.**
  - `cs_all` in `CutSelection.lean` (with `PairingLemma.lean`, 1,237 lines). No sorry; standard axioms; the full library builds.
  - It follows the second proof of Thm 21: the cut-form pairing lemma (by edge deletion) applied to one auxiliary graph B on V × V, plus T-join existence, the parity of B, the cut comparison and the CutOK algebra.

- 2026-11-27 (cloud, `claude/emc-four-even`, post-pivot): **endpoint-min-max rewritten as a paper on prescribed ends** (17 pp.). The paper now covers:
  - the cut inequality: necessary, with its four forms;
  - **cut selection** (Thm 21, unchanged numbering);
  - sufficiency at n ≤ 8 and in the dense range (Prop 29 with SP 14.1);
  - failure at n = 12 (missing-move Thm 7.5) and n = 28;
  - **Thm 27 (hardness; construction due to the project lead, with full proofs).** For connected **bridgeless** cubic H (essential 4-edge-connectivity is not needed), the gadget half-set of G(H) is cut-feasible and is realisable iff H is Hamiltonian. The proof uses Lemma 23: cuts of L(H) have size 2·(mixed vertices), so λ(L(H)) ≥ 4 iff H is bridgeless; and Prop 24: cut-feasible ⟺ λ(L(H)) ≥ 4. Then Prop 25 (realisation ⟺ Hamiltonian decomposition of L(H)), Kotzig 1957, and Garey–Johnson–Tarjan. So half-set realisability is NP-complete, even for cut-feasible half-sets with degrees in {2,4}.
  - Removed: all claims that Gallai reduces to EMM (Prop 9, Cor 22). EMM is now Question 4; EMC is Conjecture 10.
  - Script: `scripts/kotzig.py`.

- 2026-11-27 (cloud, `claude/emc-four-even`, track C2 completed): **cut selection is a theorem** (endpoint-min-max Thm 21, `scripts/construction.py`). Every connected even-order graph has an explicit good pairing; it comes from a spanning-tree T-join with transitions chosen by T-join pairings in F^v. (Its Gallai corollary was later removed; see the next entry.)
  - Also: the per-vertex matroids are now Thm 11.
  - Edmonds' intersection gives CS for any two vertices' conditions, but not for three (example in the remark).
  - The guarded-routes conjecture is superseded.

- 2026-11-27 (cloud, `claude/emc-four-even`, tracks C1/C2): `manuscripts/endpoint-min-max/`, with scripts `scripts/{evidence,cut_selection,certificates,caps}.py` and tools `cutfeas.c`, `capsub.c`.
  - EMM evidence re-run reproducibly: n = 6, 8 exhaustive (as in synthesis §6); n = 10 random seed 20261127, 250 graphs; 82 bottleneck graphs. 0 failures, 0 unsound.
  - Forms: (1) ⇔ demand ⇔ arm ⇔ arm-system (max-flow). For half-sets it is a cut condition in G^v (star at v complemented), with exact parity.
  - Cones: CS and the exact pairing criterion. Guarded route lemma ⇒ PS. Certified at every n ≤ 8, all trees ≤ 12, and samples.
  - Caps: per-vertex matroids; f not submodular; EMM ⇏ EMC formally; 4 critical n = 8 graphs are explained by neither single-vertex dominance nor submodular caps.
  - Caveat: "Gallai + EMM ⇒ CS" needs (R) ⇒ (R_s) (simple profiles; ES Cor. 6). It is not formal.

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
- 2026-11-26 (cloud session `claude/emc-four-even`, follow-up 7): **credit correction.**
  - CP(m) (all m) and the failure of Fan's test there are SP Thm 10.21. MR Thm 38 / Cor 39 already give ≤ 7-cycle openings with two ends at the hub.
  - Endpoint-structure §7, connections §N and this file now credit them. Our part is equality-forces-flower, receipt-or-flower, B′ (Prop 68) and the Lean files.
  - Rainbow-transversal work is stopped (pause requested).
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
  - **With path insertion the game wins every root of every connected graph of order 8** (\|F\| ≤ 9, which is attained by K8 − perfect matching; E14).
  - Rotation at equality and **Fan's alternative** (new lemma: either the transfer succeeds, or ≥ Σ_T b blank neighbours can each be activated; Lean `fan_alternative`) are sound but repair none of the losers (E14).
  - Degree-six hubs: a pure star is one receipt short at Fan's equality (the d6 frontier's "short by one"). By hand the rigid configuration is refuted by an edge count (A_{6,2}, Prop 5.2) or recombined as a flower (K8 − PM, Prop 5.5). The game instead holds more edges and inserts a longer path through the hub. Resistant case: A_{6,2} (n = 10), which loses at every root with a star plus ≤ 3 held edges.
  - `tools/fan_game.py` gains the options `np`, `rotR`, `altR` and `hubs`. Manuscript `manuscripts/missing-move`; connections §S (and a correction note in §R).
- **n = 8 status after path insertion (reconciled).** With \|F\| ≤ 6 and `np`, 6 critical graphs lose (independent run). The missing-move session (E14, orbit runs, \|F\| ≤ 8) reports wins for five of them at \|F\| = 7–8: Gut~~w, Gu^v~w, Guv]}{, Guv]z{ at 7, and Guv]~{ at 8. **Independently confirmed** for Guv]}{ root 0 at \|F\| = 7: F = {01,02,03,04,15,56,57}, with the leaf 2 isolated, which supplies the spare path. **K8 − perfect matching is settled by hand** (missing-move Prop 5.5, **flower lemma**). Lovász on G − s and three Fan receipts give b(s) = 3. The fourth receipt fails at equality, which forces the three paths to close into three Hamiltonian cycles through s. Cutting one edge per cycle along a transversal path gives 4 paths with b(s) = 2. This is the first concrete **two-end move at Fan's equality**. It uses an edge count that the profile cannot see. Checked by hand here.
- **FanBarrier.lean** (emc-four, route H). It proves `gallai_of_branchBase3`, so only y with ≥ 3 even neighbours remain, and the **barrier theorem** `cocktail_fan_barrier`: Fan moves on the last edge can never decompose CP(m) into m paths. Tools: an exact realisability oracle (`tools/realis.c`), an oracle-seeded Fan game, and an EMC sweep.
- d6-frontier in Lean: Thm 6.1(a), 6.1(b) at every deletion degree d, and Thm 5.2.
- 2026-11-26 (cloud, `claude/lean-d6-frontier`): **d6-frontier hub closures in Lean**, sorry-free, standard axioms, unconditional (Lovász is `lovaszStatement`). `Relay.lean`: Lemma 2.3 (`Ach.forwardRelay`, `Ach.carry`) and the hub counting (`Ach.receiveMany`, `Ach.giveAll`). `HubPhases.lean`: seeds and phases. `D6Frontier.lean`: **Thm 6.1 at every deletion degree d** (`root_hub_uniform`, `full_hub_uniform`, `full_hub_pendant_uniform`), Thm 5.2 (`full_hub_six`, `full_hub_six_pendant`), Thm 4.1(i) (`root_hub_six`). Formalization audit `research/audit/d6-frontier-lean-audit.md`: no error; two wording gaps fixed in the text (Thm 4.1(ii),(iii) need Q non-isolated; the d = 4 remark needs an odd neighbour of degree ≥ 3).
- **n = 8 is closed by the extended game**: Lovász + Fan + path insertion, \|F\| ≤ 9, every root of every connected graph. Independently confirmed on the two hardest instances (K7 + leaf at \|F\| = 7; K8 − PM at \|F\| = 9). The cocktail party graph needs the longest inserted path, consistent with `cocktail_insertion_barrier`. The next test bed is n = 10 (degree-6 hubs: A_{6,2} core roots resist).
- Lean (cloud session, branch `claude/lean-spine-113-114`): MR Thm 113 proved in full (`separatorStatement`, all three component cases); MR Thm 114 proved modulo Thm 59 (`gallai_iff_spineTests`); Gallai ⇒ both deletion tests and 3-connectivity of the parity apex proved with no hypothesis.
- 2026-11-26 (cloud, `claude/lean-d6-frontier`): **d6-frontier hub closures in Lean**, sorry-free, standard axioms, unconditional (Lovász is `lovaszStatement`). `Relay.lean`: Lemma 2.3 (`Ach.forwardRelay`, `Ach.carry`) and the hub counting (`Ach.receiveMany`, `Ach.giveAll`). `HubPhases.lean`: seeds and phases. `D6Frontier.lean`: **Thm 6.1 at every deletion degree d** (`root_hub_uniform`, `full_hub_uniform`, `full_hub_pendant_uniform`), Thm 5.2 (`full_hub_six`, `full_hub_six_pendant`), all of Thm 4.1 (`root_hub_six`, `root_hub_six_Q1`, `root_hub_six_Q2`; (ii), (iii) with the vertices of Q non-isolated). Formalization audit `research/audit/d6-frontier-lean-audit.md`: no error; two wording gaps fixed in the text (Thm 4.1(ii),(iii) need Q non-isolated; the d = 4 remark needs an odd neighbour of degree ≥ 3).
- 2026-11-26 (cloud, `claude/bs-prescribed`): **Shaik removed from MR.**
  - The prescribed-end version of BS Thm 13 is false: the family G_{t,t'} works at every odd N ≥ 5, and exact n = 7 gives 6 failures with e = 5. The x–y–x′ gadget fails on an order-9 bowtie instance with p = k.
  - Every Cor 106 use has ≤ 5 unmarked even vertices. **BP_5 with one universal vertex is proved** from Lovász + Fan: three local lemmas for 6 cores (no leaf needed), and 11 certificates for the bowtie (leaf at an odd support).
  - Lean `FiveEven.lean` and `FiveEvenCerts.lean`: 131 kernel-checked certificates, `five_even_local`, `five_even_bowtie`.
  - Corrigenda section added. The odd-order Fan game with a prescribed end is far from complete: 58 of 64 e = 5 losses at n = 7 are search failures (E14).
- **The critical Gqz~vw is closed in Lean** (`gqz_rooted_three`, standard axioms; definition checked faithful). It follows from the odd-neighbour hub lemma `hub_four_odd_rooted`: the rooted test at a degree-4 hub with one odd neighbour (missing-move session). `fan_game.py` also gains a profile-level flower move (option `flower`).
- Five-even floor end to end in Lean (`five_even_floor`, bs-prescribed).
- 2026-11-26 (missing-move, follow-up):
  - The five E13 losers are non-critical (split rule). 19 of the 47 `np`-losers at \|F\| ≤ 4 are critical, and all win with path insertion.
  - **Odd-neighbour hub** (`hub_four_odd_ends`, `hub_four_odd_rooted`) closes the critical Gqz~vw at root 3; `gqz_rooted_three` is checked by `decide`.
  - **Profile-level flower move** (manuscript Lemma 5.7, transversals for j ≤ 4): the game wins CP(4) and CP(5) with one star, attaining `cocktail_insertion_barrier`. It does not help on A_{6,2} or B′ (n = 10).
  - Base branch merged into `claude/missing-move`.
- **Flower move is a theorem** (Flower.lean, emc-four). `flower_decomp` is the general recombination. `hub_cycles`: at Fan's equality the paths close into cycles through the hub. CP(m) is reduced to a **rainbow-transversal lemma**, proved for ≤ 4 cycles, which gives `cocktail_passes_four` and `cocktail_passes_five` unconditionally (standard axioms; checked). It is open for m ≥ 6, with no failures for m ≤ 10 (E16). The emc-four session is now on the general rainbow lemma.
  - **Receipt or flower with a count** (missing-move Lemma 5.9, option `rf`) plus the orbit rule: A_{6,2}, B′, CP(4) and CP(5) win at every root with one star. A_{6,2} is closed at every root by hand (Prop 5.2 + symmetry; this corrects "core roots open"). First miss in a random n = 10 sample: Inv~|~zbw (roots 2, 3).
  - **Receipt or flower with a count** (missing-move Lemma 5.9, option `rf`) plus the orbit rule: A_{6,2}, B′, CP(4) and CP(5) win at every root with one star. A_{6,2} is closed at every root by hand (Prop 5.2 + symmetry; this corrects "core roots open"). The one miss in a random n = 10 sample, Inv~|~zbw (roots 2, 3, star + ≤ 2), wins with star + 3 via a second hub.
- **Audit A11 (bs-prescribed): SOUND.** Every use of MR Cor 106 (three citations, all in the proof of Thm 144, plus its second sentence on p. 120) has ≤ 5 unmarked even vertices and is covered. All 11 bowtie certificates were checked on all 93 labelled cases with an independent checker, and replayed on 240 random hosts. **The Shaik dependency is removed from every load-bearing use in MR.** Still conditional on Shaik and unused: Cor 106 in full generality (≥ 7 unmarked even vertices), and the MR §2.1 p. 8 remark on failing single marks. That remark is not on the spine, since MR Thm 1 is in Lean without it.
- **Uniform-in-degree hub lemmas (Lean, MissingMove.lean; standard axioms, checked).** `Ach.hub_general`: an isolated hub of degree d whose neighbours carry Σb ≥ 2d − 5 is re-inserted at the cost of one path. `Ach.two_hub` does the same for two hubs sharing a neighbour. A plain Lovász seed (b = 1 on N) meets the condition exactly when d ≤ 5. That is the degree-six obstruction in exact form, and it is what the flower or receipt-or-flower move must supply at d ≥ 6.
  - **Hubs of any degree** (missing-move §6, Lean `Ach.hub_general`, `Ach.relays`, `Ach.relay_hub`, `Ach.two_hub`; no sorry). Hub-strategy conjecture: holds at n = 8 with c = 2; needs c ≥ 3 at n = 10 (Inv~|~zbw). The proved theorems cover none of the n = 10 sample.
- **Audit A12 (missing-move; endpoint-structure §7): SOUND, no mathematical error.** The auditor's own solver reproduced the n = 8 completeness (|F| ≤ 9), Gqz~vw at |F| = 5 and K8 − PM at |F| = 9. Citation and wording fixes were applied. The missing `.log` files are gitignored; the load-bearing ones were regenerated.
  - **EMM template (track C4)**, missing-move §7: the general-profile cut criterion fails at n = 7 (linkage), which suggests EMM⁺ (p ≥ ⌈n/2⌉). Minimal-counterexample reductions are proved (leaf case in Lean). Single-edge and path-insertion moves get stuck exactly at Fan's equality.
  - **EMM is false at n = 12** (missing-move Thm 7.5): gluing a below-budget linkage failure through a vertex with b = d = 2. The budget version EMM⁺ also fails (padding, Ex 7.4). Splitting off is tested: cut-preserving splits exist on the stuck instances, but lifting paths needs a guarantee.
- **EMM is FALSE** (missing-move Thm 7.5; independently confirmed). In KsOeBW??G`?A (n = 12), saturated degree-2 vertices isolate a below-budget core carrying a 2-linkage obstruction. **Corrected target: EMM₃** (minimum degree ≥ 3, so no saturated vertices for simple profiles), which is what the least-counterexample setting (δ ≥ 6) needs. See synthesis §10.
- **EMM₃ is FALSE** (emm3-gadgets session; verified). A joined-forcing gadget of two K4 blocks glued to K_{4,4} gives n = 18 with δ = 3. The characterisation direction is closed (synthesis §14).
- Process incident: a checkpoint commit (328eb52) captured audit A13's in-progress merge, with conflict markers in endpoint-min-max.tex. A13 was notified to resolve it. A rule was added to research/WORKFLOW.md.
- **Audit A13: cut selection (endpoint-min-max Thm 21) SOUND**, as is the hardness section. **New conjecture TRC**: every transversal of a Thm-21 pairing is realisable. TRC implies Gallai and holds on all known EMM counterexamples (synthesis §15). Next step: try to refute it.
- **Cut selection in Lean: `cs_all`** (CutSelection.lean and PairingLemma.lean, 1,237 lines; standard axioms; definitions checked). For every connected even-order G there is a pairing of Ev all of whose transversals satisfy the cut inequality: `CutOK` is exactly b(W) + d(v) + b(v) ≤ |δ(W)| + 2p. The proof goes through the auxiliary graph B and is machine-checked independently of audit A13.
- **endpoint-min-max synced** (emc-four). Merged emm3-gadgets §6, which already fixes A13's ERROR (Remark 28 and open problem 1: EMM₃ is false, see §6). Added: the auxiliary-graph proof as the main proof of Thm 21, with the linked-transitions proof kept second; §4.4 with Conjecture TRC (constructible pairings; TRC ⇒ Gallai; Thm 21 is its necessary half); TRC as the main open problem; and Lean `cs_all` in Formalisation. 26 pp.
- **The spine is fully machine-checked (2026-11-27, 03:10).** `Gallai.gallai_iff_spineTests' : (GallaiConjecture ↔ SpineTests) ∧ (GallaiConjecture ↔ SpineTestsNMC)`, with no hypothesis and standard axioms; I verified it with `#print axioms` after the merge and a full build of 18,364 jobs.
  - **What it says.** Gallai's conjecture is equivalent to two deletion tests on **3-connected** graphs J, at a vertex z with J − z free of matching cuts. Here n = |V(J)| and the decompositions are of **J − z**:
    - (Test1) if z is the only even vertex of J, then for every neighbour r of z, J − z has a decomposition into ≤ (n−1)/2 paths with ≥ 2 ends at r;
    - (Test2) if z and its neighbour r are the only even vertices of J, then J − z has a decomposition into ≤ n/2 paths with ≥ 3 ends at r.
  - **Proof route.** Lovász's theorem, then MR Thm 113 (separators), then MR Thm 59 (blocks without matching cuts; cones; Lemma 6 by PMP surgery; private leaves; one Hall-defect lemma for §2.1), then MR Thm 114.
  - **Files.** Thm59Transfer, Thm59Hall, Thm59ClassC, Thm59Lemma6, Thm59Leaves, Thm59MatchingCut, Thm59; 1,933 lines.
  - **Audit.** A14 found no gap in MR and lists the formal deviations.
- **Separation theorem in Lean (2026-11-27, route-descent).** `Gallai.separation`: if G has at most one vertex of positive even degree and c, a are at distance ≥ 3, then some decomposition with ends ≡ degrees mod 2 has no path containing both c and a. `Gallai.lovasz_avoid` is the corresponding L1 at distance three.
  - **Lean:** Separation.lean and FanSupport.lean (Fan's lemma with vertex sets); sorry-free, standard axioms (verified).
  - **Status:** new strengthening of Lovász's theorem. Paper proof in route-descent.tex, with audit A16 requested. The manuscript's bibliography and build are still being fixed.
- **Spine paper (2026-11-27).** `manuscripts/spine/spine.tex`, 27 pp., builds clean. It is a standalone proof that Gallai is equivalent to the two deletion tests, following the Lean proof.
  - **Audit A15:** two independent referees found no mathematical error. One expository error and one GAP (the paper claimed to be self-contained while quoting Lovász and Hall) were fixed, along with the Lean-pointer mismatches.
  - **Lean names:** all 141 Lean names cited resolve (`SpineCheck.lean`), and 14 main declarations use standard axioms (`SpineAxioms.lean`).
- **Gallai ⇐ constrained Lovász decompositions, in Lean (2026-11-27, route-descent).** `Gallai.gallai_of_routeRR` and `gallai_of_routeRRExists` (RouteSystem.lean; standard axioms, verified). Gallai follows if every connected even-order graph has a routed pairing of Ev such that, for every transversal M, or for each even y some transversal containing y, the free graph H − routes has a decomposition satisfying all of:
  - at most one end at every vertex;
  - an end at every unmarked tail;
  - RR1/RR2 compatibility.
  - L1 (`lovasz_avoid_nonadj`) is the one-pair instance and is proved.
  - **Open:** the L∞ residual (z at distance 3), L_N for 2 pairs, and RR in general.
- **multi-sep interim (2026-11-27, 05:20; Lean merged at 7e05af7 after the 14dbc55 revert was undone, build green).**
  - **MSEP is not proved, and no counterexample is known.** The checks are all distance-3 perfect pairings of all 4,060 connected cubic graphs of order 16 (36M pairings), 8.26M random pairings at order 18, and random all-odd graphs to n = 20, 5-regular to n = 40.
  - **Stronger conjecture CSEP:** partition V into packed classes (a proper colouring of G²); some Lovász decomposition has every path rainbow.
  - **Proved in MultiSep.lean, standard axioms (verified):**
    - `lovasz_endEdge`: in an all-odd graph, any edge xu can be the terminal edge of the path ending at x;
    - `lovasz_endEdge_set`: the same, with a packed set met at most once;
    - leaf merge;
    - `caseII_lift`: CSEP reduces to graphs with one even vertex;
    - a certified Case I step;
    - sparse-class separation.
  - **Exact obstruction:** "L1 at the even vertex", i.e. prescribing uz as the terminal edge at a neighbour u of the even vertex z. It holds in about 3,300 tests, but the leaf trick does not apply.
- **Conjecture EE ("L1 at the even vertex"): partial results in Lean (multi-sep 5498405, MultiSepEE.lean; standard axioms, verified).** z is the only even vertex and u ∈ N(z). EE asks for a Lovász decomposition in which uz is the terminal edge at u.
  - `ee_noTriangle`: EE holds whenever uz lies in no triangle.
  - `ee_split` and `ee_triangle`: EE holds whenever deg u = 3, except when u's other two neighbours a, b are adjacent and have a common neighbour other than u.
  - `separation_sparse_set`: holds as well.
  - Audit A18 of the multi-sep manuscript found every result sound; only wording and count fixes were needed, and they are applied.
  - EE is the one-transition case of STL (synthesis §19). The remaining EE cases are uz in a triangle with deg u ≥ 5, and that one deg-3 configuration.
