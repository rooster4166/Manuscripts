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

## 5. Decision: Architecture C, the endpoint min-max programme

**Conjecture EMM (endpoint min-max).** Let G be connected of even order n = 2k. Let M be a half-set of its even vertices, with simple profile b (1 on odd vertices, 2 on M, 0 on the other even vertices). Then b is realised by a partition into k paths **if and only if** for every vertex v and every W ⊆ V − v,

  b(W) ≤ |δ(W)| + 2k − d(v) − b(v)                (ED, inequality (1))

The local conditions b(v) ≤ d(v) and d(v) + b(v) ≤ 2k hold automatically for simple profiles.

Necessity is ED §12.4: each path through v gives each of its ends in W a private edge of δ(W). Sufficiency is the conjecture. Evidence (§6): exact at every connected graph of order ≤ 8, and on samples at order 10, with **2,368 non-realisable half-sets, every one cut-excluded, and no exceptions**.

**Why this is the right architecture.**

1. **It is parameter-free.** There is no degree, no held-edge cap and no n0.
2. **It unifies the portfolio:**
   - SP Thm 14.1 is the dense case, where cuts never bind and only local conditions remain;
   - ED Prop 45 / Thm 46 give the necessary side and its sharpness;
   - TVS Thm 7 (exact gluing records) is a two-vertex cut computation;
   - RE Thm 13.1 and MR Cor 39 are Hall, that is cut, conditions at one vertex;
   - JM-repair's extension lemma is exactly a Hoffman cut theorem;
   - our hub, flower and barrier results are supply-versus-cut computations at a vertex.
3. **It explains EMC.** The cut inequalities are upper bounds |M ∩ X| ≤ f(X) on how many marks a set may contain. If the cap function is submodular, the realisable half-sets are the bases of the induced matroid. (Checked by the emc-four session: **the global cap is not submodular** in 1,063 of 10,893 graphs at n = 8. Each per-vertex family F_v is a matroid basis family, but F = ∩ F_v need not be a matroid: it fails in 48 non-critical graphs. All 1,082 critical graphs at n = 8 do have a matroid F. So EMM ⇒ EMC is not formal; see endpoint-min-max Question 12.) Uniformity fails exactly when some cut caps a shore, which is what ED Thm 46 shows.
4. **It splits Gallai into a hard analytic half and a combinatorial half.** Gallai ⇐ EMM + **(CS) cut selection**: every connected even-order G and every even r have a half-set M ∋ r meeting all inequalities (1). (Correction, from the emc-four session: the converse "Gallai + EMM ⇒ CS" is *not* formal. (R) may produce a non-simple profile at r, so what holds is CS ⇐ (R_s) + necessity, where R_s is the simple-profile rooted test.) CS is a pure cut/flow statement. **For cones (a universal vertex) CS follows from the classical T-join pairing lemma**: x = ±1 on marked/unmarked even vertices is unit-flow routable in G − apex.

**What it does not do.** EMM's sufficiency is a min-max theorem for path decompositions, and it is at least as hard as Gallai. The gain is that the difficulty is now a single structural statement with a natural inductive proof template:
- induction on |E|;
- deleting an edge and adjusting the profile so that the cut conditions persist;
- re-inserting the edge by Fan, hub or flower moves, whose failure must exhibit a violated cut (a tight-set, uncrossing argument).

Every local engine of the archive is a candidate move, and the cut conditions are the invariant that says which move applies.

**Plan.**

| Track | Work | Lean |
|---|---|---|
| C1 | Manuscript `manuscripts/endpoint-min-max`: statement, evidence, the dictionary in point 2 above, and consequences (EMC explanation; Gallai ⇐ EMM + CS) | `CutFeasible`; necessity of (1); `gallai_of_emm_cs` |
| C2 | Prove **CS** unconditionally: T-join and flow arguments, starting from the cone case | yes |
| C3 | Prove EMM in classes: e ≤ 4 (two-step descent); cones/apex graphs; κ-connected with e ≤ 2κ (EMM predicts *every* half-set is realisable); 2-separator gluing (TVS); dense (SP 14.1) | per class |
| C4 | Attack EMM's sufficiency: the minimal counterexample to EMM and its tight cuts | — |
| D | Bank "exact Gallai below Dirac" (close Cor 14.39) | **Deprioritised**: parameterised, and it does not lead to full Gallai |
| Spine | Finish MR Thm 59 (N3), giving a full Lean spine | yes |

## 6. Test of EMM

`tools/cut_test.py`, using the exact oracle `tools/realis.c`. For every connected even-order graph and every half-set M of Ev, the test compares realisability with (L) b(v) ≤ d(v), d(v) + b(v) ≤ 2k and (C) ED inequality (1) over all v and W ⊆ V − v.

| Order | Graphs | Half-sets | EMM failures | Unsound |
|---|---|---|---|---|
| 6 | 99 | 518 | **0** | 0 |
| 8 | 10,893 (all connected, e ≥ 2) | 101,714 (2,100 non-realisable) | **0** | 0 |
| 10, random sample (G(10,p), p = .3–.8, plus CP(5) and Inv~\|~zbw) | 246 | 4,724 (44 non-realisable) | **0** | 0 |
| ≤ 10, bottleneck families (cliques joined by 1–3 edges, theta graphs, cones over path unions, 2-sums) | 86 | 2,340 (206 non-realisable) | **0** | 0 |

"Unsound" counts realisable half-sets that violate (1); it must be 0, since (1) is necessary. The order-12 bottleneck instances were skipped because the exact oracle enumerates whole families and is too slow there.

## 7. Literature check (2026-11-27)

Two web searches for characterisations of path decompositions with prescribed end counts, by cut conditions or otherwise, found nothing of this kind. EMM appears to be new, but a careful literature section is still needed in the manuscript. Related classical results:

- Lovász's path partition theorem (one end at each odd vertex, at most two at each even vertex).
- **The Lovász–Cherkassky theorem.** In an inner-Eulerian graph, the maximum number of edge-disjoint T-paths equals ½ Σ_t λ(t, T − t). This is the closest min-max theorem with a cut-condition structure, and a natural model for proving EMM's sufficiency.
- Multiflow cut-condition theorems ("when the cut condition is enough", for example for series-parallel networks), as models for the gluing and uncrossing steps.

## 8. Refinement: EMM⁺ for general profiles (missing-move session, E17)

The cut criterion was extended to every profile b with b ≤ d, b ≡ d (mod 2) and Σb = 2p, with k replaced by p.

- **It fails below the Gallai budget.** At n = 7 there is one failure, at p = 2: FqJBo, a 2-linkage obstruction. At n = 8 there are 17 failures with p ≤ 3.
- **It holds at and above the budget.** That is every profile at n ≤ 7, every p = 4 profile at n = 8, and all p on a random n = 8 sample.

The refined conjecture is **EMM⁺**: for connected G and p ≥ ⌈n/2⌉, a profile is realisable iff it is cut-feasible. The half-set EMM is the case p = n/2.

**Reductions proved** (missing-move Lemma 7.4; Lean `leaf_step`). Leaves at unsaturated neighbours and some degree-2 configurations can be removed from a minimal counterexample to EMM⁺.

**The inductive template.** It closes most small instances. The stuck instances at n = 6 all have a cut-feasible move that lacks only its guarantee: a transfer at Fan's equality, or a two-end concatenation. **The missing ingredient is an equality lemma: at Fan's equality, either the move succeeds or a tight cut appears.** This is the same equality phenomenon as the flower move (§3), now located inside the min-max framework.

## 9. Tracks C1/C2, first results (emc-four session, `manuscripts/endpoint-min-max`, 11 pp.)

- **Equivalent forms of (1)** (Lemma 1): the demand form, the arm form, and arm systems by max-flow. For half-sets, (1) at v is a single-commodity cut condition in G^v, which is G with v's star complemented.
- **Dense case** (Prop 21): if δ ≥ (n + r − 1)/2, the local conditions imply (1) for every profile b ≤ r. This is the cut-theoretic content of SP 14.1.
- **CS for cones** (Thm 15, proved): M is cut-feasible iff its marked and unmarked even vertices pair up by edge-disjoint paths of G − apex. CS then follows from the T-join lemma.
- **PS (pairing selection)**, stronger than CS: some pairing of Ev has *all* of its transversals cut-feasible. **The guarded route lemma (Thm 17, proved)** gives PS from edge-disjoint routes pairing Ev with "guards" at busy vertices. **Certificates exist for every connected graph of order ≤ 8** (9,848 via Hamiltonian paths, 996 via other linkages, 49 via guarded routes). So **CS holds at n ≤ 8 by a proof that never uses realisability.**
- **Open: Conjecture GR.** Every connected graph has a guarded route system. GR ⇒ PS ⇒ CS.

## 10. EMM is false; the corrected target (2026-11-27)

**Refutation** (missing-move Thm 7.5; independently confirmed with `tools/cut_test.py`): KsOeBW??G`?A (n = 12) with M = {3, 4, 8, 9, 10} is cut-feasible but not realisable. Twelve such graphs of order 12 are known.

- **Mechanism.** A vertex with b = d is saturated, so no path passes through it. Saturated vertices cut the graph into pieces, and a piece can sit *below its own budget*, where 2-linkage obstructions are invisible to cuts (the EMM⁺ failures at p ≤ 3, n = 7, 8). Padding with leaves also refutes EMM⁺ above the budget.
- **For simple profiles (b ≤ 2), a saturated vertex has degree ≤ 2.** This counterexample mechanism therefore needs vertices of degree ≤ 2.

**Corrected target, EMM₃.** EMM restricted to connected graphs of minimum degree ≥ 3, where simple profiles have no saturated vertices.

- It is what the Gallai application needs. In SP's main alternative (Thm 10.16(2)), a least failure of (R) has δ ≥ 5 (≥ 6 after Thm 12.28). The other alternative, a smaller odd-order floor witness, needs the same statement one below budget, so the decomposition at saturated vertices must still be addressed for it.
- All known counterexamples have δ ≤ 2. The exhaustive n ≤ 8 data contain no δ ≥ 3 failure, because they contain no failure at all.

**Consequence for the programme.** An inductive proof of EMM₃ passes through graphs with low-degree vertices, so the induction needs a corrected general statement. Its form:
1. decompose at saturated vertices;
2. give each piece its own budget;
3. add conditions for pieces below their budget.

The last item is a *linkage* condition, beyond cuts; compare the two-paths theorem of Seymour, Shiloach and Thomassen. That makes EMM₃ a genuinely harder target than it looked. CS remains valid and useful: it is a statement about cut-feasibility only.

## 11. Cut selection is a theorem, pending audit (endpoint-min-max Thm 21)

**Thm 21.** Every connected graph of even order has a *good pairing*: a pairing of Ev all of whose transversal half-sets satisfy every cut inequality (1). Hence CS, and even PS, holds unconditionally.

**Construction.**
1. Take a forest T-join J of Ev and the free graph F = G − J.
2. At each vertex v, pair the odd vertices of F^v (F with v's edges deleted and v joined to its non-neighbours) by edge-disjoint paths, using the T-join lemma.
3. Use these pairings as the transitions of J at v.
4. Follow the transitions. Since J is a forest, the result is a set of paths pairing Ev. Lemma "linked transitions" charges every end to a distinct cut edge.

Audit A13 is running.

**Status of the reduction.** "EMM ⇒ Gallai" (Cor 22) is vacuous, since EMM is false. The live question is the exact corrected statement:
- Gallai ⇐ EMM₃ + CS needs SP's odd alternative handled separately.
- Better: Gallai ⇐ **EMM_ns** (EMM for half-sets with no marked vertex of degree 2), provided the cut-selection construction can avoid marking degree-2 vertices. Under simple profiles, marked degree-2 vertices are exactly the saturated separators.

The emc-four session is settling this. The emm3-gadgets session is testing whether EMM₃ or EMM_ns fails via forcing gadgets.

## 12. The all-half-sets trap: EMM is false at n = 28, and no polynomial characterisation exists (project lead, 2026-11-27; verified)

**Counterexample.**
1. Let P be the Petersen graph and G* = L(P) (15 vertices, 4-regular, 4-edge-connected). Delete a vertex w* with neighbours u₁…u₄; this leaves H_R on 14 vertices with 26 edges.
2. On L = {l₁…l₁₄}, take the path l₁ l₅ l₆ … l₁₄ l₂ and the edge l₃l₄. Add the cross edges l_i u_i for i ≤ 4. The result G_bad has n = 28 and m = 42, is 2-connected, and every vertex is even.
3. Take S = L.

**Why S fails.** It is cut-feasible: every slack equals 24, and an exhaustive check over the only risky W (those with |W ∩ L| ≥ 13) finds no violation. But it is not realisable. b|_R = 0 and |δ(R)| = 4 force two edge-disjoint Hamiltonian paths of H_R, and so a Hamiltonian decomposition of L(P). L(P) has 160 Hamiltonian cycles, and none has a Hamiltonian complement (`manuscripts/endpoint-min-max/scripts/petersen_counterexample.py`, which runs in 3 s).

**Hardness.** Replace P by any essentially 4-edge-connected cubic graph H. By Kotzig, L(H) is Hamiltonian-decomposable iff H is Hamiltonian. So realisability of the half-set L is NP-hard, while cut-feasibility holds and is checkable in polynomial time (the max-flow form of endpoint-min-max Lemma 1). **No polynomially checkable condition characterises all realisable half-sets unless P = NP.**

The construction uses saturated degree-2 vertices, the same mechanism as at n = 12. A forcing-gadget version would very likely carry the hardness to δ ≥ 3, so EMM₃ is not a viable target either.

**Why Gallai is unharmed.** S = L starves R: 14 even vertices, no ends, 4 boundary edges. The rooted test asks only for *some* realisable half-set containing r. Placing marks inside R removes the Hamiltonicity requirement at once. **Characterisation is the wrong problem; existence is the right one.**

## 13. Pivot (2026-11-27)

**Stop.** All proof and Lean work on EMM sufficiency, in every variant.

**Keep.**
- **Bank as theorems.** One manuscript on endpoint prescriptions: the cut inequalities are necessary (ED §12.4), always simultaneously satisfiable (Thm 21, after audit A13), sufficient at n ≤ 8, false at n = 12 and n = 28, and NP-hard to characterise (Kotzig reduction, credited to the project lead). Also hardness for δ ≥ 3, if the gadgets exist.
- **Spine.** MR Thm 59.

**Main line: existential descent** (back to FD / `BranchBase3`, the formal target). Descend from Ev (realisable by Lemma 2) to a half-set containing r, choosing which marks to drop. Existence statements escape the hardness. The new tools are:
- the good pairings of Thm 21, as a guide: drop one vertex per pair and never starve a region;
- the hub, flower and path-insertion moves, at the equality cases.

The first test is **pairing-guided descent**: for the Thm 21 pairing, can one always descend from Ev to some transversal, choosing within pairs, keeping every intermediate set realisable? Check this exactly at n ≤ 8.

**Bank in parallel.** Target D, exact Gallai below Dirac: return the o(n) exceptional set of SP Cor 14.39 using near-half-mixed-vertices and absorption. It is a major unconditional theorem, but parameterised.

**Addendum (emc-four report, 2026-11-27).**
- Thm 21 passed the author session's own adversarial review: about 50k graphs of orders 8–12, with no gap found. Audit A13, which is independent of the author, is running.
- **Evidence caveat.** At n ≤ 8, and in the random n = 10 sample, *every* half-set of every δ ≥ 3 graph is realisable (19,422 of 19,422 at n = 8). So the small-order evidence for EMM₃ was vacuous: cuts never bind there. The only informative δ ≥ 3 data are the two-blob and bottleneck families (282 cut-excluded half-sets, 0 failures).
- The conditional reduction "EMM₃ at δ ≥ 5 + Thm 21 ⇒ every Gallai failure is an odd SP 10.16(1) witness" is correct as an implication. It is moot, given §12: EMM₃ is expected to fail via gadgets.

## 14. EMM₃ is false as well (emm3-gadgets session, 2026-11-27; verified)

The gadget D is two K4 blocks plus vertices p and q, with ports p and b₀. It is **joined-forcing**: every realisation joins its two ports through a single segment. The host is G = D + K_{4,4} + {s p, s b₀}, with n = 18, m = 36, **minimum degree 3** and edge-connectivity 2. The half-set M = V(K_{4,4}) is cut-feasible, by three implementations and the max-flow form. It is not realisable, by the gluing argument; D's forcing property was checked by the oracle and by enumerating all 16 Hamiltonian decompositions of D′. Verification: `manuscripts/endpoint-min-max/scripts/emm3_counterexample.py` (9 s).

**Conclusion.** Cut conditions do not characterise realisable half-sets at any minimum degree tested. With §12, realisability of a prescribed half-set is NP-hard; a forcing-gadget version of the Kotzig reduction should give hardness at δ ≥ 3, which the gadgets session is writing up. The characterisation direction is closed. The existential-descent pivot of §13 stands.

**Addendum (verified).** EMM fails in **every connectivity class** (`scripts/emm_connectivity.py`). The graphs G_r have minimum degree and edge-connectivity 2r and vertex-connectivity 3, with a cut-feasible, non-realisable half-set:
- G₂: n = 20, δ = λ = 4;
- G₃: n = 42, δ = λ = 6.

No hypothesis of the form "δ ≥ c" or "λ ≥ c" rescues the cut characterisation. In particular, it cannot rescue it at the least counterexample of (R), where δ ≥ 6 and λ ≥ 6.

## 15. Audit A13, and the transversal conjecture TRC (2026-11-27)

**A13 verdict: Theorem 21 (cut selection) is SOUND**, in both versions and in the auxiliary-graph proof. The hardness section (§5: Lemma 23, Props 24–25, Thm 27) is sound. One ERROR is flagged: Remark 28 still calls EMM₃ open, and the emc-four session is fixing it. A13 reproduced every count independently, with about 113k constructions and no failure.

**The key finding (A13).** Not every *good* pairing has only realisable transversals. In KsOeBW??G`?A, the good pairing {03, 18, 45, 69, 7 10} has the counterexample as a transversal. But on all 12 order-12 counterexamples, **every transversal of every pairing the Thm 21 construction can produce is realisable**, and the order-28 starving half-set L is never such a transversal.

**Why.** Thm 21 pairings run along *edge-disjoint routes* (paths of a T-join), so a cut of size c is crossed by at most c routes. A transversal therefore cannot starve a region behind a small cut. For S = L in G_bad to be a transversal, 14 routes would have to cross a 4-edge cut.

**Conjecture TRC (transversal realisability).** For every connected graph G of even order, every pairing P produced by the Thm 21 construction (forest T-join J, edge-disjoint pairings of the odd vertices of each F^v), and every transversal M of P, the half-set M is realisable in n/2 paths.

- **TRC ⇒ Gallai**: take the transversal containing r.
- Its necessary half (cut-feasibility of every transversal) is Thm 21.
- It is not refuted by the NP-hardness constructions, which use starving half-sets.

TRC is trivially true at n ≤ 8, where every cut-feasible half-set is realisable. Informative tests are the counterexample families (orders 12, 18, 20, 28, and G_r) and larger random graphs.

**Next.** First try to refute TRC (the emm3-gadgets session, the natural adversary). If it survives, attack its single descent step: removing one vertex of a pair, guided by the route structure.

## 16. Gadget section written; hardness at even degrees ≥ 4; TRC versus gadgets (emm3-gadgets session, 2026-11-27)

- **Manuscript.** endpoint-min-max §6, "Minimum degree three and beyond: forcing gadgets", follows the hardness section. It contains:
  - the restriction and closing lemmas (Lemmas 29, 31);
  - Hamiltonian realisations and K_{2r} blocks (Lemmas 33, 34);
  - the cycle multigraph M_r and the gadgets D_r (Lemma 36, Prop 38);
  - arms across a cut and substitution (Lemmas 39, 40);
  - Thm 41 (G₁₈, δ = 3), Thm 42 (G_r, δ = λ = 2r) and Thm 45.

  Remark 28 and the open problems are updated, so EMM₃ is no longer listed as open. All proofs are oracle-free.
- **Thm 45 (new).** Replace the saturated tail of the Kotzig graph G(H) by a clique S of N marked vertices joined to u₁…u₄. The resulting G′(H) is 4-edge-connected, with all degrees even and ≥ 4. The half-set S is cut-feasible, and it is realisable iff H is Hamiltonian. So **NP-completeness holds at δ ≥ 4 and λ ≥ 4**, as §12 predicted. G′(Petersen) has n = 28.
- **Smallest gadget.** No two-leaf forcing gadget has order ≤ 9 (exhaustive, 1.46 × 10⁸ profiles at order 9). D₂ (order 10) is smallest. The first 4-regular graphs with a forced transition have order 11.
- **TRC.**
  - None of the failing half-sets is a transversal of a Thm 21 pairing. They starve the gadget, and edge-disjoint routes allow only |δ(D_r)| = 2r crossing pairs.
  - On G₁₈ itself, the Thm 21 pairings tested have no pair crossing δ(D₂). So every transversal puts 4 marks into D₂, and all 2,560 transversals of 10 distinct pairings are realisable (`tools/realis_wide.c`, `trc_probe.py`).
  - A gadget attack on TRC needs a *balanced* forcing gadget, with about half its even vertices marked. None exists at order ≤ 9.

## 17. Route deletion: TRC reduces to one extension lemma (2026-11-27)

The Theorem 21 class is closed under deleting a route, and the base case is Lovász's theorem. TRC, and with it Gallai, therefore comes down to a single extension step. Each step below is elementary and is written out in full.

**Setting.** (G, J, P, R) is a *Thm-21 system*:
- G is a graph whose components all have even order;
- J is a forest T-join for T = Ev(G), and F = G − J;
- R = {R_p : p ∈ P} decomposes J into edge-disjoint paths pairing Ev;
- at every v, the transitions of R (its passages, plus the end edge if v ∈ Ev) are joined by pairwise edge-disjoint paths of F^v. This is the hypothesis of Lemma linked; Theorem 21 produces such systems on every connected G.

**(U) Upward closure.** If S is realisable and x ∈ Ev ∖ S, then S + x is realisable. Since b(x) = 0, x is interior to some path; split that path at x. Hence TRC is equivalent to "every S ⊆ Ev meeting every pair of P is realisable", and the realisable sets form an up-set.

**(H) Heredity.** Let p = {a, c} and G' = G − E(R_p). Parities change only at a and c, so Ev(G') = Ev − {a, c}. J' = J − E(R_p) is a forest T-join for Ev(G'), and F' = F. For every v, N_{G'}(v) = N_G(v) minus v's R_p-neighbours, so F'^v = F^v + {vw : w an R_p-neighbour of v} ⊇ F^v. The transitions at v in G' are a subset of those in G, and their old linking paths still lie in F'^v. Linking paths do not leave a component: a path can pass through v only once, and F-edges stay inside components. So (G', J', P − p, R − R_p) is again a Thm-21 system, applied componentwise. Every component of G' has even order, because pairs lie within components.

**(B) Base.** If P = ∅, all degrees are odd, and by Lovász's theorem G decomposes into n/2 paths. Each vertex is then an end of exactly one path. This is the profile b_∅.

**(E) Extension.** Let M be a transversal with a ∈ M and c ∉ M. Suppose D' realises M − a in G'. In G', a and c are odd, each the end of exactly one path, Q_a and Q_c. If V(Q_c) ∩ V(R_p) = {c}, then Q_c ∪ R_p is a path with ends a and the far end of Q_c. Replacing Q_c by it realises M in G: a now has 2 ends, c has 0, and the path count is unchanged. If Q_c = Q_a, the condition fails automatically.

**Reduction.** TRC holds if, for every Thm-21 system, every transversal M and some pair p (the order of deletion is free), the inductive realisation D' of G' can be chosen with V(Q_c) ∩ V(R_p) = {c}. The whole difficulty is this **extension lemma**. It is the classical Lovász obstruction, now localised to one route and one end-path. The induction hypothesis must be strengthened so that it hands down end-paths avoiding a prescribed route. Choosing that strengthening is the research problem.

**Existential form (enough for Gallai).** We only need one transversal containing r. At every pair not containing r, either end may be extended: Q_c ∪ R_p, which marks a, or Q_a ∪ R_p, which marks c. Only r's own pair is forced. So the existential induction fails at a pair only if *both* end-paths meet the route.

**Assigned** to the route-descent session (ROADMAP). Its order of work:
1. falsification on the counterexample families;
2. measure the extension step;
3. strengthen the invariant;
4. compare with the existential version;
5. bank the special classes (single-edge routes, star-forest J, linkages) as a manuscript plus Lean.

## 18. Minimum T-joins remove the extension problem; Gallai reduces to a constrained Lovász theorem (route-descent, E20, connections §V)

**Finding.**
- With **minimum** T-joins, the extension step of §17 never failed: about 210,000 queries over orders 10–12, plus G₁₈. Moreover, all routes can be appended at once, which gives a route-respecting realisation (RR).
- With spanning-tree T-joins, 4–5% of extension queries fail. The failures are almost all trivial: c has degree 2 and the route passes through its other neighbour.
- TRC itself has no counterexample in about 160,000 transversals. These include the order-12 counterexamples, G₁₈, G_bad (n = 28) and G₂.

**Why minimality is the right invariant.**
- A minimum T-join is a forest, so Thm 21 applies to it.
- Every subpath of a route is a geodesic: replacing it by a shorter path gives a smaller T-join. So routes are induced paths, and the trivial obstruction cannot occur.
- **Minimality is inherited by route deletion.** If K′ were a smaller T′-join of G − E(R_p), then K′ ∪ E(R_p) would be a smaller T-join of G. Here T′ = T − {a, c}, and K′ is edge-disjoint from R_p.
- A matching that is a T-join is minimum, since every vertex of T needs degree at least 1 in J.

**The reduction (checked).** A route-respecting realisation of M is the same thing as a Lovász decomposition D of F = G − J, in which every vertex is the end of exactly one path, such that:
- (RR1) the D-path at each unmarked end c_p meets R_p only in c_p;
- (RR2) if a D-path has two unmarked ends c_p and c_q, then R_p and R_q are vertex-disjoint.

Appending each route at its unmarked end then gives every marked a_p two ends, every c_p none, and every odd vertex one. So

> **Conjecture RR.** For every Thm-21 system on a minimum T-join, and every transversal M, F has a Lovász decomposition with (RR1) and (RR2).

RR ⇒ TRC on minimum T-joins ⇒ Gallai. **Gallai is thereby reduced to a statement about decompositions of graphs with all degrees odd**, Lovász's own setting. RR\* (one D serving all M) is false.

**Special cases.**
- **L1:** the D-path at c avoids one non-neighbour a. 70,978 pairs, no failure. L1 is proved at dist(c, a) ≥ 3 by the separation theorem: Lovász's induction plus the observation that Fan's lemma keeps vertex sets.
- **L∞:** the D-path at c lies in N[c]. 19,040 out of 19,040.
- **L_N:** J is a perfect matching of G[Ev]; every route is one edge. 3,732 instances, no failure.

**L_N would give Gallai for every graph whose even vertices induce a subgraph with a perfect matching.** Such a graph automatically has even order. The class includes all Eulerian graphs with a perfect matching. As far as we know it is a new Gallai class; known classes (Pyber, Fan, Botler–Sambinelli) need G[Ev] to be sparse.

**Priorities.**
1. Prove L1 at distance 2, then L∞; L∞ ⇒ L1.
2. Prove L_N, which gives a new Gallai class.
3. Prove RR, which gives full Gallai.

The single-vertex statements L1 and L∞ come first. They are Lovász's theorem with one protected vertex, so Lovász's induction (Lovasz.lean, cases I–III) and Fan's vertex-set-preserving lemma are the tools.

**Literature check (2026-11-27).**
- Gallai's conjecture is open for Eulerian graphs in general. It is known for Δ ≤ 4 (Favaron–Kouider) and Δ ≤ 5 (Bonamy–Perrett, arXiv 1609.06257). The best general-type Eulerian bound found is p(G) ≤ 3n/5, for Eulerian graphs whose triangles are pairwise at distance ≥ 3 (Chu–Wang, arXiv 2510.12806, Oct 2025).
- No source was found on Lovász decompositions with avoidance constraints (L1, L∞, L_N, RR), nor on Gallai for "G[Ev] has a perfect matching".
- So L_N, which would give Gallai for every Eulerian graph with a perfect matching, would be a significant new result. This was a web search, not a full survey.

**Update (route-descent, 01e9f89; verified).**
- **L1 is proved in full** by the leaf trick: attach a leaf ℓ at c, so that c is the only even vertex and dist(ℓ, a) ≥ 3, then apply separation. In Lean this is `lovasz_avoid_nonadj` / `lovasz_avoid_set` (standard axioms).
- `realisable_two_even_adj` does one route-descent step end to end, and `PathDecomp.route_append` is the extension step.
- By the same trick, L_N with m pairs is equivalent to separating pendant leaves ℓ_i from the a_i in a graph whose m even vertices carry pendant leaves.
- So a leaf-tolerant MSEP would give **Gallai whenever G[Ev] has a perfect matching**, with no triangle condition; this includes every Eulerian graph with a perfect matching.
- L1 alone gives no new realisability class, since the first pair of any Fan schedule is already free.
- Evidence: MSEP held on all cubic graphs of order 16 (36M pairings) and on 41k random cubic graphs of order 18, with 0 failures (multi-sep). L_N for perfect matchings held in 2,332 decided cases, with 0 failures.

## 19. Star-terminal Lovász decompositions and the spine (coordinator, 2026-11-27)

The spine (`gallai_iff_spineTests'`) reduces Gallai to Test1 and Test2 on 3-connected graphs J with at most two even vertices. Test1 can be reached directly from Lovász decompositions of J.

**Setting.** J has exactly one even vertex z, so n is odd. A Lovász decomposition D of J has (n−1)/2 paths. Every vertex except z ends exactly one path, and z is interior to d(z)/2 paths. Call D **star-terminal** if every path through z has the form x z y …, where x is an end of that path. Call x the short end and y the long side.

**Observation (STL ⇒ Test1).** Suppose some star-terminal D has r on a long side, or has a path x z y of length 2 through z. Then Test1 holds at r.
- Delete z.
- Each path x z y B becomes y B. Here y is interior to the original path, so y's own Lovász end lies on another path, and y now has 2 ends. The vertex x has 0 ends.
- Paths of the form x z y disappear, which only gives slack.
- So J − z has at most (n−1)/2 paths and r has 2 ends.

Example: the wheel W₆, with paths v0 z v1 v2 v3, v2 z v3 v4 v5 and v4 z v5 v0 v1.

**Why it matters.** STL constrains Lovász decompositions at ONE vertex, the unique even vertex. That is the territory of the proved single-vertex results: separation, L1 and `lovasz_endEdge`. multi-sep's crux, "L1 at the even vertex" (uz terminal at a neighbour u of z), is the one-transition case of STL.

A star-type analogue for Test2 (two adjacent even vertices) together with STL would give Gallai, by `gallai_iff_spineTests'`. That is a reason for maximal skepticism.

**Assigned:** the STL session (connections §X). Its tasks: verify the observation, find the Test2 analogue, test both exhaustively on small graphs and 3-connected samples, then attempt proofs by Lovász's induction with z as the special vertex.

**First verdict (STL session, 2026-11-27 05:48).**
- **Surgery criterion, general form.** For a decomposition D of J with b_D(z) = 0, deleting z gives |D′| = |D| + #LL − #SS, where LL and SS count the long-long and short-short transitions at z. Test1 at r holds if #LL − #SS + [r short] ≤ 0.
- **The Test2 analogue, STL2.** D has b(z) = 0, b(r) ∈ {0, 2} and b = 1 elsewhere, and is star-terminal (#LL = 0).
- **Exhaustive, order ≤ 9.** Over all connected graphs with one even vertex, STL(r) ⇔ Test1(r). The 48 failures all have connectivity 1, and Test1 also fails there.
- **3-connected instances.** STL holds on all 25,210 (J, r) pairs. STL2 holds on all 948 3-connected instances of even order ≤ 8. Random 3-connected samples at n = 11–15 gave 0 failures.
- **Flexibility (n = 7, 3-connected).** **Every** perfect matching of N(z) is the transition pairing of some star-terminal Lovász decomposition (168 of 168). Not every short half-set works (244 of 266). This suggests a stronger, induction-friendly form, STL-P: prescribe the pairing at z.
- **Skeptic's note.** "Some star-terminal D exists" is already Gallai-strength: take the cone over Ev(H). So STL reformulates Gallai with all the difficulty concentrated at one vertex in Lovász's setting; it is not a shortcut. For d(z) = 2, STL is multi-sep's EE.

## 20. The main line in its current form: terminal matchings (2026-11-27, 07:30)

**Chain of reductions; the arrows marked "Lean" are machine-checked.**
1. Gallai ⇐(Lean, `gallai_of_stl`) STL + STL2 on 3-connected J with J − z free of matching cuts.
2. STL ⇐ STL-P for some pairing F of N(z) into non-edges.
3. STL-P ⇔ PTM for the matching F in the all-odd graph G = (J − z) + F. Here PTM_m asks that every F-edge be terminal, at a freely chosen end, on its own path of a Lovász decomposition. For STL(r), r's edge must be terminal at r's partner.

**Status of the rungs.**
- PTM_1 = `lovasz_endEdge` (Lean).
- STL at d(z) = 2: `stl_deg_two` (Lean, via `ee_deg_two`).
- PTM_2 and PTM_3: 1,199/1,199 random tests hold. Prescribed ends fail for m ≥ 2 (17 counterexamples), so the free choice of end is essential.
- STL-P: every 3-connected graph of order 7 and 9 holds (54,213 pairings). The only failure is W₄ with the diagonal pairing, where F is parallel to edges of J.

**Sessions.**
- **ptm** (connections §Z): PTM_2, then PTM_m, by carrying pending terminal edges. Candidate tool: the Fan mechanism of `pee_adjEven`.
- **ee** (connections §Y): the last EE case, the manuscript, and audit A21.

**Skeptic's note.** STL, and hence PTM_m for the relevant matchings, is Gallai-strength (STL session, §19). The ladder concentrates the difficulty; it does not remove it.

## 21. One obstruction, four faces (coordinator, 2026-11-27 11:10)

After a day of descent along the STL / PTM ladder, four lines stall at what looks like the same configuration:
- **L∞ residual (§V.4c).** The even vertex sits at distance 3, all its neighbours at distance 2, and it has degree ≥ 4 or lies on a triangle.
- **L1\* blocked instances (§AA).** In Lean, `l1starGen_of_blocked` reduces general L1\* to them.
- **EE with ≥ 2 common neighbours (§Y).** `ee_of_l1Blocked` reduces it to the blocked case.
- **PTM base failures (§Z).** Local copies of the K₄ / W₄ obstruction: ≥ 3 edges between the two F-edges.

Recursive certificates fail at CP(3) + apex and at double-K₄. The same cocktail-party configuration was the subject of the Fan barrier theorems (FanBarrier.lean) and of the flower move at Fan's equality (Flower.lean: `hub_cycles`, `flower_decomp_rest`; missing-move and endpoint-structure §7).

**Hypothesis.** Each residual is the equality case of Fan's inequality, and the flower / receipt-or-flower moves built earlier for that equality are the missing tool. Assigned to the tight-fan session (connections §AB).
- **If it works:** it closes L1\* and hence EE, closes L∞, and removes the girth condition from PTM₂, giving Test1 at d(z) = 4 in general.
- **If it fails:** the precise new obstruction is the next target.

**Status of the ladder (all Lean, standard axioms).**
- Gallai ⇐ `gallai_of_stl` ⇐ STL + STL2.
- STL is proved at d(z) = 2. Test1 is proved at d(z) = 4 under local girth 5 (`test1_of_localgirth`).
- EE is proved when the two vertices share at most one common neighbour.
- L1\* and EE reduce to the blocked case.
- No counterexample to any conjecture on the ladder: STL, STL2, PTM₂ (except K₄), EE, L1\* local form. The exhaustive ranges are n ≤ 9 to 11, with millions of instances.

**Orientation correction (2026-11-27 12:00; tight-fan side finding, checked against ROADMAP).**
- Spine Test1 at d(z) = 4 was already known: by two-step faithful descent and `emc_four` (EMCFour.lean), the two-end test at d = 4 holds by Lovász + Fan alone (ROADMAP, Nov 26). So `test1_of_girth5` / `test1_of_localgirth` re-derive a known case by a new mechanism. They are valuable as a *composition* method, not as new coverage.
- **The first open rung of the STL / PTM ladder is d(z) = 6**, i.e. PTM_3 or STL-P with three transitions. That is exactly **T(6)-i**, the two-end test at d = 6, which has been the project's frontier since Nov 26 (`rooted_six_of_bstmt3`, the BranchBase / BStmt 3 line, the d6-frontier certificates).
- Every line converges there. The next decisive target is T(6)-i with the new tools:
  - the separation theorems;
  - the PTM₂ walk theorem;
  - the tight-transfer (forced-chain) lemma;
  - the leaf-graph protections.

**tight-fan unification (step 1).**
- **Flowers are structurally inapplicable.** They produce b = 2 decompositions, while all residuals ask for Lovász decompositions with b ≤ 1. This is being recorded as negative lemmas.
- **Two mechanisms, not one.**
  - (A) Transfer-side, "Fan at equality with one protected blank". The chain is forced, and the invariant survives iff the forced chain avoids the protected end. This covers L∞, the minimal L1\* blocked shape, and PTM's no-walk instances. A refined Fan lemma (a blank never reached as a predecessor does not count against the supply) closes all 68/68 PTM no-walk instances at n = 8.
  - (B) Hypothesis-side admissibility. In the blocked case some u always gives a good but inadmissible instance.
  - (C) PTM's K₄ / W₄ base failures are a third, base-side configuration.

## 22. The T(6)-i residual and the composition method (ptm, 2026-11-27 13:43)

**The residual.** A failure of T(6)-i has B = J − z and U = N(z), with |U| = 6. Its core is D = K6 − B[U] ∈ {∅, K2, P3, K3, C4}: 5 shapes and 66 rooted patterns. On top of that, a long list of degree, root and odd-vertex conditions apply (MR Thm 144, L133, 4EX, INC, 6CL, d6-frontier). The core is finite, but the exterior is unbounded: every even-order graph occurs as B[O], and |B| ≥ 12. So exhaustive treatment is data only, at |B| ≤ 12–14.

**Why the chained walk does not apply directly.** ν(D) ≤ 2, so every pairing of U has at least 3 − ν(D) pairs adjacent in B. No pairing is "simple".
- A parallel pair in role e1 is harmless if the merge goes through z. This is a J-form of Thm 8.2, easy on paper, not yet in Lean.
- In roles e2/e3, the B-edge makes the endless end a blank neighbour of the first walk target. That is exactly the shape of tight-fan's `fan_single_protected_supp`, with u = y_i and the protected blank p = x_i.

**Plan by shape.**
- **C4:** the J-form chained walk alone, with no new Fan lemma.
- **K2, P3, K3:** one protected step.
- **∅:** two protected steps.

ptm is testing these on random J with B[U] = K6 − D. tight-fan's protected-blank lemma is the shared tool.

**Obstruction found (ptm, 14:04).** The chained walk's base hypothesis (Thm 8.2: one Lovász decomposition of M separating six pairs) is **unsatisfiable** for K2/P3/K3/∅.
- **Why the separation fails.** In M every edge lies on a path, so separated pairs must be non-adjacent in M. A parallel pair in role e2 or e3 keeps its B-edge in M, so the separation of {x_i, y_i} is impossible. This holds whatever Fan lemma is used; `walk_step_protected` repairs the walk-back step, not the base.
- **What the scheme can handle.** Only D = C4, with the parallel pair in role e1 and y2y3 ∈ D. Data are running.
- **What is needed for the rest.** The six separations come from vertex-set tracking ("every path through y_i"). What is actually needed is that the path *ending* at y_i avoids x_i. So an **end-path-tracking refinement** of walk_back / leaf_walk is required, or a chain design whose walks use the B-edges, before K2/P3/K3/∅ can be attacked.

**Sharpening and correction (ptm, 14:06).**
- **Forced non-edges.** The forced non-edges of B are x2y2, x3y3 and y2y3, which form a path x2 y2 y3 x3 contained in D. Only C4 contains such a path.
- **C4 needs one protected step.** Along the cycle, y2x3 is a diagonal, so the blank x3 is adjacent to the first target y2 of P1. That is exactly `walk_step_protected` with u = y2 and p = x3.
- **The "impossible" verdict for K2/P3/K3/∅ is conditional.** It depends on the proof's use of y2 ∉ V(P2), and A22c found no counterexample to Thm 8.2 without that condition. Two concrete lemmas follow:
  - (a) Thm 8.2 without y2 ∉ V(P2), via end-path tracking at y2;
  - (b) the chained walk with one protected step at the start of P1.
  - (b) covers C4; (a) + (b) might reach K2/P3/K3.

**t6-dense, report 1 (15:24).** In the dense residual the chains are free. Label so that x1y2 and x2y3 are B-edges. Then both walks are single B-edges, P2 = y3x2 and P1 = y2x1, so chain conjecture 8.6 is not needed.

**The base D0.** The whole construction can be read off one base, D0, a Lovász decomposition of M = (B − x1y2 − x2y3) + ℓ1y1, in which x3 is the only even vertex. Only end-path conditions are needed:
- (E1) the ℓ1-path avoids x1 and does not end at y2 or y3;
- (E2) P_{y2} ∌ x2;
- (E3) P_{y3} ∌ x3;
- (E4) P_{y2} ≠ P_{y3};
- (E5) P_{x2} ∌ y3;
- (E6) the static predecessor condition on D0.

This replaces vertex-set tracking, so the "separated pairs non-adjacent" obstruction disappears. **The construction covers every dense shape (∅/K2/P3/K3/C4)**, because it uses only x1y2, x2y3 ∈ B.

**Data.** Every certificate was executed and checked edge by edge.
- C4 sparse, |B| = 14: 1280/1280.
- Residual-style graphs, |B| = 14: every root of every shape certified (90/90).

**What remains for the whole dense T(6)-i residual:** the existence of a base D0 satisfying (E1)–(E6). That is a constrained-Lovász statement with one even vertex, the project's home territory. The reduction is being formalised (T6Dense.lean).

## 23. State of the programme (2026-11-27, 16:35)

**Machine-checked reductions of Gallai.** All are in Lean with standard axioms.
1. **Spine:** Gallai ⇔ Test1 ∧ Test2 on 3-connected J with J − z free of matching cuts (`gallai_iff_spineTests'`).
2. **STL:** Test1 ⇐ STL, Test2 ⇐ STL2, so Gallai ⇐ STL + STL2 (`gallai_of_stl`).
3. **RR:** Gallai ⇐ RR, a constrained Lovász decomposition of the free graph of a routed pairing (`gallai_of_routeRR`).

**Proved rungs.** These cover Test1 by degree d(z) of the even vertex.
- d(z) = 2 is trivial in 3-connected graphs. STL is proved at d(z) = 2 (`stl_deg_two`).
- d(z) = 4: Test1 is known (`emc_four` / two-step descent). There is also a new composition proof (`test1_of_localgirth`) and the d = 4 packaging `test1_deg_four`.
- d(z) = 6 (T(6)-i):
  - the sparse / far-apart case is known (six-even-incidence Thm 1(2)), with a new composition proof (`test1_of_chains3`, conditional on chains);
  - **the dense residual (∅/K2/P3/K3/C4) reduces, in Lean, to ONE base conjecture** (`test1_of_appendBases`, t6-dense Conj 5.1). That conjecture is a Lovász decomposition of a graph M with one even vertex, satisfying five or six end-path conditions. *Correction (A26):* by Prop 2.6 its main branch is EQUIVALENT to STL-P plus two prescribed terminal edges, so it is a strengthening of STL, not a weaker target. In lean mode 536 residual roots are certified and 46 are budget-undecided; none was shown to lack a base.

**Proved strengthenings of Lovász (single-vertex constraints).**
- separation (pair and set forms);
- L1 (leaf trick);
- prescribed end edge in all-odd graphs (`lovasz_endEdge`);
- EE when |N(u) ∩ N(z)| ≤ 1, and EE at d(z) = 2;
- PEE at neighbours of z;
- the refined Fan lemma with protected blanks;
- the walk theorems (PTM₂ at local girth 5, PTM₃ far-apart).

**Open core conjectures.** No counterexample to any of these.
- **ST** (some target): implies L1Blocked, hence L1*, EE and L∞ (with TR, needed only when N(g) ⊆ N(c)).
- **t6 base conjecture** (Conj 5.1): implies the dense T(6)-i residual. Together with MR Thm 144, which excludes roots isolated in the core (there D ⊇ K_{1,5}, outside the five shapes; audit A26 F1), it implies all of T(6)-i. **Superseded as a target by the triangle base conjecture of §24**, which is a weaker sufficient condition.
- **MSEP / L_N:** implies Gallai for graphs whose even subgraph has a perfect matching.
- **PTM_m** and the **chain conjecture:** composition at higher d(z).

All four are statements about Lovász decompositions with at most one even vertex, constrained at several prescribed end-paths.

**Negative results banked.**
- EMM, EMM₃, multi-leaf packed separation, PEE away from z, PEE_m with prescribed ends, ST′ and RR\* are all false.
- Flower moves cannot output Lovász decompositions.
- Realisability of a prescribed half-set is NP-hard.

**Next.** Look for the master statement behind the open core: a **constrained Lovász theorem** with several end-path constraints under a locality and compatibility condition. It should be true on the data, contain ST, the t6 base conjecture and MSEP, and be provable by Lovász's induction carrying every constraint. In parallel, t6-dense attacks its base conjecture directly.

## 24. Direct lift to Test1 through triangles at z (external proposal, verified; 2026-11-27 17:30)

**Proposal.** The project lead forwarded it from another agent "with a grain of salt". Its data:
- J with one even vertex z, d(z) = 2m, and δ(J) ≥ 3;
- r ∈ N(z), w ∈ N(z) − r, and a perfect matching M0 = {a_i b_i} of J[N(z) − {r, w}] (edges of J);
- M = J − zw − {z a_i, z b_i, a_i b_i}, with 3m − 2 edges deleted.

In M, z is a leaf at r and w is the only even vertex.

**Theorem (direct lift).** If some Lovász decomposition D0 of M satisfies, for every i, (a_i ∉ V(Q0(b_i))) ∨ (b_i ∉ V(Q0(a_i))), then Test1 holds at (J, z, r).
- **Proof.** Delete z: drop or trim the zr-path, splitting at r if needed; vertex sets only shrink. Then append each a_i b_i at an end chosen by the disjunction. The appends are legal because M0 is a matching and each path has two ends.
- **Comparison.** No STL, no star-terminal condition, and m − 1 disjunctive conditions in place of the 5–6 conditions of t6-dense Conj 5.1. Audit A26 showed Conj 5.1's main branch is STL-P plus two prescribed terminal edges, which is *stronger* than STL.

**My checks.**
1. **Hand proof.** I checked the two steps above by hand, including Q0(z) = zr and the shared-path case. The guard example (C4 + two pendants: every 2-path decomposition violates the disjunction) is also correct.
2. **Computation** (`manuscripts/direct-test1/scripts`). Random dense 3-connected J. The base is found with route_ext.c (per-end avoidance queries), and the lift is executed and verified independently.

   | order | d(z) | roots | base found | lift verified |
   |---|---|---|---|---|
   | 11 | 6 | 180 | 180 | 180 |
   | 13 | 8 | (partial) 24 | 24 | 24 |

**Manuscript:** `manuscripts/direct-test1/direct-test1.tex` (3 pp.), with Conjecture "triangle base".

**Next.**
- Lean formalisation of the lift.
- An independent audit (A28).
- Attack the triangle base conjecture, which is now the cleanest target for T(6)-i and for Test1 at every even d(z) with a near-perfect matching in N(z) − r.

**Audit A28 and the triangle-base session (2026-11-27, 18:30; connections §AF, E29).**
- **Lean.** Banked, sorry-free with standard axioms:
  - the lift for every m (`DirectTest1.lean`);
  - the packed, far-apart and L1\* cases of the base (`TriangleBase.lean`);
  - the (E7)-branch comparison `triangleBase_of_E5_E7`.
- **Precise comparison** (replacing "weaker / sharper" above). At m = 3 and r = y1, M is t6-dense's base graph, and (E5), (E7) are disjuncts of the triangle condition. So the triangle base is implied by the (E7) branch of Conj 5.1 at that root. No other implication is known.
- **Framing** (A28 F3). For fixed data, the triangle base is equivalent to Test1 with a terminal matching of N(z) − {r, w}. It is a PTM-type strengthening of Test1, not a weaker kind of statement.
- **Data** (exhaustive to order 9). The triangle base holds at every root with data of every 2-connected J. All failures are universal-twin pairs in components of M. There are no multi-pair compatibility failures.
- **New single-vertex target: Conjecture DL** (disjunctive avoidance, `DisjL1`). DL ⇒ triangle base whenever M is connected.
- **Isolated roots** (refining the next paragraph). Data at r depend only on J[N(z) − r]: they exist iff ν(J[N(z) − r]) ≥ 2 (d(z) = 6). So they exist at every root of the five dense shapes, and at an isolated root whenever the other five core vertices carry two disjoint edges (e.g. D = K_{1,5}). For "triangle base ⇒ T(6)-i", isolated roots therefore need MR Thm 144 only when ν(J[N(z) − r]) ≤ 1.

**Correction to §§22–23 (audit A26, F1).**
- Not every T(6)-i failure has a dense shape. A root isolated in the core has D ⊇ K_{1,5}, outside {∅, K2, P3, K3, C4}. Such roots are excluded by MR Thm 144 (failing roots may be taken with ≥ 3 neighbours in T; Shaik-free per ROADMAP). So "Conj 5.1 ⇒ T(6)-i" and "triangle base ⇒ T(6)-i" both use MR Thm 144 as well.
- t6-dense FINAL agrees that the direct lift (§24) is a weaker sufficient condition than Conj 5.1, and so is the better target.

## 25. Verification of three forwarded claims; the forest lift (2026-11-27 18:20)

The project lead forwarded three claims from another agent and asked that each be verified, by hand and computationally or against the Lean definitions, before anything is built on them. Script: `manuscripts/direct-test1/scripts/verify/verify3.py`. Its enumerator is exhaustive up to a cap; `bf_check.py` checks it against brute force on 60 graphs with 0 mismatches. Logs are in the same directory.

1. **Forest edge-stepping: TRUE.**
   - Setting: append each parent edge p(v)v of a rooted forest Φ at the v-end of the unique path ending at v.
   - Statement: the result is a decomposition into the same number of paths iff (i) p(v) ∉ V(Q0(v)) and (ii) siblings lie on different paths.
   - Hand proof: each path receives at most one edge per end, and the appends commute.
   - Computation: 101,282/101,282 iff agreements on 40 graphs of order 6 and 8.
   - Manuscript: direct-test1, Lemma 3.1.
2. **Forest lift to Test1: TRUE, as a sufficient condition.**
   - Setting: T = N(z) − {r, w}, Φ a forest T-join of H = J − {z, r}, M = J − zw − zT − Φ, with w's component rooted at w.
   - The parities are as claimed: z is a leaf at r, r is unchanged (r ∉ H), w is even (possibly 0), and every other vertex is odd.
   - Step 1 is unchanged. Step 2 is Lemma 3.1 on D1. Conditions (i) and (ii) transfer from Q0 to D1 because every D1 path is a subpath of a unique Q0 path.
   - Computation: 192/192 parity checks hold, 253,834 lifts all valid (T1), and 84 instances have a tree component with ≥ 3 vertices.
   - Manuscript: direct-test1, Thm 3.2.
   - It **generalises** the direct lift (Φ = M0) and needs no hypothesis on J[N(z)]. For 3-connected J it applies at every r and every w. The forest base conjecture (Conj 3.4) is formally weaker than the triangle base.
   - Lean has only the matching case (`test1At_of_triangleBase`).
3. **"A25 (L1*) gives the single-pair OR unconditionally": FALSE as argued.**
   - Component sub-claim TRUE (2-connected J, |J| ≥ 5): a component with odd set {a1, b1} would be the path a1 w b1, attached only through z. Computation: 0/246.
   - Admissibility sub-claim FALSE. Lean `Admissible G c A` requires A to be non-adjacent to every even vertex. In the claimed configuration b1 ~ w (= the even vertex), so the reverse direction is never admissible, whatever |C ∩ Odd| is. Computation: 57/246 instances have both directions inadmissible, all with |C ∩ Odd| ≥ 4.
   - Also, L1Star has no unconditional proof in Lean; it is only `l1star_of_ST_TR` / `l1star_of_gen`.
   - The OR itself held in all 246 instances. In the tail configuration (N_M(w) = {a1, b1}, N_M(b1) = {w}) it has a direct proof: delete w and b1, split at a1, prepend b1 w. See Remark 3.5.

**Consequence.** The cleanest Test1 target is now the forest base conjecture: for 3-connected J, some w, Φ, rooting and Lovász decomposition of M satisfy (i) and (ii). By Lemma 3.1 these are single-vertex avoidances plus a sibling condition.

**Addendum (18:45).**
- **The forest lift is reversible.** For fixed (r, w, Φ, rooting), the forest base holds iff J − z has a (T1) decomposition at r in which every Φ-edge p(v)v is the end edge of its path at p(v). The proof is end counting; the lower bounds sum to exactly 2k (sent to triangle-base for the tex).
  - So Conj 3.4 is "(T1) with a terminal forest T-join". This is PTM-type, the analogue of A28 F3.
  - It is still weaker than the terminal-matching form.
- **A28's no-data example has forest bases.** J = K_{3,4} + x1x2 has N(z) independent, so no triangle data. It has a forest base at all four roots (`scripts/verify/fb_k34.py`).
  - Root y1: w = y2, Φ = {x1y3, x1y4} rooted at y3. Lifted by hand: the result is a valid (T1) decomposition [y3 x1 y2 x2], [y1 x1 x2 y3], [x1 y4 x2 y1].
