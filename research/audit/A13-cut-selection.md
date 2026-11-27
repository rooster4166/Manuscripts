# A13 — Referee audit: endpoint-min-max, cut selection (Theorem 21) and its machinery

Auditor: independent adversarial referee pass, 2026-11-27.

Sources audited:
- **[EMM]** `manuscripts/endpoint-min-max/endpoint-min-max.tex`, as merged on this branch: the A13 fixes plus the author's revision 8e7346e (EMM₃, the new Prop 9 / Cor 22 via SP Theorem 10.16, wording fixes), 15 pp. Numbers such as "Lemma 20" refer to the compiled PDF. They are the same in the version I started from (a1522ab) and in the merged one.
  - The focus is §4.4, "Cut selection holds for every graph": identity (3) = (eq:split), Lemma 19 (free degrees), Lemma 20 (linked transitions) and Theorem 21 (cut selection, `thm:ps`).
  - Then the Gallai consequence: Corollary 22 and Proposition 9, both in the original form (EMM ⇒ Gallai) and in the merged form (EMM₃ at δ ≥ 5 ⇒ every Gallai failure is an SP 10.16(1) witness).
  - I also checked what they use: Lemma 1 (four forms), Lemma 6 (signed form, G^v), Lemma 7 (parity), Remark 10, Lemma 13 (good pairings), Lemma 14 (T-join pairing), Theorem 17 (guarded route lemma) and Corollary 18. I checked Theorem 11 (per-vertex matroids) and Theorem 15 (cones) more briefly.
- The inequality itself: ED = `gallai/01-original-manuscripts/even-degrees.pdf` §12.4, inequality (1), b(W) ≤ |δ_G(W)| + 2k − d(v) − b(v) for W ⊆ V(G) − v. [EMM] (1) is verbatim.
- SP = `gallai/02-november-25/separating-pairs.pdf`, Theorems 10.16 and 12.28 (as cited by the new Prop 9).
- Background:
  - `research/synthesis.md` §§5–14 and `research/connections.md` §§T–U;
  - missing-move Theorem 7.5 and its outputs (`manuscripts/missing-move/scripts/outputs/emm_counterexamples12*.{g6,log}`);
  - synthesis §12 and `scripts/petersen_counterexample.py` (the n = 28 example);
  - synthesis §14 and `scripts/emm3_counterexample.py` (the n = 18 EMM₃ example);
  - ES §1 and Lean `Doubling.lean` for (R).

**Version.**
- I started at 5e0c7f1, where the .tex was last changed in a1522ab.
- The parent session checkpointed my work (5c68000, f910027) and pushed a recompiled PDF (b9dd270).
- At the coordinator's request I merged the author's revision `origin/claude/emc-four-even` (8e7346e). The merge commit 328eb52 was committed by the main session while the merge was still in progress, and it contained unresolved conflict markers in the .tex. I resolved all six hunks as an ordinary edit (fdfaddd), keeping both sides (§5), and recompiled. The emm3-gadgets result (EMM₃ false, synthesis §14) arrived in 18d429f and eba61f6, and I recorded it in the text (4765feb).
- The conflict in `research/experiments.md` (not my file) was resolved by keeping both sides: the author's blank line, and this branch's E17 addendum 2.

**Independence.** I wrote `research/audit/A13-scripts/a13_check.py` (the construction and a brute-force check of (1)) from the text alone, before opening the authors' `scripts/construction.py`. It shares no code with `manuscripts/endpoint-min-max/scripts/`, `tools/cutfeas.c` or `tools/realis.c`. The same holds for:
- `a13_forms.py` (Lemmas 1, 6, 7 with max-flow);
- `a13_realis.py` (a new exact realisability oracle);
- `a13_emm3_18.py` and `a13_emm3_gadget.py` (the n = 18 example, rebuilt from its description).

Re-runs of the authors' script are labelled **non-independent**.

Verdicts: **SOUND**; **GAP** (fixable; the fix is stated); **ERROR** (false; a counterexample is given); **UNCLEAR** (cannot be settled from the available material).

---

## 0. Summary table

| # | Item | Verdict | Note |
|---|---|---|---|
| C1 | **Lemma 1 (four forms)**: (a) ⇔ (b) ⇔ (c) ⇔ (d) | **SOUND** | (a)⇔(b) uses b(V) = 2k; (b)⇔(c): \|δ(Y+v)\| = \|δ_{G−v}(Y)\| + d(v) − e(v,Y); (c)⇔(d): the cut {σ} ∪ X has capacity \|N(v)∖X\| + \|δ_{G−v}(X)\| + b(X). Checked on every (M, v) at n = 6 and on 78,928 (M, v) at n = 8, including the max-flow (d) (§3.3). |
| C2 | Proposition 2 (necessity by arms) | SOUND | Each end occurrence terminates ≤ 1 arm; both arms of a path through v end at its two distinct ends. |
| C3 | **Lemma 6 (signed form) and the G^v single-commodity form** | **SOUND** | b_M = 1 − x_M pointwise, \|δ_{G^v}(Y)\| = \|δ_{G−v}(Y)\| + \|Y∖N(v)\|. Gale: the cuts with finite capacity are exactly the Y ⊆ V − v. The flow version (unmarked even ≠ v → distinct marked vertices or v) matches (c) on every instance tested. The superfluous "because there are no isolated vertices" was replaced by the author in 8e7346e. |
| C4 | **Lemma 7 (parity)** | **SOUND** | \|δ_{G^v}(Y)\| = \|δ(Y)\| + \|Y\| − 2e(v,Y) ≡ \|Y ∩ Ev\|, and x_M(Y) ≡ σ_P(Y) ≡ \|Y ∩ Ev\|. Checked on every (v, Y) at n ≤ 8. |
| C5 | **Lemma 13 (good pairings ⇔ σ_P(Y) ≤ \|δ_{G^v}(Y)\| ∀ v, Y)** | **SOUND** | x_M(Y) ≤ σ_P(Y) with equality for the transversal marking outside Y. Brute force agrees on all 299 pairings at n = 6, and on every constructed pairing at n ≤ 8. |
| C6 | Lemma 14 (T-join pairing) | SOUND | Works in any graph, connected or not (handshake per component). |
| C7 | Theorem 17 (guarded route lemma) | SOUND | Token injectivity rechecked: equal edge tokens force z_p = h_{p′}, z_{p′} = h_p ∈ N(v), so h_p is a bypass that is an end of another passage, which is forbidden. Merged wording: passages are unordered pairs, and the parity of σ_P comes from \|Y∩Ev\| = σ_P(Y) + 2·#{p ⊆ Y}. Both are correct. |
| C8 | Corollary 18 | SOUND | K_{2,m}: q bypasses each passage ℓ_{2i−1} p ℓ_{2i}. |
| C9 | **Identity (3) (eq:split)** | **SOUND** | E(G^v) = E(F^v) ⊔ E(J − v), so δ_{G^v}(Y) = δ_{F^v}(Y) ⊔ δ_{J−v}(Y). Checked numerically on every (v, Y) of 23,354 constructions (n ≤ 8). |
| C10 | **Lemma 19 (free degrees)** | **SOUND** | d_F ≡ [w∈Ev] + [w∉Ev] = 1. For w ≠ v, deg_{F^v}(w) = d_F(w) − [vw∈F] + [w∉N(v)] is odd iff vw ∈ J. deg_{F^v}(v) = n − 1 − d(v). Asserted at every v of all 113,000+ constructions. |
| C11 | **Lemma 20 (linked transitions)**, original and merged wording ("one path for each passage {x, y}") | **SOUND** | The charging is injective (§2.3). It covers every Y ⊆ V − v, hence every W, for v ∈ Ev (end edge vz, path z → v crosses δ_{F^v}(Y)) and for v odd (no bad end). Good pairs are charged to J-edges, bad pairs to F^v-edges, and these sets are disjoint. The bound has no +1. |
| C12 | Paragraph after Lemma 20 (guards are linking paths) | SOUND; GAP (incomplete), **fixed** | It said only that the guards give some of the linking paths. The guard paths are edge-disjoint. Deleting them leaves z and v as the only odd vertices of F^v, and a vertex on one route has exactly two odd vertices. So the remaining linking paths exist, and Theorem 17 is a special case of Lemma 20. One sentence added. |
| C13 | **Theorem 21 (cut selection)**, original and merged | **SOUND**; GAP (one line), **fixed** | Transitions are a perfect matching of the J-edges at v, except for one end edge when v ∈ Ev. v is odd in F^v and can only be paired with a J-neighbour z. Closed trails and repeated vertices would contain a cycle of J; the justification was missing and is added. Lemma 14 needs no connectivity of F^v. Polynomial. The merged proof keeps my sentence and the author's new one (d_J(v) = 0 ⇒ v odd, nothing to link), which is correct. |
| C14 | Thm 21(1): "or any other T-join that is a forest (e.g. a minimum one)" | SOUND (remark) | This is no wider: a forest T-join is the T-join of every spanning tree containing it (T-joins in a tree are unique). A minimum T-join is a forest. |
| C15 | **Computation: `scripts/construction.py` (non-independent)** | **Reproduced**; GAP (counts), **fixed** | 0 failures in every family, with exactly the printed counts. The text's "all trees of orders 8–12" means orders 8, 10, 12 with e ≥ 2 (20, 99, 538 trees, one construction each). Order 12 uses two trees per graph. Now said, merged with the author's "e > 0 (of 112 / 11,117)". |
| C16 | **Independent check of Thm 21** | **No failure** | All connected graphs of order ≤ 8 (11,229; 10,992 with e ≥ 2): 67,822 constructions. 1,133 further graphs (cycles, K_{a,b}, trees of orders 8, 10, 12, random graphs of orders 10 and 12, …): 22,660 constructions. Two F^v-pairing procedures, one of them an arbitrary random edge-disjoint pairing. Brute force on (1) for every transversal, v and W. Random pairings fail (400 of 10,893 at n = 8), so the test has teeth. §3. |
| C17 | Proposition 9, **original** (EMM + CS₀ ⇒ Gallai) | SOUND | The pendant vertex handles odd order. Superseded in the merge. |
| C18 | Corollary 22, **original** (EMM ⇒ Gallai) | **SOUND as an implication; vacuous, since EMM is false**; GAP (status), **fixed**, then superseded by the author's revision | [a1522ab] nowhere recorded the refutation. The abstract, §4.4 and open problem 1 said that Gallai "reduces to" the sufficiency of (1). What the proof uses is that every connected even-order graph has a realisable half-set (§4.1). |
| C19 | Remark 10: "CS + sufficiency ⇒ (R_s) ⇒ (R) ⇒ Gallai", original | **Correct as an implication** | CS + EMM puts every even r in a realisable half-set, so p(H) ≤ k for every H (not only critical H), and attaching a leaf at r gives the Lean `RootedTest` directly. Then `gallai_iff_rootedTest`. Vacuous for the same reason as C18. The merged remark restricts to δ ≥ 3 and no longer claims Gallai, which is correct. |
| C26 | **Proposition 9, merged** (EMM₃ + CS at δ ≥ 5 ⇒ if Gallai fails, SP 10.16(1) occurs) | **SOUND** (given SP 10.16 as cited) | The rooted-test equivalence matches Lean `RootedTest`. The least failing even order 2h + 2 is exactly SP 10.16's hypothesis, and SP 10.16(2) puts every failing host at δ ≥ 5. At an even root, CS + EMM₃ give h + 1 paths with two ends at t, and the leaf extends one of them. At an odd root, any realised half-set has an end at t. The statement of 10.16(1) and the Thm 12.28 remark match SP verbatim. §4.2. |
| C27 | **Corollary 22, merged** (EMM₃ at δ ≥ 5 ⇒ every Gallai failure yields an SP 10.16(1) witness) | **SOUND as an implication; hypothesis open** | CS comes from Thm 21. EMM₃ at δ = 3 is false (C28), but no counterexample with δ ≥ 5 is known. The hypothesis is used for one half-set per failing host, so (R_s) on SP-10.16(2) hosts suffices. The remark after Cor 22 is rewritten to say so (§5). |
| C28 | **Conjecture 4 (EMM₃), merged** | **ERROR (refuted)**; status **recorded in the text** | The order-18 example of synthesis §14 is confirmed independently. (1) holds at every v and every W (brute force, 2^18 subsets). The gadget's forcing property holds (my oracle: D⁺ realisable, D + w with b(w) ∈ {0, 2} not realisable). The gluing argument rechecked (§4.4). One sentence added after the EMM₃ paragraph; open problem 1 now asks about δ ≥ 5. |
| C29 | Merged evidence: "at order ≤ 8 every half-set of a δ ≥ 3 graph is realisable" (Table 1, δ ≥ 3 rows) | **Reproduced (independent)** | 13 graphs / 60 half-sets at n = 6, 2,475 / 19,422 at n = 8, all cut-feasible (`out/delta3.txt`). |
| C20 | **Strengthenings tested on the known counterexamples** | **New facts** (§4.3) | (i) *Every transversal of every good pairing is realisable*: **false**. In KsOeBW??G`?A the pairing {03, 18, 45, 69, 7 10} is good, and its transversal {3, 4, 8, 9, 10} is the Thm 7.5 half-set. 4 of the 12 order-12 graphs behave like this. (ii) *Every transversal of every Thm 21 pairing is realisable*: **holds on all 12**, for every tree and every F^v-pairing (proved, §4.3). The n = 28 half-set L is never a transversal of any route-system pairing. |
| C21 | Remark "certificates and guards" | Logic SOUND; count not re-run | "31 graphs at order 8 with no guarded decomposition of a minimum T-join" was not re-run. It no longer matters (C12). |
| C22 | Remarks (1)–(2) of §4.5 | SOUND; one sentence UNCLEAR | n − 1 − d(v) = s(v) + b(v) − 1 ✓. "An apex joined to the vertices of positive slack is realised exactly, but separately for each v" has no checkable content. Left as is. |
| C23 | Theorem 11 (per-vertex matroids); matroid-intersection remark | SOUND (brief check) | λ_v is supermodular and even. ℓ_v is a supermodular projection, and g_v ≥ ⌈\|X\|/2⌉ is submodular. Edmonds; rank ≥ e/2. Intersection: ⌈a/2⌉ + ⌈(e−1−a)/2⌉ ≥ e/2. |
| C24 | Theorem 15 (cones) | SOUND (brief check) | s(u) = 0. The case u ∈ W uses \|δ(U)\| = \|δ_H(U)\| + \|U\| and d_H(v) ≤ \|δ_H(U)\| + \|U\| − 1. |
| C25 | §8 Formalisation | GAP (wording), **fixed** | `CutFeasible` and `gallai_of_emm_cs` exist on no branch (`git grep` on this branch, lean-d6-frontier and missing-move). The text read as if they did. Now "planned"; `EmmTemplate.lean` has `CutOK`. |

**Overall.** **Theorem 21 is correct**, in the original and the merged wording. Every step I was asked to check is SOUND:
- the forms of (1) and the G^v reduction, including parity;
- identity (3) and Lemma 19;
- the injective charging of Lemma 20;
- the path structure of the transitions in a forest;
- the pairing of v itself when v ∈ Ev;
- the existence of the F^v-pairings when F^v is disconnected.

Two independent implementations find no failure: the authors', and mine with arbitrary F^v-pairings and a brute-force check of (1) itself.

**The Gallai consequence.**
- The original Corollary 22 ("EMM ⇒ Gallai") is a correct but vacuous implication.
- The merged Proposition 9 / Corollary 22 are correct implications from EMM₃ at minimum degree ≥ 5, granting SP Theorem 10.16. Their hypothesis is open.
- The conjecture as stated in the merged text, EMM₃ at minimum degree 3, is false. I confirmed the order-18 counterexample independently and recorded it in the text. I changed no mathematics.

---

---

## 1. The forms of (1) and the G^v formulation

### 1.1 Lemma 1

- **(a) ⇔ (b).** Put U = V − W. Then b(W) = 2k − b(U) (this needs b(V) = 2k) and δ(W) = δ(U). The maps W ↦ V − W biject {W ⊆ V − v} with {U ∋ v}.
- **(b) ⇔ (c).** Put U = Y ∪ {v} with Y ⊆ V − v. Then b(U) = b(v) + b(Y) and \|δ(U)\| = \|δ_{G−v}(Y)\| + (d(v) − e(v,Y)). Subtracting d(v) + b(v) gives (c).
- **(c) ⇔ (d).** The network is G − v with unit arcs both ways, σ → y (y ∈ N(v), capacity 1) and z → τ (capacity b(z)). A cut {σ} ∪ X has capacity \|N(v)∖X\| + \|δ_{G−v}(X)\| + b(X), and this is ≥ d(v) iff (c) holds at X. An integral flow of value d(v), after cancelling antiparallel units and discarding cycles, is a family of edge-disjoint σ–τ paths. These are the arms, and an arm may have length 0. Conversely, arms are a flow.

### 1.2 Lemma 6 and G^v

- **The identity.** x_M = 1 − b_M holds pointwise (Od: 1 − 1 = 0; M: 1 − 2 = −1; Ev∖M: 1 − 0 = 1). So b_M(Y) = \|Y\| − x_M(Y), and the remark about isolated vertices is not needed.
- **The edges of G^v.** For Y ⊆ V − v, the edges of G^v leaving Y are those of G − v from Y to V − Y − v, together with the new edges from v to Y ∖ N(v). So \|δ_{G^v}(Y)\| = \|δ_{G−v}(Y)\| + \|Y∖N(v)\|, and (c) becomes x_M(Y) ≤ \|δ_{G^v}(Y)\|.
- **Gale's form.** The supplies are 1 at each unmarked even vertex ≠ v. The demands are 1 at each marked vertex ≠ v, and v is an uncapacitated sink. A cut whose source side contains v has infinite capacity. The others are Y ⊆ V − v, with capacity \|S∖Y\| + \|δ_{G^v}(Y)\| + \|M∩Y\|, which is ≥ \|S\| iff x_M(Y) ≤ \|δ_{G^v}(Y)\|. **Correct.**
- **The informal routing paragraph after Lemma 6.** Each unmarked even non-neighbour w has its own edge wv and contributes no net slot; the slots listed are right. SOUND as an informal reading.

### 1.3 Lemma 7 (parity)

- |δ_{G−v}(Y)| = |δ(Y)| − e(v,Y). So |δ_{G^v}(Y)| = |δ(Y)| + |Y| − 2e(v,Y) ≡ Σ_{y∈Y}(d(y) + 1) ≡ |Y ∩ Ev|.
- x_M(Y) ≡ |Y ∩ Ev|, since x_M = ±1 exactly on Ev.
- σ_P(Y) ≡ |Y ∩ Ev| as well: pairs inside Y count twice in |Y ∩ Ev|. Theorem 17 uses this.

### 1.4 Lemma 13

- **The bound.** For a transversal M: a pair inside Y contributes +1 − 1 = 0, a pair outside contributes 0, and a split pair contributes ±1. So x_M(Y) ≤ σ_P(Y).
- **Equality.** Mark the outside vertex of every split pair. Then x_M(Y) = σ_P(Y), which gives the converse.
- **Cuts.** σ_P(V − X) = σ_P(X) and every cut has a side avoiding v, so "the cut condition for the demand graph P in G^v" is the same statement.
- The pair containing v itself, when v ∈ Ev, is handled correctly. v ∉ Y always, so that pair is split iff its partner lies in Y.

**Computation (independent).**
- `a13_forms.py` compares (a), (c), the signed form, the max-flow arm system (d) and the Gale flow of Lemma 6. It does so vertex by vertex, on every half-set:
  - all connected graphs of order 6: 3,186 pairs (M, v);
  - every tenth connected graph of order 8: 1,112 graphs, 78,928 pairs (M, v).
  All five forms agree everywhere, and Lemma 7 holds on every (v, Y).
- `a13_check.py sanity` checks Lemma 13 against the definition on all 299 pairings of Ev at order 6, and they agree.
- My brute-force check of (1) reproduces the manuscript's cut-infeasible counts exactly: 18 of 518 half-sets at n = 6 and 2,100 of 101,714 at n = 8. These equal Table 1's non-realisable counts, as they must, since EMM holds at n ≤ 8.

## 2. Section 4.4: identity (3), Lemma 19, Lemma 20, Theorem 21

### 2.1 Identity (3)

- F^v and G^v share the new star at v. The other edges split as E(G − v) = E(F − v) ⊔ E(J − v).
- So E(G^v) = E(F^v) ⊔ E(J − v) as edge sets, and for Y ⊆ V − v, δ_{G^v}(Y) = δ_{F^v}(Y) ⊔ δ_{J−v}(Y). **SOUND.**
- The new edges join v to non-neighbours of v in G, not in F. A J-neighbour of v is a G-neighbour, so it is never joined to v in F^v.

### 2.2 Lemma 19

- **Degrees in F.** d_J(w) ≡ [w ∈ Ev] (T-join) and d(w) ≡ [w ∉ Ev], so d_F(w) is odd.
- **Degrees in F^v, for w ≠ v.** There are three cases:
  - vw ∈ J: degree d_F(w), odd;
  - vw ∈ F: degree d_F(w) − 1, even;
  - w ∉ N(v): degree d_F(w) + 1, even.
- **Degree of v.** deg_{F^v}(v) = n − 1 − d(v), which is odd iff v ∈ Ev.
- **Count.** The odd vertices number d_J(v) + [v ∈ Ev], which is even. **SOUND.**

### 2.3 Lemma 20 (linked transitions)

Fix v and Y ⊆ V − v, and a split pair p = {a, c} with a ∈ Y.
- **Good pairs.** R_p ⊆ J, so "good" (an edge of δ_{G−v}(Y) on R_p) means an edge of δ_{J−v}(Y). Routes are edge-disjoint, so the charges are distinct.
- **Bad pairs.** R_p must leave Y. Its first exit is not in δ_{J−v}(Y), so it is an edge xv with x ∈ Y.
  - **c = v.** The route ends at v, and its end edge is vz with z = x ∈ Y.
  - **v interior.** Let y follow v. If y ∈ Y, the rest of R_p would have to leave Y again without revisiting v, through δ_{J−v}(Y), which is impossible. So y ∉ Y ∪ {v}.
- **Injectivity.** A bad pair has exactly one transition at v, since a path visits v once. That transition is either its passage (x, y) or the end edge vz. Different routes have different transitions, because each J-edge at v lies on one route.
  - The linking paths of distinct transitions are edge-disjoint by hypothesis.
  - Each linking path joins a vertex of Y (x or z) to a vertex outside Y (y, or v itself), so it contains an edge of δ_{F^v}(Y). Distinct bad pairs therefore get distinct F^v-edges.
  - F^v-edges are never J-edges, so the two charge sets are disjoint.
- **Conclusion.** σ_P(Y) ≤ \|δ_{J−v}(Y)\| + \|δ_{F^v}(Y)\| = \|δ_{G^v}(Y)\|, with no parity unit needed. Lemma 13 then applies. **SOUND.**
- **Coverage.** All Y ⊆ V − v are covered, so all W are covered (Lemma 1). Both v ∈ Ev (the end-edge case) and v odd (no route ends at v, so there is no bad end) are covered. The hypothesis at v is used only for that v.

### 2.4 The paragraph after Lemma 20 (C12)

- **What the guards give.** A bypass u gives the path x u y: xu, uy ∈ E∖J and u ≠ v, so it lies in F − v ⊆ F^v. Private neighbours give x w_x v w_y y: vw_x ∈ F^v because w_x ∉ N(v) ∪ {v}.
- **The guard paths are pairwise edge-disjoint.** The private neighbours are distinct. Every passage end lies in N(v), while no private neighbour does. A bypass of p is not an end of another passage at v. This rules out every coincidence.
- **The missing paths exist.** At a busy even v, deleting all the guard paths leaves z and v as the only odd vertices of the rest of F^v (Lemma 19), so they are joined by a path. At a vertex on only one route, the odd vertices of F^v are exactly x, y (or z, v).
- **Consequence.** Every guarded route system satisfies the hypothesis of Lemma 20, so Theorem 17 is a special case of Lemma 20. The text said only that the guards give some of the linking paths, and I added the two sentences above.

### 2.5 Theorem 21

- **Transitions.** At v with d_J(v) > 0, Lemma 14 pairs the odd vertices of F^v. These are the J-neighbours of v, plus v when v ∈ Ev (Lemma 19).
  - G is simple, so each J-neighbour corresponds to exactly one J-edge at v.
  - When v ∈ Ev, v is odd in F^v. Every other odd vertex is a J-neighbour, so v is paired with a J-neighbour z, and vz is the unique end edge.
  - The transitions at v are therefore a perfect matching of the J-edges at v, minus one end edge when v ∈ Ev. A vertex with d_J(v) = 0 is odd (d_J ≡ [v∈Ev]) and carries nothing.
- **Following transitions.** Each J-edge has a successor at each end, or ends at an end edge. This partitions J into trails between end edges, and possibly closed trails.
  - A trail that revisits a vertex contains a closed subtrail. A closed trail has a non-empty even edge set, which contains a cycle. In a forest neither can occur.
  - So every trail is a path. Its two ends are vertices of Ev carrying an end edge, and they are distinct, because each vertex has at most one end edge. Every vertex of Ev is the end of exactly one path.
  - This sentence of the proof was asserted without the cycle argument, and I added it.
- **The routes.** The passages of the resulting routes at v are exactly the declared transitions, and the end edges are as declared. The linking paths are the Lemma 14 paths, which are edge-disjoint. Lemma 20 applies. **SOUND.**
- **Disconnected F^v.** Lemma 14 needs no connectivity: each component of any graph has an even number of odd-degree vertices. At n = 8, F^v was disconnected in 84,855 of my (construction, v) instances, 83,393 of them with a component of odd order, and v ∈ Ev was paired 264,048 times. All were fine.
- **Forest hypothesis.** It is used only to make the trails paths. It is sufficient, not necessary.

### 2.6 Remarks of §4.5

- (1): "In G^v the vertex v is joined to its n − 1 − d(v) = s(v) + b(v) − 1 non-neighbours". Correct, since s(v) + b(v) − 1 = 2k − d(v) − 1.
  - The opening sentence ("An apex joined to the vertices of positive slack is realised exactly, but separately for each v") has no precise content, and I left it.
- (2): correct.

## 3. Computations

All runs used `nice`. Outputs are in `research/audit/A13-scripts/out/`.

### 3.1 The authors' script (non-independent)

`nice python3 scripts/construction.py` (`out/author_construction.txt`):

| family | graphs | constructions | not good |
|---|---|---|---|
| all connected, order 6 | 99 | 297 | 0 |
| all connected, order 8 | 10,893 | 32,679 | 0 |
| random G(10,p), seed 20261127 | 250 | 750 | 0 |
| bottleneck families | 82 | 246 | 0 |
| trees, order 8 / 10 / 12 (e ≥ 2) | 20 / 99 / 538 | 1 each | 0 |
| random G(12,p), seed 12 | 150 | 300 | 0 |

These match the text. The tree counts and the number of trees per graph are now stated precisely (C15).

Note: the authors' F^v-pairing is deterministic (first component, first two leaves). Its goodness check uses `tools/cutfeas.c`.

### 3.2 Independent check (`a13_check.py`)

**Implementation.**
- J is the T-join of a random-weight minimum spanning tree.
- F^v is built literally from the definition. Lemma 19 is asserted at every v.
- The odd vertices of F^v are paired by one of two procedures:
  - `proof`, which follows the proof of Lemma 14 (cycles deleted, then random leaf pairs);
  - `greedy`, which joins a random odd vertex to a random odd vertex of its component by a random path and deletes it. This produces arbitrary edge-disjoint pairings, a wider class than the authors'.
- Asserted for every construction:
  - the linking paths are simple and pairwise edge-disjoint;
  - the transitions are perfect matchings apart from the end edge;
  - following them gives vertex-simple paths, which cover J exactly (no closed trails) and pair Ev;
  - every passage equals the declared transition.
- **Goodness is tested against the definition:** every transversal M of the pairing satisfies ED (1) for every v and every W ⊆ V − v. It is enumerated over all 2^n subsets with numpy, and Lemmas 1, 6 and 13 are not used.
- The `deep` mode also checks identity (3), Lemma 7 and the σ criterion of Lemma 13 on every (v, Y).

**Results.**

| family | graphs | constructions | failures |
|---|---|---|---|
| `data/conn6.g6`, all connected order 6 (99 with e ≥ 2) | 112 | 1,120 (5 trees × 2 procedures), deep | 0 |
| `data/conn8.g6`, all connected order 8 (10,893 with e ≥ 2) | 11,117 | 66,702 (3 × 2) | 0 |
| `data/conn8.g6`, deep: (3), Lemma 7, σ on every (v, Y) | 11,117 | 22,234 (1 × 2) | 0 |
| families (10 trees × 2 procedures each) | 1,133 | 22,660 | 0 |

The families are:
- cycles C₄–C₁₂;
- K_{a,b} with a + b even and ≤ 12 (20 graphs, including K_{2,2}, …, K_{2,10} and K_{4,4}, K_{4,6}, K_{4,8}, K_{6,6});
- K_{2,m} plus the hub edge;
- K_n minus a perfect matching (n = 4, …, 12; all vertices even);
- wheels, ladders and paths of orders 4–12, the Petersen graph and Q₃;
- the order-12 EMM counterexample KsOeBW??G`?A;
- **all trees of orders 8, 10 and 12** (23 + 106 + 551);
- 200 random connected G(10, p) and 60 G(12, p), p ∈ [.15, .8];
- 100 random connected order-10 graphs with e ≥ 6;
- 40 random 4-regular graphs of orders 10 and 12.

**The test has teeth.** A uniformly random pairing of Ev is bad in 7 of 99 graphs at n = 6 and in 400 of 10,893 at n = 8 (`out/sanity.txt`).

**No failure was found.**

### 3.3 Forms (`a13_forms.py`)

See §1.4: all five forms agree on all 3,186 pairs (M, v) at n = 6 and on 78,928 at n = 8 (a one-in-ten sample of the graphs).

## 4. The Gallai consequence: Proposition 9 and Corollary 22, before and after the merge

### 4.1 The original form (a1522ab): EMM + CS₀ ⇒ Gallai

- **Proposition 9.** Its proof uses EMM only to make one cut-feasible half-set realisable in each connected even-order graph. A realisation of b_M has exactly n/2 paths, and the pendant vertex handles odd order. **SOUND.**
- **Corollary 22.** CS₀ is now a theorem (Thm 21; M = ∅ when e = 0), so Corollary 22 is a correct implication.
  - Its hypothesis is false: missing-move Thm 7.5 gives a cut-feasible, non-realisable half-set at n = 12, and synthesis §12 gives one at n = 28.
  - **What the corollary actually needs** is the statement (S): *every connected graph of even order has a realisable half-set.* (S) implies Gallai through the pendant vertex, without Thm 21.
  - Thm 21 adds only a place to look for the half-set: the transversals of an explicit good pairing. This matches the existential descent of synthesis §13.
- **Remark 10, "CS + sufficiency ⇒ (R_s) ⇒ (R) ⇒ Gallai".** This is **correct as an implication.**
  - CS + EMM puts every even r into a realisable half-set M ∋ r. Its n/2 paths have two ends at r and one at every odd vertex.
  - Hence p(H) ≤ n/2 for every connected even-order H. This matters because ES's (R) is stated only for critical H, and its equivalence with the rooted statement needs p(H) ≤ n/2 as well. Here that comes for free.
  - Attaching a leaf at any r and extending a path ending at r gives p(H^r) ≤ n/2, which is the Lean `RootedTest`. `gallai_iff_rootedTest` then gives Gallai.
  - The step "(R_s) ⇒ (R)" is immediate. Like Cor 22, the chain is vacuous because EMM is false.

### 4.2 The merged form (8e7346e): EMM₃ at δ ≥ 5, via SP Theorem 10.16

**SP Theorem 10.16**, read from the PDF. Let 2h + 2 be the least even order with a connected (F, t) such that p(F^t) > h + 1. Then either:
1. there is a two-connected simple W of order 2h + 1 with no matching cut, at least h + 1 missing edges and p(W) > h; or
2. every failing host of order 2h + 2 is two-connected and four-edge-connected, has no matching cut, and has minimum degree ≥ 5.

Theorem 12.28 says that if (1) is absent, the minimum degree is ≥ 6. The manuscript cites both exactly.

**Proposition 9 (merged).** The hypothesis is that every connected even-order graph with δ ≥ 5 satisfies EMM₃ and CS. The conclusion is that a failure of Gallai forces SP 10.16(1). **SOUND.**
- *Equivalence.* Gallai ⇔ p(F^t) ≤ n/2 for all connected even-order F and all t. This is exactly Lean `RootedTest`, and `gallai_iff_rootedTest` is proved in `Doubling.lean`.
- *Least failure.* If Gallai fails, some (F, t) fails. The least even order 2h + 2 of a failure is SP's hypothesis verbatim.
- *Case (2).* Take a failing (F, t). F is connected of even order with δ ≥ 5, so the hypothesis applies.
  - **t even.** CS gives a cut-feasible M ∋ t. EMM₃ gives h + 1 paths with b(t) = 2, and extending one of them by the leaf gives p(F^t) ≤ h + 1.
  - **t odd.** Any realised half-set has b(t) = 1; when e = 0, Lovász's theorem gives this with M = ∅. Extend in the same way. This is a contradiction.
- *What it uses.* EMM₃ is applied to one half-set per failing host. So the hypothesis can be weakened to (R_s) on SP-10.16(2) hosts: every even vertex lies in a realisable half-set. With Thm 21, EMM₃ at δ ≥ 5 implies this.
- The paragraph after the proof is commentary, and it is correct: (1) is an odd-floor failure, one path below Gallai's budget, and below budget cuts alone do not suffice.

**Corollary 22 (merged).** CS holds for every graph by Thm 21, so this is Prop 9 without the CS hypothesis. **SOUND as an implication.**
- Its hypothesis, EMM₃ at δ ≥ 5, is open. The only refutation of EMM₃ known (§4.4) has δ = 3.
- Synthesis §§12 and 14 expect NP-hardness of half-set realisability to carry over to higher minimum degree through gadgets. That would make the hypothesis false unless P = NP (cut-feasibility is polynomial by Lemma 1), but it is not yet proved.
- The remark after Cor 22 now says what the corollary uses (§5, item 6).

### 4.3 Which strengthenings survive the counterexamples (`a13_realis.py`, `a13_mm12_pairings.py`, `a13_mm12_forced.py`, `a13_petersen28.py`)

**The oracle.** `a13_realis.py` is a new exact realisability oracle: a DFS that grows each path from the least vertex with an end left, memoised, with parity and component pruning.
- At n = 6 it agrees with the cut checker on all 531 half-sets, as EMM predicts there.
- On the 12 order-12 graphs of `emm_counterexamples12.g6` it finds 1,932 half-sets, 269 of them non-realisable. This is exactly the count of `emm_counterexamples12_cut_test.log`.
- Each of the 12 graphs has **exactly one** cut-feasible non-realisable half-set, the M of the log.

**(i) "Every transversal of every good pairing is realisable" is false.** I enumerated all pairings of Ev: 105 when e = 8, and 945 when e = 10. In 4 of the 12 graphs the bad M is a transversal of some good pairing:

| graph | good pairings | good pairings having M as a transversal |
|---|---|---|
| KqGUDg??GP?A | 105 | 24 |
| KqGUDg?AG@?@ | 105 | 24 |
| KsOeBW??G`?A | 657 | 48 |
| KsOeBW?CG@?@ | 657 | 48 |

An explicit witness is KsOeBW??G`?A with the good pairing {0 3, 1 8, 4 5, 6 9, 7 10} and its transversal {3, 4, 8, 9, 10}, which is cut-feasible and not realisable. This is quoted in the new remark after Cor 22.

**(ii) "Every transversal of every Theorem-21 pairing is realisable" holds on all 12 graphs, for every spanning tree and every choice of F^v-pairings.** The proof has two cases, according to the graph.
- **Complement not cut-feasible** (8 graphs). In these, Ev ∖ M is not cut-feasible, so M is a transversal of no good pairing: transversal sets are closed under complement.
  - The graphs are KqGUDg?AG@?D, KqGUDgG?G@?B, KqGUDgG?G@?E, KqGUDgG?G@?F, KsOeBW?CG@?D, KsOeBWO?G@?B, KsOeBWO?G@?E and KsOeBWO?G@?F.
- **A forced pair inside M** (the other 4 graphs). A bridge lies in every T-join iff one of its sides holds an odd number of even vertices.
  - In each of these 4 graphs, M contains both ends of a forced J-edge whose other edges at both ends are forced out of J, for example {3, 10} and {8, 9} in KsOeBW??G`?A.
  - Such an edge is a whole route in every route system of every T-join. So M is never a transversal of a Thm-21 pairing.
- In 50 random constructions per graph, every transversal of every constructed pairing was realisable (`out/mm12.txt`).

**(iii) The n = 28 example (synthesis §12, S = L) never arises from a route system.**
- Every vertex of G_bad is even, so every T-join has odd degree at every vertex.
- l₆ has degree 2, with neighbours l₅ and l₇ of degree 2. So l₆ has J-degree 1, and its J-edge goes to l₅ or l₇, which also have J-degree 1. That edge is a whole route, which pairs two vertices of L.
- So L is never a transversal of any route-system pairing, from any T-join. In 400 constructions, at least 5 pairs always lay inside L (`out/petersen28.txt`).
- I did not test the other transversals at n = 28.

**Consequence for the programme.** The weakest corrected target suggested by Cor 22 is "some transversal of the Thm-21 pairing is realisable". A stronger one is "all transversals of Thm-21 pairings are realisable". Neither is refuted by any known counterexample, whereas the intermediate "all transversals of all good pairings" is false.

The construction never marks both ends of a J-edge joining two J-degree-1 vertices. In the n = 28 example and in 4 of the 12 order-12 graphs, the bad half-set marks such a pair. In the other 8, its complement is not even cut-feasible. This fits the "never starve a region" heuristic of synthesis §13.

### 4.4 EMM₃ (merged Conjecture 4) is false: the order-18 example, checked independently

`a13_emm3_18.py` and `a13_emm3_gadget.py` rebuild the graph from the description in synthesis §14. G = D + K_{4,4} + {sp, sb₀}, where:
- D is two K₄ blocks {a₀..a₃} and {b₀..b₃}, with p ~ a₁, a₂, b₁ and q ~ a₃, b₂, b₃;
- s is a vertex of the K_{4,4}.

So n = 18, m = 36, δ = 3, e = 16, and the half-set is M = V(K_{4,4}).
- **Cut-feasible.** Brute force over every v and all 2^18 sets W ⊆ V − v: (1) holds everywhere.
- **Forcing property of D (my oracle).** D⁺ = D + leaves at p and b₀, with b = 1 at both leaves, a₀ and q, is realisable. D + w, with w ~ p, b₀ and b = 1 at a₀, q, is **not** realisable for b(w) = 2, nor for b(w) = 0.
- **Gluing argument, rechecked.** {sp, sb₀} is a 2-edge cut. The D-side has b = 0 except at a₀ and q, so its segments have at most four ends: a₀, q and the two edge-ends at s.
  - If sp and sb₀ lie on one path through s, the D-side is D + w with b(w) = 0, which is impossible.
  - Otherwise it is D⁺ with four unit ends. Every 2-path realisation of D⁺ joins the two leaves, since D + w with b(w) = 2 is not realisable. In G this would be a path through s twice, which is impossible.
  - So M is not realisable.
- A direct run of my DFS oracle on the n = 18 graph had not finished when this report was written. It is not needed, given the gluing argument.

The merged text stated EMM₃ as a conjecture without this. One sentence now records it after the EMM₃ paragraph, and open problem 1 now asks about δ ≥ 5.

**Caution for the EMM_ns route of synthesis §11.** A selection that never marks a degree-2 vertex cannot exist in general. In C_n every even vertex has degree 2. In KsOeBW??G`?A, 7 of the 10 even vertices have degree 2, and a half-set needs 5 marks.

## 5. Changes made to the .tex (recompiled twice with pdflatex each time; numbering unchanged)

Note on the build environment: `lmodern.sty` was missing on this machine. I installed the Debian package `lmodern`. With it, the unmodified source rebuilds to a PDF of exactly the committed size. The remaining overfull boxes (18.9pt, 35.6pt, 66.8pt) were already in the author's version.

**Before the merge** (committed by the parent session in f910027):
1. Abstract and §2: EMM refuted (n = 12, missing-move Thm 7.5; n = 28, synthesis §12).
2. After Lemma 20: the guard paths are edge-disjoint, and the remaining linking paths exist by Lemma 19. So Theorem 17 is a special case of Lemma 20 (C12).
3. Proof of Theorem 21: the one-line reason why trails in a forest are paths and none is closed (C13).
4. After Corollary 22: the construction-script counts are made precise (C15), and a remark says what Corollary 22 uses.
5. Open problem 1, and §8 Formalisation (the Lean names are planned, not existing; C25).

**Merge with the author's revision 8e7346e** (fdfaddd). All six conflict hunks were resolved by keeping both sides:
1. *Abstract, first paragraph.* The author's EMM₃ wording is kept, with "and by the same mechanism at order 28" added.
2. *Abstract, Gallai sentence.* The author's (via SP 10.16).
3. *§2 after the conjecture.* The author's example of Theorem 7.5 is kept, with one sentence added on the order-28 counterexample, which also rests on saturated degree-2 vertices. The edge list of the example now has `\allowbreak` (it was 115pt overfull).
4. *Proof of Theorem 21.* My cycle sentence plus the author's d_J(v) = 0 sentence.
5. *After Corollary 22.* The author's paragraph, with my precise script counts merged into the author's "e > 0 (of 112 / 11,117)". The remark "what Corollary 22 uses" is **rewritten for the merged corollary**:
   - the first version, EMM ⇒ Gallai, is vacuous;
   - the proof of Prop 9 needs EMM₃ only for one half-set per failing host, that is (R_s) on SP-10.16(2) hosts;
   - Thm 21 says where to look;
   - "every transversal of every good pairing is realisable" fails without a degree condition, with the KsOeBW??G`?A witness.
6. *Open problems.* The author's list.

**After the merge** (4765feb):
1. After the EMM₃ paragraph of §2: "EMM₃ is false as well" (synthesis §14, order 18, δ = 3). Corollary 22 assumes δ ≥ 5, which that example does not reach, so EMM₃ is used only as a hypothesis.
2. Open problem 1: EMM₃ is false at δ = 3; does sufficiency hold at δ ≥ 5?

## 6. Recommendations (not done; for the authors)

1. The paper's title and framing ("An endpoint min-max conjecture") should follow the pivot of synthesis §§13–14. The cut inequalities are:
   - necessary;
   - always simultaneously satisfiable (Thm 21);
   - sufficient at n ≤ 8;
   - not sufficient at n = 12 and n = 28, nor at minimum degree 3 (n = 18);
   - NP-hard to characterise.

   The merged Conjecture 4 (EMM₃) should be restated as refuted, and only the δ ≥ 5 case that Cor 22 uses kept open. Restructuring is the authors' call; I only made the status explicit.
2. Theorem 17 can now be stated as a corollary of Lemma 20 (§2.4). Corollary 18 and the certificate tables then become illustrations.
3. State the "forced pair" observation of §4.2 as a lemma, since it explains why the Thm-21 pairings avoid both known counterexample families. A J-edge between two vertices of J-degree 1 is a route in every decomposition. In particular, two adjacent even vertices of degree 2 whose shared edge lies in J are paired.
4. For the "pairing-guided descent" test of synthesis §13, use the observation of §4.2 that on all 12 order-12 counterexamples every transversal of every Thm-21 pairing is realisable. That makes them natural first test cases.
5. The second sentence of §4.5 Remark (1) should be rewritten or removed (C22).
