# A13 — Referee audit: endpoint-min-max ("Prescribed ends in path decompositions"), cut selection (Theorem 21) and the hardness section

Auditor: independent adversarial referee pass, 2026-11-27.

Sources audited:
- **[EMM]** `manuscripts/endpoint-min-max/endpoint-min-max.tex`. **Final version audited:** the author's rewrite ef78acc, "Prescribed ends in path decompositions: a cut inequality, cut selection, and hardness", merged with the A13 corrections in 1c24c59; 17 pp.
  - Numbers such as "Lemma 20" refer to the compiled PDF. The numbering of Lemmas 1, 6, 7, 13, 14, 19, 20, Theorems 15, 17, 21 and Corollary 18 is the same in all three versions I saw: a1522ab (start), 8e7346e (first revision) and ef78acc (rewrite).
  - The focus is §4.4, "Cut selection holds for every graph": identity (3) = (eq:split), Lemma 19 (free degrees), Lemma 20 (linked transitions) and Theorem 21 (cut selection, `thm:ps`). I also checked what they use: Lemma 1 (four forms), Lemma 6 (signed form, G^v), Lemma 7 (parity), Lemma 13 (good pairings), Lemma 14 (T-join pairing), Theorem 17 (guarded route lemma) and Corollary 18. I checked Theorem 11 (per-vertex matroids) and Theorem 15 (cones) more briefly.
  - **§5** (new in the rewrite): Definition 22, Lemma 23 (cuts of line graphs), Propositions 24–25, Theorems 26 (Kotzig) and 27 (NP-hardness), the order-28 example and Remark 28, with `scripts/kotzig.py`.
  - **The Gallai consequence** in its two earlier forms, both since removed: Prop 9 / Cor 22 "EMM ⇒ Gallai" (a1522ab) and "EMM₃ at δ ≥ 5 ⇒ every Gallai failure is an SP 10.16(1) witness" (8e7346e). Also Remark 9/10 in all versions.
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
- **First merge**, at the coordinator's request: the author's revision 8e7346e (EMM₃, Prop 9 / Cor 22 via SP 10.16). The merge commit 328eb52 was committed by the main session while the merge was still in progress, and it contained unresolved conflict markers in the .tex. I resolved all six hunks as an ordinary edit (fdfaddd), keeping both sides, and recorded that EMM₃ is false (4765feb).
- **Second merge** (1c24c59): the author's rewrite ef78acc. Where its text conflicted with my corrections, I kept the corrections (§6). Its other text is the author's.
- b7923d3 on `claude/emc-four-even` added a second proof of cut selection via an auxiliary graph on V × V (`scripts/auxgraph.py`, connections §U). It does not touch the .tex. At the coordinator's request I audited it as well (§5.5); the "transition lemma" in the same note is not audited.
- In both merges, `research/experiments.md` (not my file) conflicted only over a duplicated E18 block. First I kept both sides; then I took the rewrite's de-duplicated version.

**Independence.** I wrote `research/audit/A13-scripts/a13_check.py` (the construction and a brute-force check of (1)) from the text alone, before opening the authors' `scripts/construction.py`. It shares no code with `manuscripts/endpoint-min-max/scripts/`, `tools/cutfeas.c` or `tools/realis.c`. The same holds for:
- `a13_forms.py` (Lemmas 1, 6, 7 with max-flow);
- `a13_realis.py` (a new exact realisability oracle);
- `a13_emm3_18.py` and `a13_emm3_gadget.py` (the n = 18 example, rebuilt from its description);
- `a13_kotzig.py` and `a13_petersen_real.py` (§5 of the paper: G(H) rebuilt from Definition 22). I wrote these before reading `scripts/kotzig.py`, apart from its usage line.

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
| C17 | Proposition 9, **original** (EMM + CS₀ ⇒ Gallai) | SOUND | The pendant vertex handles odd order. **Removed** in the rewrite. |
| C18 | Corollary 22, **original** (EMM ⇒ Gallai) | **SOUND as an implication; vacuous, since EMM is false**; GAP (status), fixed in f910027; **removed** in the rewrite | [a1522ab] nowhere recorded the refutation. The abstract, §4.4 and open problem 1 said that Gallai "reduces to" the sufficiency of (1). What the proof uses is that every connected even-order graph has a realisable half-set (§4.1). |
| C19 | Remark 10: "CS + sufficiency ⇒ (R_s) ⇒ (R) ⇒ Gallai", original | **Correct as an implication** | CS + EMM puts every even r in a realisable half-set, so p(H) ≤ k for every H (not only critical H), and attaching a leaf at r gives the Lean `RootedTest` directly. Then `gallai_iff_rootedTest`. Vacuous for the same reason as C18. **Final Remark 9** makes no Gallai claim: "cut selection by itself says nothing about Gallai's conjecture". **SOUND.** |
| C26 | **Proposition 9 of 8e7346e** (EMM₃ + CS at δ ≥ 5 ⇒ if Gallai fails, SP 10.16(1) occurs); **removed** in the rewrite | **SOUND** (given SP 10.16 as cited) | The rooted-test equivalence matches Lean `RootedTest`. The least failing even order 2h + 2 is exactly SP 10.16's hypothesis, and SP 10.16(2) puts every failing host at δ ≥ 5. At an even root, CS + EMM₃ give h + 1 paths with two ends at t, and the leaf extends one of them. At an odd root, any realised half-set has an end at t. The statement of 10.16(1) and the Thm 12.28 remark match SP verbatim. §4.2. |
| C27 | **Corollary 22 of 8e7346e** (EMM₃ at δ ≥ 5 ⇒ every Gallai failure yields an SP 10.16(1) witness); **removed** in the rewrite | **SOUND as an implication; hypothesis open** | CS comes from Thm 21. EMM₃ at δ = 3 is false (C28), but no counterexample with δ ≥ 5 is known. The hypothesis is used for one half-set per failing host, so (R_s) on SP-10.16(2) hosts suffices. |
| C28 | **EMM₃**: Conjecture 4 of 8e7346e; in the final version **Remark 28** ("open") and **open problem 1** | **ERROR (refuted)**; **flagged, not fixed** (per the coordinator) | The order-18 example of synthesis §14 is confirmed independently (§4.4). (1) holds at every v and every W (brute force, 2^18 subsets). My oracle finds it **not realisable** directly (475 s), and also confirms the gadget's forcing property. Remark 28 and open problem 1 still call EMM₃ open, and need updating. The sentence I had added in 4765feb went with the conjecture in the rewrite. |
| C29 | Evidence: "at order ≤ 8 every half-set of a δ ≥ 3 graph is realisable" (Table 1, δ ≥ 3 rows; Remark 28) | **Reproduced (independent)** | 13 graphs / 60 half-sets at n = 6, 2,475 / 19,422 at n = 8, all cut-feasible (`out/delta3.txt`). |
| C20 | **Strengthenings tested on the known counterexamples** | **New facts** (§4.3) | (i) *Every transversal of every good pairing is realisable*: **false**. In KsOeBW??G`?A the pairing {03, 18, 45, 69, 7 10} is good, and its transversal {3, 4, 8, 9, 10} is the Thm 7.5 half-set. 4 of the 12 order-12 graphs behave like this. (ii) *Every transversal of every Thm 21 pairing is realisable*: **holds on all 12**, for every tree and every F^v-pairing (proved, §4.3). The n = 28 half-set L is never a transversal of any route-system pairing. |
| C21 | Remark "certificates and guards" | Logic SOUND; count not re-run | "31 graphs at order 8 with no guarded decomposition of a minimum T-join" was not re-run. It no longer matters (C12). |
| C22 | Remarks (1)–(2) of §4.5 | SOUND; one sentence UNCLEAR | n − 1 − d(v) = s(v) + b(v) − 1 ✓. "An apex joined to the vertices of positive slack is realised exactly, but separately for each v" has no checkable content. Left as is. |
| C23 | Theorem 11 (per-vertex matroids); matroid-intersection remark | SOUND (brief check) | λ_v is supermodular and even. ℓ_v is a supermodular projection, and g_v ≥ ⌈\|X\|/2⌉ is submodular. Edmonds; rank ≥ e/2. Intersection: ⌈a/2⌉ + ⌈(e−1−a)/2⌉ ≥ e/2. |
| C24 | Theorem 15 (cones) | SOUND (brief check) | s(u) = 0. The case u ∈ W uses \|δ(U)\| = \|δ_H(U)\| + \|U\| and d_H(v) ≤ \|δ_H(U)\| + \|U\| − 1. |
| C25 | §9 Formalisation | GAP (wording), fixed in f910027; **resolved by the rewrite** | `CutFeasible` and `gallai_of_emm_cs` exist on no branch (`git grep` on this branch, lean-d6-frontier and missing-move). The old text read as if they did. The rewrite drops the names. |
| H1 | **Definition 22 (G(H))** | **SOUND** | R-degrees 4 (u_i: 3 + cross edge), l-degrees 2. The path l₁l₅⋯l_Nl₂ needs N ≥ 5 (K₄: l₁l₅l₂). n = 2N, Ev = V, b(V) = 2N. G(H) is connected for every connected H: every component of L(H) − w* contains some u_i. |
| H2 | **Lemma 23 (cuts of line graphs)** | **SOUND** | In a simple cubic H, two edges share at most one end, so each L(H)-edge has a unique vertex. A 1 + 2 split gives 2 crossing pairs. In the bridge argument, y is unmixed and the path's internal vertices pass the side on. Conversely a bridge xy gives m(E(K)) = 1. **Verified on every partition** for \|E(H)\| ≤ 15 (and 4,000 random ones at 18 edges) on 10 cubic graphs, including a bridged one; λ(L(H)) ≥ 4 ⟺ bridgeless in each. |
| H3 | **Proposition 24 (the gadget is cut-feasible ⟺ H bridgeless)** | **SOUND** | v ∈ R: adding a gadget vertex changes f_v by ≥ 2 − (2 − [l∼v]) − [l∼v] = 0, so Y ⊆ R − v suffices. The cross edges play the edges to w*, and (c) at v ⟺ \|δ_{L(H)}(Y+v)\| ≥ 4. v ∈ 𝓛: e(v,Y) ≤ 1 on Y ⊆ R, and L(H) − w* is connected. Brute force on (1) agrees where n ≤ 16, and max-flow agrees on all 10 test graphs. |
| H4 | **Proposition 25 (realisable ⟺ L(H) Hamiltonian-decomposable)** | **SOUND** | b = d = 2 forces the N − 2 one-edge gadget paths; R-vertices (b = 0, d = 4) are interior to both remaining paths, which are Hamiltonian on R. My oracle agrees: K₄, prism, K₃,₃ and the cube are realisable, and **G(Petersen) (n = 28) is not** (2 s). |
| H5 | **Theorem 26 (Kotzig) and the citations** | SOUND (citation) | It is the classical statement (Kotzig 1957; Bermond 1978). The bibliography entries are correct. Checked on 10 graphs by search: L(Petersen) has 160 Hamiltonian cycles and no Hamiltonian decomposition; every Hamiltonian test graph's line graph decomposes. |
| H6 | **Theorem 27 (NP-completeness)** | **SOUND** | Cut-feasibility comes from Prop 24, and realisability from Prop 25 + Thm 26. NP membership: the partition is a certificate. The reduction is from Hamiltonicity of 3-connected cubic planar graphs (Garey–Johnson–Tarjan 1976, correctly cited), which are bridgeless; \|V(G(H))\| = 3\|V(H)\| − 2. Cut-feasibility is polynomial by n max-flows. So the "no polynomial characterisation unless P = NP" claim is correct. Nothing here needs the sufficiency of (1). |
| H7 | Example (order 28) and `scripts/kotzig.py` (non-independent) | **Reproduced** | n = 28, m = 42, slack 24 everywhere. 160 Hamiltonian cycles of L(P). The author's script: 12 test graphs, all consistent (`out/author_kotzig.txt`). |
| H8 | **Remark 28 ("EMM₃ is open")** | **Out of date — flagged** | See C28. The rest of the remark is correct (L starves R: 14 vertices, 4 boundary edges). |
| A1 | **Cut-form pairing lemma** (connections §U): Odd(Γ) has a pairing π with σ_π(S) ≤ \|δ_Γ(S)\| ∀ S | **SOUND** | Edge-deletion induction. All five cases are covered: both ends odd in Γ − xy and paired together, or paired with a ≠ b; exactly one end odd (twice); both even. Each step uses \|δ_Γ(S)\| = \|δ_{Γ−xy}(S)\| + [xy] and the triangle inequality of [ab] = \|1_S(a) − 1_S(b)\|. It is also implied by Lemma 14. Brute-force check over all S on 300 random graphs of order ≤ 12. §5.5. |
| A2 | **Auxiliary graph B on V × V**: Odd(B) = {(v,v): v ∈ Ev}; \|δ_B(S)\| = \|δ_{G^v}(Y)\| | **SOUND** | deg_B(v,w) = deg_{F^v}(w) + [vw ∈ J], which is even for w ≠ v by Lemma 19, and deg_B(v,v) = n − 1 − d(v). For S: copies u ≠ v lie wholly in S or out of it; copy v gives δ_{F^v}(Y); a J-edge ux with u, x ≠ v crosses iff it lies in δ_{J−v}(Y); J-edges at v never cross. Then (eq:split). Also σ_π(S) = σ_P(Y). §5.5. |
| A3 | **Second proof of Thm 21** (pairing lemma on B, then Lemma 13) | **SOUND**, and stronger | It works for **any** T-join, not only forests, but gives no route system. Independent check: all connected graphs of order ≤ 8, 22,906 constructions, of which 4,592 used a non-forest J. Odd(B) was asserted every time; the cut identity was checked exhaustively at n = 6 and on every 50th graph at n = 8; goodness by brute force on (1). No failure. The author's `auxgraph.py` (non-independent): 0 of 10,992 not good. |

**Overall.** **Theorem 21 is correct**, in the original and the merged wording. Every step I was asked to check is SOUND:
- the forms of (1) and the G^v reduction, including parity;
- identity (3) and Lemma 19;
- the injective charging of Lemma 20;
- the path structure of the transitions in a forest;
- the pairing of v itself when v ∈ Ev;
- the existence of the F^v-pairings when F^v is disconnected.

Two independent implementations find no failure: the authors', and mine with arbitrary F^v-pairings and a brute-force check of (1) itself.

**The hardness section (§5) is correct.** Lemma 23, Propositions 24–25 and Theorem 27 are SOUND, and Kotzig's and Garey–Johnson–Tarjan's theorems are cited correctly. My independent rebuild of G(H) confirms every claim on ten cubic graphs, including G(Petersen) being cut-feasible and not realisable.

**The Gallai consequence.**
- The original Corollary 22 ("EMM ⇒ Gallai") was a correct but vacuous implication.
- Proposition 9 / Corollary 22 of 8e7346e were correct implications from EMM₃ at minimum degree ≥ 5, granting SP Theorem 10.16.
- The rewrite removes both. Its Remark 9 correctly makes no Gallai claim.

**The auxiliary-graph proof** of Theorem 21 (connections §U, planned as the main proof) is SOUND: the cut-form pairing lemma, Odd(B) and the cut identity all check, and it does not even need J to be a forest (§5.5).

**The one outstanding problem.** Remark 28 and open problem 1 of the final text still call EMM₃ (minimum degree 3) open. It is false: the order-18 example of synthesis §14, which I confirmed independently, including by a direct oracle run. Per the coordinator I flag this and do not fix it.

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

## 4. The Gallai consequence (two earlier forms, both removed in the final rewrite), and EMM₃

The final text has no Gallai corollary. Remark 9 says that cut selection by itself says nothing about Gallai's conjecture, and that is correct: by §5 of the paper, a cut-feasible half-set need not be realisable. §§4.1–4.2 record the verdicts on the two forms that existed during this audit, since other notes cite them.

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
- In 8e7346e (as merged), the remark after Cor 22 said what the corollary uses. Both went in the rewrite.

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

An explicit witness is KsOeBW??G`?A with the good pairing {0 3, 1 8, 4 5, 6 9, 7 10} and its transversal {3, 4, 8, 9, 10}, which is cut-feasible and not realisable. The final text quotes it in the unnumbered remark "transversals of good pairings" after Theorem 21.

**(ii) "Every transversal of every Theorem-21 pairing is realisable" holds on all 12 graphs, for every spanning tree and every choice of F^v-pairings.** The proof has two cases, according to the graph.
- **Complement not cut-feasible** (8 graphs). In these, Ev ∖ M is not cut-feasible, so M is a transversal of no good pairing: transversal sets are closed under complement.
  - The graphs are KqGUDg?AG@?D, KqGUDgG?G@?B, KqGUDgG?G@?E, KqGUDgG?G@?F, KsOeBW?CG@?D, KsOeBWO?G@?B, KsOeBWO?G@?E and KsOeBWO?G@?F.
- **A forced pair inside M** (the other 4 graphs). A bridge lies in every T-join iff one of its sides holds an odd number of even vertices.
  - In each of these 4 graphs, M contains both ends of a forced J-edge whose other edges at both ends are forced out of J, for example {3, 10} and {8, 9} in KsOeBW??G`?A.
  - Such an edge is a whole route in every route system of every T-join. So M is never a transversal of a Thm-21 pairing.
- In 50 random constructions per graph, every transversal of every constructed pairing was realisable (`out/mm12.txt`).
- The final text keeps a short unnumbered remark after Theorem 21 ("transversals of good pairings") with the KsOeBW??G`?A witness and the forced-bridge reason.

**(iii) The n = 28 example (synthesis §12, S = L) never arises from a route system.**
- Every vertex of G_bad is even, so every T-join has odd degree at every vertex.
- l₆ has degree 2, with neighbours l₅ and l₇ of degree 2. So l₆ has J-degree 1, and its J-edge goes to l₅ or l₇, which also have J-degree 1. That edge is a whole route, which pairs two vertices of L.
- So L is never a transversal of any route-system pairing, from any T-join. In 400 constructions, at least 5 pairs always lay inside L (`out/petersen28.txt`).
- I did not test the other transversals at n = 28.

**Consequence for the programme.** The weakest corrected target suggested by Cor 22 is "some transversal of the Thm-21 pairing is realisable". A stronger one is "all transversals of Thm-21 pairings are realisable". Neither is refuted by any known counterexample, whereas the intermediate "all transversals of all good pairings" is false.

The construction never marks both ends of a J-edge joining two J-degree-1 vertices. In the n = 28 example and in 4 of the 12 order-12 graphs, the bad half-set marks such a pair. In the other 8, its complement is not even cut-feasible. This fits the "never starve a region" heuristic of synthesis §13.

### 4.4 EMM₃ is false: the order-18 example, checked independently

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
- **A direct run of my DFS oracle on the n = 18 graph: not realisable** (475 s, `out/emm3_18.txt`). This confirms the conclusion without the gluing argument.

**Status in the text.** 8e7346e stated EMM₃ as a conjecture, and I recorded its refutation there (4765feb). The rewrite turns EMM into Question 4 and moves EMM₃ to Remark 28 and open problem 1, both of which still call it **open**. That is out of date. Per the coordinator, this is flagged and not fixed. The fix: Remark 28 should say that EMM₃ is false at δ = 3 (synthesis §14, `scripts/emm3_counterexample.py`). Open problem 1 should keep only its second half: does Theorem 27 itself, NP-hardness, extend to δ ≥ 3?

**Caution for the EMM_ns route of synthesis §11.** A selection that never marks a degree-2 vertex cannot exist in general. In C_n every even vertex has degree 2. In KsOeBW??G`?A, 7 of the 10 even vertices have degree 2, and a half-set needs 5 marks.

## 5. Section 5 of the final version: non-sufficiency and hardness

### 5.1 Definition 22 and Lemma 23

- **G(H).** H is a connected cubic graph, so L(H) is simple and 4-regular, and w* has four distinct neighbours u₁, …, u₄.
  - N = \|E(H)\| − 1 ≥ 5, and for N = 5 the path is l₁l₅l₂.
  - Degrees: the u_i have 3 + 1 (cross edge), the other R-vertices 4, every l_i 2.
  - So n = 2N, Ev = V, the gadget 𝓛 is a half-set, and b = 2·1_𝓛 asks for N paths.
  - G(H) is connected for every connected H, since each component of L(H) − w* contains a neighbour of w*. The statement does not say this, but it is needed for G(H) to be an instance, and it holds.
- **Lemma 23.**
  - *Formula.* A vertex x of H whose three edges split 1 + 2 between A and B contributes exactly the two crossing pairs. Each edge of L(H) comes from a unique vertex, because two edges of a simple graph share at most one end.
  - *m(A) = 1 ⇒ bridge.* y ≠ x is unmixed, so all its edges are in A. Each internal vertex of a y–x path in H − e is unmixed, so the whole path is in A. But the only A-edge at x is e. **Correct.**
  - *Bridge ⇒ m(A) = 1.* Take A = E(K). The vertex x has its two K-edges in A and xy in B. The vertex y has all its edges in B. **Correct.**
  - *Consequence.* Every cut of L(H) is δ(A) for some partition, so λ(L(H)) ≥ 4 ⟺ H is bridgeless.
- **Computation (independent, `a13_kotzig.py`).** The formula |δ(A)| = 2m(A) holds on every partition for the 9 test graphs with ≤ 15 edges, and on 4,000 random partitions for the 18-edge one. λ(L(H)) = 4 for all bridgeless ones, and λ = 2 for the bridged one.

### 5.2 Proposition 24

- **v ∈ R.**
  - *Reduction to Y ⊆ R − v.* Adding a gadget vertex l to Y raises b by 2. It removes at most deg_{G−v}(l) = 2 − [l∼v] cut edges and raises e(v, ·) by [l∼v]. So f_v never decreases, and Y ⊆ R − v suffices.
  - *Transfer to L(H).* For such Y, the cross edges from Y ∩ {u_i} to the l_i correspond one-to-one with the edges from Y ∩ {u_i} to w* in L(H). So |δ_{G−v}(Y)| = |δ_{L(H)−v}(Y)| and e(v, Y) = e_{L(H)}(v, Y), and (c) at v ⟺ |δ_{L(H)}(Y ∪ v)| ≥ 4.
  - *All cuts.* The sets Y ∪ v run over all nonempty X ⊆ R, and every cut of L(H) has such a side. **Correct.**
- **v ∈ 𝓛, assuming λ(L(H)) ≥ 4.**
  - If Y meets 𝓛, then b(Y) ≥ 2 ≥ e(v, Y).
  - If Y ⊆ R, then e(v, Y) = 1 only for v = l_i (i ≤ 4) with u_i ∈ Y, and a cut edge is needed.
    - L(H) − w* is connected. Otherwise some component would receive ≤ 2 of w*'s 4 edges and have a cut of size < 4.
    - So Y ⊊ R has an edge to R ∖ Y. Y = R has the three cross edges to the l_j with j ≠ i.
  - **Correct.**
- **The converse** comes from the R-part. Prop 24 is therefore SOUND.
- **Computation.** Two methods agree: brute force on (1) over all v and W where n ≤ 16 (K₄, prism, K₃,₃), and the max-flow arm form at every vertex for all 10 test graphs. The gadget is cut-feasible exactly for the 9 bridgeless graphs.

### 5.3 Proposition 25, Theorem 26, Theorem 27

- **Prop 25, forward direction.**
  - Saturation: d = b + 2·(interior visits), so b = d = 2 leaves no interior visit. Every gadget–gadget edge is therefore a one-edge path. There are N − 3 on the long path and 1 for l₃l₄, so N − 2 in all.
  - Counting ends: l₅, …, l_N get both their ends from these paths. Each of l₁, …, l₄ gets one more, from its cross edge. So the remaining two paths Q₁, Q₂ end exactly at l₁, …, l₄.
  - Each R-vertex (b = 0, d = 4) is interior to two paths, necessarily Q₁ and Q₂. So Q_j minus its two l-ends is a Hamiltonian path of L(H) − w* between two of the u_i. Closing both through w* gives a Hamiltonian decomposition.
- **Prop 25, converse.** Each Hamiltonian cycle uses two of w*'s four edges, so the construction reverses. **SOUND.**
- **Thm 26 (Kotzig 1957).** The bibliographic data (Časopis Pěst. Mat. 82, 76–92; Bermond, Ann. Discrete Math. 3) are correct. Checked by search on the 10 test graphs:
  - L(H) is Hamiltonian-decomposable ⟺ H is Hamiltonian;
  - L(Petersen) has 160 Hamiltonian cycles, as the text says, and no complementary pair.
- **Thm 27.** **SOUND.**
  - Membership in NP: the realisation is a certificate.
  - The reduction is from Hamiltonicity of 3-connected cubic planar graphs, which is NP-complete (Garey–Johnson–Tarjan 1976). Such graphs are bridgeless, so the gadget is cut-feasible.
  - |V(G(H))| = 2(|E(H)| − 1) = 3|V(H)| − 2.
  - "Degrees in {2, 4}" and "half-sets meeting every inequality" hold by construction.
  - The P ≠ NP corollary is correct, because cut-feasibility takes n max-flows (Lemma 1(d)).
- **Direct confirmation of the non-realisable direction.** My oracle decides the gadget of G(Petersen) (n = 28) as **not realisable** in 2 s. The prism (n = 16) and cube (n = 22) gadgets are realisable (`out/petersen_real.txt`).

### 5.4 The order-28 example, Remark 28, and `scripts/kotzig.py`

- **Example.** m = |E(L(P))| − 4 + (N − 3) + 1 + 4 = 30 − 4 + 11 + 1 + 4 = 42. The slack is 28 − 4 − 0 = 28 − 2 − 2 = 24 everywhere. **Correct.**
- **`scripts/kotzig.py`** (non-independent; `out/author_kotzig.txt`). It reports all 12 test graphs consistent: bridgeless ⟺ λ ≥ 4 ⟺ cut-feasible, and Hamiltonian ⟺ Hamiltonian-decomposable, with the oracle for n ≤ 16. This matches the text.
- **Remark 28** calls EMM₃ open. It is **out of date** (§4.4). The rest of the remark is correct: "L starves R: fourteen even vertices and four boundary edges", and the observation that marks inside R remove the Hamiltonicity requirement.

### 5.5 The auxiliary-graph proof of Theorem 21 (connections §U, b7923d3; not yet in the .tex)

- **Pairing lemma, cut form.** Induct on |E(Γ)|; the empty graph has no odd vertices. Delete an edge xy, and let π′ pair Odd(Γ − xy). Write [ab] = |1_S(a) − 1_S(b)|. The cases are:
  1. *x and y odd in Γ − xy and paired together.* Drop the pair: σ decreases.
  2. *x and y odd in Γ − xy, paired with a and b.* Here a ≠ y, b ≠ x and a ≠ b. Replace {x, a}, {y, b} by {a, b}. Since [ab] ≤ [ax] + [xy] + [yb], σ rises by at most [xy].
  3. *Only x odd in Γ − xy.* Then y is not paired in π′, so a = π′(x) ≠ y. Replace {x, a} by {y, a}, using [ya] ≤ [yx] + [xa].
  4. *Only y odd.* Symmetric to case 3.
  5. *Both even in Γ − xy.* Add {x, y}.

  In every case σ_π(S) ≤ σ_{π′}(S) + [xy] ≤ |δ_{Γ−xy}(S)| + [xy] = |δ_Γ(S)|. **SOUND.** No paths, components or handshake lemma are needed, as the note says.
- **B.** The vertex set is V × V. Copy v ({v} × V) carries F^v, and each J-edge vx gives the edge (v,x)–(x,v).
  - *Parity.* deg_B(v,w) = deg_{F^v}(w) + [vw ∈ J]. For w ≠ v this is even by Lemma 19, and deg_B(v,v) = n − 1 − d(v). So Odd(B) = {(v,v) : v ∈ Ev}.
  - *Cut identity.* For v and Y ⊆ V − v, put S = (Y × V) ∪ ({v} × Y). Count the edges of B leaving S:
    - copies u ≠ v are wholly inside S or wholly outside, so their edges contribute nothing;
    - edges of copy v cross exactly when they lie in δ_{F^v}(Y);
    - a J-edge (u,x)–(x,u) with u, x ≠ v crosses exactly when ux ∈ δ_{J−v}(Y);
    - a J-edge (v,x)–(x,v) has both ends in S iff x ∈ Y, so it never crosses.

    So |δ_B(S)| = |δ_{F^v}(Y)| + |δ_{J−v}(Y)| = |δ_{G^v}(Y)| by (eq:split).
  - *Pairs.* (u,u) ∈ S ⟺ u ∈ Y, so σ_π(S) = σ_P(Y).
  - **SOUND.**
- **Conclusion.** σ_P(Y) ≤ |δ_{G^v}(Y)| for every v and every Y ∌ v. By Lemma 13, P is good.
  - The forest hypothesis is not used, since Lemma 19 and (eq:split) hold for any T-join.
  - This proof yields a good pairing but no route system in G, so the polynomial-time *route* construction of Thm 21(1)–(3) still needs the first proof. As a proof of the existence statement it is shorter, and it is correct.
- **Computation** (`a13_auxgraph.py`, independent; `out/auxgraph.txt`).
  - The pairing lemma was checked by brute force over all S on 300 random graphs of order 2–12.
  - For every connected graph of order 6 and 8, I took J both as a spanning-tree T-join and as that T-join plus random cycles of G. The non-forest J occurred in 4,592 of the 22,906 constructions.
  - Odd(B) was asserted every time. The cut identity and σ_π(S) = σ_P(Y) were checked on every (v, Y), for all graphs at n = 6 and every 50th graph at n = 8.
  - Goodness was checked by brute force on (1). No failure.
  - The author's `scripts/auxgraph.py` (non-independent; run from a copy of b7923d3) reports 0 bad pairings among 99 + 10,893 graphs (`out/author_auxgraph.txt`).

## 6. Changes made to the .tex (recompiled twice with pdflatex each time; numbering unchanged)

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

**After the first merge** (4765feb):
1. After the EMM₃ paragraph of §2: "EMM₃ is false as well" (synthesis §14, order 18, δ = 3).
2. Open problem 1: EMM₃ is false at δ = 3; does sufficiency hold at δ ≥ 5?

**Merge with the author's rewrite ef78acc** (1c24c59). This merge had five conflict hunks. The rewrite's text was taken everywhere except where it conflicted with an A13 correction:
1. *Abstract and §2.* The rewrite's text. It already states non-sufficiency (n = 12 and n = 28) and hardness, which covers my status corrections. EMM₃ no longer appears in §2, so my 4765feb sentence went with it (see C28).
2. *After Theorem 21.*
   - The precise script counts were kept (trees of orders 8, 10, 12 with e ≥ 2: 20, 99, 538; two trees at order 12).
   - The rewrite's description of this audit ("about 50,000 further graphs of orders 8–12 in twelve families") was **corrected**. The audit covered all connected graphs of orders 6 and 8 and 1,133 further graphs of orders 4–12, in about 113,000 constructions.
   - The Cor 22 remark, which no longer applies, was replaced by a short unnumbered remark, "transversals of good pairings". It gives the KsOeBW??G`?A witness, and says why no Thm-21 pairing has that transversal (3 10 and 8 9 are forced bridges, each a whole route).
3. *§5 example (order 12).* `\allowbreak` in the edge list again (it was 116pt overfull).
4. *Formalisation and open problems.* The rewrite's text. Its open problem 1 and Remark 28 still call EMM₃ open, which is flagged, not fixed (C28).

The rewrite keeps the A13 corrections that did not conflict: Theorem 17 as a special case of Lemma 20, and the trail-in-forest sentence. The final PDF has 17 pp.

## 7. Recommendations (not done; for the authors)

1. **Update Remark 28 and open problem 1** (C28). EMM₃ is false at δ = 3 (n = 18; synthesis §14; confirmed here, including by a direct oracle run). What remains open is whether Theorem 27 (hardness) extends to δ ≥ 3, and whether (1) suffices at any larger minimum degree.
2. Theorem 17 can now be stated as a corollary of Lemma 20 (§2.4). Corollary 18 and the certificate tables then become illustrations.
3. State the "forced pair" observation of §4.3 as a lemma, since it explains why the Thm-21 pairings avoid both known counterexample families. A J-edge between two vertices of J-degree 1 is a route in every decomposition. In particular, two adjacent even vertices of degree 2 whose shared edge lies in J are paired.
4. For the "pairing-guided descent" test of synthesis §13 (now open problem 2), use the observation of §4.3 that on all 12 order-12 counterexamples every transversal of every Thm-21 pairing is realisable. That makes them natural first test cases.
5. The second sentence of §4.5 Remark (1) should be rewritten or removed (C22).
6. Definition 22: add that G(H) is connected for every connected H (§5.1). This is true, and it is needed because the setting assumes G connected.
