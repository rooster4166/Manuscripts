# A13 — Referee audit: endpoint-min-max, cut selection (Theorem 21) and its machinery

Auditor: independent adversarial referee pass, 2026-11-27.

Sources audited:
- **[EMM]** `manuscripts/endpoint-min-max/endpoint-min-max.tex`, 14 pp. Numbers such as "Lemma 20" refer to the compiled PDF; they are unchanged by my edits. The focus is §4.4, "Cut selection holds for every graph": identity (3) = (eq:split), Lemma 19 (free degrees), Lemma 20 (linked transitions), Theorem 21 (cut selection, `thm:ps`) and Corollary 22 (EMM implies Gallai). I also checked what they use: Lemma 1 (four forms), Lemma 6 (signed form, G^v), Lemma 7 (parity), Proposition 9, Remark 10, Lemma 13 (good pairings), Lemma 14 (T-join pairing), Theorem 17 (guarded route lemma) and Corollary 18. I checked Theorem 11 (per-vertex matroids) and Theorem 15 (cones) more briefly.
- The inequality itself: ED = `gallai/01-original-manuscripts/even-degrees.pdf` §12.4, inequality (1), b(W) ≤ |δ_G(W)| + 2k − d(v) − b(v) for W ⊆ V(G) − v. [EMM] (1) is verbatim.
- Background: `research/synthesis.md` §§5–13, `research/connections.md` §§T–U; missing-move Theorem 7.5 and its outputs (`manuscripts/missing-move/scripts/outputs/emm_counterexamples12*.{g6,log}`); synthesis §12 and `scripts/petersen_counterexample.py` (the n = 28 example); ES §1 and Lean `Doubling.lean` for (R).

**Version.** I started at 5e0c7f1, where the .tex was last changed in a1522ab. While I worked, upstream commits added synthesis §§11–13 (0a686f3, ea53f46), the n = 28 script and ROADMAP changes. The parent session also checkpointed my scripts (5c68000). None of these touched the .tex.

**Independence.** I wrote `research/audit/A13-scripts/a13_check.py` (the construction and a brute-force check of (1)) from the text alone, before opening the authors' `scripts/construction.py`. It shares no code with `manuscripts/endpoint-min-max/scripts/`, `tools/cutfeas.c` or `tools/realis.c`. The same holds for `a13_forms.py` (Lemmas 1, 6, 7 with max-flow) and `a13_realis.py` (a new exact realisability oracle). Re-runs of the authors' script are labelled **non-independent**.

Verdicts: **SOUND**; **GAP** (fixable; the fix is stated); **ERROR** (false; a counterexample is given); **UNCLEAR** (cannot be settled from the available material).

---

## 0. Summary table

| # | Item | Verdict | Note |
|---|---|---|---|
| C1 | **Lemma 1 (four forms)**: (a) ⇔ (b) ⇔ (c) ⇔ (d) | **SOUND** | (a)⇔(b) uses b(V) = 2k; (b)⇔(c): \|δ(Y+v)\| = \|δ_{G−v}(Y)\| + d(v) − e(v,Y); (c)⇔(d): the cut {σ} ∪ X has capacity \|N(v)∖X\| + \|δ_{G−v}(X)\| + b(X). Checked on every (M, v) at n = 6 and on 78,928 (M, v) at n = 8, including the max-flow (d) (§3.3). |
| C2 | Proposition 2 (necessity by arms) | SOUND | Each end occurrence terminates ≤ 1 arm; both arms of a path through v end at its two distinct ends. |
| C3 | **Lemma 6 (signed form) and the G^v single-commodity form** | **SOUND** | b_M = 1 − x_M pointwise, \|δ_{G^v}(Y)\| = \|δ_{G−v}(Y)\| + \|Y∖N(v)\|. Gale: the cuts with finite capacity are exactly the Y ⊆ V − v. The flow version (unmarked even ≠ v → distinct marked vertices or v) matches (c) on every instance tested. Cosmetic: "because there are no isolated vertices" is not needed for b_M = 1 − x_M. |
| C4 | **Lemma 7 (parity)** | **SOUND** | \|δ_{G^v}(Y)\| = \|δ(Y)\| + \|Y\| − 2e(v,Y) ≡ \|Y ∩ Ev\|, and x_M(Y) ≡ σ_P(Y) ≡ \|Y ∩ Ev\|. Checked on every (v, Y) at n ≤ 8. |
| C5 | **Lemma 13 (good pairings ⇔ σ_P(Y) ≤ \|δ_{G^v}(Y)\| ∀ v, Y)** | **SOUND** | x_M(Y) ≤ σ_P(Y) with equality for the transversal marking outside Y. Brute force agrees on all 299 pairings at n = 6, and on every constructed pairing at n ≤ 8. |
| C6 | Lemma 14 (T-join pairing) | SOUND | Works in any graph, connected or not (handshake per component). |
| C7 | Theorem 17 (guarded route lemma) | SOUND | Token injectivity rechecked: equal edge tokens force z_p = h_{p′}, z_{p′} = h_p ∈ N(v), so h_p is a bypass that is an end of another passage, which is forbidden. |
| C8 | Corollary 18 | SOUND | K_{2,m}: q bypasses each passage ℓ_{2i−1} p ℓ_{2i}. |
| C9 | **Identity (3) (eq:split)** | **SOUND** | E(G^v) = E(F^v) ⊔ E(J − v), so δ_{G^v}(Y) = δ_{F^v}(Y) ⊔ δ_{J−v}(Y). Checked numerically on every (v, Y) of 23,354 constructions (n ≤ 8). |
| C10 | **Lemma 19 (free degrees)** | **SOUND** | d_F ≡ [w∈Ev] + [w∉Ev] = 1. For w ≠ v, deg_{F^v}(w) = d_F(w) − [vw∈F] + [w∉N(v)] is odd iff vw ∈ J. deg_{F^v}(v) = n − 1 − d(v). Asserted at every v of all 90,000+ constructions. |
| C11 | **Lemma 20 (linked transitions)** | **SOUND** | The charging is injective (§2.3). It covers every Y ⊆ V − v, hence every W, for v ∈ Ev (end edge vz, path z → v crosses δ_{F^v}(Y)) and for v odd (no bad end). Good pairs are charged to J-edges, bad pairs to F^v-edges, and these sets are disjoint. The bound has no +1. |
| C12 | Paragraph after Lemma 20 (guards are linking paths) | SOUND; GAP (incomplete), **fixed** | It said only that the guards give some of the linking paths. The guard paths are edge-disjoint. Deleting them leaves z and v as the only odd vertices of F^v, and a vertex on one route has exactly two odd vertices. So the remaining linking paths exist, and Theorem 17 is a special case of Lemma 20. One sentence added. |
| C13 | **Theorem 21 (cut selection)** | **SOUND**; GAP (one line), **fixed** | Transitions are a perfect matching of the J-edges at v, except for one end edge when v ∈ Ev. v is odd in F^v and can only be paired with a J-neighbour z. Closed trails and repeated vertices would contain a cycle of J; the justification was missing and is added. Lemma 14 needs no connectivity of F^v. Polynomial. |
| C14 | Thm 21(1): "or any other T-join that is a forest (e.g. a minimum one)" | SOUND (remark) | This is no wider: a forest T-join is the T-join of every spanning tree containing it (T-joins in a tree are unique). A minimum T-join is a forest. |
| C15 | **Computation: `scripts/construction.py` (non-independent)** | **Reproduced**; GAP (counts), **fixed** | 0 failures in every family, with exactly the printed counts. The text's "all trees of orders 8–12" means orders 8, 10, 12 with e ≥ 2 (20, 99, 538 trees, one construction each). Order 12 uses two trees per graph. Now said. |
| C16 | **Independent check of Thm 21** | **No failure** | All connected graphs of order ≤ 8 (11,229; 10,992 with e ≥ 2): 67,822 constructions. 1,133 further graphs (cycles, K_{a,b}, trees of orders 8, 10, 12, random graphs of orders 10 and 12, …): 22,660 constructions. Two F^v-pairing procedures, one of them an arbitrary random edge-disjoint pairing. Brute force on (1) for every transversal, v and W. Random pairings fail (400 of 10,893 at n = 8), so the test has teeth. §3. |
| C17 | Proposition 9 (EMM + CS₀ ⇒ Gallai) | SOUND | The pendant vertex handles odd order. |
| C18 | **Corollary 22 (EMM ⇒ Gallai)** | **SOUND as an implication; vacuous, since EMM is false**; GAP (status), **fixed** | [EMM] nowhere recorded the refutation. The abstract, §4.4 and open problem 1 said that Gallai "reduces to" the sufficiency of (1). Fixed: a status sentence after Conjecture 4, a remark after Cor 22, and wording in the abstract and open problem 1. What the proof uses: every connected even-order graph has a realisable half-set (§4). |
| C19 | **Remark 10: "CS + sufficiency ⇒ (R_s) ⇒ (R) ⇒ Gallai"** | **Correct as an implication** | CS + EMM puts every even r in a realisable half-set. Its k paths have b(r) = 2, so p(H) ≤ k for every H (not only critical H), and attaching a leaf at r gives the Lean `RootedTest` directly. Then `gallai_iff_rootedTest`. Vacuous for the same reason as C18. |
| C20 | **Strengthenings tested on the known EMM counterexamples** | **New facts** (§4.2) | (i) *Every transversal of every good pairing is realisable*: **false**. In KsOeBW??G`?A the pairing {03, 18, 45, 69, 7 10} is good, and its transversal {3, 4, 8, 9, 10} is the Thm 7.5 half-set. 4 of the 12 order-12 graphs behave like this. (ii) *Every transversal of every Thm 21 pairing is realisable*: **holds on all 12**, for every tree and every F^v-pairing (proved, §4.2). The n = 28 half-set L is never a transversal of any route-system pairing. |
| C21 | Remark "certificates and guards" | Logic SOUND; count not re-run | "31 graphs at order 8 with no guarded decomposition of a minimum T-join" was not re-run. It no longer matters (C12). |
| C22 | Remarks (1)–(2) of §4.5 | SOUND; one sentence UNCLEAR | n − 1 − d(v) = s(v) + b(v) − 1 ✓. "An apex joined to the vertices of positive slack is realised exactly, but separately for each v" has no checkable content. Left as is. |
| C23 | Theorem 11 (per-vertex matroids); matroid-intersection remark | SOUND (brief check) | λ_v is supermodular and even. ℓ_v is a supermodular projection, and g_v ≥ ⌈\|X\|/2⌉ is submodular. Edmonds; rank ≥ e/2. Intersection: ⌈a/2⌉ + ⌈(e−1−a)/2⌉ ≥ e/2. |
| C24 | Theorem 15 (cones) | SOUND (brief check) | s(u) = 0. The case u ∈ W uses \|δ(U)\| = \|δ_H(U)\| + \|U\| and d_H(v) ≤ \|δ_H(U)\| + \|U\| − 1. |
| C25 | §8 Formalisation | GAP (wording), **fixed** | `CutFeasible` and `gallai_of_emm_cs` exist on no branch (`git grep` on this branch, lean-d6-frontier and missing-move). The text read as if they did. Now "planned"; `EmmTemplate.lean` has `CutOK`. |

**Overall.** **Theorem 21 is correct.** Every step I was asked to check is SOUND:
- the forms of (1) and the G^v reduction, including parity;
- identity (3) and Lemma 19;
- the injective charging of Lemma 20;
- the path structure of the transitions in a forest;
- the pairing of v itself when v ∈ Ev;
- the existence of the F^v-pairings when F^v is disconnected.

Two independent implementations find no failure: the authors', and mine with arbitrary F^v-pairings and a brute-force check of (1) itself.

The substantive problem is one of status. EMM is false (missing-move Thm 7.5; synthesis §12), but [EMM] still presented "Gallai reduces to the sufficiency of the cut inequality" as the payoff. Corollary 22 and the chain in Remark 10 are correct implications with a false hypothesis. I recorded this in the text without changing any mathematics.

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

## 4. Corollary 22, Proposition 9 and Remark 10 after the refutation of EMM

### 4.1 What the implications use

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

### 4.2 Which strengthenings survive the counterexamples (`a13_realis.py`, `a13_mm12_pairings.py`, `a13_mm12_forced.py`, `a13_petersen28.py`)

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

The construction never marks both ends of a J-edge joining two J-degree-1 vertices. In both counterexample families, the bad half-set marks such a pair (or a pair whose complement starves a region). This fits the "never starve a region" heuristic of synthesis §13.

**Caution for the EMM_ns route of synthesis §11.** A selection that never marks a degree-2 vertex cannot exist in general. In C_n every even vertex has degree 2. In KsOeBW??G`?A, 7 of the 10 even vertices have degree 2, and a half-set needs 5 marks.

## 5. Changes made to the .tex (recompiled twice with pdflatex; 14 pp.; numbering unchanged)

Note on the build environment: `lmodern.sty` was missing on this machine. I installed the Debian package `lmodern`. With it, the unmodified source rebuilds to a PDF of exactly the committed size, and the two overfull boxes in the log already existed.

1. **Abstract.** It now says that EMM was refuted later (n = 12, missing-move Thm 7.5; n = 28). The sentence "Gallai's conjecture reduces … to the sufficiency of the cut inequality" is replaced by: the implication is vacuous as stated, and what it uses is that every connected graph of even order has a realisable half-set.
2. **After Conjecture 4.** Added: sufficiency is false in general (KsOeBW??G`?A of order 12; synthesis §12, order 28). EMM is used below only as a hypothesis.
3. **After Lemma 20.** Added: the guard paths are edge-disjoint, and the remaining linking paths exist by Lemma 19. So Theorem 17 is a special case of Lemma 20 (C12).
4. **Proof of Theorem 21.** Added the one-line reason why trails in a forest are paths and none is closed (C13).
5. **After Corollary 22.** "Gallai's conjecture reduces entirely to the sufficiency direction of EMM" is replaced by a correct statement. The construction-script counts are made precise (C15).
6. **New unnumbered remark after Corollary 22**, "what Corollary 22 uses":
   - the corollary and the Remark 10 chain are vacuous;
   - what is needed is one realisable half-set per graph;
   - "every transversal of every good pairing is realisable" is false, with the KsOeBW??G`?A witness.
7. **Open problem 1.** It no longer says that the sufficiency of EMM is "the whole of Gallai's conjecture".
8. **§8 Formalisation.** The Lean names are said to be planned, not existing; `EmmTemplate.lean` has `CutOK` (C25).

## 6. Recommendations (not done; for the authors)

1. The paper's title and framing ("An endpoint min-max conjecture") should follow the pivot of synthesis §13: the cut inequalities are necessary, always simultaneously satisfiable (Thm 21), sufficient at n ≤ 8, false at n = 12 and 28, and NP-hard to characterise. Restructuring is the authors' call; I only made the status explicit.
2. Theorem 17 can now be stated as a corollary of Lemma 20 (§2.4). Corollary 18 and the certificate tables then become illustrations.
3. State the "forced pair" observation of §4.2 as a lemma, since it explains why the Thm-21 pairings avoid both known counterexample families. A J-edge between two vertices of J-degree 1 is a route in every decomposition. In particular, two adjacent even vertices of degree 2 whose shared edge lies in J are paired.
4. For the "pairing-guided descent" test of synthesis §13, use the observation of §4.2 that on all 12 order-12 counterexamples every transversal of every Thm-21 pairing is realisable. That makes them natural first test cases.
5. The second sentence of §4.5 Remark (1) should be rewritten or removed (C22).
