# A12 — Referee audit: missing-move, and endpoint-structure §7 (barrier, flower move, receipt or flower)

Auditor: independent adversarial referee pass, 2026-11-26.

Sources audited:
- **[MM]** `manuscripts/missing-move/missing-move.tex` ("Lovász's spare path: the missing move in the Fan game"), 13 pp. after my fixes. Its scripts are in `manuscripts/missing-move/scripts/` and its outputs in `scripts/outputs/`. Numbers such as "Lemma 5.9" refer to the compiled PDF.
- **[ES]** `manuscripts/endpoint-structure/endpoint-structure.tex`, Section 7 only, "Stronger induction hypotheses, and a barrier for Fan moves": Definition 50 to Proposition 68 and the Lean paragraph after it. Sections 1–6 were audited in A9.
- **[Lean]** `lean/GallaiLean/MissingMove.lean`, `FanBarrier.lean`, `Flower.lean`, plus the definitions they use (`Insertion.lean`: `Ach`, `blankNbrs`, `Ach.addPath`; `HubPhases.lean`: `PassesAt`; `Lovasz.lean`: `lovasz_ends`). I compared statements and did not rebuild.
- Background: `research/connections.md` §N (follow-ups 5–6), §R, §S; `research/experiments.md` E13–E16; ES §5 (Lemma 15 = Fan's transfers, the passing-neighbour identity (2)).

**Version.** I started at b497409. While I worked, upstream commits ecfb34d and 74e4002 (merged as 7d3d1e4) added Lean lemmas to `MissingMove.lean` (`Ach.hub_general`, `Ach.two_hub`, `Ach.relays`, `Ach.relay_hub`), the options `simple` and `hubroot` to `fan_game.py`, and new logs. The two `.tex` files did not change. The new Lean lemmas are not described in [MM] and are not audited here. The new `fan_game.py` options leave the default behaviour unchanged, so my re-runs of the author's solver are unaffected. The parent session checkpointed my work in progress (1ec2962, 5f28d47).

**Independence.** All verdicts rest on my own re-derivations and on my own scripts in `research/audit/A12-scripts/`:
- `game.py` (a new solver for the game) and `cert_replay.py` (a new strategy-tree checker) share no code with `fan_game.py`, `certificate.py` or `tools/`.
- Exact partition checks use the A11 audit's DFS solver, `A11-scripts/exact.py`.
- Re-runs of the author's `fan_game.py` are labelled **non-independent**.

Verdicts: **SOUND**; **GAP** (fixable; the fix is stated); **ERROR** (false; a counterexample is given); **UNCLEAR** (cannot be settled from the available material).

---

## 0. Summary table

### 0.1 missing-move

| # | Item | Verdict | Note |
|---|---|---|---|
| M1 | §1 inputs (A) Lovász, (B) Fan 3.3–3.4 | SOUND | (B) is ES Lemma 15 verbatim (audited in A6, A11). Lean: `lovasz_ends`, `fan_single`, `fan_grouped`. |
| M2 | Def 1.1 (the game); soundness of every move | SOUND; GAP (citation), **fixed** | The two-even-vertex seed (b = 2 at v, 0 at u) is ES **Lemma 4** (Removing one vertex), not Lemma 3, which gives b = 2 at both. |
| M3 | Split rule: "It settles every non-critical graph" | GAP (wording), **fixed** | True for (R), false for the game. With the split rule the five E13 losers still lose at their roots with \|F\| ≤ 8, and all 47 np-losers still lose with \|F\| ≤ 4 (`out/losers5_nonp_split_k8.txt`, `out/split47_k4.txt`). |
| M4 | §1 computational facts: order 6 all won; 50 losers at n = 8, \|F\| ≤ 4; the five E13 losers at \|F\| ≤ 8; p = 3 for those five; Gqz~vw lost by the original game at root 3 with \|F\| ≤ 8; 19 of the 47 critical | **Reproduced (independent)** | Every number matches (§3). |
| M5 | **Lemma 2.1 (hub lemma)** | **SOUND** | Supplies 1 > 0, then 2 > ≤ 1 (the only neighbour of s is a). The adversary picks y. Profile identity rechecked. Lean `Ach.hub_four` states exactly this. |
| M6 | Theorem 2.2 (degree-four hubs) | SOUND | Lovász applies (≤ 1 even vertex), and 2\|D\| ≤ n − 1 forces ≤ n − 2 by parity. Lean `hub_four_ends`, `hub_four_rooted` match, including the even-vertex hypothesis. |
| M7 | Corollary 2.3 (GsRvnk) | SOUND | |
| M8 | Floor bound of G − s ⇒ (R) at a degree-4 vertex | SOUND | Lemma 2.1 accepts any seed. |
| M9 | Remark 2.4 (⌈d/2⌉ receipts; the four certificates) | SOUND | All six printed certificates replayed (§3.1). |
| M10 | **Theorem 2.5 (odd-neighbour hub)** | **SOUND** | Degrees in K: x has d − 2 (odd, ≥ 1), z has d − 1. The path y′ s x z is simple (z ∉ N[s]). Lean `hub_four_odd_ends`, `hub_four_odd_rooted` match. |
| M11 | Corollary 2.6 (Gqz~vw, root 3) | SOUND | Lean `gqzGraph` is K₈ − {03, 12, 23, 34, 56, 67}, and networkx decodes graph6 `Gqz~vw` to the same complement. Certificate replayed. {0, 3, 7} and {0, 3, 5} are realisable (exact). 4-connected. |
| M12 | **Theorem 3.1 (completeness at n = 8)** | **Reproduced exactly (independent)** | The 47-graph list at \|F\| ≤ 4 is identical to `np4_losers.g6`. Least sizes: 35 × 5, 6 × 6, 4 × 7, Guv]~{ 8 (root 2), M₈ 9. M₈ loses at every \|F\| ≤ 8. All without the split rule. |
| M13 | §3 text after Thm 3.1 | **ERROR (descriptive, no effect on any result), fixed**; GAPs fixed | "The seven dense graphs, those whose complements have at most six edges" is false: 10 of the 47 have complements with ≤ 6 edges. Gqz~vw, Gqzn~w and Gqz^~w are not among the seven. The seven are now named. Also fixed: the third repaired graph is GswNvs; the split-rule sentence; rootcheck covers A_{6,2}, B, B′, not "the order-10 examples". |
| M14 | Lemma 4.1 (rotation) | SOUND | w ≠ v because uv ∉ E(K). The b(v) paths are distinct and their predecessor edges at u are distinct. |
| M15 | **Lemma 4.2 (Fan's alternative)** | **SOUND** | Chain execution (only P₀ changes; its far side is unchanged; x₁ is not an end of P₀), Case 1, the map's injectivity, R ⊆ T ∪ N(u), and the count Σ_T b ≤ \|Z ∩ R\| all check (§2.2). Lean `fan_alternative` states exactly (a) and (b). |
| M16 | Rotation is dominated by the alternative | SOUND; GAP (wording), **fixed** | §1 said "strictly dominates". No strict example is given. |
| M17 | Proposition 4.3 (Pósa moves) | **Reproduced** (author's solver, with and without the split rule); GAP (scope), **fixed** | The stated roots stay lost (rot2/alt2 with \|F\| ≤ 4, alt1 with \|F\| ≤ 6). But the moves are not idle: with \|F\| ≤ 4 the original game loses GsRvnk at all 8 roots, and rot2 or alt2 wins 6 of them. Sentence added; §6 "add nothing" changed to "repair no losing root". |
| M18 | Lemma 5.1 (append or through) | SOUND | |
| M19 | **Proposition 5.2 (A_{6,2}), including the symmetry** | **SOUND** | \|E\| = 34. Supplies 1 > 0, 5 > 1, 4 > 2, then equality 3 = 3. The rigid case forces the fourth path to be ℓx, and 30 > 3·8. After the append and the path t′st″: 5 paths, b(s) = 4, b(t′) = b(t″) = 2 (Σb = 10). Sym(Q) fixes x, ℓ, s, s′ and acts transitively on Q; the swap s ↔ s′ is an automorphism; odd roots hold by parity. |
| M20 | Proposition 5.3 (A_{6,2} lost, star + ≤ 3) | **Reproduced (independent, no rf)** | No root wins. "A loss at x means no play wins" is correct: x is odd, so every completed play has an end at x. |
| M21 | §5 families: A_{4,4}, B, B′ | **Reproduced (independent)** | A_{4,4}: twins need star + 2. B: star + 1. B′: all roots lost at star + ≤ 2, all won at star + 3, with the printed held set. Typo "would not have refute" fixed. |
| M22 | Lemma 5.4 (flowers) | SOUND | |
| M23 | Proposition 5.5 (M₈) | SOUND | 24 edges, cycles of ≤ 8 edges, so all Hamiltonian. The transversal s a w z has distinct vertices. "The fourth receipt always fails": b(s) = 4 > \|D\| = 3 is impossible. |
| M24 | **Lemma 5.6 (transversals, j ≤ 4), k = 4 case** | **SOUND** | At step 3 there are four candidates and at most one is a₀. A C_A-choice fails only if a₃ is the unique common C_B-neighbour of a₀, a₁ (N ≥ 9 > 4), and symmetrically, so at most 2 of ≥ 3 choices fail. This is stronger than ES Prop 64: the path starts at u. |
| M25 | Lemma 5.7 (flower move); option `flower` | SOUND | The opponent chooses among all paths of length j from u in H + uT, a superset of the transversals, so the move is conservative. |
| M26 | Proposition 5.8 | Partly reproduced (author's solver) | CP(4), CP(5) won with one star with `flower`, lost without. A_{6,2}, B′ lost with `flower` at star + 0. The dense-graph and sample parts were not re-run. |
| M27 | **Lemma 5.9 (receipt or flower with a count): λ and μ** | **SOUND** | λ: a T-path has ends t, u, so it avoids Λ (degree-1 vertices outside T ∪ {u}). μ: other paths avoid u (b(u) = d_H(u)), so they have ≤ \|V⁺\| − 2 edges; the leaf case gives exactly 1. Equality makes every T-path Hamiltonian on V⁺ − Λ. Examples: A_{6,2} 31 > 25; B′ 31 = 24 + 7; CP(m) equality; Inv~\|~zbw 33 < 35. All recomputed. |
| M28 | **Proposition 5.10 (rf + orbit)** | **Reproduced (independent rf implementation)** | A_{6,2} and B′: with rf and no orbit rule, every root but the core; with the orbit rule, every root. CP(4), CP(5): every root. Inv~\|~zbw roots 2, 3: lost at star + ≤ 2 with or without rf; won at star + 3. The other nine sample graphs were not re-run. |
| M29 | Inv~\|~zbw paragraph | SOUND; GAP (wording), **fixed** | Five even vertices after isolating 2; only 9 after also holding 10 and 64; \|E(H)\| = 33; 3·9 + 8 = 35. The certificate's new path is "4 3 6 2 8 or 4 3 6 2 7" only in two of four leaves. Every leaf has ends at both 2 and 3, so the same certificate wins at root 3. Text fixed. |
| M30 | §6 Consequences | SOUND; item 3 softened (M17) | |
| M31 | §7 Lean list vs files | SOUND; GAP (stale), **fixed** | Every cited name exists and matches. "The flower and transversal lemmas are not formalised … being formalised" was stale: `Flower.lean` now has `flower_decomp`, `cocktail_passes_four` and `cocktail_passes_of_rt`. |
| M32 | Cited logs `crit47.log`, `famhub_B2_3.log`, `rf_sample.log` (and the other `.log` outputs of `run_all.sh`) | **GAP (reproducibility)**, text fixed | They are not in the repository: `.gitignore` has `*.log`, and they were never committed. I regenerated every load-bearing one independently (§3). §7 now says the logs must be regenerated. |

### 0.2 endpoint-structure §7

| # | Item | Verdict | Note |
|---|---|---|---|
| E1 | Def 50 (prescribed descent) | SOUND | The up-set reformulation is checked. |
| E2 | Lemma 51 (prescribed transfer), both directions | SOUND; Lean scope note **added** | Z_D(y) = N_K(y) ∩ (Ev(K) − S) = ∅ ⇔ N_E(y) − a ⊆ S. Lean covers only the case of Cor 52 (`desc_succ_of_transfer_two`); the converse is not formalised. |
| E3 | Corollary 52 (two even neighbours reduce) | SOUND | ya is not a bridge (bridges at y are pendant, d(a) ≥ 2). Lean `branchBase_of_three` and `gallai_of_branchBase3` match. |
| E4 | Example 53 (Gqz~vw) | SOUND; **all claims reproduced** | Critical. All 20 triples realisable. In G − 31 all 6 pairs are realisable, and likewise for 35 and 37. The original game loses root 3 with \|F\| ≤ 8. |
| E5 | Remark 54 | SOUND | GsaEDo: critical, e = 6; for each a ∈ {2, 3, 4} the pair N_E(7) − a is not realisable in G − 7a (exact). The count "22 of 275" was not re-run. |
| E6 | Def 55 (oracle game) | SOUND | |
| E7 | Remark 56 (oracle table) | Table not re-run; checkable parts SOUND | 44,008 even roots ✓. "M₈ loses for every F" follows from Cor 58 ✓. All 70 half-sets of M₈ are realisable (one per Aut-orbit, exact) ✓. |
| E8 | **Theorem 57 (last-edge barrier), (1) and (2)** | **SOUND** | u, t ∉ N^ev; every non-blank even neighbour has ≥ 2 ends; \|Z\| ≤ b(t) − 1 and b(t) ≤ \|D\|. Lean `fan_transfer_barrier` and `insertion_barrier_regular` match. The remark on d > (3n − 2)/4 is correct. |
| E9 | **Corollary 58** | **SOUND**; GAP, **fixed** | (1) 3\|D\| ≥ 4m − 3 > 3m. (2) \|F\| ≥ m − 1. The closing paragraph asserted a partition into *exactly* m − 1 paths, but the proof gave only ≤ m − 1. Added: with ≤ m − 2 paths, (2) gives \|F\| ≥ 3m − 2 > 2m − 1, more than a path can carry. Lean `cocktail_fan_barrier` (which also proves m ≤ \|D\|) and `cocktail_insertion_barrier` match. |
| E10 | Remark 59 | SOUND; GAP (wording), **fixed** | "The remaining 21 edges form three Hamiltonian paths" needs a new path of exactly 3 edges. |
| E11 | Lemma 60 (flowers) | SOUND | Stated for the collection. It is a partition when the cycles are edge-disjoint; Lean `flower_decomp` forces this through the multiset identity with E(G). |
| E12 | **Proposition 61 (equality forces a flower)** | **SOUND** | Lean `hub_cycles` matches: paths from s, targets = T as a multiset, edges = E(H). |
| E13 | Receipt bullets after Prop 61 | SOUND | Supply d(s) − j against j blanks. In this setting the receipt at equality never succeeds (b(s) would exceed \|D\|), so "either a further receipt succeeds" is vacuous here. Harmless. |
| E14 | Theorem 62 (flower move) | SOUND | |
| E15 | **Theorem 63 (CP(m) from transversals)** | **SOUND**; GAP (indexing), **fixed** | 2m(m − 1) = (m − 1)·2m. The receipt count is now "after j receipts the next has supply 2m − 2 − j against j". Lean `cocktail_passes_of_rt` and `cocktail_rooted_of_rt` take `RainbowTransversal (m−1)` on 2(m − 1) + 2 = 2m vertices, which is the paper's hypothesis. |
| E16 | **Proposition 64 (transversals, k ≤ 4); the k = 4 rotation** | **SOUND**; GAP (scope of Lean), **fixed** | a₂ a₃ s a₁ x: x ≠ s (sa₁ ∈ C₁), x ≠ a₃ (a₁a₃ ∈ C₄), x ≠ a₂; the colours are C₃, C₄, C₁, C₂. "On a common vertex set" added. Lean `rainbowTransversal_three` and `_four` hold only on 8 and 10 vertices (k = 3, 4); text now says so. |
| E17 | Corollary 65 (CP(4), CP(5)) | SOUND | Lean `cocktail_passes_four` and `_five` (`PassesAt` = ≤ n/2 paths and ≥ 2 ends at s). |
| E18 | Question 66 and "What is known" | Literature not audited; computations not re-run | |
| E19 | **Theorem 67 (receipt or flower)** | **SOUND**; GAPs **fixed** | "s ∉ T" added. The cross-reference "as in Corollary 58" for Hamiltonicity is wrong; it is Theorem 63. Lean `flower_decomp_rest` is the recombination only, as the text says. |
| E20 | "Eulerian, d(s) = n − 2" remark | SOUND | d(s) = n − 1 is impossible, since Σb would be odd. |
| E21 | **Proposition 68 (B′): 31 = 3·8 + 7 and Hamiltonicity** | **SOUND** | \|E(B′)\| = 35 and \|E(H)\| = 35 − 7 + 3 = 31. In the rigid case the three T-paths avoid ℓ (≤ 8 edges each), and R avoids ℓ and x₁, since all three edges at x₁ end T-paths (≤ 7 edges). Equality makes the C_t Hamiltonian on V − ℓ. a₁ ∈ U is automatic (N_H(x₁) ⊆ U). x₁ℓ is appended at the end x₁ of L. Both cases give 5 paths with b = 2 at a core vertex; then Sym(U). |
| E22 | A_{6,2} sentence after Prop 68 | GAP (stale), **fixed** | "[MM] lists [the core roots] as open" is no longer true: MM Prop 5.2 now includes them. |
| E23 | Lean paragraphs of §7 | SOUND | Every name exists; no `sorry` in the three files or their imports. |

**Overall.** I found **no mathematical ERROR** in either paper. The one ERROR is a false description of which graphs were run by orbits (M13). It affects no result and is fixed.

Every lemma, proposition and theorem I was asked to check is SOUND:
- the hub lemma and the odd-neighbour hub;
- Fan's alternative;
- Prop 5.2, including the symmetry that settles the core roots;
- the flower lemma, and the transversal lemmas for ≤ 4 cycles, including k = 4;
- "equality forces a flower";
- the last-edge and insertion barriers;
- Theorems 63 and 67, and Prop 68 with its count 31 = 3·8 + 7;
- Lemma 5.9 with its bounds λ and μ.

I re-ran three load-bearing computations with an independent solver. Each matches the text exactly:
- Theorem 3.1, in full;
- Gqz~vw at root 3 with \|F\| = 5;
- K₈ − PM: lost at \|F\| ≤ 8, won at \|F\| = 9.

So do the n = 10 family claims, the rf / orbit claims and every printed certificate.

The GAPs are citations, wording and stale cross-references. All of them are fixed in the .tex, and both papers recompile cleanly. The one substantive reproducibility issue is that the cited `.log` files are not in the repository.

---

## 1. missing-move: proofs

### 1.1 Hub lemma, degree-four hubs, odd-neighbour hub

- **Lemma 2.1.** s is isolated in K, so Z_D(s) = ∅.
  - The single transfer sa has supply b(a) ≥ 1 > 0.
  - Then N(s) = {a} in K + sa, so \|Z\| ≤ 1, while b(c) + b(d) ≥ 2 (c, d ≠ a are untouched). The grouped transfer {c, d} is legal, and the opponent picks y.
  - Finally y′ s x is a path in held edges (y′ ≠ x, both ≠ s).
  - Profile: b + 2e_s − e_a − e_y + e_{y′} + e_x. Since b_D(s) = 0, we get b′(s) = 2. Since x ∉ {a, y, y′}, b′(x) = b(x) + 1.
- **Theorem 2.2.**
  - Even vertices of positive degree in K = G − star(s): the even vertices of G outside N[s] (≤ 1). N(s) becomes odd, and s has degree 0.
  - Lovász gives b = 1 on N(s) and 2\|D\| = \|Od(K)\| ≤ n − 1, hence ≤ n − 2.
  - Lemma 2.1 with x = r (or any x if r = s) gives b(s) = b(x) = 2 and \|D′\| ≤ n/2.
- **Theorem 2.5.**
  - K = G − {sa, sc, sd, sx, xz}. Here a, c, d are odd. x has odd degree d(x) − 2, and d(x) ≥ 3 because x ~ s, z. z has odd degree d(z) − 1.
  - The even vertices of positive degree in K are those of G outside N[s] ∪ {z} (≤ 1).
  - Steps 1–2 of Lemma 2.1, then the path y′ s x z, whose vertices are distinct since z ∉ N[s]. Then b(s) = b(z) = 2 and x stays interior.
- **Corollary 2.6.** s = 3, N(3) = {1, 5, 6, 7}, x = 6 (degree 5), z = 0 (06 ∈ E, 03 ∉ E, degree 6). The only even vertex outside N[3] ∪ {0} is 4. The replay (§3.1) shows the play exactly as printed: supplies 1 > 0 and 2 > 1 (blank 1), and final profiles realising {0, 3, 7} and {0, 3, 5}.

### 1.2 Fan's alternative (Lemma 4.2)

I checked each step against the chain definition.
- **Executing a chain.** Rotating P₀ = x₀ ⋯ x₁ u ⋯ y gives x₁ ⋯ x₀ u ⋯ y. Only P₀ changes, and the edge x₁u is replaced by x₀u.
  - x₁ lies strictly between x₀ and u, so it is not an end of P₀. Hence P₁ ≠ P₀, and P₁ is unchanged.
  - A later step can use P₀ only from its far end y, by distinctness. Its predecessor of u read from y is unchanged.
  - In K′ = K + x₀u − x₁u the vertex x₁ is a non-neighbour of u, so the induction applies (the start of a chain needs only that). The composite is K + x₀u − x_ku with profile b − e_{x₀} + e_{x_k}.
- **Case 1.** The avoiding path Q ends at x_k and avoids u, so it is none of the rotated paths and survives the execution. Appending x_k u restores the deleted edge, giving K + tu with b + e_u − e_t.
- **Case 2.**
  - R ⊆ T ∪ N(u): every x_i with i ≥ 1 is a predecessor of u. Also T ⊆ R (k = 0), and u ∉ R.
  - The map (P, x) ↦ uπ_P(x) lands in R, by chain extension or truncation, and is injective.
    - Paths are edge-disjoint.
    - If both ends of P lie in R, then u is interior to P and the two edges at u differ.
    - If one end is u, only the other end is in the domain.
  - Hence Σ_T b + Σ_{N(u)∩R} b ≤ \|N(u) ∩ R\|, so Σ_T b ≤ \|Z ∩ R\|.
  - Each z ∈ Z ∩ R is the end of a chain with k ≥ 1 whose first step uses a path ending at t, so b(t) ≥ 1.
- **Lean.** `fan_alternative` states (a) and (b) with exactly these quantifiers. (b) asserts Σ_T ends ≤ \|W\|, with W ⊆ blank neighbours and an activation for every z ∈ W.

### 1.3 Degree six: Prop 5.2, the flower, Lemmas 5.6, 5.7 and 5.9

- **A_{6,2}.**
  - Q = K₆ gives 15 edges, x gives 6 + 1, and s, s′ give 12, so \|E\| = 34. Degrees: q has 8, x has 7, s and s′ have 6, ℓ has 1.
  - In K = G − star(s), Lovász gives 4 paths with b = 1 on Q ∪ {x, ℓ}, leaving one path spare.
  - The receipts have supplies 1 > 0, 5 > \|{y₁}\| and 4 > \|{y₁, y₂}\|. The fourth has 3 = 3.
  - Rigid case: the three T-paths are exactly the three s-paths, and the fourth path is ℓx. Then 30 edges in three paths avoiding ℓ (≤ 8 edges each) is impossible.
  - Final partition: b(s) = 4 and b(t′) = b(t″) = 2.
  - Sym(Q) (fixing x, ℓ, s, s′) and the swap s ↔ s′ are automorphisms, so a partition with b(q′) = 2 maps to one with b(q) = 2 for any q ∈ Q. **The symmetry argument for the core roots is correct.**
- **Lemma 5.6, j = 4** (§0, M24). The argument needs N ≥ 5 for "two vertices have at most one common neighbour on C". N ≥ 2j + 1 = 9 supplies it.
- **Lemma 5.9.** Re-derived from ES Theorem 67:
  - If the append fails, the j paths at u are exactly the T-paths, and the others avoid u (b(u) = d_H(u)).
  - Λ-vertices can only be ends, so the T-paths avoid Λ: λ = \|V⁺\| − \|Λ\| − 1.
  - Other paths avoid u, so each has ≤ \|V⁺\| − 2 edges.
  - If m′ = 1 and the remaining ends are a leaf ℓ of H and its H-neighbour q, the path starts ℓ q and must end at q, so it is the edge ℓq.
  - Equality forces every bound, so each C_t is a Hamiltonian cycle on V⁺ − Λ, and Lemmas 5.6 and 5.4 finish.
  - The author's `rf` code (read line by line) matches this. It treats m′ = 1 with both remaining ends at one vertex as μ = −∞, which is sound because such a path cannot exist. With m′ = 0 it omits the append branch in case (b), which is also sound: every path ends at u.

---

## 2. endpoint-structure §7: proofs

### 2.1 Barrier (Thm 57, Cor 58)

- **(1)** 2\|D\| = Σb ≥ b(u) + b(t) + 2\|N − Z\| ≥ b(u) + b(t) + 2\|N\| − 2(b(t) − 1) ≥ b(u) + 2\|N\| + 2 − \|D\|.
- **(2)** \|E(G)\| − \|F\| ≤ (n − 1)\|D\|.
- **Cor 58.**
  - In CP(m) − ut, u has 2m − 3 neighbours, all of degree 2m − 2 (even), and b(u) ≥ 1. Then 3\|D\| ≥ 4m − 3 > 3m for m ≥ 4.
  - With \|D\| ≤ m − 1: 4m(m − 1) ≤ 2(m − 1)(2m − 1) + 2\|F\|, so \|F\| ≥ m − 1.
  - The last move of a play cannot be a grouped transfer with \|T\| ≥ 2 (it leaves held edges), and a single transfer contradicts (1). So it is a new path through all remaining held edges F.
  - Added to the text: \|D\| = m − 1 exactly, since ≤ m − 2 paths would force \|F\| ≥ 3m − 2 > 2m − 1.
- **Lean.** `cocktail` is `Adj a b := a.1 ≠ b.1` on Fin m × Bool, that is K_{2m} minus {(i,0),(i,1)}. `cocktail_fan_barrier` gives m ≤ \|D\|, and m < \|D\| under Fan's condition. `cocktail_insertion_barrier` gives \|D\| + 1 ≤ m ⇒ m − 1 ≤ \|F\|. Both match the paper.

### 2.2 Flower, CP(m), transversals

- **Prop 61.** Σb = 2\|T\| gives \|D\| = \|T\|. Each path has ≤ 1 end at s, so each has exactly one. The remaining ends are one per t. P_t has ≥ 2 edges because st ∉ E(H), so C(P_t) is a cycle.
- **Thm 63.**
  - CP(m) − star(s) has 2m − 2 vertices of degree 2m − 3, and the antipode is the only even vertex. Lovász gives m − 1 paths with b = 1 on N(s).
  - Receipts: supply 2m − 2 − j against j blanks, for j = 0, …, m − 2. At j = m − 1 there is equality.
  - The cycles have 2m(m − 1) edges in total and ≤ 2m each, so they are Hamiltonian.
- **Prop 64, k = 4.** As in §0 (E16). All five vertices of a₂ a₃ s a₁ x are distinct: a₃ ∉ {s, a₁} by choice, a₂ ≠ s since sa₁ ∈ C₁, and x as in E16.
- **Lean `RainbowTransversal k`.** It quantifies over vertex types of size 2k + 2, k Hamiltonian paths from s, and Nodup of the cycle edges (edge-disjointness). `Transversal` asks for a path through s whose edge multiset is one cut edge per cycle. With k = m − 1 this is exactly Thm 63's hypothesis.

### 2.3 Receipt or flower, and B′

- **Thm 67.** If (1) fails, every T-path contains s. Since b(s) = d_H(s), no path passes through s, so each T-path ends at s. The T-paths are distinct (one end in T each), and Lemma 60 applies with the other paths unchanged.
- **Prop 68.**
  - U = K₆ gives 15 edges, x₁ gives 6 + 1, x₃ and x₄ give 12 + 1, so \|E\| = 35. Degrees: U has 8, x₁, x₃, x₄ have 7, ℓ has 1.
  - Lovász on B′ − star(x₁): 8 odd vertices, so 4 paths.
  - Receipts: 1 > 0, 5 > 1, 4 > 2. The ends are then b(x₁) = 3 = d_H(x₁), T (3 vertices), x₃ and x₄; \|E(H)\| = 31.
  - Case (1) ends with b = (x₁: 3, t: 0, t′, t″: 2, ℓ: 1, x₃, x₄: 1), Σ = 10.
  - Case (2): bounds 8, 8, 8, 7 (R avoids x₁ and ℓ). The flower gives 5 paths with b = 2 on {x₁, a₁, a₂, a₃}. Appending x₁ℓ to L at its end x₁ keeps 5 paths, with b(x₁) = 1 and b(a₁) = 2.
  - **The count 31 = 3·8 + 7 is right, and it does force the C_t to be Hamiltonian on V − ℓ.**
- **Thm 67 with a Lovász seed.** The "Eulerian, d(s) = n − 2" reading is right. Ends only on N(s) means every vertex outside N[s] is even, and at most one has positive degree, so d(s) ≥ n − 2. d(s) = n − 1 would make \|Od(K)\| = n − 1 odd.

---

## 3. Computations

### 3.1 Printed certificates (`cert_replay.py`, independent)

All ten strategy trees parse and replay (`out/cert_replay.txt`):
- `certificate_Gqz.txt`, `certificate_K8M.txt`, `certificate_B2.txt`;
- `certificate_miss1.txt`, at root 2 and at root 3;
- the six trees of `certificates.txt`.

At every node the replay checks:
- the held edges are edges of G, and the seed is a Lovász or Lemma-4 seed of K;
- every printed b(t), Z(u) and Σ_T b equals the value recomputed in the current graph, and every move is legal;
- every grouped transfer prints a branch for exactly the donors with b ≥ 1;
- every new path is simple, uses held edges and stays within budget;
- every leaf has no held edge, Σb ≤ n and b(r) ≥ 1.

The [MM] descriptions of these plays match the trees (relay, receipts, donation, new path 1 4 2 0 7 for M₈; 0 2 1 6 5 for B′), apart from the Inv~\|~zbw wording fixed in M29.

### 3.2 Re-runs against the text

| Claim (text) | Log cited | My run (A12-scripts) | Match |
|---|---|---|---|
| n = 6: original game wins every root (\|F\| ≤ 4) | E13 | `out/conn6_nonp_k4.txt`: 112 graphs, 0 losing | ✓ |
| n = 8, \|F\| ≤ 4: original game 50 losers, np 47; repaired: GsRvnk, Gqrvn[ (+1) | `np4_losers.g6` | `out/sweep8_{nonp,np}_k4.txt`: 50 and 47; **the 47 list is identical to `np4_losers.g6`**; the third repaired graph is GswNvs | ✓ |
| Thm 3.1 least sizes 35/6/4/1/1, Guv]~{ at one root, M₈ 9 (no split rule) | `step_np.log`, `dense7_orbits.log`, `k8pm.log` (not in repo) | `out/least47_k5to9.txt`: sparse 40 = 35 × 5 + 5 × 6 (GqjV^[, Gqz^~w, Gqzn]{, Gqzvm{, Gs`~~w); dense: Gut~vs 6; Gut~~w, Gu^v~w, Guv]}{, Guv]z{ 7; Guv]~{ 8 at root 2 only; `out/k8pm.txt`: M₈ every \|F\| ≤ 8 lost at every root, \|F\| = 9 won | ✓ exact |
| Split rule changes nothing in §3 | — | `out/split47_k4.txt` (47 still lost), `out/least_sparse40_split.txt` (same least sizes); the 7 dense graphs are critical (≥ 22 edges), so the rule cannot fire | ✓ (text now says so) |
| The five E13 losers lose at \|F\| ≤ 8 at GsRvnk 2, 3; GsZvnk 4; Gqrvn[ 2; Gqzvn[ 4; Gqzl\|{ 1 | E13 | `out/losers5_nonp_k8.txt` (and with split: same roots) | ✓ |
| Five losers non-critical (p = 3) | crit (§S) | `partitions.py`: explicit 3-path partitions | ✓ |
| 19 of the 47 critical | `crit47.log` (not in repo) | `out/crit47.txt`: 11 by exhaustive search + 8 by edge count (≥ 22 > 3·7) = 19 | ✓ |
| Gqz~vw root 3: np needs \|F\| = 5 (F = star(3) + 06); original game loses with \|F\| ≤ 8 | `certificate_Gqz.txt`; "rerun of E13" | `out/gqz_original.txt` | ✓ |
| Prop 4.3: rot2 (\|F\| ≤ 4), alt2 (\|F\| ≤ 4), alt1 (\|F\| ≤ 6) repair none of the six roots | `rot2_k4.log` etc. (not in repo) | author's solver, re-run with the split rule on (current code) and off (patched copy): the same losing roots | ✓ (non-independent); see M17 for the other roots |
| Prop 5.3: A_{6,2} lost at every root, star + ≤ 3 | `famhub_A62_3.log` (not in repo) | `out/hubruns.txt` | ✓ |
| A_{4,4} twins need star + 2; B star + 1; B′ lost at star + ≤ 2, won at star + 3 with star(x₁) + core triangle | `fam_np.log`, `famhub_B2_3.log` (not in repo) | `out/hubruns.txt`, `out/hubruns_A44_B.txt` | ✓ |
| Prop 5.8: CP(4), CP(5) won with one star and `flower`, lost without | `cp_flower.log` (not in repo) | author's solver (`out/author_reruns/rf_families_rerun.txt`) | ✓ (non-independent) |
| Prop 5.10: rf, no orbit: A_{6,2}, B′ lose exactly the core roots; with orbit every root; CP(4), CP(5) every root | `rf_families.log` (not in repo) | independent rf (`out/rf_checks.txt`) and author's solver | ✓ |
| Inv~\|~zbw = K₁₀ − {02, 17, 19, 24, 29, 39, 58}, 6-connected, 8 even vertices; roots 2, 3 lost at star + ≤ 2 with or without rf; won at star + 3 (F = star(2) + 01, 34, 36) | `rf_sample.log`, `miss1_k3.log` (not in repo) | `out/rf_inv.txt`, `out/hubruns.txt`; the certificate replays at roots 2 and 3; critical by edge count (38 > 4·9) | ✓ |
| ES Rem 56: 44,008 even roots; 70 half-sets of M₈ realisable | E15 | direct count; `out/es7_checks.txt` | ✓ |
| ES Rem 56 table (oracle game), Rem 54 "22 of 275", ES Question 66 evidence, MM Prop 5.8 dense/sample parts, MM Prop 5.10 nine sample graphs | various | not re-run | — |

The text's options match the runs. Thm 3.1 is stated "without the split rule", and my independent runs use none. The author's current `fan_game.py` always applies the split rule, but this makes no difference to any §3 number. That is now said in §7.

---

## 4. Lean (statements only; not rebuilt)

- **MissingMove.lean.**
  - `Ach.hub_four` is Lemma 2.1, with the profile identity stated without subtraction.
  - `hub_four_ends` is Thm 2.2. Its even-vertex hypothesis is `#(Ev ∩ {v ≠ s, ¬ s ~ v}) ≤ 1`.
  - `hub_four_rooted` is the private-leaf form pathNumber(G + leaf at r) ≤ n/2, for r = s or r ∈ N(s).
  - `hub_four_odd_ends`, `hub_four_odd_rooted` are Thm 2.5, with all its hypotheses: x odd; the others even; xz ∈ E; z ∉ N[s]; z even; ≤ 1 even vertex outside N[s] ∪ {z}.
  - **`gqzGraph`** is `a ≠ b ∧ ab ∉ {03, 12, 23, 34, 56, 67}`, exactly K₈ minus those six edges, and equal to graph6 `Gqz~vw` (checked with networkx). `gqz_rooted_three` is pathNumber(addLeaf gqzGraph 3) ≤ 4.
  - `fan_alternative` is Lemma 4.2 (§1.2).
  - No `sorry` (grep over all of `lean/GallaiLean`). The new lemmas `hub_general`, `two_hub`, `relays` and `relay_hub` are not in [MM].
- **FanBarrier.lean.**
  - `desc_succ_of_transfer_two` is the case P = {y} of Lemma 51 used in Cor 52.
  - `BranchBase3 k` is `BranchBase k` restricted to y with three distinct even neighbours, with the same bridge condition.
  - `branchBase_of_three` and `gallai_of_branchBase3` match Cor 52.
  - `fan_transfer_barrier` and `insertion_barrier_regular` match Thm 57.
  - `cocktail`, `cocktail_fan_barrier` and `cocktail_insertion_barrier` match Cor 58 (§2.1).
- **Flower.lean.**
  - `flower_decomp` (Lemma 60) and `flower_decomp_rest` (the recombination of Thm 67(2)).
  - `hub_cycles` (Prop 61).
  - `Transversal`: a path *through* s.
  - `RainbowTransversal k`: Hamiltonian, edge-disjoint, on 2k + 2 vertices.
  - **`PassesAt G r`** := ∃ D, \|D\| ≤ \|V\|/2 ∧ 2 ≤ D.ends r, which is the two-end test.
  - `cocktail_passes_of_rt` (m ≥ 4, RT(m − 1) ⇒ PassesAt at every s) and `cocktail_rooted_of_rt` are Thm 63, with Lovász and Fan from the library.
  - `rainbowTransversal_three` and `rainbowTransversal_four` are Prop 64 **only for k = 3 on 8 vertices and k = 4 on 10 vertices**. Text fixed.
  - `cocktail_passes_four` and `cocktail_passes_five` are Cor 65.
- **Not formalised.**
  - [MM]: Prop 5.2; Lemma 5.6 in its "starting at u" form (the form the game's `flower` and `rf` moves rely on); Lemmas 5.7 and 5.9.
  - [ES]: the dichotomy of Thm 67; Lemma 51 in general and its converse.

---

## 5. Changes made to the .tex (each recompiled twice with pdflatex)

`missing-move.pdf`: 13 pp., no warnings. `endpoint-structure.pdf`: 25 pp. Its two overfull boxes are pre-existing, in §§3 and 6.

**missing-move.tex**
1. Def 1.1: the two-even-vertex seed is ES **Lemma 4**, not Lemma 3.
2. §1: the split rule makes (R) trivial for non-critical graphs, but the game must still reach Σb ≤ n − 2. The five graphs still lose with \|F\| ≤ 8.
3. §1 Results: "strictly dominates" → "dominates" (no strict example is given).
4. §3:
   - the third repaired graph (GswNvs) is named;
   - the seven dense graphs are named, and the false characterisation by complement size is replaced;
   - the split-rule sentence is corrected (the game's results are unchanged);
   - rootcheck's scope is stated as A_{6,2}, B, B′.
5. After Prop 4.3: rotations and Fan's alternative win GsRvnk at six other roots with \|F\| ≤ 4. The original game needs \|F\| = 6 there.
6. §5, B′: "would not have refute" → "refuted".
7. Lemmas 5.7 and 5.9: T ∌ u.
8. Inv~\|~zbw paragraph: the donor-4 branches of the certificate are described, and the certificate also wins at root 3.
9. §6 item 3: "add nothing" → "repair no losing root".
10. §7 Lean: the stale sentence is replaced by what `Flower.lean` formalises. The transversal lemmas there are the cases j = 3, 4 on 8 and 10 vertices, in the "through u" form.
11. §7 Scripts:
    - the options `flower`, `rf` and `orbit` are listed;
    - the split rule is noted as always on and harmless;
    - the missing scripts are listed;
    - the cited `.log` files are said to be git-ignored and to need regenerating.
12. `\sloppy` in §7, to remove two overfull lines.

**endpoint-structure.tex (§7 only)**
1. Lean note after Cor 52: Lemma 51 is formalised only in the case P = {y}; its converse is not formalised.
2. Cor 58 proof: added the last step, which shows the partition has exactly m − 1 paths.
3. Remark 59: the 21-edge statement assumes a new path of exactly 3 edges.
4. Thm 63: receipt indexing ("after j receipts the next has supply 2m − 2 − j against j").
5. Prop 64: "on a common vertex set".
6. Thm 67: "s ∉ T".
7. After Thm 67: "as in Corollary 58" → "as in Theorem 63".
8. After Prop 68: the stale "[MM] lists as open" is corrected.
9. Lean paragraph: `rainbowTransversal_three` and `_four` are the cases k = 3 on 8 vertices and k = 4 on 10 vertices.

## 6. Recommendations (not done; for the authors)

1. Commit the `.log` files cited in [MM]: crit47, famhub_*, rf_sample, rf_families, cp_flower, step_np, dense7_orbits, k8pm, the rot/alt logs. Use `git add -f`, or rename them to `.txt`. Better still, cite this audit's regenerated outputs.
2. `fan_game.py` docstring and `run_all.sh`: say that the split rule is always on. Correct "Lemma 3" to ES Lemma 4.
3. [MM] relies on Lemma 5.6 in the "starting at u" form: the `flower` and `rf` options enumerate only paths from u. Either formalise that form, or note that `Flower.lean` has only the "through s" form on 2k + 2 vertices.
4. The new Lean lemmas in `MissingMove.lean` (`hub_general`, `two_hub`, `relays`, `relay_hub`) and the n = 8 "root-centred hub" logs are not yet in [MM]. Audit them when they are written up.
5. connections §S still carries the annotation "*Not reproduced … An independent run leaves 6 critical losers*". With \|F\| ≤ 6 that is consistent with Thm 3.1: the six graphs needing 7, 8 or 9 are exactly those. The annotation should be replaced by a pointer to this audit, which reproduces Thm 3.1 in full.
