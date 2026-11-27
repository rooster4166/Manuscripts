# A16 — Referee audit: route-descent ("Route descent: transversal realisability, minimum T-joins, and Lovász decompositions that separate vertices")

Auditor: independent adversarial referee pass, 2026-11-27.

Sources audited:
- **[RD]** `manuscripts/route-descent/route-descent.tex` at base commit **b9853bd** (branch `claude/quirky-dirac-d9km1q`; the .tex was last changed in 134d592 / ae9d3a1). I did not edit the manuscript.
  - Numbers are those of the committed PDF (pdftotext), which match the `\label` order: Theorem 2 (`thm:lovasz`), Lemma 3 (`lem:fan`), Definition 4, Lemmas 5–9 (`lem:basic`, `lem:up`, `lem:hered`, `lem:base`, `lem:ext`), Proposition 10 (`prop:spine`), Lemma 11 (`lem:min`), Corollary 12 (`cor:triv`), Remark 13, Proposition 15 (`prop:rr`), Conjectures 16 (RR) and 17 (L_N), Proposition 18, Theorem 19 (`thm:sep`), Corollary 20 (`cor:L1`), Theorem 21 (`thm:L1`), Corollaries 22 (`cor:onepair`) and 23 (`cor:packedroutes`), Example 24, Remark 25, Theorem 26 (`thm:isolated`), Definition 27, Theorem 28 (`thm:schedule`), Corollary 29 (`cor:upm`), Conjectures 30 (msep) and 31 (ball).
  - **Name clash.** RD's own "Theorem 21" is L₁. "Theorem 21 of [EMM]" and "Thm-21 system" refer to EMM's cut-selection theorem (`thm:ps`, Theorem 21 in the EMM PDF).
- **External statements.**
  - Fan, JCTB 93 (2005), Lemma 3.4: through the verbatim restatements collected in A7 §1a (Botler–Sambinelli Lemma 6 and Definition 1).
  - Lovász (1968): through the standard statement "u/2 + g − 1 paths for g ≥ 1 even vertices", and the Lean `lovasz_ends`.
  - EMM: `manuscripts/endpoint-min-max/endpoint-min-max.tex`, Lemmas 19 and 20, Theorem 21, §4.4.
  - The Fan schedules: `manuscripts/endpoint-structure/endpoint-structure.tex`, §"Fan certificates", and Lean `TwoEven.lean` (`FanSchedule`, `realisable_of_fanSchedule`).
- **Evidence.** `research/experiments.md` E20, `research/synthesis.md` §§17–18, and `manuscripts/route-descent/README.md`.
- **Lean**, used only to cross-check statements: `Separation.lean`, `FanSupport.lean`, `RouteDescent.lean`, `RouteSystem.lean`, `OnePair.lean`. Lean is not installed in this container, so I did not rebuild.

**Independence.** I wrote everything in `research/audit/A16-scripts/` from the text of RD alone. It is pure Python and imports nothing from `manuscripts/route-descent/scripts/`. `a16_core.py` contains:
- an independent path-partition checker;
- an exhaustive enumerator of all path partitions with a prescribed profile, by transition systems;
- a line-by-line implementation of the proof of Lemma 3 (chain by BFS or by long random chains, re-routing, append), which asserts every claim of the lemma at every step.

`a16_sep_test.py` runs the proof of Theorem 19 (Cases I–IV) as a recursive algorithm, with random choices wherever the proof says "choose any". It asserts every intermediate claim, and it also runs the leaf trick of Theorem 21 and Corollaries 20 and 22. `a16_route_test.py` builds Thm-21 systems independently and runs the proofs of Theorem 28 and Corollary 29. The oracle `tools/route_ext.c` is used only in `a16_enum.py`: for a distance-2 search on random instances, and in a cross-check against my enumerator (226 instances, full agreement). Logs are in `A16-scripts/out/`.

I also re-ran three of the manuscript's own scripts (`trc_test.py`, `unlinked.py`) in a scratch copy, to test evidence claims that the committed logs cannot settle (§6.3).

Verdicts: **SOUND**; **GAP** (fixable; the fix is stated); **ERROR** (false; the false statement is identified); **UNCLEAR** (cannot be settled from the available material).

---

## 0. Summary table

| # | Item | Verdict | Note |
|---|---|---|---|
| S1 | **Lemma 3 (Fan's lemma with vertex sets): statement** | **SOUND** | Fan's Lemma 3.4 (A7 §1a: D′(v) > \|{w ∈ N_{G′}(u) : D′(w) = 0}\|), with donor t = v and target u, plus the vertex-set bookkeeping. The proof is self-contained, so the "cf." is accurate. Grouped transfers (Fan's Lemma 3.3) are not used anywhere in RD; Lean's `fan_grouped_supp` is extra. |
| S2 | **Lemma 3: chain existence (counting)** | **SOUND** | u ∉ X. A shortest step sequence has distinct vertices. The map (x, Q) ↦ π(x, Q)u is injective (both ends of Q in X ⇒ u is interior to Q, so the two readings meet different neighbours). This gives Σ_X b ≤ \|X ∩ N(u)\| and Σ_X b ≥ b(t) + \|X ∩ N(u)\| − \|Z(u)\|. A self-loop step π(x, Q) = x (Q = x u …) is harmless. |
| S3 | **Lemma 3: execution (re-route, append, re-use of a path)** | **SOUND**; **GAP (typo)** | Every vertex-set claim holds: a re-routing keeps V(Q_i), and only Q* gains u, with u ∉ V(Q*). Re-use: Q_i = Q_j forces x_i = the other end of Q_j and i ≥ j + 2; π is preserved; a path is never used three times. **Typo:** "K_i = K + x_iu − x_{i+1}u" is wrong for i ≥ 1, since x_iu ∈ E(K) there. It should read **K_i = K + tu − x_{i+1}u** (i < k). The legality sentence is true for the corrected K_{i−1}. Checked by execution: 115,575 transfers, chains up to length 7, 325 chains re-using a path; 0 violations. §1. |
| S4 | Lemma 3: notation and typesetting | nit | Q₀ names the exceptional path in the statement but the first chain path in the proof, where the exceptional path is Q*. **The committed PDF prints the lemma header as "cf. . Fan05]"**: the `\cite[...]` inside the theorem note does not resolve. Wrap the whole note in braces, `[{… cf.~\cite[Lemma~3.4]{Fan05}}]`, and recompile. |
| S5 | Theorem 2 (Lovász, strong form) | SOUND; nit | It is equivalent to Lovász's "u/2 + g − 1 paths (g ≥ 1)" (and ⌊n/2⌋) by counting: |Od|/2 paths with b ≡ d (mod 2) force exactly one end at each odd vertex and none at the even one (isolated vertices removed first). Theorem 19 with X = ∅ reproves it, so RD stands alone. Suggest adding the one-line counting remark. |
| S6 | **Theorem 19, Case I** | **SOUND** | A target u ∈ N(z) ∖ X exists: if z ∈ X, by non-adjacency; if z ∉ X, at most one of its ≥ 2 neighbours is in X, by "no common neighbour". u is odd. K′ = K − uz has ≤ 1 even vertex, and ν drops. b(z) = 1, b(u) = 0, Z_{D′}(u) = ∅ (every K′-neighbour of u is odd and ≠ z). Good, since u ∉ X. |
| S7 | **Theorem 19, Case II** | **SOUND** | H = K − ux + uℓ has exactly one even vertex, x, and the same number of edges, so ν(H) = ν(K) − 1. Deleting ℓ: Q_ℓ = uℓ ⇔ b(u) = 0, otherwise b(u) = 2 (u is interior to Q_ℓ and keeps its own end, which lies on another path). Sub-case b(u) = 0: the path ux meets X at most at u. Sub-case b(u) = 2: Z_{D′}(x) = ∅, Lemma 3 with t = u, target x ∉ X. In the runs, "Q_ℓ = uℓ" and "b(u) = 0" occurred equally often (1,164 = 1,164). |
| S8 | **Theorem 19, Cases III–IV and exhaustiveness** | **SOUND** | III: v ∉ X has degree 1. The path vw meets X at most at w. IV: X is independent, so no edges. Exhaustive: with no even vertex and no x ∉ X of degree ≥ 3, every vertex outside X has degree 0 or 1. |
| S9 | **Theorem 19: where the distance hypothesis is used** | **SOUND** | It is used exactly twice: in Case I (the target u ∉ X; non-adjacency if z ∈ X, no common neighbour if z ∉ X) and in Case IV (non-adjacency). It is preserved by deleting edges and adding pendant vertices, and nowhere else is it needed. The Fan target only has to be **outside X**, not at distance ≥ 3 from it. Lemma 3's vertex-set form makes "outside X" enough. Executed: 1,438 set-form and 1,357 pair-form instances with every branch exercised. With X merely independent, 1,272 of 1,272 runs break at Case I, at an even vertex with every neighbour in X, and nowhere else. §2. |
| S10 | **Example 24 (distance two)** | **SOUND**; suggestion | Exhaustive: 36 Lovász decompositions, 0 separate c and a. The displayed decomposition is valid, with Q_c = c u₁. With a leaf at z, 60 of 168 separate. **Suggestion:** the example has an even vertex, and its last sentence ("adding a leaf at z … exists again") may suggest that the all-odd case is fine at distance 2. It is not. **K₄ − ca with a leaf at c and at a** (6 vertices, 7 edges, all degrees odd) has no separating Lovász decomposition (0 of 36), and the same three-line argument proves it. This shows distance three is needed in the all-odd setting of Conjecture 30 too. It is the smallest example: an exhaustive search over all all-odd graphs on ≤ 6 vertices finds nothing smaller. §3. |
| S11 | Corollary 20 | SOUND | Immediate from Theorem 19 with X = {c, a}. |
| S12 | **Theorem 21 (L₁) and its set form** | **SOUND** | K = F + cℓ has c as its only even vertex. X = Y ∪ {ℓ} is packed, since dist(ℓ, y) = 1 + dist(c, y) ≥ 3. The path through ℓ continues past c, so Q_c = Q − ℓ, and it misses Y because Q already meets X at ℓ. Executed on 1,412 instances (random packed Y of size ≤ 4 outside N[c]). |
| S13 | Corollary 22 | SOUND | F = G − ac is all-odd. Theorem 21 with Y = {a}, then append the route ca (Proposition 15). Executed on 1,309 instances; ca is terminal at a every time. |
| S14 | Corollary 23 | SOUND | (RR1) because each path meets V(J) at most once; (RR2) vacuous. Verified on 13 random minimum Thm-21 systems with V(J) packed in F. |
| S15 | **Remark after Corollary 23: "forces G[V(J)] = J, a forest, so G[Ev] is a forest. These graphs lie in Pyber's class"** | **ERROR (wording; harmless)** | Corollary 23 is stated for **any** route system, and J need not be a forest. Counterexample (16 vertices, checked): routes v₁v₂, v₃v₄, x v₂v₃ y and x′ v₄v₁ y′, plus a private leaf at each route vertex. Then J ⊇ C₄ = v₁v₂v₃v₄, V(J) is packed in F, and G[Ev] = J is not a forest. Corollary 23 still realises all 16 transversals. The remark is true for Thm-21 systems. Fix: "for a Thm-21 system (J a forest) …", or state Corollary 23 for Thm-21 systems. |
| S16 | Lemma 5 (basic facts), Lemma 6 (upward closure), Lemma 8 (base) | SOUND | Lemma 5 checked on 300 constructed systems. Lemma 6 is `Realisable.mono`. |
| S17 | **Lemma 7 (heredity of the Thm-21 class)** | **SOUND**; GAP (clarity) | Parities, Ev(G′) = Ev ∖ {a, c}, no isolated vertex, even components, J′ a forest, F′ = F, and F′^v ⊇ F^v because N_{G′}(v) ⊆ N_G(v). Checked on 688 route deletions in 300 systems, by an independent construction. **Clarity:** (i) G′ may be disconnected, while Conjecture 1 (TRC) is stated for connected G. A linking path of F^v cannot leave the component, because it passes v only once, so Thm-21 systems restrict to components; say so. (ii) The abstract Thm-21 class *equals* the class of constructible pairings: the linking paths at v pair exactly the odd vertices of F^v (EMM Lemma 19). RD states only one direction. |
| S18 | **Lemma 9 (extension ⇔ terminal route)** | **SOUND** | Both directions are correct. Checked as a **bijection** by exhaustive enumeration: 1,906 (G, P, M, p), 58,876 realisations matched one-to-one, with both maps of the proof applied to every object. |
| S19 | **Proposition 10 (existential form; TRC ⇒ Gallai)** | **SOUND** (first statement); **GAP (stand-alone)** | The first statement is Lean's `desc_of_rootedHalfSet`. The "in particular" (⇒ Gallai) is delegated to the Lean theorem `gallai_of_branchBase`, whose content (BranchBase, Desc, the rooted test) is not in RD. A direct two-line proof exists and needs no root: a realisable transversal has \|Od\|/2 + \|Ev\|/2 = n/2 paths, and odd n reduces to even n by a pendant edge (EMM §4.4). So "for each of its even vertices y" is unnecessary for Gallai. Add this argument, and keep the Lean spine as a remark. |
| S20 | **Lemma 11 (minimum T-joins), items (1)–(5)** | **SOUND** | The symmetric-difference argument is correct for (1)–(3). In (4), K′ ∪ E(R_p) is disjoint, with parity T′ △ {a, c} = T. In (5), every T-join has ≥ \|T\|/2 edges. Checked on 150 minimum T-joins: forest; every segment of every route a geodesic (483 segments); random cycles satisfy (2); exact minimum size after every route deletion (4); 93 matching T-joins minimum (5). |
| S21 | Corollary 12 (no trivial obstruction) | SOUND | Another neighbour of c on R_p would be a chord. Checked on every route deletion. |
| S22 | **Abstract and §9: "the only obstruction ever met with spanning-tree T-joins … cannot occur" / "avoid the only obstruction ever observed"** | **ERROR (wording)** | False as written. E20 records 95 nontrivial extension failures at n = 10 (sparse) and 70 on block trees, and RD §8 itself reports the 70. My reruns find 24 nontrivial failures in 600 constructions on the order-12 graphs, and 46 of 94 failures nontrivial on block trees (seed 71, exhaustive). The defensible statement is "the obstruction behind almost all failures in random graphs". §6.3. |
| S23 | Remark 13 | **GAP (wording)** | "Most failures are of the trivial kind": true in random graphs (95%) and on the order-12 family (my rerun: 6,064 of 6,088), but false on block trees (70 of 115 nontrivial in E20; 46 of 94 in my exhaustive rerun). "The only instances in which no route at all admits the extension were all of this kind": E20's block-tree run had 1 stuck transversal and does not classify it. That run was budgeted, and `trc_test.py` counts an undecided query as a failure (`e = False`), so the stuck instance may be an artefact. My exhaustive rerun (seed 71, 2,172 transversals) has 0 stuck. Qualify the sentence. §6.3. |
| S24 | **Proposition 15 (compatible decompositions ⇔ route-respecting realisations)** | **SOUND** | Both directions: (RR1) and (RR2) make the appended object a path; each route has one tail with exactly one end; the end counts give b_M; the converse strips non-empty terminal routes. Checked as a **bijection**: 1,125 (G, P, M) with arbitrary edge-disjoint routes, 12,066 route-respecting realisations matched one-to-one. Lean `realisable_of_compatible` states the forward direction with "≤ 1 end everywhere and ≥ 1 at tails", which is equivalent on an all-odd F. |
| S25 | Conjecture 16, the L_N reduction, Conjecture 17, Proposition 18 | SOUND | The one-edge routes are linked trivially, since F^v has exactly two odd vertices, v and z (EMM Lemma 19). (RR2) is automatic. Proposition 18 counts n/2 paths. |
| S26 | **Theorem 26 (Fan-isolated routes)** and the remark that G[Ev] is a matching | **SOUND**; novelty honest | Each transfer r_{i−1} → r_i is legal: Z(r_i) ⊆ N(r_i) ∩ Ev ⊆ N_{R_p}(r_i), and those edges are not yet present. The matching argument is correct. 50 Fan-isolated systems: every order and orientation is a schedule, and G[Ev] is a matching. "New only as a statement about all transversals" is accurate. Nit: t is both the route length and Lemma 3's donor. |
| S27 | **Definition 27 and Theorem 28 (route schedules)** | **SOUND**; nit | Every vertex of a later pair is odd in G_j. N(r_i) in the current graph equals N_{G_{j−1}}(r_i). An earlier tail lying on the route gains and then loses one end. Executed: 198 schedules, all outputs checked. Nit: "the vertices without ends **are** those of U_{j−1} …" should be "are among". "Exactly the Fan schedules (semi-induced matchings)": SOUND. This is ES §Fan certificates with even steps, with heads w_i and tails x_i. ES also allows unmatched marked even vertices and a lone x₁; RD's version is the perfect-matching case. |
| S28 | **Corollary 29 (unique perfect matching)** | **SOUND**; novelty honest | An alternating cycle would give a second PM, so the relation is acyclic. N − c_ia_i is unique in G′. Z(a_i) = ∅. "Uniqueness ⇔ every orientation admits an order" is correct: an alternating cycle, oriented along itself, is a directed cycle. Executed on 164 orientations. I found no unique-PM statement in endpoint-structure, so "follows from the Fan schedules", as the novelty paragraph puts it, is accurate. |
| S29 | §8, heuristic paragraph after Conjecture 31 ("the leaf case nearly goes through") | SOUND as a heuristic | I re-derived the claims. Chain vertices after the first are interior, so a leaf is never one. A target at distance ≥ 3 from c can never be appended to Q_ℓ ⊆ {ℓ} ∪ N[c]. The only unsafe case is z at distance 3 with every neighbour at distance 2. The degree-2 lift is correct: adding uu′ does not shorten distances from c, since u and u′ are both at distance 2. The paragraph claims no result. |
| S30 | Conjecture 30 ⇒ Conjecture 17 at distance ≥ 3 ⇒ Gallai for "PM of G[Ev] with no edge in a triangle" | SOUND | A common F-neighbour of c_i and a_i is exactly a triangle on c_ia_i. |
| S31 | **§8 evidence vs E20: numbers** | **MATCH**, with five exceptions (S32–S35) | Match exactly: TRC 86,400 / 3,600; ≈ 60,000 random (E20: 60,712); 1,280 (G₁₈); 128 (G_bad); 1,280 (prism); 115 + 13 (G′(Petersen)); 4–5% and 95%; 115 and 70 (block trees); 21,896 (16 undecided); 8,896 (n = 14); RR\* in 2 of 12; linking 4 of 1,834; L₁ 70,978; N[c] 19,040 + 5,026 (41 undecided); L_N for perfect matchings 2,332 decided (157 undecided), 2,421 of 2,489 at distance 2; separation 2,892 (925 perfect matchings; 102 undecided); 500 of 2,191 ≈ a fifth; Remark 25: 648 of 5,399, 2 of 221, 998; Conjecture 31: 1,984 + 1,211 = 3,195. |
| S32 | §8 RR bullet: "An M-compatible decomposition was found for **every transversal tested** with minimum T-joins" | **GAP (wording)** | E20 has minimum-T-join transversals for which RR stayed **undecided**: n = 14, 212 of 2,232; G′(prism), 221 of 640 (419 found, `rrfail_kprism_min_rr.jsonl` empty, so none refuted); G₂ half, 251 of 352. None was refuted. Say "found whenever decided; never refuted; undecided in …". |
| S33 | §8 L_N bullet: "No failure of L_N in 3,732 instances" | GAP (wording) | E20: 135 of these were undecided. Say "3,597 decided (135 undecided)". |
| S34 | Counts in the abstract and §8 | nit | "About 220,000 pairs (M, p)" with minimum T-joins: E20 sums to ≈ 241,000 (210,431 + 8,896 + 21,896). "About 1.5 × 10⁵ transversals": E20 sums to ≈ 1.6 × 10⁵. Conjecture 31's "orders 7–15" has no order 12. |
| S35 | Logs | **GAP (documentation)** | E20 and the README cite `scripts/outputs/*.log` (`ln_perfect.log`, `ball_*.log`, `msep3.log`, `trc_blocks_*.log`, …). **None is committed**, because the root `.gitignore` contains `*.log`. Only the `*.jsonl` failure lists are in the repository. Rename them (`*.txt`) or add a `!manuscripts/route-descent/scripts/outputs/*.log` exception. |
| S36 | §8 "Linking is needed" | SOUND (independently confirmed) | A fresh `unlinked.py` run reproduces such instances. For one of them my own code confirms that J is minimum (5 edges = the minimum), that the transitions at vertex 8 cannot be linked in F⁸ (exhaustive), and that transversals {8, 2, 9} and {8, 6, 9} have **0** realisations by exhaustive enumeration. |
| S37 | Remark 25 (small claims) | SOUND | On the path c z a the only Lovász decomposition is the path. For K₁,₃ with hung leaves, all 3 Lovász decompositions join two hung leaves. Exhaustive. |
| S38 | **§10 Formalisation** | **GAP (documentation)** | (i) Lean proves Lemma 3 only in the **cover form**: every new path lies in an old path ∪ {u} (`fan_exec_supp` and the others). It does not prove the bijection with V(φ(Q)) = V(Q). The cover form is all Theorem 19 needs (`meetsOnce_of_cover`). Say so. (ii) The "Not formalised" list omits **Theorem 28** (and Corollaries 12 and 23 and Proposition 18). Theorem 26 is formalised only in the case G[Ev] is a perfect matching, as stated. |
| S39 | Lean cross-check of statements (not rebuilt) | consistent | `separation_set`: Packed means no two X-vertices adjacent or with a common neighbour; MeetsOnce; ends = deg mod 2; at most one even vertex. `lovasz_avoid_set` has the same hypotheses as Theorem 21. `SepStrong` uses the same ν. `realisable_of_compatible` and `Compatible` are (RR1) and (RR2). Lean's `RouteSystem` lets the two orientations of a pair use different routes, which is more general and harmless. |
| S40 | Novelty of Theorem 19 and Theorem 21 ("We have not found either in the literature") | UNCLEAR (not re-searched) | The phrasing is honest. I relied on the synthesis's web search (§18) and did not repeat it. |

**Overall.** **Every theorem, lemma, corollary and proposition of RD is correct as stated.** I checked each part of the scope:
- Lemma 3, through every case of the chain argument, including the re-use of a path from its other end. There are no grouped transfers.
- All four cases of the separation induction, its measure and its exhaustiveness. The target is always outside X; packedness is used exactly in Case I and Case IV.
- Example 24, exhaustively.
- L₁ and its set form, by the leaf trick.
- Heredity of the Thm-21 class and of minimality; the geodesic route segments.
- Extension ⇔ terminal route, and Proposition 15, verified as bijections by exhaustive enumeration.
- TRC ⇒ Gallai.
- Theorems 26 and 28 and Corollary 29, by executing their proofs.

The mathematical items to fix are small:
- a typo in the definition of K_i in the proof of Lemma 3 (S3);
- the delegation of "⇒ Gallai" in Proposition 10 to an undefined Lean notion, where a two-line argument suffices (S19);
- a false remark after Corollary 23 that J is a forest (S15).

The **evidence statements** need several corrections:
- the abstract's and §9's "only obstruction ever met" is false (S22);
- Remark 13 needs qualifying for block trees (S23);
- the RR and L_N bullets omit undecided cases (S32, S33);
- the cited logs are not in the repository (S35);
- §10 overstates what Lean proves of Lemma 3 (S38).

None of these affects a proof. One addition would strengthen §6: an all-odd distance-2 counterexample (S10).

---

## 1. Lemma 3 (Fan's lemma with vertex sets)

### 1.1 Statement against Fan's Lemma 3.4

A7 §1a quotes BS Lemma 6 ("a result of Fan [Lemma 3.4]"): for uv ∈ E(G), G′ = G − uv and a path decomposition D′ of G′, if D′(v) > |{w ∈ N_{G′}(u) : D′(w) = 0}|, then uv is addible towards u. "Addible towards u" means a decomposition of G of the same size, with one more end at u and one fewer at v.

RD's Lemma 3 is this statement with K = G′, t = v and target u, and with Z_D(u) = {w ∈ N_K(u) : b_D(w) = 0}. The added content is the bijection φ: every V(φ(Q)) = V(Q) except one, and that one equals V(Q₀) ∪ {u}. RD proves the lemma in full, so "cf." is the right citation.

Lean's `fan_single_supp` (docstring "Fan's Lemma 3.4") has the same hypothesis.

### 1.2 Chain existence

Let X be the set of vertices reachable from t by steps x ↦ π(x, Q).
- **u ∉ X**: π(x, Q) is the vertex *before* u, so it is never u, and t ≠ u.
- **If no chain exists, every path with an end in X contains u.** A shortest step sequence to an end vertex x ∈ X has distinct vertices, and together with a u-avoiding path at x it would be a chain.
- **Injectivity of (x, Q) ↦ π(x, Q)u.** Distinct paths have disjoint edges. If Q has both ends x₁, x₂ ∈ X, neither end is u (since u ∉ X), so u is interior to Q, and the two readings stop at the two different Q-neighbours of u.
- **Self-loops.** If Q = x u …, then π(x, Q) = x. This is still an edge xu of Q with x ∈ X ∩ N(u), so the counting is unaffected, and a shortest sequence never uses such a step.
- **Lower bound.** t ∉ N(u), and every vertex of X ∩ N(u) ∖ Z has an end. So Σ_X b ≥ b(t) + |X ∩ N(u)| − |Z ∩ X| ≥ b(t) + |X ∩ N(u)| − |Z|.

Combining the two bounds gives b(t) ≤ |Z|. **SOUND.**

### 1.3 Execution

**Re-routing.** Read Q_i from x_i as x_i ⋯ x_{i+1} u ⋯ y. The new path is (x_i ⋯ x_{i+1})ʳ u ⋯ y. It is a path, because the reversed segment and the rest are disjoint and x_iu is free. It has the same vertex set and ends x_{i+1} and y. If y = u, the new ends are x_{i+1} and u, which is still correct.

**Re-use.** Suppose Q_i = Q_j with j < i.
- Then x_i is an end of the original Q_j and x_i ≠ x_j, so x_i is its other end y_j.
- i ≠ j + 1: x_{j+1} = π(x_j, Q_j) is followed by u, so it is not the far end y_j.
- After step j, the path read from y_j is unchanged up to u, so π(x_i, current) = x_{i+1}.
- A third use would need a third end.
- I worked through the composite. With Q_j = x_j A x_{j+1} u B x_{i+1} C y_j, the path after both steps is (x_{i+1} C y_j)ʳ u (x_j A x_{j+1})ʳ. Its vertex set is unchanged.

**Append.** Q* avoids u, so it is not a Q_i and is untouched. Q* + x_ku is a path. x_ku is free: it is tu if k = 0, and was freed at step k − 1 otherwise.

**Typo (GAP).** RD writes "K_i = K + x_iu − x_{i+1}u for i < k". For 1 ≤ i < k, x_i is a K-neighbour of u, so "K + x_iu" is undefined under RD's own convention ("for tu ∉ E(K)"). Read as a multigraph, it also omits tu. The graph after step i is
> **K_i = K + tu − x_{i+1}u (0 ≤ i < k), and K_k = K + tu.**

With this correction:
- D_{i+1} partitions K_i;
- the legality sentence ("x_iu is absent from K_{i−1}, and x_{i+1}u lies on Q_i") holds verbatim;
- the final graph is K + tu.

Nothing else in the proof uses K_i.

**Execution test** (`a16_fan_test.py`; `out/fan_shortest.txt`, `out/fan_long.txt`). The setup:
- random graphs of order 4–13 and random path partitions with arbitrary profiles;
- every (t, u) with tu ∉ E and b(t) > |Z(u)|;
- either shortest (BFS) chains, or long random chains of distinct vertices, which the proof allows.

The code asserts at every step:
- that a chain exists (S2);
- that π(x_i, current form) = x_{i+1};
- that no path is used three times;
- that Q* is untouched;
- the final graph, partition and profile;
- the bijection with equal vertex sets except V(Q*) ∪ {u}.

Results: **115,575 transfers, 0 violations.** Chains reached length 7, and 325 chains re-used a path from its other end.

### 1.4 Lean

`fan_exec_supp`, `fan_grouped_supp` and `fan_single_supp` conclude only "∀ Q′ ∈ D′, ∃ Q ∈ D, V(Q′) ⊆ V(Q) ∪ {u}". There is no bijection and no equality. This is weaker than Lemma 3 as stated, but it is exactly what Theorem 19 uses (`meetsOnce_of_cover`). §10 of RD should say "Lemma 3 in the form: every new path lies in an old path plus u" (S38).

---

## 2. Theorem 19 (separation), pair and set forms

The measure is ν(K) = 2|E| + [no positive-even vertex].

| Case | Graph passed to the induction | ν | Claims checked |
|---|---|---|---|
| I: z even | K − uz, with u ∈ N(z) ∖ X | ≤ 2\|E\| − 1 < 2\|E\| | u exists (packing); u odd; ≤ 1 even vertex in K′; b(z) = 1, b(u) = 0; Z(u) = ∅; Lemma 3 with t = z gives b = d mod 2 |
| II: no even vertex, x ∉ X with d(x) ≥ 3 | H = K − ux + uℓ | 2\|E\| < 2\|E\| + 1 | x is the only even vertex of H; X is packed in H; Q_ℓ has ℓ as an end; b(u) ∈ {0, 2} (= 0 exactly when Q_ℓ = uℓ); b(x) = 0; other ends = d mod 2; goodness kept when ℓ is deleted; sub-case b = 0: path ux; sub-case b = 2: Z(x) = ∅ and Lemma 3 with t = u, target x ∉ X |
| III: no even vertex, every x ∉ X of degree ≤ 2 | K − vw, with v ∉ X of degree 1 | < 2\|E\| + 1 | w becomes even or isolated; b(w) = b(v) = 0; the path vw meets X at most at w |
| IV | none | — | X is independent, so there are no edges |

**Where packedness enters.** Only in Case I, and only through the target. If z ∈ X, a neighbour of z in X would be adjacent to z. If z ∉ X, two neighbours in X would share the neighbour z. Case IV uses non-adjacency. Case II does not need packedness: its target x lies outside X by the choice of case, and its one-edge path ux meets X at most at u.

Packedness is inherited because the recursion only deletes edges and adds pendant edges at new vertices. A new vertex lies on no path between old vertices, and deleting edges only increases distances. The even vertex moves, from z to u in Case I and to x in Case II. That is why the hypothesis must hold for all of X, and not just near the current even vertex.

**"Target outside X at distance ≥ 3".** The proof needs the target only to be outside X. The new vertex set is V(Q*) ∪ {u}, and Q* already met X at most once. The target may be adjacent to X: in Case I, u is adjacent to z, which may lie in X. Distance three is used only to guarantee that the target exists.

**Execution** (`a16_sep_test.py`; `out/sep_*.txt`). Each mode builds random instances of order 3–14 and runs the case analysis recursively, asserting every row of the table above. The final output is checked independently.

| Mode | Instances | Recursive steps (case counts) |
|---|---|---|
| set form, random packed X | 1,438 | I 15,889; II (b = 0) 1,164; II (b = 2) 1,337; III 6,068; IV 1,438 |
| pair form, X = {c, a}, dist ≥ 3 | 1,357 | 17,226 calls to Lemma 3 in the set-form mode |

All outputs are good Lovász decompositions.

**Control.** I ran the same algorithm with X independent but not packed. 1,272 of 1,272 runs fail, every one in Case I, at an even vertex all of whose neighbours lie in X. Nothing else breaks. This confirms that Case I is the only use of the distance-3 hypothesis beyond Case IV.

---

## 3. Example 24 and distance two (`a16_enum.py`; `out/enum_*.txt`)

The enumerator lists every transition system, keeps those whose trails are paths, and so lists every path partition with the profile exactly once.

- **Example 24.** K has 7 vertices and 8 edges, and z is the only even vertex.
  - It has 36 Lovász decompositions, and **none separates c and a**. RD's argument is correct: each u_i has exactly one passage; if u_i ends the path through u₁zu₂, its passage is {c, a}; otherwise that path reaches two distinct vertices of {c, a}.
  - The displayed decomposition c u₁ | ℓ_c c u₂ z u₁ a | u₂ a ℓ_a is a valid Lovász decomposition with Q_c = c u₁. Of the 36 decompositions, 18 have a ∉ Q_c.
  - With a leaf at z, all degrees are odd, and 60 of the 168 Lovász decompositions separate c and a. For example: a ℓ_a | c ℓ_c | ℓ_z z u₂ a u₁ | u₂ c u₁ z.
- **All-odd distance two** (suggestion for RD). An exhaustive search over all all-odd graphs on ≤ 6 vertices finds 30 non-separable distance-2 pairs, counted as labelled pairs on one representative of each of the 16 isomorphism classes on 6 vertices; there are none on 4 vertices. Exactly one graph has the minimum, 7 edges: **K₄ − ca with a pendant leaf at c and at a**. This is Example 24 with z contracted into the edge u₁u₂.
  - It has 36 Lovász decompositions, and none separates c and a. RD's three-line argument applies verbatim: u₁ and u₂ have one passage each, and the path through u₁u₂ must reach both c and a.
  - It satisfies L₁ (18 of 36 decompositions) and even S₁ (10 of 36).
  - K₃,₃ is non-separable at every distance-2 pair as well.

  Example 24 needs an even vertex, and RD notes that a leaf at z restores separation. So as written, RD leaves open whether distance 2 suffices when all degrees are odd. That is exactly the setting of Conjecture 30 and of the Eulerian discussion at the end of §8. The K₄ − e example settles it: distance 3 is needed. E20's `sep2.py` ("446 of 2,945 fail in all-odd graphs") agrees. Add this example to Example 24 or to Remark 25.
- **Remark 25.** On the path c z a the unique Lovász decomposition is c z a. For K₁,₃ with leaves hung at its three leaves, the hung leaves are pairwise at distance 4, so they are packed. All 3 Lovász decompositions contain a path joining two of them.
- **Oracle cross-check.** The S query of `tools/route_ext.c` agrees with the enumerator on 226 random instances.

---

## 4. L₁, Corollary 20 and Corollary 22

**Theorem 21.** Write K = F + cℓ.
- c is the only even vertex of K: it has degree d_F(c) + 1 ≥ 2.
- X = Y ∪ {ℓ} is packed in K. Y keeps its F-distances, since ℓ is pendant, and dist_K(ℓ, y) = 1 + dist_F(c, y) ≥ 3 because y ∉ N[c].
- In D_K, the path Q through ℓ has ℓ as an end. c has no end, so Q continues past c.
- Q − ℓ ends at c, and b(c) becomes 1 = d_F(c) mod 2.
- Q meets X at ℓ, so Q − ℓ misses Y. Every other path is unchanged.

**SOUND.** Executed with Y of size 1–4: 1,412 instances (`out/sep_l1.txt`). The "in particular" uses Y = {a}, which is packed and outside N[c] exactly when a ≠ c and a ≁ c. The task statement "all degrees odd" is the special case with no isolated vertices.

**Corollary 20** is Theorem 19 applied to X = {c, a}. **Corollary 22:** F = G − ac is all-odd and d_F(c) ≥ 1. Theorem 21 with Y = {a}, plus the single route ca (head a), gives (RR1), and (RR2) is vacuous. Executed on 1,309 instances: the result realises {a}, with ca the last edge of its path (`out/sep_onepair.txt`).

The Lean statements `lovasz_avoid_set` and `lovasz_avoid_nonadj` have exactly these hypotheses.

---

## 5. Route-descent reductions (`a16_route_test.py`; `out/route_*.txt`)

### 5.1 Construction

The test systems are built independently:
- a forest T-join, either the T-join of a random spanning tree or a minimum one (shortest paths along a minimum-cost matching of Ev, computed by DP; its size equals the lower bound);
- at every v, F^v and a random edge-disjoint pairing of its odd vertices;
- the routes, by following the transitions.

EMM Lemma 19 (odd vertices of F^v = J-neighbours of v, plus v when v is even) is asserted every time. Definition 4 is checked directly: J is a forest, and every transition is joined by its own path of F^v, the paths pairwise edge-disjoint.

### 5.2 Lemmas 5, 7, 11 and Corollary 12

These were checked on 300 systems and 688 route deletions:
- Lemma 5: odd free degrees, and interior vertices of degree ≥ 3.
- Lemma 7: no isolated vertex; even components; Ev(G′) = Ev ∖ {a, c}; F′ = F; the remaining links are edge-disjoint paths of F′^v that link exactly the remaining transitions; J′ a forest.
- Lemma 11: (1) a minimum T-join is a forest; (2) on random cycles; (3) every segment of every minimum route equals the BFS distance (483 segments); (4) the minimum T′-join size of G′ is exactly |J| − |R_p|; (5) 93 perfect matchings of G[Ev] were minimum.
- Corollary 12 for both ends.

There were no violations.

**Clarity points for Lemma 7 (S17).**
1. G′ can be disconnected, while TRC is stated for connected graphs. The induction runs inside the class of graphs with even components, and a Thm-21 system restricts to each component C. The reason: in F^v, v is the only vertex with edges between components, a path passes v at most once, and so a linking path between two vertices of C, or from z ∈ C to v, stays inside C ∪ {v}. Synthesis §17(H) says this ("applied componentwise"); RD does not.
2. Conversely, every abstract Thm-21 system on a connected graph is constructible. By EMM Lemma 19, the linking paths at v pair exactly the odd vertices of F^v, so they are a legal step-2 choice, and they reproduce the routes. Stating this would make "Thm-21 system" and "pairing produced by the cut-selection construction" (Conjecture 1) visibly the same class.

### 5.3 Lemma 9 and Proposition 15 as bijections

These are proved for arbitrary route systems, so the test uses random edge-disjoint routes pairing Ev on graphs with ≤ 13 edges. For each (G, P, M, p) it lists both sides exhaustively, applies the map of each direction of the proof to every object, and checks that the images coincide and the counts agree.

| Statement | Instances | Objects matched | Instances with a nonempty side |
|---|---|---|---|
| Lemma 9 | 1,906 | 58,876 | 1,475 |
| Proposition 15 | 1,125 | 12,066 route-respecting realisations ↔ M-compatible Lovász decompositions of F | 697 |

There were no mismatches. Both proofs are **SOUND**, including the converse half of Proposition 15, which is not formalised.

### 5.4 Proposition 10 and TRC ⇒ Gallai

The first statement is Lean's `desc_of_rootedHalfSet` word for word, and it is correct. For the "in particular", RD's text proves only BranchBase_k and then cites `gallai_of_branchBase`. A reader of RD cannot check that step, because BranchBase, Desc and the rooted test are not defined in RD. An elementary argument exists and needs no root:
> If a connected graph of even order has a realisable transversal M of some pairing of Ev, then b_M has |Od|/2 + |Ev|/2 = n/2 paths. A connected graph of odd order n reduces to even order: add a pendant edge, partition into (n + 1)/2 paths, delete the pendant vertex.

EMM §4.4 says exactly this. So TRC, and its existential form with a single realisable transversal per graph, implies Gallai. The root y matters only for the Lean spine. Fix: add the argument and keep the BranchBase statement as a remark (S19).

### 5.5 Theorems 26 and 28, Corollary 29

These were run as algorithms: Lovász on F (the proof of Theorem 19 with X = ∅), then Lemma 3 once per route edge, with every legality condition asserted by `fan`.

- **Theorem 28:** 198 schedules, found by random orderings and orientations of Thm-21 systems. Every output is a realisation of {a₁, …, a_m}.
- **Theorem 26:** 50 systems satisfy the Fan-isolated hypothesis. For each, every order and orientation (≤ 24 orders × all 2^m orientations) is a schedule, and G[Ev] is a matching whose edges are one-edge routes. This confirms the remark after Theorem 26 and RD's "the case in which every order and every orientation is a schedule".
- **Corollary 29:** 164 orientations of unique perfect matchings of G[Ev]. A sink always exists, as the acyclicity argument predicts, and the reconstruction is a valid realisation every time.

**Novelty (scope item 5).** The novelty statements are honest:
- Theorem 26: "lies inside Pyber's class; new only as a statement about all transversals".
- Corollary 29: "follows from the Fan schedules".
- The schedule correspondence: endpoint-structure §"Fan certificates", with even steps only. Its condition "w_i adjacent to none of x₁, …, x_{i−1}" is RD's "head a_j not adjacent to earlier tails", with heads w and tails x. ES's certificate also allows a lone tail x₁ and unmatched marked even vertices; RD's Definition 27 with one-edge routes is the perfect-matching case.
- I found no statement about unique perfect matchings in endpoint-structure, so Corollary 29's observation (uniqueness ⇔ every orientation admits a schedule) is new there, and it is correct.

---

## 6. Conjectures and evidence (scope item 6)

### 6.1 Statements

- Conjectures 16, 17, 30 and 31 are stated consistently with the reductions: Proposition 15 for 16 ⇒ TRC; Proposition 18 for 17 ⇒ the perfect-matching class; §8 for 30 ⇒ 17 at distance ≥ 3.
- The leaf corollary of Conjecture 31 is correct. Q_ℓ ⊆ B₂(ℓ) = {ℓ} ∪ N_F[c], so Q_c ⊆ N_F[c]. On a minimum route, c has no F-neighbour, so this gives (RR1).
- The heuristic paragraph is S29.

### 6.2 Numbers against E20

Every number in §8 and Remark 25 matches E20 (S31), with these exceptions:
- **RR bullet (S32).** "Found for every transversal tested" leaves out the minimum-T-join transversals whose RR status stayed undecided: n = 14 (212), G′(prism) (221; none refuted, since `rrfail_kprism_min_rr.jsonl` is empty) and G₂ half (251). The evidence is "never refuted", not "always found".
- **L_N bullet (S33).** 135 of the 3,732 instances were undecided.
- **Counts (S34).** About 241,000 minimum-T-join extension pairs, not "about 220,000". About 1.6 × 10⁵ transversals in all. Conjecture 31 was tested at orders 7–11 and 13–15.
- **Logs (S35).** E20's `outputs/*.log` files are not in the repository, because `.gitignore` excludes `*.log`. E20's statistics cannot be checked against committed output. The `*.jsonl` failure lists are present, and they are consistent with E20 where they apply. For example, `nontrivial_rand10sparse.jsonl` is non-empty, and every min-T-join `rrfail_*` file is empty.

### 6.3 Re-runs for the obstruction claims (S22, S23)

I re-ran the manuscript's `trc_test.py` in a scratch copy, with networkx in a scratch virtualenv and the committed scripts unchanged. Nothing was written to the repository.

| Run | Constructions | Extension queries | Failures | Trivial | Nontrivial | Stuck |
|---|---|---|---|---|---|---|
| `order12`, spanning-tree T-joins | 600 | 67,200 | 6,088 | 6,064 | **24** | 0 |
| `blocks 2 32 71`, tree, RR = 1, exhaustive (no budget) | 120 | 10,460 | 94 | 48 | **46** | **0** (of 2,172 transversals) |

The order-12 run had 0 TRC failures.

So nontrivial obstructions occur in every family tested. The abstract's "the only obstruction ever met with spanning-tree T-joins" and §9's "the only obstruction ever observed" are false. The correct claim is that the trivial obstruction accounts for 95–99.6% of failures in random graphs and the EMM family, and for none of them with minimum T-joins.

Remark 13's "most failures are trivial" does not hold on block trees.

Remark 13's claim about stuck instances could not be confirmed for E20's block-tree "1 stuck". That run used a budget, and `trc_test.py` counts an undecided extension query as false when it decides whether a transversal is stuck (`if e is None: … e = False`). The exhaustive seed-71 rerun has no stuck transversal. A budgeted rerun of seed 72 was too slow to finish (§7), so E20's stuck instance remains unclassified.

**Linking is needed (S36).** A fresh `unlinked.py 10 100 200000` run found 2 non-realisable transversals among 600, both in one graph:
- edges 04 08 12 18 19 23 26 29 47 48 59 69 78;
- routes 0–8, 2–6, 7–8–1–9.

My own code confirms that this J is a minimum T-join (5 edges), that the transitions at vertex 8 cannot be linked by edge-disjoint paths of F⁸ (exhaustive), and that {8, 2, 9} and {8, 6, 9} have no realisation (exhaustive enumeration). This supports the qualitative claim "linking is needed". The count "4 of 1,834" is E20's and cannot be checked without the log.

---

## 7. Scripts and outputs

All scripts are in `research/audit/A16-scripts/`, with pure Python 3 and no dependencies; `gcc` is needed only for the oracle cross-check. Outputs are in `out/`, saved as `.txt` because the repository ignores `*.log`.

| Script | Purpose | Log |
|---|---|---|
| `a16_core.py` | graphs; partition checker; exhaustive enumerator of path partitions by transition systems; **the proof of Lemma 3 as code**, asserting every claim; oracle wrapper | — |
| `a16_fan_test.py [trials] [seed] [long]` | Lemma 3 on random partitions and every admissible (t, u); shortest or long random chains | `fan_shortest.txt`, `fan_long.txt` |
| `a16_sep_test.py MODE [trials] [seed]` | the proof of Theorem 19 as an algorithm (`sep`, `pair`), the leaf trick of Theorem 21 (`l1`), Corollary 22 (`onepair`), and the control with independent but not packed X (`dist2`) | `sep_*.txt` |
| `a16_enum.py MODE` | Example 24 (`ex24`), the all-odd K₄ − e example (`k4e`), Remark 25 (`path`, `star`), the exhaustive all-odd distance-2 search (`odd2`), and the oracle cross-check (`oracle`); `all` runs the first group | `enum_all.txt`, `enum_odd2.txt` |
| `a16_route_test.py MODE [trials] [seed]` | Lemmas 5, 7, 11 and Corollary 12 (`basics`); Lemma 9 and Proposition 15 as bijections (`bij`); Theorems 26 and 28 (`sched`); Corollary 29 (`upm`); Corollary 23 and the remark with a cycle in J (`packed`); the "linking is needed" instance (`unlinked`) | `route_*.txt` |

**Seed-72 block-tree rerun (§6.3).** I tried it twice. Exhaustively, the oracle was still on a single query of the first graphs after 6 minutes. With BUDGET = 200000 and FINAL = 0, the first ten graphs had not finished after a further 10 minutes. I stopped both runs. So E20's block-tree "1 stuck" remains **unclassified**: S23 is a GAP because the claim is unverified, not because it is refuted.
