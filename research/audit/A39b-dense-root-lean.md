# A39b: Audit of `DenseRootB.lean` (Theorem B of dense-root)

Date: 2026-11-28. Referee stance: adversarial. Grades: **SOUND**; **ERROR** (false as stated); **GAP** (an omission that changes how a result reads; fixable); **NIT** (wording or hygiene).

**Version.**
- `lean/GallaiLean/DenseRootB.lean`: 1,211 lines, md5 `e12f66bb…`. Unchanged since 33fc1f0.
- `manuscripts/dense-root/dense-root.tex`: md5 `e019c46d…`, as committed in be56355, which landed during this audit.
- "l." means a line of `dense-root.tex`.

**Scripts.** All are in `research/audit/A39b-scripts/`. `runs.sh` lists every command I ran.

---

## 0. Verdict

**The Lean file is correct and faithful. No ERROR.**

1. **Build and axioms.**
   - `DenseRootB.lean` compiles (exit 0, 59 linter warnings, no errors). `lake build` completes with 18,436 jobs, as the Files section says.
   - There is no `sorry`, `admit`, `native_decide` or `axiom` in `DenseRootB.lean` or `DenseRoot.lean`.
   - `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all seven declarations: `consPath`, `exists_lovasz_connector`, `connector_core`, `exists_decomp_of_connector`, `exists_decomp_of_connector_mid`, `test1At_of_connector`, `test1At_of_connector_mid`. `GPath.liftLe` gives `[propext, Quot.sound]`.
2. **Both headline theorems formalise Theorem 4.1 exactly**, for δ = 0 and δ = 1:
   - the hypotheses match;
   - the condition matches, with the same floors, [t ≤ λ], h̃ and t-range;
   - the conclusion matches (k paths, exactly two ends at r).
   - The parameter λ, which may be any upper bound, is harmless: the condition is antitone in λ.
3. **The Lean is more general in one respect, and this matters (F1).** The δ = 1 theorem has no length bound, so it also covers connectors of length 3, `q₁ y s q₂` and `q₁ s y q₂`.
   - At order 9 this certifies (T1) at **28 roots** that the manuscript counts as outside Theorems A and B. All 28 are among the 52 roots "with no short connector" in §5 and §8.
   - I instantiated `test1At_of_connector_mid` at all 28 in Lean; every instance compiles with the standard axioms.
4. **Non-vacuity.**
   - Both theorems and both spine forms are instantiated in Lean, with every side condition closed by kernel `decide`.
   - This includes a 3-connected order-9 root for each spine form where t = 3 is in range and the condition is tight (⌊h̃₃/2⌋ + 1 + 3 = 5 = k + 1).
5. **The spine forms are correct specialisations to B = J − z.**
6. **The docstrings and Remark 4.3 have small inaccuracies** (F2–F6).

**Recommendation.** Accept the Lean. Act on F1: either state Theorem 4.1 at the generality of the Lean and update the counts, or say explicitly that the counts use only connectors of length ≤ 2. The rest are NITs.

---

## 1. Faithfulness: Theorem 4.1 against the Lean statements

Paper: l.253–269. Lean: `exists_decomp_of_connector` (δ = 0, l.561), `exists_decomp_of_connector_mid` (δ = 1, l.836). Signatures are printed by `axioms.lean`.

| Item | Paper | Lean | Grade |
|---|---|---|---|
| Order, root degree | \|B\| = 2k ≥ 4, d_B(r) = 2k − 2 | `hk : 2 ≤ k`, `hW : card W = 2k`, `hr : B.degree r + 2 = 2k` | SOUND |
| G = B − r | B − r | `starDel B r`, with r isolated. Q has positive length, so r ∉ V(Q) | SOUND |
| Ends of Q in N | q₁, q₂ ∈ N | `hq1`, `hq2` | SOUND |
| δ = 0 | length 1, or middle vertex ∉ N, i.e. Q = q₁q₂ or q₁sq₂ | `hQint`: every vertex of Q adjacent to r is an end | SOUND. Same class: interior ⊆ V(G) ∖ N = {s}, so the length is ≤ 2 |
| δ = 1 | Q = q₁yq₂, y ∈ N | `y`, `hy`, `hyr`, `hy1`, `hy2`; `hQint`: N ∩ V(Q) ⊆ {q₁, q₂, y} | More general: interior ⊆ {y, s}, so the length is ≤ 3, which adds q₁ysq₂ and q₁syq₂ (F1). `hy` is unused by the proof (F5) |
| Parity | every x ∈ N odd in G' = G − E(Q) | `hodd` on `delList (starDel B r) Q.edges` | SOUND |
| λ | Σ_{v∈V(Q)} ⌈d_{G'}(v)/2⌉ | any `lam ≥ Σ_{v ∈ support.toFinset} (d_{G'}(v)+1)/2` | SOUND. Equivalent: set lam to the sum. The condition only weakens as λ decreases |
| h̃_t | #{x ∈ N ∖ V(Q) : d_B(x) ≥ 2t} | `#((heavyNbrs B r t).filter (· ∉ Q.walk.support))`, where `heavyNbrs` is N filtered by 2t ≤ d_B | SOUND |
| Condition | ⌊(h̃_t+δ)/2⌋ + [λ ≥ t] + t ≤ k+1 or ⌊(h̃_{t+1}+δ)/2⌋ + [λ ≥ t] + 2t ≤ k+1, for 3 ≤ t ≤ k−1 | identical: ℕ-division, `if t ≤ lam then 1 else 0`, `3 ≤ t → t ≤ k - 1` | SOUND |
| Conclusion | k paths, exactly two ends at r | `∃ D : PathDecomp B, D.size = k ∧ D.ends r = 2` | SOUND |
| "Every Lovász decomposition of G' gives one" | stated | existential only. The proofs start from an arbitrary `lovasz_ends` decomposition, but no Lean statement quantifies over D | NIT (F3) |

**Literal cross-check at order 9** (`lean_hyp_cov.py`).
- **Method.** I evaluated the Lean hypotheses as written in the signatures at all 1,262 roots with s ∈ Z. I enumerated every path of G with ends in N, with no length bound, and wrote my own graph6 parser.
- **Lengths allowed by the hypotheses.** Admissible δ = 0 connectors have length 1 or 2 only; admissible δ = 1 connectors have length 2 or 3 only. This confirms the forced length bounds.
- **Agreement with the paper.** On connectors of length ≤ 2, the Lean condition and the paper's formula agree on every connector (0 mismatches).
- **Counts.** The Lean δ = 0 theorem applies at 838 roots, and at 1,143 roots with connectors of length ≤ 2. Both match Table 1.
- **The extension.** With length-3 connectors the count is **1,171**.

**Other items.**

| Item | Grade | Notes |
|---|---|---|
| `GPath.liftLe`, `consPath` | SOUND | `consPath` is Q followed by the lifted paths of a decomposition of `delList G Q.edges`. Disjointness and covering use `delList_edgeSet`. |
| `exists_lovasz_connector` | SOUND | Its docstring is accurate: ends are exactly N, and there are k − 1 paths. The argument: evenSet(G') ⊆ {s}, Σ e = \|N\| + e(s), and e(s) is even and ≤ 1. |
| `connector_core` | SOUND | Hall counting for any attachment plan, with one optional exempt far end `jU` (the "+[jU.isSome]" term). Its docstring omits `jU` (F4). |
| Attachment plans | SOUND | They match the paper's rules. δ = 0: if P(q₁) = P(q₂), Q is attached at q_Q and the path at q_O; otherwise the lighter of o(q₁), o(q₂) is paired with the heavier. δ = 1: Case A, o(y) ∈ {q₁, q₂}, unpaired end o(q_O); Case B, otherwise, unpaired end o(y). The remaining L-paths are attached at the heavier end. |
| Spine forms | SOUND | `hW` comes from `card_delVert` and `hV` (2k + 1 − 1 = 2k). d_B(r) + 2 = 2k comes from `delVert_degree` with `J.Adj r z` (d_J(r) = 2k − 1 = n − 2). The hypotheses are stated on B = `delVert J z`, with degrees d_B; Cor. 4.2 (J-form) stays paper-only, as Table 1 says. 3-connectivity and "z is the only even vertex" are not assumed: the spine forms are more general than the Setting. `Test1At` gives size ≤ (2k+1−1)/2 = k and ≥ 2 ends at r. |
| Results table, l.117 | SOUND | "Theorem B … proved, Lean; Cor. 4.2 paper." |
| Files section | SOUND | The declaration list, the axiom claim and the 18,436 jobs all check. |
| Abstract (iv), l.44–46 | SOUND as a statement | "the even vertices of B − r are q₁, q₂, s and a path Q from q₁ to q₂ meets N(r) in at most one further vertex" is equivalent to the Lean hypotheses: interior vertices keep their parity, ends flip, and s is forced even. It is the Lean generality, not Theorem 4.1's, and the next sentences undercount it (F1). |

---

## 2. Findings

**F1 (GAP). The formalised Theorem B is stronger than Theorem 4.1, and the paper's counts and open problems do not reflect it.**

*Locations.*
- Theorem 4.1 (l.254), which says "of length 1 or 2".
- Cor. 4.2 (l.307–311).
- Abstract l.48–51: "distance at most two"; 1,602 / 1,445.
- Table 1 (l.379–380).
- §5 l.394–398: "154 roots outside", "52 roots … no connector of length ≤ 2".
- §8 item 2 (l.521): "No short connector … open".
- README l.32 and l.45.

*What the Lean proves.* `exists_decomp_of_connector_mid` holds for every connector whose only N-vertices are q₁, q₂ and one interior y. That allows q₁ y s q₂ and q₁ s y q₂, which Theorem 4.1 excludes. The paper's δ = 1 proof also covers these word for word: s ∉ N is never a trivial member and only enters λ.

*Order 9* (`len3_roots.py`, `dist_check.py`).
- 28 roots have an admissible length-3 connector, all at dist_G(q₁, q₂) = 3. All 28 satisfy the degree condition.
- The other 21 distance-3 roots have no path q₁ys q₂ or q₁syq₂. The 3 distance-4 roots have no admissible connector either.
- 27 of the 28 are among multi-token's unscheduled roots.
- `len3_instances.lean` proves `Test1At` at all 28 with `test1At_of_connector_mid`. Each instance is closed by `decide` and uses the standard axioms.

*Consequences.*
- Theorem B: 1,143 → **1,171**.
- A ∪ B: 1,602 → **1,630**; unscheduled roots 1,041 → **1,068** and 1,445 → **1,472**.
- Roots outside A ∪ B: 154 → **126**, as 24 + 102. The 102 are unchanged: no length-3 connector passes where every length-≤2 connector fails.
- "No short connector" now applies to **24** roots: 21 at distance 3 and 3 at distance 4.
- The abstract is also internally inconsistent: (iv), as phrased, covers these 28 roots, but the next sentence and the counts do not.

*Fix, preferred.*
- State Theorem 4.1 at the Lean's generality: Q is a path of G with ends q₁, q₂ ∈ N meeting N in at most one further vertex, and δ = |V(Q) ∩ N| − 2. It follows that Q ∈ {q₁q₂, q₁sq₂, q₁yq₂, q₁ysq₂, q₁syq₂}.
- Add one sentence to the δ = 1 proof.
- Extend Cor. 4.2 to "or q₁, q₂ are joined by a path q₁ys q₂ or q₁syq₂ in J − {z, r} with y ∈ N".
- Update the numbers above in the abstract, Table 1 (a row "Theorem B, all admissible connectors"), §5, §8 item 2 and the README.

*Fix, minimal.* Keep Theorem 4.1. Say in Remark 4.3 and in the caption of Table 1 that the Lean δ = 1 theorem also covers q₁ysq₂ and q₁syq₂, and that the counts use length ≤ 2 only. Then §8 item 2 must say that 28 of the 52 roots are covered by the Lean theorem.

**F2 (NIT). Remark 4.3, l.323: "neither needs the length of Q to be at most two" is imprecise.**
- It is literally true, but the hypotheses bound the length anyway. For δ = 0 the interior lies in {s}, so the length is ≤ 2: no generality is gained. For δ = 1 the interior lies in {y, s}, so the length is ≤ 3.
- *Fix:* "the δ = 0 hypotheses force length ≤ 2; the δ = 1 theorem also covers q₁ysq₂ and q₁syq₂ (length 3)".

**F3 (NIT). Remark 4.3 omits that the Lean conclusion is existential.**
- Theorem 4.1 ends "every Lovász decomposition of G' gives one" (l.268). No Lean statement quantifies over the Lovász decomposition. The proofs do start from an arbitrary `lovasz_ends` decomposition, and `connector_core` is stated for an arbitrary D.
- The paragraph after Theorem A has this caveat (A39 F10); Remark 4.3 does not.
- *Fix:* add the same parenthesis.

**F4 (NIT). Docstrings.**
- *Module header* (l.3–17): it says "Theorem 4.1 with `δ = 0`", and its bullet list names only the δ = 0 results. It does not mention `exists_decomp_of_connector_mid`, `test1At_of_connector_mid` or `exists_lovasz_connector`. This is stale since 33fc1f0.
- *`connector_core`* (l.132–135): the docstring says partners exist for all j ≠ iQ. It omits:
  - the optional exempt index `jU`, whose far end is unpaired and which adds `[jU.isSome]` inside both floors;
  - the requirement that each partner `π j` be the attachment of some L-path (`hπdes`). This is what makes far ends and partners disjoint.
- The other docstrings are accurate. In `exists_decomp_of_connector`, "d(x)" means d_B(x).
- *Fix:* update the header; add "except at most one far end (`jU`)" and "an attachment" to the `connector_core` docstring.

**F5 (NIT). Unused hypotheses** (`unused_hyps.lean` walks the proof terms).
- `hy : y ∈ Q.walk.support` in `exists_decomp_of_connector_mid` is unused, so the theorem holds for any neighbour y ∉ {q₁, q₂} of r. When y ∉ V(Q) it is a weakening of the δ = 0 theorem, so nothing is gained.
- `hjU : ∀ j, jU = some j → j ≠ iQ` in `connector_core` is unused.
- Keeping `hy` keeps the statement literal to the paper. Either drop both or rename them to `_hy` and `_hjU`.

**F6 (NIT). Code hygiene. Correctness is unaffected.**
- `exists_decomp_of_connector` re-proves `exists_lovasz_connector` inline: l.576–642 duplicate l.487–553. The δ = 1 proof calls the lemma.
- There are 59 linter warnings:
  - 45 deprecated `if_pos`, `if_neg` or `if_true`;
  - 8 unused simp arguments;
  - 2 unused variables (F5);
  - 1 unused section variable `[DecidableEq W]` in `delList_le'`.

---

## 3. What I ran

Every command is in `A39b-scripts/runs.sh`. All Lean commands were run from `lean/` with `lake env lean`.

- **`DenseRootB.lean`.** Compiled: exit 0, warnings only. `lake build`: "Build completed successfully (18436 jobs)". A grep for `sorry`, `admit`, `native_decide` and `axiom` in `DenseRootB.lean` and `DenseRoot.lean` found nothing.
- **`axioms.lean`.** `#print axioms` for the seven declarations (plus `consPath_length` and `GPath.liftLe`); `#check` of the full signatures; `#print` of `Test1At`, `delVert`, `delList`, `heavyNbrs`, `endsAt` and `ends`.
- **`unused_hyps.lean`.** A MetaM check of the binders unused by each proof term. Result: `connector_core` [hjU] and `exists_decomp_of_connector_mid` [hy]; none elsewhere.
- **`nonvacuous.lean`.** Eight theorems, all with standard axioms, every side condition closed by `decide`:
  1. δ = 0, k = 2: K₄ − rs.
  2. δ = 0, k = 4 on Fin 8: t = 3 in range, h̃₃ = 3, λ = 4, tight.
  3. δ = 1, k = 3.
  4. δ = 1 with a length-3 connector q₁ysq₂, k = 3.
  5. Spine δ = 0, k = 2.
  6. Spine δ = 0 at the order-9 root `Hsbfn\~` (J9_d6.g6 l.419): z = 5, r = 0, Q = q₁sq₂, λ = 4, h̃₃ = 2, tight.
  7. Spine δ = 1 at `HsaBe]~` (l.27).
  8. Spine δ = 1 at ``Hs`@dZ^`` (l.55) with a length-3 connector.

  For the order-9 graphs, `J_onlyEven` (z is the only even vertex) is also checked.
- **`sanity_fail.lean`.** It must fail, and does: `decide` rejects h̃₃ = 4. This shows the `decide` proofs are really evaluated.
- **`lean_hyp_cov.py`.** The Lean hypotheses evaluated literally at order 9, compared with the paper's formula: 838 / 1,143 / 1,171; length distribution; 0 mismatches.
- **`len3_roots.py`, `dist_check.py`.**
  - The 28 roots reachable only through length 3: all at distance 3, 27 of them unscheduled.
  - Distances recounted: 670 / 540 / 49 / 3, so 52 = 49 + 3 as in §5.
  - Unscheduled roots: 1,041 with length ≤ 2 and 1,068 with all lengths.
  - Of the 49 distance-3 roots, 28 have a q₁ysq₂ or q₁syq₂ path.
- **`gen_len3_instances.py` → `len3_instances.lean`.** 28 `Test1At` theorems via `test1At_of_connector_mid`. All compile (19 s), all with `[propext, Classical.choice, Quot.sound]`.

I modified no file outside this report and `A39b-scripts/`, and committed nothing.
