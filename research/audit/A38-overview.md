# Audit A38: the programme paper `manuscripts/overview/overview.tex`

**Target.** `manuscripts/overview/overview.tex` at commit **f0b8752** (branch `claude/overview`).
During the audit the branch moved to 4e79079; only `scripts/converses_run.txt` and a `.gitignore`
changed (`git diff f0b8752 4e79079 --stat`), so the paper audited is the paper of f0b8752.
Numbering is that of a fresh compile in a scratch copy (pdflatex ×3, no warnings, 19 pp., same as
the committed PDF). Components were recompiled the same way; terminal-matching does not compile
(a `\cite[...]` inside a theorem note, l. 241) and was read from its committed PDF.

**Referee stance.** Adversarial. Grades: **SOUND**, **GAP** (fixable omission), **ERROR** (false as
stated), **OVERCLAIM** (true content, status or scope overstated), **MINOR** (wording, labels,
citations; no mathematical effect).

**Independence.** Everything in `research/audit/A38-scripts/` was written for this audit from the
paper's text; nothing is imported from `manuscripts/overview/scripts/` or from any component's
scripts. nauty (`nauty-geng`) was installed in the container from the Ubuntu archive for graph
generation. Logs are next to the scripts.

## 0. Verdict

The mathematics that the paper proves itself is correct. The stripping lemma (Lemma 3.2), both
cases of the all-odd lift (Theorem 3.10), the three converses (Propositions 3.11, 3.15, 3.17), the
deletion step (Lemma 3.13) and every claim of Example 3.12 survive a line-by-line check and an
independent exact computation. The computation is larger than the paper's own: every rooting, not
only admissible ones; Lemmas 3.1 and 3.2 asserted on every instance; and the order-9 statement of
Example 3.12 re-derived over all 25,210 roots. Every quoted count that I could recompute (717,942;
478/554; 10,118; 8,340; 2,435/2,438; 1,597; the four order-10 instances; triangle bases at every
order-9 root with data) agrees. All 104 Lean names exist, in the stated files.

What does not survive is a layer of status and scope claims:

- **Two errors of fact (F1, F2).**
  - `HsaAD~}` does not have an independent N(z). The claim is inherited from direct-test1 Ex 4.7,
    which contradicts its own Remark 4.8.
  - The frontier section twice says that the residual has *bounded degrees*. Only d(z) is
    bounded; δ(B) ≥ 6 is a lower bound.
- **Four status upgrades (F3–F6).**
  - Figure 1 draws the literature → RE arrow as a Lean implication.
  - Figure 1 draws DL(1) → DL(k) as a paper-proved implication. No such implication exists; the
    paper's own text says compatibility is open.
  - Table 1 credits audit A28 with `test1At_of_disjL1`. A28 §7 explicitly lists `TriangleBase.lean`
    and DL as *not audited*.
  - The abstract and §1.4 say single constraints with one even vertex are "proved outside an
    explicit core". The non-blocked L₁* instances are only *reduced* to that core.
- **Two scope overclaims in §6 (F7).** The all-odd 54/54 data are random graphs, not residual roots.
  "The bases themselves exist at all these roots" is not backed by a cited source for the
  multi-token residual seeds, the clt graph, or the all-odd bases.
- **Minor items.** Nineteen label, hypothesis and citation slips (F8–F26), listed below.

§9's six disagreements are all real and correctly described; it misses four further ones (F27).

## 1. Findings

| id | location | grade | reason | suggested fix |
|---|---|---|---|---|
| F1 | Ex 3.9, l. 442 | **ERROR** | `HsaAD~}` "N(z) independent" is false: N(z) = {0,2,3,4,5,6} spans the star 0–2,0–3,0–4,0–5. Inherited from direct-test1 Ex 4.7, contradicted by its Rem 4.8. | "N(z) − r is independent at the failing root r = 0; J[N(z)] is K_{1,4} at r plus an isolated vertex". Add to §9. |
| F2 | §6.3(5) l. 1046; §6.4 bullet 2 l. 1063 | **ERROR** | "the degrees are bounded" / "δ(B) ≥ 6 are bounded". δ(B) ≥ 6 is a lower bound; residual degrees are unbounded (C4 open for twins of degree ≥ 8, isolated roots with d(r) ≥ 8, generic exterior degree ≥ 5). | "Only d(z) = 6 is bounded; the minimum degree is only known to be ≥ 6, so it need not be linear in \|J\|." |
| F3 | Fig. 1, l. 220 (`\draw[L] (LIT) -- (RE)`) | **OVERCLAIM** | Solid means Lean, but Thm 4.4 (planar, tw ≤ 3, Δ ≤ 4, …) is [paper] from the literature. Only Thm 4.5 (degree n − 2) is Lean. | Split LIT into two boxes: dashed from the literature, solid from `rootedDecomp_of_degStar`. |
| F4 | Fig. 1, l. 228 (`\draw[P] (DL1) -- (DL)`) | **OVERCLAIM** | Dashed means "proved on paper", but DL(1) ⇒ DL(k) is not proved. §5.4 and the abstract say compatibility is open. | Delete the arrow, or draw it as "special case k = 1" in a fourth style, with the direction reversed. |
| F5 | Table 1, l. 1101 | **OVERCLAIM** | "A28 (re-check §7)" for `test1At_of_disjL1`. A28 §7, "Not audited (new content)", lists DL (`DisjL1`), `triangleBase_of_disjL1_reach` and `TriangleBase.lean`; the name does not occur in A28. | Audit column: "none". |
| F6 | Abstract l. 65; §1.4 l. 167 | **OVERCLAIM** | "single constraints are proved outside an explicit core". For a ≁ g the constraint is an L₁* instance. `l1starGen_of_blocked` is a global induction (L1Blocked ⇒ L1StarGen), so non-blocked instances are proved only *assuming* the core. | "reduced to an explicit core". |
| F7 | §6.1 label l. 995; §6.2 last line l. 1027 | **OVERCLAIM** (scope) | 54/54 is from random 3-connected J of orders 7–11 (`research/coordinator/alloddlift.py`, enumeration capped at 4,000), not residual roots. No cited source checks triangle bases on multi-token's own residual seeds or the clt graph, or all-odd bases anywhere beyond 54 roots. The A38 runs support the claim at order 9 (§3.4). | State the scope; cite A38 for order 9; drop "all these roots" for the residual families. |
| F8 | §5.3 l. 900; §6.2(3) | MINOR | The steering "residual families" (72/180, 109/144) are multi-token's own seeds (its Table 3: "our seeds, since those of [1, §5] are not recorded"), not the direct-test1 families of Conj 3.6. 109/144 includes a C4 subfamily at \|O\| = 8. | Say so. |
| F9 | Lemma 5.1, l. 775 | MINOR | Tagged Lean `fan_single_supp`, which proves only V(Q) ⊆ V(Q′) ∪ {u} for some Q′: no bijection, no equality. The bijection form is route-descent Lemma 2.2 (paper). | Tag the bijection [paper] and the containment [Lean]. |
| F10 | Prop 5.6, l. 847 | MINOR (GAP) | `csys_caseI` and clt Thm 5.3 also need "u is not avoided" (`hu : ¬ S.Avoided u`). | Add the hypothesis. |
| F11 | Def 5.8 (S), l. 879; Thm 5.9 | MINOR | The suppression move drops its conditions (neither neighbour a leaf of a tail; {a,b} ≠ {x,s} for a live tail) and its effect (K − pa − pb + ab). Thm 5.9 drops (TS) and (TI). | Restore. |
| F12 | Thm 3.18, l. 610–614 | MINOR | `test2At_of_pair_farApart` and `test2At_of_pair_steer2` have the extra hypothesis d_J(w) ≥ 3 (`hw3`); the paper's (T2) setting assumes only d_J(r) ≥ 3. | Add d_J(w) ≥ 3, or "J 3-connected". |
| F13 | Thm 3.10 label l. 463; §5.5(4) l. 966 | MINOR | "[paper: synthesis §31]": synthesis.md is not a manuscript (§1.3 defines [paper]). The all-odd steering obstruction has no written proof: multi-token has no §7 / Prop 7.2, and the Lean docstring only sketches the start counts. The arithmetic does check (§2.6). | Tag [new] or [coordinator note], or give the two-line start-state count. |
| F14 | Abstract l. 55 | MINOR | "for fixed data, a base exists iff the test holds with a prescribed terminal matching or forest". For the floor lift the equivalent is the *floor bound* with terminal Φ, which is strictly stronger than (T2) and fails at all 20 tight instances. §3.5 says this correctly. | "…iff the test (for the floor lift, the floor bound) holds with…". |
| F15 | Table 1, l. 1127 | MINOR | Audit A16 for `gallai_of_routeRR`: A16 never mentions it. It cross-checked `RouteSystem.lean` statements (`realisable_of_compatible`, `Compatible`), S39. | "A16 (RouteSystem statements)". |
| F16 | Table 1, spine and Lovász rows; l. 1080 | MINOR | `SpineAxioms.lean` holds the `#print axioms` *commands*, not their output. The record is spine.tex §8 / A14 / `lean/README.md`. | Cite the record. |
| F17 | Thm 2.2 proof, l. 294 | MINOR | "Audits A1, A2 and A14 found no gap in MR". A1 and A2 found no *error* but list GAP/UNCLEAR items: A2 §0 interface issues (FHZ, Shaik, missing supplement); spine: "found no error but recorded gaps in its exposition". | "found no error". |
| F18 | Thm 2.2 proof, l. 279 | MINOR | The bridge double is spine Lemma 7.1; Lemma 7.2 is the rooted bounds, Prop 7.3 the forward direction. | "spine Lemmas 7.1–7.2, Prop 7.3". |
| F19 | §5.2, l. 856 | MINOR | "dl-one Thms 5.1, 6.1": Thm 6.1 assumes d(a) ≥ 3 and gives S_a; DL(1) at d(g) = 2 is Cor 6.2 (`disjL1_deg_two`). | Cite Cor 6.2. |
| F20 | §5.4(4), l. 922 | MINOR | "l1star Conjs 1.2, 1.3; Lean L1Star, L1Blocked". Conj 1.3 is the general form (`L1StarGen`); L1Blocked is the blocked case (Def 4.1, Thm 4.3); the statement displayed is Conj 1.3, while `L1Star` has \|A\| ≤ 2. | Pair 1.2 ↔ `L1Star`, 1.3 ↔ `L1StarGen`; L1Blocked ↔ Def 4.1/Thm 4.3. |
| F21 | Prop 3.5 label, l. 399–400 | MINOR | "checked exhaustively … 1,148 at order 9": these were data choices on *random* order-9 graphs (direct-test1, after Prop 2.2). | "1,148 data choices on random graphs of order 9". |
| F22 | Ex 3.9, l. 445 | MINOR | "The variant in which Φ passes through r also fails there (synthesis §25)": §25 tested only the K_{2,6} cone. True at `HsaAD~}` root 0 as well (A38, `thru_r=False`). | Cite A38 for the third root. |
| F23 | §9(6), l. 1178 | MINOR | "(T2) at d(z) = 6 and 8 is closed in the collection" omits what Rem 2.3 records: Thm 128 is conditional on FHZ for two seven-site shapes and on an unquoted CFZ lemma (A8 U1–U2). | Add "(d = 8 conditional; Rem 2.3)". |
| F24 | §1.3, §8 | MINOR | At f0b8752 `converses_run.txt` was empty; the quoted 2,154/869/1,329 etc. were committed only in 4e79079. They now agree with the paper. | None (process note). |
| F25 | Def 2.1 and every "z the only even vertex" | MINOR | The paper's convention lets other isolated vertices exist. Lean's `Test1` and the `hz` hypotheses use `Even (degree v) ↔ v = z`, so degree 0 counts as even and isolated vertices are excluded. Harmless for 3-connected J. | Remark that the Lean form excludes isolated vertices. |
| F26 | §9(5), l. 1176 | MINOR | A data file is typeset with `\lean{…}`. | `\texttt`. |
| F27 | §9 | GAP | Missing disagreements: (a) F1 (direct-test1 Ex 4.7 vs Rem 4.8 vs the graph); (b) direct-test1 Ex 4.7 says H = J − {z,r} is "the star with centre r" (it is centred at r′); (c) the `Test2Lift.lean` docstrings cite `manuscripts/test2/test2.tex` and its Thm 3.2, 4.1, Cor 4.2, 4.4, Prop 5.3, Cor 5.4, none of which exist; (d) synthesis §31 addendum says the `not_steerK` invariant is "generalised [in Lean] to cover" the all-odd setting, but the Lean docstring says that instance is "applied on paper only" (the paper follows Lean, rightly). | Add (a)–(d). |
| S1 | Lemma 3.2 | SOUND | Hand proof checked; asserted on every stripped decomposition of every instance in §3.3 (strip_equal counts there). | — |
| S2 | Thm 3.10 (a), (b) | SOUND | Parities and the end count b(r) = 1 − [r child] + c(r) checked; asserted on every lift executed. | — |
| S3 | Props 3.11, 3.15, 3.17 | SOUND | Hand proofs checked; 0 disagreements in the exact runs of §3.3, for every rooting. | — |
| S4 | Lemma 3.13 | SOUND | Both directions checked by hand; the (T2) step executed on every admissible positive (T2)-instance. | — |
| S5 | Ex 3.12 | SOUND | Every claim reproduced exactly (§3.2); the order-9 statement re-derived over all 25,210 roots (§3.4). | — |
| S6 | §3 numbers, §5–6 numbers | SOUND | See §4. | — |
| S7 | §6.2(2) `not_steerK` | SOUND | The two inequalities, the entry argument and the end violation match `ObstrInv.tok`/`.pot` and `not_steerK` (`MultiTokenObstruct.lean` l. 481). | — |
| S8 | §6.4 GGKO; Thm 4.4 (a), (e) | SOUND | Checked on arXiv (§5). | — |
| S9 | §9 items 1–6 | SOUND | Each is real and correctly described (§6). | — |

Counts: ERROR 2, OVERCLAIM 5, GAP 1 (F27; F10 is graded MINOR (GAP)), MINOR 19, SOUND 9 groups.

## 2. Details of the non-SOUND findings

### F1. `HsaAD~}` and "N(z) independent"
`HsaAD~}`: z = 7, N(z) = {0,2,3,4,5,6}. Adjacency, from `roots_bases.py`:

    0: 1 2 3 4 5 7 8    1: 0 6 8    2..5: 0 7 8    6: 1 7 8    7: 0 2 3 4 5 6    8: 0..6

The edges inside N(z) are 02, 03, 04, 05.
- direct-test1 Ex 4.7 says "(graph6 HsaAD~}), where d(z) = 6 and N(z) is independent".
- direct-test1 Rem 4.8 says "the even subgraph of B is a star with four leaves at r, plus an
  isolated vertex", which is the true picture.

The overview copies Ex 4.7. What is true is that J[N(z) − 0] is independent, which is why root 0
has no triangle data. Every other root of `HsaAD~}` also lacks triangle data, because N(z) − r
contains the star at 0, with ν = 1.

### F2. "Bounded degree"
- §6.3(5): "In the residual d(z) = 6 and δ(B) ≥ 6 are bounded, while |J| is unbounded."
- §6.4: "the degrees are bounded and |J| is not."

t6-dense §1 and STATUS §3.5(a) give only lower bounds: δ(B) ≥ 6, δ(B[O]) ≥ 4, and at least three odd
neighbours per even site. They list as open "C4 with twins of degree ≥ 8" and "generic exterior
degree ≥ 5". MR Thm 144's failing roots have d(r) ≥ 8. Nothing bounds the maximum degree.

The GGKO comparison survives on its other two grounds, which are correct:
- the o(n) error;
- minimum degree that is not linear in |J|.

### F3, F4. Figure 1 arrow styles
Caption: "Solid arrows are implications proved in Lean, dashed arrows are proved on paper."
Checked arrow by arrow against the Lean source:

- **Correct.** T1→G and T2→G (`gallai_iff_spineTests'`); TB→T1; FB→T1 (`test1At_of_forestBase`);
  F2→T2 (`test2At_of_forestBase2`); FL→T2 (`test2At_of_floorBase`); SK→TB
  (`triangleBase_of_steerK`); DL→TB (`triangleBase_of_disjL1_reach`); DL→FL (`test2At_of_disjL1`,
  through `floor_of_matchingBase`); S2→FL (`test2At_of_pair_*`); TRN→N (`conjN_of_core2`);
  RE⇔T1 (`test1_fullCone_iff`); AO→T1 dashed (paper only).
- **Defensible.** ONE→SK: `avoid_leafTail` uses `lovasz_avoid_nonadj`, `TRNSteer.lean` l. 67.
  L1S→DL: `triangleBase_of_L1Star`, with the caption's restriction. AODL→AO and AODL→F2: the
  bases are instances of the problem.
- **Wrong style (F3).** LIT→RE is solid. The literature cases of Thm 4.4 are [paper]. They enter
  only through the Lean bridge lemmas `rootedDecomp_iff_addLeaf` and `rootedDecomp_of_dbl`, and
  the external theorems (BBB, BSCL, Anto–Basavaraju, ZLH, BP, BS) are not formalised.
- **Wrong arrow (F4).** DL1→DL (dashed) asserts that DL(1) implies DL(k), on paper. The paper
  itself says (abstract; §5.4(1); §6.3(1)) that what is open beyond DL(1) is compatibility.

### F5. Table 1, DL ⇒ (T1)
A28 §7, after the rewrite, has a list "**Not audited (new content):** … §6, 'Toward the conjecture':
… Conjecture DL (`DisjL1`), `triangleBase_of_disjL1_reach`; `TriangleBase.lean`; E29", and
recommends a follow-up audit A28b. `grep test1At_of_disjL1 A28-direct-test1.md` finds nothing.
The axiom record [R] is fine: `lean/README.md` triangle-base section, blanket statement.

### F6. "Proved outside an explicit core"
dl-one §1: "a ≁ g: S_b is an instance of the avoidance conjecture L∗1 … which is open; it reduces to
its blocked case". l1star Thm 4.3: "If every blocked instance is good, every instance is good"
(Lean `l1starGen_of_blocked : L1Blocked → L1StarGen`). So a DL(1) pair with a ≁ g and a common
neighbour is proved only under L1Blocked, which applies to all graphs, not only that instance.
The abstract reads as if such instances were theorems.

### F7. Scope of the 54/54 and "the bases exist"
- `research/coordinator/alloddlift.py` draws J from `verify3.gen_J` (G(n,p) plus parity repair,
  orders 7, 9, 11) and calls `lovasz_decomps(Hh, cap=4000)`. The log reads
  `FINAL {'roots': 60, 'data': 54, 'ok': 54 …}`.
- §3.4 states this scope correctly. §6.1 places it under the dense residual and calls it "exact".
- §6.2's "these roots" include:
  - multi-token's residual families, generated with multi-token's own seeds (Table 3 caption);
  - the clt graph `M~~zRz{~m~~lX|j~_`;
  - the all-odd steering roots.

  No cited source checks triangle bases on the first two, or all-odd bases at all; the multi-token
  README says only "the triangle base holds in all data [1, §5], without proof", meaning
  direct-test1's own families.
- A38 evidence at order 9 (§3.4):
  - triangle bases at all 22,772 data roots;
  - all-odd matching bases (case (a)) at all 8,340 roots at d(z) = 6 that have a perfect matching
    of J[N(z)], including all 1,546 of degree 7 = n − 2.

### F9–F12. Hypotheses
- **F9.** `fan_single_supp` (`FanSupport.lean` l. 449) concludes
  `∀ Q ∈ D.paths, ∃ Q' ∈ D'.paths, ∀ x ∈ Q.walk.support, x ∈ Q'.walk.support ∨ x = u`.
  This is weaker than the bijection with equal vertex sets of route-descent Lemma 2.2.
- **F10.** `csys_caseI (… (hfar : ∀ w, S.Touched w → w ≠ u ∧ w ≠ g ∧ ¬ G.Adj w u)
  (hu : ¬ S.Avoided u) …)`. Without `hu` an avoided u could be added to the path ending at its tail.
- **F11.** Multi-token Def 2.2(S): "a token p with N_K(p) = {a, b}, a ≁ b, neither a nor b the leaf
  of a tail, and {a, b} ≠ {x, s} for every live tail; then K′ = K − pa − pb + ab".
- **F12.** `test2At_of_pair_farApart … (hw3 : 3 ≤ J.degree w)`, and likewise `…_steer2`.

### F13. The all-odd obstruction
- Lean docstring (`MultiTokenObstruct.lean`, header): "In the all-odd lift (manuscript §7, synthesis
  §31) the start has k tokens, k live tails, ρ = 1 … and |A| = t + 1 …, so t ≤ k − 2 excludes every
  schedule; that instance is applied on paper only."
- The multi-token manuscript has sections 1–8, with §7 "Formalisation" and no all-odd material, so
  "manuscript §7 / Prop 7.2" does not exist. That part of §9(4) is correct.
- My check of the arithmetic. In the invariant of `not_steerK`, `tok` reads (t + 1) + 2 ≤ k + 1,
  that is t ≤ k − 2. `pot` reads (t + 1) + 3 ≤ 2k, which is implied by t ≤ k − 2 once k ≥ 2. The
  statement is therefore right, but it is proved nowhere in writing.

### F14–F26
Each one-line reason in the table is the evidence. The quoted sources:
- F17: A1 §0 "No ERROR found … up to the expository points"; A2 §0 "What remains are interface and
  dependency issues … listed as GAP or UNCLEAR".
- F21: direct-test1, after Prop 2.2: "the 1,148 data choices on random graphs of order 9".
- F23: Rem 2.3 of the overview itself.

### F27. Missing disagreements
- (a) See F1.
- (b) direct-test1 Ex 4.7: "Here H = J − {z, r} is the star with centre r". The case analysis that
  follows uses centre r′, correctly.
- (c) `Test2Lift.lean` header: "Manuscript: `manuscripts/test2/test2.tex`, §3", and the docstrings
  say "manuscript Theorem 3.2 / 4.1 / Corollary 4.2 / 4.4 / Proposition 5.3 / Corollary 5.4(a)";
  `manuscripts/test2/` contains no .tex file. The overview rightly reads the Lean instead.
- (d) synthesis §31 addendum: "Lean: the invariant of `not_steerK` … is generalised to cover this
  setting", whereas the Lean says "applied on paper only".

## 3. Independent computations (`research/audit/A38-scripts/`)

### 3.1 Engine
`a38lib.py` implements:
- an exact enumerator of path decompositions with at most p paths;
- forest T-joins, from a spanning forest plus the cycle space;
- rootings, forest stepping, stripping and terminal-at-parents;
- a constrained exact search `find_decomp` / `find_base`: end capacities per vertex, plus a
  per-path predicate.

`selftest.py` and an inline check compare the enumerator with a restricted-growth brute force:
1,360 comparisons, 136,695 decompositions, 0 mismatches. `find_base` agrees with enumerate-and-filter
on 94 random instances. K_{2,6} has 6,360 decompositions into ≤ 4 paths (the overview log says the
same).

### 3.2 Examples 3.9 and 3.12 (`roots_bases.py`, log `roots_bases_k26_hsaad.txt`)
Exact at every root, over every w, forest join and rooting.

**Cone over K_{2,6}** (z = 8): 3-connected, d(z) = 8.
- No root has triangle data, the six degree-3 roots included.
- Hubs 0 and 1:
  - forest base: none;
  - Φ-through-r variant: none;
  - all-odd case (a): none, with 32 forests and 128 rootings, as claimed;
  - all-odd case (b): present (300 rootings);
  - (T1): holds.
- Degree-3 roots: forest base and case (a) both present.

The explicit witness was checked by hand. Φ = {20, 03, 04, 51, 16, 17} has odd degree at every
vertex; H = {05, 06, 07, 12, 13, 14}. D = {506, 07, 213, 14} has one end per vertex; (i) and (ii)
hold. The lift {5061, 2071, 2130, 5140} covers all 12 edges once, with two ends at 0.

**`HsaAD~}`** (z = 7, N(z) not independent, F1). With 56 forest N(z)-joins:
- Root 0 (d_J = 7): no forest base; Φ-through-r variant fails too; case (a) none (128 rootings);
  case (b) present (358 rootings); (T1) holds.
- Roots 2–6: forest base and case (a) present; case (b) impossible, since d_B(r) = 2.

### 3.3 The converses (`conv.py`, logs `conv_small.txt`, `conv_B8.txt`, `conv_A9_le16.txt`, `conv_C7_le12.txt`; a wider ≤ 18-edge run at order 9 was stopped unfinished after 40 CPU-minutes)
**Method.**
- **LHS** (base exists): exact constrained search.
- **RHS** (decomposition within the budget with Φ terminal at parents): a constrained search with
  the per-path predicate "every Φ-edge on P is an end edge at its parent". On the smaller inputs it
  is also decided by full enumeration (`fullenum`), which must agree with the search.
- **Checks on every LHS witness.** It is lifted, and the lift is checked:
  - a path decomposition, with Φ terminal at parents;
  - b(u) = b₀(u) − [u child] + c(u) for every u (Lemma 3.1).
- **Checks on every RHS witness** (and, under `fullenum`, every RHS decomposition). It is stripped,
  and Lemma 3.2 is asserted: a decomposition of size ≤ |D|; if equal, every shortened path ends at
  its child and avoids the parent.
- **(A), every rooting.** No RHS decomposition has fewer than c(u) ends, or an odd number of ends,
  at any u ∈ N(z).
- **(B), admissible rootings.** No RHS decomposition has fewer than 2 ends at r. The Lemma 3.13
  step is executed and must give ≥ 3 ends at r within n/2 paths.

**Results.**

| prop | inputs | instances (all rootings) | agree | positive | other checks |
|---|---|---|---|---|---|
| 3.11 (A) | every connected J of order 5 and 7 with one even vertex, full enumeration | 5,974 | 5,974 | 4,036 | all end claims; 23,722 strips with equality |
| 3.11 (A) | every 3-connected one-even J of order 9 with ≤ 16 edges (277 graphs) | 44,675 | 44,675 | 39,507 | end claim (≥ c(u), even) asserted by search at every u ∈ N(z) |
| 3.15 (B) | every connected J of order 4, 6 with two adjacent even vertices, d(r) ≥ 3, full enumeration | 576 (231 admissible) | 576 | 514 | 215 (T2) executions |
| 3.15 (B) | every connected J of order 8 with ≤ 14 edges (5,850 graphs read) | 35,425 (12,261 admissible) | 35,425 | 32,800 | 11,272 (T2) executions |
| 3.17 (C) | every connected B of order 3, 5, and order 4, 6 plus an isolated vertex, full enumeration | 6,646 | 6,646 | 4,190 | |
| 3.17 (C) | every connected B of order 7 with ≤ 12 edges (614 graphs), every w | 70,904 | 70,904 | 45,292 | every lift and strip checked |

No disagreement anywhere; no assertion failed.

### 3.4 The order-9 statement of Example 3.12

**Census** (`census9.py`, `census9.txt`). Input: `nauty-geng -c -d3 9` filtered to 3-connected J
with exactly one even vertex. Output: 5,231 graphs (d(z) = 4: 3,250; 6: 1,819; 8: 162) and 25,210
roots, of which 22,772 have triangle data and 2,438 do not. At d(z) = 6:
- 10,118 roots have data;
- 8,340 roots lie in graphs with a perfect matching of J[N(z)];
- 1,597 roots have data and degree 7.

**Triangle bases** (`tri9.py`, `tri9.txt`, exact). At all 22,772 roots with data (11,389 / 10,118 /
1,265); every base lifted and verified.

**Roots without data** (`nodata9.py`, `nodata9.txt`, exact). Forest bases at 2,435 of 2,438. The
three exceptions are the two hubs of `H??F~z~`, which is isomorphic to the cone over K_{2,6}, and
root 8 of `H?AFvx~`, which is isomorphic to `HsaAD~}`. Each has an all-odd base in case (b) and none
in case (a).

So the statement is reproduced in full, independently of direct-test1's oracle runs and of the
overview's scripts.

**All-odd matching bases** (`allodd9.py`, `allodd9_d6.txt`, exact). Case (a), Φ a perfect matching
of J[N(z)], every orientation: present at all 8,340 roots at d(z) = 6.

### 3.5 Component data
- **`t2_nonroot10.py`.** At the four order-10 instances of `forestbase2_order10_nonroot.txt`, exact
  over all forest N(z)-joins (64 / 64 / 112 / 112): no (T2) forest base with r a root, and one with
  r a child having c(r) ≥ 2. "Need" is confirmed.
- **`dz4_8.py`.** At order 8: 948 instances, 637 with d(z) = 4, 554 with data, 83 without, and 478
  covered by separation or two-token steering. The theorem's hypothesis a ∉ Q(b) itself holds at
  548 of the 554. My FAR/STEER split is 128 + 350 (or 12 + 466 the other way round), against
  test2's 88 + 390. Only the total is quoted, and it agrees.

## 4. Numbers checked against components

| number in the paper | source | verdict |
|---|---|---|
| 717,942 (T2) instances; all witnesses verified | test2 README; `t2_order10.summary` (4 chunks, 716,984) + 948 + 10 | ✓ |
| forest base at every instance of orders 8 and 10; 4 need r a child | README; `forestbase2_order10.summary` (ABSENT 4 = exhaustive tier X, dim ≤ 14); `_nonroot.txt` | ✓ (A38 exact, §3.5) |
| 478 of 554 at d(z) = 4, order 8 | `dz4_order8.txt` (88 + 390) | ✓ (A38) |
| 20 tight instances, odd semi-cliques | README, `tight_le10.txt` (2 + 5 + 13) | ✓ |
| "98.5%" empty file (§9(5)) | `dz4_order10_sample.txt` is 0 bytes; ROADMAP l. 142 | ✓ |
| 7,529 / 10,118 (74%); 76,474 schedules | multi-token abstract, Table 1 | ✓ |
| 72/180, 109/144, 10/48 | multi-token Table 3 (6+15+19+14+18; 23+19+18+21+15+13) | ✓ (F8) |
| ROADMAP 71/180, 107/144 | ROADMAP l. 147 | ✓ disagreement real |
| 2,101 / 8,340 (25%) | `multi-token/data/runs/J9_d6_aodd.txt` SUMMARY | ✓; 8,340 also A38 |
| 1,597 roots of degree n − 2 unscheduled | multi-token §6; A38 census | ✓ |
| 53 proved-unscheduled, 42 frozen, 3 or 5 non-neighbours | multi-token §6 (33 + 12 + 6 + 2; 27 + 7 + 6 + 2; 38 + 4) | ✓ |
| 300,540 roots, 30,054 graphs; 14,156 tight, 14,131 at d(r) = n − 2 | eulerian-cone Table 1, §6.2 | ✓ |
| 13,507 by Thm 4.5 | re-tight §5 ("13,507 roots (95.6%)") | ✓ |
| 2,435 / 2,438 | direct-test1 §4 (`fb_nodata.py`) | ✓ (A38 exact) |
| 2,426 (κ = 2), 22,890 (κ ≥ 3); 59 failures at κ = 1 | direct-test1 §6.2 table | ✓ (A38: 22,772 at order 9) |
| 180, 144, 36; 48 E28; 71/71 at d(z) = 8 | direct-test1 §§6.3–6.5 | ✓ |
| 444 / 1,148 (Prop 3.5) | direct-test1 after Prop 2.2 | ✓ numbers (F21 wording) |
| 269M pairs to order 11 | dl-one §8 (268,990,425 at order 11) | ✓ |
| 12,312 graphs (CLT) | clt l. 82 | ✓ |
| 40/40, 54/54 (coordinator) | `research/coordinator/alloddlift_d{4,6}.log` FINAL | ✓ numbers (F7 scope) |
| 2,154/869/1,329; 1,872/822/921; 8,818/17,120/7,243 | `converses_run.txt` at 4e79079 | ✓ (empty at f0b8752, F24) |
| 32 forests, 128 rootings (K_{2,6}) | A38 exact; also by hand: d₀ ∈ {1,3,5}, 6 + 20 + 6 = 32; Σ(1 + d₁) = 36 + 80 + 12 = 128 | ✓ |

## 5. Literature (arXiv, fetched during the audit)
- **arXiv:1911.05501** (Girão–Granet–Kühn–Osthus, J. LMS 104 (2021) 1085–1134). From the PDF text:
  - Thm 1.10: for α, δ > 0 and n ≥ n₀, δ(G) ≥ αn ⇒ (i) at most n/2 + δn paths.
  - Thm 1.11: weakly-(α/2, p)-quasirandom and δ(G) ≥ αn ⇒ (i) at most max{odd(G)/2, Δ(G)/2} + δn
    paths.
  - Cor 1.12: δ(G) ≥ n/2 + εn ⇒ the same.
  - The abstract: "asymptotically best possible".

  The overview's §6.4 is accurate: "determine asymptotically" is fine, since max{odd/2, Δ/2} is a
  trivial lower bound. Thm 1.11 also keeps the linear minimum degree, which the overview's sentence
  leaves implicit.
- **arXiv:2110.08870** (Blanché–Bonamy–Bonichon, v2 21 June 2022). Every connected planar graph
  except K₃ and K₅ − e decomposes into ⌊n/2⌋ paths ✓.
- **arXiv:1609.06257** (Bonamy–Perrett). Gallai for Δ ≤ 5, i.e. (n+1)/2 paths ✓. The arXiv page
  carries no journal reference, so "Discrete Math. 342 (2019) 1293–1299" was not verified.
- **arXiv:2510.12806** (Chu–Wang, Oct 2025). 3n/5 for Eulerian graphs with triangles pairwise at
  distance ≥ 3 ✓. The journal reference was not verified.
- **arXiv:2611.21673** (Zhang–Liu–Hong, 14 Nov 2026). K₅-minor-free graphs, ⌊n/2⌋ except K₃ and
  K₅ − e ✓.

## 6. §9 checked item by item
1. **Real.** ROADMAP l. 164 and synthesis l. 799 say TRN ⇒ N ⇒ DL(1). dl-one Prop 9.2 is "Conjecture
   9.1 reduces DL(1) to near twins". The proof leaves N(a) − g = N(b) − g open.
2. **Real.** K_{2k} − PM is (2k − 2)-regular, so all its vertices are even and no Lovász
   decomposition is defined. (The all-Hamiltonian phenomenon belongs to K_{2k}, whose pairs are
   all adjacent.)
3. **Real.** Synthesis §31: "The forest version needs … r a root" and "fails on the cone over
   K_{2,6}". A38 confirms case (a) fails and case (b) succeeds.
4. **Real.**
   - The multi-token abstract says Prop 6.1 is "proved on paper".
   - Commit 9914d37 ("multi-token: Lean proof of the obstruction (Prop 6.1)") exists.
   - The Lean docstring cites a nonexistent Prop 7.2.
   - ROADMAP l. 147 gives 71/180 and 107/144.
5. **Real.** The file has 0 bytes; ROADMAP l. 142 cites it.
6. **Real** (a self-qualification), but see F23.

## 7. Lean (read, not built)
- **Names.** All 104 `\lean{…}` names resolve to declarations in the stated files; the one
  non-name is F26. `triM_parity` is `TriangleData.triM_parity`.
- **Statements checked against hypotheses and conclusions.** `Test1`, `Test2`, `Test1At`, `Test2At`,
  `gallai_iff_spineTests'`, `TriangleData`, `test1At_of_triangleBase`, `ForestData`,
  `test1At_of_forestBase`, `ForestData2`, `ForestBase2`, `test2At_of_forestBase2`,
  `test2At_of_leafDecomp`, `FloorData`, `FloorBase`, `floor_of_floorBase`, `test2At_of_floor(Base)`,
  `floor_of_matchingBase`, `test2At_of_disjL1`, `test2At_of_pairAvoid`, `…_farApart`, `…_steer2`,
  `DisjL1`, `UnivTwins`, `test1At_of_disjL1`, `disjL1_one_allOdd`, `L1Star`, `L1StarGen`, `L1Blocked`,
  `avoid_free_target`, `disjL1_free_target`, `csys_caseI`, `fan_single_supp`, `not_steerK`,
  `not_steerK_triangle`, the RETight corollaries, `append_forest_ends`.
- **Mismatches.** F9, F10, F12, F20, F25.
- **Axiom records.**
  - test2 / trn / multi-token `axioms.txt` list every [ax] name of Table 1.
  - `lean/README.md` sections give blanket standard-axiom statements for the [R] rows (cones,
    triangle-base, route-descent, NA, FanBarrier).
  - A23, A24, A25, A27, A29, A30, A31, A33, A35 and A20 each record a re-run.
  - Exceptions: F16 (the spine row's [ax] source holds commands only), F15, F5.

## 8. Not checked
- **Lean builds and axioms.** The toolchain could not be installed; all statements were read from
  source.
- **MR / collection results quoted through STATUS and A8** (Thms 123, 128, 144, root-shape theorem,
  OSB Cor 44). Taken from STATUS and the audits.
- **Steering and residual-family counts.** These are multi-token's searches; I re-checked them
  against the run summaries, not by recomputation. Triangle bases on multi-token's residual seeds
  (|J| = 15, 17) are too heavy for my Python search.
- **The (T2) order-10 exhaustive data.** Accepted from the test2 summaries, except the four
  nonroot instances.
- **DL(1) to order 11, CLT, MT and NA data.** Accepted from the components and audits.
- **The overview's own scripts.** Read for scope only, never run or imported.
- **The BP and CW journal references.** Not on the arXiv pages.

## 9. Author's response (overview session, after the audit)

Every finding was addressed in the commit that records this report. The paper also changed for reasons
outside the audit; those changes are listed at the end and were not audited.

| id | action |
|---|---|
| F1 | Ex 3.9 now says the root is r = 0 of degree 7, J[N(z)] is K_{1,4} centred at r plus an isolated vertex, and N(z) − r is independent. The direct-test1 Ex 4.7 slip is added to §9. |
| F2 | §6.3(5) and §6.4 now say only d(z) = 6 is bounded, and δ(B) ≥ 6 is a lower bound that need not be linear in \|J\|. |
| F3 | Figure 1: the literature box has a dashed arrow (literature cases) and a solid arrow (Lean, degree n − 2); the caption says so. |
| F4 | Figure 1: the DL(1)–DL(k) arrow is replaced by a thin grey line labelled k = 1, and the caption says it is not an implication. |
| F5 | Table 1: audit "none (A28 §7 lists TriangleBase.lean as not audited)". |
| F6 | Abstract and §1.4: single constraints with one even vertex are *reduced* to an explicit core. The abstract adds "TRN implies N (Lean), N reduces DL(1) to near twins, and near twins are open" (coordinator's wording). |
| F7 | §3.4: the cap of 4,000 is stated, and A38's exact order-9 result (8,340 roots, 1,546 of degree n − 2) is cited. §6.1: the label gives each scope, and says the bases were not searched on the residual families. §6.2: "wherever the bases were searched for, they exist", with the scope listed and multi-token's own seeds excluded. |
| F8 | §5.3: multi-token's families are its own seeds; the C4 subfamily at \|O\| = 8 is mentioned; the counts are tied to the committed run files (coordinator agreed). |
| F9 | Lemma 5.1: the bijection is [paper]; Lean proves the containment form. The table row says "containment form". |
| F10 | Prop 5.6: "u not avoided" added. |
| F11 | Def 5.8 (S): the conditions and K′ = K − pa − pb + ab are restored. Thm 5.9 now assumes (TS) and (TI), with a one-line gloss. |
| F12 | Thm 3.18: "If moreover d_J(w) ≥ 3" before the two corollaries. |
| F13 | Thm 3.10 label: [new], crediting the coordinator's note for case (a). §5.5(4) gives the start count and the arithmetic, and cites the docstring and A38 §2. |
| F14 | Abstract: "(for the floor lift: the floor bound, which is stronger than (T2))". |
| F15 | Table: "A16 (RouteSystem statements)". |
| F16 | The axiom record is now spine §8 (the recorded output). |
| F17 | Thm 2.2 proof: "found no error"; A1 and A2 record expository gaps and interface items. |
| F18 | "spine Lemmas 7.1–7.2, Prop 7.3". |
| F19 | "dl-one Thm 5.1, Cor 6.2". |
| F20 | §5.4(4) pairs Conj 1.2 with `L1Star` (\|A\| ≤ 2) and Conj 1.3 with `L1StarGen`, and gives the blocked case (l1star §4) with `L1Blocked`. |
| F21 | "on 1,148 data choices of random graphs of order 9". |
| F22 | "(synthesis §25 for the cone; A38 for HsaAD~})". |
| F23 | §9(6): "d = 8 is conditional, Remark 2.3". |
| F24 | No action: the log was completed and committed in 4e79079 and later. |
| F25 | Remark after Def 2.1: Lean's `Even (J.degree v) ↔ v = z` excludes isolated vertices. |
| F26 | Data paths are typeset with `\path`. |
| F27 | §9 gains items (a)–(d). For (c): test2.tex now exists, so the item records the stale theorem numbers in the `Test2Lift.lean` docstrings. |

**Changes after the audit, not audited.** The coordinator branch was merged in after the audit (test2
manuscript and audit A37, `Test2Converse.lean`, the order-10 d(z) = 4 data, dense-root milestone 1).
The paper now:
- cites test2.tex numbers for the (T2) statements;
- credits the (T2) forest and floor converses to test2 Props 4.6 and 5.2, with Lean for matchings
  (`forestBase2_matching_of_test2`, `matchingFloorBase_of_terminal`); the overview's versions are
  independent proofs, the forest one in leaf-graph form;
- adds test2 Conjs 7.1 and 7.2 to the open list;
- cites the order-10 figure 7,358 / 7,467 (98.5%) and marks §9(5) resolved;
- adds the parity remark that universal twins cannot occur in all-odd graphs (coordinator, c58bf5f);
- adds a paragraph in §6.3 on dense-root Theorem A (`exists_decomp_of_oneEven`, `test1At_of_oneEven`;
  near-cone hypothesis) and its order-9 computation (1,756 roots; unaudited);
- marks §9 items 1, 2 and 4 as corrected or agreed by the coordinator.
