# A20: Referee audit of `stl` (star-terminal Lovász decompositions and the deletion tests)

- **Date:** 2026-11-27
- **Auditor:** fresh subagent (adversarial referee pass). I edited no manuscript, Lean or script file; my only writes are this report and `research/audit/A20-scripts/`.
- **Scope:** `manuscripts/stl/stl.tex`, `lean/GallaiLean/StarTerminal.lean`, `manuscripts/stl/STLAxioms.lean`, the outputs in `manuscripts/stl/scripts/out/`, and `research/experiments.md` E22 (claims only). Background: spine §1/§7 (`gallai_iff_spineTests'`, `Test1`, `Test2`), RD (separation, L₁), MS (EE, Prop. EE, Prop. EE3, prescribed end edge).
- **Version audited.** The files changed while I worked (commits 367de83 → fb81dcb → 78e380f → ff6e414). This report is about **HEAD ff6e414**:
  - `stl.tex` md5 `f2da6058…` (653 lines); line numbers below refer to it.
  - `StarTerminal.lean` md5 `3922ff18…` (1038 lines, adds `stl_of_deg_two`, `stl_of_deg_two_tri`).
  - Earlier versions had the placeholders `NN14` and `NG11 … NP11` in Tables 2 and 3. These are now filled and agree with the logs.
- **Independent checks** (`research/audit/A20-scripts/`, written from scratch; no code shared with `tools/stl.c`, `brute.py` or `brute_flex.py`):
  - `pdec.py` is an exhaustive path-decomposition search with a prescribed end profile and path-level constraints at z, with memoised failures. Tests T1/T2 are computed exactly via profiles of J − z.
  - `check.py` covers W₄, the bowtie, full n = 5, 7 runs, the n = 9 failure records, a 3-connected n = 9 sample and STL2.
  - `flex7.py`: EE, STS, HALF and PAIR at n = 5, 7.
  - `prop41.py`: Prop. 4.1 against the definition.
  - `prop44.py`: Prop. 4.4 against the definition.
  - `jzdisc.py`: pairs with J − z disconnected.
  - `wheels.py`: STL-P on W₄ … W₁₂.

## Summary verdict

The mathematics is **sound**. Every proof checks, including the degenerate cases:
- length-2 paths through z, a short r, d(r) small, isolated vertices;
- adjacent pairs in Prop. 4.4, which are excluded by hypothesis;
- z never an end, because b(z) = 0 is built into every definition.

The Lean definitions match the paper, and the theorem statements say what the paper claims:
- no `sorry`;
- `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound` for all six theorems;
- the module compiles against fresh oleans.

Nothing in the paper says or implies that Gallai's conjecture or STL is proved. The "Honest status" paragraph is accurate.

Every positive and negative count I could recompute agreed with the repo's oracle. The problems are in how the data are summarised:
- **One wrong number.** The abstract, Table 1 and E22 give "54,336 pairs with J − z connected". The correct figure is **44,336**.
- **One false claim, repeated four times.** The text says "on all graphs of order ≤ 9, STL ⇔ BAL ⇔ (T1)", and that "both fail exactly when J − z is disconnected".
  - Both claims are false as stated.
  - STL holds but (T1) fails at about 1,190 pairs, all with d(r) = 1.
  - At n = 7 there are 83 pairs with J − z disconnected and d(r) ≥ 3; 76 of them satisfy both STL and (T1).
  - The correct statements need the restriction d(r) ≥ 3 and "only if" respectively.
- **Smaller issues:**
  - an "Equivalently" in Conjecture STL-P that holds only for pairings without adjacent pairs;
  - a Question whose first half is trivially true;
  - an "In particular" that drops the degree hypotheses;
  - a few wrong citations and internal inconsistencies.

**Overall: SOUND WITH FIXES (all fixes are wording or numbers; no proof needs repair).**

## Grades

| # | Statement | Grade | Note |
|---|---|---|---|
| 1 | (F1)–(F3), Def. 2.1 (transitions), Def. 2.2 (STL, STL2, BAL, BAL2), "STL ⇒ BAL" | SOUND | (F1)–(F3) = spine Lemmas 2.2–2.4 (checked) |
| 2 | Lemma 3.1 (surgery) | SOUND | |
| 3 | Theorem 3.2(a) | SOUND | |
| 4 | Theorem 3.2(b) | SOUND | |
| 5 | Theorem 3.2, final "In particular STL ⇒ (T1), STL2 ⇒ (T2)" | GAP (wording) | false without d(r) ≥ 3 and d(r) ≥ 4 (fix 3) |
| 6 | Remark 3.3 (i)–(iii) | SOUND | 744/948 matches `run2_8.txt` |
| 7 | Corollary 3.4 | SOUND | Lean-checked (`gallai_of_stl`) |
| 8 | Prop. 4.1 (J − z characterisation) | SOUND | also verified on all 462 pairs, n = 5, 7 |
| 9 | Prop. 4.2 (cone) | SOUND | |
| 10 | Prop. 4.3 (d(z) = 2 ⇔ EE) | SOUND | "EE" means EE *without classes* (fix 9) |
| 11 | Remark after 4.3 (EE3 citation) | SOUND | matches MS Prop. EE3 |
| 12 | Prop. 4.4 (pairing ⇔ terminal matching) | SOUND | verified on all 137 non-adjacent pairings, n = 5, 7 |
| 13 | Example 4.5 (W₄) | SOUND | verified: diagonal fails, other two work, STL at all r |
| 14 | Example 4.6 (two K₄ sharing z; prism) | SOUND | verified |
| 15 | Theorem 5.1 (d(z) = 2), both cases | SOUND | Lean: `stl_of_deg_two`, `stl_of_deg_two_tri` |
| 16 | Remark after 5.1 (overlap with EE3(a); new EE case) | SOUND | |
| 17 | Remark 5.2 (limits of the tools) | UNCLEAR (heuristic) | not a theorem; construction is specific to d(z) = 4; citation (fixes 10, 11) |
| 18 | "Composition" subsection | SOUND (as a data report) | counts match `ptm_*.log`; cross-reference wrong (fix 12) |
| 19 | §5 tables vs logs | GAP | 54,336; "STL ⇔ T1 on all graphs ≤ 9"; undecided policy (fixes 1, 2, 7) |
| 20 | Conj. 6.1 ⇒ Gallai (via 4.2); 3-connected cases suffice (via 3.4) | SOUND | |
| 21 | "Up to order 9 the two are equivalent, and both fail exactly when J − z is disconnected" | ERROR | fix 2 |
| 22 | Conj. 6.3 (STL = (T1)) and "only ⇐ is open" | SOUND (statement and evidence) | evidence is right for d(r) ≥ 3 |
| 23 | Conj. 6.4 (STL-P), "Equivalently (Prop. 4.4)" | GAP | Prop. 4.4 needs non-adjacent pairs (fix 5) |
| 24 | Question 6.5 ("Is EE implied by … STS?") | ERROR (trivial) | STS(u) ⇒ EE(u) by definition (fix 6) |
| 25 | Lean definitions `StarAt`, `LongAt`, `HasShortShort`, `STL`, `STL2` | SOUND | faithful (details below) |
| 26 | Lean `star_delete`, `test1_of_stl`, `test2_of_stl2`, `gallai_of_stl`, `stl_of_deg_two(_tri)` | SOUND | statements match; nits in fix 13 |
| 27 | Abstract and intro vs body and logs | GAP | fixes 1, 2, 4, 8 |

## Details

### Mathematics

**Def. 2.1 / 2.2.**
- With b_D(z) = 0, "#LL = 0" ⇔ every path through z has a short side ⇔ z is the second vertex read from that end. This is correct.
- The disjunct b_D(r) = 0 in STL2 is redundant, as the text notes: r is then not an end, so it is long.
- Nit: "Every w ∈ N(z) lies on exactly one path through the edge wz" should read "the edge wz lies on exactly one path".

**Lemma 3.1.**
- A path A z B loses a₁z and zb₁. The pieces A and B are vertex-disjoint and avoid z, and a side is short iff its piece is trivial. So the path contributes 2/1/0 pieces for LL/SL/SS, which gives |D′| = |D| + #LL − #SS.
- End changes occur only at a₁ and b₁. A second path through z that contains a₁ does not use a₁z, so its piece containing a₁ keeps a₁'s edges.
- A leaf w at z is always short and becomes isolated in J − z with b = 0. This is consistent with the formula.

**Theorem 3.2.**
- (a): 2|D| = n − 1. If r is long, b′(r) = 2 and |D′| ≤ (n−1)/2. If r is short, |D′| ≤ (n−1)/2 − 1 and b′(r) = 0, with d_{J−z}(r) even ≥ 2, so (F3)(a) applies.
- (b): n is even and 2|D| = n − 2 + β. β = 0 forces r long. The three cases are exhaustive, and (F3)(b) needs d_{J−z}(r) odd ≥ 3, which holds because d_J(r) ≥ 4.
- **The last sentence ("In particular STL ⇒ (T1) at r, STL2 ⇒ (T2)") omits the degree hypotheses, and is false without them:**
  - P₃ (z the middle vertex);
  - the spider r–z–a–{b,c} (n = 5): the path r z a is SS, so STL holds, but r is isolated in J − z;
  - 46 pairs (J, r) with |J| ≤ 7 and d(r) = 1 (my `check.py n 5/7`, plus P₃);
  - for STL2, 28 instances of order ≤ 6 with d(r) = 2 where STL2 holds and (T2) fails (`check.py stl2 conn4/conn6 all`).

  The Lean theorems do carry the hypothesis (`hdeg`).

**Remark 3.3(iii).**
- J − zr has all degrees odd, and z ≠ r are non-adjacent in it.
- `lovasz_avoid_nonadj` needs exactly: `evenSet = 0`, c = z of odd degree, c ≠ a, ¬adj.
- Appending zr gives b(z) = 0 and b(r) = 2.
- Correct.

**Prop. 4.1.**
- (⇒) T is the set of long neighbours. "Long sides whose remainder is nonempty" is redundant: a long side always has a remainder.
- (⇒) σ(y) ∉ B_y because the vertices of a path are distinct. The B_y are distinct because a star-terminal transition has at most one long side.
- (⇐) Distinctness of the B_y is exactly what prevents a D′-path with both ends in T from being extended twice. End counts and star-terminality check.
- (iv) ⇒ (r long or #SS ≥ 1).
- Also verified exhaustively: `prop41.py` agrees with the direct STL test on all 20 + 442 pairs at n = 5, 7.

**Prop. 4.2.**
- |Ev(H)| is even. In J = H + z(Ev H), z is the unique even vertex and J − z = H is connected.
- |D| = N/2, and Lemma 3.1 with #LL = 0 gives p(H) ≤ N/2.
- Odd N: removing the leaf edge from its path gives p(G) ≤ p(G + leaf).
- Every r ∈ N(z) has d_J(r) = d_H(r) + 1 ≥ 3, so Conjecture 6.1 (which requires d(r) ≥ 3) does imply the hypothesis. The claim "Conj. 6.1 implies Gallai without the spine" is correct.

**Prop. 4.3.**
- The single transition is u z r. (S,L) or (S,S) qualify; (L,S) does not; (L,L) is not star-terminal. So the condition is exactly "u short". Correct.
- MS's Conjecture EE (Conjecture 17 in MS) is stated with a class family 𝒜. STL at d(z) = 2 is its case 𝒜 = ∅, which is MS Question 23 / Prop. EE3's setting.

**Prop. 4.4.**
- The hypothesis "no pair of M adjacent in J" is exactly what makes G simple.
- (⇒) A path x z y ⋯ becomes x y ⋯, still a path. Each path passes z once, so it carries ≤ 1 M-edge.
- (⇐) The direct replacement.
- The converse construction (G − F) + z(V(F)) preserves degrees and makes z even of degree 2|F|. Edge case: F = ∅ gives an isolated z, which is harmless.
- Verified: `prop44.py` agrees on all 6 + 131 non-adjacent pairings at n = 5, 7.

**Examples.**
- W₄: my search gives the diagonal pairing as not realisable. Witnesses for the other two:
  - {12, 34}: `1 0 2 3 4 | 2 1 4 0 3`;
  - {14, 23}: `1 0 4 3 2 | 3 0 2 1 4`.
- W₄ also has STL = BAL = T1 = true at all four r, and HALF realisable for exactly the 2 "alternating" half-sets {1,3}, {2,4} out of 6. This matches Table 3 (2/6, 2/3, 4/4).
- Bowtie: a Lovász decomposition exists, but no star-terminal one (ST false). STL, BAL and T1 are false at all six r. The prism is cubic and 3-connected.

**Theorem 5.1.**
- `separation` (Lean) takes `FarApart` (distinct, non-adjacent, no common neighbour) with no connectivity hypothesis, so d(u) = 1 (u isolated in K) is covered.
- Case uw ∉ E: d_K(z) = 1, d_K(u) = d(u) − 1 is even (possibly 0), and FarApart(z, u) holds because w ≁ u. Appending zu makes u short.
- Case uw ∈ E:
  - d_K(w) = d(w) − 1 is even and ≥ 2; d_K(u) = d(u) − 2 is odd.
  - u, w are FarApart in K because z ≁ u there and there is no other common neighbour.
  - Q_u avoids w; P_z contains w (z's only edge), so it avoids u, and Q_u ≠ P_z.
  - Extending Q_u by uw and then P_z by zu gives b(u) = 0 + 1, b(w) = 0 + 1, b(z) = 0.
- Correct.
- The Lean versions have exactly these hypotheses (`hN`, `huw`/`¬huw`, `hcom`) and conclude `STL J z w`. The other conclusion follows by the u ↔ w symmetry.
- The remark that case uw ∉ E is MS Prop. EE3(a) at d(z) = 2 is right. So is the claim that case uw ∈ E with d(u) ≥ 5 is new relative to MS: EE3(b) and (c) have d(u) = 3.
- No d(z) = 2 instance appears among the 58 recorded failures, which is consistent.

**Remark 5.2.**
- Heuristic, and labelled as such.
- The parity-neutral construction (delete ac, add leaves at b, d) keeps all degrees of J − z odd only when N(z) = {a, b, c, d}, i.e. d(z) = 4. For d(z) ≥ 6 the other neighbours stay even. Say so.
- "[RD, E20]": E20 is an entry of `research/experiments.md`, not part of RD. The RD statement is Remark 6.7 (`rem:L1res`, "L₁ fails if the graph already has an even vertex").

**Composition subsection.**
- 1,199 = 299 + 300 + 300 + 300 instances; 17 = 8 + 2 + 0 + 7 PEE failures; 317 = 81 + 90 + 32 + 114 with G − F disconnected. All match `ptm_*.log`.
- But the text says "(Section 5)", and Section 5 does not describe this experiment. It is only in E22(F).

### Conjectures and their stated relationships

- **Conj. 6.1 ⇒ Gallai** (Prop. 4.2) and **3-connected cases of 6.1/6.2 ⇒ Gallai** (Cor. 3.4): correct.
- **"Up to order 9 the two are equivalent, and both fail exactly when J − z is disconnected" (l. 580–581): ERROR.**
  - Equivalence holds only for d(r) ≥ 3 (see the d(r) = 1 counts below).
  - "Exactly when" is false. `jzdisc.py`, n = 7: 124 pairs have J − z disconnected; 83 of them have d(r) ≥ 3, and 76 of those satisfy both STL and (T1). Smallest example: `DsO` (n = 5), z = 1, r = 0.
  - The data support only "every failure has J − z disconnected".
- **Conj. 6.3 (STL = (T1), d(r) ≥ 3; STL2 = (T2), d(r) ≥ 4):** correctly stated, with "only ⇐ is open" right.
  - The STL evidence is complete for d(r) ≥ 3 up to order 9: when STL holds, (T1) holds by Theorem 3.2, and the pipeline checks (T1) at every STL failure.
  - My n ≤ 7 run: STL ≠ (T1) at 0 pairs with d(r) ≥ 3.
  - For STL2 (n ≤ 8), `run2_8.txt` reports `STL2fail-but-T2 0`.
- **Conj. 6.4 (STL-P), "Equivalently (Proposition 4.4)": GAP.**
  - Prop. 4.4 covers only pairings with no pair adjacent in J. For a pair xy ∈ E(J), G = (J − z) + M is a multigraph.
  - The conjecture and the PAIR data quantify over all perfect matchings. In W₄, for instance, both realisable pairings consist of rim edges.
  - Consistency check: the conjecture survives W₆, W₈, W₁₀ (945/945 pairings) and W₁₂ (10,395/10,395) in my `wheels.py`.
- **Question 6.5: ERROR (trivial).** STS(u) is EE(u) plus star-terminality, so "EE implied by STS" holds by definition. The intended question is "Does EE(u) imply STS(u)?", i.e. are they equivalent?

### Lean

- **Compilation.** `lake env lean GallaiLean/StarTerminal.lean` (current file) and `lake env lean ../manuscripts/stl/STLAxioms.lean` both succeed with no output except the axiom lines. There is no `sorry`, `admit` or `axiom`. The oleans are not stale (every `.olean` is newer than its source). I did not run a full `lake build`.
- **`StarAt D z`** := ∀ P ∈ D, z ∈ P → s(src, z) ∈ P.edges ∨ s(tgt, z) ∈ P.edges.
  - When z is not an end, s(src, z) ∈ edges ⇔ src and z are consecutive ⇔ z is the second vertex. So it is **equivalent** to the paper's definition.
  - If z were an end, the clause would only admit single-edge paths, but every use has b(z) = 0 (`not_end_of_ends_zero`, and z even in `STL`/`STL2`). Not vacuous.
- **`LongAt D z r`** := the path through zr does not end at r. This matches "r long".
- **`HasShortShort D z`** := some path has all its edges at z. With b(z) = 0 this is exactly a path x z y. A length-1 path would end at z, which is excluded.
- **`STL`** = Lovász (ends = deg mod 2 everywhere) ∧ StarAt ∧ (LongAt ∨ HasShortShort). This matches Def. 2.2.
- **`STL2`** = ends = deg mod 2 off r, ends r ∈ {0, 2}, StarAt, (ends r = 0 ∨ LongAt ∨ SS). This matches; b(z) = 0 comes from z ≠ r being even.
- **`star_delete`.** States |D′| + #SS ≤ |D| (an inequality; the paper's Lemma 3.1 has equality) and the end identity b′(v) + Σ c_P[i_P = 1] = b(v) + Σ c_P[i_P = 2]. For v ∈ N(z), exactly one P has c_P = 1, so this is b′ = b + [long] − [short]. This is what §7 says.
- **`test1_of_stl`, `test2_of_stl2`.**
  - Hypotheses: `hdeg` (every neighbour has degree ≥ 3) and STL at every r. The conclusion is the library's `Test1`/`Test2` verbatim.
  - This is the "all r" form, not the per-r form "STL(J, z, r) ⇒ (T1) at r" of the paper. It suffices for the corollary.
  - In `test2`, d(r) ≥ 4 is derived from d(r) ≥ 3 and evenness.
- **`gallai_of_stl`.** Hypotheses are exactly Cor. 3.4 (KConnected 3, ¬HasMatchingCut (J − z), parity, all r). The conclusion is `GallaiConjecture.{u}`, via `gallai_iff_spineTests'.2.2`. The hypotheses are not vacuous or contradictory, and the conclusion is the real conjecture (`pathNumber ≤ (card + 1)/2`).
- **`stl_of_deg_two`, `stl_of_deg_two_tri`.** They match Theorem 5.1, cases 1 and 2.

### Computation (independent)

All with my `pdec.py`:

| check | result | agrees with repo |
|---|---|---|
| W₄: pairings {12,34}, {13,24}, {14,23} | realisable, **not**, realisable; STL at all r | yes (Ex. 4.5, Table 3) |
| bowtie (two K₄ at z) | Lovász yes, ST no, STL/BAL/T1 false at all 6 r | yes (Ex. 4.6) |
| all one-even graphs n = 5 (7 graphs, 20 pairs) | STL fails 1 (`Dus`, r = 2); ST fails 0 | yes (`fail_5.jsonl`) |
| all one-even graphs n = 7 (130 graphs, 442 pairs) | STL fails 9 (exactly the 9 of `fail_7.jsonl`), BAL fails at the same 9, ST fails 1 (`FujTO` = bowtie); 0 failures with J − z connected (318 pairs), including all 126 pairs of the 28 3-connected graphs | yes |
| same, (T1) | fails at 6 (n = 5) and 48 (n = 7) pairs; STL true & (T1) false at 5 + 39 pairs, **all d(r) = 1**; STL ≠ T1 at 0 pairs with d(r) ≥ 3 | refutes the caption claim (fix 2) |
| flexibility, 3-connected n = 5, 7 | W₄: EE/STS 4/4, HALF 2/6, PAIR 2/3; n = 7: 28 graphs, EE/STS 126/126, HALF 244/266, PAIR 168/168 | yes (Table 3) |
| `fail_9.jsonl` records | see the "n = 9 failures" line below | yes, no disagreement |
| 3-connected n = 9, random sample | see the "n = 9 sample" line below | |
| STL2: order 4 and 6, all connected | 4 + 52 instances, 1 failure (`Eqig` z = 0, r = 1, = `fail2_6.jsonl`); 3-connected: 10 instances, 0 failures, β = 0 in 4 | yes: gives 2,828 = 4 + 52 + 2,772, 958 = 10 + 948, 748 = 4 + 744 |
| STL2: order 8, 3-connected | see the "STL2 n = 8" line below | |
| Prop. 4.1, Prop. 4.4 | 0 disagreements (462 pairs; 137 pairings) | |
| counts of J − z connected pairs | n = 5: 4 graphs / 10 pairs; n = 7: 99 / 318; n = 9: 10,893 / 44,008. **Total 10,996 graphs, 44,336 pairs** | graphs yes; **pairs no (paper: 54,336)** |
| d(r) = 1 pairs, n = 9 | 1,162 (16 of them STL failures in `fail_9`); with n ≤ 7, ≈ 1,192 pairs where STL holds and (T1) fails | |

- **n = 9 failures** (all 48 records of `fail_9.jsonl`, 60 s limit per query; output in `A20-scripts/out_fail9_all.txt`):
  - Every graph has exactly one even vertex z, and J − z is disconnected in all 48.
  - The 32 records with d(r) ≥ 3 are all confirmed: STL, BAL and (T1) are all false.
  - Of the 16 records with d(r) = 1, 8 are confirmed. In the other 8, the pure-Python search hit the time limit on the exhaustive negative for STL/BAL. These are dense graphs (J − z = a dense 7-vertex component plus r). (T1) is false there trivially.
  - No disagreement.
- **n = 9 sample:** N9_RESULT
- **STL2 n = 8:** STL2_8_RESULT

Log cross-checks:
- Table 1 random rows are the sums of the `s1_*` logs: 3,256 = 1,642 + 1,614; 3,470; 2,082; 338.
- 9,146 = 8,808 + 338.
- Families: 1,232 = 400 + 360 + 280 + 192; 102 graphs; zconn 780; zdisc11 1,282 pairs with 4 failures = 4 (T1) failures.
- Table 2 random rows: 1,200; 1,000; 500.
- Every undecided entry of the `s1_*`/`s2_*` samples has a matching "resolved" line, ending "undecided left 0".
- Table 3 n = 11: 1,290; 4,691/4,702 (+200 undecided); 5,196. These match `flex_11_*` together with `flex_11_gnp.res.log`.
- `flex_9.log`: 54,045. 54,213 = 168 + 54,045.

## Required fixes

1. **The count 54,336 is wrong; it should be 44,336.** It appears in the abstract (l. 57), Table 1 row 3 (l. 498), E22 (A) and connections §X.3. In Table 1, also replace "among these" in that row: it spans n ≤ 9 while the row above is n = 9 only.
2. **"STL ⇔ BAL ⇔ (T1) on all graphs of order ≤ 9" is false for d(r) = 1.**
   - Restrict it to pairs with d(r) ≥ 3 in the Table 1 caption (l. 511–512), §6 (l. 580), E22 (A) and connections §X.3.
   - The example is the spider r–z–a–{b, c}, where r z a is SS, so STL holds, but r is isolated in J − z. About 1,190 such pairs exist with |J| ≤ 9.
   - Replace "both fail exactly when J − z is disconnected" (l. 581) by "every failure has J − z disconnected". At n = 7, 76 of the 83 pairs with J − z disconnected and d(r) ≥ 3 satisfy both.
   - Make the abstract's "on these graphs STL is equivalent to the first test" say "for d(r) ≥ 3". If "these graphs" means J − z connected, the equivalence is trivial, because both always hold.
   - Relabel E22's "Test1 fails" column: Test1 was evaluated only where STL failed.
3. **Theorem 3.2, last sentence:** write "In particular, under the degree hypotheses of (a) and (b), …". Counterexamples otherwise: P₃; 28 STL2 instances with d(r) = 2 at n ≤ 6.
4. **The abstract's d(z) = 2 claim** ("unless the two neighbours of z have a second common neighbour") is weaker than Theorem 5.1 and differs from the intro. Use "unless the two neighbours of z are adjacent and have a second common neighbour".
5. **Conjecture STL-P (l. 596–601):** restrict "Equivalently (Proposition 4.4)" to pairings with no pair adjacent in J, or state the multigraph version. The conjecture itself and the PAIR data range over all pairings.
6. **Question 6.5:** STS(u) ⇒ EE(u) is trivial. Ask "Does EE(u) imply STS(u)?" (equivalently: are EE and STS equivalent?).
7. **Undecided policy is inconsistent.** §5.1 says "every undecided instance reported below was re-run … until decided", but Table 3's footnote leaves 200 HALF queries undecided. Qualify the §5.1 sentence. Also, the STL2 counts for n = 4, 6 (used in 2,828, 958 and 748) have no log in `scripts/out/` (only `fail2_4/6.jsonl`); add `run2_6.txt` or the like. My recount agrees with the numbers.
8. **Intro item (2)** lists four Lean theorems; add `stl_of_deg_two` and `stl_of_deg_two_tri`, now proved. §7 says StarTerminal "imports Separator.lean"; it now also imports `Separation`.
9. **Prop. 4.3 and the abstract:** "EE of [MS]" should say **without classes** (MS Conjecture EE has a class family). The open d(z) = 2 case is MS Question 23 / Prop. EE3's setting.
10. **Citations.**
    - "[MS, Question 5.2]" (l. 357) does not exist: MS numbers globally, and the packed-set question is Question 25 (`q:pe`). Cite by name or label.
    - "[RD, E20]" (l. 437): E20 is `research/experiments.md`, not RD; the RD statement is Remark 6.7 (`rem:L1res`).
    - "[MS, §5]" (l. 441): the multi-prescription problem is the open question in MS §10. §5 only mentions it.
11. **Remark 5.2, parity-neutral construction:** state that it is for d(z) = 4 (N(z) = {a, b, c, d}). For d(z) ≥ 6 the remaining neighbours stay even.
12. **Composition subsection:** "(Section 5)" should point to E22(F) and `ptm_run.py`, or the experiment should be added to §5 with its table (n, m: 8,2 / 10,2 / 12,2 / 10,3; 299 / 300 / 300 / 300).
13. **Nits.**
    - Table 1, wheels row: "8 pairs" is one r per wheel (by symmetry); say so.
    - Def. 2.1: "the edge wz lies on exactly one path".
    - Prop. 4.1 proof: "long sides whose remainder is nonempty" is redundant. In "r ∈ T unless r is short or lies on an SS path, in which case |T| < k", the conclusion |T| < k comes from STL's disjunct #SS ≥ 1, not from r being short (an SL transition with r short has |T| = k if there is no SS). Reword as "if r is short, STL gives #SS ≥ 1, so |T| < k".
    - Lean `star_delete` proves |D′| + #SS ≤ |D| (not equality); `test1_of_stl` / `test2_of_stl2` are the all-r forms with `hdeg` at every neighbour. Fine for Cor. 3.4, but §7 could say so.
