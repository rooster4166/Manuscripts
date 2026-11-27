# A20: Referee audit of `stl` (star-terminal Lovász decompositions and the deletion tests)

- **Date:** 2026-11-27
- **Auditor:** fresh subagent (adversarial referee pass). I edited no manuscript, Lean or script file. My only writes are this report and `research/audit/A20-scripts/`. A checkpoint of both was committed by the session in 3d8b5df; I made no commit myself.
- **Scope:**
  - Primary: `manuscripts/stl/stl.tex`, `lean/GallaiLean/StarTerminal.lean`, `manuscripts/stl/STLAxioms.lean`, the outputs in `manuscripts/stl/scripts/out/`, and `research/experiments.md` E22 (claims only).
  - Background: spine §1/§7 (`gallai_iff_spineTests'`, `Test1`, `Test2`), RD (separation, L₁), MS (EE, Prop. EE, Prop. EE3, prescribed end edge), and PE (`ee_atMostOneCommon`, `ee_deg_two`; Lean statements and axioms only).
- **Version audited.** The files changed five times while I worked: 367de83 → fb81dcb → 78e380f → ff6e414 → 3d8b5df.
  - The report is about **HEAD 3d8b5df**: `stl.tex` md5 `98c20831…` (670 lines), `StarTerminal.lean` md5 `91ac94a6…`. Line numbers refer to that `stl.tex`.
  - Numbering in that version:
    - §2: Defs 2.1–2.2.
    - §3: Lemma 3.1, Thm 3.2, Remark 3.3, Cor. 3.4.
    - §4: Props 4.1–4.4, Examples 4.5–4.6.
    - §5: Thm 5.1, **Cor. 5.2 (new: STL at every d(z) = 2)**, Remark 5.3 (the former Remark 5.2, `rem:limit`), "Composition".
    - §6: Computations.
    - §7: Conjectures 7.1 (STL), 7.2 (STL2), 7.3 (STL = (T1)), 7.4 (STL-P), Question 7.5.
    - §8: Lean.
  - Earlier versions had placeholders (`NN14`, `NG11 … NP11`) in Tables 2 and 3. They are now filled and agree with the logs.
- **Independent checks** (`research/audit/A20-scripts/`, written from scratch; no code shared with `tools/stl.c`, `brute.py` or `brute_flex.py`):
  - `pdec.py`: exhaustive path-decomposition search with a prescribed end profile and path-level constraints at z, with memoised failures. (T1)/(T2) are decided exactly over the end profiles of J − z.
  - `check.py`: W₄, the bowtie, full n = 5 and n = 7 runs, the n = 9 failure records, a 3-connected n = 9 sample, and STL2.
  - `flex7.py`: EE, STS, HALF and PAIR at n = 5, 7.
  - `prop41.py`, `prop44.py`: Props. 4.1 and 4.4 against the definition.
  - `jzdisc.py`: pairs with J − z disconnected.
  - `wheels.py`: STL-P on W₄ … W₁₂.

## Summary verdict

**The mathematics is sound.** Every proof checks, including the degenerate cases:
- length-2 paths through z;
- r short;
- d(r) small;
- isolated vertices;
- adjacent pairs in Prop. 4.4, which are excluded by hypothesis;
- z as an end, which never happens because b(z) = 0 is built into every definition.

**The Lean is faithful.** The definitions match the paper, and the theorem statements say what the paper claims.
- No `sorry`.
- `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound` for all seven theorems of `STLAxioms.lean`.
- All oleans are fresh.

**No overclaim.** Nothing in the paper says or suggests that Gallai's conjecture or STL is proved. The "Honest status" paragraph is accurate. The new claim "STL holds at every vertex of degree two" is correct and Lean-checked; it rests on PE's `ee_deg_two`.

**The data agree.** Every positive and negative count I recomputed agreed with the repo's oracle. The problems are in how the data are summarised:
1. **A wrong number.** The abstract, Table 1 and E22 give "54,336 pairs with J − z connected". The correct figure is **44,336**.
2. **A false claim, repeated four times.** The claim "on all graphs of order ≤ 9, STL ⇔ BAL ⇔ (T1)", and its companion "both fail exactly when J − z is disconnected", are false as stated.
   - STL holds and (T1) fails at 1,192 pairs, all with d(r) = 1.
   - At n = 7, 76 of the 83 pairs with J − z disconnected and d(r) ≥ 3 satisfy both STL and (T1).
   - The correct statements need "d(r) ≥ 3" and "only if".
3. **Smaller issues:**
   - an "Equivalently" in Conjecture STL-P that holds only for pairings with no adjacent pair;
   - a question whose first half is trivially true;
   - an "In particular" that drops the degree hypotheses;
   - several wrong citations and internal inconsistencies.

**Overall: SOUND WITH FIXES.** All fixes are to wording or numbers. No proof needs repair.

## Grades

| # | Statement | Grade | Note |
|---|---|---|---|
| 1 | (F1)–(F3); Def. 2.1 (transitions); Def. 2.2 (STL, STL2, BAL, BAL2); "STL ⇒ BAL" | SOUND | (F1)–(F3) are spine Lemmas 2.2–2.4 (checked) |
| 2 | Lemma 3.1 (surgery) | SOUND | |
| 3 | Theorem 3.2(a) | SOUND | |
| 4 | Theorem 3.2(b) | SOUND | |
| 5 | Theorem 3.2, last sentence: "In particular STL ⇒ (T1), STL2 ⇒ (T2)" | GAP (wording) | false without d(r) ≥ 3, resp. d(r) ≥ 4 (fix 3) |
| 6 | Remark 3.3 (i)–(iii) | SOUND | 744/948 matches `run2_8.txt` |
| 7 | Corollary 3.4 | SOUND | Lean-checked (`gallai_of_stl`) |
| 8 | Prop. 4.1 (J − z characterisation) | SOUND | verified on all 462 pairs at n = 5, 7; one proof sentence misattributes a step (fix 13) |
| 9 | Prop. 4.2 (cone) | SOUND | |
| 10 | Prop. 4.3 (d(z) = 2 ⇔ EE) | SOUND | "EE" here means EE *without classes* (fix 9) |
| 11 | Remark after 4.3 (EE3 and PE citations) | SOUND | matches MS Prop. EE3 and the PE Lean |
| 12 | Prop. 4.4 (pairing ⇔ terminal matching) | SOUND | verified on all 137 non-adjacent pairings at n = 5, 7 |
| 13 | Example 4.5 (W₄) | SOUND | verified: the diagonal pairing fails, the other two work, STL holds at every r |
| 14 | Example 4.6 (two K₄ sharing z; the prism) | SOUND | verified |
| 15 | Theorem 5.1 (d(z) = 2), both cases | SOUND | Lean: `stl_of_deg_two`, `stl_of_deg_two_tri` |
| 16 | Corollary 5.2 (STL at every d(z) = 2) | SOUND | Lean `stl_deg_two` from PE `ee_deg_two`; axioms clean |
| 17 | Remark after 5.1 (overlap with EE3(a) and with PE) | SOUND | |
| 18 | Remark 5.3 (limits of the tools) | UNCLEAR (heuristic) | not a theorem; the construction is specific to d(z) = 4; citations (fixes 10, 11) |
| 19 | "Composition" subsection | SOUND as a data report | counts match `ptm_*.log`; wrong cross-reference (fix 12) |
| 20 | §6 tables vs logs | GAP | 54,336; "STL ⇔ (T1) on all graphs ≤ 9"; undecided policy (fixes 1, 2, 7) |
| 21 | Conj. 7.1 ⇒ Gallai (via Prop. 4.2); the 3-connected cases suffice (via Cor. 3.4) | SOUND | |
| 22 | "Up to order 9 the two are equivalent, and both fail exactly when J − z is disconnected" (l. 593–594) | ERROR | fix 2 |
| 23 | Conj. 7.3 (STL = (T1)) and "only ⇐ is open" | SOUND (statement and evidence) | the evidence is complete for d(r) ≥ 3 |
| 24 | Conj. 7.4 (STL-P), "Equivalently (Prop. 4.4)" | GAP | Prop. 4.4 needs non-adjacent pairs (fix 5) |
| 25 | Question 7.5 ("Is EE implied by … STS?") | ERROR (trivial) | STS(u) ⇒ EE(u) by definition (fix 6) |
| 26 | Lean definitions `StarAt`, `LongAt`, `HasShortShort`, `STL`, `STL2` | SOUND | faithful (details below) |
| 27 | Lean `star_delete`, `test1_of_stl`, `test2_of_stl2`, `gallai_of_stl`, `stl_of_deg_two`, `stl_of_deg_two_tri`, `stl_deg_two` | SOUND | statements match; nits in fix 13 |
| 28 | Abstract and intro vs body and logs | GAP | fixes 1, 2, 8 |

## Details

### Mathematics

**Definitions 2.1 and 2.2.**
- With b_D(z) = 0, "#LL = 0" holds iff every path through z has a short side, iff z is the second vertex read from a suitable end. Correct.
- The disjunct b_D(r) = 0 in STL2 is redundant, as the text notes: r is then not an end, so it is long.
- Nit: "Every w ∈ N(z) lies on exactly one path through the edge wz" should read "the edge wz lies on exactly one path".

**Lemma 3.1.**
- A path A z B loses the edges a₁z and zb₁. Its pieces A and B are vertex-disjoint and avoid z.
- A side is short iff its piece is trivial. So the path contributes 2, 1 or 0 pieces for LL, SL or SS, and |D′| = |D| + #LL − #SS.
- End counts change only at a₁ and b₁. A second path through z that contains a₁ does not use a₁z, so its piece containing a₁ keeps a₁'s edges.
- A leaf w at z is always short. It becomes isolated in J − z with b = 0, consistent with the formula.

**Theorem 3.2.**
- (a) 2|D| = n − 1.
  - r long: b′(r) = 2 and |D′| ≤ (n−1)/2.
  - r short: |D′| ≤ (n−1)/2 − 1 and b′(r) = 0, with d_{J−z}(r) even and ≥ 2, so (F3)(a) applies.
- (b) n is even and 2|D| = n − 2 + β.
  - β = 0 forces r to be long.
  - The three cases are exhaustive.
  - (F3)(b) needs d_{J−z}(r) odd and ≥ 3, which holds because d_J(r) ≥ 4.
- **The final "In particular STL ⇒ (T1) at r, STL2 ⇒ (T2)" drops the degree hypotheses, and is false without them.**
  - P₃ (z the middle vertex) is a counterexample.
  - So is the spider r–z–a–{b, c} at n = 5: the path r z a is SS, so STL holds, but r is isolated in J − z.
  - In total, 46 pairs (J, r) with |J| ≤ 7 and d(r) = 1 (`check.py n 5`, `n 7`, plus P₃).
  - For STL2, 28 instances of order ≤ 6 with d(r) = 2 have STL2 true and (T2) false (`check.py stl2 conn4/conn6 … all`).
  - The Lean theorems do carry the hypothesis (`hdeg`).

**Remark 3.3(iii).**
- J − zr has all degrees odd, and z ≠ r are non-adjacent in it.
- `lovasz_avoid_nonadj` needs exactly `evenSet = 0`, c = z of odd degree, c ≠ a, and ¬adj.
- Appending zr gives b(z) = 0 and b(r) = 2. Correct.

**Proposition 4.1.**
- (⇒)
  - T is the set of long neighbours. The phrase "long sides whose remainder is nonempty" is redundant.
  - σ(y) ∉ B_y because the vertices of a path are distinct.
  - The B_y are distinct because a star-terminal transition has at most one long side.
  - The sentence "r ∈ T unless r is short …, in which case |T| < k" misattributes the conclusion. |T| < k follows from STL's disjunct #SS ≥ 1, not from r being short (fix 13).
- (⇐)
  - Distinctness of the B_y is exactly what prevents a D′-path with both ends in T from being extended twice.
  - End counts and star-terminality check, and (iv) gives "r long or #SS ≥ 1".
- `prop41.py` agrees with the direct STL test on all 20 + 442 pairs at n = 5, 7.

**Proposition 4.2.**
- |Ev(H)| is even. In J = H + z(Ev H), z is the unique even vertex and J − z = H is connected.
- |D| = N/2, and Lemma 3.1 with #LL = 0 gives p(H) ≤ N/2.
- Odd N: removing the leaf edge from its path gives p(G) ≤ p(G + leaf).
- Every r ∈ N(z) has d_J(r) = d_H(r) + 1 ≥ 3. So Conjecture 7.1, which assumes d(r) ≥ 3, does imply the hypothesis, and "Conj. 7.1 implies Gallai without the spine" is correct.

**Proposition 4.3.**
- The single transition is u z r. The pairs (S, L) and (S, S) qualify, (L, S) does not, and (L, L) is not star-terminal. So the condition is exactly "u short". Correct.
- MS's Conjecture EE (Conjecture 17 there) is stated with a class family 𝒜. STL at d(z) = 2 is its case 𝒜 = ∅, i.e. MS Question 23 and the setting of Prop. EE3.

**Proposition 4.4.**
- The hypothesis "no pair of M adjacent in J" is exactly what makes G simple.
- (⇒) A path x z y ⋯ becomes x y ⋯, which is still a path. Each path passes z once, so it carries at most one M-edge.
- (⇐) Direct replacement.
- The converse construction (G − F) + z(V(F)) preserves degrees and makes z even of degree 2|F|. F = ∅ gives an isolated z, which is harmless.
- `prop44.py` agrees on all 6 + 131 non-adjacent pairings at n = 5, 7.

**Examples.**
- **W₄.** My search finds the diagonal pairing not realisable. The other two pairings are realisable, with witnesses:
  - pairing {12, 34}: `1 0 2 3 4 | 2 1 4 0 3`;
  - pairing {14, 23}: `1 0 4 3 2 | 3 0 2 1 4`.
- **W₄, other counts.** STL, BAL and (T1) hold at all four r. HALF is realisable for exactly 2 of the 6 half-sets ({1, 3} and {2, 4}). This matches Table 3 (2/6, 2/3, 4/4).
- **Bowtie.** A Lovász decomposition exists, but no star-terminal one does (ST is false). STL, BAL and (T1) fail at all six r. The prism is cubic and 3-connected.

**Theorem 5.1.**
- `separation` takes `FarApart` (distinct, non-adjacent, no common neighbour) and assumes no connectivity. So d(u) = 1, with u isolated in K, is covered.
- Case uw ∉ E:
  - d_K(z) = 1, and d_K(u) = d(u) − 1 is even (possibly 0).
  - FarApart(z, u) holds because w ≁ u.
  - Appending zu makes u short.
- Case uw ∈ E:
  - d_K(w) = d(w) − 1 is even and ≥ 2; d_K(u) = d(u) − 2 is odd.
  - u and w are FarApart in K, since z ≁ u there and they have no other common neighbour.
  - Q_u avoids w. P_z contains w (z's only edge), so it avoids u, and Q_u ≠ P_z.
  - Extending Q_u by uw and then P_z by zu gives b(u) = 0 + 1, b(w) = 0 + 1, b(z) = 0. Correct.
- The Lean versions have exactly these hypotheses (`hN`, `huw` or `¬huw`, `hcom`) and conclude `STL J z w`. The other conclusion follows by the symmetry u ↔ w.

**Corollary 5.2 (new).**
- `stl_deg_two` assumes `hev` (z the only even vertex), `hzu`, `hzw`, `hne` and `hN`, i.e. N(z) = {u, w}, and concludes `STL J z w`.
- It applies PE's `ee_deg_two` (EE at u whenever d(z) = 2). That theorem comes from `ee_atMostOneCommon`: u and z have at most one common neighbour, which is automatic when d(z) = 2.
- `ee_atMostOneCommon` concludes a Lovász decomposition and a path P ending at u with `s(u, z) ∈ P.edges`. Since u occurs once on P, uz is the terminal edge at u. Prop. 4.3 then gives STL. Correct.
- I checked the Lean statements, the absence of `sorry`, and the axioms. I did not referee PE's proof beyond that.
- No d(z) = 2 instance appears among the 58 recorded failures, which is consistent.

**Remark 5.3 (formerly 5.2).**
- It is heuristic, and labelled as such.
- The parity-neutral construction (delete ac, add leaves at b and d) keeps every degree of J − z odd only when N(z) = {a, b, c, d}, i.e. d(z) = 4. For d(z) ≥ 6 the remaining neighbours stay even. The remark should say so.
- "[RD, E20]" is a wrong citation. E20 is an entry of `research/experiments.md`, not of RD. The RD statement is Remark 6.7 (`rem:L1res`: "L₁ fails if the graph already has an even vertex").

**Composition subsection.**
- The counts match `ptm_*.log`:
  - 1,199 instances = 299 + 300 + 300 + 300;
  - 17 PEE failures = 8 + 2 + 0 + 7;
  - 317 instances with G − F disconnected = 81 + 90 + 32 + 114.
- The text says "(Section 6)", but §6 does not describe this experiment. It appears only in E22(F).

### Conjectures and their stated relationships

- **Conj. 7.1 ⇒ Gallai** (by Prop. 4.2) and **the 3-connected cases of 7.1 and 7.2 ⇒ Gallai** (by Cor. 3.4): correct.
- **"Up to order 9 the two are equivalent, and both fail exactly when J − z is disconnected" (l. 593–594): ERROR.**
  - The equivalence holds only for d(r) ≥ 3.
  - "Exactly when" is false. In `jzdisc.py` at n = 7, 124 pairs have J − z disconnected. 83 of them have d(r) ≥ 3, and 76 of those satisfy both STL and (T1). The smallest example is `DsO` (n = 5) with z = 1, r = 0.
  - The data support only "every failure has J − z disconnected".
- **Conj. 7.3 (STL = (T1) for d(r) ≥ 3; STL2 = (T2) for d(r) ≥ 4).** Correctly stated, and "only ⇐ is open" is right.
  - For d(r) ≥ 3 the evidence is complete up to order 9. Where STL holds, (T1) holds by Thm. 3.2; where STL fails, the pipeline evaluates (T1).
  - My n ≤ 7 run found STL ≠ (T1) at 0 pairs with d(r) ≥ 3.
  - For STL2 at n ≤ 8, `run2_8.txt` reports `STL2fail-but-T2 0`.
- **Conj. 7.4 (STL-P) and "Equivalently (Proposition 4.4)": GAP.**
  - Prop. 4.4 covers only pairings with no pair adjacent in J. If xy ∈ E(J), then G = (J − z) + M is a multigraph.
  - Both the conjecture and the PAIR data range over all perfect matchings. For example, both realisable pairings of W₄ consist of rim edges.
  - The conjecture itself survives my `wheels.py`: W₆, W₈, W₁₀ (945/945) and W₁₂ (10,395/10,395).
- **Question 7.5: ERROR (trivial).** STS(u) is EE(u) together with star-terminality, so "EE is implied by STS" holds by definition. The intended question is presumably whether EE(u) implies STS(u).

### Lean

- **Compilation.**
  - `lake env lean GallaiLean/StarTerminal.lean` compiles. I ran it on a scratch copy with `#print axioms` appended, at an intermediate version.
  - `lake env lean ../manuscripts/stl/STLAxioms.lean` (HEAD) prints only the axiom lines, for all seven theorems.
  - No `sorry`, `admit` or `axiom` in `StarTerminal.lean` or `PrescribedEnd.lean`.
  - Every `.olean` is newer than its source. I did not run a full `lake build`.
- **`StarAt D z`** := ∀ P ∈ D, z ∈ P → s(src, z) ∈ P.edges ∨ s(tgt, z) ∈ P.edges.
  - When z is not an end, s(src, z) ∈ edges iff src and z are consecutive, iff z is the second vertex. So it is **equivalent** to the paper's definition.
  - If z were an end, the clause would admit only single-edge paths. But every use has b(z) = 0 (`not_end_of_ends_zero`, and z even in `STL`/`STL2`). Not vacuous.
- **`LongAt D z r`** := the path through zr does not end at r. This is "r long".
- **`HasShortShort D z`** := some path has all its edges at z. With b(z) = 0 this is exactly a path x z y; a length-1 path would end at z.
- **`STL`** = Lovász (ends = deg mod 2 everywhere) ∧ StarAt ∧ (LongAt ∨ HasShortShort). This is Def. 2.2.
- **`STL2`** = ends = deg mod 2 off r, ends r ∈ {0, 2}, StarAt, and (ends r = 0 ∨ LongAt ∨ SS). This is Def. 2.2; b(z) = 0 follows because z ≠ r is even.
- **`star_delete`.**
  - It states |D′| + #SS ≤ |D|, an inequality, whereas Lemma 3.1 has equality.
  - It states the end identity b′(v) + Σ c_P[i_P = 1] = b(v) + Σ c_P[i_P = 2]. For v ∈ N(z) exactly one P has c_P = 1, so this reads b′ = b + [long] − [short], which is what §8 says.
- **`test1_of_stl`, `test2_of_stl2`.**
  - Hypotheses: `hdeg` (every neighbour of z has degree ≥ 3) and STL at every r. The conclusions are the library's `Test1`/`Test2` verbatim.
  - This is the "all r" form, not the per-r "STL(J, z, r) ⇒ (T1) at r". It suffices for Cor. 3.4.
  - In `test2`, d(r) ≥ 4 is derived from d(r) ≥ 3 and evenness.
- **`gallai_of_stl`.**
  - Its hypotheses are exactly those of Cor. 3.4: KConnected 3, ¬HasMatchingCut (J − z), parity, all r.
  - The conclusion is `GallaiConjecture.{u}`, obtained via `gallai_iff_spineTests'.2.2`.
  - The hypotheses are neither vacuous nor contradictory, and the conclusion is the real conjecture (`pathNumber ≤ (card + 1)/2`).
- **`stl_of_deg_two`, `stl_of_deg_two_tri`, `stl_deg_two`.** These match Thm. 5.1 (cases 1 and 2) and Cor. 5.2.

### Computation (independent)

All results below come from my `pdec.py`.

| check | result | agrees with repo |
|---|---|---|
| W₄: pairings {12, 34}, {13, 24}, {14, 23} | realisable, **not** realisable, realisable; STL at all r | yes (Ex. 4.5, Table 3) |
| bowtie (two K₄ at z) | Lovász yes, ST no; STL/BAL/(T1) false at all 6 r | yes (Ex. 4.6) |
| all one-even graphs, n = 5 (7 graphs, 20 pairs) | STL fails at 1 pair (`Dus`, r = 2); ST fails on 0 graphs | yes (`fail_5.jsonl`) |
| all one-even graphs, n = 7 (130 graphs, 442 pairs) | STL fails at 9 pairs, exactly those of `fail_7.jsonl`; BAL fails at the same 9; ST fails on 1 graph (`FujTO`, the bowtie); 0 failures among the 318 pairs with J − z connected, which include all 126 pairs of the 28 3-connected graphs | yes |
| same graphs, (T1) | fails at 6 pairs (n = 5) and 48 (n = 7); STL true and (T1) false at 5 + 39 pairs, **all with d(r) = 1**; STL ≠ (T1) at 0 pairs with d(r) ≥ 3 | refutes the caption claim (fix 2) |
| flexibility, 3-connected, n = 5 and 7 | W₄: EE/STS 4/4, HALF 2/6, PAIR 2/3. n = 7: 28 graphs, EE/STS 126/126, HALF 244/266, PAIR 168/168 | yes (Table 3) |
| all 48 records of `fail_9.jsonl` (60 s per query; `out_fail9_all.txt`) | all 48 have exactly one even vertex and J − z disconnected; all 32 with d(r) ≥ 3 confirmed (STL, BAL, (T1) false); 8 of the 16 with d(r) = 1 confirmed; the other 8 dense ones timed out on the STL/BAL negative, with (T1) false trivially | yes, no disagreement |
| 25 random 3-connected graphs from `one_even_9.g6` (seed 77; `out_n9_3c_sample_b.txt`) | 124 pairs; ST on 25/25 graphs, STL and (T1) at 124/124 pairs (BAL timed out at the 8 pairs of `Hs`vfz~`, where STL implies it) | yes (`run_9.txt`: 25,210/25,210) |
| STL2, orders 4 and 6, all connected graphs | 4 + 52 instances; 1 failure (`Eqig`, z = 0, r = 1, as in `fail2_6.jsonl`); 3-connected: 10 instances, 0 failures, β = 0 in 4 | yes; gives 2,828 = 4 + 52 + 2,772, 958 = 10 + 948 and 748 = 4 + 744 |
| STL2, order 8, 20 random 3-connected graphs (seed 11; `out_stl2_8_3c_sample_b.txt`) | 40 instances; STL2 and (T2) hold in all; β = 0 in 32 | yes (`run2_8.txt`: 948/948) |
| Props. 4.1 and 4.4 against the definitions | 0 disagreements (462 pairs; 137 pairings) | |
| pairs with J − z connected | n = 5: 4 graphs / 10 pairs; n = 7: 99 / 318; n = 9: 10,893 / 44,008; **total 10,996 graphs, 44,336 pairs** | graphs yes; **pairs no (paper says 54,336)** |
| pairs with d(r) = 1 | n = 9: 1,162, of which 16 are STL failures in `fail_9`. So STL holds and (T1) fails at 1,146 pairs at n = 9, plus 46 at n ≤ 7: **1,192** in all | |

**Log cross-checks** (all agree):
- Table 1, random rows: sums of the `s1_*` logs (3,256 = 1,642 + 1,614; 3,470; 2,082; 338). Also 9,146 = 8,808 + 338.
- Families:
  - universal z: 1,232 = 400 + 360 + 280 + 192 pairs on 102 graphs;
  - zconn: 780;
  - zdisc11: 1,282 pairs, 4 STL failures, 4 (T1) failures.
- Table 2, random rows: 1,200; 1,000; 500.
- Undecided entries: every undecided entry of the `s1_*` and `s2_*` samples has a matching "resolved" line, ending with "undecided left 0".
- Table 3, n = 11: 1,290; 4,691/4,702 (plus 200 undecided); 5,196. These match `flex_11_*` together with `flex_11_gnp.res.log`.
- `flex_9.log`: 54,045. Also 54,213 = 168 + 54,045.

## Required fixes

1. **54,336 → 44,336.**
   - Correct it in the abstract (l. 58), Table 1 row 3 (l. 511), E22 (A) and connections §X.3.
   - In that table row, "among these" is wrong: the row covers n ≤ 9, while the row above covers n = 9 only.
2. **"STL ⇔ BAL ⇔ (T1) on all graphs of order ≤ 9" is false for d(r) = 1.**
   - Restrict it to pairs with d(r) ≥ 3 in the Table 1 caption (l. 524–525), §7 (l. 593), E22 (A) and connections §X.3.
   - Counterexample: the spider r–z–a–{b, c}. There r z a is SS, so STL holds, but r is isolated in J − z. There are 1,192 such pairs with |J| ≤ 9.
   - Replace "both fail exactly when J − z is disconnected" (l. 594) by "every failure has J − z disconnected". At n = 7, 76 of the 83 pairs with J − z disconnected and d(r) ≥ 3 satisfy both.
   - In the abstract (l. 59), "on these graphs STL is equivalent to the first test" should say "for d(r) ≥ 3". If "these graphs" means J − z connected, the statement is trivial, since both always hold there.
   - Relabel E22's "Test1 fails" column: (T1) was evaluated only where STL failed.
3. **Theorem 3.2, last sentence (l. 216–217).** Write "In particular, under the degree hypotheses of (a) and (b), …". Without them it fails: P₃ is a counterexample to the (T1) part, and 28 instances with d(r) = 2 at n ≤ 6 are counterexamples to the (T2) part.
4. **§6.1 oracle paragraph (l. 485–487), verification table.** Add a sentence saying what is computed where. (T1) and (T2) were evaluated only at STL/STL2 failures. This is legitimate for d(r) ≥ 3 by Thm. 3.2, but it is why fix 2 was not caught.
5. **Conjecture 7.4 (STL-P, l. 608–614).** Restrict "Equivalently (Proposition 4.4)" to pairings with no pair adjacent in J, or state the multigraph version. The conjecture and the PAIR data range over all pairings.
6. **Question 7.5 (l. 620–624).** STS(u) ⇒ EE(u) is trivial. Ask instead "Does EE(u) imply STS(u)?", i.e. are EE and STS equivalent?
7. **The undecided policy is stated inconsistently.**
   - §6.1 (l. 486–487) says "every undecided instance reported below was re-run … until decided". Table 3's footnote (l. 574–575) says 200 HALF queries were left undecided. Qualify the §6.1 sentence.
   - The STL2 counts for n = 4 and 6, used in 2,828, 958 and 748, have no log in `scripts/out/`; only `fail2_4.jsonl` and `fail2_6.jsonl` exist. Add a summary log. My recount agrees with the numbers.
8. **Lean mentions are stale.**
   - Intro item (2) lists four Lean theorems. Add `stl_of_deg_two`, `stl_of_deg_two_tri` and `stl_deg_two`.
   - §8 (l. 627) says StarTerminal "imports Separator.lean". It now also imports `Separation`, and `stl_deg_two` uses `PrescribedEnd`.
9. **Prop. 4.3, intro and abstract.** "EE of [MS]" should say **without classes**, since MS's Conjecture EE (Conjecture 17 there) carries a class family.
10. **Citations.**
    - "[MS, Question 5.2]" (l. 359) does not exist. MS numbers statements globally, and the packed-set question is Question 25 (`q:pe`). Cite it by name.
    - "[RD, E20]" (l. 450): E20 is in `research/experiments.md`, not in RD. The RD statement is Remark 6.7 (`rem:L1res`).
    - "[MS, §5]" (l. 454): the multi-prescription problem is the open question in MS §10. §5 only mentions it.
11. **Remark 5.3, parity-neutral construction (l. 450–454).** State that it is for d(z) = 4, i.e. N(z) = {a, b, c, d}. For d(z) ≥ 6 the remaining neighbours stay even.
12. **Composition subsection (l. 466).** "(Section 6)" should point to E22(F) and `ptm_run.py`. Alternatively, add the experiment and its table to §6: (n, m) = (8, 2), (10, 2), (12, 2), (10, 3), with 299, 300, 300, 300 instances.
13. **Nits.**
    - Table 1, wheels row: the "8 pairs" are one r per wheel (by symmetry). Say so.
    - Def. 2.1 (l. 158): "the edge wz lies on exactly one path".
    - Prop. 4.1 proof (l. 287–290): "long sides whose remainder is nonempty" is redundant. In "r ∈ T unless r is short or lies on an SS path, in which case |T| < k", the bound |T| < k does not follow from r being short: an SL transition with r short and no SS gives |T| = k. It follows from STL's disjunct #SS ≥ 1. Reword as "if r is short, STL gives #SS ≥ 1, so |T| < k".
    - Lean, §8: `star_delete` proves |D′| + #SS ≤ |D|, not equality. `test1_of_stl` and `test2_of_stl2` are all-r forms with `hdeg` at every neighbour. Both are fine for Cor. 3.4, but §8 could say so.

## Fixes applied (stl session, after this audit)
All 13 required fixes were applied to `manuscripts/stl/stl.tex`, E22 and connections §X.

1. **Count.** 54,336 → 44,336 (abstract, Table 1, E22(A), §X.3). The Table 1 sub-row labels now say "rows 1–2 with J − z connected (n ≤ 9)" and "row 2 with J 3-connected".
2. **Equivalence claim.**
   - STL ⇔ BAL ⇔ (T1) is now restricted to d(r) ≥ 3 (abstract, Table 1 caption, §7, E22, §X.3), with the d(r) = 1 explanation added.
   - "Fail exactly when J − z is disconnected" is replaced by "every failure has J − z disconnected (most disconnected pairs satisfy both)".
   - E22's column is relabelled "Test1 fails among these".
3. **Thm 3.2.** "Under the degree hypotheses of (a) and (b)" is added.
4. **§6.1.** It now says that (T1) and (T2) were evaluated only at STL/STL2 failures.
5. **Conj. STL-P.** The equivalence is restricted to pairings with no pair adjacent in J; the multigraph variant is noted.
6. **Question.** Now asks whether EE(u) ⇒ STS(u); the converse is trivial.
7. **Undecided policy.** §6.1 now says that all STL/STL2 undecided entries were resolved and only the 200 marked HALF queries remain. `scripts/out/run2_4.txt` and `run2_6.txt` were regenerated.
8. **Lean descriptions.** The intro and §8 now list `stl_of_deg_two`, `stl_of_deg_two_tri` and `stl_deg_two`, and the imports (Separator, Separation, PrescribedEnd). The all-r form of the test theorems and the ≤ in `star_delete` are stated.
9. **"Without classes"** is added to every mention of EE from [MS].
10. **Citations.** Now [MS, Conj. 17], [MS, Prop. 16], [MS, Prop. 18], [MS, Thm. 14], [MS, Question 25] and [RD, Remark 6.7]. The numbers were verified by compiling both manuscripts and reading their `.aux` files.
11. **Remark 5.3.** "For d(z) = 4" is added.
12. **Composition data.** New §6 subsection "Composition data" with Table `tab:ptm` (E22(F), `ptm_run.py`); the Composition paragraph cites it.
13. **Nits.**
    - The wheels row says "one r each".
    - Def. 2.1 wording fixed.
    - Prop. 4.1 proof: |T| < k now comes from #SS ≥ 1.
