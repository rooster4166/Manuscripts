# A28 — Audit of direct-test1 (manuscript, `DirectTest1.lean`, scripts)

Date: 2026-11-27. Referee stance: adversarial. Grades: **SOUND**, **GAP** (fixable), **ERROR** (false as stated), **OVERCLAIM** (true content, overstated).

**Version.** Everything below is audited at branch `claude/triangle-base`, **d9aad30**: tex and pdf from d2e13de, scripts from 2a92f02, Lean from bd616c7. The branch moved during the audit:
- `tb.py` appeared at 17:39, untracked.
- 159820d added `TriangleBase.lean` (Conjecture DL).
- 468582a added E29 (draft) and the `dl_*.py` scripts.
- An uncommitted rewrite of `direct-test1.tex` appeared, which already adopts most fixes below.

None of the new material is audited here. §7 records the status of the rewrite as of 18:06.

**Line numbers.** "l." is `direct-test1.tex` (186 lines). "L." is `lean/GallaiLean/DirectTest1.lean` (845 lines).

**Numbering.** The brief and the Lean docstrings say "Conjecture 3.1", "Example 4.1" and "§5". The compiled PDF numbers them **Conjecture 2.4** (l. 126), **Example 3.1** (l. 141) and **§4 Evidence** (l. 156). The conjecture sits inside §2, and the theorem counter is per section. I use the PDF numbers below, with the brief's in brackets where it helps. See F9.

**Auditor files** (written in the session scratchpad; copied into `research/audit/A28-scripts/` when the audit was recorded, without the regenerable logs; paths inside the scripts still point at the scratchpad):
- `A28Check.lean`: Lean proof that an (E7) base of t6-dense is a triangle base (§2.1).
- `aud28.py`: data availability, the counterexample, and an independent brute-force equivalence check.
- `equiv9.py`: the same equivalence check on random order-9 graphs.
- `tb9.py`: exhaustive order-9 triangle-base run with witness verification.
- `e7dense.py`, `e7dense_rest.py`, `e7lib.py`, `e7cmp.py`: (E7) base versus triangle base on the same graph M (logs `e7dense.log`, `e7dense_rest.log`).
- `run/`: the compiled oracle, the logged reruns of `dtl.py`, and the `recheck.py` output.

---

## 0. Headline

1. **The mathematics of the lift is correct.** I checked Lemma 1.2 and both steps of Theorem 2.1 line by line, including:
   - the case Q0(z) = zr;
   - the shared-path case in Step 2;
   - the "extended at most twice" argument.

   The guard example is correct. I enumerated all its decompositions; one sentence of justification is wrong (F7). The only hypothesis Theorem 2.1 really uses is d(r) ≥ 3, beside the single even vertex z. δ ≥ 3 elsewhere, 3-connectivity and m ≥ 2 are not used.
2. **The Lean is faithful, and slightly more general.**
   - `lake build` is green (18,400 jobs). There is no `sorry`.
   - `test1At_of_triangleBase`, `test1_of_triangleBases` and `test1_of_triangleBaseConj` depend only on `propext`, `Classical.choice` and `Quot.sound`. So do `append_pairs`, `triM_parity` and `triM_size`.
   - `TriangleData`, `triM`, `TriangleDisj`, `TriangleBase` and `Test1At` match Definition 1.1, (2.1) and (T1) exactly.
   - `TriangleBaseConj` differs from the paper's conjecture: it adds the hypothesis that data exist. The Lean form is the correct one (point 3).
3. **ERROR: Conjecture 2.4 [3.1] as stated is false.** It asserts that "for every r there are data as in Definition 1.1". Data need not exist.
   - J = K_{3,4} + x1x2 is 3-connected. Its only even vertex is z, with d(z) = 4, and N(z) is independent. So no root has data.
   - On TM's order-9 list (1,819 instances (J, z)), 796 of 10,914 roots have no data. 354 instances have such a root, and 17 have no data at any root.
   - Lean's `TriangleBaseConj` is conditional on data existing. That is the statement the note means (see l. 131–133).
4. **ERROR: Remark 2.2, "the auxiliary graphs differ" (l. 114–115).** For m = 3, take r = y1, w = x3 and M0 = {x1y2, x2y3}. Then t6-dense's base graph and this note's M are the *same graph*. t6-dense's conditions (E5) and (E7) are one disjunct each of (2.1).
   - So every (E7)-branch base of t6-dense Conj 5.1 at a labelling is, verbatim, a triangle base at y1. I proved this in Lean (`triangleBase_of_E5_E7`, standard axioms). It uses neither (E1)–(E4) nor the parity hypothesis.
   - Hence "neither base condition obviously implies the other" is false in one direction.
   - In effect, Theorem 2.1 at m = 3 is the two chain-edge appends of t6-dense Theorem 2.2 (its Steps 2 and 4), followed by deleting z. The rest of that proof rebuilds the star at z.
5. **The lift is reversible (missing converse; framing).** For fixed data (r, w, M0), M has a Lovász decomposition with (2.1) **iff** J − z has a (T1) decomposition at r in which every edge of M0 is terminal (an end edge of its path).
   - I proved this by hand (§2.2).
   - I confirmed it by an independent brute force: all graphs of order 7 (444 data choices, 18 with neither side, **0 disagreements**) and 1,148 data choices on random order-9 graphs (0 disagreements).
   - So Conjecture 2.4 is (T1) with a prescribed terminal matching of N(z) − {r, w}. It is a terminal-matching strengthening of (T1), not a weaker statement of a new kind. This is the A26 F2 situation again, one level lower.
6. **Data reproduce, with an overstatement.**
   - `python3 dtl.py ORACLE 1 30 11` reproduces the table exactly (180/180/180/175, 9 "undecided", 2 min). The command and log are not committed.
   - "Nine individual queries exceeded the budget" (l. 176) is wrong. **177 of 756** queries hit the budget. "9" counts *data choices* with no success and at least one budget hit.
   - No query returned 0. So the five roots where the first data choice "does not work" are budget-undecided, not refuted.
   - The d(z) = 8 "results recorded in `scripts/out/`" (l. 177–178) are one `NO BASE` line. My rerun at a 30M budget finds a base for that root.
   - An independent exhaustive order-9 run finds a triangle base at **all 10,118 roots that have data**. All 10,118 witnesses were verified independently (Lovász profile, edge partition and (2.1)). The project's scripts never verify the base D0 itself.

## 1. Verdict per claim

| Claim | Verdict | Notes |
|---|---|---|
| Setting, Lovász decomposition (l. 42–49) | SOUND | Order 2k+1 follows from the single even vertex; d(z) ≥ 4 follows from δ ≥ 3. Lean's `ends v = degree v % 2` is exactly "end of exactly d(v) mod 2 paths". |
| Def 1.1 (l. 51–58) | SOUND | 1 + 3(m−1) = 3m − 2 deleted edges. `TriangleData` + `triM` are verbatim (§3). |
| Lemma 1.2 (l. 60–72) | SOUND | §1.1. Nit: "Disconnected M is handled componentwise" (l. 71) is irrelevant to an end count. |
| Thm 2.1, Step 1 (l. 86–98) | SOUND | §1.2. Both cases checked; "vertex sets only shrink" is correct. |
| Thm 2.1, Step 2 (l. 100–106) | SOUND | §1.2. "At most twice" needs one more clause (F8, nit). |
| Thm 2.1, hypotheses | SOUND | Uses only "z is the only even vertex" and d(r) ≥ 3. Lean (`hz`, `hr3`) states exactly this and allows m = 1. |
| Remark 2.2: "five or six end-path conditions" (l. 111–112) | SOUND (nit) | (E1)–(E5)+(E7) is six end-path conditions; (E1)–(E5)+(E6) is five plus a predecessor condition. Say so. |
| Remark 2.2: "neither ... obviously implies the other, since the auxiliary graphs differ" (l. 114–115) | **ERROR** | F2. The graphs coincide; (E7) branch ⇒ triangle base, in Lean. |
| Remark 2.2: A26 citation (l. 112–113) | SOUND | Now t6-dense Prop 2.6. Cites `test1_of_appendBases`; the base-on-M form is `test1_of_lovaszBases`. |
| Remark 2.3: data in the five dense shapes (l. 119–121) | SOUND | Checked: every root of each shape has 5–15 data choices. |
| Remark 2.3: "peeling" (l. 121–123) | Informal; OVERCLAIM (mild) | No statement covers the peeled instance (O2). |
| Conj 2.4 [3.1] (l. 126–129) | **ERROR** | F1: data are not guaranteed. Lean's `TriangleBaseConj` is the correct, conditional form. |
| Sentence after the conjecture, first half (l. 131–132) | SOUND, given F1 | It matches `test1_of_triangleBaseConj` if "admits the data" means at every root. |
| "covers the two-end half of Gallai's conjecture in that range" (l. 132–133) | OVERCLAIM | F4. |
| Abstract framing "(T1) follows from a single Lovász decomposition of ... M" (l. 28–31) | OVERCLAIM (framing) | F3: the condition is equivalent to (T1) plus a terminal matching. |
| Abstract "replaces the five or six ... by two disjunctive ones" (l. 32–33) | OVERCLAIM (mild) | F2: it *drops* (E1)–(E4) and weakens (E5), (E7) on the same graph. |
| "(2.1) fails exactly when ..." (l. 137–138) | SOUND | The first alternative is a special case of the second. |
| Example 3.1 [4.1] (l. 141–154) | SOUND; GAP in one sentence | F7. All decompositions enumerated (§1.3). |
| §4 [§5] method description (l. 158–164) | SOUND | Oracle query A is exactly per-end avoidance (§4). D0 itself is not verified (F6). |
| §4 table (l. 166–174) | SOUND, not documented | Reproduces exactly with seed 1 (F5). |
| "Nine individual queries exceeded the budget" (l. 176) | **ERROR** | F5: 177 queries; 9 is a count of data choices. |
| "results at d(z) = 8 are recorded in `scripts/out/`" (l. 177–178) | OVERCLAIM | F6. |
| Lean faithfulness | SOUND | §3. The conjecture form differs from the paper (F1), and numbering pointers are wrong (F9). |
| Build / axioms / `sorry` | SOUND | §3.1. |

### 1.1 Lemma 1.2

- **z.** Of the 2m edges at z, only zr survives. So d_M(z) = 1.
- **w.** w is matched by no pair and w ≠ z, so it loses only zw. Then d_M(w) = d_J(w) − 1 is even and ≥ 2. This uses δ ≥ 3 at w; nothing later uses d_M(w) ≥ 2.
- **a_i, b_i.** Each loses exactly za_i (or zb_i) and a_ib_i. Pairs are vertex-disjoint, so no other pair edge is incident. So the degree stays odd, and it is ≥ 1 automatically.
- **Everything else.** r keeps zr. Vertices outside N[z] are untouched.
- **Count.** 2k odd vertices, one end each, so k paths. No connectivity is involved. "Disconnected M is handled componentwise" (l. 71) can go, or move to the existence remark (Lovász's theorem).
- **Lean.** `triM_parity` (L. 601–625) and `triM_size` (L. 628–639) prove the parity and size parts from `hz` alone. They do not need δ ≥ 3.

### 1.2 Theorem 2.1

**Step 1.**
- B0 = M − z = J − z − M0. In B0:
  - w and r are even, of degrees d_J(w) − 1 and d_J(r) − 1;
  - every other vertex is odd.
- Q0(z) is the unique path ending at the leaf z, so it starts z, r.
- **Length ≥ 2.** r is interior: it is the second of at least three vertices, and the path is simple. So the unique end of r in D0 is on a different path. Trimming z gives r a second end and keeps k paths of positive length.
- **Q0(z) = zr.** Since r is odd in M, its only end is on zr. After deletion r has no end but has degree d_J(r) − 1 ≥ 2. So every visit to r is internal, and splitting one path there gives k paths with exactly two ends at r.
- **This is the only use of d(r) ≥ 3.** If d_J(r) = 1, (T1) fails outright.
- **Vertex sets shrink.** Every other odd vertex keeps exactly one end. Its path is Q0(v), Q0(v) − z, or the piece of a split Q0(v) carrying the end v. So V(P1(v)) ⊆ V(Q0(v)).

**Step 2.**
- **Choice.** (2.1) and the inclusion give (v_i, u_i) with u_i ∉ V(P1(v_i)).
- **When pair i is processed:**
  - The end at v_i is untouched, since earlier appends act at v_j and create ends at u_j, and {v_i, u_i} ∩ {v_j, u_j} = ∅.
  - The current path through v_i is P1(v_i), possibly extended once at its *other* end by some u_j.
  - It cannot have been extended twice there: after an append the new end is u_j, and u_j is never a v_l. For l = j, v_j ≠ u_j; for l ≠ j, the pairs are disjoint.
  - So V(P(v_i)) ⊆ V(P1(v_i)) ∪ {u_j} with u_j ≠ u_i, and the append is legal.
- **Distinct paths.** P(v_i) ≠ P(u_i), since u_i ∉ V(P1(v_i)).
- **Count and ends.** The count stays k. Ends move only from v_i to u_i, and r ∉ ⋃{a_i, b_i}, so r keeps two ends.
- **Where the matching property enters.** It is used three times:
  - v_i's end is not disturbed by earlier appends;
  - u_j ≠ u_i;
  - the same disjointness bounds the extensions per end to one.
- **Gap.** The text gives only the second use (l. 104) and "a path has two ends" (l. 105). See F8 (nit).
- **Hypotheses.** None is missing. 3-connectivity, δ ≥ 3 off r and m ≥ 2 are not used. For m = 1 (L = []), the statement is the trivial "delete the leaf z". The Lean allows it.

### 1.3 Example 3.1: all decompositions

H has edges ax, xb, by, ya, bt1, at2 and degrees a = b = 3, x = y = 2, t1 = t2 = 1. With two paths, the four ends lie on a, b, t1, t2, one each.

- **{t1, t2}, {a, b}.** The paths are t1 b x a t2 + b y a, or t1 b y a t2 + b x a. Q(a) = Q(b), which violates (2.1).
- **{t1, a}, {t2, b}.** The paths are t1 b x a + t2 a y b, or the same with x and y exchanged. Each path contains the other vertex, which violates (2.1).
- **{t1, b}, {t2, a}.** The t1-path must be the single edge t1b. The other path would then contain the 4-cycle, which is impossible.

So every such decomposition violates (2.1), and **the example is correct**. But l. 144 says "Since t1 is a leaf at b, no path joins t1 to b". That is false: the edge t1b is such a path. What fails is the complementary path (F7).

## 2. Comparison and novelty (Remark 2.2, abstract)

### 2.1 The two base graphs coincide; the (E7) branch implies the triangle base

t6-dense Definition 2.1 (`t6-dense.tex` l. 203–227) uses M_t6 = J − {zx1, zx2, zx3, zy2, zy3, x1y2, x2y3}, with x1y2, x2y3 ∈ E(J).

For r = y1, w = x3 and M0 = {x1y2, x2y3}, Definition 1.1 deletes {zx3} ∪ {zx1, zy2, x1y2} ∪ {zx2, zy3, x2y3}. That is **the same seven edges**. The chain edges are exactly a perfect matching of N(z) − {y1, x3} by edges of J.

Now compare the conditions:

| Pair of (2.1) | Disjunct | t6-dense condition |
|---|---|---|
| (x1, y2) | y2 ∉ V(Q0(x1)) | (E7) "P_{x1} avoids y2" |
| (x2, y3) | y3 ∉ V(Q0(x2)) | (E5) "P_{x2} avoids y3" |

So **every (E1)–(E5)+(E7) base at a labelling is a triangle base at y1**, with the same D0. The proof is `triangleBase_of_E5_E7` in `A28Check.lean`. It compiles against the built library and depends only on `propext`, `Classical.choice` and `Quot.sound`.

Its hypotheses are:
- the distinctness and N(z) clauses of `LovaszBase`;
- the chain edges;
- a Lovász decomposition of `baseM`;
- (E5) and (E7).

The proof shows `baseM J z x₁ x₂ y₂ x₃ y₃ = triM J z x₃ [(x₁,y₂),(x₂,y₃)]` by `ext`, then transports D0.

**Consequences.**
- "Neither base condition obviously implies the other, since the auxiliary graphs differ" is false.
  - The correct statement is that, at m = 3 and root r = y1, the triangle base is implied by the (E7) branch of the t6-dense base on the same graph. It drops (E1)–(E4) and keeps only one disjunct each of (E5) and (E7).
  - No implication is known for the (E6) branch, or for labellings with r ∈ {y2, y3}. Conj 5.1 allows both.
  - Synthesis §24 and ROADMAP l. 601 call the triangle base "weaker" or "sharper". That is right for this branch but is not proved in general, and it contradicts the note's own wording.
- **Novelty.**
  - The base graph M (at m = 3) and the append mechanism (`append_full`, reused in the Lean) come from t6-dense.
  - Theorem 2.1 at m = 3 is the two chain-edge appends of t6-dense Theorem 2.2, followed by deleting z. Those appends are its Step 2 (x2 → y3, legal by (E5)) and Step 4 (x1 → y2, legal by (E7)); see `t6-dense.tex` l. 372–414.
  - Steps 1, 3 and 5–8 there rebuild the star at z (leaves ℓ2, ℓ3, transitions x_i z y_i). (E1)–(E4) are used only for those steps and their leaf conditions. A (T1) target does not need any of this.
  - What is new:
    - the general-m statement;
    - the disjunctive form of the end conditions;
    - the direct (T1) target, bypassing STL;
    - the general-m Lean.
  - Remark 2.2 should say this. The proposal is credited to an external collaborator (l. 34–35), which is fine.
- **Data (partial).** `e7dense.py` is an exact Python brute force with no budget. It ran over **18 of the 28** dense-core graphs of TM's order-9 list, then I stopped it, because some graphs take about 10 minutes each.
  - Covered: 108 roots, 1,052 data choices and 8,416 labellings.
  - Every data choice has both a triangle base and an (E7) base for at least one of its 8 labellings, and in fact every labelling has an (E7) base.
  - There is no case with a triangle base but no (E7) base. So strictness is not visible on these graphs.
  - The other 10 graphs (60 roots) are unchecked. A26 found 16 labellings without an (E7) base in this family, so none of them lies in the 18 graphs covered.
- **"Five or six end-path conditions"** is accurate if read as six with (E7), or five end-path conditions plus the predecessor condition (E6). t6-dense itself says "six of them" (l. 639).

### 2.2 The lift is an equivalence (the triviality question)

**Proposition (auditor).** Fix data (r, w, M0) at (J, z), with z the only even vertex. The following are equivalent:
- (a) M has a Lovász decomposition D0 satisfying (2.1) for every i;
- (b) B = J − z has a decomposition into at most k paths, with at least two ends at r, in which every edge a_ib_i of M0 is terminal (the first or last edge of its path).

**Proof.**
- **(a) ⇒ (b).** This is Theorem 2.1. Each a_ib_i is appended at v_i and becomes the terminal edge at u_i. It stays terminal, because no later append acts at u_i (u_i is never a v_l).
- **(b) ⇒ (a).** Count ends.
  - In B, N(z) is exactly the set of even vertices.
  - The 2k − 2m odd vertices have at least one end each.
  - r has at least two.
  - The vertex u_i at which a_ib_i is terminal is even and has an end, so it has at least two.
  - That totals at least (2k − 2m) + 2 + 2(m − 1) = 2k ends. There are 2·size ≤ 2k ends, so equality holds everywhere:
    - exactly k paths;
    - one end at each odd vertex;
    - two at r and two at each u_i;
    - none at w and none at the other endpoint v_i.
  - In particular no path is the single edge a_ib_i, since that would give an end at v_i.
  - **Undo the appends.**
    - Delete each a_ib_i from its path end at u_i. A path with M0-terminal edges at both ends has length ≥ 3.
    - Then append z to one of the two r-paths.
    - The result decomposes M with one end everywhere except w, so it is Lovász.
  - Q0(v_i) is the shortened path. It no longer contains its former end u_i, and later changes remove another end vertex or add z. So u_i ∉ V(Q0(v_i)), and (2.1) holds.

**Check (independent of `route_ext.c` and of the project scripts).**
- `aud28.py` decides (a) by an exact DFS over Lovász decompositions with per-end avoidance, one run per orientation.
- It decides (b) by an exact DFS over all decompositions of B. That DFS prescribes no end profile and only bounds the count by k.
- Results:
  - **All graphs of order 7** with one even vertex and δ ≥ 3 (35 graphs, 28 of them 3-connected): 444 data choices, 426 with both sides, 18 with neither, 0 with one side only.
  - **Random order 9**, d(z) = 6 (40 graphs) and d(z) = 4 (60 graphs): 828 + 320 data choices, 0 disagreements.
  - In every run, each root where (T1) holds and data exist also has a triangle base. The only (T1) failures (6 roots) are all in one order-7 graph, which has a cut vertex (z joined to two triangles).

**Consequence.**
- Conjecture 2.4 [3.1] says that (T1) at r holds with a **terminal matching**: a perfect matching of N(z) − {r, w} by edges of J, each matching edge terminal at its doubled end.
- This is a strengthening of (T1) itself, of the same type as PTM in `terminal-matching`. It is not a statement in a weaker "Lovász setting".
- The note's framing (abstract l. 28–31; "auxiliary graph M with one even vertex") hides this. A26 F2 made the same point for t6-dense, and t6-dense now states its converse as Prop 2.6. This note should do the same (F3).
- The reformulation is still useful. It is uniform in m, has no chain hypothesis, and in the data it fails exactly where (T1) fails.

## 3. Lean faithfulness

### 3.1 Build and axioms

- **Build.** `export PATH=$HOME/.elan/bin:$PATH; cd lean; lake build` gives "Build completed successfully (18400 jobs)". `GallaiLean.lean` l. 74 imports `GallaiLean.DirectTest1`. The log shows no warnings from DirectTest1; the only warnings are T6Dense linter notes.
- **`#print axioms`** (scratch file importing `GallaiLean.DirectTest1`, run with `lake env lean`): `test1At_of_triangleBase`, `test1_of_triangleBases`, `test1_of_triangleBaseConj`, `append_pairs`, `TriangleData.triM_parity` and `TriangleData.triM_size` all give `[propext, Classical.choice, Quot.sound]`.
- **`sorry`/`admit`.** Grep finds none in `GallaiLean/*.lean`. The only hit for `admit` is the word "admits" in the docstring at L. 832; `sorry` occurs only in `THM59_PLAN.md`.
- There is no axioms file for DirectTest1, unlike `T6DenseAxioms.lean`. That is optional.

### 3.2 Definitions against the note

| Lean | Note | Verdict |
|---|---|---|
| `TriangleData` (L. 295–298): `(r :: w :: pairVerts L).Nodup`, `J.Adj z v ↔ v = r ∨ v = w ∨ v ∈ pairVerts L`, `∀ p ∈ L, J.Adj p.1 p.2` | Def 1.1 | **Exact.** Nodup makes the pairs a matching that avoids r and w; `nbr` makes it perfect on N(z) − {r, w}. The list encodes an ordering and orientation of M0, and both are irrelevant, since (2.1) is symmetric under a ↔ b and the appends commute. `L = []` only if d(z) = 2 (m = 1), which the note excludes and Lean allows. |
| `zDel`, `triDel`, `triM` (L. 279–287) | M (l. 55) | Exact: zw, za_i, zb_i, a_ib_i. |
| `TriangleDisj` (L. 302–304) | (2.1) | Exact, same direction: "every path ending at b avoids a, or every path ending at a avoids b". Under the Lovász profile, "every path ending at b" is Q0(b). |
| `TriangleBase` (L. 310–312): `∃ w L, data ∧ ∃ D₀, (∀ v, D₀.ends v = (triM ..).degree v % 2) ∧ TriangleDisj` | "data + Lovász decomposition with (2.1)" | Exact; the Lovász condition is the note's definition (l. 42–44) verbatim. |
| `Test1At` (L. 316–318): `∀ hr, ∃ D : PathDecomp (delVert J z), D.size ≤ (card V − 1)/2 ∧ 2 ≤ D.ends r` | (T1) at (J, z, r) (l. 48–49) | Exact; (card V − 1)/2 = k. `Test1 J z` (`ThreeConnected.lean` l. 186) is `hz → ∀ r, Test1At`-shaped (`test1_of_test1At`). |
| `test1At_of_triangleBase` (L. 778–820): `hz → 3 ≤ J.degree r → TriangleBase J z r → Test1At J z r` | Thm 2.1 | **Concludes exactly (T1).** The hypotheses are *weaker* than the note's "Throughout" (no δ ≥ 3 off r, no d(z) ≥ 4). The proof appends first (`append_pairs`, `append_full`), then trims the leaf (`mapInj` to `addLeaf (J − z) r`, `trim_ends`, `leafCost`, `exists_two_ends`). That is valid, and documented at L. 18–25. The note's inclusion V(P1(v)) ⊆ V(Q0(v)) is therefore not formalised, and not needed. |
| `test1_of_triangleBases` (L. 824–827) | — | Correct per-root assembly; `hdeg` at N(z) only. |
| `TriangleBaseConj` (L. 833–836): `KConnected 3 J → hz → ∀ r, J.Adj z r → (∃ w L, TriangleData J z r w L) → TriangleBase J z r` | Conj 2.4 [3.1] (l. 126–129) | **Weaker than the note**: it adds the data hypothesis. The note's version is false (F1), so the Lean is the right statement; the note must be changed to match. |
| `test1_of_triangleBaseConj` (L. 839–843): `hC → KConnected 3 J → (∀ r ∈ N(z), ∃ data) → Test1 J z` | l. 131–132 | Matches, reading "whose even vertex admits the data" as "at every root r ∈ N(z)". `Test1` carries `hz` internally, and `hdeg` comes from `KConnected.le_degree`. |

Lemma 1.2 is formalised by `triM_adj_z`/`triM_degree_z` (z a leaf at r), `triM_parity` and `triM_size`. "d_M(w) ≥ 2" is not formalised and not needed.

### 3.3 Pointer issues (non-mathematical)

- **Numbering.** Several docstrings point to items the PDF numbers differently:
  - L. 38, 309, 831 say "manuscript Conjecture 3.1"; the PDF has Conjecture 2.4.
  - L. 38 says "the remark after it", but l. 131–133 is an unnumbered paragraph.
  - The brief likewise says "Example 4.1" and "§5"; the PDF has Example 3.1 and §4.
- **The note never mentions `DirectTest1.lean`.** It was committed (bd616c7, 17:35) after the note (d2e13de, 17:16).
- Remark 2.2 cites `test1_of_appendBases` (the split form). The base-on-M form matching Def 2.1 is `test1_of_lovaszBases` / `LovaszBase`.

## 4. Data

### 4.1 What the scripts do

- **(i) Base search.** For each data choice, `dtl.py` (l. 158–169) sends 2^(m−1) `WAB` queries with profile b = deg_M mod 2 and `avoid[b_i] = {a_i}` or `avoid[a_i] = {b_i}`. In `route_ext.c`, query A means:
  - the start vertex's mask is put into `vis`, so the path never visits it (l. 197);
  - the closing vertex's mask is checked against the path mask (l. 133–134).

  That is exactly "the path ending at v avoids x_v". The failure memo (rem, b) is exact, because each constraint is checked when its path closes and budget-aborted subtrees are not memoised (l. 198). So "exact oracle, four per-end avoidance queries, node budget per query" is accurate.
- **(ii) The lift.** `lift` (l. 73–111) runs Step 1 as written. Step 2 is greedy: it tries (b_i, a_i) and then (a_i, b_i) against the *current* path, rather than the orientation the query certified. That is still a legal sequence of appends, and by the proof of Thm 2.1 it succeeds whenever (2.1) holds.
- **(iii) Verification.** `verify` (l. 114–129) checks:
  - each path is simple and has positive length;
  - every edge is in B and used once, and the count equals |E(B)|;
  - there are ≤ k paths and ≥ 2 ends at r.

  That is exactly the claim at l. 163–164. Two caveats:
  - structural failures are Python `assert`s, which crash the run (and vanish under `python -O`) rather than counting as `lift_fail`;
  - the base D0 is never checked to be a Lovász decomposition of M or to satisfy (2.1). "Base found" rests on the oracle alone.
- **Scope.** `dtl2.py` and `dtl_resid.py` differ from `dtl.py` only by a general-m matching enumerator and a residual-file loader.

### 4.2 Reproduction

- **The table.** `python3 dtl.py <route_ext> 1 30 11` (seed 1, 30 trials, n = 11) gives `FINAL {'roots': 180, 'roots_ok': 180, 'first_ok': 175, 'lift_ok': 180, 'lift_fail': 0, 'nomatch': 0, 'undecided': 9}` in 2 min, and no `NO BASE` or `LIFT FAIL` lines. That matches l. 171 exactly.
  - The seed, arguments and log are not recorded anywhere. I found them by trying the script default seed. `dtl.py`'s default `nvals` is "11,13", not "11".
- **"Nine individual queries exceeded the budget" is wrong.** I reran with a logging wrapper around the oracle. Of 756 queries, **177 returned 2 (budget)**, 579 returned 1 and **0 returned 0**.
  - The script's `undecided` counter (l. 171–172) counts *data choices* in which some query hit the budget and none succeeded. That is the 9.
  - Since no query was refuted, the 5 roots whose first data choice "does not work" are budget-undecided, not proved base-free. The column header suggests otherwise.
- **d(z) = 8 (l. 177–178).** `scripts/out/` contains only `nobase_budget.txt`, with three `NO BASE` lines.
  - One is d(z) = 8, n = 13, r = 1.
  - Two are n = 15, d(z) = 6, r = 1, 2, from the K2-residual run of `dtl_resid.py`. That run is not mentioned in the note, and its input file is not committed.
  - There are no summary statistics for d = 8. The "24/24" of synthesis §24 is recorded nowhere, and the `NO BASE` line contradicts a clean 24/24.
  - `recheck.py` at a 30M budget per query (8 min) gives:
    - the d = 8 root: **FOUND** (w = 3, pairs (6,7), (8,10), (9,12));
    - both n = 15 roots: **UNDECIDED**.

### 4.3 Independent exhaustive order 9 (auditor)

`tb9.py` ran over TM's `d6_9.g6`: 1,819 instances (J, z), with J 3-connected and z the only even vertex, d(z) = 6.
- It tests every root and every data choice until one is found, with a 2M budget and an exact oracle.
- Every witness is decoded and **verified in Python**: a partition of E(M) into simple paths, ends equal to deg_M mod 2, and (2.1).

The result is `roots 10,914; no data 796; found 10,118; absent 0; undecided 0; 40,472 queries, 0 budget hits; 10,118 witnesses verified`.

| Shape | Roots with a base |
|---|---|
| ∅ | 12 |
| K2 | 36 |
| P3 | 48 |
| K3 | 30 |
| C4 | 42 |
| other D | 9,950 |

The dense counts (28 graphs, 168 roots) agree with A26's order-9 census. 1,465 of the 1,819 instances have data at every root, so `test1_of_triangleBaseConj` reaches about 80% of them at order 9. 337 have data at some roots only, and 17 at none.

## 5. Required fixes

- **F1 (ERROR, Conjecture 2.4 [3.1], l. 126–129).**
  - "for every r there are data" is false. Counterexamples:
    - J = K_{3,4} + x1x2 (n = 7, κ = 3, N(z) independent);
    - at order 9, 354 of 1,819 instances have a root without data.
  - **Fix.** State the conjecture exactly as `TriangleBaseConj`: "If J is 3-connected, then every r ∈ N(z) for which data exist has some data (w, M0) and a Lovász decomposition of M satisfying (2.1)." Optionally restrict to J[N(z) − r] having a near-perfect matching by edges of J.
  - Then l. 131–132 needs "at every root r ∈ N(z)".
- **F2 (ERROR, Remark 2.2 l. 114–115; abstract l. 32–33).**
  - Replace "Neither base condition obviously implies the other, since the auxiliary graphs differ" with something like: "For r = y1, w = x3 and M0 = {x1y2, x2y3}, the graph M is the base graph of t6-dense Def. 2.1, and (E7), (E5) are disjuncts of (2.1). So every (E1)–(E5)+(E7) base is a triangle base at y1. No implication is known for the (E6) branch or for roots y2, y3."
  - Cite the Lean (`A28Check.lean`'s `triangleBase_of_E5_E7` can be added to `DirectTest1.lean`).
  - Credit t6-dense for the base graph and the append mechanism: Theorem 2.1 at m = 3 is Thm 2.2 there without the reinsertion of z.
  - In the abstract, say "drops (E1)–(E4) and weakens (E5), (E7) to disjunctions" instead of "replaces".
  - Align synthesis §24 and ROADMAP l. 601 ("weaker", "sharper") with this precise statement.
- **F3 (framing; abstract l. 28–31, Remark 2.2).**
  - State the converse (§2.2) as a proposition: for fixed data, triangle base ⇔ a (T1) decomposition at r in which every edge of M0 is terminal.
  - Present Conjecture 2.4 as "(T1) with a terminal matching of N(z) − {r, w}", a strengthening of (T1) of PTM type.
  - Mention that in all computed instances it fails exactly where (T1) fails.
- **F4 (OVERCLAIM, l. 132–133).**
  - "With the spine reduction, this covers the two-end half of Gallai's conjecture in that range" should go. The spine (MR Thm 114, `gallai_iff_spineTests'`) needs Test1 *and* Test2 for *all* 3-connected J. A subclass of Test1 instances is not a "half of Gallai in a range": the class is not closed under the reduction, and it misses about 20% of the order-9 instances.
  - Replace with: "Conjecture 2.4 implies Test1 J z for every 3-connected J in which every root admits data (Lean `test1_of_triangleBaseConj`)."
- **F5 (data, l. 176 and the table).**
  - Replace "Nine individual queries exceeded the budget" with "for 9 data choices no orientation was decided within the budget (177 of 756 queries hit the budget, none was refuted); in each case another data choice at the same root succeeded".
  - Say that the 5 first-choice failures are budget-undecided.
  - Record the command `dtl.py ORACLE 1 30 11` and commit its log.
- **F6 (data, l. 177–178 and l. 161–164).**
  - The d(z) = 8 results are not in `scripts/out/`, only one budget `NO BASE` line. Either commit the d = 8 run log and statistics, or drop the sentence. The recheck at 30M now finds a base for that root.
  - Mention or remove the K2-residual run (`dtl_resid.py`, two roots still undecided at 30M) and commit its input file.
  - Add a check that the oracle's D0 is a Lovász decomposition of M satisfying (2.1). As written, "base found" is not independently verified. The auditor's order-9 run does this for 10,118 witnesses; consider citing it.
- **F7 (GAP, Example 3.1 l. 144).** "Since t1 is a leaf at b, no path joins t1 to b" is false. Write instead: "if t1 and b were the ends of one path, it would be the edge t1b, and the other path would contain the 4-cycle".
- **F8 (nit, l. 104–105).** Add the missing clause: "an end created by an append is u_j, which is never a v_l, so each end is extended at most once; and the end at v_i is not moved by earlier appends because the pairs are disjoint".
- **F9 (pointers).**
  - Lean docstrings L. 38, 309, 831 cite "Conjecture 3.1" and "the remark after it". The PDF has Conjecture 2.4 and an unnumbered paragraph. Either give the conjecture its own section, so that it becomes 3.1 and the guard and evidence become 4 and 5 as in the brief, or fix the docstrings.
  - Add Lean pointers to the note: `test1At_of_triangleBase` for Thm 2.1; `triM_parity`/`triM_size` for Lemma 1.2; `TriangleBaseConj`/`test1_of_triangleBaseConj` for the conjecture and l. 131–132.
  - In Remark 2.2, cite `test1_of_lovaszBases` (the base on M) rather than `test1_of_appendBases`.

## 6. Optional suggestions

- **O1.** Note in Thm 2.1 that only d(r) ≥ 3 is used, as in the Lean (`hr3`), and that m = 1 is allowed.
- **O2.** Remark 2.3's "peeling" (l. 121–123) is informal. After peeling a maximal matching of size s < m − 1, z is even again with 2(m − s) − 1 unmatched odd neighbours plus r, and no theorem here applies. Either mark it as a heuristic or drop it.
- **O3.** Measure the strengthening:
  - Look for 3-connected J where (T1) holds at r but no data choice has a terminal matching. None exist in my order-7 and order-9 runs.
  - Record whether the conjecture's "some data" can be strengthened to "the first data choice" or "all data". The note's column 5 hints at this, but those failures are budget artefacts.
- **O4.** Fold the auditor's Lean lemma `triangleBase_of_E5_E7` into `DirectTest1.lean`. It is about 90 lines, needs no new infrastructure, and has standard axioms.
- **O5.** Lemma 1.2, l. 71: delete "Disconnected M is handled componentwise", or move it to the existence statement of Lovász's theorem.

## 7. Status of the uncommitted rewrite (snapshot 18:06, not audited in full)

The working tree's `direct-test1.tex` (uncommitted, about 390 changed lines) and `TriangleBase.lean` (159820d plus uncommitted changes) already take up most of the fixes. Line numbers in this section ("w.l.") refer to the working-tree tex.

| Finding | Status in the rewrite |
|---|---|
| F1 | Adopted. The conjecture is restated as `TriangleBaseConj`, with the K_{3,4}+x1x2 example and the 354/1,819 count. |
| F2 | Adopted: the Remark is rewritten and the abstract says "keeps, on the same graph M, only two of the conditions". Not checked: whether synthesis §24 and ROADMAP l. 601 were aligned. |
| F3 | Adopted as "Proposition (the converse; audit A28)". **New slip, w.l. 147:** it reads "the 2k−2m+2 odd vertices". B has 2k − 2m odd vertices, and with "+2" the count gives 2k + 2 > 2k. Fix: "2k−2m". |
| F4 | Adopted ("reaches about 80%"). |
| F5 | Adopted. The command is recorded and the log is `scripts/out/run11_d6.log`. |
| F6 | Partly adopted. The d = 8 sentence is gone and the K2-residual run is in a table. But the table cells `\RESIDA`, `\RESIDK`, `\HEADTOHEAD` and `\RANDOMTB` are **unfilled placeholders** (w.l. 311, 313, 320, 326). The claim that `tb.py` verifies D0 was not checked here. |
| F7, F8 | Adopted. |
| F9 | Adopted. The conjecture has its own section, so it is Conjecture 3.1 again, matching the Lean docstrings and the brief. Lean pointers are added, and the Remark cites `test1_of_lovaszBases`. `triangleBase_of_E5_E7` is now at `TriangleBase.lean` l. 287. |
| O1, O2, O4, O5 | Adopted. |
| "In the order-9 dense cores the two bases coexist at every root and data choice (A28)" | **Overstates A28.** A28 checked 18 of the 28 dense cores (108 of 168 roots; §2.1). Write "in 18 of the 28 order-9 dense cores", or finish the run (a C version of the search would be faster). |

**Not audited (new content):**
- the exhaustive order ≤ 9 table over `one_even_{5,7,9}.g6` (κ = 1, 2, ≥ 3);
- the residual-family and head-to-head tables;
- §6, "Toward the conjecture": Props `triangleBase_of_packed`/`farApart`, `triangleBase_of_L1Star`, Conjecture DL (`DisjL1`), `triangleBase_of_disjL1_reach`;
- `TriangleBase.lean`;
- E29.

**Wording.** The abstract (w.l. 40–41), "it holds at every root of every 2-connected graph that admits the data", should say "of order at most 9". As written it reads as a general claim.

**Recommendation.** These need a follow-up audit (A28b) once they are committed.

## 8. Fixes applied (triangle-base session, after the audit)

| Finding | Status | Where |
|---|---|---|
| F1 Conjecture states that data exist | **Fixed.** The conjecture now matches `TriangleBaseConj`: "every root that admits data". The K_{3,4}+x1x2 example and the order-9 count are quoted. | tex §3 |
| F2 "the auxiliary graphs differ" | **Fixed.** Remark 2.3 states the coincidence of the base graphs at m = 3, r = y1, the (E7)-branch implication, credit to t6-dense, and what is new. `triangleBase_of_E5_E7` / `triangleBase_of_lovaszBase_E7` are folded into `TriangleBase.lean` (renamed helpers `PathDecomp.transport_eq`, `ends_eq_of_triples`, `avoid_of_triples`). The abstract says "keeps two of the conditions, each weakened to a disjunction". synthesis §24 and ROADMAP are aligned. | tex Rem 2.3; Lean; synthesis §24; ROADMAP |
| F3 Converse / framing | **Fixed.** Prop 2.2 (the auditor's proof) gives the equivalence with Test1 plus a terminal matching. The abstract and §3 present the conjecture as a PTM-type strengthening. The converse is paper-only (not in Lean). | tex Prop 2.2, abstract, §3 |
| F4 "half of Gallai" | **Fixed.** Now: "implies Test1 J z for every 3-connected J in which every root admits data (`test1_of_triangleBaseConj`)", with the ≈80% coverage. ROADMAP line corrected. | tex §3; ROADMAP |
| F5 budget count | **Fixed.** "177 of 756 queries hit the budget; none refuted; 9 data choices undecided". The 5 first-choice failures are called budget-undecided. The command is recorded; the log is `scripts/out/run11_d6.log`. | tex §6.1 |
| F6 d(z) = 8 / K2 run / D0 unverified | **Fixed.** The d(z) = 8 and K2-residual logs are committed (`out/run13_d8_partial.log`, `out/run_k2resid.log`), and their budget roots were rechecked (E29 (F)). `tb.py` verifies D0 itself (`check_base`). The auditor's 10,118 verified witnesses are cited. | tex §6; E29 |
| F7 guard sentence | **Fixed** as suggested. | tex Ex 5.1 |
| F8 "at most twice" | **Fixed.** The three uses of disjointness are spelled out. | tex Thm 2.1 proof |
| F9 pointers / numbering | **Fixed.** The conjecture has its own section, so it is now Conjecture 3.1, as in the Lean docstrings. The coordinator's forest lift, merged afterwards, became §4; the guard and the evidence are therefore Example 5.1 and §6, and §7 is "Toward the conjecture". Lean names are given in the statements. Remark 2.3 cites `LovaszBase` / `test1_of_lovaszBases`. | tex |
| O1 | **Done.** Thm 2.1 assumes only d(r) ≥ 3 and allows m = 1. | tex |
| O2 | **Done.** Peeling is marked as a heuristic. | tex Rem 2.4 |
| O3 | **Done.** Data: "some data" cannot be "all data" in 3-connected J (4 of 88,526 data choices at n = 9 have no base). "First data choice" holds at 36,779 of 36,781 roots. No (T1)-but-no-base instance exists in 2-connected J of order ≤ 9. | E29 (A), (B) |
| O4 | **Done.** | `TriangleBase.lean` |
| O5 | **Done.** The sentence is deleted. | tex Lemma 1.2 |
| Final hand-back (two points on the rewrite, §7) | **Fixed.** The converse proof now counts 2k − 2m odd vertices (it said 2k − 2m + 2). The coexistence of the two bases is stated for the 18 of 28 order-9 dense cores (108 of 168 roots) that were actually compared. | tex Prop 2.2, §6.4; E29 (E) |
