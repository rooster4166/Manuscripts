# Audit A37b: the material added to test2 since A37

**Auditor:** independent audit agent, 2026-11-28. **Scope:** the material added to
`manuscripts/test2/test2.tex` since audit A37 (`research/audit/A37-test2.md`), the new Lean file
`lean/GallaiLean/Test1AllOdd.lean`, and the new or changed scripts and data in `manuscripts/test2/`
(items 1 to 8 of the brief). My scripts and outputs are in `research/audit/A37b-scripts/`. I edited
no manuscript, Lean or `manuscripts/test2/scripts` file, and made no commit.

Conventions as in A37. Each finding is classified as ERROR (false statement or invalid proof), GAP
(missing argument), OVERCLAIM (stated more strongly than proved or computed), MINOR (wording, typos,
numbering) or OK. Line numbers refer to `test2.tex` at HEAD.

## 0. Version audited

| object | version |
|---|---|
| repository | `956f509` (branch `claude/test2`), working tree clean apart from my scripts directory |
| `test2.tex` | 843 lines, md5 `7be96e2f…` |
| `test2.pdf` | matches the source: `pdftotext` of the shipped PDF and of my own recompile are identical |
| `Test1AllOdd.lean` | md5 `e2511168…` |
| `allodd_dl.c`, `tb1_odd.py`, `t2.c`, `verify_t2.py`, `allodd_xcheck.py` | md5 `2ef4752c…`, `84ba98f4…`, `c426cf0f…`, `36dab7e6…`, `827c5ef5…` |

The draft compiles cleanly with `pdflatex`, with no undefined references and no overfull boxes.
The compiled numbering of the new items:
- §7 is "The all-odd twin for (T1)": Theorem 7.1 (`thm:oddlift`), Corollary 7.2 (`cor:oddmatch`), Example 7.3 (`ex:t1theta`).
- §8 is "The base conjecture": Conjectures 8.1 (`conj:base`), 8.2 (`conj:two`) and 8.3 (`conj:common`).

**My own tools** (none imports or copies the session's search code):
- `obase.c`: an exact decider for constrained Lovász decompositions. It answers whether some
  decomposition has the prescribed number of ends b(v) ∈ {0,1} at each vertex, with the path ending
  at each v avoiding a vertex set X_v, and with some end pairs forbidden. Every such constraint
  concerns one path only, so the failure memo is keyed on (remaining edges, ended set), which is
  complete. Pruning uses parity, "every component with an edge has an unended vertex", and the
  per-component degree bounds (proved valid in §6.2). An optional node budget answers "unknown".
- `ao_xcheck.py`: my own enumeration of the six constraint families (from the manuscript's
  definitions), decided by `obase` (a set holds iff some choice of one literal per clause holds) and
  optionally by my own CP-SAT model, with every witness checked.
- `oddbase_lib.py`, `ex_t1theta.py`, `tb1_repro.py`: all forest T-joins through the cycle space, all
  rootings, exact base decisions by `obase`, my own lift, and a (T1) check.
- `count_allodd.c`: my own filter and counter for the constraint sets.
- `allodd_dl_audit.c`: a copy of `allodd_dl.c` instrumented to validate independently every
  decomposition it records, and every set it strikes.
- `A37bCheck.lean`, `A37bW4.lean`, `A37bAxioms.lean`: the Lean checks.
- From A37 I reuse its auditor library `a37lib.py`: graph6 decoder, 3-connectivity, decomposition
  checker and CP-SAT path model.

---

## 1. §7, the all-odd twin for (T1) (lines 567–637)

### 1.1 Theorem 7.1 (the all-odd lift, l. 573–588): OK
Every step checks.
- **Parities.** In B = J − z the even vertices are exactly N(z), since z is the only even vertex of J.
  Φ has odd set N(z), so every vertex of H = B − E(Φ) is odd, and in particular no vertex of H is
  isolated.
- **Paths.** A Lovász decomposition D₀ of H has one end at every vertex, so it has (n − 1)/2 paths.
  Here n is odd, since J has n − 1 odd vertices.
- **Appending.** Lemma 4.4 applies, since every non-root ends exactly one path, and keeps |D₀| paths.
- **Ends at r.** r ∈ N(z) has odd Φ-degree, so r ∈ V(Φ). As a root it ends 1 + c(r) = 1 + d_Φ(r) ≥ 2
  paths; as a child, 1 − 1 + c(r) ≥ 2.

No connectivity or minimum-degree hypothesis is needed, and none is stated.

### 1.2 Corollary 7.2 (the matching case, l. 593–603): OK
Orienting each other pair by a true disjunct makes the parent the avoided vertex. With r's pair rooted
at r, condition (i) at a₀ is "r ∉ V(Q(a₀))". A matching has no siblings, so (ii) is void. M₀ is a
forest N(z)-join of B whose edges lie in B, and Theorem 7.1 applies.

### 1.3 "So at d(z) = 2m both spine tests reduce … to one fixed avoidance and m − 1 disjunctions" (l. 605–609): OVERCLAIM
- The (T2) half of the identification is correct: M = (J − z) − M₀ + zr, with no even vertex, and
  the conditions are the same.
- But both bases exist only where J[N(z)] has a perfect matching, and they are sufficient conditions,
  not equivalent ones. "Both spine tests reduce" drops the qualifier "at roots with matching data".
- The qualifier is substantial. At n ≤ 9, 8,112 of the 25,340 (T1) instances (32%) have no matching
  data (TONEDATA, reproduced in §7). For (T2) at n = 10 the shipped tier table has 196,802 of
  716,984 instances outside tier M.
- The status list (l. 787–789) words it correctly: "it would give both spine tests at every root with
  matching data". The same overclaim is in the abstract (§3).
- Fix: "At every root with matching data, both spine tests at d(z) = 2m follow, through their matching
  bases, from one fixed avoidance and m − 1 disjunctions …".

### 1.4 Example 7.3 (no all-odd base, l. 611–634): OK (hand proof re-derived; exhaustive check reproduced)
**Hand proof.** I re-derived it line by line; the setup and Case 1 are correct:
- **Setup.** J = K₃,₆ + h₂h₃ has degrees 6 (h₁) and 7, 7, 3, …, 3, so z = h₁ is the only even vertex.
  J is 3-connected (computed). In B each leaf has degree 2, so d_Φ(leaf) = 1. Then d_Φ(r) = 1, which
  forbids "r a child with c(r) ≥ 2", so r is the root of its component. "r joined to h₂" is no loss
  of generality, by the h₂ ↔ h₃ symmetry.
- **Case 1, h₂h₃ ∉ Φ.** The parities give |A| and |C| even.
  - H is the double star described, with the edge h₂h₃ kept.
  - A leaf a ∈ A − r has only the neighbour h₃ in H. By (i) its path avoids h₂, so it ends at h₃ or
    goes on to another leaf of A. By (ii) that leaf must be r.
  - h₃ ends one path, and r ends one path, so |A − r| ≤ 2. Hence |A| = 2 and |C| = 4.
  - The h₃–C star has ≥ 3 sibling leaves: 4 if it is rooted at h₃, 3 if at a leaf c₀. Their paths
    avoid h₃, so each ends at h₂ or goes h₂ → c₀. At most two fit, a contradiction. (Rooted at h₃,
    even only one fits.)

Case 2 checks as well:
- **Case 2, h₂h₃ ∈ Φ.** |A| and |C| are odd, and H is the disjoint union of the stars h₂C and h₃A.
  - The tree Φ is rooted at r, so C consists of siblings, the children of h₃.
  - A Lovász decomposition of a star K₁,ₛ with s odd has one single edge and (s − 1)/2 leaf pairs.
    So (ii) forces |C| = 1, and then |A| = 5.
  - The star h₃A has three paths, one through r, and the four siblings A − r cannot be split among
    them without a sibling pair.

**Exhaustive check** (`ex_t1theta.py`, graph6 `H??F~z}`, z = 7):
- There are 64 T-joins (cycle-space dimension 6), and all 64 are forests.
- For each of the six leaves r there are 144 admissible rootings, all with r a root, and **0 bases**.
- The 144 also follows by hand: 2 · Σⱼ C(5, j) · (number of rootings) = 2 · 72.

The other claims of the example also check:
- (T1) holds at all six instances (CP-SAT witnesses, checked).
- At the cone over K₂,₆ (`ex_cone_k26.out`) the converse claim checks:
  - at r a hub, no base with r a root (0 of 128 rootings) and 180 bases with r a child (of 300);
  - at r a leaf, bases with r a root exist.
- The cited direct-test1 example ("the forest base can fail", `ex:forestfail`) is indeed the cone over
  K₂,₆ at a hub.

### 1.5 The (T1) data paragraph (\TONEDATA, l. 36–42 and 636–637): OK; one MINOR
I reproduced it independently in full (`tb1_repro.py`), not only at orders 7 and 9 as asked. My
filter, matchings, T-joins, exact decider and lift are all my own. Every base found is lifted and
checked as a (T1) decomposition.

| order | graphs | instances | with matching data | tier M | tier S (r a root) | tier C (r a child) | none |
|---|---|---|---|---|---|---|---|
| 5 | 1 | 4 | 4 | 4 | 0 | 0 | 0 |
| 7 | 28 | 126 | 88 | 88 | 38 | 0 | 0 |
| 9 | 5,231 | 25,210 | 17,136 | 17,136 | 8,065 | 3 | 6 |

- This is identical to `data/tb1_odd_le9.txt`. The graph counts equal A8's (1 + 28 + 5,231), and the
  order-9 instances split as 13,000 + 10,914 + 1,296 = 25,210, as in A8.
- The macro's arithmetic adds up:
  - 17,228 = 4 + 88 + 17,136;
  - 8,112 = 25,340 − 17,228 = 8,103 + 3 + 6;
  - 8,103 = 38 + 8,065;
  - 24,782 + 552 = 25,334 = 25,340 − 6.
- **Tier C.** The three instances are `H??F~z~` at (z, r) = (8, 6) and (8, 7), which is isomorphic to
  the cone over K₂,₆ (both hubs), and `H?AFvx~` (6, 8), a relative. All three have a cycle space of
  dimension ≤ 6. My search therefore enumerated **every** forest T-join there: no base with r a root
  exists at these three. This is more than the manuscript claims.
- **The six "none" instances** are those of Example 7.3, decided exhaustively (cycle-space dimension 6).
- **MINOR (l. 41–42).** "r gets two ends in 24,782 cases and four in 552" describes the bases that
  `tb1_odd.py` happened to find, not the instances. My search finds 24,639 + 130 = 24,769 cases with
  two ends and 565 with four. Fix: "in the bases found".

`tb1_odd.py` itself (method): OK.
- Tiers M, S and C are as described.
- `rootings(..., nonroot=True)` requires d_Φ(r) ≥ 3 and a root ≠ r, which is exactly c(r) ≥ 2.
- Query C with masks {v, p(v)} encodes (i) and (ii), as checked in A37.
- `check_and_lift` checks the base, appends parents first, and verifies (T1): a path partition of
  J − z, at most (n − 1)/2 paths, at least two ends at r.
- The S and C searches are incomplete (spanning-tree joins, at most 50 rootings), but they are used
  only for positive claims. The "none" claim rests on the hand proof, now also checked exhaustively.

---

## 2. §8, the base conjectures (lines 639–728)

### 2.1 Conjecture 8.3 and "fixed ⇒ free and every mixed form; j = 1 is L₁" (l. 673–685): OK
- The fixed form, for every orientation, gives every mixed form. "Conjecture 8.2 is the mixed form with
  j = 2" checks: (a₁, b₁) = (x, c) fixed and (a, b) free.
- For j = 1, `lovasz_avoid_nonadj` needs no connectivity: it holds in any graph with no positive
  even-degree vertex, with c odd and a ≁ c.

### 2.2 "Both matching bases … are instances of one statement" / "are the mixed form …" (l. 670–671, 684–685): MINOR
Conjecture 8.3 assumes G **connected**. But H = (J − z) − M₀ and M need not be connected; even the
smallest instance is not. For the wheel W₄ with r a rim vertex, H = C₄ − M₀ is two disjoint edges.
The reduction is easy:
- an all-odd graph has no isolated vertex, so it decomposes into all-odd components;
- apply the conjecture in each component;
- a pair split between two components is satisfied automatically.

The manuscript states this reduction only in the status list (l. 788–789). Fix: move it to l. 684, or
drop "connected" from Conjecture 8.3, which is equivalent by the same remark.

### 2.3 "No exception" (l. 687–692): OK; one MINOR
- **The argument.** Let a, b be non-adjacent, in one component C, with every other vertex of C adjacent
  to both. Then a is adjacent to exactly C − {a, b}, so d(a) = |C| − 2. In an all-odd graph |C| is
  even, so d(a) is even, which is impossible. Non-adjacency is used, and it is a hypothesis of
  Conjecture 8.3, so the paragraph is correct.
- **MINOR.** The parenthesis "(Lean `UnivTwins`: a, b non-adjacent, and every other vertex of their
  component adjacent to both)" does not match the Lean definition.
  - `UnivTwins G a b := G.Reachable a b ∧ ∀ x ≠ a, b, Reachable a x → Adj a x ∧ Adj b x`
    (`TriangleBase.lean:186`) has **no** non-adjacency clause. In `DisjL1` non-adjacency is a
    separate hypothesis.
  - `univTwins_every_path` (`DLOne.lean:1247`) is the whole-graph form: every vertex other than a, b
    is adjacent to both. It is not the component form.
  - Fix: "(Lean `UnivTwins`, with the pairs non-adjacent as in `DisjL1`; connected form
    `univTwins_every_path`)".

### 2.4 The data paragraph and \ALLODDTEN (l. 43–47, 694–701): OK (counts exact; orders 6 and 8 reproduced in full; order 10 sampled)
- **Population and counts, independently and exactly** (`count_allodd.c`):

  | order | connected all-odd graphs | F2 | F3 | X2 | X3 | XF | XF2 |
  |---|---|---|---|---|---|---|---|
  | 6 | 13 | 107 | 12 | 428 | 96 | 428 | 72 |
  | 8 | 224 | 10,850 | 10,508 | 43,400 | 84,064 | 43,400 | 63,048 |
  | 10 | **32,851** | **5,142,487** | **12,848,069** | **20,569,948** | **102,784,552** | **20,569,948** | **77,088,414** |

  The order-10 sum is **239,003,418**. The structure checks too: X2 = XF = 4·F2 and X3 = 8·F3 by the
  orientation counts, and XF2 = 6·F3.
- **Orders 6 and 8, reproduced in full by my own decider.** Every one of the 1,143 and 255,270
  constraint sets holds (`ao6_own_all.out`, `ao8_own_all.out`; every witness checked). This includes
  Conjecture 8.2 at order 8 (XF, 43,400), which **closes A37's open item** (its pure-Python run timed out).
- **Order 10.** I did not rerun all 239M sets. Instead:
  - the instrumented copy of `allodd_dl.c` (§6.6) ran on three samples, every set struck by an
    independently validated decomposition:
    - the 100 graphs with the most constraint sets: 2,218,611 sets;
    - the 300 densest (m ≥ 32): 294,003 sets;
    - 300 random graphs: 2,169,603 sets;
  - independent re-decisions by `obase` and CP-SAT (§6.7).

  0 failures and 0 unknowns in all of them.
- The order-10 total of 239,003,418 "0 fail, 0 undecided" is a computation I sampled, not reproduced.
  The tester's logic makes a "fail 0" answer sound (§6.1).

### 2.5 Validation sentence (l. 699–701): OK, reproduced
- **Order 6, with `-A`.** My decider and allodd_dl give identical FAIL lists for **all six**
  families: X2 784/2,340; X3 675/1,560; F2 69/585; F3 27/195; XF 549/2,340; XF2 294/1,170. The
  authors' own route_ext cross-check (`allodd_xcheck.py`) reproduces "784, 675, 0 mismatches".
- **Order 8, with `-A`.**
  - Identical FAIL lists for X2 (**21,425** of 188,160), F2 (747 of 47,040) and XF (12,585 of 188,160).
  - The current allodd_dl's order-8 `-A` totals equal `data/allodd_dl_validation.txt`.
  - (F3 1,977/94,080, X3 120,633/752,640 and XF2 40,104/564,480 were run but not compared.)
- My CP-SAT model was itself validated in both directions: on every order-6 X2 and XF set with `-A`
  it finds 784 and 549 infeasible, with 0 disagreements.

### 2.6 New comparison-table rows (l. 714–715, 718–719): OK
"(T1) all-odd matching base: no even vertex; one fixed + DL(m − 1), no twin exception; open;
Conjecture 8.3" and the extended (T2) row are consistent with §§7–8.

### 2.7 Conjecture 8.1 and its equivalence paragraph (l. 641–652, the A37 GAP fix): OK
- The "Equivalently" clause is gone from the conjecture. The new paragraph restricts the equivalence
  to rootings of type (a) (r a root of Φ-degree 1) and (b) (r a child).
- For a root with d_Φ(r) ≥ 3 the paragraph states the stronger form. I checked the count: the lower
  bounds are c(u) at non-roots, c(u) + 1 at roots other than r, 1 off Φ, and c(r) + 2 at r. They sum
  to (|V(Φ)| − q) + (q − 1) + 2 + (|B| − |V(Φ)|) = n, so the reconstruction of Prop 4.6 applies and
  leaves 2 ends at r.

---

## 3. Abstract, summary table, status list

| place | claim | class |
|---|---|---|
| abstract l. 84–85 | all-odd twin for (T1), "also in Lean" | OK (§5) |
| abstract l. 85–86 | "Through their matching bases, both spine tests at d(z) = 2m **become** one fixed avoidance plus m − 1 disjunctions …" | **OVERCLAIM**, as §1.3: only at roots with matching data, and only as a sufficient condition. Fix: "… at every root with matching data, both spine tests follow from …" |
| abstract l. 86–88 | common base stated as a conjecture; no twin exception | OK (§2.3) |
| table l. 166–167 | all-odd lift and matching case: proved; Lean | OK |
| table l. 157–158 | "(T2) and slack witnesses verified" | OK (§4) |
| table l. 175–177 | Conjectures 8.1–8.3: no counterexample in the computed ranges | OK |
| status 2 (l. 772–773) | all-odd lift, Lean | OK |
| status 5 (l. 780–783) | "the (T1) all-odd base to order 9" | **MINOR**: the base is computed to order 9 and *fails* at six instances (Example 7.3). Say "(exists at every instance except the six of Example 7.3)". The rest of item 5 is accurately scoped: "Conjecture 8.2 to order 10", "Conjecture 8.3 with j ≤ 3 at order 10". |
| status 6 (l. 787–789) | Conjecture 8.3 "would give both spine tests at every root with matching data (applied to each component …)" | OK. This is the correct form of §1.3 and §2.2. For (T2), Theorem 4.5 also needs d_J(r) ≥ 3, which holds in a 3-connected J. |
| appendix l. 806–809 | new commands | OK (they run as given) |

---

## 4. Section 2 validation: slack witnesses (t2.c `-s`, verify_t2.py `--require-slack`): OK, reproduced in full

**Code review.**
- `t2.c -s` snapshots the solver stack after `solve(E, k−1)` succeeds. On success `solve` leaves all
  pushed paths on the stack: in the disconnected case it pops only on failure. The snapshot is
  printed after the (T2) witness, behind the token `S`.
- `verify_t2.py` is the trust anchor, and it is sound:
  - `check_partition` asserts that every listed sequence is a path of B = J − z (length ≥ 1, no
    repeated vertex, consecutive vertices adjacent, no edge twice) and that the paths cover E(B);
  - a slack witness must have ≤ n/2 − 1 paths and may only occur when slack = 1;
  - with `--require-slack`, a slack = 1 line without a witness is rejected;
  - the J-level checks (exactly two even vertices z and r, adjacent; degree fields) are unchanged.
- The population filter (3-connectivity) is not re-checked by the verifier, but A37 reproduced the
  counts with its own filter.

**Reproduction** (`t2_repro.out`, `t2_full10.log`). I ran `nauty-geng -q -C -d3 n | t2 -s |
verify_t2.py --require-slack` at n = 6, 8, the order-10 slice `0/40`, **and the whole of order 10**
(5.9 s for t2, 66 s for the verifier):

| n | instances | (T2) witnesses verified | slack witnesses verified | tight |
|---|---|---|---|---|
| 6 | 10 | 10 | 8 | 2 |
| 8 | 948 | 948 | 943 | 5 |
| 10, slice 0/40 | 17,450 | 17,450 | 17,450 | 0 |
| 10, all | 716,984 | 716,984 | 716,971 | 13 |

8 + 943 + 716,971 = **717,922**, as claimed at l. 202 and 222. The order-10 slice sums in
`data/t2_slack_witnesses.txt` also add up: 358,492 graphs, 716,984 instances, 716,971 slack, 13 tight.
The 20 tight instances carry no slack witness, and A37 certified them by edge counting. **The A37 GAP
(item 14) is closed.**

---

## 5. Lean: `Test1AllOdd.lean`

### 5.1 Build, forbidden constructs, axioms: OK
- `lake build GallaiLean.Test1AllOdd` is green. The module is also imported by `GallaiLean.lean`, and
  `lake env lean GallaiLean/Test1AllOdd.lean` recompiles the file from source with no error.
- No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `unsafe`, `opaque` or `extern`.
- `#print axioms` (`A37bAxioms.out`): `twoEnds_of_oddBase`, `test1At_of_oddBase`,
  `oddBase_of_matching`, `test1At_of_matchingOdd`, `even_delVert_iff_adj` and `append_forest_ends`
  depend on `[propext, Classical.choice, Quot.sound]`; `orientPairs_avoid` on `[propext, Quot.sound]`.
  This matches `data/axioms.txt`.

### 5.2 Faithfulness: OK
| manuscript | Lean | check |
|---|---|---|
| forest N(z)-join Φ of B, rooted; edges of B | `OddData.edge`, `children` (distinct children), `edges` (distinct edges), `parent_first` | the parent map is a rooted forest; acyclicity follows from distinct children plus parent-first order (A37 §2.3) |
| odd set of Φ = T | `tjoin`: count of Φ-edges at v ≡ [v ∈ T] (mod 2) | exact (edges duplicate-free) |
| r ∈ N(z); r a root or c(r) ≥ 2 | `r_mem`; `r_child`: r a child ⇒ #{p : parent p = r} ≥ 2 | exact |
| Lovász decomposition D₀ of H = B − E(Φ) | `PathDecomp (delList B (L.map pairEdge))` with `ends v = degree v % 2` for all v | exact |
| (i) p(v) ∉ V(Q₀(v)) | every path with an end at the child p.1 avoids p.2 | exact |
| (ii) Q₀(x) ≠ Q₀(y) for siblings | no path has ends at two distinct children with one parent | exact |
| "the even vertices of B are T" | `twoEnds_of_oddBase` hypothesis `hev` | exact |
| (T1) at (J, z, r) | `Test1At J z r`: ∀ z ~ r, ∃ D of J − z, size ≤ (|V| − 1)/2, ≥ 2 ends at r | I re-derived `Test1 J z ↔ (hz → ∀ r, z ~ r → Test1At J z r)` against the spine's `Test1` (`A37bCheck.lean`) |
| Theorem 7.1 hypotheses | `test1At_of_oddBase`: z the only even vertex (`hz`), T lists N(z) (`hT`), `OddBase (J − z) r T` | exact; no extra hypothesis |
| Corollary 7.2 | `test1At_of_matchingOdd`: `hnd` (disjoint pairs), `hcover` (they cover exactly N(z)), `hedge` (edges of J − z), `D₀`/`hD₀` (Lovász decomposition of H), `hfix` (r ∉ Q(a₀)), `hdisj : TriangleDisj D₀ L` | exact: `TriangleDisj` is "a ∉ Q(b) or b ∉ Q(a)" for every pair (`DirectTest1.lean:302`) |

- MINOR: Theorem 7.1 states "(n − 1)/2 paths with 1 − [r is a child] + c(r) ends at r".
  `twoEnds_of_oddBase` exports only "≤ |B|/2 paths and ≥ 2 ends". The exact count is inside the proof
  (`hDe` of `append_forest_ends`) but is not stated. That is harmless, since (T1) needs only ≥ 2.
- The new Lean docstrings cite the manuscript by labels (`thm:oddlift`, `cor:oddmatch`). This fixes
  A37 item 21 for the new file as well.

### 5.3 Non-vacuity, machine-checked: OK
All three instances below are checked with standard axioms (`A37bCheck.out`, `A37bW4.out`):

| instance | graph | data | Lovász decomposition D₀ | theorem that fires |
|---|---|---|---|---|
| r a root | B = C₄, T = all four vertices | Φ = {01, 23} as `[(1,0), (2,3)]` | [1 2], [3 0] | `twoEnds_of_oddBase` |
| r a **child** with two children | B on Fin 6, edges 01 02 03 04 25 13, T = [0,1,2,3] | `[(0,1), (2,0), (3,0)]` | [0 4], [2 5], [1 3] | `twoEnds_of_oddBase` |
| a genuine (T1) instance | wheel W₄ (hub z = 4), r = 0, a₀ = 1, other pair (2,3) | matching data | [1 2], [3 0] | `test1At_of_matchingOdd`, giving `Test1At W4 4 0` |

- In the r-a-child case, every field is proved by `decide`.
- A negative control shows `OddData` rejects r as a child with only one child.

So `OddData` and `OddBase` are satisfiable in both rooting types.

---

## 6. The exact all-odd tester `allodd_dl.c`

### 6.1 Is "fail 0, undecided 0" sound? Yes
- A set leaves the working list in only two ways:
  - it is struck in `record()` by a recorded decomposition that satisfies it;
  - it is moved to `left[]`, then printed and counted as FAIL or UNDEC.
- So "fail 0, undecided 0" means every set was struck by a recorded decomposition. Soundness
  therefore needs only two things: recorded decompositions are genuine Lovász decompositions, and the
  satisfied-literal mask `sat` is computed correctly.
- Both hold by reading the code:
  - `extend` grows simple paths (vertex mask) along edges still in R;
  - a path closes only at an unended vertex y ≠ x, and its edges are removed;
  - `record` runs only at n/2 paths with R = 0, when every vertex has ended exactly once;
  - `sat` sets [c|x] exactly when x is not on the path ending at c.
- Both are also confirmed by instrumentation (§6.6).
- Pruning and memo errors could only produce false FAILs, not false successes. They matter for the
  "no budget hit" claim and for the `-A` validations, which I reproduced (§2.5).

### 6.2 `feasible()` (l. 194–230): OK, every bound is a valid necessary condition
Write q = |C − ended|/2 for a component C of R. A path lies in one component and visits a vertex at
most once.
- **Parity.** An ended vertex has even degree in R (it is only passed through); an unended one has
  odd degree (one end plus passes). An unended vertex of degree 0 therefore fails parity.
- **Edge total.** |R| ≤ (remaining paths) · (n − 1).
- **Component with an edge.** It needs q ≥ 1 (un is even by parity).
- **Degree at an ended vertex.** d ≤ 2q, since each of the q paths of C passes it at most once.
- **Degree at an unended vertex.** d ≤ 1 + 2(q − 1) = 2q − 1, since its own path ends there and
  does not pass it.
- **Component edges.** e(C) ≤ q(|C| − 1).
- **Total.** Σq = remaining paths, which is implied by parity: unended = n − 2(np + 1).

### 6.3 Failure memo key (l. 108–123, 141–165, 272–287): OK, complete
- Below a node, the completions are the decompositions of R whose ends are exactly the unended
  vertices.
- For a literal [c|x] with c ended, the value is already fixed. For c unended, it depends only on the
  completion.
- So target satisfiability is a function of (R, ended, the values of the decided literals). The key
  `ended | lit_status << 16` encodes exactly this, since "decided" is c ∈ ended and the bit gives the
  value.
- The search below a node is also a function of the key: the choice of x, `forced_avoid` and
  `target_violated` read only ended and endS of decided literals.
- A failure is stored only if the subtree was exhausted: not aborted, nothing recorded, target unchanged.
- The hash has no false positives, since it requires an exact (R, key) match. Linear probing with
  no deletion is correct.
- The memo is reset per orientation (`memo_reset` in the orientation loop), as it must be, since the
  target changes.

### 6.4 `forced_avoid` (l. 124–140): OK
- If every other literal of a clause containing [s|x] is decided false, then Q(s), the path now grown
  from s, must avoid x.
- Skipping x in `extend` also forbids closing at x, which is correct: Q(s) may not contain x at all.
- With fixed orientations every clause is a single literal, so this is exactly "Q(s) avoids X_s".
- `cur_avoid` is saved and restored around the recursive `dfs`.

### 6.5 Orientation search for free sets (l. 375–413): OK
- A set of OR-clauses holds iff some choice of one literal per clause holds, and the program tries
  them all (`norient = Π nl[j]`).
- FAIL is reported only if every orientation was exhausted without abort. UNDEC is reported if any
  orientation aborted and none succeeded.
- When one succeeds, the `record()` call that found it also strikes `sets[0]`, since the oriented
  literals lie in the set's clauses.

### 6.6 Set enumeration (F2, F3, X2, X3, XF, XF2) and instrumentation: OK
- **Enumeration.**
  - Pairs: unordered non-adjacent pairs a < b; with `-A`, all pairs.
  - Pairs of pairs, and triples, must be vertex-disjoint.
  - Per pair of pairs: F2 1, X2 4, XF 4. Per triple: F3 1, X3 8, XF2 6.
  - My independent counts agree exactly at orders 6, 8 and 10 (§2.4), and the FAIL **sets**, keyed by
    clause content, agree exactly (§2.5). So the families are what the manuscript says.
- **Instrumentation.** `allodd_dl_audit.c` is a copy that stores each path's edge mask.
  - In every `record()` it checks independently: n/2 paths; each a simple path from u to v whose
    vertex set is `pathsS`; edge-disjoint; covering E; one end per vertex.
  - It recomputes `sat` from the validated paths and aborts on any mismatch.
  - It re-checks every struck set against the recomputed `sat`.
- **Instrumented runs** (every set struck, 0 fail, 0 undecided, no abort):

  | run | decompositions validated | struck sets re-checked |
  |---|---|---|
  | order 6 | 83 | 1,143 (all) |
  | order 8 | 4,587 | 255,270 (all) |
  | order 10, 100 heaviest graphs | 1,441 | 2,218,611 |
  | order 10, 300 densest graphs | 15,031 | 294,003 (21.6 min) |
  | order 10, 300 random graphs | 13,231 | 2,169,603 |

### 6.7 Independent re-decision at order 10: OK
- **obase.** On the 300 random graphs, 40 random sets per graph across all families: **12,000 / 12,000
  hold**, every witness checked. On 150 of the dense graphs (m ≥ 32), up to 40 per graph: **5,938 / 5,938 hold** (F2 262, F3 244, X2 1,047, X3 1,892, XF 1,045, XF2 1,448), with no budget hit (`OB_SMALL=200000`, `OBASE_BUDGET=20000000`).
- **CP-SAT plus obase.** On 40 graphs (20 dense, 20 random), 6 sets per graph: **240 / 240 hold by
  both**. On 60 more dense graphs, 5 per graph: **300 / 300 hold by both** (F2 9, F3 6, X2 67, X3 94,
  XF 49, XF2 75). That is 540 CP-SAT decisions in all, every witness checked. The CP-SAT model was
  validated to refute as well (§2.5).

### 6.8 Code MINORs (no effect on any claim at n ≤ 10)
- **The header says "n <= 12", which is false.** The literal mask `B(c, x) = 1 << (12c + x)` is
  128-bit and overflows for c ≥ 10 once 12c + x ≥ 128. The edge mask R is 64-bit, while n = 12 allows
  m = 66 (`1ULL << m` is undefined for m ≥ 64). The program is correct for n ≤ 10 (indices ≤ 117,
  m ≤ 45), which is the whole claimed range.
- **`left[200000]`.** Unsatisfied sets beyond 200,000 per graph are dropped from the counts. The first
  200,000 are still counted, so "fail 0" stays sound, but a failure count could be understated.
- **Stale numbering.** "(Conjecture 7.2)" appears in the `allodd_dl.c` header, `README.md` (table
  row of `allodd_pairs.py`) and `research/experiments.md` E34. It is now Conjecture 8.2.

---

## 7. `tb1_odd.py` and `data/tb1_odd_le9.txt`
See §1.5: the method is OK. Orders 5, 7 and 9 are reproduced **in full** and independently, with
identical tier counts. The three tier-C instances are identified and confirmed exhaustively to have
no base with r a root. The \TONEDATA arithmetic adds up. One MINOR: the end counts depend on the
search order.

---

## 8. The A37 fixes

| A37 item | status at HEAD |
|---|---|
| 2: Prop 3.2 pointer "last paragraph" | fixed (l. 274–275 quotes the OSB sentence) |
| 3: Cor 3.3 proof; missing bibitems; "originals not accessible" | fixed: proof l. 296–301 (checked); BBB, BS, BSCL, FHZ, JM, MR, OSB added; l. 284–286 now separates Pyber/Fan (not accessible) from BBB/BSCL (read on arXiv); BP Question 1.1 cited (l. 280). **Still open (MINOR):** direct-test1, eulerian-cone, the trn and multi-token sessions, and Chu–Fan–Zhou (l. 125, new text) are cited by name with no bibliography entry |
| 4: Lemma 4.2 Lean attribution | fixed (l. 321–322) |
| 6: Prop 4.6 wording; case (b) automatic | fixed (l. 409, 411–413) |
| 7: Conj 7.1 "Equivalently" (GAP) | fixed (l. 641–652; §2.7 above) |
| 10: DL overclaim; "same data condition" | fixed: abstract l. 77–80, table l. 168, §5 l. 504–520, status l. 770; the twin examples are cited with A37 |
| 11: Prop 6.1 proof | fixed (l. 529–532) |
| 12: packed paragraph (undefined y; m ≥ 3 vs d(z) = 4) | fixed (l. 555–565: "packed" defined, y introduced, "Even at m = 2 …"; `coverage.py` honestly marked as not reproduced) |
| 14: slack answers unwitnessed (GAP) | **fixed and reproduced in full** (§4) |
| 15: reason for ≤ d_H(r) + 2 ends | fixed (l. 234–237; the computation checks) |
| 16: connectivity remark | fixed (l. 247–248) |
| 17: abstract "tight exactly at semi-cliques" | fixed (l. 94–96) |
| 18: README stale | fixed (README now lists the new files); its "Conjecture 7.2" is stale (§6.8) |
| 21: Lean docstring numbering | fixed (`Test2Lift.lean`, `Test2Converse.lean` now cite LaTeX labels) |
| (f): `dz4_cover.py` docstring | fixed (FAR answers declared not cross-checked) |
| A37 "not reproduced": Conjecture 7.2 at order 8 | **now reproduced** by A37b with my own decider (§2.4) |
| A37 "not reproduced": `coverage.py`, order-12 sample, full order-10 base search | still not reproduced (not in this brief); the manuscript labels `coverage.py` as such |

The new framing paragraph (l. 121–132) and abstract l. 60–63 cite A8. I checked the numbers against
`A8-marked-deletion-tests.md`: T(6)-ii is Thm 123, T(8)-ii is Thm 128 (conditional on FHZ for two
shapes and on the unchecked CFZ Lemma 2.1), and A8 lists 771,972 instances at |J| = 10 and 17,521
random instances at order 12. They agree.

---

## 9. Proved / computed / claimed

**Proved (paper, checked here):**
- Theorem 7.1 and Corollary 7.2;
- Example 7.3 (no all-odd base at K₃,₆ + h₂h₃ with r a leaf);
- "fixed ⇒ free ⇒ mixed";
- "no universal twins in all-odd graphs";
- the identification of both matching bases with the mixed form of Conjecture 8.3, given the
  component reduction (§2.2).

**Proved in Lean (checked):** `twoEnds_of_oddBase`, `test1At_of_oddBase`, `oddBase_of_matching`,
`test1At_of_matchingOdd`. They are faithful to Theorem 7.1 and Corollary 7.2 and non-vacuous (three
concrete instances), with standard axioms.

**Computed, and reproduced by me with independent code:**
- slack witnesses at n ≤ 10, in full (717,922);
- the (T1) all-odd base data at n = 5, 7, 9, in full;
- Example 7.3, exhaustively;
- all constraint-set counts at n = 6, 8, 10;
- Conjecture 8.3 (j = 2, 3, all families) at n = 6 and 8, in full;
- the `-A` validations at n = 6 (all six families) and n = 8 (X2, F2, XF).

**Computed by the session, and sampled by me:** Conjecture 8.3 at n = 10, j ≤ 3, 239,003,418 sets.
My samples:
- 4.68M sets re-checked through the instrumented tester;
- 12,000 random-graph sets and 5,938 dense-graph sets decided by my own code;
- 540 sets decided by CP-SAT.

There were no failures. The tester's logic makes a "fail 0" answer sound.

**Claimed only:** nothing in the new material rests on an unverified claim. j ≥ 4, and any order
> 10, are untested, and the manuscript does not claim otherwise.

## 10. Summary table

| # | Item | Location | Class | Fix |
|---|---|---|---|---|
| 1 | Theorem 7.1 (all-odd lift) | l. 573–588 | OK | — |
| 2 | Corollary 7.2 (matching case) | l. 593–603 | OK | — |
| 3 | "both spine tests reduce/become … one fixed avoidance and m − 1 disjunctions": no "at roots with matching data", and sufficiency only | l. 605–609; abstract l. 85–86 | OVERCLAIM | add "at every root with matching data … follow from" |
| 4 | Example 7.3: hand proof re-derived; exhaustive check (64 forests, 144 rootings per r, 0 bases); (T1) holds; cone over K₂,₆ converse | l. 611–634 | OK | — |
| 5 | \TONEDATA: tiers reproduced in full at n = 5, 7, 9; arithmetic OK; tier C identified (cone over K₂,₆ ×2, `H?AFvx~`) and exhaustive | l. 36–42, 636–637 | OK | — |
| 6 | "r gets two ends in 24,782 … four in 552" is search-dependent (mine: 24,769 / 565) | l. 41–42 | MINOR | "in the bases found" |
| 7 | Conj 8.3 statement; fixed ⇒ free/mixed; Conj 8.2 = mixed j = 2; j = 1 is L₁ | l. 673–685 | OK | — |
| 8 | the matching-base graphs need not be connected (already W₄); component reduction only in status 6 | l. 670–671, 684–685 | MINOR | move the component remark to l. 684 |
| 9 | "No exception" argument | l. 687–692 | OK | — |
| 10 | Lean `UnivTwins` has no non-adjacency clause; `univTwins_every_path` is the whole-graph form | l. 688–689 | MINOR | reword the parenthesis |
| 11 | \ALLODDTEN counts (32,851 graphs; 239,003,418 sets, by family) | l. 43–47, 694–699 | OK (exact) | — |
| 12 | 0 failures at n = 6, 8 (all 1,143 + 255,270 sets, own decider); n = 10 sampled (4.68M instrumented, 12,000 + 5,938 own, 540 CP-SAT) | data | OK | — |
| 13 | `-A` validation vs route_ext: n = 6 (all families) and n = 8 (X2, F2, XF), identical FAIL sets | l. 699–701 | OK | — |
| 14 | new comparison-table rows | l. 714–719 | OK | — |
| 15 | Conj 8.1 equivalence paragraph (A37 GAP fix) | l. 647–652 | OK | — |
| 16 | status 5 "the (T1) all-odd base to order 9" (it fails at six instances) | l. 783 | MINOR | add the exception |
| 17 | slack witnesses: code review; full reproduction at n ≤ 10 (717,922) | l. 197–203, 222–223 | OK | — |
| 18 | Lean build; no sorry/axiom/native_decide; axioms standard | `Test1AllOdd.lean` | OK | — |
| 19 | Lean faithfulness (`OddData`, `OddBase`, `Test1At`, `TriangleDisj`, hypothesis lists); non-vacuous (root, child, W₄) | `Test1AllOdd.lean` | OK | — |
| 20 | Thm 7.1's exact end count not exported by Lean (only ≥ 2) | `twoEnds_of_oddBase` | MINOR | optional |
| 21 | `allodd_dl.c` soundness: "fail 0" sound; `feasible` valid; memo key complete; `forced_avoid` and orientation search correct; families as stated | script | OK | — |
| 22 | `allodd_dl.c` header "n ≤ 12" false (u128/u64 overflow at n = 12); `left[200000]` cap | script | MINOR | "n ≤ 10"; enlarge or count the overflow |
| 23 | stale "Conjecture 7.2" (`allodd_dl.c`, README, experiments E34) | scripts/docs | MINOR | 8.2 |
| 24 | A37 fixes applied (all listed items) | various | OK | — |
| 25 | names cited without a bibliography entry: direct-test1, eulerian-cone, trn/multi-token sessions, Chu–Fan–Zhou | l. 125, passim | MINOR (open from A37 item 3) | add entries |

No ERROR and no GAP was found in the new material. There is one OVERCLAIM, in the abstract and §7
(item 3), and several MINOR items.

## 11. Verdict

- **Item 1 (§7: Theorem 7.1, Corollary 7.2, Example 7.3, data): sound.** The proofs are correct.
  The example is correct by hand and confirmed exhaustively. The data are reproduced in full by
  independent code. To fix: the "reduce/become" overclaim (item 3), here and in the abstract.
- **Item 2 (§8: Conjecture 8.3, "No exception", data, table): sound.** The component reduction should
  sit next to the "instances" claim (item 8), and the UnivTwins parenthesis needs rewording (item 10).
- **Item 3 (abstract, table, status): pass with fixes.** Items 3 and 16.
- **Item 4 (slack witnesses): PASS.** Reproduced in full at n ≤ 10; the A37 GAP is closed.
- **Item 5 (Lean): PASS.** Green, standard axioms, faithful, and non-vacuous in both rooting types and
  on a genuine (T1) instance.
- **Item 6 (`allodd_dl.c`): PASS.** "fail 0" is sound by construction and by instrumentation. Every
  pruning rule and the memo key are valid. The FAIL lists agree exactly with an independent decider on
  every set at order 6 and on X2, F2 and XF at order 8, and order-10 samples confirm the totals.
- **Item 7 (`tb1_odd.py`): PASS.** Reproduced in full at n ≤ 9.
- **Item 8 (A37 fixes): applied.** Only the bibliography for internal manuscripts remains open
  (MINOR).

## 12. Reproduction (from `research/audit/A37b-scripts/`)

    gcc -O2 -o obase obase.c; gcc -O2 -o count_allodd count_allodd.c
    gcc -O2 -o t2 ../../../manuscripts/test2/scripts/t2.c
    gcc -O2 -o allodd_dl ../../../manuscripts/test2/scripts/allodd_dl.c
    gcc -O2 -o allodd_dl_audit allodd_dl_audit.c
    gcc -O2 -o route_ext ../../../tools/route_ext.c
    ./t2_repro.sh; ./t2_full10.sh                                    # §4
    python3 ex_t1theta.py 'H??F~z}' 7; python3 ex_t1theta.py "$(cat cone_k26.g6)"   # §1.4
    for n in 5 7; do nauty-geng -q -c -d3 $n | python3 tb1_repro.py 30; done        # §1.5
    python3 tb1_repro.py 16 < t1_order9.g6
    nauty-geng -q -c 10 | ./count_allodd > allodd10.txt                             # §2.4
    nauty-geng -q -c 8 | ./allodd_dl_audit -d 0                                     # §6.6
    ./allodd_dl_audit -d 0 -b 50000000 < ao10_heavy100.g6   (also ao10_dense300, ao10_rand300)
    python3 ao_xcheck.py compare F2,F3,X2,X3,XF,XF2 ao8.g6 empty.fail               # §2.4
    ./allodd_dl -A -d 0 < ao6.g6 > ao6_A.out; python3 ao_xcheck.py compare F2,F3,X2,X3,XF,XF2 ao6.g6 ao6_A.out adj
    gunzip -k ao8_A.out.gz; python3 ao_xcheck.py compare X2,F2,XF ao8.g6 ao8_A.out adj   # §2.5
    python3 ../../../manuscripts/test2/scripts/allodd_xcheck.py X2 ao6.g6 ao6_A.out  # authors' check
    python3 cp_validate6.py                                                         # CP-SAT model check
    python3 ao_xcheck.py sample F2,F3,X2,X3,XF,XF2 ao10_rand300.g6 40 303           # §6.7
    OB_SMALL=200000 OBASE_BUDGET=20000000 python3 ao_xcheck.py sample F2,F3,X2,X3,XF,XF2 ao10_dense150.g6 40 101
    python3 ao_xcheck.py sample F2,F3,X2,X3,XF,XF2 ao10_cp40.g6 6 202 cpsat
    cd ../../../lean && lake env lean ../research/audit/A37b-scripts/A37bCheck.lean # §5 (also A37bW4, A37bAxioms)

Binaries are not kept; build them as above. `obase.c` was strengthened during the audit (degree
bounds, a constrained start vertex, an optional node budget). Every version is an exact decider. The
final version reproduces the order-6 `-A` FAIL lists (`ao6_A_compare_final.out`), and
`ex_t1theta.out`, `ex_cone_k26.out` and `tb1_repro_*.out` were regenerated with it.
`ao8_own_all.out` came from the first version (parity and component pruning only); it is exact, only
slower.

Large outputs were deleted after checking: the full order-10 `t2 -s` output had 716,984 lines (md5
`c970ffd6432d…`) and is regenerated in about 6 s. `ao8_A.out` is kept gzipped.
