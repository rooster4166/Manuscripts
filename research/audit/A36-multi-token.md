# A36. Audit of multi-token: k-token steering, `MultiToken.lean`, the schedule data

Date: 2026-11-28. Adversarial referee. Grades: **SOUND**, **GAP** (fixable, claim not justified as
written), **ERROR** (false as stated), **NIT** (wording, citation, bookkeeping).

**Version.** Branch `claude/multi-token`, commit 2afae07.
- The author kept working in the same tree during the audit. These changes are **not audited**:
  - new untracked files: `lean/GallaiLean/MultiTokenObstruct.lean`, `data/runs/*_undec_open*.txt` and,
    briefly, `resid_O10_undec_EK2K3_seed{7,11}.txt`;
  - `data/runs/resid_O10_undec_EK2K3.txt` deleted from the working tree.
- The branch also moved during the audit, from 2afae07 to b8b15a3 (9914d37 … b8b15a3, below). Commits
  4e9b5bb and b8b15a3 are the other session's interim snapshots of this report; I committed nothing.
- So I audited a clean `git archive 2afae07` export in my scratch directory. The Lean build and
  axiom check ran in the live tree, where `MultiToken.lean` and `DirectTest1.lean` are byte-identical
  to the commit.

| file | lines | md5 |
|---|---|---|
| `manuscripts/multi-token/multi-token.tex` | 621 | `06feef412ce054f9853fc86bb4c449e5` |
| `manuscripts/multi-token/multi-token.pdf` (9 pp.; text identical to my recompilation) | | `97686066449f8f185e67901911be27c8` |
| `manuscripts/multi-token/README.md` | 69 | `5381c9e36dd0a7d96b179c9f8a2a92bd` |
| `lean/GallaiLean/MultiToken.lean` | 851 | `192c6fcbad8b5d0bd3815bb8bbec8855` |
| `lean/GallaiLean/DirectTest1.lean` | 845 | `70c77764757c358710cafbf6d2fa49c1` |
| `lean/README.md` | 993 | `5f598a2e9f70b8ef6677320788334cf7` |
| `scripts/mtok.cpp` / `mt_verify.py` / `pattern.py` | 246 / 259 / 136 | `46f42c50…` / `a4162e1c…` / `841c32f2…` |
| `scripts/firstmove.py` / `explore.py` / `mt_conj.py` / `filt.py` | 62 / 74 / 35 / 13 | `88d9f46a…` / `65a9ac25…` / `143c07b1…` / `940d89a3…` |
| `scripts/axioms_mt.lean` / `data/axioms.txt` | 13 / 11 | `b2fcbf2c…` / `e42982dc…` |
| `data/J7_d6.g6` / `J9_d6.g6` | 7 / 1,819 | `2a15d0cd…` / `7d2d5867…` |
| `data/resid_O8.g6` / `resid_O10.g6` / `e28_hard.g6` / `clt_hard.g6` | 30 / 24 / 8 / 1 | `a00e25e0…` / `0a6a8327…` / `178ca633…` / `b2d27907…` |
| `data/runs/` (41 files; md5 of the sorted md5 list) | | `c3f84654…` |
| `tools/route_ext.c` / `direct-test1/scripts/tb.py` / `t6-dense/scripts/gen_resid.py` | 272 / 391 / 125 | `a9d07031…` / `862b8e6b…` / `51948eee…` |

**Auditor files** (`research/audit/A36-scripts/`). None uses `mtok.cpp`, `mt_verify.py`, `pattern.py`,
`explore.py`, `firstmove.py`, `mt_conj.py` or `route_ext`, except where stated (`tamper.py`
deliberately drives `mt_verify.py`).
- `indep_mt.cpp`: my own schedule search, written from Definition 2.2.
  - Own graph6 parser and own enumeration of data choices; orientations all 2^k.
  - An exact visited set: the key is the whole edge set, with no hash shortcut. The state graph is
    acyclic, since every move lowers |E| by one.
  - Exhaustive for an instance without a schedule, and it reports the least potential Φ reached.
  - Variants: `SUPP`, `DROP`, `TERM=0/1/2`, `FIRSTONLY` (legal first moves), `PRINT` (SCHED lines in
    the authors' format), and a state cap.
- `agg_resid.py`: aggregates its output (the Proposition 6.1 check and the frozen/partial table).
- `cmp_roots.py`: per-root comparison with the authors' run files.
- `table3_prop61.py`: Table 3 per row from the authors' run files, with the roots that
  Proposition 6.1 settles.
- `thm42.py`: Theorem 4.2 from its hypotheses, written from the text.
  - It tries every (A, B) combination, labelling and orientation.
  - It includes `replay()`, an own legality checker for Definition 2.2 (end condition included) that
    replays each certificate.
- `thm42_leafroot.py`: an instance of Theorem 4.2 at a root of degree 1 (finding M2).
- `example33.py`: every fact stated in Example 3.3.
- `ex33_steerK.lean`: Example 3.3 as a concrete `SteerK` derivation, closed by kernel `decide`. It is
  fed to `triangleBase_of_steerK` and `test1At_of_steerK`.
- `axioms_extra.lean`: axioms of the bookkeeping lemmas that `axioms_mt.lean` omits.
- `tamper.py`, two modes:
  - `strict`: the committed `mt_verify.check`, with `verify_test1` wrapped so that its result is
    asserted (finding M4);
  - `tamper`: random corruptions, comparing `mt_verify`'s accept/reject decision with my `replay()`.
- `mt_indep.cpp`: my own test of Conjecture 6.2.
  - Own exact solver: backtracking over paths between odd vertices, failure memo, component pruning,
    and a re-check of every solution.
  - Own instance enumeration, also covering the shared-stem and shared-avoided-vertex instances
    that (TS) allows.
- `prop61_case.py`: finds the case that the proof of Proposition 6.1 mishandles (finding M3).

## Verdict per item

| item | verdict |
|---|---|
| Def 2.1 (tails, (TS), (TI), (TG)) | SOUND; `TailSys`, `TailInv`, `TailGood`, `OffTails`, `OneLive`, `SuppOK` are faithful |
| Def 2.2 (schedule) | SOUND. `SteerK`, `mtok.cpp`, `mt_verify.py` and my search are the same notion (per-instance sets identical at order 9) |
| Lemma 2.3 (Fan step, many even vertices) | SOUND |
| Lemma 2.4 (bookkeeping) | SOUND |
| Lemma 2.5 (three steps) | SOUND |
| Lemma 2.6 (multi-tail leaf lemma) | SOUND |
| Theorem 2.7 (transfer) | SOUND |
| Remark 2.8 (TRN Def 6.3 as a special case) | SOUND |
| Theorem 3.1, Corollary 3.2 | SOUND. NIT M14 (Lean exports only the "in particular") |
| Example 3.3 | SOUND: every fact checked, and built as a `SteerK` derivation in Lean. NIT M11 |
| Proposition 4.1 (potential) | SOUND. NIT M10 |
| Theorem 4.2 (certificate family) | Proof SOUND. **ERROR M2**: the "Test1 holds" clause needs d_J(r) ≥ 3, which is not assumed |
| 882 / 10,118 and 6 / 40 | SOUND; my implementation gives the same 882 roots |
| Remark 4.3 | SOUND (all "none" verdicts confirmed by exact search). NIT M5: Proposition 6.1 already proves it |
| §5 tools, executor | **GAP M4** (`verify_test1` result discarded); executor otherwise SOUND and independent; NIT M7 (tamper test) |
| Table 1 | SOUND, reproduced in full at orders 7 and 9 |
| Table 2 (ablation) | SOUND, all six rows reproduced |
| Table 3 | Numbers SOUND as search verdicts. **ERROR M1**: 34 of its "undecided" roots are proved unscheduled by Proposition 6.1 |
| §6 "What is left" bullets | SOUND except "39 and 21 undecided … E28 … 20 undecided" (ERROR M1); NIT M13 |
| Proposition 6.1 | Statement SOUND (0 violations in every test). **GAP M3** in the proof (suppression case) |
| Frozen / partial table, "42 of 53", "38 / 4" | SOUND, reproduced exactly; NIT M12 |
| Conjecture 6.2 and its test | Test SOUND as described. NIT M6 (scope; the k = 3 counts are ordered). The extended class also passes |
| Remark 6.3 | SOUND as an informal sketch; NIT M6 (it assumes distinct stems) |
| §7 Formalisation; build, `sorry`, axioms | SOUND: 18,426 jobs, no `sorry`, standard axioms (also for the lemmas not listed) |
| "What remains" | **ERROR M1** (item 1, last sentence) |
| Abstract and introduction | Numbers SOUND. NIT M8 (citations), M9 (scope labels) |
| README, Lean README | Numbers SOUND. GAP M4 ("including the Test1 lift") |

Two ERRORs, two GAPs. No ERROR touches the Lean-formalised core (Sections 2–3). M1 is an
inconsistency between the paper's own Proposition 6.1 and its residual statements. M2 is a missing
hypothesis in one theorem's conclusion.

## Findings

**M1 (ERROR). Proposition 6.1 settles 34 roots that Table 3 and §6 call "undecided". So "What remains"
item 1, "At |O| = 10 the shapes ∅, K2, K3 have no root proved unscheduled; whether every such root
has a schedule is open", is false.**
- *What.* Every root of degree n − 2 in a residual family satisfies the hypotheses of
  Proposition 6.1 (δ(J) ≥ 3, k = 2, one non-neighbour). So it has no schedule, whatever the search
  budget.
- *Count.* From the authors' own run files (`table3_prop61.py`), with no new search:

  | family, row | none / undecided in Table 3 | of the undecided, degree n − 2 | with Prop 6.1: none / undecided |
  |---|---|---|---|
  | `resid_O8` ∅ / K2 / P3 / K3 / C4 | 25/5, 15/6, 9/8, 10/12, 10/8 | 2, 3, 0, 1, 0 | 27/3, 18/3, 9/8, 11/11, 10/8 |
  | `resid_O10` ∅ / K2 / P3 / K3 / C4 (TW=2) | 0/1, 0/5, 1/5, 0/3, 7/2 | 1, 4, 4, 3, 2 | 1/0, 4/1, 5/1, 3/0, 9/0 |
  | `resid_O10` C4, \|O\| = 8 (TW=1) | 6/5 | 2 | 8/3 |
  | E28 hard graphs | 18/20 | 12 | 30/8 |

  Totals: |O| = 8 goes from 69 proved / 39 undecided to 75 / 33; |O| = 10 from 14 / 21 to 30 / 5;
  E28 from 18 / 20 to 30 / 8.
- *Examples.* `resid_O10` ∅: `O~~zLjn}jc^lnk]V\nCym` r = 2 has degree 15 = n − 2. K2:
  `O^~}vF|nXtJW}z~rZqN|d` r = 3, 4, `O^~}upm}feL}|huvxlunu` r = 1, `O^~||[y{vz~I~Ul\_U|QR` r = 2. K3:
  `OF~|]re]Wwl~j|vYnVR^g` r = 4, `OF~~F~l~u]NgzTnnyduJt` r = 5, `OF~}b||?Vszqke~{Qu}`w` r = 3.
- *The committed list.* The authors' own `data/runs/resid_O10_undec_EK2K3.txt` lists 9 undecided
  roots of these three shapes. Eight of them have degree n − 2. The ninth (`O^~}vF|nXtJW}z~rZqN|d`
  r = 5) is the only one Proposition 6.1 does not settle; the post-commit seed runs (not audited)
  find a schedule there.
- *No contradiction.* No root of degree n − 2 is scheduled anywhere: 0 of 42 in `resid_O8`, 18 in
  `resid_O10`, 24 in E28.
- *Fix.*
  - In Table 3, add a column "of which degree n − 2 (Prop 6.1)", or move these roots to "none" with a
    footnote.
  - Correct the §6 bullet ("75 and 30 proved, 33 and 5 undecided; E28: 30 proved, 8 undecided"),
    and the README.
  - Replace the last sentence of "What remains" item 1. At |O| = 10 every shape has roots without a
    schedule, by Proposition 6.1. For ∅ and K3 every root is now decided (23 + 1 and 21 + 3); K2 has
    one undecided root left in the committed data.
  - The frozen table may stay restricted to search-proved roots, but should say so.

**M2 (ERROR, one missing hypothesis). Theorem 4.2 concludes "and Test1 holds at (J, z, r)" without
assuming d_J(r) ≥ 3, and the hypotheses do not imply it.**
- *Where.* (A2) and (B1) force d_J(r) ≥ 3, but (A1) + (B2) do not.
- *Counterexample* (`thm42_leafroot.py`):
  - J = `Lsech?H?GA_B?@` (order 13, κ = 1; graph6 labels), z = 0, r = 1 with N(r) = {z}, w = 2,
    (y₁, x₁) = (4, 3), (y₂, x₂) = (6, 5). Then N(w) = {z, 5, 7} with 5 ≁ 7, N(y₁) = {z, 3, 8}, and
    N(8) = {4, 7, 9} with 7 ≁ 9 and 8 ≁ 6.
  - (A1) and (B2) hold, and the certificate S 2:5-7, 4 → 8, S 8:7-9, D(ℓ₁) is legal and terminal. It is
    checked by my `replay()`, and `pattern.py` reports this root covered with the same certificate.
  - So the triangle base holds. But r is isolated in J − z, so no decomposition of J − z has two
    ends at r, and Test1 fails.
- *Scope.* The proof flags the condition itself ("in general Corollary 3.2 needs it"), and every J
  in the paper's data is 3-connected, so no number changes.
- *Fix.* Add "d_J(r) ≥ 3 (e.g. J 3-connected)" before "and Test1 holds", or end the statement at
  "J has a triangle base at r". Optionally add the d(r) ≥ 3 filter to `pattern.py`, which lacks it
  (`mtok.cpp` and `explore.py` have it).

**M3 (GAP; the statement is true). The proof of Proposition 6.1 splits the suppression case
wrongly.**
- *Location.* "A suppression of a token p with N(p) = {a, b}: if p ∈ A, then p is isolated
  afterwards; otherwise p ∼ r, …". Then: "A used-up vertex is isolated or adjacent to r from then
  on, so it is never used again."
- *The problem.* A vertex p ∈ A can become adjacent to r before any entry: an earlier suppression
  with a = r, b = p adds rp. If p is later suppressed, the "p ∈ A" branch counts p as used up a
  second time, so "never used again" fails for the argument as written.
- *Not hypothetical* (`prop61_case.py`, first hit at order 9):
  - J = `HsaBEy~`, z = 7, r = 1, w = 3, pairs (y, x) = (8, 4), (0, 5), A = {2, 3, 4, 5, 8};
  - the legal sequence 8→6, D(ℓ₁), **S 6:1-2** (2 ∈ A becomes adjacent to r), 0→4, D(ℓ₂), 8→5, 0→2;
  - then **S 2:1-8**, a legal suppression of p = 2 ∈ A while p ∼ r. The corrected split uses up
    b = 8 ∈ A here;
  - the whole sequence is also legal under my independent `replay()`.
- *Fix.* Split on the current adjacency of p to r:
  - if p ≁ r now, then p ∈ A (no edge at r has been deleted before an entry), p is not isolated,
    and it becomes isolated;
  - if p ∼ r now, then r ∈ {a, b}, say a = r, and b ≁ r, b is not a leaf, b ≠ z, so b ∈ A. Also b
    is not isolated, and it becomes adjacent to r.

  In both cases the vertex used up was, just before, neither isolated nor adjacent to r, so the
  count R ≤ t and the rest of the proof go through.
- *Data check.* My exact search found 0 violations of the statement:
  - 1,597 roots (order 9, 3-connected) and 20 (order 7);
  - every one-even graph of order 9 with δ ≥ 3: 1,651 roots at d(z) = 6, and 230 at d(z) = 8 (k = 3);
  - 51 random roots at order 11 with d(z) = 10 (k = 4) and t = 3. At odd order t = n − 1 − d(r) is
    odd, so t = 3 < k needs k ≥ 4.

**M4 (GAP, computational claim). `mt_verify.py` never checks the Test1 lift.**
- *What.* Line 242 calls `verify_test1(J, z, r, paths)` and discards its result. `tb.verify_test1`
  asserts only that the paths partition E(J − z). The Test1 conditions are its boolean return value,
  `len(paths) <= (n-1)//2 and ends[r] >= 2`. Every other caller in the repository tests it
  (`tb.py:231`, `fb_nodata.py:178`, `fb_exhaustive.py:76`).
- *So these are not justified as written:*
  - §5 "finally lifts it to a Test1 decomposition … with … verify_test1";
  - README "executed and checked independently, including the Test1 lift";
  - the Test1 part of "verified 76474 / 882 / 130 …".
- *The results are still right.* `tamper.py strict` asserts the result inside the committed
  executor. It verifies all 76,474 order-9 schedules found by **my** search (the same instance set as
  the authors', below) and all 130 at order 7, including the Test1 size and ends. This is also
  guaranteed by [DT, Thm 2.1] whenever d(r) ≥ 3.
- *Fix.* `assert verify_test1(J, z, r, paths), 'Test1 lift fails'`, then rerun the verify logs.
- *Minor.* The leaf-deletion assertion just above has an operator-precedence slip
  (`A and B or C`). It is harmless, because `check_parity(M, D0, …)` follows.

**M5 (NIT, could be stronger). Remark 4.3 and the abstract's "no structural condition covering a
whole dense residual shape" rest on computation, "valid up to the correctness of the search
(128-bit hash)".**
- *Proposition 6.1 already proves it.* Every shape of `resid_O8` has roots of degree n − 2 (15, 10,
  5, 9 and 3 of them), and so does every row of `resid_O10`.
- *The hash.* My exact search (no hashing) confirms every "none" verdict: 23 / 2,589 / 69 / 14 /
  18 / 6.
- *Fix.* Cite Proposition 6.1 in Remark 4.3. That turns it into a theorem for both |O| = 8 and
  |O| = 10, and the hash caveat can go.

**M6 (NIT, scope of the MT test).**
- *Conjecture 6.2 is broader than the test.* The conjecture is stated under (TS) and (TI). (TS)
  allows two tails with the same stem, and two tails with the same avoided vertex. `mt_conj.py`
  tests only distinct stems and distinct avoided vertices, and the text says so.
- *My extension passes.* `mt_indep.cpp` covers everything (TS) allows and finds 0 failures:
  - two tails, connected G with n ≤ 8: 37,707 instances, 18,849 of them with sharing;
  - three tails, n ≤ 7: 61 / 4,982 / 12,170 instances at n = 5 / 6 / 7.
- *The authors' class, reproduced* with my own solver: 1, 29, 113, 6,502 and 18,858 instances for
  n = 4, …, 8, and 92 and 1,026 for three tails.
- *Counting.* For three tails, `mt_conj.py` counts ordered triples (552 = 6 · 92 and 6,156 = 6 · 1,026),
  but unordered pairs for two tails.
- *Remark 6.3* ("a stem is adjacent to its own leaf only", so N(g) = {x₁, x₂} or {c_j, x_i}) assumes
  distinct stems. With s₁ = s₂ = g, the case N(g) = {c₁, c₂} also arises; it is trivial.
- *Fix.* Say "unordered" or divide by 3!, and add "(distinct stems and avoided vertices)" to the
  test description. Remark 6.3 needs "with distinct stems".

**M7 (NIT, reproducibility).** The §5 tamper test (130 order-7 schedules; "14 swaps of two
commuting moves" accepted) has no committed script, seed or output.
- My `tamper.py` ran 3 × 130 random corruptions (first or last move removed, target changed,
  adjacent swap, wrong drop index, move turned into a suppression).
- `mt_verify` accepted exactly the corruptions that my `replay()` judges to be legal schedules, and
  rejected all the others. There were no disagreements: 38 accepted, all valid (33 commuting swaps
  and 5 moves that happened to be valid suppressions); 352 rejected, all invalid.
- *Fix.* Commit the script and its output.

**M8 (NIT, citations).**
- *DT section.* Introduction "There the triangle base holds in all data [DT, §5]" and the Table 3
  caption "[DT, §5]". In the compiled DT, §5 is "A local guard". The evidence is §6, and the residual
  families are §6.3.
- *E28.* "E28 hard graphs [T6, E28]": E28 is the experiment-log entry `research/experiments.md` E28
  (E), not a section of t6-dense. That entry identifies the 8 graphs, and confirms that the triangle
  base certifies all 48 roots.
- *d(z) = 4.* "Test1 at d(z) = 4 was already known" has no citation. Cite `emc_four` / two-step
  descent (synthesis §28).

**M9 (NIT, scope labels and wording).**
- *Abstract status label* "everything in Sections 2–3 is proved and formalised in Lean". Remark 2.8
  is not formalised, and Example 3.3 is a computed example (it is now a Lean derivation in
  `ex33_steerK.lean`).
- *"Coverage (paper)".* The 882 is a computation (`pattern.py`); only Theorem 4.2 is on paper.
- *"Token removals".* "A schedule needs 2k − 1 token removals" counts drops that isolate a stem.
  These remove a tail, not a token; Proposition 4.1 says "moves of the second kind". The same applies
  to "frozen … no token can ever be removed".
- *Abstract, move (M).* It should say "outside {ℓ_i, x_i} of the live tails" and "adjacent to no other
  token after the deletion".
- *"Almost every".* "In the dense residual almost every other unscheduled root is frozen" means
  42 of 53 (79%). Give the number.

**M10 (NIT).** Proposition 4.1, "In M⁺, Φ = 2k + 1", needs d_J(w) ≥ 3 (otherwise w is isolated in M
and Φ = 2k). The hypothesis δ(J) ≥ 3 appears only in the next sentence.

**M11 (NIT).** Example 3.3, "the schedule found by the search, with four moves after the
suppression".
- The default search (`mtok`, the J9 run) finds a different, 6-move schedule for this data and
  orientation: S1:0-6 M8-2 M4-8 D0 M8-3 M3-7.
- The stated one is the shortest, from `MAXLEN` (`MAXLEN=8 mtok` prints exactly
  S1:0-6 M8-3 M3-7 M4-8 D0).
- *Fix.* "The shortest schedule (`MAXLEN`)".

**M12 (NIT).** §6: "explore.py explores all reachable states". In `resid_O8_explore.txt` it hit
its state cap at 3 roots: `M~~|yrU~Ufn^hLN~_` r = 3 and `MF~~~^~]jzIfflv}_` r = 3, 4, marked
"capped".
- All three have degree n − 2, so they sit in the n − 2 column.
- My uncapped exploration gives the same least Φ (4, 5, 5) and agrees with every `*_explore.txt`
  line. So the table is right; disclose the cap, or cite the exhaustive recheck.

**M13 (NIT).** §6, order-7 bullet: "All of them lie in cones J = K₁ + B over Eulerian B". At order 7
with d(z) = 6, z is adjacent to every other vertex, so every J of Table 1 is such a cone. The sentence
is true but carries no information. Otherwise the bullet is exact: 18 roots of Fr~vw, Fqz^w and
Fut~w, plus FsQ~w r = 0, 5 and Fsz\w r = 4, 5, 6. The three roots of degree 3 lie in Fqz^w (2, 3)
and Fut~w (2).

**M14 (NIT, Lean).**
- *`triangleBase_of_steerK`* concludes `TriangleBase J z r`, the "in particular" of Theorem 3.1. The
  first clause (for these data, x_i ∉ V(Q(y_i)) for every i) is proved inside (`Or.inl` for every
  pair) but not exported. Either export it or say that the Lean statement is the second clause.
- *Duplicates.* Two duplicated `omit [DecidableEq U] in` lines (before `live_move` and `live_supp`).
- *Usability.* To make `decide` close the side conditions of a concrete derivation, I needed
  `DecidablePred ((delEdge G a b).Adj x)`/`plusEdge` instances. Instance search fails on nested graph
  operations, although `Decidable ((delEdge G a b).Adj x y)` is found. I also needed `Decidable`
  instances for the `def`s `OffTails`, `SuppOK`, `OneLive`. They are in `ex33_steerK.lean`; consider
  adding them to the library.

**M15 (NIT, bookkeeping).**
- *Axioms.* §7 says `#print axioms` was run "for every theorem listed", but `axioms_mt.lean` omits
  the nine lemmas `evenSet_*`, `tailInv_*`, `live_*` of the §7 table. I checked them
  (`axioms_extra.lean`): standard axioms.
- *Uncompressed schedules.* `data/runs/J9_s1_all.txt` is gitignored; only the `.gz` is committed. The
  `.gz` is byte-identical to a fresh `SUPP=1 mtok g6 0 0 0 2` run, so the README's
  `grep SCHED all9.txt` reproduces.

### Further checks, all SOUND

**Definitions 2.1–2.2 against Lean, C++ and Python.**
- (TS) is `TailSys`: xc, xw, and cross (c′ ≠ c, c′ ≠ s, x′ ≠ c, x′ ≠ s for t ≠ t′).
- (TI) is `TailInv`, and (TG) is `TailGood` (`MeetsOnce` on {c, x}).
- (M) is `move`. With τ = evenSet, `u ∉ τ` plus adjacency means u odd. `OffTails` is u ∉ X(K), and
  the token condition is quantified over τ − p in K − up.
- (D) is `drop` (s ∉ τ with cs ∈ K means s odd). (S) is `supp` plus `SuppOK`: leaves of all tails,
  since a dead leaf is isolated, and {a, b} ≠ {x, s} for live tails.
- The end is `fin`.
- `mtok.cpp`: priorities and seeds only reorder moves. The (S) test on live leaves only is
  equivalent, and so is "p is not y_i of a live tail". Memoising failures is sound on an acyclic
  state graph, and the budget exits before inserting into the failure set.
- `mt_verify.py`'s replay re-derives each condition.

**Proofs.**
- Lemma 2.3: b′(p) = 1, Z′(u) = ∅, ends b′ − 1_p + 1_u. This is `fan_step_multi` verbatim.
- Lemma 2.4:
  - c ∉ {p, u, a, b, c₀, s₀} keeps N(c) = {s};
  - x stays odd (x ≠ p, x ≠ u; (TS) for the drop; degrees of a, b unchanged);
  - the new edge ab is not xs.
- Lemma 2.5(b): the path cs carries the ends at c and s, misses x and, by (TS), every other tail's
  leaf. Lemma 2.5(c): p ∉ X because p is even.
- Lemma 2.6: the leaf-tail lemma [TRN, Lemma 6.1]; its hypotheses (x ∉ {c, s} odd, x ≁ s, at most one
  even vertex) match `avoid_leafTail`.
- Theorem 2.7: induction.
- Theorem 3.1: the end count at y_i after deleting the leaves, and the trace argument (a path through
  x_i avoids ℓ_i, so it has one edge at y_i and would end there, against b(y_i) = 0).
- Remark 2.8: in G⁺ from (g, y) the vertices of positive even degree are exactly the token positions
  (A35), so "u odd" is "u ≠ the other token", and the end at ≤ 1 token is a retirement.
- Proposition 4.1: the case analysis.
- Theorem 4.2: steps 1–4 checked line by line, including:
  - v ∈ {p, q} under (A1);
  - y₁ ∉ {p, q} (it would force v = w);
  - under (A2), v ∉ {w, r, z} keeps d(v);
  - {s, t} ≠ {x₁, y₁} because y₁ ≁ v after step 2;
  - the token set is {y₁, y₂} after step 1, and {y₂} at the end.

**Theorem 4.2 count** (`thm42.py`, own code).
- 882 of 10,118 roots at order 9 and 6 of 40 at order 7: the same root set as `J9_pattern.txt`,
  which `pattern.py` reproduces byte-identically.
- All 1,938 certificate schedules (610 A1B1, 633 A1B2, 695 A2B2) replay legally under my `replay()`.
  `pattern.py` reports 1,808 because it stops at the first applicable (A).
- Every covered root is scheduled in my search.

**Example 3.3** (`example33.py`, `ex33_steerK.lean`).
- N_J(w) = {z, 0, 6}, 0 ≁ 6, d_J(4) = 3, r ≁ 4.
- After S the tokens are {4, 8}; 8 → 3 gives {3, 4}; 3 → z retires; 4 → 8 lands on an odd 8 (degree 5,
  no token neighbour), and N(4) = {ℓ₁}. The drop isolates 4; one token (8) and the tail (ℓ₂, 8, 5)
  remain.
- In Lean the derivation `supp`, `move`, `move`, `move`, `drop`, `fin` elaborates, with
  `evenSet K0 = {1, 4, 8}`. It yields `TriangleBase J33 7 3` and `Test1At J33 7 3`, with axioms
  `propext`, `Classical.choice`, `Quot.sound` and no `native_decide`. So the Lean definition is
  usable as claimed.

**Executor independence and Fan's chain.**
- `mt_verify.py` shares no code with `mtok.cpp`.
- Its `fan()` is exactly the forced chain of [TRN, §2]:
  - start at x₀ = p;
  - σ(x) is the vertex before u on the current path read from x;
  - re-route P_j to x_{j+1} W⁻¹ x_j u W′, on the current version;
  - the next path is the original path ending at x_{j+1}, which is never P_j, because x_{j+1} is
    interior to it;
  - append u at the last end.
- Every intermediate decomposition is re-checked: cover, simple paths, ends = deg mod 2, live
  {ℓ_i, x_i} at most once. So an error in `fan()` could cause a rejection, never a false acceptance.
- Tamper test: no disagreement with my replayer (M7).

**Tables 1–2 and the per-instance data** (`indep_mt`, order 9 in 2.8 s).
- *Table 1.* Order 7: 40 roots, 17 scheduled, 71 / 242 data, 130 / 968 instances. Order 9: 10,118,
  7,529, 30,769 / 45,644, 76,474 / 182,576.
- *Per-root verdicts* are identical to `J7_s1.txt` and `J9_s1_all.txt.gz`. The 2,589 none roots are
  identical to `J9_none.txt`.
- *The 76,474 scheduled (data, orientation) instances* are identical to the SCHED lines of
  `J9_s1_all.txt.gz`. The authors' `mt_verify.py` accepts all of my 76,474 schedules (with Test1
  asserted), so the search and the executor cross-validate.
- *Table 2:* 7,045 (no S), 7,529, 7,620 (end at ≤ 1 token), 7,529 (sparse end; it matches
  `separation_sparse`, since each {ℓ_i, x_i} is packed by (TI)), 7,558 (no D, end at ≤ 1 token),
  and 0 (no D, ≤ 1 live tail). The last row is 0 trivially: without drops both tails stay live.
- *Inputs.* `filt.py 6 < one_even_{7,9}.g6` reproduces `J7_d6.g6` and `J9_d6.g6`. Independently,
  `nauty-geng -c -d3` plus my filter gives 7 and 1,819 graphs up to isomorphism, none missing, so
  "every 3-connected J" holds.

**Residual families.**
- *Inputs.* `gen_resid.py 6 8 2 7 SHAPE` (five shapes) reproduces `resid_O8.g6` byte-identically.
  `gen_resid.py 4 10 2 11 SHAPE` plus `gen_resid.py 4 8 1 77 C4` reproduces `resid_O10.g6`.
- *Table 3* agrees row by row with `*_s1_b2e6.txt`: 72 / 180, 109 / 144, 10 / 48, 0 / 6.
- *"None" verdicts.* My exact, uncapped search confirms every one: 69, 14, 18 and 6 roots, with no
  schedule in any of 3,088 / 376 / 912 / 360 instances.
- *Per-root comparison* (`cmp_roots.py`) with my search capped at 2·10⁶ states per instance (mtok's
  2·10⁶ nodes bound its distinct states):
  - all of `resid_O8` (180 roots, about 45 min on 3 cores): identical, 72 scheduled, 69 none,
    39 undecided under both, with no conflict;
  - a `resid_O10` sample, graphs 0, 4, 12 and 19 (one each of ∅, K2, K3, C4; 24 roots): identical,
    13 / 6 / 5.
- *Not run:* the other 20 `resid_O10` graphs and the E28 graphs in full. Their "none" roots are all
  confirmed (above).

**Proposition 6.1 data and the frozen table** (`agg_resid.py`).
- 1,597 roots with one non-neighbour at order 9, all unscheduled. The other 992 unscheduled roots
  have degree 5 (783) or 3 (209).
- Frozen-table rows, all exact:
  - order 7: 23 | 20 | 0 | 1 | 0 | 2;
  - order 9: 2,589 | 1,597 | 113 | 597 | 121 | 161;
  - `resid_O8` 69 | 36 | 27 | 4 | 2 | 0, `resid_O10` 14 | 2 | 7 | 3 | 2 | 0, E28 18 | 12 | 6 | 0 | 0 | 0,
    clt 6 | 4 | 2 | 0 | 0 | 0.
- Frozen among the n − 2 roots: 15 / 20 and 376 / 1,597. In every family the least Φ at an n − 2 root
  is 4 or 5.
- 53 proved-unscheduled roots of degree < n − 2 in the dense families, 42 of them frozen (38 with
  three non-neighbours, 4 with five).
- *Legal first moves* (`FIRSTONLY`): 260 of the 10,118 order-9 roots have none; this set is identical
  to `J9_firstmove.txt` and all are unscheduled. Residual 178 / 180, 144 / 144, 48 / 48.

**Lean.**
- `lake build`: "Build completed successfully (18426 jobs)".
- `lake env lean ../manuscripts/multi-token/scripts/axioms_mt.lean` is identical to `data/axioms.txt`
  (11 theorems, standard axioms). `axioms_extra.lean` gives standard axioms for the 9 bookkeeping
  lemmas.
- No `sorry`, `admit`, `native_decide`, `axiom` or `implemented_by` in `MultiToken.lean`.
- `TriangleBase`, `TriangleDisj`, `Test1At` (`DirectTest1.lean`) are used as intended. The schedule
  starts at `evenSet (triLeaf …)`, the orientation is the coordinate order of each pair of `L`
  (y = `p.2` carries the leaf `inr p.2`), and `test1At_of_steerK` takes `3 ≤ J.degree r`, as
  Corollary 3.2 does.
- The theorem docstrings match the compiled numbering (2.1–2.7, 3.1, 3.2).

**Consistency.** Every number in the abstract, the introduction, Tables 1–3, §6, "What remains", the
README and the Lean README section agrees with the data files and with my recomputation:
- 7,529 / 10,118 (74%), 76,474, 882, 72 / 180, 109 / 144, 10 / 48, 7,558, 91, 1,597 / 2,589, 260,
  181 / 324, 18,426 jobs, 2,860,182;
- the exceptions are M1 (what the "undecided" counts mean) and M4 ("including the Test1 lift").

## After 2afae07 (not audited; consistency only)

Commits 9914d37 … b8b15a3 (03:53–04:30) change the manuscript, scripts and data, partly in response
to an interim snapshot of this report. I did not audit them. Compared with the findings above, as
of b8b15a3:
- **Addressed:**
  - M1: Table 3 has a "Prop. 6.1" column, and its numbers equal mine. The §6 bullet and "What
    remains" item 1 are corrected. Two more `resid_O10` roots are scheduled at budget 2·10⁷ (seeds 7,
    11), so 33 / 3 are left undecided.
  - M4: `mt_verify.py` now asserts `verify_test1`.
  - M5: Remark 4.3 cites Proposition 6.1, with the per-shape counts 15, 10, 5, 9, 3 and
    1, 4, 4, 3, 2, 4, which match mine.
- **Not addressed:**
  - M2: the statement of Theorem 4.2 is unchanged.
  - M3: the paper proof of Proposition 6.1 is unchanged. Proposition 6.1 now cites a Lean proof
    (`not_steerK_triangle`, `not_steerK` in `MultiTokenObstruct.lean`, not audited). If that proof is
    sound, the statement is formal, but the paper proof still needs the corrected split.
  - M8: `[DT, §5]`, twice, and `[T6, E28]`.
- **New and not audited:** the all-odd lift (Section "aodd", Propositions `aoddlift` and `aoddobs`),
  the d(z) = 4 runs, `MultiTokenObstruct.lean`, and the changed `mtok.cpp`.

## Reproduced (commands)

S is my scratch directory. C is a `git archive 2afae07` export.

1. `g++ -O3 -std=c++17 indep_mt.cpp`, then:
   - `indep_mt g6 0 < J7_d6.g6` and `< J9_d6.g6` give Table 1;
   - `PRINT=2` gives the 76,474 SCHED lines;
   - `SUPP=0`, `TERM=1`, `TERM=2`, `DROP=0 TERM=1`, `DROP=0` (with `STOPDATA=1`) give Table 2.
2. `indep_mt resid 0 < *_none.txt` (exact; 9.5 s for `resid_O8`). `STOPDATA=1 indep_mt resid 2000000
   < resid_O8.g6` (three parts) gives the per-root comparison.
3. `python3 -I agg_resid.py 2 < …` gives the frozen table and the Proposition 6.1 check.
   `table3_prop61.py C/data` gives M1.
4. `python3 -I thm42.py < J9_d6.g6` gives 882. `example33.py`, `thm42_leafroot.py` and
   `prop61_case.py` give M2 and M3.
5. `python3 -I tamper.py C/scripts route_ext strict < my9sched.txt`: "verified 76474 schedules, Test1
   size and ends asserted" (2 min). `tamper … tamper SEED` for seeds 1, 2, 3.
6. `mt_indep 2 distinct|all`, `mt_indep 3 distinct|all` on `nauty-geng -cq n`.
7. Authors' tools rebuilt in S:
   - `SUPP=1 mtok g6 0 0 0 2 < J9_d6.g6` is byte-identical to `J9_s1_all.txt.gz`, and the PRINT=0
     run is byte-identical to `J7_s1.txt`;
   - `pattern.py` is byte-identical to `J9_pattern.txt`; `mt_verify.py` gives "verified 130" at
     order 7;
   - `MAXLEN=8` gives the Example 3.3 schedule.
8. `pdflatex` twice: 9 pages, no undefined references, text identical to the committed PDF. The label
   numbers match the item list (Def 2.1–2.2, Lemmas 2.3–2.6, Thm 2.7, Rem 2.8, Thm 3.1, Cor 3.2,
   Ex 3.3, Prop 4.1, Thm 4.2, Rem 4.3, Prop 6.1, Conj 6.2, Rem 6.3).
9. Lean: `lake build`; `lake env lean …/axioms_mt.lean`; `lake env lean
   ../research/audit/A36-scripts/ex33_steerK.lean` (8 s) and `axioms_extra.lean`.

## Overall verdict

The formal core is correct and faithfully formalised:
- the k-token schedule, Fan's step with many even vertices, the drop and suppression steps, the
  multi-tail leaf lemma, the transfer theorem, and the triangle base and Test1 from a schedule;
- `SteerK` is the manuscript's Definition 2.2, which is also what `mtok.cpp`, `mt_verify.py` and an
  independent search compute;
- a concrete schedule (Example 3.3) goes through the Lean pipeline to `Test1At` by `decide`.

All the computations reproduce exactly from independent code: Tables 1 and 2, the 76,474 schedules,
882, the none lists, the frozen table, the first-move counts, and the MT counts. The MT tests extend
without failure to shared stems and shared avoided vertices.

The paper understates its own Proposition 6.1. That proposition proves 34 of the residual roots it
reports as "undecided", which makes the closing claim about |O| = 10 false (M1). Theorem 4.2's Test1
clause lacks d_J(r) ≥ 3 (M2). The proof of Proposition 6.1 needs a corrected case split, although the
statement holds in every test (M3). The executor's Test1 check is a no-op as written, although every
lift passes when the check is asserted (M4).

None of this affects the Lean results or any table entry as a search verdict. The triangle base at
d(z) = 6 remains, as the paper says, unproved.

**Required fixes.**
1. M1: correct Table 3 (or annotate it), the §6 bullet, the README and "What remains" item 1 with the
   Proposition 6.1 roots (|O| = 8: 75 / 33; |O| = 10: 30 / 5; E28: 30 / 8); at |O| = 10 every shape has
   roots without a schedule.
2. M2: add d_J(r) ≥ 3 (or 3-connectivity) to the Test1 clause of Theorem 4.2.
3. M3: split the suppression case of Proposition 6.1 on the current adjacency of p to r.
4. M4: assert `verify_test1`'s result in `mt_verify.py` and regenerate the verify logs.

Recommended: M5 (cite Proposition 6.1 in Remark 4.3), M6 (scope and counting of the MT test,
Remark 6.3), M7 (commit the tamper test), M8 (DT §6.3, E28 source, the d(z) = 4 citation), M9–M15.

## Response (authors, after the audit)

Each finding, with where it is fixed (manuscript numbering unchanged).
- **M1** fixed in 3d7f0ca, before the final report: Table 3 has a "Prop. 6.1" column; the §6 bullet,
  Remark 4.3, "What remains" item 1 and the README use the corrected counts (|O| = 8: 75 without /
  33 undecided; |O| = 10: 30 / 3 after the seed reruns; E28: 30 / 8). The frozen table now says that
  it covers search-proved roots only.
- **M2** fixed: Theorem 4.2 now concludes Test1 only "if d_J(r) ≥ 3 (for example if J is
  3-connected)", and the proof cites the counterexample `Lsech?H?GA_B?@`. `pattern.py` skips roots
  with d(r) < 3; the counts are unchanged (882 / 10,118 and 6 / 40), and the counterexample is no
  longer reported.
- **M3** fixed: the proof of Proposition 6.1 is rewritten with the current set
  A(K) = {v ∈ V(J) − r : d_K(v) > 0, v ≁_K r} (Lean `nonNbr`). Before the first entry no move adds a
  vertex to A(K), and every removal takes one out; the suppression case splits on the current
  adjacency of p to r. Proposition 7.2 refers to the same set and split.
- **M4** fixed in 28376e6 (`assert verify_test1(...)`). The precedence slip in the leaf-deletion
  assertion is fixed too. All verifications were rerun after both fixes (`scripts/reverify.sh`;
  `data/runs/reverify_summary.txt`), and all pass.
- **M5**: the abstract and Remark 4.3 rest on Proposition 6.1. The hash caveat is replaced by the
  confirmation from this audit's exact search.
- **M6**: §6 states the scope of the test (distinct stems and avoided vertices), gives the three-tail
  counts unordered (92, 1,026; ordered 552, 6,156), and reports this audit's extension (37,707 and
  17,213 instances, 0 failures). Remark 6.3 assumes distinct stems and disposes of the case
  N(g) = {c₁, c₂}.
- **M7**: the tamper test now cites `A36-scripts/tamper.py`, run with seeds 1–3 against the fixed
  executor (`manuscripts/multi-token/data/runs/J7_tamper_seed*.txt`; the schedules are
  `J7_s1_sched.txt`). It accepts 38 corruptions, all valid (33 swaps, 5 suppressions), and rejects
  352, all invalid, which is the same as this audit's run.
- **M8**: [DT, §6] / [DT, §6.3]; E28 is cited as the experiments-log entry; d(z) = 4 cites synthesis
  §28 (two-step descent, `emc_four`).
- **M9**: the status labels exclude Remark 2.8 and Example 3.3. "Coverage" is labelled as a theorem
  on paper with a computed count. "Removals" is defined (retirements, suppressions, isolating drops).
  The wording of move (M) is fixed, and "almost every" becomes 42 of 53.
- **M10**: Proposition 4.1 assumes d_J(w) ≥ 3. **M11**: Example 3.3 is "the shortest schedule
  (MAXLEN=8)". **M12**: the explore cap and this audit's uncapped recheck are disclosed. **M13**: the
  order-7 cone sentence is a parenthetical remark (every J there is a cone).
- **M14**: §8 and the Lean docstring say that `triangleBase_of_steerK` exports the last clause, the
  first being proved inside. The duplicated `omit` lines are removed. `ex33_steerK.lean` (with its
  Decidable instances) is cited in §8.
- **M15**: `axioms_mt.lean` now lists all 22 theorems and lemmas of the §8 table, all on the
  standard axioms. `lake build` is green (18,428 jobs).
