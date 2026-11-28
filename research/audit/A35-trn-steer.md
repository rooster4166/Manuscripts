# A35. Audit of trn: Section 6 (two-token steering), `TRNSteer.lean`, the steering data, and the A34 fixes

Date: 2026-11-28. Adversarial referee. Grades: **SOUND**, **GAP** (fixable, claim not justified as
written), **ERROR** (false as stated), **NIT** (wording, citation, bookkeeping).

**Version.** Branch `claude/trn`, commit b01386d, clean working tree. The two placeholders
`VERIFY9` and `RANDOM101` are pending by design and are not findings (what they should contain is
at the end).

| file | md5 |
|---|---|
| `manuscripts/trn/trn.tex` (969 lines) | `51147b944cf58dab84e3b188aa884136` |
| `manuscripts/trn/trn.pdf` (text identical to my recompilation of the tex) | `0611ef40eef52fefa0c93ac39d0a7d8d` |
| `manuscripts/trn/README.md` | `4698b0cb331f9a532c8d84a5a6c31d2a` |
| `lean/GallaiLean/TRN.lean` | `702adf4bb1c01cce8c954afe6a132da3` |
| `lean/GallaiLean/TRNSteer.lean` | `284f8c742af72e0710c04f72441ff024` |
| `scripts/steer2.cpp` / `steer.cpp` | `4ed4525c…` / `c347fe8e…` |
| `scripts/steer_stats.py` / `steer_verify.py` / `brute.py` | `31f2838d…` / `e683188d…` / `94484903…` |
| `scripts/core.cpp` / `classify.cpp` / `rerouted2.cpp` / `summarize.py` | `259e185d…` / `36717ad5…` / `61b9c026…` / `12f9bddd…` |
| `scripts/run.sh` / `build.sh` / `axioms_trn.lean` | `06ad45c2…` / `5e41fe91…` / `c4b29874…` |
| `data/steer.txt` / `steer_core_stats.txt` / `steer_core7.txt` / `steer_verify57.txt` | `b02952fb…` / `12dc2c28…` / `e4617419…` / `60d9feea…` |
| `data/core.txt` / `classify7.txt` / `classify7_core.txt` / `classify9_first4000.txt` | `0a3627e4…` / `050d1582…` / `dc8ab450…` / `78534b09…` |
| `data/rerouted2.txt` / `axioms.txt` / `instances57.txt` / `random_11_13.txt` | `12d77af7…` / `52079639…` / `18612173…` / `16bc9dc5…` |
| `stl/scripts/one_even_{5,7,9}.g6` | `58bd4356…` / `f9bc10f8…` / `2d190bbd…` |
| `l1-induction/scripts/lind.h` / `orc2.h` / `dec.h` | `c9eb7241…` / `2cdf8785…` / `a5834e6d…` |

**Auditor files** (`research/audit/A35-scripts/`):
- `indep_steer.cpp`: an independent recomputation of Table 1 and Table 2. It uses none of the
  authors' headers or scripts.
  - Its own graph6 parser.
  - Its own goodness oracle: (H, y, {x}) is good iff some path from y to an odd vertex, avoiding x,
    leaves a graph with a parity decomposition. The parity-decomposition search is exact, with
    three exact prunings: Lovász's theorem, a degree bound, and a component test.
  - Its own schedule search, a forward BFS over states (edge set, g-token, y-token) of G+ with ℓ an
    explicit vertex. It implements Definition 6.3 literally. Modes: both tokens; the y-token only
    (move (T)); both tokens with the first move by the y-token.
- `exec_sched.py`: replays schedules and checks them against Definition 6.3, then executes the proof
  of Theorem 6.5. It finds the bottom decomposition by its own search, undoes each move by its own
  forced chain, and checks b(t) = 1, Z(w) = ∅, the parity ends and "meets X once" at every step.
  It then deletes ℓ and checks for a Lovász decomposition of G with x ∉ Q(y). It shares no code
  with `steer_verify.py` or `brute.py`.
- `examples_a35.py`: Examples 6.6, 6.11, 9.2, 9.3 (the steering claims), by brute force.
- `agg9.py`: an independent aggregation of `data/classify9_first4000.txt`, with the hard-core split.
- `steer2_examples.lean`: builds the schedules of Examples 6.6 and 9.2 as `Steer2` derivations,
  move by move, and applies `avoid_of_steer2`. It also checks that TRN's own step g → u fails the
  side condition of `Steer2`.

## Verdict per item

| item | verdict |
|---|---|
| Lemma 6.1 (leaf tail) | SOUND (all three branches; w = g; isolated vertices). Citation NIT S2 |
| Lemma 6.2 (Fan step, two even vertices) | SOUND. NIT S3 (the remark after it) |
| Definition 6.3 | SOUND. The sequential and inductive forms are equivalent. `Steer2` is the same notion |
| Lemma 6.4 | SOUND (non-even token, retirement, symmetry, invariant) |
| Theorem 6.5 | SOUND |
| Example 6.6 (FsRDG) | SOUND: every stated fact checked, including the three intermediate decompositions |
| Remark 6.7 | SOUND. NIT S4 (move (T) must also avoid ℓ) |
| Def 6.8, Theorem 6.9 | SOUND, and formalised faithfully |
| Proposition 6.10 | SOUND |
| Observations after Table 2 | **ERROR S1** (first move by the y-token); the rest SOUND |
| Example 6.11 (FqHTg, Dqw) | SOUND (36 / 24 reproduced; Dqw; 8 edges at order 7) |
| Examples 9.2, 9.3, steering claims | SOUND (FqJPo's stated output is one of the 4 the construction can produce) |
| Citations in §6 | SOUND except S2 |
| Lean faithfulness (`TRNSteer.lean`, (C0) in `TRN.lean`) | SOUND |
| Build, `sorry`, axioms | SOUND: 18,424 jobs, no `sorry`, 15 theorems with standard axioms |
| `steer2.cpp` vs Definition 6.3; CORETESTS vs `core.cpp` | SOUND. Identical per-triple results to my independent search at orders 5, 7, 9 |
| Table 2 and its bullets | Numbers SOUND, all reproduced independently at orders 5, 7, 9. ERROR S1 |
| Table 1 (with (C0)) | SOUND, reproduced independently at orders 5, 7, 9 |
| Table 4 core column, §9 observation | SOUND (order 7 independent; order-9 sample re-aggregated) |
| Re-routing count (§2) | SOUND (11,522 of 152,264) |
| A34 F1–F11 | all fixed. One sentence added for F1 is NIT S8 |
| Overclaiming | NIT S5, S6, S7. TRN is clearly marked as unproved throughout |

No GAP. The single ERROR is one sentence about the data. It does not touch any proof or table.

## Findings

**S1 (ERROR, one sentence; no proof affected). "In every schedule found, the first move is by the
y-token, as Proposition 6.10 requires" is false for the schedules of Table 2.**
- *Location.* §6, third bullet after Table 2.
- *What.* Table 2's first column, and `steer2 N`, count the schedules of all instances of N, and
  most of those start with the g-token. From `SCHED=1 ./steer2 N 2000000 0 0`:

  | order | schedules | first move by the g-token | first move by the y-token |
  |---|---|---|---|
  | 5 | 3 | 0 | 3 |
  | 7 | 840 | 592 | 248 |
  | 9 | 238,265 | 194,175 | 44,090 |

- *It is not only the search order.* My BFS with the first move restricted to the y-token finds that
  some scheduled instances of N have **no** schedule starting with the y-token: 232 of 840 at
  order 7 and 36,543 of 238,265 at order 9.
- *What is true.* The statement holds for core triples, which is all that `steer_stats.py` checks
  (29,874 of 29,874 at order 9). It holds more generally for every all-tight instance: I found 0
  exceptions, as Proposition 6.10 forces.
- *Fix.* "In every schedule found for a core triple (indeed for every all-tight instance), the first
  move is by the y-token." Since Proposition 6.10 proves this, the bullet is really a consistency
  check of the search, and could be worded as one.

**S2 (NIT, citation).** Lemma 6.1, second bullet: "(This is the free-target transfer of [DL,
Prop. 7.1]; Lean `avoid_free_target`.)"
- DL Prop 7.1 assumes that u is adjacent to neither a nor b. In Lemma 6.1 the target u ∉ {x, c, w}
  may be adjacent to x.
- The statement used is the paragraph after DL Prop 7.1 ("a target u ∉ N[b] ∪ {a} carries S_b"),
  which is the Lean `avoid_free_target` (it needs only u ≠ a, u ≠ b, b ≁ u, b ≠ g). It is also step
  (2) of [CN, Thm 4.6].
- The paper's own argument in that bullet is complete, so only the citation changes.

**S3 (NIT).** Remark after Lemma 6.2: "If u ∼ o in H − uz, then Z(u) ∋ o".
- This holds only when o is even (b(o) = 0); an odd o has its end.
- In the use, o is the other token and is even (see the invariant under "Further checks"). Add
  "and o is even".

**S4 (NIT).** Remark 6.7, move (T): "a trail y = y_0, …, y_k of distinct edges with every y_i
(i ≥ 1) outside N[g] ∪ {x}, ending at a vertex left isolated".
- In G+, y_1 = ℓ is excluded as well (ℓ ∈ X). Either add ℓ, or say "a trail in G".
- "Left isolated" is meant in G+. In G it makes no difference: a trail from y that ends at y uses an
  even number of y's edges and d_G(y) is odd, so y is never left isolated.
  - This is why `steer.cpp`, which works in G without ℓ, agrees with `steer2`.
- With that reading, the equivalence with y-only schedules is correct; my BFS confirms it at
  orders 5, 7 and 9 (3, 287 and 59,630).

**S5 (NIT, overclaim).** §6, first sentence: "This section proves the conclusion of TRN outright …
for most core instances".
- The proof covers the scheduled instances. Whether these are "most" is computed and depends on
  the order: 2/10 at order 5, 177/480 (37%) at order 7, 64,291/90,056 (71%) at order 9.
- At order 7 it is false. Say "for many core instances (71% of the core tests at order 9,
  Table 2)".

**S6 (NIT, overclaim).** §11, item 1.
- "By Theorem 6.9 it is all of Conjecture N." Theorem 6.9 is one implication. Say "it is all that
  remains of Conjecture N" or "it implies Conjecture N".
- "About half of its instances have no legal first move (Proposition 6.10)." This is computed and
  counts triples, not tests: 63/133 at order 7 and 4,048/8,777 at order 9 of the unscheduled core
  triples. State the scope.

**S7 (NIT, abstract wording).**
- "never onto x or ℓ and never onto a neighbour of the other token" omits "nor onto the other token".
- "The step of TRN is exactly the forbidden move" should be "is a forbidden move". Moves onto x or
  ℓ, onto the other token, and other moves next to it are forbidden too. Remark 6.7 says this
  precisely.

**S8 (NIT, introduced by the F1 fix; the wording is A34's own).** §5, after Def 5.1: "Conditions
(C0) and (C3) differ exactly when y ∼ g, g ≁ x and N(y)∖{g} ⊆ N(x)".
- The two conditions also differ the other way round: (C0) holds and (C3) fails when
  W(G, y, x) = {u}.
- Example: `DsO` with g = 1, y = 2, x = 4, u = 0, where N(y) = {0} and the child is good. Orders 5
  and 7 have 293 TRN tests with a good child, (C0), and no (C3).
- The intended statement is true and is the one behind the 1,834 count: "(C3) holds and (C0) fails
  exactly when y ∼ g, g ≁ x and N(y)∖{g} ⊆ N(x)."

**S9 (NIT, bookkeeping).** §10, "Library results used": add `avoid_of_apexSep`, the Lean form of
[NA, Lemma 2.3], which `avoid_of_steer2` ends with, and `apex_degree_none`.

### Further checks, all SOUND

**Lemma 6.1.**
- Branch 1: c ≁ x because c's only neighbour is w ≠ x.
- Branch 2:
  - H − gu keeps c as a leaf at w, since gu ≠ cw because c ∉ {g, u}.
  - Only u can be even in H − gu.
  - c is not a chain vertex, because c ≠ g and c ∉ N(u). This covers w = g too, including
    Q′(c) = c g: then P_0 = Q′(c), the chain is trivial and Q(c) = c g u.
- Branch 3:
  - g = w is impossible, since N(g) ⊆ {c} would give d(g) ≤ 1.
  - Otherwise N(g) = {x, w}, and Prop 4.5(ii) applies with (G, y, u) = (H, c, w), {a, b} ≠ {x, c}.
- The Lean proof follows the same three branches.

**Lemma 6.4.**
- "a not even" is the base case, and it is needed in this generality.
- For Theorem 6.5 the case never arises. In G+ from (g, y), the vertices of positive even degree are
  always exactly the token positions until a token retires.
  - A move a → u flips a to odd. It flips u, which was odd (not a token position, positive degree),
    to even or isolated. The other token's vertex is untouched.
  - So a token that moves onto y after the y-token has left (Example 9.2) or back onto g's start
    finds an odd vertex and makes it even.
  - y is never isolated because of yℓ. Parity alone already rules this out, so the `q == Y` test in
    `steer2.cpp` is redundant but harmless.
- "u ≁ b in K − au" is the same as u ≁ b in K, since a ≠ b.
  - The Lean `Steer2.fin` omits it because isolation implies it.
  - Every derivation from a ≠ b keeps a ≠ b.
- Hence Definition 6.3, `Steer2` and the C++ search are the same notion.

**Theorem 6.5.**
- In every K′, ℓ is a leaf at y, x keeps its odd G-degree, and x ≁ y.
- P_ℓ has length ≥ 2 because b(y) = 0.
- [NA, Lemma 2.3] is the pendant-leaf lemma.

**Proposition 6.10.** Both directions are correct, and the second needs no edge at g to have been
deleted. `examples_a35.py` confirms that FqHTg and FsQnO have no legal first move.

**Citations checked against the sibling manuscripts, compiled in scratch.**
- [NA, Lemma 2.3] (pendant leaf), [NA, Def. 3.1] (steering sequence), and [NA, §10(3)] ("graphs with
  an even vertex … intermediate graphs would have two even vertices").
- [CN, Conj. 1.1], [CN, Conj. 4.1], [CN, Lemma 4.3] (split), [CN, Lemma 4.4] (degree-two case is
  NA), [CN, Thm 4.6], and [CN] "the 5 left: d(g) = 2, N(g) = {u, x}, u ∼ x, y ∉ N(g), d(y) = 5".
- [DL, Conj. 9.1], [DL, Prop. 9.2].
- [PE, Conj. 1.5] (EE); [PE, Thm 5.1 and §7] ("By Theorem 5.1, EE is open only when …" is the first
  sentence of PE §7).
- [RD, Lemma 2.2, Thm 6.1, Thm 6.3]; [TF, Prop 2.1, Cor 2.3, Lemma 3.2]; [L1I, Lemma 2.2, Lemma 4.2,
  Conj. 4.1].

**Lean faithfulness.**
- `TightTransferNCore2` is `TightTransferNCore` with exactly one more hypothesis,
  `¬ Steer2 (leafX x) (apex G {y}) (some g) (some y)`, inserted before the child hypothesis. The
  argument lists are otherwise identical.
- `conjN_of_core2 : TightTransferNCore2 V → ConjNOn V` is Theorem 6.9. It is per vertex type, which
  is, if anything, stronger.
- `tightTransferNCore2_of` and `tightTransferNCore_of_core2` show that the two restricted
  conjectures are equivalent. That is the intended content: the scheduled instances are settled.
- (C0) in Lean is `∃ w, G.Adj y w ∧ w ∉ evenSet G ∧ ¬ G.Adj x w`. With g the only even vertex this is
  w ≠ g, as in Def 5.1. `conjN_of_core` passes ⟨w0, …⟩ as A34 asked.
- Other statements:
  - `fan_step_two` is Lemma 6.2 verbatim.
  - `avoid_leafTail` is Lemma 6.1 verbatim.
  - `steer2_meetsOnce` generalises Lemma 6.4 to an arbitrary property P closed under deleting edges
    with no end in X. In `avoid_of_steer2`, P is "a subgraph of G+ keeping every edge at X", which
    is exactly the paper's class.
  - `apex G {y}` with `leafX x = {none, some x}` is G + yℓ with X = {ℓ, x}.
- The Lean docstring numbers (6.1, 6.2, 6.3, 6.4, 6.5, 6.8, 6.9) match the compiled manuscript.
- `steer2_examples.lean` builds the schedules of Examples 6.6 and 9.2 as `Steer2` derivations, so the
  Lean definition accepts the paper's schedules. Example 9.2 is the one where the g-token enters y
  and returns to g.

## The A34 findings

| A34 | status in b01386d | new error? |
|---|---|---|
| F1 (core lacked (C0)) | **Fixed.** (C0) is in Def 5.1 and `TightTransferNCore`, and `conjN_of_core` passes w0. All core counts are recomputed, with my independent values in brackets: Table 1 (114/366, 36,728/53,328 and 1,834 excluded by (C0)); Table 4 core column (14,540 bad, 320 unrepaired); §9 (9,243, 4,975, 2, 5,297, 320). Example 9.2 is now the reached FqJPo. The abstract and §5 no longer say "reaches" or "exactly". The secondary remark (one target per instance) has been added | S8 (a wording from A34 itself) |
| F2 (DL(1)) | Fixed: "reduces DL(1) to near twins" | no |
| F3 (random run) | Fixed in substance: the undecided test is named and decided ("all 96 tests": I confirm 54 + 42 = 96 tests, TRN_E holds in all), and the 101 dropped tests are disclosed. RANDOM101 is pending | no |
| F4 ("not a proof route") | Fixed: "A proof of TRN_E in full would prove EE"; §7 says that it is not known whether the core form contains EE | no |
| F5 (EE citation) | Fixed: [PE, Conj. 1.5], "open only when", [PE, Thm 5.1 and §7] | no |
| F6 (cross-references) | Fixed: CN Conj. 4.1 (paper, README, TRN.lean), TF Lemma 3.2 = L1I Lemma 2.2, L1I Lemma 4.2, Lean "Lemma 4.1" | no |
| F7 (status lists, jobs) | Fixed: the Status lists, §1 item 2 and §10 agree; "18,424 jobs" matches my build; rot is called a checked computation | no |
| F8 (validation claim) | Fixed: §8 says what `chain.cpp` and `rot.cpp` check and what `classify.cpp` does not | no |
| F9 (a)(b)(c) | Fixed: the re-routing paragraph in §2 (count 11,522 / 152,264, reproduced by `rerouted2` and by the A34 checker); the converse in Prop 3.1(b); "vertex-set statements do not use goodness" in 3.1 and 3.2 | no |
| F10 (wording, keys, connected, scripts) | Fixed: "trivial"; twelve rules listed, matching the 12 lines of `rules.cpp` output (the sentence "each of the others fails on some test" is true; min\|P0\| fails on 2 tests); "connected one-even graphs"; `build.sh` builds every tool; the exploratory tools are documented; /tmp is disclosed | no |
| F11 (NA proved) | Fixed: the abstract, Theorem 5.2 ("the core alone"), §10 (`conjNDegTwoOn`), README | no |

## Placeholders (not findings)

**VERIFY9.** `run.sh` describes the planned sample: every 40th order-9 schedule
(`awk 'NR%40==1'`), which is 5,957 of the 238,265. It should report "verified 5,957 schedules", or
the number actually run.
- For comparison, my `exec_sched.py`:
  - replayed all 238,265 order-9 schedules against Definition 6.3 (5.7 s);
  - executed the same 5,957 (every 40th), with all checks passing (92 s);
  - executed every 4th, EXEC4.

**RANDOM101.** It should say how many of the 101 dropped candidates were decided, and how.
- A34 decided 43 of them: 32 with the A34 counter and 11 with `orc` at budget 2·10⁸. All had a good
  child and satisfied TRN_E.
- The other 58 lie in three dense order-13 graphs.

## Reproduced (commands)

S is my scratch directory. The authors' tools were compiled into `$S/bin` with
`g++ -O2 -I ../../l1-induction/scripts`, not into `scripts/`. `O=../../stl/scripts`.

1. **Lean.**
   - Commands:
     - `lake build`: "Build completed successfully (18424 jobs)" (cached);
     - `lake env lean GallaiLean/TRNSteer.lean` and `lake env lean GallaiLean/TRN.lean`:
       re-elaborated with no output;
     - `lake env lean ../manuscripts/trn/scripts/axioms_trn.lean`: 15 theorems, each
       `[propext, Classical.choice, Quot.sound]`, identical to `data/axioms.txt`;
     - `lake env lean ../research/audit/A35-scripts/steer2_examples.lean`: compiles, standard
       axioms.
   - `grep sorry` finds nothing in either file.
2. **Table 2, orders 5, 7, 9.**
   - Commands: the `run.sh` steering block (`steer N`, `steer2 N … 1`, `steer2 N`, `steer2 RESID`,
     `steer2 CORETESTS`).
   - Result: byte-identical to `data/steer.txt`; all of order 9 runs in 2.3 s.
   - `SHOWCORE=1 steer2 CORETESTS | steer_stats.py` is identical to `data/steer_core_stats.txt` and
     `data/steer_core7.txt`.
3. **Independent Tables 1 and 2.**
   - Command: `indep_steer full < one_even_k.g6`; order 9 takes 17 s.
   - Every entry of Table 1 is reproduced at orders 5, 7, 9: tests, core split, the five
     exclusions and the d(g) splits.
   - Every entry of Table 2 is reproduced: 3/12, 840/1,161, 238,265/263,264; all-tight 3/10,
     216/403, 41,447/52,070; core tests 2/10, 177/480, 64,291/90,056; core triples 2/7, 123/256,
     29,874/38,651; move (T) 3, 287, 59,630.
   - N(y) ⊆ N[g] holds for 3, 63 and 4,048 of the unscheduled core triples, and for 0 of the
     scheduled ones.
   - Per triple, the following sets are identical to the authors' at all three orders:
     - the scheduled instances of N (vs `SCHED=1 steer2 N`);
     - the move-(T) instances (vs `steer2 N … 1`);
     - the core triples with their schedule flags (vs `SHOWCORE`).
4. **Schedules executed.**
   - `steer_verify.py` on orders 5 and 7: "verified 3", "verified 840", identical to
     `data/steer_verify57.txt`.
   - `exec_sched.py exec` (my code): 3 and 840 legal and verified; order 9 as under VERIFY9.
5. **First moves (S1).** Computed with `awk '{print $6}'` on the `SCHED` lines, and with
   `indep_steer` mode 2.
6. **Examples.** `python3 -I examples_a35.py`: ALL OK.
   - FsRDG: the core test, the schedule, the bottom graph and its single even vertex 1, steps 3, 2
     and 1 exactly as printed, and the final decomposition (one of 16 possible outputs).
   - FqHTg: u ∈ {0, 3, 5} are core tests; 36 good D′ and 24 transfers for u = 0; the stated D′; no
     legal first move.
   - Dqw: 6 edges, two unscheduled core triples, each with a legal first move.
   - FqJPo: the schedule; the stated output is one of the 4 possible.
   - FsQnO: no first move. FsRLO: the schedule, and d(y) = 3.
   - Smallest unscheduled core triples: 6 edges at order 5 and 8 at order 7, from `indep_steer`
     output.
   - The residual facts of 9.2 and 9.3 were rechecked with `A34-scripts/examples.py`: loc 0, rot 0,
     rep 0 good transfers, exch false, transfers as printed.
7. **Table 4, core column (with (C0)).**
   - `CORE=1 classify 10` is byte-identical to `data/classify7_core.txt` (480 / 414); `classify 6`
     is identical to `data/classify7.txt`.
   - Independent: the A34 checker (`indep CORE`), restricted to its lines with an N-witness and
     aggregated by `agg.py`, gives every entry of the core column:
     - 14,540 bad; 13,042 with y∼g; 8,309 / 6,231 by i; 3,176 / 11,364 by side; 4,578 with
       u ∈ Q′(y);
     - 561 / 1,926 / 96 by exch / rot / rep; 14,218 by loc; 14,220 by some move;
     - 320 by none, with 290 / 106 / 320 in the last row;
     - §9: 9,243 outside the hard core; 4,975 + 2 of 5,297 inside.
8. **Order-9 sample.** `agg9.py data/classify9_first4000.txt` gives every number of §8 and §9:
   - 98,614 classified, 59,212 skipped;
   - 63,254,161 bad, of which 59,114,393 repaired by some move and 58,670,619 by loc;
   - 4,139,768 by none, all with u ∉ Q′(y), 24,176 of them with i ≥ 2;
   - outside the hard core 30,217,696 / 30,193,520 / 24,176; inside 33,036,465 / 28,477,099 by
     loc / 28,920,873 by some move.

   `summarize.py` agrees. The first 4,000 graphs have 8 to 25 edges, as stated.
9. **Re-routing (§2).** `rerouted2` is identical to `data/rerouted2.txt`: 0 of 26 at order 5, and
   11,522 of 152,264 at order 7. The A34 checker gives the same.
10. **Random undecided test.** The A34 counter on `LUIiOg?gICW^XK` gives 96 candidates, 54 + 42
    tests, TRN_E holds in all. `indep_steer full` also counts 96 tests.
11. **Manuscript.** `pdflatex` twice in scratch: 14 pages, no undefined references. The text is
    identical to the committed `trn.pdf`. The label numbers match every reference checked.
