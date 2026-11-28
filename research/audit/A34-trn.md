# A34. Audit of trn (manuscript, `TRN.lean`, scripts, data)

Date: 2026-11-28. Adversarial referee. Grades: **SOUND**, **GAP** (fixable, statement or claim not
justified as written), **ERROR** (false as stated), **NIT** (wording, citation, bookkeeping).

**Version.** I started on the uncommitted draft. During the audit the author committed it
(d3051bb, 4c48071) and merged "NA proved" (53dae68). The audited files at HEAD 53dae68, with no
working-tree changes to them:

| file | md5 |
|---|---|
| `manuscripts/trn/trn.tex` (630 lines) | `02eb916bd7b4e77c2ca12ca81c1cf908` |
| `manuscripts/trn/trn.pdf` (2 min older than the tex; numbering identical) | `0c189eaf71b35fc468569c770d755265` |
| `manuscripts/trn/README.md` | `a5aa54007b22a8c6a3776c57c4834518` |
| `lean/GallaiLean/TRN.lean` | `056da9c63a64f0fdd64ef8a808530fc8` |
| `scripts/classify.cpp` / `trne.cpp` / `core.cpp` | `acd7b5c7…` / `a5d224c2…` / `cb14ae0a…` |
| `l1-induction/scripts/dec.h` / `lind.h` / `orc2.h` | `a5834e6d…` / `c9eb7241…` / `2cdf8785…` |

Several files appeared during the audit, and I did not audit them:
- the untracked `scripts/steer*.{cpp,py}`, `data/classify9_first4000.txt` and
  `lean/GallaiLean/TRNSteer.lean`;
- the edit to `lean/GallaiLean.lean`.

My `lake build` ran before `TRNSteer.lean` existed. ORDER9SUMMARY and SLICE517 are placeholders and
are not findings.

**Auditor files** (`research/audit/A34-scripts/`):
- `indep.cpp`: an independent checker for orders 5 and 7. It uses none of the authors' headers.
  - It enumerates Lovász decompositions as transition systems: at each vertex it pairs the edges,
    leaving d mod 2 of them as ends, and it accepts a pairing only if it joins two different
    chains whose vertex sets meet only in that vertex.
  - It computes Fan's transfer by a closed formula on transitions, not by re-routing:
    φ(x_{j+1}) = x_j at u; at x_j the edge paired with x_j u becomes an end and the old end edge is
    paired with x_j u; at g the end edge is paired with gu.
  - It checks Prop 3.1 and its sub-claims, Lemma 2.2(i), Lemma 3.2 on every re-pairing, and the
    constructions of Lemmas 4.2 and 4.3. It recomputes the whole classification (exch, rot, rep,
    loc, hard core). It also records whether G itself has an N-witness.
  - Every decomposition it produces (enumerated, transferred, rotated, re-paired, exchanged) is
    checked to be a Lovász decomposition.
- `agg.py`: aggregates the output of `indep.cpp`.
- `indep9.cpp`: an independent TRN / TRN_E / core counter (its own path-growing search with a memo).
  It reads graph6 directly from `nauty-geng`. It also counts core tests in which G has an N-witness.
- `examples.py`: pure-Python brute force of Examples 8.2 and 8.3, plus a suggested replacement for
  Example 8.2.
- `axioms.lean`: `#print axioms` for every theorem of `TRN.lean`, and a check that the core alone
  now implies N.
- `core_with_witness.lean`: the fix for F1, compiled.
- `undecided.cpp`: re-decides the budget-undecided random tests. It uses the authors' oracle, for
  identification only.
- `per_graph.sh`, `cmp_random.py`: run `indep9` graph by graph on the random set and compare the
  counts with `trnbud`.
- `g6.py`: a graph6 helper.

## Verdict per item

| item | verdict |
|---|---|
| Lemma 2.1 (cited) vs `fan_single_supp` | SOUND |
| Lemma 2.2 (chain facts) | SOUND; NIT F9(a) |
| Prop 3.1 (failure mechanism, exact iff) | SOUND. Exhaustively confirmed on all 152,290 good D′ (orders 5, 7) with an independent transfer. NIT F9(b) |
| Lemma 3.2 (half-path invariance) | SOUND. All 166,822 re-pairings at orders 5, 7 checked. NIT F9(c) |
| Lemma 4.1 (separation survives) | SOUND, formalised |
| Lemma 4.2 (exchange, also y ∼ g) | SOUND. All 1,365 applications at orders 5, 7 built and checked. Citation NIT F6 |
| Lemma 4.3 (rotations α, β) | SOUND. 127 α and 2,944 β applications built and checked |
| Lemma 4.4 (re-pairing) | SOUND. "Some re-pairing gives a good D″ with a good transfer" coincides with the lemma's condition: 342 at order 7 by both |
| Prop 4.5 (i), (ii), (iii) | SOUND. (i) and (ii) formalised |
| Def 5.1, Thm 5.2 | Implications SOUND (paper and Lean). **GAP F1**: the core is not "the instances that the induction reaches" |
| Prop 6.2 (TRN_E ⇒ EE) | SOUND for the class-free EE. NIT F5 (citation), F4 (conclusion overstated) |
| Examples 8.2, 8.3 | Every stated fact SOUND (independent brute force). Example 8.2 is not an instance that N needs (F1) |
| Lean faithfulness | SOUND: Def 5.1 = `TightTransferNCore`, Thm 5.2 = `conjN_of_core`, Lemma 4.1 and Prop 4.5(i),(ii) match, with the Lean forms more general. Docstring NITs F6 |
| Lean axioms, `sorry`, build | SOUND: no `sorry`; all 6 theorems use only `propext`, `Classical.choice`, `Quot.sound`; `lake build` succeeds (18,422 jobs) |
| Computations (Tables 1–3, §6–8) | SOUND: all reproduced, most of them independently. NIT F3, F8 |
| Overclaiming | GAP F1; NIT F2–F5, F7, F11 |

## Findings

**F1 (GAP). The core omits the hypothesis that G itself is an instance of N, so it is strictly
larger than what the induction reaches. The "smallest core residual", Example 8.2, is never
reached.**
- *Location.*
  - Def 5.1 and `TightTransferNCore` (TRN.lean l.181).
  - Abstract: "the instances that its induction reaches".
  - §5, first paragraph: "We record exactly what it needs".
  - README, and the TRN.lean docstrings (l.21, l.173).
  - Example 8.2 and the core columns of Tables 1 and 3.
- *What.*
  - The induction of Thm 5.2 runs on an instance of N. In Lean, `conjN_of_core` l.216 has
    `obtain ⟨w0, hyw0, hw0e, hxw0⟩ := hw`.
  - So whenever the core is applied, G has some w0 ∈ N(y) with w0 ∉ evenSet G (so w0 ≠ g) and
    w0 ≁ x.
  - (C3) asks only for a child witness w ≠ u, and w = g is allowed.
  - The two conditions differ exactly when y ∼ g, g ≁ x and N(y)∖{g} ⊆ N(x). In that case the only
    child witness is g, and (G, y, x) is not an instance of N.
- *Counterexample: Example 8.2 itself.*
  - FsObO with g=4, y=1, x=2, u=6 has N(1) = {0, 4, 6}, with 0 ∼ 2, 6 ∼ 2 and 4 = g.
  - Theorem 5.2 never applies the core here.
- *Counts* (independent; `indep.cpp`, `indep9.cpp`, column "with an N-witness").
  - Order 7: 14 of the 494 core tests are unreached. They carry 64 of the 384 unrepaired core bad
    D′, including both FsObO instances. All 64 have y ∼ g, d(g) = 2 on the triangle g y u, and x on
    the partner half.
  - Order 7, size: every reached core residual has at least 10 edges; FsObO has 8.
  - Order 9: 1,834 of the 91,890 core tests are unreached, all with y ∼ g. The reached core is
    36,728 + 53,328 = 90,056.
- *Fix (checked).*
  - Add (C0), "some w ∈ N(y)∖{g} is not adjacent to x", to Def 5.1 and to `TightTransferNCore`.
  - In `conjN_of_core`, pass `⟨w0, hyw0, hw0e, hxw0⟩` at l.274. `core_with_witness.lean` compiles
    this variant, `conjN_of_coreW`, with the three standard axioms.
  - Recompute:
    - Table 1: core y∼g becomes 366 at order 7 and 53,328 at order 9.
    - Table 3: core column.
    - §8: core counts become 320 unrepaired instead of 384.
  - Replace Example 8.2 by a reached instance of the same shape. A candidate, verified by
    `examples.py`:
    - G = FqJPo, edges 01,02,05,13,15,24,26,35,36,46; g=4, y=2, x=3, u=6.
    - d(g) = 2 on the triangle g y u, and 0 is an N-witness.
    - D′ = {0 1 3, 1 5 3 6 2 4, 2 0 5}, so P_0 = g y u x 5 1 and Q′(y) = 2 0 5. Here q = 5 ∈ R lies
      beyond x, the same obstruction as in FsObO.
    - The transfer has Q(y) = 2 4 6 3 5 1 ∋ x.
    - loc fails: all 4 re-decompositions put x on y's path. No rotation and no re-pairing works, and
      the exch hypothesis fails.
  - Alternatively, keep Def 5.1 and drop "exactly" and "reaches".
- *Secondary remark.* Even with (C0), the induction needs the conclusion for one tight target per
  (G, x, y), not for every one. By (C1) the child of every tight target with a witness is good, so
  the per-u core is still stronger than needed.

**F2 (NIT, overclaim).**
- Abstract: "Conjecture N, which gives DL(1)".
- By DL Prop 9.2, N *reduces DL(1) to near twins*. The introduction says this correctly.

**F3 (NIT, overclaim).**
- Abstract: "The same holds on random graphs of orders 11, 13". README: "TRN-E holds everywhere
  tested … 39,098 tests".
- `data/random_11_13.txt`, which I reproduced byte for byte, has "TRN-E holds 39097, undecided 1".
  It also shows that 101 candidate tests whose child hit the budget were dropped from the 39,098;
  neither Table 2 nor the text mentions this.
- I decided the undecided test with no budget: `LUIiOg?gICW^XK`, g=6, y=10, x=3, u=1. TRN_E holds
  there, by `orc2` with no budget and by `indep9`.
- I re-decided 43 of the 101 child-undecided candidates; all 43 have a good child and satisfy
  TRN_E.
  - 32 were decided by `indep9`, which finished 395 of the 400 graphs: 38,515 tests, TRN_E holds in
    all, and 0 per-graph mismatches against `trnbud`.
  - 11 more were decided by `orc` at budget 2·10⁸.
  - The other 58 sit in 3 dense order-13 graphs where both searches are slow.
- Fix: report 39,098 / 39,098 after re-deciding, and mention the 101.

**F4 (NIT, overclaim).**
- Abstract: "so it is not a proof route". §6: "TRN must be proved with non-trivial chains in
  general" and "TRN_E is not a proof route on its own".
- Prop 6.2 only shows that proving TRN_E *in full* is at least as hard as (class-free) EE.
- N needs only the core, where dist(x, y) = 2. By §10(3), that form does not obviously contain EE.
- Rephrase, e.g. "a proof of TRN_E in full would prove EE".

**F5 (NIT, citation).**
- Prop 6.2 cites "[MS, Conj. EE]". MS Conjecture 17 is EE *for class families* ("rainbow for A"),
  and TRN_E does not obviously imply it.
- The statement proved, and quoted, is the class-free EE, which is PE Conjecture 1.5. Cite that.
- "EE is open exactly when …": PE's wording is "open only when" (PE §7, open problem (1)).

**F6 (NIT, wrong cross-references).**
- Conj 1.1 cites "[CN, Conjecture 4.5]". In conj-n, TRN is **Conjecture 4.1**; 4.5 is the Remark
  "easy cases of NA". The same error is in the README and TRN.lean l.8.
- After Prop 3.1: "[L1I, Lemma 3.2] (a chain avoiding y suffices)". L1I has no Lemma 3.2. This is
  [TF, Lemma 3.2], which is [L1I, Lemma 2.2].
- §4: "The next lemma is [L1I, Lemma 4.3]". The exchange lemma is **L1I Lemma 4.2**; 4.3 is the
  Example "TR is sharp".
- TRN.lean l.14 and l.44 say "manuscript Lemma 3.3". It should be **Lemma 4.1**.

**F7 (NIT, status bookkeeping).**
- §9: "Not formalised: Prop 3.1, Lemmas 3.2–4.4, Prop 6.2". The range 3.2–4.4 contains Lemma 4.1,
  which *is* formalised. The list omits Lemma 2.2 and Prop 4.5(iii).
- §1 Results, item 2: "Lemma 4.1 and Proposition 4.5 are formalised". Only 4.5(i) and (ii) are.
- §1 Status, "Proved on paper": the list omits Lemma 2.2.
- §9 "18,420 jobs": today's successful `lake build` reports 18,422.
- §7 "The first three are proved moves". `rot` (any rotation at y along any path through y, then
  Fan) is a checked computation. Only its restriction to P_0 is Lemma 4.3.

**F8 (NIT, validation claim).**
- §7: "Every transfer and every repaired decomposition is checked to be a Lovász decomposition
  (check_decomp)".
- `classify.cpp`, the source of Table 3 and §8, never calls `check_decomp`:
  - exch is counted from its hypothesis;
  - rep is counted from the matching condition;
  - loc's decomposition is never built;
  - rot's D″ and all transfers are not checked.
- `local.cpp`, `halves.cpp`, `rules.cpp`, `minchain.cpp` and `trne.cpp` do not check either. Only
  `chain.cpp` (transfers) and `rot.cpp` (D″ only) do.
- `brute.py`'s "separate" Fan simulation is the same sequential algorithm, with the same `orig`
  bookkeeping as `dec.h`. So it validates the enumerator, not the Fan semantics.
- No effect on any number: `indep.cpp` checks every object and reproduces Table 3 exactly.
- Fix: add `check_decomp` calls to `classify.cpp`, or reword the sentence.

**F9 (NIT, proof exposition).**
- (a) §2 states the re-routing rule for "the path P_j of D′".
  - If P_j = P_m with m < j, that path was already re-routed at its other end. The rule must then
    act on the current version.
  - The segment from x_j to u is unchanged, so σ and Lemma 2.2 are unaffected.
  - This happens in 11,522 of the 152,264 good D′ at order 7.
  - L1I's proof of the exchange lemma says this explicitly; add one sentence. The f′ in the proof
    of Lemma 4.2 is where the case shows.
- (b) Prop 3.1(b).
  - The converse "the chain reaches e ⇒ it reaches y" is not argued. It needs: e's unique end is
    on P_y ∋ u, so the chain does not stop at e, and σ(e) = y.
  - The closing "Hence D is good iff …" only makes sense in case (b), since e is undefined in (a).
- (c) The proof of Lemma 3.2 applies Prop 3.1 to D″, which need not be good. Say that the
  vertex-set statements of (b) do not use goodness.

**F10 (NIT, wording and reproducibility).**
- §6, "the shortest forced chain always has length one": this means one vertex (k = 0). Say
  "is trivial".
- The §6 list of "other keys we tried" names 4 keys. `rules.cpp` tests 11, adding the max variants,
  yu-first, #paths through u and |P_yu|. All fail at order 7.
- Tables 1 and 2, "all one-even graphs": these are the *connected* ones. TRN reduces to connected
  G, since g, u, y lie in one component and x elsewhere is trivial. I checked that the lists equal
  `geng -c` up to isomorphism at orders 5, 7, 9 (7, 130, 11,936).
- §11: `build.sh` does not build `localshow`, which the paper lists. `repair*.cpp`, `feat.cpp`,
  `clean.cpp` and `steer*` are present but undocumented. `run.sh` writes to `/tmp`.

**F11 (NIT, currency).**
- NA was proved and formalised (`neighbourAvoidOn`) and merged into this branch during the audit
  (53dae68).
- Hence the core of TRN *alone* now implies N. `axioms.lean` checks
  `conjN_of_core_neighbourAvoid hT neighbourAvoidOn : ConjNOn V` with the three standard axioms.
- The abstract, Thm 5.2, §10 and the README still present NA as a hypothesis.

No ERROR found. Every proof on paper is correct. I also checked the cases S empty (a = g),
R empty, a path re-routed at both ends, the far end of Q′(y) being a chain vertex (including
q = g), y ∼ g against y ≁ g, d(y) = 1, and d_K(u) = 2.

## Reproduced (commands)

S denotes my scratch directory. Tools are rebuilt with
`cd manuscripts/trn/scripts && ./build.sh`, and `O=../../stl/scripts`.

1. **Validation.**
   - Command: `./chainlist < $O/one_even_k.g6 | sort` and `python3 brute.py < $O/one_even_k.g6 | sort`
     for k = 5, 7.
   - Result: identical, 14 and 1,847 lines.
   - Independent check: `indep` gives the same per-instance triples (nD, nAv, nGood) byte for byte:
     `TRIPLES=… indep < one_even_k.g6`, then `cmp`.
2. **Table 2, orders 5, 7, 9.**
   - Command: `./trne 0 < $O/one_even_k.g6` (9.5 s at order 9).
   - Result: 4/10, 787/1,060, 236,891/254,032 tests; TRN_E holds in all.
   - Independent check: `indep9 < one_even_9.g6`, and also `nauty-geng -cq 9 | indep9` (16 s),
     gives the same counts and 0 TRN violations.
3. **Table 1 and the d(g) split.**
   - Command: `./core < $O/one_even_k.g6`.
   - Result: identical to `data/core.txt`.
   - Independent check: `indep9` gives the same, including 370,094 / 12,150 / 6,345 / 10,444 and
     the d(g) splits. It adds the N-witness column (F1).
4. **Random 11/13.**
   - Command: `python3 randg.py 400 11 11 13 | ./trnbud 2000000`.
   - Result: identical to `data/random_11_13.txt` (21.7 s). The undecided test is decided by
     `undecided 2000000 0 0 < r1113.g6`: TRN_E = 1 and TRN = 1.
   - Independent check: `per_graph.sh` runs `indep9` on each graph with a 30 s limit, and
     `cmp_random.py` compares the results.
     - 394 graphs finished, plus `LUGvmz~RI?vEz~` at 900 s.
     - The per-graph test counts equal `trnbud`'s, or exceed them only by child-undecided
       candidates (32).
     - TRN_E holds in all 38,515 tests.
5. **Slice 17/2000.**
   - Command: `nauty-geng -cq 11 17/2000 | ./trnbud 0`.
   - Result: 365,665 tests, TRN_E holds in all (88 s), identical to `data/slice11_17of2000.txt`.
6. **Table 3 and the §8 Observation.**
   - Commands: `./classify 6 < $O/one_even_7.g6`, `CORE=1 ./classify 10 < …`,
     `./classify 0 < one_even_5.g6`.
   - Result: byte-identical to `data/classify{5,7,7_core}.txt`.
   - Independent check: `indep < one_even_7.g6` and `indep CORE < …`, aggregated by `agg.py`,
     reproduce every number of Table 3 and §8:
     - bad D′ 31,477; y∼g 24,332; i=1 18,994; e-half 7,361; u ∈ Q′(y) 8,228;
     - exch 1,363; rot 5,273; rep 342; loc 30,489; some move 30,491;
     - none 986, all with i=1 and u ∉ Q′(y); of these, y∼g 846, triangle 170, child witness 788;
     - core 14,753 / 384 and the other core entries;
     - hard core 13,212, of which 12,224 by loc and 2 by re-pairing only; outside the hard core,
       18,265 bad, all repaired by loc.
   - The order-5 entries are reproduced too: 4 bad pairs, all repaired.
7. **Witness-restricted repairs.** 24,942 / 4,393 / 342 / 24,152, reproduced from the `indep`
   output.
8. **Examples 8.2 and 8.3.**
   - Command: `python3 -I examples.py`.
   - Every stated fact holds: graph6 names, degrees, (C2)–(C5), D′, P_0, Q′(y), chain, transfer,
     "every re-decomposition … puts x on y's path", and the stated good D′ with trivial chain and
     Q(y) = 1 4 6.
   - No rotation, re-pairing or exch works, and no good decomposition of G keeps the non-chain
     path. The N-witness status is as in F1.
9. **Lean.**
   - Commands: `lake env lean research/audit/A34-scripts/axioms.lean` (axioms) and
     `lake env lean GallaiLean/TRN.lean` (no warnings).
   - `lake build` succeeds with 18,422 jobs. `core_with_witness.lean` compiles.
