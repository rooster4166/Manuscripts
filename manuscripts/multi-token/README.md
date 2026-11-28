# Multi-token steering (cloud session `claude/multi-token`)

Manuscript: `multi-token.tex` (compile with `pdflatex` twice). Lean: `lean/GallaiLean/MultiToken.lean`.

**Target.** The triangle base (direct-test1 Conj 3.1) at d(z) = 6: a Lovász decomposition of
M = J − zw − {za_i, zb_i, a_ib_i} with a_i ∉ Q(b_i) or b_i ∉ Q(a_i) for every pair. It gives Test1.

## Status

**The triangle base is not proved at d(z) = 6.** It is proved, in Lean, whenever the leaf graph has a
k-token schedule, and on paper on an explicit certificate class (Theorem 4.2). Schedules cannot exist
at roots with fewer than k non-neighbours (Proposition 6.1, Lean), which occur in every residual shape.

### Proved and formalised (no `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound` only; `data/axioms.txt`)
- `SteerK` (Definition 2.2): tokens are the even vertices; moves (M) Fan step onto an odd vertex off
  the live tails' `{ℓ_i, x_i}` and not adjacent to another token, (D) drop of a live tail whose stem is
  odd, (S) suppression of a degree-2 token with non-adjacent neighbours; end at ≤ 1 token and ≤ 1
  live tail.
- `fan_step_multi` (Lemma 2.3), the bookkeeping lemmas (2.4), the three steps (2.5:
  `tailGood_move`, `tailGood_drop`, `tailGood_supp` with `splitOff_supp`), the multi-tail leaf lemma
  `tailGood_fin` (2.6), **`steerK_good`** (Theorem 2.7, the transfer theorem, for any graph and any
  number of tails).
- **`triangleBase_of_steerK`** (Theorem 3.1) and **`test1At_of_steerK`** (Corollary 3.2).
- **`not_steerK_triangle`** (Proposition 6.1, `MultiTokenObstruct.lean`): if r has fewer than k
  non-neighbours in J − r, no data choice and orientation at r has a schedule (needs only d(w) ≥ 2);
  at d(z) = 6 this is every root of degree |J| − 2. It rests on **`not_steerK`**, an invariant over
  `SteerK` for any graph, tails and vertex r (also covering tails whose avoided vertex is r).

### Proved on paper
- Proposition 4.1 (the potential: a schedule needs 2k − 1 removals, each at a vertex of degree ≤ 2).
- Theorem 4.2 (a certificate family: w suppressible or retiring through r; y₁ of degree 3 whose
  token is removed at its third neighbour; drop of tail 1). It applies at 882 of the 10,118 roots
  with data at order 9; all 882 certificates executed by `mt_verify.py`.
- Proposition 7.1 (the all-odd lift of synthesis §31, coordinator) and the instance of Proposition
  7.2 (in the all-odd lift no root with at most k − 2 non-neighbours has a schedule; the invariance
  is `not_steerK`).

### Computed (exact scope in the manuscript, Sections 5 and 6)
- Order 9, d(z) = 6, all 1,819 3-connected J: a schedule for some data choice and orientation at
  7,529 / 10,118 roots (74%), no search undecided. All 76,474 schedules (every scheduled data choice
  and orientation) executed and checked independently, including the Test1 lift.
- Residual families (`gen_resid.py`; Table 3): 72 / 180 roots (|O| = 8) and 111 / 144 (|O| = 10), at
  node budget 2·10⁶ with the default move order, plus budget 2·10⁷ with seeds 7 and 11 for the roots
  left open (two more at |O| = 10). The milestone-1 counts 71 / 180 and 107 / 144 were at budget 2·10⁵.
  Roots without a schedule: 69 + 6 (|O| = 8) and 14 + 16 (|O| = 10), by the search + by Prop 6.1. Every shape at |O| = 8 has roots where the
  exhaustive search proves that no schedule exists, so no condition covering a whole shape exists for
  this move set.
- E28 hard graphs: 10 / 48 roots; the clt ∅ graph `M~~zRz{~m~~lX|j~_`: 0 / 6 (all proved none).
- All-odd lift (Section 7): 2,101 / 8,340 order-9 roots (25%; triangle base 74%), 0 / 36 at order 7,
  resid |O| = 8 14 / 180 (budget 2·10⁶), |O| = 10 54 / 144 (2·10⁵), E28 0 / 48. All schedules executed.
- d(z) = 4, order 9: triangle base 11,347 / 11,389 roots, all-odd lift 6,456 / 7,572.
- Conjecture MT (6.2; the multi-tail lemma with any number of live tails): 0 failures in all tests
  (two tails on every connected base graph of order ≤ 9, 2,860,182 instances at order 9; three tails
  at order ≤ 7). It would add only 91 roots at order 9.
- Residual structure: 260 of the 2,589 unscheduled order-9 roots have no legal first move; in the
  dense families almost every unscheduled root is *frozen* (no reachable state allows a token removal).

## Files
- `scripts/mtok.cpp`: the schedule search (env `SUPP=1` suppression, `AODD=1` the all-odd lift,
  `MAXLEN` iterative deepening, `SEED` move-order shuffle; input lines `g6 [roots]`).
- `scripts/mt_verify.py`: the independent executor (needs `route_ext` built from `tools/route_ext.c`
  and `direct-test1/scripts/tb.py`); `SCHED` lines (triangle base) and `SCHEDA` lines (all-odd lift).
  Note: before commit 28376e6 it did not assert the boolean returned by `tb.verify_test1` (path count
  and two ends at r); all verifications were re-run after the fix and pass.
- `scripts/pattern.py`: Theorem 4.2 from its hypotheses, writing certificates.
- `scripts/firstmove.py`, `scripts/explore.py`: legal first moves; exhaustive state exploration
  (least potential reached).
- `scripts/mt_conj.py`: the test of Conjecture MT.
- `scripts/filt.py`: inputs; `scripts/axioms_mt.lean`: the axiom check.
- `data/*.g6`: inputs (`J7_d6`, `J9_d6`, `resid_O8`, `resid_O10`, `e28_hard`, `clt_hard`).
- `data/runs/`: outputs (`*_s1_b2e6.txt` residual runs; `J9_s1_all.txt.gz` all order-9 schedules;
  `*_none.txt` proved-unscheduled roots; `*_explore.txt` their least potential; `*_verify.txt`).

## Reproduce
```
cd scripts
g++ -O2 -std=c++17 -o mtok mtok.cpp && gcc -O3 -o route_ext ../../../tools/route_ext.c
SUPP=1 ./mtok g6 0 0 0 2 < ../data/J9_d6.g6 > all9.txt          # all order-9 schedules
grep SCHED all9.txt | python3 mt_verify.py ./route_ext            # verified 76474 schedules
SUPP=1 ./mtok resid 2000000 0 0 1 < ../data/resid_O8.g6           # Table 3
python3 pattern.py < ../data/J9_d6.g6 | python3 mt_verify.py ./route_ext   # Theorem 4.2
```
