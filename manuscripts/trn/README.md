# TRN — the tight transfer (cloud session `claude/trn`)

Manuscript: `trn.tex` (compile with `pdflatex` twice). Lean: `lean/GallaiLean/TRN.lean`, `lean/GallaiLean/TRNSteer.lean`.

**TRN** (conj-n Conjecture 4.1; Lean `TightTransferNOn`).
- Setting: G has at most one even vertex g; x, y are odd and non-adjacent; u ∈ N(g) ∩ N(y), u ≠ x.
- Claim: if G − gu has a Lovász decomposition whose path ending at y avoids x, so does G.
- The case y ≁ g is TR of l1-induction with A = {x}; the case y ~ g is TightTransferAdj.
- TRN ∧ NA ⇒ Conjecture N (conj-n). NA is now proved (`manuscripts/na`), so TRN is the only missing piece of N.

## Status

**TRN is not proved.** Conjecture N is reduced, formally, to TRN on the *unscheduled core*: the core instances that two-token steering does not settle.

### Proved and formalised
No `sorry`. All 15 theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound` (`data/axioms.txt`, from `scripts/axioms_trn.lean`). The full library builds (18,424 jobs).
- `conjN_of_core`, `conjN_of_core_neighbourAvoid` (Theorem 5.2): Conjecture N follows from the **core of TRN** (`TightTransferNCore`, Definition 5.1) plus the degree-two case, which is NA. A core instance has everything the induction for N has at hand when it applies TRN:
  - (C0) G is an instance of N;
  - (C1) N holds on smaller graphs (`ConjNBelow`);
  - (C2) all-tight;
  - (C3) the child keeps a witness;
  - (C4) x and y have a common neighbour;
  - (C5) N(g) is not an independent pair.

  `tightTransferNCore_of`: TRN ⇒ core. At order 9 the core has 90,056 of the 490,923 TRN tests.
- `avoid_of_separating_child` (Lemma 4.1): if some Lovász decomposition of G − gu separates x and y, then (G, y, {x}) is good.
- Outright cases, where (G, y, {x}) is good with no hypothesis on G − gu:
  - `avoid_of_farApart`: dist(x, y) ≥ 3;
  - `avoid_of_degTwo_indep`: d(g) = 2 with N(g) independent.
- **Two-token steering** (Section 6, `TRNSteer.lean`).
  - Setup: hang a leaf ℓ at y. The leaf graph has two even vertices, g and y; put a token on each.
  - A move sends a token along an edge to a vertex that is not x or ℓ, not the other token, and not adjacent to the other token after the edge is deleted.
  - Theorem 6.5 (`avoid_of_steer2`): if a schedule of moves retires one token (it reaches a vertex with no edge left), then (G, y, {x}) is good. No hypothesis on G − gu is used.
  - Ingredients:
    - the leaf-tail lemma (Lemma 6.1, `avoid_leafTail`): N for a leaf tail; its neighbour may be the even vertex;
    - Fan's step with two even vertices (Lemma 6.2, `fan_step_two`);
    - `steer2_meetsOnce` (Lemma 6.4).
  - TRN's own Fan step g → u is exactly a forbidden move, since u ~ y.
  - Theorem 6.9 (`conjN_of_core2`): **TRN on the unscheduled core ⇒ Conjecture N.**

### Proved on paper
- **Proposition 3.1** (the failure mechanism). For a good D′ of G − gu, let P_y be the path through yu and e its end on y's side. Fan's transfer fails iff all three hold:
  - P_y ≠ Q′(y);
  - the forced chain reaches e (then e ∈ {g} ∪ N(u));
  - x ∈ V(P_y).
- **Lemma 3.2** (half-path invariance). The forced chain depends only on the half-paths at u. Re-pairing at u keeps the chain.
- Further results:
  - the chain facts (Lemma 2.2);
  - exchange (Lemma 4.2), now also for y ~ g;
  - rotations at y (Lemma 4.3);
  - re-pairing at u (Lemma 4.4);
  - the case d(y) = 1.
- **Proposition 6.10** (the first move). In an all-tight instance, the first move must take the y-token to N(y) ∖ N[g]. So N(y) ⊆ N[g] leaves no schedule.
- **Proposition 7.2.** TRN-E (some good D′ has a trivial chain) implies EE. A proof of TRN-E in full would therefore prove the open conjecture EE.

### Computed
- **Steering coverage** (exhaustive, orders 5, 7, 9; `data/steer.txt`, `data/steer_core_stats.txt`):

  | | order 5 | order 7 | order 9 |
  |---|---|---|---|
  | core tests with a schedule | 2 / 10 | 177 / 480 | 64,291 / 90,056 |
  | instances of N with a schedule | 3 / 12 | 840 / 1,161 | 238,265 / 263,264 |

  - Among the unscheduled core triples, 4,048 of the 8,777 at order 9 have no legal first move.
  - Every schedule at orders 5 and 7 (843) was executed by an independent Python verifier (`steer_verify.py`). At order 9, a sample of 5,957 of the 238,265 schedules (every 40th) was executed, all verified (`data/steer_verify9_sample.txt`).
- **TRN and TRN-E hold in every test run:**
  - all 490,923 order-9 TRN tests;
  - 39,098 tests on 400 random graphs of orders 11 and 13. One test was budget-undecided and holds with no budget. 101 candidate tests were dropped because the child was budget-undecided: RANDOM101README;
  - all 365,665 and 466,120 tests of the order-11 `geng` slices 17/2000 and 517/2000.

  0 TRN violations in all of these.
- **Classification of failing pairs (G, D′).** Exhaustive at orders 5 and 7; order 9 on the first 4,000 graphs.
  - At order 7 there are 31,477 bad D′. loc (re-decomposing the chain paths + Q′(y) + gu) repairs 30,489.
  - Every bad D′ outside the **hard core** is repaired by loc at order 7. The hard core: the chain meets y at its first step, and u ∉ Q′(y).
  - At order 9 (sample) this fails for 24,176 of 30,217,696 bad D′ outside the hard core.
  - Example 9.2 (`FqJPo`) is a reached core residual whose D′ no move repairs; it nevertheless has a schedule. Example 9.3 (`FsQnO`) is unscheduled too.

### Validation
- The C++ enumerator and forced-chain simulator (dec.h of l1-induction, `chainlist.cpp`) agree with a Python brute force (`brute.py`, different enumeration) on all 14 + 1,847 tests at orders 5 and 7.
- The audit A34 (`research/audit/A34-trn.md`) recomputed Tables 1, 3, 4 and the order-9 counts with independent code.

## Reproduction (`scripts/`)
Requirements: g++, Python 3 (networkx for `randg.py`), nauty (`nauty-geng`, order-11 slices only), Lean via elan for `axioms_trn.lean`.
```
cd scripts
./build.sh          # tools; oracle headers from ../../l1-induction/scripts
./run.sh            # validation, TRN/TRN-E (orders 5,7,9), random 11/13, core counts, classification 5/7, steering
./classify9.sh      # order-9 classification sample (hours)
nauty-geng -cq 11 17/2000 | ./trnbud 0      # an order-11 slice
python3 summarize.py ../data/classify7.txt   # the aggregates of Table 4
./show FqJPo 4 2 3 6                         # every good D' of one test, with chain and transfer
SHOWCORE=1 ./steer2 CORETESTS 2000000 0 0 < ../../stl/scripts/one_even_7.g6   # core triples with schedules
(cd ../../../lean && lake env lean ../manuscripts/trn/scripts/axioms_trn.lean)
```
