# TRN — the tight transfer (cloud session `claude/trn`)

Manuscript: `trn.tex` (compile with `pdflatex` twice). Lean: `lean/GallaiLean/TRN.lean`.

**TRN** (conj-n Conjecture 4.5; Lean `TightTransferNOn`).
- Setting: G has at most one even vertex g; x, y are odd and non-adjacent; u ∈ N(g) ∩ N(y), u ≠ x.
- Claim: if G − gu has a Lovász decomposition whose path ending at y avoids x, so does G.
- The case y ≁ g is TR of l1-induction with A = {x}; the case y ~ g is TightTransferAdj.
- TRN ∧ NA ⇒ Conjecture N (conj-n).

## Status

**TRN is not proved.**

### Proved and formalised
No `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound` only; the full library builds (18,420 jobs).
- `conjN_of_core`, `conjN_of_core_neighbourAvoid` (Theorem 5.2): Conjecture N follows from the **core of TRN** (`TightTransferNCore`, Definition 5.1) plus NA (via the degree-two case). The core is TRN restricted to the instances that N's induction reaches, with N available on smaller graphs (`ConjNBelow`). A core instance satisfies:
  - all-tight;
  - the child keeps a witness;
  - x and y have a common neighbour;
  - N(g) is not an independent pair.

  `tightTransferNCore_of`: TRN ⇒ core, so this strengthens `conjN_of_tight_degTwo`. At order 9 the core holds 91,890 of the 490,923 TRN tests.
- `avoid_of_separating_child` (Lemma 4.1): if some Lovász decomposition of G − gu separates x and y, then (G, y, {x}) is good.
- Outright cases, where (G, y, {x}) is good with no hypothesis on G − gu:
  - `avoid_of_farApart`: dist(x, y) ≥ 3;
  - `avoid_of_degTwo_indep`: d(g) = 2 with N(g) independent.

### Proved on paper
- **Proposition 3.1** (the failure mechanism). For a good D′ of G − gu, let P_y be the path through yu and e its end on y's side. Fan's transfer fails iff all three hold:
  - P_y ≠ Q′(y);
  - the forced chain reaches e (then e ∈ {g} ∪ N(u));
  - x ∈ V(P_y).
- **Lemma 3.2** (half-path invariance). The forced chain depends only on the half-paths at u. Re-pairing at u keeps the chain.
- Exchange (Lemma 4.2), now also for y ~ g; rotations at y (Lemma 4.3); re-pairing at u (Lemma 4.4); the case d(y) = 1.
- **Proposition 6.2.** TRN-E (some good D′ has a trivial chain) implies EE, which is open. So TRN-E is not a proof route by itself.

### Computed
- **TRN-E holds everywhere tested:**
  - all 490,923 order-9 TRN tests;
  - 39,098 tests on 400 random graphs of orders 11/13;
  - all 365,665 tests of the order-11 `geng` slice 17/2000.

  0 TRN violations in all of these.
- **Classification of failing pairs (G, D′).** Exhaustive at orders 5 and 7; order 9 on the first 4,000 graphs. At order 7, 31,477 bad D′:
  - loc (re-decomposing chain paths + Q′(y) + gu) repairs 30,489;
  - every bad D′ outside the **hard core** is repaired by loc. The hard core is: the chain meets y at its first step, and u ∉ Q′(y).
  - In the hard core, 986 of 13,212 bad D′ are repaired by no move.
- **Smallest core residuals:**
  - `FsObO` (y ~ g, d(g) = 2 on the triangle g y u);
  - `FsQnO` (y ≁ g, d(g) = 4);
  - `FsRLO` (y ≁ g, d(g) = 2 on a triangle through x).

### Validation
The C++ enumerator and forced-chain simulator (dec.h of l1-induction, `chainlist.cpp`) agree with an independent Python brute force (`brute.py`: different enumeration, separate Fan simulation) on all 14 + 1,847 tests at orders 5 and 7.

## Reproduction (`scripts/`)
Requirements: g++, Python 3 (networkx for `randg.py`), nauty (`nauty-geng`, order-11 slices only).
```
cd scripts
./build.sh          # tools; oracle headers from ../../l1-induction/scripts
./run.sh            # validation, TRN/TRN-E (orders 5,7,9), random 11/13, core counts, order-5/7 classification
./classify9.sh      # order-9 classification sample (hours)
nauty-geng -cq 11 17/2000 | ./trnbud 0      # an order-11 slice
python3 summarize.py ../data/classify7.txt   # the aggregates of Table 3
./show FsObO 4 1 2 6                         # every good D' of one test, with chain and transfer
```
