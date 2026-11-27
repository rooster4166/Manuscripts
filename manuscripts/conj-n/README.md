# Conjecture N — cloud session `claude/conj-n`

Manuscript: `conj-n.tex` (compile with `pdflatex` twice). Lean: `lean/GallaiLean/ConjN.lean`, `lean/GallaiLean/ConjNFar.lean`.

**Conjecture N** (dl-one Conj. 9.1). Setting: G has at most one even vertex g; x, y are odd and non-adjacent; y has a neighbour w ≠ g with w ∉ N(x). Claim: some Lovász decomposition has x ∉ Q(y).

## Status
- **N is not proved, and no closed inductive class was found.**
- **Proved and formalised** (no `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound` only):
  - `conjN_of_tight_degTwo`, `conjN_of_tight_neighbourAvoid`: **TRN ∧ NA ⇒ N**.
    - TRN = TR of l1-induction for A = {x}, with the tail also allowed to be adjacent to g (`TightTransferNOn`).
    - NA = in a graph with no even vertex, Q(y) can avoid a *neighbour* x when y has a neighbour w ≠ x not adjacent to x (`NeighbourAvoidOn`).
    - The induction never leaves N, and no L1* is used. A non-tight target always gives an N-child, so the witness makes the hypothesis side (ST of l1-induction) automatic.
  - `conjNDegTwo_of_neighbourAvoid`: NA implies the degree-two case N(g) = {x, y} of N. The converse (subdivide xy, then suppress g) is on paper only (Lemma 4.4).
  - Caveat (Remark 4.10): for the blocked part of L1* with |A| = 1 that N covers, the reduction replaces ST by NA *together with* the counterpart of TR for tails adjacent to g (A = {x}). That counterpart is a new conjecture, not part of l1-induction's reduction.
  - `avoid_of_splitOff`: move (e), splitting off a vertex of degree two.
  - `tightTransferNOn_of`, `conjN_of_TR_neighbourAvoid`: TR (`TightTransfer`) + its c ~ g counterpart (`TightTransferAdj`) + NA ⇒ N.
  - `fan_single_protected_path` (Lemma 3.2, ends outside N(u)): Fan's lemma keeping a path of the old decomposition unchanged. Proof: remove the path (`PathDecomp.erase_path`), apply Fan, re-add it (`PathDecomp.add_path`).
  - `avoidFar_target` (Theorem 3.3, move (x)), the target-in-A move: for u ∈ N(g) ∖ N[c], u possibly in A, the child is (G − gu, c, A, B ∪ N_G(u)), where B constrains the far end of Q_c (`AvoidFarDecomp`).
- **Proved on paper only** (used only in the computations):
  - Lemma 3.1: the leaf-path move.
  - Lemma 3.2 with degree-one ends in N(u).
  - The far-end moves (b_B), (C), (c_B) of Theorem 3.3.
  - Lemma 4.4, the converse and the no-common-neighbour clause.
  - Remark 4.5: NA holds when d(y) = 3 (split (g) at y with the pair x, w) and when d(x) = 1 (Lemma NP).
- **Verified by computation** (exhaustive in the stated range):
  - Certificates for N:
    - Old calculus (l1-induction Thm 3.1, every route for (h)): 115 of the 263,264 order-9 N-instances have no certificate.
    - New moves: 5 remain, all with d(g) = 2 and g on a triangle.
    - Every count is for the *uncapped* calculus: leaf paths of every length, every g–c route for (h). The first draft capped both (7 instead of 5 uncertified, and higher stuck counts); see `research/audit/A31-conj-n.md`, F2.
  - TRN: 0 violations.
    - Order 9: 236,891 tests with y ≁ g and 254,032 with y ~ g.
    - Order-11 geng slices 17 and 517 (of 2000): 831,785 tests.
  - TR* (c ~ g, |A| ≤ 2): 565,744 tests at order 9, 0 violations.
  - NA: all good at orders 4, 6, 8, 10 (1,305,621 instances at order 10). Outside the easy cases of Remark 4.5 and Lemma 4.4, 1,011,733 of these remain at order 10 (`nadjstat.cpp`).
  - N⁺ (Q(y) ∌ x and Q(y) does not end next to x), for x ~ g: 134,911 / 134,911 at order 9.
  - Closure:
    - Under TR*, the class N ∪ NA has 0 stuck instances at orders 5, 7, 9. These orders contain only its N members. Its NA members (even orders) are stuck in 22/215 at order 6 and 2,451/9,558 at order 8, so N ∪ NA is not closed; NA is the residual.
    - Unconditionally, N is stuck only at all-tight configurations: every stuck instance is all-tight. At order 9, 35,338 of the 52,070 all-tight instances (of 263,264) are stuck.
- **The obstruction** (manuscript §6): three shapes persist under every refinement tried.
  1. The all-tight configurations. They need a transfer through a tight target.
  2. NA. Its leaf-graph children carry a forbidden pair {x, g} with x ∈ N(g).
  3. An even vertex of degree two on a triangle (a subdivided double edge).

  Classes tried and their failures:
  - The set form N₂ stays stuck.
  - The union with L1*-admissible instances stays stuck.
  - The subcubic restriction stays stuck.
  - Every far-end or witness class contains false instances (smallest: `DEk`).

## Reproduction (scripts/)
Requirements: g++, gcc, Python 3, nauty (`nauty-geng`). The oracle header `lind.h` is in `../l1-induction/scripts` (pass `-I`). `enum.c` from `../dl-one/scripts` is needed for the cross-check.
```
I=../../l1-induction/scripts; O=../../stl/scripts
for t in ncert closure2 xcert tx nplus gplus nadj tradj trn qb; do g++ -O2 -I $I -o $t $t.cpp; done
gcc -O2 -o allodd allodd.c; (cd ../../dl-one/scripts && gcc -O2 -o enum enum.c)
mkdir -p out
for k in 5 7 9; do ./ncert BMSR < $O/one_even_$k.g6 | tail -1; done   # old calculus, all routes: 115 uncertified at order 9
./ncert BMSR < $O/one_even_9.g6 | grep UNCERT | awk '{print $2}' | sort -u > out/unc9.g6
./xcert < out/unc9.g6 | tail -1                                         # new moves: 5 uncertified
for k in 5 7 9; do ./trn < $O/one_even_$k.g6 | tail -1; done          # TRN
nauty-geng -cq 11 17/2000 | ./trn | tail -1                             # TRN, an order-11 slice
./tradj 2 < $O/one_even_9.g6 | tail -1                                  # TR* with c ~ g, |A| <= 2
for n in 4 6 8 10; do nauty-geng -cq $n | ./allodd | ./nadj | tail -1; done   # NA (order 10: minutes)
for k in 5 7 9; do ./nplus < $O/one_even_$k.g6 | tail -1; ./tx < $O/one_even_$k.g6 | tail -1; done
./tables.sh                                                             # closure tables (incl. subcubic) -> out/tables.txt
./closure2 N1NA -T2 -b 0 -p 0 < $O/one_even_9.g6 | tail -1              # 0 stuck under TR*
./closure2 N1 -b 0 -p 1000000 < $O/one_even_9.g6 | python3 n1stuck.py $O/one_even_9.g6   # stuck ⊆ all-tight
(for n in 4 5 6; do nauty-geng -cq $n; done; cat $O/one_even_7.g6) | python3 xcheckb.py | tail -1   # 399,762 queries
./rerun.sh                                                              # regenerates all of ../data (hours)
```
- `tables.sh` enumerates orders ≤ 8 with `nauty-geng` labellings and order 9 from `one_even_9.g6`. The one-liners above use the `one_even` lists, so their `move_*` breakdowns can differ from `data/tables.txt`; the STUCK and FALSE counts agree.
- `closure2 -cap` (and `-L k`) reproduce the capped calculus of the first draft.
`closure2 CLASS [-s] [-g] [-a maxA] [-b maxB] [-T|-T2] [-p maxprint]`:
- classes: `N1 N2 V L1 U C1 N1NA N2B NBA N2XC W`, and `D_N2` with `-D k -G k`;
- `-s` checks soundness (prints FALSE lines);
- `-g` prints the goodness of every stuck instance's children;
- `-T` adds TR as a move, `-T2` adds TR*;
- `-cap` restores the caps of the first draft (leaf paths ≤ 2, ≤ 8 shortest routes).

| File | Content |
|---|---|
| `scripts/ext.h` | extended instances (G, c, A, B), all moves (l1-induction Thm 3.1 + manuscript §3), base cases, optional TR/TR* move |
| `scripts/orcb.h` | exact oracle with far-end restriction (on top of `lind.h`) |
| `scripts/closure2.cpp` | closure computation for a class: stuck / false instances |
| `scripts/ncert.cpp`, `scripts/xcert.cpp` | certificates for N, old calculus and extended calculus |
| `scripts/trn.cpp`, `scripts/tradj.cpp` | TRN and TR* tests |
| `scripts/nadj.cpp`, `scripts/nadjstat.cpp`, `scripts/allodd.c` | NA tests; census of the cases of Remark 4.5; all-odd filter |
| `scripts/nplus.cpp`, `scripts/tx.cpp`, `scripts/gplus.cpp` | N⁺, the (x)-child of the core, far-end form of "Q(c) avoids g" |
| `scripts/xcheckb.py`, `scripts/qb.cpp` | far-end oracle vs full enumeration (399,762 queries, 0 mismatches) |
| `scripts/tables.sh`, `scripts/rerun.sh`, `scripts/n1stuck.py`, `scripts/feat2.py`, `scripts/show.py` | tables, full regeneration, classification of stuck instances |
| `data/tables.txt` | closure tables (manuscript §5.3) |
| `data/conjecture_tests.txt` | conjecture tests (manuscript §5.2) |
| `data/ncert9_uncertified.txt`, `data/xcert9_uncertified.txt` | the 115 and the 5 uncertified order-9 instances |
| `data/n1_stuck9.txt`, `data/n1_stuck57.txt` | stuck N-instances by shape; all-tight counts |
