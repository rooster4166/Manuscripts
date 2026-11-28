# Conjecture AE is Conjecture EE; the deletion form of AE (session `claude/ae`)

Manuscript `ae.tex` (working draft). No PDF was built in this session, because there was no TeX installation. Lean: `lean/GallaiLean/AEEquiv.lean`.

**Status.** AE is **not** proved in general. It is now known to be the same problem as EE (prescribed-end).

- **Proved, Lean** (no sorry; standard axioms, `data/axioms.txt`):
  - `conjAE_iff_conjEE`: Conjecture AE ⇔ Conjecture EE. Instance by instance, AE at (K, c, g) is EE at (K + gc, c, g):
    - `avoidDecomp_of_terminal` (EE ⇒ AE) drops the terminal edge gc;
    - `ee_of_avoid` (multi-sep) is the converse.
  - `avoidDecomp_of_atMostOneCommon`: AE holds whenever g and c have ≤ 1 common neighbour. This comes from prescribed-end's `ee_atMostOneCommon`.
  - `ln2_of_leaf_at_head_of_atMostOneCommon`: the leaf-at-head case of L_N(2) (`ln2_of_leaf_at_head`) without the AE hypothesis, when a_j and c_j have ≤ 1 common neighbour.
- **Proved on paper** (`ae.tex`):
  - the exact deletion form of AE (Prop. 4.1): profiles b(w) ∈ {0, 2} on H = K − g, with a disjoint pairing of pieces;
  - a 5-vertex instance where the zero-free form CF0 fails (Prop. 4.2).
- **Computed** (every SAT witness re-checked by `aecheck.c`; solver cross-validated by `brute.py`):
  - **Exhaustive, n = 5, 7, 9** (8 / 354 / 47,354 AE instances):
    - AE holds at every instance;
    - the coordinator's form CF0 (b(w) = 2 at every non-leaf w ∈ N(g)) fails at 6 / 33 / 337 instances;
    - CF≤1 (at most one zero) holds at every instance.
  - **Random, n = 11** (7,274 + 98,056 instances; 61,357 of the latter with t ≥ 2): AE and CF≤1 hold everywhere; CF0 fails at 1 + 10. The n = 13 sample is in `data/cf.txt` if it finished.
  - **Via EE**: AE at every instance of order ≤ 11, from prescribed-end's exhaustive EE run (59,688,458 pairs at n = 11).
- **Open:** AE with t = |N(g) ∩ N(c)| ≥ 2. This is exactly EE with ≥ 2 common neighbours, which prescribed-end and l1star reduce to the blocked case of L1*. CF≤1, which is stronger than AE, is also open.

## Contents

| Path | What |
|---|---|
| `scripts/aesolve.c` | `conj-r/scripts/lnsolve3.c` plus the constraint `T w x` (the path ending at w does not have terminal edge wx) |
| `scripts/aecheck.c` | `conj-r/scripts/wcheck.c` plus `T`; independent witness checker |
| `scripts/brute.py` | independent brute force (no shared code), for validation |
| `scripts/gen.c` | copy of `conj-r/scripts/gen.c` (all graphs of order N) |
| `scripts/cfgen.py` | AE / CF0 / CF1 query lines from a graph6 list |
| `scripts/cfrun.py` | exhaustive AE, CF0, CF≤1 over a graph list, with witness checking, by common-neighbour count t |
| `scripts/randae.py` | random AE instances of order N with t ≥ 2 |
| `scripts/tegen.py` | terminal-edge queries TE(L, g, x): `even` (x the even vertex: AE), `odd` (x odd: fails, as PEE does) |
| `data/cf.txt` | all CF / AE results (exhaustive n ≤ 9, random 11 and 13) |
| `data/validation.txt` | solver vs brute force; TE at odd neighbours |
| `data/axioms.txt` | `#print axioms` for the headline theorems |

## Reproduce (from a scratch directory)

    gcc -O2 -o gen scripts/gen.c; gcc -O2 -o aesolve scripts/aesolve.c; gcc -O2 -o aecheck scripts/aecheck.c
    for N in 5 7 9; do ./gen $N > all$N.g6; python3 scripts/cfrun.py all$N.g6 ./aesolve ./aecheck "n = $N"; done
    python3 scripts/randae.py 11 20000 111 > r11.g6; python3 scripts/cfrun.py r11.g6 ./aesolve ./aecheck "random n = 11"
    python3 scripts/cfgen.py cf1 < all7.g6 > q.txt; python3 scripts/brute.py < q.txt    # cross-check

The scripts read `manuscripts/ln/scripts/lnlib.py` (graph6 decoding) by relative path.
