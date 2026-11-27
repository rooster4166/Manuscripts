# Scripts for `t6-dense` (experiment E28)

Build the search engine once: `gcc -O2 -o lsearch lsearch.c`. You need Python 3 with `networkx`.
Raw outputs go to `out/`, which is git-ignored and can be regenerated.

## Files

| file | purpose |
|---|---|
| `lsearch.c` | Path decompositions with prescribed end counts, found by depth-first search with memoised failures (the engine of `tools/stl.c` and `walk3p.c`). Supported constraints: `sep` (separation), `ef` (the path ending at v avoids S), `ep` (forbidden end pairs), `es` (the end on p's side of the edge pq lies outside S). The input format is in the header comment. |
| `walksim.py` | Leaves, Fan transfers with the forced chain, the static predecessor check, the J-form un-lift, and an edge-by-edge check of decompositions. |
| `c4.py` | The C4 shape with the chained walk and one protected step. Modes: `sep` (the six separations of TM Thm 8.2, chains violating TM Def 8.1(ii), so the protected step is only executed), `end` (E1–E4 with Fan walks), `endA` (for this labelling exactly E1–E6). |
| `dense.py` | All five shapes, all roots, all labellings with x1y2, x2y3 ∈ E(B). Modes: `lean`, exactly the Lean hypothesis `AppendBase` (`endT` first, otherwise `leanE6`); `endT` (E1–E5, E7; Thm 2.2); `leanE6` (E1–E6; Thm 2.3); `endA` (E6 without its redundant clause w = y3, checked by execution); `endZ` (stronger than E6); `end` (E1–E4 with Fan walks, no theorem). See the docstring and manuscript §6. |
| `labstats.py` | For each root, counts the labellings that have a base. |
| `admissible.py`, `partial.py` | Which base conditions are L1*-admissible, and how often the inadmissible ones hold when they are not imposed. |
| `gen_core.py` | Sparse random J with a dense core (copied from `terminal-matching`). |
| `gen_resid.py` | Random 3-connected J with a dense core and the residual conditions of a smallest T(6)-i failure imposed. |
| `relabel.py` | Moves U = N(z) to the front of the vertex order and keeps the graphs with a dense core. Used on `terminal-matching/scripts/out/d6_9.g6`. |
| `equiv.py` | Prop 2.6 by exact search: an (E7)-base of M exists iff J has a star-terminal Lovász decomposition with transitions x_i z y_i and x1y2, x2y3 terminal at y2, y3 (audit A26 §2.1). |
| `stlp.py` | E28(B′): per labelling, (E7)-base, (E6)-base and STL-P for the oriented pairing. |
| `run_big.sh`, `run_lean.sh`, `run_lean2.sh` | The runs of E28. |

## Typical calls

```sh
python3 gen_resid.py 5 8 2 7 C4 > out/a.g6          # 5 residual-style C4 graphs, |O| = 8
python3 dense.py lean 2 2000000 < out/a.g6          # every root, Lean hypothesis
python3 relabel.py < ../../terminal-matching/scripts/out/d6_9.g6 > out/d6_9_dense.g6
python3 dense.py lean 1 0 < out/d6_9_dense.g6       # exhaustive order 9, exact search
python3 labstats.py 0 < out/d6_9_dense.g6           # labellings with a base, per root
```

Each `SUMMARY` line reports:
- `roots_ok`: roots with a certified base;
- `labs_tried`;
- `und`: searches that hit the node budget;
- `bad` and `notok`: bases whose executed construction did not verify; the expected value is 0.
