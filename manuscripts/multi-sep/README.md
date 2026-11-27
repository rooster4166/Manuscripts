# Multi-pair separation (MSEP) — cloud session `claude/multi-sep`

Manuscript: `multi-sep.tex` (compile with `pdflatex` twice). Lean: `lean/GallaiLean/MultiSep.lean`.
Experiment log: `research/experiments.md`, E21. Conclusions: `research/connections.md`, §W.
Audit: `research/audit/A18-multi-sep.md`.

## Status
- MSEP (and its class version CSEP) is **open**. There is no counterexample, and the evidence is strong (E21).
- Proved, sorry-free in Lean:
  - leaf merge;
  - prescribed end edge in all-odd graphs (with a packed set);
  - Case II reduction for class separation;
  - certified Case I step;
  - sparse class separation (generalises `separation_set`).
- Proved in the manuscript only: the reduction to Gallai, covers, Case I ⟺ end-edge prescription, and the rotation lemma.

## Reproduction (scripts/)
Requirements: Python 3 (networkx not needed), gcc, nauty (`nauty-geng`).
```
cd scripts
gcc -O2 -o cubsep cubsep.c && gcc -O2 -o route_ext ../../../tools/route_ext.c
python3 validate_cubsep.py                         # checker vs independent enumerator (285 agree)
for n in 10 12 14 16; do nauty-geng -cq -d3 -D3 $n | ./cubsep all 0; done     # exhaustive cubic MSEP
nauty-geng -cq -d3 -D3 18 | ./cubsep rand 200 1   # 8,260,200 random pairings at n = 18
python3 search_general.py 3000 11 pair 12 20 2000000 > out/gen_pair.txt   # random all-odd graphs
python3 randlov.py out/gen_pair.txt               # certify undecided instances
python3 exp_sqcol.py 14 150 1 1 5000000 cubic     # CSEP, minimum colourings of the square
python3 exp_conflict.py 12 3 3 1 2000000          # union of three pairings: failures
python3 exp_ee.py 300 1 3000000 0                 # Conjecture EE without classes
python3 exp_cl.py 14 200 2 1 3000000              # EE in Case I configurations (cubic)
python3 coarsen_fail.py 10                        # certified strategy: exhaustive failures
python3 rotate.py 12 "" 2 10                      # rotation strategy
python3 exp_twoend.py 300 2 2000000 4             # prescribed end edges on packed sets
```
Other scripts (`exp1.py`, `exp2.py`, `exp_inv.py`, `exp_csepf.py`, `exp_p2.py`, `exp_eeall.py`,
`exp_se.py`, `kotzig.py`, `exp_extremal.py`, `exp_min2.py`, `hardness.py`, `dense_search.py`,
`strat_rreg.py`, `exp_elov.py`, `exp_strat.py`, `exp_classes.py`) are the tests listed in E21. `msl.py` is the
pure-Python library: graphs, enumeration of Lovász decompositions, Fan chains.
