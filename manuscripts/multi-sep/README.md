# Multi-pair separation (MSEP) — cloud session `claude/multi-sep`

Manuscript: `multi-sep.tex` (compile with `pdflatex` twice). Lean: `lean/GallaiLean/MultiSep.lean`,
`lean/GallaiLean/MultiSepEE.lean`.
Experiment log: `research/experiments.md`, E21. Conclusions: `research/connections.md`, §W.
Audit: `research/audit/A18-multi-sep.md`.

## Status
- MSEP (and its class version CSEP) is **open**. There is no counterexample, and the evidence is strong (E21).
- Proved, sorry-free in Lean:
  - leaf merge;
  - prescribed end edge in all-odd graphs (with a packed set);
  - Case II reduction for class separation;
  - certified Case I step;
  - sparse sets: families of packed subsets of a sparse set separated at once (generalises `separation_set`);
  - Conjecture EE without classes at degree three (Proposition EE3: no triangle on uz; suppression +
    L1; triangle case), which covers the Case I step after one Case II step in a cubic graph.
- Proved in the manuscript only: parts (a), (b) of the reduction (part (c) is formalised), covers, Case I ⟺
  end-edge prescription with classes, the rotation lemma, and the corollary of the sparse theorem.
- Audit A18 (fresh subagent): no mathematical error; three computational descriptions corrected (see E21).

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
python3 validate_classes.py                       # cubsep classes mode vs oracle (150 agree)
for n in 10 12 14 16; do python3 cub_sqcol.py $n 1 1; done   # CSEP, minimum colourings of K^2, all cubic
python3 exp_sqcol.py 12 100 1 2 200000 rand       # CSEP, minimum colourings, random all-odd graphs
python3 exp_conflict.py 12 3 3 1 2000000          # union of three pairings: failures
python3 exp_ee.py 300 1 3000000 0                 # Conjecture EE without classes
python3 exp_cl.py 14 200 2 1 3000000              # EE in Case I configurations (cubic)
python3 coarsen_fail.py 10                        # certified Case I/II only: exhaustive failures
python3 rotate.py 12 "" 2 12                      # rotation only, every cycle length
python3 combined.py 10                            # all three certified moves interleaved (audit A18)
python3 exp_twoend.py 300 2 2000000 4             # prescribed end edges on packed sets
```
Other scripts (`exp1.py`, `exp2.py`, `exp_inv.py`, `exp_csepf.py`, `exp_p2.py`, `exp_eeall.py`,
`exp_se.py`, `kotzig.py`, `exp_extremal.py`, `exp_min2.py`, `hardness.py`, `dense_search.py`,
`strat_rreg.py`, `exp_elov.py`, `exp_strat.py`, `exp_classes.py`) are the tests listed in E21. `msl.py` is the
pure-Python library: graphs, enumeration of Lovász decompositions, Fan chains.
