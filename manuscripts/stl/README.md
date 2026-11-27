# Star-terminal Lovász decompositions (STL) — cloud session `claude/stl`

Manuscript: `stl.tex` (compile with `pdflatex` twice). Lean: `lean/GallaiLean/StarTerminal.lean`;
axiom check `STLAxioms.lean`. Experiment log: `research/experiments.md`, E22. Conclusions:
`research/connections.md`, §X. Audit: `research/audit/A20-stl.md`.

## Status
- **Proved and formalised.** Sorry-free; `#print axioms` shows only propext, Classical.choice, Quot.sound; full `lake build` green.
  - `star_delete`: delete z from a star-terminal decomposition, with exact end counts.
  - `test1_of_stl`: STL ⇒ Test1.
  - `test2_of_stl2`: STL2 ⇒ Test2.
  - `gallai_of_stl`: STL + STL2 on 3-connected graphs ⇒ Gallai, via `gallai_iff_spineTests'`.
  - `stl_of_deg_two`, `stl_of_deg_two_tri`: STL for d(z) = 2 in two cases, by direct separation arguments.
  - `stl_deg_two`: STL at every vertex z of degree 2, from `ee_deg_two` (claude/ee).
- **Proved in the manuscript only:**
  - the general criterion #LL − #SS + [r short] ≤ 0 (BAL / BAL2);
  - the J − z characterisation of STL;
  - the cone proposition: "some star-terminal Lovász decomposition exists" for all J with J − z connected ⇒ Gallai;
  - d(z) = 2 ⇔ EE;
  - pairing ⇔ terminal matching;
  - Examples W₄ (STL-P fails) and the K₄-bowtie (ST fails).
- **Open.** STL (Conjecture), STL2, STL-P for 3-connected J ≠ W₄. No counterexample with J − z connected is known (E22).

## Reproduction (`scripts/`)
Requirements: Python 3 with networkx, gcc. The oracle is compiled automatically by `common.build()`
from `tools/stl.c` (binary `scripts/stl`, ignored by git).
```
cd scripts
python3 brute.py 7                    # oracle vs brute force: ST/STL/BAL (1,066 queries)
python3 brute_flex.py                 # oracle vs brute force: short sets / pairings (1,295 queries)
python3 gen_one_even.py 9 > one_even_9.g6          # 11,936 graphs (also 5, 7)
python3 stl_run.py one_even_9.g6 out/fail_9.jsonl  # (A) STL/BAL/Test1, n = 9 (13 min)
python3 stl2_run.py ../../../data/conn8.g6 out/fail2_8.jsonl   # (B) STL2, n = 8
python3 sample_run.py 1 13 300 1302 gnp 4000000 out/s1_13_gnp.jsonl   # (C) mode 1 = STL, 2 = STL2
python3 resolve.py out/s1_13_gnp.jsonl out/s1_13_gnp.res.jsonl       # re-decide budget-undecided
python3 flex_run.py one_even_9.g6 out/flex_9.jsonl                    # (D) EE/STS/HALF/PAIR
python3 families.py univ 12 30 8 out/fam_univ12.jsonl                  # (E) families (also wheel, zconn, zdisc)
python3 ptm_run.py 10 2 300 102 2000000 out/ptm_10_2.jsonl           # (F) PTM / PEE_m: composition
```
Outputs: `scripts/out/` (`fail_*.jsonl`: every failure with its Test1 verdict; `run_*.txt`, `*.log`:
summaries; `s1_*`, `s2_*`: samples; `flex_*`: flexibility; `fam_*`: families).
