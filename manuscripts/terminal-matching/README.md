# Two terminal edges at once (PTM) — cloud session `claude/ptm`

Manuscript: `terminal-matching.tex` (compile with `pdflatex` twice). Lean: `lean/GallaiLean/TerminalMatching.lean`;
axiom check `PTMAxioms.lean` (`cd lean && lake env lean ../manuscripts/terminal-matching/PTMAxioms.lean`).
Experiment log: `research/experiments.md`, E24. Conclusions: `research/connections.md`, §Z. Audits: `research/audit/A22-ptm.md`, `research/audit/A22b-localgirth.md` (local girth five).

## Status
- **Proved and formalised** (sorry-free; only propext, Classical.choice, Quot.sound; full `lake build` green):
  - `walk_back`: restoring a path edge by edge with Fan's lemma, tracking vertex sets.
  - `ptm2_of_base` (walk theorem): two terminal edges from a separation problem in a base graph with one even vertex.
  - `sep_sparse_fix`, `ptm2_of_sparse`: the base from `separation_sparse`, with one exceptional vertex.
  - `ptm2_girth5`: PTM₂ with one prescribed end for every all-odd graph of girth ≥ 5 (reachability between the edges suffices).
  - `stl_of_ptm2`, `stl_of_girth5`, `test1_of_girth5`: the STL / Test1 consequences at d(z) = 4, through `test1_of_stl`.
- **Audit A22**: no error in any proof; corrections to claims applied (STL citation numbers, K₄ caveats, the base problem has genuine NOBASE failures, EE needs a non-adjacent complementary pair).
- **Audit A22b** (local girth five, Theorem 6.1 and Corollary 7.2 local forms): sound, no error; every excluded short cycle passes through an end of the two edges; `NoShortCycleAt` proved equivalent to Mathlib's cycle-length form (`A22b-scripts/A22bSemantics.lean`). Statement-level wording fixes applied.
- **Open.** PTM₂ beyond the sparse case (the base problem alone is not enough: 832 NOBASE instances at n = 8); PTM_m for m ≥ 3; the multigraph case (Conjectures 2.3, 2.4).
- **Counterexamples.** K₄ with a perfect matching (PTM₂); the prism with its rungs (PTM₃, G − F disconnected).

## Reproduction (`scripts/`)
Requirements: gcc, Python 3 with networkx, nauty (`nauty-geng`, `nauty-labelg`).
```
cd scripts
gcc -O2 -o ptm ptm.c; gcc -O2 -o walk walk.c; gcc -O2 -o encode encode.c
for n in 4 6 8; do for m in 2 3 4; do nauty-geng -cq $n | ./ptm s $m > out/s_${n}_${m}.txt; done; done   # E24(A)
for n in 4 6 8; do nauty-geng -cq $n | ./ptm p 0 > out/pc_$n.txt; done; python3 analyze.py out/pc_8.txt # E24(C)
for n in 6 8 10 12; do nauty-geng -ctfq -d1 $n | ./ptm s 2 0 0 > out/g5_${n}_2.txt; done              # E24(D)
nauty-geng -cq -d1 10 | <filter all-odd> > out/odd10.g6; ./run_n10.sh 2                              # E24(B)
./run_random.sh                                                                                        # E24(E)
nauty-geng -cq 8 | python3 gen_pairs.py > out/pairs_8.txt; ./walk 0 < out/pairs_8.txt; ./walk 0 1 < out/pairs_8.txt  # E24(F)
python3 und_rerun.py out/rnd_*.out > out/rnd_und.in                                                  # E24(E), re-run:
for m in 2 3 4; do awk -v m=$m 'NF==1+2*m' out/rnd_und.in > out/rnd_und_$m.in; ./ptm f $m 5000000 0 < out/rnd_und_$m.in > out/rnd_und_$m.out; done
./run_multi.sh                                                                                         # E24(G)
./run_extra.sh                                                                                         # E24(H), walk extra=2
```
`ptm` usage and modes are documented at the top of `ptm.c`; `walk` at the top of `walk.c`.
