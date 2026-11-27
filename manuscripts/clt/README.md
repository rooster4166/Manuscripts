# Constrained Lovász decompositions (session `claude/clt`)

Manuscript `clt.tex` (in progress), Lean `lean/GallaiLean/ConstrainedLovasz.lean`, experiments E29
in `research/experiments.md`, conclusions in `research/connections.md` §AE.

## Scripts (`scripts/`)
* `enum.c` — enumerates **all** Lovász decompositions of small graphs (graph6 on stdin).
  `-v L` prints, per graph, the inclusion-minimal violation sets over the atoms
  av(c,a) (path ending at c avoids a) and ne(u,v) (paths ending at u, v differ);
  `L = 0` all av atoms, `1` a ∉ N[c] ∪ N(g), `2` a ∉ N[c]; `-E -v 5`: graphs whose even vertices
  are pairwise at distance ≥ 3, with separation atoms.
* `trans.c` — exact search for unsatisfiable constraint systems of a prescribed shape (minimum
  hitting sets of the violation family), e.g. `trans bip1 8 < v1_8.txt`.
  Shapes: any, in1, func, lin, match, out1, star, bip, bip1, bipx, bipx2 (av atoms);
  pmatch, pdeg2, comp (separation atoms); options `ne`, `net`, `tdeg=`, `hdeg=`, `gdeg=`.
* `clt_lib.py` — graph6, the exact solver interface (`manuscripts/t6-dense/scripts/lsearch.c`,
  compiled to `$LSEARCH`, default `/tmp/claude-0/lsearch`), witness checker.
* `rand_clt.py` — random tests of the maximal forms (star, bip1, bip1ne, bipx, lnmatch).
* `t_l1ee.py` — L1* local form at c together with EE at a neighbour of g.
* `lsls.py` — local search (k-path re-decomposition) for dense instances where the DFS stalls.
* `t6probe.py`, `t6all.py` — the t6 append base for every labelling of residual graphs.

## Regenerating
```
gcc -O2 -o /tmp/claude-0/enum enum.c; gcc -O2 -o /tmp/claude-0/trans trans.c
gcc -O2 -o /tmp/claude-0/lsearch ../../t6-dense/scripts/lsearch.c
for n in 4 5 6 7 8; do nauty-geng -cq $n | /tmp/claude-0/enum -v 1 > v1_$n.txt; done
for s in bip1 bipx; do /tmp/claude-0/trans $s 10 < v1_8.txt | tail -1; done
python3 rand_clt.py bip1 14 300 14 2000000
python3 t6all.py 20000 3000 < resid_C4.g6      # graphs from ../../t6-dense/scripts/gen_resid.py
```
Raw outputs are regenerable and are not committed.
