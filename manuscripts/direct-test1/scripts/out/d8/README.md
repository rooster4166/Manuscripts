# d(z) = 8, n = 13: triangle-base run (coordinator)

- `run13_d8.log`: `dtl2.py ORACLE 11 20 13 8` at a 3·10⁶ node budget per query.
  - The run was stopped by a time limit during graph 9.
  - Results: 64 roots of 8 complete graphs, 43 bases found and lift-verified, 0 lift failures. In addition, 7 roots of the 9th graph are "NO BASE" lines.
- `nobase13.txt`: the 28 "NO BASE" lines. All of them are budget-undecided.
- `recheck13_30M.log`: the 3·10⁷ recheck (`recheck.py`), stopped once superseded: 21 FOUND and 1 UNDECIDED.
- `witnesses13.txt`: clt's `tb_ls.py` (exact DFS, small budget, then local search) on all 28 lines.
- `verify13.log`: the independent check `../../verify/vw_gen.py`. It confirms that D0 is Lovász on M, that the disjunctions hold, and that the executed lift satisfies (T1).
  - **28/28 verified.**

So every root tested at d(z) = 8, n = 13 has a triangle base: 71 roots, 0 failures.
