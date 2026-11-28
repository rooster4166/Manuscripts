# L_N(2): the multi-tail leaf theorem and pre-committed end paths (session `claude/ln`)

Manuscript `ln.tex` / `ln.pdf` (working draft). Lean: `lean/GallaiLean/LeafTails.lean`.
Audit: `research/audit/A40-ln.md`.

**Status.** L_N(2) is **not** proved. Proved: Theorem A (multi-tail leaf theorem, Lean) and
Corollary B (Lean); Lemma R (paper). Computed: Criterion R at order 8 (exhaustive) and on a sample at
order 10, every certificate executed and checked. Conjectured: MTL2, Conjecture R.

## Contents

| Path | What |
|---|---|
| `scripts/lnsolve.c` | Exact DFS for parity decompositions with constraints: `A t a` (path ending at `t` avoids `a`), `S p q` (no common path), `J p q` (one path with ends `p, q`), `R v k` (end count). Failure memo, node budget. |
| `scripts/lnlib.py` | graph6, witness checker `check_witness`, independent brute force `brute` (exact cover by all simple paths). |
| `scripts/validate.py` | Cross-check of `lnsolve` against `brute` on random instances. |
| `scripts/gen_ln2.py` | L_N(2) instances (connected all-odd graphs, unordered pairs of disjoint ordered pairs). |
| `scripts/gen_mtl2.py`, `gen_mtl2b.py`, `gen_mtlk.py`, `gen_g11.py` | Instances of the leaf-tail statements (two tails; sets; one leaf tail plus one general tail). |
| `scripts/sched.py`, `scripts/sched3.py` | Multi-token schedules (moves M, D, S) for two / any number of tails, fin `mtl2`, `sparse` (Theorem A) or `old`. |
| `scripts/joint_sched.py` | Lemma R(a): a c1–c2 path P avoiding a1, a2 with a free token schedule in F − E(P). |
| `scripts/precommit.py` | First version of Criterion R (search only). **Superseded by `routeR.py`**: it allowed P to end at a_j, which breaks the multi-token invariant (found by the executor, see below). |
| `scripts/routeR.py` | Criterion R with an independent executor: replays the moves, solves the bottom exactly with `lnsolve`, undoes the moves (Fan's forced chain, drop, subdivision), checks every level and the final Lovász decomposition. |
| `scripts/allodd_filter.c` | graph6 filter: all degrees odd. |
| `scripts/two_even_exist.py`, `gen_ev3.py`, `rand_ev3.py`, `rescue.py`, `adj_fail.py`, `find_r1.py`, `resid_mtl.py` | Side experiments (two-even existence, residual analysis of the MTL2 induction). |
| `data/axioms.txt` | `#print axioms` for the Lean headline theorems. |
| `data/mtl2_exhaustive.txt` | Conjecture MTL2, exhaustive n ≤ 9. |
| `data/coverage_order8.txt` | Coverage of the routes at order 8. |
| `data/routeR_order8.txt`, `data/routeR_order10_sample.txt` | Criterion R certificates (per instance: route, P, number of moves), executed. |
| `data/validation.txt` | `validate.py` output. |

## Reproduce

    gcc -O2 -o lnsolve scripts/lnsolve.c
    nauty-geng -cq 8 | python3 scripts/gen_ln2.py > ln2_8.txt
    python3 scripts/routeR.py ./lnsolve < ln2_8.txt > routeR_order8.txt
    gcc -O2 -o allodd_filter scripts/allodd_filter.c
    nauty-geng -cq 10 | ./allodd_filter > allodd10.g6     # 32,851 graphs; sample as in ln.tex §7
    python3 scripts/validate.py ./lnsolve 8 1500 2

Raw intermediate outputs are regenerable and are not committed, except the certificate lists.
