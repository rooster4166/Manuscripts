# Conjecture R: joint end paths, static steering, gluing, and the residual (session `claude/conj-r`)

Manuscript `conj-r.tex` / `conj-r.pdf` (working draft). Lean: `lean/GallaiLean/LemmaR.lean`,
`lean/GallaiLean/JointR.lean`. Builds on `manuscripts/ln` (Lemma R, Criterion R, Conjecture R).

**Status.** Conjecture R and L_N(2) are **not** proved.

- **Proved, Lean** (no sorry; standard axioms, `data/axioms.txt`):
  - Lemma R (`lemmaR`, `lemmaR_leaf`), Criterion R ⇒ good (`ln2_of_criterionR`), Conjecture R ⇒ L_N(2) (`ln2_of_conjR`).
  - Joint cases: ≤ 1 even vertex or a leaf (`joint_of_card`, `joint_of_leaf`), suppression (`joint_of_supp`), and static steering. For the last, a steering sequence is a two-token schedule (`steerK_of_steer`, `joint_of_steer`, `joint_of_inv`).
  - Leaf at the other head ⇐ AE (`ConjAE`, `ln2_of_leaf_at_head`).
- **Proved on paper:**
  - Lemma S: an exact T-join criterion for static steering.
  - Theorem G: gluing at a cut vertex, cases G1–G3.
  - Proposition 9.2: Criterion R3 ⇒ L_N(3).
- **Computed:**
  - Conjecture J (joint form) at every joined instance of orders 6, 8 and 10: 374, 40,538 and 20,151,960 instances, every witness re-checked by `wcheck.c`.
  - Conjecture AE: exhaustive for n ≤ 9, and on 292,838 derived order-10 instances.
  - Coverage and residual at orders 6 and 8 and on the order-10 sample.
  - Criterion R on the order-10 separated residual (31,897, executed).
  - m = 3 at order 8.
- **Conjectured:** J, AE.

## Contents

| Path | What |
|---|---|
| `scripts/gen.c` | Graphs up to isomorphism (vertex addition + individualisation–refinement canonical form); `gen N oddc` gives the connected all-odd graphs of order N. |
| `scripts/lnsolve3.c` | `ln/scripts/lnsolve.c` with joint-pair branching and a degree bound (both keep the search exhaustive). |
| `scripts/wcheck.c` | Independent witness checker for solver output (A, S, J, R constraints). |
| `scripts/pscan.py`, `pall.py` | Single-edge P, and every P, with exact Lemma R hypothesis (lnsolve) and schedules (routeR.search). |
| `scripts/an1.py`, `an4.py`, `an5.py`, `an7.py`, `an8.py` | Summaries of the order-8 path data (single edges, all paths, joint rules, obstruction classes). |
| `scripts/jall.py`, `mkJ.py` | Conjecture J, exhaustive over a graph list; splits off the separated instances. |
| `scripts/cov.py`, `tjoin.py`, `allcov.py`, `cov2.py` | Proved conditions: static-steering trail search, Lemma S's T-join test, union coverage and residual. |
| `scripts/sepcov2.py`, `sepcls.py`, `g3p.py`, `leafD.py`, `aeq.py`, `aegen.py` | Separated case: gluing classes, AE queries (derived and exhaustive). |
| `scripts/m3.py`, `r3.py` | m = 3: exact L_N(3) and joint extension; Criterion R3 with executor. |
| `scripts/val3.py`, `val3b.py`, `val3c.py` | Cross-validation of lnsolve3 against lnsolve. |
| `data/conjJ_exhaustive.txt` | Conjecture J at orders 6, 8, 10. |
| `data/single_edge_order8.txt`, `all_paths_order8.txt`, `caseA_order8.txt` | Which P work at order 8. |
| `data/coverage.txt`, `residual_order6.txt`, `residual_order8.txt`, `residual_order10_sample.txt` | Coverage of the proved conditions and the residual lists. |
| `data/tjoin_vs_trail.txt` | Lemma S's criterion against the exact trail search (62,530 cases, all agree). |
| `data/separated.txt`, `separated10_criterionR.txt`, `routeR_order6.txt` | Separated case classes; Criterion R certificates (order-10 separated residual; all of order 6). |
| `data/conjAE.txt` | Conjecture AE. |
| `data/joint_ends_order8.txt` | Joint ends without avoidance at order 8. |
| `data/m3_order8.txt`, `m3_J3_failures_order8.txt`, `m3_R3_certificates.txt` | m = 3. |
| `data/validation.txt`, `data/axioms.txt` | Solver, generator and checker validation; `#print axioms`. |

## Reproduce (from a scratch directory)

    gcc -O2 -o gen scripts/gen.c; gcc -O2 -o lnsolve3 scripts/lnsolve3.c; gcc -O2 -o wcheck scripts/wcheck.c
    gcc -O2 -o lnsolve ../ln/scripts/lnsolve.c
    ./gen 10 oddc > odd10c.g6                      # 32,851 graphs
    python3 scripts/jall.py odd10c.g6 ./lnsolve3 ./wcheck 2000000 J10    # Conjecture J, order 10 (about 2.5 h on 4 cores)
    ./gen 8 oddc > odd8c.g6; python3 ../ln/scripts/gen_ln2.py < odd8c.g6 > inst8.txt
    python3 scripts/pall.py ./lnsolve -int < inst8.txt > pall8.out       # every P at order 8 (exact)
    python3 scripts/cov2.py inst8.txt residual_order8.txt                # coverage and residual
    python3 scripts/m3.py odd8c.g6 m3_J3fail8.txt                        # m = 3 (expects ./lnsolve3, ./wcheck)

Raw intermediate outputs (`pall8.out` is 91 MB) are regenerable and are not committed.
