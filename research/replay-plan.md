# Independent replay plan for load-bearing computations

None of the collection's code, certificates or Lean files is in this repository. Until a computation is replayed by independent code, every claim that depends on it is conditional.

The table lists the computations the main lines of argument depend on, with a priority and a feasibility estimate. "Replay" means regenerating the case list from the paper's definitions and re-deciding each case with our own exact solver (`tools/pathnum.py`). Replaying the authors' certificates is not enough.

| # | Computation | Feeds | Size | Feasibility | Priority |
|---|---|---|---|---|---|
| R1 | MR §6–7 contact-order classification: 8 contacts, unique bad order 03476125, links 12, 34, 67 doubled; 1,320 path and 202 cycle templates | MR Thms 2, 3; block-degree §6; the whole cycle-absorption line | small | High: each template is a two-path partition test on ≤ 30 edges | **1** |
| R2 | 485 thin-pair classes (MR Thm 3, "at most one with exactly five") | MR Thms 2, 3 | small | High | 1 |
| R3 | six-even-root-shapes: the 66 fixed-root patterns and the isolated-root list (32,661 of 32,768 cores pass) | the whole d = 6 program | 2^15 cores × tests | Medium: needs the paper's exact test list (Lovász, Fan, Botler–Sambinelli) | **1** |
| R4 | six-even-incidence: \|S(x)\| ∈ {1, 2} certificates (396 and 990 inputs) | d = 6 | small | High | 2 |
| R5 | MR Thm 124 seven-site certificate (1,044 classes, 10,906 graphs) | MR Thms 128, 130 (three-end test at d = 8) | medium | Medium | 2 |
| R6 | block-degree Thm 4: 25,003 three-path configurations and 1,154 boundary certificates | block-degree Δ ≤ 8, Δ ≤ 9, cutwidth 8, Thms 7–13 | medium | Medium: needs the §10.2 definitions | 2 |
| R7 | block-degree §13: about 4.86M degree-9 placements | Δ ≤ 9 only | large | Low priority: Δ ≤ 7 and Δ ≤ 8 come first | 4 |
| R8 | cycle-and-contact twelve-contact catalogue: 1,509 exceptions in 9,985,920 orders | Thm 1 (12 cycles) | large | Medium (C++) | 3 |
| R9 | separating-pairs Thm A.1 (2,832 patterns) and Thm 13.34 (2^9 terminal graphs) | Cor 4.4; the odd witness | small | High | 2 |
| R10 | odd-semi-clique-boundary Thm 11, k < 130 (17,507 triples; 629,462 quadruples) | exact endpoint sets on semi-cliques | medium | High (arithmetic) | 3 |

## Conclusion-level checks

These test the final statements on all small graphs, whatever the proof. They are independent of the authors' certificates, and they catch errors in statements, though not in proofs.

| Check | Status |
|---|---|
| Rooted test p(B + leaf) ≤ \|B\|/2, all connected B, \|B\| ≤ 6 | done; no failures |
| Same at \|B\| = 8 (11,117 graphs; includes every six-even instance of order 8) | running |
| Floor bound outside semi-cliques, n ≤ 7 | done (via the CP and descent runs); no failures |
| Floor bound outside semi-cliques, n = 9 (261,080 graphs) | planned. This covers block-degree Thm 1 and MR Thm 144 at order 9. |
| MR Thm 144 form (odd W with a leaf and exactly 5 even vertices), \|W\| ≤ 11 | planned; generate the class directly |
| Three-connected deletion tests (MR Thm 114), \|J\| ≤ 11 | planned |
