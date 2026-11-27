# Prescribed end edges (PEE / EE) — cloud session `claude/ee`

Manuscript: `prescribed-end.tex` (compile with `pdflatex` twice). Lean: `lean/GallaiLean/PrescribedEnd.lean`, `lean/GallaiLean/PrescribedEndOutside.lean`.
Experiment log: `research/experiments.md`, E23. Conclusions: `research/connections.md`, §Y.
Audit: `research/audit/A21-pee.md`.

## Status
- **PEE away from the even vertex z is false.** Smallest counterexample: 5 vertices (Proposition 3.1).
- **EE (uz terminal at u) is a theorem when u and z have at most one common neighbour**, for every d(u). Hence also for d(z) = 2 in every configuration. This contains multi-sep EE3 and the d(z) = 2 cases of STL. Lean: `sep_atMostOneCommon`, `ee_atMostOneCommon`, `ee_deg_two`.
- **Protected-end lemma.** A Fan transfer with target g keeps xy terminal at x when x ∉ N(g) or y = g. Consequences:
  - EE implies PEE at every "reachable" edge xy (some z–y path with interior outside N[x]).
  - Unconditionally, PEE holds when y ∈ N(z) and x, y have at most one common neighbour other than z. Lean: `pee_adjEven` (k = 1).
- **Open: EE when |N(u) ∩ N(z)| ≥ 2.** It reduces to the avoidance conjecture L1* (Corollary 7.4; Lean `ee_of_L1Star`), via the triangle reduction (`ee_of_triangle`) and the outside-neighbour reduction (`ee_of_outside`).
- No counterexample to EE:
  - exhaustive to n = 11 (n = 11: 11,959,367 graphs, 59,688,458 pairs (z, u));
  - 25,962 random tests at n = 11–17.
- Audit A21 found no error or gap; its fixes are applied.

## Reproduction (scripts/)
Requirements: gcc, Python 3 with networkx, nauty (`nauty-geng`).
```
cd scripts
gcc -O2 -march=native -o pee pee.c
nauty-geng -cq 7 | python3 brute.py                 # oracle vs transition-system brute force (n <= 7)
for n in 5 7 9; do nauty-geng -cq $n | ./pee g6 > out/exh$n.txt; done   # PEE, all edges
for i in 0 1 2; do nauty-geng -cq 11 $i/3 | ./pee g6 z > out/ee11_$i.txt & done   # EE only, n = 11
python3 analyze_fail.py out/exh9.txt                 # failure features; reverse prescription
python3 block_check.py out/exh9.txt                  # every failure is unreachable
nauty-geng -cq 9 | ./pee g6 w | python3 sharp.py     # reachable vs unreachable, all away edges
cp pee pee2 && nauty-geng -cq 9 | ./pee2 l1p all     # L1 with an even vertex (g ~ a vs not)
nauty-geng -cq 9 | ./pee2 l1s2                       # |A| = 2 avoidance; triangle-lemma hypothesis
nauty-geng -cq 7 | ./pee2 sepee                      # separation of u, z in K - uz, by |N(u)∩N(z)|
gcc -O2 -o pee3 pee.c && nauty-geng -cq 7 | python3 tri_sep.py   # separating w from {u, z}
gcc -O2 -o route_ext ../../../tools/route_ext.c
nauty-geng -cq 9 | python3 xcheck_route_ext.py ./route_ext       # vs independent oracle
python3 rand_test.py 6000 101 5000000 11 13 15 17 > out/rand_A2.txt   # prints each away failure with reachability
nauty-geng -cq 11 0/100 | ./pee g6 w > out/exh11_slice0of100_w.txt   # residue 0 mod 100 of order 11, all edges (we ran the first 84,002 graphs: out/exh11_slice0of100_prefix.txt.gz)
./regen.sh                                           # regenerates the validation and Section 7 outputs
```
`pee`, `pee2` and `pee3` are the same source; separate copies let long runs continue while the source changes.

| File | Content |
|---|---|
| `pee.c` | exact oracle. Modes: `g6` (all edges, or `z` = EE only, `w` = per-edge verdicts), `ed`, `edq` (generic queries: PEE, avoidance, separation), `l1p`, `l1s2`, `sepee` |
| `brute.py` | independent brute force (transition systems) |
| `xcheck_route_ext.py` | cross-check against `tools/route_ext.c` (queries X and S) |
| `analyze_fail.py`, `feat.py`, `block_check.py`, `sharp.py` | structure of the failures |
| `tri_sep.py` | the stronger "separate w from {u, z}" invariant (fails) |
| `rand_test.py` | random graphs, orders 11–17 |
| `out/` | outputs; `exh11_away_partial_fails.txt.gz` holds the away failures of a partial n = 11 run (initial segment of each of three geng slices) |
