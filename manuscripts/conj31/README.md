# Conjecture 31: profile form, block criterion, joint paths (session `claude/conj31`)

Manuscript `conj31.tex` / `conj31.pdf` (working draft). Lean: `lean/GallaiLean/Conj31.lean`, `lean/GallaiLean/Conj31Up.lean`.
Builds on `manuscripts/endpoint-structure` §5 (the two-even problem, Conjecture 31) and `manuscripts/conj-r`
(Conjecture J).

**Status.** Conjecture 31 is **not** proved. Conjecture J and Conjecture AE are **not** proved. AE was not attempted.

## Proved

**In Lean** (no `sorry`; full library build green, 18,450 jobs; axioms `propext`, `Classical.choice`,
`Quot.sound` only, see `data/axioms.txt`):
- `tight_iff_realisesProfile`.
- (DB) is necessary: `degree_add_le_sum_of_realises`.
- (DB) fails only at a vertex adjacent to everything: `universal_of_not_degreeBound`.
- The moves TR (Fan transfer), NEW, SUP and TRI, realisation step: `realisesProfile_transfer`, `_newPath`, `_suppress`, `_tri`.
- **PC ⇒ Conjecture 31**: `conj31_of_profileConj`.
- Upward closure, by splitting a path at an interior vertex: `realisesProfile_up`, `realisesProfile_of_le`.
- **PC with ≤ 1 zero**: `realisesProfile_of_no_zero` and `realisesProfile_of_one_zero`. Any graph without isolated vertices; the one-zero version needs even order.

**On paper:**
- PC with ≤ 1 zero at every order.
- PC reduces to minimal profiles, i.e. to "Ev∖{u,v} realisable for every pair" plus the (O1) boundary.
- The moves CYC, EAR, SPL, TW2, DOWN, and the output conditions of all moves.
- A minimal counterexample to PC is irreducible.
- Gluing at cut vertices is exact, so PC ⇒ (BC ⇒ realisable).
- PC + Conjecture P ⇒ Conjecture J.

## Computed

Solver `scripts/psolve.h` (exact). Every positive answer has a witness re-checked by `scripts/wcheck31.py`
or `scripts/jwcheck.py`, which share no code with the solvers. The exceptions are noted in the manuscript.

| Claim | Scope | Data file |
|---|---|---|
| Conjecture 31, exhaustive | Order 10: 799,993 two-even 2-connected graphs without a universal odd vertex, all tight | `data/conj31_order10.txt` |
| Reproduces the census of endpoint-structure §5 | Orders 4–8 | `data/census_le8.txt` |
| PC, two zeros | n ≤ 8: 6,849,521 (DB) profiles, all realisable | `data/pc_le8.txt` |
| PC, ≤ 1 zero (check of a theorem) | n ≤ 8: 14,297,554 profiles | `data/pc_le1zero.txt` |
| BC ⟺ tight for every connected two-even graph | n ≤ 10. At n = 10: 1,114,873 graphs, 0 disagreements | `data/bc_census.txt` |
| Conjecture J: a joint path with an (L), (C) or (B) remainder | Every joined instance at orders 6, 8, 10 (374; 40,538; 20,151,960). All certified remainders exactly tight; 20.2M joint decompositions checked | `data/jcert_le8.txt`, `data/jcert_order10.txt` |
| Conjecture 31 alone (C) plus (L) | Covers only 26,611 of the 40,538 joined instances at order 8 and 14,890,194 of the 20,151,960 at order 10 | as above |
| Irreducible instances | Two zeros, n ≤ 8: 366 with all moves, 355 of them with twin zeros. None with ≤ 1 zero | `data/irreducible.txt` |

## Open

- **PC** (Conjecture 3.1); its core is the twin case.
- **Conjecture 31**.
- **Conjecture P** (path choice): every joined instance has a joint path whose remainder satisfies BC.

## Contents

| Path | What |
|---|---|
| `scripts/psolve.h` | Exact solver: path decomposition with a prescribed end profile (memoised DFS, sound pruning). |
| `scripts/t31.c` | Conjecture 31 (`c31`) and the census (`census`) over a graph6 stream. |
| `scripts/pc_test.c` | PC: every zero set of size `MAXZ` ∈ {0, 1, 2}, every profile, (DB) vs realisability. |
| `scripts/stuck.c` | Irreducible PC instances under the moves (option `down` adds DOWN). |
| `scripts/blockcrit.h`, `scripts/bc_census.c` | Block criterion BC; BC vs exact tightness. |
| `scripts/jcert.c` | Conjecture J: joint paths with an (L), (C) or (B) remainder, exact check of the remainder, witnesses. |
| `scripts/wcheck31.py`, `scripts/jwcheck.py` | Independent witness checkers, with their own graph6 decoder. |
| `data/*.txt` | Outputs as listed above; `data/axioms.txt` (`#print axioms`), `data/build.txt`. |

## Reproduce (scratch directory; needs `nauty-geng`)

    gcc -O2 -o t31 scripts/t31.c; gcc -O2 -o pc_test scripts/pc_test.c; gcc -O2 -o stuck scripts/stuck.c
    gcc -O2 -o bc_census scripts/bc_census.c; gcc -O2 -o jcert scripts/jcert.c
    for i in 0 1 2 3; do nauty-geng -Cq 10 $i/4 | ./t31 c31 w10_$i.txt; done        # Conjecture 31, order 10
    python3 scripts/wcheck31.py w10_*.txt
    nauty-geng -Cq 8 | ./pc_test 2 99 pw8.txt; python3 scripts/wcheck31.py --profile pw8.txt   # PC, n = 8
    nauty-geng -cq 10 | ./bc_census                                                   # BC vs tightness
    nauty-geng -cq 8 | ./jcert jw8.txt bc; python3 scripts/jwcheck.py jw8.txt         # Conjecture J, order 8
    nauty-geng -Cq 8 | ./stuck 2 down                                                 # irreducible instances

The order-10 runs were sharded with `geng res/mod` over 4 cores. Witness files (up to 1.5 GB) are
regenerable and are not committed. For the J runs, the all-odd graphs are `nauty-geng -cq 10` filtered by
degree parity (32,851 graphs).
