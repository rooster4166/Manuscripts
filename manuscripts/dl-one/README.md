# DL(1): the disjunctive avoidance conjecture for one pair — cloud session `claude/dl-one`

Manuscript: `dl-one.tex` (compile with `pdflatex` twice). Lean: `lean/GallaiLean/DLOne.lean`.
Experiment log: `research/experiments.md`, E31.

## Status
- **DL(1) is not proved.** Modulo L1* (open; it would settle a ∉ N(g) or b ∉ N(g)), the open core is a, b ∈ N(g), d(a), d(b) ≥ 3, every neighbour of g adjacent to a or b, and d(g) ≥ 4 or (d(g) = 2 and a second common neighbour; 1,108 of the 1,430 non-twin core pairs with d(g) = 2 through order 9, all good).
- **Proved and formalised** (no `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound` only):
  - `univTwins_every_path`, `not_triangleDisj_of_twins`: universal twins lie on every path (the exception is needed; connected form);
  - `leaf_exchange`, `not_paired_adj` (Lemma NP: all-odd graph, x ~ y, d(x) ≥ 3 ⇒ some Lovász decomposition with Q(x) ≠ Q(y));
  - `avoid_leaf`, `disjL1_leaf`: DL(1) when a is a leaf at g;
  - `avoid_deg_two`, `disjL1_deg_two`: DL(1) when d(g) = 2 and g is the only common neighbour of a, b;
  - `avoid_free_target`, `disjL1_free_target`: Case I across a target adjacent to neither a nor b carries each orientation, hence the disjunction (same disjunct).
- **Proved on paper only:** the child of a free target is never twin; Corollary 6.2 second part (d(g) = 2, N(g) independent ≠ {a,b}); Corollary 7.2 (smallest counterexample); Proposition 9.5 (Conjecture SF ⇒ DL(1) when g is the only common neighbour).
- **Verified by computation:** DL(1) fails exactly at universal twins for every connected graph with one even vertex of order 5, 7, 9, 11 (failures/pairs: 3/21, 14/947, 170/166,217; order 11: 12,516/268,990,425 over 11,959,367 graphs, per-slice summaries in `data/n11_slices.txt`). Every non-twin pair to order 9, and every non-twin pair of the order-11 slices 17 and 517 (178,755 pairs, `data/n11_certificates.txt`), is certified by the proved transfer calculus (independent of the exact solver).
- **Conjectures with data:** N (fixed orientation, neighbour condition), N2 (set form), CN1 (both orientations in one decomposition when g is the only common neighbour and d(a), d(b) ≥ 3), and **SF**, the single missing step for that case: G − ga has a decomposition separating a, b whose path at b does not end next to a (10,916/10,916 at order 9; SF ⇒ DL(1) there, Prop. 9.5).
- **Residual:** DL(1) is not an inductive hypothesis for Case I (`FsOrg`); separation + Fan to a fails (`FsPzw`); the N2 class does not close (`DCw`, `DEk`); full separation fails at one common neighbour (118/118 at orders ≤ 7, only 14 with a degree-two reason, e.g. `FsPIW`). Audit: `research/audit/A29-dl-one.md`.

## Reproduction (scripts/)
Requirements: gcc, g++, Python 3 with networkx, nauty (`nauty-geng`).
```
cd scripts
gcc -O2 -o dl dl.c ; gcc -O2 -o enum enum.c
g++ -O2 -I ../../l1-induction/scripts -o dlrec dlrec.cpp
O=../../stl/scripts
cat $O/one_even_5.g6 $O/one_even_7.g6 > oe57.g6
python3 brute.py oe57.g6 3000000 > brute57.txt ; ./dl < oe57.g6 > dl57.txt
python3 compare.py dl57.txt brute57.txt                    # 942 pairs, 0 mismatches
./dl -m sum < $O/one_even_9.g6                             # order 9: 166,217 pairs, 170 fail = 170 twins
./dl -m pairs < oe579.g6 > pairs579.txt ; python3 stats.py pairs579.txt   # §8 structure statistics (oe579 = orders 5,7,9)
for k in 5 7 9; do ./dlrec BMS < $O/one_even_$k.g6 | tail -1; done   # certificates
./run11.sh 0 3 OUT & ./run11.sh 1 3 OUT & ./run11.sh 2 3 OUT &        # order 11 (2000 geng slices; hours)
nauty-geng -c 11 17/2000 | ./dlrec BMS | tail -1                       # order-11 certificates, one slice (filters to one even vertex)
./dl -m sets -k 2 < $O/one_even_9.g6 | tail -1             # Conjecture N2, |A| <= 2
./dl -m nmax < $O/one_even_9.g6 | tail -1                  # N2 maximal form and L1* local form
./dl -m both < $O/one_even_9.g6 | tail -1                  # CN1 both orientations at once
./dl -m sepfar < $O/one_even_9.g6 | tail -1                # Conjecture SF
./dl -m sep1 < oe57.g6 > sep1.out ; python3 sep1_reason.py sep1.out   # §10.4 full separation
python3 exp1.py oe57.g6 | tail -1                          # robustness of Case I targets
python3 exp3.py oe57.g6 | tail -1 ; python3 exp4.py oe57.g6 ; python3 exp5.py oe57.g6 | tail -1
for n in 5 7; do python3 closure.py $n | tail -1; done     # N2 class closure
```

| File | Content |
|---|---|
| `dl.c` | exact solver: modes `pairs`, `core`, `sum` (order-11 driver), `sets`, `nmax`, `both`, `sep1`, `sepfar`; `-q` interleaves the two orientations |
| `brute.py` | independent brute force over transition systems |
| `enum.c`, `dllib.py` | enumerate all Lovász decompositions; forced Fan transfer; checks |
| `dlrec.cpp` | DL certificates from the proved transfer calculus (`moves.h` of l1-induction) |
| `exp1.py`–`exp5.py`, `closure.py` | the strategy experiments of manuscript §10 |
| `stats.py`, `sep1_reason.py` | §8 statistics and the §10.4 count (from audit A29) |
| `run11.sh` | order-11 exhaustive driver (`nauty-geng -c 11 i/2000 | dl -m sum -q`) |
| `../data/` | order-11 slice summaries and the two certified slices |
