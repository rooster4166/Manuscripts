# Lovász's induction for L1* — cloud session `claude/l1-induction`

Manuscript: `l1-induction.tex` (compile with `pdflatex` twice). Lean: `lean/GallaiLean/L1Induction.lean`.
Experiment log: `research/experiments.md`, E27. Conclusions: `research/connections.md`, §AC.
Audit: `research/audit/A25-l1-induction.md`.

## Status (audit A25 applied)
- **`L1Blocked` is not proved.** No candidate induction hypothesis closes.
- **Proved and formalised** (sorry-free, standard axioms):
  - `avoid_of_target_child` and `avoid_of_target_adj_child`: the Case I moves (b) and (c) transfer goodness *unconditionally* (stated for c ∉ N(g));
  - `l1Blocked_of_someTarget : TightTransfer → SomeTarget → L1Blocked`, hence `l1starGen_of_ST_TR`, `l1star_of_ST_TR`, `ee_of_ST_TR`, `lInfty_of_ST_TR`;
  - `l1Blocked_iff_tightTransferAdm`: given ST, L1Blocked ⟺ TR on admissible instances, so ST is the substantive half;
  - `l1Blocked_of_out_tight`: ST_out (a good *non-tight* target whenever one exists) plus the all-tight case N(g) ⊆ N(c) give L1Blocked;
  - `l1Blocked_of_someTargetLocal : SomeTargetLocal → L1Blocked`.
- **Proved on paper:**
  - the transfer calculus (Thm 3.1, per-move proof; it needs c ∉ A, now part of the definition of an instance);
  - walk to a degree-two vertex, a new reduction (Prop 3.3);
  - the exchange lemma at c (Lemma 4.2);
  - ST′ is false (Prop 4.8, order 7, `FEhv?`).
- **Conjectures with exhaustive support:**
  - **TR** (tight transfer): 1,735,156 tests to order 9, 1,097,584 of them with A meeting N(g); 0 violations. It fails if A may meet N(c).
  - **ST** (some target): all 135,188 blocked instances to order 9, every admissible A. **ST_out**: all 100,990 with a non-tight target.
  - On 4 of the 100 slices of order 11 (1,037,788 blocked instances, A = Amax) and on random orders 11–15: no failure, a few undecided.
- **Minimal obstructions** (manuscript Table 1):
  - ST′ (n = 7);
  - instance-level certificates: 6 stuck instances at n = 9;
  - certificate excursions: gap 5 at n = 8;
  - c-admissible dead ends (n = 5, `DEk` − 04).

## Reproduction (scripts/)
Requirements: g++, Python 3 with networkx, nauty (`nauty-geng`). Build each tool with `g++ -O2 -o NAME NAME.cpp`. `./regen.sh` rebuilds the tools and regenerates every short run; the long runs are listed at its end.
```
nauty-geng -cq 9 | ./rec2 adm MB      > out/rec_adm9_MB.txt     # Rec, Amax (also n = 10)
nauty-geng -cq 9 | ./rec2 adm MBT     > out/rec_adm9_MBT.txt    # Rec_T (TR targets)
nauty-geng -cq 9 | ./rec2 subsets MBT > out/rec_sub9_MBT.txt    # every admissible A
nauty-geng -cq 9 | ./rec2 stuck0 MB   > out/stuck0_9.txt        # stuck admissible instances
grep STUCK0 out/stuck0_9.txt | awk '{print $2,$3,$4}' | ./tt 2000000   # D-level tight transfer
./rec2 explore MBT < out/norec9T.g6 > out/explore9_MBT.txt      # stuck states below failures
nauty-geng -cq 9 | ./tr2       > out/tr2_9.txt                  # TR, every A (minutes)
nauty-geng -cq 9 | ./rechoice  > out/rechoice9.txt              # re-choice of D'
nauty-geng -cq 9 | ./stprime   > out/stprime9.txt               # ST and ST', every admissible A
nauty-geng -cq 9 | ./l1e                                        # L1E
nauty-geng -cq 9 | DUMP=1 ./targets > out/badtargets9.txt       # target census
nauty-geng -cq 9 | ./alltarget                                  # every-target form
nauty-geng -cq 8 | ./gap 6 ; nauty-geng -cq 7 | TR=1 ./gap 6    # certificate gaps
nauty-geng -cq 7 | ./minobs 6 4                                 # Case I dead ends
nauty-geng -cq 9 | ./walk2 0 10 ; nauty-geng -cq 9 | ./walk2 1 10   # walk census
nauty-geng -cq 7 | ./exch                                       # coverage of TR by lemmas
nauty-geng -cq 7 | ./trall                                      # TR sharpness (A arbitrary)
python3 randg.py 3000 27 11 13 | ./randtest 2000000 > out/rand_11_13_v2.txt
python3 randg.py 600 41 15     | ./randtest 2000000 > out/rand_15.txt
for n in 4 5 6 7; do nauty-geng -cq $n | ./xcheck2; done        # oracle cross-check
./example "FEhv?" 6 3,5                                         # Prop 4.8 decompositions
```

| File | Content |
|---|---|
| `lind.h` | graph type, graph6, exact avoidance oracle (port of `l1star/scripts/l1s.c`) |
| `orc2.h` | oracle with several constrained paths (and a disjointness mode) |
| `dec.h` | enumeration of good Lovász decompositions; exact forced Fan chain; decomposition checker |
| `moves.h`, `rec2.cpp` | the moves (a)–(i), (t) and the certificate class Rec; modes `adm`, `subsets`, `stuck0`, `explore`, `cert` |
| `rec.cpp` | first version of Rec (superseded by `rec2.cpp`; produced `out/rec_adm*_MB.txt`) |
| `tt.cpp` | D-level Case I step: every good D' of G − gu, forced chain, result |
| `tr2.cpp`, `trall.cpp` | TR with A ∩ N[c] = ∅; TR with A arbitrary |
| `rechoice.cpp`, `exch.cpp` | re-choice of D'; coverage by the proved lemmas |
| `stprime.cpp`, `l1e.cpp`, `l1e1.cpp`, `smove.cpp` | ST / ST′; L1E; one-instance L1E check; move (s) |
| `targets.cpp`, `alltarget.cpp` | target census; every-target form |
| `gap.cpp`, `minobs.cpp`, `walkadm.cpp`, `walk2.cpp` | certificate gaps; dead ends; TR-walks; walk to a degree-two vertex |
| `randg.py`, `randtest.cpp` | random graphs (one even vertex); ST, TR, L1E with a node budget |
| `xcheck2.cpp`, `example.cpp`, `qedge.cpp`, `dcstat.py` | validation; explicit decompositions; single-edge Q_c; tabulation |
| `out/` | outputs |
