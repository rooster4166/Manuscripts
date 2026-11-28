# Neighbour avoidance (NA): cloud session `claude/na`

Manuscript: `na.tex`. Compile with `pdflatex` twice. Lean: `lean/GallaiLean/NeighbourAvoid.lean`.

**NA** (conj-n Conjecture 4.2, Lean `NeighbourAvoidOn`).
- Setting: G has no even vertex, x ~ y, and y has a neighbour w ≠ x with w ≁ x.
- Claim: some Lovász decomposition has x ∉ Q(y).

## Status
- **NA is proved, and the proof is formalised.** There is no `sorry`. The axioms are `propext`, `Classical.choice` and `Quot.sound`. The full library builds (18,420 jobs).
  - **Theorem A** (`avoid_packed_of_reach`), the set form. Hypotheses:
    - Y is packed and y ∉ Y is odd;
    - the component of y in G − Y is not contained in N(Y).

    Conclusion: some Lovász decomposition meets Y at most once per path, with Q(y) ∩ Y = ∅. This extends L1 (`lovasz_avoid_set`), which needs y ∉ N(Y).
  - **NA** (`neighbourAvoid`, `neighbourAvoidOn`) is Theorem A with Y = {x}. The single-vertex form under the weak hypothesis is `avoid_of_reach`.
  - **Theorem C, the exact boundary** (`mem_pathEndingAt_of_component_sub`, `avoid_iff_reach`). For distinct x, y with y odd, Q(y) can avoid x **if and only if** the component of y in G − x contains a vertex not adjacent to x. The set form is sharp too (`meets_of_component_sub`, `avoid_packed_iff_reach`), among decompositions meeting Y at most once.
  - **Consequences for Conjecture N:**
    - `conjNDegTwoOn`: the degree-two case of N holds;
    - `conjN_of_tightTransferN`: TRN ⇒ N;
    - `conjN_of_TR`: TR ∧ `TightTransferAdj` ⇒ N.
- **Proof idea.** Hang a leaf ℓ at y, so that y becomes the only even vertex, and set X = Y ∪ {ℓ}.
  - Run Lovász's Case I from y with every target outside X. Fan's lemma with vertex sets keeps "every path meets X at most once" up the chain.
  - Because ℓ is a leaf, the target may be y itself. Move (b) of the conj-n calculus forbids that target, and the wheel `EUZw` needs it.
  - The chain is steered by a parity lemma until the even vertex disappears. The steering uses a farthest odd vertex t of y's component in G − Y, toggled shortest paths, and a walk along the resulting subgraph.
  - At the bottom of the chain there is no even vertex, and L1 applies.
- **Checked against the R1 and R2 reformulations:**
  - R1 is a correct sufficient condition. The proof does not use it.
  - R2 is equivalent to a stronger statement: Q(y) ∌ x and xy terminal in Q(x). It held in all NA instances of orders 4, 6 (brute force, `r2check.py`) and 8 (4,970/4,970, exact, `r2exact.py`). It is not proved.
- **Audit:** `research/audit/A-na.md` (fresh referee). It graded every proof SOUND. The errors it found were in the surrounding text and the unfilled §8 table; they are fixed.

## Computation (`scripts/`, outputs in `data/`)
| file | content |
|---|---|
| `nalib.py` | The proofs as an algorithm: Fan's lemma (general chain), the separation theorem (Cases I–IV), L1, Lemmas 4.1/4.3 as written, and a second, independent steering routine (T-join + Euler trail), plus an independent verifier (`check_lovasz`, `check_na_output`). |
| `exact.py` | Exact decision of "Q(y) avoids X" (memoised path search), and `brute_all`, an enumeration of all transition systems used to validate it. |
| `run_na.py` | Runs over `nauty-geng` output, every ordered pair x ~ y. Options: `--exact`, `--exact-neither`, `--brute`, `--sets`, `--trailbf`. |
| `random_na.py` | Random all-odd graphs of order N (G(N,p) with a parity repair), construction for every pair, and a random packed Y. |
| `r2check.py`, `r2exact.py` | The R2 strengthening, by brute force (orders 4, 6) and by the exact solver (order 8). |

Commands:
```
cd scripts
for n in 4 6; do nauty-geng -cq $n | python3 run_na.py --exact --brute --sets --trailbf; done
nauty-geng -cq 8 | python3 run_na.py --sets > ../data/n8.txt
for i in 0 1 2; do nauty-geng -cq 8 $i/3 | timeout 2700 python3 run_na.py --exact-neither --progress > ../data/n8_exact_neither_$i.txt; done
for i in 0 1; do nauty-geng -cq 10 $i/2 | python3 run_na.py > ../data/n10_$i.txt; done
for n in 12 14 16 20; do python3 random_na.py $n 1000 $n; done > ../data/random.txt
for sl in 17 517; do nauty-geng -cq 12 $sl/20000 | python3 run_na.py --sets > ../data/n12_slice${sl}of20000.txt; done
nauty-geng -cq 6 | python3 r2check.py
nauty-geng -cq 8 | python3 r2exact.py > ../data/r2_n8.txt
```
Requirements: Python 3 and nauty (`nauty-geng`). The exact numbers are in the manuscript, §8.
