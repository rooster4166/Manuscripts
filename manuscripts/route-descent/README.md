# Route descent

`route-descent.tex` / `route-descent.pdf` (13 pages): route descent for the transversal realisability conjecture TRC, minimum T-joins, route-respecting realisations as constrained Lovász decompositions, and the separation theorem for Lovász decompositions.

No proof in the manuscript depends on computation. The scripts below produced the evidence in its section "Conjectures and their status" and in `research/experiments.md` E20.

## Lean

All files are in `lean/GallaiLean/`. They are sorry-free, use only the standard axioms, and the full library builds.

- `RouteDescent.lean`:
  - `gallai_of_pairingTRC`, `gallai_of_pairingTRCExists`, `branchBase_of_rootedHalfSets` (Prop. "existential form and the Lean spine");
  - `IsEvenPairing.of_isPairing` (the `cs_all` pairings qualify);
  - `isMinTJoin_sdiff`, `isMinTJoin_of_two_mul_card_le` (Lemma "minimum T-joins" (4), (5));
  - `realisable_of_even_matching` (Theorem "Fan-isolated routes", one-edge routes);
  - `PathDecomp.route_append` (Lemma "extension", (i) ⇒ (ii): the inductive step of route descent).
- `FanSupport.lean`: `fan_single_supp`, `fan_grouped_supp`, `fan_exec_supp` (Lemma "Fan's lemma with vertex sets").
- `Separation.lean`: `separation_set` (Theorem "separation", packed sets), `separation` (two vertices), `lovasz_avoid` (Corollary "L₁ at distance three").

## Oracle

`tools/route_ext.c` is an exact realisability oracle (n ≤ 32, m ≤ 128). Its query types:

| Query | Meaning |
|---|---|
| `P` | is the profile realisable? |
| `X` | realisable with the path at `c` avoiding a set? |
| `C` | route-respecting realisation |
| `A` | per-end avoidance sets |
| `S` | no path contains both vertices of any listed pair |
| `W*` | witnesses for the above |
| `B` | budgeted randomised search; answer 2 means undecided |

`scripts/rd_lib.py` compiles it on first use. `scripts/validate_oracle.py` checks it against `tools/realis.c` and against a brute force over all path partitions: `python3 validate_oracle.py 300`, then the arguments `C` or `A` for those queries.

## Scripts (`scripts/`)

| Script | Purpose |
|---|---|
| `rd_lib.py` | oracle interface, partition checker, Thm 21 construction (tree or minimum T-joins, random linked transitions), route-respecting test |
| `families.py` | test families: order-12 EMM counterexamples, G₁₈, G₂, G_bad (n = 28), Kotzig even-degree graphs G′(prism), G′(Petersen), random graphs, block trees |
| `trc_test.py FAMILY cons maxT seed` | TRC, extension step and heredity checks. Environment: `TJOIN=min`, `RR=1` / `RR=only`, `BUDGET`, `FINAL=0`, `COUNT`, `PMIN`, `PMAX`, `TAG`, `PROGRESS` |
| `stuck_analysis.py FILE` | classifies stuck instances (trivial obstruction) and tests re-routing |
| `exist_test.py n count cons` | existential form of the extension step |
| `lovasz_matching.py trials nmax [budget]` | conjecture L_N, random partial matchings |
| `ln_perfect.py trials budget nmin nmax` | L_N for perfect matchings (the Eulerian case) |
| `l1_search.py MODE trials` | L₁ and its one-even-vertex variant |
| `msep3.py trials budget` | multi-pair separation at distance ≥ 3 |
| `sep2.py trials budget` | separation at distance 2 (fails often) |
| `unlinked.py n count budget` | minimum T-joins with unlinked transitions (linking is needed) |

Logs are in `scripts/outputs/`.
