# Papers

Standalone papers consolidated from the working notes in `manuscripts/` and the Lean library in
`lean/GallaiLean/` (plan and standard: `../CONSOLIDATION.md`). Each paper has its own directory
`Pk-<slug>/` with `paper.tex`/`paper.pdf`, a claim map in `README.md`, the Lean entry file
`lean/Pk.lean` with `axioms.expected`, `scripts/`, `data/`, `SHA256SUMS` and `reproduce.sh`.

Check all papers against the library: `scripts/check_papers.sh` (from the repository root; one
paper: `scripts/check_papers.sh P1`).

One row per paper; each paper's session edits only its own row.

| # | Title | Status | Depends on | Directory |
|---|---|---|---|---|
| P1 | A machine-checked reduction of Gallai's path decomposition conjecture to two rooted tests on 3-connected graphs | Complete: all results proved in the text and in Lean (standard axioms only); audit A45 | — | [`P1-spine/`](P1-spine/) |
| P2 | Constrained Lovász decompositions: separation, neighbour avoidance, leaf tails and prescribed ends | In preparation (wave 1) | P1 (Lovász, Fan) | — |
| P3 | Reversible lifts from constrained Lovász decompositions to the spine tests | In preparation (wave 1) | P1, P2 | [`P3-reversible-lifts/`](P3-reversible-lifts/) |
| P4 | Rooted Gallai for Eulerian graphs, and the two-end test at near-universal roots | Planned (wave 2) | P1 (§9) | — |
| P5 | Endpoint structure of path decompositions at the Gallai budget | Planned (wave 2) | P1 | — |
| P6 | Exact path decompositions below the Dirac threshold | Planned (wave 2) | — | — |
| P7 | Repairs of three lemmas used in the Gallai literature | Planned (wave 2) | — | — |
