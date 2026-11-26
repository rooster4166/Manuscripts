# jm-repair

`jm-repair.tex` / `jm-repair.pdf`: a repair of the extension step (Theorem 8, Claim 12) in
Javadi–Miralaei, "A conjecture on rainbow Hamiltonian cycle decomposition" (arXiv:2403.17290;
Discrete Math. 349 (2026) 114676). It also gives the corrected transfer lemma for their
Theorem 7 (gap JM1 in `research/audit/A4-semi-cliques-JM.md`, §2) and writes Theorem 7 out in
full.

Status summary (Section 11 of the manuscript has the precise version):

- **Proved here.** Theorem A, i.e. JM Theorem 8 under the hypothesis r ≤ 2t − 1. Its core is
  Theorem B, a two-vertex extension lemma, proved via a flow network, Hoffman's circulation
  theorem and a counting/parity argument.
- **Consequence.** Wu's conjecture follows from Theorem A, JM Theorem 7 (with the corrected
  transfer lemma), and the theorems of Hilton (1984), Hoffman (1960) and Liu–Chen (2023).
  These three results are used without proof. We did not check the proof of Liu–Chen.
- **Not done.** This is a single, unrefereed re-derivation. JM's Claim 12 itself is not
  repaired; the new argument replaces it.

`scripts/` contains the sanity checks. None of them is part of any proof.

| Script | What it checks |
|---|---|
| `lf.py` | Shared utilities. |
| `solvers.py` | Shared CP-SAT and flow solvers. |
| `test_random.py`, `test_adversarial.py`, `test_flow_large.py` | Theorem B three ways: direct search, flow, cut conditions. |
| `test_noUbound.py` | That some bound on \|U\| is needed (violating 2\|U\| ≤ k − 2 can make Theorem B fail; the bound itself is not shown to be optimal). |
| `check_valid_lemma.py` | Exhaustive check of Lemma 5.1. |
| `check_colour_lemmas.py` | The per-colour inequalities. |
| `pipeline.py` | End-to-end construction for Theorem A. |
| `check_thm7_counts.py` | The counts in JM Theorem 7. |
| `independent/` | An internal referee agent's own direct-search checks (no flows or records), including the \|U\|-size probe. |

Logs are in `data/`. To reproduce, run e.g. `cd scripts && python3 pipeline.py 11 40`. The
scripts need `networkx` and `ortools`.
