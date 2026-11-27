# A12 scripts

Independent checks for audit A12 (`manuscripts/missing-move`, and `manuscripts/endpoint-structure` §7).
The game solver `game.py` and the certificate replayer `cert_replay.py` were written for this audit and share
no code with `manuscripts/missing-move/scripts/` or `tools/`. Exact partition checks (`partitions.py`) reuse
the audit's own DFS solver `../A11-scripts/exact.py`. Run from this directory with `nice -n 15 python3 ...`
(networkx needed). Outputs are in `out/`; `out/author_reruns/` holds re-runs of the author's
`fan_game.py`, which are not independent.

| script | checks | output |
|---|---|---|
| `game.py` | the Fan game of missing-move Def. 1.1: single and grouped transfers (adversarial donor), one-edge and multi-edge new paths, Lovász and Lemma-4 seeds; options split rule, receipt-or-flower (Lemma 5.9, written from the statement), orbit rule. A state's value is the exact set of winning roots | library |
| `cert_replay.py` | parses every printed strategy tree in `outputs/certificate*.txt` and recomputes, in the current graph, every supply and blank count, the seed, every donor branch, every new path and every end state | `out/cert_replay.txt` |
| `sweep.py` | least held-set size per root over a graph6 file, held sets up to Aut(G) | `out/sweep8_np_k4.txt`, `out/sweep8_nonp_k4.txt`, `out/least47_k5to9.txt`, `out/least_sparse40_split.txt`, `out/split47_k4.txt`, `out/losers5_nonp*_k8.txt`, `out/conn6_nonp_k4.txt` |
| `k8pm.py` | K8 − PM: the printed \|F\| = 9 certificate set; every held set of size ≤ 8 loses at every root, \|F\| = 9 wins (held sets up to the 384 automorphisms) | `out/k8pm.txt` |
| `gqz_original.py` | Gqz~vw at root 3: path insertion needs \|F\| = 5; the original game loses with \|F\| ≤ 8 | `out/gqz_original.txt` |
| `partitions.py` | criticality of the 47 (`crit`), endpoint-structure Example 53 (`ex53`) | `out/crit47.txt` |
| `es7_checks.py` | ES Remark 54 (GsaEDo), Remark 56 (all 70 half-sets of M8 realisable) | `out/es7_checks.txt` |
| `hubrun.py`, `hubruns.sh` | order 10, held sets "a star plus k edges": B′, A_{6,2}, Inv~\|~zbw, A_{4,4}, B (no rf) | `out/hubruns.txt`, `out/hubruns_A44_B.txt` |
| `rf_check.py`, `rf_checks.sh` | Prop 5.10 with the independent rf implementation, with and without the orbit rule | `out/rf_checks.txt`, `out/rf_inv.txt` |

`run_all.sh` reproduces everything (about an hour on one core; the criticality check of the 47 is the slow part).
