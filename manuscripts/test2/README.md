# test2: the three-end test (T2) of the spine

Session `claude/test2`. Manuscript: `test2.tex` / `test2.pdf` (working draft; audited in A37, `research/audit/A37-test2.md`, fixes applied).

## Contents so far

| Path | What |
|---|---|
| `scripts/t2.c` | Exact solver for (T2). Search core copied verbatim from `manuscripts/eulerian-cone/scripts/re.c` (audit A30); new: rooted search with e ends at r, filters, driver. |
| `scripts/verify_t2.py` | Independent witness checker (path partition of J − z, ≤ n/2 paths, ≥ 3 ends at r, parity of J). |
| `scripts/bf_t2.py` | Independent brute force (exact cover by listed paths) for slack / (T2) / emax, small graphs. |
| `scripts/tb2.py` | The (T2) forest base: search with `tools/route_ext.c` (query C), lift executed and verified in Python. |
| `scripts/tb2_pm.py` | The (T2) matching base, per perfect matching of J[N(z)]. |
| `data/t2_order6_8.txt` | Every instance at orders 6, 8, with witnesses and emax. |
| `data/t2_order10_fields.txt.gz` | Every instance at order 10 (fields only; rerun `t2 -E -B 20000000` for witnesses). |
| `data/tight_le10.txt` | The 20 tight instances (p(J − z) = n/2) at order ≤ 10, with witnesses. |
| `data/forestbase2_order8.txt`, `data/matchingbase2_order8.txt` | Base searches at order 8. |
| `data/t2_slack_witnesses.txt` | Slack-witness check at n ≤ 10 (`t2 -s` into `verify_t2.py --require-slack`). |
| `data/axioms.txt` | `#print axioms` for the Lean lift. |
| `scripts/tb2_floor.py` | The floor lift (B − Φ with w the only even vertex), per instance or per matching data choice. |
| `scripts/coverage.py`, `scripts/dz4_cover.py`, `scripts/lit_cover.py` | Reach of the proved tools: packed sets (separation / L1 / NA set forms), d(z) = 4 by separation or two-token schedules (port of trn steer2.cpp), Pyber/Fan floor conditions. |
| `scripts/allodd_pairs.py`, `scripts/cones.py`, `scripts/gen_t2.py` | Conjecture 7.2 (all-odd, two constraints); cone instances; random order-12 generator. |
| `data/forestbase2_order10*`, `data/floorbase_*`, `data/dz4_*`, `data/coverage_*`, `data/lit_cover_*` | Outputs of the above. |
| `data/t2_order12_sample*` | 20,000 random order-12 graphs, 40,000 instances. |
| Lean | `lean/GallaiLean/Test2Lift.lean`: lifts (`test2At_of_forestBase2`, `test2At_of_floorBase`, `floor_of_matchingBase`), `test2At_of_floor`, `test2At_of_disjL1`, d(z)=4 (`test2At_of_pair_farApart`, `test2At_of_pair_steer2`). `lean/GallaiLean/Test2Converse.lean`: converses, matching case (`matchingFloorBase_of_terminal`, `forestBase2_matching_of_terminal`). |

## Reproduce

    gcc -O2 -o t2 scripts/t2.c
    nauty-geng -q -C -d3 10 | ./t2 -E -B 20000000 > t2_10.out     # (T2) at every instance, order 10
    python3 scripts/verify_t2.py < t2_10.out                        # witness check
    python3 scripts/tb2.py ROUTE_EXT < instances                     # forest base + lift check

Line format of t2.c: `g6 z r d(z) d(r) n slack t2 emax | witness |` (with `-s`, followed by ` S | slack witness |`), where slack = [p(J − z) ≤ n/2 − 1],
t2 = [(T2) holds], emax = most ends at r over decompositions with ≤ n/2 paths (−e: ≥ e, search cut off;
−1: not computed).

## Data (exhaustive: every 3-connected J of order n ≤ 10 with exactly two even vertices z ~ r; both orientations)

| n | graphs | instances | (T2) holds | tight (p(J − z) = n/2) |
|---|---|---|---|---|
| 6 | 5 | 10 | 10 | 2 |
| 8 | 474 | 948 | 948 | 5 |
| 10 | 358,492 | 716,984 | 716,984 | 13 |

All 717,942 (T2) witnesses verified by `verify_t2.py`; all 717,922 slack answers (p(J − z) ≤ n/2 − 1)
carry witnesses (`t2 -s`) verified by `verify_t2.py --require-slack` (`data/t2_slack_witnesses.txt`). In every tight instance J − z is an odd semi-clique
K_{2k+1} − H with e(H) < k (tightness then follows by edge counting). Order 8: the forest base exists at
all 948 instances (685 by a perfect matching of J[N(z)], 263 by a spanning-tree T-join), every lift
verified; every one of the 1,512 perfect matchings of J[N(z)] gives a matching base.
