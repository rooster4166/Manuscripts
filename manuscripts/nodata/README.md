# nodata: roots without matching data in the spine tests

Session `claude/nodata`. Manuscript: `nodata.tex` / `nodata.pdf` (working draft). Lean:
`lean/GallaiLean/NoData.lean` (no `sorry`; every theorem depends only on `propext`,
`Classical.choice`, `Quot.sound`; the full library builds).

## Lean (`NoData.lean`)

| Theorem | Content |
|---|---|
| `PathDecomp.twin_insert` | two new vertices of degree two on the same two neighbours cost one path; ends change only at one twin (+2). From `cycle_insert` (eulerian-cone). |
| `theta_decomp`, `theta_rooted` | the theta graph with `2n` leaves has `n + 1` paths; rooted at a leaf with two ends there. |
| `test1_fatTheta` | Test1 on `K_{3,t} + h₂h₃` at `h₁`, every even `t ≥ 2`. |
| `test1At_of_twins`, `test2At_of_twins` | twin reductions for any `J`. |
| `ForestLN`, `CherryList`, `CherryLN`, `test1At_of_cherryLN` | the cherry conjecture CL and CL ⇒ Test1 at roots with cherry data. |
| `lN_of_cherryLN`, `test1At_of_LN_matching` | CL ⇒ `LN` (ConstrainedLovasz.lean); `LN` ⇒ Test1 at every root with matching data. |
| `fan_root_move`, `test1At_of_move1`, `test1At_of_move2`, `test1At_of_move1'`, `test1At_of_move2'`, `delVert_eq_delList` | the root moves M1, M2 (MR Thm 145's one-edge steps), from `fan_single`. |

## Scripts

| Path | What |
|---|---|
| `scripts/ndsolve.h` | exact constrained Lovász solver (route-respecting masks = route_ext query C). |
| `scripts/nd.c` | classification of no-data roots: Gallai–Edmonds data, twins, triangle data, tiers 1–5 of all-odd bases with witnesses. Flags: `-t1`/`-t2`, `-b` (input B = J − z), `-a` (also roots with data), `-x` (no 3-connectivity / δ filter), `-U`/`-UU` (universality: every structure), `-D` (dump solver queries for cross-checks). |
| `scripts/ndq.c`, `scripts/gen_cq.py` | query-C line interface and random queries, for cross-checking `ndsolve.h` against `tools/route_ext.c`. |
| `scripts/verify_nd.py` | independent check of every base and lift (networkx). |
| `scripts/xcheck_tiers.py` | independent check of the negative tier claims (networkx linkages + route_ext). |
| `scripts/twin_cert.py` | certifies tier 4–5 roots by the twin reduction, executed and verified. |
| `scripts/rootmove.py`, `scripts/rootmove2.py` | root moves to matching data (single M1 paths; closure of M1, M2). |
| `scripts/fl.c`, `scripts/oddfilter.c` | abstract forest-L_N families on all connected all-odd graphs. |
| `scripts/star_hall.py` | the star Hall condition (H1) against outcomes. |

## Data (`data/`)

| File | What |
|---|---|
| `nd_t1_le9.txt` | every (T1) no-data root, n ≤ 9 (8,112), with witnesses. `verify_t1_le9.txt`, `xcheck_t1_le9.txt`: checks. |
| `nd_t2_le10.txt.gz` | every (T2) no-data root, n ≤ 10 (197,067). `verify_t2_le10.txt`, `xcheck_t2_le10.txt`. |
| `nd_t1_11_summary.txt`, `nd_t1_11_agg.txt` | (T1) order 11, all 8,738,914 graphs (three slices of `nauty-geng -C 10 i/3`); aggregates by deficiency, d(z), twins. The full output (12.8M lines, 1.5 GB) is not committed; `nd_t1_11_ge2.txt.gz` has every root of tier ≥ 2 (147,070). `verify_t1_11_ge2.txt`, `xcheck_t1_11_ge2.txt`, `verify_t1_11_sample.txt` (2.5% random sample of tier 1). |
| `twincert_t1_le9.txt`, `twincert_t1_11.txt` | the 9 + 75 roots of tier 4–5, certified by the twin reduction. |
| `rootmove_t1_le9.txt`, `rootmove_t1_le9_perroot.txt`, `rootmove_t1_11_ge3.txt` | root-move closure. |
| `univ_t1_le9_summary.txt`, `univ_t1_le9_tier2_failures.txt`, `star_hall_t1_le9.txt` | universality at n ≤ 9 and the Hall analysis. |
| `fl_le8.txt.gz`, `fl_10_*.txt` | abstract families at orders 4–8 and 10. |
| `cells.tex` | numbers used in the manuscript. |

## History of the code (for the auditor)

* The first version of the linkage enumerator in `nd.c` reused one path buffer across recursion
  levels, so recorded linkages could be corrupted. That gave label-dependent false negatives in tiers
  1–2: an early n ≤ 9 run reported 7,082 / 636 / 347 at tiers 1 / 2 / 3. It was fixed to per-depth
  buffers (commit ff51181 has the fixed code), and every number in the manuscript is from the fixed
  code. The two input modes (direct J, and B = J − z) now agree exactly.
* `ndsolve.h` first lacked the degree bound `d_R(v) ≤ 2P − need(v)` and the per-component edge
  bound, which made some searches explode. Adding them changed running times, not answers.
* The universality mode `-U` first stopped a root's tier-3 enumeration at the first linkage that
  was a base (an unguarded early return; audit A41, F17), so its tier-3 counts covered only part of
  the structures. It is fixed (`!univ` guard), and `univ_t1_le9_summary.txt` and
  `star_hall_t1_le9.txt` are from the fixed code: 278,296 of 1,239,486 tier-3 structures fail.
  Tiers 1, 2 and 4 were unaffected.
* Later, after the `nd.c` data runs, `ndsolve.h` was given a fail-first branching order
  (constrained vertices first) and a larger failure memo (2^22). That made the order-10 runs of
  `fl.c` feasible. It is exact either way. Re-running `nd -t1` on n ≤ 9 with the new header gives
  identical levels and excesses (md5 of the level columns agrees). The order-10 `fl` runs use the
  new header; the order ≤ 8 `fl` runs agree with it up to the number of exact searches.

## Reproduce

    gcc -O2 -march=native -o scripts/nd scripts/nd.c
    gcc -O2 -march=native -o scripts/fl scripts/fl.c
    gcc -O2 -o scripts/oddfilter scripts/oddfilter.c
    (for n in 5 7 9; do nauty-geng -q -C -d3 $n; done) | scripts/nd -t1 > nd_t1_le9.txt
    for i in 0 1 2; do nauty-geng -q -C 10 $i/3 | scripts/nd -t1 -b > t1_11_$i.txt; done
    (nauty-geng -q -C -d3 6; nauty-geng -q -C -d3 8; nauty-geng -q -C -d3 10) | scripts/nd -t2 > nd_t2.txt
    python3 scripts/verify_nd.py < nd_t1_le9.txt
    python3 scripts/xcheck_tiers.py ROUTE_EXT < nd_t1_le9.txt
    python3 scripts/rootmove2.py 6 -p < nd_t1_le9.txt
    nauty-geng -q -c 10 | scripts/oddfilter > odd10.g6; scripts/fl -f kp < odd10.g6
