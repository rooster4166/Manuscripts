# RE at roots of degree n − 2 (session `claude/re-tight`)

Manuscript `re-tight.tex` (compile with `pdflatex` twice). Lean: `lean/GallaiLean/RETight.lean`.
Background: synthesis §§26–28, `manuscripts/eulerian-cone` (Remark 7.2 is the reformulation used here).

## Status
- **Proved and formalised** (no `sorry`; only `propext`, `Classical.choice`, `Quot.sound`; full `lake build` green, 18,414 jobs):
  - `exists_decomp_of_degStar`, `rootedDecomp_of_degStar` (Theorem 3.1). Hypotheses: `B` has order `2k`, all degrees even, `d(r) = 2k − 2`. Let `h_t` be the number of neighbours of `r` of degree ≥ `2t`. Suppose that for every `3 ≤ t ≤ k − 1`, `⌊h_t/2⌋ ≤ k+1−t` or `⌊h_{t+1}/2⌋ ≤ k+1−2t`. Then `B` has exactly `k` paths with exactly two ends at `r`. No connectivity is needed, and `d(s)` is free.
  - `rootedDecomp_of_few_heavy` (Cor 3.3(a)): at most five neighbours of `r` have degree ≥ 6.
  - `rootedDecomp_of_deg_le_six` (Cor 3.3(b)): `n ≥ 10` and every neighbour of `r` has degree ≤ 6.
  - `test1At_fullCone_of_degStar`: hence (T1) at the apex of the cone over `B` for the root `r`.
  - `reassemble`: the general reassembly. A decomposition of `B − r` whose ends pair up `N(r)`, together with a partial injection from paths to trivial ends that misses them, gives a decomposition of `B` through `r`.
- **Proved on paper**: Prop 4.1, the Hamiltonian obstruction. When `m(B) ≥ 2k² − 3k + 4`, the method fails for every Lovász decomposition. Such `B` have ≥ `k + 4` vertices of degree `n − 2`, which is the range of MR Cor 168.
- **Computation**: see the manuscript, §5 (Table 1 and the order-12–16 samples).
- **Audit A31** (`research/audit/A31-re-tight.md`): every proof correct, Lean faithful, every checked number reproduces; findings F1–F12 (two wrong sentences, a missing Lovász check in the verifier, provenance, wording) applied.
- **Open**: everything outside (∗∗) with fewer than k − 1 vertices of degree n − 2; the method struggles in its dense part (§6 of the manuscript).

## Scripts (`scripts/`)
- `ret.c`: exact checker for the family form of RE at a root of degree `n − 2`. Modes:
  - default: RE;
  - `-z`: `k − 1` pairs, which holds iff `p(B) ≤ k − 1`;
  - `-L`: the Lovász-plus-matching method, exhaustive over all Lovász decompositions and orientations;
  - `-T`: every Lovász decomposition with the lower-degree end trivial; reports the least matching;
  - options `-b` (budget), `-r` (root), `-q A:B`, `-S`, `-c`.
  - Compile with `-DWIDE` for up to 128 edges in `B − r`.
- `verify_family.py`: independent witness check. It checks the family, reassembles the paths of `B` and checks the decomposition. With `-L` it also checks the Lovász property.
- `compare_z.py`: `-z` against `re.c -p`.
- `check_star.py`: Theorem 3.1 against `-T`.
- `coverage.py`: Table 1. It covers (∗), (∗∗), MR Cor 168, MR Thm 170, the decided literature classes, and the method.
- `near_regular.py`: random dense graphs in which only the root has degree `n − 2`.
- `samples.py`: regenerates every order-12–16 sample input byte for byte (seeds inside).
- `run_roots.py`: runs `ret` on a list of `graph6 root` lines (shell `read` mangles backslashes in graph6).
- `run_all.sh`: regenerates the data, with the budgets of the shipped files noted.
