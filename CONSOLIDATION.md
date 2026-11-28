# Consolidation into publishable papers (plan, 2026-11-28)

Goal: turn the project's ~39 working notes (`manuscripts/`) and the Lean library (`lean/GallaiLean/`) into a
small set of **standalone, definitive papers**. Each paper must be submittable together with its code
and Lean artifact and must hold up on its own.

## The papers

| # | Working title | Main content | Draws on (`manuscripts/…`) | Wave |
|---|---|---|---|---|
| P1 | **A machine-checked reduction of Gallai's path decomposition conjecture to two rooted tests on 3-connected graphs** | Spine (MR Thms 59/113/114) in Lean; Lovász's theorem from Fan's lemma in Lean; cones ⇔ rooted Eulerian Gallai | spine, lovasz-fan, eulerian-cone §2 | 1 |
| P2 | **Constrained Lovász decompositions: separation, neighbour avoidance, leaf tails and prescribed ends** | Proved strengthenings of Lovász's theorem (see below), all in Lean | route-descent, na, ln, conj31, dl-one, prescribed-end, multi-sep, ae, conj-n, clt, trn, multi-token | 1 |
| P3 | **Reversible lifts from constrained Lovász decompositions to the spine tests** | Reduction of (T1) and (T2) to constrained Lovász statements, with data | direct-test1, test2, nodata, multi-token, conj-r, t6-dense, stl, terminal-matching, overview | 1 |
| P4 | **Rooted Gallai for Eulerian graphs, and the two-end test at near-universal roots** | Eulerian rooted Gallai results (see below) | eulerian-cone, re-tight, dense-root | 2 |
| P5 | **Endpoint structure of path decompositions at the Gallai budget** | Cut selection `cs_all` (Thm 21), the endpoint matroid for four even vertices, `two_step_descent`, the spare path and hub lemmas, the cocktail-party barrier, hub closures | endpoint-min-max, endpoint-structure, missing-move, d6-frontier | 2 |
| P6 | **Exact path decompositions below the Dirac threshold** | Thm 1.1 (unconditional) and Thm 9.3 (conditional, with its hypothesis isolated) | near-dirac | 2 |
| P7 | **Repairs of three lemmas used in the Gallai literature** | Javadi–Miralaei Thm 8; Chu–Fan–Zhou Lemma 2.4; removal of the Shaik dependency | jm-repair, cfz-lemma, bs-prescribed, corrigenda | 2 |

**P2 content (proved strengthenings of Lovász's theorem, all in Lean):**
- Fan's lemma with vertex sets;
- the separation theorem (pair and set forms) and L₁;
- NA, with its exact boundary and set form;
- the multi-tail leaf theorem;
- Lovász with prescribed end counts (≤ 1 zero), with the degree bound and upward closure;
- EE with ≤ 1 common neighbour; AE ⇔ EE;
- the leaf exchange and Lemma NP;
- the steering transfer theorems and their obstruction invariant.

The open core (L_N, CL, J, PC / Conj 31, EE / AE, CLT-B) is stated precisely, with exhaustive data and the dependency map, and labelled as conjectures.

**P3 content (reductions of (T1) and (T2), with data):**
- Lifts, all reversible:
  - triangle, forest and all-odd lifts for (T1);
  - forest and floor lifts for (T2).
- Bridges from the conjectures:
  - DL ⇒ (T1), (T2);
  - L_N ⇒ (T1), (T2) at matching-data roots;
  - CL ⇒ (T1).
- Reductions at special roots: root moves M1/M2, twin reductions, the fat-theta family.
- Certificates and obstructions:
  - Lemma R / Criterion R ⇒ L_N(2);
  - k-token schedules as certificates;
  - the obstruction for roots of degree n − 2.
- Exhaustive coverage data.

**P4 content:**
- RE ⇔ (T1) on cones;
- the literature classes;
- reductions and cycle insertion;
- the degree-(n − 2) theorem;
- dense-root Theorems A and B;
- data.

Material from tight-fan, l1star, l1-induction, d6-frontier, two-even, six-clique and similar notes goes into P2, P3 or P5 where it is definitive. Otherwise it stays in the working notes.

## Standard every paper must meet ("definitive")

1. **Standalone mathematics.** Every claimed theorem has a complete proof in the text. Correctness never rests on the Lean code or on unpublished notes. Computer-assisted claims are declared as such, with exact scope and reproduction instructions.
2. **Honest status.** Every statement is labelled Theorem/Proposition/Lemma (proved in the text), Computation (with exact scope: orders, counts, solver, independent checks) or Conjecture. Nothing conjectural is phrased as known.
3. **Literature.** Citations are checked against the actual sources: arXiv, journals, exact theorem numbers. Prior work is credited. Results from the author's unrefereed manuscript collection (MR, SP, OSB, …, in `gallai/`) are cited as manuscripts, and every dependency on them is stated. Forwarded or external ideas are credited as in the working notes.
4. **Artifact.** Each paper gets a directory `papers/Pk-<slug>/` containing:
   - `paper.tex` and `paper.pdf`, compiling cleanly with bibtex or thebibliography;
   - `README.md`, a claim-by-claim map from each numbered result to its proof section, its Lean name (if any), and its script and data file (if computed);
   - `lean/Pk.lean`, a single Lean entry file. It imports exactly the modules the paper uses, restates or `#check`s every headline theorem, and runs `#print axioms` on each. The expected output is recorded in `axioms.expected`;
   - `scripts/` and `data/`, everything needed to regenerate every computed number, with `SHA256SUMS` and a `reproduce.sh` that runs end to end. Long runs carry stated times; quick checks must be separable from full runs;
   - the toolchain: Lean version, Mathlib commit (from `lean/lean-toolchain` and `lake-manifest.json`), compilers, Python packages.
5. **Repo level.** `papers/README.md` indexes the papers and their dependencies. A single `lake build` must succeed for the whole library. `scripts/check_papers.sh` builds the library and verifies each `Pk.lean` against `axioms.expected`.
6. **Audit.** Before completion, a fresh subagent referees the paper and its artifact adversarially. It re-runs at least the quick checks and the Lean entry file. Findings are fixed and the report is committed (`research/audit/`).
7. **Presentation.**
   - Consistent notation across papers.
   - Cross-references between papers by title and number.
   - Author field: the placeholder `[Author]`, for the user to fill. Do not put personal names or emails in files.
   - A generic statement that the work was prepared with AI assistance and machine-checked in Lean. No model names or identifiers anywhere.

## Process
- Wave 1 (P1–P3) runs now. Wave 2 (P4–P7) follows, given the usage limits.
- Each paper is written by one cloud session on branch `claude/paper-Pk`. The coordinator merges it through the build gate and checks the axioms of headline theorems.
- The working notes in `manuscripts/` remain as the research record. The papers supersede them for citation.
