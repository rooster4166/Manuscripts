# Workflow toward unrestricted Gallai

This file says how the work is organised, so that any session can resume it. `ROADMAP.md` is the single source of truth for where things stand. Everything below feeds into it.

## Loop

1. **Orient.** Read `ROADMAP.md` (proof DAG and node status, external dependencies, work queue) and `STATUS.md` (where the project stands against the literature).
2. **Pick a node.** Prefer work that unblocks the final-assembly target in `ROADMAP.md`: the floor bounds BP_t for every odd t, which are equivalent to Gallai via the audited marked-reduction spine.
3. **Work it in one of four modes:**
   - **Audit.** An adversarial referee pass that grades every step SOUND, GAP, ERROR or UNCLEAR. Reports go in `research/audit/A*.md`, with scripts next to them. Confirmed fixes go in `manuscripts/corrigenda/corrigenda.tex`.
   - **Experiment.** Exhaustive or random computation with `tools/`. Every result goes in `research/experiments.md`, negative results included. Conjectures are always tested before any proof attempt.
   - **Prove.** New results go into a standalone LaTeX manuscript in `manuscripts/<topic>/`. Each manuscript must stand alone: computer-assisted steps ship with their scripts, outputs and a standalone verifier (for example `manuscripts/endpoint-structure/certificates/verify.py`).
   - **Formalize.** Lean 4 + Mathlib in `lean/` (v4.36.0). Every elementary lemma of the spine and of new manuscripts is formalized when feasible. Rules: no `sorry`, only standard axioms (check with `#print axioms`), and `lake build` green before every commit. Classical theorems not yet formalized (Lovász, Botler–Sambinelli, …) enter as explicit hypotheses, named in the README.
4. **Update.** Change the node status in `ROADMAP.md`, the log, and `research/connections.md` for cross-paper insights. Then commit and push.

## Grades used throughout

| Grade | Meaning |
|---|---|
| `PROVED-EXT` | published external result |
| `CLAIMED` | in a collection manuscript, not audited |
| `AUDITED` | passed an adversarial audit |
| `GAP` / `ERROR` | the audit found a fixable gap / a false step |
| `OPEN` | not proved |
| `CONJ` | conjecture with computational evidence |
| `REFUTED` | counterexample known |
| `lean` | formalized in `lean/` |
| `comp(n ≤ N)` | exhaustive computation up to order N |

## Tooling

| Tool | Purpose |
|---|---|
| `tools/pathnum.py` | exact solver; enumerates paths and solves a CP-SAT exact cover; dense graphs up to about 9 vertices |
| `tools/pathnum2.py` | circuit-constraint CP-SAT solver, cross-checked against pathnum; up to about 14 vertices |
| `tools/graphgen.py` | all connected graphs up to isomorphism (counts match OEIS through n = 8) |
| `tools/*` | the experiments listed in `research/experiments.md` |
| `lean/` | formal proofs (see `lean/README.md`) |

## Constraints met so far

- Building downloaded third-party code (nauty sources; Shaik's Lean repository) is blocked by the session's permission policy. Such checks are recorded in `ROADMAP.md` with the exact commands, so a person can run them.
- The machine has 4 cores and is shared by the agents. Run background jobs with `nice`, and print with `flush` so partial results survive.

## Rule added 2026-11-27: never commit during someone else's merge

Before any checkpoint commit, for example one prompted by the stop hook, check `test -f .git/MERGE_HEAD` and `git diff --name-only --diff-filter=U`. If a merge is in progress or files are unmerged, an agent is mid-resolution. Do not commit: wait for that agent, or ask it to finish. A checkpoint commit made with `git add -A` during a merge once pushed conflict markers in `endpoint-min-max.tex` (commit 328eb52).
