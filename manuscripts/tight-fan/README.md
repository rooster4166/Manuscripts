# Fan's lemma at equality — cloud session `claude/tight-fan`

Manuscript: `tight-fan.tex` (compile with `pdflatex` twice). Lean: `lean/GallaiLean/TightFan.lean`.
Experiment log: `research/experiments.md`, E26. Conclusions: `research/connections.md`, §AB.
Audit: `research/audit/A24-tight-fan.md`.

## Status
- **The four residuals are not literally one configuration.** Two mechanisms, plus a third kind:
  - *transfer side, literally Fan at equality with one protected blank p*. The protected path P* has an end p adjacent to the Fan target w; in the leaf graph b(t) = 1 = |Z(w)|. On Lovász decompositions Fan's chain is forced, and the invariant survives iff the forced chain avoids p.
    - L∞ residual (p = far end of the leaf path).
    - The minimal blocked shape of L1* (p = c).
    - PTM instances with no admissible walk (p = the short end x).
  - *hypothesis side*: in a blocked L1* instance, (G − gu, c, A) is inadmissible for every u, but good for some u in every irreducible instance of order 9.
  - *base side*: PTM's K4/W4 base failures.
- **Flowers do not apply** (proved, Lean). With at most one end everywhere, the hub hypothesis forces |T| ≤ 1. Every flower or receipt-or-flower output has two ends on the transversal, so no flower move ends in a Lovász decomposition. All four residuals ask for one.
- **Proved and formalised** (sorry-free, standard axioms):
  - `fanPred_unique`: the chain is forced.
  - `fan_exists_chain_protected`, `fan_single_protected_supp`: Fan's lemma with protected blanks.
  - `l1_tight_transfer`: the tight case of L1*, conditional on the decomposition.
  - `lInfty_of_l1Blocked`: L1Blocked ⇒ L∞. With `ee_of_l1Blocked`, residuals 1–3 are one statement.
  - Flower negatives.
  - **`test1_deg_four`**: spine Test1 at d(z) = 4 whenever J − z is connected, via `emc_four`, with no PTM.
- **Paper only:** the tight walk theorem for PTM (walks through N(x)). It closes all 68 no-walk instances at n = 8.
- **Precise obstruction.** In 59 of the 133 L∞ residual instances of order 9, every target u admits an induction decomposition whose forced chain reaches the protected end. So a proof must strengthen the hypothesis; choosing the target cannot suffice.

## Reproduction (`scripts/`)
Requirements: gcc, Python 3 with networkx, nauty (`nauty-geng`). `./regen.sh` regenerates every quoted output except the long runs listed at its end.

| File | Content |
|---|---|
| `tf.py` | exact enumerator of path decompositions with prescribed end counts (transition systems, optional Q_c / region / separation pruning); Fan's chain executed exactly with every choice; checker |
| `xcheck.py` | cross-check of `tf.py` against `l1s` (`manuscripts/l1star/scripts/l1s.c`, mode `ed`) |
| `resid.py` | blocked L1* instances, irreducible one level deep (as `l1star/scripts/irred_all.py`) |
| `exp1c.py` | E26(A): is (G − gu, c, A) good for some target u (via `l1s ed`)? |
| `exp1d.py` | E26(A): forced chain through c vs result, over every good D' |
| `exp1e.py` | E26(A): the sufficient condition of Theorem 4.2 |
| `linf.py` | E26(B): the L∞ residual configuration, exhaustive |
| `ptmwalk.py` | E26(C): tight walk theorem on PTM's NOBASE instances |
| `ee_inst.py` | E26(D): CP(3) + apex and the double K4 |
| `nowalk68.txt`, `nobase764.txt`, `nobase764_s10.txt` | PTM NOBASE instances (from `terminal-matching/scripts/out/walk_8_0.txt`); `_s10` is every tenth line |
| `out/` | outputs |
