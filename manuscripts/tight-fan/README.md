# Fan's lemma at equality — cloud session `claude/tight-fan`

Manuscript: `tight-fan.tex` (compile with `pdflatex` twice). Lean: `lean/GallaiLean/TightFan.lean`.
Experiment log: `research/experiments.md`, E26. Conclusions: `research/connections.md`, §AB.
Audit: `research/audit/A24-tight-fan.md`.

## Status
- **The four residuals are not literally one configuration.** Two mechanisms, plus a third kind:
  - *transfer side, Fan at equality with one protected vertex p*. The protected vertex p is adjacent to the Fan target w and is (or, in the leaf graph, becomes) a blank of w, so b(t) = 1 = |Z(w)|. With at most one end per vertex, Fan's chain is forced. **The transfer can fail only if the forced chain passes through p.** For L∞ (and PTM) the converse holds too. For L1* it does not: order-9 counterexample `H??FFf}` (audit A24, F2).
    - L∞ residual (p = far end of the leaf path).
    - The minimal blocked shape of L1* (p = c).
    - PTM instances with no admissible walk (p = the short end x).
  - *hypothesis side*: in a blocked L1* instance, (G − gu, c, A) is inadmissible for every u, but good for some u in every irreducible instance of order 9.
  - *base side*: PTM's K4/W4 base failures.
- **Flowers do not fit** (proved, Lean, as far as it goes). With at most one end everywhere, the hub hypothesis forces |T| ≤ 1. Every flower or receipt-or-flower output has two ends on the transversal. So a flower move cannot be the *last* move of a proof of any of the four statements; no flower-based sequence ending in a Lovász decomposition was found.
- **Proved and formalised** (sorry-free, standard axioms):
  - `fanPred_unique`: the chain is forced.
  - `fan_exists_chain_protected`, `fan_single_protected_supp`: Fan's lemma with protected blanks.
  - `l1_tight_transfer`: the tight case of L1*, conditional on the decomposition.
  - `lInfty_of_l1Blocked`: L1Blocked ⇒ L∞. With `ee_of_l1Blocked`, residuals 1–3 are implied by one statement (the general form of L1* on blocked instances); neither implication reverses.
  - Flower negatives.
  - `walk_step_protected`: one walking-back step whose target has a protected blank neighbour, in the hypothesis form of `walk_back` (for chained walks, e.g. ptm's T(6)-i dense residual). Added after audit A24; not audited.
  - `test1_deg_four`: spine Test1 at d(z) = 4 whenever J − z is connected, via `emc_four`. This is a Lean packaging of a known case (terminal-matching Remark 7.3, `rooted_four'`).
- **Paper only:** Lemma 3.2 (a chain avoiding c suffices, L1*), and the tight walk theorem for PTM (walks through N(x), under the hypothesis that the forced chain does not reach x). The tight walk closes all 68 no-walk instances at n = 8; the static sufficient condition alone closes 47 (audit A24, F1).
- **Precise obstruction.** In 59 of the 133 L∞ residual instances of order 9, every target u admits an induction decomposition whose forced chain reaches the protected end. So a proof by this Case I step must control the decomposition the hypothesis supplies; the choice of target alone does not suffice. The naive strengthening GL⁺ (far end not adjacent to the even vertex) fails in general (`DTw`), though it holds in every residual step of order 9.
- **Mechanism (B) (admissibility).** Every local weakening of admissibility tested fails on 2.5–3.1% of instances at order 9. But in every admissible instance of order 9 with c ∉ N(g), some target u makes (G − gu, c, A) good.
- **Audit A24:** proofs sound, Lean faithful, data reproduced. Three errors (F1: 68 vs 47; F2: the L1* converse; F3: citation numbers) and the wording findings are applied.

## Reproduction (`scripts/`)
Requirements: gcc, Python 3 with networkx, nauty (`nauty-geng`). `./regen.sh` regenerates every quoted output except the long runs listed at its end.

| File | Content |
|---|---|
| `tf.py` | exact enumerator of path decompositions with prescribed end counts (transition systems, optional Q_c / region / separation pruning); Fan's chain executed exactly with every choice; checker |
| `xcheck.py` | cross-check of `tf.py` against `l1s` (`manuscripts/l1star/scripts/l1s.c`, mode `ed`) |
| `resid.py` | blocked L1* instances, irreducible one level deep (as `l1star/scripts/irred_all.py`) |
| `exp1c.py` | E26(A): is (G − gu, c, A) good for some target u (via `l1s ed`)? |
| `exp1d.py` | E26(A): forced chain through c vs result, over every good D' |
| `exp1e.py`, `exp1f.py` | E26(A): the sufficient condition of Theorem 3.3 (all D' at order 7; existence with early stop; the order-9 run was not completed) |
| `linf_far.py`, `glplus.py` | E26(B): far ends outside N(u); the strengthening GL⁺ |
| `exp2.py`, `exp3.py` | E26(E): weakenings of admissibility; the one-step derived class |
| `linf.py` | E26(B): the L∞ residual configuration, exhaustive |
| `ptmwalk.py` | E26(C): tight walk theorem on PTM's NOBASE instances |
| `ee_inst.py` | E26(D): CP(3) + apex and the double K4 |
| `nowalk68.txt`, `nobase764.txt`, `nobase764_s10.txt` | PTM NOBASE instances (from `terminal-matching/scripts/out/walk_8_0.txt`); `_s10` is every tenth line |
| `out/` | outputs |
