# A24. Audit: "Fan's lemma at equality: one residual configuration behind four Lovász-type problems, a protected-blank form of Fan's lemma, and why flowers do not apply"

- **Date:** 2026-11-27
- **Auditor:** fresh subagent (adversarial referee). I made no edits to the manuscript, the Lean files or the authors' scripts and outputs, and I committed nothing.
- **Scope:**
  - `manuscripts/tight-fan/tight-fan.tex`, compiled twice with `pdflatex` in a scratch copy (no errors, no undefined references). Every statement and proof: Proposition 2.1, Theorem 2.2, Corollary 2.3, Definition 2.4, Proposition 3.1, Theorems 3.2, 3.3, 3.4, Conjecture 3.5, Proposition 4.1, Theorem 5.1. The numbering in the freshly compiled PDF is exactly this. The abstract, "Results", "Honest status", the summary table, Sections 6–8.
  - The citations to l1star (L1S), prescribed-end (PE), route-descent (RD), terminal-matching (TM) and endpoint-structure (ES), checked against their `.tex` and PDFs.
  - `lean/GallaiLean/TightFan.lean`, and the definitions it uses (Basic, Fan, FanSupport, L1Star, Flower, ThreeConnected, Realisable, EMCFour, EMCFourFree).
  - `manuscripts/tight-fan/scripts/` and `scripts/out/` as committed in `39f2d37`, `manuscripts/tight-fan/README.md`, and `research/experiments.md` E26.
- **Out of scope:**
  - The two long runs: `out/ptm764s_*.txt` (placeholder PTM-SAMPLE; unfinished at the end of the audit: shard 0 still running, shards 1 and 2 no longer running, each file with 5 INST lines and no summary) and the order-9 run of `exp1e.py` (placeholder ORDER9-E1E; its output `scripts/out_exp1e_9.txt` was empty at `39f2d37` and was deleted at `39b162e`; see F4).
  - Files added after the audited commit, while I worked (`c6ebecf`, `39b162e`, `1e0aa0f`, `be1b2dc`, `af1d09c`): `exp1f.py`, `exp2.py`, `exp3.py`, `glplus.py`, `linf_far.py`, their outputs, and the ROADMAP entries. None of them changes a file listed below.
  - `research/connections.md` §AB.
- **Audit scripts:** `research/audit/A24-scripts/` (outputs in `A24-scripts/out/`):
  - `mylib.py`: independent library (own graph6 decoder; enumeration of path decompositions by *path growing*, a different algorithm from `tf.py`'s transition systems; own checker; Fan's forced chain and its execution as in RD Lemma 2.2; exhaustive Fan over all chains). Does not import `tf.py`.
  - `check_tf.py`: `tf.py` against `mylib.py` (item (d)).
  - `a_dichotomy.py`: E26(A) re-derived independently (item (a)).
  - `b_linf.py`, `b_linf_peru.py`: E26(B) re-derived independently (item (b)).
  - `ptmwalk_audit.py` (a modified copy of `ptmwalk.py`), `c_verify.py`, `c_trace.py`, `c_independent.py`: E26(C) (item (c)).
  - `a_counterexample.py`, `a_exp1d_single.py`: the order-9 counterexample of F2.
  - Scripts that use the authors' `tf.py` take its directory as first argument (`check_tf.py`, `a_counterexample.py`, `a_exp1d_single.py`) or need it on `PYTHONPATH` (`ptmwalk_audit.py`, `c_trace.py`). I used a `git archive` copy of `39f2d37` in the session scratchpad. `a_dichotomy.py`, `b_linf*.py`, `c_independent.py`, `c_verify.py` use only `mylib.py`.
  - `A24AxiomCheck.lean`: the axiom/definition check. It was run from `lean/` with `lake env lean` and then deleted from `lean/`; the copy here is for the record.
- **Version audited:** branch `claude/tight-fan`, commit `39f2d37`. The audited files are unchanged up to the latest HEAD seen during the audit, `af1d09c`.

| file | md5 |
|---|---|
| `manuscripts/tight-fan/tight-fan.tex` | `e46798df6a6ad0a4f2a22d9fd0a934af` |
| `manuscripts/tight-fan/tight-fan.pdf` (committed) | `d8c9a9b7c8959429c3111c53daa29c5b` |
| `lean/GallaiLean/TightFan.lean` | `4a2791bab89db089c00814896823aa1e` |
| `manuscripts/tight-fan/scripts/tf.py` | `0434c6c9fc0f8daa80a6292ffbf28449` |
| `manuscripts/tight-fan/scripts/ptmwalk.py` | `65c094e6f508632ad23bb080afdcdc6c` |
| `manuscripts/tight-fan/scripts/linf.py` | `75afd80a24d299ab9f4344011061a760` |
| `manuscripts/tight-fan/scripts/exp1c.py` | `1669f6f3fd76d33c233ad4f0167be22f` |
| `manuscripts/tight-fan/scripts/exp1d.py` | `14fb8833ccd2ea8a8d2cd2a8ccf00191` |
| `manuscripts/tight-fan/scripts/exp1e.py` | `f938c1f0197b61e7139f1c2826af8a55` |
| `manuscripts/tight-fan/scripts/resid.py` | `b0dbf254ee434cb5eb6f5dcab634165e` |
| `manuscripts/tight-fan/scripts/xcheck.py` | `94936af7e916d85e034081539f3617f2` |
| `manuscripts/tight-fan/scripts/ee_inst.py` | `e380a1a8cfca0e839e891087e999539a` |
| `manuscripts/tight-fan/scripts/regen.sh` | `71abaefa1511d7b510755e2135369edd` |
| `manuscripts/tight-fan/README.md` | `1e16df113a0a6436b5cb9bc4f31fef7d` |
| `manuscripts/l1star/scripts/l1s.c` | `4134e75de7273e40cb85d3df4d11f317` |
| `research/experiments.md` | `d337f517fa02f0198a1a36e573143953` |

## 0. Verdict

**The proved mathematics is correct, and the Lean file is faithful. But two headline claims are false as stated, the walk-theorem citations are wrong, and several claims are overstated.**
- The two false claims are the L1* half of the dichotomy "the invariant survives iff the forced chain avoids p" (F2) and "Theorem 3.4 closes all 68 no-walk instances" (F1).
- **Sound.** Proposition 2.1, Theorem 2.2, Corollary 2.3, Proposition 3.1, Theorems 3.2, 3.3, 3.4 and 5.1, and Proposition 4.1 are correct as proved. Theorem 3.4 (paper only) is a correct modification of TM's walk theorem: admissibility is used there only through the hypothesis of the walking-back lemma, and Theorem 2.2 replaces it at the tight steps.
- **Lean.** `TightFan.lean` builds, has no `sorry`, and every main theorem uses only `propext`, `Classical.choice`, `Quot.sound`. The statements match the manuscript, with small differences in docstrings and one in strength (§4).
- **F1 (ERROR, data claim about Theorem 3.4).** "In the data it [Theorem 3.4] closes every one of the 68 instances" is false. The script never tests the hypothesis of Theorem 3.4. Testing it exhaustively (all 8 orientations, all walks, all base decompositions), it holds for some walk in **47** of the 68 instances; in the other **21**, every successful walk-back violates it at some tight step. All 68 are closed, because at each tight step the *forced chain happens not to reach x*. That is a weaker hypothesis, which is provable by the same argument (Corollary 2.3(1)), but it is not Theorem 3.4.
- **F2 (ERROR, central claim).** "The invariant survives exactly when the forced chain avoids p" is a theorem for L∞ (Proposition 3.1) and trivially for PTM (the leaf-graph chain is stuck at x).
  - **For L1* it is false.** "Avoids ⇒ survives" is a true, easy lemma, but it is unwritten. "Reaches ⇒ fails" was only observed at order 7, where every tight transfer lies in an instance of the minimal shape. The abstract says "without exception" and does not say "order 7".
  - **At order 9 it fails, in the minimal blocked shape itself.** H??FFf}, g = 3, c = 0, A = {1,3}, u = 7: the forced chain 3 → 6 → 0 passes through c, and the result is good (`out/a_counterexample_9.txt`; the authors' own `tf.py` pipeline records 114 such transfers in this instance).
  - In a 101-instance order-9 sample, 34,577 of 487,872 through-c tight transfers succeed (`out/a_dichotomy_9_s10.txt`). The order-7 counts themselves (896/696/56, 930/515/618) reproduce exactly.
  - Order 9 is the unfilled placeholder ORDER9-E1E.
- **F3 (ERROR, citation).** The walk theorem of TM is **Theorem 4.2**, not Theorem 3.2 (TM Theorem 3.2 is sparse separation). "[TM, E24(F)]" cites the experiment log, not TM.
- **Overclaims (WORDING):** flowers (F5: the Lean negatives exclude a flower only as the *last* move); Test 1 at degree four (F6: already in TM Remark 7.3 via `rooted_four'`); "three faces of one statement" / "(R3) is (R2)" and the |A| ≤ 2 vs general form of L1* (F7); "any proof must strengthen the hypothesis" (F9).
- **Data.** Every number that the manuscript and E26 quote from committed outputs is reproduced exactly: by re-running the authors' scripts (byte-identical outputs), and independently with my own code for E26(A) at order 7, E26(B) at orders 7 and 9, and E26(C). The committed PDF is stale (F4). The two placeholders are unfilled (F4).

| class | findings |
|---|---|
| ERROR | F1 (Thm 3.4 data claim), F2 (dichotomy false for L1* at order 9), F3 (TM citations) |
| GAP | F4 (stale PDF, placeholders, missing order-9 output) |
| WORDING | F5 (flowers), F6 (Test 1 known), F7 (L1* form, "one statement", L1S Prop 3.1 credit), F8 (CP(3)+apex "tight"), F9 ("any proof"), F10 (minimal shape is automatic), F11 (Def. 2.4 / Conj. 3.5 informal), F12 (Thm 2.2 "unchanged on B") |
| DATA | F13 (uniqueness of the Fan image not checked by scripts) |
| NIT | N1–N8 |

## 1. Findings

### Errors

**F1 (ERROR, data claim; l.317–318, E26(C) l.440–445, §7 item 4 l.471–473, README "Paper only", E26(C) in `experiments.md`).** The text says of Theorem 3.4: "In the data it closes every one of the 68 instances of order 8 that have no admissible walk."
- Theorem 3.4's hypothesis: at each step i with p_i ∈ N(x), no vertex of {p_{i+1}} ∪ N(p_i) has x as its predecessor of p_i. Equivalently, the end e on x's side of the path through xp_i lies outside {p_{i+1}} ∪ N(p_i).
- `ptmwalk.py` never tests this. It runs the walk back with `tf.fan_moves` and keeps every result. So a success shows only that, at each tight step, the forced chain from p_{i+1} did not reach x (Corollary 2.3(1)).
- **Test.** `ptmwalk_audit.py` is a copy of `ptmwalk.py` with the hypothesis recorded at every tight step. In mode `thm34` it keeps searching (all 8 orientations, all walks of length ≤ 7, i.e. all walks at n = 8, all base decompositions) for a success satisfying the hypothesis at every tight step.
  - The first success found by the original search satisfies the hypothesis in 32/68 instances.
  - A success satisfying it exists in **47/68** (42 with walk length 2, 5 with length 3). In **21/68** none does (`out/ptm68_thm34.txt`: the `INST` lines with `NONE`).
  - **Independent confirmation** (`c_independent.py`, `mylib` only: own base enumeration with the separations as a path veto, own forced chains, own merge and check): 68/68 closed; 47/68 closed with the hypothesis; the same 21 instances without (`out/c_independent_68_part1_full.txt`, `…_part2_early.txt`).
- **Example** (`c_trace.py`): `G?AQV{` with F = {03, 14}, orientation (a,b,x,y) = (0,3,1,4), walk 4 7 0, base D0 = [(0,5), (7,1,6), (2,7,3,ℓ1), (3,5,7,6,4)].
  - At the tight step with target 7 (x = 1 ∈ N(7)), the path through x7 is 4 7 1 6. Its end on x's side is e = 6 ∈ N(7). So the hypothesis of Theorem 3.4 fails.
  - The forced chain from the source 0 is the single vertex 0: its path (0,5) avoids 7, and 7 is appended. The walk back succeeds and gives a verified PTM₂ decomposition.
- **What is true and provable.** "If at each tight step the forced chain from p_{i+1} does not reach x, the conclusion of the walk theorem holds." Proof: that chain is a Fan chain, and RD Lemma 2.2 gives the end counts and vertex sets. x is never a chain vertex (it has no end), so b(x) = 0 and the separations survive. This is the hypothesis the data actually test, and it closes 68/68.
- **Fix:** either state Theorem 3.4 with the forced-chain hypothesis (keeping the predecessor condition as a sufficient "for instance"), or say "Theorem 3.4 as stated applies to 47 of the 68; all 68 are closed by walks whose forced chains avoid x". Correct README, E26(C) and §7 item 4 accordingly.

**F2 (ERROR, central claim; abstract l.43–49; §3.2 l.250–253; Results item 2 l.110–113; "Honest status" l.124 ("the exact form of the obstruction"); E26(A) "The result is good iff the forced chain avoids c, without exception"; README Status; ROADMAP entry).** The text says: "The invariant survives exactly when the forced chain avoids p. Exhaustive data confirm this dichotomy without exception in the L∞ residual and in the blocked residual of L1*…", and in §3.2 "the plain transfer succeeds exactly when the forced chain avoids c".
- **L∞ (R1): proved.** Proposition 3.1 gives both directions. P* changes iff the chain ends at y, and then P* gains u ∉ B. So the E26(B) count "fails exactly when the chain reaches y" is a consequence of Proposition 3.1, not independent confirmation.
- **PTM (R4): trivially proved.** In the two-leaf graph x has no end. A forced chain that reaches x is stuck, and there is no transfer at all (Corollary 2.3(1)).
- **L1* (R2): false in the "only if" direction.**
  - *"Avoids ⇒ survives"* is true, but nowhere stated or proved. Theorem 3.2 is in the leaf graph under a stronger hypothesis. The plain-graph proof is short: if c is not a chain vertex, Q_c is untouched, re-routed at its other end (same vertex set) or extended there by u ∉ A, using A ∩ N(g) = ∅.
  - *"Reaches ⇒ fails"* has no proof and is false. If the chain first meets c at step i, the new Q_c is the re-routed Q_{i−1} ∈ 𝒟′, with vertex set V(Q_{i−1}). So the result is good iff V(Q_{i−1}) ∩ A = ∅.
    - This is automatically bad only when i = 1 and g ∈ A, since Q_0 ∋ g.
    - At order 7 the 696 (|A| ≤ 2) "through c" transfers split into 404 automatic and 292 that are bad only empirically. With A maximal the split is 325/190 (`out/a_dichotomy_7*.txt`).
  - The authors' data are exhaustive only at order 7. There every tight transfer lies in an instance of the minimal shape (g ∈ A, d(g) = 2): the 14 instances with |A| ≤ 2 and the 61 with A maximal. The other 5 order-7 residuals are separated, and their targets lie outside N(c).
  - **Counterexample at order 9** (`a_counterexample.py`, cross-checked with `tf.fan_moves`, and by hand). G = `H??FFf}` (edges 06 07 08 16 17 18 26 27 28 37 38 48 58 67 68), g = 3, c = 0, A = {1,3}.
    - The instance is admissible, blocked, irreducible and of the minimal shape: N(g) = {7,8} ⊆ N(c), 78 ∉ E, A = ∂C. It is the second instance of the authors' own `exp1c_9.txt` EX list.
    - Target u = 7. D′ = {8 2 7 0 6, 0 8 4, 5 8 1 6 2, 1 7 6 8 3} is a Lovász decomposition of G − 37 with Q_c = 0 8 4, which avoids A.
    - The forced chain is 3 → 6 → 0 (= c) → stop: the path 0 8 4 avoids 7.
    - The result {0 6 7 2 8, 7 0 8 4, 5 8 1 6 2, 6 8 3 7 1} is a Lovász decomposition of G with **Q_c = 0 6 7 2 8, which avoids A**. The transfer succeeds although the chain passes through c.
  - **Order-9 sample (every 10th irreducible instance, |A| ≤ 2; `out/a_dichotomy_9_s10.txt`):** the first 101 of the 242 sampled instances (69 with g ∈ A and d(g) = 2, 14 with g ∈ A and d(g) = 4, 18 separated); at most 20,000 good D′ per target and 15 s per target (50 targets capped, 3 timed out). I stopped the run after 110 sampled instances to free the CPU; the counts are those of the last `PARTIAL` line, written after instance 101.
    - Tight transfers (u ∈ N(c)) whose forced chain avoids c: 1,243,484, all good.
    - Chain through c: 487,872, of which **34,577 are good**. All of these are in instances of the minimal shape. The other 453,295 are bad.
    - In every case the result is good iff V(Q_{i−1}) ∩ A = ∅, as derived above. 252,764 of the through-c transfers hit c at step 1, where badness is automatic.
    - The condition of Theorem 3.2 never failed to deliver, and it holds for some D′ in all 83 tight instances. This is a partial order-9 check of the ORDER9-E1E claim.
    - In the separated instances no target in N(c) has a good D′.
    - The authors' own `exp1d.py` logic (`tf.decomps` + `tf.fan_results`) on the single instance H??FFf} records 114 transfers with "chain passes c, result good" (`a_exp1d_single.py`, `out/a_exp1d_single_HFFf.txt`).
- **Fix:**
  - Replace the dichotomy by what is true: "the transfer can fail only if the forced chain passes through p (a lemma for L1*, which should be added); for L∞ the converse also holds (Proposition 3.1)". Report the order-9 counts.
  - Correct the abstract, Results item 2, §3.2, E26(A), README and ROADMAP accordingly.
  - "Literally one configuration" for the minimal shape of L1* should then read "the same *failure mechanism*".

**F3 (ERROR, citations; l.297, l.311, l.441).**
- "the walk theorem [TM, Theorem 3.2]" and "The proof of [TM, Theorem 3.2]": in TM (both the `.tex` and the PDF) the walk theorem is **Theorem 4.2** (Section 4, with Definition 4.1 for admissible walks). TM Theorem 3.2 is "sparse separation [MS]". The walking-back lemma that the proof of Theorem 3.4 really modifies is TM **Lemma 3.4**.
- "[TM, E24(F)]" (l.441): E24(F) is in `research/experiments.md`, not in TM. The 832/764/68 counts are in TM §8 ("How far the walk theorem reaches").
- **Fix:** cite TM Theorem 4.2 and Lemma 3.4, and TM §8 (or "experiment log E24(F)").
- The other citations are correct (§3).

### Gaps

**F4 (GAP/DATA, unfinished data and stale PDF).**
- **Placeholders.** The manuscript contains the literal placeholders "ORDER9-E1E" (l.428) and "PTM-SAMPLE" (l.446). Both appear as text in the PDF.
  - E26(A) says "Order 9: see `out/exp1e_9.txt`". That file does not exist. At `39f2d37` there was an empty `scripts/out_exp1e_9.txt`; at `39b162e` it was renamed to `out/exp1f_9.txt` (0 bytes), for a different, early-stopping script.
  - **Fix:** fill or delete both placeholders, and point E26 to an existing output.
- **Stale PDF.** The committed `tight-fan.pdf` does not match `tight-fan.tex`. `pdftotext` diff against a fresh compile:
  - It still has the older numbers "1,826 have a chain avoiding c … 1,211 through c" (now 896/696/56), and "walk length 2: 20, 3: 27, 4: 18, 5: 3" (now 63/5).
  - It still has "[3, Lemma 7.x]" and "[3, Remark after Corollary 7.x]", "Fan, Hou and Zhou had already settled the deletion tests at d = 4", and a garbled Theorem 3.2 header ("c ≠ x odd... precisely:").
  - **Fix:** recompile and commit.

### Wording and overclaims

**F5 (WORDING, overclaim; abstract l.56–59; §4 l.368–378; §7 item 1 l.461–462; "Honest status" l.126; README; E26(E)).** The text says: "No flower move ends in a Lovász decomposition, so none of the four residuals can be closed by it", "at any order", "a structural fact", "a complete negative answer for flower moves".
- **What is proved** (Proposition 4.1, Lean): the *immediate output* of `flower_decomp` / `flower_decomp_rest` has b ≥ 2 on every vertex of L. And the hub hypothesis of `hub_cycles` with b ≤ 1 forces |T| ≤ 1. Both are one-line consequences of the end-count hypotheses: b(s) = |T| ≤ 1, and b(L.src) = 2.
- **This excludes a flower only as the final move.** It says nothing about a flower followed by further moves that lower the end counts on L, or that merge the spare path back:
  - path joins at a common end;
  - Fan transfers;
  - leaf merges.

  ES itself does this. In ES Proposition 68 (the graph B′, §7), receipt-or-flower is followed by "appending x₁ℓ at the end x₁ of L", which lowers b(x₁).
- The manuscript's own description is fairer ("it is a tool for the rooted tests…, not for Lovász-type invariants, which have no spare path"). That is a heuristic, not a theorem.
- **Fix:** say "no flower move can be the last move of a proof of (R1)–(R4); the end-count bookkeeping (one spare path, two ends on L) makes it unsuited to Lovász-type invariants". Drop "at any order", "structural fact" and "complete negative answer", or prove a statement about flower-then-merge sequences.

**F6 (WORDING, priority; abstract l.60–62; Results item 4; §5 l.379–400).** Theorem 5.1 (Test 1 at d(z) = 4) is presented as a result. The parenthesis says the tests "were already settled …; the point here is that the spine's Test 1 at degree four is now a Lean theorem that does not depend on PTM".
- **TM Remark 7.3** ("the first test at degree four is known") already derives exactly this:
  - from `rooted_four'` (Lean, unconditional, Lovász + Fan only, `EMCFourFree.lean`) by a three-line leaf argument;
  - "So Corollary 7.2 adds nothing to the first test at degree four". It also cites BS Theorem 13.
- ROADMAP l.72 calls `test1_deg_four` "a packaging of the known T(4) / `rooted_four'`".
- **What is new:** the Lean statement with conclusion `Test1 J z`, under "J − z connected" (TM's remark assumes J 3-connected), via `emc_four` instead of `rooted_four'`.
- STATUS.md attributes d = 4 to Fan–Hou–Zhou. That is a published result, for the deletion tests generally.
- **Fix:** cite TM Remark 7.3 in §5 and in the abstract ("a Lean packaging of TM Remark 7.3, with J − z connected instead of 3-connected"). Remove "That test needs no PTM:" as a new observation; it is TM's.

**F7 (WORDING, the form of L1*, and credit; (R2) l.91–93; Theorem 3.3 l.278–287; abstract l.54–55; Results l.113–115; l.289).**
- **(a) The form of L1*.** (R2) defines L1* with *arbitrary* A. That is L1S **Conjecture 1.3** ("general form"). L1S's L1* (Conjecture 1.2, PE Conjecture 7.3) has |A| ≤ 2.
  - Theorem 3.3 needs the general form: A = V ∖ N[c] is large. Blocked L1* with |A| ≤ 2 does not give L∞ by this proof.
  - Lean is right (`L1Blocked` has no bound on |A|). The paper should say "general form" in (R2) and Theorem 3.3.
  - The E26(A) data use |A| ≤ 2 or A maximal, which should be said in the summary.
- **(b) Credit.** L1S Proposition 3.1 already records that in an all-odd graph the local form (equivalent to the general form) says V(Q_c) ⊆ N[c]. So Theorem 3.3 is L1S Theorem 4.3 + L1S Proposition 3.1 + L1S Corollary 4.4. The new part is the Lean proof `lInfty_of_l1Blocked`. The Lean docstring of `LInfty` cites L1S Proposition 3.1; the paper should too.
- **(c) "One statement".** "So three of the four residuals are one statement" and "(R1), (R2) and (R3) are three faces of one statement" (and "(R3) is (R2)") are overstated. `L1Blocked` *implies* L∞ and EE. Neither implies `L1Blocked`.
  - Moreover, the residual analysed in §3.1 is the residual of the leaf statement GL (RD Conjecture 8.2 with s = ℓ), which is stronger than L∞. L1* does not give GL by this route: with c′ = ℓ, the set A = V ∖ ({ℓ} ∪ N[c]) is admissible only if N(z) ⊆ {ℓ} ∪ N[c], which fails in the residual.
  - **Fix:** "are implied by one statement"; say that the L∞ face is reached by a different route (A = V ∖ N[c], no leaf) from the GL residual of §3.1.

**F8 (WORDING; l.290–294 and E26(D)).** "In CP(3) plus an apex … every Case I target of (K−uz,z,{u}) lies in N(c), so every step is tight at c."
- In these instances g = u, c = z and A = {u} = {g}. So A ∖ {g} = ∅, and L1S **Theorem 4.2(c)** applies to every target x ∈ N(g) ∩ N(c). The tight Case I transfer is one option, not forced.
- The difficulty in CP(3) + apex lies deeper: L1S's certificates fail after several reductions.
- **Fix:** add "(Theorem 4.2(c) of L1S also applies to these targets; the tight transfer is the alternative to it)".

**F9 (WORDING, overclaim; "Honest status" l.126–129; §3 after Conj. 3.5 l.342–343; §7 item 2 l.463–467; README "Precise obstruction").** "Any proof must therefore strengthen the induction hypothesis…, not only choose the target", "choosing the target cannot suffice".
- The 59/133 count (reproduced) concerns one specific step: delete an edge zu at the even vertex, take *any* GL-decomposition of K − zu, restore zu by one Fan transfer. It says nothing about other deletions, other moves (e.g. L1S Theorem 4.2(d)-type leaf moves, Proposition 5.2/5.3-type routes), or other inductions.
- Moreover, every (instance, target) pair of order 9 has *some* successful D′: 320 pairs, 271 of them with at least one tight D′ (`out/b_linf_peru_9.txt`). So at order 9 every target works for a suitable D′. The obstruction is only that the hypothesis may supply a bad D′, which is consistent with Conjecture 3.5 read per target.
- **Fix:** "a proof by this Case I step must control the decomposition supplied by the hypothesis; the choice of target alone does not suffice."

**F10 (WORDING; §3.2 l.250–252; E26(A) l.416–417).** "In all 1,200 instances with g ∈ A and d(g) = 2 … every good u lies in N(c)" and "including every instance of the minimal shape … every good target lies in N(c)" are presented as data.
- They are automatic: the irreducibility filter (L1S Corollary 5.6(5), `resid.py`) forces N(g) ⊆ N(c) whenever g ∈ A and d(g) = 2. So *every* target is in N(c).
- **Fix:** say so; the data content of that bullet is only the d(g) = 4 split 637/382 and the separated 195.

**F11 (UNCLEAR; Definition 2.4 l.208–215; Conjecture 3.5 l.337–343).**
- **Definition 2.4** is informal: "the property to be kept is a property of V(P*) that the final append … would destroy". It calls the PTM steps "Case I steps", but walking back is not a step of Lovász's induction: TM's own Remark 4.3 says the intermediate graphs are outside Lovász's setting. Nothing depends on the definition, but the claims that rest on it ("literally one configuration") then have no precise content.
- **Conjecture 3.5** is ill-posed for L1*. In the blocked case, the induction hypothesis does not apply to (G − gu, c, A) at all, because it is inadmissible. So "the decompositions that the induction hypothesis can supply" is empty there.
- **Fix:** give Definition 2.4 as a precise list of hypotheses (D′, t, w, P*, p, with b ≤ 1). Restrict Conjecture 3.5 to GL, or say which inductive class supplies D′ for L1*.

**F12 (WORDING; Theorem 2.2 l.163–165; docstring of `fan_grouped_protected_supp`).** "with end counts b − 1_t + 1_w (in particular unchanged on B)" needs w ∉ B.
- The hypotheses allow w ∈ B: w is never anyone's predecessor of w. Then b changes at w.
- **Fix:** add w ∉ B, or "unchanged on B ∖ {w}".

### Data

**F13 (DATA, minor; §6 l.408–409; E26 "Tooling").** "In every Case I step tested below the Fan image was unique, as Proposition 2.1 predicts."
- None of `exp1d.py`, `exp1e.py`, `linf.py` or `ee_inst.py` checks this; each takes `fan_results(...)[0]`.
- The claim is true where I checked:
  - `check_tf.py`, orders 3–7: on every connected graph with exactly one even vertex g, every u ∈ N(g) and every Lovász decomposition of G − gu, `tf.fan_moves` returns exactly one result, equal to my forced chain and to my exhaustive all-chain search. That is 108,870 cases at order 7, with identical chain sequences.
  - `a_dichotomy.py` at order 7 also confirms it.
- **Fix:** add the assertion `len(outs) == 1` to the scripts, or cite the audit check.

### Nits

- **N1 (Lean docs).** The module docstring of `TightFan.lean` lists `flower_decomp_two_ends`, `flower_decomp_rest_two_ends` and `flower_not_lovasz`, which do not exist; the theorems are `flower_decomp_not_le_one` and `flower_decomp_rest_not_le_one`. The docstring of `l1_tight_transfer` says "manuscript Theorem 4.2" (it is 3.2) and "c ∉ N(g)", which is not a hypothesis of the statement (the statement is more general, correctly).
- **N2 (Lean docs).** The docstring of `fan_single_protected_supp` says "provided the end of the path through pu on p's side is not reached by the chain". That is the sharp condition of F1; the theorem assumes the stronger predecessor condition on all of {v} ∪ N(u).
- **N3 (abstract l.50–51).** "a blank that no chain vertex reaches as a predecessor does not count": the theorem requires this for every vertex of T ∪ N(w), not only for chain vertices. Say "no vertex of T ∪ N(w)".
- **N4 (Theorem 5.1).** The paper says "into (|J|−1)/2 paths with two ends at r"; Lean's `Test1` says "at most (|J|−1)/2 paths, at least two ends". The proof gives the exact statement; the Lean statement is the spine's.
- **N5 (§8 l.495).** "Not formalised: Corollary 2.3(1), …": Corollary 2.3(2) is not formalised either (Lean takes the predecessor condition as a hypothesis), nor the "Hence" part of Proposition 2.1. Also "Everything stated as a theorem is formalised … except Theorem 3.4" (abstract) should mention Corollary 2.3 and Proposition 3.1.
- **N6 ((R1) l.88–90).** "Lovász's induction proves it except when …": RD says the *induction step* goes through except in that configuration; nothing is proved for a class of graphs. Say "the induction step goes through except …".
- **N7 (Theorem 3.4).** "the current decomposition" depends on the base decomposition D₀. Say "if M has a Lovász decomposition D₀ with the three separations such that, in the walk back from D₀, …". The chains are forced, so D₀ determines everything.
- **N8 (E26(C) l.443–444).** "trying walks in order of length, the shortest successful walk has length 2 in 63 of them and 3 in 5". The script reports the shortest walk of the *first successful orientation*, not the minimum over orientations. I computed the minimum over all 8 orientations independently; it is the same (63/5; `c_independent.py`). The 63/5 split equals the edge distance (2 or 3) of E24.

## 2. Item-by-item verdicts

| # | Item (lines) | Verdict | Key checks |
|---|---|---|---|
| 1 | §2 setup, chain definition (l.131–141) | SOUND | Chain and execution as in RD Lemma 2.2; `fan_exec_supp`, `fan_exists_chain` exist with these statements. |
| 2 | Prop 2.1 (l.143–152) | SOUND | b(x) ≤ 1 ⇒ one path ends at x, once; predecessor unique in a path. Lean `fanPred_unique` is exactly the first sentence. The forced sequence is injective because t ∉ N(w) and pred is injective. |
| 3 | Thm 2.2 (l.157–184) | SOUND (F12) | Reachable set R ⊆ T ∪ N(w), R ∩ B = ∅ by induction. The end→edge map {ends in R} → {zw : z ∈ R ∩ N(w)} is injective (two ends in R of one path read w's two different neighbours on it; w itself is never in R). The count gives Σ_T b ≤ #blanks outside B. Lean faithful. |
| 4 | Cor 2.3 (l.188–206) | SOUND | e is the only vertex with predecessor p (p is interior, b(p) = 0, w ∉ {e}). (1): chain injective, so it terminates; at p it is stuck. (2): the predecessor condition on {p} ⇔ e ∉ T ∪ N(w). Not formalised. |
| 5 | Def 2.4 (l.208–215) | UNCLEAR (F11) | Informal; not used in proofs. |
| 6 | Prop 3.1 (l.225–239) | SOUND | u ∉ B, so P* is never re-routed; ℓ is never a chain vertex; at y the only path is P*, which avoids u. The last sentence follows directly (y is interior to the yu-path, so only e has predecessor y); the "second leaf" detour is unnecessary but correct. |
| 7 | §3.2 text (l.243–253) | ERROR (F2: "succeeds exactly when the chain avoids c" is false at order 9), WORDING (F10) | "Never admissible": u has d(u) ≥ 3 (blocked), so u is the even vertex of G − gu and has a neighbour in A ∖ {g}. Lemma 2.4 of L1S applies when u ∉ N(c). |
| 8 | Thm 3.2 (l.255–270) | SOUND | Z(x) ⊆ {c} in the leaf graph (other neighbours odd, unchanged; ℓ ∉ N(x)). Theorem 2.2 with T = {g}, B = {c}: 0 < 1. b(x) = 0 + 1, b(g) = 0, b(c) = 0, leaf path ⊆ old + x ∉ A; L1S Lemma 2.3(ii). The "for instance" sentence (l.272–274) is right: with Q_c = c x ⋯ the only vertex with predecessor c is ℓ. Lean faithful (no c ∉ N(g) needed; b(ℓ) = 1 forced by parity). |
| 9 | Thm 3.3 (l.278–287) | SOUND (F7) | L1S Thm 4.3 + A = V ∖ N[c] admissible when there is no even vertex; L1S Cor 4.4. Requires the general form of L1*. |
| 10 | §3.3 text (l.289–295) | SOUND data, WORDING (F7, F8) | 456/320/168 reproduced. |
| 11 | Thm 3.4 (l.303–316) | SOUND as a proof sketch (N7); citation ERROR (F3); data claim ERROR (F1) | Checked against TM Thm 4.2 and Lemma 3.4: the only use of admissibility is the walking-back hypothesis. At step i the zero-end vertices are x, p_i and isolated vertices, so Z(p_i) ⊆ {x}. b(p_{i+1}) = 1 (for i + 1 = k: d_M(a) = d(a) − 2 ≥ 1, odd). T = {p_{i+1}} is a non-neighbour in the current graph, x ∉ T since x ∉ V(P), and b ≤ 1 throughout. Theorem 2.2 gives b − 1_{p_{i+1}} + 1_{p_i}, x untouched, vertex sets ⊆ old + p_i ∉ {x, a, ℓ₁, ℓ₂}. Steps 1 and 3 of TM are unchanged. |
| 12 | Summary table (l.321–333) | SOUND WITH FIXES | "literally tight? yes" for PTM rests on F1's distinction; "(R3) reduces to (R2)" (F7). |
| 13 | Conj 3.5 (l.337–343) | UNCLEAR (F11) | For GL, consistent with order 9 (every (instance, u) has a successful D′). For L1* it is ill-posed. |
| 14 | Prop 4.1 (l.353–366) | SOUND (trivial) | (1) b(s) = \|T\| ≤ 1. (2) b(L.src) = 2. Lean faithful. |
| 15 | §4 conclusions (l.368–378) | WORDING (F5) | Excludes a flower only as the last move. |
| 16 | Thm 5.1 (l.383–395) | SOUND (F6, N4) | J − z: even order, exactly four even vertices = N(z), all degrees positive. `emc_four` gives {r,x} or {r,y}. A realisation has (\|J\| − 5)/2 + 2 = (\|J\| − 1)/2 paths and 2 ends at r. Lean faithful; uses `lovaszStatement` (proved). |
| 17 | §5 remark (l.397–400) | WORDING (F6) | Already in TM Remark 7.3. |
| 18 | §6 Computations (l.402–455) | SOUND WITH FIXES | All committed numbers reproduced (§5). F1, F2, F4, F10, F13, N8. |
| 19 | §7 (l.457–474) | WORDING (F1, F5, F9) | |
| 20 | §8 Formalisation (l.476–496) | SOUND (N5) | Build, no sorry, axioms, full library up to date (§4). |
| 21 | Abstract, Results, Honest status | ERROR in one claim (F2), otherwise SOUND WITH FIXES | F2 (dichotomy), F5 (flowers), F6 (Test 1), F7 (one statement), F9 ("any proof"). |

## 3. Details

### 3.1 The dichotomy "the invariant survives iff the forced chain avoids p"

| setting | "avoids ⇒ survives" | "reaches ⇒ fails" | where |
|---|---|---|---|
| L∞ / GL residual, p = y | proved | proved | Proposition 3.1 |
| PTM no-walk, p = x (leaf graph) | proved (Fan chain, RD Lemma 2.2) | trivial: the chain is stuck, there is no transfer | Corollary 2.3(1) |
| L1* blocked, p = c, plain transfer in G | true, easy, **not written** | **false** at order 9 (F2); true at order 7 only; automatic only when the first hit is at step 1 and g ∈ A | E26(A), `exp1d_7*`; audit order 9 |
| L1* blocked, leaf graph | reaching c means stuck (Corollary 2.3(1)) | — | Theorem 3.2 is the sufficient form |

In the plain graph, when the chain first meets c at step i, the new Q_c is the re-routed Q_{i−1}. I checked this in RD's execution: later steps can re-route it only at its other end. So the result is good iff V(Q_{i−1}) ∩ A = ∅.

In the order-9 counterexample of F2, i = 2: Q_1 = 8 2 7 0 6 misses A = {1,3}.

Independent order-7 counts (`out/a_dichotomy_7*.txt`):

| order 7 | through c, step 1 (Q₀ ∋ g ∈ A: automatic) | step 2 | step 3 (Q₂ ∋ g) | step 4 | all bad |
|---|---|---|---|---|---|
| \|A\| ≤ 2 | 360 | 268 | 44 | 24 | 696/696 |
| A maximal | 257 | 167 | 68 | 23 | 515/515 |

### 3.2 Theorem 3.4 against TM

TM's walk theorem (Theorem 4.2) uses admissibility once: in Step 2, to verify the hypothesis of the walking-back Lemma 3.4 ("every vertex v ≠ w₀ adjacent to one of w₀,…,w_{k−1} has b ≥ 1"). The tight version cannot use Lemma 3.4 as a black box, because x is adjacent to some p_i and has b(x) = 0. The proof must redo the induction of Lemma 3.4 step by step. That is what "use Theorem 2.2 with B = {x} instead" means; the bookkeeping in item 11 of §2 shows it works.

The data claim is a different matter (F1). Among all successful walk-backs, 21 instances only ever succeed with e ∈ {p_{i+1}} ∪ N(p_i) at some tight step: the forced chain simply never visits e.

### 3.3 Flowers

- `flower_decomp`, `flower_decomp_rest` (Flower.lean) give a decomposition with ends `2·[v ∈ L] (+ endsL rest v)`. `hub_cycles` assumes b(s) = |T|, b = 1 on T and 0 elsewhere.
- The three negative lemmas are correct and faithful to Proposition 4.1. They are immediate from these end-count hypotheses.
- In ES §7 the flower arises after *grouped receipts at a hub s*, starting from a Lovász seed of G minus the star at s, so that b(s) = j ≥ 2 (not Lovász's induction). In ES Proposition 68 (B′) the flower output is post-processed (an append at x₁).
- So the fair statement is: a flower is never the last move towards a Lovász decomposition (F5).

### 3.4 Citations

| citation | target | status |
|---|---|---|
| [RD, Lemma 2.2] | Fan's lemma with vertex sets | correct |
| [RD, §8] | L∞ / GL residual (leaf case of Conj 8.2) | correct |
| [L1S, Lemma 2.4] | protected transfer | correct |
| [L1S, Lemma 2.3(ii)] | deleting a leaf at c | correct |
| [L1S, Theorem 4.3], [L1S, Corollary 4.4] | blocked ⇒ all; EE from blocked | correct |
| [L1S] (CP(3)+apex, certificates fail) | L1S Remark after Cor 4.4 | correct |
| [PE] (EE; open for ≥ 2 common neighbours) | PE Conj 1.5, Thm 5.1 | correct |
| [TM, Theorem 3.2] (walk theorem, twice) | TM Theorem **4.2** | **wrong (F3)** |
| [TM, E24(F)] | `research/experiments.md` E24(F) / TM §8 | **wrong target (F3)** |
| [TM] (Test 1 through STL) | TM §7 | correct, but TM Remark 7.3 not cited (F6) |
| [ES, §7] (flower lemma, receipt-or-flower, spare path) | ES §7 | correct |
| [ES] (endpoint matroid for four even vertices) | ES Theorem 21 (§5) | correct (no number given; add "Theorem 21") |
| [Fan05], [L68] | | correct |

## 4. Lean

- **Build.**
  - `export PATH=$HOME/.elan/bin:$PATH; cd lean; lake build GallaiLean.TightFan`: "Build completed successfully (18333 jobs)".
  - `lake env lean GallaiLean/TightFan.lean`: no output, 7.5 s.
  - `GallaiLean.lean` l.70 imports `TightFan`. `lake build --no-build` for the whole library: "All targets up-to-date (18392 jobs)". So "the full library builds" holds.
- **No sorry.** grep for `sorry|admit|^axiom|native_decide|implemented_by|unsafe|@[extern` in `TightFan.lean`: no hits.
- **Axioms.** Every one of the following gives `[propext, Classical.choice, Quot.sound]`:
  - `fanPre_protect`, `fan_exists_chain_protected`, `fan_grouped_protected_supp`, `fan_single_protected_supp`;
  - `fanPred_unique`, `pred_unique_of_isPath`, `succ_unique_of_isPath`;
  - `l1_tight_transfer`;
  - `lInfty_of_l1StarGen`, `lInfty_of_l1Blocked`, `ee_of_l1Blocked`;
  - `hub_cycles_card_le_one`, `flower_decomp_not_le_one`, `flower_decomp_rest_not_le_one`;
  - `test1_deg_four`, and also `emc_four` and `lovaszStatement`.

  The check file `A24AxiomCheck.lean` was run as `lake env lean` inside `lean/` and then deleted; a copy is in `A24-scripts/`.
- **Fidelity** (definitions printed with `#print`):

| Lean | manuscript | match / differences |
|---|---|---|
| `fan_exists_chain_protected D u T B huT hT hBT hB hsum` | Thm 2.2, existence and avoidance | exact (u = w). `hB : ∀ x z, (x ∈ T ∨ K.Adj x u) → FanPred D u x z → z ∉ B`; `hsum` counts `K.Adj u w ∧ ends w = 0 ∧ w ∉ B`. |
| `fan_grouped_protected_supp` | Thm 2.2, transfer | exact: size, `ends' + [t=w] = ends + [u=w]`, vertex sets ⊆ old + u. Does not state "unchanged on B" (F12). |
| `fan_single_protected_supp` | Thm 2.2, \|T\| = 1 | exact, with `v ∉ B` (v = source); G' = G − uv. |
| `fanPred_unique` | Prop 2.1 (first sentence) | exact: `D.ends x ≤ 1 → FanPred D u x z → FanPred D u x z' → z = z'`. |
| `l1_tight_transfer` | Thm 3.2 | exact. `hev : (evenSet G).card ≤ 1`, `hg : g ∈ evenSet G`; D₃ on `apex (delEdge G g x) {c}` with ends = d_{G−gx} mod 2 off c, 0 at c (b(ℓ) = 1 is forced by parity); leaf path avoids A; `hB` over `y = g ∨ Adj y x` in the leaf graph (= {g} ∪ N_{G−gx}(x)). Conclusion `AvoidDecomp G c A`. No c ∉ N(g) (docstring says otherwise, N1). |
| `LInfty` | L∞ (R1) | exact: `(evenSet G).card = 0`, c odd, ∃ Lovász D with Q_c ⊆ N[c]. |
| `lInfty_of_l1StarGen`, `lInfty_of_l1Blocked` | Thm 3.3 | exact; `L1StarGen` / `L1Blocked` have unbounded A (general form, F7). |
| `hub_cycles_card_le_one` | Prop 4.1(1) | exact (does not even need s ∉ T). |
| `flower_decomp_not_le_one`, `flower_decomp_rest_not_le_one` | Prop 4.1(2) | exact; they take the end-count conclusion of `flower_decomp(_rest)` as hypothesis. |
| `test1_deg_four J z h4 hconn : Test1 J z` | Thm 5.1 | `Test1` = (∀ v, Even (deg v) ↔ v = z) → ∀ r ∈ N(z), ∃ D of J − z with ≤ (\|V\|−1)/2 paths and ≥ 2 ends at r (N4). `hconn : (delVert J z).Connected`. Via `emc_four lovaszStatement`. |

## 5. Computations

**Re-runs of the authors' scripts** (scratch copy of `39f2d37`, `l1s` rebuilt with `gcc -O2`): every output is **byte-identical** to the committed `out/` file:
- `xcheck.txt` (1,772 queries, 0 mismatches);
- `exp1c_7`, `exp1c_7max`, `exp1c_9`, `exp1c_9max`;
- `exp1d_7`, `exp1d_7max`;
- `exp1e_7`, `exp1e_7max`;
- `linf7`, `ee_inst`, `ptm_nowalk68`.

**Numbers in §6 and E26 against `out/`:**

| claim | out/ | independent (audit) |
|---|---|---|
| 1,772 xcheck queries, 0 mismatches | xcheck.txt | re-run identical |
| 2,414 = 1,200 + 1,019 + 162 + 33; good u for every one; outside N(c): 162 + 33 + 637; only in N(c): 1,200 + 382 | exp1c_9 | re-run identical (l1s oracle) |
| A max, order 9: 12,622 = 7,832 + 4,790; 2,938 = 2,399 + 539 | exp1c_9max | re-run identical |
| order 7, \|A\| ≤ 2: 896 / 696 / 56; 14 + 5 instances | exp1d_7 | **reproduced** (`a_dichotomy.py`, own enumerator and chain): 896 / 696 / 56, 14 gA + 5 sep |
| order 7, A max: 930 / 515 / 618; 61 instances | exp1d_7max | **reproduced** |
| Thm 3.2 condition: 14 and 49 tight instances, never fails | exp1e_7, exp1e_7max | **reproduced**: SC 648 / noSC-avoid 248 / noSC-hit 696; max 772 / 158 / 515; 14/14 and 49/49 instances; the leaf chain is stuck exactly when the plain chain passes c (Corollary 2.3) |
| L∞ order 7: 3 instances, 54 + 14 | linf7 | **reproduced** (`b_linf.py`) |
| L∞ order 9: 133 instances; 409,416 = 202,636 + 152,816 + 53,964; y ∈ N(u) in 206,780; 53,964 fail exactly; 59 / 74; GL in all | linf9b | **reproduced exactly** (`b_linf.py`, full order-9 run, own code) |
| (not claimed) per target, GL, order 9 | — | every one of the 320 (instance, target) pairs has a successful D′ (271 have a tight D′, 49 none; `b_linf_peru.py`) |
| "result good iff the forced chain avoids c" (L1*, claimed exhaustive) | exp1d_7 (order 7 only) | order 7 reproduced; **false at order 9** (F2): in a 101-instance sample, 34,577 of 487,872 through-c tight transfers give a good result; counterexample H??FFf} |
| CP(3)+apex 456 / 320 / 168; double K4 108 / 108 / 108; triangle instances 0 good D′ at tight targets, 4/4 elsewhere | ee_inst | re-run identical |
| PTM: 832 = 68 + 764 NOBASE | — | `nowalk68.txt`, `nobase764.txt` = TM's `walk_8_0.txt` lines (anypath=0/1), exactly; `_s10` = every tenth line |
| PTM: 68/68 closed; shortest walk 2 in 63, 3 in 5 | ptm_nowalk68 | **reproduced**: 68 decompositions printed and verified by my own checker (`c_verify.py`: Lovász, both F-edges terminal, different paths, walk avoids b, x, non-admissible); independent re-run `c_independent.py`: 68/68; minimum over all orientations 63/5 (N8) |
| "closed by Theorem 3.4" | — | **47/68** (F1) |
| Fan image unique | not checked | true (F13) |

**(d) `tf.py`** (`check_tf.py`, against `mylib.py`):
- **Enumeration.** I compared the multisets of canonical decompositions from `tf.decomps` and from my path-growing enumerator, with no mismatches:
  - orders 3–5 with Lovász b and two random feasible b (87 cases, 350 decompositions);
  - orders 3–6 with Lovász b and one random b (282 cases, 20,114 decompositions);
  - all 853 connected graphs of order 7 with Lovász b (41,661 decompositions).

  No duplicates were produced; every decomposition was verified.
- **Pruning.** `avoid` and `region` pruning agree with post-filtering on 836 cases (orders 3–6).
- **Fan.** `fan_moves` was checked on every connected graph of order ≤ 7 with exactly one even vertex g, every u ∈ N(g) and every Lovász decomposition of G − gu: 82 cases at order 5 and 108,870 at order 7. In each case it gives exactly one result, equal (as a decomposition and as a chain sequence) to my forced chain executed per RD Lemma 2.2, and to my exhaustive search over all chains of distinct vertices.
- **Separation pruning.** `sep` pruning (used by `ptmwalk.py`) is validated indirectly. My separation-veto enumerator gives the same 68/47/21 outcome on every base graph of the 68 instances.

## 6. Summary

**Mathematics.** All proofs are correct. Theorem 3.4 is correct against TM's Theorem 4.2 and Lemma 3.4. The points I tried hardest to break all hold:
- the counting in Theorem 2.2 with B (the end→edge map is injective, and R ∩ B = ∅);
- the uniqueness of the vertex with predecessor p in Corollary 2.3;
- the blanks of x in Theorem 3.2;
- the tight steps of the walk back.

**Required corrections:**
- **F1:** Theorem 3.4 as stated closes 47, not 68, of the no-walk instances. Restate it with the forced-chain hypothesis, which closes 68, or correct the count.
- **F2:** the L1* half of the dichotomy is false at order 9: a chain through c can still give a good result, even in the minimal blocked shape. Only "avoids ⇒ succeeds" holds, as an unwritten lemma. Restate the central claim as "failure requires the chain to pass p".
- **F3:** TM Theorem 4.2 / Lemma 3.4, not Theorem 3.2.
- **F5–F7, F9:** tone down the flower, Test 1, "one statement" and "any proof" claims; credit TM Remark 7.3 and L1S Proposition 3.1; say "general form" of L1*.
- **F4:** fill or remove the placeholders, and recompile the PDF.

**Lean.** Builds, no sorry, standard axioms, faithful statements.

**Data.** Everything committed is reproduced, most of it independently.

## 7. Fixes applied (authors, after the audit)

| Finding | Action |
|---|---|
| F1 | Theorem 3.5 (tight walk) restated with the forced-chain hypothesis ("the forced chain does not reach x"), which is what closes 68/68. The static predecessor condition is kept as a sufficient condition (Corollary 2.3(3)), and the paper quotes 47/68 for it. Corollary 2.3(2) added. |
| F2 | "Survives iff the chain avoids p" replaced by "can fail only if the forced chain passes through p". New Lemma 3.2 (a chain avoiding c suffices) is proved on paper. The converse holds for L∞ (Prop. 3.1); for L1* the counterexample `H??FFf}` and the sample counts are reported. Abstract, Results, summary table, E26, README, §AB and ROADMAP are corrected. |
| F3 | Citations changed to TM Theorem 4.2, Lemma 3.4, Remark 4.3 and §8; E24(F) is cited as the experiment log. |
| F4 | Both placeholders filled (A24's order-9 sample; the PTM sample prefix of 15 instances, reported as such). The PDF is recompiled. |
| F5 | The flower section is retitled "Flowers do not fit"; the claim is limited to "cannot be the last move"; ES Prop. 68 is mentioned; "at any order", "structural fact" and "complete negative answer" are removed. |
| F6 | Theorem 5.1 is presented as a Lean packaging of TM Remark 7.3 / `rooted_four'`, under "J − z connected". |
| F7 | (R2) and Theorem 3.4 now say "general form" (L1S Conjecture 1.3); L1S Prop. 3.1 is credited; "implied by one statement" replaces "one statement"; the remark that the L∞ route avoids GL is added. |
| F8 | The CP(3) + apex text notes that L1S Theorem 4.2(c) also applies. |
| F9 | Changed to "a proof by this Case I step must control the decomposition"; A24's per-(instance, u) count is cited. |
| F10 | Now stated as automatic from the irreducibility filter. |
| F11 | Definition 2.4 is now a precise list of hypotheses, with kinds (a) and (b); the PTM steps are labelled as not Lovász steps (TM Remark 4.3). Conjecture 3.5 is replaced by Question 3.6 for GL, with the GL⁺ data. |
| F12 | "unchanged on B ∖ {w}". |
| F13 | `exp1d.py` asserts uniqueness, and A24's 108,870-case check is cited. |
| N1, N2 | Lean docstrings corrected (no proof changes). |
| N3–N8 | Applied: abstract wording; the "at most / at least" form of Theorem 5.1; the full not-formalised list; (R1) wording; the D₀ quantifier in Theorem 3.5; the minimum over orientations. |
