# Audit A40-followup: the revision 4973558 → 61abb4e of `manuscripts/ln`

**Auditor:** independent audit agent, 2026-11-28. **Scope:** `git diff 4973558 61abb4e -- manuscripts/ln`,
checked against `research/audit/A40-ln.md` (A40), `manuscripts/multi-token/multi-token.tex` (MT) and
`manuscripts/multi-sep/multi-sep.tex` (MS). Classes as in A40. **All line numbers refer to `ln.tex` at
61abb4e** (identical to the working tree). My scripts and outputs are in
`research/audit/A40-followup-scripts/`. I edited no other file and made no commit.

## Verdict

| item | verdict | main point |
|---|---|---|
| 1. A40 findings #2–#10 | **all resolved** | Every fix is correct. None overcorrects, and every quotation of A40 is accurate. |
| 2. Def 6.2 (Criterion R), Prop 6.3 and its proof | **OK** | The proof establishes every hypothesis of MT Thm 2.7 and of Lemma 6.1, for both tail forms and for case (a). Some implicit points are **MINOR**. |
| 3. Certificates vs Def 6.2 | **OK** | `routeR.py` searches a subset of Def 6.2. All 46,400 shipped lines satisfy its static conditions. |
| 4. Counterexamples (§7) | **OK** | They are stated correctly and are unsatisfiable. My own exhaustive enumeration and `lnsolve` both confirm this. |
| 5. Data | **OK**, one **MINOR** | The MTL2 rows (12 of 12), both validation lines and `sample10.py` (byte-identical output) all reproduce. The text misdescribes the sampling distribution. |
| 6. Overclaim; compilation | **OK**, two **MINOR** | L_N(2) is never claimed proved. The compilation is clean. |

No ERROR, GAP or OVERCLAIM. Nothing *must* be fixed. Three MINOR wording fixes are recommended (end of report).

## 1. A40 findings #2–#10

| A40 # | where now | check | verdict |
|---|---|---|---|
| 2 | ll. 193–196, 198–200, 204 | **Case 4.** Lemma 2.1 is applied with t = u and target x, and the count is 0 < 2 = b(u). This is correct: in K − ux every neighbour w ≠ u of x has unchanged odd degree and one end. Afterwards u and x each have one end.<br>**Case 5.** T = ∅ because tail leaves have degree 1. Then X = ∅, and failing Cases 1–4 forces every degree to be 0. Correct.<br>**Remark 3.2.** It now says "needed only in Case 2". | resolved |
| 3 | ll. 210–212, 430–442; README l. 10 | **Remark 3.2.** It now says "false in general", and keeps MTL2 open.<br>**§7.** It gives both examples and retracts the sampled claim.<br>**Counts.** The MTL2 counts 15,690 / 121,205 match A40 §1.2, including the shared-leaf instances. That is within "two tails, one head each", since T is a family. | resolved |
| 4 | ll. 44–45, 153–156, 205–206 | **Abstract.** "Every separated pair is a leaf and a vertex at distance ≥ 3" is exactly the containment: MS Thm (i) needs all of X sparse, while Theorem A needs only the heads sparse. The parenthesis on larger sets is correct.<br>**Remark 3.2.** "All heads, except possibly one tail leaf" is right. Two degree-1 neighbours, or d(g) = 2 with one tail leaf, fall under Case 2. | resolved |
| 7 | ll. 308–344, 411, 454 | Def 6.2(b) now has p ∉ {c_j, a_j} and both tail forms. Prop 6.3 supplies the proof (see §2). Conjecture 8.2 and l. 454 now go through Prop 6.3. | resolved |
| 8 | ll. 48–53 | Lemma R and Criterion R are now separate bullets, with "implies L_N(2) for that instance". One new imprecision remains: N2. | resolved |
| 9 | ll. 59–61, 236–258 | **§5.** It is declared informal. Fan's condition is stated as a hypothesis, the CLT condition is called "sufficient", and the obstruction is limited to specific invariants (`not_steerK`, `not_steerK_triangle`; checked in `MultiTokenObstruct.lean`).<br>**Drop claim.** The drop claim is now an order-8 observation. Its inference is valid: the Theorem-A-fin routes contain the one-tail-fin routes, and both counts are 31,532 in `coverage_order8.txt`. | resolved |
| 10 | ll. 267–269, 356, 373, 425, 458–460; data; scripts | The "free tokens" claim is qualified, and the degree-3 suppression now carries the S side conditions. The validation order is now ≤ 7. The MTL2 count 483 is added, plus a new noTS row. `sample10.py` and `validate_join.py` are shipped. A new issue: N1. | resolved |

Quotations of A40 checked against A40 and `A40-scripts/d_mutation.out`:
- l. 340, "317 … among 2,808";
- ll. 412–414, re-check "including (TI) after every move": A40 §3(c) checked exactly the conditions that Def 6.2 now states;
- l. 419, "1,800 … 0 disagreements";
- l. 430, "exhaustive search over n ≤ 9, confirmed with lnsolve";
- l. 472;
- README ll. 12–16.

All are accurate.

## 2. Definition 6.2 and Proposition 6.3: OK

I checked the proof against MT Def 2.1 ((TS), (TI)), Def 2.2 (M, D, S; at the end at most one token and one live tail) and Thm 2.7. I also checked the Lean `TailSys`, `TailInv`, `SteerK` and `steerK_good`, and Lemma 6.1.

- **Case (a)** (T = ∅). (TS) and (TI) hold vacuously, so Thm 2.7 gives a parity decomposition of K₀. Lemma 6.1(a) needs exactly p = c_j, a_j ∉ V(P), a_i ∉ V(P) and that decomposition. OK.
- **Case (b), τ = (ℓ, c_j, a_j)**, K = K₀ + c_jℓ.
  - (TS): a_j ≠ ℓ (ℓ is new) and a_j ≠ c_j (the pairs are disjoint).
  - (TI):
    - N_K(ℓ) = {c_j}.
    - a_j ≁ c_j holds in F, hence in K.
    - a_j is odd in K. In K₀ only c_i and p change parity, and a_j ∉ {c_i, p}. The edge c_jℓ changes only c_j, and a_j ≠ c_j. This includes a_j as an interior vertex of P, which happens in 3,732 of the order-8 certificates.
  - Thm 2.7 then gives what Lemma 6.1(b) assumes, and p ≠ c_j is part of Def 6.2(b). OK.
- **Case (b), leaf variant τ = (c_j, w, a_j)**, K = K₀.
  - (TS): a_j ∉ {c_j, w}.
  - (TI): N_{K₀}(c_j) = {w}, a_j ∉ N_{K₀}(w), and a_j is odd by the same argument.
  - This also holds when c_j is an interior vertex of P with d_F(c_j) = 3, which Def 6.2 allows and Lemma 6.1 covers (A40 §1.4).
  - Lemma 6.1's leaf variant is exactly the conclusion. OK.

Nothing false is used. The following points are used without being stated (N4, MINOR):
- τ is live in K, which Thm 2.7 needs;
- a_j ≠ c_j is used for the parity of a_j in K (it is stated only as part of (TS));
- τ is written in MT's triple notation (c, s, x), but ln's own tails are pairs (c, A) (Def 2.2), and the switch is not flagged;
- Lemma 6.1 implicitly needs P to have at least one edge ("other end p"). `routeR.py` enforces this.

N3 (MINOR, l. 338) concerns "The condition p ≠ a_j is needed. If p = a_j, then a_j is a token".
- It is needed **for the argument**: (TI) fails and a schedule need not certify. A40's 317 failures show this. It is not shown to be needed for the truth of Prop 6.3, because no instance failing L_N(2) is known.
- If d_F(a_j) = 1, then p = a_j leaves a_j isolated, not a token, and the constraint is trivial.
- Suggested wording: "is needed for the transfer: if p = a_j, then a_j is even or isolated in K, (TI) fails, …".

## 3. Certificates vs the wording of Def 6.2: OK

From reading `routeR.py`:
- **Paths.** P starts at c_i, has at least one edge and never contains a_i (`y != ai`). It stops on reaching c_j, so c_j is never interior.
- **Case (a).** P ends at c_j with a_j ∉ P, and there is no tail. This is Def 6.2(a).
- **Case (b).** P ends outside {c_j, a_j} (`P[-1] == aj: continue`).
  - The leaf variant is used exactly when d_{K₀}(c_j) = 1 with stem w and a_j ∉ {w} ∪ N(w); otherwise the ℓ form is used.
  - This is Def 6.2(b), with the choice between the two forms made deterministically. Both forms are allowed by the definition.
- **Moves.** (M), (D) and (S) are MT's moves (identical to Lean `SteerK`). The one difference: (S) additionally requires p ∉ X, which is redundant under (TI).
- **End test.** `len(tok) <= 1 and len(tails) <= 1`, where `tails` are the live tails. This is MT's end condition.

So every routeR certificate is a Def 6.2 certificate. The definition is broader: it allows P through c_j, the ℓ form when the leaf form applies, and S at a token in X. Prop 6.3 covers all of that.

A static re-scan of every shipped line (`defR_static.py`) checks:
- P is a path from c_i avoiding a_i;
- joint: p = c_j and a_j ∉ P;
- pre: p ∉ {c_j, a_j} and c_j ∉ P.

Result: **43,400 / 43,400 and 3,000 / 3,000** lines pass. The leaf-variant counts are 2,589 + 797 = 3,386 (order 8) and 100 + 5 = 105 (order 10), as in A40. I did not re-execute the certificates; A40 §3(c) did.

## 4. The counterexamples (ll. 433–437): OK

`cex_check.py` shares no code with `lnsolve` or `lnlib`. For each example it builds the graph from the stated edges, checks the leaf-tail conditions of Def 2.2, and enumerates **all** parity decompositions by exact cover.

| | n = 7 | n = 9 |
|---|---|---|
| graph6 (same as A40) | `FCRV?` | ``H?`@Fbp`` |
| degrees | 3,3,1,2,1,3,3 | 3,3,3,2,1,1,1,5,5 |
| only even vertex | 3 ✓ | 3 ✓ |
| connected | yes | yes |
| tails | (2,{5}), (4,{0,2}) | (4,{1,2,3}), (5,{0,2,3}), (6,{0,1,3}) |
| leaf of degree 1, heads far apart (Def 2.2) | ✓ | ✓ |
| heads sparse? | no (6 sees 0, 2; 3 sees 0, 5) | no (7 and 8 see all of 0–3) |
| "a tail avoids another tail's leaf" | yes (4 avoids 2) ✓ | no ✓ |
| parity decompositions | 24 | 984 |
| decompositions keeping every tail | **0** | **0** |
| deleting any single head | SAT | SAT |

The last row shows both examples are head-minimal. `lnsolve` with S constraints: UNSAT and UNSAT (`lnsolve_cex.out`).

## 5. Data and scripts

- **`mtl2_exhaustive.txt`: all 12 rows reproduced exactly** (`mtl2_rerun.out`). That is gen_mtl2 8 / 84 / 385 / 11,040; noTS evenx 40 / **483** / 1,192 / 38,100; noTS 40 / 399 / 1,192 / **30,912** (the new n = 9 row); all SAT. The row labels now match the flags of `gen_mtl2b.py`.
- **`validation.txt`: both lines reproduced exactly** (`validation_rerun.out`).
  - `validate.py lnsolve 7 1500 1` gives 880 / 620 / 0 / 0.
  - `validate_join.py lnsolve 600 3` gives 538 / 62 / 0 / 0.
  - `lnlib.brute` does enforce J: a path with an end in {p, q} must have exactly the ends {p, q}, and the all-odd graph gives r(p) = r(q) = 1.
- **`sample10.py`.** `nauty-geng -cq 10 | ./allodd_filter` gives 32,851 graphs (in 5 s). `sample10.py` on that list reproduces `order10_sample_instances.txt` **byte for byte** (`sample10_rerun.out`).
- **N1 (MINOR, ll. 372–373).** The text says the sample is "drawn uniformly over the 32,851 connected all-odd graphs and then over the pairs". That is not what `sample10.py` does.
  - On a rejected quadruple (c_i ~ a_i), the script redraws the **graph** too (`continue` at the top of the loop). So a graph is drawn with probability proportional to its number of admissible quadruples. The sample is uniform over (graph, quadruple) instances, and dense graphs are under-represented.
  - Measured mean edge count (`sample_bias.py`):

    | | mean edges | sd |
    |---|---|---|
    | graph-uniform | 22.59 | 3.74 |
    | quadruple-weighted | 21.35 | 3.59 |
    | the sample | 21.38 | — |

    The sample's z-score is −17.7 against graph-uniform and +0.5 against quadruple-weighted. Graphs with at least 35 edges are 0.2% of the population and appear once in 3,000 draws.
  - The script's docstring describes the procedure correctly. The manuscript sentence does not, and A40 §3(c)'s "consistent with uniform sampling" is superseded.
  - Fix the wording, not the data: "a graph and four vertices drawn uniformly, both redrawn if c_i ~ a_i (so graphs are weighted by their number of admissible pairs)".

## 6. Overclaim scan and compilation

- **L_N(2).** Every occurrence in `ln.tex` (ll. 26–454) and the README was checked.
  - L_N(2) is "not proved" (abstract l. 37, README l. 6) or "open" (table l. 102).
  - The new claims are all instance-level: abstract l. 53, table l. 97, l. 324, README l. 7.
  - **OK.**
- **New sentences of the abstract and status table.** They are accurate (MS containment; "informally"; table l. 97, "proved on paper (via MT Thm 2.7)"), with one exception:
  - **N2 (MINOR, abstract ll. 50–53).** "Otherwise a parity decomposition of F−E(P) with a leaf hung at c_j … finishes it" also covers the case p = c_j with a_j ∈ V(P). There Lemma 6.1 gives nothing: c_j would get two ends. Write "If P does not end at c_j". The abstract's paraphrase of Criterion R ("such a P together with a token schedule") also omits p ≠ a_j, the condition A40 found missing. Add "(P not ending at a_j)".
- **README** ll. 6–16, 25–27, 39–41 and 49–52 are accurate. The reproduce commands work as written (I ran the sample10 and validate commands).
- **N5 (MINOR, optional, pre-existing lines).**
  - Table l. 384: "Lemma R(a) with a free schedule — proved (Lemma 6.1)" uses the transfer theorem, so cite Prop 6.3.
  - §9 l. 489 lists Lemma 6.1 as not formalised but does not mention Prop 6.3.
- **Compilation** (scratch copy of the 61abb4e `ln.tex`, `latex.out`):
  - 8 pages; no errors; no undefined references or citations after run 2; **no overfull or underfull boxes**. The 3.8 pt box and the underfull boxes that A40 reported are gone.
  - Run 2 still prints "Label(s) may have changed": label `sec:R` moves from p. 5 to p. 4, and that page number is printed nowhere. A third run is fully clean.
  - Numbering: Def 6.2 (Criterion R), Prop 6.3, Conj 8.1 (MTL2), Conj 8.2 (R), matching README l. 7.
  - The text of the shipped `ln.pdf` equals that of my build (`pdftotext`).

## Findings

| # | finding | location (61abb4e) | class |
|---|---|---|---|
| F1 | A40 #2, #3, #4, #7, #8, #9, #10 resolved correctly, without overcorrection; A40 quoted accurately | see §1 | OK |
| F2 | Prop 6.3 proof complete: (TS) and (TI) in K for both tail forms, a_j odd including a_j interior to P, case (a) with T = ∅ | ll. 323–336 | OK |
| F3 | Implicit points: τ live; a_j ≠ c_j used for parity; MT triple notation not introduced; P has ≥ 1 edge | ll. 312–336, 272–273 | MINOR (N4) |
| F4 | "p ≠ a_j is needed" means needed for the argument; "a_j is a token" fails when d_F(a_j) = 1 | l. 338 | MINOR (N3) |
| F5 | routeR searches a subset of Def 6.2; all 46,400 certificate lines pass the static conditions | `routeR.py`, data | OK |
| F6 | Counterexamples n = 7 and n = 9 correct and UNSAT (independent enumeration and lnsolve) | ll. 430–438 | OK |
| F7 | MTL2 rows (12/12), validation (2/2) and sample10 (byte-identical) reproduce | data, scripts | OK |
| F8 | Sampling described as graph-uniform; it is weighted by admissible quadruples (z = −17.7) | ll. 372–373 | MINOR (N1) |
| F9 | Abstract "Otherwise" includes p = c_j with a_j ∈ P; Criterion R paraphrase omits p ≠ a_j | ll. 50–53 | MINOR (N2) |
| F10 | Table "R(a) … proved (Lemma 6.1)" should cite Prop 6.3; §9 silent on Prop 6.3 | ll. 384, 489 | MINOR (N5, optional) |
| F11 | L_N(2) never claimed proved; the build is clean | throughout | OK |

## To fix

**Nothing must be fixed:** there is no ERROR, GAP or OVERCLAIM. Recommended wording fixes:
1. **N1** (ll. 372–373): describe the sample as uniform over (graph, quadruple) instances, with the graph redrawn on rejection, so dense graphs are under-weighted.
2. **N2** (abstract ll. 50–53): "If P does not end at c_j" instead of "Otherwise", and add "P not ending at a_j" to the Criterion R paraphrase.
3. **N3** (l. 338): "needed for the transfer"; "a_j is even or isolated".

Optional: N4 (state that τ is live and introduce the triple notation, citing MT Def 2.1) and N5 (cite Prop 6.3 in table l. 384 and in §9).

## Reproduction (from `research/audit/A40-followup-scripts/`; L = `../../../manuscripts/ln`)

    python3 -I cex_check.py                                   # cex_check.out
    gcc -O2 -o lnsolve $L/scripts/lnsolve.c && ./lnsolve < lnsolve_cex.in   # lnsolve_cex.out
    for f in routeR_order8.txt routeR_order10_sample.txt; do python3 -I defR_static.py $L/data/$f; done
    gcc -O2 -o allodd_filter $L/scripts/allodd_filter.c; nauty-geng -cq 10 | ./allodd_filter > allodd10.g6
    (cd $L/scripts && python3 sample10.py $OLDPWD/allodd10.g6) | cmp - $L/data/order10_sample_instances.txt
    python3 -I sample_bias.py allodd10.g6 $L/data/order10_sample_instances.txt   # sample_bias.out
    cd $L/scripts; for n in 6 7 8 9; do nauty-geng -cq $n | python3 gen_mtl2b.py noTS evenx | lnsolve | cut -d' ' -f1 | sort | uniq -c; done   # likewise noTS, gen_mtl2.py
    python3 validate.py lnsolve 7 1500 1; python3 validate_join.py lnsolve 600 3      # validation_rerun.out

Not redone: re-execution of the certificates, the Lean build, and A40's own searches (A40 §§2–3).
