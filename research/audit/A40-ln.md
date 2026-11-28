# Audit A40: the multi-tail leaf theorem, Lemma R and Criterion R, session `claude/ln`

**Auditor:** independent audit agent, 2026-11-28. **Scope:** `manuscripts/ln/ln.tex`,
`lean/GallaiLean/LeafTails.lean`, and the scripts and data in `manuscripts/ln/` (items 1 to 4 of the
brief). My scripts are in `research/audit/A40-scripts/`. I edited no other file and made no commit.

## Verdict

| item | verdict | main finding |
|---|---|---|
| Theorem A (Section 3), proof | **OK** | All five cases are correct, including the degree and parity bookkeeping; the Lean proof matches. Exhaustive test: 0 failures in 60,312 hardest-family instances (all graphs with n ≤ 9, and connected all-odd graphs with n = 10). |
| Corollary B (Section 4) | **OK** | — |
| Lemma R (Section 6) | **OK** | Correct as stated, and it covers every certificate that `routeR.py` produces (item 4). |
| Criterion R (Def 6.2) and "Conjecture R ⇒ L_N(2)" | **GAP** | The definition omits "P does not end at a_j" (that is, (TI)) and the leaf-variant tail. Without them a schedule does not certify Lemma R(b): 317 failing executions found. |
| Remark 3.2, "the statement without sparseness held in every test", and §7 l. 384 | **OVERCLAIM** | Counterexamples at n = 7 and n = 9. The second has no tail avoiding another tail's leaf. MTL2 itself survives. |
| Abstract, status table, §§5, 7, 8 | **OK on L_N(2)**: it is never claimed proved. Some **OVERCLAIM** and **MINOR** wording. | — |
| Lean `LeafTails.lean` | **PASS** | Builds; no `sorry`; standard axioms; statements faithful; both theorems fire on a concrete instance. |
| Computations (a)–(d) | **PASS** | The solver cross-check, the data and the bug fix all check out. Every certificate was re-checked and re-executed by my own code. |

No ERROR was found in any proof.

## 0. Versions audited

The session committed twice while the audit ran.
- I started on the untracked draft (md5 `78a02090…`, 420 lines).
- The primary version is commit `4973558` (`ln.tex` md5 `48794646…`, 444 lines). **All line numbers below refer to it.**

`4973558` changes four things:
- It fixes two reference pointers, `[CLT, Thm 3.2]` and "route-descent Rem. V.4".
- It adds the certificate table, the "bug found by the executor" paragraph and the solver-validation paragraph to §7.
- It removes a 110 pt overfull box in §9.
- It adds the data files `routeR_order8.txt` and `routeR_order10_sample.txt` (with summaries), `order10_sample_instances.txt`, `validation.txt`, and the scripts `summarize_routeR.py` and `r1count.py`.

Unchanged throughout: `LeafTails.lean` (md5 `2bfce370…`), `routeR.py` (`6ece0bda…`) and `lnsolve.c` (`9fffbadd…`).

**Not audited.** As the audit ended, a further uncommitted revision of `ln.tex` appeared (md5
`527966a9…`, +127/−61 lines), together with `sample10.py`, `validate_join.py` and edited data files.
A skim of its diff suggests it addresses findings #3, #4, #7, #8 and #9:
- a restated Criterion R with "p ∉ {c_j, a_j}" and the leaf-variant tail;
- a new Proposition R;
- the counterexamples are cited;
- §5 is marked informal.

I did not check it.

Compilation of a scratch copy (`pdflatex`, twice) gives 7 pages, with no undefined references and no
errors. Warnings:
- an overfull hbox of 3.8 pt (status table, ll. 91–92);
- an overfull vbox of 1.6 pt;
- underfull hboxes at ll. 91–92, 309–311 and 411–415.

Numbering in the compiled version: Conj 1.1 (L_N), Lemma 2.1 (Fan), Def 2.2, **Theorem 3.1 (= Theorem A)**,
Rem 3.2, **Cor 4.1 (= B)**, **Lemma 6.1 (= R)**, Def 6.2 (Criterion R), Conj 8.1 (MTL2), Conj 8.2 (R).

## 1. The manuscript

### 1.1 Theorem A: OK (proof checked line by line)

The measure is ν = Σd + [no even vertex]. In every case the child has at most one even vertex, its tails
are leaf tails and its heads are sparse. Leaves of degree 1 are never the even vertex z, are never
x (d(x) ≥ 3), and are never the Fan target u (u ∉ L), so their degree is unchanged. Far-apartness and
sparseness pass to subgraphs.

- **Case 1 (`lt_case_target`).**
  - In K − zu only u can be even. z has one end. A neighbour of u with no end would be even in K − zu, hence equal to u.
  - So Fan's count is 0 < 1. The target u is neither a head nor a tail leaf, so `keepsTails_of_cover` applies.
  - ν drops by at least 1. OK.
- **Case 2 (`lt_case_path`).**
  - Neighbours of z lie in X ∪ L, and by sparseness at most one lies in X. With d(z) ≥ 2, either two neighbours have degree 1, or N(z) = {c, y} with d(c) = 1.
  - (i) y is a leaf: in K′, y is isolated and z is even or isolated. (ii) d(z) = 2: z is isolated and y is even or isolated.
  - Restoring c z y gives ends 1 at c, 1 at y (d(y) is odd) and 0 at z.
  - For a tail at c, z ∈ N(c) and y is at distance 2, so neither is a head; the same holds at y. Tails at c or y are dropped from T′ because their leaf is isolated.
  - ν drops by at least 3. OK.
- **Case 3 (`lt_case_leaf`).** w becomes even or isolated. The path vw keeps the tails at v and at w (if w is a leaf), since a head is neither the leaf nor adjacent to it. OK.
- **Case 4 (`lt_case_big`).**
  - The graph H = K − ux + uℓ has x as its only even vertex (d(x) − 1 ≥ 2) and the same Σd, so ν(H) = ν(K) − 1.
  - A tail leaf equal to u stays a leaf. The far-apart condition survives: ℓ is adjacent only to u, so it is not a common neighbour of any leaf c and head a ≠ c. Sparseness survives for the same reason.
  - After deleting ℓ, u has 0 or 2 ends (parity, and at most one extra end). With 0 ends, add the path ux: x is adjacent to u, so it is not a head of a tail at u, and x is not a leaf. With 2 ends, apply Fan towards x ∉ X ∪ L.
  - OK.
- **Case 5 (`lt_case_empty`).** OK.

Minor points:
- MINOR (Case 4, ll. 184–189): Fan's hypothesis is not stated. It is b(u) = 2 > 0: every neighbour w ≠ u of x in K − ux is odd, so it has an end.
- MINOR (Case 5 vs Remark 3.2, l. 197): "sparseness enters only in Case 2" is true in substance, but the written proof of Case 5 (and `lt_case_empty`) invokes sparseness. It is not needed: with no vertex of degree 1, T = ∅ (every tail leaf has degree 1), so X = ∅ and all degrees are 0. Simplify Case 5, or say "is needed only in Case 2".
- MINOR (Rem 3.2, l. 198): "the residual is an even vertex g whose neighbours are all heads". In fact g may also have one leaf neighbour.
- MINOR (l. 44, §3 bullet 3): "the leaf case of sparse separation" is contained only for two-element sets {c, a} with c a leaf. For a larger packed set, `MeetsOnce` also separates the heads from each other, and Theorem A does not give that.
- The three comparison claims (TRN Lemma 6.1 = one tail, |A| = 1, x odd; MT Lemma 2.6; MS) are otherwise accurate. I checked them against `avoid_leafTail`, `tailGood_fin` and `separation_sparse`/`SparseFam`.

### 1.2 Remark 3.2 and §7 (sets): OVERCLAIM, with counterexamples

Remark 3.2 ends: "The statement without sparseness held in every test." Theorem A without sparseness
is **false**. My own exhaustive search (`b_thmA.py full`, `b_core.py`) finds deletion-minimal failures, which `lnsolve` confirms:
- `FCRV?` (n = 7, one even vertex):
  - edges 0–3, 0–5, 0–6, 1–4, 1–5, 1–6, 2–6, 3–5;
  - tails (2, {5}) and (4, {0, 2});
  - UNSAT. Here tail 4 avoids the other tail's leaf 2.
- `H?`@Fbp` (n = 9, one even vertex 3):
  - leaves 4, 5, 6 at the stems 0, 1, 2; the stems and 3 are joined to both 7 and 8; 7–8 is an edge;
  - tails (4, {1,2,3}), (5, {0,2,3}), (6, {0,1,3});
  - UNSAT, and the whole family is the minimal core.
  - **No tail avoids another tail's leaf.** This contradicts the suggestion of §7, l. 384 ("never failed either, as long as no tail avoids another tail's leaf"). That sentence reports a sample; the exhaustive n = 9 search finds this one failure (`b_thmA.py fullnoleaf`: 0 / 323 at n ≤ 8, 1 / 4,909 at n = 9).

Conjecture MTL2 itself (two tails, one head each) survives:

| order | graphs searched | instances | failures |
|---|---|---|---|
| n ≤ 8 | all graphs, incl. disconnected | 15,690 | 0 |
| n = 9 | all graphs, incl. disconnected | 121,205 | 0 |

These counts include the cases c₁ = c₂ (one tail with two heads) and heads equal to the other leaf.

Fix: "held in every test for two tails with one head each (Conjecture MTL2). For larger head sets it fails (examples above)."

### 1.3 Corollary B: OK
- In F + cℓ, c is the only even vertex.
- (ℓ, {a}) is a leaf tail: the only common neighbour candidate is c, and a ≁ c.
- The tails of T keep degree 1, because their leaves differ from c. Their far-apart condition survives, because ℓ is adjacent only to c and c is not a leaf of T.
- The heads stay sparse.
- c has 0 ends in the Theorem A decomposition, so the ℓ-path continues past c, and deleting ℓ gives Q(c) avoiding a.
- The sentence "So L_N(m) holds whenever all tails but one are leaves … heads sparse" (ll. 222–223) follows correctly. The pairs are disjoint, so the leaves differ from c.

### 1.4 Lemma R: OK
(a) In K₀ = F − E(P), c_i and c_j are even and every other vertex is odd: interior vertices of P lose two edges and stay odd, with degree ≥ 1. Adding P to a parity decomposition gives one end everywhere, and Q(c₁) = Q(c₂) = P. Correct.

(b) I checked the proof in every configuration the statement allows:
- **c_j an interior vertex of P.** Its degree in K₀ is d − 2, odd. P contributes no end at c_j, and Q(c_j) = P_ℓ − ℓ. Correct.
- **p = a_j.** The lemma is still correct: a_j has 0 ends in D_K and gets its end from P. Lemma R does not need p ≠ a_j; only the schedule certification does (§1.5).
- **Leaf variant, "c_j a leaf of K₀".** This includes the case d_F(c_j) = 3 with c_j interior to P. The path of D₀ through c_j ends there and avoids a_j. Correct.
- In every case c_i and p have 0 ends in D_K, because c_j ∉ {c_i, p}. So D₀ ∪ {P} is a Lovász decomposition with Q(c_i) = P.

**Item 4 of the brief: the match with `routeR.py` is exact, in the inclusion direction.**
- routeR's case (a) is "P ends at c_j, a_j ∉ P, no tail", and its search is on K₀. This is Lemma R(a).
- routeR's case (b) has P ≠ c_j at the end, P never through c_j (the search stops at c_j), and P not ending at a_j. Its tail is (ℓ, c_j, a_j), or (c_j, w, a_j) when c_j has degree 1 in K₀ and a_j ∉ {w} ∪ N_{K₀}(w). This is Lemma R(b), with stronger side conditions.
- Every certificate therefore satisfies the hypothesis of Lemma R(a) or (b). Lemma R is more general than what routeR searches.

The remarks after the lemma are correct, in particular the Conjecture 31 sentence, ll. 287–292. For a
2-connected K₀, c₁ and c₂ have degree ≥ 2 and are exactly the two even vertices. "No vertex of degree
n − 1" is stronger than Conjecture 31's "no odd universal vertex".

### 1.5 Definition 6.2 (Criterion R) and "By Lemma R, Conjecture R implies L_N(2)" (l. 397): GAP
The definition says: certified by "a token schedule (moves M, D, S of [MT, Def 2.2])", with, in (b),
"the single tail (ℓ, c_j, a_j)". Two things are missing.

1. **P must not end at a_j.** The transfer theorem [MT, Thm 2.7] (`steerK_good`) needs (TS) and (TI) in K. (TI) requires the head a_j to be odd, and that fails exactly when p = a_j.
   - MT's move (S) excludes heads only through (TI).
   - Without it, a schedule in the sense of Def 2.2 does not certify Lemma R(b). `d_mutation.py` allows P to end at a_j, tries only such P, and executes every schedule found with my executor. Over 1,500 random order-8 instances: **317 of 2,808 schedules fail** (the leaf path meets a_j). All 317 suppress the head.
   - With "never suppress a head" but p = a_j still allowed, 0 of 2,807 fail.
   - §7 (ll. 368–372) now describes the bug and the fix correctly, but the definition and Conjecture 8.2 do not contain the fix.
2. **The leaf-variant tail (c_j, w, a_j)** is used by `routeR.py` but is not in the definition. It carries **3,386 of the 28,547** order-8 (b) certificates and 105 of the 2,263 at order 10.

So the stated implication "Conjecture R ⇒ L_N(2)" is not justified for the definition as written.

Fix: in Def 6.2, require in (b) that p ≠ a_j. The tail is then (ℓ, c_j, a_j), or (c_j, w, a_j) when c_j is a leaf of K₀ with stem w and a_j ∉ {w} ∪ N(w). Then (TS) and (TI) hold in K, and MT Thm 2.7 gives the hypothesis of Lemma R. An alternative is "no move suppresses a head", with Theorem A (which allows the even vertex to be the head) as the fin. Conjecture 8.2 inherits whichever definition is chosen.

All shipped certificates satisfy the stricter definition (§3(c)), so the computational claims are unaffected.

### 1.6 Abstract and status table: L_N(2) is never claimed proved (OK); one MINOR
- Places that state L_N(2) is not proved or open:
  - abstract l. 37: "We do not prove L_N(2)";
  - status table l. 97: "L_N(2) open";
  - §8: "Conjecture R implies L_N(2)";
  - README: "L_N(2) is **not** proved".
- No sentence implies otherwise.
- "Criterion R … proved; executed" (table, l. 346) refers to the route, given (TI) (§1.5).
- MINOR (abstract, ll. 47–50), Lemma R bullet:
  - "then L_N(2) holds" should read "then this instance satisfies L_N(2)".
  - The token-schedule part is Criterion R plus MT Thm 2.7 under (TI). It is not Lemma R, which assumes a parity decomposition.
- The other abstract claims, Theorem A and Corollary B, match the theorems.

### 1.7 Section 5: OVERCLAIM (heuristics stated as facts)
- l. 227: "Every Fan-type proof keeps at most one even vertex at a time".
  - This is false as stated: MT's schedules carry k tokens, and Criterion R carries three.
  - What is true is that Fan's inequality (b(t) = 1 > #neighbours of u with no end) fails when the target is adjacent to a second token.
- Abstract l. 56 ("we explain why … two tokens cannot be retired in dense graphs") and l. 236 ("In a dense graph no such vertex is reachable") are informal. Only `not_steerK` / `not_steerK_triangle`, for specific invariants, are theorems.
- ll. 242–243: "every schedule that reaches one token with sparse heads can also drop a tail". This is an observation at order 8 (31,532 = 31,532, `coverage_order8.txt`), stated as a general fact.
- MINOR (ll. 232–233): "survives a Fan step **only if** the target avoids N[c]". CLT's "Fan transfers carry systems" (Thm 5.2 in the compiled CLT) is a sufficient condition, not a necessary one. The draft's pointer "[CLT, Thm 3.2]" was Conjecture CLT-B; this is fixed in `4973558`.

### 1.8 Sections 6, 7 and 8: MINOR
- l. 255: "Those tokens are free: no tail restricts their targets". In (b) the tail (ℓ, c_j, a_j) still forbids the targets ℓ and a_j. This is true only in (a).
- l. 401 (§8, bullet 1): "If c_i has degree … three, the token at c_i … can be suppressed". (S) needs its two remaining neighbours to be non-adjacent, not tail leaves, and not {x, s}. In a triangle it cannot be suppressed.
- §8, bullet 2 is correct. P = c₁ u₁ … u_k c₂ through all universal vertices avoids a₁ and a₂, because c_i ≁ a_i means neither a_i nor c_i is universal.
- l. 317 vs l. 375 and `validation.txt`: "order ≤ 8" vs "order ≤ 7". The J validation ("600 instances of order 6 and 8") has no output file or command line.
- l. 381 and `mtl2_exhaustive.txt`:
  - The data file labels the second row "noTS evenx", but its n = 7 count 399 is for odd heads (`gen_mtl2b.py noTS`). With even heads allowed the count is 483. I computed both; all are satisfiable.
  - The other seven MTL2 counts are reproduced exactly (§3(b)).
- §7, ll. 332–333: the order-10 sampler (seed 11) is not among the scripts.

## 2. Lean (`LeafTails.lean`): PASS

- **Build.**
  - `lake build GallaiLean.LeafTails` and the full `lake build` (18,440 jobs) succeed.
  - There are deprecation warnings only (`if_pos`/`if_neg`), plus one unused-section-variable lint (`KeepsTails.avoid`).
- **No `sorry`.** There is no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by` or `unsafe`.
- **Axioms.**
  - `A40-scripts/A40Check.lean` prints `[propext, Classical.choice, Quot.sound]` for `leaf_tails`, `lovasz_avoid_leafTails`, `lt_strong`, the five `lt_case_*`, `keepsTails_of_cover`, `PathDecomp.add_path2_supp` and `KeepsTails.avoid`.
  - This matches `data/axioms.txt`.
- **Faithfulness.** The definitions printed by Lean match the manuscript:
  - `LeafTails G T := ∀ t ∈ T, deg t.1 = 1 ∧ ∀ a ∈ t.2, FarApart G t.1 a`, where `FarApart` = (c ≠ a, ¬ c ~ a, no common neighbour) from `Separation.lean`;
  - `heads T = ⋃ t.2`;
  - `KeepsTails D T`: no path through t.1 meets t.2;
  - `SparseIn G X`: no vertex has two distinct neighbours in X;
  - `evenSet` = vertices of positive even degree.
- **The two headline statements.**
  - `leaf_tails`: `(evenSet G).card ≤ 1 → LeafTails G T → SparseIn G (heads T) → ∃ D, (∀ v, D.ends v = deg v % 2) ∧ KeepsTails D T`. This is Theorem A word for word.
  - `lovasz_avoid_leafTails`: evenSet empty; c of odd degree; c ≠ a; ¬ c ~ a; leaf tails with leaves ≠ c; `SparseIn G (insert a (heads T))`. The conclusion is a parity decomposition with every path ending at c avoiding a, and `KeepsTails`. This is Corollary B.
  - `fan_single_supp` is Lemma 2.1, with the count over the neighbours of the target.
- **Non-vacuity, machine-checked.** `A40Instance.lean` builds G on Fin 6 (edges 01, 12, 13, 34, 35) and discharges every hypothesis by `decide`:
  - `leaf_tails` fires with T = {(0, {4})};
  - `lovasz_avoid_leafTails` fires with c = 2, a = 4 and T = {(5, {0})};
  - both use the standard axioms only.

## 3. Computations

My solver `trsolve.c` shares no code with `lnsolve.c` or `lnlib.py`, and uses a different method.
- It enumerates **transition systems**: at each vertex, a choice of r(v) end half-edges and a perfect matching of the rest.
- Chains are kept in a union-find structure with vertex masks. A pairing is allowed only if the two chains meet exactly in the current vertex, so every chain is a path.
- The constraints A, S, J and R are checked on the masks.
- It uses a failure memo at vertex boundaries (128-bit hashed keys; off when a J constraint is present) and randomised restarts.
- Every SAT answer is checked by my own checker, `a40lib.check`.

### (a) lnsolve vs trsolve: AGREE (0 mismatches in 1,800)
`a_crosscheck.py` draws random graphs of orders 3–9, 60% of them repaired to at most one even vertex by
pendant leaves. It adds random A, S, J and R constraints: A in 912 instances, S in 710, J in 557, R in 327.

| result | count |
|---|---|
| SAT | 694 |
| UNSAT | 1,106 |
| disagreements | 0 |
| bad witnesses, either solver | 0 |

Nine lines exceeded trsolve's default budget. All nine came out UNSAT, as `lnsolve` says:
- the five without J by a long run;
- the four with J by path splitting (`a_jsplit.py`).

I also read `lnsolve.c`. It branches completely on all paths from one vertex with an unspent end, its
memo key (remaining edges, end vector) is exact and sufficient, and every pruning rule is a valid
necessary condition. **OK.**

### (b) Theorem A, exhaustive with an own generator: 0 failures
`b_thmA.py` takes every graph with at most one vertex of positive even degree and at least one leaf
(disconnected graphs included). Keeping is monotone in A_c, so every admissible family is dominated
by the family A_c = X ∩ far(c) for some *maximal* sparse X ⊆ ⋃ far(c). Testing those families is therefore exhaustive.

| population | graphs | hardest families | SAT |
|---|---|---|---|
| all graphs, n ≤ 8 | 372 | 975 | 975 |
| all graphs, n = 9 | 4,991 | 18,311 | 18,311 |
| connected all-odd, n = 10 | 10,060 | 41,026 | 41,026 |

Every witness was checked. The non-sparse variants are in §1.2.

MTL2 counts from §7, reproduced with my own generator (`b_mtl2count.py`), all satisfiable:
- (TS) setting: 8 / 84 / 385 / 11,040 at n = 6, 7, 8, 9 (exact);
- no-(TS) setting: 40 / 1,192 / 38,100 at n = 6, 8, 9 (exact); at n = 7 see §1.8.

### (c) Data: every certificate re-verified and re-executed by my own code
- **Instance sets.**
  - `gen_inst.py` regenerates order 8 from `nauty-geng -c 8`: 224 graphs and 43,400 instances, the **identical multiset** to `routeR_order8.txt`.
  - `count_odd.c`: `nauty-geng -c 10` gives 11,716,571 graphs, of which 32,851 are all-odd (as stated).
  - All 3,000 order-10 sample graphs are in that list. They cover 2,859 distinct graphs, which is consistent with uniform sampling, and the routeR file lists exactly the sample instances in order.
- **`c_data.py`, on all 43,400 order-8 lines and all 3,000 order-10 lines.** On every line it does the following:
  1. it checks the instance (connected, all degrees odd, disjoint non-adjacent pairs);
  2. it decides the instance by trsolve and checks the witness;
  3. it recovers the certificate with `routeR.find` (search only) and checks that P, the number of moves and the route kind equal the data line;
  4. it checks the certificate against MT Def 2.1/2.2 with my own code:
     - P is a path from c_i avoiding a_i;
     - in the joint case P ends at c_j and avoids a_j; otherwise P does not end at a_j and the tail is (ℓ, c_j, a_j) or (c_j, w, a_j);
     - (TS) holds, and **(TI) holds after every move**;
     - every M, D and S move is legal;
     - at most one token and one live tail remain at the end;
  5. it executes the certificate with my own executor: the bottom by trsolve, then each move undone with my own Fan chain, drop path or subdivision. Every level is checked, and then the final Lovász decomposition with a_i ∉ Q(c_i).

  Result: **43,400 / 43,400 and 3,000 / 3,000 pass every step.**

  The shapes reproduce the summaries:
  - order 8: joint 14,853, (b) 28,547 (with ℓ 25,161; leaf variant 3,386);
  - order 10: joint 737, (b) 2,263 (leaf variant 105).
- **Coverage table, reproduced with my own code.**
  - "Joint decomposition (exact)": **40,538 exactly** (`e_joint8.py`, trsolve, witnesses checked).
  - "Lemma R(a) with a free schedule": **40,532 exactly** (`e_freesched.py`, an own search over paths and M/S schedules).
  - Not reproduced: 31,532 and 32,837 (two-tail schedules), 42,904 (union), the m = 3 numbers (637 / 643), 38,908 (single edge), and "287 rejected".

### (d) The routeR fix: CORRECT
From reading `routeR.py`:
- **P.** In case (b), `P[-1] == aj` is skipped.
- **(M).** The target u must be odd and outside X = {leaf, head}, and no token other than p may be adjacent to u. This is exactly Fan's hypothesis (count 0 < 1). The new paths lie in old paths plus u ∉ X, so the tail is kept.
- **(D).** It acts only when the stem is odd. The added path c s misses x, by (TS).
- **(S).** It needs deg p = 2, p ∉ X ("heads are never suppressed"), a ≁ b, a and b not leaves, and {a, b} ≠ {x, s}. Subdivision adds only p ∉ X.

Hence no move can put a head on the leaf path. The bottom has at most one token and one live tail
satisfying (TI), so it is solvable by Theorem A or MT Lemma 2.6. The executor checks every level and
the final decomposition with `check_witness`, which is complete (simple paths, exact cover, end
counts, avoidance, separation).

My legality check confirms that (TI) holds at every level of all 46,400 certificates. With (TI), a
head is always odd, so it cannot be suppressed anyway. In the mutation test (§1.5), suppressing the
head was the only failure mode of the unguarded search: every one of the 317 failures does it, and with
heads protected there were none in 2,807 schedules.

## 4. Summary of findings

| # | finding | location | class |
|---|---|---|---|
| 1 | Theorem A proof (Cases 1–5), Lean-matched | §3 | OK |
| 2 | Case 4: Fan's count not stated; Case 5 uses sparseness needlessly (T = ∅ there) | ll. 184–193, 197 | MINOR |
| 3 | "without sparseness held in every test" / "never failed as long as no tail avoids another tail's leaf": counterexamples `FCRV?` (n = 7) and `H?`@Fbp` (n = 9, no tail avoids a leaf) | ll. 202, 384 | OVERCLAIM |
| 4 | "leaf case of sparse separation" holds only for two-element sets; residual description in Rem 3.2 | ll. 44, 148, 198 | MINOR |
| 5 | Corollary B | §4 | OK |
| 6 | Lemma R (a), (b), leaf variant; covers all routeR certificates | §6 | OK |
| 7 | Def 6.2 omits p ≠ a_j ((TI)) and the leaf-variant tail; "Conjecture R ⇒ L_N(2)" unjustified as written (317 failing executions without the guard) | ll. 294–299, 397 | GAP |
| 8 | Abstract: "then L_N(2) holds"; schedules attributed to Lemma R | ll. 47–50 | MINOR |
| 9 | §5: "every Fan-type proof keeps at most one even vertex"; dense-graph and drop-a-tail claims stated as facts; CLT "only if" | ll. 56, 227–243 | OVERCLAIM (wording) |
| 10 | "tokens are free"; degree-3 suppression; validation order ≤ 8 vs ≤ 7; MTL2 n = 7 count 399 vs label; no sampler or J-validation output | ll. 255, 317, 375, 381, 401 | MINOR |
| 11 | L_N(2) never claimed proved | abstract, table, §8, README | OK |
| 12 | Lean build, no sorry, axioms, faithfulness, non-vacuity | `LeafTails.lean` | OK |
| 13 | lnsolve validated (1,800 instances, 0 mismatches) | (a) | OK |
| 14 | Theorem A exhaustive (60,312 hardest families: all graphs n ≤ 9, connected all-odd n = 10) | (b) | OK |
| 15 | all 46,400 certificates re-verified, legal under (TS)/(TI), re-executed; 40,538 and 40,532 reproduced | (c) | OK |
| 16 | routeR fix correct; no other move can violate the tail | (d) | OK |

**To fix before release:** #7 (the definition of Criterion R and Conjecture R), #3 (the claims
without sparseness) and #9 (the Section 5 wording). Everything else is minor.

## 5. Reproduction (from `research/audit/A40-scripts/`)

    gcc -O2 -o trsolve trsolve.c; gcc -O2 -o lnsolve ../../../manuscripts/ln/scripts/lnsolve.c; gcc -O2 -o count_odd count_odd.c
    python3 a_crosscheck.py ./lnsolve 800 40 8; python3 a_crosscheck.py ./lnsolve 400 41 7 9; python3 a_crosscheck.py ./lnsolve 600 42 8 9
    grep ' J ' undec_lines.txt | python3 a_jsplit.py                      # (a) J lines left undecided
    ./trsolve -nomemo -b 16000000000 < undec_nonJ.txt                      # (a) the other five
    for n in 3 4 5 6 7 8 9; do nauty-geng -q $n | python3 b_thmA.py sparse; done   # (b) Theorem A
    nauty-geng -cq 10 | ./count_odd > allodd10.g6; python3 b_thmA.py sparse < allodd10.g6
    nauty-geng -q 9 | python3 b_thmA.py full|fullnoleaf|mtl2;  python3 b_core.py 'FCRV? A 2 5 A 4 0 A 4 2'
    nauty-geng -cq 9 | python3 b_mtl2count.py ts|nots|notsodd           # MTL2 counts
    nauty-geng -cq 8 | python3 gen_inst.py > inst8.txt                    # (c) instances
    python3 c_data.py ../../../manuscripts/ln/data/routeR_order8.txt 0 0 all
    python3 c_data.py ../../../manuscripts/ln/data/routeR_order10_sample.txt 0 0 all
    python3 e_joint8.py; for k in 0 1 2; do python3 e_freesched.py inst8.txt $k 3; done
    python3 d_mutation.py inst8.txt 1500 7; python3 d_mutation.py inst8.txt 1500 7 noheadS   # (d)
    cd ../../../lean && lake env lean ../research/audit/A40-scripts/A40Check.lean && lake env lean ../research/audit/A40-scripts/A40Instance.lean

Outputs of my runs: `a_crosscheck.out`, `a_jsplit.out`, `undec_nonJ.out`, `b_*.out`, `b9_*`,
`b_mtl2count9.out`, `c_order8_all.out`, `c_order10_all.out`, `d_mutation.out`, `e_free_*.out`,
`count10.out`. Regenerable inputs (`inst8.txt`, `allodd10.g6`) and binaries are not kept.
