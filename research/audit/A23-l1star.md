# A23. Audit: "The avoidance conjecture L1*: a local form, a reduction to blocked instances, and two even vertices"

- **Date:** 2026-11-27
- **Auditor:** fresh subagent (adversarial referee). I made no edits to the manuscript, the Lean files or the authors' scripts and outputs.
- **Scope:**
  - `manuscripts/l1star/l1star.tex` and its PDF. The PDF matches the .tex: same numbering, same quoted numbers.
  - Every statement and proof in Sections 2–5: Lemmas 2.1–2.4, Propositions 3.1 and 3.3, Remark 3.4, Example 3.5, Theorems 4.2 and 4.3, Corollary 4.4, Remark 4.5, Lemma 5.1, Propositions 5.2–5.5, Corollary 5.6.
  - The numbers in Section 6 and the claims in Section 7.
  - `lean/GallaiLean/L1Star.lean`.
  - The scripts and outputs in `manuscripts/l1star/scripts/`.
  - Results cited from RD, PE and MS are taken as established. I checked only how they are cited and used.
- **Out of scope:**
  - `out/max11_*` (the order-11 run is still in progress; see F3).
  - `ball_test.py` and `out/ball_5_9.txt`, `rand_te3*.txt` and `rand_max_17_20.txt`. These were committed during the audit and are not quoted in the manuscript.
  - `research/experiments.md` E25 and `research/connections.md` AA. I read E25 only for consistency.
- **Audit scripts:** written for this audit and kept outside the repository, in the session scratchpad `/tmp/claude-0/-home-user-Manuscripts/71b899f6-ad34-551b-bf8a-084caa0f3e63/scratchpad/`:
  - `swap54.py`
  - `fan_tests.py`
  - `localcheck.py`
  - `dk4.py`
  - `dk4b.py`
  - `examples.py`

  The Lean axiom check is `/tmp/l1s_audit_lean/Axioms.lean`. The rebuilt oracle is `/tmp/l1s_audit`.
- **Version audited:** branch `claude/l1star`, commit `df63ef4`.
  - The manuscript, PDF, Lean file and `l1s.c` were last changed in `f01ccc6` / `35e03f2`.
  - Another session committed `98fbe7a`, `429d842` and `df63ef4` during the audit. They add outputs and scripts, and make the edge-probability range of `rand_max.py` configurable (defaults unchanged). None of them touches the files listed below.

| file | md5 |
|---|---|
| `manuscripts/l1star/l1star.tex` | `897d672e882620dba6db80db53ab60ee` |
| `manuscripts/l1star/l1star.pdf` | `8bc3f30b923b47b57a0e83f4898b9ce8` |
| `lean/GallaiLean/L1Star.lean` | `5d731a0a11bf11a2b13b6ee2800d20ce` |
| `lean/GallaiLean/PrescribedEndOutside.lean` | `5d66b3349e7c253e0d9520d4ca0956a9` |
| `manuscripts/l1star/scripts/l1s.c` | `8c01b8b13fd7d8751f923f134e58ae1c` |
| `manuscripts/l1star/scripts/brute.py` | `db6402b90743e7bb0e8281b3ca8fbbab` |

## 0. Verdict

**The theorems are correct, with one exception. Theorem 4.2(b) is false as stated in a degenerate case.**
- When c ∈ N(g), the vertex u = c satisfies the hypothesis of (b), but G − gc is not an instance (F1).
- The fix is the hypothesis c ∉ N(g), which the Lean version `l1_case_target` already has. Theorem 4.3 never uses (b) in that case, because it applies (a) first.

**The headline results are correct.**
- Theorem 4.3 (a smallest counterexample is blocked) and Corollary 4.4 (EE follows from the blocked case) are correct.
- Both are formalised faithfully. The file elaborates with no errors, has no `sorry`, and uses only the standard axioms.
- `l1star_of_gen` does give the existing `L1Star`.

**Sections 2, 3 and 5 are correct.**
- All of Lemmas 2.1–2.4, Propositions 3.1, 3.3 and 5.2–5.5, Lemma 5.1 and Corollary 5.6 are correct.
- Every degree and parity count after deletion checks out.
- Every new instance is admissible.
- The measure decreases (lexicographically in Section 5), with one NIT: Lemma 5.1 is the identity when ∂C = A.
- Every Fan transfer meets b(t) > |Z(w)|.
- In every case the path ending at c still avoids A.
- One proof step, the case d(c) = 1 of Proposition 5.3, cites the statement of PE Lemma 4.1 where its proof is what is used (F5, GAP). The argument is correct.

**Independent tests agree.** I executed the constructions of Theorem 4.2(a)–(d) and Propositions 5.2, 5.3, 5.4(i), 5.4(ii) and 5.5 on every Lovász decomposition of the reduced graph, for all small graphs (within an enumeration cap):
- Fan's lemma was implemented independently, and its hypothesis was asserted at every call.
- The tests made 289,854 Fan calls at order 7 alone.
- They found no failure of any hypothesis and no bad output.

**One remark is wrong.** In Remark 4.5, "the reductions of Section 5 then finish" the double K4 is false (F2, ERROR in a remark; no proof depends on it).

**Two data claims were unsupported at the audited commit:**
- **F3:** "no counterexample among all connected graphs of order at most 11". The order-11 run has not finished, and the committed `max11_*.txt` are empty.
- **F4:** the order-7 brute-force cross-check. It finished during the audit (49,920 queries, 0 mismatches) and was committed after the audited commit (`59417d6`).

**Every other number in Section 6 is reproduced exactly.**

| class | findings |
|---|---|
| ERROR | F1 (Thm 4.2(b), degenerate case u = c); F2 (Remark 4.5, double K4 sentence) |
| GAP | F3 (order 11), F4 (order-7 cross-check), F5 (Prop 5.3, d(c) = 1 step) |
| NIT | N1–N11 |

## 1. Findings

### Errors

**F1 (ERROR, statement; Theorem 4.2(b), l.247–248; proof l.269–272).** The hypothesis "u ∈ N(g) ∖ N(c)" allows u = c when c ∈ N(g), since c ∉ N(c). The condition "u has no neighbour in A ∖ {g}" then holds automatically, because A ∩ N(c) = ∅.
- In G − gc the vertex c has even degree d(c) − 1, or is isolated. So (G − gc, c, A) is not an instance.
- The proof step "c is odd" (l.269) is false in this case.
- **Example:** G = K_{1,4} with centre g, c a leaf, A = ∅, u = c. In G − gc, c is isolated.
- **Effect:**
  - The proof of Theorem 4.3 (l.299–300) is unaffected: it applies (a) whenever c ∈ N(g), and uses (b) only for c ∉ N(g).
  - The Lean case `l1_case_target` has the hypothesis `hgc : ¬ G.Adj g c`.
  - Proposition 5.3 excludes u = c through c ∉ V(R).
- **Fix:** in (b) add "c ∉ N(g)" (or "u ≠ c"). Optionally note that (c) needs no such hypothesis. I checked (c) with c ∈ N(g): g ∈ N''(c), but g ∉ A because g ∈ N(c).

**F2 (ERROR, computational claim in a remark; Remark 4.5, l.318–321).** The remark says: "In the double K4 (FQhVw) every branch of the reductions of Theorem 4.2 for EE at a vertex u ≠ z reaches a blocked instance with d(g) = 2; the reductions of Section 5 then finish it."
- **The first half is true.** I followed every branch of Theorem 4.2(a)–(d) from all EE instances of FQhVw (`dk4.py`), both of the form (K−uz, z, {u}) and of the form (K−{uz,uw,wz}, w, {u,z}).
  - All 72 leaves (36 distinct) are blocked with d(g) = 2.
  - No branch ends at Proposition 3.1.
- **The second half is false.** None of the 36 distinct blocked leaves admits any reduction of Section 5, not even one level deep: Lemma 5.1 shrinking, Propositions 5.2, 5.3, 5.4(i) or (ii), or 5.5. None is settled by RD Theorem 6.1 either.
  - `cert.py`, with all its moves including M2′ and a fresh memo per instance, certifies 0 of them.
  - **Example leaf** (FQhVw labels, K4's {0,2,4,6} and {1,3,5,6}, z = 6): the graph K − {02, 06, 26, 16}, with g = 1, N(g) = {3,5}, 35 ∈ E, c = 2, A = {0,6}. It comes from the triangle instance (u, w) = (0, 2), whose even vertex is 6, by one step of (b) with free neighbour 1. Here:
    - g ∉ A;
    - A separates c from g;
    - every Fan route from g ends next to 6 ∈ A;
    - d(c) = 1.
  - The instance is good: take Q_c = 24, then 046513, then 536.
- **What `cert_ee.py` actually shows** (`dk4b.py`):
  - The six instances (K−uz, z, {u}) of FQhVw are certified (6/6) only when Section 5 moves are applied *before* the Theorem 4.2 branches reach a blocked instance.
  - With Theorem 4.2 moves alone ((a)–(d), i.e. `cert.py`'s M1 and M3, with or without B), 0/6 are certified.
  - The twelve triangle instances (K−{uz,uw,wz}, w, {u,z}), which the remark's first sentence names as "the instances that the proof of EE needs", are certified 0/12 under every move set I tried, including all moves with M2′.
- **Fix:** replace the sentence. For example: "every branch of Theorem 4.2 alone ends in a blocked instance with d(g) = 2, to which no reduction of Section 5 applies. Interleaving the reductions of Section 5 earlier certifies the instances (K−uz, z, {u}) (cert_ee.py), but not the triangle instances."

### Gaps

**F3 (GAP, data claim; abstract l.39–42, table l.464, and README "Status").** The text says: "There is no counterexample among all connected graphs of order at most 11 (1,000,000+ pairs (G,c) at order 10 and 11 together)".
- At the audited commit the three `out/max11_*.txt` are empty (0 bytes).
- The run (the three-slice job of `run_n11.sh`, started 09:08) was still running when the audit ended.
- The table row gives no numbers ("see out/max11_*.txt").
- "1,000,000+ … at order 10 and 11 together" is a running count with no denominator. The complete order-11 run has about 1.2·10⁸ pairs: 11,959,367 connected graphs with one even vertex (PE's order-11 EE run), with ten odd vertices each.
- *Post-audit:* commit `3cb56ba` ("order-11 slices 1/3 and 2/3 complete, 0 failures") added SUMMARY lines for two of the three slices; slice 0 was still running. As instructed, I did not audit these files.
- **Fix:** state exhaustiveness for order ≤ 10 only, and give order 11 (graphs, pairs, failures) in the table once all three SUMMARY lines exist. Until then call order 11 partial and give its coverage.

**F4 (GAP, validation claim; l.442–446).** The text says: "every connected graph of order at most 7 … the order-7 run is recorded in out/xcheck_7.txt".
- At the audited commit `out/xcheck_7.txt` is committed empty, and the run was in progress.
- It finished during the audit, at 10:42, in the uncommitted working tree: `SUMMARY xcheck queries=49920 mismatches=0`.
- This matches 780 pairs (G,c) × 2⁶ subsets = 49,920.
- Orders 1–3 were not run. They are trivial, but "at most 7" should say "4–7".
- *Post-audit:* the output was committed in `59417d6` after the audited commit.
- **Fix:** quote 49,920 queries with 0 mismatches in the text.

**F5 (GAP, proof step; Proposition 5.3, l.368–371, case d(c) = 1 with e_i ∈ N(c)).** The proof invokes "the protected-end lemma [PE, Lemma 4.1] in the leaf graph H(K_i;c,e_i), together with Lemma 2.1 there".
- The *statement* of PE Lemma 4.1 preserves only the end edge c e_i, not V(Q_c). What is needed is its leaf-graph proof.
- The argument is correct. Here it is in full:
  1. In H = H(K_i; c, e_i) the vertex c is isolated, since d(c) = 1.
  2. ℓ is a leaf at e_i and is the end of the image of Q_c. The neighbours of e_i in H are ℓ, which has an end, and odd vertices of K_i. So Z_H(e_i) = ∅ < 1 = b(e_{i−1}).
  3. Lemma 2.1 gives a decomposition of H + e_{i−1}e_i = H(K_{i−1}; c, e_i). In it the leaf path lies in its old vertex set, because e_i is already on it.
  4. Lemma 2.2 merges ℓ back into c; c lies on no path of H.
- I executed exactly this 39,537 times at order 7 (`fan_tests.py`) with no failure.
- **Fix:** write these four lines in place of the citation.

### Nits

- **N1** (l.327–328). "Each maps an instance to an instance that is smaller in (ν, |A|)" fails for Lemma 5.1 when ∂C = A, where the map is the identity. Add "when ∂C ≠ A". Corollary 5.6(2) is unaffected.
- **N2** (l.341, l.357–358).
  - Proposition 5.2 presupposes an even vertex g.
  - In Proposition 5.3, "e_i ∉ A for all i" and "e_i ∉ N(c) for all i" mean i ≥ 1. g ∈ A and g ∈ N(c) are allowed, and the proof works with them. Corollary 5.6(4) uses "vertices after g". Say i = 1, …, k.
- **N3** (l.351–352). The citation "route append, [RD, Lemma 3.6]" points to a lemma about route systems and transversal realisations in graphs whose components have even order. Only the observation "two paths sharing exactly one vertex, an end of both, form a path" is used. State it directly.
- **N4** (l.108, l.559). "The two-even theorem (Conjecture 3.2)": it is a conjecture. Write "two-even conjecture".
- **N5** (abstract l.42; l.470–473). 199 of the 38,896 random pairs are undecided at the node budget. "No counterexample … among 38,896 random pairs" should say "38,697 decided pairs, 0 failures, 199 undecided".
- **N6** (l.504–521, census).
  - `blocked_count.py` counts 1 ≤ |A| ≤ 2; A = ∅ is excluded.
  - It tests case (c) before case (b). So row (b) means "a free u exists but none in N(c)". The table's order and "first case … that applies" suggest the opposite priority.
  - The 0.59% (l.521, abstract l.53) is 2,414 / 411,948, the census denominator. `irred_all.py`'s own `total` is 267,664 (only the instances with c ∉ N(g)), of which 2,414 is 0.90%. Name the denominator.
- **N7** (l.525–527). "cert.py searches recursively for a certificate built only from these reductions" is inaccurate.
  - `cert.py` also uses a move M2′ that the paper does not state: a route from g to a neighbour y of c, restored by Fan transfers in a leaf graph, giving the instance (G − E(R) − yc, y, A ∪ {c}). I checked the argument for M2′ by hand and it is valid.
  - It also uses these base cases:
    - A misses the component of c;
    - A ∪ {c} packed (RD Thm 6.1);
    - all-odd with A packed (RD Thm 6.3);
    - all-odd with d(c) = 1.
  - I re-ran `cert.py 2` at orders 5–7 and `cert_ee.py` at order 7 without M2′. The counts are identical to `out/cert_5_7.txt` and `out/cert_ee7.txt`: 35 uncertified at n = 7, and the six CP(3)+apex pairs.
  - **Fix:** list the base cases and either state M2′ as a proposition or drop it.
- **N8** (l.500). "Every graph is decomposable (orders 6–10)": order 7 has no graph with ≥ 2 packed even vertices; `packedev7.txt` has no data line. Write "orders 6, 8, 9, 10".
- **N9** (l.561–562). Open problem 2 says "At order 8, one graph needs a different argument (G?Bvvo)". `te3walk6.txt` also has one uncertified graph at order 6 (`EEz_`).
- **N10** (l.536–551, Section 7).
  - Lemma 2.4 is not a Lean lemma of its own; it is inlined in `l1_case_target`.
  - `l1_case_target` and `l1_case_target_adj` assume c ∉ N(g). This is needed for (b) (F1); for (c) it is weaker than the manuscript.
  - The list of formalised items should say both.
- **N11** (scripts, not the paper).
  - The docstrings use old numbering: `blocked_count.py` "Theorem 3.5", `irred_all.py` "Theorem 3.3", "Lemma 4.1". Now these are Theorem 4.2 and Lemma 5.1.
  - `l1s.c`'s header lists an "(unused)" mode `sep` that `main` does not implement ("unknown mode").
  - It omits the modes `stats`, `gen`, `two`, `packedev` and `peloc`, which are documented only in the README.

## 2. Item-by-item verdicts

| # | Item (lines) | Verdict | Key checks |
|---|---|---|---|
| 1 | Def. instance, Conj 1.2–1.4, equivalence (l.72–95) | SOUND | A_max is admissible and contains every admissible set. If g ∉ N(c) then g ∈ A_max. PE Conj 7.3 is identical to Conj 1.2. |
| 2 | Lemma 2.1, Fan (l.125–130) | SOUND | Weaker than RD Lemma 2.2. Z is taken in K (before adding tw), as in RD. |
| 3 | Lemma 2.2, merge with avoidance (l.136–148) | SOUND | MS Lemma 12 gives b(x) = 0 + 1. The leaf path is the unique path with an end at ℓ, so its image is Q_x, and V(Q_x) = V(P_ℓ) − ℓ + x misses A. (y ∉ A is forced by the hypothesis.) |
| 4 | Lemma 2.3, leaf at c (l.150–163) | SOUND | (ii) The leaf path is not ℓc, since b(c) = 0. c ∉ A is forced. |
| 5 | Lemma 2.4, protected transfer (l.165–177) | SOUND | N_{K^{+c}}(w) = N_K(w). The ends change only at c ∉ N(w) and at ℓ ∉ N(w), so Z(w) = ∅ < 1 = b(t). A new path through ℓ lies in the old leaf path plus w ∉ A. b(c) and b(ℓ) are unchanged since c, ℓ ∉ {t, w}. |
| 6 | Prop 3.1 (l.183–191) | SOUND | G − cy: y has degree d(y) − 1, even or 0, and c is isolated. Adding cy gives b(c) = b(y) = 1. |
| 7 | Prop 3.3 (l.198–208) | SOUND | N_{G^{+y}}(x) = N_G(x). A third vertex of Q_w would lie in N(x) ∩ N(y) = ∅. Deleting Q_w = wy leaves b(y) = 0 = b(x). |
| 8 | Remark 3.4 (l.216–221) | SOUND (data) | 61 / 404,488 reproduced. GCQbVg: even vertices 3 and 4 at distance 3; 76 decompositions with b = d mod 2, none with V(Q_1) local (brute force). Each order-10 graph is decomposable (`packedev10`). |
| 9 | Example 3.5 (l.223–231) | SOUND | DTw decodes to 02, 03, 04, 14, 23, 24 and has 4 Lovász decompositions, none with Q_1 ∩ {0,2} = ∅. K_{1,4}: Q_c ∈ {cga}. Order 9: 3,162 / 47,526 reproduced. |
| 10 | Thm 4.2(a) (l.245–246, 260–267) | SOUND | g: d−1 odd; c: d−1 even or 0. A ∪ {c} admissible. H(G;c,g) = G′ + gℓ. b(g) = 1 − 1 = 0. ν drops by ≥ 1. |
| 11 | Thm 4.2(b) (l.247–248, 269–272) | **ERROR in statement (F1)**; proof SOUND for u ≠ c | u: d−1 even or 0. A admissible via "no neighbour in A ∖ {g}". Lemma 2.4 hypotheses: b(g) = 1, Z(u) = ∅, c ∉ N(u), u ∉ A since u ∈ N(g). |
| 12 | Thm 4.2(c) (l.249–250, 274–282) | SOUND | Details in §3 below. |
| 13 | Thm 4.2(d) (l.251–252, 284–287) | SOUND | c: d(c) − 1 ≥ 2 even; ℓ odd. N_H[ℓ] = {ℓ, y} misses A ∪ {c}. ν(H) = ν(G) − 1. |
| 14 | Thm 4.3 (l.293–302) | SOUND | The case split is exhaustive. In case (b), u ≠ c because c ∉ N(g). Induction on ν ∈ ℕ. |
| 15 | Cor 4.4 (l.304–310) | SOUND | L1StarGen ⇒ L1* (|A| ≤ 2) ⇒ EE by PE Cor 7.4. |
| 16 | Remark 4.5 (l.312–322) | SOUND except one sentence (**ERROR F2**) | "Never blocked when N(u)∖{z} ⊆ N(z)": blocked forces N(z)∖{u,w} ⊆ N(u), hence N(u)∖{z} = N(z)∖{u} and d(u) = d(z), a contradiction. When d(z) = 2 there is no even vertex at all. CP(3)+apex = F]~vw (checked: K7 minus the matching 01, 23, 45). |
| 17 | Lemma 5.1 (l.330–338) | SOUND (N1) | N(C) ⊆ A. A path from c that avoids ∂C stays in C. |
| 18 | Prop 5.2 (l.340–354) | SOUND (N2, N3) | Details in §3 below. |
| 19 | Prop 5.3 (l.356–372) | SOUND, **GAP F5** in the d(c) = 1 step | Details in §3 below. |
| 20 | Prop 5.4 (l.377–398) | SOUND | (i) G′ has no even vertex; N′(c) = N(c) since c ∉ {g,u,v}; if Q′_c ∌ u then Q_c ∌ g. (ii) g is interior to Q_c, uv ∉ E(Q_c), and g ∉ V(P) because both edges at g lie on Q_c. Verified by brute force (§5). |
| 21 | Prop 5.5 (l.400–410) | SOUND | c ∉ N(g) gives g ∉ N(c), so N′(g) = N(g). d′(c) = 1. The path through y₁y₂ is not Q′_c. ν drops by 2. |
| 22 | Cor 5.6 (l.412–430) | SOUND | Each item is the contrapositive of the cited reduction under lexicographic minimality. Items 2 and 5 use minimality of |A| (Lemma 5.1; Prop 5.4(ii)). Item 5 uses (i) twice (u and v symmetric) and item 3. Item 6 uses Prop 5.5 with y₁, y₂ swapped. Item 7 holds for every instance (RD Thm 6.1). |
| 23 | Section 6 (l.432–532) | SOUND WITH FIXES | All committed numbers reproduced (§5). Order 11 (F3), xcheck_7 (F4), N5–N9. |
| 24 | Section 7 / Lean (l.534–551) | SOUND (N10) | Builds, no sorry, standard axioms, faithful statements (§4). |
| 25 | Abstract / introduction | SOUND WITH FIXES | Order-11 claim (F3); random undecided pairs (N5); "two-even theorem" (N4). The citations to PE (Conj 1.5, Thm 5.1, Lemma 4.1, Conj 7.3, Cor 7.4), RD (Lemma 2.2, Lemma 3.6, Thm 6.1) and MS (Lemma 12) are correctly numbered (checked against the PDFs). |

## 3. Details: degree and parity bookkeeping, Fan hypotheses, and Q_c

**Theorem 4.2(c).** G″ = G − cu − gu.
- Degrees:
  - u ≠ g is odd with d(u) ≥ 3, so d″(u) ≥ 1 is odd.
  - c loses one edge: even or 0.
  - g loses one edge: odd.
  - So c is the only possible even vertex.
- Admissibility of A ∪ {c} for u:
  - c ∉ N″[u].
  - A ∩ N″(u) = ∅, since N″(u) = N(u) ∖ {c, g}.
  - A ∩ N″(c) ⊆ A ∩ N(c) = ∅.
  - This also holds if c ∈ N(g): then g ∈ N″(c), but g ∉ A.
- Leaf graph: G″ + uℓ = H(G − gu; c, u).
- Fan step (t = g, w = u): N(u) = (N(u) ∖ {c, g}) ∪ {ℓ}, all with an end, so Z = ∅ < 1 = b(g).
- Q_c: the new leaf path lies in the old one plus u ∉ A ∪ {c}.
- H + gu = H(G; c, u), since gu ≠ cu. Merge with b(c) = 0 and b(ℓ) = 1.
- Measure: ν drops by ≥ 3.

**Proposition 5.2.**
- R is a shortest path in G − A with V(R) ⊆ V − A, so R is induced in G.
- Degrees: g and c change parity; the interior loses 2 each and stays odd ≥ 1.
- Admissibility:
  - N′[g] ∩ V(R) = {g} and N′(c) ∩ V(R) = ∅, so V(R) ∖ {g} is admissible together with A.
  - A ∩ N′[g] = ∅, since g ∉ A.
- Q_c: Q′_g ∩ V(R) = {g}, so Q′_g ∪ R is a path. It ends at c and misses A.
- Measure: ν drops by ≥ 2k − 1 ≥ 3.

**Proposition 5.3.**
- Degrees in K_i: g loses 1 (odd), e_1, …, e_{i−1} lose 2 (odd), and e_i loses 1 (even or 0).
- Fan step i (t = e_{i−1}, w = e_i): t is odd in K_i, so b(t) = 1. Every neighbour of e_i is odd, so Z(e_i) = ∅.
- Q_c, case e_i ∉ N(c): Lemma 2.4 applies, with c ∉ V(R) and w = e_i ∉ A.
- Admissibility in K_k:
  - N_{K_k}[c] = N[c].
  - A ∩ N_{K_k}(e_k) ⊆ A ∩ (N(e_k) ∖ {e_{k−1}}) = ∅.
  - If g ∈ A: for k = 1, g ∉ N_{K_1}(e_1); for k ≥ 2, e_{k−1} ∉ A gives N(e_k) ∩ A = ∅.
- Measure: ν drops by ≥ 1.
- The case d(c) = 1 is F5.

**The questions in the brief:**
- *Is c's end ever moved by a Fan chain?*
  - In Lemma 2.4 it cannot be. The leaf gives c no end, and c ∉ N(w), so c is neither a chain vertex nor in Z(w).
  - In (c) and in the d(c) = 1 case of Prop 5.3, c is represented by the leaf ℓ. ℓ is not the target and has b(ℓ) = 1 throughout.
- *Is the target ever appended to Q_c?*
  - Possibly, in Lemma 2.4, (c) and Prop 5.3.
  - In each case the target (u, or e_i) is outside A ∪ {c}. In the d(c) = 1 case it is already on the leaf path.

## 4. Lean

- **Compilation.** `source ~/.elan/env && cd lean && lake env lean GallaiLean/L1Star.lean`: exit 0, no output (no errors or warnings), 7.9 s.
- **Build state.**
  - `lake build GallaiLean.L1Star --no-build`: "All targets up-to-date (18319 jobs)", so the imported oleans are current.
  - `lake build --no-build` for the whole library: "All targets up-to-date (18390 jobs)". `GallaiLean.lean` l.66 imports `L1Star`. The only warning is a deprecation in `MultiSep.lean:1530`.
  - So "the full library builds" (l.537–538) holds.
- **No sorry.** grep for `sorry|admit|^axiom|native_decide|implemented_by|unsafe|@[extern` in `L1Star.lean`, `PrescribedEndOutside.lean` and `PrescribedEnd.lean`: no hits.
- **Axioms.** Scratch file `/tmp/l1s_audit_lean/Axioms.lean` (`import GallaiLean.L1Star`, compiled with `lake env lean`). `#print axioms` for each of the following gives `[propext, Classical.choice, Quot.sound]`:
  - `Gallai.l1starGen_of_blocked`
  - `Gallai.ee_of_l1Blocked`
  - `l1star_of_gen`
  - `ee_of_L1StarGen`
  - `avoid_of_leafSep`
  - `avoid_of_apexSep`
  - `l1_strong`
- **Fidelity of the definitions** (printed with `#print`):
  - `evenSet G = {v | 0 < deg v ∧ Even (deg v)}`. This is "even" = positive even degree.
  - `Admissible G c A := ∀ a ∈ A, a ≠ c ∧ ¬Adj c a ∧ ∀ g ∈ evenSet G, ¬Adj g a`. This is A ∩ (N[c] ∪ N(g)) = ∅, with N(g) = ∅ when there is no even vertex. g ∈ A is allowed.
  - `AvoidDecomp G c A := ∃ D, (∀ v, D.ends v = deg v % 2) ∧ ∀ P ∈ D.paths, (P.src = c ∨ P.tgt = c) → ∀ a ∈ A, a ∉ P.walk.support`.
    - The first conjunct is the Lovász condition b(v) = d(v) mod 2 at every vertex.
    - For odd c exactly one path ends at c, so the second conjunct is V(Q_c) ∩ A = ∅.
  - `L1StarGen`: for every finite G with `(evenSet G).card ≤ 1`, every c with `deg c % 2 = 1`, and every finite A with `Admissible`: `AvoidDecomp`. There is no bound on |A|. This is Conjecture 1.3.
  - `L1Blocked`: the same, plus `∀ g ∈ evenSet G, ¬Adj g c → (∀ w, Adj g w → ∃ a ∈ A, a ≠ g ∧ Adj w a) → AvoidDecomp`. This is "every blocked instance is good" exactly.
  - `L1Strong n` uses the measure `∑ deg + [evenSet = ∅]`, which is ν.
- **`l1star_of_gen` really gives `L1Star`.**
  - `L1Star` (`PrescribedEndOutside.lean` l.198) is, after unfolding, the body of `L1StarGen` with `A.card ≤ 2 →` inserted.
  - The proof term `fun V _ _ G _ hev c hc A _ hA => h V G hev c hc A hA` ignores the cardinality hypothesis.
  - `#check` gives `Gallai.L1StarGen → Gallai.L1Star`, and a universe-0 `example` also elaborates.
  - `ee_of_l1Blocked` is the composite `ee_of_L1Star ∘ l1star_of_gen ∘ l1starGen_of_blocked`. Its statement is EE: z is the only even vertex, x ∈ N(z), and xz is terminal at x in some Lovász decomposition.
- **Case lemmas versus Theorem 4.2.**
  - `l1_case_adj` is (a). `l1_case_big` is (d), with the leaf graph `apex (G − cy) {y}` = H(G;c,y). `l1_case_leaf` is Prop 3.1.
  - `l1_case_target` is (b) with c ∉ N(g); this hypothesis is required (F1).
  - `l1_case_target_adj` is (c) with c ∉ N(g); this hypothesis is unnecessary for (c).
  - `l1_strong` follows the proof of Theorem 4.3 case by case.

## 5. Computations

**Reproduced with the rebuilt oracle** (`gcc -O2 -o /tmp/l1s_audit l1s.c`; outputs in scratchpad `l1s_runs/`). Every SUMMARY line is identical to the committed `out/` file and to the manuscript.

| run | manuscript | rerun |
|---|---|---|
| `max 4 q`, n = 5, 6, 7, 8 | 7/28, 13/78, 130/780, 224/1,792, 0 failures | identical (trivial A_max: 15, 15, 180, 85) |
| `max 4 q`, n = 9, 10 | 11,936/95,488, 32,851/328,510, 0 failures | identical (0.4 s, 20 s) |
| `max 3 n`, n = 5, 7 | failures at 5 and 7, all meeting N(g) | byte-identical (n = 7: 627/780 pass; 158 + 14 minimal sets). "Meeting N(g)" follows because every admissible subset of A_max passes. |
| `gen 4`, n = 9 | 350,934 + 213,062 + 1,750 admissible, 0 fail; 3,162/47,526 separated non-admissible fail | identical (all six classes) |
| `two`, n = 6, 8, 10 | table l.494–496 | identical (n = 10 in 48 s) |
| `packedev`, n = 6, 8, 9 | all decomposable; 52 graphs with 3 at n = 9 | identical |
| `peloc`, n = 6, 8, 9, 10 | 61/404,488 at n = 10; GCQbVg, c = 1 | identical (n = 8: G?`eVg c=0, GCQbVg c=1) |
| `stats` n = 5–8 | five vertices outside N[c]; Hamiltonian at n = 8 | rerun: byte-identical; `stats7`: min-out 5 for one pair; `stats8`: 8 pairs with min length 7, all in K8 (`G~~~~{`) |
| `blocked_count.py 2` n = 7, 9 | table l.511–516 | rerun: byte-identical to `out/`; rows sum to 1,868 and 411,948; blocked 57,214 = 13.9% |
| `irred_all.py 2` n = 7, 9 | 2,414 left; d(g) ∈ {2,4}; 2,219 with g ∈ A | rerun: byte-identical to `out/`; 2,414 RESIDUAL, 2,219 gA, d(g) ∈ {2,4}; see N6 for the denominator |
| `cert.py 2` n = 5, 6, 7; `cert_ee.py` n = 7 | n = 6 all certified; n = 7: 35/1,868 not; EE: only the six F]~vw pairs | identical, with and without M2′ (N7) |
| `rand_max_11_16.txt` (committed) | 3,000 graphs (483–521 per order), 38,896 pairs, 0 failures, 199 undecided | per order 521/483/512/507/492/485; no FAIL line (N5) |
| `xcheck_brute.py`, n = 4, 5, 6 | 64, 448, 2,496 queries, 0 mismatches | rerun: identical; `xcheck_7.txt` see F4 |

**Independent tests of proof claims** (brute force with `brute.py`'s `lovasz_decomps`, whose transition-system enumeration I read and found correct, plus my own code):

1. **Proposition 5.4(ii), the degree-two triangle swap** (`swap54.py`).
   - **Setup:** every connected graph with one even vertex g, d(g) = 2, N(g) = {u,v} and uv ∈ E. Every odd c ∉ N[g]. Every Lovász decomposition with g ∈ Q_c.
   - **Structural claims checked:**
     - g is interior to Q_c;
     - Q_c = X u g v Y;
     - uv lies on exactly one other path P, and g ∉ P.
   - **Exchange:** performed, and the result re-verified from scratch: an edge partition into paths, with b = d mod 2, and path ending at c with vertex set V(Q_c) − g.
   - **Existence statement:** checked for *every* B ⊆ V ∖ {c, g}, admissible or not: if some decomposition avoids B, some decomposition avoids B + g.
   - **Results:** 0 failures.

   | order | graphs | pairs (G,c) | decompositions | swaps checked | existence tests (non-trivial) | graphs skipped (enumeration cap) |
   |---|---|---|---|---|---|---|
   | 5 | 2 | 4 | 16 | 8 | 32 (7) | 0 |
   | 7 | 24 | 96 | 11,344 | 3,830 | 3,072 (635) | 2 |
   | 9 | 171 | 1,026 | 838,944 | 180,516 | 131,328 (25,671) | 1,215 (cap 20,000) |

2. **The constructions of Theorem 4.2 and Propositions 5.2–5.5** (`fan_tests.py`).
   - **Fan's lemma:** implemented from RD's chain proof (BFS for the chain, re-routings, final append). At every call it asserts b(t) > |Z(w)| in the graph where the call is made. It checks the output: a decomposition of K + tw, ends b − 1_t + 1_w, and every vertex set unchanged except one path, which gains w.
   - **Tests:** each construction runs on *every* Lovász decomposition of the reduced graph:
     - Lemma 2.4 (leaf at c, Fan, delete leaf);
     - the leaf and merge steps of (a), (c) and (d);
     - the Fan route of 5.3, for every route g e₁⋯e_k with k ≤ 4, including the d(c) = 1 leaf variant;
     - the explicit replacements of 5.2, 5.4(i) and 5.5.

     The set A plays no role in these constructions, only in admissibility. So for 5.3, every route with k ≤ 4, c ∉ V(R) and the N(c) condition is tested. For 5.2, the routes tested are the shortest g–c paths of G (A = ∅).
   - **What is checked:**
     - the result is a Lovász decomposition of G;
     - V(Q_c) lies in the set the proof promises. For (b) and 5.3 this is V(Q′_c) plus the targets; for (c) it is V(Q″_u) + c. This settles every admissible A at once.
   - **Results:** order 7 gave the counts below (graphs whose enumeration space exceeded the cap were skipped). Order 5 gave (a) 48, (b) 20, (c) 20, 5.2 14, 5.3 58, 5.4(i) 18, 5.5 4. Orders 4 and 6 gave (d) 27 and 7,905. In all runs: no Fan hypothesis failed, no output was bad, and 0 BAD lines appeared. I also started an order-9 run (cap 3,000). It hit the 9-minute limit before its first progress line, so it gives no counts; it printed no BAD line and no assertion failure.

   | order 7 | (a) | (b) | (c) | 5.2 | 5.3 (Fan steps; d(c) = 1 leaf steps) | 5.4(i) | 5.5 | Fan calls |
   |---|---|---|---|---|---|---|---|---|
   | checks | 21,450 | 31,184 | 21,154 | 11,473 | 105,139 (237,516; 39,537) | 10,172 | 7,308 | 289,854 |

3. **Local form by full enumeration** (`localcheck.py`, enumeration cap 3·10⁵):

   | order | pairs passing | graphs skipped |
   |---|---|---|
   | 5 | 28/28 | 0 |
   | 6 | 72/72 | 1 |
   | 7 | 684/684 | 16 |
   | 8 | 888/888 | 113 |

   This agrees with `l1s max`.
4. **Examples** (`examples.py`): Example 3.5 (DTw, K_{1,4}) and Remark 3.4 (GCQbVg) checked as in §2. The graph6 strings FQhVw and F]~vw are the double K4 and CP(3)+apex, as stated.
5. **Remark 4.5** (`dk4.py`, `dk4b.py`): see F2.

## 6. Summary

**Mathematics.** The proofs in Sections 2–5 are correct. Points I tried hardest to break, all of which hold:
- the leaf trick in Lemma 2.4 (Z(w) unchanged because c ∉ N(w));
- case (c) of Theorem 4.2 (target u appended to the leaf path; u ∉ A ∪ {c});
- the Fan route of Proposition 5.3, including d(c) = 1;
- the swap of Proposition 5.4(ii);
- the lexicographic minimality in Corollary 5.6.

**Required corrections:**
- **F1:** add c ∉ N(g) to Theorem 4.2(b).
- **F2:** rewrite the double-K4 sentence of Remark 4.5. Section 5 does not finish the blocked leaves of Theorem 4.2; the certificate interleaves the moves; the triangle instances remain uncertified.
- **F5:** write out the d(c) = 1 step of Proposition 5.3.

**Lean.** Theorem 4.3 and Corollary 4.4 are formalised faithfully: the file builds, there is no sorry, and only standard axioms are used. `l1star_of_gen : L1StarGen → L1Star` is correct.

**Data.**
- Everything committed is reproduced exactly.
- The order-11 claim in the abstract (F3) and the order-7 cross-check (F4) were not backed by committed output at the audited commit.
  - The cross-check has since finished (49,920 queries, 0 mismatches), committed in `59417d6`.
  - Two of the three order-11 slices have finished (`3cb56ba`, not audited); slice 0 is still running.
- N1–N11 are wording and documentation fixes.

## 7. Author's response (applied)

- **F1:** Theorem 4.2(b) now assumes c ∉ N(g), and its proof says why c is odd in G − gu. Section 7 notes that both Lean cases assume c ∉ N(g).
- **F2:** Remark 4.5 is rewritten as suggested. Theorem 4.2 alone ends in blocked instances to which Section 5 does not apply (the example leaf is quoted). Interleaving certifies the six instances (K − uz, z, {u}) but not the twelve triangle instances.
- **F3:** the order-11 run finished: 11,959,367 graphs, 119,593,670 pairs, 0 failures (`out/max11_*.txt`). The abstract and table give these numbers. The random counts give decided and undecided pairs separately.
- **F4:** the cross-check is quoted as 49,920 queries at order 7, 0 mismatches, for orders 4–7.
- **F5:** the d(c) = 1 step of Proposition 5.3 is written out in four steps, as in the report.
- **N1–N10:** applied.
  - N1: Lemma 5.1 is strict only when ∂C ≠ A.
  - N2: Propositions 5.2 and 5.3 presuppose g; indices run i = 1, …, k.
  - N3: the RD Lemma 3.6 citation is replaced by the direct observation.
  - N4: "two-even conjecture".
  - N5: decided and undecided counts are separate.
  - N6: the census states its range of |A|, its priority order and both denominators.
  - N7: the base cases are listed, and the composite move is stated with a note that the counts are the same without it.
  - N8: orders 6, 8, 9, 10.
  - N9: `EEz_` at order 6 is added.
  - N10: Section 7 says what Lean assumes.
- **N11:** the script docstrings use the current numbering, and the header of `l1s.c` lists every mode.
- **Added after the audit, not audited:** Remark 3.5, on route-descent's one-sided separation and the intersection region N[c] ∪ (N(g) ∩ B₂(c)), with `ball_test.py` data at orders ≤ 9; random runs at orders 17–20 and for the two-even conjecture.
