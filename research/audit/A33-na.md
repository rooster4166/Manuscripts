# Audit A33: "Neighbour avoidance in Lovász decompositions" (`manuscripts/na`)

Referee: adversarial audit, branch `claude/na`.

What was audited (md5 unchanged from start to end of the audit):

| file | md5 |
|---|---|
| `manuscripts/na/na.tex` (631 lines) | `44d0f4c1…6e6f6` |
| `lean/GallaiLean/NeighbourAvoid.lean` (1386 lines) | `35ae7761…fb5e5` |
| `manuscripts/na/scripts/nalib.py` | `64a293e9…2e68860` |
| `exact.py` / `run_na.py` / `random_na.py` | `d11a9008…` / `1af20fe6…` / `bd300232…` |
| `r2check.py` / `r2exact.py` | `877dd908…` / `3605284f…` |

Numbering is that of the compiled draft: Conjecture 1.1 (NA), Theorem 1.2 (set form, `thm:A`),
Corollary 1.3 (NA), Theorem 1.4 (boundary, `thm:C`), Corollaries 1.5–1.6; Lemma 2.1 (Fan),
Theorem 2.2 (L1), Lemma 2.3 (leaf); Definition 3.1, Lemmas 3.2–3.3; Lemmas 4.1–4.3; §5 proof
steps (a)–(g), Remark 5.1, Example 5.2; §6 boundary proof, Remarks 6.1–6.2; §7 remarks; §8
computations; §9 Lean; §10 open problems.

Audit scripts are in `research/audit/A33-scripts/` (see the end of this file). I did not edit
the manuscript, the Lean file or the scripts, and I did not commit. Note: a concurrent session
committed my in-progress scripts in its checkpoints (`2e91d75`, `f5a9fa4`, `261a2eb`, `56b264f`,
`8c636d5`) while the audit was running; I did not make those commits.

## Verdict in one paragraph

The mathematics is correct. The proof of Theorem 1.2 holds step by step. The parity
bookkeeping is right, Fan's hypothesis holds at every back-step (in the strong form b(t) = 1,
Z(u) = ∅), L1's hypotheses hold at the bottom of the chain, and the target y is legitimately
allowed. The counting proof of Theorem 1.4 is correct. The Lean file builds with no `sorry`, and
the axioms are only `propext`, `Classical.choice` and `Quot.sound`. The headline Lean statements
say what the manuscript says, with harmless redundancies. My own exact solver and verifier, which
use none of the manuscript's code, reproduce every number for orders 4 and 6. They also confirm the
iff of Corollary 1.5 and of the set form on all of order 6 (K6 included), on 578 of the 783 bad pairs of order 8, and
on random disconnected graphs.

The errors are in the surrounding text and the computational section:
- an unfilled results table (placeholders);
- two false comparative claims about other manuscripts ("22 of the 215 NA instances";
  "NA is stronger than Lemma NP");
- a few mis-stated side claims.

None of them touches a proof.

## Summary table

| # | item | grade | one-line reason |
|---|---|---|---|
| 1 | Abstract | GAP (minor) | "y odd" is missing from both bullet statements. The order-10 claim is now backed by the rerun data. |
| 2 | Conjecture 1.1 (NA) | SOUND | Same as conj-n Conj. 4.2 and Lean `NeighbourAvoidOn`. |
| 3 | §1 bullet "TRN and NA imply N; N reduces DL(1)…" | SOUND | conj-n Thm 4.6 and dl-one Prop 9.2 say this. The DL(k)/(T1) clause is inherited from conj-n and was not re-checked. |
| 4 | §1 bullet "NA is the adjacent-pair analogue of L1" | SOUND | |
| 5 | §1 bullet "NA is stronger than Lemma NP of [DL]" | **ERROR** | NP needs only d(x) ≥ 3. In K4, NP holds while NA's hypothesis and conclusion both fail. The statements are incomparable. |
| 6 | §1 bullet "22 of the 215 NA instances … 2,451 of the 9,558" | **ERROR** | 215 and 9,558 are the sizes of the class N1 ∪ NA. The NA parts are 129 and 4,970, as the paper's own table says. |
| 7 | §1 "the smallest is the wheel W5" | SOUND | Fewest edges among the 22 (conj-n §6.2). |
| 8 | Theorem 1.2 (set form) | SOUND | §5 proof checked step by step. Lean `avoid_packed_of_reach`. |
| 9 | Corollary 1.3 | SOUND | Y = {x}. The witness lies in the component. |
| 10 | Theorem 1.4 (boundary) | SOUND | The count is correct. The per-path identity holds on 39,265 decompositions. |
| 11 | Corollary 1.5 | SOUND | Verified by my solver on all 228 pairs of order 6, on 578 of the 783 non-weak pairs of order 8, and on 5,040 random pairs of orders 8 and 10. |
| 12 | Corollary 1.6 (1)–(3) | SOUND | Lean compositions with `ConjN.lean`, checked. |
| 13 | §1 "Status" | GAP (minor) | Overstates what is formalised. Lemma 2.1's bijection and Lemma 4.3's "t ∈ C odd" are not in the Lean statements. Remarks 5.1, 6.1 and 6.2 are also paper-only. |
| 14 | §1 "The idea"; "three features" | SOUND | conj-n also has the trivial move (i) in no-even-vertex graphs, but it is vacuous for NA. |
| 15 | Lemma 2.1 (Fan with vertex sets) | SOUND | Matches RD Lemma 2.2 and its proof. Lean `fan_single_supp` proves only the weaker cover form, which is all that is used. |
| 16 | Theorem 2.2 (L1 set form) | SOUND | Hypotheses match RD Thm 6.3. |
| 17 | Lemma 2.3 (pendant leaf) | SOUND | |
| 18 | Definition 3.1 and its `Steer` equivalence | SOUND | |
| 19 | Lemma 3.2 (one Fan step) | SOUND | Z(u) = ∅ and b(z) = 1. Confirmed at 99,894 logged back-steps (orders 6 and 8). |
| 20 | Lemma 3.3 (steered chain) (1)–(3) | SOUND | Parities checked by hand and by machine. |
| 21 | Lemma 4.1 (walking along S) | SOUND | (S1)–(S4) inheritance checked case by case. The induction is well founded. |
| 22 | Lemma 4.2 (toggling) | SOUND | |
| 23 | Lemma 4.3 (the subgraph) | SOUND | The farthest-vertex argument and the parities are correct. |
| 24 | §5 opening (L1 case; x unique) | SOUND | |
| 25 | §5 (a)–(c) | SOUND | Degree formulas correct. Every odd vertex of H is free. |
| 26 | §5 (d) (S1)–(S4) | SOUND | |
| 27 | §5 (e) L1 at the bottom | SOUND | Hypotheses hold. Machine-checked at every bottom (orders 6 and 8). |
| 28 | §5 (f)–(g) | SOUND | |
| 29 | Target y allowed | SOUND | Lemma 3.2 needs only u ∉ X, and y ∉ X. Target y occurs in 47 of 286 sequences at order 6 and 4,870 of 11,558 at order 8; all verified. |
| 30 | Remark 5.1 | SOUND | |
| 31 | Example 5.2 (wheel) | SOUND, one **ERROR** (wording) | "All its degrees are odd" is false: vertex 3 is isolated in K5. "y = N(ℓ)" should read N(ℓ) = {y}. The other claims were machine-checked (24 steering sequences, all return to y). |
| 32 | §6 proof of Theorem 1.4 | SOUND | |
| 33 | Remark 6.1 ("blocks") | UNCLEAR | "Block" is undefined, so the "equivalently" cannot be checked. |
| 34 | Remark 6.2 | SOUND (minor) | "The wheel with x as its hub" needs an odd number of spokes. "14 at order 6" confirmed. |
| 35 | §7 "the open part of N is TRN" | UNCLEAR | TRN is sufficient but stronger than N. With NA, N is equivalent only to the restriction of TRN used in conj-n Thm 4.6. |
| 36 | §7 "Q(y) ∌ x whenever y has a neighbour not adjacent to x" | **ERROR** (wording) | x itself is such a neighbour. "w ≠ x" is needed, and K4 is a counterexample as written. |
| 37 | §7 `avoid_deg_two` follows from the degree-two case | SOUND | The parenthetical omits ab ∉ E. |
| 38 | §7 R1 | SOUND | Checked: subdivide xw by y. Common neighbours unchanged. |
| 39 | §7 R2 equivalence and data | SOUND, UNCLEAR wording | The new vertex t is never defined. Independently re-verified: 3/3 and 129/129. |
| 40 | §7 "leaf tails" | GAP | "Applies verbatim with X = A ∪ {c}" conflates goodness (Q_c ∩ A = ∅) with "meets A ∪ {c} at most once" once \|A\| ≥ 2. Easily repaired. |
| 41 | §7 obstructions / DL(1) via Prop 9.2 | SOUND | |
| 42 | §8 Tools: construction | SOUND | It is the proof as written, with runtime asserts. `separation()` does not assert that X is packed (harmless). |
| 43 | §8 Tools: verifier independent and sound | SOUND | It shares only trivial helpers. It agrees with my verifier on 858 mutants and rejects all 49,444 decompositions in which x ∈ Q(y). |
| 44 | §8 Tools: exact vs brute force "18 … and 198 of order 6" | GAP (minor) | Brute force skips K6 (the cap): 198 of 228. My solver covers all 228. |
| 45 | §8 results table, rows for orders 4 and 6 | SOUND | Reproduced exactly. |
| 46 | §8 results table, rows for order 8, order 12 and random | **ERROR** | Unfilled placeholders (`\textsc{n8pairs}`, …). The order-12 and random data have since finished; the order-8 run is still going. |
| 47 | §8 results table, order-10 row | SOUND | The rerun (both routines) finished: 1,484,200 / 1,305,621 / 1,448,874, all built. |
| 48 | §8 bullets (NA counts agree with CN; good ⇔ weak; set form 16) | SOUND | "and the counts in data/" names no file. The counts are now in the order-12 slice files and `random.txt`. |
| 49 | §9 Lean claims (no sorry, axioms, 18,420 jobs) | SOUND | Re-run here. |
| 50 | §9 mapping table | GAP (minor) | See items 13 and 15. New Lean theorems (`meets_of_component_sub`, `avoid_packed_iff_reach`) are not mentioned. |
| 51 | §10 (1) "TRN … is the whole of Conjecture N" | UNCLEAR | Same as item 35. |
| 52 | Lean headline theorems (7 named) | SOUND | Statements match the manuscript, with redundant `0 < degree w`. Definitions are faithful. |
| 53 | `nalib.py` / `exact.py` / `run_na.py` | SOUND | Minor code and doc issues; see details. |
| 54 | `random_na.py` | SOUND (doc ERROR) | The docstring says "the component of a random vertex is kept". The code does not do this, so graphs may be disconnected. |
| 55 | `r2check.py` | SOUND | It silently skips graphs over the cap. At order 6 that is K6, which has no NA instance, so nothing is lost. |

## Detailed findings

### A. The proof of Theorem 1.2 (Sections 2–5)

I re-derived every step. The points the commissioning brief asked about:

1. **Parity bookkeeping.**
   - Lemma 3.2. In K' = K − uz the vertex z has odd degree d(z) − 1 ≥ 1. The vertex u was odd,
     because it has positive degree and is not the even vertex. Every neighbour of u in K' is odd,
     because K' has no even vertex other than u. So in a Lovász decomposition b(z) = 1 and
     Z(u) = ∅. The Fan output has b = 0 at z, 1 at u and d mod 2 elsewhere.
   - Lemma 3.3(1).
     - In K_{i+1}, g_i drops from a positive even degree to an odd one.
     - g_{i+1} was odd: it is adjacent to g_i and is not g_i.
     - If i + 1 < k, then g_{i+1} keeps e_{i+2}, an edge distinct from e_1, …, e_{i+1}, so it is the
       even vertex. If i + 1 = k, it is isolated by definition.
   - Lemma 4.1.
     - Every inheritance of (S1)–(S4) in Case 2 is correct.
     - Well-foundedness: (S4) for u in Case 2 forces S' ≠ ∅. If |E(S)| = 1, then u has odd degree 1
       in S, so u ∈ A by (S2), and Case 1 applies.
   - Lemma 4.3. A shortest s–o walk through t would give dist(s, o) ≥ dist(s, t) + 1. The parity
     formula and its read-off are correct.

2. **Fan's hypothesis b(t) > |Z(u)| at every step.** This holds in the stronger form b(t) = 1 and
   |Z(u)| = 0. I instrumented `nalib.fan` during the back-steps only, not inside the separation
   theorem's own Case I/II calls. Over 1,235 back-steps at order 6 and 98,659 at order 8 (all 224 graphs, both routines),
   every step had b(t) = 1 and Z(u) = ∅ (`audit_run.py`, fields `fan_steps`, `fan_bad`).

3. **L1 at the bottom of the chain.**
   - K_k has no even vertex.
   - ℓ is still a leaf at y, because no edge at X is deleted (Lemma 3.3(2)).
   - Y is packed in K: ℓ is a pendant vertex at y ∉ Y. Hence Y is packed in the subgraph K_k.
   - Y ∩ N[ℓ] = Y ∩ {ℓ, y} = ∅.
   - The hypotheses of RD Thm 6.3 are exactly these. They were logged at every call (`l1_bad=0`).
   - "Meets X at most once" then follows: the path through ℓ is Q(ℓ) and avoids Y. Every other path
     meets X only in Y.

4. **The target y.** Lemma 3.2 needs only u ∈ N(z) \ X, and y ∉ X = Y ∪ {ℓ}. The invariant is a
   statement about vertex sets alone. Fan's lemma keeps every vertex set except one, and that one
   gains u. So it does not matter that y ∈ N(ℓ), or that ends move during the re-routings. A
   side remark the paper could add: ℓ can never be a chain vertex x_{i+1}. That would need ℓ to
   precede u = y on a path read from an end other than ℓ, but ℓ is an end.
   - At order 6 the target y occurs in 47 of the 286 constructed sequences.
   - At order 8 it occurs in 4,870 of 11,558.
   - All of them verified.

5. **Section 5, steps (a)–(g).**
   - The degree formula d_H(v) = d_K(v) − [v = y] − |N_G(v) ∩ Y| holds, with |N_G(v) ∩ Y| ≤ 1 by
     packing.
   - d_H(y) = d_G(y) − 1 is even.
   - "Every odd vertex of H is free" is correct.
   - C (the component in H) is the component of y in G − Y, because H's edges are exactly the
     edges of G − Y.
   - w ≠ y gives d_G(w) ≥ 1, so d_H(w) is odd.
   - A = {t} ∪ (odd vertices of H outside C) consists of free vertices, so (S1) holds.
   - (S2) holds because y ≠ t (y is even in H and t is odd).
   - Lemma 2.3 applies: b(y) = 0 in D_K, so P_ℓ ≠ ℓy.

   All SOUND. The Lean proof follows the same route. Its set A is defined as "free ∧ (= t or outside
   C)", which makes freeness explicit.

### B. Theorem 1.4 and Corollary 1.5 (Section 6)

The two counts are right:
- Σ n(P) = |C|, because every vertex of C is adjacent to x, hence odd, hence has exactly one end.
- Σ e(P) = |C|, because each vertex of C has exactly one edge to x.

The per-path claim e(P) = n(P) for x ∈ V(P) is right: each half of P leaves x once and then stays in
C exactly when its end lies in C. Q(y) ∌ x would give n = 2 > 0 = e, a contradiction. SOUND.

Machine check (`audit_run.py --lds`): all Lovász decompositions of every order-6 graph were
enumerated by an edge-driven recursion independent of `exact.py`. For all 85 non-weak pairs, every
decomposition (39,265 in total) has x ∈ Q(y), e(P) = n(P) on paths through x, and e(P) ≤ n(P)
elsewhere.

Remark 6.1 is UNCLEAR: "blocks" is not defined. Remark 6.2: K_{2m} is fine. "The wheel with x as
its hub" must be a wheel with an odd number of spokes, otherwise the hub is even. I checked W5 with x
as the hub: not good and not weak.

### C. Claims about other manuscripts

Checked against the sources; numbering was recomputed from the `.tex` files (`thmnum.py`).

| claim in na.tex | source | verdict |
|---|---|---|
| NA is [CN, Conj. 4.2] | conj-n 4.2 | correct; statements identical |
| TRN ∧ NA ⇒ N is [CN, Thm 4.6]; degree-two case is [CN, Lemma 4.4]; TR ∧ TR_adj ∧ NA ⇒ N is [CN, Cor 4.7] | conj-n §4 | correct |
| NA counts 3, 129, 4,970, 1,305,621 agree with [CN §5] | conj-n §5 table | correct |
| "22 of the 215 NA instances of order 6 and 2,451 of the 9,558 of order 8" have no move | conj-n `data/tables.txt`: `class=N1NA … inclass=215 base=86`, `inclass=9558 base=4588` | **wrong**. 215 = 129 NA + 86 N1 (L1-type, all base cases); 9,558 = 4,970 + 4,588. The correct statement is "22 of the 129" and "2,451 of the 4,970". (conj-n's own table label "NA part … 22/215" is ambiguous, and na.tex turned it into a false sentence that contradicts its own §8 table.) I recomputed both decompositions of the counts. |
| obstruction (2) of [CN §6] is "NA"; (1), (3) remain | conj-n §6 end | correct |
| moves for NA in [CN] are (d), (g), leaf paths; (b) forbids N[c] | conj-n §6.2, Thm 2.3 | correct ((i) is also available but vacuous for NA) |
| N is [DL, Conj 9.1]; [DL, Prop 9.2] reduces DL(1) to near twins | dl-one §9 | correct |
| "NA is stronger than Lemma NP of [DL], which gives only Q(x) ≠ Q(y)" | dl-one Lemma 4.2: *no even vertex, x ∼ y, d(x) ≥ 3 ⇒ Q(x) ≠ Q(y)* | **wrong**. NP has no witness hypothesis. In K4 (x ∼ y, d(x) = 3) NP holds (Q(x) ≠ Q(y) in some decomposition), but no decomposition has x ∉ Q(y) (Theorem 1.4). Machine-checked. NA implies NP only on instances with a witness, at y or at x. |
| `avoid_deg_two` [DL Thm 6.1] follows from the degree-two case | dl-one Thm 6.1 | correct (the parenthetical omits ab ∉ E) |
| Fan [RD Lemma 2.2]; separation [RD Thm 6.1]; L1 set form [RD Thm 6.3] | route-descent §2, §6 | correct; hypotheses match exactly |
| TR is [L1I Conj 4.1]; move (b) is [L1I Thm 3.1] | l1-induction | correct |
| sparse sets of [MS] | multi-sep Thm 21 | correct |
| Fan 2005 JCTB 93, 117–125; Lovász 1968 Tihany | | correct |

### D. Section 7 remarks

- **"Q(y) ∌ x whenever y has a neighbour not adjacent to x"** is false as written. x is a neighbour
  of y and is not adjacent to itself. Add "w ≠ x". With that, the comparison with Q(x) ≠ Q(y) is
  correct.
- **R1** is correct. Given a decomposition of G' = G − xy − yw + xw in which no path contains both x
  and y, the path P through xw contains x and not y. Replacing xw by x y w keeps it a path and adds
  no ends. Q(y) ≠ P, so Q(y) is unchanged and avoids x.
- **R2.**
  - The equivalence is correct: t is a new leaf at y, x is even in G − xy + yt, and the two
    directions are a rename.
  - But t is never introduced in the text. A reader without the R2 note cannot parse the bullet.
  - Brute-force data re-verified with my own enumerator (`r2_indep.py`): 3/3 at order 4 and
    129/129 at order 6.
- **Leaf tails.** GAP.
  - For |A| ≥ 2, goodness of (G − gu, c, A) means only Q_c ∩ A = ∅. It does not mean "every path
    meets A ∪ {c} at most once", which is the invariant of Lemma 3.2. So "applies verbatim" is not
    literally true.
  - The correct argument is one line. c is a leaf, so it lies on exactly one path, and that path is
    Q_c. Fan's lemma keeps that path's vertex set, or adds u ∉ A to it. So Q_c still avoids A after
    the step.
  - The certification claim for NA (|A| = 1) is fine. For |A| = 1 the two invariants coincide.
- **"The open part of N is TRN"** (and §10(1), "it is the whole of Conjecture N") is an
  overstatement. TRN is stronger than N: it also asserts transfers for parents with no witness, about
  which N is silent. With NA, N follows from TRN, and N is equivalent to the restricted TRN that
  conj-n Thm 4.6 actually uses (both child and parent have a witness). Reword to "N reduces to TRN".

### E. Section 8 (computations) and the scripts

**Reproduction.**
```
$ nauty-geng -cq 4 | python3 -B run_na.py --exact --brute --sets --trailbf
graphs=6 allodd=2 pairs=18 na=3 weak=3 weak_not_na=0 neither=15 construct_ok=3 exact_good=3 exact_bad=15 mismatch=0 brute_checked=18 set_instances=0 set_ok=0 trail_bf=3
$ nauty-geng -cq 6 | python3 -B run_na.py --exact --brute --sets --trailbf
graphs=112 allodd=13 pairs=228 na=129 weak=143 weak_not_na=14 neither=85 construct_ok=143 exact_good=143 exact_bad=85 mismatch=0 brute_checked=198 set_instances=16 set_ok=16 trail_bf=143
```
Both rows of the table, the "15/85 non-weak all bad" bullet, "14 at order 6" and "16 set
instances" are reproduced. `brute_checked=198`, not 228: `brute_all` hits its 2,000,000 cap on K6
(15^6 transition systems). `run_na.py` then silently sets `brute = None` and skips the
cross-check for K6's 30 pairs. The text "198 of order 6" is accurate. "All 18 … and 198" should say
"198 of the 228 (K6 exceeds the cap)".

**Independent re-check (my code, none of the manuscript's).** `indep.py` has:
- a graph6 reader;
- a verifier;
- an exact solver that grows the path through the least uncovered edge in both directions, memoised
  on the remaining edge set — a different decomposition order from `exact.py`'s "path from the least
  odd vertex";
- an enumerator of all Lovász decompositions.

`audit_run.py` results:

| range | pairs | NA | weak | good (mine) | iff fails | exact.py disagrees | constructions verified (both methods) | packed sets Y∋x, \|Y\|∈{2,3}: iff fails / built / verify fails |
|---|---|---|---|---|---|---|---|---|
| order 4 | 18 | 3 | 3 | 3 | 0 | 0 | 6/6 | – |
| order 6 (all, K6 included) | 228 | 129 | 143 | 143 | 0 | 0 | 286/286 | 0 / 16 / 0 (35 packed sets, 19 non-weak all bad) |
| order 8, every 40th graph | 140 | 108 | 124 | 124 | 0 | 0 | 248/248 | – |
| order 8, all 224 graphs, constructions only (`--noexact`) | 6,562 | 4,970 | 5,779 | – | – | – | 11,558/11,558 | – |
| order 8, non-weak pairs, my solver only (`nonweak8.py`, stopped by a 1,700 s limit after 200 of 224 graphs) | 578 of 783 | | | 0 good | 0 | – | – | – |

On every construction I also checked the steering sequence against Definition 3.1 and Lemma
3.3(1) with my own code (`steer_bad=0`). Order-8 classification counts, for the table
placeholders: 6,562 pairs, 4,970 NA, 5,779 weak, 783 non-weak.

Random disconnected inputs (`random_audit.py`: two random all-odd pieces and isolated vertices,
which exercises the "odd vertices outside C" part of A):

| N | graphs | weak pairs | constructions verified | iff checked / fails | random packed Y: checked iff / fails; built / verify fails |
|---|---|---|---|---|---|
| 8 | 300 | 2,069 | 4,138 / 4,138 | 4,642 / 0 | 1,947 / 0; 1,699 / 0 |
| 10 | 15 | 251 | 502 / 502 | 398 / 0 | 235 / 0; 227 / 0 |
| 16 | 100 | 5,982 | 11,964 / 11,964 | – | –; 5,775 / 0 |
| 24 | 20 | 3,361 | 6,722 / 6,722 | – | –; 3,267 / 0 |

**Verifier soundness (mutation test, `mutate.py`).**
- For every weak pair at order 6 the constructed output was corrupted 858 ways: a path dropped, an
  edge dropped, a path duplicated, paths merged, a non-edge appended, two vertices swapped.
  `nalib.check_na_output` and my verifier agreed on every mutant (715 rejected by both).
- I also fed it every Lovász decomposition in which x ∈ Q(y), from the full enumeration: 49,444 of
  them, all rejected.
- The verifier shares only `path_edges`, `ends_count` and `deg` with the construction. Its
  independence claim is fair.

**The data behind the table.**
- Order 10. The row's numbers first came from commit `ba80a1c`, whose `na_construct` used only the
  T-join/Euler-trail routine. The paper's routine (Lemmas 4.1/4.3) and "both routines on every
  instance" were added afterwards. The rerun with both routines (started 23:58 with the current
  `nalib.py`/`run_na.py`) has now finished
  (`data/n10_0.txt`, `data/n10_1.txt`: construct_ok = weak = 730,674 + 718,200), and the row is
  supported.
- Order 8, order-12 slices and random. Still placeholders: `\textsc{n8pairs}`, `n8weak`, `n8result`,
  `n12pairs`, `n12na`, `n12weak`, `n12result`, `rndpairs`, `rndweak`, `rndresult`. The random
  row also has an empty NA cell.
- At the end of the audit these runs had finished:
  - `data/random.txt`: N = 12, 14, 16, 20, every weak pair and set built and verified;
  - both order-12 slices: construct_ok = weak, set_ok = set_instances;
  - `data/r2_n8.txt`: R2 holds in 4,970/4,970.

  `data/n8.txt` (construction plus exact on the non-weak pairs) was still empty and running. The
  numbers now exist for every placeholder except the order-8 result. The text still has to be
  written: R2 at order 8 is not mentioned in §7 or §10, which say "orders 4 and 6".
- "The counts in `data/`" for the set form: these now exist (`set_instances` in the order-12 slice
  files, `sets` in `random.txt`), but the text should name the files and give the numbers.

**Code-level remarks (none affects a result).**
- `nalib.separation` documents "X packed" but never asserts it. The final verifier would catch any
  consequence.
- `nalib` module docstring and `exhausting_trail` refer to "the trail lemma of the manuscript". The
  manuscript no longer has one; it was replaced by Lemmas 4.1–4.3.
  - The descent `assert D2 < D` is valid: components of C − t₂ not containing y lie in D \ {t₂}.
    But this is not argued anywhere.
- `run_na.py` line 69, `assert exact_trail(C, y) if False else …`, is dead code that would raise
  `NameError` if the condition were ever true.
- `--sets` runs only the "paper" routine.
- `random_na.py`:
  - The docstring says "the component of a random vertex is kept", but nothing is removed, so the
    graphs may be disconnected. Harmless; the docstring is wrong.
  - With odd N, the even-vertex pairing would index past the list. Only even N are used.
- `r2check.py` silently skips graphs over the brute-force cap. At order 6 that is only K6, which has
  no NA instance, so the 129 count is complete.

### F. Lean (`NeighbourAvoid.lean`)

**Build.** `lake build GallaiLean.NeighbourAvoid` succeeds (18,385 jobs). The full `lake build`
succeeds with 18,420 jobs, as §9 says. The file produces no warnings.
`grep sorry|admit|axiom|native_decide|implemented_by` finds nothing in the file.

**Axioms.** `#print axioms` (scratch file `A33-scripts/Axioms.lean`) gives
`[propext, Classical.choice, Quot.sound]` for 17 theorems:
- `neighbourAvoidOn`, `neighbourAvoid`, `avoid_packed_of_reach`, `avoid_of_reach`, `avoid_iff_reach`;
- `mem_pathEndingAt_of_component_sub`, `meets_of_component_sub`, `avoid_packed_iff_reach`;
- `conjNDegTwoOn`, `conjN_of_tightTransferN`, `conjN_of_TR`;
- `steer_meetsOnce`, `steer_of_inv`, `exists_inv_subgraph`, `exists_toggle_walk`,
  `fan_step_meetsOnce`, `apexSep_meetsOnce`.

**Statements versus the manuscript.**
- `neighbourAvoidOn : NeighbourAvoidOn V`, where `NeighbourAvoidOn` (ConjN.lean l.169) is:
  - `(evenSet G).card = 0`;
  - `G.degree y % 2 = 1` (redundant);
  - `G.Adj x y`;
  - `∃ w, G.Adj y w ∧ w ≠ x ∧ ¬G.Adj x w`;
  - conclusion `AvoidDecomp G y {x}`.

  This is exactly Conjecture 1.1. `AvoidDecomp` is a `PathDecomp` (edge-disjoint paths covering
  E, each with `IsPath` and positive length) with `ends v = degree v % 2`, whose paths ending at
  y miss A. That is faithful, and nothing in it trivialises the statement.
- `avoid_packed_of_reach`:
  - hypotheses: `Packed G Y` (no two adjacent, no common neighbour), y ∉ Y odd, a walk y → w
    avoiding Y, w with no neighbour in Y and `0 < degree w`;
  - conclusion: `MeetsOnce D Y` and Q(y) ∩ Y = ∅.

  This is Theorem 1.2. The degree hypothesis is redundant: if w = y, y is odd; otherwise w ends a
  walk. §9 states this formulation correctly.
- `avoid_iff_reach`. This is Corollary 1.5; the RHS has the same redundant positive degree.
- `mem_pathEndingAt_of_component_sub`. This is Theorem 1.4 without "y odd": slightly more
  general, and vacuous if y is isolated.
- `conjNDegTwoOn`, `conjN_of_tightTransferN`, `conjN_of_TR`. These are one-line compositions of
  `conjNDegTwo_of_neighbourAvoid`, `conjN_of_tight_neighbourAvoid` and
  `conjN_of_TR_neighbourAvoid` with `neighbourAvoidOn`. The ConjN definitions match conj-n:
  - witness `w ∉ evenSet` is w ≠ g;
  - `TightTransfer` and `TightTransferAdj` quantify over all A and all `V : Type u`, which is
    stronger than needed, as conj-n Remark 4.8 says.

**Hypotheses that are vacuous or too strong.** None found. `steer_meetsOnce` is stated for an
arbitrary edge-deletion-stable property P. In the application P K' is "K' ≤ K and K' agrees
with K at X". It is correctly discharged at every step, since steering never deletes an edge at
X.

**Mismatches between the Lean and the manuscript's statements** (the §1 "Status" claim is
"every numbered result … is formalised"):
- Lemma 2.1 claims a bijection φ with exact vertex sets. `fan_single_supp` proves only a cover:
  every new path lies in an old path plus u. That suffices (`meetsOnce_of_cover`), but it is weaker
  than the lemma as stated.
- Lemma 4.3 asserts t ∈ C with t odd in H. `exists_inv_subgraph` does not export this. It is not
  needed, because the Lean A carries freeness explicitly.
- Lemma 4.1 in Lean is more general than stated: A need not consist of free vertices.
- Lemma 3.3(1)–(2) are proved inside `steer_meetsOnce`, not stated.
- The file also proves a set-form boundary, `meets_of_component_sub` and
  `avoid_packed_iff_reach` (Theorem 1.2 is sharp). The manuscript does not state or list it.

### G. Example 5.2 (machine-checked, `wheel.py`)

- In H, the odd vertices are 3 and 4, and d_H(y) = 4. ✓
- y,2,3,4,y,3 is a steering sequence. ✓
- K5 has edges yℓ, y1, y5, 12, 15, 45. ✓
- "All its degrees are odd" is wrong: vertex 3 has degree 0. It should say "no even vertex".
- There are exactly 24 steering sequences from y avoiding {1, ℓ}. They end at 3 or 4, and every
  one revisits y. ✓
- The hand argument in the third bullet is correct.

## Required fixes

1. **§8 table.** Replace the placeholders (`\textsc{n8pairs}`, `n8weak`, `n8result`,
   `n12pairs`, `n12na`, `n12weak`, `n12result`, `rndpairs`, `rndweak`, `rndresult`). Fill the
   empty NA cell of the random row, or drop those rows until the runs finish. Make "the counts in
   `data/`" name the files.
   - For order 8 the classification is 6,562 pairs, 4,970 NA and 5,779 weak (783 non-weak).
   - The order-12 slices and random rows can be filled from `data/` now: slices 17 and 517 have
     217,750 + 479,522 pairs, 199,689 + 448,780 NA and 215,324 + 475,333 weak, all built, with
     57,463 + 123,426 set instances, all built. Random N = 12–20 has 402,664 pairs, 389,542 NA and
     398,380 weak, all built.
   - If R2 at order 8 (`data/r2_n8.txt`, 4,970/4,970) is to be used, update §7 and §10, which still
     say "orders 4 and 6".
2. **§1, "Why it matters", fourth bullet.** "22 of the 215 NA instances of order 6 and 2,451 of
   the 9,558 of order 8" should be "22 of the 129 … and 2,451 of the 4,970". 215 and 9,558 are the
   sizes of N1 ∪ NA in conj-n's closure run (`tables.txt`: base = 86 and 4,588).
3. **§1, third bullet.** Delete or correct "NA is stronger than Lemma NP of [DL], which gives only
   Q(x) ≠ Q(y)". NP (dl-one Lemma 4.2) needs only d(x) ≥ 3 and holds in K4, where NA's
   conclusion fails. Say instead that, on instances with a witness, NA's conclusion is stronger than
   NP's.
4. **§7, second bullet.** "whenever y has a neighbour not adjacent to x" should be "a neighbour
   w ≠ x not adjacent to x". As written it is false (K4).
5. **Example 5.2.** "all its degrees are odd" should be "it has no even vertex" (vertex 3 is
   isolated). Write N(ℓ) = {y} rather than y = N(ℓ).
6. **§7, "Leaf tails".** Replace "the proof of Lemma 3.2 applies verbatim with X = A ∪ {c}" by
   the correct invariant. For |A| ≥ 2, goodness is not "meets A ∪ {c} at most once". The proof
   is: the leaf c lies on exactly one path; Fan keeps its vertex set or adds u ∉ A; so Q_c still
   avoids A.
7. **§1 "Status" and §9 table.**
   - Do not claim that Lemma 2.1 (bijection form) and Lemma 4.3 (t ∈ C, t odd) are formalised
     as stated. Say that `fan_single_supp` gives the cover form used, and that the Lean Lemma 4.3
     omits the property of t.
   - List Remarks 5.1, 6.1 and 6.2 among the paper-only items.
8. **§7 first bullet and §10(1).** Replace "the open part of N is TRN" and "it is the whole of
   Conjecture N" by "N reduces to TRN". TRN is stronger than N.
9. **§8 Tools, exact solver.** State that the brute-force cross-check covered 198 of the 228
   order-6 pairs (K6 exceeds the enumeration cap).

## Optional suggestions

- Abstract, bullets "Set form" and "Exact boundary": add "y odd".
- Remark 6.1: define "block" or delete the remark. Remark 6.2: "a wheel with an odd number of
  spokes".
- §7 R2: define t (a new leaf at y) before using it.
- §7 `avoid_deg_two` parenthetical: add ab ∉ E.
- §5 or Remark 5.1: add the one-line observation that ℓ is never a Fan chain vertex. It makes the
  "target y is allowed" point concrete for readers used to move (b).
- State the set-form boundary (`meets_of_component_sub`, `avoid_packed_iff_reach`: Theorem 1.2 is
  sharp among decompositions meeting Y at most once). It is already in Lean, and my solver confirms
  it on all 35 packed sets at order 6 and 2,182 random instances of orders 8 and 10.
- Scripts:
  - Assert packedness in `nalib.separation`.
  - Delete the stale "trail lemma of the manuscript" references, or add a proof of the descent in
    `exhausting_trail` to the README.
  - Remove the dead `exact_trail … if False` code.
  - Fix the `random_na.py` docstring.
  - Make `run_na.py --brute` report how many pairs were skipped by the cap instead of skipping
    silently.
- conj-n still lists NA as open (Conj. 4.2, §8 item 2). A cross-reference there would help.

## Audit scripts (`research/audit/A33-scripts/`)

| file | purpose |
|---|---|
| `thmnum.py` | recompute amsthm numbering of a `.tex` file (used to check every cross-manuscript citation) |
| `indep.py` | independent graph6 reader, verifier, exact solver (edge-driven, memoised), enumerator of all Lovász decompositions; no manuscript code |
| `audit_run.py` | driver: iff check, comparison with `exact.py`, constructions checked by my verifier, Fan/L1/steering instrumentation, §6 per-path identity (`--lds`), set form (`--sets`) |
| `wheel.py` | every claim of Example 5.2 |
| `mutate.py` | mutation test of `check_na_output` |
| `r2_indep.py` | independent check of the R2 data |
| `random_audit.py` | random disconnected graphs with isolated vertices and random packed sets; iff checks at small N |
| `Axioms.lean` | `#print axioms` and `#check` of the headline theorems |
| `nonweak8.py` | my solver on the non-weak pairs of order 8 (Theorem 1.4 says all are bad) |
| `logs/results.txt`, `logs/nonweak8_partial.txt` | raw outputs of every run quoted here |

Commands used:
```
cd research/audit/A33-scripts
nauty-geng -cq 6 | python3 -B audit_run.py --sets --lds
nauty-geng -cq 8 | python3 -B audit_run.py --every 40      # both exact solvers
nauty-geng -cq 8 | python3 -B audit_run.py --noexact       # all constructions
nauty-geng -cq 8 | timeout 1700 python3 -B nonweak8.py
nauty-geng -cq 6 | python3 -B mutate.py
python3 -B wheel.py
for n in 4 6; do nauty-geng -cq $n | python3 -B r2_indep.py; done
python3 -B random_audit.py 8 300 1 --exact; python3 -B random_audit.py 10 15 2 --exact
python3 -B random_audit.py 16 100 3; python3 -B random_audit.py 24 20 4
source ~/.elan/env && cd lean && lake env lean ../research/audit/A33-scripts/Axioms.lean
```
