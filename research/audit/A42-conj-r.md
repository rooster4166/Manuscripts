# Audit A42: Conjecture R, joint form, static steering, gluing and the residual (session `claude/conj-r`)

**Auditor:** independent audit agent, 2026-11-28. **Scope:** `manuscripts/conj-r/conj-r.tex` (and PDF),
`README.md`, `data/`, `scripts/`; `lean/GallaiLean/LemmaR.lean` and `lean/GallaiLean/JointR.lean`.
**Scripts and outputs:** `research/audit/A42-scripts/`. I edited no other file and made no commit.
Classes: ERROR = false statement; GAP = proof missing a needed step; OVERCLAIM = status or claim stronger
than supported; MINOR = wording or precision.

## Verdict

| item | verdict | main finding |
|---|---|---|
| Lemma 3.1 (Lemma R), Lemma 3.2 | **OK** | Correct. The end counting and the pendant-leaf step are complete, and the Lean proofs match. |
| Def 3.3, Prop 3.4 (Criterion R ⇒ good) | **OK** | (TS) and (TI) are established for (a), (b) and (b′). `CritRPath` is exactly Def 3.3. |
| Remark 3.5 (exact form) | **OK** | — |
| Prop 6.1, Prop 6.2, Thm 6.3 | **OK**, MINOR | Proofs correct. The Lean statements conclude only `LN2Good`, not Q(c₁)=Q(c₂)=P, and `joint_of_leaf` covers only d(c₁)=1. |
| **Lemma 6.4 (Lemma S)**, both directions and the g∼h variant | **OK**, MINOR | Correct. The sufficiency, the necessity, the t = g case and the g∼h reduction all check. My own implementation agrees with an exhaustive trail search on **694,256** cases (all order-8 joint paths; the order-10 sample; order 6), with 0 disagreements. Two implicit steps are MINOR. |
| Cor 6.5 | **OK**, MINOR | Needs both ends of P to have positive degree in K₀ (otherwise Prop 6.1 applies). |
| **Theorem 7.1 (gluing)**: G1–G3, both parities of d_B(v) | **OK**, MINOR | Every case is correct, including d_A(v)=0, X = Q_A(c_i) under (G1), and merged paths ending at c_i or c_j. (G3)'s first disjunct is redundant. The (G3) branch silently assumes (G1) fails. "NA's boundary theorem [NA, Cor 1.3]" is the wrong name: Cor 1.3 is NA's positive corollary, and the boundary theorem is Thm 1.4. |
| Conj 7.2 (AE), Prop 7.3 | **OK** | — |
| "reduces exactly to AE" (l. 53–54), "(R2) … equivalent to AE for F − cᵢaⱼ" (l. 552) | **OVERCLAIM** | Only AE ⇒ good is proved. AE for F − cᵢaⱼ is equivalent to "good with Q(cᵢ) = cᵢaⱼ", not to "good". |
| Def 9.1, Prop 9.2 (Criterion R3 ⇒ L_N(3)) | **OK** | Correct. This includes interior c_k and a_k, and ends of P₁ interior to P₂. All 84,064 shipped R3 certificates (commit d877c9f) satisfy Def 9.1 and complete to valid L_N(3) decompositions. |
| **Abstract l. 45–46**: "the non-tight remainders F − E(P) are exactly those with a universal odd vertex or a cut vertex" | **ERROR** | False. At order 8, 123,830 tight remainders have a cut vertex and 4,375 tight ones are disconnected. 859 non-tight ones are disconnected with neither a cut vertex nor a universal vertex. The body (l. 288–289) states the correct version. |
| **§10 l. 639–643**: "(R3) the 2-cut separations … A proof of J and AE together with a 2-cut gluing lemma would prove L_N(2)" | **OVERCLAIM** | (R3) also contains the cut-vertex class outside Theorem G with cᵢ not a leaf: 45 instances at order 8 and 4,323 at order 10. Neither J, nor AE, nor a 2-cut lemma covers it. |
| Lean (`LemmaR.lean`, `JointR.lean`) | **PASS**, MINOR | Builds. No `sorry`, `admit`, `axiom` or `native_decide`. `#print axioms` gives `propext, Classical.choice, Quot.sound` for all 16 theorems (matches `data/axioms.txt`). `CritRPath`, `CriterionR`, `LN2`, `ConjR` and `ConjAE` are faithful. Some table and docstring wording is MINOR. |
| Computations | **PASS** | Every number I re-derived matches (table in §3), with my own code. That code is a generator check (Burnside plus isomorphism test), an independent exact solver, an independent checker and my own coverage code. `lnsolve3`'s degree bound is sound (proof and 0 disagreements). `wcheck.c` accepts no corrupted witness. The Conjecture J spot check is 111,445 order-10 queries. |
| Status labels, README | **OK**, MINOR | L_N(2) and Conjecture R are never claimed. The remaining points are wording, connectivity of the data, one example sentence and reproducibility details. |

**Required fixes: 3** (one ERROR, two OVERCLAIM). No GAP in any proof. The MINOR fixes are recommended.

## 0. Versions audited

- I started at commit `10426fa`. While the audit ran, `d877c9f` appeared. It only adds
  `data/m3_R3_all_order8.txt.gz` and six summary lines in `data/m3_order8.txt` (Criterion R3 at all 84,064
  instances); I audited those too (§3.9).
- Unchanged throughout:

  | file | md5 |
  |---|---|
  | `conj-r.tex` | `a1a8f3ec…` |
  | `README.md` | `7536f8fc…` |
  | `LemmaR.lean` | `134c2ce5…` |
  | `JointR.lean` | `3f96caad…` |
  | `lnsolve3.c` | `b243f689…` |
  | `wcheck.c` | `02a5d925…` |
  | `gen.c` | `4776ca6f…` |

- **Line numbers** refer to `conj-r.tex` at `a1a8f3ec`.
- **Compiled numbering:** Lemma 3.1 (R), Lemma 3.2, Def 3.3, Prop 3.4, Rem 3.5, Conj 5.1 (J), Props 6.1, 6.2, Thm 6.3, Lemma 6.4 (S), Cor 6.5, Thm 7.1 (G), Conj 7.2 (AE), Prop 7.3, Examples 8.1–8.3, Def 9.1, Prop 9.2.
- **pdflatex** (scratch copy, run twice): 11 pages, no errors, no undefined references, no overfull boxes. There are five underfull hboxes (ll. 116, 121–122, 163–171, 673–680) and one hyperref Unicode warning (`latex.out`).
- The committed `conj-r.pdf` differs in bytes from my build. That is expected from timestamps.

## 1. The proofs

### 1.1 Lemma 3.1 (Lemma R), ll. 153–171: OK

The proof establishes b_D = b_P + b_{D₀} and uses the parity lemma.
- At an end v of P: d_G(v) is odd (positive degree, no even vertex). So 1 + b_{D₀}(v) is odd, and with b_{D₀} ≤ 1 this gives b_{D₀}(v) = 0.
- Elsewhere b_D = b_{D₀} ≤ 1 with the right parity.

The path ending at cᵢ is P, because b_{D₀}(cᵢ) = 0. The two cases for c_j are handled correctly. P may end at a_j, and a_j may be interior to P in the case "P does not end at c_j": nothing requires otherwise. The hypothesis cⱼ ≠ cᵢ is used.

Lean `lemmaR` states exactly this. Its conclusion is existential (∃ D); D₀ ∪ {P} is the witness in the proof.

### 1.2 Lemma 3.2, ll. 177–188: OK

cⱼ is not an end of P (cⱼ ≠ cᵢ and P does not end at cⱼ), so d_{K₀}(cⱼ) is odd. The hypothesis d_G(cⱼ) odd is needed: an isolated cⱼ would break the pendant-leaf lemma. The pendant-leaf lemma (NA Lemma 2.3, `avoid_of_apexSep`) needs:
- cⱼ odd in K₀;
- b(ℓ) = 1 and b(cⱼ) = 0 in K₀ + cⱼℓ.

Both hold for a parity decomposition of K₀ + cⱼℓ. P_ℓ ∌ aⱼ gives Q(cⱼ) = P_ℓ − ℓ ∌ aⱼ. `lemmaR_leaf` matches.

### 1.3 Def 3.3, Prop 3.4, ll. 190–210: OK

- **(a)** T = ∅. Lemma 3.1 applies with P ending at cⱼ and aⱼ ∉ P.
- **(b)** The proof gives (TS): aⱼ ∉ {ℓ, cⱼ}. It gives (TI): N(ℓ) = {cⱼ}; aⱼ ≁ cⱼ; and aⱼ is odd, since aⱼ ≠ cᵢ, P does not end at aⱼ (so aⱼ is off P or interior to it) and aⱼ ≠ cⱼ.
- **(b′)** (TS) uses aⱼ ∉ {cⱼ, w}, and (TI) uses N_{K₀}(cⱼ) = {w}, aⱼ odd and aⱼ ≁ w. All three are hypotheses or proved. (TG) for the leaf cⱼ gives "the path ending at cⱼ avoids aⱼ".

The definition matches LN Def 6.2 as revised after A40. `CritRPath` is a faithful transcription: (b) is `apex K₀ {cⱼ}` with the tail `(none, some cⱼ, some aⱼ)`, and (b′) has `∀ v, K₀.Adj cⱼ v ↔ v = w`, `aⱼ ≠ w` and `¬K₀.Adj aⱼ w`. `CriterionR` is the disjunction over both orientations.

### 1.4 Remark 3.5, ll. 212–218: OK

D − Q_D(cᵢ) has one end per vertex. If P = Q_D(cᵢ) ends at cⱼ, then P = Q_D(cⱼ) avoids aⱼ. Otherwise the paths of D₀ ending at cⱼ are Q_D(cⱼ).

### 1.5 Props 6.1, 6.2 and Thm 6.3, ll. 331–363: OK

- **6.1.** The even vertices of K₀ lie in {c₁, c₂}. A leaf cᵢ is isolated in K₀. Conversely, K₀ has at most one even vertex if and only if some cᵢ is a leaf. So "Prop 6.1 coverage = some cᵢ a leaf" (`cov.py`) is exact.
- **6.2.** An end with N_{K₀}(g) = {y, z} and y ≁_{K₀} z is a token of degree 2. With T = ∅ the side conditions of (S) are vacuous, and at most one token remains. Note that y ∼ z in F via an edge of P is allowed. This is correct, since K₀ − gy − gz + yz is still simple.
- **6.3.**
  - Edges at h are never deleted: g₀ = g ≠ h and g_t ∉ X ∋ h for t ≥ 1.
  - The tokens of K_t lie in {g_t, h}.
  - A target u is odd. It is not g_t, it is not h (u ∉ X), and it has an edge. The proof should say this last point (MINOR M7).
  - u is not adjacent to h, since N(h) ⊆ X.
  - A return to g (when g ∉ X) is legal, because g is then odd.

  `steerK_of_steer` proves exactly this by induction on `Steer`. A case g = h is vacuous, since the first target would be a neighbour of h outside X.

### 1.6 Lemma 6.4 (Lemma S), ll. 367–399: OK (two implicit steps, MINOR)

I checked each direction line by line.

- **Sufficiency, t ≠ g.**
  - T_t ⊆ V(H) − t: N(t) ⊆ V(H), t ∉ N(t) and t ≠ g.
  - d_K(t) is odd: t ≠ g, t ≠ h (t ∉ X) and d(t) > 0.
  - In S = star(t) ∪ J the parities are: t odd; w ∈ N(t) − g even (1 + odd); g odd in both sub-cases g ∈ N(t) and g ∉ N(t); every other vertex even. The proof omits the last kind of vertex (trivial).
  - star(t) ⊆ E(H) and J ⊆ E(H − t), so S ⊆ E(H).
  - The component of g contains t, hence star(t).
  - The Euler trail stays in V(H) = V(K) − X. Every intermediate arrival is at an odd vertex not adjacent to h. That includes arrivals at t (interior passes keep parity) and returns to g.
  - The last edge at t is used last, so the token retires at t.
- **Sufficiency, t = g.** S is even, the Euler circuit from g uses all of star(g), and each intermediate return to g is to an odd vertex (d(g) − 1 − 2m).
- **Necessity.**
  - Legal M-moves of the g-token alone with T = ∅ are exactly the steps of a trail with every target outside N[h]. Such a target, once its edge is deleted, would be adjacent to the token h, and h's edges are never deleted. The proof uses this translation without stating it (MINOR M8).
  - The trail lies in H, every edge at t is used (so N(t) ⊆ V(H)), and the odd vertices of S are {g, t} or none.
  - S − star(t) ⊆ E(H − t) has odd set exactly T_t: d_J(w) = d_S(w) − [w ∈ N(t)].
  - A T-join exists if and only if every component has even |T ∩ C|.
- **g ∼ h.**
  - The first move goes to u ∈ N(g) − X. In K − gu, X is unchanged: the edge gu is not at h.
  - g is odd and in X, so it is never a target again.
  - u is even in K − gu unless it is a leaf, which retires at once. The first part applies with u in the role of g, since u ∉ X.

The statement "whose even vertices are g and h (g ≠ h, g even)" should say that h is even. With h of degree 0 the equivalence still holds, with X = {h}. With h odd, the M-move semantics differ (targets in N[h] become legal), and the "only if" is no longer the right statement. In the application both ends have degree ≥ 3, so this is MINOR (M8).

**Computational confirmation** (`jcov.c`, own code: trail search, and the T-join criterion implemented from the statement):

| instances | cases (joint path with both ends active, × 2 orientations) | disagreements |
|---|---|---|
| all of order 8 | 443,128 | 0 |
| the order-10 sample | 250,316 | 0 |
| all of order 6 | 812 | 0 |

The manuscript reports 62,530 cases.

### 1.7 Cor 6.5, ll. 408–411: OK

It follows from the sufficiency direction and Thm 6.3, in both cases g ∉ X and g ∼ h. Lemma 6.4 needs both ends of P of positive degree in K₀. When an end is a leaf of F, Prop 6.1 applies instead (MINOR M9). `cov2.py` applies `tjoin_ok` only when no cᵢ is a leaf, so the coverage is sound.

### 1.8 Theorem 7.1 (gluing), ll. 424–474: OK (MINOR wording)

Setting:
- B is a component of F − v, so there is no A–B edge.
- E(F) = E(F_A) ⊔ E(F_B) and V(F_A) ∩ V(F_B) = {v}.
- cᵢ ∈ A, because cᵢ ≠ aⱼ.

Both tools are correct:
- **The pendant leaf, two-end form.** If R_ℓ ≠ ℓv, v is interior to R_ℓ, and the path carrying v's own end is a different path not containing ℓ.
- **Gluing.** The two paths share only v.

**d_B(v) odd.**
- F_B is all-odd, and L₁ (`lovasz_avoid_nonadj`) for (cⱼ, v) applies: cⱼ ≁ aⱼ. Then Y = Q_B(v) ≠ Q_B(cⱼ), so the other end of Y is not cⱼ.
- F_A + vℓ is all-odd. When aᵢ ∈ A, L₁ for (cᵢ, aᵢ) applies. If R_ℓ = Q(cᵢ), then R_ℓ − ℓ is a sub-path and still avoids aᵢ. When aᵢ ∈ B, Q_A(cᵢ) ⊆ A ∪ {v}.
- If b_A(v) = 2, the two A-paths at v are distinct, and at most one ends at cᵢ. Merging the other with Y gives b(v) = 2 + 1 − 2 = 1. The merged path ends at neither cᵢ nor cⱼ.
- d_A(v) = 0 is possible only for disconnected F. Then R_ℓ = ℓv and b_A(v) = 0, which is fine.

**d_B(v) even.**
- F_A is all-odd. L₁ on F_B + vℓ for (cⱼ, v) gives Q(cⱼ) ∌ v, hence ∌ ℓ. After deleting ℓ, b_B(v) ∈ {0, 2}, and no B-path at v is Q_B(cⱼ).
- **(G1):** L₁ on F_A for (cᵢ, aᵢ). If X = Q_A(cᵢ) is merged, X ∪ Y₁ avoids aᵢ, because Y₁ ⊆ B ∪ {v} and aᵢ ∈ A.
- **(G3), cᵢ ≁ v:** L₁ for (cᵢ, v).
- **(G3), cᵢ ∼ v:** NA's corollary (`avoid_of_reach`) applies with G = F_A, x = v, y = cᵢ: F_A has no even vertex, and the component of cᵢ in F_A − v equals that in F − v.
- Under (G3) the proof writes "Q_A(cᵢ) ⊆ A avoids aᵢ ∈ B". This is valid only if the (G3) route is used when (G1) fails, that is, when aᵢ ∈ B. With aᵢ ∈ A the (G3) route could put aᵢ on Q_A(cᵢ). Say so (MINOR M4).

Hypotheses of the cited results: L₁ needs an all-odd graph, c odd, a ≠ c and a ≁ c. NA Cor 1.3 needs no even vertex, x ≠ y, y odd, and a non-neighbour of x in y's component of G − x. All are met in every application.

Wording (MINOR M3, M4):
- (G3)'s first disjunct "cᵢ ≁ v" implies the second, because cᵢ is itself a vertex of its component not adjacent to v.
- l. 466 calls NA Cor 1.3 "NA's boundary theorem". Cor 1.3 is the positive corollary; the boundary theorem is NA Thm 1.4, which l. 481 uses without a citation.

`allcov.gluing` is exactly (G1) ∨ (G2) ∨ (G3) for the orientation v = aⱼ with cᵢ ∉ B, and it is applied in both orientations.

### 1.9 Conj 7.2 (AE), Prop 7.3, ll. 485–506: OK

- In K = F − cᵢaⱼ: cᵢ is isolated; aⱼ is the only possible even vertex; cⱼ is odd; cⱼ ≁ aⱼ.
- AE with g = aⱼ gives D₀, and if aⱼ is isolated any Lovász decomposition works.
- Lemma 3.1 with P = cᵢaⱼ: aᵢ ∉ {cᵢ, aⱼ}, P does not end at cⱼ, and P may end at aⱼ.
- The remark on L₁* is right: {g} ∩ (N[c] ∪ N(g)) = ∅ (L1I Def 2.1). So are the two remarks on why the leaf-tail lemma and a Case-I step do not apply.

`ConjAE` is AE: `card ≤ 1` and `g ∈ evenSet` mean exactly one even vertex. `ln2_of_leaf_at_head` is the "hence" form, under the global `ConjAE` (MINOR M10).

**OVERCLAIM (required fix #3).**
- l. 53–54 says the leaf case "reduces **exactly** to Conjecture AE".
- l. 552 says (R2) is "**equivalent** to AE for F − cᵢaⱼ".

Only AE(F − cᵢaⱼ; cⱼ, aⱼ) ⇒ good is proved. The true equivalence is AE(F − cᵢaⱼ; cⱼ, aⱼ) ⟺ the instance has a good decomposition with Q(cᵢ) = cᵢaⱼ. The converse "good ⇒ AE" fails to follow. In a good decomposition, Q(cᵢ) may continue through aⱼ. Deleting cᵢ then leaves two ends at the even vertex aⱼ (the pendant-leaf tool of Thm 7.1), so no Lovász decomposition of K results. No counterexample exists in the data, but the equivalence is not proved.

### 1.10 Def 9.1, Prop 9.2, ll. 594–617: OK

- **Ends of the pre-committed paths.** They are even or isolated in K₀: in (B), an end of P₁ is not an end of P₂ (four distinct ends) and loses 1 + {0, 2} edges.
- **Other vertices.** These include c_k and a_k, even when interior to P, or to both P₁ and P₂ (losing 4 edges). They stay odd with positive degree.
- **(TS) and (TI).** They hold for the new-leaf and the leaf tail as in Prop 3.4.
- **Conclusion.** D₀ ∪ {pre-committed paths} has exactly one end per vertex, with Q(cᵢ), Q(cⱼ) the pre-committed paths and Q(c_k) in D₀. The fact that c_k is odd in K₀ (needed for the pendant leaf) is implicit in "every vertex not an end is odd". `r3.py` implements Def 9.1 exactly and checks the final decomposition with all three avoidances.

### 1.11 Abstract l. 45–46: ERROR (required fix #1)

> "At order 8 the non-tight remainders F − E(P) are exactly those with a universal odd vertex or a cut vertex."

The order-8 joint paths with both ends active, recomputed with my solver (`k0_breakdown.out`), give:

| K₀ (both ends active) | tight | not tight |
|---|---|---|
| 2-connected, no universal odd vertex | 72,975 | **0** |
| 2-connected, universal odd vertex (O1) | 0 | 10,595 |
| cut vertex, O1 | 0 | 5,233 |
| cut vertex, no O1 | **123,830** | 3,697 |
| disconnected (non-isolated part), no O1 | **4,375** | **859** |

So "exactly those" fails in both directions:
- Most remainders with a cut vertex are tight.
- If "cut vertex" is meant literally, 859 non-tight remainders have neither property.

The body (l. 288–289) states the correct fact: a 2-connected K₀ is tight if and only if it has no universal odd vertex. In addition, "O1 ⇒ not tight" is a theorem, not only data. With two even vertices there are (n₀ − 2)/2 paths, so a vertex of degree n₀ − 1 would need n₀ − 1 ≤ 1 + 2((n₀ − 2)/2 − 1) = n₀ − 3. Hence l. 290 ("a universal vertex of F must lie on P") is provable (MINOR M6).

### 1.12 §10, ll. 630–643: OVERCLAIM (required fix #2)

- (R3) is defined at l. 553–554 as "a cut vertex aⱼ with all of the component of cᵢ in F − aⱼ adjacent to aⱼ, but cᵢ not a leaf; or a 2-cut".
- §10 item 3 (l. 639) calls (R3) "The 2-cut separations".
- l. 643 concludes: "A proof of J and AE together with a 2-cut gluing lemma would prove L_N(2)."

The cut-vertex part of (R3) is non-empty: 45 instances at order 8 and 4,323 at order 10 (`instclass.out`; I reproduced the count). It is separated (so J does not apply) and has no leaf at the head (so AE does not apply). It is not a 2-cut. So the implication is not supported as stated.

## 2. Lean

- **Build.** `lake build`: "Build completed successfully (18446 jobs)". I also recompiled `LemmaR.lean` and `JointR.lean` from source with `lake env lean`: no errors.
- **Forbidden constructs.** `grep` finds no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by` or `unsafe`.
- **Axioms.** `A42Axioms.lean` / `A42Axioms.out` runs `#print axioms` on all 16 theorems, including `evenSet_delEdgeList_sub`, which is not in `axioms.txt`. Each gives `[propext, Classical.choice, Quot.sound]`, which matches `data/axioms.txt`.

Faithfulness:

| manuscript | Lean | verdict |
|---|---|---|
| Lemma 3.1 / 3.2 | `lemmaR` / `lemmaR_leaf` | faithful; conclusion ∃ D |
| Def 3.3 | `CritRPath`, `CriterionR` | faithful (all three branches, both orientations) |
| Prop 3.4 | `ln2_of_criterionR` (instance: odd degrees, `[c₁,a₁,c₂,a₂].Nodup`, cᵢ ≁ aᵢ) | faithful |
| L_N(2), Conj R | `LN2`, `ConjR`, `ln2_of_conjR : ConjR.{u} → LN2.{u}` | faithful; instances need not be connected |
| Prop 6.1 | `joint_of_card`, `joint_of_leaf` | conclusion only `LN2Good` (no Q(c₁)=Q(c₂)=P); `joint_of_leaf` assumes d(c₁)=1 only (MINOR M10) |
| Prop 6.2, Thm 6.3 | `joint_of_supp`, `joint_of_steer`, `steerK_of_steer` | faithful hypotheses; conclusion only `LN2Good` |
| Lemma 6.4 sufficiency | `joint_of_inv` (NA's subgraph form, via `steer_of_inv`) | an honest description. The T-join step (S = star(t) ∪ J, A = {t}) is not formalised, and the g ∼ h case is not covered directly (`hSX` forces g ∉ X), as the text says. |
| Conj 7.2, Prop 7.3 | `ConjAE`, `ln2_of_leaf_at_head` | `ConjAE` faithful; the proposition takes the global `ConjAE.{u}`, not AE for the one graph K (MINOR M10) |
| "adding a path, both directions of the correspondence" (l. 655) | `PathDecomp.add_path_full` | it gives one direction only (every new path is P or an old path) (MINOR M10) |

Docstrings (MINOR M10):
- `JointR.lean` says "Manuscript … Section 5"; it is Section 6.
- `LemmaR.lean` cites "Definition 6.2 / Proposition 6.3". That is `ln`'s numbering; here they are Def 3.3 and Prop 3.4.

## 3. Computations: every re-derived number

I used only my own code: `a42lib.py` (graph6, checker) and `a42solve.c` (exact solver). It branches on an uncovered edge and has no degree bound, so it differs from `lnsolve`'s vertex-start search. I also wrote a C coverage program and C instance enumerators. The project binaries were compiled with `gcc -O2` in `/tmp/claude-0/a42`.

### 3.1 Solvers

- **`a42solve` validation.**
  - Against a label brute force (`brute_tiny.py`: assign every edge a path label and accept if every class is a simple path), on 1,500 random tiny queries. These have graphs with even vertices, and R, J, A and S constraints (597 SAT). `a42solve`, `lnsolve3` and `lnsolve` all agree: 0 disagreements.
- **Three-way cross-validation** (`xval.py`). Query types: J+A+A; K₀ = F − E(joint P); K₀ + cⱼℓ with S ℓ aⱼ; A+A; AE; J+A+A+A.

  | orders | queries | disagreements | witnesses checked by my checker | note |
  |---|---|---|---|---|
  | 6, 8 | 40,000 | 0 | 113,865 | |
  | 6, 8 | 4,000 | 0 | — | |
  | 10 | 1,000 | 0 | 2,902 | 50 budget-limited |

- **`lnsolve3`'s degree bound is sound.**
  - `feasible()` runs only between paths. The remaining edges must be decomposed into exactly remtot/2 paths (each takes 2 unspent ends).
  - v is an end of rem(v) of them, using one edge at v each. A path with both ends at v is impossible, so rem(v) = 2 with one path left is infeasible anyway.
  - Each other path passes v at most once, using two edges.
  - So rdeg(v) ≤ rem(v) + 2(remtot/2 − rem(v)) in every completion.
  - The joint-pair-first branching only changes which vertex with an unspent end starts the next path. The failure memo is keyed on the full (edges, rem) state, and constraints are per path, so the search stays exhaustive.
  - The project's own validation (`val3b.py`) used only all-odd graphs. Mine adds graphs with even vertices and leaves, where the bound actually prunes.

### 3.2 `wcheck.c`

`wcheck_tamper.py` produced 2,714 cases, each a single targeted corruption: drop or duplicate a path; split a path; make it non-simple; vertex out of range; one-vertex path; rotation; changed A or J target in the query; wrong graph name; hand-made traps.
- `wcheck` rejected every invalid witness that my checker rejects.
- It accepts all reversals (valid; this matches the reported "12 accepted").

There are two robustness quirks, neither able to validate a false witness from the shipped pipeline (MINOR M12):
- an unknown query token (e.g. `X 0 5`) is silently ignored;
- `0-5x` is read as `0-5`.

I also read the code: `ecount == m`, no edge twice, ends equal req, A/S/J checks, and graph-name match. Pair alignment holds, because `lnsolve3` prints exactly one line per non-empty query.

### 3.3 Generator and instance counts

| claim | mine | |
|---|---|---|
| connected all-odd graphs 13 / 224 / 32,851 (orders 6, 8, 10) | Burnside count of all-odd graphs 16 / 243 / 33,120, inverse Euler transform 13 / 224 / 32,851 (`burnside_allodd.py`); `gen`'s lists pairwise non-isomorphic, connected, all-odd (`isocheck.py`) | ✓ |
| `gen` counts 1, 2, 4, 11, 34, 156, 1044, 12346, 274668 | reproduced | ✓ |
| instances 428 / 43,400 / 20,569,948 | `instclass.c` | ✓ |
| joined 374 / 40,538 / **20,151,960**; separated 54 / 2,862 / **417,988** (20,151,960 + 417,988 = 20,569,948) | ✓ | ✓ |

### 3.4 Conjecture J

**Orders 6 and 8, exhaustive** (`J68_own.out`): my own solver finds a witness at all 374 and all 40,538 joined instances, and every witness passes my checker.

**Order 10 (spot check, not a rerun).**

These are `J10_spotcheck.out`. `lnsolve3` solved the queries, and every witness was checked by my checker.

| sample | queries | result |
|---|---|---|
| uniform over joined instances (p = 10⁻³) | 20,271 | all SAT and valid |
| every joined instance of the 191 graphs with \|E\| ≥ 33 (uniform sampling under-weights them) | 25,476 | all SAT; also `wcheck` |
| two random joined instances of every order-10 graph | 65,698 | all SAT |
| my own solver on 1,500 of the uniform sample | 1,500 | 1,470 witnesses found, 30 budget-limited, 0 UNSAT |

I reviewed `jall.py`. The query `J c1 c2 A c1 a1 A c2 a2` is exactly Conjecture J's conclusion. UNDEC is rerun at 100 × B, and `non-SAT 0` with SAT(checked) = J-queries shows that every query has a checked witness.

**Disconnected F.** The instance definition (l. 74–76) allows disconnected F, while the data are for connected F. Conjecture J for a disconnected F of order ≤ 10 reduces, through the component containing c₁, c₂, to one of three cases. I checked each exhaustively at orders ≤ 8:
- J itself;
- joint ends without avoidance (`joint_ends_all224.out`: order 4: 12, order 6: 195, order 8: 6,272, all SAT);
- a one-avoidance form J c₁ c₂ A c₂ a₂ (`J_one_avoid.out`: 12 / 628 / 35,300, all SAT).

So the claim is in fact true for all instances of order ≤ 10, but the text should say how (MINOR M1).

### 3.5 Section 4 (order 8): all reproduced exactly

| claim (§4) | mine | |
|---|---|---|
| 257,584 single-edge records; anyexact 42,130; noz 40,964; 1,270 none | `sec4_single.out`; all nine (kind, exact) classes identical | ✓ |
| no-single-edge counts by \|E\| (all with \|E\| ≥ 21) | identical table | ✓ |
| d(cᵢ)=1, x ∉ {cⱼ,aⱼ}, x ≁ aⱼ: exact at every record | 5,192 / 5,192 | ✓ |
| 5,732,328 all-path records; per-(length, kind) counts | identical (`sec4_allpaths.out`) | ✓ |
| least working length 1: 40,964, 2: 2,132, 3: 258, 4: 38, 5: 8 | identical (exact, by increasing length) | ✓ |
| 88.5 % mean; 72 % single edges (b); 97.5 % length 6 | on an 800-instance sample: 88.8 %, 73.0 %, 97.7 % | ✓ (sample) |
| 252,266 joint paths; 231,882 tight | identical (`sec4_joint.out`) | ✓ |
| rules: 40,538 / 39,966 / 39,452 / 37,544 / 36,460 | identical | ✓ |
| tightness table 72,975 / 0, 0 / 10,595, 128,205 / 9,789, 30,702 | identical (all nine classes) | ✓ |
| six instances without case-(a) schedule are adjacent twins N(c₁)−c₂ = N(c₂)−c₁ = {0,1,2,3}; no first move for P = c₁c₂ | checked by decoding | ✓ |

The schedule columns (38,908; 40,532; 39,960; 37,107; 230,241) come from `ln`'s `routeR.search` (audited in A40), and I did not rerun them. They are consistent with my exact counts: 509 = 40,532 − 40,023 joined instances have a case-(a) schedule but no proved condition.

### 3.6 Section 6 coverage

`jcov.c` is independent of `cov.py`, `allcov.py` and `cov2.py`.
- **Order 8:** C1 12,176; C2 30,607; C3 37,371; union 40,023; residual 515.
- **Union with B (2,858) and G (798):** covered 41,047; residual 2,353.

All match. Note that `cov.py` certifies C3 with an actual trail, so its coverage is Theorem 6.3 (Lean) and does not need Lemma 6.4. `cov2.py`'s `tjoin_ok` implements Lemma 6.4 exactly: VH = (V − X) ∪ {g}, the N(t) ⊆ V(H) test, T_t, components of H − t, and the g ∼ h branch with the leaf shortcut.

### 3.7 Residual (Section 8)

`resid_cmp.out` compares my residual with the committed lists. The committed order-8 list uses `ln`'s graph labels, not `gen.c`'s (MINOR M12).

| order | residual sets | types (mine) |
|---|---|---|
| 6 | identical (32) | 0 joined, 30 leaf at head, 0 cut, 2 2-cut |
| 8 | identical (2,353) | 515 joined, 1,579 leaf, 45 cut, 214 2-cut; joined 13 ≤ \|E\| ≤ 24, 508 with \|E\| ≥ 16 |
| 10 sample | identical (74), with no path cap | 21 joined, 45 leaf, 1 cut, 7 2-cut |

### 3.8 Separated case and AE (Section 7)

Order-10 classification with the manuscript's precedence: B 37,170; G 58,283; leaf 292,643; cut 4,323; 2-cut 25,569. All match. Order 8: 342 / 682 / 1,579 / 45 / 214, so 1,579 of 1,624 ✓.

AE:

| set | count | check |
|---|---|---|
| derived AE queries (not B, not G-without-NA, leaf), orders 6 / 8 / 10 | 30 / 1,582 / 292,838 ✓ | all order-10 witnesses valid (`AE10_check.out`) |
| exhaustive AE, n = 5 … 8 | 8, 8, 354, 354 ✓ | all SAT with my solver (`ae_exh.out`) |
| exhaustive AE, n = 9 | 47,354 ✓ | `lnsolve3` witnesses all valid under my checker (`AE9_lnsolve3_check.out`). My own solver (budget 2·10⁶, 20-min cap per part) found and verified 46,921 witnesses; 2 hit the budget, 431 were not reached, none was UNSAT (`ae_exh.out`). |

(The n = 6 and n = 8 counts equal those at n = 5 and n = 7, since a graph of even order with exactly one even vertex has an isolated vertex; the claim "n ≤ 9" is still right.)

**Criterion R run (31,897).** My set (not B, not G-without-NA, not leaf) equals the certificate file's instance set. Every certificate is type `pre`, P is a path from cᵢ avoiding aᵢ ending outside {cⱼ, aⱼ}, and Lemma R(b) holds exactly for that P (`sep10.out`, `CR10_exact_check.out`). The length distribution is 27,877 / 2,791 / 1,208 / 14 / 7 ✓.

### 3.9 m = 3 (Section 9)

`m3check.py` used my solver and checker throughout:
- 84,064 instances; L_N(3) SAT at all.
- 83,956 with a joint choice; J3 at 83,872; 84 failures.
- The failure list is identical to `m3_J3_failures_order8.txt`. Their 148 queries are UNSAT for my solver too.
- The smallest failures have 9 edges (8 instances; `G??XU[` has 9 edges). 108 instances have no joint choice.
- My counts of 314,461 checked witnesses and 2,937 UNSAT equal the data line exactly.

Certificates (`m3cert.py`):
- All 1,692 certificates of `m3_R3_certificates.txt` (A 1,491, B 201) satisfy Def 9.1 and complete exactly to valid L_N(3) decompositions.
- The same holds for the new `m3_R3_all_order8.txt.gz` (commit d877c9f): 84,064 certificates (A 83,765, B 299 ✓), whose instance set is exactly my enumeration (`m3cert_all.out`).

The manuscript does not yet report this stronger result (MINOR M11).

### 3.10 Examples 8.1–8.3, by hand

- **8.1** `E@UW` = net {05, 14, 23, 34, 35, 45}, instance (0,1;2,5).
  - 4 ∼ 1, 5, so the pair set is not sparse.
  - B = {1,2,3,4} ∋ a₁, d_B(5) = 2 and 0 ∼ 5, so (G1)–(G3) fail. The other orientation has cᵢ ∈ B.
  - The decomposition {05, 234, 1453} is valid with Q(0) = 05 and Q(2) = 234. The AE witness checks.
  - Criterion R with P = 053 is form (b′): c₂ = 2 is a leaf of K₀ at 3, and 5 ∉ {3, 2, 4}. Vertex 3 is the only token, so no moves are needed. This is also the shipped certificate.
- **8.2** `E@]o` = {05, 14, 23, 24, 25, 34, 35}, instance (0,2;1,3).
  - F − {2,3} has components {0,5} and {1,4}; F − 2 and F − 3 are connected.
  - {053, 142, 4325} is valid. P = 0534 is form (b′) with no moves.
  - The swap (2 3) is an automorphism carrying (0,2;1,3) to (0,3;1,2). These two are the only non-leaf residual instances at order 6.
- **8.3** `G?`vfc` has 13 edges, and 6 and 7 have degree 5.
  - It is the only 13-edge joined residual graph; the four 14-edge ones are `G?Bvvg` and `G?o~fc`.
  - The joint decomposition {607, 04, 152673, 271635} is valid.
  - "Criterion R holds in case (b) with P = 6 0 and two moves" is true for (6,4;7,5), whose shipped certificate is `P=6-0 moves=2`. For (6,5;7,4) the shipped certificate is `P=6-1 moves=6`; the twin swap 6↔7 maps the first certificate to P = 7 0 (MINOR M5).

## 4. Required fixes (ERROR, GAP, OVERCLAIM)

1. **ERROR, abstract l. 45–46.** Replace "At order 8 the non-tight remainders F − E(P) are exactly those with a universal odd vertex or a cut vertex." by:
   > At order 8, a 2-connected remainder F − E(P) is tight exactly when it has no universal odd vertex (with a universal odd vertex it is never tight, by a degree count); every non-tight remainder is not 2-connected or has such a vertex.

   Optionally add the counts 72,975 / 10,595.
2. **OVERCLAIM, §10 l. 639–643.**
   - In item 3, replace "The 2-cut separations (R3)." by "The other separations (R3): a cut vertex outside Theorem 7.1 with cᵢ not a leaf (45 at order 8, 4,323 at order 10), or a 2-cut."
   - Replace the last sentence by:
     > A proof of J and AE, together with gluing lemmas for the remaining separations (a cut vertex outside Theorem 7.1, and a 2-cut), would prove L_N(2).

   Also check l. 101–104, which lists them correctly.
3. **OVERCLAIM, l. 53–54 and l. 552.**
   - l. 53–54: replace "reduces exactly to Conjecture AE" by "reduces to Conjecture AE (Proposition 7.3)".
   - l. 552: replace "(R2) … equivalent to AE for F − cᵢaⱼ" by:
     > (R2) a leaf at the other head (Proposition 7.3): AE for F − cᵢaⱼ implies the instance is good, and is equivalent to a good decomposition with Q(cᵢ) = cᵢaⱼ.

## 5. Recommended fixes (MINOR)

- **M1, connectivity of the data** (l. 41–44, 74–77, 96–98, 304–306, 586, 117).
  - The counts and checks are for connected F. Add "connected" to the order-10 claim, or note:
    > For disconnected F of order ≤ 10, J reduces to J, the joint-ends test and its one-avoidance form at orders ≤ 8, all of which hold (audit A42).
  - Likewise "L_N(3) holds at all 84,064 instances of order 8 (F connected)".
- **M2, abstract bullet "Proved joint cases (Lean)"** (l. 47–50): Lemma S is paper-only. Write "… stays put (Lean). We prove on paper that the last condition (Lemma S) …". Also, at l. 51–53, "gluing two applications of L₁" also uses NA's corollary. "and cᵢ ∼ aⱼ fails NA's boundary condition" could read "and cᵢ ∼ aⱼ with every vertex of cᵢ's component in F − aⱼ adjacent to aⱼ".
- **M3, NA citations** (l. 466, 481): "NA's corollary [NA, Cor. 1.3] (`avoid_of_reach`)" at l. 466, and "By NA's boundary theorem [NA, Thm 1.4]" at l. 481.
- **M4, Theorem 7.1.** In (G3), drop "cᵢ ≁ v, or" (it is implied), or keep it with "(in particular if cᵢ ≁ v)". At l. 469 write "Under (G3), used when (G1) fails (so aᵢ ∈ B), …"; or order the bullets at l. 463–467 so that (G3) is used only when aᵢ ∈ B.
- **M5, Example 8.3** (l. 578): "Criterion R holds in case (b): with P = 6 0 and two moves for (6,4;7,5), and with P = 7 0 for (6,5;7,4) by the automorphism 6 ↔ 7."
- **M6, l. 287–290.** Note that "O1 ⇒ not tight" is a degree count: with two even vertices, (n₀ − 2)/2 paths give d(u) ≤ n₀ − 3. So "a universal vertex of F must lie on a working joint P" is a theorem. Also, l. 300–301 says "Lemma 3.1(a)", but Lemma 3.1 has no part (a); write "Lemma 3.1 with P ending at c_j".
- **M7, Theorem 6.3 proof** (l. 358): "The target is odd: every vertex other than g_t and h has odd degree or is isolated, and the target is neither (it is in no X ∋ h, and differs from g_t)."
- **M8, Lemma 6.4.**
  - Statement: "whose even vertices are exactly g and h (both even), …".
  - Necessity: add "A legal M-move of the g-token goes to an odd vertex outside N[h], since h keeps all its edges; so the moves form a trail avoiding X."
  - Sufficiency: add "every other vertex has even degree d_J" to the parity list.
  - l. 403–406: "on every joint path with both ends of positive degree in K₀ … (62,530 cases)".
  - Optionally cite this audit's 694,256-case check.
- **M9, Cor 6.5:** add "with both ends of P of positive degree in K₀ (otherwise Proposition 6.1 applies)".
- **M10, Lean wording.**
  - Table l. 655: "adding a path (every path of the result is P or an old path)".
  - Props 6.1–6.3: note that the Lean conclusions are `LN2Good`, with Q(c₁) = Q(c₂) = P only in the construction, and that `joint_of_leaf` treats d(c₁) = 1 (d(c₂) = 1 by symmetry).
  - Prop 7.3: the Lean form assumes the full `ConjAE`.
  - Docstrings: `JointR.lean` says "Section 5", which should be "Section 6". `LemmaR.lean` should cite conj-r Def 3.3 and Prop 3.4, or say "(`ln` numbering)".
- **M11, m = 3** (abstract l. 61–62, §9 l. 619–628): `d877c9f` now ships Criterion R3 at all 84,064 instances (A 83,765, B 299; checked here). The text can say "certifies all 84,064 instances" instead of "every hard instance and a sample of 1,500".
- **M12, data, scripts and README.**
  - `residual_order8.txt` uses `ln`'s (geng) graph labels. The README recipe (`gen 8 oddc` + `gen_ln2.py` + `cov2.py`) therefore reproduces the same 2,353 instances under different labels. Say so, or regenerate.
  - `single_edge_order8.txt` cites `an2.py`, which is not shipped.
  - `g3p.py` hard-codes `/home/user/Manuscripts/...`.
  - `coverage.txt` says "Counts are per condition", but `cov2.py` evaluates C2 and C3 only when C1 and B fail and stops at the first success. The §6 per-condition counts come from `cov.py`.
  - `pall.py` and `pscan.py` record UNDEC as 'U', the same as UNSAT. This has no effect, since my exact recount matches.
  - `wcheck.c` should reject unknown query tokens.
  - `joint_ends_order8.txt` (6,216 = 222 graphs) does not support "every pair of every graph" (l. 323–324). All 224 graphs (6,272 pairs) hold (`joint_ends_all224.out`). Write "of every graph (6,272 pairs)" or "of the 222 graphs with an instance".
- **M13, §2 schedule summary** (l. 135–138): (S) also requires that neither neighbour is a tail leaf and {a,b} ≠ {x,s}. Add "with the side conditions of [MT, Def. 2.2]".
- **M14, other wording.**
  - Abstract l. 58: "smallest examples (orders 6 and 8)"; (R1)'s smallest is order 8.
  - l. 242: "the mean fraction of paths (not ending at aⱼ) that work exactly".
  - l. 483: "of the 1,624 such instances not covered by Corollary B".
  - l. 516–517: "Corollary B covers 37,170; Theorem 7.1 covers 58,283 of the rest".
