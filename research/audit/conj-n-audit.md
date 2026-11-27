# Audit of conj-n (manuscript, `ConjN.lean`, `ConjNFar.lean`, scripts)

Date: 2026-11-27. Referee stance: adversarial. Grades: **SOUND**, **GAP** (fixable), **ERROR** (false as stated), **OVERCLAIM** (true content, overstated), **MINOR**.

**Version.** Branch `claude/conj-n`. The author changed the files while the audit ran:
- I started on an uncommitted draft (tex of 716 lines, with no `ConjNFar.lean`).
- Commit **82a43a7** added `ConjNFar.lean`, imported it from `GallaiLean.lean`, and edited the abstract, §1 Status and the §7 table of the tex, the README and `lean/README.md`.
- Commit **27cf961** added only `scripts/nadjstat.cpp`, which nothing references.
- **Everything below refers to HEAD 27cf961.** At the end of the audit, the working tree equals HEAD for every audited file.

| file | md5 |
|---|---|
| `manuscripts/conj-n/conj-n.tex` (727 lines) | `da9fbf63dc18284a0a10203c612e6d42` |
| `manuscripts/conj-n/conj-n.pdf` | `0a99c68c03c74aa49350b3c43065bb6d` |
| `manuscripts/conj-n/README.md` | `ee406de1ea80313165ecad744d646b80` |
| `lean/GallaiLean/ConjN.lean` | `52e96634418b6817a4cf646252552ccf` |
| `lean/GallaiLean/ConjNFar.lean` | `2afb5176a2beb44989ef354fc3771ccb` |
| `lean/GallaiLean.lean` | `e33b163f0672e57f1506d23772d0d6b5` |
| `lean/README.md` | `00a542cf89eb5081d46c0cd243f01eed` |
| `scripts/ext.h` | `9ccc65fd7ec288cbfc27129ee5015ff7` |
| `scripts/orcb.h` | `0632b63834bb980eb0075a7c967b26bf` |
| `scripts/closure2.cpp` | `ffde512b055f71810ba820165aa50547` |
| `scripts/ncert.cpp` / `xcert.cpp` | `0145c8649b804bbb2a51b0a03fe277ca` / `583726dd42bfe74de3f1d29da7c22719` |
| `scripts/trn.cpp` / `tradj.cpp` / `nadj.cpp` | `a1e81f8e4971463687319bb22bc4da9b` / `de0d1c3b3f54dfc9c87a932be54c854f` / `57daeb25a45db25d74a3df485a78cfca` |
| `scripts/nplus.cpp` / `tx.cpp` | `945e59459c19c49ef6ca3d90b6c4c981` / `4a40a29315b2974f3200dafdfb7c9889` |
| `scripts/gplus.cpp` / `qb.cpp` | `90027a3fa33abd322da53ee14f044eab` / `df33948fab69e4f31b97fc5b0e420b7b` |
| `scripts/xcheckb.py` / `n1stuck.py` / `tables.sh` | `fd140f7f544a176c261138029da3c472` / `7a3527360471b77cf14025ba469af0a2` / `2ff9bc27516c20b2ed755f283dcbb190` |
| `scripts/nadjstat.cpp` (27cf961) | `62a9732dc5a3d998fa2d2268834688a2` |
| `data/tables.txt` / `conjecture_tests.txt` | `e2ef9209147ff66c218ad88bda128155` / `99e1e1392a1a292de468529f9e633364` |
| `data/ncert9_uncertified.txt` / `xcert9_uncertified.txt` | `7cdd224644badcda1de3a915c8e6b7d8` / `fcc7d2c8d61d95d2dcca57b092fb6999` |
| `l1-induction/scripts/lind.h` / `moves.h` | `c9eb724194a2d80e943d39d1dd368cd2` / `0beba7992062aaeb5e77baf1baec0a77` (unchanged since A25/A29) |

- **PDF.** It is in sync with the tex. I recompiled the tex three times in a scratch copy, and the `pdftotext` diff against the committed PDF is empty. The log has no warnings and no undefined references.
- **Numbering in the compiled PDF.** Fan's lemma with end paths is **Lemma 2.2**, and the transfer calculus is **Theorem 2.3**. The brief's "Lemma 2.1" is the dl-one numbering. Remark 3.4 follows Theorem 3.3; Conjectures 4.1 (TRN) and 4.2 (NA); Lemma 4.3 (split); Lemma 4.4 (degree two); Theorem 4.5; Corollary 4.6; Proposition 4.7; Remark 4.8 (blocked L1*).
- "l." below means a line of `conj-n.tex` at 27cf961.

**Auditor files.** `research/audit/conj-n-scripts/` contains:
- `axioms.lean`: `#print axioms` and `#print` of the definitions;
- `movecheck.cpp`: for every instance (G, c, A, B) and **every move** of `ext.h`, it checks that a good child implies a good parent, and that every base case is good, using the exact oracle;
- `make_variants.sh`: builds auditor variants of `ext.h` in a scratch directory:
  - three deliberately permissive moves, to check that `movecheck` has power;
  - an uncapped calculus: leaf paths up to length 8 and all g–c routes for (h);
- `alltight.py`: counts all-tight instances of N against the stuck list;
- `stuckfeat.py`: features of STUCK and FALSE lines;
- `tables_aud.sh`: `tables.sh` with paths for a scratch directory;
- `run_audit.sh`: every run below.

The authors' code was compiled **unmodified** into a scratch directory (`g++ -O2 -I ../../l1-induction/scripts`). The repository was not modified outside `research/audit/`.

---

## 0. Headline

1. **Every proof is correct.** I found no mathematical error in Lemma 3.1, Lemma 3.2, Theorem 3.3 (x), (b_B), (C), (c_B) and the B-carrying of the other moves, Lemma 4.3, Theorem 4.5, Corollary 4.6 or Proposition 4.7.
   - Theorem 4.5 is the headline. Its step (4), the parity argument, is right, and so is the use of the witness in steps (2) and (3), including the witness being the old g.
   - The gaps:
     - Lemma 4.4's converse and its no-common-neighbour clause omit the step that carries goodness back from the subdivided graph (F4).
     - (c_B) relies on the forced-chain clause outside the setting where its cited sources state it (F12).
     - A base case is stated without its non-twin exception (F7).
2. **The Lean is faithful, builds, and uses standard axioms only.**
   - `lake build` of the full library: "Build completed successfully (**18416 jobs**)".
   - Neither file contains `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `unsafe` or `opaque`.
   - All 19 theorems of the two files depend on at most `propext`, `Classical.choice` and `Quot.sound`.
   - The definitions encode Conjecture 1.1, Conjecture 4.1, the degree-two case, Conjecture 4.2, far-end goodness, Lemma 3.2 (case of ends outside N(u)) and move (x) exactly.
   - The mismatch: Lemma 4.4 and the abstract's "NA is exactly the case N(g) = {x, y}" are listed as formalised, but only NA ⇒ degree-two case is in Lean (F5).
3. **Every number I re-ran reproduces exactly.** That is every number of §5.1, §5.2, the §5.3 table, §6 and the README, including the order-10 NA run and both order-11 TRN slices. The far-end oracle matches full enumeration on all 399,762 queries.
4. **The moves of `ext.h` are implemented with the proved conditions.**
   - I tested every move against the exact oracle: all orders 3–8 with every A and B, order 7 including disconnected graphs, and 1,152,000 + 2,239,680 instances from order-9 samples. There are **0 violations and 0 false base cases**.
   - The check has power: dropping one far-end condition from (b), (c) or (x) gives 10,243, 6,028 and 22,484 violations at order 7.
   - But the **certificate and stuck counts depend on two implementation caps**: leaf paths of length ≤ 2, and at most 8 *shortest* routes for (h). The paper's moves have neither cap. Without the caps, 5 instances stay uncertified instead of 7, and several stuck counts drop, for example 37,652 → 35,338 (F2).
5. **Framing.**
   - "N is stuck **exactly** at the all-tight configurations (37,652 of 263,264)" is false as an equality: there are **52,070** all-tight instances; the 37,652 stuck ones are a proper subset (F1).
   - "Replaces ST by NA" omits the second transfer conjecture that is needed (F3).
   - "N ∪ NA has no stuck instance" omits that its NA members are stuck at even orders (F6).

## 1. Verdict per claim

| Claim | Verdict | Notes |
|---|---|---|
| Conj 1.1 (N), definitions of instance and extended instance | SOUND | `ConjNOn`: "w ∉ evenSet" = "w ≠ g". |
| Lemma 2.2 (Fan with end paths) | SOUND as cited | The tracking part is CLT Thm 5.1 (`fan_single_track`). Forced-chain clause: F12. |
| Theorem 2.3 (calculus of L1I) | SOUND as cited | c ∉ A is in the definition of an instance, so A25-F1 does not apply. (a) adds g ∉ A, which is harmless. |
| Base cases, §2 | SOUND as implemented; MINOR as stated | The leaf case lacks the twin exception, "packed" is undefined, and the avoid_deg_two hypotheses are not stated (F7). The B ≠ ∅ bases are correct. |
| Lemma 3.1 (leaf paths) | SOUND | |
| Lemma 3.2 (protected Fan) | SOUND | Lean: case with ends outside N_K(u). |
| Thm 3.3 (x) | SOUND | Lean `avoidFar_target`. |
| Thm 3.3 (b_B) | SOUND | Tracking statement only. |
| Thm 3.3 (C) | SOUND | Uses the degree-one case of Lemma 3.2. |
| Thm 3.3 (c_B) | SOUND, with a GAP in the citation | F12. |
| "the other moves carry B" | SOUND | Checked move by move (§2.3), and by `movecheck` with B ≠ ∅. |
| Remark 3.4 | SOUND | |
| Conj 4.1, Conj 4.2 | statements SOUND | TRN is stronger than the proof needs (F9). |
| Lemma 4.3 | SOUND | Lean `avoid_of_splitOff`. |
| Lemma 4.4, forward | SOUND | Lean. |
| Lemma 4.4, converse and no-common-neighbour clause | GAP (minor) | F4. Not formalised (F5). |
| Theorem 4.5 | SOUND | Lean `conjN_of_tight_degTwo`. |
| Corollary 4.6 | SOUND | Lean. Hypothesis stronger than needed (F9). |
| Prop 4.7 | SOUND (paper) | |
| Remark 4.8 | OVERCLAIM | F3. |
| §5.1 certificates (115, 7, the shape of the 7) | Data SOUND | The 7 depends on the caps (F2). "So no class closes under the old calculus" is robust, since all routes still give 115. |
| §5.2 table and bullets | SOUND | All rows reproduced. |
| §5.3 closure table | Data SOUND for the implemented calculus | Uncapped counts differ (F2). |
| §6.1 | SOUND | "Exactly … with no other move" is correct but tautological; the abstract/README version is F1. |
| §6.2 | SOUND except "the smallest … EF~w" | F11. |
| §6.3 | SOUND | 72/54/58, 8 subcubic on a triangle, DEk false instance by hand. |
| §7 table | SOUND, except Lemma 4.4 | F5; numbering F8. |
| §8 item 4 | MINOR | F13. |
| Abstract and README | ERROR in one claim (F1); OVERCLAIM (F3, F5, F6) | |

## 2. Proofs (details)

### 2.1 Lemmas 3.1, 3.2

**Lemma 3.1.**
- Interior vertices of P lose two edges. An even g of degree 2 becomes isolated; an odd c inside P keeps odd degree ≥ 1.
- The ends of P become isolated, with b = 0. Re-adding P gives them b = 1.
- Q_c is untouched, since c is not an end of P.
- **Correct.** It is also valid for any length; `movecheck -L 8` finds 0 violations among 102,489 good children at order 7.

**Lemma 3.2.**
- Write K° = K − E(P) and D° = D ∖ {P}.
- b(t) is unchanged, since t is not an end of P.
- Z_{D°}(u) ⊆ Z_D(u): an end of P that is in N_{K°}(u) would be in N_K(u), so it would have degree 1, so it would be isolated in K°, which is impossible.
- tu ∉ E(P), so adding P back gives a decomposition of K + tu with b = b_D − 1_t + 1_u.
- The hypothesis e ≠ u is not needed. It is harmless.
- **Correct.** Lemma 3.2 does not need a Lovász decomposition, so it applies to H in (C), where u and c may both be even.

### 2.2 Theorem 3.3
- **(x).**
  - In G′ = G − gu, g is odd with b(g) = 1.
  - Every neighbour of u in G′ is a vertex ≠ g whose degree is unchanged, so it is odd with an end, and Z(u) = ∅.
  - The ends of Q′_c: c ∉ {g, u} ∪ N_{G′}(u), because u ∉ N[c] and c ≠ g by parity. q ∉ N_G(u) ⊇ {g} ∪ N_{G′}(u), and q ≠ u because u has even degree in G′ and so no end.
  - The degenerate case d(u) = 1 also works: u is isolated in G′, Z(u) = ∅, and the chain appends gu.
  - u ∈ A is allowed, because Q_c = Q′_c and Q′_c avoids A. g ∈ A and c ∼ g are also allowed.
- **(b_B).**
  - By tracking, the new Q_c comes from Q′_c, because c ∉ {g, u} ∪ N_{G′}(u). So V(Q_c) ⊆ V(Q′_c) ∪ {u}, and u ∉ A.
  - Far end f: either f = q ∉ B, or f ∈ {g, u} ∪ N_{G′}(u) ⊆ N_G[u], which misses B because u ∉ B and N(u) ∩ B = ∅.
- **(C).**
  - d(u) ≥ 3, because u ∼ g, c and u is odd. So d_K(u) ≥ 1 is odd, and K's only possible even vertex is c.
  - In H = K + uℓ, u is even with no end. N_H(u) = N_K(u) ∪ {ℓ}, all with b = 1, and c ∉ N_H(u). So Z(u) = ∅ < b(g) = 1.
  - The ends of R = ℓuR₀ satisfy Lemma 3.2: ℓ has degree 1, and p ∉ N_G(u) ⊇ {g, c} ∪ N_K(u), with p ≠ u.
  - The merge is legal, because R avoids c. Then b(c) = 0 + 1 and b(u) = 1.
  - Q_c = cuR₀ avoids A ∪ {c}, and its far end is p ∉ B. **Correct.**
- **(c_B).**
  - ℓ is never a chain vertex, since it precedes u only when R is read from ℓ.
  - R contains u, so it is never the appended path.
  - If p = x_i, which includes p = g = x₀, R is re-routed once. It keeps V(R), and its new end x_{i+1} is the neighbour of u on R₀, which lies in N_K(u) ⊆ N_G(u).
  - The degenerate x_{i+1} = x_i cannot occur: x_i u would lie on two paths.
  - Far end ∈ {p} ∪ N_G(u), which misses B. **u ∉ B is not needed** (and `ext.h` does not require it), but only because of the forced-chain clause (F12).
- **The other moves with B.**
  - (a): Q_c = c g Q′_g, with the same far end.
  - (d): the leaf merge keeps the far end.
  - (e): subdivision, and with g ∈ A the child avoids w, so Q′_c does not use uv.
  - (f): the swap keeps the ends of Q_c.
  - (g): Q_c = Q′_c.
  - (h): Q_c = R ∪ Q′_g, with the far end of Q′_g.
  - (i): a path from c avoiding ∂C stays in C, so its far end lies in C, and "∉ B ∩ C" gives "∉ B".
  - Leaf path: Q_c is unchanged.
  - **All correct.** The preamble "with even vertex g" conflicts with (d), which needs none (F7).

### 2.3 Section 4
- **Lemma 4.3.**
  - g is isolated in H, so it lies on no path. Subdividing ab by g gives a path, since g ∉ R. b(g) = 0, and Q_c gains at most g ∉ A.
  - **Correct.** Lean matches; it has hg : g ∈ evenSet, which is automatic.
- **Lemma 4.4, forward.**
  - H has no even vertex. A witness w ≠ g has w ∈ N_H(y), because yw ≠ gy.
  - w ∉ N_H(x) = N_G(x) ∖ {g} ∪ {y}, because w ≠ y.
  - NA, then Lemma 4.3 with A = {x} ∌ g. **Correct.** Converse and last clause: F4.
- **Theorem 4.5.**
  - (1) L1 needs only x ≠ y, x ≁ y and y odd. Correct.
  - (2) In G − gu: x, y ≠ g, u, so their degrees are unchanged. evenSet ⊆ {u}. w₀ ≠ u, because u ∉ N(y). yw₀ ≠ gu, because y ∉ {g, u}. `avoid_free_target` needs only u ∉ {x, y}, u ≁ y and y ≠ g: u ∼ x is allowed and y ∼ g is allowed. Correct.
  - (3) u ∈ N(g) ∩ N(y), so d(u) ≥ 3 and u is even in the child. The child witness w ≠ u may be g, which is odd there. TRN's hypotheses hold. Correct.
  - (4) The shape of N(g):
    - With (2) and (3) failing, T ⊆ {w₀}.
    - If w₀ ∈ N(g), then w₀ ∈ T, and (3) at u = w₀ with w = g gives y ∼ g ⇒ x ∼ g.
    - |N(g)| is even and positive and N(g) ⊆ {x, y, w₀}. The candidates are {x, y} (when w₀ ∉ N(g)) and {x, w₀}; {w₀, y} is excluded by the implication, and {w₀} and {x, y, w₀} by parity.
    - In the case {x, w₀}: x ≁ w₀, and H has no even vertex. y ≁ x in H, because the new edge xw₀ has w₀ ≠ y. Then L1 and Lemma 4.3.
    - **Correct**, and it matches the Lean case split line for line (`conjN_strong`, l. 252–375).
  - Hidden assumptions checked:
    - d(u) = 1: the child has u isolated, possibly with no even vertex at all, and is handled by (1).
    - x ∼ g or not, y ∼ g or not: no case uses either beyond (4).
    - The witness being g in a child: handled in (3).
    - Isolated vertices: evenSet requires positive degree.
    - g outside y's component: then (2) always applies.
- **Corollary 4.6.** TR with A = {x}: y ∉ A, u ∉ A, A ∩ N(y) = ∅. Correct.
- **Proposition 4.7.** Bullet 1 is the contrapositive of step (2) with minimality in Σd. Bullet 2: the case N(g) = {x, u} with u ∈ W is closed by the split plus L1 without TRN. Correct.

## 3. Lean

### 3.1 Build and axioms
- `lake build` (my run, after ConjNFar was added): **18416 jobs, green**. `/tmp/fullbuild.log` (18,414 jobs, `EXIT 0`) predates ConjNFar.
- `#print axioms` (`conj-n-scripts/axioms.lean`, run with `lake env lean`) gives `[propext, Classical.choice, Quot.sound]` for:
  - `conjN_of_tight_degTwo`, `conjN_of_tight_neighbourAvoid`, `conjNDegTwo_of_neighbourAvoid`;
  - `conjN_of_TR_neighbourAvoid`, `avoid_of_splitOff`, `tightTransferNOn_of`, `conjN_strong`;
  - `evenSet_delEdge_sub`, `evenSet_delEdge_card`, `avoidDecomp_singleton_iff`;
  - `fan_single_protected_path`, `avoidFar_target`, `PathDecomp.erase_path`, `PathDecomp.add_path`;
  - `exists_decomp_of_edgesM_both`, `PathDecomp.eq_of_ends_one`, `delEdgeList_edgeSet`.
- `delEdge_adj_of_ne` and `PathDecomp.exists_end_of_ends_pos` give `[propext, Quot.sound]`.
- The library results used (`lovasz_avoid_nonadj`, `avoid_free_target`, `splitOff_facts`, `fan_single`) are covered transitively.

### 3.2 Definitions against the paper (`#print` output checked)

| Paper | Lean | Match |
|---|---|---|
| Conj 1.1 | `ConjNOn V`: card evenSet ≤ 1; x, y odd; x ≠ y; ¬xy; ∃ w, y ∼ w, w ∉ evenSet, ¬xw ⇒ `AvoidDecomp G y {x}` | exact |
| Conj 4.1 (TRN) | `TightTransferNOn V`: g ∈ evenSet, x, y odd, x ≠ y, ¬xy, g ∼ u, y ∼ u, u ≠ x, child good ⇒ G good | exact. No witness is required, which is stronger than Thm 4.5 uses (F9). |
| degree-two case | `ConjNDegTwoOn V`: N(g) = {x, y}, the rest as N, with witness w ≠ g | exact |
| Conj 4.2 (NA) | `NeighbourAvoidOn V`: card evenSet = 0, y odd, x ∼ y, ∃ w ∼ y, w ≠ x, ¬xw | exact (x odd is automatic) |
| "TR for tails adjacent to g" | `TightTransferAdj`: TR with `G.Adj g c`, **all A** with c, x ∉ A and A ∩ N(c) = ∅ | Matches TR* restricted to c ∼ g. Stronger than needed (A = {x}); data only for \|A\| ≤ 2 at order 9 (F9). |
| far-end goodness | `AvoidFarDecomp G c A B`: Lovász D, and every path ending at c avoids A, with its other end ∉ B | exact |
| Lemma 3.2 (ends ∉ {t, u} ∪ N_K(u)) | `fan_single_protected_path`: G′ = G − ut, Fan's inequality on D′, P ∈ D′ with no end in {t, u} ∪ N_{G′}(u) ⇒ D of G with ends u + 1, t − 1, others equal, and Q ∈ D with the src, tgt and support of P | exact. "P ∈ D⁺" is expressed by equal ends and support, which determine the walk. |
| Thm 3.3 (x) | `avoidFar_target`: card ≤ 1, g ∈ evenSet, g ∼ u, c ≠ u, ¬cu, c odd, any A, B, child `AvoidFarDecomp (G − gu) c A (B ∪ N_G(u))` ⇒ `AvoidFarDecomp G c A B` | exact (u ∈ A or B is allowed; more general than the paper). |
| Lemma 4.4 | `conjNDegTwo_of_neighbourAvoid`: NA ⇒ degree-two case | **forward direction only** (F5) |
| Thm 4.5, Cor 4.6 | `conjN_of_tight_degTwo`, `conjN_of_tight_neighbourAvoid`, `tightTransferNOn_of`, `conjN_of_TR_neighbourAvoid` | exact |

- **Vacuity.** No hypothesis is vacuous.
  - The hypotheses of the reduction are the conjectures themselves. Each is satisfiable and supported by the data.
  - The per-type form (`… V → ConjNOn V`) is the strong form, since the induction stays on V.
  - Nothing is accidentally weaker: the conclusion is exactly `AvoidDecomp G y {x}` for every instance of N.

## 4. Data

### 4.1 Reproduced exactly (authors' code, unmodified, built in scratch)

| Claim | Run | Result |
|---|---|---|
| §5.1 old calculus | `ncert` on one_even 5, 7, 9 | 12/12, 1,161/1,161, 263,149 certified, **115** uncertified (all good). The list is identical to `data/ncert9_uncertified.txt`. |
| §5.1 new calculus | `xcert < unc9.g6` | 2,262 instances on those graphs, **7** uncertified, identical to `data/xcert9_uncertified.txt`. |
| §5.1 shape of the 7 | `show.py` | all have d(g) = 2, N(g) = {u, x}, u ∼ x, u ∈ N(y), y ∉ N(g), d(y) = 5. Example HsOceO}. |
| attribution to the new moves | `xcert` with exclusions | without x, C, k: 115; without x and C: 106; without x: 106; without C: 20. So move (x) does the work, and the extra base cases (sparse, avoid_leaf, avoid_deg_two) add nothing. |
| TRN | `trn` | 5: 4/10; 7: 787/1,060; 9: **236,891 / 254,032**; geng 11 17/2000: 178,485/187,180; 517/2000: 207,816/258,304 (sum **831,785**); 0 violations |
| TR* | `tradj` | 10; 2,036 (order 7, all A); **565,744** (order 9, \|A\| ≤ 2); 0 violations |
| NA | `allodd \| nadj` | 3, 129, 4,970, **1,305,621** (32,851 all-odd graphs of order 10), all good |
| N⁺, (x)-child, far form of "avoids g" | `nplus`, `tx`, `gplus` | 262,847 / 263,264 (x ∼ g: 134,911/134,911; failures 417 of 128,353 with x ≁ g); TX 134,869 / 134,911, core 18,315/18,315, sanity 0; GPLUS 46,553 / 46,638, plain 46,638 |
| §5.3 table | `tables.sh` + subcubic lines | **every STUCK, FALSE, base and inclass number is identical** to `data/tables.txt`. The move breakdowns are identical too, given geng labelling (F10). |
| N1 ∪ NA under T* | `closure2 N1NA -T2 -b 0`, order 9 | 0 stuck (base 47,222, moved 216,042, of which `move_t` = 112,527) |
| N1 under U, orders 5/7/9 | `closure2 N1 -b 0` + `n1stuck.py` | 4 / 214 / 37,652. Every stuck instance has nontight = 0. |
| §6.1 with TR / TR* | `-T`, `-T2` + `n1stuck.py` | 154, all y ∼ g; 14 and 1,521, all x ∼ g, y ∼ g, d(g) = 2 |
| §6.2 C1 at order 7 under T* | `-g` + `stuckfeat.py` | 164, every one with a good child; g ∈ A in **89**; every witness ∼ g in **102** |
| §6.3 N2 under T* | same | 72, all with a good child; **54** with g ∈ A; **58** with every witness ∼ g |
| §6.3 subcubic | `geng -D3` | 2/36, 8/812, 182/22,592. All 8 at order 7 have d(g) = 2 and g on a triangle. |
| far-end false instances | `closure2 N2B -s` | 20/202 stuck, 22 false at order 5, in DEk (12), DTw (8) and D]w (2); the fewest edges is DEk. (DEk, c = 1, A = {2}, B = {4}) is FALSE, which I also checked by hand. |
| far-end oracle validation | `xcheckb.py` with absolute paths | orders 4–6 (139 graphs) + one_even_7 (130): **399,762 queries, 0 mismatches** |

### 4.2 Independent checks (auditor)
- **Move soundness** (`movecheck`; the oracle is validated above):
  - all connected graphs of orders 3–8, every c, A and B: e.g. order 7: 379,080 instances, order 8: 3,919,104;
  - all graphs of order 7, disconnected included: 464,784;
  - order-9 samples: 600 graphs with \|A\| ≤ 2, \|B\| ≤ 1 (1,152,000 instances); 120 graphs with \|A\|, \|B\| ≤ 3 (2,239,680 instances);
  - **0 false base cases, and 0 violations for every move a, b, c, C, d, e, f, g, h, i, k, x.**
  - For example, at order 9 (\|A\|, \|B\| ≤ 3) there are 2,629,132 good (x)-children, 1,584,541 good (C)-children and 718,167 good (c)-children, all with good parents. With `-T2`, 5,922 good (t)-children at order 7 have 0 violations.
- **Power.**
  - (b) without its B conditions: 10,243 violations at order 7.
  - (c) without N(u) ∩ B = ∅: 6,028.
  - (x) with B ∪ N(u) − g: 22,484.
- **Code against proofs (read).** Every move in `ext.h` has exactly the hypotheses of Thm 2.3 / Thm 3.3:
  - (b): u ∉ A ∪ B ∪ N[c] and N(u) ∩ B = ∅;
  - (x): only u ∈ N(g) ∖ N[c];
  - (c): u ∉ A and N(u) ∩ B = ∅;
  - (C): u ∉ A;
  - (t): B = ∅, A ∩ N[c] = ∅, u ∉ A, and c ≁ g unless TR*.
  - `xcompact` restricts B to odd vertices outside A + c, which is valid because a far end is odd, avoids A and is ≠ c.
  - For B ≠ ∅ only the two stated bases fire (`if (B & C) return false`).
  - The B = ∅ bases match the Lean statements:
    - `separation_set` (Packed A + c);
    - `lovasz_avoid_set`;
    - `csys_good_of_sparse` (hone, hloc);
    - `avoid_leaf`, whose `UnivTwins` is component-relative and equals the code's `tw` test;
    - `avoid_deg_two` with a := c, b := the vertex of A.
  - Certificates memoise "in progress" as false, so any "certified" has a finite derivation, and the counts are sound.
- **Robustness to the caps** (`make_variants.sh`, F2).
  - `ncert` with all routes: still 115.
  - `xcert` with leaf paths ≤ 8 and all routes: **5**. HsOeUTf and Hs`@Egv are certified by a leaf path of length 7–8. Leaf ≤ 3–6 gives 6.

## 5. Findings

**F1 (ERROR, wording/data; abstract l.79–81; README "Unconditionally, N is stuck exactly at the all-tight configurations: 37,652 / 263,264").**
- **Claim.** "Under the unconditional calculus, N is stuck exactly at all-tight configurations … (37,652 of the 263,264 at order 9)."
- **What the data show** (`alltight.py`):
  - Order 9 has **52,070** all-tight instances of N. 37,652 are stuck, and **14,418 all-tight instances are not stuck**: they are base cases or move by (e), (g), (k), ….
  - Orders 5 and 7: 10 and 403 all-tight instances, of which 4 and 214 are stuck.
  - Stuck ⊆ all-tight holds with 0 exceptions.
- **§6.1** ("exactly the all-tight instances with no other move") is correct but tautological.
- **Fix.** "N is stuck only at all-tight configurations: every stuck instance is all-tight (37,652 of the 52,070 all-tight instances at order 9; 4/10 at order 5, 214/403 at order 7)."

**F2 (GAP, data qualification; §5 "Moves" l.~486, §5.1, the §5.3 table, §6, abstract, README).**
- **The caps.** All certificate and stuck counts are for a capped implementation:
  - leaf paths of length ≤ 2 (§5 says "paths of length two");
  - (h) restricted to at most 8 shortest g–c routes in G − A, which is not stated anywhere in conj-n.
- **Neither cap is in the proved calculus.** Lemma 3.1 has no length bound, and Theorem 2.3(h) allows any route.
- **Uncapped counts** (leaf paths ≤ 8, all routes), each as capped → uncapped:

  | quantity | capped | uncapped |
  |---|---|---|
  | uncertified, order 9 | 7 | 5 |
  | N₁ / U, order 7 | 214 | 197 |
  | N₁ / U, order 9 | 37,652 | 35,338 |
  | N₁ / T, order 7 | 154 | 144 |
  | N₁ / T*, order 9 | 1,521 | 1,396 |
  | N₂ / U, order 7 | 249 | 228 |
  | N₂ / T*, order 7 | 72 | 71 |
  | C₁ / T*, order 7 | 164 | 160 |
  | NA, order 8 | 2,522 | 2,451 |
  | N₂^B, order 5 | 20 | 18 |
  | N₂^B, order 7 | 4,856 | 4,572 |

  The leaf-path cap alone produces every one of these changes.
- **What does not change.** The 115, NA at order 6 (22), L₁ (26), subcubic order 7 (8) and every FALSE count stay the same. So does every qualitative conclusion: no class closes, stuck ⊆ all-tight, T* stuck ⇒ N(g) = {x, y}, and the 5 remaining have the triangle shape.
- **Fix.** State both caps in §5 and next to every quoted count. Alternatively, rerun with `-L 8` and all routes and quote those numbers (the uncapped variants pass `movecheck`).

**F3 (OVERCLAIM; Remark 4.8 l.458–461; abstract l.56–57).**
- **Claim.** "Theorem 4.5 replaces ST by NA … The transfer side TR is still needed."
- **What the proof actually needs.** It needs TRN in **both** forms.
  - Start from a blocked instance (y ∉ N(g)). Step (3) produces G − gu, whose even vertex u is adjacent to y.
  - From then on, steps (3) need the y ∈ N(g) form, that is `TightTransferAdj` with A = {x}. That is a new conjecture, not part of L1I's TR ∧ ST ⇒ L1Blocked (L1I Thm 4.6 uses TR only with c ∉ N(g)).
  - The degree-two case N(g) = {x, y}, hence NA, is reached only after such a step.
- **Fix.** "replaces ST by NA together with the counterpart of TR for tails adjacent to g (A = {x})"; the same in the abstract.

**F4 (GAP, minor; Lemma 4.4 l.388–390 and proof l.395–399).**
- **What is missing.** "Conversely, subdividing xy turns every instance of NA into an instance of N with N(g) = {x, y}" maps instances, but goodness is never carried back. "NA holds when x, y have no common neighbour … covered by [DL, Thm 6.1]" needs exactly that step: Thm 6.1 is a statement about the subdivided graph.
- **The missing step** (two lines):
  - In the subdivided graph, g has b = 0, so g is interior to the path through x g y. Replace x g y by xy.
  - Q(y) avoids x, so it does not contain g, and it is unchanged.
- The abstract's "NA is exactly the case N(g) = {x, y} of N" relies on this step.
- **Fix.** Add the suppression step to the proof.

**F5 (OVERCLAIM, minor; abstract l.44–51 "Proved and formalised … NA is exactly the case N(g) = {x, y}"; §1 Status "Lemma 4.4 … proved and formalised"; §7 table).**
- **What is formalised.** `conjNDegTwo_of_neighbourAvoid` is NA ⇒ degree-two case only.
- **What is not.** Neither the converse (degree-two case ⇒ NA, which needs a fresh vertex, e.g. `Option V`) nor the no-common-neighbour clause is formalised.
- **Fix.** Mark the converse and the last clause "paper only" (with F4's step). Alternatively, formalise the converse via `Option V`.

**F6 (OVERCLAIM, presentation; abstract l.75; README "Closure: Under TR*, the class N ∪ NA has 0 stuck instances at orders 5, 7, 9"; §5.3 l.585–586).**
- **What the statement covers.** At orders 5, 7 and 9, the class has no NA members: a connected graph of odd order has an even vertex. So the statement re-runs the case analysis of Theorem 4.5 under TRN.
- **What it omits.** N ∪ NA is **not** closed. Its NA members are stuck in 22 of 215 (order 6) and 2,522 of 9,558 (order 8). The table shows this, but the abstract and README do not.
- **Fix.** Add "(its NA members, at even orders, are stuck in 22/215 and 2,522/9,558)".

**F7 (MINOR, statement hygiene; §2 l.223–240; Thm 3.3 preamble l.280).**
- **The leaf case.** "the leaf case N(x) = {g} (`avoid_leaf`)" omits "unless the component is the path x g c (universal twins)". The case is false for P₃. `ext.h` checks it.
- **Packed.** "Packed" (pairwise distance ≥ 3) is not defined in the note.
- **The degree-two base.** Its hypotheses are not stated: N(g) = {c, a}, ca ∉ E, N(c) ∩ N(a) = {g}, d(c) ≥ 3.
- **Theorem 3.3.** It says "extended instance with even vertex g", but lists (d), which needs no even vertex, among the moves that carry B.
- **Witness set.** W = N(y) ∖ (N(x) ∪ {g}) needs "({g} only if g exists)".

**F8 (MINOR, cross-references).**
- `ConjN.lean` l.377 says "manuscript Theorem 4.1". It is Theorem 4.5.
- `lean/README.md` says "manuscript Thm 4.3". It is Thm 4.5.
- `trn.cpp` l.1 says "manuscript Conjecture 4.2". It is Conjecture 4.1.
- `tables.sh` l.2 says "(Section 6)". It is §5.
- The §7 list "Library results used" omits `fan_single`, which `ConjNFar.lean` uses.

**F9 (MINOR, hypotheses stronger than needed; Conj 4.1, Cor 4.6, `TightTransferAdj`).**
- **TRN.** The proof of Theorem 4.5 applies TRN only when the child has a witness (some w ∈ N(y) ∖ N(x), w ≠ u). TRN as stated, and as tested, needs no witness. That is fine, but the weaker witness form would suffice.
- **TightTransferAdj.** Corollary 4.6 assumes it for **all** A. Only A = {x} is needed, and the data cover \|A\| ≤ 2 at order 9 (all A at order 7).
- **Fix.** Optional. State Cor 4.6 with A = {x}, or note the gap between the hypothesis and the data.

**F10 (MINOR, reproducibility; README).**
- **xcheckb.** The README command (`nauty-geng -cq 6 | python3 xcheckb.py`) gives 18,954 queries, not the 399,762 claimed. The claimed number needs orders 4–6 plus `one_even_7.g6`.
- **tables.sh.** It enumerates orders ≤ 8 with geng labelling, while the README one-liners use the `one_even` lists. So the `move_*` breakdowns differ between the two, e.g. N₁ at order 7 has move_b 411 vs 407. The STUCK and FALSE counts are identical.
- **The subcubic rows.** They are appended to `data/tables.txt` by hand (comment in `tables.sh`).
- **nadjstat.cpp.** It is new in 27cf961 and is referenced nowhere. Its comment claims that the cases d(y) = 3 and d(x) = 1 of NA are settled on paper. That is correct:
  - d(y) = 3: (g) with y₁ = x and y₂ = a witness gives the d(c) = 1 base;
  - d(x) = 1: dl-one Lemma NP.

  But the manuscript does not say it, and the claim is unaudited there.

**F11 (MINOR; §6.2 l.620–622).**
- **Claim.** "The smallest NA instances with no move into N₁ ∪ NA are of order 6: EF~w".
- **What the data show.** Order 6 has three such graphs:
  - EF~w: 9 instances, 12 edges;
  - EQ~w: 8 instances;
  - EUZw: 5 instances, **10 edges**.
- In EF~w, y ranges over {3, 4, 5}, not only y = 3.
- **Fix.** Say "for example EF~w", or name EUZw as the smallest.

**F12 (MINOR, citation; Lemma 2.2 l.195–204, proof of (c_B) l.333–342).**
- **What (c_B) uses.** The forced-chain clause: re-routing keeps vertex sets, and only the last path gains u.
- **Where it is applied.** To the decomposition of H = K + uℓ, which is not a Lovász decomposition of a graph G − gu: u and c may both have even degree in H.
- **What the cited sources state.**
  - dl-one Lemma 2.1 states the clause only for Lovász decompositions of G − gu.
  - CLT Thm 5.1 gives only tracking.
  - With tracking alone, the far end of Q_c could be u. Then (c_B) would need u ∉ B, which `ext.h` does not require.
- The clause does hold for any decomposition with b ≤ 1 and Z(u) = ∅ ([TF, Prop. 2.1], cited in L1I; RD Lemma 2.2's chain construction). `movecheck` finds 0 violations of (c) with u ∈ B allowed.
- **Fix.** Cite [TF, Prop. 2.1] / RD Lemma 2.2 for the forced clause. Say "b ≤ 1, any decomposition".

**F13 (MINOR, §8 item 4 l.709–711).**
- **Claim.** "Its far-end constraint is what move (x) needs."
- **Why it is loose.** The (x)-child at u = x is (G − gx, y, {x}, N_G(x)). There x is the even vertex, so the child is not an N⁺ instance. N⁺ has the same shape of constraint, but it is not a hypothesis that applies to the child.
- **Fix.** Reword as an analogy.

**F14 (MINOR, §5.3 l.548).** "XC: N₂ together with the (x)-children of N₂ instances": `P_XC` admits only (x)-children whose target lies in A. Fix: say so.

## 6. Overall verdict and required fixes

**Mathematics: SOUND.**
- The headline reduction TRN ∧ (degree-two case) ⇒ N, and hence TRN ∧ NA ⇒ N, is correct, and so are the protected Fan lemma, the far-end calculus and the split.
- Gaps: the suppression step in Lemma 4.4 (F4) and the citation of the forced chain in (c_B) (F12).

**Lean: SOUND and faithful.**
- It builds (18,416 jobs), has no `sorry`, and uses standard axioms only. The definitions match the paper.
- The formalisation is overstated only for Lemma 4.4 (F5).

**Computations: SOUND and reproducible.**
- Every quoted number reproduces exactly. Every move of `ext.h` is proved and passes an exhaustive soundness check with demonstrated power.
- The counts are for a capped calculus (F2).

**Framing: needs correction.** The required fixes are:
1. **F1.** "stuck exactly at all-tight (37,652)" → "only at all-tight; 37,652 of 52,070 all-tight", in the abstract and README.
2. **F2.** State the leaf-path cap (≤ 2) and the route cap (≤ 8 shortest) with every certificate and stuck count, or rerun uncapped (7 → 5; 37,652 → 35,338; …).
3. **F3.** Remark 4.8 and the abstract: ST is replaced by NA **plus** TR for tails adjacent to g (A = {x}).
4. **F4.** Add the suppression step to Lemma 4.4's converse and to the no-common-neighbour clause.
5. **F5.** Mark the converse of Lemma 4.4 and the no-common-neighbour clause as paper only, in the abstract, the Status and §7.
6. **F6.** Abstract and README: add that the NA members of N ∪ NA are stuck at orders 6 and 8.
7. **F7–F14.** Statement hygiene, cross-references, README commands, "smallest EF~w", the citation for (c_B), the §8 wording and the XC definition.

With F1–F6 fixed, the note accurately records the following:
- a formalised conditional reduction of Conjecture N to TRN and NA;
- a proved far-end calculus, with move (x) and the protected Fan lemma also formalised;
- exhaustive evidence to order 9 (TRN to two order-11 slices, NA to order 10);
- an honest map of where single-tail inductive classes fail.

Conjecture N remains open, as the note says.

## Response (author session, 2026-11-27)

All findings were addressed in the commit following 27cf961.

- **F1.** Abstract, §6.1 and README now say "stuck only at all-tight configurations: every stuck instance is all-tight". They give the counts as stuck / all-tight: 2/10, 197/403, 35,338/52,070 at orders 5, 7, 9. The counts are produced by `n1stuck.py` with the graph list, and the data are in `data/n1_stuck*.txt`.
- **F2.** The uncapped calculus is now the default in `ext.h`: leaf paths of every length, and every g–c route for (h). `ncert` takes the flag `R` for all routes. The capped variant remains available as `closure2 -cap`. Every count in the manuscript, README and `data/` was regenerated (`rerun.sh`):
  - 5 uncertified instead of 7; the 115 is unchanged;
  - N₁: 2 / 197 / 35,338; with TR* 13 / 1,396;
  - NA at order 8: 2,451; N₂: 0 / 228 / 106,014;
  - and the rest of the table.

  §5 states that the counts are uncapped and refers to this audit for the capped ones. The per-shape claims of §6 were rechecked on the new data, and the smallest N₁-stuck example is now `DTw` only: `DEk` is certified by a leaf path of length 3.
- **F3.** Remark 4.10 and the abstract now say that ST is replaced by NA *together with* the counterpart of TR for tails adjacent to g (A = {x}). They also say why that counterpart is needed, and that it is new.
- **F4.** The suppression step was added to the proof of Lemma 4.4, both for the converse and for the no-common-neighbour clause.
- **F5.** The abstract, Status, §7 table, `ConjN.lean` docstrings and `lean/README.md` now say that only "NA ⇒ degree-two case" is formalised. The converse is on paper.
- **F6.** The abstract, §5.3 and README add that the NA members of N ∪ NA are stuck: 22/215 at order 6 and 2,451/9,558 at order 8. So N ∪ NA is not closed.
- **F7.** "Packed" is now defined. The base cases state the universal-twin exception and the hypotheses of the degree-two base. The preamble of Theorem 3.3 says which moves need g. The witness set is defined when no g exists.
- **F8.** Cross-references were fixed:
  - `ConjN.lean`: Theorem 4.6, which is the new number after adding Remark 4.5;
  - `lean/README.md`: Thm 4.6;
  - `trn.cpp`: Conjecture 4.1;
  - `tables.sh`: §5.3;
  - §7 now lists `fan_single`.
- **F9.** A new remark after Corollary 4.7 states that only A = {x} and the witness form are used, and the gap between the data and the all-A hypothesis of `TightTransferAdj`.
- **F10.** The README cross-check command now covers all 399,762 queries. It notes the labelling difference in `move_*`, and that the subcubic rows are now produced by `tables.sh`. `nadjstat.cpp` is documented. The easy cases of NA (d(y) = 3 via the split (g); d(x) = 1 via Lemma NP) are now Remark 4.5, with the census in §5.2.
- **F11.** §6.2 names three graphs of order 6, with `EUZw` (the 5-spoke wheel, y the hub) as the one with fewest edges.
- **F12.** Lemma 2.2 and the proof of (c_B) now cite [TF, Prop. 2.1] and RD Lemma 2.2 for the forced chain of any decomposition with b ≤ 1.
- **F13.** The §8 item 4 wording was changed to an analogy.
- **F14.** The XC definition now says "whose target lies in A".
