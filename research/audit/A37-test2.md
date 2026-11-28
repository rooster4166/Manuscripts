# Audit A37: the three-end test (T2), session `claude/test2`

**Auditor:** independent audit agent, 2026-11-28. **Scope:** the manuscript `manuscripts/test2/test2.tex`,
the Lean file `lean/GallaiLean/Test2Lift.lean`, and the data and scripts in `manuscripts/test2/`
(items 1 to 3 of the brief). My scripts are in `research/audit/A37-scripts/`. I edited no other file
and made no commit. (Commit `54c1b90`, "interim snapshot of the auditor's scripts", was made by
someone else from my working directory while the audit was running.)

## 0. Which version was audited

The session kept working in the same checkout while I audited it, so the targets moved:

| object | version audited (primary) | later versions (checked only where stated) |
|---|---|---|
| `test2.tex` | the 611-line untracked draft present when the audit started (md5 `cdaaf15a…`, `\TWELVEFAIL`/`\TWELVETIGHT` "(pending)"). This is the version the brief describes. **All line numbers below refer to it.** | `7cfa4c0` (621 lines; adds order-12 data, "Lean for matchings" converse labels, an order-10 floor sample) and `22e3323` (622 lines; renames the converse to `forestBase2_matching_of_test2`). Shifts are +3 to +10 lines. |
| `Test2Lift.lean` | md5 `5d449fd7…`, unchanged through `22e3323` | — |
| `Test2Converse.lean` | not in the brief | light check only (§2.6) |

Numbering in the compiled draft: Def 1.1, **Lemma 1.2** (parities), Lemma 3.1, Prop 3.2, Cor 3.3,
Def 4.1, Lemma 4.2, Rem 4.3, Lemma 4.4 (stepping), **Thm 4.5** (forest lift), **Prop 4.6**
(converse), **Ex 4.7** (fat theta), Thm 5.1, Prop 5.2, Cor 5.3, Prop 6.1, Cor 6.2, Conj 7.1, 7.2,
Prop 8.1. The brief's "Lemma 1.1, Thm 4.4, Prop 4.5, Ex 4.6" are the same statements under these
numbers. The draft compiles cleanly with `pdflatex`: no undefined references and no overfull boxes
reported.

## 1. The manuscript

Each finding gives a classification: ERROR (false statement or invalid proof), GAP (missing
argument), OVERCLAIM, MINOR (wording or typos), or OK.

### 1.1 Lemma 1.2 (parities): OK
All four claims are correct:
- n is even, since J has n − 2 odd vertices;
- deleting z flips exactly N(z), so the even vertices of B are N(z) − r (2m − 1 of them) and r becomes odd;
- d_J(r) is even and ≥ 3, so d_J(r) ≥ 4 and d_B(r) ≥ 3;
- the budget is ⌈(2k+1)/2⌉ = k + 1.

Machine check: `g_lit.py` asserts "even vertices of B = N(z) − r" on all 717,942 instances.

### 1.2 Lemma 3.1 (floor ⇒ T2): OK
r is odd in B with degree ≥ 3, so it ends an odd number of paths. If it ends only one, some path
passes through r; splitting that path there adds one path and two ends.

### 1.3 Proposition 3.2 (odd semi-cliques): OK; one MINOR
I compared the proof with the text of OSB Theorem 4 (`pdftotext`, §2):
- OSB states p(G) = k + 1 for m = e(H) < k, realised by a path Q of length L = k − m plus k Hamilton paths.
- OSB equation (1) is b_v = d_H(v) + 2·1{v ∈ V(Q)}. It also follows directly: every vertex lies on all k Hamilton paths, plus Q if v ∈ Q.
- OSB: "The individual cap is always attainable at any one vertex v. Start Q at v in (1)."

So Prop 3.2 cites OSB correctly. d_H(r) = 2k − d_B(r) is odd, hence ≥ 1, and r gets d_H(r) + 2 ≥ 3
ends within k + 1 = n/2 paths. The dependence on Javadi–Miralaei and on an unrefereed manuscript is
disclosed (line 215, and the table).

- MINOR (line 222): "(the last paragraph of that proof)". The sentence is in the paragraph after the
  sharpness construction; the proof goes on with the cases m = k and m > k. Fix: "(OSB, proof of
  Theorem 4, the sentence 'The individual cap is always attainable … Start Q at v')".

### 1.4 Corollary 3.3 (literature ranges): OK; two MINOR
- The E-subgraph of B is B[N(z) − r] = J[N(z) − r], so Pyber and Fan apply in the floor form
  restated in `research/notes/eulerian-gallai-literature.md`:
  - BS Theorem 2(b)(c);
  - Bonamy–Perrett: "G_E a forest ⇒ ⌊n/2⌋";
  - Fan: "each block of G_E triangle-free with Δ ≤ 3 ⇒ ⌊n/2⌋".
- The literature notes record verbatim statements for:
  - BBB Theorem 1.2 (planar, exceptions K3, K5⁻);
  - BSCL Theorem 3.2 (partial 3-trees, exceptions K3, K5⁻);
  - BSCL Theorem 4.1 ("maximum degree 4", exceptions K3, K5, K5⁻).
- The exceptions are handled correctly:
  - K3 would need J = K4, which has no even vertex;
  - K5 is never J − z, since B would have 5 even vertices but |N(z) − r| ≤ 4;
  - K5⁻ is an odd semi-clique (k = 2, e(H) = 1) and does occur as J − z, with d(z) = 4. It is covered by Prop 3.2.
- MINOR: Cor 3.3 has no proof. One line is needed: the floor plus Lemma 3.1, with Prop 3.2 for the exceptions.
- MINOR (lines 229–231 and the bibliography): "the original papers were not accessible to us" is
  true of Pyber and Fan only. BBB and BSCL were read on arXiv, per the notes.
  - The following are cited by name with no bibliography entry: Blanché–Bonamy–Bonichon,
    Botler–Sambinelli(–Coelho–Lee), Botler–Sambinelli, OSB, Javadi–Miralaei, MR, the A30 audit.
  - The `\bibitem{BP}` "small maximum degree" paper is used only for the *Question* 1.1. That is fine, but cite Question 1.1 explicitly.
- "Reach" numbers (lines 241–243): **reproduced exactly** (§3g below).
- The MR remark (lines 244–245) is consistent with the MR abstract ("The three-end test holds through
  deletion degree eight"), whose Proposition 10 uses Fan's addible-edge lemmas. It is not relied on: OK.

### 1.5 Definition 4.1, Lemma 4.2, Remark 4.3: OK; one MINOR
- The parities are correct, and every vertex of M is odd, so a Lovász decomposition has exactly n/2 paths.
- Remark 4.3 is correct: keeping zw forces the odd set N(z) − w, of odd size 2m − 1.
- MINOR (line 259): the Lean names cited for Lemma 4.2 (`forM2_odd_child`, `forM2_odd_r`) prove
  oddness only at r and at the children, not "every vertex". The Lean lift never needs the rest, since
  it uses `forM2_size` (≤ |V|/2 paths). Say "(Lean: oddness at r and at the children)".

### 1.6 Lemma 4.4 (stepping with ends): OK
- It is direct-test1 Lemma 4.1 with the end count ε′(u) = ε(u) − [u is a non-root] + c(u).
- "Parents before children" is what makes the dynamic appends see the original end paths.
- It matches `append_forest_ends` exactly; see §2.

### 1.7 Theorem 4.5 (forest lift): OK
Every step checks:
- z ∉ V(Φ);
- D₁ has n/2 paths, and r ends 1 − [r is a child] + c(r) ≥ 2 of them;
- trimming z adds an end at r; if the z-path is the single edge zr, dropping it leaves ≥ 1 end at r, and one split at r restores three ends within n/2 paths.

I also checked the corner case "r a child and Q₀(z) = zr". Then Q₀(r) = zr, the append gives z r p(r), and trimming z gives the end.

The matching case (4.1) and its L₁ remark are correct: r ≁ a₀ in M because ra₀ ∈ Φ.

### 1.8 Proposition 4.6 (the converse): OK; checked line by line; one MINOR
(⇐), the lower bounds. Write ε(u) for the number of ends at u.

Distinct children give distinct end occurrences: each child gives a different end edge at u, and
a path cannot have both ends at u. With d_B(u) even ⟺ u ∈ N(z) − r, and d_Φ(u) = c(u) + [u is a
non-root] odd ⟺ u ∈ N(z):

| vertex | parity facts | bound |
|---|---|---|
| non-root u ≠ r, u ∈ N(z) | c(u) even, ε even | c(u) |
| non-root u ≠ r, u ∉ N(z) | c(u) odd, ε odd | c(u) |
| root u ≠ r, u ∈ N(z) | c(u) odd, ε even | c(u) + 1 |
| root u ≠ r, u ∉ N(z) | c(u) even, ε odd | c(u) + 1 |
| u ∉ V(Φ) | u ∉ N(z), ε odd | 1 |
| r, case (a): root, d_Φ(r) = 1 | (T2) gives ε ≥ 3 | 3 = c(r) + 2 |
| r, case (b): child | c(r) even ≥ 2, ε odd | c(r) + 1 (≥ 3 automatically) |

The sums, using Σ_{V(Φ)} c = |V(Φ)| − q:
- (a): (|V(Φ)| − q) + (q − 1) + 2 + (|B| − |V(Φ)|) = |B| + 1 = n.
- (b): (|V(Φ)| − q) + q + 1 + (|B| − |V(Φ)|) = n.

Both are correct. So |D| = n/2 and every bound is attained.

The reconstruction is also correct:
- A single-edge path p(v)v with v ≠ r a non-root would exceed c(v).
- A path whose two end edges are both terminal at parents has length ≥ 3.
- Removing the terminal edges gives ε′(u) = ε(u) − c(u) + [u is a non-root]. That is 1 at every u ≠ r and 2 at r.
- The exceptional subcase is exactly "(b) and p(r)r is a whole path of D". There ε′(r) = 0, and adding the path zr repairs it.
- The two r-ends lie on distinct paths. Attaching z to the r-path that did *not* lose p(r)r is what keeps (i) at r.
- (i) and (ii) follow as stated.

(⇒) is also right. The edge p(v)v becomes the end edge at p(v), and nothing is appended later at
p(v) on that path: by (i), Q₀(p(v)) ≠ P(v). Trimming z and splitting at r change no other end.

- MINOR (lines 347–348): "has length at least three, since the two parents differ". The reasons are
  that length 1 would make the parent relation cyclic, and length 2 would give the middle vertex two
  parents (direct-test1's wording). Also note that in case (b) the hypothesis "≥ 3 ends" is implied.

### 1.9 Conjecture 7.1, "Equivalently (Proposition 4.6)": GAP
- Location: lines 486–487.
- Prop 4.6 covers only forests of type (a), r a root with d_Φ(r) = 1, and type (b), r a child.
- For r a root with d_Φ(r) ≥ 3, the lower bound at r is only c(r), and the bounds sum to n − 2. The
  base is then equivalent to the *stronger* statement with ≥ d_Φ(r) + 2 ends at r. Lines 360–362 say
  exactly this.
- So the conjecture's stated equivalent ("(T2) with some such forest terminal") follows from the base,
  but the converse is not proved for forests with r a root of Φ-degree ≥ 3.
- Fix: in the equivalent form, take "such" to mean type (a) or (b), or require ≥ d_Φ(r) + 2 ends when r is a root.

### 1.10 Example 4.7 (fat theta): OK, hand argument verified; exhaustive check reproduced
- Hand argument:
  - each leaf has Φ-degree 1, |A| is odd and |C| is even;
  - M is the disjoint union of a star at r (leaves C + z) and a star at h₂ (leaves A);
  - with r a root, (ii) on the h₂-star forces |A| = 1;
  - then at least two pairs of the r-star are C–C pairs, and under either rooting of the h₂-component at least one of them is a sibling pair.

  All of this is correct.
- The base with r a child: I checked it vertex by vertex, and my own code finds it and lifts it (§3d).
- Second graph `I??CFx~~w`: J − z is K₂,₅ with the hub edge plus a path 9–0–6–8 and a chord 6–9. The
  abstract's "K₂,₇ and a relative" is acceptable.
- "Only four instances without a base rooted at r" is consistent with the shipped data: every other
  instance is in tier M or S, both rooted at r.

### 1.11 Section 4 data table and its method paragraph: OK
- route_ext query C: a path with ends s, w satisfies V(P) ∩ r_s = {s}, V(P) ∩ r_w = {w}, and r_s ∩ r_w = ∅.
  I read `tools/route_ext.c`: the initial `vis` contains crv[a], and the final test is
  `(pm2 & crv[w]) == 1<<w && (crv[a] & crv[w]) == 0`.
- With r_v = {v, p(v)} at children, this is exactly (i) plus (ii). The extra disjointness cases are all
  implied by (i).
- Tier counts are consistent: 520,182 + 196,798 + 4 = 716,984. In my sample of 600 the M share is 72%;
  in the population it is 72.6%.

### 1.12 Theorem 5.1 and Proposition 5.2 (floor lift and its converse): OK
- In B − Φ, w is the only even vertex, so a Lovász decomposition has exactly k paths. The non-roots
  differ from w and are odd, so Lemma 4.4 applies.
- Converse: the bounds are the same as in Prop 4.6, with c(w) at the root w (or 0 if w ∉ V(Φ)). They
  sum to (|V(Φ)| − q) + (q − 1) + (|B| − |V(Φ)|) = |B| − 1 = 2k, and the same holds when w ∉ V(Φ).
  Hence the bounds are tight and the reconstruction goes through.
- The proof is terse but complete.

### 1.13 Corollary 5.3 (DL ⇒ T2): OK as stated; the surrounding claims are OVERCLAIMED
- The corollary and `test2At_of_disjL1` agree, including the universal-twin hypothesis.
- **OVERCLAIM.** The following phrases drop the twin condition:
  - abstract, lines 59–61: "DL implies (T2) at every root with matching data, with the same data condition … that give (T1)";
  - §5, lines 438–440: "So DL yields both spine tests at every root with matching data";
  - table line 124: "DL ⇒ (T2) at roots with data";
  - Status 1: "DL ⇒ (T2) at roots with data".

  The condition cannot be dropped:
  - At an odd semi-clique with matching data the floor is false. So *every* matching data choice
    there has a universal-twin pair, and DL yields nothing at that root.
  - The same happens **outside** the semi-cliques (`h_twins.py`). At order 8 there are **5 instances
    with matching data, not odd semi-cliques, at which every data choice (w, M₀) has a universal-twin
    pair**: `G?b~~{` (0,4) and (4,0), `GCv~~{` (1,4), `GQj~~{` (1,3) and (3,1), all with d(z) = 4 and
    3 data choices. In a 20,000-instance order-10 sample there are 2 more: `ICvv~~~~w` (1,5) with
    d(z) = 6 and 15 choices, and `I?bfN~~~w` (4,0).
  - At these roots Cor 5.3 is inapplicable, so "DL ⇒ (T2) at every root with matching data" does not
    follow from anything in the paper. (T2) does hold there: the session's floor base is found through
    spanning-tree joins (tier S in `floorbase_order8.txt`).
  - The (T1) analogue `test1At_of_disjL1` requires `M` connected, which is a different side
    condition. So "the same data condition" is also inaccurate.

  Fix: "at every root with twin-free matching data". Do not suggest that twin pairs occur only at
  odd semi-cliques; they do not.
- The order-8 data numbers (2,280 twin-free data choices all with a base; 153 twin choices none): **reproduced exactly** (§3h).
- "At order 10 also at the fat theta" (lines 443–444): the fat-theta part is verified (§3h). The
  audited draft gives no per-instance order-10 floor data for the "precisely" claim. Commit `7cfa4c0`
  replaces the sentence with a sample statement and ships `floorbase_order10_sample.txt.gz`, which I
  did not check. OK in the later version.

### 1.14 Proposition 6.1 and Corollary 6.2 (d(z) = 4): OK; one MINOR
- Prop 6.1 is Thm 5.1 with Φ = {ab} rooted at a, so (i) reads a ∉ Q(b). Cor 6.2(a) is separation
  (FarApart(G, b, a)). Cor 6.2(b) is `avoid_of_steer2`. The Lean statements match (§2).
- MINOR: Prop 6.1 has no proof. Add "Theorem 5.1 with Φ = {ab} rooted at a".
- The numbers are consistent:
  - 846 + 6,512 + 109 = 7,467, and (846 + 6,512)/7,467 = 98.5%;
  - TRIDATA: 40,454 + 1,145 = 41,599 and 265,632 + 40,454 = 306,086;
  - order 8: 88 / 390 / 76 is **reproduced exactly** with my own implementation of `Steer2` (§3f).
- MINOR (§6, lines 473–479): "some N(z) − y is pairwise at distance at least three". Here y is undefined.
  The paragraph opens with "For m ≥ 3 …" but all 37 hits are at d(z) = 4 (m = 2), which reads as a
  contradiction. Also, `coverage.py` was not reproduced by me.

### 1.15 Conjecture 7.2 and the all-odd check: OK
- At order 6 I reproduced 13 graphs, 428 choices and 0 failures with my own exhaustive enumeration.
- Order 8: see §3h.

### 1.16 Proposition 8.1 (cones): OK
All four parts are correct:
- (a): the even vertices of J are the odd vertices of B, and u is odd;
- (b): J − a ≅ B^{+a} via u ↦ a;
- (c): C = B − a has odd set N_B(a) − x;
- (d): with w = u and the star u–O rooted at u, T′ = O, (J − a) − Φ = C^E, and (i), (ii) become the two stated conditions. |O| = d_B(a) − 1 is even and ≥ 2.

The counts 6 / 204 / 35,952 are reproduced: all have t2 = 1, and all 20 tight instances are cones (`h_cones.py`).

### 1.17 Section 2 (data and validation)
- OK: Observation 2.1 and the tight data are reproduced (§3b).
- **GAP (validation claim, line 153).** "Every positive answer comes with a witness" is false for the slack answers:
  - `t2.c` prints only the (T2) witness, so its 717,922 answers slack = 1 (p(B) ≤ k) are unwitnessed (8 + 943 + 716,971 at n = 6, 8, 10);
  - "tight at exactly 20" and the first clause of Observation 2.1 rest on them;
  - the brute-force cross-check `bf_t2.py` covers order 6 only.

  Mitigation: the search core is verbatim `re.c` (diffed; audited in A30). My CP-SAT re-decides slack
  at every order-6/8 instance and at 2,250 random order-10 instances, with 0 disagreements and every
  witness checked.

  Fix: print and verify slack witnesses, or say that slack answers are unwitnessed.
- MINOR (lines 185–186): "every decomposition into at most n/2 paths has exactly k+1 paths, so it has
  at most d_H(r)+2 ends". The reason is missing: r lies on (d_B(r) + ε(r))/2 ≤ k + 1 paths. "Exactly"
  is not needed.
- MINOR (lines 195–197): the cut-vertex failures show that *some* connectivity is needed, not that the
  spine's 3-connectivity is needed. All 2-connected instances pass. The numbers (1,084 hold; 3 cut-vertex failures) are **reproduced**.
- The order-12 sentence was skipped as instructed. Note that Status item 3 lists "the order-12 sample"
  as computed while the macros were pending in this draft; `7cfa4c0` fills them in (not audited).

### 1.18 Abstract, last paragraph: OVERCLAIM
- Location: line 70. "They are tight exactly at semi-cliques" is stated as a fact.
- Only "⇐" is proved, by edge counting. "⇒" is computed for n ≤ 10 and is the Bonamy–Perrett
  question on this class, which the status section itself lists as open.
- Fix: "(computed, n ≤ 10)".

### 1.19 Summary table and status labels
- "Floor ⇒ (T2); floor lift", "Forest lift", "d(z) = 4 …": the labels "proved; Lean" are correct.
- "Odd semi-cliques: proved from OSB Thm 4 (unrefereed, uses JM)" and "Pyber / Fan ranges: proved from
  the literature (restated floor forms)" are honest labels.
- The "DL ⇒ (T2) at roots with data" row is the overclaim of §1.13.
- "(T2) … tight ⟺ J − z an odd semi-clique: computed, exhaustive, witnesses verified": only the (T2)
  witnesses were verified (§1.17).
- MINOR: `manuscripts/test2/README.md` (audited version) still says "the manuscript test2.tex will be added here".

## 2. Lean (`Test2Lift.lean`)

### 2.1 Build, sorry, axioms: OK
- `lake build GallaiLean.Test2Lift`: green in 7 s. There are deprecation warnings only (`if_pos`/`if_neg`).
- No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by` or `unsafe` in the file.
- My own `A37-scripts/A37Check.lean` (`lake env lean`) prints `[propext, Classical.choice, Quot.sound]` for all ten named theorems and two helpers:
  - `test2At_of_forestBase2`, `test2_of_forestBases2`;
  - `floor_of_floorBase`, `floor_of_matchingBase`;
  - `test2At_of_floor`, `test2At_of_floorBase`, `test2At_of_disjL1`;
  - `test2At_of_pairAvoid`, `test2At_of_pair_farApart`, `test2At_of_pair_steer2`;
  - helpers `append_forest_ends`, `test2At_of_leafDecomp`.

  This matches `data/axioms.txt`.

### 2.2 `Test2At` and `test2_of_test2At`: OK (faithful)
- `Test2At J z r := ∀ hr : J.Adj z r, ∃ D : PathDecomp (delVert J z), D.size ≤ card V / 2 ∧ 3 ≤ D.ends r`.
  It is vacuous only when z ≁ r, and every theorem is used with z ~ r.
- `test2_of_test2At` concludes `Gallai.Test2` from `ThreeConnected.lean`, the definition used by
  `gallai_iff_spineTests'` via `SpineTests`.
- In `A37Check.lean` I re-proved `Test2 J z ↔ ∀ r, J.Adj z r → (only evens z, r) → Test2At J z r` by hand.

### 2.3 `ForestData2` / `ForestBase2`: OK (faithful, and non-vacuous)
- The fields encode exactly:
  - T = N(z) − r, duplicate-free;
  - Φ ⊆ E(J − z);
  - distinct children and edges;
  - parent-first order;
  - odd set of Φ equal to N(z);
  - "r a child ⇒ c(r) ≥ 2".
- Acyclicity is not required, but it is implied: in any cycle of Φ-edges every vertex would be a child
  through a cycle edge, so the parent map would be cyclic, and parent-first order forbids that. So L is
  always a rooted forest.
- `ForestBase2` requires a Lovász decomposition of `forM2 = J − zT − Φ` with (i) and (ii) over all pairs,
  including r when it is a child. This is Thm 4.5's hypothesis.
- **Non-vacuity, machine-checked.** `A37Check.lean` builds a concrete instance and fires the main theorem: `A37.test2At6 : Test2At J6 3 5`, standard axioms. The instance:
  - J6 = K₃,₃ + 35 (graph6 `EFzo`), z = 3, r = 5, T = [0,1,2];
  - L = [(0,5),(4,1),(2,4)], whose rooting is (5, 1);
  - an explicit `PathDecomp` [0 4], [1 5], [2 5 3] of M;
  - every field and condition proved by `decide`;
  - `ForestBase2 J6 3 5` is then built, and `test2At_of_forestBase2` applied.

### 2.4 `FloorData` / `FloorBase`: OK (faithful, and non-vacuous)
- The fields are Φ ⊆ E(B), w ∉ T, w never a child, distinct children and edges, parent-first order,
  and odd set equal to T. This is Thm 5.1.
- `test2At_of_floorBase` adds hT: the even vertices of J − z, namely (N(z) − r), are exactly w plus T.
  That is correct by `even_delVert_iff`.
- Concrete instance in `A37Check.lean`: B5 = K₃,₂, w = 0, T = [1,2], L = [(3,1),(2,3)], with
  decomposition [3 0 4], [1 4 2]. It gives `A37.floor5 : ∃ D, D.size ≤ 2` (standard axioms).

### 2.5 The other statements: OK
- `test2At_of_floor`: J − z has ≤ (n−2)/2 paths, which is Lemma 3.1. It uses only that d_J(r) is even and ≥ 3.
- `test2At_of_disjL1`: its hypotheses are `hT`, disjoint pairs, w not in a pair, pairs edges of J − z,
  and **no universal twins**. Lean is more faithful here than the abstract (§1.13).
- `test2At_of_pairAvoid`: hT with `pairVerts [(a,b)]` forces N(z) = {r, w, a, b}, and `AvoidDecomp (B − ab) b {a}` is Prop 6.1.
- `test2At_of_pair_farApart`: the hypothesis is that a and b have no common neighbour in J − z. This
  equals "none in G = B − ab", since only the edge ab is removed.
- `test2At_of_pair_steer2`: `Steer2 (leafX a) (apex G {b}) (some w) (some b)`. By the symmetry of the
  data, the swapped pair (b, a) gives the other orientation that `dz4_cover.py` also uses.
- MINOR: the docstrings carry stale numbering:
  - "§3" (line 8), "Theorem 3.2" (lines 34, 484), "Lemma 3.1" (49), "Definition 3.1" (237) should be §4, Thm 4.5, Lemma 4.4, Def 4.1;
  - "Theorem 4.1" (542, 736) and "Corollary 4.2" (672) should be Thm 5.1;
  - "Corollary 4.4" (805) should be Cor 5.3;
  - "Proposition 5.3" (919) should be Prop 6.1;
  - "Corollary 5.4(a)/(b)" (986, 1006) should be Cor 6.2.

### 2.6 `Test2Converse.lean` (not in the brief; light check)
- It builds green with no `sorry`.
- `matchingFloorBase_of_terminal`, `forestBase2_matching_of_terminal` and `forestBase2_matching_of_test2`
  depend only on the standard axioms (`A37Converse.out`).
- The signatures match the later manuscript's description: the matching case only, from a (T2)
  decomposition of `delVert J z` with a terminal matching to `ForestData2`-shaped data.
- Faithfulness was not audited.

## 3. Data

Everything was run with my own code. The common pieces are in `a37lib.py`:
- a graph6 decoder;
- a k-connectivity test;
- a CP-SAT path-decomposition model: slots, oriented edges, in/out-degree ≤ 1, one start and one finish per used slot, position labels against cycles;
- a decomposition checker.

Every CP-SAT witness was re-checked by that checker. CPU use was kept to one worker per job.

### (a) Order-8 row (and order 6): REPRODUCED IN FULL
`a_order8.py` regenerates the row from scratch:
- `nauty-geng -c 8`, i.e. *all* connected graphs, with my own filters (δ ≥ 3, exactly two even vertices, adjacent, 3-connected);
- my CP-SAT model then decides (T2) and slack at **every** instance, not only at a sample.

| check | result |
|---|---|
| order 8 | 474 graphs, 948 instances, (T2) at all 948, slack at 943, tight 5 (all odd semi-cliques) |
| order 6 | 5 graphs, 10 instances, all hold, 2 tight |
| agreement with `t2_order6_8.txt` | per (slack, t2) pair; canonical-form multisets equal (479 graphs) |
| 2-connected, not 3-connected, δ ≥ 3, order 8 | 63 graphs, 126 instances, all hold, so 1,084 = 10 + 948 + 126 in total |
| cut vertex, order 8 | 8 instances; (T2) fails at exactly 3 (`GCdbNw` 7 5, `GQhTUg` 0 7 and 7 0) |

### (b) tight ⟺ odd semi-clique: REPRODUCED; converse by reasoning OK
`b_tight.py`, on the 20 lines of `tight_le10.txt`:
- all 20 witnesses check;
- all 20 have e(H) < k;
- d_H(r) = 1 at 18 instances and d_H(r) = 3 at 2 (`IQj~~~~~w`, both orientations);
- my CP-SAT finds the maximum number of ends at r, and it equals d_H(r) + 2 at all 20 (5 ends at `IQj~~~~~w`);
- at n ≤ 8, CP-SAT also proves p(B) > k and that d_H(r) + 4 ends are infeasible.

Over **all 717,942 field lines**, slack = 0 ⟺ e(B) > 2k²: 2 + 5 + 13 slack-0 lines are all semi-cliques, and no semi-clique has slack 1.

Converse, by hand:
- If B = K_{2k+1} − H with e(H) < k, then e(B) ≥ 2k² + 1 while k paths cover ≤ 2k · k edges, so p(B) ≥ k + 1. With (T2), the instance is tight.
- The forward direction (tight ⇒ semi-clique) is computational only. It depends on the slack = 1 answers, which are unwitnessed (§1.17); my samples in (c) support them.

### (c) Order-10 sample and filters: REPRODUCED
- **Counts:** my C filter `count10.c` (shares no code with `t2.c`), on `nauty-geng -c -d3 10` (5,203,110 graphs), keeps **358,492 graphs**. That gives 716,984 instances, with d(z) = 4 / 6 / 8 at 307,231 / 346,599 / 63,154. All exactly as claimed.
- **Sample:** `c_order10.py` takes 250 (seed 37) plus 2,000 (seed 2026) random lines. For each line it:
  - checks the fields d(z), d(r), n;
  - checks parity and 3-connectivity with my own code;
  - decides (T2) by CP-SAT (≤ 5 paths, ≥ 3 ends at r) and checks the witness;
  - decides slack by CP-SAT (≤ 4 paths) and checks the witness.

  Result: **2,250 / 2,250 hold (T2), and slack agrees at 2,250 / 2,250** (all slack 1), so 0 disagreements.

### (d) Fat theta: REPRODUCED
`d_theta.py` is my own exhaustive search with no oracle. It runs over all edge subsets of B, all rootings and all Lovász decompositions of M.

| instance | forest T-joins | rootings, r a root | bases | rootings, r a child | (rooting, D₀) bases |
|---|---|---|---|---|---|
| `I???F~}~o` (7,9) and (9,7) | 64 | 288 | **0** | 847 | 5,040 |
| `I??CFx~~w` (7,8) and (8,7) | 112 | 280 | **0** | 988 | 9,120 |

- In each case one child base is lifted by my own lift code and verified as (T2).
- For (7,9) the base found is the manuscript's construction: |A| = 3 rooted at ℓ₀, |C| = 4 rooted at c₀.
- These rooting counts equal the session's query counts (288 = 49 + 175 + 63 + 1; 288 + 847 = 1,135).
- Floor at the fat theta (`h_thetafloor.py`): p(K₂,₇) ≤ 4 (CP-SAT witness), and over all w, all
  forest T′-joins and all w-rootings (3,472) there is **no** floor base. This confirms lines 443–444.

### (e) `tb2.py` re-run with independent checks: REPRODUCED
`e_tb2.py` calls the session's `tb2.process` with `route_ext` on a seeded sample of **600** order-10
instances (430 tier M, 170 tier S) and on the 4 tier-N instances. On every returned witness my own code checks:
- Φ ⊆ E(B) is a forest with odd set N(z);
- the parent map is a valid rooting, with r a root or a child with c(r) ≥ 2;
- D₀ is a Lovász decomposition of my own M (one end per vertex, n/2 paths), with (i) and (ii);
- `tb2`'s lifted paths are a valid (T2) decomposition;
- my own independent lift also gives a valid (T2) decomposition.

**604 / 604 pass.** The route_ext query-C semantics was checked by reading the C source (§1.11).

Also (`h_2conn8.py`): at the 126 order-8 instances with δ ≥ 3 that are 2- but not 3-connected
(generated here), a forest base is found at all 126 (92 M, 34 S), and all 126 pass my own check.
This confirms the §4 and Conj 7.1 claim.

### (f) `dz4_cover.py` steering vs Lean `Steer2` and `steer2.cpp`: MATCHES
- Python vs C++: line-by-line they agree:
  - same move rule: q ≠ x, q ≠ the other token, after deleting pq, q not adjacent to the other token;
  - same done rule: q isolated and q ≠ y, because the leaf at y is not stored;
  - same memo key, and either token may move.
- Python vs the Lean inductive:
  - `fin` = a move to a vertex whose only neighbour is the mover, which is isolated after the deletion. Python treats this as done, and its extra adjacency test is then vacuous.
  - `step` = the same move rule.
  - `swap` = either token moves.
  - The leaf L = `none` ∈ X is never a target, and its edge is never deleted, so y is never isolated. This matches Python's `q == y` exception.
- Executable check: `f_steer.py` implements `Steer2` directly from the three constructors, as a least
  fixed point over (K, {a, b}). It agrees with `dz4_cover.steer2` on **3,806 / 3,806** (G, w, y, x)
  cases: all order-8 d(z) = 4 data choices, plus 300 random order-10 triangle instances.
- It reproduces order 8 exactly: FAR 88, STEER 390, not covered 76, no data 83 (of 637).
- On the triangle sample: 295 STEER and 5 not covered, consistent with 40,454 / 41,599.
- MINOR: the `dz4_cover.py` docstring says "every positive answer is cross-checked", but FAR answers
  are not sent to the oracle. They are a theorem, and the manuscript only claims schedules are cross-checked.

### (g) `lit_cover.py` (Pyber / Fan): REPRODUCED EXACTLY, order 8 and order 10
`g_lit.py` uses my own block decomposition (maximal 2-connected induced subgraphs, then bridges) and
my own forest test; there is no networkx.
- Order 8: FAN 533 / 104, PYBER 533 / 64, SEMI 1 / 4, neither 103 / 203.
- Order 10, all 716,984 lines: FAN 265,632 / 127,504 / 3,767; PYBER 265,632 / 93,173 / 981; SEMI 1 / 6 / 6; neither 41,598 / 219,089 / 59,381.
- Both are identical to `lit_cover_order8.txt` and `lit_cover_order10.txt`.
- "At d(z) = 4 Fan fails exactly when N(z) − r is a triangle" holds at all 307,231 instances.

### (h) Extra: order-6/8 matching-base and DL-data claims (own exhaustive code, no oracle): REPRODUCED
`h_bases8.py` enumerates every Lovász decomposition, with an early stop once a base is found.

| claim | my count |
|---|---|
| order 8: perfect matchings of J[N(z)] | **1,512**, every one giving a matching base (some orientation and some D₀) |
| order 8: instances with a matching base | **685** |
| order 6: instances with a matching base | **8** of 10 (the table's 8 M / 2 S) |
| order 8 DL data (w, M₀), twin-free | **2,280**, all with a floor base |
| order 8 DL data (w, M₀), with a twin pair | **153**, none with a floor base |
| order 8: instances with a floor matching base | **834** (= the M tier of `floorbase_order8.txt`) |

The lines "exists for all 2,280 … fails for all 153" and "every one of the 1,512 perfect matchings"
are therefore confirmed. The per-instance twin structure behind §1.13 is in `h_twins8.out` and `h_twins10.out`.

Conjecture 7.2 claim, all-odd graphs: order 6 gives 13 graphs, 428 choices, 0 failures, reproduced
(`h_allodd6.out`).

Order 8 was **not completed**. My pure-Python enumerator hit its 25-minute limit before finishing.
No FAIL line was printed, and FAIL lines are flushed immediately. But the summary, and so the number
of choices covered, was lost when the run was killed. So the session's "224 graphs, 43,400 choices,
0 failures" at order 8 is not independently confirmed.

### Not reproduced
- `coverage.py`: the packed-regime 37 / 685 and 0 / 14,434.
- The order-10 runs of `tb2_pm.py` and `tb2_floor.py` (later versions).
- The full order-10 base search: I checked a sample plus the 4 special instances.
- Conjecture 7.2 at order 8: my run timed out; see (h).
- The order-12 sample (skipped as instructed).

## 4. Summary table

| # | Item | Location (audited draft) | Class | Fix |
|---|---|---|---|---|
| 1 | Lemma 1.2, Lemma 3.1 | §1, §3 | OK | — |
| 2 | Prop 3.2 vs OSB Thm 4 | l. 219–225 | OK (+ MINOR pointer "last paragraph") | cite the exact sentence |
| 3 | Cor 3.3: no proof; missing bibitems; "originals not accessible" applies only to Pyber/Fan | l. 227–239, bibliography | MINOR | one-line proof; add entries |
| 4 | Lemma 4.2's Lean attribution covers only r and the children | l. 259 | MINOR | reword |
| 5 | Lemma 4.4, Thm 4.5 | §4 | OK | — |
| 6 | Prop 4.6 (bounds, sums, exceptional subcase, (i)/(ii)) | l. 321–358 | OK (+ MINOR "since the two parents differ") | reword |
| 7 | Conj 7.1 "Equivalently (Prop 4.6)": converse unproved for r a root with d_Φ(r) ≥ 3 | l. 486–487 | GAP | restrict to types (a)/(b) or demand d_Φ(r)+2 ends |
| 8 | Example 4.7 hand argument and second graph | l. 364–387 | OK | — |
| 9 | Thm 5.1, Prop 5.2, Cor 5.3 | §5 | OK | — |
| 10 | "DL ⇒ (T2) at every root with matching data" / "the same data condition". Five non-semi-clique order-8 roots have only twin data | abstract l. 59–61; l. 438–440; table l. 124; status 1 | OVERCLAIM | add "twin-free"; (T1) needs M connected |
| 11 | Prop 6.1 has no proof | l. 448–451 | MINOR | "Thm 5.1 with Φ = {ab}" |
| 12 | Packed paragraph: undefined y; m ≥ 3 vs the d(z) = 4 numbers | l. 473–479 | MINOR | reword |
| 13 | Prop 8.1 and cone data | §8 | OK | — |
| 14 | "every positive answer comes with a witness" (slack unwitnessed) | l. 153; table l. 119 | GAP | print and verify slack witnesses, or qualify |
| 15 | missing reason for the "≤ d_H(r)+2 ends" bound | l. 185–186 | MINOR | each vertex lies on ≤ k+1 paths |
| 16 | "connectivity hypothesis of the spine is needed" | l. 195–197 | MINOR | "some connectivity is needed" |
| 17 | abstract: cone tests "tight exactly at semi-cliques" | l. 70 | OVERCLAIM | "(computed, n ≤ 10)" |
| 18 | status 3 lists the order-12 sample while it is pending; stale README | l. 575; README | MINOR | — (fixed in 7cfa4c0) |
| 19 | Lean build, no sorry, axioms (all 10) | Test2Lift.lean | OK | — |
| 20 | Lean faithfulness of Test2At / ForestData2 / ForestBase2 / FloorData / FloorBase; non-vacuous (concrete instances built) | Test2Lift.lean | OK | — |
| 21 | Lean docstring numbering stale | Test2Lift.lean l. 8, 34, 49, 237, 484, 542, 672, 736, 805, 919, 986, 1006 | MINOR | renumber |
| 22 | (a) order-8 row | data | OK (full, independent) | — |
| 23 | (b) tight ⟺ semi-clique | data | OK (forward direction computational, see 14) | — |
| 24 | (c) order-10 filters, counts and sample (2,250) | data | OK | — |
| 25 | (d) fat theta claims | data | OK | — |
| 26 | (e) tb2 lifts (604 independently re-checked) | data | OK | — |
| 27 | (f) steering port = Lean Steer2 = steer2.cpp | scripts | OK (+ MINOR docstring) | — |
| 28 | (g) Pyber/Fan coverage, orders 8 and 10 | data | OK (exact) | — |

No ERROR was found. Every proof in the manuscript is valid as written. The findings are one GAP in a
stated equivalence (7), one GAP in the validation claim (14), two OVERCLAIMS (10, 17), and minor items.

## 5. Verdict per item

- **Item 1 (manuscript): sound, with fixes required.**
  - Every proof was checked line by line and is correct: Lemma 1.2, Lemma 3.1, Prop 3.2, Cor 3.3,
    Lemma 4.2, Lemma 4.4, Thm 4.5, Prop 4.6 (both cases and the exceptional subcase), Example 4.7,
    Thm 5.1, Prop 5.2, Cor 5.3, Prop 6.1, Cor 6.2, Prop 8.1.
  - To fix before release: the DL overclaim in the abstract, §5, the table and the status list (10);
    the cones-tightness overclaim in the abstract (17); the "Equivalently" in Conj 7.1 (7); and the
    witness claim in §2 (14).
- **Item 2 (Lean): PASS.**
  - The build is green, with no sorry and standard axioms.
  - The definitions say what the manuscript says, and `test2_of_test2At` concludes the spine's `Test2`.
  - Both base structures are satisfiable: concrete instances are machine-checked and the main theorems fire on them.
  - Only docstring numbering is stale.
- **Item 3 (data): PASS.** Every reproduced number matches exactly:
  - order-8 row and the connectivity remark;
  - order-10 counts;
  - 2,250 sampled order-10 instances, including slack;
  - tight ⟺ semi-clique on every line, and the emax values;
  - fat theta, both graphs and both orientations, plus the floor at the fat theta;
  - 604 tb2 lifts;
  - Steer2 port equivalence, with order-8 FAR/STEER exact;
  - Pyber/Fan coverage at orders 8 and 10;
  - cone counts;
  - order-8 matching-base and DL-data numbers (1,512; 685; 2,280 / 153; 834).

  The one caveat is that the slack = 1 answers of `t2.c` are unwitnessed in the shipped data (14).

## 6. Reproduction (from `research/audit/A37-scripts/`)

    python3 a_order8.py                      # (a) ~1 min
    python3 b_tight.py                       # (b)
    gcc -O2 -o count10 count10.c && nauty-geng -q -c -d3 10 | ./count10 >/dev/null   # (c) counts
    python3 c_order10.py 250 37; python3 c_order10.py 2000 2026                         # (c) sample
    python3 d_theta.py 'I???F~}~o' 7 9   (and 9 7; 'I??CFx~~w' 7 8 and 8 7)            # (d)
    python3 h_thetafloor.py 'I???F~}~o' 7 9                                             # (d) floor
    gcc -O2 -o route_ext ../../../tools/route_ext.c; python3 e_tb2.py ./route_ext 600 11 # (e)
    python3 f_steer.py 300 3                 # (f)
    python3 g_lit.py <order-8 lines>; python3 g_lit.py ../../../manuscripts/test2/data/t2_order10_fields.txt.gz  # (g)
    python3 h_cones.py; python3 h_bases8.py; python3 h_allodd.py 6 1000000; python3 h_allodd.py 8 200000
    cd ../../../lean && lake env lean ../research/audit/A37-scripts/A37Check.lean   # Lean checks
