# A6 — Audit of the deletion-degree-six frontier (six even vertices)

Date: 2026-11-26. Referee stance: adversarial. Every step is graded **SOUND**, **GAP** (fixable; fix given), **ERROR** (false as stated; counterexample given) or **UNCLEAR** (cannot be decided from the collection).

**Pieces audited.**
- RS = six-even-root-shapes (shape theorem, isolated-root descent, private-leaf argument, C4 twins).
- INC = six-even-incidence (Thm 1, Lemma 2).
- 6CL = six-clique-prescribed-ends (Lemma 2 = Fan's grouped transfer, Lemmas 3–4, Thm 1, Cor 5, Thm 6).
- D10 = degree-ten-marked-root.
- MR = marked-reduction: Thm 144 and Cor 138, with the parts of Lemma 133 and Thms 135–137 they rest on.

Sources: the raw texts in `scratchpad/raw/`, and two primaries I downloaded. These are Botler–Sambinelli (arXiv 1911.04546) and **Fan, JCTB 93 (2005)**; the second is the full PDF, from the scispace mirror.

**Scripts and outputs:** `research/audit/A6-scripts/`. They need the tools in `/home/user/Manuscripts/tools` (pathnum.py) and OR-Tools.

---

## 0. Headline

1. **No ERROR was found in any audited statement.** None of the computations found a counterexample:
   - every connected 8-vertex graph with six even vertices, at every even root;
   - the precise end-vector claims of INC Lemma 2, 6CL Thm 1 and 6CL Thm 6, on all 8-vertex instances and on random 10–14-vertex instances;
   - Fan's grouped lemma, on 3,000 random instances;
   - the path-plus-cycles lemmas of D10.
2. **The shape theorem's certificate banks are absent from the collection, but I re-derived them independently.**
   - The method: an exhaustive AND–OR search over every held edge set on the seven-site record. It uses only the Lovász exact-end seed and Fan's Lemma 3.3/3.4 rule.
   - It reproduces RS's contact table *exactly*: K0 31, K1 30, K2 27, K3 15 certified, with exactly the printed survivors.
   - It certifies all 7 one-universal cores × 31 contact sets.
   - It certifies all 32 exterior masks of the K2 refinement.
   - Sixteen certificates were replayed end to end on concrete random hosts with Fan's own sequence construction. Each gave a verified floor partition.
   - So the case analysis of the shape theorem is confirmed, and the printed survivors cannot be removed by any seven-site certificate of this kind.
3. **Fan's Lemma 3.3 now MATCHES verbatim.** I obtained the primary text. This upgrades A7 item 1c from NOT FOUND to MATCHES. The 6CL Lemma 2 statement and every use I checked agree with it.
4. **MR Thm 144 can be made Shaik-free.**
   - Contrary to A7 §4 and the status map, Botler–Sambinelli (BS) *alone* does not suffice. It covers the "r ∈ T" step and the Cor 106 uses with ≤ 4 unmarked even vertices.
   - It does not cover the step "at least two universal vertices in K". That step needs one of two inputs:
     - FHZ together with MR Lemma 133. Lemma 133's proof only uses connectivity, although it is stated for 2-connected B.
     - The seven-site one-universal bank (recomputed here).
   - With either, Thm 144 no longer depends on the unrefereed preprint.
5. **Remaining UNCLEAR items all rest on finite data absent from the collection**, which I did not regenerate:
   - INC Lemma 2's trees;
   - 6CL Thm 6's 31,442 records;
   - D10's selection lemma, full-tails and five-edge tables;
   - MR Thm 135 (9,330 entries), Thm 137 (235 cases), Lemma 121, and Lemma 133's M/P/C table.

   The statements built on them pass every test I ran.

---

## 1. Verdict table

### 1.1 RS — six-even-root-shapes

| # | Step | Verdict | Note |
|---|---|---|---|
| RS1 | Private-leaf equivalence: rooted partition of B ⇔ floor partition of W = B + ℓ (trim; paid split) | SOUND | r has positive even degree since B is connected |
| RS2 | B[T] subcubic ⇒ floor in W by BS Thm 13 | SOUND | BS Thm 13 checked verbatim: "Δ(EV(G)) ≤ 3 ⇒ Gallai graph or SET". A SET graph has exactly 3 even vertices, and W has 5 |
| RS3 | Exactly one universal ⇒ "one-universal rim certificates cover all such A" | UNCLEAR as written; **independently confirmed** | Bank absent; the text does not say which shapes it covers (F1). My search certifies all 7 shapes × 31 A |
| RS4 | ≥ 2 universal ⇒ core is one of K0–K3 | SOUND | K2 has three universal vertices a, b, d; the labelling is consistent |
| RS5 | First (seven-site) bank: survivors K1: abe; K2: abd, abcd, abde, abcde; K3: all \|A\| ≥ 3; K0: none | UNCLEAR as written; **independently reproduced exactly** | 31/30/27/15 (F2) |
| RS6 | Certificate semantics: external vertices odd with one end, never blank; holds even if the seed disconnects | SOUND | Replayed on concrete hosts (§3.3) |
| RS7 | K2 refinement: x ∈ N(r) \ T ⇒ second bank covers all 32 masks; otherwise d(r) = 4 and deleting r gives one even site | SOUND (bank reproduced) | The degree-4 argument is MR Thm 136 t = 4 |
| RS8 | Translation of survivors into D ∈ {∅, K2, P3, K3, C4} with root positions | SOUND | Checked case by case. Non-listed shapes (2K2, P3 with r at an end, K3 off r, C4 off r, …) all land on certified rows |
| RS9 | Isolated root: C − r ∈ {K5, K5−e, K5−P3}; the other five roots pass (D − s has no isolate ⇒ C − s subcubic ⇒ BS) | SOUND | |
| RS10 | Census: 66/396; 41; 32,661; 32,381 and 306/20/45/16; 51·32 = 1,632; 86 + 41 = 127; 107; 642 | SOUND | Recomputed (`census.py`, plus the count of 51 cores) |
| RS11 | Isolated-root descent (hold the approach path, H passes at y ⇒ B passes) | SOUND | Every Fan inequality checked: the receiver misses T; the only blank outside T is the receiver; the donor is untouched |
| RS12 | "The argument neither needs nor transfers 2-connectivity…" and the Thm 144 caveat | SOUND | Correctly hedged |
| RS13 | Example K_{m+6} minus the 5 edges r–T | SOUND | Parities, minimum degree m, no matching cut |
| RS14 | C4 interaction: profile list {∅, abe, abcd, acde, bcde, abcde} via the bank and the cde elimination | **see §3.4** | Parity identity #acde + #abcde odd: SOUND |
| RS15 | Joint failure ⇒ both pairs twins ⇒ automorphisms ⇒ all four cycle roots fail; hubs pass; x ≡ y ≡ p ≡ q ≡ 1 + f | SOUND | |
| RS16 | "Small odd neighbourhoods" (2-connected hosts; ≥ 3 odd neighbours; C-universal ⇒ ≥ 5) | UNCLEAR (external inputs absent); arithmetic SOUND | Applies to 2-connected hosts only, as stated |
| RS17 | Pendant identity p2(A + xry, r) = 1 + p(A + xr) = 1 + p2(A, x) | SOUND | 13,452 labelled inputs reproduced |
| RS18 | Provenance: verify.sh, extract.py, Lean, JSON banks | UNCLEAR | Not in the collection (F6) |

### 1.2 INC — six-even-incidence

| # | Step | Verdict | Note |
|---|---|---|---|
| I1 | Thm 1(1) = shape reduction + Lemma 2 | SOUND given RS and Lemma 2 | |
| I2 | Lemma 2 (exactly k paths; r, two others doubled, three blank, odd vertices once) | UNCLEAR (trees absent); **no counterexample** | All 88 eight-vertex instances; 150 random 10-vertex and 80 random 12-vertex instances (F7) |
| I3 | Seed rules (0 or 2 even sites, leaf trick, componentwise) | SOUND | |
| I4 | "Virtual two ends" trick for isolated r | SOUND | The slot is spent at the first r-donor offer. Before that, r has an actual end whenever it has a present edge, so blank counts agree. Final value 2 < d + 2 forces the slot to be spent |
| I5 | Four-edge example (K6, S(x) = {a, b}) | SOUND | All four inequalities rechecked: (1,0), (2,1), (3,2), (1,0) |
| I6 | Thm 1(2): a C-universal site has an odd neighbour x with 1 ≤ \|S(x)\| ≤ 2 | SOUND | Every residual D has an isolated vertex |
| I7 | Thm 1(2), isolated root via descent; y has ≤ 2 core neighbours, every residual shape needs ≥ 3 | SOUND | |
| I8 | Inputs listed as "Lovász, Fan, two tables" | GAP (citation) | The shape reduction also uses BS Thm 13 (F8) |
| I9 | §4 "a separate argument handles complete cores whose clique edges separate the ports" | UNCLEAR | Absent (F9) |
| I10 | Circulant family "remains open" | SOUND as an example; claim superseded | n_h = s is odd, so 6CL Thm 1 closes it (F9) |
| I11 | Obstruction to dropping the witness location (pendant u, r, y) | SOUND | |

### 1.3 6CL — six-clique-prescribed-ends

| # | Step | Verdict | Note |
|---|---|---|---|
| C1 | Lemma 2 statement = Fan [JCTB 2005, Lemma 3.3 + 3.4] | **SOUND / MATCHES verbatim** | See §2 (F10) |
| C2 | Lemma 2's own proof (closure R, injection) | SOUND, terse | "A chain … leads to a path avoiding v" leaves the chain selection implicit. Fan's backward-uniqueness argument fills it (F10) |
| C3 | Lemma 3 (insert an even F by shortest-cycle peeling and arc transfers) | SOUND | Checked: the receiver never sees w before the last step; the triangle case is fine |
| C4 | Lemma 4 (pair rectangles) | SOUND | All eight transfers re-derived, including when xy is present |
| C5 | §4 representatives: 5 paths, D0, D1, D2, 16 transfers, final path | SOUND | Simulated (`sim6cl.py`). The 24-edge display is exact; the (supply, blanks) table is reproduced exactly under worst-case representative–representative adjacency; the final end vector is (2,0,2,2,0,0 \| 1⁶) |
| C6 | Thm 1 | SOUND | CP-SAT: all 16 classes of even F at m = 6 × all 20 triples; 60 random m = 8 instances (14 vertices) |
| C7 | Sharpness example (57 edges > 55) | SOUND | |
| C8 | Cor 5 | SOUND, terse | "The same argument with the remaining two ports at a triple" should be written out (F11) |
| C9 | Thm 6 small neighbourhoods (a ∈ A(x) ⊆ {a, b}; r ∈ A(x), \|A\| ≤ 3) | SOUND | Inequalities (0,1,2 blanks; 5 > 4; 4 > 3; 3 > 2) rechecked |
| C10 | Thm 6 congruences n_r ≡ 1 + e (+ b_r), n_i ≡ 1 + d_H(i) (+ b_i) | SOUND | Re-derived |
| C11 | Thm 6 counts: 34; 1,024; 3,213 (1, 15, 105, 440, 1,140, 1,512); 256 circuits, 10 of them two triangles; 31,442 rooted classes; 3,290,112 | SOUND | Recomputed, rooted classes by Burnside (`count6cl.py`) |
| C12 | Thm 6 finite records (34 + 31,442 records, 402,701 branches) | UNCLEAR (absent); **no counterexample** | All 372 eight-vertex instances; 150 random 10-vertex and 80 random 12-vertex instances (F12) |

### 1.4 D10 — degree-ten-marked-root

| # | Step | Verdict | Note |
|---|---|---|---|
| D1 | Mixed case: disjoint edge/non-edge pairs (Kneser K(5,2) is connected) | SOUND | |
| D2 | Seed (delete w, hold ab, insert cd ⇒ only e even ⇒ k − 1 exact paths) | SOUND | |
| D3 | Carrier cut, the three ownership bullets, the six-set interchange, parity ⇒ ≥ 2 singles | SOUND | All three bullets checked, including singleton pieces |
| D4 | Reserve (t′, t, w, e) plus j ≤ 2 cycles ⇒ j + 1 paths, by Chu–Fan–Zhou Lemma 2.4 | GAP (citation); claim tested | The CFZ statement is unverifiable and A7 found conflicting paraphrases (≤ 6 vs ≤ 7). The note only needs \|V(P)\| + j ∈ {5, 6}. Random test: 600/600 (F13) |
| D5 | Independent case (shortest Q, satellites, degree drops, private leaf) | UNCLEAR | Depends on the four-edge-path/two-cycle "full tails" theorem, the "through-five-contact repair" and the two-member contact results through seven sites, none in the collection. Spot-checked geometric steps are SOUND (F14) |
| D6 | "This is the three-contact argument of Marked Proposition 139" | GAP (citation) | Prop 139 assumes 2-connectivity, while the comparison may be disconnected. The note's own sketch (Pyber/Lovász seed, one single, at most one cycle) is self-contained and SOUND (F15) |
| D7 | Clique case: finite selection lemma (2,620 partitions) | UNCLEAR | Enumeration absent |
| D8 | Clique case physical return | SOUND given D9 and the ≤ 7-contact path–cycle results | |
| D9 | Five-edge path + two cycles with ≥ 2 off-path spokes ⇒ 3 paths | UNCLEAR (tables absent); **tested** | See §3.6 |
| D10 | Sharpness example on Z7 | SOUND | p = 4 computed (19 edges > 18) |
| D11 | Bridge 2:3 and genuine-bridge sections | not audited in depth | Not needed for the headline claim |

### 1.5 MR — Thm 144 and Cor 138

| # | Step | Verdict | Note |
|---|---|---|---|
| M1 | Equivalence statement (leafy floor ⇔ restricted deletion test) | SOUND | |
| M2 | r ∈ T: "Shaik [25, Cor 1.2] gives k paths" | GAP (unrefereed input) | Fix: BS Thm 13. B has 4 even vertices, so it is not SET (F16) |
| M3 | "By Cor 106 with mark r, at least two vertices of K have degree four" | GAP (Shaik via Cor 106) | Fix: BS on W if K is subcubic. With exactly one universal: Lemma 133 (FHZ + M/P/C table, connectivity only) or the seven-site one-universal bank. BS alone is **not** enough (F17) |
| M4 | r sees 1 or 2 members of T; bridge case; spokes all bridges | SOUND | Cor 106 uses here have ≤ 4 unmarked even vertices, so BS suffices: the leaf at the mark has no even neighbour and the graph is not SET (F18) |
| M5 | Pendant blocks; ≥ 3 leaves; two leaves on one support (Thm 123); two supports (Cor 129) | SOUND given Thm 123 and Cor 129 | Thm 123 and Cor 129 inherit the Lemma 121 tables (F19) |
| M6 | Matching cut (Lemma 6; Cor 106 with ≤ 4 unmarked) | SOUND modulo Lemma 6; BS suffices | |
| M7 | Separating pairs via the Thm 113 substitutions | SOUND by reference (A2) | |
| M8 | J is 3-connected; only z even; d(z) = 6 | SOUND | |
| M9 | d(r) ≥ 8 from Cor 138 + Prop 139 | SOUND given Cor 138 | |
| M10 | Cor 138 | UNCLEAR (inherited) | Thm 136 checked in full (all t), SOUND. Prop 134 SOUND given Cor 129 and Lemma 133. Thm 135: the Fan part is SOUND, but the 9,330-entry geometric table is absent. Thm 137: the 235-case supplement is absent (F21) |
| M11 | Lemma 133 hypothesis "two-connected" | not an error | The proof uses only connectivity (Section 2.1 needs only "G connected"; the table states "no connectivity assumption"). Useful for M3 (F20) |

---

## 2. Fan's addible-edge lemma: statement against use

Primary text (Fan, JCTB 93 (2005) 117–125, p. 120):

> **Definition 3.1.** D(v) denotes the number of the nontrivial paths in D that have v as an end.
>
> **Definition 3.2.** Let a be a vertex in a graph G and let B be a set of edges incident with a. Set H = G \ B. Suppose that D is a path-decomposition of H. For any A ⊆ B, say that A = {ax_i : 1 ≤ i ≤ k}, we say that A is addible at a with respect to D if H ∪ A has a path-decomposition D* such that (a) |D*| = |D|; (b) D*(a) = D(a) + |A| and D*(x_i) = D(x_i) − 1; (c) D*(v) = D(v) for each v ∈ V(G) \ {a, x_1, …, x_k}.
>
> **Lemma 3.3.** Let a be a vertex in a graph G and let H = G \ {ax_1, ax_2, …, ax_s}, where x_i ∈ N_G(a). Suppose that D is a path-decomposition of H. Then either (i) there is x ∈ {x_1, …, x_s} such that ax is addible at a with respect to D; or (ii) Σ_{i=1}^{s} D(x_i) ≤ |{v ∈ N_H(a) : D(v) = 0}|.
>
> **Lemma 3.4.** Let G be a graph and ab ∈ E(G). Suppose that D is a path-decomposition of H = G \ {ab}. If D(b) > |{v ∈ N_H(a) : D(v) = 0}|, then ab is addible at a with respect to D.

**Comparison with the uses.**
- 6CL Lemma 2, INC §2, RS ("grouped Fan addition"), MR (book paragraph p. 131, Lemma 126, Thms 135/144) all use the contrapositive of 3.3:
  > if Σ_{donors} b(y) > #(present neighbours of the receiver with no end), some offered edge is added toward the receiver, moving one end from that donor.
- The neighbourhood is N_H, the *current* graph: other still-held edges are absent, and the offered edges are absent.
- The donors are distinct non-neighbours.
- **This MATCHES.**

**Points a referee should still see stated.**
1. Only a donor with D(x) ≥ 1 can be returned, since Fan's pairs (x, P) need an end at x. A certificate that offers a zero-end donor is harmless, because that branch never occurs.
2. Fan's proof of 3.3 replaces each P_i by (P_i \ {b_{i+1}a}) ∪ {b_i a}. It says nothing about the case where one path is entered twice, from its two ends. The modifications then compose to a single simple path, and 6CL's proof says so explicitly.
3. Lemma 3.3 gives no control over *which* donor is returned. Every certificate in RS, INC and 6CL accordingly branches on all offered donors.

**Computation** (`fan_proc.py`):
- 3,000 random instances: n = 5–11, random decompositions, receiver a, donor set X of 1–5 non-neighbours with Σ D(x) > Z(a).
- I ran Fan's own sequence construction, applied the edge substitutions and verified the output: a decomposition of H + ax with |D*| = |D| and the exact end-vector change.
- It succeeded in **every** instance: 826, 865, 676, 409 and 224 instances with s = 1, …, 5.
- The earlier exact (CP-SAT) existence test (`fan_test.py`) was too slow on the loaded machine. It was superseded by this constructive test, which is strictly stronger.

---

## 3. Computations

### 3.1 Rooted test on all connected 8-vertex graphs with six even vertices (`c1d.py`)

For every graph in `data/conn8.g6` with exactly six even vertices, and every even root r, I decided feasibility of "≤ 4 paths with ≥ 2 ends at r":
- with a compact circuit-based CP-SAT model (`circ.py`, self-tested on K3–K8);
- verifying every returned partition with `pathnum.verify_partition`;
- re-checking any infeasibility with the path-enumeration model.

I also recorded whether 3 paths already suffice ("slack") or not ("tight").

**Result:** [FILLED BELOW]

### 3.2 Independent re-derivation of the RS certificate banks (`fancert.py`, `sevensite.py`, `bank2.py`)

**Model.**
- Local record: T = {a, b, c, d, e} (even in W), u (= r), v (= ℓ), with the known local edges.
- External vertices are odd with exactly one end, never blank, never held.
- A seed holds H ⊆ local edges so that exactly one local vertex is even (W-setting). Lovász then gives k paths with exact ends.
- B-setting variant for the second bank: 0 even sites, or 2 even sites with the leaf trick at a site that keeps a local edge.
- Moves: a receiver x and a donor set S of held neighbours with Σ b > Z(x), branching on every donor.
- I took only inclusion-minimal donor sets. This is WLOG, since a superset only adds branches.
- Search: AND–OR with memoisation, **exhaustive over all held sets H**. If a contact set is reported uncertified, no certificate of this kind exists.

**Results.**

| Core on T | Certified contact sets A ≠ ∅ | Surviving (no certificate) | RS / MR printed |
|---|---|---|---|
| K0 (book) | 31 | none | none ✓ |
| K1 (book + cd) | 30 | abe | abe ✓ |
| K2 (book + cd, de) | 27 | abd, abcd, abde, abcde | same ✓ |
| K3 = K5 | 15 (all \|A\| ≤ 2) | all 16 sets with \|A\| ≥ 3 | same ✓ |
| one universal: rim ∅, K2, 2K2 (= M), P3, K3, P4 (= P), C4 (= C) | 31 each | none | "cover all such A" ✓ |

- Second bank (K2, A = abcd and A = abde, x ~ r): **all 32** x-masks certified, matching RS.
- Logs: `bank1_K.out`, `bank1_U.out`, `bank2_K2.out`.

Consequences:
- The shape theorem's case analysis (RS3, RS5, RS7) is confirmed independently of the missing banks, modulo Lovász, Fan 3.3/3.4 and BS 13 (all published and checked).
- The 66-pattern list is *optimal* for single seven-site certificates.

### 3.3 End-to-end replay on concrete hosts (`replay_cert.py`)

Method:
1. Take 8 certificates: U_M/a, U_C4/abcde, U_P4/bd, K0/ac, K1/abcde, K2/abc, K3/ab and K3/c.
2. For each, build two random concrete hosts W of 11 and 13 vertices. Exterior vertices are odd, with arbitrary exterior adjacency, including edges to T, u and v.
3. Obtain the Lovász-type seed with the exact end vector by CP-SAT.
4. Follow the certificate tree, applying Fan's own construction at each offer and taking the branch of the donor actually returned.
5. Verify the final decomposition.

**16/16 replays produced verified floor partitions** of W (5 and 6 paths). This validates the claim that the local certificates work "for arbitrary outside degrees and even if holding the edges disconnects the seed".

### 3.4 C4 profile claim (`k1x.py`)

Setup: K1 core with N_T(r) = abe. The exterior x has N_T(x) = S and xr ∈ {0, 1}. That gives 64 masks, or 36 orbits under (a b)(c d).

The question is which masks lack an unconditional seven-site certificate (W-setting, with B-setting as fallback). RS claims the masks without a certificate project to {∅, abe, abcd, acde, bcde, abcde, cde}, and that every mask distinguishing c, d is certified.

**Result:** [FILLED BELOW]

### 3.5 Exact end-vector claims

| Claim | Instances | Failures |
|---|---|---|
| INC Lemma 2: k paths, odd ends 1, r = 2, two other U = 2, three U = 0. Shapes ∅, K2, P3 (middle), K3, C4 (on cycle), some x with \|S(x)\| ∈ {1, 2} | all 88 rooted instances from conn8; 150 random on 10 vertices; 80 random on 12 vertices | 0 |
| 6CL Thm 1 (every x sees exactly 5, n_h odd, any triple doubled) | m = 6: all 16 iso-classes of even F × 20 triples; m = 8: 60 random | 0 |
| 6CL Thm 6 (U = K6, every x sees ≤ 5, every r) | all 372 eight-vertex instances; 150 random on 10 vertices; 80 random on 12 vertices | 0 |

The 10- and 12-vertex hosts were generated with random exterior structure and parity repaired by exterior edges (`gen.py`). These are falsification tests of the *precise endpoint vectors*, which are not implied by Gallai's conjecture.

### 3.6 D10 path-plus-cycles lemmas (`pathcycle.py`)

The cycles are random, through w, edge-disjoint, and biased to intersect P heavily.

| Claim | Instances | Failures |
|---|---|---|
| P = (t′, t, w, e) with j ∈ {1, 2} cycles through w ⇒ j + 1 paths (the CFZ Lemma 2.4 use) | 600 | 0 |
| Four-edge path with w internal + 2 cycles ⇒ 3 paths | [FILLED BELOW] | |
| Five-edge path, w third or fourth, + 2 cycles, ≥ 2 of the 4 spokes off P ⇒ 3 paths | [FILLED BELOW] | |
| Sharpness: Z7, steps 1 and 2 cycles, P of step 3, w = 6 | p = 4 | (as claimed) |

The early "FAIL" printed in a first run was a solver timeout on the loaded machine. Rechecked: p = 3. The script now separates timeouts.

### 3.7 Counts reproduced

- RS: 66/396; 41; 32,661; histogram 32,381/306/20/45/16; 51 labelled cores with ≥ 2 universal vertices; 13,452.
- 6CL: 3,213 independent subsets with sizes 1/15/105/440/1,140/1,512; 1,024 zero-sum families; 256 circuits; 10 two-triangle circuits; rooted classes 34/238/1,246/4,540/11,068/14,316 = 31,442; labelled 3,290,112.

All match.

---

## 4. Findings

**F1 (RS3, UNCLEAR → resolved computationally).**
- The text says "the one-universal rim certificates cover all such A" without saying which cores they cover.
- MR's corresponding table (Lemma 133, boundary-even.json) covers only M, P, C. The other four one-universal cores go through Fan–Hou–Zhou, which RS does not list among its inputs.
- My exhaustive search certifies all seven one-universal cores for every A in the seven-site setting. So the claim is true.
- *Fix:* publish the 217 certificates, or say "FHZ for the four bowtie-free cores, and the M/P/C table".

**F2 (RS5).** The first bank is absent, but the table is reproduced exactly and is optimal for the method. *Fix:* include the bank, or cite this audit's search as an independent replay.

**F3 (RS7).** The second bank is absent; reproduced: all 32 masks.

**F4 (RS14, C4 profile list).** [FILLED BELOW]

**F5 (RS16).** The "small odd neighbourhoods" consequences are for *2-connected* hosts (correctly stated) and rely on external proofs not in the collection. UNCLEAR, low impact.

**F6 (RS18, INC, 6CL, D10).** None of verify.sh, extract.py, the Lean files, the JSON banks or the C++ checkers is in the collection.

**F7 (INC Lemma 2).** The trees (18 + 29 representatives) are absent. The statement passed every falsification test (§3.5). UNCLEAR, low risk.

**F8 (INC, citation GAP).** INC uses the RS shape reduction, which invokes Botler–Sambinelli Thm 13 (and FHZ, see F1). Neither is in INC's bibliography or input list. *Fix:* add them.

**F9 (INC §4).**
- The "separate argument" for complete cores whose fifteen clique edges separate the ports is absent: UNCLEAR.
- The circulant family is claimed open, but it is a case of 6CL Thm 1: every exterior vertex sees exactly five clique vertices and n_h = s is odd. *Fix:* cross-reference 6CL.

**F10 (6CL Lemma 2 / Fan).**
- The statement MATCHES Fan's Lemma 3.3 verbatim (§2).
- The proof's last step is terse: "A chain of distinct reached vertices therefore leads to a path avoiding v". *Fix:* take the chain backwards from the path avoiding v, using Fan's uniqueness of (P_i, b_i) given b_{i+1}. This also shows the reached vertices are distinct.

**F11 (6CL Cor 5, minor GAP of exposition).**
- The triple-type rows ("the same argument with the remaining two ports at a triple completes its two-spoke seed row") and the requirement "the other blank is absent when a blank is introduced last" are only sketched.
- They follow from Lemma 4's two rectangles. *Fix:* write out the triple-type rectangle with its inequalities.

**F12 (6CL Thm 6).** The finite records are absent (Lean covers only the odd-type portion). The hand parts and all counts check out, and the statement passed all tests. UNCLEAR, low risk.

**F13 (D10, citation GAP).**
- "Chu–Fan–Zhou … Lemma 2.4 … since j + 4 ≤ 7": the exact CFZ hypothesis is unverifiable here, and A7 §5c reports conflicting paraphrases (≤ 6 vs ≤ 7).
- The note only needs |V(P)| + j ∈ {5, 6}, so the weaker ≤ 6 form suffices.
- 600 random instances of exactly this configuration passed.
- *Fix:* quote the lemma, or prove the j ≤ 2, |P| = 4 case directly. It is a small finite check because w has degree ≤ 6 in the union.

**F14 (D10 independent and clique cases).** These depend on prior finite theorems and enumerations that are not in the collection:
- the full-tails four-edge theorem;
- the two-member contact results through seven sites;
- the 2,620-partition selection lemma;
- the 11/38/69 and 9,990/97,592/1,249,220 tables, and the 262 colourings.

UNCLEAR. The geometric steps I checked are sound (shortest-Q minimality, satellite disjointness, the degree-6 comparison).

**F15 (D10, citation GAP).** "This is the three-contact argument of Marked Proposition 139": Prop 139 is stated for 2-connected B, but the comparison here may be disconnected. The note's own sketch is complete and sound:
- Pyber componentwise, or Lovász after holding hm;
- one single extension and at most one cycle;
- cycle + edge ⇒ 2 paths, with the odd degree at w giving the second end.

*Fix:* drop the citation, or note that only connectivity is used.

**F16 (MR Thm 144, r ∈ T step).** Shaik's unrefereed Cor 1.2 is used where BS Thm 13 suffices: B is connected of even order with four even vertices, Δ ≤ 3, and is not SET. *Fix:* replace [25] by [7, Thm 13]. This agrees with A7.

**F17 (MR Thm 144, "By Corollary 106 with mark r, at least two vertices of K have degree four").** This inherits Shaik through Cor 106. BS alone does not suffice when K has exactly one universal vertex (A7 is right on that point). But Shaik *can* be removed:
- K subcubic: BS Thm 13 on W. W[T] = K has 5 vertices, so W is not SET.
- Exactly one universal: MR Lemma 133. Its proof uses only connectivity: Section 2.1's FHZ marked bound for the four bowtie-free cores, the boundary-even M/P/C table, and the shortest-path transfer. The 2-connectivity in its statement is unused.
- Alternatively, the seven-site one-universal bank applies. ℓ is a T-free odd vertex, so the shortest path from ℓ supplies (u, v). It is recomputed and replayed here.

*Fix:* replace the Cor 106 sentence by "by BS [7, Thm 13] and Lemma 133 (whose proof uses only connectivity)". Thm 144 then no longer depends on [25]. The same replacement works for the Thm 114 remark at p. 129 (MR line 6643). This corrects the status map's "Botler–Sambinelli probably suffices instead": BS suffices only together with FHZ + Lemma 133, or the bank.

**F18 (MR Thm 144, remaining Cor 106 uses).**
- In the 1–2-contact step and the matching-cut step, the unmarked even set has ≤ 4 vertices.
- BS suffices there. The private-leaf graph L_A(G) is not SET, since each leaf has no even neighbour. When A = ∅, BS gives Gallai's ceiling and the two-leaf trick avoids SET.
- *Fix:* cite BS.

**F19 (MR Thm 144, inherited dependencies).**
- Thm 123 (three ends at an odd support) and Cor 129 (degree-two vertex) rest on the FHZ marked bound plus the Lemma 121 tables, which are absent.
- Thm 113's substitutions were audited in A2.
- UNCLEAR by inheritance.

**F20 (MR Lemma 133).** Not an error: the hypothesis is stronger than the proof needs. This matters for F17 and for reuse on merely connected hosts.

**F21 (MR Cor 138).** UNCLEAR by inheritance:
- The proof is a four-line citation chain.
- Thm 136: I verified all four cases t = 0, 1–2, 3, 4, including the SET sub-case (P = ads or as, and the restoration of ac), and the t = 0 two-fan argument. SOUND, modulo Lemma 121.
- Thm 135: the Lovász/Fan restoration is SOUND, but the existence of P and Q is delegated to a 9,330-entry table that is absent.
- Thm 137: rests on the 235-case supplement, which is absent.

**F22 (status map).** Corrections to the program summary:
1. "Thm 144 … Botler–Sambinelli probably suffices instead" → see F16–F18.
2. "INC Lemma 2 … Two independent computations and a Lean certificate": absent, but the statement is tested.
3. The RS banks are now independently reproduced, so RS's shape theorem no longer rests on missing data.

---

## 5. Recommended fixes (priority order)

1. **MR Thm 144:**
   - replace [25, Cor 1.2] by BS [7, Thm 13] (r ∈ T);
   - replace "By Corollary 106" by "by BS [7, Thm 13] and Lemma 133 (connectivity suffices)";
   - cite BS in the two remaining Cor 106 uses.

   Thm 144 is then Shaik-free.
2. **MR Lemma 133:** weaken the hypothesis to "connected".
3. **RS:** publish the three banks, or attach this audit's exhaustive search (`A6-scripts/sevensite.py`, `bank2.py`, `k1x.py`). State which one-universal cores the rim certificates cover.
4. **INC:** cite Botler–Sambinelli (and FHZ if F1 is resolved that way); cross-reference 6CL Thm 1 for the circulant family; supply or remove the "separate argument".
5. **6CL:** expand Lemma 2's chain step (Fan's backward uniqueness) and Cor 5's triple rectangles.
6. **D10:** quote CFZ Lemma 2.4 exactly, or replace it by a direct finite check; drop or qualify the Prop 139 citation; include the selection-lemma and five-edge tables.
7. **Cor 138:** include the Thm 135 and Thm 137 tables, or regenerate them. These are now the main unreplayed inputs of the d = 6 frontier, together with Lemma 121.
