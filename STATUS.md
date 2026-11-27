# Gallai path decompositions: where the project stands

*Orientation document. Written 2026-11-26 from a full read of the 31-paper collection in `gallai/` (942 pp.) and a literature check.*

Detailed reader notes, with theorem numbers, are in `research/notes/`.

---

## 1. Bottom line

- **The full conjecture is still open, in the literature and in this collection.** Every paper here says so. No paper claims an unconditional proof.

- **The collection proves an equivalence spine.** Gallai is reduced, by computer-free two-directional arguments, to two rooted tests on 3-connected graphs (marked-reduction Thm 114), together with several other equivalent forms.
  - The tests are graded by the degree d of the deleted vertex.
  - They are closed for small d.
  - The first open case is the **two-end test at d = 6**. It is equivalent to the floor bound for odd-order graphs with a leaf and exactly five even vertices (MR Thm 144).
  - d is unbounded, and each new value of d has so far needed its own large, computer-assisted case analysis.

- **If the collection's claims survive verification, it moves the published frontier substantially.** It settles:
  - the odd semi-cliques exactly;
  - the floor bound for graphs whose blocks have maximum degree ≤ 7 (≤ 9, conditionally on computation);
  - exact results above the Dirac threshold;
  - many E-subgraph classes;
  - near-complete graphs.

- **The main risk is verification, not ideas.**
  - None of the code, Lean files or certificate banks the papers cite is in the collection.
  - Several load-bearing steps rest on large enumerations.
  - One formerly load-bearing citation, an unrefereed 2026 preprint (Shaik), has been removed (`manuscripts/bs-prescribed`). Another is a very recent theorem (Javadi–Miralaei).
  - The index's readiness caveat understates what depends on unreplayed computation (§6).

---

## 2. The published frontier (literature check, Nov 2026)

Gallai (1966; Lovász 1968): every connected graph on n vertices has p(G) ≤ ⌈n/2⌉. It is Erdős problem #583 and is open.

| Direction | Best published / preprint result |
|---|---|
| Parity (E-subgraph = graph induced by even vertices) | ≤ 1 vertex (Lovász); forest (Pyber); each block triangle-free with Δ ≤ 3 (Fan); further triangles (Fan–Hou–Zhou; Botler–Sambinelli); clique K_r with r ≤ 15 giving ⌊n/2⌋+1 (Chu–Fan–Zhou) |
| Max degree | Δ ≤ 5 (Bonamy–Perrett 2019); floor at Δ ≤ 6 with independent degree-6 vertices (Chu–Fan–Liu) |
| Width | treewidth ≤ 3 (Botler–Sambinelli–Coelho–Lee); treewidth ≤ 4 (Lu–Yi, DM 2024) |
| Minor-closed | planar (Blanché–Bonamy–Bonichon); **K5-minor-free** (Zhang–Liu–Hong, arXiv 2611.21673, 14 Nov 2026) |
| Degeneracy | 2-degenerate (Anto–Basavaraju, DMTCS 2025) |
| Odd semi-cliques | p ≤ (4n+6)/7 (Chu–Fan–Zhou, DM 349, 2026) |
| Dense | p ≤ n/2 + o(n) for linear min degree (Girão–Granet–Kühn–Osthus); quasirandom (Glock–Kühn–Osthus) |
| Computation | every connected graph through order 11, ceiling bound (community project; order 12 running) |
| Strong form | Bonamy–Perrett question: floor ⌊n/2⌋ outside odd semi-cliques. Botler–Sambinelli dichotomy conjecture. |

A related problem was recently claimed solved: the Erdős–Gallai cycle decomposition conjecture (O(n) cycles and edges; J. Kim, arXiv 2610.07840, Oct 2026). It is a different conjecture.

---

## 3. What the collection does: the architecture

### 3.1 Exceptional family: settled

**Odd semi-cliques** are K_{2k+1} − H with e(H) < k. For them p = k+1 exactly, at every order.
- Source: odd-semi-clique-boundary Thm 4; the September note.
- Method: plant a path Q of length k − e(H), then apply the Javadi–Miralaei rainbow Hamilton decomposition (Wu's conjecture) to H ∪ E(Q).
- Consequence: the Botler–Sambinelli dichotomy is equivalent to the Bonamy–Perrett question.

### 3.2 The equivalence spine

All of these are computer-free, two-directional and class-level. Each says: "Gallai ⇔ …".

| Form | Statement | Source |
|---|---|---|
| Rooted private leaf | ∀ connected H on 2k vertices, ∀ r: p(H + leaf at r) ≤ k | root-endpoint-costs §1; separating-pairs §1 (doubling: p(double) = 2p(H^r) − 1) |
| Marked + three-end | marked bound q(F,S) ≤ ⌊(\|F\|−\|S\|)/2⌋ on 2-connected F, and three ends at odd x in tight odd 2-connected J | MR Thm 1 |
| 2-connected, no matching cut | F₂(B,x) ≤ k (even order, even x) and F₃(B,x) ≤ k+1 (odd order, odd x) | MR Thms 7, 57, 59 |
| **3-connected deletion tests** | (i) z the unique even vertex of 3-connected J: J−z has ≤ (\|J\|−1)/2 paths with ≥ 2 ends at any r ∈ N(z). (ii) z, r the only even vertices and adjacent: ≤ \|J\|/2 paths with ≥ 3 ends at r | **MR Thm 114** (via separator Thm 113) |
| Restricted roots | d(r) = 2 or ≥ 3 even neighbours; ≥ 2 even neighbours of degree ≥ 6 | MR Thm 145; REC Cor 13.8 |
| Single edge pair | p(H^{xy}) ≤ k+1 ⇒ p(H) ≤ k, with xy on an even cycle | MR Thm 162, Cors 163–164 |
| Leaf and cut-vertex floors | floor on graphs with a leaf / with a cut vertex / 2-connected D with 1–2 leaves | OSB Thms 46, 48 |
| Doubles | ceiling on bridge-doubles and diamond-doubles | OSB Thm 50; MR Thm 59 |
| Dense regime | Gallai restricted to large even N with ≤ CN missing edges, for any fixed C | OSB Cor 44 (so the dense linear regime is as hard as Gallai) |
| Bandwidth automata | for every b, every cycle mean of a finite automaton is ≤ 1/2 (decidable for each fixed b) | even-degrees Cor 21 |

### 3.3 Structure of a minimal counterexample

- **separating-pairs, Thm 10.16 and §§12–13.** At the first failing even order, either:
  - there is a 2-connected odd **Bonamy–Perrett witness**: no matching cut, ≥ h+1 missing edges, p > h; or
  - every failing host is 2-connected, **6-edge-connected**, has no matching cut, and has **δ ≥ 6**. Eulerian failing hosts have δ ≥ 10.

  The odd witness is restricted too (≤ 1 vertex of degree 2, ≤ 1 cubic vertex, quintic vertices have only odd neighbours). Odd witnesses with δ ≥ 4 and no degree-2 or cubic vertex are not excluded.
- **root-endpoint-costs.** A smallest failed rooted host is one block plus at most one leaf, and its cuts have size ≥ 4. If triangle-free, it has ≤ 1 quartic vertex, and a cubic vertex forces δ ≥ 6 elsewhere and d(z) ≥ 8.
- **marked-reduction.**
  - Residual cycles in a cycle-minimum mixed partition meet each partner in ≥ 8 vertices (Thm 3).
  - Matching bonds bisect (Thm 55).
  - In the d = 6 test: δ(B) ≥ 5, even vertices have degree ≥ 6, and the core is restricted to K1, K2 or K3 on T (Cor 138, §19).

### 3.4 Classes settled by the collection (conditional on verification)

- **Block degree.** Every 2-connected block has Δ ≤ 7 gives the floor outside odd semi-cliques, plus the marked bound (block-degree Thm 3). Cut-vertex degrees are unrestricted.
  - This already goes beyond Bonamy–Perrett (Δ ≤ 5) and Chu–Fan–Liu (Δ ≤ 6 with independent degree-6 vertices).
  - Δ ≤ 8, Δ ≤ 9, cutwidth ≤ 8, and the hereditary density families of Thm 7 depend on **unreplayed** computation (§6).
- **Cycle conditions.** Every cycle has ≤ 3 vertices of block-degree ≥ 6 (MR Thm 2). Cycle–path pairs share ≤ 7 vertices (MR §5–7).
- **E-subgraph classes** (root-endpoint-costs Thm 13.20, 16.1, Cor 16.2).
  - Triangle-free components with ≤ 2 sites of E-degree ≥ 4; ≤ 3 at girth 5; ≤ 4 at girth 6; ≤ 2·3^t − 2 at girth 6t+1.
  - K_{s,m} blocks, 2 ≤ s ≤ 5.
  - K_{4,m} with the rooted bound.
  - These are incomparable with Fan, and strictly stronger than Fan on single-block components.
- **Dense, exact** (separating-pairs §14). At δ ≥ (1/2+ε)n and large n, every bounded endpoint profile is realised. So Gallai and Bonamy–Perrett hold exactly there, the odd semi-cliques are the only floor exceptions, and the same holds for robust expanders.
  - Near-half failures lie within o(n²) of K_{n/2,n/2}.
  - Bipartite graphs with δ ≥ (1/2−γ)n are settled.
- **Near-complete graphs** (OSB).
  - At large n: ≤ 4n − 20007 deletions; Δ(H) ≤ k/100; ≤ n²/6000 deletions with δ conditions.
  - At all k with k ≥ 6x: any k + x deletions.
- **High girth** (even-degrees Thm 7). Girth > 2⌊(Δ−1)/2⌋ + 5 gives the floor.
- **Asymptotic** (even-degrees Thm 1). p ≤ n/2 + 3n/√(d+1) when all even vertices have degree ≥ d.
- **Fractional** (fractional-paths). p_f ≤ n/2 always, via Li's perfect path double cover. So Gallai is purely an integrality problem, but the integrality gap can be about n/3, so rounding alone cannot work.

### 3.5 The frontier inside the collection

**(a) Two-end test at deletion degree 6 (six even vertices).** Equivalently, the floor bound for odd-order graphs with a leaf and five even vertices. The Nov 26 studies close large parts of it:

- the core shapes reduce to D = K6 − C ∈ {∅, K2, P3, K3, C4}: 66 patterns for a fixed root (six-even-root-shapes);
- odd vertices with 1–2 even neighbours (six-even-incidence);
- odd-induced degree ≤ 3, and degree-≤ 5 vertices (four-exterior-neighbors, Part IV);
- a 4-regular odd part;
- a clique core with no full exterior vertex (six-clique Thm 6);
- C4 with degree-6 twins;
- a C-universal root with 5 odd neighbours (degree-ten note).

**What a failure must still look like:** every odd vertex has odd-induced degree ≥ 4 in one of a few residual configurations, and some odd vertex has degree ≥ 5.

**Open:**
- D = ∅ with full exterior vertices;
- D ∈ {K2, P3, K3}, with no shape-specific results;
- C4 with twins of degree ≥ 8;
- generic exterior degree ≥ 5.

Details: `research/notes/reader-six-even-program.md`.

**(b) Higher deletion degrees.**
- Two-end test, d = 8: only root degree 2.
- Two-end test, d ≥ 10: open.
- Three-end test: closed for d ≤ 8; d = 10 partial; d = 12–16 only with a hub.

**(c) Cycle absorption** (marked / block-degree route). Residual-cycle absorption is handled up to about 12 contacts by heavy enumeration. Unbounded contacts are handled only under block-structure hypotheses.
- The "m cycles through a vertex ⇒ m+1 paths" bound is known for m ≤ 8 and m = 12 (nearly spanning only).
- The consecutive-visit "degree-50" case is reduced, but its set-up is not in the collection.

**(d) The odd alternative.** This is the Bonamy–Perrett floor for 2-connected odd graphs with no matching cut and ≥ h+1 missing edges (separating-pairs Thm 10.16, alternative 1). It is strictly stronger than Gallai at odd order.

---

## 4. Distance to full unrestricted Gallai

The spine is a genuine reduction, but it reduces Gallai to statements that are, by design, equivalent to Gallai. Progress is measured by closing classes of the 3-connected tests. Three things stand between the current state and a proof.

1. **No argument is uniform in the deletion degree d.**
   - d = 4 is closed by a published theorem (Fan–Hou–Zhou).
   - d = 6 (two-end) is mostly closed, by about 20 separate papers and notes with large certificates.
   - d = 8 and d = 10 are barely started.

   A proof needs an argument that handles every d at once. Plausible sources are the endpoint-profile theory, where the dense side is already uniform, or an induction on d that does not grow in case count.
2. **Cycle absorption is uniform only in bounded contacts.** The residual-cycle obstruction at unbounded intersection size has no general mechanism.
3. **The two "global" alternatives.**
   - The odd Bonamy–Perrett witness must be excluded. This is a stronger statement than Gallai.
   - The near-half-degree regime near K_{n/2,n/2} is located but not closed. OSB Cor 44 shows the dense linear-deletion regime is as hard as the whole problem.

**A frank estimate.** The collection is a large, well-organised campaign with a credible reduction spine and many new partial results. As it stands it is not close to a proof of the unrestricted conjecture, because the remaining parameter (d, or contact size) is unbounded and the per-case cost is growing. Success needs a new uniform idea, and a verification effort before more breadth.

---

## 5. Paper catalog

| Folder / file | Pages | Role |
|---|---|---|
| **01-original-manuscripts** | | |
| fractional-paths | 20 | Integrality gaps p/p_f; denominators; composition laws; p_f ≤ n/2 |
| odd-semi-clique-boundary | 56 | Exact semi-cliques; near-complete floor at large n; equivalences (Thms 46, 48, 50, Cor 44) |
| even-degrees | 38 | n/2 + O(n/√d); high girth; bandwidth automaton ⇔ Gallai; four-even prescriptions |
| marked-reduction | 192 | **The equivalence spine** (Thms 1, 59, 113, 114, 144, 145, 162); deletion-degree results; cycle absorption to 8; cycles through a vertex |
| block-degree | 54 | Floor for blocks of Δ ≤ 7 (≤ 9 / cutwidth 8 conditional); hereditary classes |
| **02-november-25** | | |
| root-endpoint-costs | 157 | Rooted formulation; E-subgraph classes; smallest failed host; finite tests |
| separating-pairs | 177 | First-failure alternative; δ ≥ 6, 6-edge-connected; exact dense results (§14) |
| quartic-exterior | 25 | Finite reduction for exterior Δ ≤ 4 (N(k) doubly exponential; tests not run) |
| **03-november-26-papers** | | |
| cycle-and-contact | 17 | Twelve nearly spanning cycles give 13 paths; focal-pair contacts; conditional degree-50 case |
| degree-preserving-decompositions | 8 | 2^{C(r,2)} tree decompositions per degree class; forest-density sets |
| two-vertex-separators | 7 | Exact gluing formula at a 2-separator; private-leaf formula |
| **04-research-studies** (d = 6 frontier) | | six-even shapes, incidence, clique, exterior-degree and twin studies; see the reader notes |
| **05-technical-notes** | | degree-ten root, false twins, mixed vertices, dense exact counts, matched subcubic, degree-eight twins |
| **06-historical-context** | 9 | September odd-semi-clique note |

---

## 6. Verification status and risks

1. **No code, data or Lean is in the collection.** Every cited supplement is absent, the papers give no URL, and the September note has "[repository URL to be inserted]". Named files include:
   - `classify_eight.cpp`, `verify_nine.py`, `c8-pair-rows.tsv`, `check_thin_pairs.py`;
   - `referee/verify.sh`;
   - `FiveSiteFan.lean`, `ApexConnectivity.lean`, `DonorTable.lean`;
   - `three-site/verify.py`.
2. **The index's block-degree caveat is too narrow.** Thm 4 (holding the 25,003 three-path and 1,154 boundary cases) feeds Thm 5.
   - So degree 8, cutwidth 8 and all of Thms 7–13 also depend on it.
   - Degree 9 additionally rests on about 4.86M placements.
   - **Only Thm 3 (Δ ≤ 7) and Thm 2 avoid it.**
   - The paper itself claims an "independent replay" that the index says does not exist.
3. **External dependencies to confirm.**
   - **Javadi–Miralaei** (rainbow Hamilton decomposition, DM 349, 2026) is used more than 40 times, including the equality case of separating-pairs Thm 10.16. OSB cites a "Theorem 3.8" that does not exist in arXiv v1; it is Theorem 8.
   - **Shaik** (Hexagon preprint, Oct 2026, unrefereed) is **no longer needed**. MR uses Cor 106 only with ≤ 5 unmarked even vertices. That case (BP_5 with one universal vertex) is proved from Lovász + Fan in `manuscripts/bs-prescribed`, with Lean `five_even_floor`.
   - Check the Zhang–Liu–Hong and Chu–Fan–Liu ≤ 5-contact exception lists against the sources.
4. **Large-n results rest on an in-paper sketch.** The OSB §11.1 random degree-partition lemma is a sketch, and it is applied at √N log N discrepancy.
5. **Notation and extraction issues.**
   - e(G) means "missing edges" in several OSB theorems.
   - Overlines were lost in some statements.
   - Results are unnumbered in cycle-and-contact.
   - 4EX has three different "Theorem 1".
   - Some later notes supersede earlier ones without cross-citation.
6. **Authorship.** Every paper carries an AI-assistance declaration. The pace is very high: 942 pages dated Nov 23–26. Independent human or replayed-machine verification of the load-bearing steps should come before submission.

---


## 6a. Audit outcomes (updated 2026-11-26, evening)

Independent adversarial audits, with reports in `research/audit/` and fixes in `manuscripts/corrigenda/`:

| Audited part | Verdict |
|---|---|
| MR Thms 1, 7, 57, 59 (A1) | **sound**; wording gaps only |
| MR Thms 113, 114, 145, 162–164 (A2) | **sound**; no errors |
| SP doubling equivalence and the Thm 10.16 chain; Thm 12.28, Cors 13.5, 13.12 (A3) | **sound** modulo JM; two citation gaps |
| OSB Thm 4 and §15 equivalences (A4) | **sound** modulo JM; e(G) notation errors in statements (proofs fine); Cor 44 quantifier |
| block-degree Thm 3 (Δ ≤ 7) and Thm 2 (A5) | **sound**; **every enumeration independently replayed**; cited five-contact lemmas re-proved exhaustively |
| d6-frontier; endpoint-structure §§5–6, including the bridge reduction to BranchBase (A9) | **sound**: no error in any theorem or proof; 13 gaps fixed; one abstract error fixed |
| JM repair: new proof of JM Thm 8, transfer lemma, Thm 7 (A10) | **sound**: no error, no substantive gap; independent brute-force checks agree |
| bs-prescribed: five-even floor bound, Shaik removal (A11) | **sound**: scope verified against every Cor 106 use; certificates independently checked |
| missing-move; endpoint-structure §7 (flower, barriers, receipt-or-flower) (A12) | **sound**: no mathematical error; key computations independently reproduced |
| endpoint-min-max: cut selection Thm 21; hardness §5 (A13) | **sound**; Remark 28 (EMM₃ open) is out of date, since EMM₃ is false |
| external statements (A7) | Fan–Hou–Zhou, Botler–Sambinelli, Lu–Yi, Pfenninger, CKLOT match; see risks below |

**Formally verified in Lean** (`lean/`, 30+ files, sorry-free, standard axioms only; state on 2026-11-26, night):

- **Spine:**
  - Gallai ⇔ the rooted private-leaf test (`gallai_iff_rootedTest`);
  - Gallai ⇔ the marked bound;
  - **MR Thm 1** (`gallai_iff_tests`: Gallai ⇔ marked 2-connected test ∧ three-end test);
  - **MR Thm 113 in full** (`separatorStatement`), and **MR Thm 114 modulo Thm 59** (`gallai_iff_spineTests`). Only Thm 59 (node N3) of the spine is not yet formalized.
- **Classical theorems, proved from first principles:**
  - Fan's addible-edge lemmas (single and grouped);
  - **Lovász's theorem**, by an original induction from Fan's lemma;
  - **Pyber's theorem**, from Lovász and Fan.
- **New results:**
  - endpoint-structure Lemmas 1–4;
  - **two-step faithful descent**;
  - **EMC for four even vertices** (as a Mathlib `Matroid`);
  - **BP₃**;
  - k-step descent infrastructure, with three-step descent reduced to two base cases;
  - Fan descent, Fan transfer, E-twins, Fan certificates;
  - **six-clique Thm 1** (prescribed ends at a clique of six even vertices).
  - the d6-frontier certificates: Lemma 2.3, Thm 4.1, Thm 5.2, and Thm 6.1 at every deletion degree;
  - the five-even floor bound (`FiveEven.five_even_local`, `five_even_bowtie`; 131 kernel-checked certificates), which replaces Shaik in MR Cor 106 (audit A11 running);
  - **the reduction of Gallai to one named statement** (`gallai_of_branchBase3`);
  - **the barrier theorems** for Fan moves on cocktail party graphs;
  - **cut selection** (`cs_all`): every connected even-order graph has a pairing whose transversals all satisfy the cut inequality.

**Open risks:**

1. ~~Javadi–Miralaei (Wu's conjecture)~~: **repaired and audited** (`manuscripts/jm-repair`, audit A10: sound). The new proof of JM Thm 8 holds under r ≤ 2t − 1, which covers both uses in the semi-clique manuscript. It relies on Hilton, Hoffman and Liu–Chen (Liu–Chen not re-checked).
2. ~~Chu–Fan–Zhou Lemma 2.4~~: **resolved** (`manuscripts/cfz-lemma`). The common-vertex form with sum ≤ 7 is proved.
3. **Shaik [25]** (unrefereed) is **removed** from MR Cor 106 and Thm 144 (`manuscripts/bs-prescribed`; corrigenda). The proposed lemma, Botler–Sambinelli Thm 13 with one prescribed end, is false; the counterexamples include the family G_{t,t'}. What Cor 106 needs is the five-even one-universal floor bound. It is proved from Lovász + Fan alone and formalized in Lean (`five_even_floor`). Still open without Shaik, and unused by MR: Cor 106 with ≥ 7 unmarked even vertices in the one-exception odd case.

**Formal reduction of the whole conjecture (Lean, `gallai_of_branching`).** Gallai's conjecture follows from the statements `BStmt j` (j ≥ 3): j-step descent at an even vertex that has two even neighbours. No other hypotheses are needed.

**Endpoint matroid conjecture: complete check at n = 8.** All 1,082 connected critical graphs of order 8 satisfy EMC. 1,030 have uniform matroids, including all 476 three-connected ones. The 52 non-uniform ones have connectivity ≤ 2 (E15). **Route (H) verdict.** A stronger induction hypothesis cannot close BranchBase through Fan moves alone. The Lean barrier theorems (`cocktail_fan_barrier`, `cocktail_insertion_barrier`) show that for CP(m) the last move must be a new path of ≥ m − 1 held edges, a flower-type move at Fan's equality.

**Frontier, conceptual** (connections §R, experiments E13). Lovász's theorem with Fan's transfers is a finite game on end profiles. It proves the rooted test for every graph at n = 6, but not at n = 8. The single critical failure is Gqz~vw (4-connected) at a degree-4 root. **So full Gallai needs either a move beyond Fan's inequality or a stronger induction hypothesis.** This is now the central open problem of the programme (cloud session "missing-move").

## 7. Process going forward

See `research/README.md`. In short:

1. Rebuild the missing verification layer independently. Start with an exact solver (`tools/pathnum.py`), then replay the load-bearing enumerations.
2. Test every proposed generalization on small graphs before attempting a proof. The log is `research/experiments.md`.
3. Hunt for uniform-in-d mechanisms that connect the separate pieces (`research/connections.md`).
