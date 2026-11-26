# A3 — Referee audit: "Separators and endpoint exchange in the rooted Gallai problem" (separating-pairs.pdf, 177 pp.)

Scope:
1. §1: the doubling equivalence and Lemma 1.1.
2. The chain to Theorem 10.16 (p. 40).
3. The strengthenings Thm 12.28, Cor 13.5 and Cor 13.12.

Method: I read every step and classified it as SOUND, GAP (fixable), ERROR (false as stated) or UNCLEAR. I also ran independent exact computations on small graphs (CP-SAT path partitions, an independent check of the Javadi–Miralaei theorem for small n, and brute-force checks of the peripheral-path lemmas). Page numbers are printed (= PDF) page numbers.

Sources:
- Text: `scratchpad/raw/02-november-25__separating-pairs.txt`.
- PDF: pp. 40–41 were checked visually.
- Javadi–Miralaei: arXiv 2403.17290v1, published as Discrete Math. 349 (2026) 114676.

## 0. Bottom line

- **No ERROR found** in (1), (2) or (3).
- **The chain (1)–(2) to Theorem 10.16 is sound as written.** Every step checks:
  - every reduction lands on a strictly smaller even host where R<n applies (or is an explicit same-order construction);
  - every odd witness produced is connected, of order 2h+1, with p > h and at least h+1 missing edges, and Cor 8.7 upgrades it to the Alternative-1 form;
  - the parity and end-count bookkeeping is correct in every case I checked.
- **Javadi–Miralaei uses.** Every use is the main theorem with at most h distinct marks in K_{2h+1}, padded by an arbitrary extra mark when only h−1 are needed. That is exactly the hypothesis of JM (Wu's conjecture, proved for all n and every n-edge subgraph). JM's Theorem 8 (the matching-extension result) is never used. I independently confirmed the JM statement for n ≤ 5, all H up to isomorphism.
- **Theorem 10.15 is not used in the proof of Theorem 10.16.** The JM equality case ("exactly h holes ⇒ p ≤ h") is invoked directly in the proof of 10.16, twice. Theorem 10.15 enters only later, via Cor 10.17 → Prop 10.18 → Cor 12.14 → … → Lemma 12.27, that is, in chain (3).
- **(3) Thm 12.28, Cor 13.5 and Cor 13.12 are sound modulo two citation-level items.**
  - **G1 (UNCLEAR).** The connectivity of admissible spanning trees under single exchanges, as used in Thm 12.6, is attributed partly to a transversal-matroid paper [6]. Its validity hinges on the exact statement of Farber–Richter–Shank [5].
  - **G2 (GAP).** The external lemma used in Thm 12.29 is replaceable by the paper's own Lemma 13.6. This part was audited by careful spot-checking of each lemma used; it was not re-derived line by line for every sub-case of §12.3–12.11.
- One trivial point: the Eulerian clause of Thm 10.16 (δ ≥ 6) follows from δ ≥ 5 and even degrees, so it needs no argument.

## 1. Verdict table

### (1) §1

| Step | Page | Verdict | Notes |
|---|---|---|---|
| Doubling: p(double) = 2p(H^r) − 1 | 1–2 | SOUND | The bridge lies on exactly one path; cutting it gives partitions of both copies with total p+1. Conversely, the two leaf-paths join across the bridge; this is simple because the copies are disjoint. Gallai at order 4k gives rooted at order 2k. Rooted gives Gallai at both parities by trimming. Verified computationally (§3, T1). |
| Lemma 1.1 | 2 | SOUND | Trim the leaf. A vanished singleton pays for a split through u (u has positive degree). End parity gives two ends on distinct paths, because a simple path has distinct ends. Verified at orders 4 and 6 (T2). |

### (2) The chain to Theorem 10.16

| Step | Page | Verdict | Notes |
|---|---|---|---|
| Lemma 2.1 | 2 | SOUND | Hosts A^u (order 2s+2) and B^r (order 2h) are both < n. The two-leaf trimming case analysis is complete. The r ∈ A case uses the proxy-leaf substitution. |
| Thm 2.2 | 3 | SOUND | n=4 base cases checked (T3). Odd proper unions are singletons, via Lemma 2.1 with sides of sizes ≥3 and ≥4. Hence a cut vertex supports exactly one leaf and D is 2-connected. The two-leaf case is excluded in all three root placements. |
| Cor 2.3 | 3–4 | SOUND | (F,u)→(F,x) transfer; J = D+w is 2-connected; the degree-two w splits into two leaf copies. Residual case: r=u with deg_D(u) odd. That case is handled in Thm 10.16 by the semi-clique argument. |
| Thm 4.1 (feeds Cor 4.2) | 15–16 | SOUND | Checked all three constructions: both-ports-exposed; xy absent with both A-degrees even (graft, then the A+xy carrier cases); xy present (four-path switch). Arms omit the opposite port, so every join is simple. Sizes 2h, 2j ≤ n−2. |
| Cor 4.2 | 16 | SOUND | |
| Elementary grafts and peripheral-path fact (§8 preamble) | 21–22 | SOUND | Adjacent pair; nonadjacent with S=T, \|S∩T\|=1, disjoint; root at a degree-2 vertex. Peripheral path: L(J) is 3-connected, then Tutte [14] gives an induced arc with consecutive labels non-parallel, hence a vertex-simple path. Brute-force verified (T5). |
| Lemma 8.1 | 22 | SOUND | |
| Thm 8.2 | 23 | SOUND | {a,d} is a nonadjacent separating pair, so both shores are even (Cor 4.2). A 2-vertex shore is an adjacent degree-2 pair (graft). {c,d} gives c,d odd in F, hence even in V. Host orders 2h and 2j+2 are < n. |
| Cor 8.3 | 23–24 | SOUND (terse) | Cuts of K lift to F. The multi-low-vertex case reduces to two chosen virtual labels plus the peripheral path; virtual edges on the connector are swapped for physical backings. The Eulerian case gives 4-edge-connectivity by parity. Recommend expanding the case list. |
| Thm 8.4 | 24 | SOUND | |
| Lemma 8.5 | 24 | SOUND | Not needed for 10.16. All root placements checked, including the bridge sub-case. |
| Thm 8.6 | 24–25 | SOUND | Minimal matching bond, t ≥ 3. Bounds ⌊(u+t)/2⌋ and ⌊(v+1+t)/2⌋ checked in all four parity combinations. Auxiliary orders u+1, u+2, v+1, v+2 < n. |
| Cor 8.7 | 25 | SOUND | Forward reference to Lemma 10.1 (not circular). The j=2 extra split and the 2-vertex even shore are handled. Floors sum to exactly h. Verified at orders 5 and 7 (T4). |
| Lemma 10.1 | 31 | SOUND | Verified at orders 5 and 7 (T4). |
| Lemma 10.2 | 31 | SOUND | JM with h − \|M\| plant edges; ends d_M(v) + 2·1_{v∈Q}. For m = h−1, R is split at t. Verified for h = 2, 3 at all M, a, b, t (T6). |
| Thm 10.3 | 31–32 | SOUND | Missing-edge counts: J misses ≥ h (Lemma 10.2), and exactly h is excluded by JM. Roots t=a, b, z (three sub-cases) and exterior t (peripheral path from tc to ab) are covered. In the Eulerian case the parity claim is correct. |
| Lemma 10.6 | 33–34 | SOUND | Lengthening step: more than m outside vertices; a non-common-neighbour accounts for a distinct missing edge. The stationary case grows Q from b avoiding c. |
| Lemma 10.7 | 34 | SOUND | The maximal-component proof of the prescribed-edge/avoided-vertex peripheral cycle is correct (I checked the chord and attachment-gap argument). Brute-force verified (T5). |
| Thm 10.8 | 34–35 | SOUND | Both hypotheses (two trees; 3-edge-connected) are checked in all neighbour-edge patterns (0, 1, 2, 3 edges) and all root positions, including t a neighbour. |
| Cor 10.9 | 35 | SOUND | |
| Lemma 10.10 | 35–36 | SOUND | Verified as a special case of T7. |
| Thm 10.11 | 36–37 | SOUND | A 3-cut has connected bridgeless shores. It is not a matching (Thm 8.6) and not a star, so deleting one crossing leaves a matching. The route uses 3−j crossings. Augmented line graph is 3-connected (shore min-degree ≥ 2 by bridgelessness; 2-label deletions use 3-edge-connectivity). The count ⌊(\|A\|+j)/2⌋ + ⌊(\|B\|+j)/2⌋ − j + 1 = n/2 is correct. |
| Thm 10.12 | 37–38 | SOUND | Both constructions (nonadjacent tips; K4 tips). Parity formula checked. Greedy degree bound 2h−m−2 ≥ q uses h ≥ 2. |
| Cor 10.13 | 38 | SOUND | |
| Thm 10.14 | 38–39 | SOUND | k≥3: two odd supports on distinct rows, plus the dense case via JM. k≤2: the deleted-spoke transfer plus the rotation (Fan) argument (I checked the arborescence and arm-preservation details), then Thm 10.8 on D. The parity identity is correct. |
| Thm 10.15 | 39–40 | SOUND | Three-odd-tip lift: all three C/pyq configurations are correct. Hall dichotomy; second-case growth bound h+m−1 > m uses h ≥ 2. Equality case m=h uses JM correctly. The k≤2 case goes through Thm 10.12 on D. Not used by 10.16 itself. |
| **Thm 10.16** | 40–41 | **SOUND** | Uses Cor 8.7, JM equality, Thm 10.3, Cor 10.9, Thm 10.11, Cor 10.13, Thm 10.12, Thm 10.14, Thm 8.6, Thm 2.2 and Cor 2.3. Cut-vertex case: t≠u reduces via Cor 2.3 to a 2-connected failure with a degree-2 vertex. For t=u: either p(D) ≤ h, or D is a semi-clique and a plant at u gives two distinct ends (verified for h = 2, 3 in T6). The Eulerian δ ≥ 6 clause is trivial. |

### (3) Strengthenings

| Step | Page | Verdict | Notes |
|---|---|---|---|
| Lemma 11.1 / Thm 11.2 / Cor 11.4 | 45–48 | SOUND | Threshold D ≥ 2U−1 derived correctly. Cor 11.4's deferral and seeding cases checked. Lemma 11.1 verified on small graphs (T7). |
| Lemma 12.1, Thm 12.2 (+ physical-edge form) | 57–58 | SOUND | Density bound 2h−m−3 ≥ h−m needs h ≥ 3. That holds wherever it is used, via Cor 12.14 (d(t) ≥ 6). |
| Cor 12.3, Thm 12.4, Thm 12.8 (+ Lemma 12.7), Thm 12.10, Thm 12.11, Lemmas 12.12–12.13 | 58–66 | SOUND (spot-checked) | Thm 12.8's three lift sub-cases checked in full. In Thm 12.10, the contact lemma and the both-at-a sub-case were checked. |
| Thm 12.6 | 60–61 | **UNCLEAR (G1, citation)** | The center-uniqueness argument is correct. However, "the unused slot is part of this theorem [6]" cites Farber's paper on *transversal* matroids, which do not cover graphic matroids. See G1. |
| Cor 12.14, Thm 12.16, Cor 12.17 | 67–69 | SOUND | Prop 10.18 gives \|B\|≠1. Thm 12.16's final case uses kl ≥ 2h−1 ≥ h+1 missing cross pairs plus Cor 8.7. Cor 12.17's complementary-pair analysis is complete. |
| Cor 12.18 | 69–70 | not re-audited | Load-bearing Lean/Python finite check ("FiveTip.dense"). Not needed for 12.27/12.28. |
| Lemmas 12.19–12.20, Thm 12.21, Lemma 12.22 | 70–72 | SOUND | 12.21 uses Cor 5.2: a root-free odd component with a single edge to y makes y a leaf of the closure. Lemma 12.22 depends on Thm 12.6 (G1). |
| Lemma 12.23 | 72–74 | SOUND | Covers: two-port even shore (pattern 3,1); odd shores (triple port excluded; two 2-matchings); even shores with ≥3 ports (one deletion, or the opposite-wedges route). The r=x even case goes via Cor 11.4. |
| Lemma 12.24, Thm 12.25 | 74–75 | SOUND | All three route cases (t∈B; t∈A with b∈U or b∉U) checked. The protected peripheral cycle only needs separators avoiding g. |
| Lemma 12.27 | 76–77 | SOUND given G1 | Partition-maximiser argument: parts carry two trees and R is simple and a union of two forests. Basis-extension count gives 4p−2e ≥ 4b. Components with 2–4 labels are excluded via Lemmas 12.19/12.20 and Cor 12.17. The absorption process terminates in a part with ≤ 3+1 boundary edges, giving the proper 4-bond. |
| **Thm 12.28** | 77 | **SOUND given G1** | 10.16 → 12.25 (5-edge-connected) contradicts the 4-bond of 12.27. |
| Thm 13.3 | 88–89 | SOUND | Two-port shore excluded by parity (q_x, q_w odd, sum 5). Covers: matching colouring 3+2; triple in A; triple in B with y≠z or y=z; residual-leaf installation for patterns 3 / 2,1 / 1,1,1. |
| Thm 13.4 | 89–90 | SOUND | Covers: repeated port x≠t; t repeated (route, or the component argument via Cor 4.2 / Thm 4.1 showing the crossings from A−t number ≥ 4); unrooted-shore h+3 bound for patterns 1^5, 2111, 41, 3·(deg 6/≥7), 221 (degrees 5/6/≥7). |
| **Cor 13.5** | 91 | **SOUND** | |
| Lemma 13.6, 13.7, 13.8, Thm 13.9 | 91–92 | SOUND | |
| Thm 12.29 | 77–78 | **GAP (G2, citation)** | The cycle-merging step cites Chu–Fan–Zhou [3, Lemma 2.4] through a paraphrase of its hypotheses. The paper's own Lemma 13.6 covers the configuration. Density part (L ≥ 2 and L = 1 words) checked. |
| Cor 13.10 | 92 | SOUND (given G2) | |
| Thm 13.11 | 93–95 | SOUND | Covers: three shortcut properties; opening three cycles (cases 1–3 complete); dense complement q=1, q≥2 (list ≤ q+1, = q+2, and the j=4 universal-t exception). End-count bookkeeping is correct when the two lists are read as restored through y. |
| **Cor 13.12** | 95 | **SOUND (given G2)** | 13.5 (6-edge-connected) and 13.2 (two trees) feed 13.11. Degree 6 is excluded by 13.10. |

## 2. Findings

### G1 — Theorem 12.6, p. 60: inapposite citation for basis-pair connectivity with unused edges (UNCLEAR → GAP; low-to-moderate severity)

Severity hinges on what [5] actually proves. If [5] proves connectivity only when E(J) = T ∪ U, then nothing in the paper supplies the one-exchange connectivity of admissible first trees when J has extra edges. In that case the uniform center z would be unproved, and with it Lemma 12.22, Lemma 12.27, Thm 12.28, Cor 13.5 and Cor 13.12. I could not access [5]: the publisher returned 403. I could not derive the needed statement from the E = T ∪ U case in the time available. A direct reduction (basis exchanges in M ∨ M combined with exchanges within one union) does not obviously go through.

**Where it matters.** Theorem 12.6 shows that all admissible spanning trees of J share one center z. Here a tree is admissible when its complement contains a spanning tree. The proof needs any two admissible trees to be linked by a sequence of admissible trees, where consecutive trees differ by one edge exchange. The paper says this follows from the "graphic basis-pair graph of Farber, Richter and Shank [5]". It then adds that "the unused slot is part of this theorem [6]".

**What is wrong.** Reference [6] is M. Farber, *Basis pair graphs of transversal matroids are connected* (Discrete Math. 73, 1989). Graphic matroids are not transversal in general, so [6] cannot supply the graphic statement.

**What probably fixes it.** The abstract of [5] (JGT 9, 1985) says: "any pair of edge-disjoint spanning trees can be obtained from any other by a sequence of single edge exchanges in a way that preserves, at each step, the property of being edge-disjoint spanning trees". This is stated for an arbitrary graph, so it plausibly already covers graphs with edges outside T ∪ U. Whether [5]'s "single edge exchange" lets an edge move into or out of the unused set needs to be confirmed from the paper itself. If exchanges were only T↔U swaps, then T∪U would be invariant and the cited fact would not give connectivity of all admissible first trees.

**Dependents.** Lemma 12.22 → Lemma 12.27 → Thm 12.28 → Cor 13.5 and Cor 13.12. Cor 12.14's six-label remarks also depend on it.

**Fix.** Either:
- state and cite the exact exchange theorem of [5], and drop [6]; or
- prove the needed one-edge connectivity of admissible first trees directly.

Note: the other step in this argument is fine. Trees differing by one exchange share a two-component forest, and the ≥ k−1 ≥ 3 label component has a unique center.

### G2 — Theorem 12.29, p. 77: external lemma cited only by paraphrase; an internal lemma suffices (GAP, low severity)

**The citation.** The step "Their edges together with the remaining path … decompose into at most one more path than the number of cycles" is justified by Chu–Fan–Zhou [3, Lemma 2.4]. It is described only through a paraphrase ("route has at most four vertices … sum of its order and number of cycles at most six").

**The repair.** In every distance case the held route is an induced path of F^t ending at y: ℓ–y–s (t = y), ℓ–s–y (t = s), or ℓ–t–s–y with t ≁ y. It is edge-disjoint from the ≤ 2 closed cycles, since ts is removed from W and the cycle spokes go to the active tips. This is exactly the hypothesis of the paper's own Lemma 13.6 (p. 91), whose proof I verified.

**Fix.** Cite Lemma 13.6 (a forward reference) instead of [3, Lemma 2.4].

**Dependents.** Cor 13.10 (degree-six vertices at distance ≤ 2) → Cor 13.12.

### Remarks (not gaps)

- **R1 (Cor 8.3, p. 23).** The proof that there is at most one degree-two vertex compresses a case analysis into one paragraph:
  - root high: pair two nonroot low vertices;
  - root low: pair the root with another low vertex;
  - all other low vertices get physical backing by pairing;
  - then the peripheral path between the two virtual labels, with backing swaps on the connector.

  It is correct, but each outstanding case should be written out.
- **R2 (Thm 10.16, p. 40).** The Eulerian δ ≥ 6 clause is immediate from δ ≥ 5 and even degrees. Theorem 10.15 is not an ingredient of 10.16. The task description assumed it was, but the "exactly h holes" JM use inside 10.16 is direct.
- **R3 (descriptive citations).** Each descriptive name in chains (1)–(3) resolves to an existing result that says what is needed:

  | Descriptive name in text | Resolves to |
  |---|---|
  | "elementary/adjacent-pair graft", "exterior-root graft", "degree-two-root graft" | §8 preamble |
  | "peripheral-path lemma" | §8 preamble, and the protected form at the start of §12.10 |
  | "separating-pair bound/rule" | Cor 4.2/4.3 |
  | "asymmetric-cut corollary" | Cor 11.4 |
  | "separated-leaf / distinct-leaf lemma" | Lemma 10.10 |
  | "two-mark bound" | Lemma 10.10 and the Lemma 11.1 two-leaf start |
  | "degree-two suppression result" | Cor 8.3 |
  | "first-order odd reductions" | Cor 8.7 and Lemma 10.1 |

  "Fan's edge-addition lemma [7, Lemma 3.4]" is re-proved inline (Thm 10.14). "The cubic odd-core proposition" (p. ~108, Thm 13.36) lies outside these chains; it presumably means Prop 13.26 and should be cited by number.
- **R4 (Thm 13.11, p. 94).** The phrase "precisely two contributions … with two provisional ends at a singleton" is correct only if each list is read as restored and joined to y as one path (Q1⁻¹ y Q2). Under the alternative reading, where the extra path is just r1 y r2, the count fails at the far ends. Recommend writing the additional path explicitly.
- **R5 (JM status).** JM is now published (Discrete Math. 349 (2026) 114676). The bibliography entry is correct. All ~20 uses in chains (1)–(3) are K_{2h+1} with exactly h marks: missing edges plus plant edges, or h−1 marks padded by one arbitrary edge to leave one cycle intact. The opened cycles then give rows ending at the two ends of each mark, as the paper uses.

## 3. Computations

Scripts are in `/tmp/claude-0/-home-user-Manuscripts/a40c9215-4484-5bc3-a3e1-2bba3a808810/scratchpad/audit/`. They use `/home/user/Manuscripts/tools/pathnum.py` (exact CP-SAT) and `data/conn*.g6`. No project files were modified.

RESULTS_PLACEHOLDER

**Interpretation.** Most statements in chain (2) are of the form "a least failure has property X". These are vacuous on small graphs, because the rooted bound holds there. The tests therefore target the unconditional ingredients the chain relies on:

| Test | What it checks |
|---|---|
| T1 | doubling identity |
| T2 | Lemma 1.1 |
| T3 | rooted bound at orders 4 and 6 (base case of Thm 2.2) |
| T4 | Lemma 10.1 and Cor 8.7 (stronger than Gallai) |
| T5 | peripheral-path lemmas |
| T6 | Lemma 10.2, the semi-clique plant, and the JM-equality floor |
| T7 | Lemma 11.1 / 10.10 |
| T8 | the external JM theorem |

None produced a counterexample.

## 4. Fixes requested from the author

1. **G1.** Replace "[6]" in Thm 12.6 by the precise statement from [5]: connectivity of the pair-of-disjoint-spanning-trees exchange graph in an arbitrary graph, with one tree changing by one edge per step. Alternatively, give a direct proof that admissible first trees are connected under single exchanges.
2. **G2.** In Thm 12.29, replace the Chu–Fan–Zhou citation by Lemma 13.6. Note explicitly that the held route is induced in F^t and edge-disjoint from the closed cycles.
3. **R1.** Expand Cor 8.3's case list.
4. **R3.** Cite "cubic odd-core proposition" by number.
5. **R4.** Write the joined list path explicitly in Thm 13.11.
6. **Optional.** In Thm 10.16, note that the Eulerian clause is immediate, and that Theorem 10.15 is not used there.
