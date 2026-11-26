# A2 audit: marked-reduction, §18–§19, Theorems 113, 114, 145, 162–164 and the parity apex

**Target.** "Cut vertices and cycle intersections in Gallai's path decomposition problem" (J. Williams, Nov 24 2026), `gallai/01-original-manuscripts/marked-reduction.pdf`. PDF page numbers equal the printed page numbers.

**Referee stance.** Adversarial. Every step was re-derived by hand. The local constructions of Theorem 113 were also replayed by an independent program (§6). Theorem 59 is taken as given, as instructed; §2 lists exactly what is taken from it.

## 0. Bottom line

- **No ERROR was found in the load-bearing chain** Theorem 59 ⇒ Theorem 113 ⇒ Theorem 114, nor in Theorems 145, 162, 163 and 164.
- The separator argument (Theorem 113) is complete. It covers:
  - odd and even components;
  - both parities of the port degrees inside the component;
  - the adjacent and nonadjacent separating pair, handled through "assign xy to A" and the re-added edge;
  - the root at a port, including the case where its degree drops to one.

  Every concatenation was checked for simplicity, and the program reproduces the paper's row count and endpoint-preservation claims on every instance through order 8 (§6).
- In Theorem 114 the following are all correct:
  - the bound |S| ≥ 4;
  - the 3-connectivity of the parity apex;
  - the parity and budget bookkeeping;
  - both directions of the equivalence;
  - the restriction "J − z has no matching cut".
- What remains are **interface and dependency issues**. None of them is a hole in the logic of 113/114:
  - the wording of Theorem 59's finite-order clause;
  - external lemmas used in paraphrase: Fan's addible-edge lemmas, Fan–Hou–Zhou, Shaik;
  - an unavailable supplement;
  - one redundant sub-case in §18.

  They are listed as GAP or UNCLEAR in §1 and §3.

## 1. Verdict table

| # | Location (page) | Claim / step | Verdict |
|---|---|---|---|
| 1 | Thm 113, p. 127 | Setup: A = B[C∪{x,y}] (with xy), E = B − C − xy is connected, and both ports have positive E-degree. | SOUND |
| 2 | Thm 113, p. 127 | Marked bound on connected graphs with blocks of order ≤ n−2, from Thm 59's finite-order clause with m = n−2. | SOUND given Thm 59; wording GAP in Thm 59's statement (F1) |
| 3 | Thm 113, p. 127 | Rooted bound on smaller W: two ends at a positive even root; three ends at an odd root of degree ≥ 3 (private leaf, mark, trim). | SOUND |
| 4 | Thm 113, p. 127 | Floor bound for odd-order W with a leaf (two copies of W − z joined by a bridge, cut, keep the better copy). | SOUND |
| 5 | Thm 113, p. 127 | Odd component: s ≥ 1; exactly one port u is odd in A; Lovász gives s+1 paths with one end at each odd vertex and none at v. | SOUND |
| 6 | Thm 113, p. 127 | Odd component, P omits v: W = E + leaf at u; substitution preserves exterior ends; order n − 2s; parities. | SOUND |
| 7 | Thm 113, p. 127 | Odd component, odd root v dropping to degree 1 in W: floor on W plus a split at v. | SOUND |
| 8 | Thm 113, p. 127 | Odd component, P visits v: W = E + uv + leaf at v; same-row and different-row substitutions. | SOUND |
| 9 | Thm 113, p. 127 | Even component, both ports odd in A: W = E + xy; the X = Y and X ≠ Y substitutions. | SOUND |
| 10 | Thm 113, pp. 127–128 | Even component, both ports even in A: the "two ends at x, none at y" decomposition and the graft (row omitting y, or local path omitting y, or the symmetric versions). | SOUND |
| 11 | Thm 113, p. 128 | Even/even, a row L x M y N: distinguished edge e, subdivided Lovász; cases R = e, e terminal, e internal with X = Y or X ≠ Y. | SOUND |
| 12 | Thm 113, p. 128 | Even/even, odd root at a port with E-degree 1: floor on E plus a split. | SOUND |
| 13 | Thm 113 | Minimality: only "both tests hold below order n" and 2-connectivity of B are used. Every comparison graph has order n − 2s ≤ n − 2. | SOUND (stronger statement available, F7) |
| 14 | Thm 114, p. 128 | Forward direction: bridge double and diamond host on J − z (2-connected, any matching cuts). Root degree ≥ 2 (test 1) or ≥ 3 (test 2). | SOUND given Thm 59's converse constructions |
| 15 | Thm 114, p. 128 | \|S\| even; \|S\| = 2 passes at either parity, via Lovász plus a leaf, or Lovász plus a split; hence \|S\| ≥ 4. | SOUND |
| 16 | Thm 114, p. 129 | J = B + z(S) is 3-connected (pair deletions via Thm 113; the r-component contains r ∈ S). | SOUND (single deletions omitted, trivial: F6) |
| 17 | Thm 114, p. 129 | Parity of J: only z is even (n even); exactly z, r even and adjacent (n odd). Budgets (\|J\|−1)/2 = \|J−z\|/2 and \|J\|/2 = ⌈\|J−z\|/2⌉. | SOUND |
| 18 | Thm 114, p. 129 | "May restrict to J − z with no matching cut": the constructed J − z = B ∈ C. | SOUND |
| 19 | Thm 114, p. 129 | Neighbourhood paragraph: E-subgraph of the test host is 2K; FHZ ⇒ suffices d_J(z) ≥ 6; Shaik ⇒ two universal vertices at d = 6. | Logic SOUND; depends on [15] (UNCLEAR, F3) and on unrefereed [25] (UNCLEAR, F2) |
| 20 | p. 129 | "Partition before deletion": m + s − j rows; the "exactly when" criterion; both examples. | SOUND; examples verified by computer |
| 21 | pp. 130–131 | Five-vertex book (K2 ∨ co-K3) floor bound, six cases; transfer to both deletion tests. | SOUND given Fan's lemmas (F4); every restoration step was re-checked by hand |
| 22 | p. 131 | K_i table (seven-site certificates). | UNCLEAR: supplement not available (F5). Not used by 113/114. Spot-tested (§6) |
| 23 | p. 131 | Two degree-two vertices at the same pair. | SOUND |
| 24 | pp. 131–132 | Odd-order deletion with a root contact in T (t = 1,…,5). | SOUND given Fan's lemmas; re-checked by hand |
| 25 | pp. 158–159 | Thm 145: lexicographic minimisation (n, \|E\|, d(r)); the one-edge step; the reducible forms (cut vertex, matching cut); Fan restoration. | SOUND given Fan's Lemma 3.4 (F4) |
| 26 | p. 159 | Thm 145: second even neighbour of degree ≥ 4; both even neighbours of degree 2 (the D = H + uv swap). | SOUND |
| 27 | p. 159 | Thm 145 / Cor 146: Thm 113 applies again to (H, w), so its parity apex is 3-connected. | SOUND |
| 28 | p. 171 | Thm 162: Lovász decomposition, completing one edge per cycle to K4, the two-path cover, successive removals. | SOUND |
| 29 | p. 171 | Cor 163: deleting a matching F that meets all even cycles; Pyber; returning the pairs at +1 each; tested edges stay on even-site cycles. | SOUND (Pyber's Thm 0, standard) |
| 30 | pp. 171–172 | Cor 164: minimise (#even, order); no eligible pair; p(H) = k+1 and p(H−xy) = k; exactly one eligible pair in H^{xy}; no even–even bridge; the ab-nonedge remark. | SOUND |
| 31 | p. 173 | p(H^{xy}) vs p(H): K3 example; the 16-vertex decrease example. | SOUND; verified by computer |
| 32 | p. 188 | ApexConnectivity.lean, the "apex checker", and the §19 substitution checkers. | UNCLEAR: not available (F5). The equivalence itself is elementary (§4) and was re-checked by computer |
| 33 | §18, pp. 103–126 | Lemma 81, Lemma 82, Thm 83, Cor 84, Lemma 87, Thm 88, Cor 89, Thm 92, Props 94 and 96, Cor 95, Thm 97 (main construction), Cor 99, Thm 101 (all three cases: four distinct exterior neighbours at odd and even order, one common neighbour, two common neighbours), Thm 103, Prop 105. | SOUND on the points re-derived. One vacuous sub-case in Thm 83 (F8). Not used by 113/114 |
| 34 | §18, remaining items: Props 85, 86, 93, 104, 107–112; Cors 90, 98; Thm 100; the split cases of Thm 97 | Read for structure only. | NOT FULLY RE-DERIVED (§5) |

## 2. What 113/114 take from Theorem 59 (interface check)

1. **Finite-order clause (used by Thm 113 and throughout §18).** The statement on p. 84 reads: "These assertions through core order m + 1 suffice for every connected graph whose two-connected blocks have order at most m." Theorem 113 (p. 127) and §18 (p. 103) use this as the **marked bound (1)** on such graphs, not merely as the ordinary ceiling. The proof of Theorem 59 (p. 85) does conclude the marked bound ("The block-tree transfer in Section 2 then gives the marked bound for any number of these blocks"), so this is consistent with the proof. The statement does not say what "suffice" means, however. See F1.
2. **Converse constructions (used by Thm 114 ⇒).** These are the bridge-double identity p = 2F₂(B,x) − 1 and the diamond identity p = 2F₃(B,x) − 1.
   - Both hold for any connected B, so the forward direction may be applied to a J − z that has matching cuts, as the paper says.
   - The bridge identity needs the root to have positive even degree. In test (1) the root degree is d_J(r) − 1 ≥ 2.
   - The diamond lower bound splits at a core terminal with one end, which needs root degree ≥ 3. In test (2) the root degree is d_J(r) − 1 ≥ 3, because an even vertex of a 3-connected graph has degree ≥ 4.
   - This was checked.
3. **Converse of the equivalence (used by Thm 114 ⇐).** If Gallai fails, some B ∈ C fails a test. A least-order failure is then well defined, and every member of C of smaller order passes both tests. This is exactly what Theorem 113 consumes.

**No mismatch** was found in how 113/114 use Theorem 59, beyond the wording point in item 1.

## 3. Findings

**F1. GAP (wording, interface), Thm 59 p. 84, as used on pp. 103 and 127.**
- The finite-order clause should state its conclusion explicitly: "If both tests hold for all members of C of order ≤ m+1, then the marked bound (1) holds on every connected graph whose 2-connected blocks have order ≤ m."
- Theorem 113 needs exactly this with m = n − 2, as does the private-leaf variant: adding a leaf creates a K2 block only, which needs m ≥ 2.
- **Fix:** restate the clause as above. No change to any proof is needed.

**F2. UNCLEAR (external, unrefereed), Thm 114 "neighbourhood" paragraph, p. 129.**
- The conclusion "at d_J(z) = 6 a failure requires two universal vertices in K" uses Shaik [25, Cor. 1.2], an unrefereed Hexagon preprint (v1, Oct 2026).
- Without [25], Fan–Hou–Zhou alone forces only one universal vertex. Failure needs a bowtie or a block with a degree-4 vertex, and on five vertices both contain a universal vertex.
- Nothing in the equivalence of Theorem 114 depends on this. Later sections (Thm 144; the d = 6 programme) do.
- **Fix:** mark the "two universal vertices" consequence as conditional on [25].

**F3. UNCLEAR (citation precision), Thm 114 p. 129, and the Section 2.1 criterion on p. 8 (used in Props 105 and 107).**
- Fan–Hou–Zhou [15] is invoked with the hypothesis "the E-subgraph contains no two triangles meeting in exactly one vertex, and each block has maximum degree ≤ 3".
- I could not check this wording against [15]. In particular, I could not check whether "maximum degree ≤ 3" is meant inside each block or for the E-subgraph as a whole.
- The answer matters in Section 2.1's doubling step: a joining bridge between two even supports adds a K2 block but raises each support's E-degree by one.
- It does not matter for the Thm 114 paragraph, where the E-subgraph is exactly 2K with no extra edges.
- [15] is used only as the ordinary ceiling on hosts, so the floor-versus-ceiling question does not arise.
- **Fix:** quote the exact theorem of [15].

**F4. UNCLEAR → supported (external lemma in paraphrase), Fan [14] Lemmas 3.3 and 3.4.**
- **Where used:** pp. 114 and 130–132 (book, contacts), 157 (Thm 144), 158–159 (Thm 145).
- **The reading used:** let P be a path decomposition of G, and let w, t be nonadjacent.
  - If b_P(t) > |{x ∈ N_G(w) : b_P(x) = 0}|, then G + wt has a decomposition with the same number of paths and endpoint vector b + e_w − e_t, all other counts unchanged.
  - For a set S of donors (Lemma 3.3), if Σ_{t∈S} b(t) exceeds the same count, the conclusion holds for some t ∈ S.
- The paraphrase is consistent across all uses. I did not compare it with [14].
- I tested it by exact search on random graphs (§6, C1), with no counterexample. Thm 145, the book and the contact arguments are SOUND under this reading.
- **Fix:** quote Fan's lemmas verbatim once, including the "other counts unchanged" clause, which every application uses.

**F5. UNCLEAR (unavailable supplement), p. 188.**
- **Not available:** ApexConnectivity.lean, the "apex checker" (all labelled 2-connected graphs through 6 vertices), the "separate checks for Section 19", FiveSiteFan.lean (103 cases), and the seven-site certificate trees behind the K_i table (p. 131).
- None of these is needed for 113/114: the apex equivalence is elementary (§4), and the table is used only at d_J(z) = 6.
- The K_i table claims remain unverified beyond the spot tests in §6.

**F6. GAP (trivial, presentational), Thm 114 proof, p. 129.**
- 3-connectivity is argued for deletions of {z, v} and {v, w} only. Deleting at most one vertex is not mentioned, and this does not follow formally from the pair case.
- It is immediate: B − v is connected and z keeps a neighbour since |S| ≥ 2; J − z = B.
- **Fix:** one sentence. The proof in §4 below covers all cases.

**F7. Remark (strengthening, not a defect), Thm 113, p. 127.**
- The proof never uses that B fails, nor that B has no matching cut. It uses only:
  - (i) B is 2-connected;
  - (ii) both tests hold on all members of C of order < n.
- Under (i) and (ii), every 2-connected B of order n passes the rooted test at every eligible r outside an all-odd component behind a separating pair.
- Stating it this way would make the later uses transparent: Thm 145 at (H, w), Cor 146 along trails, Thm 144 in the leafy class.

**F8. Minor imprecision (no error), Thm 83, p. 105, the "m = 3" exceptional bridge.**
- This sub-case lies in the branch where x is not an A-port.
- The detached component must avoid x, because α survives, so x lies on the retained side of the bridge together with the retained port r.
- That side has boundary {bridge, crossing at r} in B. If x ≠ r, it has an edge and gives a proper 2-edge cut. So "that side is just {r}" forces x = r, contradicting x not being a port.
- The exceptional case is therefore impossible, and the leaf-deletion construction that follows is unnecessary. The theorem is unaffected.
- (The letter r here is the retained port, not the root. The clash of notation obscures this.)

**F9. Minor wording (no error), p. 129, "partition before deletion".**
- "Exactly when j ≥ s and zr does not terminate at r" is correct only for direct trimming, as stated.
- If j ≥ s + 1, a terminal zr can be repaired by a split at r using the spare row.
- Harmless, since the paragraph is illustrative.

**F10. Extraction note, p. 130.** "K2 ∨ K3" must read K2 ∨ K̄3 (three independent pages). The proof uses "pages independent" explicitly ("by independence"). With K3 the five sites would induce K5, the i = 3 row of the later table.

No item found is of type ERROR.

## 4. Detailed audit notes

### 4.1 Theorem 113 (pp. 127–128)

**Minimality order.**
- Order only. Every comparison graph W has |W| = n − 2s with s ≥ 1:
  - odd |C| = 2s+1: W = E + leaf, or E + uv + leaf, of order n − (2s+1) + 1;
  - even |C| = 2s: W = E + xy, or E, of order n − 2s.
- The leafed version used for an odd root has order ≤ n − 1 and blocks of order ≤ n − 2.
- So only the marked bound for blocks of order ≤ n − 2 is needed. By Theorem 59 this follows from both tests through order n − 1, which hold at a least-order failure.
- W is connected because E is connected: every component of B − {x,y} other than C attaches to both ports, by 2-connectivity.

**Port parities.**
- Degrees of vertices in C are the same in A and in B.
- Odd |C| gives an odd sum of the C-degrees, so exactly one port is odd in A.
- Even |C| gives equal port parities in A.
- In every branch the comparison graph corrects the port parities:
  - odd |C|, P omits v: d_W(u) = d_E(u) + 1 and d_W(v) = d_E(v);
  - odd |C|, P visits v: d_W(u) = d_E(u) + 1 and d_W(v) = d_E(v) + 2;
  - even |C|, odd ports: E + xy;
  - even |C|, even ports: E.
- A root at a port keeps its parity. Its degree in W can fall to 1 only for an odd root at v (odd |C|, P omits v) or at a port with E-degree 1 (even ports). Both cases are treated by the floor lemma plus a split. The split uses a restored local path through the root, which exists because the root has positive even A-degree and receives no local end.
- A positive even root keeps degree ≥ 2.

**Lovász counts.**

| Case | Graph | Vertices | Odd vertices | Paths | Conclusion |
|---|---|---|---|---|---|
| Odd \|C\| | A | 2s+3 | 2s+2 | s+1 | one end per odd vertex, none at v |
| Even \|C\|, odd ports | A | 2s+2 | all | s+1 | one end per vertex |
| Even \|C\|, even ports | A + leaf at x | 2s+3 | 2s+2 (y even) | s+1 | after trimming the leaf (with a split if it was a singleton): two ends at x, none at y, one in C |
| Even \|C\|, even ports | A with xy subdivided | 2s+3 | 2s+2 (only the subdivision vertex even) | s+1 | one end at every original vertex |

All of these are exact.

**Substitutions.**
- In every display the exterior pieces L x and y N omit the opposite port, and they lie in E.
- Local pieces lie in C ∪ {ports}. Rx and Ry are disjoint and avoid the opposite port.
- So every concatenation is simple, including when a piece is a single vertex.
- Edge bookkeeping: the distinguished copy e is discarded, and a physical xy, if present, lies in A and is covered by a local path.
- Count: local paths are absorbed with net +s in every case. For example, in the e-internal case with X ≠ Y, four rows (the exterior row, X, Y, R) become three, while s+1 local paths are used.
- Exterior end counts are preserved by inspection. The program confirms this (§6, C3).

**Case exhaustiveness (even ports).**
1. Some row visits x and omits y.
2. Otherwise, some x-ended local path omits y; any row through x then works.
3. The same two checks with the ports exchanged.
4. Otherwise there is a row containing both ports. Then R = e, or e is terminal at exactly one port (which reduces to case 3 with the path yR′ omitting x), or e is internal.

This is exhaustive: a path that ends at both ports and contains xy is xy itself.

**Verdict:** SOUND.

### 4.2 Theorem 114 (pp. 128–129)

**Parity and budget.**
- Test (1): |J| is odd and J − z has order 2k. A root r ∈ N(z) has even degree d_J(r) − 1 ≥ 2, so this is the even test F₂ ≤ k with k = (|J|−1)/2.
- Test (2): |J| is even and J − z has order 2k+1. The root r has odd degree ≥ 3, so this is the odd test F₃ ≤ k+1 with k+1 = |J|/2.
- In both cases the budget is ⌈|J−z|/2⌉.

**|S| ≥ 4.**
- *n = 2k with exactly two even vertices.* Adding a leaf at r leaves one even vertex. Lovász gives k paths with one end at r. Trimming the leaf gives two ends at r, or, if the leaf edge was a singleton, a free row for a split at r (whose degree is positive and even). So F₂ ≤ k.
- *n = 2k+1 with one even vertex.* Lovász gives k paths with one end at r. Since d(r) ≥ 3 there is an internal visit, and a split gives three ends in k+1 paths.
- Hence a failure has |S| ≥ 4. Since |S| is even, |S| = 3 cannot occur; |S| ≥ 3 is all that the connectivity argument needs.

**3-connectivity of the apex: the elementary equivalence.** Let B be 2-connected, S ⊆ V(B) with |S| ≥ 3, and J = B + z with N(z) = S. Then J is 3-connected if and only if every component of B − {x,y}, over all separating pairs, meets S.

*Proof.* Take X ⊆ V(J) with |X| ≤ 2.
- If z ∈ X, then J − X = B − (X∖z), which is connected.
- If z ∉ X, every component of B − X meets S ∖ X: this is trivial when B − X is connected, since |S| ≥ 3, and it is the hypothesis otherwise. So z joins all the components.
- Conversely, a component of B − {x,y} that misses S is separated from z by {x,y}.

**Applying it.** At a least failure, the component of r contains r ∈ S, and every other component contains an even vertex by Theorem 113. So J is 3-connected.

**Matching cuts.** J − z = B ∈ C, so the restriction "J − z has no matching cut" is justified. The forward direction does not need it.

**Verdict:** SOUND.

**Side material on pp. 129–132.**
- *Neighbourhood paragraph.* The induced subgraph on the even vertices of the bridge double and of the diamond host is exactly two disjoint copies of K: in the bridge double r becomes odd; in the diamond host r stays odd and a, b are cubic. The reductions are correct relative to [15] and [25] (F2, F3).
- *Partition before deletion.* The count is m + s − j: the s passages through z each create a piece, and the j terminal spokes vanish. Correct.
- *Examples.*
  - J = K6 − {02, 23, 13}: 3-connected, with exactly 0 and 1 even and adjacent. The rows are valid, the deletion gives 4 paths with 1 end at r, and the 3-path partition of J − 0 has 3 ends at 1.
  - The 9-vertex example: 3-connected, only vertex 7 even, K has universal vertices 6 and 8, the four rows are valid with terminal spokes {3, 6, 8}, and deletion gives 4 paths with 2 ends at 1. The impossibility argument for the terminal set {2, 3, 6} is correct (vertex 6 would need three visits with degree 4 and no ends).
  - All of this was verified by computer.
- *Book.* All six cases were re-checked, restoration by restoration, against the paraphrased Fan inequality. Each starting deletion leaves exactly one even vertex, as claimed, and the case split over N(u) ∩ book is exhaustive. The transfer to the deletion tests (one or two private leaves at r, trimming, spare row for a split) is correct.
- *Two degree-two pages and odd-order contacts (t = 1,…,5).* Re-checked line by line. Correct under F4.

### 4.3 Theorem 145 (pp. 158–159)

**Order.** The failure is chosen lexicographically by (order, edges, prescribed degree), among failures of either unrestricted test. The moves:
- (a) **Cut vertex in H = B − rw.** δ(H) ≥ 2 rules out a block of order n − 1, so the transfer through order n − 1 applies.
- (b) **Matching cut.** Take an inclusion-minimal sub-matching; the shores are connected with ≥ 2 vertices; the leaf goes on w's shore; blocks have order ≤ n − 2.
- (c) **One-edge step.** The order is the same and there are fewer edges. Fan's lemma applies with donor w (≥ 2 ends) against at most one zero-end neighbour of r (the possible even neighbour). r gains one end on top of an odd count ≥ 1.
- (d) **Second even neighbour of degree ≥ 4.** The new root is v. Every H-neighbour of r has an end, and the donor is u (odd, ≥ 1 end).
- (e) **Both even neighbours of degree 2.** They are nonadjacent, since otherwise r is a cut vertex. D = B − ru + uv has the same order and size and a smaller prescribed degree. Two ends at u lie on distinct rows; removing uv exposes v, or a lost singleton pays for a split; then Fan as in (d).

Every move preserves or lowers the order in the right lexicographic sense.

**Claim "Thm 113 applies again to (H, w)".** It needs only that the order n is least. That holds, so the new parity apex on the even set of H (in which w has replaced r) is 3-connected by §4.2.

**Verdict:** SOUND, given F4.

### 4.4 Theorems 162–164 (pp. 171–173)

- **Thm 162.**
  - The two-path cover of a cycle with a K4 completion on xy: (z…xyuv) and (z,y,v,x,u). Correct, also for triangles.
  - Budget: a Lovász decomposition with a paths and j cycles, a + j ≤ k, gives ≤ k + j paths on order 2k + 2j.
  - The implication is applied j times, each time to a connected even-order graph containing the supporting edge.
  - Odd orders are handled by a leaf.
  - SOUND.
- **Cor 163.**
  - Deleting a matching F that meets all cycles of H[even] leaves the remaining even set inducing a forest, and its induced graph in H − F equals that in H.
  - Pyber's Theorem 0, applied per component, gives ⌊n/2⌋.
  - Each pair returns at +1: the six edges are covered as P₁·xuv, P₂·yv and (u,y,x,v), or, when x and y end the same row, by the cycle construction of Thm 162.
  - Tested edges stay on even-site cycles, because the gadget vertices are cubic and old parities are preserved.
  - SOUND.
- **Cor 164.**
  - Minimising (#even, order) gives:
    - no eligible pair;
    - for even–even nonbridges, p(H − xy) = k and p(H) = k+1;
    - p(H^{xy}) ≤ k+1 by the Cor 163 return;
    - exactly one eligible pair in H^{xy};
    - xy can be chosen on a shortest, hence induced, even cycle, which exists by Pyber.
  - The bridge argument (⌈n₁/2⌉ + ⌈n₂/2⌉ − 1 ≤ k) and the remark p(H + ab) = k are correct.
  - SOUND.
- **p. 173 examples.** The K3 cover by two paths and the 16-vertex example (p(H) = 6, p(H^{xy}) = 5) were verified by computer: the five rows are valid, the graph is 2-connected, and the cycle degrees are 4, 6, 6, 6, 8. The lower bound p(H) ≥ 6 follows from the shore argument, which is correct.

### 4.5 §18 (pp. 103–126), lighter pass

§18 is **not used** by Theorems 113 or 114. Theorem 113 cites only Proposition 94, and only for the private-leaf trimming device.

**Re-derived and SOUND.**
- **Lemma 81** (stitching budget). Both numerators are odd under a + t + ε odd, giving a total of k + ε − 1 + 1. The root-end parity is correct in both cases.
- **Lemma 82** (induced cycle with connected complement). The maximality and substitution argument and the two-vertex separation of a gap are correct, including the gap that wraps around through αβ.
- **The line-graph routing device.** Induced arcs give simple physical paths to the first terminal.
- **Thm 83.** The parity choice of t, the lost-port bookkeeping and the m ≥ 4 nesting argument are correct; the m = 3 sub-case is vacuous (F8).
- **Cor 84.** The classification of 3-edge bipartite crossing graphs is complete, and the "after deleting an edge" clause is correct.
- **Lemma 87, Thm 88, Cor 89.**
- **Thm 92**, all three root cases: the joins in the last case use four distinct rows, and the x-end count is correct.
- **Cor 99.**
- **Props 94 and 96, Cor 95.**
  - The order and parity bookkeeping is correct in all four parity combinations of (a, d).
  - In Cor 95, the three-row exchange when one port has even crossing multiplicity is correct.
  - So is the three-mark count ⌊(N−3)/2⌋ + 3 = ⌈N/2⌉ + 1.
- **Thm 97**, the identification argument: the merged vertex is the unique even vertex, the graph stays simple, and the auxiliary edge is inserted in the one row that pairs the x-incidence.
- **Thm 101**:
  - the root on the pair;
  - the contraction case at odd order;
  - the full even-order table (add/delete/keep), including the two-component analysis that reduces to Prop 93 and the end-transfer bookkeeping;
  - the one-common-neighbour case: D is connected, the protected-node routing works, and so does the r = s split with D + ab;
  - the two-common-neighbours case (square or diamond).
- **Thm 103**, the three-tip and five-tip cases. The cited Lemma 66, Corollary 68 and Lemma 102 were taken as given.
- **Prop 105.**

**Not re-derived in full.** Props 85, 86, 93, 104, 107–112; Cors 90, 98; Thm 100; the U/V split cases of Thm 97. Cor 98 also relies on an unavailable finite check (orders 4, 6, 8).

## 5. Things the referee could not check

- Fan [14] Lemmas 3.3/3.4 verbatim (F4).
- Fan–Hou–Zhou [15] verbatim (F3).
- Shaik [25] (F2).
- The supplement: ApexConnectivity.lean, FiveSiteFan.lean, the §19 substitution checkers, the K_i certificate trees, and the Cor 98 catalogue check (F5).
- The full §18 items listed above.

## 6. Computations

Scripts are in `/tmp/claude-0/-home-user-Manuscripts/a40c9215-4484-5bc3-a3e1-2bba3a808810/scratchpad/a2/`. They use `tools/pathnum.py` (exact CP-SAT).

RESULTS_PLACEHOLDER

## 7. Recommended fixes

1. **F1.** Restate the finite-order clause of Theorem 59 as an explicit marked-bound statement.
2. **F2, F3, F4.** Quote [14] Lemmas 3.3/3.4 and the theorem of [15] exactly. Mark the Shaik-dependent conclusions (two universal vertices at d = 6; Thm 144 and onwards) as conditional.
3. **F6.** Add the single-deletion sentence, or the apex lemma of §4.2, to the proof of Theorem 114.
4. **F7.** Restate Theorem 113 under hypotheses (i) and (ii). This makes the re-applications in Thm 144, Thm 145 and Cor 146 immediate.
5. **F8.** Delete the m = 3 paragraph of Thm 83, or replace it by the two-edge-cut contradiction. Rename the retained port so it does not clash with the root r.
6. **F10.** Fix "K2 ∨ K3" to "K2 ∨ K̄3".
7. **F5.** Publish the supplement. Until then, the d = 6 table on p. 131 is unverified.
