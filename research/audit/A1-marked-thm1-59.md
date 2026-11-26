# Audit A1: marked-reduction, Theorems 1, 7, 57 and 59

**Paper.** "Cut vertices and cycle intersections in Gallai's path decomposition problem" (marked-reduction.pdf, 192 pp., Nov 24 2026).

**Scope.** I audited these results and every step they depend on:

- **Theorem 1.** §1, pp. 2–3; §2, pp. 4–7; §2.1, pp. 7–8.
- **Theorem 7.** Lemma 6 and Theorem 7, pp. 12–14.
- **Theorem 57.** Theorem 57 with its degree-two refinement, pp. 81–83.
- **Theorem 59.** Theorem 59 and its proof, pp. 84–85.

Some nearby material is not a dependency of these four theorems. I read it at lower depth:

- §1: semi-cliques, the "sharp simultaneous version".
- §2.2: Theorem 4 and Lemma 5.
- §2.4: Proposition 8.
- §3: Propositions 9 and 10.
- p. 85: the deletion criterion.

Page numbers are the printed numbers, which equal the PDF page indices. I checked garbled formulas against the PDF images: pp. 2–7, 12–13, 81–82 and 84–85.

## 0. Overall verdict

**No ERROR found.** Every step in the chain Theorem 1 → Theorem 7 → Theorem 57 → Theorem 59 is SOUND as written, up to the expository points below. Specifically:

- I reconstructed and checked by hand:
  - the minimal-counterexample case analysis of Theorem 1 (bridges, leaves, cut vertices, the pendant configuration);
  - identity (2);
  - the reduction to even marks;
  - the parts-and-paths reduction;
  - the matching-cut removal;
  - the three-copy host of Theorem 57;
  - the bridge-double and diamond-double identities.
- The checkable identities agree with exact computation in every instance I ran: 0 mismatches over about 2,200 instances (§3).

The weaknesses are all expository: imprecise wording, unproved one-line facts, and one theorem sentence that is true only in context. None needs a new idea. Ten items are listed as GAP or REMARK in §2, with suggested fixes in §4.

## 1. Verdict table

| # | Step | Page | Verdict |
|---|---|---|---|
| S1 | Definition of q(F,S) and the marked bound (1); summation over components | 2 | SOUND. See G3: notation scope. |
| S2 | Cone identity h = \|S\| + 2q(F,S) on X = F + z | 3 | SOUND (verified). |
| S3 | p(W(F,S)) = \|S\| + 2q + 1 and \|W\| = 2\|F\| + 2, eq. (2) | 3 | SOUND (verified). See G2: wording of the "cannot return through z" step. |
| S4 | Marked bound on (F,S) ⇔ ceiling on W(F,S); one mark ⇒ ordinary ceiling | 3 | SOUND. |
| S5 | Exact bridge formula q = α₁ + α₂ + 1[β₁>α₁ ∧ β₂>α₂] | 4 | SOUND (verified). |
| S6 | Bridge reduction: no bridge with both sides ≥ 2 vertices | 4 | SOUND. See G4: an unproved one-line identity. |
| S7 | Leaf deletions in all four cases (marked or unmarked leaf, marked or unmarked neighbour) | 4–5 | SOUND. |
| S8 | Residual pendant case: odd J, unmarked leaf at unique mark v, leaf unique, J bridgeless, p(J) = k+1, d_J(v) odd | 5 | SOUND. |
| S9 | Cut vertex, x marked: odd/odd floors; even side with an added leaf; three outcomes; join | 5 | SOUND. |
| S10 | Cut vertex, x unmarked: temporary mark; both r_i even; unmarked tight side; split-and-double-join | 5–6 | SOUND. |
| S11 | Bridgeless with no cut vertex ⇒ 2-connected; same for leaf plus bridgeless core | 6 | SOUND. |
| S12 | Sufficiency in Theorem 1: final contradiction via (A) or (B) | 6 | SOUND. |
| S13 | Necessity of (B): leaf at x, mark x, trim, parity | 6 | SOUND (verified on K5 − e). |
| S14 | Triangle replacement of a marked leaf | 6 | SOUND. Not needed for Theorem 1. |
| S15 | Transfer through a block tree | 6–7 | SOUND. |
| S16 | Rank inequality ρ(A∪O) ≥ ρ(A) + ⌈o/2⌉ via the endpoint multigraph | 7 | SOUND (verified). |
| S17 | A = ∅ case, including use of three ends at an odd mark | 7 | SOUND. |
| S18 | Restriction of (A) to even marks (Theorem 1, last sentence) | 2, 7 | SOUND only for the conjunction (A) ∧ (B). See G1. |
| S19 | Private-leaf identity q(G,A) = p(L_A(G)) − \|A\| for even A | 8 | SOUND (verified). |
| S20 | Lemma 6, both inequalities | 12–13 | SOUND. |
| S21 | Theorem 7: induction over block order; L_A(B) step; odd marks | 13 | SOUND. See G7: implicit use of §2.1. |
| S22 | Matching cut ⇒ admissible 2-part decomposition with connected sides | 13 | SOUND. |
| S23 | Three-clique example: 2-connected, no matching cut, p = 3h | 13–14 | SOUND (verified for h = 1). |
| S24 | Theorem 57 claim p(H⁺) ≤ ⌊(h+ℓ)/2⌋: host has no matching cut; split count | 82 | SOUND (no-matching-cut part verified). See G8. |
| S25 | Theorem 57: both tests on B with no matching cut, then Theorem 7 | 82 | SOUND. |
| S26 | Theorem 57 necessity; "at most one matching cut" | 82 | SOUND. |
| S27 | Profile (k, k+1, k+1) of a failed bridge test | 82 | SOUND. |
| S28 | Degree-two suppression; K₃–K₄ example | 82–83 | SOUND (example verified). |
| S29 | Theorem 59: X = B + z ∈ C; marked inequalities from rooted tests on X | 85 | SOUND. |
| S30 | Theorem 59 singletons: even order (test 1 or Lovász); odd order via B + w | 85 | SOUND. |
| S31 | Theorem 59 finite-order form ("through core order m+1") | 84–85 | SOUND. See G10: could be stated more sharply. |
| S32 | p(B⁺) = F₁(B,x); bridge double has path number 2F₂ − 1 | 85 | SOUND (verified). |
| S33 | Diamond optimum 3; diamond double has path number 2F₃ − 1 | 85 | SOUND (verified). See G9: tacit d_B(x) ≥ 3. |
| S34 | External: Lovász (paths and cycles ≤ ⌊n/2⌋) | 7, 85 | SOUND. Exactly the classical statement. |
| S35 | External: Javadi–Miralaei (Wu's conjecture) | 3, 10–11 | Statement matches its use. Not load-bearing for Theorems 1/7/57/59. |

## 2. Detailed findings

### 2.1 Theorem 1, sufficiency (pp. 4–6)

I re-derived every inequality. Notation: n = |F|, u = n − |S| is the number of unmarked vertices, and all sub-instances are connected with a nonempty mark set.

**Bridge formula and reduction (p. 4).**

- The three competing costs α₁+α₂+1, β₁+α₂ and α₁+β₂ arise from cutting the bridge path at its midpoint. With β_i ≥ α_i integral, this gives the formula.
- The reduction uses the following bounds:
  - α_i ≤ ⌊t_i/2⌋, from the marked bound on (J_i⁺, S_i ∪ {ℓ_i});
  - min{α_i+1, β_i} ≤ ⌊(t_i+1)/2⌋, from (J_i⁺, S_i);
  - α_i = q(J_i, {root}) ≤ ⌊(t_i−1)/2⌋ when S_i = ∅.
- The case split (some t_i even, or both odd) then gives q ≤ ⌊(t₁+t₂)/2⌋ in all four sub-cases. This includes t_i = 0, where α_i = β_i = 0 is forced.
- J_i⁺ has at most n − 1 vertices because the other side has at least 2.

**Leaves (pp. 4–5).** The four cases are exhaustive and each budget computation is correct:

- **Marked leaf, other marks exist:** use F − w with S − w, and assign the leaf edge singly.
- **Marked leaf, sole mark:** mark its neighbour y in F − w; the budget is ⌊(n−2)/2⌋.
- **Unmarked leaf at an unmarked neighbour:** use F − w with S + y, at budget ⌊u/2⌋ − 1, plus one.
- **Unmarked leaf at a marked neighbour:** either u is even (budget u/2 − 1, plus one), or another mark exists (unmark y).
- **Residue:** u is odd and S = {v}, so |J| = n − 1 is odd.

**Pendant configuration (p. 5).**

- A second leaf must also be of the residual type, at v. Deleting both and adding the path w v w′ unassigned recovers the budget exactly.
- J is bridgeless. A pendant edge of J at a leaf a ≠ v would be a second leaf of F. A pendant edge of J at v is a bridge of F with sides {v, w} and J − v, both of size ≥ 2 once |J| ≥ 3.
- From q(J,{v}) ≤ k and p(J) = k+1 we get an optimum with an end at v. Parity then forces d_J(v) odd, or else two ends would exist.

**Cut vertex (pp. 5–6).** Write r_i for the unmarked vertices of J_i other than x.

- *x marked.*
  - Both r_i odd: the duplicate-x unit is absorbed.
  - Some r_i even: the leaf-augmented even side (budget r_i/2) yields one of three outcomes: one unit of slack; x unused; or two distinct x-ended paths, one of them carrying x.
  - In the third outcome, joining the other side's x-assigned path R to the trimmed path P′ (not to Q) keeps the cost. P′ ≠ Q because x is interior to the untrimmed P.
- *x unmarked.*
  - Temporary marks cost at most one extra, which is absorbed when some r_i is odd.
  - If both r_i are even and both sides have real marks, the sum r₁/2 + r₂/2 meets the budget.
  - If both r_i are even and J₁ is unmarked and tight, the leaf trick gives two x-ends in a (k+1)-partition of J₁.
  - A J₂ path ending at x is joined once to one of them. Otherwise a J₂ path through x is split and both halves are joined to distinct J₁ paths, for a net saving of 1.
  - All joins are simple because the sides meet only at x.

**Closing (p. 6).** In a connected bridgeless graph, every cut vertex splits it into sides of order ≥ 3. A two-vertex side would be a bridge. The final configurations are therefore a 2-connected F, which contradicts (A), or J plus a leaf with J 2-connected, odd, tight and d_J(v) odd. In the second case (B) gives ≥ 3 ends at v: extend one ending path by the leaf and assign another to v, at cost k. Every case is covered.

**Necessity (p. 6).** Gallai applied to W gives the marked bound for J + leaf with S = {x}. This forces k+1 paths with x assigned and the leaf edge on a nontrivial path different from the x-assigned one. Trimming gives two x-ends, and parity gives three.

### 2.2 Eq. (2) and the cone identity (p. 3)

- **h = |S| + 2q.** After splitting at internal occurrences of z, exactly |S| = d_X(z) paths contain z, each with one end outside z. The other paths lie in F and are unassigned, and the continuations give a valid assignment. Conversely, prepend spokes to assigned paths.
- **p(W) ≥ h + 1.** z is a cut vertex of W with three lobes (copy 1, copy 2, and the leaf). A simple path meets z at most once. Cutting each path at z when it changes lobe preserves all ends away from z. Each copy then carries a partition of X with ≥ h ends away from z, and the leaf adds one more. So 2|P| ≥ 2h + 1.
- **p(W) ≤ h + 1.** Pair the z-ends of the two (identical) copies. The numbers match, and paths with z interior are left alone. Each joined path is simple because the copies share only z. Adding the pendant edge gives (2h − 2A + 2A)/2 + 1 = h + 1 paths, where A is the number of z-ended paths per copy.
- **G2 (wording).** The phrase "since a simple path cannot return through z" is imprecise. A path can pass through z with both neighbours in the same copy. The correct justification is "z is a cut vertex visited at most once; split each path at z when its two z-neighbours lie in different lobes". The argument is otherwise complete.

### 2.3 Even marks suffice (§2.1, p. 7) and the private-leaf identity (p. 8)

**Rank inequality.**

- The endpoint multigraph is loopless, since no simple path has both ends at one vertex, and its degrees have the parity of d_G.
- The deficits in assigning S are exactly the tree components lying wholly in S, isolated sites included.
- A newly enclosed tree contains a positive even number of O-sites, so ρ(A∪O) ≥ ρ(A) + ⌈o/2⌉.
- The floor inequality ⌊(n−a)/2⌋ − ⌈o/2⌉ ≤ ⌊(n−a−o)/2⌋ holds.

**A = ∅.** The four sub-cases are correct. In the tight case, the bipartite site–row incidence graph has maximum degree 2, so König's theorem gives a matching of size ≥ o/2 + 1.

**Restriction to even marks.**

- p(G) ≤ ⌈n/2⌉ follows from an even singleton if one exists. Otherwise every vertex is odd, so n is even, and Lovász gives n/2 paths with no cycles.
- In the odd tight case, (B) is required, and an even vertex always exists since n is odd.

**Private-leaf identity.**

- A row containing two leaves keeps an original edge, because the supports are distinct.
- A support that is not a singleton keeps ≥ 1 end, hence ≥ 2 by even degree.
- Hall's condition holds because each row has ≤ 2 ends.

**G1 (statement precision, p. 2).** Theorem 1 ends: "In the first assertion it suffices to test nonempty sets consisting entirely of even-degree vertices." The proof (p. 7) establishes this only for the conjunction. Purely odd markings on odd tight graphs are recovered from assertion 2. The author acknowledges this on p. 7: "it does not give the odd-root assertion from all-even markings…". Read in isolation, the sentence claims (A_even) ⇔ (A) for assertion 1 alone, which is not proved.

### 2.4 Lemma 6 and Theorem 7 (pp. 12–14)

**Lemma 6.**

- An end v of R can receive a path only if V(R) ∩ V_i = {v}. So the appended local path meets R only at v.
- Two receiving ends of one R lie in different parts, so the two appended paths are disjoint.
- Assignments use distinct sites, so each local path is used once.
- The second inequality follows by doubling the floors.

**Theorem 7.**

- Strong induction on block order is valid. Blocks in the restricted class satisfy the tests by assumption, and the others satisfy them by the inductive step. The parts B_i and the leaf-enlarged parts have only blocks of order < |B|.
- With U equal to all 2|R| distinct ends, d = 0, so p(B) ≤ ⌊|B|/2⌋ and (B) is vacuous. The same holds for L_A(B), with leaves kept in their parts and conditions 1–3 preserved.
- Odd marks follow by the rank gain.
- From a matching cut, an inclusion-minimal disconnecting submatching gives a bond with exactly two connected shores. Using each cut edge as a one-edge path satisfies conditions 1–3.

**G7 (implicit step, p. 13).** "Assume the two tests on the restricted class." If the tests are taken in their even-mark form (as Theorem 1 allows), the block transfer needs the marked bound for *all* markings on smaller restricted-class blocks. This follows from §2.1 using (B) and Lovász, but is not said. Add one sentence.

**G6 (wording, p. 2).** "blocks assembled from three or more parts" does not match Theorem 7, which allows ≥ 2 parts. Matching cuts are exactly the 2-part case.

The three-clique example (2-connected, no matching cut, p = 3h, and the 3h two-edge interpart paths satisfy conditions 1–3) is correct. I verified it for h = 1.

### 2.5 Theorem 57 (pp. 81–83)

**The claim's host.**

- Each copy of H, being connected without a matching cut, is monochromatic in any matching cut of the host.
- An identified common vertex has two edges into every copy. In the single-support case, K_{3,ℓ} with ℓ ≥ 2 does the same job.
- The split count is right: the total degree at common vertices is 3ℓ, and o odd common vertices force o ends. Hence 3p(H⁺) ≤ |P| + (3ℓ − o)/2, with c − o ≤ 1.
- The final bound 6p ≤ 3(h+ℓ) + 2 gives p ≤ ⌊(h+ℓ)/2⌋ in both parities.

**G8 (minor).** The integrality step "6p ≤ 3(h+ℓ)+2 ⇒ p ≤ ⌊(h+ℓ)/2⌋" is correct but terse. Spell out the odd case: p ≤ (h+ℓ)/2 + 1/3 < (h+ℓ+1)/2.

**The tests on B.**

- Two or more even marks use the claim plus the private-leaf identity.
- An even singleton at even order uses the bridge double: p = 2p(B⁺) − 1 ≤ 2k gives p(B⁺) ≤ k.
- At odd order, two leaves at x plus tightness give two x-ends, and three for odd x.
- The rest follows from §2.1. A bridge host has exactly one matching cut.

**Failed bridge profile.** If p(B) ≤ k − 1, one split gives F₂ ≤ k. So p(B) = k with zero root ends. Three leaves give at most k + 1 rows, and every leaf survives trimming. So F₄ ≤ k + 1, F₂ = k + 1 and d(x) ≥ 4. SOUND.

**Degree-two refinement.**

- Suppression preserves "no matching cut": put y on a's side, so that ab becomes yb. Partitions lift.
- For cores, the failed root has degree ≥ 4, so it is not y. The two-leaf bound on H = B/y then exposes x within k paths.

The K₃–K₄ example is correct (verified).

### 2.6 Theorem 59 (pp. 84–85)

**From rooted tests to marked tests.**

- X = B + z lies in C. It is 2-connected because z has t ≥ 2 neighbours, and B monochromatic plus t ≥ 2 edges at z rules out a matching cut.
- By the cone identity, t + 2q = min(2|P| − b(z)).
- If n is even and t odd, test 2 at z (|X| = n+1 odd) gives ≤ n − 1. If n is odd and t even, test 1 gives ≤ n − 1. Either way q ≤ (n − 1 − t)/2 = ⌊(n−t)/2⌋.
- When n − t is even, removing one mark gives the bound, and putting it back cannot raise the cost.
- Singletons:
  - even order: test 1 at an even vertex, or Lovász when all vertices are odd;
  - odd order: X′ = B + w with w adjacent to x and one other vertex is in C, and test 1 at w followed by trimming gives cost ≤ k.
- (B) is test 2 directly.
- The finite-order bookkeeping is correct: tests are used at orders n and n + 1 ≤ m + 1, and the Theorem 7 induction and block transfer stay within blocks of order ≤ m.

**Bridge double.** p(B⁺) = F₁(B,x): trim the leaf, or if it is a singleton, use the saved row to split at x. Cutting the bridge adds exactly one path. F₁ = F₂ for even d(x). Hence p = 2F₂ − 1 on 2n vertices. With n = 2k, the ceiling 2k is equivalent to F₂ ≤ k.

**Diamond double.**

- *Upper bound.* uabv, ub and va are joined to four reserved root ends in the two cores. These are distinct rows, because a path has at most one end at x. This gives 2F₂ − 1 paths.
- *Lower bound.* Cut at the j transitions at each terminal, and record c ∈ {0, 2} diamond ends (parity) and e core ends. The repair cost satisfies 1[c=0] + 1[e<2] ≤ 2 − j in all three cases j = 0, 1, 2. So each terminal adds at most 2 paths, and |P| + 4 ≥ 2F₂ + 3.
- Since d(x) is odd, F₂ = F₃. The ceiling 2k + 2 on 2n + 2 = 4k + 4 vertices is equivalent to F₃ ≤ k + 1.

**G9 (tacit hypothesis).** The repair step for e < 2 (so e = 1) splits a core path through x internally. This needs d_B(x) ≥ 3, which holds because B is 2-connected and d_B(x) is odd. The identity fails for d_B(x) = 1, where F₃ = ∞. One clause fixes it.

**G10 (remark, not a defect).** The finite-order form could say exactly which order-(m+1) instances are used: cones B + z (z adjacent to ≥ 2 marks) and B + w (w of degree 2). This matters for later finite verifications (Theorems 113/145).

### 2.7 External results (question f)

**Lovász [18].** "Every graph on n vertices decomposes into ≤ ⌊n/2⌋ paths and cycles." It is used on p. 7 and p. 85 only in the all-odd case: n is even, the n forced ends force ≥ n/2 paths, so there are no cycles. This is exactly the classical theorem, and the use is correct.

**Javadi–Miralaei [17].** The arXiv 2403.17290 abstract states a full proof of Wu's conjecture: for any H ⊆ K_{2n+1} with n edges, some Hamilton decomposition puts each edge of H on its own cycle. The abstract lists no small-case exceptions; I did not check the proof.

- The use on p. 3 needs exactly k edges, H ∪ E(Q) with |H| = m and |Q| = k − m, which are disjoint because Q ⊆ J. This matches.
- Opening each cycle at its rainbow edge gives the end count d_H(w) + 2·1[w ∈ Q], which I verified.
- This is **not** used by Theorems 1/7/57/59. It feeds only the semi-clique remarks and Theorem 4.
- The citation is to a 2026 Discrete Math. version that I did not inspect.

**Fan–Hou–Zhou [15], Fan [14] Lemmas 3.3–3.6, Xie [28], Shaik [25].** These appear in §2.1 side results and §3 (Proposition 10). They are not in the four-theorem chain, and I did not verify them. Two points:

- The manuscript paraphrases FHZ as "no two triangles meeting in exactly one vertex and every block of max degree ≤ 3". That paraphrase should be checked against the published statement before Corollary 58 or §19 lean on it. My web search could not locate the paper's exact statement. Fan 2005 and Botler–Sambinelli 2021 have related but different hypotheses.
- Shaik is an unrefereed preprint, as already flagged in the reader notes.

### 2.8 Off-chain material read at lower depth

- **§1, "full affirmative answer to Question 1.1 … by the semi-clique partition above" (p. 3).** The conclusion is right. Question 1.1 implies Gallai directly: even order via a pendant leaf, and odd semi-cliques have p = k + 1. The attribution to "the semi-clique partition" is loose. Minor.
- **Proposition 8 (pp. 14–15).** SOUND. I checked all five cases of the reverse inequality. Notation clash: L denotes Σℓ(v) in the statement but ℓ(v) for one vertex in the proof.
- **Proposition 9 (p. 15).** SOUND. The component bookkeeping is correct in all split cases, including the case where z is isolated in the endpoint multigraph.
- **Theorem 4.** Verified exhaustively for k = 2 (§3). k = 3 was not completed because of time limits.
- **Proposition 10.** Not audited (it depends on Fan's lemmas).
- **Deletion criterion (p. 85).** The formula F_{ε+2j} = h + ε + min{u + max(j,s)} and the translation into u ≤ L − 1 and u + s ≤ L are correct as derived. Not tested numerically.
- **Lemma 60 (p. 86).** SOUND on reading.

## 3. Computational checks

All checks are exact CP-SAT computations. I used `pathnum.py` for path partitions, plus a direct marked-cost solver: path variables, site-assignment variables, and the objective |P| − (number assigned).

Scripts are in `/tmp/claude-0/-home-user-Manuscripts/a40c9215-4484-5bc3-a3e1-2bba3a808810/scratchpad/audit/`:

- `mq.py`
- `chk_eq2.py`
- `chk_leaf_rank.py`
- `chk_bridge_tri.py`
- `chk_doubles2.py`
- `chk_struct.py`
- `chk_thm4.py`

| Claim | Instances | Result |
|---|---|---|
| Eq. (2): p(W(F,S)) = \|S\| + 2q + 1; cone identity min(2\|P\| − b(z)) = \|S\| + 2q; marked bound itself; \|W\| = 2\|F\| + 2 | All connected F with n ≤ 4 and all nonempty S; n = 5 with ≤ 7 edges and 6 random S each. 210 instances | 0 mismatches |
| Private-leaf identity q(G,A) = p(L_A) − \|A\| for even A | All connected G with n ≤ 5 and all even A; n = 6 with ≤ 9 edges, sampled. 446 instances | 0 mismatches |
| Rank formula ρ = \|S\| − #trees ⊆ S, and ρ(A∪O) ≥ ρ(A) + ⌈o/2⌉ | Random path partitions of random G(n,p), 3 ≤ n ≤ 8. 1,391 instances | 0 failures |
| Bridge formula q = α₁ + α₂ + 1[β₁>α₁ ∧ β₂>α₂], with α and β computed independently by constrained solves | 120 random bridge-joined pairs, sides ≤ 4 vertices, random S | 0 mismatches |
| Triangle-replacement equivalence | All tight odd J of order 3; K5 − e at both vertex types | Agrees |
| Theorem 1 (B) mechanism on K5 − e: q(K5−e + leaf, {x}) = 2 = budget; F₃(K5−e, x) = 3 = k+1 | — | Agrees |
| Bridge double p = 2F₂(B,x) − 1 and diamond double p = 2F₃(B,x) − 1 | All connected B of order 4–6 (orders 5–6 limited to ≤ 8 edges), every eligible root: bridge at n = 4 and 6, diamond at n = 5 with d(x) ≥ 3. 210 instances (182 bridge, 28 diamond), 32 of them with B ∈ C. The identities also hold outside C, as the proofs predict: neither uses 2-connectivity beyond d(x) ≥ 3 | 0 mismatches, 0 timeouts. Dense members of C also agree: K5 − e diamond double (F₃ = 3, p = 5) and K6 − PM bridge double (F₂ = 3, p = 5). W5 has no even root, so it was not tested |
| Theorem 57 host has no matching cut | Every H with 3 ≤ \|H\| ≤ 6 that is connected without a matching cut, every support multiset with ℓ ∈ {2, 3}. 4,222 hosts | All without a matching cut |
| Three-clique example, h = 1 (9 vertices, 15 edges) | — | 2-connected, no matching cut, p = 3, interpart ends distinct |
| K₃–K₄ + y example | — | No matching cut; after deleting y, a matching cut exists |
| Theorem 4, k = 2 (K5 − H, m ≤ 3) | Marked bound for every nonempty S: 248 instances. Omission criterion at m = k + 1: 20 instances | 0 failures (k = 3 timed out) |
| Wu/Javadi–Miralaei statement | arXiv 2403.17290 abstract | Matches the use |

## 4. Suggested fixes (all local)

1. **G1, p. 2.** Rephrase the last sentence of Theorem 1: "In the presence of the second assertion, the first may be restricted to nonempty sets of even-degree vertices (§2.1)."
2. **G2, p. 3.** Replace "since a simple path cannot return through z" with: "z is a cut vertex of W and lies on each path at most once; splitting each path at z when its two neighbours there lie in different lobes yields partitions of both copies of X and of the pendant edge, with all ends away from z preserved."
3. **G3, pp. 2, 7, 12.** Define q(F, ∅) = p(F) in §1, or note that Lemma 6 uses the §2.1 definition, which allows U_i = ∅.
4. **G4, p. 4.** Add: "α_i = q(J_i⁺, S_i ∪ {ℓ_i}): an unassigned open path can be assigned to the leaf." Clarify that a "free" open path is uncounted and, without loss of generality, unassigned.
5. **G6, p. 2.** Change "three or more parts" to "two or more parts (two parts with a matching between them is a matching cut)".
6. **G7, p. 13.** Add after "Assume the two tests on the restricted class": "by §2.1 these give the marked bound for every nonempty marking on each such block."
7. **G8, p. 82.** Spell out the integrality step for odd h + ℓ.
8. **G9, p. 85.** Add "(possible since d_B(x) ≥ 3 by 2-connectivity)" to the split at a core terminal.
9. **G10, p. 84.** Optionally state which order-(m+1) instances the finite-order form uses: cones B + z with d(z) ≥ 2, and B + w with d(w) = 2.
10. **§2.4.** Rename the per-vertex L in the proof of Proposition 8.
11. **External.** Before relying on Fan–Hou–Zhou [15] downstream (Corollary 58, §19), quote its exact published hypothesis.
