# Cross-paper connections and candidate uniform statements

*Started 2026-11-26.*

This file looks for links between results in different papers, especially links that could turn a fixed-parameter result into an all-n or all-d statement. Every entry is graded:

| Grade | Meaning |
|---|---|
| **Observed** | Read off the papers. |
| **Tested** | Computational evidence, recorded in `experiments.md`. |
| **Conjecture** | Tested but not proved. |
| **Refuted** | A counterexample is known. |

---

## A. Housekeeping connections

These are cross-paper facts the papers themselves do not state.

1. **MR Thm 144 can probably drop Shaik.**
   - The Shaik citation is an unrefereed Hexagon preprint, dated 16 Oct 2026. It is used at the "r ∈ T" step.
   - In that step the even sites other than r number at most four, so their induced graph is automatically subcubic. Botler–Sambinelli Thm 13 (refereed) then gives the floor.
   - six-even-root-shapes already argues this way and never uses Shaik.
   - **Action:** rewrite the step to cite Botler–Sambinelli, and check the "two universal vertices" remark (MR p.129) separately.
2. **Superseded results in the six-even program:**
   - six-even-incidence §4: its "open" circulant family is covered by six-clique Thm 1. Its complete-core constraints are superseded by six-clique Thm 6.
   - five-odd-neighbors §4.3 (U = K6, four-contact exterior) cannot fail, by six-clique Thm 6.
   - two-exterior-contacts is subsumed by six-even-incidence Thm 1(2) for the single-root bound.
   - At six sites, ordered-even-clique and short-faithful Thm 7 are subsumed by six-clique, so their thresholds of 88/252 and 76 are unnecessary there.
   - **Action:** cross-cite these, or merge them into a single d = 6 paper.
3. **Parity rules out complete joins in the 66 root patterns.** Every one of the 66 fixed-root patterns of six-even-root-shapes has a core vertex of core degree 5. So the complete-join hypothesis of short-faithful Thm 5 can only arise for isolated-root cores.
4. **The 3c-dependent closures and RS's descent don't compose.**
   - four-exterior-neighbors Part IV Props 7, 8, 12, 13, 15 and §5.1 (and hence MR Cor 138) need J to be 3-connected.
   - RS's isolated-root descent produces only a connected host.
   - The route through MR Thm 144 keeps 3-connectivity. **The final d = 6 write-up must take that route.**
5. **Different notions of "minimal counterexample".**
   - separating-pairs: least even order, rooted.
   - root-endpoint-costs: order, then edges, then leaves.
   - marked-reduction: least order of the pair of tests.
   - The odd witness of separating-pairs: order, then edges.

   Properties proved for one notion are not automatically available for another. Section E is a synthesis that keeps track of which properties are compatible.
6. **The block-degree dependency is wider than the index says.** See `STATUS.md` §6.2. Only Thm 3 (Δ ≤ 7) is free of the unreplayed computations.

---

## B. The endpoint-profile structure

**Grade: Conjecture (Tested at n ≤ 6; n = 7, 8 running).**

### The observation

The exact endpoint theorems in the collection all characterise the achievable end vectors by parity, a degree box and the total count:

- separating-pairs Thm 14.1 (dense): b ≡ d (mod 2), b(v) ≤ min{d(v), 2k − d(v)}, Σb = 2k.
- star-deletion Thm 1: the same three conditions.
- odd-semi-clique-boundary Thm 11: every vector with b ≥ d_H and the right total.
- six-clique Thm 1: any 3 of the 6 even vertices can be doubled.
- dense-exact-counts: profiles with caps.

Sets cut out like this are **M-convex sets**: the integer points of an integral base polyhedron, after halving the parity.

### Conjecture M

Let C_k(G) be the halved endpoint vectors c, with b(v) = (d(v) mod 2) + 2c(v), over all decompositions of G into exactly k paths.

**Conjecture M:** for every graph G, C_{p(G)}(G) is M-convex. That is, for x, y ∈ C_p and u with x(u) > y(u), there is v with x(v) < y(v) such that x − e_u + e_v and y + e_u − e_v both lie in C_p.

**Evidence:** it holds for all 142 connected graphs on ≤ 6 vertices. It is **false at k = p + 1**: there are 3 violations at n = 6. So the optimum level matters.

### Why it would matter

1. **The rooted test becomes a loop question.** The even-order rooted test, which is equivalent to Gallai, is nontrivial only when p(B) = |B|/2 (root-endpoint-costs §1). It asks that no even vertex is a *loop* of C_p(B), i.e. never exposed. Under Conjecture M, C_p(B) is the base family of an integral polymatroid with rank function f(X) = max over optimal decompositions of the number of end-pairs in X. The rooted test is then exactly f({r}) ≥ 1 for even r, a statement with a min–max dual. The "cut inequalities" of root-endpoint-costs are natural candidates for that dual.
2. **Single swaps suffice.** Under Conjecture M, if r is exposable at all, then from every optimal decomposition there is an optimal one with end vector c − e_u + e_r. Fan's addible-edge transfer is exactly such a swap, b ↦ b + e_a − e_x. The matched-subcubic Lemma 2 criterion (a unique perfect matching, so an acyclic restoration order) is the classical unique-base criterion. So the d = 6 case analyses are all searches for exchange sequences in this one structure.
3. **Gluing is convolution.** The cut-vertex composition laws (fractional-paths Thms 8, 10) and the two-separator formula (two-vertex-separators Thm 1) combine local endpoint records. M-convex sets are closed under such convolutions, which is consistent with the local-records warning of two-vertex-separators Thm 2.

**Next tests:**
- n = 7, 8 exhaustive (running);
- whether the matroid on even vertices at p = n/2 has any further uniform property (connectivity, no parallel pairs), which would be a strong rooted statement.

---

## C. A level-descent formulation of the deletion test, uniform in d

**Grade: Conjecture; testing.**

### Setting

MR Thm 114(i) concerns J 3-connected with unique even vertex z, d(z) = d, B = J − z, |B| = 2k, U = N(z).

Lovász applied to J gives k paths with one end at each odd vertex and z internal on d/2 paths. Deleting z gives a decomposition of B into **k + d/2** paths in which every u ∈ U has exactly 2 ends and every odd vertex has 1. In halved form this is c = 1_U at level k + d/2.

### The descent property

(U\*) For connected G of even order n, every level k' ≥ n/2 + 1 with k' − 1 ≥ p(G), every c ∈ C_{k'}, and every **even** r with c(r) ≥ 1, there is u such that c − e_u ∈ C_{k'−1} and r is still exposed.

### Why it would matter

Given (U\*) and Gallai for B (induction), descending d/2 levels from 1_U keeps r exposed. That is the deletion test at r, **for every d at once**. (U\*) also implies the rooted test directly: split an optimal decomposition at r, then descend once.

So (U\*) is a strengthening of Gallai. It is worth having only if it is true and more local, and its local form, "un-merge one end-pair", is the kind of statement exchange arguments prove.

### Evidence

- Allowing odd roots (three ends at an odd r) makes it fail at n = 4, e.g. K4. That version is irrelevant: the rooted test never needs it.
- With even roots only, it holds for all 6 connected graphs at n = 4.
- n = 6 is running.

---

## D. Closing the dense regime below the Dirac threshold

**Grade: Observed; a route, not done.**

- separating-pairs Cors 14.24 and 14.26: failures with δ ≥ n/2 − o(n) are within o(n²) edits of K_{n/2,n/2}.
- Cor 14.36 and Thm 14.37: bipartite graphs, and two-coloured graphs with ≤ κn same-colour neighbours per vertex, satisfy the floor and the rooted bound.
- o(n²) edits leave only o(n) vertices with ≥ εn same-colour neighbours. The near-half-mixed-vertices note restores **s ∈ {1, 2}** such vertices by splitting their incidences and using a Hamilton decomposition in the near-half regime (Csaba–Kühn–Lo–Osthus–Treglown).

**Connection.** The note combined with Cor 14.24 and Thm 14.37 leaves one gap. Extending the note from s ≤ 2 to s = o(n) exceptional vertices, absorbed in batches as in the robust-decomposition method, would give:

> **Target D.** There is γ > 0 such that every sufficiently large connected G with δ(G) ≥ (1/2 − γ)n satisfies Gallai, the floor outside odd semi-cliques, and the rooted bound.

This would be an *exact* Gallai theorem below the Dirac threshold. Today the published result in that range is the asymptotic n/2 + o(n) of Girão–Granet–Kühn–Osthus.

It does **not** reach full Gallai. OSB Cor 44 shows that the linear-deletion dense regime is as hard as the whole problem, but only by using vertices of low degree, which Target D excludes.

---

## E. The core object: tight odd graphs

**Grade: Observed.**

Three manuscripts arrive at the same core object independently: odd order n = 2k+1 with p = k+1 ("tight"):

- marked-reduction Thm 1(2): three ends at odd vertices of tight 2-connected J;
- separating-pairs Thm 10.16, alternative 1: a tight 2-connected J outside the semi-cliques;
- odd-semi-clique-boundary Thms 46 and 48: the floor for graphs with a leaf;
- MR Thm 144: the floor for odd graphs with a leaf and five even vertices.

Combining them:

1. Bonamy–Perrett for **2-connected** graphs (tight 2-connected ⇒ odd semi-clique), together with the marked bound on 2-connected graphs, implies Gallai. Proof: MR Thm 1, with assertion (2) supplied by semi-clique Thm 4 / §1.
2. MR's interpolation lemma: any 2-connected Bonamy–Perrett counterexample yields a spanning 2-connected supergraph with p = k+1 exactly and ≥ k missing edges. So minimal witnesses are tight *and* have ≥ k holes.
3. OSB: the floor holds outside semi-cliques when ≤ 4n − 20007 edges are missing (large n). separating-pairs: the witness has no cut of ≤ 3 edges, ≤ 1 vertex of degree 2, and ≤ 1 cubic vertex.
4. **Open question that would unify these:** is every tight 2-connected odd graph dense (o(n²) missing edges, or even O(n))? If so, OSB plus separating-pairs §14 classify them. MR Cor 44 does not refute this, because its embedding uses a bridge and is therefore not 2-connected.

---

## F. Cycles through a vertex: m ↦ m+1 for all m

**Grade: Conjecture; random tests running.**

**Known:**
- ≤ 7 cycles (MR Thm 38);
- 8 cycles (Thm 175, with K17 sharp);
- 12 nearly spanning cycles (cycle-and-contact Thm 1);
- general m: m + ⌊√m⌋ − 1 (Cor 176), and m + ⌊√m⌋ (even-degrees Lemma 2).

**Uniform target.** If C_1, …, C_m are edge-disjoint cycles through x, then their union U has F_2(U, x) ≤ m + 1.

**Sufficient condition.** A rainbow path Q with one edge from each cycle, positioned so that x collects two ends. Opening each C_i at its Q-edge then gives m + 1 paths.

**Where it fails.** Greedy rainbow growth stalls once the path has about 2(m+1−k) > k − 2 sites. That is where the computer enters at m = 12, k = 10, 11. A Pósa-rotation argument for rainbow paths in unions of cycles is the missing uniform tool.

---

## G. Refuted on the way

- **Complementary pairs (CP).** Two decompositions in which each odd vertex ends once in each, and each even vertex ends twice in exactly one. This would imply the floor. It fails at n = 7 for K3 ∨ 4K1 and for K6 plus a degree-3 vertex. Cause: an even vertex of degree 2t cannot end a path in a t-path decomposition. See `experiments.md` E2.

---

## H. Reformulations from the deletion-test analysis (2026-11-26, later)

1. **The first descent step is free** (proved; manuscript `endpoint-structure`, Lemma 3). For every even u, the set E − u is realisable. Proof: apply Lovász to G + z with z joined to E − u; then u is the only even vertex.

   Deeper steps would need prescribed-end versions of Pyber or Fan on an apex extension. Applying Pyber to G + z with z joined to E − {u, v} only says that one of u, v, z takes two ends; it gives no control over which.

2. **Reducing d to d − 2 is circular.** Add an edge xy between two even vertices of N(z) − r and use the degree-(d−2) test. Removing xy afterwards stays within budget exactly when xy is the terminal edge of its path, which is the statement that some realisable S contains r and y but not x.

3. **The test as chain selection in the endpoint multigraph.**
   - Lovász on J gives a faithful D0 on B = J − z together with a perfect matching μ of U (the transitions at z). For every μ-pair the two half-paths are vertex-disjoint.
   - In the endpoint multigraph M (one edge per path, joining its ends), every u ∈ U has degree 2 and every odd vertex degree 1.
   - The rooted test asks for some faithful D0 and some W ⊆ U − r with |W| = d/2 such that suppressing W in M turns every chain of paths into a simple path, and no cycle of M is completely suppressed.
   - **Possible uniform dichotomy:** either many end-pairs are disjoint (a selection or counting argument), or the overlaps force density, where separating-pairs §14 applies. That paper's "obstruction in the multigraph of path endpoints" is the natural starting point.

## I. The deletion-test hierarchy as floor bounds BP_t

Let J be 3-connected with unique even vertex z, d = d(z), B = J − z, r ∈ N(z), and W = B with a private leaf at r. Then:

- W has odd order 2k+1.
- Its even vertices are exactly N(z) − r, so there are t = d − 1 of them.
- Test (i) at r holds iff p(W) ≤ k = ⌊|W|/2⌋, i.e. iff W satisfies the floor bound.

This is MR Thm 144's equivalence, written for general d.

**Definition.** BP_t: every connected odd-order graph with a leaf and exactly t even vertices satisfies p ≤ ⌊n/2⌋. The leaf excludes odd semi-cliques.

| t | Status |
|---|---|
| 1 | Lovász's theorem |
| 3 | follows from Botler–Sambinelli: any graph on 3 vertices is in their family 𝒢 |
| 5 | the open d = 6 frontier |
| ≥ 7 | open |

At t = 5, Botler–Sambinelli covers every E-subgraph outside the following: E-subgraphs containing a bowtie (two triangles sharing a vertex) or a block with a vertex of degree 4. On five vertices both force a universal vertex.

**So the remaining frontier is BP_t for dense E-subgraphs.** This is the regime of Chu–Fan–Zhou's clique theorem (E-subgraph K_r with r ≤ 15 gives ⌊n/2⌋ + 1, not the floor) and of six-clique Thm 6.

A uniform target suggested by this view: **the floor bound for odd-order graphs with a leaf whose E-subgraph is a clique, for every clique order.**

## J. Why the full-vertex case at d = 6 resists Fan transfers (working note)

**Setting.** B[U] = K6. Some exterior x sees all of U. Let H = B − rx.

- The even set of H is (U − r) ∪ {x}, again a K6 core, now with root x.
- By induction on edges, H has an optimal decomposition doubling x and two vertices of U − r.
- Its three unexposed even vertices all lie in U − r, so all are neighbours of r.

**Restoring rx fails.** Restoring rx towards r by Fan's lemma needs b(x) = 2 > #(zero-end neighbours of r) = 3, which fails.

**Grouped transfers don't fix it.** They add *some* edge rt, not necessarily rx.

**What is known.** The false-twin-return note handles the case where r lies in a large false-twin class of H.

**What a general argument needs.** A second apex, i.e. using x itself as a parity absorber, or a transfer that moves two ends at once.

## K. Marked descent (faithful descent in the marked setting)

The marked bound is now formalized: `gallai_iff_markedBound`, where Gallai ⇔ q(F,S) ≤ ⌊(n − |S|)/2⌋ for all connected F and nonempty S.

**How the bound behaves when a site is removed.** Removing a site v from S changes the two sides as follows:

- q(F, S − v) ≤ q(F, S) + 1, since the path assigned to v becomes unassigned;
- the budget ⌊(n − |S| + 1)/2⌋ exceeds ⌊(n − |S|)/2⌋ by exactly [n − |S| odd].

So the bound transfers for free when n − |S| is odd. When n − |S| is even, the transfer needs an optimal marked partition for S that does not use v.

**Marked descent.** For S = V(F) the bound is easy: q(F, V) = 0 for decompositions into few enough paths. Gallai follows from a descent S = V(F) → … → {r} in which every even step keeps q unchanged. This is the cone (W(F,S)) form of faithful descent (section C). Under the formalized identities the two are the same problem, which gives a Lean-ready statement of the descent step.

## L. Cor 106, the one-exception odd-order case, without Shaik (attempts)

**Goal.** L has odd order 2k+1, a leaf at an odd support s, and exactly one vertex x of E-degree ≥ 4. Show p(L) ≤ k.

1. **Doubling with a bridge** (the manuscript's approach). Join two copies of L − ℓ by the bridge ss′. The double has 4k vertices, and cutting the bridge gives 2p(L) ≤ p(D) + 1, so p(D) ≤ 2k suffices. But the E-subgraph of the double has two exceptions, x and x′, in different components, and that case needs Shaik.
2. **Adding the edge xx′ as well.** Now x and x′ are odd, so the E-subgraph has Δ ≤ 3, and Botler–Sambinelli Thm 13 gives p(D) ≤ 2k. But cutting two cross edges only yields p(L) ≤ k + 1, so the count is one short.
3. **Joining x to x′ through a new vertex y** (path x–y–x′, so |D| = 4k+1). Botler–Sambinelli gives p(D) ≤ 2k. If y is an end of two paths, deleting y costs nothing and p(L) ≤ k follows. If y is interior, the count is again one short. So this route needs the floor with y prescribed as an end, which is a Shaik-type statement again.
4. **A longer joining path** x–y–y′–x′ (even order). Fan–Hou–Zhou Thm 5 exposes y at the ceiling 2k + 1, which is again one short after cutting.

**Conclusion.** Every gadget costs exactly one unit of budget. The missing ingredient is the floor with one prescribed even vertex when Δ(EV) ≤ 3, i.e. Botler–Sambinelli Thm 13 with a prescribed end. That is a natural lemma to aim for.

## M. A 2-sum picture for the endpoint matroid (conjecture, being tested)

**Observation.** Every non-uniform endpoint matroid found so far (at n = 6 with a cut vertex; at n = 8 with κ = 2) has its non-bases exactly equal to the sides of a 2-separation. Example: GsaFC{ is a sparse paving matroid whose two circuit-hyperplanes are the two sides of the separations at the universal vertex.

**Conjecture (two parts).**

- (a) **3-connected critical graphs have uniform endpoint matroids**: every half-set of the even vertices is realisable.
- (b) **At a 2-separation the endpoint matroid is a matroid 2-sum** (or parallel connection) of the endpoint matroids of the two sides, computed with suitable virtual edges.

**Consequence.** (a) + (b) ⇒ EMC ⇒ Gallai, with the reduction running through 3-connected pieces. This is compatible with MR Thm 114, which already reduces Gallai to 3-connected J.

**The gluing tool.** two-vertex-separators Thm 1 (an exact gluing formula with five endpoint types and the disjointness matching number ρ) and Thm 7 (all attainable endpoint vectors) are exactly what (b) needs.

**Test.** (a) at n = 8 on all 2,388 three-connected graphs (critical ones only): running.

## O. The second descent step is a "Lovász theorem for two even vertices"

**Sufficient condition (proved).** Let G have even order, E its even vertices, and u ≠ v ∈ E. Let z be a new vertex joined to E − {u, v}, and ℓ a new leaf at z.

  If G + z + ℓ has a decomposition into |odd|/2 paths, then E − {u, v} is realisable in G.

The graph G + z + ℓ has exactly two even vertices, u and v. A decomposition into |odd|/2 paths, i.e. one meeting the parity bound, has every odd vertex as an end exactly once and u, v internal.

**Proof.**

- Delete ℓ. If its path is the single edge ℓz, this removes z's only end. Otherwise z gains a second end.
- Delete z. Each neighbour of z then has 0 or 2 ends; split at those with 0.
- The vertices u and v are not adjacent to z, so they keep 0 ends. The odd vertices keep 1.

**The converse is not claimed.** Pairing path ends through z needs the two paths to be vertex-disjoint.

So Lovász's theorem, covering at most one even vertex, gives the first descent step (Lemma 3), and the second step is exactly:

> **Two-even-vertex Lovász problem.** Characterize the connected graphs with exactly two even vertices u, v that admit a decomposition into |odd|/2 paths.

**Known.**

- At most one even vertex: always (Lovász).
- Two even vertices: not always. K4 − e fails, with u, v the two degree-2 vertices: one path cannot contain both a–u–b and a–v–b.

**Why it matters.** A characterization, even a sufficient local condition such as "u and v are not degree-2 twins", would give the second faithful-descent step for most pairs.

**Natural tools.** Fan's grouped transfer (now formalized), applied to the Lovász decomposition of G + z_u.

## Q. Two-step descent: hand verification and the k-step template

**Result.** The cloud session `claude/emc-four-even` proved `two_step_descent` in Lean: for G connected of even order with e ≥ 4, and all distinct even y, w, there is an even v ∉ {y, w} with Ev ∖ {w, v} realisable. **Every step was checked by hand (coordinator):**

1. **Transfer across an even edge.** s, t, u′ are even, st ∈ E, su′ ∉ E. In K = G − st both s and t are odd. Lemma 3 gives Ev(K) ∖ {u′} realisable, i.e. Ev ∖ {s, t, u′} doubled with s and t at one end each. The only zero-end vertex is u′, which is not a neighbour of s. Fan's single lemma adds st towards s. Result: Ev ∖ {t, u′}.
2. **Star.** y is adjacent to even w, x, z. In K = G − {yw, yx, yz} the vertices y, w, x, z are odd; take the faithful decomposition (Lemma 2).
   - Add yw towards y: there are no zero-end neighbours.
   - Add one of yx, yz towards y by the grouped lemma: 1 + 1 > 1, the 1 being w.
   - Add the last edge towards its far end: b(y) = 3 > 2 ≥ |N(z) ∩ {w, x}|.
   - Result: Ev ∖ {w, x} or Ev ∖ {w, z}.
3. **Lift.** y is even, t an odd neighbour, K = G − yt. If S ∋ t is realisable in K and y has no neighbour among the zero-end even vertices of K, a single transfer of yt towards y realises S − t + y.
4. **Induction along a y–w path.**
   - Base: y has an even neighbour (cases by whether w is a neighbour, using 1 or 2).
   - Otherwise the next vertex t is odd. Apply induction to t in G − yt and lift back with 3. The lift hypothesis holds because y has no even neighbours.
   - Degrees stay positive, since the path has length ≥ 2.

**k-step template.** Each lemma generalizes, with the removed set W in place of {u′}, {w, v}, …:

- Transfer: if Ev(K) ∖ ({s, t} ∪ W′) is realisable in K = G − st and s has no neighbour in W′, then Ev ∖ ({t} ∪ W′) is realisable.
- Lift: as stated, with W the zero-end set.
- Star and base cases: need extension with more edges at y.

So a three-step descent ("for all distinct even y, w with e ≥ 6 there are v1, v2 with Ev ∖ {w, v1, v2} realisable") would follow by the same induction along a path, provided the base case (y has an even neighbour) can be handled with two removed vertices. **That base case is now the exact target** of the redirected two-even cloud session. It would give T(6)-i.

**A caveat for a general k-step version:** the prescribed vertex w might be a coloop of the endpoint matroid at the bottom level. The rooted test needs only reachability, so the right statement prescribes w only in the first step.
## N. EMC for four even vertices (cloud session)

**Grade: Proved (manuscript `endpoint-structure`, section "Two descent steps, and four even vertices"); Lean-verified (`lean/GallaiLean/EMCFour.lean`, Lovász as the hypothesis `LovaszStatement`, Fan's transfers proved).**

### Results

Numbering: "Lemma 2" (faithful partition, Ev realisable) and "Lemma 3" (Ev − u realisable) are as in §H; in the compiled PDF they are Lemmas 3 and 4. Lemma 15–Cor 22 are the PDF numbers.

1. **Two descent steps (Thm 19).** If G is connected of even order with e ≥ 4 even vertices, then for all distinct even y, w there is an even v ∉ {y, w} with Ev − {w, v} realisable. Lemma 3 was the first step of faithful descent for every deleted vertex. This is the second step, for every kept vertex y and every first deleted vertex w. **So FD (§C, Conjecture 12) holds for all S with |S| ≥ e − 1.** Criticality is not used. Connectivity is needed: P3 ⊔ (K5 − e) has no realisable pair at the centre of P3.
2. **Four even vertices (Cor 20).** For connected even-order G with e = 4: for distinct even y, x, z, {y,x} or {y,z} is realisable. Equivalently, every even vertex lies in ≥ 2 realisable pairs, and the non-realisable pairs are pairwise disjoint.
3. **EMC for e = 4 (Thm 21).** If H is connected and critical with e = 4, then the minimal realisable sets are exactly the realisable pairs. They are the bases of a loopless rank-2 matroid whose non-trivial parallel classes are the (at most two, disjoint) non-realisable pairs. Lean: `endpoint_matroid_four` builds a Mathlib `Matroid` and proves it `Loopless`. Two triangles joined by an edge (n = 6) show that both parallel classes can occur.
   - The task's "triangle form" (non-realisability is transitive) is weaker. Since every 3-set is realisable (Lemma 3), EMC at e = 4 also needs every 3-set to contain a basis. So EMC(e=4) is equivalent to the disjointness form, and that is what is proved.
4. **Rooted test / BP_3 without Botler–Sambinelli (Cor 22).** Lean: `rooted_four` and `rooted_le_four` (at most four even vertices). This makes Prop "small even sets" (e = 4) and the floor bound BP_3 depend only on Lovász + Fan. Both deletion tests at d = 4 are BP_3 instances, via the audited floor form (MR Thm 114), so T(4) no longer needs Fan–Hou–Zhou or BS.

### The proof (all from Lovász + Fan's single/grouped transfers)

- **Transfer across an even edge (Lemma 16).** Let s ~ t and s ≁ u' (all even). Lemma 3 on G − st gives Ev − {s, t, u'}. Its only unexposed vertex is u', which is not a neighbour of s. A single Fan transfer of st towards s then gives Ev − {t, u'}. This holds for any e at even order.
- **Star lemma (Lemma 17).** Let y ~ w, x, z (all even). Lemma 2 on G − yw − yx − yz has no unexposed vertex. Transfer yw towards y. Then do a grouped transfer of {yx, yz} towards y: only w is passing, so 1 < 2. Finally transfer the last edge y t'' towards t'': only w and t' are passing, so 2 < 3 = b(y). The result is Ev − {w, t'}.
- **Lifting (Lemma 18).** For an odd neighbour t of y, a realisation of S ∋ t in G − yt lifts to S − t + y, provided the unexposed even vertices avoid N(y).
- **Induction on a path** from y to another even vertex.
  - If y has an even neighbour: Lemma 16 when y ~ w and y misses some even vertex, or when y ≁ w; Lemma 17 when y sees all of them.
  - If y has no even neighbour: its path-successor t is odd. In G − yt, t plays y and the path is shorter. Lift back with Lemma 18; the passing set {w, v} avoids N(y) because y has no even neighbours.

### What this says about the uniform mechanism (§B, §C, §H)

- §H.1 said: "Deeper steps would need prescribed-end versions of Pyber or Fan on an apex extension." The second step needs neither. Fan transfers on G minus one or three edges at y, with Lemmas 2/3 as seeds, are enough. The passing-neighbour counts are controlled exactly by the profile identity Z_D(u) = N(u) ∩ (Ev(K) − S).
- **Third step (e = 6, i.e. the open T(6)-i / BP_5).** Theorem 19 gives a realisable 4-set containing r and avoiding any prescribed w. (R) needs a 3-set.
  - Iterating Lemma 16 with Theorem 19 in place of Lemma 3: delete yt (t even), get Ev(K) − {w', v'} in K = G − yt, then transfer yt towards y.
  - This works whenever K is connected and **w', v' ∉ N(y)**. Here w' is prescribed but v' is not.
  - **Next target:** a version of Theorem 19 in which the second deleted vertex v avoids a prescribed set (e.g. N(y)). For e = 6 that would close the simple-profile third step whenever y has two even non-neighbours. The cases where y has ≥ 4 even neighbours would go to a star-type lemma.
- The star lemma uses the grouped transfer in the regime "one passing neighbour, two donors". A four-donor version (|T| = 4, ≤ 2 passing) is the natural candidate for the e = 6 star case.

### Sanity checks

`tools/emc_four.py` checks all connected graphs with e = 4 at n = 4, 6, 8, critical or not. Results:

- n = 6: 44 graphs, 0 failures of the strong form. The critical graphs with non-realisable pairs are Esq_, Esqo and EqhO, each with exactly two disjoint pairs.
- n = 8: see `research/experiments.md` E13.

### k-step infrastructure (follow-up, same session)

Manuscript `endpoint-structure`, subsection "k-step descent" (Lemma 24, Thms 25–26, Cor 27). Lean: `lean/GallaiLean/KStep.lean` (no sorry; primed forms use `lovaszStatement`).

- **Definition.** k-step descent at (y, W₀): some k-set R ⊆ Ev − y with W₀ ⊆ R has Ev − R realisable. Lemma 3 is k = 1, Thm 19 is k = 2.
- **General transfer (Lemma 24, `realisable_transfer`).** For adjacent even s, t and K = G − st: if S ∈ F(K) and N(s) ∩ (Ev(K) − S) = ∅, then S ∪ {s} ∈ F(G).
- **Connected reduction (Thm 25, `desc_reduction`).** k-step descent in connected graphs reduces to two base cases:
  - y has an even neighbour, or
  - every edge at y is a bridge.

  The proof is an induction on |E|: delete a non-bridge edge yt to an odd neighbour and lift (Lemma 18). It uses no parity and no criticality.
  - **Why connectivity, not path form:** for k = 3 the path-form base statement fails for disconnected graphs. (K5 − e) ⊔ (K5 − e) has e = 6, every even vertex has an even neighbour, and every realisable set has ≥ 4 elements.
  - **Not reduced:** the all-bridges case. It splits G into parts that may have odd order, where descent is the floor problem.
- **One even neighbour (Thm 26, `desc_succ_of_unique`).** If y has exactly one even neighbour t, then (k+1)-step descent at y follows from k-step descent in G − yt, at a vertex joined to another even vertex. Choose one by pigeonhole over the ≤ 2 sides of yt.
- **Three steps (Cor 27, `desc_three_of_unique`).** Theorem 19's path induction supplies k = 2, so three-step descent holds at every even vertex with exactly one even neighbour (connected, even order, e ≥ 6).
  - **For e = 6 this is (R) at y.** In deletion-test terms: **test (i) at d = 6 holds at every r ∈ N(z) with exactly one neighbour in N(z).**
- **Three-step reduction (`desc_three_reduction`).** Three-step descent for connected even-order graphs with e ≥ 6 now reduces to:
  - (i) y has ≥ 2 even neighbours;
  - (ii) y has no even neighbour and every edge at y is a bridge.

  Case (i) is where the obstruction of Remark 23 lives: the second deleted vertex must avoid N(y).
- The n = 8 e=4 exhaustive run was stopped at the coordinator's request after ≥ 500 of 5,523 graphs, with no exception.

## R. Lovász–Fan certificates are a game on profiles, and the game is incomplete (2026-11-26, night)

**Grade: Observed (computation, small); conceptual consequence.**

Fan's single and grouped transfers have hypotheses that depend only on the end profile b and on the current graph. So every argument of the form "Lovász seed, then re-insert edges by Fan transfers" is a play in a finite game on (graph, profile). The following are all such plays:
- Lovász from Fan (manuscripts/lovasz-fan), with one induction;
- Lemma 3;
- the two descent steps;
- the star lemma;
- Fan schedules and FanCert;
- Pyber's theorem (Lean, Pyber.lean);
- the six-clique insertion schedules;
- every d6-frontier certificate.

A winning play is a short certificate that can be checked without exhibiting paths (E13).

- At n = 6 the game wins every root of every connected graph. The restricted calculus FanCert does not.
- At n = 8 it does not. The obstruction is a clique of even vertices with full exterior vertices, two of them false twins (GsRvnk, E13). d6-frontier Thm 3.1 is the local form of the same phenomenon: if every held edge lies in U ∪ {full vertices}, the last Fan step cannot produce the standard profile.
- Inductive seeds that use only (R) do not repair this. The adversary keeps the freedom to place zeros next to the re-inserted edges.

> **Correction (§S, cloud session missing-move).** The incompleteness at n = 8 is an artefact of the game allowing only one-edge new paths. With *path insertion* (a new path of any length made of held edges) the game wins every root of every connected graph of order 8 with |F| ≤ 6. Pósa moves at the profile level repair none of the losers. The paragraph below stands as originally written. Read "Lovász + Fan transfers alone" as "with one-edge new paths only".

**Consequence for the programme.** Full Gallai cannot come from Lovász + Fan transfers alone, even with (R) as the induction hypothesis. One of two ingredients is needed:
- **(M) a move beyond Fan's inequality.** Fan's lemma is iterated Pósa rotation. When the inequality is tight, a rotation still moves the missing edge from uv to uw and moves an end from v to w. A two-end transfer at equality, as the d6-frontier agent suggests, is of this kind.
- **(H) a stronger induction hypothesis** that controls the zero set of the seed. Candidates are EMC (matroid exchange) and FD with several prescribed vertices.

The n = 8 losers are the natural test bed: the right move or hypothesis must make every one of them winnable. Cloud session "missing-move" (ROADMAP).

## S. The missing move is Lovász's spare path, not a move beyond Fan's inequality (2026-11-26, cloud session missing-move)

**Grade: Proved (hub lemma, degree-four hubs; Lean `MissingMove.lean`); computation (completeness at n = 8; Pósa moves negative; n = 10 test bed).** Manuscript `manuscripts/missing-move`.

**The spare path.**
- Isolate a vertex s in K = G − F. If K has at most one even vertex of positive degree, Lovász gives |Od(K)|/2 ≤ n/2 − 1 paths. One path of the budget is spare.
- Fan transfers keep the path count, so the spare path can only be spent by a new path.
- The game of §R allowed new paths of length one only.

**Hub lemma** (`Ach.hub_four`). Let s be isolated in K, with b ≥ 1 at a, c, d, and let x be a fourth vertex. Re-insert sa, sc, sd, sx as follows:
- a single transfer sa towards s;
- a grouped transfer {sc, sd} towards s, with supply 2 > 1 blank;
- the new path y′ s x.

The cost is exactly one path. The profile changes by +2 at s, −1 at a and at the adversary's y ∈ {c, d}, and +1 at the other y′ and at x. The lemma accepts any seed.

**Degree-four hubs** (`hub_four_ends`, `hub_four_rooted`; unconditional, via `lovasz_ends`). Hypotheses: d(s) = 4, every neighbour of s is even, and at most one even vertex lies outside N[s]. Then G has a partition into ≤ n/2 paths with b(s) = 2 and b(x) = 2, for any prescribed neighbour x. So (R) holds at s and at N(s). This closes GsRvnk (roots s, s′). The hypotheses force e ≤ 6, the BP_5 regime.

**Completeness at n = 8** (E14). With path insertion the game wins every root of every connected graph of order 8:
- |F| ≤ 4 suffices for all but 47 graphs;
- the 47 win with |F| ∈ {5, 6}.

All the certificates found for the five §R losers are hub-shaped: an isolated hub, receipts, then one new path through the hub, sometimes extended along a further held edge. A hub of degree d with b ≥ 1 on its neighbours absorbs ⌈d/2⌉ adversarial receipts. So the spare path closes it iff d ≤ 5.

**Pósa moves fail at the profile level.** Two candidate moves were proved and tested.
- *Rotation* (Lemma 4.1 in the manuscript): either uv appends, or the opponent picks W ⊆ N(u) of size b(v), we pick w ∈ W, and the held edge becomes uw.
- *Fan's alternative* (Lemma 4.2, new): either some t ∈ T transfers, or at least Σ_T b blank neighbours z of u can each be *activated* (end t → z, held edge tu → zu). This is the "rigidity at equality" of d6-frontier §8, made into a statement. As game moves it dominates rotation.

Neither repairs any losing root: rotation with ≤ 2 uses and |F| ≤ 4; the alternative with ≤ 2 uses and |F| ≤ 4, or 1 use and |F| ≤ 6.

Why: the losers need the spare path to be spent on a 2-edge path c–s–d through the hub. Imitating it with a one-edge path cs plus a transfer of sd needs to know that one of the three paths ending at s is cs, which avoids d. The profile forgets this. *Path insertion is the memory of one explicit path.* The obstruction at n = 8 is budget allocation, not exchange.

**Degree six: one receipt short** (manuscript §5). A degree-6 hub absorbs 3 adversarial receipts. Closing it with one spare path needs 4, and the 4th is exactly at Fan's equality (supply 3, three blanks).

On A_{6,2} (K6 core of degree-8 vertices, a full vertex x with a leaf ℓ, two false twins on the core; n = 10) the 4th receipt is forced by **append-or-through plus an edge count**:
- if every path ending at T = the remaining core neighbours passed through s, then, since b(s) = d_H(s), the three s-paths would join T to s;
- the fourth path would then be ℓx;
- so 30 edges would have to fit in three paths of ≤ 8 edges, which is impossible.

This is the d6 frontier's "short by one" (Remark 3.5), and the "two-end transfer at equality" made concrete. The rigid configuration must be refuted by information *outside* the profile (path lengths).

On K8 minus a perfect matching (n = 8, 6-regular) the 4th receipt *always* fails: all three Lovász paths of G − s end at the hub. The count then makes the three paths plus the held edges three Hamiltonian cycles through s, a **flower**. Cutting one edge from each so that the three cut edges form a path s–a–w–z spends the spare path and gives (R) (manuscript Lemma 5.4, Prop 5.5). This is a genuine two-end move at equality: the ends move from T to the transversal path. It too is invisible in the profile.

The extended game (path insertion, F = full star plus ≤ 2 edges) loses A_{6,2} at every root, odd roots included. It also loses the Q2-type graph B′ (K6 core, a full vertex with a leaf, two adjacent full vertices) at every root with a star plus ≤ 1 edge; see E14 for k = 2.

**Consequences.**
- §R's "Lovász + Fan is incomplete" is corrected: at n = 8 the missing move was path insertion, which is already in the Lean insertion library (`Ach.addPath`).
- Inductive seeds have Σb = n and so no spare path. The spare path is the floor ⌊N/2⌋ at odd order. An induction that keeps it needs the floor bounds BP_t, and the hub lemma converts them into (R) at degree-four vertices.
- The first genuine gap is at n = 10, at degree-six hubs. The next ingredient is a non-profile count at Fan's equality: Question 5.6 of the manuscript.

