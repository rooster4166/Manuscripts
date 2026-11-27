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

### D.1 Status after the near-dirac session (2026-11-27)

Manuscript: `manuscripts/near-dirac`.

- **Proved: balanced return theorem (Thm 1.1).** Exceptional sets of linear size with arbitrary two-sided neighbourhoods and moderate degree are returned exactly, at both parities. The condition is the *balance condition*: the internal edges at exceptional vertices on each side are matched by the internal edges of the other side, up to cm and the correction ρm/2. This contains SP 14.27.
- **Corollary 1.2.** The floor and the rooted bound hold for near-regular graphs near K_{n/2,n/2} whose degree excess balances across a bisection.
- **Corollary 1.3.** Every failure sequence violates the balance condition on every admissible (partition, X).
- **Counting identity (Lemma 4.1).** In any two-apex Hamilton finish, b'(B) − b'(A) = 2(e_R(A) − e_R(B)) + ρD. Its bipartite case is SP's §14.18 obstruction. Together with |l(A) − l(B)| ≤ 2q, it forces a balance condition of this type, up to an error of order q. It does so only for finishes whose preliminary paths avoid the internal edges at X. This is why imbalanced configurations, and unequal shores near K_{m,m+d}, appear to need SP's one-apex removal scheme.

Open:

- (P7.1) Two-sided removal: SP 14.33 with labelled pairs on both shores. Its counting half is **proved** (§8) for the "keep X in J" route, under (B1): every exceptional vertex has at most D healthy neighbours in each shore, which excludes intermediate vertices (Remark 8.4).
  - Lemmas 8.1 and 8.2: mirror-symmetry balancing.
  - Prop 8.3: an exact two-sided sweep, due to audit A19. It meets the window for every |X|, under (B1) and the degree window.
  - Open: the scheduling half, stated as the Scheduling Hypothesis SH (§9).
  - Thm 9.3 (proved, conditional on SH): near-regular failures must contain an intermediate vertex (Problem 9.4).
- (P7.2) High-degree exceptional vertices, of degree at least (1/2 + β)n.

Two observations from this session (heuristic, not proved in the manuscript):

- Bounded |X| is *not* easier than |X| = o(n). Each exceptional vertex individually needs about n/4 integrated visits, and the healthy shores can be unbalanced regardless of |X|.
- An "X-in-J with one-sided labels" scheme appears unable to balance more than about two two-sided vertices.

This session's own referee subagent, run before audit A17, found no error in the proof of Thm 1.1. It found one gap, now fixed: Cor 1.3 needed |X| ≤ cm. It also raised two attribution points, now credited in the manuscript: SP 14.30 already threads exceptional vertices through rows as u, x, v, and SP §14.18 contains the bipartite case of the counting identity. Audit A17 (`research/audit/A17-near-dirac.md`) confirms Thm 1.1; its wording items are addressed in 7228bdb and later commits.

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

**Outcome (2026-11-26, cloud session `claude/bs-prescribed`; manuscript `manuscripts/bs-prescribed`).**
- **The prescribed-end lemma is false.**
  - Lemma (forcing): a cycle whose vertices other than one have degree 2 contains an end of every partition.
  - Family G_{t,t'}: y has degree 2 between two odd vertices s, s′, and s, s′ carry t, t′ pendant triangles. For every odd N ≥ 5, y cannot be an end of a floor partition. This is precisely the x–y–x′ gadget's configuration.
  - Exact census at n = 7, Δ(EV) ≤ 3: 6 failures with e = 5, 101 with e = 3, and all 130 with e = 1 (E14).
- **The gadget cannot be rescued by restricting the class.** Take the order-9 graph L in which x carries two pendant triangles. Its even subgraph is a bowtie, it has a leaf at an odd support, and p(L) = 4. Its 17-vertex double D still has no 8-path partition with an end at y: four forced triangle ends plus y.
- **What Cor 106 needs is BP_5 with one universal vertex**: every MR use has ≤ 5 unmarked even vertices. This is now **proved from Lovász + Fan**.
  - Six cores need no leaf. Three local lemmas cover them: two disjoint even edges, the odd star, and the universal star.
  - The bowtie needs adjacent odd u, v with N(u)∩T ≠ ∅ = N(v)∩T. A leaf at an odd support plus connectivity supplies them through a shortest path.
  - The bowtie is closed by 11 orbit certificates. All 131 labelled certificates are in Lean (`FiveEvenCerts.lean`).
- **Lesson for the uniform programme (§R).**
  - At odd order with a prescribed end, Lovász–Fan certificates are far from complete even for subcubic E-subgraphs: 58 of the 64 game losses with e = 5 at n = 7 are search failures.
  - The useful prescriptions are those that are not forced against. Theorem 1 prescribes nothing at all: it realises a 2-set in W directly.

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

### Bridges and the branching reduction (follow-up 2)

Manuscript: Lemma 28 (bridge gluing), Theorem 29 (reduction to the branching case), Cor 30.

- **Bridge gluing.** Let yt be a bridge with sides A ∋ y and B ∋ t, and set A⁺ = G[A ∪ {t}], B⁺ = G[B ∪ {y}].
  - (1) F(A⁺) × F(B⁺) → F(G) by union. Concatenate the two paths through yt: P_A·yt·P_B.
  - (2) If y is even, realisations of G[A] and G[B] glue by extending a path of G[B] that ends at t with the edge ty. This removes t if t is even in G, and needs t kept in G[B] if t is odd in G.
- **Theorem (B_3 ∧ … ∧ B_k ⇒ D_k).** D_j means j-step descent at (y, {w}) in every connected even-order graph with e ≥ 2j. B_j is D_j restricted to y having ≥ 2 even neighbours. The proof is an induction on k, then on |E|:
  - Case 1: y has ≥ 2 even neighbours (B_{k+1}).
  - Case 2: y has a non-pendant bridge (gluing).
    - If |A| is odd, use A⁺ and B⁺.
    - If |A| is even, use G[A] and G[B].
    - The capacities always add up to e/2, or to e/2 − 1 plus the forced removal of t.
  - Case 3: y has exactly one even neighbour and yt is not a bridge. Transfer from D_k in G − yt.
  - Case 4: y has no even neighbour, and some edge yt is neither pendant nor a bridge. Thm 25 step.
- **Corollary.** B_k for all k ≥ 3 implies Gallai, through (R) at e = 2k. B_3 implies (R) for e = 6, i.e. T(6)-i. **The only open input is therefore "y has ≥ 2 even neighbours" at each level.** The all-bridges case of `desc_three_reduction` is closed by Case 2.
- Lean: done (`Bridge.lean`, `BranchBase.lean`). Pieces are subgraphs on the same vertex set, transported through the induced graph on their non-isolated vertices.
### The single named hypothesis (follow-up 3)

`lean/GallaiLean/BranchBase.lean` contains **`gallai_of_branchBase : (∀ k, BranchBase k) → GallaiConjecture`** and **`rootedTest_of_branchBase : (∀ k, BranchBase k) → RootedTest`**. No sorry, standard axioms.

**BranchBase k** is the weakest base statement the reduction supports. It is required only in connected even-order graphs with e ≥ 2k, and only at even vertices y such that:
- y has ≥ 2 even neighbours, and
- y has **no bridge to a vertex of degree ≥ 2**, because bridges are handled before the branching case.

The conclusion is **Desc H k y ∅**: y lies in a realisable (e − k)-set, with no prescribed removed vertex. `branchBase_one` and `branchBase_two` are theorems, so `gallai_of_branchBase_three` needs only k ≥ 3. `branchBase_of_bstmt` shows that BranchBase is weaker than BStmt.

Coordinator's finding (base branch, E13 / §R): Lovász seeds + Fan transfers do not prove three-step descent in general. Gqz~vw at y = 3 has no certificate with ≤ 8 held edges. So BranchBase k for k ≥ 3 needs a new ingredient.

**Update (path insertion).** The missing-move session found that the n = 8 losers need no move beyond Fan's inequality. They need *path insertion*: a Lovász seed on G − F with an isolated vertex leaves one spare path, and it pays for re-inserting two held edges as one new path through the hub. With path insertion the game wins the five non-critical n = 8 losers and the critical Gqz~vw (independently re-checked). **But an independent re-check of all 50 kmax-4 losers with `6 np` leaves 6 losers, all critical.** They are Guv]}{ (K7 + leaf), Guv]z{, Guv]~{, Gut~~w, Gu^v~w, and the cocktail party graph K_{2,2,2,2} = Gr~v~w (every vertex a degree-6 hub). So the degree-six obstruction already appears at order 8. The original §R list was incomplete: the kmax-8 run was OOM-killed before reaching these graphs. The degree-six obstruction is also visible at order 10 (`manuscripts/missing-move`). There the spare path pays for one receipt too few, and the deficit sits at Fan's equality.

### Route (H): stronger induction hypotheses (follow-up 4)

**Grade: Proved (Lean `FanBarrier.lean`, no hypotheses, standard axioms); computation (exhaustive, n ≤ 8).** Manuscript: endpoint-structure §7 (Def 50 – Remark 59).

The question (coordinator, route (H)): is there an induction hypothesis stronger than D⁰ / Desc, in the spirit of EMC, under which the transfer and lift steps can steer the seed's zeros away from the re-inserted edge?

**Answer: partly yes, mostly no.**

- **Prescribed transfer** (Lemma 51). Let ya be an even edge, and suppose G − ya has descent keeping (P − y) ∪ (N_E(y) − a). Then G has descent keeping P + y, one level up.
  - Conversely, every set produced by transferring ya towards y contains {y} ∪ N_E(y) − a and avoids a.
  - So the hypothesis must prescribe m − 1 vertices, where m = |N_E(y)|.
- **Two even neighbours reduce** (Cor 52, Lean `desc_succ_of_transfer_two`, `branchBase_of_three`, `gallai_of_branchBase3`). With m = 2, D⁰_k at the root b in G − ya suffices.
  - **Gallai ⇐ ∀ k ≥ 3, BranchBase3 k**, where y has ≥ 3 even neighbours.
  - Check: 13,360 instances with m = 2 at n = 8, and 92 at n = 6, all pass.
- **Gqz~vw at root 3** (Example 53). Yes, a hypothesis on G − e works there.
  - K = G − 31 has four even vertices {0, 4, 5, 7} with all six pairs realisable.
  - The pair {5, 7} = N_E(3) − 1 transfers to {3, 5, 7}. The edges 35 and 37 work the same way.
  - The hypothesis needed is that a *specific pair* lies in the endpoint matroid of G − ya. EMC-4 (Thm 21) allows that pair to be a non-realisable pair.
  - The oracle game also finds F = {01} with seed S_K = {3} in the non-critical G − 01, plus a new path 01.
- **Propagation** (Remark 55). D^{(j)} means descent keeping any |P| ≤ j.
  - It passes through bridges (except t ∈ P, t even, |A| even), through the unique-even-neighbour step (if t ∉ P) and through the lift.
  - The branching transfer needs D^{(j+m−2)}. So no bounded j is closed.
  - D^{(2)} is false at the critical level (e = 4 graphs with non-realisable pairs).
  - The matroid-qualified version needs N_E(y) − a to be independent in M(G − ya) for some a. That fails whenever m > e/2, and in 22 of the 275 critical instances with n = 8, e = 6, m = 3 (e.g. GsaEDo, y = 7).
  - Base case left: m ≥ 3.
- **Oracle-seeded Fan game** (Def 54, Remark 56; `tools/fan_oracle.py`, exact oracle `tools/realis.c`). The seed is any realisable profile of G − F, which is the strongest information any hypothesis on G − F can supply. Even roots of all connected graphs, n ≤ 8:
  - Simple seeds:
    - |F| = 1: K_{2,2,2} loses at n = 6; 6 graphs lose at n = 8.
    - |F| ≤ 2 and |F| ≤ 3: 3 graphs lose at n = 8. They are M8 = K8 − PM (all roots), Gqzn^[ (root 1) and Gut~~w (roots 1, 3, 4).
  - General profiles, |F| = 1: **everything wins except M8**. Compare 50 losers with Lovász seeds and |F| ≤ 4.
- **Last-edge barrier** (Thm 57, Cor 58; Lean `fan_transfer_barrier`, `insertion_barrier_regular`, `cocktail_fan_barrier`, `cocktail_insertion_barrier`).
  - If Fan's condition b(t) > |Z(u)| holds for a partition D of H = G − ut, then b(u) + 2|N^ev_H(u)| + 2 ≤ 3|D|.
  - For CP(m) = K_{2m} − PM with m ≥ 4, the last move of any Fan certificate is not a transfer and not a short path. It must be a new path of ≥ m − 1 held edges added to an (m − 1)-path partition of CP(m) − F.
  - For m = 4 that is exactly the flower of missing-move Prop 5.5 (|L| = 3 = m − 1, bound attained).
  - M8 has a uniform endpoint matroid U_{4,8}. **So the obstruction is in the moves, not the hypothesis. Route (H) alone cannot close BranchBase; (M) (spare paths at Fan's equality) is necessary.**
- **EMC at n = 8** (E15). All 1,082 connected critical graphs satisfy EMC, and 1,030 are uniform.
  - Every 3-connected one is uniform (476). This answers E7's question at n = 8.
  - The 52 non-uniform ones have κ = 1 (46) or κ = 2 (6: GsaFC{, GsaFeW, GsbFEo, GsbFeW, GsbfMo, GsPI^{).

### The flower move (follow-up 5)

**Grade: Proved (Lean `Flower.lean`, no hypotheses; standard axioms); one open lemma (rainbow transversals) with computation.** Manuscript: endpoint-structure §7, "The flower move" (Lemma 60 – Question 66). This is the positive counterpart of the last-edge barrier.

- **Flower lemma** (Lean `flower_decomp`, from `exists_close_cut`). Close paths P_1..P_k into cycles C(P_i) = P_i + (src, tgt). Let L be a path whose edges are one e_i ∈ C(P_i) each. Then the paths C(P_i) − e_i, together with L, are k + 1 paths. They cover all the cycle edges, with b = 2 on V(L) and 0 elsewhere.
- **Equality forces a flower** (Lean `hub_cycles`). Suppose b(s) = |T|, b = 1 on T and 0 elsewhere. Then |D| = |T|, every path joins s to T, and each t ∈ T ends exactly one path. With the edges st, the paths close into edge-disjoint cycles through s.
- **Receipts at a hub.** With the seed b = 1 on N(s), the j-th grouped receipt has supply d(s) − j against j blanks. So it succeeds iff j < d(s)/2; at j = d(s)/2 we reach exactly the equality state. "Either a further receipt succeeds or the paths close into cycles."
  - A Lovász seed provides this when d(s) = n − 2, N(s) ⊆ Ev(G) and the non-neighbour s* is even.
- **Flower move** (Thm 62). A transversal through s gives |D| + 1 paths with b(s) = 2.
  - Within budget iff |D| ≤ n/2 − 1, i.e. there was a spare path.
  - The move itself needs no edge count. Hamiltonicity only matters for the existence of a transversal.
  - L has |T| = d(s)/2 edges. For CP(m) this is m − 1, the barrier's minimum.
- **CP(m)** (Thm 63; Lean `cocktail_passes_of_rt`, `cocktail_rooted_of_rt`). Lovász on CP(m) − star(s), with m − 1 paths. Then m − 1 receipts: supplies 2m − 2 − j > j. Equality follows, and the cycles are Hamiltonian by the edge count 2m(m − 1) = (m − 1)·2m. A transversal finishes the proof. So **the rooted test for CP(m) ⇐ RainbowTransversal(m − 1).**
- **Transversals for ≤ 4 cycles** (Prop 64; Lean `rainbowTransversal_three`, `rainbowTransversal_four`).
  - Greedy s a_1 a_2 a_3 settles k ≤ 3.
  - For k = 4, if a_3's two C_4-neighbours are s and a_1, the path a_2 a_3 s a_1 x works, where x is a_1's other C_2-neighbour.
  - **So CP(4) and CP(5) pass, unconditionally** (Lean `cocktail_passes_four`, `cocktail_passes_five`). CP(4) is missing-move Prop 5.5; CP(5) is new (n = 10).
- **Open: rainbow transversals for k ≥ 5** (Question 66). No failures for m ≤ 10 (E16). Random greedy fails 5–15% of the time, so a proof needs rotations.

### Rainbow transversals and receipt-or-flower (follow-up 6)

**Grade: Proved (receipt-or-flower; B′ by hand; Lean `flower_decomp_rest`); rainbow-transversal lemma for k ≥ 5 still open, with literature and computation.** Manuscript: endpoint-structure §7, after Question 66 (Theorem 67, Proposition 68).

- **Literature.** Nothing covers our case: colour degree exactly k with every colour class 2-regular, path length k, at a prescribed vertex.
  - Chen–Li: colour degree ≥ k gives a rainbow path of length ≥ k − 1 for 3 ≤ k ≤ 7, and ≥ ⌈2k/3⌉ + 1 for k ≥ 8. The conjecture k − 1 is open.
  - Andersen's n − 2 conjecture for proper colourings of K_n holds asymptotically (Alon–Pokrovskiy–Sudakov).
  - Gyárfás–Mhalla: length (2n + 1)/3 in 1-factorisations. Maamoun–Meyniel: no rainbow Hamilton path in some 1-factorisations of K_{2^t}.
  - Graph systems (Joos–Kim): these need minimum degree n/2 in each graph.
- **Computation** (`tools/rainbow_variants.py`).
  - The transversal starting at s exists also for random 2-factorisations with short cycles (m ≤ 8). So Hamiltonicity is not the point.
  - Warnsdorff greedy without backtracking fails in about 1% of cases from m = 8.
  - Segment transversals (one contiguous segment per cycle; the flower lemma extends verbatim) were always found by a no-backtracking rule, m ≤ 11. This is a promising route for a proof.
- **Receipt or flower** (Thm 67). Let b_D(s) = d_H(s), and let b = 1 on T (non-neighbours of s in H). Then either
  - some t ∈ T ends a path avoiding s, and appending ts works (missing-move Lemma 5.1); or
  - the T-paths all join T to s, close into cycles, and any transversal L gives |D| + 1 paths with b' = b − |T|·[s] − 1_T + 2·1_{V(L)}. Other paths are untouched (Lean `flower_decomp_rest`).
  - With a Lovász seed and receipts from all of N(s), no other paths are left exactly when G is Eulerian, n is even and d(s) = n − 2.
- **B′ resolved by hand** (Prop 68): K6 core U, a full vertex x1 with a leaf ℓ, and adjacent full vertices x3, x4.
  - Setup: Lovász on B′ − x1 gives 4 paths. Three receipts follow (supplies 1 > 0, 5 > 1, 4 > 2).
  - Case (1): append tx1, then the leaf edge, then the new path t′x1t″. This gives b = 2 at core vertices.
  - Case (2): the count 31 = 3·8 + 7 is tight, so the cycles are Hamiltonian on V − ℓ. RT_3 then gives a transversal x1 a1 a2 a3, and the flower plus the leaf edge give 5 paths with b(a1) = 2, a1 ∈ U.
  - Sym(U) gives (R) at every core vertex; odd vertices hold by parity.
- **A_{6,2} core roots.** The partition in missing-move Prop 5.2 already has b = 2 at the two core vertices t′, t″. By Sym(Q) this gives (R) at all core roots, which that manuscript lists as uncovered. (To be confirmed by the missing-move session.)

### Credit: CP(m) is SP Theorem 10.21 (follow-up 7)

- **The rooted test for CP(m) = K_{2h+2} minus a perfect matching, at every root and every m ≥ 4, is separating-pairs Theorem 10.21** (gallai/02-november-25/separating-pairs.pdf, pp. 44–45). The proof is explicit:
  - take the Walecki cycles on {t} ∪ Z_{2h};
  - detour each antipodal missing edge through y, the mate of t, which gives h Hamilton cycles;
  - open all of them along Q = (t, 1, …, h), adjoin Q, and extend by the leaf.
  - The same theorem proves that both orientations fail Fan's numerical test in every partition of (F − e)^t within budget.
  - So `cocktail_fan_barrier` re-derives its negative half in leafless form, and the CP(m) flower is its positive half. **Question 66 is moot for CP(m)**; it is kept only as an independent combinatorial question about arbitrary Hamilton decompositions and the receipt route.
- **Marked-reduction Theorem 38 / Corollary 39**:
  - j ≤ 7 edge-disjoint cycles through x (not necessarily Hamiltonian) partition into ≤ j + 1 paths with ≥ 2 ends at x; the count is Chu–Fan–Zhou Lemma 2.5.
  - Corollary 39 has the same structure as receipt-or-flower.
  - So the receipt route closes CP(m) for m ≤ 8 without any transversal, and Prop 64 (k ≤ 4) is subsumed.
- **Separating-pairs Theorem 13.18**: neighbour-exchange conditions for opening any number of cycles through a vertex, including segment-type openings.
- **What remains ours:**
  - the flower lemma in this generality, formalised (it also appears in MM Lemma 5.4 and in the proof of MR Theorem 38);
  - "equality forces a flower" (`hub_cycles`);
  - receipt-or-flower (Thm 67; close to MR Cor 39), and Prop 68 (B′ by hand);
  - the Lean files `Flower.lean` and `FanBarrier.lean`.
- **Endpoint-structure §7 updated:** credits at the barrier, the flower lemma, Thm 63 and Question 66, and in the abstract. Rainbow-transversal work is stopped at the coordinator's request.

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

> **Correction (§S, cloud session missing-move).** The incompleteness at n = 8 is an artefact of the game allowing only one-edge new paths. With *path insertion* (a new path of any length made of held edges) the game wins every root of every connected graph of order 8 with |F| ≤ 9 (9 is needed for K8 minus a perfect matching). Pósa moves at the profile level repair none of the losers. The paragraph below stands as originally written. Read "Lovász + Fan transfers alone" as "with one-edge new paths only".

**Consequence for the programme.** Full Gallai cannot come from Lovász + Fan transfers alone, even with (R) as the induction hypothesis. One of two ingredients is needed:
- **(M) a move beyond Fan's inequality.** Fan's lemma is iterated Pósa rotation. When the inequality is tight, a rotation still moves the missing edge from uv to uw and moves an end from v to w. A two-end transfer at equality, as the d6-frontier agent suggests, is of this kind.
- **(H) a stronger induction hypothesis** that controls the zero set of the seed. Candidates are EMC (matroid exchange) and FD with several prescribed vertices.

The n = 8 losers are the natural test bed: the right move or hypothesis must make every one of them winnable. Cloud session "missing-move" (ROADMAP).
## P. Two-even-vertex problem (cloud session)

*Session branch `claude/two-even-lovasz`. Manuscript: `manuscripts/endpoint-structure`, §5 (Remark 15 to Proposition 30); numbers below are the current PDF's. Lean: `lean/GallaiLean/TwoEven.lean`, sorry-free, standard axioms only, Lovász only as `LovaszStatement`. Sanity checks: `tools/two_even.py`.*

### P.1 Dictionary

The leaf dictionary (Lemma 5) gives an exact equivalence:

> Ev − {u, v} is realisable ⇔ G^{Ev−{u,v}} is **tight**, i.e. meets the parity bound p = |Od|/2.

Here G^{Ev−{u,v}} is G with a pendant vertex at every other even vertex, and it has exactly two even vertices. So the second descent step *is* the two-even problem for these graphs. The apex graph G + z + ℓ of §O gives only the sufficient direction.

Side remark (Remark 15): Lemmas 3 and 4 (faithful partitions; removing one vertex, "Lemma 3" in older notes) hold at every order. Use pendant vertices instead of the apex.

### P.2 The mechanism

This answers the "Fan moves preserve the number of paths, descent needs a merge" gap.

1. Delete an edge uw between two even vertices. Both become odd, so Lemma 4 in G − uw already has the descended size: o/2 rises by one and |S| falls by two.
2. Fan's Lemma 3.4 then puts uw back at constant size, moving u's end to w.
3. Its hypothesis, "fewer zero-end neighbours of w than ends at u", becomes: w has no neighbour among the removed even vertices.

When w is adjacent to a removed vertex, Fan's **grouped** lemma takes over, with two candidate edges into w. This is the pair step.

### P.3 Results

| # | Statement | Status |
|---|---|---|
| Lemma 18 (Fan descent) | u, w ∈ S ⊆ Ev, uw ∈ E, N(w) ∩ (Ev − S) = ∅, S − {u,w} realisable in G − uw ⇒ S − u realisable | **proved, lean** `realisable_erase_of_fan` |
| Lemma 19 (Fan transfer) | u ∈ Ev − S, w odd, uw ∈ E, the even neighbours of w other than u lie in S, S realisable in G − uw ⇒ S realisable in G | **proved, lean** `realisable_of_fan_transfer` |
| **Thm 20 (second step)** | u, v, w distinct even, uw ∈ E, vw ∉ E ⇒ Ev − {u, v} realisable | **proved, lean** `realisable_evenSet_erase_pair` |
| **Cor 22** | non-realisable pairs {u, v} are **E-twins** (same neighbours among the other even vertices); twin classes are cliques or independent sets of G[Ev] | **proved, lean** `etwin_of_not_realisable` |
| Cor 23 | FD step 2 from Ev − u with root r fails only if Ev − r lies in u's twin class: G[Ev] ∈ {K_e, empty, K_{e−1} + isolated r, star at r} | proved; lean `fd_second_step` (non-twin form) |
| Thm 24 (Fan certificates) | even steps (E) and odd transfers (O) compose; soundness | **proved, lean** `FanCert`, `realisable_of_fanCert` |
| **Cor 25 (uniform in d)** | a semi-induced matching x_i w_i in G[Ev] (w_i ≁ x_k for k < i), with j = e/2 and r ∉ {x_i}, gives (R) at r for critical G. In MR Thm 114(i) this is a condition on J[N(z)] alone, for every d. | **proved, lean** `realisable_of_fanSchedule` |
| **Thm 26 (pair step)** | u, a, a' distinct even; w ≠ u a common neighbour of a, a'. If w is even of degree ≥ 4, or w is odd with aa' ∉ E or a, a' ≁ u, then Ev − {u,a} or Ev − {u,a'} is realisable. Uses Fan's grouped lemma, then the single lemma. | **proved, lean** `realisable_pair` |
| **Cor 27 (FD step 2)** | e ≥ 4, u ≠ r. Some v ∉ {u, r} works unless (i) G[Ev] is edgeless and the N(a), a ∈ Ev − {u, r}, are pairwise disjoint, or (ii) e = 4 and G[Ev] = K_3 + isolated r | proved (manuscript); ingredients in lean |
| **Thm 28 (goal (b))** | G connected, e ≥ 4, r ∈ Ev ⇒ there are u ≠ v in Ev − r with Ev − {u, v} realisable, **unless e = 4 and G[Ev] = K_3 + r**. The edgeless case uses a shortest path between even vertices as a Fan certificate. | proved (manuscript); path step in lean (`OddPath`, `realisable_of_oddPath`) |
| Prop 29 (moves L, S, C) | pendant neighbour; degree 2 with non-adjacent neighbours (suppression); all neighbours even and kept (star) | proved; not in lean (vertex deletion) |
| Prop 30 (obstructions) | (O1) odd vertex of degree n − 1 (this contains the edge bound); (O2) triangle uvx with d(u) = d(v) = 2; (O3) N(u) = N(v) = {x, y}, xy ∈ E, d(y) = 3; exact gluing rule at a cut vertex | proved; (O1) in lean `degree_le_of_tight` |

**Link to `claude/emc-four-even`.** For e = 4, Cor 22 says: if a 2-set {x, y} of even vertices is not realisable, then its complement {u, v} is an E-twin pair. Equivalently, x and y see u and v alike. This constrains which 2-sets can be non-bases, independently of the matroid axioms.

### P.4 What is left of the second step

- **Prescribed u, Cor 27(i).** The even vertices are independent, and each a ∈ Ev − {u, r} has a private set of odd neighbours. Paths avoiding N(u) still give certificates (Thm 28's argument), so only a u whose neighbourhood blocks all such paths resists.
- **Four even vertices, triangle plus isolated r.**

Both resist Fan moves, since every move sees a zero-end neighbour. Neither case produces a failure through n = 8: at n = 8 there are 1357 instances of Cor 27(i)/(ii) and 399 of the Thm 28 exception, all succeed.

**Update: both are closed by `two_step_descent`** (`lean/GallaiLean/EMCFour.lean`, base branch `claude/quirky-dirac-d9km1q`, emc-four workstream). It says: connected G, even order, e ≥ 4, y ≠ w even ⇒ some even v ∉ {y, w} has Ev − {w, v} realisable. I rebuilt the base branch in a scratch worktree: the build is green, and `#print axioms two_step_descent` shows only the standard axioms (Lovász enters as the hypothesis `LovaszStatement`). With y = r and w = u it settles Thm 28, and Cor 27 for connected G, in full, K_3 + r included (manuscript Remark 32). Connectivity matters: P_3 ⊔ (K_5 − e) with r the middle vertex of P_3 is a disconnected instance of exception (ii) where no v works. The twin criterion (Cor 22) and the pair step (Thm 26) still give explicit information: which pairs can fail, and which candidates suffice.

### P.5 Corrections to §O, and computations

- "u, v degree-2 twins" is **not** an obstruction: in K_{2,4} plus an edge, every twin pair of degree-2 vertices is realisable. K4 − e fails by (O1).
- Prop 13 (e = 4) proves (R), i.e. r is an end of some n/2-partition. Its statement claims a realisable 2-set, and the proof does not show the profile is simple (Cor 6 allows an odd vertex with 3 ends). The claim needs a check.
- Census of two-even graphs (experiments E13):
  - n = 4: 3 graphs, 2 not tight, both (O1).
  - n = 6: 47 graphs, 17 not tight: 16 (O1), 1 (O2).
  - n = 8: 2668 graphs, 372 not tight: 344 (O1), 21 (O2), 4 (O3), and 3 with a cut vertex where one side is infeasible.
- **Every non-tight 2-connected graph with n ≤ 8 is (O1).** Conjecture 31: a 2-connected two-even graph is tight unless an odd vertex is universal.
- At n = 6: every non-realisable pair is an E-twin pair (384 pairs in graphs with e ≥ 3; 12 non-realisable pairs when e ≥ 4); 565 pair-step instances, no violation; 657 Fan-schedule certificates, all realisable; 3 + 9 residual instances of Thm 28 / Cor 27, all succeed.
- **Lean: done** (`lean/GallaiLean/Bridge.lean`, about 2,000 lines, no sorry, standard axioms, no Lovász hypothesis).
  - **`gallai_of_branching : (∀ j ≥ 3, BStmt j) → GallaiConjecture`.**
  - `rooted_six_of_bstmt3`: B_3 gives the rooted test for six even vertices.
  - `dstmt_of_branching`, with `dstmtE_succ` as the one-level step.
  - Pieces are `restr G C` graphs on the same vertex type, with isolated vertices allowed. The level statements apply to them through `H.induce {non-isolated}` (`desc_of_dstmt`).
  - Gluing (1) is `glue_bridge`: erase the B⁺ bridge path, take the union, replace the A⁺ bridge path by the concatenation. Gluing (2) is `glue_append`: union, then `append_move`.

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

**Completeness at n = 8** (E14). *Not reproduced: see the correction in §R. An independent run leaves 6 critical losers, including K_{2,2,2,2}.* The session reported that, with path insertion, the game wins every root of every connected graph of order 8:
- |F| ≤ 4 suffices for all but 47 graphs;
- of the 47: 35 need |F| = 5, 6 need 6, 4 need 7, Guv]~{ needs 8, and K8 − perfect matching needs 9 (every held set of size ≤ 8 loses).

The certificate for K8 − PM holds the star at the root plus three edges. Its play is a relay into the hub, receipts, one donation, and a new path 1–4–2–0–7 of length four through the hub.

All the certificates found for the five §R losers are hub-shaped: an isolated hub, receipts, then one new path through the hub, sometimes extended along a further held edge. A hub of degree d with b ≥ 1 on its neighbours absorbs ⌈d/2⌉ adversarial receipts. So the spare path closes it iff d ≤ 5.

**Pósa moves fail at the profile level.** Two candidate moves were proved and tested.
- *Rotation* (Lemma 4.1 in the manuscript): either uv appends, or the opponent picks W ⊆ N(u) of size b(v), we pick w ∈ W, and the held edge becomes uw.
- *Fan's alternative* (Lemma 4.2, new): either some t ∈ T transfers, or at least Σ_T b blank neighbours z of u can each be *activated* (end t → z, held edge tu → zu). This is the "rigidity at equality" of d6-frontier §8, made into a statement. As game moves it dominates rotation.

Neither repairs any losing root: rotation with ≤ 2 uses and |F| ≤ 4; the alternative with ≤ 2 uses and |F| ≤ 4, or 1 use and |F| ≤ 6.

Why: the losers need the spare path to be spent on a 2-edge path c–s–d through the hub. Imitating it with a one-edge path cs plus a transfer of sd needs to know that one of the three paths ending at s is cs, which avoids d. The profile forgets this. *Path insertion is the memory of one explicit path.* The obstruction at n = 8 is budget allocation, not exchange.

**Degree six: the pure star is one receipt short** (manuscript §5). A degree-6 hub absorbs 3 adversarial receipts. Closing it with one spare path needs 4, and the 4th is exactly at Fan's equality (supply 3, three blanks).

On A_{6,2} (K6 core of degree-8 vertices, a full vertex x with a leaf ℓ, two false twins on the core; n = 10) the 4th receipt is forced by **append-or-through plus an edge count**:
- if every path ending at T = the remaining core neighbours passed through s, then, since b(s) = d_H(s), the three s-paths would join T to s;
- the fourth path would then be ℓx;
- so 30 edges would have to fit in three paths of ≤ 8 edges, which is impossible.

This is the d6 frontier's "short by one" (Remark 3.5), and the "two-end transfer at equality" made concrete. The rigid configuration must be refuted by information *outside* the profile (path lengths).

On K8 minus a perfect matching (n = 8, 6-regular) the 4th receipt *always* fails: all three Lovász paths of G − s end at the hub. The count then makes the three paths plus the held edges three Hamiltonian cycles through s, a **flower**. Cutting one edge from each so that the three cut edges form a path s–a–w–z spends the spare path and gives (R) (manuscript Lemma 5.4, Prop 5.5). This is a genuine two-end move at equality: the ends move from T to the transversal path. It too is invisible in the profile.

**In the game** the pure-star deficit is bypassed by holding more edges: relays feed the hub, and the inserted path runs through the hub along the extra held edges.
- K8 − PM needs |F| = 9.
- The Q2-type graph B′ (K6 core, a full vertex x1 with a leaf, two adjacent full vertices; n = 10) loses with a star plus ≤ 2 edges. It wins at every root with a star plus 3: the star at x1 plus a core triangle, then a relay, receipts, and the new path 0–2–1–x1–5.
- **A_{6,2} loses at every root with a star plus ≤ 3 edges.** This is the resistant case we know of. The count above closes its twins and odd roots by hand with the pure star, so a sound count move would let the game do the same. Its core roots are covered by neither the game nor the count; (R) holds there by CP-SAT.

**Follow-up (missing-move, after the coordinator's notes).**
- *Criticality.* The five E13 losers are non-critical (p = 3) and fall to the split rule. Of the 47 `np`-losers at \|F\| ≤ 4, 19 are critical, and path insertion wins them all (\|F\| ≤ 9).
- *The critical Gqz~vw at root 3* is closed by the **odd-neighbour hub** (Thm 2.5): s = 3 has degree 4 and one odd neighbour x = 6. Holding xz (z = 0) extends the new path to y′–s–x–z. In Lean: `hub_four_odd_ends`, and `gqz_rooted_three` by `decide`. It is an instance of BranchBase3 (k = 3), with a simple final profile {0, 3, 7}.
- *Profile-level flower move* (Lemma 5.7; Question 5.6(b) of the earlier draft) for Hamiltonian flowers, j ≤ 4 (transversal Lemma 5.6). With it the game wins CP(4) and CP(5) at every root with one held star, attaining `cocktail_insertion_barrier` (m − 1 inserted edges). It adds nothing on A_{6,2}, B′, the other dense n = 8 graphs, or a sample of 5 critical n = 10 graphs.
- *Correction:* A_{6,2} is closed at every root (Prop 5.2 + Sym(Q)); B′ is closed by hand (endpoint-structure Prop 68).
- *Receipt or flower with a count* (manuscript Lemma 5.9; option `rf`), plus the orbit rule, wins A_{6,2}, B′, CP(4) and CP(5) at every root with one held star. On a sample of ten random critical n = 10 graphs it changes nothing. The first miss is **Inv~|~zbw** (K10 − {02, 17, 19, 24, 29, 39, 58}, roots 2 and 3, star + ≤ 2). There the count 33 < 35 decides neither case: a degree-6 hub with two odd neighbours. With a star plus 3 edges (\|F\| = 9) it wins without `rf`, via a second hub along the inserted path 4–3–6–2–8. So every sampled graph is won.
- *Hubs of arbitrary degree* (manuscript §6; Lean `Ach.hub_receipts`, `Ach.hub_general`, `Ach.relays`, `Ach.relay_hub`, `Ach.two_hub`). A degree-d hub whose neighbours carry Σb ≥ 2d − 5 costs one path. Relays z → x from even non-neighbours raise the supply (relay-hub Thm 6.4). Two isolated hubs with one common neighbour share one new path (Lemma 6.5). This is the receipts-only half of the d6-frontier hub calculus, with the spare path as payment.
- *Hub-strategy conjecture* (Conj 6.7): at a BranchBase3 root, star(y) + X wins with \|X\| ≤ lb(y) + c. It holds at n = 8 with c = 2 (all 9268 root orbits). At n = 10 it **needs c ≥ 3**: Inv~|~zbw roots 7 and 9 (E14 addendum 3). The proved theorems cover 2757/9268 root orbits at n = 8 and **none** of the 108 in the n = 10 sample. At high degree the game wins by moves (donations, rf) that the lemmas do not cover.
- *Re-derivations (archive integration).* missing-move Prop 5.5, (R) for K8 − PM, is the case m = 4 of separating-pairs Thm 10.21. That theorem gives (R) for every CP(m), m ≥ 4, by Walecki Hamilton cycles opened along Q = (t, 1, …, h). It also proves the failure of Fan's test, which `cocktail_fan_barrier` formalises. The flower lemmas are special cases of marked-reduction Thm 38 (j ≤ 7 cycles) and cycle-and-contact Thm 1 (12 nearly spanning cycles). The hub shape at path level is marked-reduction Cor 39. On Inv~|~zbw, separating-pairs Thm 12.29 with y = 9 (G − 9 = K9 − 4 edges, rainbow Hamilton decomposition of Javadi–Miralaei, repaired in jm-repair) gives (R) at the roots 9 and 6. It does not decide 1, 2, 3, and the other roots are not of its form. Inv~|~zbw is a density boundary, so held-edge caps are not raised further.
- Still open: a sharper count than Lemma 5.9 (Inv~|~zbw); a transversal lemma for every j, which would give a flower for every CP(m) (emc-four session); completeness at n = 10 (manuscript Question 5.11); donations and paybacks after the spare-path hub, to reach a simple profile (needed for BranchBase3 when d ≥ 6).

**Consequences.**
- §R's "Lovász + Fan is incomplete" is corrected: at n = 8 the missing move was path insertion, which is already in the Lean insertion library (`Ach.addPath`).
- Inductive seeds have Σb = n and so no spare path. The spare path is the floor ⌊N/2⌋ at odd order. An induction that keeps it needs floor bounds at odd order, which hold only in special classes: Lovász's, and the BP_t. The hub lemma turns any such floor partition of G − s with ends on N(s) into (R) at a degree-four vertex s.
- The next difficulty is the degree-six hub. At Fan's equality the rigid configuration (Fan's alternative plus append-or-through) must be refuted by an edge count, recombined as a flower, or bypassed by longer inserted paths. The open questions are Question 5.9 of the manuscript: (a) is the game with path insertion complete at n = 10, with A_{6,2} as the test; (b) is there a profile-level move capturing the count or the flower.

**Reconciliation (n = 8).** The six critical graphs that lose with \|F\| ≤ 6 are closed as follows. Five win with \|F\| = 7–8 (missing-move E14, orbit runs; Guv]}{ root 0 independently confirmed at \|F\| = 7). K8 − perfect matching is settled by the flower lemma (missing-move Prop 5.5): when the fourth Fan receipt at a degree-6 hub fails at equality, the three paths close into Hamiltonian cycles through the hub, and cutting them along a transversal path gives the two ends. So at n = 8 the rooted test follows from Lovász + Fan + path insertion + the flower move. The open question is a *profile-level* version of the equality move (missing-move Question 5.6), which would make the game self-contained at n = 10.

**Barrier theorem (Lean, FanBarrier.lean).** For CP(m) = K_{2m} − perfect matching (m ≥ 4), every decomposition of CP(m) − ut has ≥ m paths, and > m when Fan's condition holds. So *no* argument whose final step re-inserts one edge by a Fan transfer or as a one-edge path can prove the bound for CP(m), whatever came before: Lovász seed, induction hypothesis, or oracle. The cocktail party graphs are therefore a certified test family for any proposed missing move. The flower recombination (missing-move Prop 5.5) passes this test at m = 4. A uniform flower argument for all CP(m), and then a profile-level form of it, is the natural next target.

## T. EMM sufficiency: the inductive template (track C4; coordination with emc-four)

Contribution from the missing-move session, 2026-11-27. Details: E17, missing-move §7.

- **Class.** The induction needs general profiles. The general-profile cut criterion is **false**: n = 7, p = 2 (FqJBo, a 2-linkage obstruction), and 17 failures at n = 8 with p ≤ 3. Proposed class: **EMM⁺**, p ≥ ⌈n/2⌉ per component.
  - EMM⁺ holds for all profiles at n ≤ 7, for all profiles with p = 4 at n = 8, and on the n = 8 sample at every p.
  - EMM is the special case of half-sets.
- **Minimal counterexample (proved).** It is connected, and has no reducible leaf or degree-2 vertex (Lemma 7.8).
  - The leaf case is in Lean, `EmmTemplate.lean`.
  - Names used there: `cutCount`, `CutOK` (conditions (L), (C) for general profiles), `cutOK_leaf`, `ach_of_leaf`, `leaf_step`. C1 may want to reuse or rename `CutOK`.
- **Template test.** Moves are new path, Fan transfer, concatenation and path insertion.
  - Stuck instances remain at n = 6 (12 among reduced instances; 6 in the EMM⁺ class even with path insertion of any length).
  - Each one is at **Fan's equality**, or is a concatenation with one end at each endpoint.
  - So step (2) of the template needs an equality lemma producing a tight cut. The stuck instances, which include the butterfly, the octahedron and `Eqzo`, are the test cases.
- Not done here: 2-connectivity of a minimal counterexample through TVS Thm 7 / SP §2 gluing.
- **Update, same day: EMM is false** (missing-move Theorem 7.5; E17 addendum).
  - Construction: glue an n = 8 below-budget linkage failure that has a leaf to a realisable gadget through a degree-2 vertex with b = 2, which no path crosses. This gives simple half-set counterexamples of order 12: 12 graphs, all confirmed by `tools/cut_test.py`.
  - The budget version EMM⁺ already fails by padding (Example 7.4).
  - Open repairs (Remark 7.6):
    - (a) EMM when no vertex with b = d is a cut vertex. All counterexamples have such a cut vertex; a 2-connected version needs two saturated separators.
    - (b) Cut conditions plus linkage conditions for the pieces below their budgets.
  - Consequence for the programme: Gallai ⇐ EMM + CS no longer stands as stated. CS and EMC remain as before.



## U. EMM definitions for Lean, and cut selection (tracks C1/C2; coordination with lean-d6-frontier)

Contribution from the emc-four session, 2026-11-27. Manuscript: `manuscripts/endpoint-min-max/`. (The coordinator asked for this as §T, but §T was already taken by C4.)

**Shared definitions.** Reuse `CutOK G b p` from `EmmTemplate.lean`. It is form (a) of the manuscript's Lemma 1, written as Σ_W b + d(v) + b(v) ≤ cut(W) + 2p. Then:
- `simpleProfile G M v := if Odd (G.degree v) then 1 else if v ∈ M then 2 else 0`;
- `HalfSet G M := M ⊆ Ev ∧ 2 * M.card = Ev.card`;
- `CutFeasible G M := CutOK G (simpleProfile G M) (Fintype.card V / 2)`;
- `EMM : Prop := ∀ G connected of even order, ∀ M, HalfSet G M → CutFeasible G M → Ach G.edgeSet (simpleProfile G M)`, together with Ach's path count;
- `CS0 G := ∃ M, HalfSet G M ∧ CutFeasible G M`, `CS G := ∀ r ∈ Ev, ∃ M ∋ r, …`, `PS G := ∃ P` (a pairing of Ev) `, ∀ transversals M, CutFeasible G M`.

**Theorems for the Lean session.**
- `cutOK_of_ach` (necessity, any profile): realisation by p paths ⇒ `CutOK b p`. The manuscript's proof is by arms: each edge vy is extended along its path to an end, and the arms are edge-disjoint and end at distinct end occurrences. This may be easier to formalise than ED's count.
- `gallai_of_emm_cs0 : EMM → (∀ G, CS0 G) → GallaiConjecture`. The odd-order case uses a pendant vertex. The case e = 0 needs no hypothesis (M = ∅).
- Optional: `cutOK_iff_arm` (the algebra (a) ⇔ (c), which needs b(V) = 2p).

**C2 targets that are finite and elementary** (no flows needed):
- `parity_Gv`: |δ_{G^v}(Y)| ≡ |Y ∩ Ev| (mod 2);
- `good_pairing_of_cuts` (the "if" half of the manuscript's Lemma 13);
- `guarded_route_lemma` (Thm 17): a token-injection argument plus parity;
- `cone_ps`: the T-join pairing lemma plus the guarded route lemma with the apex as bypass.

The exact cone criterion (Thm 15) needs Gale's theorem. It is not needed for CS.

**Open after this session.**
- Conjecture GR: every connected even-order graph has a guarded route system. This would give PS ⇒ CS.
- Why EMM's family is a matroid on critical graphs (Question 12). Four n = 8 critical graphs are not explained by one dominant vertex or by a submodular cap: Gs`ALo, GsQcaO, GqHTTS, GqhTTS.
- (R) ⇒ (R_s): turning a rooted partition into a simple one.

**Related work (added after the coordinator's pointer).** The manuscript now has a related-work section (§6). It covers Lovász 1968, Pyber, Fan, Bonamy–Perrett, Botler–Sambinelli, Lovász–Cherkassky, Mader/Frank splitting, Gale/Hoffman, T-joins and Okamura–Seymour.
- New **Prop 24** (proved; numbered 22 before the C2 update): completely splitting off any vertex v in G_b (Mader) preserves the EMM conditions at every other vertex. What splitting loses is only the "each path passes v once" constraint: the cycles through t may use at most one split edge from v. So a splitting proof of EMM must choose Mader pairs compatibly with this, which is the same equality phenomenon as in §T.
- Lovász–Cherkassky is recorded as an analogy of proof structure (simultaneous Menger numbers), not as a reduction. With pendant terminals, the slot-respecting packing is trivial here; the content of EMM is covering all edges.
- **EMM₃** (δ ≥ 3), the corrected target, survives the first refutation attempts (E17 addendum 2, Remark 7.7).
  - The bridge or edge-cut analogue of the counterexample mechanism needs a δ ≥ 3 "core" (pendant leaves plus a cut-feasible non-realisable simple profile). There is none up to order 8 exhaustively, and none in 4,000 random cores of orders 9 and 10.
  - EMM₃ has no failure on 3,000 random graphs at n = 10 or 300 at n = 12. These samples never hit a cut-infeasible half-set.
  - Next: targeted dense cores (2-separators with TVS records), then the equality lemma inside δ ≥ 3, with linkage conditions for below-budget pieces.


**C2 closed (later the same day): CS holds for every connected graph of even order** (manuscript Thm 21; Lemmas 19–20; Cor 22 as revised after EMM was refuted: EMM₃ at δ ≥ 5 ⇒ every Gallai failure is an SP 10.16(1) witness).
- *Construction.* J = the T-join (T = Ev) of a spanning tree, and F = G − J. F^v is F − (edges at v) + (v joined to its non-neighbours).
  - Lemma 19 (parity): F has all degrees odd. The odd vertices of F^v are exactly the J-neighbours of v, plus v itself iff v is even.
  - At each v, pair those odd vertices by edge-disjoint paths of F^v (T-join pairing lemma), and use the pairs as J's transitions at v; v's partner gives v's end edge.
  - J is a forest, so the transitions decompose J into paths pairing Ev.
- *Why it is good* (Lemma 20). For v and Y ∌ v, a split pair is either charged to its own J-edge of δ_{G−v}(Y), or it is bad. A bad pair has a transition at v split by Y, and it is charged to the edge of δ_{F^v}(Y) on that transition's linking path. Since |δ_{G^v}(Y)| = |δ_{J−v}(Y)| + |δ_{F^v}(Y)|, the pairing criterion (Lemma 13) holds.
- *Key point.* Once J is fixed, vertex v's cut system depends only on v's transitions, and in a forest those can be chosen independently. That is how the simultaneity is resolved.
- *Lean.* Lemmas 13, 19, 20 and Thm 21 are elementary. With them, the reduction to EMM needs no CS hypothesis. Since EMM is false, the Lean target should be `cs_all` (Thm 21) plus the SP 10.16 bookkeeping of Prop 9, with the hypothesis EMM₃ restricted to δ ≥ 5. Without a Lean SP 10.16, a cleaner standalone target is `cs_all` by itself.
- *Matroid side* (coordinator's question). Edmonds' intersection theorem gives CS for any two vertices' conditions, because each I_v has rank ≥ ⌈|A|/2⌉ on every A. Three such matroids can fail (the three partition matroids on {1,2,3,4}), and F needs up to 6 of the F_v at n = 8. So matroid intersection does not give CS; Thm 21 does.

**EMM refuted; corrected to EMM₃** (after missing-move Thm 7.5; manuscript revised).
- KsOeBW??G`?A with M = {3,4,8,9,10} is cut-feasible but not realisable. I re-verified this here with cutfeas.c and realis.c. The mechanism is saturated degree-2 vertices.
- The manuscript now states **EMM₃** (δ ≥ 3) as Conjecture 4, with the example. Prop 9 and Cor 22 are rephrased: EMM₃ at δ ≥ 5 plus CS (Thm 21) excludes SP 10.16(2). Hence any Gallai failure is an SP 10.16(1) witness: odd order 2h+1, 2-connected, no matching cut, ≥ h+1 missing edges, p > h.
- **Evidence caveat.** At n = 6, 8 and in the n = 10 random sample, every half-set of a δ ≥ 3 graph is realisable (19,422/19,422 at n = 8), so EMM₃ holds vacuously there. Binding cuts at δ ≥ 3 occur in the bottleneck families (22 graphs, 62 cut-excluded half-sets, 0 failures) and in the two-blob samples (`evidence.py blobs`). EMM₃ needs larger tests with binding cuts.
- CS (Thm 21) is unaffected: it concerns cut-feasibility only.

**Post-pivot (endpoint-min-max rewritten).**
- Gallai-reduction statements are removed (old Prop 9, Cor 22). Theorem numbers up to Thm 21 are unchanged (EMC became Conjecture 10 to keep them).
- New Sect. 5, hardness:
  - Def 22: G(H).
  - Lemma 23: |δ_{L(H)}(A)| = 2·#mixed vertices, so λ(L(H)) ≥ 4 iff H is bridgeless.
  - Prop 24: the gadget is cut-feasible iff λ(L(H)) ≥ 4.
    - At R-vertices, (c) reduces to |δ_{L(H)}(X)| ≥ 4 for X ∌ w*, because adding gadget vertices to Y never lowers the slack.
    - At gadget vertices it is automatic once L(H) − w* is connected.
  - Prop 25: realisable iff L(H) is Hamiltonian-decomposable.
  - Thm 26: Kotzig.
  - Thm 27: NP-completeness.
- Note: bridgeless suffices; the synthesis's "essentially 4-edge-connected" is stronger than needed.
- Lean: Lemma 23 and Props 24–25 are elementary. Kotzig would be imported.
### T.handoff (missing-move session → fresh session on the equality lemma), 2026-11-27

**Exact current target: EMM₃.** Let G be connected, of even order n = 2k and minimum degree ≥ 3. Let M be a half-set of Ev(G), with the simple profile b (1 on odd vertices, 2 on M, 0 on Ev − M). Then b is realised by k paths **iff** (L) and ED inequality (1) hold for every v and every W ⊆ V − v. Lean predicate: `CutOK G b k` in `EmmTemplate.lean`.

**What is known to fail, so the statement must not claim it** (missing-move §7):
- **General profiles.** One failure at n = 7 (FqJBo, p = 2, a 2-linkage), and 17 at n = 8 with p ≤ 3 (Prop 7.1).
- **The budget class EMM⁺.** Padding FqJBo with leaves at its saturated vertex gives a failure at n = 10 with p = 5 (Ex 7.4).
- **EMM.** Gluing a below-budget failure with a leaf to a gadget through a degree-2 vertex with b = 2 gives 12 graphs of order 12 (Thm 7.5).
- **Common mechanism.** A vertex with b = d is never crossed, and an edge cut restricts exactly to its side plus temporary leaves. The decomposition can therefore isolate a **below-budget piece**, where a linkage obstruction is invisible to (1).

**What a general inductive statement must add.** Edge deletion leaves δ ≥ 3 and simple profiles, creating degree-2 vertices and b up to 3. So the induction needs a general class. Proposed shape, untested:
- Decompose (G, b) at every saturated vertex (b = d), at every edge cut, and along forced one-edge paths (both ends saturated). Assign each piece its own budget p_piece = Σ_piece b / 2.
- Assert: if every piece has p_piece ≥ ⌈n_piece/2⌉, then cut-feasible ⇒ realisable.
- For pieces below their budget, a separate **linkage condition** is needed, in the spirit of the Seymour–Shiloach–Thomassen 2-linkage theorem. FqJBo is the planar square with two doubled sides.
- Test set for that condition: the 17 n = 8 failures (`gemm8_lowp.log`) and FqJBo (`gemm7.log`).
- Checks still to make: that the decomposition is well defined, and that the padding and gluing counterexamples are exactly the below-budget-piece cases.

**Equality lemma, (c′) form** (the target of the next session). Setting: (G, b) is in the class and cut-feasible, uv is an edge, H = G − uv, and D is a partition of H with the adjusted profile b′. Suppose the re-insertion move is at equality: a Fan transfer with b′(u) = |Z_H(v)|, or a concatenation with b′(u) = b′(v) = 1. Then one of the following holds:
- (a) the move succeeds for D;
- (b) another move succeeds: a concatenation, a rotation then append, a guarded split, or a path insertion;
- (c′) D exhibits a set W with uv ∈ δ(W) on which (1) is **tight**, or a saturated separator that splits G into pieces one of which is below its budget.

(c) with a *violated* cut is impossible in any class that contains the counterexamples above, by minimality. The force behind (c′) should be `hub_cycles`: at equality every path ending at u passes v, entering through distinct blank neighbours.

**Test cases (stuck instances, all n = 6, reduced).**
- EMM⁺ class, single-edge moves: 14 stuck (`tmpl6_plus.log`, with diagnosis in `tmpl6_plus_diag.log`). Every one has a cut-feasible move that fails only at equality.
- With guarded splits and path insertion (L ≤ 5): 4 stuck, namely EsRo with b = (0,3,0,2,1,0) and (0,3,2,0,1,0), Eqzo with (0,0,3,0,3,0), and Eu^o with (0,0,3,0,3,0) (`tmpl6_plus_split_peel5.log`).
  - Eqzo reduces exactly to a below-budget piece: the edge 24 between two saturated vertices is a forced path, which leaves 2 paths on G − 24.
- The simple class (b ≤ 2) has more: 38/456 stuck, 28 with splits and path insertion (`tmpl6_simple*.log`).
- Further test cases: the butterfly, the octahedron with four ends at antipodes, and C4 with b = (0,2,2,0) (`tmpl6_red_diag.log`).

**EMM₃ evidence so far: no counterexample.**
- Cores (pendant leaves, all other degrees ≥ 3, cut-feasible but not realisable): none up to order 8, exhaustively; none in 4,000 random cores at orders 9–10.
- Cores at a vertex 2-separator (no end-record at the terminals realisable, though some record is cut-feasible): none among 8,774 graphs, 101,524 terminal pairs and 976,339 profiles up to order 8 (`emm3_sep_core.log`).
- Random EMM₃ at n = 10 and 12: no failure, but no half-set was cut-infeasible, so the test is non-discriminating.
- Binding test (`tools/emm3_binding.py`, `emm3_binding.log`): 47 structured δ ≥ 3 graphs (cliques K4–K6 joined by 3–5 edges, spread or concentrated; K4 chains and triangles; cones over two cycles joined by 1–3 edges, ED Thm 46 type, n ≤ 12).
  - 1,063 half-sets, of which only **8 are cut-infeasible**, all in K5+K5 with 3 or 4 concentrated join edges. The other 1,055 are realisable: **0 failures**.
  - So the test discriminates only weakly. At n ≤ 12 these cones never bind.
  - A sharper binding test needs sparse δ = 3 graphs with small edge cuts and many marks on one shore (cubic-like shores). Larger n needs `tools/cutfeas.c`.
- Forcing gadgets (proposed next, not done): δ ≥ 3 blocks with two temporary leaves whose every realisation joins, or always separates, the leaves. They would replace the degree-2 vertices of a below-budget core (n ≈ 25–35).

**Tools.** All take graph6 input. The logs are in `manuscripts/missing-move/scripts/outputs/` and are reproduced by `emm_runs.sh`.
- `tools/gemm_test.py`: the cut criterion, general profiles.
- `tools/emm_template.py`: the template moves, with options reduced, atleasthalf, simpleclass, split, vertex, peelL and diag.
- `tools/emm_split.py`: splitting off, with exact lifting.
- `tools/emm_glue_search.py`, `tools/emm_lift_search.py`: the counterexample constructions.
- `tools/emm3_core_search.py`, `tools/emm3_sep_core.py`, `tools/emm3_random.py`, `tools/emm3_binding.py`: the EMM₃ searches.
- `tools/emm_reduction_check.py`.
- Lean: `lean/GallaiLean/EmmTemplate.lean` (`CutOK`, `cutCount`, `leaf_step`). No sorry.

#### T.handoff-2: the forcing-gadget search for an EMM₃ counterexample (for a fresh session)

**Exact gluing argument** (edge-cut restriction; proved, missing-move Remark 7.7 and Theorem 7.5).
- Let F = δ(K) be an edge cut of G with |F| = s, and let D be any partition of G into paths with profile b. Then D restricted to E(K) ∪ F is a partition of K⁺ := K plus one new pendant leaf ℓ_f per cut edge f, with profile b on K and b(ℓ_f) = 1, into (b(K) + s)/2 segments.
- Reason: a path meets K ∪ F in segments, and each segment ends at a vertex of K with an end of the path, or at a cut edge, which then ends at its leaf.
- So: **G realisable ⇒ K⁺ realisable**. If K⁺ with this profile is cut-feasible but not realisable (a core), no G built on K by an edge cut realises b.
- A vertex with b(c) = d(c) is likewise never crossed (Thm 7.5, used at d(c) = 2). Under EMM₃ (δ ≥ 3, simple profiles) such vertices do not exist, so only edge cuts remain.

**The difficulty.** Every known core has degree-2 vertices: FqJBo (n = 7), the 17 order-8 failures in `gemm8_lowp.log`, and in particular **GsOeBW** with b = (0,0,1,1,2,0,0,0) and **GqGUDg** with b = (0,1,1,1,1,0,0,0), the two with a leaf. There is no δ ≥ 3 core up to order 8:
- edge cuts and leaves: 1,146 graphs (`emm3_cores*.log`);
- vertex 2-separators: 8,774 graphs (`emm3_sep_core.log`);
- random orders 9–10: 4,000 graphs.

**Gadget specifications.** Replace each degree-2 vertex w of a core, with neighbours x and y, by a block D attached through two edges x–x′ and y–y′. Here x′ and y′ are in D, every vertex of D has degree ≥ 3 in the result, and D has a simple profile. By the gluing argument, D⁺ is D plus temporary leaves λ_x (at x′) and λ_y (at y′), each with one end.
- **Pass-through gadget** (for w with b(w) = 0): every partition of D⁺ with the chosen profile has **one segment with ends λ_x and λ_y**, and it must have at least one partition. The core then sees exactly "a path from x to y", as through w. Realisations correspond: a core partition with x–w–y ↔ a G-partition joining the two core segments through D. The segments must be distinct, which holds because w is interior.
- **Double-end gadget** (for w with b(w) = 2): every partition of D⁺ has λ_x and λ_y on **different** segments, each ending inside D, and at least one partition exists. The core then sees two separate path ends, as at w.
- **The core's own leaf** (for example vertex 3 of GsOeBW) needs no gadget: make it a bridge into the surplus block B.
- Global constraints:
  - the glued G must have δ ≥ 3;
  - its profile must be a **simple half-set** (Σb = n), with the surplus coming from B, as in Thm 7.5;
  - it must be **cut-feasible**.
- Non-realisability then follows from the gluing argument; no oracle is needed.

**Search plan.**
1. Enumerate small δ ≥ 3 blocks D (order 4–8, graph6 from `data/conn*.g6`) with two attachment vertices x′, y′ and simple profiles. For each, determine with `realis.profile_ok` and the enumerator `all_partitions` in `tools/emm_split.py` whether every partition of D⁺ joins the leaves (pass-through) or separates them (double-end).
2. Assemble GsOeBW (or GqGUDg) with gadgets for its degree-2 vertices and a surplus block B joined by a bridge at the core leaf. The order will be about 25–35.
3. Verify cut-feasibility with **`tools/cutfeas.c`**. Its input is one graph per line, "n m u1 v1 … um vm" (n ≤ 20, n even), and its output is the number of cut-feasible half-sets and their bitmasks. It is O(2^n) per half-set, so it needs **n ≤ 20**. Either keep the assembly small (gadgets of order ≤ 4–5, shared or merged), or extend it to n ≤ 32 with uint64 masks and a single prescribed half-set instead of all of them.
4. As a cheaper first step, glue just one gadget into the core and check the partial instance (degree-2 vertices remaining elsewhere) with `tools/cut_test.py` / `realis` at n ≤ 14. This verifies the gadget's forcing behaviour in context.

**Logs and tools** (all in `manuscripts/missing-move/scripts/outputs/`; `emm_runs.sh` reproduces them):
- `emm_counterexamples12.g6` and `emm_counterexamples12_cut_test.log`: the Thm 7.5 graphs;
- `emm_glue_GsOeBW.log`, `emm_glue_GqGUDg.log`: the gluing search;
- `gemm7.log`, `gemm8_lowp.log`: the cores below budget;
- `emm3_*.log`: the EMM₃ searches.

Tools: `tools/emm_glue_search.py`, `tools/emm3_core_search.py`, `tools/emm3_sep_core.py`, `tools/emm3_random.py`, `tools/emm3_binding.py`, `tools/emm_split.py` (`all_partitions`), `tools/gemm_test.py` (`prepare`, `feasible` for general profiles), `tools/cut_test.py`, `tools/realis.c`, `tools/cutfeas.c`.


**Coordination after EMM₃ was refuted (n = 18, emm3-gadgets) and while audit A13 runs.**
- *Placement.* The gadgets/δ ≥ 3 material belongs to the emm3-gadgets session. Proposal: it becomes §5.3 "Minimum degree three" of endpoint-min-max, written by that session. After A13's edits land, emc-four will only:
  - change Remark 28 ("EMM₃ open") to point to §5.3;
  - drop EMM₃ from the open problems.
  No duplicate text.
- *Lean plan for `cs_all` (Thm 21).* It needs no forests and no route paths. One engine lemma suffices.
  - **Transition lemma.** J is any finite graph and T = Odd(J). For each v, τ_v pairs D_v = N_J(v) ∪ [v ∈ T]{v}. Then some pairing P of T satisfies σ_P(Y) ≤ |δ_{J−v}(Y)| + s_v(Y) for all v and all Y ∌ v, where s_v(Y) counts the τ_v-pairs split by Y.
    - Proof: induction on |E(J)|. Follow transitions from some a ∈ T to get a trail Q ending at c ≠ a (orbit of an injective dart map). Delete E(Q); the unused transitions stay valid. Then P = P' + {a, c}. If a and c are split, Q crosses either δ_{J−v}(Y) or a split v-transition (or ends at v from Y); this is a walk lemma.
    - The trail form of manuscript Lemma 20 needs no forest: a bad trail may revisit v, but one of its v-transitions is split.
  - **T-join pairing in F^v**: the same lemma with J := F^v and arbitrary transitions, using s_v(Y) ≤ e(v,Y).
  - **T-join existence** for T = Ev in connected G: induction on |T| with paths and symmetric difference.
  - **Parity of F^v**: Lemma 19.
  - **Edge identity**: |δ_{G^v}(Y)| = |δ_{J−v}(Y)| + |δ_{F^v}(Y)|.
  - **Pairing criterion ⇒ CutOK** for the profile of every transversal.
  - Mathlib provides `Walk.IsTrail.even_countP_edges_iff`, `even_card_odd_degree_vertices` and `deleteEdges_adj`.

**Simpler proof of Thm 21 (found while planning the Lean proof; checked by `scripts/auxgraph.py` on all n ≤ 8).**
1. **Pairing lemma, cut form.** For any finite graph Γ, Odd(Γ) has a pairing π with σ_π(S) ≤ |δ_Γ(S)| for every S.
   - Proof by edge deletion. Delete xy and take π' for Γ − xy.
     - If x and y were both odd in Γ − xy and paired with each other, drop the pair.
     - If they were paired with x′ and y′, replace these pairs by {x′, y′}.
     - Mixed cases are analogous.
     - When both are even in Γ − xy, add {x, y}.
   - The cut-indicator triangle inequality [x′y′] ≤ [x′x] + [xy] + [yy′] gives the bound. No paths, components or handshake are needed.
2. **One auxiliary graph B on V × V.**
   - Take a T-join J (T = Ev) and F = G − J.
   - Copy v carries F^v on {v} × V. Each J-edge vx gives (v,x)–(x,v).
   - Lemma 19 gives Odd(B) = {(v,v) : v ∈ Ev}.
   - For v and Y ∌ v, put S = {(u,w): u ≠ v, u ∈ Y} ∪ {(v,w): w ∈ Y}. Copies u ≠ v do not cross, copy v contributes δ_{F^v}(Y), and J-edges contribute δ_{J−v}(Y). So |δ_B(S)| = |δ_{G^v}(Y)|.
3. Hence the pairing of Odd(B) from step 1 is a good pairing of Ev (Lemma 13). **So Thm 21 = the pairing lemma applied to B.**

This is the Lean route: the T-join (paths + symmetric difference), the pairing lemma (edge deletion), B with its parity and cut identity, and the CutOK algebra. It will also go into the manuscript as the main proof after A13's edits land; the transition proof becomes a remark.

**Lean: `cs_all` is done** (`lean/GallaiLean/CutSelection.lean`, `PairingLemma.lean`; standard axioms; full build OK). The statement matches §U: `CutOK G (profile G M) (card V / 2)` for every transversal M of a pairing P of `evenSet G`, for connected G of even order. The proof is the auxiliary-graph proof, so Thm 21 now has a machine-checked proof independent of audit A13.

#### T.result-3 (emm3-gadgets session, 2026-11-27): forcing gadgets exist; EMM₃ is false; hardness at even degrees ≥ 4

Details: E19; endpoint-min-max §6 (`sec:gadgets`, Lemmas 29–40, Thms 41, 42, 45). Branch `claude/emm3-gadgets`, merged with the coordinator branch at 5976455.

- **Placement (done, no further edits needed from emc-four).** §6 is a separate section, "Minimum degree three and beyond: forcing gadgets", placed after §5 (`sec:hard`) rather than as §5.3, because it brings eight lemmas of its own. This session has already made the follow-up edits proposed above:
  - Remark 28 now points to §6;
  - open problem 1 is replaced by gadget questions;
  - the abstract, overview and the paragraph after Question 4 are updated;
  - `Als08` (Walecki) is added to the bibliography.
  If emc-four has meanwhile edited Remark 28, keep either wording; the content is the same.
- **Handoff-2 correction.** A "double-end gadget" (forcing the two leaves apart) is useless. By Lemma 29 applied to the outside, the outside always sees two leaves, and forcing apart constrains nothing (Remark 32(1)). Only *joined* forcing matters. It imitates a degree-2 vertex with b = 0, never the saturated b = 2 vertex of Thm 7.5. The search plan "replace each degree-2 vertex of GsOeBW" therefore cannot work for the saturated vertex. The closing lemma (both forced edges at one outside vertex s) replaces it.
- **Gadget ⟺ one-saturated-vertex failure** (Remark 32(2)). A two-leaf gadget at x₁ ≠ x₂ is the same as a non-realisable profile X + w with w the only degree-2 vertex (b(w) = 2), all other degrees ≥ 3, and the cut conditions at every other vertex. Ports of a forced pair carry no ends (Remark 32(3)).
- **Results.**
  - The two-leaf gadget D₂ has order 10 and is of least order (none with |X| ≤ 9).
  - G₁₈ has order 18, δ = 3, λ = 2.
  - G_r, r ≥ 2, has δ = λ = 2r, all degrees even, and κ = 3 (half blow-up) or 2r − 1 (full blow-up, r = 2, 3).
  - G′(H), the Kotzig graph with a marked clique in place of the saturated tail, gives NP-completeness for 4-edge-connected graphs with all degrees even and ≥ 4 (Thm 45). G′(Petersen) has n = 28 and δ = 4.
  - Every proof is oracle-free. The forcing comes from the 2r-regular multigraph M_r (C_{2r}, multiplicities r−1, r, plus w), which has a unique Hamiltonian decomposition; K_{2r} blocks are crossed exactly twice by each cycle (Lemma 34).
- **TRC (synthesis §15) survives every construction here.** All failing half-sets starve the gadget, so they need N > |δ(D_r)| = 2r pairs across the cut, while Thm 21 routes are edge-disjoint. Refuting TRC with gadgets would need a forcing gadget with about half its even vertices marked. None exists with |X| ≤ 9, of any kind.
  - Suggested test of TRC: G_r and G′(H) with marks moved inside the gadget, using Thm 21 pairings from random spanning trees. Realisability at n > 16 needs `tools/realis_wide.c`, which is slow on dense S, or a sparse S.
- **Lean (task item 3) not applicable.** Gadgets exist, so the positive structural lemma it would formalise is false. A Lean proof of Thm 41 would need path-partition infrastructure for the closing lemma (Lemmas 29, 31), plus the Hamiltonian-decomposition argument for D₂ (Lemmas 33, 34, 36). The cut-feasibility half is a finite check, too large for `decide` at n = 18. Not attempted.

**Manuscript sync (emc-four, 2026-11-27).** I merged `claude/emm3-gadgets` (§6, `sec:gadgets`) into `claude/emc-four-even`, keeping both texts in this section. I kept its fix of Remark 28 and open problem 1, which settles EMM₃ and points to §6. Added on top:
- **Thm 21 now has the B-graph proof as its main proof** (valid for any T-join; it also proves the explicit construction by lifting each route to a path of B). For a forest J, the pairings obtained from B are exactly the Thm-21 (constructible) pairings. The linked-transitions argument (Lemma 20) is kept as the second proof of the construction.
- §4.4 "Transversals of the constructed pairings" (`sec:trc`). It contains A13's remark on good pairings, the A13 evidence on the twelve order-12 graphs, the starving argument, and **Conjecture TRC** (unnumbered, so the numbering of §6, Lemmas 29–40 and Thms 41–45, is unchanged). It also gives TRC ⇒ Gallai (odd order via a pendant edge) and TRC ⇒ (R_s) at every even r.
- Rem 9 (`rem:converse`) points to TRC.
- The abstract mentions TRC.
- Formalisation (`sec:lean`) records `cs_all`.
- TRC is open problem 1, the main one.
- One correction to the gadgets text: open problem 2, bullet 2 now says "constructible pairing" instead of "good pairing". A13's n = 12 witness is a failing transversal of a *good* pairing that needs no gadget.

#### T.result-4 (emm3-gadgets session): TRC versus gadgets, the balance lemma, and a test of "balanced EMM"

This answers the coordinator's TRC messages. The route-descent session owns the TRC extension step; this note is for it.

1. **Is V(S) a transversal of a constructible pairing?** No: not in G₁₈, G_r or G′(H). The reason is the balance lemma below.
   - G₁₈: D₂ has 8 even vertices, all unmarked, and |δ(D₂)| = 2. A transversal equal to V(S) would need 8 split pairs.
   - G_r: N split pairs are needed, but there are only 2r cut edges.
   - G′(H): N split pairs against 4 cut edges.

   On G₁₈ the constructible pairings built from 12 random trees give 10 distinct pairings. **None of them splits δ(D₂) at all**, so every transversal has exactly 4 marks in D₂, and **all 2,560 transversals are realisable** (`scripts/trc_probe.py`, `outputs/trc_G18.log`). G₂ was not tested: realis_wide.c does not finish on its dense S within 600 s.

2. **Balance lemma** (the obstruction that protects TRC from every gadget construction here). Let P be a constructible pairing with edge-disjoint routes in J, and M a transversal, U = Ev − M. Then for every X ⊆ V,

   | |M ∩ X| − |U ∩ X| | ≤ #(pairs split by X) ≤ |δ_J(X)| ≤ |δ(X)|.

   Proof: a pair inside X contributes one vertex to M and one to U; a pair outside contributes nothing; a split pair contributes ±1. Each split pair's route crosses δ(X), and routes are edge-disjoint.
   - So constructible transversals cannot starve or flood a region behind a small cut. This is exactly what Lemma 31 (closing), Thm 41, Thm 42, Thm 45 and the Kotzig graph G(H) exploit.
   - The lemma is **not** implied by cut-feasibility: V(S) in G₁₈ is cut-feasible with imbalance 8 across a 2-edge cut.
   - Nor is it necessary for realisability: L in G(H), for Hamiltonian H, is realisable with imbalance N − 4 across 4 edges.

3. **"Balanced EMM" (BEMM), a candidate clean statement between Thm 21 and TRC.** Every cut-feasible half-set satisfying the balance condition | |M ∩ X| − |U ∩ X| | ≤ |δ(X)| for all X is realisable.
   - BEMM ⇒ TRC ⇒ Gallai, by the lemma.
   - **Test on G₁₈** (the only informative δ ≥ 3 failure graph small enough for the oracle): 10,136 of 12,609 cut-feasible half-sets are balanced, and **all 10,136 are realisable** (`scripts/balance.c`, `scripts/bemm_run.py`, `outputs/bemm_G18.log`).
   - The n = 12 failures (KsOeBW-type) are good tests too. Their failing half-sets contain a whole one-edge route (manuscript remark). A version with δ(X) restricted to the T-join's edges, |δ_J(X)|, is the sharper invariant to test there.
   - Caveat: BEMM is a characterisation-type statement, so by Thm 27 it cannot be decided in polynomial time unless P = NP. Balance is polynomially checkable (it is a cut condition on the signed vector χ_M − χ_U), so BEMM would contradict the hardness theorem unless every hard instance is unbalanced. **That holds for G(H) and G′(H)**: their starving half-sets are unbalanced. So BEMM is consistent with Thm 27 and Thm 45, but a balanced hard family would refute it.
   - A natural adversarial next step: hardness reductions whose half-sets are balanced.

4. **Hardness and connectivity.** G′(H) (Thm 45) is 4-connected and 4-edge-connected on the prism, K₃,₃, the cube and Petersen, by computation only. So prescribed-half-set realisability is NP-hard on graphs with δ ≥ 4 and λ ≥ 4, and very likely on 4-connected graphs too, but there is no proof of κ ≥ 4 in general.
5. **Balance as linkage** (Gale/Hoffman; added). With x = χ_M − χ_U, the balance condition is |x(X)| ≤ |δ(X)| for every X. Since x(V) = 0, this is the cut condition for a single-commodity flow with unit supplies on M, unit demands on U and unit edge capacities.
   - So **M is balanced iff M and U can be paired by edge-disjoint paths of G, each pair consisting of one marked and one unmarked vertex.** This is checkable by one max-flow.
   - BEMM thus reads: *a cut-feasible half-set that admits an edge-disjoint M–U linkage is realisable.*
   - This parallels the cone theorem (manuscript Thm 15). In a cone, the cut-feasible half-sets are exactly the transversals of pairings of Ev by edge-disjoint paths avoiding the apex.

## V. Route descent (cloud session `claude/route-descent`, 2026-11-27)

*Experiments: E20. Manuscript: `manuscripts/route-descent/route-descent.tex`. Oracle: `tools/route_ext.c`.*

### V.1 Verdicts on the brief's observations
- **Upward closure, heredity, base, extension** (synthesis §17): all correct as stated; heredity is also machine-checked on every route of every construction in E20. Two small additions: deleting a route never isolates a vertex (an interior vertex of degree 2 would be even and also a route end, forcing J-degree ≥ 3), and linking paths of a component never leave it.
- **Extension ⟺ terminal route.** "Some realisation of G − E(R_p) has V(Q_c) ∩ V(R_p) = {c}" is equivalent to "G has a realisation of M in which R_p is a terminal segment ending at a". This is what the oracle tests.

### V.2 The finding: minimality of J removes the extension problem (in the data)
- With spanning-tree T-joins the extension fails (4–5% of queries). Almost all failures are *trivial*: the unmarked end c has degree 2 and the route runs through c's other neighbour, so Q_c cannot leave the route. Stuck transversals (no route works) occur only in this way, and re-routing fixes every one.
- **With a minimum T-join, every route admits the extension for every transversal** (E20: about 210,000 queries, no failure). Moreover a **route-respecting realisation** exists: all routes are terminal segments at once.
- Why minimality is natural. (i) A min T-join is a forest, so Thm 21 applies. (ii) Every subpath of a route is a geodesic of G; in particular routes are induced, so the trivial obstruction is impossible. (iii) **Minimality is inherited by route deletion**: a smaller T′-join K′ of G − E(R_p) would give the smaller T-join K′ ∪ E(R_p) of G. (iv) A matching that is a T-join is minimum. So the class "Thm-21 system on a minimum T-join" is closed under the descent.
- Hence the **strengthened invariant**: prescribe that J is minimum. The induction hypothesis then needs nothing about end-paths at all, if conjecture RR holds.

### V.3 RR is a constrained Lovász theorem
A route-respecting realisation of M is the same thing as a Lovász decomposition D of F = G − J (all degrees odd, one end per vertex) such that (RR1) the path of D at each unmarked end c_p meets R_p only in c_p, and (RR2) a path whose ends are two unmarked ends c_p, c_q has R_p, R_q vertex-disjoint. So:

> **Conjecture RR.** For a Thm-21 system on a minimum T-join and every transversal M, F has a Lovász decomposition satisfying (RR1), (RR2).

RR ⇒ TRC for min-T-join systems ⇒ Gallai. RR\* (one D for all M) is false (E20).

The single-edge case is the cleanest: J = N a perfect matching of G[Ev] (always minimum).
> **Conjecture L_N.** If F has all degrees odd and N = {c_i a_i} is a matching of non-edges of F, oriented c_i → a_i, then F has a Lovász decomposition in which the path at each c_i avoids a_i (then (RR2) is automatic).

L_N would give **Gallai for every graph whose even vertices induce a subgraph with a perfect matching**, which includes every Eulerian graph with a perfect matching. Gallai is open there; Pyber, Fan and Botler–Sambinelli need the even subgraph to be a forest, or blocks of maximum degree ≤ 3. Its one-pair case is **L1** (avoid one non-neighbour), and E20 finds no failure of L1, L1e, L∞ or L_N.

### V.4 Proved: separation at distance three (the base of the programme)
**Theorem (separation).** If G has at most one vertex of positive even degree and dist(c, a) ≥ 3, then G has a decomposition with ends ≡ degrees mod 2 in which **no path contains both c and a**.

Proof: Lovász's own induction (Lovasz.lean cases I–III) carries the invariant through, because of one observation about **Fan's lemma**. Its proof (a chain of re-routings and one append) keeps the vertex set of every path, except that one path gains the target vertex g. So any Fan transfer with g ∉ {c, a} preserves separation. At distance ≥ 3, every case of Lovász's induction can choose its target outside {c, a}. Corollary: **L1 holds when c and a have no common neighbour.** At distance 2, separation can fail (7-vertex example with an even vertex), while L1 survives. So the right inductive invariant there is still to be found.

**Lean (done).** `lean/GallaiLean/Separation.lean`: **`separation`** and **`lovasz_avoid`**, sorry-free, standard axioms, full build green. They rest on `FanSupport.lean` (**`fan_single_supp`**: Fan's lemma with vertex sets) and on support-tracking copies of `Retract.delete` and `PathDecomp.add_edge`.

**Multi-pair version (conjecture, strong evidence).** If all degrees are odd and disjoint pairs are each at distance ≥ 3, some Lovász decomposition separates every pair. E20: 2,892 instances (n = 8–16, 925 of them perfect matchings), 0 failures. At distance 2 the symmetric version is false (about 22% of instances fail).
- It would give Gallai, with every orientation realisable, for every graph whose even subgraph has a perfect matching none of whose edges lies in a triangle. This includes all triangle-free Eulerian graphs with a perfect matching.
- The proof of the one-pair theorem does not extend: when every vertex is paired, every Fan target is paired, and the path gaining the target may contain its partner.

**L1 at distance 2: how far the induction goes.** The L1 invariant (Q_c ∌ a) survives a Fan transfer towards g ≠ a when c ∉ N(g). The chain lies in N(g) ∪ {t}, and re-routings keep vertex sets. When c ∈ N(g) it survives provided the path through the edge cg avoids a: if c enters the chain, c's end moves onto exactly that path.
- So Lovász's induction proves L1 except in two residual configurations:
  - (R-I) the even vertex z has N(z) ⊆ N[c] ∪ {a};
  - (R-II) all degrees are odd and the non-isolated vertices are c, N(c) and a, with N(a) ⊆ N(c) and every vertex of N(c) of degree ≥ 3.
- In addition, leaves adjacent to c finish at once (Q_c = cv), and leaves outside N[c] are deleted.
- Separation itself fails at distance 2 in about 15% of all-odd instances (E20), so the residual cases need an invariant strictly between L1 and separation.

### V.4a Proved: L1 in full (the leaf trick)
**Theorem (L1).** If all degrees of F are odd and c, a are distinct and non-adjacent, some Lovász decomposition of F has a ∉ V(Q_c). More generally, Q_c can avoid any packed set Y ⊆ V ∖ N[c], while every path meets Y at most once.

Proof, in one step from the separation theorem. Attach a new leaf ℓ at c: K = F + cℓ.
- In K the vertex c is the **only** vertex of positive even degree, and dist_K(ℓ, a) = 1 + dist_F(c, a) ≥ 3.
- Separation therefore gives a Lovász decomposition of K in which no path contains both ℓ and a.
- The path through ℓ is ℓ c w ⋯. It does not stop at c, because c has no end.
- Delete ℓ. The result is a Lovász decomposition of F whose path ending at c avoids a.

**Lean (done).** `Separation.lean`: **`lovasz_avoid_set`** and **`lovasz_avoid_nonadj`**, sorry-free, standard axioms. `OnePair.lean`: **`realisable_two_even_adj`**, one step of route descent end to end (L1 on G − ca as the base, `route_append` as the step, which now also records that R is terminal). `Retract.delete_supp` now also returns that each new path is the kept part of an old path.

So the residual configurations (R-I), (R-II) of V.4 are moot: the right invariant was not to be found inside Lovász's induction on F, but on F + leaf.

What L1 does and does not give:
- It is the m = 1 case of L_N / RR, and it makes the edge ca terminal at a (Cor "onepair", now without the triangle condition).
- It gives **no new realisability class by itself**. The first pair of any Fan schedule is always free, and one-edge "mixed schedules" (one pair appended last via L1, the rest by Fan) need the special pair to be a sink of the schedule digraph, so they are already acyclic.
- **Limits** (E20):
  - L1 is false in graphs that already have an even vertex z (e.g. the path c z a). In 5,399 random pairs it failed 648 times, always with dist(c, a) = 2, z ~ a, and N(z) ⊆ N[c] ∪ N[a].
  - Multi-leaf *packed* separation is false: with leaves at three pairwise non-adjacent vertices, the star K_{1,3} already fails. With two leaves plus one packed extra vertex, it fails in about 1% of instances. So any extension must be pair-by-pair.
  - For m ≥ 2 pairs, the leaf trick creates m even vertices, one per tail. So L_N ⇔ separating each leaf from its head in a graph whose even vertices all carry pendant leaves. MSEP (all-odd) is the analogue without even vertices. A proof of MSEP that tolerates even vertices with pendant leaves would give L_N at distance ≥ 2, hence Gallai for every graph whose even subgraph has a perfect matching.
- **Open, with evidence.**
  - **S1**: both a ∉ Q_c and c ∉ Q_a at distance 2, in one decomposition. 998 decided instances, 0 failures.
  - **One-sided separation (BALL)**: with ≤ 1 even vertex, Q_s ⊆ B_2(s); 3,195 instances (n ≤ 15), 0 failures. Via the leaf, BALL ⇒ Q_c ⊆ N[c] in all-odd graphs (itself 5,026 vertices, 0 failures), which gives (RR1) for any single route of a minimum T-join.

### V.4c L∞ via the leaf: Lovász's induction leaves one residual configuration
**Target.** L∞ (synthesis §18 priority 1): in an all-odd F, some Lovász decomposition has V(Q_c) ⊆ N[c]. Attaching a leaf, this is GL: if K has ≤ 1 positive even vertex and ℓ is a leaf with neighbour c, some Lovász decomposition has the path through ℓ inside B = {ℓ} ∪ N[c]. That is one-sided separation (BALL) at a leaf.

**Key observation.** A leaf is never a chain vertex of Fan's lemma. Chain vertices after x₀ are of the form π(x, Q), which lies strictly inside Q. Fan's lemma keeps every vertex set except that of Q*, the path ending at the last chain vertex. So a Fan move with t ≠ ℓ and target u changes the ℓ-path only if Q* is the ℓ-path: then the last chain vertex is the other end y of the ℓ-path, and the ℓ-path gains u. That is harmless when u ∈ B.

**Case analysis** (Lovász's induction, in its current graph; d = distance from c):
- **I, even vertex z.**
  - z = c: delete cu for some u ∈ N(c) ∖ ℓ. The target u ∈ B. Safe.
  - z ∈ N(c): delete zc. Then c becomes the even vertex, and the target c is already on the ℓ-path, so Q* is not the ℓ-path. Safe.
  - d(z) = 2: delete zw for w ∈ N(z) ∩ N(c). Target w ∈ B. Safe.
  - d(z) ≥ 4, or d(z) = 3 with a neighbour u at d ≥ 3: every vertex of N(u) has d ≥ 2, so none is in B. So y ∉ N(u), and z ∉ B. Safe.
- **II, all odd.** Take x = c if deg c ≥ 3, with u ∈ N(c) ∖ ℓ. The Fan target is x = c ∈ B, or the new path ux is added. Safe. If deg c = 1, the component of c is the edge ℓc, which is trivial.
- **III, a leaf v ≠ ℓ.** Delete vw and add the path vw back. Safe.

**Residual (the only gap).** z is the even vertex with d(z) = 3, and **every neighbour of z is at distance exactly 2 from c**. Deleting uz (u ∈ N(z)) fails if the ℓ-path ends at y ∈ N(u) ∩ N(c) and Fan's chain from z ends at y. Counting shows this is a tight case of Fan's inequality: every vertex reachable from z is a neighbour of u, and the only u-avoiding path with an end there is the ℓ-path.
- **Partial fix.** If deg z = 2 and its two neighbours u, u′ are non-adjacent, lift: K° = K − z + uu′.
  - K° has no even vertex and fewer edges. The ℓ-path avoids uu′, since u ∉ B. Replacing uu′ by u z u′ is safe, because z is isolated in K°.
  - So the residual needs deg z ≥ 4, or deg z = 2 with z in a triangle.
  - For deg z ≥ 4, lifting one pair fails when the lifted path already passes through z.
- Lifting z–u–w to zw does not close it: the lifted path may already pass through u.
- The leaf-at-u variant gives b(z) = 2.
- The even vertex cannot be kept near c either: after deleting cu at z = c, the new even vertex u may lie far from c in the smaller graph.

So **L∞ ⇐ handling this one configuration**. BALL data (8,000+ instances, n ≤ 15) shows no failure. A targeted test of the residual configuration itself (E20, `residual_test.py`) also shows no failure, in 1,531 instances. The obstruction is in the method, not in the statement.

### V.4b Lean: Gallai ⟸ RR (formal)
`RouteSystem.lean`: **`gallai_of_routeRR`** and **`gallai_of_routeRRExists`**. If every connected graph of even order has a pairing of its even vertices, routed by edge-disjoint paths, such that for every transversal (resp. one through each even vertex) the free graph has an M-compatible Lovász decomposition (RR1 + RR2), then Gallai holds.
- The core is **`append_routes`** (Prop. rr, ⇐): routes are appended one at a time, and compatibility passes to each intermediate decomposition (the new path ends at a head, which is no tail).
- The final profile comes from the parity lemma alone; no degree bookkeeping is needed.
- So the programme's reduction "Gallai ⟸ constrained Lovász decompositions of all-odd graphs" is now formal end to end. L1 (`lovasz_avoid_nonadj`) is the m = 1 instance of the hypothesis.

### V.5 Existential version and BranchBase
- A realisable transversal M ∋ y gives Desc H k y ∅ for **every** k ≤ e/2, by upward closure on R ⊆ Ev ∖ M. So TRC_∃ ⇒ BranchBase_k for all k ⇒ Gallai (`gallai_of_branchBase`), with none of BranchBase's side hypotheses used. **Lean:** `RouteDescent.lean`, `gallai_of_pairingTRC`, `gallai_of_pairingTRCExists` and `branchBase_of_rootedHalfSets`. Also `isMinTJoin_sdiff` (heredity of minimality) and `IsEvenPairing.of_isPairing` (the `cs_all` pairings qualify).
- Measured (E20): with fixed tree routes the existential step fails about as often as the universal one (45 / 8,562 roots). The cure is minimality, not the choice of end.

### V.6 Classes (honest comparison)
- *G[Ev] has a unique perfect matching ⇒ every orientation is realisable.* This is Fan descent along an acyclic order. It is a direct corollary of endpoint-structure Cor 25 / `realisable_of_fanSchedule`; uniqueness is exactly what makes every orientation acyclic. Not new as Gallai: Gallai for these graphs follows from Cor 25.
- *Fan-isolated routes* (every vertex of a route has no even neighbours except its route-neighbours): TRC by Fan transfers along each route. Inside Pyber's class (G[Ev] is then a matching), so new only as a TRC (all-transversals) statement.
- *Separation theorem*: new as far as we know; a strengthening of Lovász's theorem.
- *L1*: now a theorem (V.4a), new as far as we know. *Conjectures RR / L_N*: new; L_N would be a genuinely new Gallai class.

## W. Multi-pair separation (cloud session `claude/multi-sep`, 2026-11-27)

*Experiments: E21. Manuscript: `manuscripts/multi-sep/multi-sep.tex`. Lean: `lean/GallaiLean/MultiSep.lean`. Audit: `research/audit/A18-multi-sep.md`.*

### W.1 Verdict
- **MSEP is not proved, and no counterexample was found.** The evidence is now much stronger:
  - all 36,024,731 distance-3 perfect pairings of the 4,060 connected cubic graphs of order 16 (and all of orders 10–14);
  - 8.26M random pairings at order 18;
  - random all-odd graphs to order 20, and 5-regular graphs of orders 30–40.
- **The reduction checks** (manuscript Prop. "reduction"). An N-edge ca is at F-distance ≥ 3 iff it lies in no triangle of G. If a path has two tails as ends, both heads are off it and distinct, so all orientations are realisable. The class is new, and it contains all triangle-free Eulerian graphs with a perfect matching.

### W.2 The right generalisation: class separation (CSEP)
- **Statement.** Partition V into *packed* sets (pairwise distance ≥ 3). Equivalently, take the fibres of a locally injective homomorphism, or the colour classes of a proper colouring of K². CSEP: some Lovász decomposition has every path rainbow.
- MSEP is the case of classes of size ≤ 2; the separation theorem is the case of one class.
- **Evidence.** CSEP never failed, including for *minimum* colourings of K² (4–10 colours).
- It is false for overlapping families (the union of three pairings), but not for the union of two.
- It holds for the fibres of coverings of all-odd graphs (lift Lovász's decomposition).

### W.3 Proved (all formalised except where noted)
- **Leaf merge** (`leaf_merge`). Let H = (K − xu) + leaf ℓ at u. A decomposition of H with no path containing both x and ℓ maps to one of K under ℓ ↦ x. The ends at x add up.
- **Prescribed end edge** (`lovasz_endEdge_set`). This is new and unconditional.
  - Statement: if all degrees are odd, then for every edge xu some Lovász decomposition has xu as the terminal edge of the path ending at x. Moreover every path can be made to meet a given packed set containing x at most once.
  - Proof: `separation_set` on H with the packed set X ∪ {ℓ}, then the merge.
  - It is the dual of the leaf trick that proves L1 (V.4a): there a leaf is attached; here an edge is detached.
- **Case II is free for CSEP** (`caseII_lift`, `classSep_allOdd`): the leaf joins x's class. So CSEP reduces to graphs with exactly one positive even vertex.
- **Certified Case I** (`classSep_caseI`): if z joins u's classes in K − uz (and {u, z} is a class), the transfer is a plain append. The manuscript also has a **rotation lemma**: remove a cycle, let c_i join c_{i+1}'s class, then extend each end path by one cycle edge; no even vertex is ever created (not formalised).
- **Sparse classes** (`separation_sparse`): CSEP holds for *overlapping* packed classes whose union X has at most one neighbour at every vertex. This generalises `separation_set`. Its Gallai corollary (every orientation realisable) lies inside Fan's class for p(G) alone.

### W.4 The obstruction, exactly
- **Equivalence** (manuscript Prop. "EE"): Lovász's Case I with a trivial Fan chain at the even vertex z and target u is equivalent to "uz is the terminal edge at u of a rainbow Lovász decomposition of K". This is **L1 at the even vertex**: the end path of z in K − uz must avoid u and u's class.
- **Conjecture EE** (for every u). Tested on 869 + 788 random pairs and 1,652 cubic-derived Case I configurations: 0 failures.
- **Why L1's leaf trick does not reach it.** The trick would attach a leaf at z, which already has the even vertex u at distance 2, giving two even vertices. L1 with an extra even vertex is false (V.4a).
- **What the data rule out:**
  - the plain hypothesis (for ~half of the configurations, no u works for every D′);
  - six natural strengthened invariants (E21 (E));
  - inductions built only from certified local moves (E21 (F): they fail on small or dense graphs).

  A proof of MSEP needs non-local information.

### W.5 Open (in order of promise)
1. Conjecture EE, even without classes.
2. **Prescribed end edges on a packed set**: are end edges prescribable at every vertex of a packed set at once? 540 tests, 0 failures. Note the split-graph form: even vertices each carrying a pendant leaf separated from them, which is exactly the shape of the remark in V.4a on L_N.
3. MSEP for cubic graphs, or for two pairs.
4. CSEP.
