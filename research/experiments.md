# Experiment log

## E1. Solver self-test

Command: `tools/pathnum.py`

Exact path numbers come out correct for:

- K2–K8;
- C3–C8;
- the Petersen graph (5);
- K5−e (3);
- K3,3 (3);
- K4,4 (3).

Each returned partition was checked to cover every edge exactly once, using only simple paths.

## E2. Complementary-pair property CP

Command: `tools/complementary.py 7`

**CP(G):** there are path decompositions D1, D2 of G such that:

- every odd vertex ends exactly one path in each;
- every even vertex ends two paths in one of them and none in the other.

Counting ends gives |D1| + |D2| = n, so CP(G) implies p(G) ≤ ⌊n/2⌋. This was motivated by:

- the complementary trail partitions in root-endpoint-costs Thm 6.1;
- the complementary cone profiles in even-degrees;
- the "any 3 of 6 doubled" prescription in six-clique;
- Li's perfect path double cover.

**Result: all connected graphs with n ≤ 7 (atlas).**

| n | CP holds | CP fails |
|---|---|---|
| 2 | 1 | 0 |
| 3 | 1 | 1 |
| 4 | 6 | 0 |
| 5 | 19 | 2 |
| 6 | 112 | 0 |
| 7 | 847 | 6 |

The failures are the odd semi-cliques (K3, K5−e, K5, and four graphs K7−H with e(H) ≤ 2), plus **two non-semi-cliques**:

- K3 ∨ 4K1 (n = 7, m = 15);
- K6 plus a vertex adjacent to three of its vertices (n = 7, m = 18).

Both satisfy the floor p = 3.

**Why they fail.** An even vertex of degree 2t cannot be an end in a t-path decomposition. In both examples the smaller member of any candidate pair would have to expose an even vertex of degree 2|D|.

**Status: REFUTED as stated.** CP is strictly stronger than Bonamy–Perrett, and it fails through degree saturation in dense odd-order graphs.

The obvious relaxation, |D1| + |D2| ≤ n + 1, is just Gallai: take D1 = D2. A degree-restricted version (for example Δ ≤ n − 2) is untested.

## E3. M-convexity of optimal endpoint vectors (Conjecture M)

Command: `tools/endpoint_matroid.py`

- **k = p (optimal decompositions):** C_p(G) is M-convex for all 142 connected graphs with n ≤ 6.
- **k = p + 1:** 3 violations at n = 6. So the property is specific to optimal decompositions.
- n = 7 (k = p) and n = 8 (critical graphs only) are running.

## E4. Plain level descent (U\*)

Command: `tools/descent.py`

- **With odd roots allowed** (three ends at an odd r): fails already at n = 4, e.g. K4. This version is irrelevant to the rooted test.
- **With even roots only:** holds at n = 4. Fails at n = 6, but only on vectors where r carries ≥ 4 ends, which a descent from a faithful decomposition never passes through.

The test was superseded by E5.

## E5. Faithful descent (FD)

Command: `tools/faithful_descent.py`

**Definitions.** S ⊆ E (the even vertices) is *realisable* if some decomposition has exactly 2 ends on S, 0 on E − S, and 1 at each odd vertex.

- Cai: E itself is realisable. Equivalently, apply Lovász to B + z, where z is joined to E.
- The realisable family is an up-set: split a path at an unexposed even vertex to add it.

**FD:** every realisable S with |S| > e/2 has, for each r ∈ S, some u ≠ r with S − u realisable.

FD implies the even-order rooted test, and hence Gallai.

**Result:**

| n | FD | rooted test (FD-reach) |
|---|---|---|
| 4 | 4/4 graphs | holds |
| 6 | 99/99 graphs with even vertices | holds |
| 8 | running | running |

**Odd-order chain version** (`tools/faithful_descent_odd.py`): is there any chain E ⊃ … ⊃ S with |S| = (e−1)/2? Such a chain gives the floor.

- n = 5: the chain fails exactly on K5 and K5−e (the semi-cliques). All 19 other graphs pass.
- n = 7: one non-semi-clique failure so far, K3 ∨ 4K1, where the floor holds. Its optimal decompositions must give an odd vertex 3 ends: all three even vertices have degree 6 = 2·3, so none of them can end a path. The odd-order chain restricted to simple profiles is therefore strictly stronger than the floor.
- At even order, no even vertex can be saturated at level n/2, since that would need degree n.

## E6. Realisable family as matroid spanning sets (EMC)

Command: `tools/realisable_matroid.py`

| | Critical graphs (p = n/2) | Noncritical graphs (p < n/2) |
|---|---|---|
| n = 4 and 6 | 37/37: minimal realisable sets have size e/2 and satisfy basis exchange, i.e. the bases of a matroid of rank e/2; all loopless | 16 of 65 are not matroids (minimal sizes {1,2} or {2,3}), as expected |

**Endpoint Matroid Conjecture (EMC).** For every connected B of even order with p(B) = |B|/2, the minimal realisable sets are the bases of a loopless matroid on the even vertices, of rank e/2.

- "Loopless" is exactly the rooted test, which is equivalent to Gallai.
- "Matroid" adds exchange structure, and suggests looking for a rank formula (a min–max theorem).

## E7. Uniform half-set statements

Command: `tools/uhc.py`

**UHC\*.** For every 2-connected graph of even order n, every set of exactly e/2 even vertices is the doubled set of some decomposition into exactly n/2 paths.

**REFUTED at n = 6.** Counterexample EsQw: edges 01 02 03 05 14 25 35 45, all degrees even, p = 2 < 3. Two hubs 0 and 5 are joined by an edge and by three degree-2 routes. If both short-route vertices 2 and 3 are internal, the hub cannot be internal. This is a non-critical graph, so it is irrelevant to Gallai.

**UHC (critical only, p = n/2).**

- n = 6: all 21 two-connected critical graphs have uniform endpoint matroids. All three non-uniform critical graphs have a cut vertex.
- n = 8: **REFUTED.** Counterexample GsaFC{: vertex 0 is universal; 6 sees 0, 1, 2, 7; 7 sees 0, 3, 4, 5, 6; vertices 1–5 have degree 2. Exactly the two complementary half-sets {1,2,6} and {3,4,5} are unrealisable. These are the two sides of the 2-separations at 0. The surviving 18 triples form a **sparse paving matroid**, which is loopless, so EMC survives. A second example, GsaFeW, has the same shape.
- Remaining question: are 3-connected critical graphs uniform? The full n = 8 run is in progress.

**Critical is not the same as trivially forced.**

Let H be K_{2k+1} minus two disjoint edges ac and bd (k ≥ 3). Add a vertex w adjacent to a and b.

- The graph is 2-connected, has n = 2k+2, Δ = n − 2 and exactly (n/2 − 1)(n − 1) edges.
- So none of the trivial lower bounds (o/2, ⌈Δ/2⌉, ⌈m/(n−1)⌉) forces n/2.
- But a decomposition into k paths would have to consist of k Hamilton paths. Each would contain w, which has degree 2, and that is impossible.
- Hence p = k + 1 = n/2.

So critical graphs, the only ones on which the rooted test bites, carry genuine Hamiltonian rigidity.

## E8. Terminal-edge prescriptions in Lovász's theorem

Commands: `tools/terminal_edge.py`, `tools/terminal_edge1.py`

| Variant | Statement | Result |
|---|---|---|
| TEL1 | In an all-odd graph, for any vertex v and edge vy, some decomposition with one end per vertex has v's end on vy | holds for all all-odd connected graphs with n ≤ 6 |
| TEL2 | the same with two simultaneous prescriptions | **fails** already in K4, e.g. (2 via 21, 3 via 31) |
| TEL1′ | TEL1 for graphs with exactly one even vertex | **fails** at n = 5 (graph Dqw) |

Motivation: TEL1′ applied to G + z with z ∼ E − u would make E − {u, v} realisable for *all* pairs. That cannot hold in general, since uniformity is refuted (E7). So the terminal-edge route only yields a second descent step under extra hypotheses.

## E9. EMC on the critical-but-not-forced family

The graph K7 − {ac, bd} plus a vertex w ∼ {a, b} (n = 8, p = 4, E of size 6): all 20 half-sets are realisable, so its endpoint matroid is uniform.

## E10. Three-connected, not-forced critical graphs

The graph is K9 minus {a1a2, b1b2, c1c2}, plus w ∼ {a1, b1, c1}. Its properties:

- n = 10, m = 36 = (n/2 − 1)(n − 1), Δ = 8, and it is 3-connected.
- 4 paths are infeasible (exact circuit solver), so p = 5 = n/2.
- **All 20 half-sets of its 6 even vertices are realisable: the endpoint matroid is uniform.** This supports conjecture (a) of connections §M.

The construction generalizes to the j-family of Prop. "critical graphs need not be forced" in endpoint-structure.

**Cones at n = 10** (`tools/emc_cones.py`): every random cone so far has a uniform endpoint matroid.

## E11. Why critical graphs are critical (n = 6)

Command: `tools/critical_reasons.py`

Connected 6-vertex graphs with at least one even vertex:

| Class | Count |
|---|---|
| non-critical | 65 |
| critical, forced by a universal vertex (Δ = n − 1) | 27 |
| critical, forced by edge count | 4 |
| critical "rigid" (no trivial bound forces it) | 3: EsPG, EqhO, Eqzg |

EqhO is a theta graph: two degree-3 vertices joined by three threads. The other two rigid graphs have leaves.

The 3-connected n = 8 classification is running. At n ≥ 10 the j-family gives 3-connected rigid examples (E10).

## E12. Cones at n = 10 (complete run)

Command: `tools/emc_cones.py 10 12 5`

9 random cones K1 ∨ H with e ∈ {4, 6} even vertices (3 trials were skipped for having e < 4). **All have uniform, loopless endpoint matroids.**

**Heuristic for conjecture (a).** The only non-realisability mechanism found so far, the theta obstruction (several degree-2 routes between two hubs), needs vertices of degree 2. In a 3-connected graph every vertex has degree ≥ 3, so every even vertex has degree ≥ 4.

## E13. Completeness of Lovász–Fan certificates (the Fan game)

Tools: `tools/fan_calculus.py` and `tools/fan_game.py`.

**Setting.** A *Lovász–Fan certificate* (the "Fan game") consists of three steps:
1. Hold a set F of edges, so that K = G − F has at most two even vertices.
2. Start from a Lovász seed on K. Either b = d_K mod 2, or, when e(K) = 2 and K has no isolated vertex, Lemma 3's profile.
3. Re-insert F one edge at a time by Fan transfers: single, or grouped with an adversarial donor. A new one-edge path is allowed if the budget permits.

The certificate wins for root r if the final profile has Σb ≤ n and b(r) ≥ 1. Every move is `fan_single` or `fan_grouped`, so a winning certificate proves the rooted test at (G, r). This is the certificate format of the d6-frontier manuscript, and it contains:
- FanCert;
- Fan schedules;
- two-step descent (flattened);
- the star lemma;
- Pyber's proof;
- the six-clique insertion schedules.

Soundness check: on P₃ ∪ (K₅ − e), the game loses exactly at the middle vertex of P₃, where the rooted test is false.

**Results.**

| Test | Outcome |
|---|---|
| FanCert (even steps and odd transfers only), n = 6 | fails on 6 of 112 graphs, including 3 with e = 4, where two-step descent is a theorem. **FanCert is strictly weaker than the full transfer game.** |
| Fan game, n = 6, every root, \|F\| ≤ 4 | **wins all 112 graphs at every root** |
| Fan game, n = 8, every root, \|F\| ≤ 4 | 50 of 11,117 graphs have a losing root |
| the same 50 graphs, \|F\| ≤ 8 | most win with larger F (for example K_{2,6} needs \|F\| ≥ 5). **Genuine losers remain.** |

The first genuine loser is GsRvnk. It has a clique Q = {0,5,6,7} of even vertices of degree 6. Vertex 1 is adjacent to Q and to a leaf 4. Vertices 2 and 3 are false twins, each adjacent to exactly Q. Roots 2 and 3 lose. The graph is not critical: p = 3, realised by (1,0,6,2,7,5,3), (2,0,5,6,3,7,1,4), (2,5,1,6,7,0,3). **So Lovász seeds with Fan transfers do not suffice for the rooted test.** The obstruction is the full-vertex configuration (connections §J; d6-frontier Thm 3.1, the terminal-step classification).

**Inductive seeds** (`fan_game.py FILE kmax ind`). The seed on K = G − F may also come from the induction hypothesis: the simple-profile rooted test on the smaller connected K, with r' prescribed and the rest of the half-set S' chosen by an adversary. With \|F\| ≤ 3 this still loses on 38 of the 50 graphs. Prescribing one vertex leaves the adversary free to put zeros next to every re-inserted edge. **An induction through Fan transfers needs a stronger hypothesis than (R)**, one that controls where the zeros of S' lie (as in EMC or FD), or a move beyond Fan's inequality.
## E13. Two-even-vertex problem and the second descent step (cloud session `claude/two-even-lovasz`)

Command: `tools/two_even.py {census,twins,pair,residual,schedule} n`. Exhaustive over `data/conn{n}.g6`. All checks are sanity checks of proved statements (endpoint-structure §5, Lean `TwoEven.lean`), except the census and the residual check.

**Census of connected graphs with exactly two even vertices** (tight = meets p = |Od|/2):

| n | graphs | not tight | (O1) odd vertex of degree n − 1 | (O2) degree-2 triangle | (O3) K4 − e pendant | cut vertex, side infeasible |
|---|---|---|---|---|---|---|
| 4 | 3 | 2 | 2 | – | – | – |
| 6 | 47 | 17 | 16 | 1 | – | – |
| 8 | 2668 | 372 | 344 | 21 | 4 | 3 (GsPDD_, GsPDDc, GsPDdc) |

At n = 8, 274 of the (O1) graphs are 2-connected; no other 2-connected graph fails. **Conjecture 31** (manuscript): a 2-connected graph with exactly two even vertices is tight unless an odd vertex is universal. The (O1) graphs at n = 8 were not solved: (O1) is a proved obstruction (Lean `degree_le_of_tight`).

**Proof checks (n ≤ 6):**

| Check | Result |
| non-realisable pairs are E-twins | 384 pairs, 0 violations |
| pair step | 565 instances, 0 violations |
| Fan schedules | 657 certified sets, all realisable |
| Fan calculus (E, O) vs truth, all pairs, n = 6 | 300 of 431 pairs certified; adding (S), (L), (C) gives 358 |

**Residual cases** (Cor 27 with u prescribed; Thm 28 with e = 4 and G[Ev] = K_3 + r): at n = 6 there are 9 and 3 instances, and the step succeeds in all of them. n = 8: see the end of this entry.
