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
