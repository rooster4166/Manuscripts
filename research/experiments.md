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

Random check of Conjecture 31 (`tools/two_even_random.py`, circuit solver `pathnum2`): 2-connected graphs with exactly two even vertices and no universal odd vertex, all tight:

| n | edge probability | graphs |
|---|---|---|
| 10 | 0.3–0.8 | 40 |
| 10 | 0.8–0.95 | 30 |
| 12 | 0.3–0.9 | 15 |

**Proof checks (n ≤ 6):**

| Check | Result |
| non-realisable pairs are E-twins | 384 pairs, 0 violations |
| pair step | 565 instances, 0 violations |
| Fan schedules | 657 certified sets, all realisable |
| Fan calculus (E, O) vs truth, all pairs, n = 6 | 300 of 431 pairs certified; adding (S), (L), (C) gives 358 |

**Residual cases** (Cor 27 with u prescribed; Thm 28 with e = 4 and G[Ev] = K_3 + r): at n = 6 there are 9 and 3 instances, and the step succeeds in all of them. n = 8: see the end of this entry.

**E13 addendum (path insertion; independent re-check).** Command: `python3 tools/fan_game.py lose8.g6 6 np`. The file holds the 50 graphs that lose with \|F\| ≤ 4; the tool includes the split rule and per-F cache clearing. **6 graphs still lose, all critical** (pathnum: p = 4 = n/2):

| graph | κ | losing roots |
|---|---|---|
| Guv]}{ (K7 + leaf at 0) | 1 | all |
| Guv]z{ | 2 | 1,3,4,5,6 |
| Guv]~{ | 2 | 2 |
| Gut~~w | 4 | 1,3,4 |
| Gu^v~w | 5 | 6,7 |
| Gr~v~w = K8 − perfect matching = K_{2,2,2,2} | 6 | all |

The earlier kmax-8 run without np was OOM-killed before it reached these graphs. The critical Gqz~vw wins with `6 np`. The cocktail party graph, in which every vertex is a degree-6 hub, is the smallest instance of the degree-six obstruction.
**Residual cases** (Cor 27 with u prescribed; Thm 28 with e = 4 and G[Ev] = K_3 + r): at n = 6 there are 9 and 3 instances; at n = 8 there are 1357 and 399. The step succeeds in every one (`tools/two_even.py residual 8`).

## E14. The missing move: path insertion (Fan game, continued)

Tool: `tools/fan_game.py`, with new options. Manuscript `manuscripts/missing-move`, whose `scripts/` and `scripts/outputs/` hold copies of the solver, the drivers and every log.

| Option | Move added |
|---|---|
| `np` | **path insertion**: a path of length ≥ 2 made of held edges becomes one new path |
| `rotR` | at most R Pósa rotations: direct append, or the opponent picks W ⊆ N(u) of size b(v), we pick w, and the held edge uv becomes uw |
| `altR` | at most R uses of **Fan's alternative** (manuscript Lemma 4.2): the transfer, or ≥ Σ_T b blank neighbours of u can be activated |
| `hubs` | held sets restricted to "a full star plus k edges" (for n = 10) |

**Results at n = 8.**

| Test | Outcome |
|---|---|
| `np`, all 11,117 connected graphs, \|F\| ≤ 4 | 47 graphs with a losing root (base game: 50) |
| the 47, `np`, \|F\| raised from 5 | every root wins. Of the 40 sparser graphs (`stepper.sh`, all roots), 35 need \|F\| = 5 and 5 need 6. The 7 dense graphs (complements of ≤ 6 edges) were run one root per automorphism orbit (`orbit_run.py`): Gut~vs needs 6; Gut~~w, Gu^v~w, Guv]}{ and Guv]z{ need 7; Guv]~{ needs 8 (root 2); **K8 − perfect matching (Gr~v~w) needs 9**. Every held set of size 8 loses there; the star plus three edges wins, with a new path of length 4 through the hub |
| the five §R losers, `np` | win; every certificate found is hub-shaped (`outputs/certificates.txt`) |
| the five losers, `rot2` \|F\| ≤ 4; `alt2` \|F\| ≤ 4; `alt1` \|F\| ≤ 6 | **no losing root repaired** (GsRvnk 2, 3; GsZvnk 4; Gqrvn[ 2; Gqzvn[ 4; Gqzl\|{ 1) |
| (R) by CP-SAT on the five losers | holds at every root |

So **the Fan game with path insertion wins every root of every connected graph of order 8** (connections §S).

*Correction to E13.* K8 − perfect matching loses with path insertion at every \|F\| ≤ 8, so it also loses the original game there. The E13 list of five genuine losers at \|F\| ≤ 8 is therefore incomplete: K8 − PM is a sixth. With path insertion it wins at \|F\| = 9. The certificate for GsRvnk, root 2, is the following:
- hold the star at 2;
- take Lovász on G − 2 (3 paths, one spare);
- single transfer 0 → 2;
- grouped transfer {5, 6} → 2;
- new path y′–2–7.

Theorem `hub_four_ends` (Lean) is the general form.

**Results at n = 10** (`scripts/families.py`; F = a full star plus k ≤ 2 edges, `np hubs`):

| Graph | Description | Outcome |
| A_{4,4} | K4 core, full vertex with a leaf, four false twins | wins at k = 2 |
| A_{6,2} | K6 core, full vertex with a leaf, two false twins (the degree-6 analogue of GsRvnk) | **loses at every root with k ≤ 3** (k = 3: one root per orbit; the odd root x loses, so no play wins) |
| B | K6 core, two adjacent full vertices, two half-contact vertices | wins at k = 1 |
| B′ | K6 core, a full vertex with a leaf, two adjacent full vertices (Q2 type) | loses at every root with k ≤ 2; **wins at every root with k = 3** (star at x1 + a core triangle; new path 0–2–1–x1–5) |

(R) holds at every root of all four (CP-SAT).

**A_{6,2} by hand** (manuscript Prop 5.2). The hub s has degree 6. After three adversarial receipts, b(s) = 3 = d_H(s), and the 4th receipt is at Fan's equality. If it failed:
- every path ending in T would join T to s (append-or-through);
- the fourth Lovász path would be the leaf edge ℓx;
- 30 edges would then have to fit in three paths of ≤ 8 edges, which is impossible.

So the receipt succeeds and (R) holds at the twins. On B′ the same count is tight (31 = 3·8 + 7) and does not decide.

**K8 − perfect matching by hand** (manuscript Prop 5.5). Here the 4th receipt at the degree-6 hub always fails, because all three paths end at the hub. The rigid configuration is a flower of three Hamiltonian cycles through s, and a transversal path of cut edges closes it (Lemma 5.4).

**Follow-up (cloud session missing-move, after the coordinator's notes).**

Criticality (`scripts/crit.py`, CP-SAT):
- The five E13 losers are non-critical (p = 3). The split rule Σb ≤ n − 2, now in `fan_game.py`, settles them trivially.
- Of the 47 graphs that lose with `np` at \|F\| ≤ 4, **19 are critical**: Gqz~vw, the seven dense graphs, and 11 others. All 47 win with `np` (\|F\| ≤ 9).
- A_{6,2} and B′ are critical; A_{4,4} and B are not.

**Gqz~vw** (critical, 4-connected; the original game loses it at root 3) is won by the odd-neighbour hub (manuscript Thm 2.5, Cor 2.6):
- held set F = star(3) + 06, with the Lovász seed;
- single transfer 1 → 3;
- grouped transfer {5, 7} → 3;
- new path 0–6–3–7 (or 0–6–3–5).

The final profile is simple: it realises {0, 3, 7} or {0, 3, 5}. The Lean version is `gqz_rooted_three`, checked by `decide`.

**The flower move** (option `flower`; manuscript Lemmas 5.6–5.7). At a saturated hub with b(u) = d_H(u) = j = |T| ≤ 4, b = 1 on T, Σb = 2j and |E(H)| + j = j·|V′|, the paths close into j Hamiltonian cycles. A transversal path L from u, chosen by the opponent, gives j + 1 paths with b = 2 on L.

| Test | Without flower | With flower |
|---|---|---|
| CP(4), F = one star (\|F\| = 6), all roots | loses (`np` needs \|F\| = 9) | **wins** |
| CP(5) = K10 − PM, F = one star (\|F\| = 8) | loses (with `np` too) | **wins** |
| A_{6,2}, B′ (star + ≤ 1) | loses | loses |
| the 7 dense n = 8 graphs, `np`, \|F\| ≤ 6 | 5 lose | 5 still lose (CP(4) and Gut~vs win) |
| 5 random critical n = 10 graphs with a degree-6 vertex (`sample10.py`) | win at star + ≤ 2 | win at the same size |

The flower's last step is the insertion of the path L, which has m − 1 held edges. This attains `cocktail_insertion_barrier` (FanBarrier.lean).

**Receipt or flower with a count** (option `rf`, manuscript Lemma 5.9, after endpoint-structure Thm 67), and the **orbit rule** (option `orbit`: an end anywhere in the root's automorphism orbit wins).

*Correction:* A_{6,2} is closed at **every** root by hand. In Prop 5.2 two core vertices end with two ends each, and Sym(Q) acts by automorphisms. The earlier "core roots open" was wrong; the emc-four session pointed this out. B′ is closed by hand in endpoint-structure Prop 68.

| Test (F = one star, `np rf`) | Without `orbit` | With `orbit` |
|---|---|---|
| A_{6,2} | wins except at the core roots | **wins every root** |
| B′ | wins except at the core roots | **wins every root** |
| CP(4), CP(5) | wins every root | wins every root |

On the core roots without `orbit`: the opponent can make the root a donor, and the hand proofs also use symmetry.

**Sample** (`rf_sample.sh`): ten random critical n = 10 graphs with a degree-6 vertex, held sets = a star plus k ≤ 2 edges, `np orbit` with and without `rf`.
- Nine win, at k = 1 or 2, and `rf` changes nothing.
- **First miss: Inv~|~zbw**, i.e. K10 − {02, 17, 19, 24, 29, 39, 58}: 6-connected, 8 even vertices, critical. It loses at roots 2 and 3 with or without `rf`; (R) holds by CP-SAT.
- At root 2 (a degree-6 hub with two odd neighbours), holding star(2) + 10 + 64 gives a Lovász seed. At the 4th receipt the count is |E(H)| = 33 < 3·9 + 8 = 35, so neither case of Lemma 5.9 is decided.
- With a star plus 3 held edges (F = star(2) + 01, 34, 36, so \|F\| = 9) Inv~|~zbw **wins** at roots 2 and 3, with or without `rf`. The play: a relay 0 → 1 → 2, receipts at 2, a second hub at 3, and a new path through both hubs (4–3–6–2–8). The miss is a held-set-size artefact (`outputs/certificate_miss1.txt`).



**Reading.**
- At n = 8 the incompleteness of E13 was budget allocation: Lovász's spare path could only buy a one-edge path.
- Pósa moves at the profile level add nothing at n = 8. The rotation adversary and Fan's alternative both lose the memory that one of the paths ending at the hub is the fresh path cs.
- Degree-six hubs: with a pure star they are one receipt short at Fan's equality. By hand the gap closes by an edge count (A_{6,2} twins) or a flower (K8 − PM); the count is tight on B′.
- The game bypasses the deficit with more held edges and a longer inserted path through the hub: K8 − PM at \|F\| = 9, and B′ with a star plus 3.
- The resistant case we know of is A_{6,2}, which loses at every root with a star plus ≤ 3 held edges. Prop 5.2 closes its twins and odd roots by hand with the pure star: a sound count at Fan's equality would let the game do the same. Its core roots are covered by neither. General held sets at n = 10 are out of the solver's reach.
- Inductive seeds have Σb = n and no spare path, so `np` does not change the `ind` variant.

**E14 addendum (independent).** `fan_game.py Gr~v~w 8 np`: K8 − perfect matching = K_{2,2,2,2} **loses at every root with path insertion and \|F\| ≤ 8** (23 CPU-min). This is consistent with the Lean barrier theorem `cocktail_fan_barrier`, which says that no last step by a Fan transfer or a one-edge path can work. The game also finds no path-insertion finish within \|F\| ≤ 8. The rooted test for K_{2,2,2,2} is settled only by the flower recombination (missing-move Prop 5.5).
**E14 addendum 3 (missing-move, hub-strategy conjecture; manuscript §6, Prop 6.8).** Game: `np rf orbit hubs`. Roots: even y with ≥ 3 even neighbours and no bridge yt with d(t) ≥ 2 (the root hypotheses of BranchBase3), one per automorphism orbit. X = held edges besides the star. lb(y) = ⌊e(y)/2⌋, where e(y) counts the non-leaf odd neighbours of y and the even vertices outside N[y] (parity lower bound for |X| when the star is at y). Scripts are in `manuscripts/missing-move/scripts/`, outputs in `outputs/`.
- **n = 8**, all 11117 connected graphs (`data/conn8.g6`), 9268 root orbits.
  - Star at y (`hubroot`), least \|X\| = 0/1/2/3 for 3100/5375/787/6 root orbits, identical with the simple target (`hs8_R_root.log`, `hs8_simple_root.log`).
  - lb ≤ 1 always. \|X\| − lb = 0/1/2 for 8475/783/10 (`hs8_root_parity.txt`), so the conjecture holds at n = 8 with c = 2.
  - Star at any vertex: 0/1/2 for 7000/2256/12 (R target) and 6997/2259/12 (simple) (`hs8_R.log`, `hs8_simple.log`).
  - Shapes of one winning X (lexicographic first; `hs8_root_shapes.txt`).
    - \|X\| = 1: relay O–n 2468, n–n 1495, O–O 1332, other 80.
    - \|X\| = 2: 757 paths (611 through an even neighbour of y) and 30 matchings.
    - \|X\| = 3: 4 paths, 2 triangles.
- **Proved theorems alone at n = 8** (`relay_cover.py`). The relay-hub Theorem 6.4 covers 2556 root orbits, the two-hub Corollary 6.6 covers 379, and one of them covers 2757 of the 9268. Each replays as a game win with the theorem's own held set (`relay_cover8.txt`).
- **n = 10**: the 10 graphs of Prop 5.10 plus 40 new critical graphs (`sample10.py 23 40`, `sample10_50.g6`). 30 of them have a root, 108 root orbits in all, lb = 0/1/2 for 2/39/67.
  - Star at y (KMAX 4, R target): least \|X\| = 0/1/2/3/4 for 1/35/68/3/1 (`hs10_R_root.log`).
  - \|X\| − lb = 0/1/2/3 for 102/3/1/2. **lb + 3 is needed** at Inv~|~zbw root 7 (d = 8, lb 0, \|X\| 3) and root 9 (d = 6, lb 1, \|X\| 4). So the c = 2 form of the conjecture is **false** (`hs10_root_parity.txt`).
  - Simple target: the same, except Inv~|~zbw root 2 needs 4 instead of 3 (`hs10_simple_root.log`).
  - Star anywhere: 0/1/2/3 for 3/93/10/2, both targets (`hs10_R.log`, `hs10_simple.log`).
  - The proved theorems cover **0 of 108** (`relay_cover10.txt`). For the relay theorem, 99 root orbits have no partners z_i, 4 fail (iii) and 5 fail (ii). Only 3 roots have d = 4 (`relay_cover10_reasons.txt`).
  - 54 of the 57 degree-8 root orbits win with \|X\| = lb ≤ 2, below the 3 relays Theorem 6.4 would need, so the game wins there by moves outside the receipts-only lemmas.

## E15. Oracle seeds, the last-edge barrier, and EMC at n = 8 (cloud session `claude/emc-four-even`, route (H))

Tools:
- `tools/realis.c` with its front end `tools/realis.py`: an exact realisability oracle. It runs a depth-first search for the paths one at a time, with necessary-condition pruning and memoised failures. A whole realisable family at n = 8 takes milliseconds.
- `tools/fan_oracle.py`: the Fan game of E13 with **oracle seeds**. The seed on G − F (F ≠ ∅) is any realisable simple profile, or with `+gen` any realisable end profile.
- `tools/emc_sweep.py`: EMC, plus the transfer test at branching vertices.

Cross-check: the oracle agrees with the CP-SAT oracle (`faithful_descent.make_oracle`) on the full realisable families of 60 random graphs at n = 6 and 35 random graphs at n = 8 (9–18 edges). There were no mismatches. The ILP is too slow on the densest graphs, so they were not cross-checked.

**EMC at n = 8 (complete).**
- All 1,082 connected critical graphs satisfy EMC: the minimal realisable sets all have size e/2, satisfy basis exchange and are loopless.
- 1,030 of them are uniform, including **every 3-connected one** (476).
- The 52 non-uniform graphs:
  - κ = 1: 46;
  - κ = 2: 6 (GsaFC{, GsaFeW, GsbFEo, GsbFeW, GsbfMo, GsPI^{), all with e = 6.
- n ≤ 6 reproduces E6: 3 + 34 critical graphs.

**Transfer test at branching vertices** (Lemma 51 of endpoint-structure). For critical G at n = 8:

| m = \|N_E(y)\| | instances | no a with N_E(y) − a ⊆ S_K, \|S_K\| ≤ e/2 − 1 in G − ya |
|---|---|---|
| 2 | 964 | 0 |
| 3 | 656 | 403 |
| 4 | 215 | 209 |
| ≥ 5 | 154 | 154 |

- Restricted to e = 6 and m = 3: 22 of 275 instances fail.
- With m = 2 and a non-bridge even edge, all 13,360 (n = 8) and 92 (n = 6) instances pass with the root b prescribed (Cor 52, `branchBase_of_three`).

**Oracle game** (even roots).

| n | seeds | \|F\| | graphs with a losing root |
|---|---|---|---|
| 4 | simple | 1 | 0 |
| 6 | simple | 1 | 1 (K_{2,2,2}, all roots) |
| 6 | simple | ≤ 2 | 0 |
| 6 | general | 1 | 0 |
| 8 | simple | 1 | 6 (Gqzn^[, Gq~v~w, Gr~v~w, Gr~v~{, Gut~~w, Gu^~v{) |
| 8 | simple | ≤ 2, ≤ 3 | 3 (Gqzn^[ root 1; Gr~v~w all roots; Gut~~w roots 1, 3, 4) |
| 8 | general | 1 | **1: Gr~v~w = K8 − perfect matching** |
| Gr~v~w | simple, orbit-reduced | ≤ 4 | loses |
| Gr~v~w | general, orbit-reduced | ≤ 3 | loses |

Gqz~vw at root 3 wins with |F| = 1 in two ways:
- F = {01}: seed {3} in the non-critical G − 01 (3 paths), then a new path 01;
- F = {31}: seed {5, 7}, then a single transfer, which gives {3, 5, 7}.

**Explanation of the Gr~v~w loss (proved, Lean `cocktail_fan_barrier`, `cocktail_insertion_barrier`).**
- Take CP(m) = K_{2m} − PM with m ≥ 4, and let D be any partition of CP(m) − ut.
- If Fan's condition for ut towards u holds, then 3|D| ≥ 4m − 3, so |D| > m.
- A new path made of the held edges F, added to a partition into ≤ m − 1 paths, needs |F| ≥ m − 1.
- So no oracle play with one-edge new paths can win, for any F.

**Reading.**
- The strongest hypothesis on end profiles of G − e, played through Fan's moves on e, certifies (R) at every even root of every connected graph with n ≤ 8, except K8 − PM.
- K8 − PM is critical with uniform endpoint matroid U_{4,8}, so the failure lies in the moves.
- Its only possible finish is a ≥ 3-edge spare path into a 3-path partition, i.e. three Hamiltonian paths. That is the flower of missing-move Prop 5.5.

**E14 addendum 2 (independent).** `one_root.py Gr~v~w 0 9` (path insertion, \|F\| ≤ 9): **WIN** at root 0, and hence at every root by vertex-transitivity. F is the full star at 0 together with {13, 14, 24}. The Lovász seed is b = (0,1,0,1,1,1,1,1). Together with Guv]}{ (root 0, \|F\| = 7; checked independently above), this confirms the missing-move session's claim: **the extended game (Lovász + Fan + path insertion) wins every root of every connected graph of order 8 with \|F\| ≤ 9.** The flower lemma (Prop 5.5) gives a shorter proof for K8 − PM, but at n = 8 it is not needed.
## E14. Prescribed ends at odd order; five even vertices with one universal vertex (cloud session `claude/bs-prescribed`)

Scripts: `manuscripts/bs-prescribed/scripts/`.

**Prescribed-end lemma** (odd N, Δ(EV) ≤ 3, even y, partition into (N−1)/2 paths with an end at y). Exact with `exact_prescribed.py` (CP-SAT); game with `odd_fan_game.py` (Lovász seeds, plus Lemma 3 seeds at any order, plus Fan transfers; at most 4 held edges).

| N | e | pairs (G, y) | no floor partition ending at y | lost by the game |
|---|---|---|---|---|
| 5 | 1 | 7 | 7 (forced by counting) | 7 |
| 5 | 3 | 30 | 9 (5 SET) | 14 |
| 5 | 5 | 5 | 0 | 0 |
| 7 | 1 | 130 | 130 | 130 |
| 7 | 3 | 1236 | 101 (29 SET) | 230 |
| 7 | 5 | 845 | **6** | 64 (63 still lost with ≤ 8 held edges) |
| 7 | 7 | 7 | 0 | 0 |

- The six e = 5 failures at N = 7:
  - FqHPO = G_{1,1} and FsQc_ = G_{2,0} (the forcing family);
  - FsQaO and FsPL_ (pendant triangle, or K4 − e, at y plus a pendant triangle elsewhere);
  - Fs`Do and FqilW (y between a leaf and a K_{1,1,3} or a K5).
- **Random N = 9** (`sample_prescribed.py 9 150 3 1`, exact by `tools/pathnum2.py`): 596 pairs.
  - Genuine exceptions: 6 with e = 1 and 3 with e = 3; none with e ≥ 5.
  - Game search failures: 1 with e = 3, 7 with e = 5, 2 with e = 7.
- **Conclusion.**
  - The lemma is false, with exceptions built from forcing gadgets (manuscript Prop. 5).
  - The odd-order prescribed game is far from complete. This contrasts with even order: E13 found that Δ(EV) ≤ 3 makes every root winnable at n = 8.

**Five even vertices, one universal vertex** (`certgen.py`, `verify_certs.py`, `sevensite_cert.py`):
- **Seven-site bank (A6) re-derived independently**: all 7 cores × 31 contact sets are certified, with held sets of 2–6 edges and depth ≤ 6.
- **Local certificates** (model = T only, no leaf): all cores except the bowtie M. The bowtie has none (exhaustive over held sets).
- **Bowtie with u only** (no v): 25 of 31 contact sets. The exceptions are A ⊇ {a, b} with A ∩ {c, d} ∈ {∅, {c, d}}, and symmetrically.
- **Labelled tables for Lean**: 38 local rims and 3 × 31 bowtie cases, all verified (46 and 129 leaves).

**End-to-end random hosts** (`random_hosts.py`, circuit solver):
- all 60 + 40 hosts with a leaf, of orders 9 and 11, over all one-universal cores;
- all 60 + 40 + 20 bowtie hosts without a leaf, of orders 9, 11 and 13.

Every host satisfies the floor bound. So the leaf is probably not needed for the bowtie either, but the local certificates need it.
## E16. Rainbow transversals of Hamiltonian decompositions (the flower move; cloud session `claude/emc-four-even`)

Tool: `tools/rainbow_transversal.py MMAX SAMPLES [seed]`.

**Question.** In CP(m), take a system of m − 1 edge-disjoint Hamiltonian cycles. Does every vertex s start (or at least lie on) a path with exactly one edge from each cycle? This is endpoint-structure Question 66; it is what the flower move of Theorem 63 needs.
- Proved for ≤ 4 cycles (Prop 64; Lean `rainbowTransversal_three`, `rainbowTransversal_four`), hence for CP(4) and CP(5).

**Run** (seed 7). Each m tests 60 random Hamiltonian decompositions and one Walecki-type decomposition, at every vertex, for a transversal *starting* at s (exhaustive search):

| m | failures | random greedy success |
|---|---|---|
| 4 | 0 | 100% |
| 5 | 0 | 94% |
| 6 | 0 | 91% |
| 7 | 0 | 89% |
| 8 | 0 | 87% |
| 9 | 0 | 86% |
| 10 | 0 | 85% |

Earlier scratch runs:
- The same question on K_{2k+1}, for k ≤ 6: no failures.
- One rotation always repaired a stuck greedy path, on all (k − 1)-paths through s in 6 random decompositions each at m = 5 (40 stuck paths) and m = 6 (478).

**Reading.** The transversal exists in every case tested, but greedy alone fails 6–15% of the time beyond m = 4. So a general proof needs rotations. The question is a rainbow-path problem: length k with colour degree k. Chen and Li conjectured length k − 1 for arbitrary colourings; here each colour class is a Hamiltonian cycle.

**Variants** (`tools/rainbow_variants.py twofactor|segment|warnsdorff MMAX SAMPLES`):
- `twofactor`: random 2-factorisations of CP(m) with short cycles. No vertex without a transversal starting there (m ≤ 8, 40 samples each).
- `warnsdorff`: deterministic greedy without backtracking. It fails 1/480, 5/540 and 8/600 times at m = 8, 9, 10.
- `segment`: segment transversals by a no-backtracking rule succeed in every case (m ≤ 11, 25 samples each). The same rule with unit segments fails up to 9/550.

## E17. The inductive template for EMM (track C4; cloud session missing-move)

Scripts: `tools/gemm_test.py` and `tools/emm_template.py`, with the exact oracle `tools/realis.c`. Logs are in `manuscripts/missing-move/scripts/outputs/` (`gemm*.log`, `tmpl*.log`) and are reproduced by `emm_runs.sh`. Manuscript: missing-move §7.

**Cut criterion for general profiles.** A profile is any b ≤ d with b ≡ d mod 2 and Σb = 2p. It is cut-feasible if (L) b ≤ d and d + b ≤ 2p hold, and (C), ED (1) with k replaced by p. We compare this with realisability.

| order, profiles | graphs | profiles | cut-feasible | not realisable |
|---|---|---|---|---|
| 4, all | 6 | 61 | 52 | 0 |
| 5, all | 21 | 894 | 767 | 0 |
| 6, all | 112 | 14,786 | 13,897 | 0 |
| 7, all | 853 | 481,442 | 467,373 | **1** (p = 2) |
| 8, p = 4 | 11,117 | 434,011 | 362,546 | 0 |
| 8, p ≤ 3 | 11,117 | 175,935 | 74,435 | **17** (14 with p = 2, 3 with p = 3) |
| 8, all p, 200 random graphs (seed 5) | 200 | 534,586 | 528,727 | 0 |

- No realisable profile is cut-infeasible.
- The n = 7 failure is FqJBo with b = (1,0,1,2,0,0,0). It is a 2-linkage obstruction, confirmed by brute force.
- So EMM does not extend to arbitrary profiles. All failures lie below the Gallai budget. This suggests **EMM⁺**: for connected G and p ≥ ⌈n/2⌉, cut-feasible ⇔ realisable.
- EMM⁺ holds:
  - for every profile at n ≤ 7;
  - for every profile with p = 4 at n = 8;
  - on the n = 8 sample, at every p.
- At n = 8 the bound cannot be lowered to p = 3.

**Reductions (proved; missing-move Lemma 7.4).** A minimal counterexample to EMM⁺:
- is connected;
- has no degree-2 vertex with b = 0 and non-adjacent neighbours;
- has no leaf at an unsaturated neighbour (Lean `cutOK_leaf`, `ach_of_leaf`, `leaf_step`);
- has no degree-2 vertex with two ends lying on a cycle, unless each of its neighbours is saturated or both neighbours have b = 0.

Before the proof, the last reduction was checked to keep cut-feasibility on all 9,537 instances at n ≤ 6 (`tools/emm_reduction_check.py`, `reduction_d_check.log`).

**Template** (stuck = no edge with a valid move; a valid move has a cut-feasible, in-class b′ and a profile-level guarantee):

| instances, moves | n = 4 | n = 5 | n = 6 |
|---|---|---|---|
| all; NP, T, C | 2/52 | 15/767 | 56/13,897 |
| reduced; NP, T, C | 0/35 | 9/600 | 12/10,866 |
| reduced; with path insertion of length ≤ 3 | – | 0/600 | 4/10,866 |
| EMM⁺ class, reduced; NP, T, C | 0/35 | 4/589 | 14/10,847 |
| EMM⁺ class, reduced; with path insertion of length ≤ 5 | 0/35 | 2/589 | 6/10,847 (all with p = ⌈n/2⌉) |

- Every stuck instance at n = 6 has a cut-feasible move that lacks only its guarantee: a transfer at Fan's equality, or a concatenation with one end at each of u and v (`tmpl6_red_diag.log`, `tmpl6_plus_diag.log`).
- Reading: single-edge and bounded path-insertion moves do not make cut-feasibility inductive. The missing ingredient is an **equality lemma**: at Fan's equality, either the move succeeds or a tight cut appears.


## E18. Cut selection, pairing selection and caps (tracks C1/C2; cloud session `claude/emc-four-even`)

Scripts are in `manuscripts/endpoint-min-max/scripts/`; tools are `tools/cutfeas.c` (all cut-feasible half-sets) and `tools/capsub.c` (caps).

- **EMM** (`evidence.py`). 0 failures and 0 unsound throughout:
  - n = 6: 99 graphs, 518 half-sets;
  - n = 8: 10,893 graphs, 101,714 half-sets, 2,100 non-realisable;
  - n = 10, G(10,p) with seed 20261127: 250 graphs, 4,222 half-sets, 8 non-realisable;
  - bottleneck families of order 6–10: 82 graphs, 1,568 half-sets, 208 non-realisable.
- **CS and PS** (`cut_selection.py`). There is no failure at n ≤ 8, in the n = 10 sample or in the bottleneck families.
  - PS (a pairing of Ev all of whose transversals are cut-feasible) always holds.
  - A good pairing made of edges of G exists in 6,773 of 10,893 graphs at n = 8.
  - At n = 6 the script also confirms the arm form and the pairing criterion against enumeration.
- **Certificates** (`certificates.py`) for the guarded route lemma:
  - n = 8: 9,848 by a Hamiltonian path, 996 by a linkage, 49 by guarded routes, 0 uncertified;
  - n = 6: 82 / 16 / 1;
  - n = 10 random: 236 / 14;
  - bottleneck: 69 / 13;
  - also all trees of order ≤ 12 (guards are needed for 1, 8 and 62 trees at orders 8, 10, 12), 300 sparse G(n,p) at each of n = 10, 12, and K_{2,m} for m = 6, 8, 10.
  - Every certified pairing is good by enumeration.
  - Stress test (`certificates.py stress`): random route systems in 400 random graphs (n = 8, 10). All 3,310 guarded systems with a busy vertex and all 1,691 linkages are good. 7,079 of the 7,227 unguarded systems are also good, so the guards are far from necessary.
- **Caps** (`caps.py`).
  - Every per-vertex family F_v is a matroid basis family (n = 6, 8).
  - The global cap is non-submodular in 1,063 graphs at n = 8, and the cap system is a non-matroid in 70.
  - F is not a matroid basis family in 48 graphs at n = 8 (all non-critical, e.g. GsaAD{) and in 1 at n = 6.
  - Critical graphs at n = 8: all 1,082 have matroid F. F = F_v for one v in 1,071; the cap is submodular in 1,057; 4 are explained by neither.

**E18 addendum: the cut-selection construction** (`construction.py`). Each check uses a random spanning tree, takes its T-join and chooses the transitions by T-join pairings in F^v; the resulting pairing is then checked against the enumeration.
- Coverage:
  - all 99 graphs at n = 6 and all 10,893 at n = 8, with 3 trees each (32,679 constructions at n = 8);
  - the n = 10 sample (750 constructions);
  - the bottleneck families (246);
  - all trees of order 8, 10, 12 (657);
  - 150 random G(12, p) graphs (300).
- **0 failures**, which agrees with Thm 21.
- Also measured:
  - the number of per-vertex families F_v needed to cut out F at n = 8 is 1 in 10,798 graphs, 2 in 75, and 3, 4, 5, 6 in 11, 5, 3, 1;
  - the union of the transversal families of good pairings equals the complement-closed part of F in all but 2 graphs at n ≤ 8.
