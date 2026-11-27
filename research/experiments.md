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

**Reductions (proved; missing-move Lemma 7.8).** A minimal counterexample to EMM⁺:
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
| reduced; with path insertion of length ≤ 3 | 0/35 | 0/600 | 4/10,866 |
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

**E17 addendum: EMM is false (counterexamples of order 12).** Manuscript: missing-move Example 7.4, Theorem 7.5 and Remark 7.6.
- **Padding (EMM⁺ false).** In FqJBo, vertex 3 is saturated (b = d). Attach t leaves to 3 and raise b(3) by t; each new edge is then a forced one-edge path.
  - t = 3 gives `IqJBo_OC?`: n = 10, p = 5 = n/2, b = (1,0,1,5,0,0,0,1,1,1).
  - t = 4 gives n = 11, p = 6 = ⌈n/2⌉.
  - Both are cut-feasible, by `gemm_test.feasible` and by `cut_test.cut_ok`, and not realisable, by `realis.c` and by a brute-force enumeration.
- **Gluing (EMM false).**
  - Construction: a core that is a below-budget failure with a leaf is glued to a realisable gadget with a leaf, identifying the two leaves. The glued vertex c has degree 2 and b = 2, so no path crosses it. The gadget's surplus of ends makes the profile a simple half-set, and the cut slacks grow.
  - `tools/emm_glue_search.py` uses the cores GsOeBW (b = 0,0,1,1,2,0,0,0) and GqGUDg (b = 0,1,1,1,1,0,0,0) from the n = 8 failure list, with all gadgets of order 5. It gives 14 glued instances, all cut-feasible and not realisable: 12 distinct graphs of order 12.
  - **`tools/cut_test.py` (the EMM test of the synthesis) on them: "tested 12 graphs, 1932 half-sets (269 non-realisable): 12 EMM failures, 0 unsound"** (`emm_counterexamples12_cut_test.log`).
  - Example: KsOeBW??G`?A, edges 01,02,03,06,14,16,17,25,27,47,57,3-10,10-8,8-9,9-11, M = {3,4,8,9,10}. It is confirmed non-realisable by an independent brute force, which agrees with the oracle on 40 realisable half-sets of the same graph.
- **No failure in a targeted search of simple lifts.** FqJBo plus three vertices attached to the terminals 0, 2, 3 (199 graphs, 10,327 cut-feasible half-sets) gives no failure (`emm_lift_search.log`).
- **Splitting off** (the coordinator's Lovász–Cherkassky pointer; `tools/emm_split.py`).
  - Cut side: every degree-4 vertex with b = 0 in the 14 stuck EMM⁺ instances at n = 6 has a cut-preserving split, 39 in all. But 26/35 (n = 4) and 267/589 (n = 5) reduced instances have no split at all.
  - Lift side: in 10 of the 14 instances some split lifts for every partition (`split_lift6.log`).
- **Template variants** (Prop 7.9):
  - guarded splits give 0/35, 1/589, 4/10,847;
  - with path insertion as well: 0, 0, 4;
  - in the simple class (b ≤ 2): 0/6, 14/68, 38/456, or 0, 10, 28 with splits and path insertion.

**E17 addendum 2: EMM₃** (minimum degree ≥ 3; the coordinator's corrected target; missing-move Remark 7.7).
- Mechanism: a bridge, or any edge cut δ(K), decouples like a saturated degree-2 vertex does. A partition of G restricts to K plus one pendant leaf per cut edge, with one end at each leaf. So an EMM₃ counterexample by gluing needs a **core**: pendant leaves, all other degrees ≥ 3, and a simple profile that is cut-feasible but not realisable.
- Cores:
  - exhaustive up to order 8 (`tools/emm3_core_search.py`, `emm3_cores.log`, `emm3_cores_one.log`): 1,146 graphs with this degree pattern, 11,832 cut-feasible simple profiles, **0 cores**;
  - random (`tools/emm3_random.py cores`): order 9, 2,000 graphs, 41,295 cut-feasible profiles; order 10, 2,000 graphs, 52,482. **0 cores.**
- EMM₃ directly (`tools/emm3_random.py emm3`):
  - order 10: 3,000 random connected graphs, δ ≥ 3, m ∈ [15, 30], 48,784 half-sets, **0 failures**;
  - order 12: 300 graphs, m ∈ [18, 30], 8,396 half-sets, **0 failures**.
  - Every sampled half-set was cut-feasible, so these runs test realisability, not the sharpness of (1).
- Toughness-type Hamiltonicity obstructions are cut-detected. At slack 0, (C) for the complements of the components of G − S gives #components ≤ |S| + 1.
- **Cores at vertex 2-separators** (`tools/emm3_sep_core.py`, `emm3_sep_core.log`). A core here has no end-record at the terminals that is realisable, though some record is cut-feasible. 8,774 graphs up to order 8, 101,524 terminal pairs, 976,339 profiles: **0 cores**.
- **Binding test** (`tools/emm3_binding.py`, `emm3_binding.log`). 47 structured δ ≥ 3 graphs with n ≤ 12, 1,063 half-sets.
  - **8 cut-infeasible**, all in K5+K5 with 3 or 4 concentrated joins.
  - 1,055 cut-feasible, all realisable: **0 failures**.
  - Weakly discriminating: at n ≤ 12 the cones over two cycles never bind.

**E18 addendum 2: the Kotzig reduction** (`manuscripts/endpoint-min-max/scripts/kotzig.py`). The script builds G(H) for each test graph H. It checks cut-feasibility of the gadget by max-flow (Lemma 1(d)), cross-checks by brute force where n ≤ 10, and checks the following.
- λ(L(H)) ≥ 4 ⟺ H is bridgeless ⟺ the gadget is cut-feasible (Lemma 23, Prop 24).
- Hamiltonian decomposability of L(H) ⟺ H is Hamiltonian (Kotzig; searched where |V(L(H))| ≤ 24).
- Realisability by the oracle where n ≤ 16 (Prop 25).

Test graphs: K4, the prism, K33, the cube, Petersen, six random cubic graphs of orders 8–18, and a cubic graph with a bridge. All are consistent. Petersen gives cut-feasible but not realisable, and the bridged graph is not cut-feasible.

## E19. Forcing gadgets: EMM₃ and every connectivity class (cloud session `claude/emm3-gadgets`)

Manuscript: endpoint-min-max §6 ("Minimum degree three and beyond: forcing gadgets"; Lemmas 29–40, Thms 41, 42, 45). Logs are in `manuscripts/endpoint-min-max/scripts/outputs/`.

**Forcing gadget.** A two-leaf gadget is a graph X with leaves ℓ₁ at x₁ and ℓ₂ at x₂, all other degrees ≥ 3, and a simple profile. It is *forcing* if X⁺ is realisable and every realisation has a path ℓ₁…ℓ₂. Equivalently, for x₁ ≠ x₂: X + w (w joined to x₁, x₂, b(w) = 2) is not realisable.
- `tools/gadget.c` runs the exact search of realis.c on X⁺. Inputs: every connected X (geng -c -d1), every port pair x₁ ≤ x₂ (x₁ = x₂ allowed), every simple profile. It computes tot (realisable) and sep (a realisation whose ℓ₁-path does not end at ℓ₂). A gadget has tot ∧ ¬sep.
- **No forcing gadget with |X| ≤ 9** (`gadget_search_le9.log`):
  - |X| = 8: 113,914 port pairs, 2,415,862 profiles;
  - |X| = 9: 4,425,119 port pairs, 145,724,764 profiles (4 shards).
- **Sanity check.** With min degree 2 allowed, the search finds the trivial gadgets (b(X) = 0, X a path): DQo, ECZ?, and others.

**Hamiltonian regime** (manuscript Lemma 33). If d + b = 2r on X, every realisation of X⁺ is r Hamiltonian paths of X. Closing them through w gives a Hamiltonian decomposition of the 2r-regular graph X + w. A forced pair is then a forced transition at w.
- `tools/hamdec.c` checks 4-regular graphs for a vertex with a single transition over all Hamiltonian decompositions (`hamdec_4reg_le12.log`). Forced vertices exist:
  - none up to order 10;
  - **2 graphs of order 11**, `JCQTbQsZAU?` (= D₂ + w, 16 decompositions) and `JCQTbQsYaY?`;
  - 10 graphs of order 12.
- **Structure of D₂.** It consists of two K₄ blocks A, B and vertices p, q, with edges pa₁, pa₂, pb₁, qa₃, qb₂, qb₃ and ports p, b₀ (a₀ and q odd, b = 1). Contracting the blocks gives M₂: the 4-cycle with side multiplicities 1, 2, 1, 2, plus w. M₂ has a unique Hamiltonian decomposition.
- **Generalisation.** M_r is C_{2r} with side multiplicities alternating r−1 and r, plus w. Its unique decomposition pairs c_{2j} with c_{2j+1}. Blowing up into K_{2r} blocks gives the gadgets D_r. In a half blow-up only the odd c_i are blown up (|D_r| = 2r² + r); in a full blow-up all of them are (4r²).

**Counterexamples** (cut-feasible, not realisable; non-realisability is the gluing argument, Lemma 31):

| graph | n | δ | λ | κ | check |
|---|---|---|---|---|---|
| G₁₈ = D₂ + K₄,₄ + {sp, sb₀} | 18 | 3 | 2 | – | gemm_test, cut_test, cutfeas.c (12,609 cut-feasible half-sets in all), max-flow; realis_wide.c: not realisable (75 s) |
| G₂ half | 20 | 4 | 4 | 3 | gemm_test, cut_test, max-flow; forcing by realis.c |
| G₂ full | 32 | 4 | 4 | 3 | max-flow |
| G₃ half | 42 | 6 | 6 | 3 | max-flow |
| G₃ full | 72 | 6 | 6 | 5 | max-flow |
| G′(Petersen) | 28 | 4 | 4 | – | max-flow; L(P) has no Hamiltonian decomposition |

Scripts: `emm3_counterexample.py` (G₁₈; it also checks that the outer side K₄,₄ + 2 leaves is realisable, so the obstruction is the pairing), `emm_connectivity.py` (G_r, both blow-ups, r = 2, 3), and `kotzig_even.py`.

**`kotzig_even.py` (Thm 45, hardness at even degrees ≥ 4).** G′(H) is L(H) − w* plus a marked clique S on N = |E(H)| − 1 vertices, joined to u₁…u₄. The script checks:
- the prism, K₃,₃, the cube, Petersen, 5 random cubic graphs of orders 8–16, and a bridged cubic graph;
- the degrees, λ = 4 and cut-feasibility by max-flow (and that the bridged graph is not cut-feasible);
- for the Hamiltonian graphs, an explicit realisation from a Hamiltonian decomposition of L(H) and the clique lemma, which is verified for 6 ≤ N ≤ 29;
- realis.c at n = 16 (the prism and K₃,₃).

All checks agree.

**`tools/realis_wide.c`.** This is realis.c with 2-bit profile packing, valid because simple profiles keep b ≤ 2 throughout the search. It handles n ≤ 30 and m ≤ 64, and agrees with realis.c on 2,470 random simple-profile queries (`realis_wide_G18.log`). G₂ (n = 20, dense S) did not finish within 600 s.

**TRC (synthesis §15).** None of these failing half-sets is a transversal of a Thm 21 pairing. They starve the gadget: all of D_r's even vertices are unmarked, so all N pairs would have to cross δ(D_r), which has only 2r edges, while the routes are edge-disjoint. A gadget attack on TRC would need a forcing gadget with about half its even vertices marked, i.e. near or above its budget. The exhaustive search found no gadget of any kind with |X| ≤ 9.
- `trc_probe.py` on G₁₈ (`trc_G18.log`) built 10 distinct Thm 21 pairings from 12 random spanning trees. In each, no pair crosses δ(D₂), so every transversal has 4 marks in D₂. **All 2,560 transversals are realisable** (tools/realis_wide.c).

**E19 addendum: the balance condition** (connections §T.result-4).
- **Balance lemma** (proved). If M is a transversal of a constructible pairing and U = Ev − M, then for every X ⊆ V,

  | |M ∩ X| − |U ∩ X| | ≤ #(pairs split by X) ≤ |δ_J(X)| ≤ |δ(X)|.

- On G₁₈: of the 12,609 cut-feasible half-sets, 10,136 are balanced (`scripts/balance.c`). **All 10,136 balanced ones are realisable** (`scripts/bemm_run.py` with `tools/realis_wide.c`, about 45 min on 4 threads; `outputs/bemm_G18.log`). The 2,473 unbalanced half-sets include M = V(K₄,₄), which is not realisable; the others were not tested.
- **Connectivity of G′(H)** (Thm 45). By networkx, κ = 4 and λ = 4 for the prism, K₃,₃, the cube and Petersen. So the hardness instances are 4-connected there, even where L(H) itself is only 3-connected (the prism). There is no general proof.

## E20. Route descent: TRC tests, the extension step, minimum T-joins and constrained Lovász decompositions (cloud session `claude/route-descent`)

Manuscript: `manuscripts/route-descent/route-descent.tex`. Scripts: `manuscripts/route-descent/scripts/` (`rd_lib.py`, `families.py`, `trc_test.py`, `stuck_analysis.py`, `exist_test.py`, `lovasz_matching.py`, `l1_search.py`, `validate_oracle.py`); logs in `scripts/outputs/`.

**Oracle `tools/route_ext.c`.** The search of `tools/realis.c` for n ≤ 32, m ≤ 128, with constrained queries:
- `P` (realisability), `X` (the path at c avoids a vertex set F), `C` (route-respecting: all routes appendable), `A` (per-end avoidance sets), `S` (no path contains both vertices of any listed pair), witness variants `W*`, and a randomised budgeted mode `B` (shuffled vertex order, node budget, answer 2 = unknown; an exhaustive finish within budget is definitive).
- Validation (`validate_oracle.py`): P agrees with realis.c on 325 random simple profiles (n ≤ 12); P, X, C, A, S agree with a brute force that enumerates *all* path partitions (m ≤ 10): 3,936 P, 27,066 X, 948 C, 912 A, 996 + 420 S queries. Every witness is re-checked by an independent partition checker.

**Constructions.** Random spanning-tree T-joins ("tree"), or random *minimum* T-joins ("min": min-weight perfect matching on Ev under a perturbed unit metric), and at every v a random edge-disjoint pairing of the odd vertices of F^v (greedy removal of random odd–odd paths, which always completes). Heredity (Obs. 2: J − R_p a forest T-join of Ev − {a,c}, F′ = F, the remaining links pair the odd vertices of every F′^v) is asserted for every route of every construction: no violation.

**(A) TRC.** No counterexample.

| family | T-join | constructions | transversals | not realisable |
|---|---|---|---|---|
| 12 order-12 EMM counterexamples | tree | 2,400 | 57,600 | 0 |
| same | min | 1,200 | 28,800 | 0 |
| G(10,p), p∈[.25,.7], 300 graphs | tree / min | 1,200 / 1,200 | 7,328 / 7,880 | 0 / 0 |
| G(10,p), p∈[.15,.35], 600 / 300 graphs | tree / min | 2,400 / 1,200 | 15,024 / 7,560 | 0 / 0 |
| G(12,p), p∈[.25,.7], 200 graphs | tree | 600 | 6,006 | 0 |
| G(12,p), p∈[.12,.3], 300 graphs | tree / min | 900 / 900 | 8,346 / 8,568 | 0 / 0 |
| G₁₈ (n = 18, δ = 3) | min | 20 | 1,280 (all route-respecting) | 0 |
| G₁₈ | tree | 6 | 144 (131 decided) | 0 |
| G_bad (n = 28, Petersen) | min | 4 | 128 sampled (all route-respecting) | 0 |
| G₂ half (n = 20) | min | 4 + 3 | 256 + 96 sampled: 37 + 64 route-respecting, the rest undecided within budget (6 of the second 96 undecided for plain realisability) | 0 |
| G′(prism), Kotzig even-degree graph (n = 16, degrees 4–8) | min / tree | 10 / 10 | 640 / 640 (all realisable; 419 / 553 route-respecting found) | 0 |
| G′(Petersen) (n = 28, m = 116) | min | 4 | 128 sampled: 115 realisable, 13 undecided | 0 |

Marks inside the gadgets are automatic: all transversals of Thm-21 pairings were tested (sampled where 2^{e/2} > 256).

**(B) The extension step** (for (G, P, M, p) with a ∈ M: does G − E(R_p) have a realisation of M − a whose path at c avoids V(R_p) − c? Equivalently: does G have a realisation of M with R_p as a terminal segment?).
- **Tree T-joins.** Order 12: 244,100 of 268,800 queries succeed, and every transversal has a good p. n = 10 sparse: 41,158 of 43,104 succeed; of the 1,946 failures, **1,851 are trivial** (N_{G′}(c) ⊆ V(R_p): c has degree 2 and the route passes through its other neighbour) and 95 are not. **Stuck** transversals (no p works): 66 of 15,024 at n = 10 sparse, 8 of 7,328 at n = 10, 2 of 8,346 at n = 12 sparse, 0 elsewhere. In every stuck instance every route is trivially obstructed, all have one or two routes, and **re-routing (another construction with the same pairing) fixes all of them** (`stuck_analysis.py`).
- **Minimum T-joins: the extension never fails.** Order 12: 134,400 / 134,400 queries; n = 10: 23,160 / 23,160; n = 10 sparse: 21,656 / 21,656; n = 12 sparse: 30,240 / 30,240; G₁₈: 975 / 975 decided. So *every* route admits the extension for *every* transversal.
- **Route-respecting realisations (RR):** a realisation of M in which *all* routes are terminal segments simultaneously, i.e. a Lovász decomposition of F = G − J along which every route can be appended at its unmarked end (oracle query C). Min T-joins: 1,276 / 1,276 (n = 10), all 1,280 transversals of G₁₈, all 128 sampled transversals of G_bad. Tree T-joins: G₁₈ 111 / 131.
- **Linking is needed** (`unlinked.py`). Minimum T-joins decomposed into routes by arbitrary transitions, with no linking condition: 4 of 1,834 transversals (n = 10) are not realisable. So conjecture RR must keep the Thm-21 linking hypothesis; minimality alone does not suffice.
- **RR\* is false.** One Lovász decomposition of F serving all transversals at once fails for min T-joins in 1 of 250 graphs (n = 10) and in 2 of the 12 order-12 graphs (tree: 55 / 250, 10 / 12). The realisation must depend on M.

**(C) Existential version** (tree T-joins, n = 10 sparse, 600 graphs × 3 constructions; `exist_test.py`). The universal one-step induction fails at 59 / 10,842 transversals; the existential one (choose the end to extend, r's pair forced) fails at **45 / 8,562 roots**. The freedom of the existential form does not rescue fixed routes; minimality of J does.

**Constrained Lovász decompositions** (the problem RR reduces to; F has all degrees odd, decompositions have one end at every vertex).
- **L1** (the path at c avoids a non-neighbour a): 70,978 pairs, n ≤ 10, **0 failures** (adjacent pairs: 13,639 / 70,914 fail, as they must). One even vertex a with no end (L1e): 4,516 pairs, 0 failures.
- **L∞** (the path at c lies inside N[c]): 19,040 / 19,040; random subsets of non-neighbours: 16,821 / 16,821. Simultaneous N[·]-confinement at several vertices is false (two vertices: 80 / 1,426 fail).
- **L_N** (single-edge routes: a matching of forbidden pairs (c_i, a_i), one orientation): 3,732 instances, n ≤ 14, up to 7 pairs, **0 failures** (135 undecided within budget).
- **Block trees** (`trc_test.py blocks 2 32 71/72`, RR=1; `outputs/trc_blocks_*.log`): 120 random block trees (blocks K4, K5, K5−e, C5, K33 joined along a tree by paths of length 1–3, plus up to two chords, n ≤ 20), 2 constructions each.
  - Minimum T-joins: **4,512 transversals, TRC 0 failures, RR 4,512 / 4,512**; extension 21,896 true, 16 undecided, **0 false**.
  - Tree T-joins: 4,052 transversals, TRC 0 failures; extension failed 115 times (**70 nontrivial**, 45 trivial; 230 undecided), and 1 transversal was stuck (no route extendable). So on block trees the tree-T-join failures are mostly nontrivial, unlike random graphs, while minimum T-joins still never fail.
- **G′(Petersen) rerun** (`TJOIN=min RR=only BUDGET=300000 FINAL=0`, seed 1): no better than the first run (the first construction left 5 transversals undecided, against 2 before; the search is randomised). Stopped. The status stays at 115 realisable and 13 undecided out of 128, with no counterexample.
- **L_N on regular Eulerian graphs** (`ln_regular.py`, `outputs/ln_regular{4,6}.log`): G random connected 2k-regular, N a random perfect matching, F = G − N (2k−1)-regular, random orientation. For 4-regular, n = 14–20: **400 instances, 0 failures, 0 undecided**. For 6-regular, n = 14–18: **200 instances, 0 failures, 0 undecided**.
- **L_N for perfect matchings** (`ln_perfect.py 2500 60000 8 20`, `outputs/ln_perfect.log`): F all-odd on n = 8–20 vertices, N a random perfect matching of non-edges of F, random orientation (so G = F + N is Eulerian with a perfect matching, and L_N asks for every orientation of N to be realisable with N-edges terminal). **2,489 instances: 2,332 decided, 0 failures**, 157 undecided (mostly n ≥ 16); 2,421 of the 2,489 have a pair at F-distance 2. So the asymmetric L_N survives at distance 2, where symmetric separation fails.
- **SEP** (no path contains both c and a): **proved for dist(c, a) ≥ 3** (manuscript Thm "separation"). It can fail at distance 2 when there is an even vertex: z adjacent to u₁, u₂, each u_i adjacent to z, c, a, plus a leaf at each of c, a (n = 7). There L1 still holds, and adding a leaf at z restores SEP.
- Counting: among all Lovász decompositions of 2,417 small graphs, the fraction with a ∉ Q_c is ≥ 0.217 (no half-and-half involution).
- **Separation at distance 2** (`sep2.py`): fails for 446 / 2,945 pairs in all-odd graphs and 961 / 2,438 with one even vertex (budget-undecided excluded). So separation is a distance-3 phenomenon; L1 at distance 2 is strictly weaker, and had no failure.
- **L1 is proved** (manuscript Theorem "L₁", Lean `lovasz_avoid_set` / `lovasz_avoid_nonadj`): attach a leaf ℓ at c, apply separation to (ℓ, a) at distance ≥ 3 in F + cℓ (c the only even vertex), delete ℓ. Sanity check (`l1_leaf_check.py 600 200000`): separating decompositions of F + cℓ found in 582 / 582 random distance-2 instances (n = 6–12).
- **L1 with an extra even vertex z is false** (`l1z_test.py`, `l1z_classify.py 1500 100000 5 11`). Smallest example: the path c z a. In 5,399 decided random pairs (n = 5–11) it failed 648 times. **Every** failure had dist(c, a) = 2, z ~ a and N(z) ⊆ N[c] ∪ N[a]; there were 0 failures with z ≁ a, and 0 when z has a neighbour outside N[c] ∪ N[a].
- **S1** (both a ∉ Q_c and c ∉ Q_a, one decomposition) at distance 2, all-odd (`l1z_test.py 600 200000 6 12 odd`): 998 decided, **0 failures**.
- **One-sided separation BALL** (`ball_test.py`): K with exactly one positive-even vertex, s odd; is Q_s ⊆ B_2(s) achievable? **1,984 instances (n = 7–11), 0 failures** (`outputs/ball_z.log`). The leaf case, all-odd F with Q_c ⊆ N[c] (`outputs/ball_leaf.log`): **5,026 decided vertices (n = 6–12), 0 failures**, 41 undecided. Larger orders (`ball_test.py 1500 200000 z 12 15`, `outputs/ball_z_big.log`): **1,211 instances, n = 13–15, 0 failures**.
- **Multi-leaf separation is false** (`mls_test.py trials budget k ny`). Attach leaves at k pairwise non-adjacent vertices C of an all-odd F, and ask for a Lovász decomposition of F + leaves with every path meeting X = leaves ∪ Y at most once, Y packed outside N[C].
  - k = 2, |Y| = 0: 0 / 249 failures, as L1 predicts.
  - k = 2, |Y| = 1: 2 / 221 fail. k = 2, |Y| = 2: 3 / 76 fail.
  - k = 3, |Y| = 0: fails on the star K_{1,3} with C its three leaves.
  - With C pairwise at distance ≥ 3 (`mls_test.py 300 100000 k ny 3`):
    - (k, |Y|) = (2, 1): 0 / 157 failures; at distance ≥ 4: 0 / 68.
    - (2, 2): 7 / 78 fail, e.g. a triangle with three pendant edges.
    - (3, 0): 0 / 63. (3, 1): 2 / 47 fail.
  - L_N itself survives these instances; only the packed-set strengthening fails.
  - So the leaf trick generalises only pair by pair (L_N), not to packed sets with several leaves.
- **L∞ residual configuration, targeted** (`residual_test.py 200000 200000`). Random sparse graphs with exactly two even vertices c, z, plus a leaf ℓ at c; kept only if d(c, z) = 3, every neighbour of z is at distance 2 from c, and deg z ≥ 4 or z lies on a triangle. That is exactly the case the induction of connections §V.4c cannot handle. GL (the ℓ-path stays in {ℓ} ∪ N[c]): **1,531 instances, 0 failures, 0 undecided**.
- **Local invariant with an even vertex** (`lloc_z_test.py 700 100000 5 11`): Q_s ⊆ N[s] in graphs with one even vertex z fails 240 / 846 decided when z ~ s, and 90 / 1,036 when z ≁ s (smallest example n = 5). So the strong local invariant cannot be carried through Lovász's induction, and one-sided separation (radius 2) stays open.
- **Multi-pair separation** (`msep3.py`, query S; `outputs/msep3.log`). F all-odd, a random maximal matching of pairs at F-distance ≥ 3. **2,892 instances, n = 8–16, 0 failures**, of which 925 are perfect matchings; 102 undecided within budget. With some pair at distance 2: 500 / 2,191 fail. So symmetric separation needs distance 3.
- **n = 14, minimum T-joins** (80 graphs, 160 constructions): 2,232 transversals, 0 not realisable, 8,896 / 8,896 extension queries succeed, RR true for 2,020, undecided for 212, never false.

## E21. Multi-pair separation (MSEP), class separation (CSEP) and the Case I lemma (cloud session `claude/multi-sep`)

Manuscript: `manuscripts/multi-sep/multi-sep.tex`. Scripts: `manuscripts/multi-sep/scripts/` (see its README); outputs in `scripts/out/`. Oracle: `tools/route_ext.c` (query `S`, also `A` and budgeted `B`), compiled locally as `scripts/route_ext`.

**Tools.**
- `cubsep.c`: an exact MSEP checker for cubic graphs. It chooses at each vertex an end edge (the other two edges form the transition) by depth-first search, keeping path components by union–find with vertex masks. Linking is allowed iff the two components meet only at the vertex, the end edge is in neither, and the merged component contains no pair. Modes: `all` (every perfect pairing at distance ≥ 3), `rand N seed` (random pairings), `given` (explicit pairs).
- `validate_cubsep.py` cross-checks `cubsep` against the independent enumerator `msl.all_decomps` on all 19 cubic graphs of order 10: 285 queries, pairs at distance 2 or 3, 9 failures (all at distance 2), 0 disagreements. (An earlier version reported 12: it also counted the three zeros of cubsep's summary line. Audit A18 found this; fixed.)
- `cubsep classes` (one colour per vertex after the graph) checks CSEP for a given colouring; validated against the oracle on 150/150 queries (`validate_classes.py`). Its FAIL line now prints the colouring (it printed zeros before).
- `randlov.py`: random runs of Lovász's induction (random choices, random Fan chains), then annealed end-swaps. A positive certificate, used for instances the budgeted oracle leaves undecided.

**(A) MSEP on cubic graphs, perfect pairings at distance ≥ 3.** 0 failures.

| order | graphs (nauty `geng -c -d3 -D3`) | pairings tested | time |
|---|---|---|---|
| 10 | 19 | 54 (all) | < 1 s |
| 12 | 85 | 2,846 (all) | < 1 s |
| 14 | 509 | 269,966 (all) | 0.3 s |
| 16 | 4,060 | 36,024,731 (all) | minutes |
| 18 | 41,301 | 8,260,200 (200 random per graph) | 30 s |

**(B) MSEP on other graphs.** 0 failures in every run.
- `search_general.py 3000 11 pair 12 20 2000000`: random all-odd graphs of orders 12–20 (edge density 0.12–0.5, at most 120 edges), with a random maximal pairing at distance ≥ 3, exact oracle with budgets of 2M, 8M, 32M and 128M nodes. Dense instances are often undecided within the budget. This run (3000 planned trials) was stopped before completion, so it printed no totals. All 269 undecided instances it listed in `out/gen_pair.txt` were certified by `randlov.py` (225/225 in `out/gen_pair_cert.txt` and the remaining 44/44 in `out/gen_pair_cert2.txt`; earlier batches 26/26 and 182/182). A complete smaller run, `search_general.py 400 12 pair 12 20 2000000` (`out/gen_pair_400.txt`): 368 instances (122 with perfect pairings), 0 failures, 41 undecided, all 41 certified (`out/gen_pair_400_cert.txt`).
- Random regular graphs (`dense_search.py`), perfect pairings at distance ≥ 3, all certified: 5-regular of order 30 (10/10) and 40 (30/30), cubic of order 26 (200/200). For 7-regular graphs of order 40 and 9-regular graphs of order 60, no perfect pairing at distance 3 exists in the samples.
- *Hardest instances* (`hardness.py`): rank instances by the fraction of random runs of Lovász's induction that separate. Minimum 0.067 for cubic graphs (orders 12–20) and 0.000 for random graphs (order 18). Every one of the hardest eight in each family has a separating decomposition.

**(C) CSEP (classes).** 0 failures except for overlapping families.
- Classes of size 3, pairwise at distance ≥ 3 (`exp_classes.py`), cubic: 32 (n = 12), 193 (n = 14), 174 (n = 16).
- Greedy maximal classes: n = 14, 326 instances each for size caps 4, 8 and 32; n = 18, 200 each.
- **Minimum colourings of the square** (classes = colour classes, so every path must be rainbow). *Correction (audit A18):* `exp_sqcol.min_colouring` started its search at ⌊Δ(K²)/2⌋ + 1, which is not a lower bound for χ(K²); for 5 of the 85 cubic graphs of order 12 the colourings were not minimum. It now starts at Δ(K) + 1 (closed neighbourhoods are cliques of K²). The old counts (cubic n = 10, 12, 14: 57, 170, 150) are superseded. Rerun, 0 failures:
  - `cub_sqcol.py` (all connected cubic graphs, `cubsep classes`): n = 10, 5 random minimum colourings per graph (95); n = 12, 3 per graph (255; 24 with 4 colours); n = 14, 2 per graph (1,018); n = 16, 1 per graph (4,060; colours used 4: 55, 5: 914, 6: 2,929, 7: 152, 8: 10). `out/cub_sqcol.txt`.
  - `exp_sqcol.py ... rand` (random all-odd graphs, oracle): n = 10 (100, 0 undecided) and n = 12 (100, 3 undecided, all certified by `randlov.py`). `out/exp_sqcol_rand.txt`, `out/exp_sqcol_rand12.txt`.
- Overlapping families (`exp_conflict.py`): the union of two perfect pairings (each vertex in two pairs) never fails, in 228 (n = 12) + 398 (n = 14) instances. The union of three fails twice in 228 at n = 12 (e.g. `K??FEaKR@oE_` with pairs 0-9, 0-10, 1-8, 1-11, 2-7, 2-8, 2-9, 3-6, 3-8, 3-9, 4-6, 4-7, 4-11, 5-6, 5-7, 5-10). So CSEP needs disjoint classes.

**(D) The Case I step of Lovász's induction with pairs.**
- `exp1.py` uses K with one even vertex z whose neighbours are all paired. For each u ∈ N(z) it enumerates all separating Lovász decompositions D′ of K − uz, and all Fan transfers z → u. Over 13 instances:
  - (A) some (u, D′, chain) works: 13/13;
  - (B) some u works for every D′: only 6/13;
  - (C) every u and every D′ works: 2/13.
  
  So the plain inductive hypothesis is not enough.
- `exp2.py`: of the failing transfers, 25,047 have a trivial chain (the end path Q_z contains the partner u′) and 3,838 have chain length 1. Chains of length ≥ 2 almost never fail.
- **(EE) / CL holds in every test.** (EE) says: z is the only positive even vertex, u ∈ N(z), and uz is the terminal edge at u of some rainbow decomposition.
  - `exp_ee.py`: 869 decided pairs (z, u) without classes, and 788 with pairings, 0 failures (51 undecided).
  - `exp_cl.py`: Case I configurations obtained from cubic graphs with perfect pairings by one Case II step (the leaf joins the class of x). Every neighbour w was tested: 456 (n = 12), 796 (n = 14) and 400 (n = 16), 0 failures. `exp_cl_big.py` (random cubic graphs): 300 (n = 18), 200 (n = 20) and 120 (n = 22), 0 failures, 0 undecided.
- `exp_swap.py`: of 206,068 separating D′ of K − uz whose Q_z meets u's class, only 84,315 are repaired by a single end-swap at a vertex of Q_z before the class vertex. So one local switch does not suffice.
- `exp_extremal.py`, `exp_min2.py`: among separating D′ of K − uz, those minimising |V(Q_z)| always avoid u's class (228/228, and all cubic-derived configurations). But the minimum is usually a single edge, so this is weak evidence.

**(E) Natural strengthenings that are false.**

| statement | script | failures |
|---|---|---|
| end paths avoid the partners of all neighbours (I1′) | `exp_inv.py` | 182/228 (n=12), 209/398 (n=14) |
| one forbidden class at every vertex | `exp_csepf.py` | 114/199 (dist ≥ 2), 79/199 (dist ≥ 3); 0/199 at half the vertices |
| even vertex is the centre of a path of length 2 (P2) | `exp_p2.py` | 8/200, 7/102, 4/198 |
| all neighbours of z end at z (EE-all) | `exp_eeall.py` | 32/200, 7/102 |
| Q_z ⊆ N[z] with separation (L∞) | `exp_se.py` | 1/600 (all-odd), 37/550 (one even vertex; includes z a leaf at the even vertex) |
| Kotzig P₄-decompositions (perfect matching + oriented 2-factor) suffice for cubic MSEP | `kotzig.py` | 2/228 at n = 12 (0/40 at 10, 0/298 at 14) |

**(F) Certified strategies.** These are inductions using only certified moves: the leaf merge (Case II), the certified Case I (z joins u's classes, needs distance ≥ 3 in K − uz) and rotation along cycles or leaf paths. *Correction (audit A18):* the earlier text described one search mixing all three moves; in fact `coarsen_fail.py` and `rotate.py` are separate searches, and the rotation figures depended on a cap on cycle length.
- `coarsen.py` (randomised Case I/II) succeeds on cubic graphs: 99/99 (n = 14), 299/300 (n = 16), 269/269 (n = 16, girth ≥ 5) and 200/200 (n = 18, girth ≥ 5).
- `coarsen_fail.py` (Case I/II only, exhaustive over all choices, memoised; 3 random perfect pairings per graph, seed 1) fails on 13/24 cubic instances at n = 10, on 6/9 triangle-free instances at n = 10, on 3/63 (n = 12, triangle-free), on 3/15 (n = 12, girth 5), and on 0/108 (n = 14, girth 5).
- `rotate.py n flag per maxlen` (rotation only, own sampled pairings): with cycles and leaf paths of every length (maxlen ≥ n), it fails on 1/24 (n = 10, per 3), 4/152 (n = 12, per 2) and 1/63 (n = 12 triangle-free, per 3). With maxlen 10 it fails on 14/152 at n = 12 (the number reported before); with the default maxlen 8, on 23/152 (audit). `out/rotate_uncapped.txt`.
- `combined.py` (from the audit's `A18-scripts/combined.py`: all three moves interleaved freely, all cycle lengths, exhaustive, on the instances of `coarsen_fail.py`) fails on 2/24 at n = 10 (`I?`cspoX?` with pairs (7,1)(5,3)(0,8)(9,4)(2,6), `ICOef?kF?` with (7,9)(6,8)(2,3)(0,4)(5,1)), 0/9 at n = 10 triangle-free, 1/63 at n = 12 triangle-free (`K?ABEb_J?sB_`). All are separable. `out/combined.txt`, `out/combined_tf.txt`.
- `strat_rreg.py`: random 5-regular graphs, n = 30: no certificate found in 10/10 instances (separating decompositions exist).
- Conclusion: local certificates need room at distance 3. The three certified moves alone do not suffice on some small instances.

**(G) Prescribed end edges** (`exp_twoend.py`). The question: are end edges at all vertices of a packed set (|X| ≤ 4) achievable simultaneously? The test uses the split graph with classes {x, ℓ_x}. Result: 311 + 229 instances, 0 failures among the 539 decided (1 undecided). |X| = 1 is a theorem (manuscript Thm "prescribed end edge").

**(H) Side test (`exp_elov.py`).** Lovász decompositions with b = deg mod 2 when the even vertices are pairwise at distance ≥ 3: 182 decided random instances, 0 failures. The first version of the test was degenerate: it made the even vertices by pendant leaves, which is trivially solvable.


**(I) Audit A18 and the degree-three case of EE.**
- Audit A18 (`research/audit/A18-multi-sep.md`, fresh subagent): no mathematical error; Lean statements match. Corrections applied: the certified-moves description (F), the cross-check count (9, not 12), the minimum colourings (C), plus wording and citation fixes in the manuscript.
- New theorem (manuscript Proposition "EE3", Lean `MultiSepEE.lean`): without classes, Conjecture EE holds when uz lies in no triangle, or when N(u) = {z, a, b} with ab, zb ∉ E (suppress u, apply L₁), or with ab ∈ E and u the only common neighbour of a, b. This covers every Case I configuration reached from a cubic graph by one Case II step, so the 2,272 configurations of (D) are a theorem without classes; with the pairing classes they remain computational evidence.
## E22. Star-terminal Lovász decompositions (STL, STL2) and the deletion tests (cloud session `claude/stl`)

Manuscript: `manuscripts/stl/stl.tex`. Scripts: `manuscripts/stl/scripts/` (see `manuscripts/stl/README.md`); outputs in `scripts/out/`. Oracle: `tools/stl.c` (new).

**Oracle.** `tools/stl.c` is the DFS of `route_ext.c` (memoised failures, so negative answers are exact), extended as follows.
- Query `Q`, given z and a profile b with b(z) = 0, decides whether some decomposition has #LL − #SS + [r short] ≤ thr (optionally with #LL = 0, the star-terminal case). The counters are part of the memo key.
- Flag `T` prescribes or forbids terminal edges.
- Flag `M` restricts the allowed transitions at z.
- Flags `W` (witness) and `B` (budget) work as in `route_ext`.
- Profiles up to 15 ends per vertex.

**Validation.** Two independent enumerators of all decompositions agree with the oracle on every one-even connected graph of order ≤ 7, with 0 disagreements:
- `brute.py`: 1,066 queries for ST, STL and BAL;
- `brute_flex.py`: 1,295 queries for prescribed short sets and pairings.

**(A) STL on all connected graphs of odd order ≤ 9 with exactly one even vertex** (`gen_one_even.py`, then `stl_run.py`). There are 7, 130 and 11,936 graphs at n = 5, 7, 9, built from `data/conn{n-1}.g6` with isomorphism rejection.

| n | graphs | pairs (J,r) | STL fails | BAL fails | Test1 fails among these | ST fails |
|---|---|---|---|---|---|---|
| ≤ 7 | 138 | 464 | 10 | 10 | 10 | 1 |
| 9 | 11,936 | 48,850 | 48 | 48 | 48 | 2 |

- Test1 was evaluated only at STL failures. Every failure has J − z disconnected, and Test1 fails at each of them. With the criterion theorem, on all graphs of order ≤ 9 and at every r with d(r) ≥ 3: **STL(r) ⇔ BAL(r) ⇔ Test1(r)**.
- The equivalence fails at d(r) = 1. There STL can hold through an SS path while r is isolated in J − z; the audit counted 1,192 such pairs, e.g. the spider r–z–a–{b,c}.
- Most pairs with J − z disconnected satisfy both STL and Test1. At n = 7, 76 of the 83 such pairs with d(r) ≥ 3 do.
- With J − z connected (10,996 graphs, 44,336 pairs), STL never fails. The earlier figure 54,336 was an arithmetic slip, found by audit A20.
- 3-connected graphs at n = 9: 5,231 graphs, 25,210 pairs, 0 failures (4,699 of the graphs have J − z ∈ C).

**(B) STL2 (Test2 analogue) on all connected graphs of even order ≤ 8** (`stl2_run.py`).
- 2,828 instances, 10 failures. Every failure has J − z disconnected, and Test2 fails there too (in 4 of them d(r) = 2).
- 3-connected: 958 instances, 0 failures.
- A "perfect" decomposition with β = b(r) = 0 exists in only 748 of the 958; STL2 then uses β = 2.

**(C) Random 3-connected samples** (`sample_run.py`, with every budget-undecided entry re-decided by `resolve.py` / `resolve2.py`). 0 failures throughout.
- STL: n = 11 (600 graphs, 3,256 pairs), n = 13 (600, 3,470), n = 15 (350, 2,082), n = 17 (60 sparse, 338).
- STL2: n = 10 (1,200 instances), n = 12 (1,000), n = 14 (500).

**(D) Flexibility on 3-connected graphs** (`flex_run.py`).

| class | graphs | EE(u) and STS(u) | HALF(S) | PAIR(M) |
|---|---|---|---|---|
| n = 5 (only W₄) | 1 | 4/4 | 2/6 | 2/3 |
| n = 7 | 28 | 126/126 | 244/266 | 168/168 |
| n = 9 | 5,231 | 25,210/25,210 | 66,818/67,220 | 54,045/54,045 |
| random, n = 11, d(z) ≤ 8 | 240 | 1,290/1,290 | 4,691/4,702 decided (200 undecided) | 5,196/5,196 |
| random, n = 13, d(z) ≤ 6 | 120 | 586/586 | 1,462/1,462 | 996/996 |

- STS(u): u is short in some star-terminal Lovász decomposition.
- HALF(S): the short set is exactly S.
- PAIR(M): the transitions at z are exactly M.
- **The only PAIR failure is W₄ with the diagonal pairing**; a hand proof is in the manuscript, Example W4.
- On all graphs with J − z connected at n ≤ 7 (103 graphs, 3-connected or not), PAIR again fails only on W₄.

**(E) Families** (`families.py`). 0 failures throughout.
- Wheels W₄ … W₁₈.
- J = H + universal z, with H random 4-regular of order 10, 12, 14, 16 (102 graphs, 1,232 pairs; J − z Eulerian, d(z) up to 16).
- Random non-3-connected J with J − z connected, n = 11 and 13 (250 graphs, 780 pairs).
- Random J with J − z **disconnected**, n = 11 (`families.py zdisc`; 300 graphs, 1,282 pairs). STL fails at 4 pairs, and Test1 fails at exactly those 4. So STL ⇔ Test1 persists beyond order 9. At n = 13 (200 graphs, 1,087 pairs): STL holds at 1,080, fails at 3 (Test1 fails at all 3), and 4 remain undecided after budgets up to 2·10⁹ nodes; an exact run, `resolve_fam.py`, is in progress.

**(F) Composition: two terminal edges at once** (`ptm_run.py`). Setup: a random connected all-odd graph G of order n and a random matching F of m edges. By the pairing proposition, PTM(G, F) is STL-P(J, F) for J = (G − F) + z(V(F)).
- PTM(G, F): some Lovász decomposition of G has every F-edge terminal *at some end* and no path with two F-edges.
- PEE_m: the same, with every F-edge terminal at a *prescribed* end.

| n, m | instances | PTM fails | PEE_m fails |
|---|---|---|---|
| 8, 2 | 299 | 0 | 8 |
| 10, 2 | 300 | 0 | 2 |
| 12, 2 | 300 | 0 | 0 |
| 10, 3 | 300 | 0 | 7 |

- PTM held in every instance, including the 317 with G − F disconnected. Its known exceptions are K₄ with a perfect matching (= W₄) and the prism with its rungs; neither arises at these orders.
- **Every PEE_m failure has two adjacent prescribed ends**; in 16 of the 17, both ends have degree 3. With pairwise non-adjacent prescribed ends, PEE_m held in all 612 instances.
- Independence of the ends is not the whole story, though. In (D), HALF(S) fails for 10 of 13,666 *independent* short half-sets at n = 9. All 10 are dense configurations whose short ends have degree 3.
- **Conclusion:** single-transition lemmas with prescribed ends (EE, PEE, prescribed end edge) cannot be composed transition by transition. A composition step must keep the choice of the short end free.

**Negative results.**
- STL-P (every pairing realisable) is false on W₄.
- HALF (every short half-set realisable) is false in general: 402 of 67,220 half-sets fail at n = 9.
- ST already fails when J − z is disconnected; the smallest example is two K₄ sharing z.

## E23. Prescribed end edges with one even vertex: PEE, EE, L1* (cloud session `claude/ee`)

Manuscript: `manuscripts/prescribed-end/prescribed-end.tex`. Scripts and outputs: `manuscripts/prescribed-end/scripts/` (README there). Conclusions: connections §Y.

**Oracle.** `pee.c` decides whether xy is terminal at x (the path ending at x has last edge xy) in some Lovász decomposition. It builds Q_x first through xy, then runs an exact search for the rest, with memoised failures and the pruning `deg(v) ≤ 2P − b(v)`. Further modes: avoidance (Q_c ∩ A = ∅), separation, EE-only.
- Validation against an independent brute force over transition systems (`brute.py`): all graphs n ≤ 7 with ≤ 1 even vertex, 2,279 queries, 0 disagreements.
- Validation against `tools/route_ext.c` (`xcheck_route_ext.py`), using queries X (EE via Prop EE) and S (away edges via the leaf graph): n = 9, 47,688 + 47,738 queries, 0 disagreements.
- No failure on the 224 connected all-odd graphs of order 8 (6,359 queries), as `lovasz_endEdge` requires.

**(A) Exhaustive.** Connected graphs with exactly one even vertex (odd order). "Away" counts ordered edges (x, y) with y ≠ z and d(x) ≥ 3.

| n | graphs | EE tests | EE fail | away tests | away fail (graphs) |
|---|---|---|---|---|---|
| 5 | 7 | 14 | 0 | 37 | 5 (2) |
| 7 | 130 | 401 | 0 | 1,910 | 54 (31) |
| 9 | 11,936 | 47,688 | 0 | 330,449 | 1,410 (1,049) |
| 11 | 11,959,367 (EE only, `ee11_*.txt`) | 59,688,458 | 0 | — | — |
| 11, part: first 84,002 graphs of residue 0 mod 100 (geng order), all edges | 84,002 | 409,360 | 0 | 3,694,899 | 1,079 (992) |

- n = 11, EE only: complete, covering all connected graphs of order 11 with exactly one even vertex; summary lines in `out/ee11_*.txt`.
- A partial n = 11 run over all edges (the initial segment of each of three geng slices, killed for time) found 56,739 away failures and 0 EE failures. The failure lines are in `out/exh11_away_partial_fails.txt.gz`.

**(B) Structure of the away failures.** All of the following hold at n = 5, 7, 9; at n = 11 (the part-slice and the partial run; `out/analyze_fail_11partial.txt`, `out/feat_11partial.txt`); and for the 99 random failures:
- y ∉ N(z) and dist(x, z) ≤ 2 in every failure;
- the reverse prescription (xy terminal at y) holds in every failure (5/5, 54/54, 1,410/1,410, and 56,739/56,739 in the partial n = 11 run);
- d(x) ∈ {3, 5, 7}, d(z) ∈ {2, 4, 6} at n ≤ 9; at n = 11 also d(x) = 9 (1,763 failures) and d(z) = 8 (964) (`feat.py`).

**Reachability** (manuscript §6): xy is reachable if some z–y path has all interior vertices outside N[x].
- Every failure is unreachable: n = 5, 7, 9, the partial n = 11 run (56,739 of 56,739), the n = 11 part-slice (1,079 of 1,079; reachable away edges 3,266,268, all succeed; unreachable 428,631), and the 99 random failures (`out/rand_A2.txt`, a re-run with the same seed that prints each failure with its reachability).
- Among all away edges (`sharp.py`):
  - n = 7: 1,451 reachable, all succeed; 459 unreachable, 54 fail.
  - n = 9: 270,875 reachable, all succeed; 59,574 unreachable, 1,410 fail.
- This matches the theorem "EE ⇒ PEE at reachable edges".

**(C) Invariants for the open case of EE** (|N(u) ∩ N(z)| ≥ 2).

Separation of u and z in K − uz (`sepee`):

| n | \|T\| ≤ 1 | \|T\| = 2 | \|T\| ≥ 3 |
|---|---|---|---|
| 5 | always holds | fails 7/7 | — |
| 7 | always holds (242 tests) | fails 99/135 | fails 65/65 |

Here T = N(u) ∩ N(z). So full separation is the wrong invariant, and only Q_z ∌ u can be carried.

L1 with an even vertex g (`l1p all`; c odd, a odd, a ∉ N[c]):

| n | g ≁ a: tests / fail | g ~ a: tests / fail |
|---|---|---|
| 5 | 10 / 0 | 32 / 14 |
| 7 | 792 / 0 | 1,102 / 158 |
| 9 | 161,652 / 0 | 170,782 / 6,423 |

Other invariants:
- **|A| = 2 avoidance** (`l1s2`): ≤ 1 even vertex g, c odd, A = {a₁, a₂} disjoint from N[c] ∪ N(g). 0 failures: n = 5: 5; n = 6: 153; n = 7: 738; n = 8: 8,939; n = 9: 203,658.
- **Hypothesis of the triangle reduction**: in K − {uz, uw, wz} the path ending at w avoids u and z. It holds for every triple (z, u, w): n = 5: 18; n = 7: 622; n = 9: 88,356 (41,594 pairs (z, u) with a triangle).
- **Separating w from {u, z}** in K − triangle (`tri_sep.py`) fails in 267 of 622 triples at n = 7.

**(D) Random** (`rand_test.py 6000 101 5000000 11 13 15 17`, `out/rand_A.txt`). 6,000 connected graphs of orders 11–17 with one even vertex, node budget 5·10⁶.

| statement | tests | fail | undecided |
|---|---|---|---|
| EE, \|T\| ≤ 1 | 13,200 | 0 | 120 |
| EE, \|T\| ≥ 2 | 12,762 | 0 | 112 |
| away edges (12 sampled per graph) | 71,965 | 99 | 457 |
| L1*, A = {a}, a ≠ z | 42,315 | 0 | 276 |
| L1*, A = {z} | 5,669 | 0 | 27 |
| triangle-reduction hypothesis | 44,892 | 0 | 383 |

None of the 99 away failures is reachable, has y ∈ N(z) or dist(x, z) ≥ 3, or fails at both ends.

**Outputs.** Every number above has a file in `scripts/out/` (`regen.sh` regenerates the validation and (C) outputs). Audit A21 recounted orders 5, 7, 9 with an independent solver; all agree.

**Negative results.**
- PEE is false away from z (5-vertex example).
- Separation of u, z in K − uz fails when |T| ≥ 2.
- Separation of w from {u, z} after triangle removal fails.
- L1 with an even vertex adjacent to the avoided vertex fails (known: RD Remark 6.7). Here the adjacency is shown to be exactly the obstruction at n ≤ 9.

## E24. Two terminal edges at once: the terminal-matching property PTM (cloud session `claude/ptm`)

Manuscript: `manuscripts/terminal-matching/terminal-matching.tex`. Scripts and outputs: `manuscripts/terminal-matching/scripts/` (README in the manuscript directory). Conclusions: connections §Z. Lean: `lean/GallaiLean/TerminalMatching.lean`.

**Statement tested.** PTM(G, F): G has all degrees odd, F a matching; some Lovász decomposition has every F-edge terminal at one of its ends, no two on one path. PTM(G, F; e@x): additionally e terminal at x. PEE: all ends prescribed. Tested through J = (G − F) + z V(F): a star-terminal Lovász decomposition of J with transitions F at z (STL-P, stl.tex Prop 3.4). In the multigraph case an F-edge may be parallel to an edge of G' = G − F (a pair of the pairing adjacent in J).

**Oracle.** `ptm.c`: the search engine of `tools/stl.c` (validated in E22 against brute force), verbatim except for generation-stamped memo reset; every positive answer is re-checked by an independent verifier (edge partition, path property, end counts, star condition, allowed transitions, prescribed ends). 0 bad witnesses in all runs. Modes: `s` (all matchings of M edges of all-odd G), `p` (G' given, F all perfect matchings of the even vertices of G'), `f` (instances given). Budget mode re-runs undecided instances 6 times with growing budgets and shuffled orders.

**(A) Exhaustive, simple G** (all connected all-odd graphs, `nauty-geng -c`; every matching, not up to isomorphism):

| n | m | instances | PTM fail | PTM(e@x) tests / fail | PEE tests / fail |
|---|---|---|---|---|---|
| 4 | 2 | 3 | 3 (K4) | — | — |
| 6 | 2 | 206 | 0 | 824 / 0 | 824 / 36 |
| 8 | 2 | 13,025 | 0 | 52,100 / 0 | 52,100 / 420 |
| 6 | 3 | 47 | 1 (prism) | 276 / 2 | 368 / 122 |
| 8 | 3 | 14,077 | 1 | 84,456 / 13 | 112,608 / 3,259 |
| 8 | 4 | 1,955 | 0 | 15,640 / 14 | 31,280 / 2,787 |

Every PTM failure with m ≥ 3 and every PTM(e@x) failure has G − F disconnected. PTM_2 fails only at K4 (even with G − F disconnected allowed). Caveat: e@x is tested only on PTM-positive instances (52,100 = 13,025 × 4), so K4, where every e@x fails with G − F = C4 connected, is not counted in the e@x column. The PTM(e@x) conjecture excepts it. An independent brute force (audit A22, `research/audit/A22-scripts/bf.py`) reproduces every row and the exact failure sets.

**(B) Exhaustive, n = 10, up to isomorphism.** `encode.c` (each F-edge subdivided by a vertex with two pendant leaves, the only even vertices) → `nauty-labelg` → `sort -u` → `decode.py` → `ptm f`. The 32,851 connected all-odd graphs of order 10 give 3,474,599 classes (G, F) with |F| = 2 (validated at n = 8: 13,025 instances → 3,913 classes, all pass). Run `run_n10.sh 2`. Chunks 18–23 were moved to 4 workers (`n10_finish`, same oracle and aggregation). **Partial result (18 of 24 chunks, 2,605,950 of 3,474,599 classes): 0 PTM failures, 0 undecided; 10,423,800 PTM(e@x) tests, 0 failures, 0 undecided (exact search, every witness verified).** The last six chunks hold the densest graphs and took over three hours each with exact search. A container restart at 16:13 killed chunks 18–21 before they finished. They were restarted as `rest_00..03` (the 868,649 classes of chunks 18–23, split four ways), with `ptm f 2 2000000 0`: node budget 2·10⁶, 6 attempts, cut-offs reported as UND, to be re-run exactly. The total is to be added when they finish.

**(C) Multigraph case** (`ptm p 0`, all connected G' of order ≤ 8, F any perfect matching of Ev(G') with G' + F connected):

| n | instances | with a parallel pair | PTM fail | PTM(e@x) fail |
|---|---|---|---|---|
| 4 | 6 | 4 | 1 (K4) | 0 |
| 6 | 299 | 236 | 0 | 16 |
| 8 | 76,327 | 65,712 | 28 | 1,926 |

Every failure other than K4 has a cut vertex in G' = G − F, and J of connectivity ≤ 2 (`analyze.py`; confirmed independently by audit A22). So 2-connected G − F never fails. 3-connected J implies 2-connected G − F, but not conversely.

**(D) Girth ≥ 5** (`nauty-geng -ctf`, all-odd): n = 6, 8, 10, 12: 4 + 20 + 221 + 1,252 instances (m = 2), 5,988 PTM(e@x) tests, 0 failures, as Theorem 6.1 of the manuscript requires.

**(E) Random, n = 12, 14, 16** (`gen_random.py`, `run_random.sh`; G(n,p), p ∈ [0.15, 0.5], parities repaired; m = 2, 3, 4; F chosen at random, or "close" (each new F-edge adjacent to an earlier one), or "share" (each new F-edge at distance exactly two, sharing neighbourhoods); 150 instances per cell, budget 2·10⁵ nodes per attempt). 0 PTM failures, 0 PTM(e@x) failures (4,050 instances, 23,950 e@x queries); undecided counts in `out/random.log`.
- 56 PTM and 75 e@x queries were undecided.
- Re-run of the 120 instances concerned (`und_rerun.py` → `ptm f`, budget 5·10⁶; `out/rnd_und.log`): all but 8 PTM and 23 e@x queries decided, every one positively.
- The audit's independent brute force (`A22-scripts/und_bf.py`) decides 82 of the 120 as positive for PTM and every e@x: all 23 with m = 2, 39 of 40 with m = 3, 20 of 57 with m = 4. One m = 3 instance (``OAdCiI?HMc@?KqaKB`laP``) is still open after 8 × 120 s; the rest were not reached. No failure.

**(F) Reach of the walk theorem** (`walk.c`, all 2-matchings of all connected all-odd graphs; all 8 orientations; all admissible walks of least length):

| n | instances | no admissible walk | base hypothesis holds | sparse hypotheses hold (proved theorem applies) |
|---|---|---|---|---|
| 6 | 206 | 1 | 160 | 31 |
| 8 | 13,025 | 68 | 12,193 | 2,288 (3,093 with walks up to 3 longer) |

The base hypothesis is decided exactly (the stl.c engine with a separation constraint). Outputs: `out/walk_{6,8}_0.txt`, `out/walk_8_2.txt` (walks up to 2 longer), `out/walk_{6,8}_0_sparse.txt`, `out/walk_8_3_sparse.txt` (sparse mode, `walk EXTRA 1`).

- **Longer walks do not help the base hypothesis.** With walks up to 2 longer than shortest, the count stays at 12,193 (the same 832 NOBASE lines). With every admissible walk of every length, none of the 832 is covered either (`walk 6 0` on the NOBASE lines, `out/walk_8_nobase_all.txt`). They do help the sparse form (2,288 → 3,093).
- **So the base problem has genuine failures.** In the 832 NOBASE instances (764 with an admissible walk) the base separation fails for every orientation, although PTM₂ holds.
- **Where the failures are** (distance between the edges in G − F; `nobase_profile.py`, `out/nobase_profile_8.txt`). There are two kinds:
  - no admissible walk at all: 68 instances, all at distance 2 (63) or 3 (5);
  - admissible walk but base fails: 764 instances, 761 at distance 1 (the shortest walk is a single edge, k = 1) and 3 at distance 2.
  - So with the edges at distance ≥ 2 and an admissible walk, the base hypothesis fails in 3 of 616 instances. At distance 1 it fails in 761 of 12,341.
  - NOBASE graphs are dense: 21.7 edges in G − F on average, against 13.8 for the others.
- **The number of edges of G − F joining the two F-edges decides** (`connector_profile.py`, `out/connector_profile.txt`):

  | joining edges | 0 | 1 | 2 | 3 | 4 |
  |---|---|---|---|---|---|
  | instances, n = 8 | 684 | 2,434 | 4,556 | 3,608 | 1,743 |
  | NOBASE with a walk | 3 | 0 | 0 | 182 | 579 |
  | no admissible walk | 68 | 0 | 0 | 0 | 0 |

  At n = 6, NOBASE occurs only with 4 joining edges (45 of 63) plus one instance without a walk.
  - In J, 4 joining edges mean that z and N(z) span W₄ with F as its diagonal pairing (the K₄ obstruction); 3 mean W₄ minus a rim edge.
  - So the base problem fails exactly at local copies of the K₄ obstruction, apart from walk-less instances and 3 exceptions.
- **The packed case has none.** With the three pairs packed in M, every base graph is separable: n = 6: 200 of 1,298 base graphs packed; n = 8: 11,810 of 85,608 (audit A22, `packedbase.py`).

**(G) Random multigraph case, G − F 2-connected** (`run_multi.sh`, `gen_multi.py n M 120 seed 2conn` → `ptm p M`, budget 2·10⁵; `out/multi.log`). For each n = 10, 12, 14 and M = 2, 3: 120 random 2-connected G' with exactly 2M even vertices, and every pairing F of them.

| | total |
|---|---|
| instances | 6,480 |
| with a pair adjacent in G' (parallel F-edge) | 4,978 |
| PTM failures | 0 |
| PTM(e@x) failures | 0 |
| undecided within the budget | 48 PTM, 86 e@x (not re-run) |

Supports Conjecture 2.4.

**(H) Cubic graphs, |F| = 2, up to isomorphism** (`run_extra.sh`: `geng -d3 -D3` → `encode 2 | labelg | decode` → `ptm f`, budget 2·10⁶; `out/extra.log`):

| order | classes (G, F) | e@x tests | failures | undecided |
|---|---|---|---|---|
| 12 | 3,745 | 14,980 | 0 | 0 |
| 14 | 46,407 | 185,628 | 0 | 0 |

**(I) Reach of the local-girth corollary** (`localgirth_stat.py 300 7 11 15 21 31 51`; `out/localgirth.log`). Random 3-connected J with degree sequence (4, 3, …, 3): configuration model, simple graphs only, node connectivity ≥ 3. A pairing {ab, cd} of N(z) qualifies if:
- ab, cd ∉ E(J);
- c is reachable from a in J* = (J − z) + ab + cd;
- no triangle or 4-cycle of J* passes through a, b, c, d (the hypothesis of stl_of_localgirth / test1_of_localgirth).

| order | graphs | pairings (non-adjacent) | local hypothesis holds | J* girth ≥ 5 | graphs with a local pairing | graphs with a girth-5 pairing |
|---|---|---|---|---|---|---|
| 11 | 300 | 638 | 5 | 5 | 5 | 5 |
| 15 | 300 | 710 | 34 | 5 | 29 | 3 |
| 21 | 300 | 775 | 91 | 7 | 73 | 6 |
| 31 | 300 | 815 | 216 | 17 | 138 | 11 |
| 51 | 300 | 856 | 438 | 32 | 210 | 14 |

Audit A22b re-derived these with an independent script (`research/audit/A22b-scripts/stat_check.py`). With 3000 graphs per order (`stat_check_3000.log`):
- order 11: 19/3000 = 0.6% for both forms (the 5/300 above is a small-sample high);
- order 51: 68.1% local, 3.7% global;
- order 101: 83.6% local, 3.5% global.

**(J) Degree six: PTM_3 for the pairings of N(z), and the chained walk theorem** (`gen_d6.py`, `d6_pairings.py`, `walk3.c`, `d6_cover.py`; outputs `out/d6_*`, `out/walk3_d6_*`).

Instances: J 3-connected, z the only even vertex, d(z) = 6, G' = J − z. Every perfect matching F of N(z) is tested, including pairs adjacent in G' (multigraph G = G' + F), with `ptm p 3`.

| J | graphs | instances (with a parallel pair) | PTM_3 fail | PTM(e@x) tests / fail |
|---|---|---|---|---|
| order 7, all (`geng -c -d3`) | 7 | 105 (95) | 0 | 630 / 0 |
| order 9, all | 1,819 | 27,285 (24,328) | 0 | 163,710 / 0 |
| order 11, random (degrees 6 and 3/5, seed 611) | 200 | 3,000 (1,625) | 0 | 18,000 / 0 |
| order 13, random (seed 613) | 200 | 3,000 (1,327) | 0 | 18,000 / 0 |
| order 15, random (seed 615, first 300; budget 2·10⁶) | 300 | 4,500 (1,886) | 0 (0 UND) | 27,000 / 0 |
| order 17, random (seed 617, first 300; budget 2·10⁶) | 300 | 4,500 (1,619) | 0 (0 UND) | 27,000 / 0 (3 UND at 2·10⁶, all positive at 10⁸: `out/d6_r17_und.out`) |

- **Every pairing works at d(z) = 6 when J is 3-connected**, parallel pairs included, with any one prescribed end.
- The prism-with-rungs failure of PTM_3 has J − z disconnected, so it does not occur here.
- Prescribing all three short ends (PEE) fails in 1,156 of 218,280 tests at order 9 (`ptm p 3 0 1`).

**Chained walk theorem** (manuscript §8): leaf the first edge, walk P2 from y3 to x2 and P1 from y2 to x1. `walk3 0 [1]` tests the base hypothesis (a Lovász decomposition of M separating {x1,ℓ1}, {x2,y2}, {x3,y3}, {ℓ1,y2}, {ℓ1,y3}, {y2,y3}). It uses simple pairings only, all 48 orders/orientations, and shortest admissible chains.

| J | simple instances | base | no admissible chain | J with all 6 r covered |
|---|---|---|---|---|
| 9 (all) | 2,957 | 2,269 | 120 | 509 / 1,819 (593 have no simple pairing; 315 have no base) |
| 11 | 1,375 | 1,367 | 2 | 199 / 200 (one has 5) |
| 13 | 1,673 | 1,669 | 1 | 200 / 200 |
| 15 | 2,614 | 2,613 | 0 | 300 / 300 |
| 17 | 2,881 | 2,880 | 0 | 300 / 300 |

"Covered" means r is a long end (y_i) of some configuration with a base. The theorem then reduces STL(J,z,r), hence Test1 at z, to the base hypothesis.

**Far-apart form (manuscript Prop 8.3, Cor 8.4).** If the six neighbours of z are pairwise at distance ≥ 3 in J − z, the base hypothesis holds for every admissible chain (sparse separation, no exceptional vertex). So only chain existence is needed. `d6_reach.py 200 61 21 31 51 101 201` (`out/d6_reach.log`) uses random 3-connected J with degrees (6, 3/5, …). Chains are searched greedily: a shortest constrained P2, then a shortest P1 edge-disjoint from it.

| order | 21 | 31 | 51 | 101 | 201 |
|---|---|---|---|---|---|
| N(z) pairwise at distance ≥ 3 in J − z | 0 | 1 | 15 | 69 | 99 |
| of which every r has a chain | 0 | 1 | 15 | 69 | 99 |

**Chain existence (manuscript Conjecture 8.6).** `chain_search.py COUNT SEED EXTRA` (`out/chain_search.log`) is an adversarial search:
- J: z, its six neighbours, two private neighbours each (so N(z) is far apart), EXTRA further degree-3 vertices, outer edges wired at random; 3-connected, all degrees off z odd.
- Chains are searched exactly: every P2, then a BFS for P1 avoiding P2's edges. This uses Definition 8.1 as now stated, with y1 free.

| EXTRA | order | graphs | some r uncovered | r needing r ∈ {y2, y3} |
|---|---|---|---|---|
| 0 | 19 | 100 | 0 | 0 |
| 2 | 21 | 100 | 0 | 0 |
| 4 | 23 | 100 | 0 | 0 |
| 6 | 25 | 100 | 0 | 0 |

Second family (`chain_search.py 100 SEED EXTRA 3 BRIDGES`, `out/chain_search_halves.log`): two halves, each holding three neighbours of z with their private pairs and EXTRA/2 extra vertices, wired separately and joined by BRIDGES edges. So J − z has a 2- or 4-edge cut while J is 3-connected.

| EXTRA | order | BRIDGES 2: graphs / uncovered | BRIDGES 4: graphs / uncovered |
|---|---|---|---|
| 4 | 23 | 100 / 0 | 100 / 0 |
| 8 | 27 | 100 / 0 | 100 / 0 |
| 12 | 31 | 100 / 0 | 100 / 0 |

r = y1 always suffices, which is why Conjecture 8.6 is stated with y1 = r.

Audit A22c (G1): the Lean `AdmChain` takes N(x3) in G, so P1 avoids y3. `d6_reach.py` and `chain_search.py` now exclude y3 from P1, and all three tables were re-run with identical counts. The logs now record BRIDGES. The PEE cross-check is reproducible with `scripts/ptm_pee.sh` (207 failures on the order-9 simple instances).

**Cross-check of the theorem against the oracle.** At order 9 (all configurations, `walk3 0 1`) there are 9,457 base configurations. For each of them, PEE with the three short ends x1, x2, x3 is realisable. Checked with a scratch copy of `ptm.c` that prints each PEE failure. The 207 PEE failures on the simple instances (54 distinct (graph, short set) keys) never coincide with a base configuration; about 80 would be expected by chance.

## E25. The avoidance conjecture L1*: the local form, two even vertices, blocked instances (cloud session `claude/l1star`)

Manuscript: `manuscripts/l1star/l1star.tex`. Scripts and outputs: `manuscripts/l1star/scripts/` (README there). Conclusions: connections §AA.

**Oracle.** `l1s.c` decides whether some Lovász decomposition has Q_c ∩ A = ∅. Its search core is the `pee.c` oracle of E23: Q_c is grown first and never enters A, then the remaining edges get an exact search with prescribed ends.
- Validation against an independent brute force over transition systems (`brute.py`, `xcheck_brute.py`): every connected graph of order ≤ 7 with ≤ 1 even vertex, every odd c, and *every* subset A ⊆ V ∖ {c}, admissible or not.
  - 64 + 448 + 2,496 queries at n = 4, 5, 6, 0 mismatches.
  - n = 7: 49,920 queries, 0 mismatches (`out/xcheck_7.txt`).

**(A) Local form, exhaustive** (`l1s max`): A_max = V ∖ (N[c] ∪ N(g)) for every connected graph with ≤ 1 even vertex and every odd c. A pass implies L1* for every admissible A, of any size.

| n | graphs | pairs (G, c) | failures |
|---|---|---|---|
| 5 | 7 | 28 | 0 |
| 6 | 13 | 78 | 0 |
| 7 | 130 | 780 | 0 |
| 8 | 224 | 1,792 | 0 |
| 9 | 11,936 | 95,488 | 0 |
| 10 | 32,851 | 328,510 | 0 |
| 11 | 11,959,367 | 119,593,670 | 0 |

**(B) Random.**
- `rand_max.py 3000 7 5000000 11 … 16`: 3,000 connected graphs at n = 11–16, 38,896 pairs (G, c), 0 failures, 199 undecided (budget 5·10⁶).
- At n = 17–20 (p ∈ [0.12, 0.35]): 400 graphs, 7,202 pairs, 0 failures, 185 undecided.
- The two-even conjecture on random graphs: 358 of 360 graphs (n = 12–16) decomposable, 2 undecided. Three packed even vertices (n = 13, 15): 318 of 320 decomposable, 2 undecided.
- Region forms, exhaustive n ≤ 9 (`ball_test.py`): 0 failures for route-descent's B₂(c) (its Conjecture 8.2), the leaf form, and the intersection N[c] ∪ (N(g) ∩ B₂(c)).

**(C) Necessity and shape.**
- Dropping A ∩ N(g) = ∅ gives failures (`maxn5–7`); every minimal failing set meets N(g).
- "A separates c from g" does not replace the condition: at n = 9, 3,162 of 47,526 such instances with A ∩ N(g) ≠ ∅ fail (`gen9.txt`). The smallest is `DTw`.
- Admissible instances with |A| ≤ 4 at n = 9: 565,746, 0 failures.
- Q_c can be forced to be long (Hamiltonian at n = 8) and to use up to five vertices of N(g) ∖ N[c] (n = 7; `stats*.txt`).

**(D) Two even vertices** (`l1s two`, `packedev`, `peloc`). Is there a decomposition with b = d mod 2?
- Two even vertices at distance ≥ 3: always (n = 6: 3, n = 8: 173, n = 10: 50,561 graphs).
- Distance 1 fails in 22,100 of 562,856 graphs at n = 10; distance 2 fails in 21,258 of 501,456.
- Packed even vertices (pairwise distance ≥ 3): always, n ≤ 10 (including 52 graphs with three at n = 9).
- The local form with two packed even vertices fails in 61 of 404,488 pairs at n = 10 (the smallest is `GCQbVg`, c = 1, n = 8).

**(E) Census of reductions** (`blocked_count.py`, `irred_all.py`; |A| ≤ 2, one even vertex).
- n = 9: 411,948 instances.
  - 144,284 have c ∈ N(g); 68,678 have a free u ∉ N(c); 141,772 have a free u ∈ N(c).
  - **57,214 are blocked** (13.9%; 13,672 with g ∈ A).
- After every reduction of the manuscript, one level deep, 2,414 remain (0.59%). All have d(g) ∈ {2, 4}; 2,219 have g ∈ A, and in the rest A separates c from g.
- Recursive certificate search from the reductions (`cert.py`, `cert_ee.py`):
  - n = 6: every instance is certified.
  - n = 7: 35 of 1,868 instances are not.
  - EE at n = 7: every pair is certified except the six pairs of CP(3) + apex (`F]~vw`, |T| = 4).

## E26. Fan's lemma at equality: the common residual of L∞, L1*, EE and PTM (cloud session `claude/tight-fan`)

*Manuscript: `manuscripts/tight-fan/tight-fan.tex`. Scripts and outputs: `manuscripts/tight-fan/scripts/`. Lean: `lean/GallaiLean/TightFan.lean`.*

**Tooling.** `tf.py` enumerates every path decomposition with prescribed end counts (transition systems). It can prune on Q_c ∩ A, on a region, or on separated pairs, and it executes Fan's chain exactly with every choice. It matches `l1s ed` on 1,772 random avoidance queries at n = 5–7, with 0 mismatches (`out/xcheck.txt`). In every Case I step run below the Fan image was unique, as `fanPred_unique` predicts.

**(A) L1* blocked residuals** (`exp1c.py`, `exp1d.py`, `exp1e.py`).
- Order 9: all 2,414 irreducible blocked instances (|A| ≤ 2, one level of every reduction). **Every one has a target u ∈ N(g) with (G − gu, c, A) good, although inadmissible.** (`out/exp1c_9.txt`)
  - Such a u lies outside N(c) in: all 162 + 33 separated instances; 637 of the 1,019 instances with g ∈ A, d(g) = 4.
  - Every good u lies in N(c) (the tight case at c) in: all 1,200 instances with g ∈ A, d(g) = 2; the other 382 with d(g) = 4.
- A = V ∖ (N[c] ∪ N(g)), order 9, the 12,622 blocked instances with A = ∂C: every one has a good target. In 2,938, every good target lies in N(c) (`out/exp1c_9max.txt`).
- Order 7, every good D' of G − gu and its forced Fan image (`out/exp1d_7*.txt`). |A| ≤ 2:
  - u ∈ N(c), chain avoids c: 896 transfers, all good.
  - u ∈ N(c), chain passes c: 696 transfers, all bad.
  - u ∉ N(c): 56 transfers, all good.
  - With A maximal: 930 / 515 / 618, the same pattern.
  - At order 7 the result is good iff the forced chain avoids c. **The "if" direction is a lemma** (manuscript Lemma 3.2). **The "only if" direction fails at order 9** (audit A24, F2):
    - counterexample `H??FFf}`, g = 3, c = 0, A = {1, 3}, u = 7;
    - in A24's sample of 101 order-9 instances, 34,577 of 487,872 through-c transfers are good, and all 1,243,484 avoiding transfers are good.
- The sufficient condition of `l1_tight_transfer`: the c-side end of the cx-path lies outside N(x) ∪ {g}, or cx is terminal on Q_c.
  - Order 7: it holds for some good D' in every tight instance (14 with |A| ≤ 2; 49 with A maximal). It never failed to deliver (`out/exp1e_7*.txt`).
  - Order 9: met in all 83 tight instances of A24's sample. A full existence run (`exp1f.py 9 2`) was started and stopped unfinished after more than an hour of CPU time.

**(B) The L∞ residual** (`linf.py`, `out/linf7.txt`, `out/linf9b.txt`). K connected, a leaf ℓ at c, exactly one even vertex z, d(c, z) = 3, N(z) at distance 2, and d(z) ≥ 4 or z on a triangle; B = {ℓ} ∪ N[c].
- Orders 7 and 9: 3 and 133 instances. GL holds in all.
- Order 9, all 409,416 pairs (u, D'), with D' a decomposition of K − zu whose ℓ-path lies in B:
  - the far end y of the ℓ-path is in N(u) in 206,780 of them;
  - the forced chain reaches y in 53,964, and exactly these fail. This is a consequence of manuscript Proposition 3.1, which proves both directions, so it confirms the implementation rather than giving independent evidence.
- Every instance closes for some (u, D').
- **In 59 of the 133 instances every target u admits a failing D'.** In the other 74, some u succeeds for every D'. Every pair (instance, u) has some successful D' (A24). So in this Case I step the choice of target alone does not suffice; the hypothesis must control D'.
- For every instance and every target u, some D' has its far end outside N(u), which makes the step safe (`linf_far.py`, `out/linf_far9.txt`: 106 instances with 2 of 2 targets, 27 with 4 of 4).
- The strengthening GL⁺ (some GL decomposition has its far end not adjacent to the even vertex) is false in general (`glplus.py`):
  - it fails at d(c, g) = 1, 2 already at order 5; the smallest distance-2 failure is `DTw`;
  - it holds at order 7 when d(c, g) ≥ 3 (`out/glplus5.txt`, `out/glplus7.txt`). An order-9 run was stopped unfinished.

**(C) PTM NOBASE instances, order 8** (`ptmwalk.py`). Walks of any length are allowed, admissible or not. Base decompositions with the three separations are enumerated exactly. The walk back uses exact Fan chains, and every success is checked as a Lovász decomposition of G with ab terminal at a and xy terminal at x on different paths.
- The 68 instances with no admissible walk: **all 68 are closed by a tight walk** (through N(x)), under the forced-chain hypothesis ("the forced chain does not reach x"). The shortest successful walk, minimised over orientations, has length 2 in 63 of them and 3 in 5 (`out/ptm_nowalk68.txt`; minimum over orientations confirmed by A24).
- Under the static sufficient condition alone (no vertex of {p_{i+1}} ∪ N(p_i) has x as predecessor), 47 of the 68 are closed (A24, F1).
- The 764 K4/W4-type instances: a systematic 1-in-10 sample of 77, with walks of length ≤ 6. The first 15 were completed (`out/ptm764s_*.txt`); the rest were stopped (too slow):
  - 14 have no walk, admissible or not, in any orientation, with a separated base decomposition;
  - 1 (`GCdbF_`) is closed by a tight walk of length 2.

**(D) The named instances** (`ee_inst.py`, `out/ee_inst.txt`). For each EE pair (z, u): the instance (K − uz, z, {u}) and the triangle instances. None is blocked at the first level.
- CP(3) + apex (`F]~vw`): every Case I target of (K − uz, z, {u}) is adjacent to c. Per target: 456 good D'; 320 successful transfers; 168 meet the sufficient condition.
- Double K4 (`FQhVw`):
  - (K − uz, z, {u}): every target is tight, and all 108 good D' per target meet the condition.
  - Triangle instances: the tight targets have no good D' at all (hypothesis side); the other targets have 4 good D', all successful.

**(E) Weakening admissibility** (`exp2.py`, `exp3.py`). All A ⊆ V ∖ N[c] with |A| ≤ 2, order 9: 1,046,152 instances.
- Admissible instances (411,948) never fail.
- Every local weakening tested fails on 2.5–3.1% of the instances it covers (`out/exp2_9.txt`). The weakenings were: N(g) ⊄ A; g has a neighbour outside A ∪ N[c]; g ∈ N(c); and variants.
- One-step derived instances (G − gu, c, A), for admissible (G, c, A) with c ∉ N(g): bad for some particular u (2,258 cases where not every u is good). But in **all 267,664** admissible instances some u makes (G − gu, c, A) good (`out/exp3_9.txt`; order 7: `out/exp3_7.txt`).

**(F) Flowers.** No computation is needed. Every flower or receipt-or-flower output has two ends on the transversal (`flower_decomp_not_le_one`), so a flower cannot be the last move of a Lovász-type argument. Lovász decompositions never meet the hypothesis of `hub_cycles` with |T| ≥ 2 (`hub_cycles_card_le_one`).

**Audit A24** (`research/audit/A24-tight-fan.md`): every committed number reproduced. Fan-image uniqueness was checked in 108,870 cases at order 7, and `exp1d.py` now asserts it. F1 (47 vs 68) and F2 (L1* converse) are corrected above.

## E27. Lovász's induction for L1*: transfer calculus, TR and ST, candidate classes (cloud session `claude/l1-induction`)

*Manuscript: `manuscripts/l1-induction/l1-induction.tex`. Scripts and outputs: `manuscripts/l1-induction/scripts/` (C++, `g++ -O2`; `regen.sh` regenerates every short run). Lean: `lean/GallaiLean/L1Induction.lean`. Audit: `research/audit/A25-l1-induction.md` (all corrections applied below).*

**Tooling.**
- `lind.h`: the exact avoidance oracle, a port of `l1s.c` (E25). Audit A25 cross-checked it with an independent transition-system oracle.
- `orc2.h`: several constrained paths, with an optional disjointness constraint.
- `dec.h`: enumerates all good Lovász decompositions and simulates the forced Fan chain exactly. Every decomposition and Fan image is checked.
- Cross-check `xcheck2.cpp` (`out/xcheck2_4_7.txt`): `orc2` against enumeration, 31,704 queries at n = 4–7, 0 mismatches.
- `moves.h` / `rec2.cpp`: the certificate class Rec. Intermediate instances are NOT required admissible.
  - Moves (a)–(i) of manuscript Thm 3.1. (b) and (c) are applied also when c ∈ N(g). (h) is used only when c ∉ N(g), along ≤ 8 shortest routes in G − A; flag `R` allows every route.
  - Flag `T` adds TR targets (move (t)).

**(A) Certificates without intermediate admissibility** (`rec2.cpp`). A = Amax unless stated.
- Moves (a)–(d) only: 26 of 78 not certified already at n = 6 (`out/rec_ad_only_6_8.txt`). K_{3,3} needs the split (g) at c.
- All moves (`MB`):
  - n ≤ 8: every admissible instance certified, for every admissible A: 9 / 23 / 405 / 2,150 / 27,837 at n = 4–8 (`out/rec_subsets_4_8.txt`).
  - n = 7, |A| ≤ 2: all 1,868 certified (`out/rec_small7.txt`). E25's `cert.py`, which demanded admissible intermediates, failed 35 of them (A25 reproduces the 35).
  - n = 9: 209 not certified (163 blocked); with every route, 208 (162) (`out/rec_adm9_MBR.txt`). With (b), (c) restricted to c ∉ N(g): 301 (A25).
  - n = 10: 54.
- **Stuck admissible instances** (`out/stuck0_9.txt`): good, but every instance-level move gives a bad child. There are 6 at n = 9 and none at n ≤ 8.
  - They come from 5 non-isomorphic graphs. All share one mechanism: d(g) = 4, d(c) = 5, N(c) independent, N(g) ⊆ N(c), every target u with N(u) = {g, c, a_u}, a_u ∈ A.
  - `H?ABvrw` is `G?Bvvo` (l1star §8) with a leaf at its degree-2 even vertex.
  - All 6 are closed by the D-level tight transfer (`out/tt_stuck0_9.txt`): 76–92% of the good D' have their chain avoiding c, and all of these transfer.
- With TR targets (`MBT`):
  - n = 9: 56 not certified (35 blocked); with every route, 55 (34) (`out/rec_adm9_MBTR.txt`).
  - Every admissible A: 57 of 574,566 (36 blocked; 55 / 34 with every route, A25). With (b), (c) restricted to c ∉ N(g): 203.
  - n = 10: 33 of 328,510.
  - Stuck states below the 56 (`out/explore9_MBT.txt`): 1,296, none admissible. 1,184 admit no move (N(g) ⊆ A).
- **Gap** (`gap.cpp`, `out/gap_6_8*.txt`): the longest run of inadmissible intermediates in the best certificate.
  - n = 7: 760 / 11 / 5 / 4 instances need gap 0 / 1 / 2 / 3; with TR, 764 / 11 / 5 / 0.
  - n = 8: 1,589 / 68 / 112 / 20 / 0 / 3, with or without TR. Gap 5 is K8 − K3 with c in the triangle.
  - This is a statement about certificates. It does not show that "within k moves of some admissible instance" fails to close (A25, F12).

**(B) The transfer side: TR.** Tight target x ∈ N(g) ∩ N(c), c ∉ N(g), A ∩ (N[c] ∪ {x}) = ∅. If (G − gx, c, A) is good, is (G, c, A) good?
- `tr2.cpp`, every such A: n = 7, 3,764 tests (2,156 admissible, 1,608 with A meeting N(g)); **n = 9, 1,735,156 tests (637,572 admissible, 1,097,584 with A meeting N(g)), 0 violations** (`out/tr2_7.txt`, `out/tr2_9.txt`; split by A25).
- **Only the admissible part (TR_adm) is used by the reduction, and it is implied by L1Blocked.** Given ST, L1Blocked ⟺ TR_adm (Lean).
- Sharpness (`trall.cpp`, `out/trall_5_7.txt`, n = 7, A arbitrary):
  - non-tight targets: 6,672 tests, 0 violations;
  - tight targets: 8,066 tests, 14 violations, all with A ∩ N(c) ≠ ∅. Example `FCZ~o`.
- Re-choice (`rechoice.cpp`, `out/rechoice_5_7.txt`, `out/rechoice9.txt`): every good tight pair has a good D' whose chain avoids c. That is 8 / 457 / 82,079 pairs at n = 5 / 7 / 9.
- Coverage (`exch.cpp`, `out/exch7.txt`; n = 7, A = Amax, all tight pairs with c ∉ N(g)): of 34,778 good D', 24,738 have the chain avoiding c and 375 more satisfy the exchange lemma. Of the remaining 9,665, 824 have a good plain Fan image. So a proof must re-choose D' or repair the image by some other argument.

**(C) The hypothesis side: ST, ST', ST_out** (`stprime.cpp`; blocked instances, every admissible A).
- n = 7: 406 instances. ST holds in all, ST' in 386, ST_out in all 266 with a non-tight target (`out/stprime7.txt`).
- **n = 9: 135,188 instances. ST holds in all, ST' in 133,926. ST_out holds in all 100,990 with a non-tight target, and ST in all 34,198 with N(g) ⊆ N(c)** (`out/stprime9_v2.txt`).
- **ST' is false**: `FEhv?` (n = 7), g = 4, c = 6, A = {3,5} or {3,4,5}. With {3,4,5} it is the l1star Cor 5.6(5) minimal shape. With {3,5}, g ∉ A, and the split (e) settles it anyway.
- All 1,262 ST' failures at n = 9 have N(g) ⊆ N(c).
  - 1,238 have d(g) = 2 with N(g) independent; 619 of these have g ∈ A (the minimal shape).
  - 24 have d(g) = 4, d(c) = 5.
  - In 1,208 of the 1,262, every target u has N(u) ∖ {g, c} ⊆ A.
- L1E (`l1e.cpp`, `out/l1e_5_9.txt`): with A = Amax and c ∉ N(g), it holds in all 8 / 338 / 46,638 instances at n = 5 / 7 / 9.
- Move (s) (`smove.cpp`): Q_c = cu, i.e. G − cu − gu with Q_g, Q_u disjoint. It closes the 6 stuck instances. It is a three-even statement, so it gives no proof.

**(D) Targets and the c-admissible class.** n = 9, blocked, A = Amax (`out/targets9_summary.txt`, `out/badtargets9.txt`):
- 41,074 (instance, target) pairs; 496 have (G − gu, c, A) bad: 476 with d(c) = 1, and 20 with d(g) = 2, d(c) = 3.
- No simple rule always picks a good target. The best rule is right in 15,241 of 15,277.
- Every-target form over all instances (`out/alltarget9.txt`): there is no bad target when d(g) ≥ 4 and d(c) ≥ 5, or when d(g) ≥ 6 and d(c) ≥ 3. With d(g) = 4, d(c) = 3: 16 bad of 50,516. (The earlier sentence "0 for d(c) ≥ 5 or d(g) ≥ 6" was false; there are 41 bad for d(g) ≥ 6, d(c) = 1 and 28 for d(g) = 2, d(c) ≥ 5.)
- The 476 bad d(c) = 1 children are not two-even instances (A25): 442 have u = y, 29 do not force Q_c = cy, and 5 force it at distance 2.
- Dead ends of Case I in the c-admissible class (`minobs.cpp`, `out/minobs_5_7.txt`): the smallest is the child `DEk` − 04 (g = 4, c = 1, A = {0,2}) of the admissible (`DEk`, 1, {0,2}), at n = 5.
- TR-licensed walks to an admissible instance (`walkadm.cpp`, `out/walkadm_7_9.txt`): 12 of 83 at n = 7, 2,325 of 15,277 at n = 9. The first version's 24 and 4,283 counted unlicensed trails (A25, F3).

**(E) Walk to a degree-two vertex** (manuscript Prop 3.3, proved on paper; `walk2.cpp`, `out/walk2_7_9.txt`). n = 9, A = Amax, blocked, 15,277 instances:
- mode 0: the walk applies to 3,969;
- mode 3: l1star Prop 5.3 as stated applies to 149, all with d(c) = 1; 45 of these have no walk (A25);
- mode 1, tight steps as far as TR licenses: walk 6,552, Fan trail 2,325, either 7,506 (49%);
- mode 2, the first version's unrestricted trails (12,980 / 4,283 / 13,259): not all licensed by TR.

**(F) Order 11 and random graphs.** `randtest.cpp`: budget 2·10⁶, A = Amax. So its TR tests are TR_adm, i.e. L1* itself.
- Exhaustive slices k/100 of order 11, k = 0–3 (`out/slice11_*of100.txt`): 554,998 graphs, 1,037,788 blocked instances.
  - ST: no failure (31 undecided).
  - ST_out (slices 1–3): 776,230 with a non-tight target, no failure (51 undecided).
  - L1E: no failure.
  - TR_adm: 6,046,289 tests, 0 violations (5,308 undecided).
- Random, n = 11 and 13, 3,000 graphs (`out/rand_11_13_v3.txt`): 9,071 blocked; ST 9,069 (2 undecided); ST_out 8,401 / 8,410 (9 undecided); L1E 9,068 (3 undecided); TR_adm 32,267 tests, 0 violations.
- Random, n = 15, 600 graphs (`out/rand_15_v3.txt`): 2,816 blocked; ST 2,805 (11 undecided); ST_out 2,668 / 2,683 (15 undecided); TR_adm 10,460 tests, 0 violations.
- The first run (`out/rand_11_13.txt`) reported 2 spurious L1E failures: a budget-hit target was not marked undecided. Both hold (`out/l1e_check13.txt`).
**(F) Random graphs** (`randg.py` + `randtest.cpp`, budget 2·10⁶, A = Amax).
- n = 11 and 13, 3,000 graphs, 9,071 blocked instances (`out/rand_11_13_v2.txt`):
  - ST: 9,069 hold, 2 undecided;
  - L1E: 9,068 hold, 3 undecided;
  - TR: 32,267 tight tests, 0 violations, 150 undecided.
  - The first run, `out/rand_11_13.txt`, reported 2 L1E "failures". They were tester artefacts: a target whose ST query hit the budget was skipped for L1E without being marked undecided. The tester is fixed; both were rechecked with no budget (`out/l1e_check13.txt`) and hold.
- n = 15, 600 graphs, 2,816 blocked instances (`out/rand_15.txt`): ST 2,805 hold, 11 undecided; L1E 2,803 hold, 13 undecided; TR 10,460 tight tests, 0 violations, 146 undecided.

## E28. The dense T(6)-i residual: the append chain and end-path bases (cloud session `claude/t6-dense`)

*Manuscript: `manuscripts/t6-dense/t6-dense.tex`. Scripts: `manuscripts/t6-dense/scripts/` (`gcc -O2 -o lsearch lsearch.c`; Python 3 + networkx). Raw outputs in `scripts/out/` (git-ignored, regenerable by `run_big.sh`, `run_lean.sh` and `run_lean2.sh`). Lean: `lean/GallaiLean/T6Dense.lean`.*

**Tooling.**
- `lsearch.c`: the depth-first decomposition search of `tools/stl.c` / `walk3p.c`, with memoised failures. Its constraints depend only on the path being closed, so the memo stays exact:
  - `sep` (no path contains both);
  - `ef` (the path with an end at v avoids S);
  - `ep` (no path has ends exactly a, b);
  - `es` (the path through the edge pq has its end on p's side outside S).
  - Constrained vertices are expanded first. A node budget gives "undecided".
- `walksim.py`: leaves, Fan transfers with the **forced chain** (it fails exactly when a blank is reached), the static predecessor check, and the J-form un-lift (every leaf → z, append x_i). It **verifies every final decomposition of J edge by edge**: paths simple, every edge once, end counts, star condition.
- `c4.py`: the C4 shape. Labelling x2 y2 y3 x3 along the cycle, {x1,y1} universal; chains P2 = y3x2, P1 = y2x1.
- `dense.py`: all shapes, all labellings with r ∈ {y1,y2,y3} and x1y2, x2y3 ∈ B.
  - Mode **`lean`** is exactly the Lean hypothesis `AppendBase`: `endT` first, else `leanE6`, checking that the static condition then holds in D3.
  - `endT` = (E1)–(E5) + (E7): all seven steps are appends (Thm 2.2).
  - `leanE6` = (E1)–(E5) + (E6) exactly as in Lean (Thm 2.3).
  - `endA` = (E1)–(E5) + (E6) without its clause w = y3. The clause is redundant (A26 §1.2), but Thm 2.3 is proved with it, so `dense.py endA` bases are checked by execution only. (`c4.py endA` uses the C4 labelling, where x2y2, y2y3 ∉ B, and is exactly (E1)–(E6).)
  - `endZ` = `endA` with z and y3 added to the mask (every leaf = z): stronger than (E6), so `endZ` bases satisfy Thm 2.3.
  - `end` = (E1)–(E4) with Fan walks: the hypothesis of no theorem.
- `gen_resid.py`: random 3-connected J with B[U] = K6 − D and *some* of the residual conditions of a smallest failure (not imposed: C4 twins of degree ≥ 8, MR Thm 144's d(r) ≥ 8 with ≥ 3 core neighbours, the bad-vertex table):
  - δ(B) ≥ 6, δ(B[O]) ≥ 4;
  - ≥ 3 odd neighbours per site, ≥ 5 for a universal site;
  - |S(x)| ∈ {0,3,4,5,6};
  - C4: closed twins (both opposite pairs; TW = 1: one pair);
  - ∅: a full exterior vertex.
  - With |O| = 8: |B| = 14, 64–82 edges.

**(A) C4, the chained walk with one protected step** (`c4.py`, 10 `gen_core` graphs, |B| = 14, 4 seeds, budget 2·10⁶; 40 roots, 320 configurations).
- Mode `sep` (the six separations of TM Thm 8.2, protected step executed with the forced chain; these chains violate TM Def 8.1(ii) for C4, so the step is not guaranteed):
  - base found in 304/320 configurations (230 searches undecided);
  - the protected step succeeds for 834 of 1,050 distinct bases;
  - every root certified (40/40); the static condition held for 726 bases.
- Mode `end` (E1–E4): 320/320 configurations have a base; 992 of 1,280 bases execute; 40/40 roots.
- Mode `endA` (E1–E6): 320/320 configurations; **all 1,280 bases execute** (as the theorem predicts; 0 W2 failures); 40/40 roots.
- Residual C4 graphs (`gen_resid.py`, |O| = 8, 5 graphs):
  - `endA`: 160/160 configurations, 290/290 bases execute; |O| = 10: 160/160, 282/282.
  - `sep`: **0/160 configurations have a base found**: every one of the 320 searches hit the 5·10⁶ budget.

**(B) All shapes, the append chain** (`dense.py`; a root is certified if some labelling has a base and the executed construction verifies).

| graphs | mode | J | roots | certified | failures of executed bases |
|---|---|---|---|---|---|
| `gen_core` ∅, K3, C4, \|B\| = 14 | endA | 18 | 108 | 108 | 0 |
| residual, 3 per shape, \|O\| = 8 | endA | 15 | 90 | 90 | 0 |
| same | endZ | 15 | 90 | 90 | 0 |
| same, a subset: 3 K2, 3 C4, 2 P3 | endT | 8 | 48 | 48 | 0 |
| residual C4, \|O\| = 8 (TW = 2) | endZ | 20 | 120 | 120 | 0 |
| residual K3, \|O\| = 8 | endZ | 20 | 120 | 120 | 0 |
| residual P3, \|O\| = 8 | endZ | 20 | 120 | 114 | 0 |
| same subset (3 K2, 3 C4, 2 P3) | lean | 8 | 48 | 48 (K2: 16 E7, 2 E6) | 0 |
| residual K2, \|O\| = 8 (partial run, 4 graphs) | endZ | 4 | 24 | 24 | 0 |
| residual C4, \|O\| = 8 (TW = 2) | lean | 8 | 48 | 48 (all via E7) | 0 |
| residual K3, \|O\| = 8 | lean | 8 | 48 | 48 (46 E7, 2 E6) | 0 |
| residual P3, \|O\| = 8 | lean | 8 | 48 | 48 (all E7) | 0 |
| residual ∅ (full exterior vertex), \|O\| = 8 | lean, ≤ 60 labellings | 8 | 48 | 42 | 0 |
| residual C4 (TW = 2), \|O\| = 10 | lean, ≤ 60 labellings | 8 | 48 | 48 (all E7) | 0 |
| residual P3, \|O\| = 10 | lean, ≤ 60 labellings | 8 | 48 | 44 (41 E7, 3 E6) | 0 |
| residual K3, \|O\| = 10 | lean, ≤ 60 labellings | 8 | 48 | 42 (all E7) | 0 |
| residual K2, \|O\| = 10 | lean, ≤ 60 labellings | 8 | 48 | 42 (40 E7, 2 E6) | 0 |
| residual ∅, \|O\| = 10 | lean, ≤ 60 labellings | 8 | 48 | 48 (45 E7, 3 E6) | 0 |
| residual C4 (TW = 1), \|O\| = 10 | lean, ≤ 60 labellings | 8 | 48 | 48 (all E7) | 0 |
| residual K2, \|O\| = 8 | lean, ≤ 60 labellings | 8 | 48 | 30 (all E7) | 0 |

- Uncertified roots: every search of every tried labelling hit the node budget (or the 60-labelling cap was reached); no search returned NONE for them. Each such graph has all or most of its roots uncertified, which points at the search, not at the graph:
  - endZ P3, \|O\| = 8: `MV~~Nv{f~|q|~\lj_`, 6 roots;
  - lean P3, \|O\| = 10: `OV~~N}}~nyqz|Ef[~RFzF`, roots 1–4;
  - lean ∅, \|O\| = 8: `M~~zwFn~}~hi~z~z?`, all 6 roots;
  - lean K3, \|O\| = 10: `OF~~~U|^ay^v^hvayjnzw`, all 6 roots;
  - lean K2, \|O\| = 10: `O^~zn~{|nt}]vxXR}{FsL`, all 6 roots;
  - lean K2, \|O\| = 8: `M^~~Zxv^N~RJZujl_`, `M^~|x|vvhrnMnLy~_`, `M^~yn|{~mv^zJ\F]?`, all 6 roots each (the first also uncapped: all 240 labellings undecided).
  - Total: 46 roots in 8 graphs.
  - **Recheck with a count of proved absences** (`dense.py` now prints `none=` when a search returns NONE). For the five graphs found last (`out/hard3`–`hard5`), every one of the 4 searches per labelling was undecided (und = 4 · labs_tried), and none = 0.
  - **The search, not the base.** On `M^~~Zxv^N~RJZujl_`, STL-P for the labelled pairing (weaker than the base) is undecided for 20/20 labellings at the same budget 2·10⁶ (scratch check with `equiv.jsharp_query`). Dense residual graphs of this size are at the limit of `lsearch`.
  - A rerun of `OV~~N}}…` and `M~~zwF…` with budget 10⁷ and 3 seeds timed out after 3,000 s inside the first graph: inconclusive.
- "failures" counts bases whose executed construction did not verify. In the six-separation and `end` modes the protected step fails for 216/1,050 and 288/1,280 bases (A); those modes are not theorem hypotheses. No base satisfying (E1)–(E5) with (E6) or (E7), in any mode, failed to verify.

**(B′) Exhaustive, order 9** (`relabel.py` on `terminal-matching/scripts/out/d6_9.g6`; exact search, no budget).
- The 1,819 3-connected J of order 9 with z the only even vertex and d(z) = 6 include 28 with a dense core: 2 ∅, 6 K2, 8 P3, 5 K3, 7 C4.
- `dense.py lean 1 0`: all 168 roots certified at the first labelling, through (E7).
- `labstats.py 0`, over all 42,432 (root, labelling) pairs with the chain edges:
  - 42,384 have an (E7) base and 24 more an (E6) base;
  - 24 (all C4) have none;
  - every root has a base for ≥ 96.7% of its labellings;
  - 0 failures of executed constructions.
- The random sparse graphs of orders 11–17 of E24(J) have no dense core.
- **STL-P versus the base, per labelling** (`stlp.py`, exact search; side (b) of Prop 2.6 is `equiv.py`, written by the auditor). For all 14,144 labellings with chain edges:
  - STL-P for the oriented pairing (transitions x_i z y_i, x_i an end) holds for **all 14,144**;
  - an (E7)-base exists for 14,128, and side (b) of Prop 2.6 (STL-P plus x1y2 terminal at y2 and x2y3 at y3) holds for exactly the same 14,128 (A26, 0 disagreements);
  - an (E6)-base exists for 8 of the other 16;
  - 8 labellings, all C4, have no base although STL-P holds.
  - So Conj 5.1 is strictly stronger than STL-P on single labellings, but at order 9 it costs no root.

**(B″) The base conjecture versus L1\*** (`admissible.py`, `partial.py`).
- A condition "P_c avoids A" is L1\*-admissible if A misses N_M[c] ∪ N_M(x3).
- Fewest inadmissible base conditions over all labellings:
  - C4: E1, E7;
  - K3: E1, E2;
  - P3: E2, E4′, E7;
  - K2: E1, E2, E4′, E7;
  - ∅: every one of E1–E7 except the avoidance of z.
  - E4′ is the avoidance strengthening of E4.
- Residual C4 graphs (|O| = 8, canonical labellings, 3 seeds): 1,920 Lovász decompositions of M were found satisfying only the admissible conditions (E1′, E2, E3, E4, E5). Of these, E1 holds in 186, E7 in 1,042, and both in 120.
- So the inadmissible conditions are binding, and the base conjecture is a joint statement in the regime A ∩ N(g) ≠ ∅, where single-constraint L1\* is false in general (`DTw`).

**(C) Undecided searches.** Dense residual graphs make many searches hit the budget. On average a root needs 3–25 labellings, depending on shape; ∅ and P3 are the hardest. No search returned NONE (a proved absence of a base) for a labelling that was later needed.

**Verdict** (revised after audit A26).
- The (E7) form of the base is **equivalent** to STL-P with two further prescribed terminal edges (Prop 2.6). So Conj 5.1 is a uniform *strengthening* of STL-P, not a reduction to a weaker statement. It is strictly stronger on single labellings ((B′): 8 labellings with STL-P and no base).
- In the computed instances, for all five dense shapes, every root has a labelling with an append base, except 46 roots in 8 graphs that are budget-undecided. No search proved a base absent for a needed labelling, so the data show no counterexample to Conj 5.1.
- By the Lean theorems this gives STL at y1, y2, y3, and Test1 on every fully certified instance.
- The six-separation base of TM Thm 8.2 is the wrong hypothesis in the dense regime. It is impossible for D ≠ C4 (TM §9(1)), and in residual-style C4 graphs it was never found within the budget.

**(D) Audit A26** (`research/audit/A26-t6-dense.md`, fresh subagent).
- Mathematics correct: Thms 2.2, 2.3, Cor 2.4, Lemmas 2.5, 3.1, 4.1 SOUND. Prop 4.2 true, with an incomplete proof sketch, since rewritten.
- Lean faithful: build green, no `sorry`, standard axioms; `LovaszBase` is Def 2.1 verbatim, and the Lean (E6) is the paper's. The Lean conclusions record the STL data, not the transitions; the paper's Lean tags now say so.
- One ERROR, fixed: roots isolated in the core have D ⊇ K_{1,5}; Conj 5.1 ⇒ T(6)-i needs MR Thm 144 to exclude them.
- Novelty corrected: the (E7) equivalence (above); end-path tracking was proposed in TM §9(1); STL / `test1_of_stl`, STL-P ⇔ PTM₃ and TM Thm 8.2 were already one-even-vertex reductions.
- Data overstatements fixed: "every root"; mode definitions; the failure counts of non-theorem modes; the K2 cells.

## E29. The triangle base conjecture and the disjunctive avoidance conjecture DL (cloud session `claude/triangle-base`)

*Manuscript: `manuscripts/direct-test1/direct-test1.tex` (§§6–7). Scripts: `manuscripts/direct-test1/scripts/` (`tb.py`, `tb_compat.py`, `disj_general.py`, `dl_rand.py`, `dl_recheck.py`; oracle `gcc -O3 -o route_ext tools/route_ext.c`; Python 3 + networkx). Raw outputs are regenerable and not committed. Lean: `lean/GallaiLean/DirectTest1.lean`, `TriangleBase.lean`. Audit: `research/audit/A28-direct-test1.md`.*

**Tooling.**
- `tb.py` handles every J, every root r ∈ N(z) with d(r) ≥ 3, and every data choice (w, M0).
  - The base question for each data choice is 2^(m−1) exact per-end avoidance queries (route_ext `A`), one per orientation of the disjunctions.
  - Every base found is checked independently (an edge partition of M, ends = deg mod 2, the disjunctions), lifted by Steps 1–2 of Thm 2.1, and the lift is verified (an edge partition of J − z into simple paths, ≤ k paths, ≥ 2 ends at r).
  - At a root with no base, Test1 is decided exactly over all profiles with b ≤ 3.
  - Budgeted queries retry undecided orientations with further seeds.
- `tb_compat.py`: per data choice, which orientations are satisfiable and which pairs are satisfiable alone (the multi-pair compatibility question).
- `disj_general.py`, `dl_rand.py`: the disjunctive condition in arbitrary graphs with one even vertex g (Conjecture DL).

**(A) Exhaustive, order ≤ 9.** Every connected J with exactly one even vertex and d(z) ≥ 4 (`stl/scripts/one_even_{5,7,9}.g6`), every root with d(r) ≥ 3, every data choice, exact.

| n | κ(J) | graphs | roots with data | base | failures | Test1 at failures |
|---|---|---|---|---|---|---|
| 5 | 1 / 3 | 2 / 1 | 3 / 4 | 3 / 4 | 0 | – |
| 7 | 1 | 41 | 115 | 108 | 7 | fails at all 7 |
| 7 | 2 / ≥3 | 6 / 28 | 24 / 114 | 24 / 114 | 0 | – |
| 9 | 1 | 3,317 | 11,659 | 11,607 | 52 | fails at 28, holds at 24 |
| 9 | 2 | 583 | 2,402 | 2,402 | 0 | – |
| 9 | ≥ 3 | 5,231 | 22,772 | 22,772 | 0 | – |

- **Every root with data of every 2-connected J of order ≤ 9 has a triangle base.**
- At order 9, 36,779 of the 36,781 roots with a base have one at the first data choice tried. 123,787 bases were lifted, and every lift verified.
- **Every failure is explained by universal twins.** Each of the 243 data choices at the 52 failing roots (n = 9) has a pair (a_i, b_i) that is a pair of universal twins (N(a)=N(b)=C−{a,b}) of a component C of M. Such a C misses z.
- Roots without data: 5,375 at n = 9, where J[N(z) − r] has no near-perfect matching.

**(B) Orientations and multi-pair compatibility** (`tb_compat.py`, 3-connected, n = 9: 5,231 graphs, 25,210 roots, 88,526 data choices).
- 88,522 data choices have a base.
  - The other 4 (d(z) = 8, two graphs) each contain a universal-twin pair in a component of M not containing z.
- **0 compatibility failures**: whenever each pair's disjunction is satisfiable alone, all of them are jointly.
- Hence **every data choice with M connected has a base**, which is the strong form predicted by DL (Prop 7.4).
- Orientations:
  - m = 2: both orientations hold in all 20,052 data choices.
  - m = 3: all four in 45,576 of 45,644.
  - m = 4: all eight in 22,700 of 22,830.
- Order 7, 3-connected: 378/378 data choices have a base.

**(C) The disjunctive condition in arbitrary graphs (Conjecture DL).** Setting: G has one vertex g of positive even degree, and the pairs are disjoint pairs of non-adjacent odd vertices.
- One pair, exhaustive (`disj_general.py … 1`):
  - n = 5: 21 pairs, 3 failures.
  - n = 7: 947 pairs, 14 failures.
  - n = 9: see the final count below.
  - **Every failure is a pair of universal twins** (a, b adjacent to every other vertex, hence to g).
  - At n = 7 every universal-twin pair fails. At n = 9 a minority does.
- Two pairs, exhaustive:
  - n = 7 with one even vertex: 1,404 instances, 0 compatibility failures. The 34 failures each contain a failing single pair.
  - All-odd graphs of order 8 (`--allodd`): 10,850 instances, all satisfiable. There a single pair always succeeds by L1.
- Random (`dl_rand.py`): pairs inside N(g) (the regime where L1* is inadmissible), universal twins skipped, budget 2·10⁶, three seeds. See the table below.
- **The free orientation is used.** At n = 11, one orientation alone fails in 17 of 266 instances at p = 0.4 and in 99 of 286 at p = 0.6.
- **Proposition 7.5** (the exception is needed): in K_{2k+1} minus a perfect matching of K_{2k}, every Lovász decomposition consists of k Hamiltonian paths.

**(C′) Reach of the proved cases** (`TriangleBase.lean`): 3-connected J of order 7 and 9, roots with data.
- m = 2 (11,463 roots):
  - far-apart (Prop 7.1(b), unconditional): 2,491;
  - a ≁ w or b ≁ w (Prop 7.2, conditional on L1\*): 9,575, which includes all the far-apart roots;
  - left over: 1,888 roots where every data choice has a, b ∈ N(w).
- m = 3: packed pairs (Prop 7.1(a)) at 12 of 10,158 roots.
- m = 4: at 0 of 1,265 roots.

**(D) Residual families of T(6)-i** (`t6-dense/scripts/gen_resid.py`, budget 2·10⁶, seeds 7, 11, 13).

| family | graphs | roots | certified | undecided | proved absent |
|---|---|---|---|---|---|
| \|O\| = 8, 6 per shape (∅, K2, P3, K3, C4 TW=2) | 30 | 180 | 178 | 2 (one ∅ graph) | 0 |
| \|O\| = 10, 4 per shape; C4 TW=1, \|O\| = 8, 4 graphs | 24 | 144 | 144 | 0 | 0 |

**(E) Head-to-head against Conj 5.1 / STL-P on the E28 hard graphs.** These are the 8 graphs in which every Conj 5.1 search for 46 roots hit the budget.
- **The triangle base certifies all 48 of their roots.**
  - 42 roots are certified at budget 2·10⁶ with seed 7. This covers every root of the P3 |O|=8, P3 |O|=10 and K3 |O|=10 graphs.
  - The other 6 are certified at budget 2·10⁷ with seeds 7, 11, 13, 17, 19: the ∅ graph at r = 1, 3; K2 |O|=10 at r = 5; `M^~~Zxv^N~RJZujl_` at r = 1, 3, 5. Each took 23–270 s.
- Every lift was verified edge by edge.
- So on the instances where the dense-residual base was out of reach, the triangle base is decided by the same oracle. It is weaker in form, and much easier to find.
- On order-9 dense cores the two bases coexist at every root and data choice, as far as checked: the auditor's `e7dense.py` compared 18 of the 28 cores (108 of 168 roots) before it was stopped (A28).

**(F) The coordinator's budget-undecided roots** (`scripts/out/nobase_budget.txt`):
- n = 13, d(z) = 8, r = 1: base found by exact search with no budget (184 s; also by the auditor at 3·10⁷).
- n = 15 (K2 residual), r = 2: base found at 2·10⁸ (coordinator, `out/recheck_200M.log`).
- n = 15 (K2 residual), r = 1: undecided at 3·10⁷ (A28) and at 2·10⁸. An exact run with no budget is pending; see the final status below.

**(G) The forest base at roots without triangle data** (coordinator's request; `fb_nodata.py`, `fb_exhaustive.py`, `fb_bruteforce.py`).
- **Setting.** Every 3-connected J of order 9 with d(z) ≥ 4 and every root without triangle data: 2,438 roots.
  - Test1 was decided exactly at each root.
  - Forest base search: for each w, up to 30 forest T-joins of J − {z, r} (the T-join inside a spanning tree) and up to 8 rootings.
  - Conditions (i) and (ii) together are exactly route_ext's query C with r_v = {v, p(v)}.
- **Results.**
  - Test1 holds at all 2,438 roots.
  - A forest base was found, and its lift verified, at 2,435.
  - At the remaining 3 roots, the exhaustive check (every w, every forest T-join via T-join + cycle space, every rooting, exact) finds **no forest base**. An independent brute force over all Lovász decompositions of M agrees (735 and 2,100 decompositions).
  - Condition (i) alone is satisfiable at every rooting, so the obstruction is the sibling condition (ii).
- **The counterexamples.**
  - J = `HsaCB~~`, the cone over K_{2,6}, at both degree-7 roots. Hand proof in manuscript Example 4.7: H is a star, the T-join is unique, and sibling leaves are forced onto one path through r.
  - J = `HsaAD~}` (d(z) = 6, N(z) independent), at r = 0.
- **So the forest base conjecture (manuscript Conj 4.5) is false as stated, although Test1 holds at those roots.** At order 7 all 12 roots without triangle data have a forest base.
