# Audit A22c: degree six in terminal-matching (§8: data, chained walk theorem, far-apart form, chain conjecture)

**Scope.** `manuscripts/terminal-matching/terminal-matching.tex`, Section 8 (`sec:six`), the abstract sentence on degree six, and Results item (6). The audit followed the branch while it moved:

- f0ebc7c: data, Definition 8.1, Theorem 8.2, the m-edge remark, the walk3 reach table.
- aada488: Proposition 8.3 (`prop:far`), Corollary 8.4 (`cor:six`), the `d6_reach.py` table.
- 31eadcb: the Lean formalisation `lean/GallaiLean/TerminalMatching3.lean`.
- 66c479c, d864daf, 905636e: y1 removed from Definition 8.1; Conjecture 8.5 (`conj:chains`) with `chain_search.py`.

The final text audited is HEAD **905636e**, and line numbers below refer to it.

**Method.** I re-read the proofs against Lemmas 3.1, 3.3 and 3.4 and the Lean `walk_back`. Everything computational was re-derived with code written for this audit, in `research/audit/A22c-scripts/`:

- `dsolve.c`, an edge-based path-decomposition solver that shares no code with `ptm.c`, `walk3.c` or `stl.c`. `test_dsolve.py` validates it against a naive enumerator: 12,000 random queries with separations, cover sets and special edges, 0 disagreements.
- An independent PTM oracle that works on G directly (a multigraph when a pair is adjacent).
- An independent implementation of Definition 8.1 and of the base test.
- **The proof of Theorem 8.2, executed** (`construct.py`). Every Fan step of Lemmas 3.1 and 3.4 is realised by brute force: a decomposition with end counts b + 1_g − 1_t in which every path lies inside V(Q) + g for an old path Q. This is exactly what Lemma 3.1 guarantees, and all the proof uses. Before each step the script checks the hypothesis that the text claims (Z(g) = ∅, b(t) ≥ 1). After every step it checks each vertex-set claim the text makes. It then merges the leaves and verifies the final decomposition of G independently. Random seeds vary the base decomposition and every Fan step.

I made no commits. Some of the files in `A22c-scripts/` were swept into the coordinator's commits 66c479c and d864daf.

## Verdicts

| Item | Verdict |
|---|---|
| (a) Hypotheses of Lemmas 3.1/3.3/3.4 in the proof of Thm 8.2 | **Correct.** Every hypothesis is verified; the parity claim is right. One ambiguity, N(·) in G or in G − F, is **G1**. |
| (b) Separation tracking, Steps 1–5 | **Correct.** All six pairs are needed and preserved; Q2 is neither leaf path; the three final paths are distinct. No counterexample found. |
| (c) m-edge remark | Plausible, the separations are right, but it is **underspecified** (G2). |
| (d) `walk3.c` | **Correct** for the f0ebc7c Definition 8.1 (N in G, y1 excluded). The independent replica reproduces every number and every base configuration. The label of one row is loose (N4). |
| (e) Data | **All reproduced** (details below). |
| (f) Claims vs logs | **E1** (order-9 reach sentence), **E2** (status of the far-apart case), **G1** (Conj 8.5 / d6_reach / chain_search vs Def 8.1 and Lean), plus NITs. |
| Prop 8.3 | **Correct** (paper and Lean). One wording NIT (N1). |
| Cor 8.4 | **Correct as mathematics** (paper and Lean). Its Test1 part is **not** a case of the open T(6)-i (E2). |
| Conj 8.5 | Evidence reproduced and extended (an exhaustive order-19 family). Its statement does not match the formalised Definition 8.1 (G1). |
| Lean `TerminalMatching3.lean` | Statements match the paper: `AdmChain` = Def 8.1 with N = N_G and y1 free; `FarEnds` and `FarNbrs` = distance ≥ 3; `PTM3At` = terminal at x_i on three distinct paths. Build up to date (`lake build --no-build` reports all targets up to date), no `sorry`, and `PTM3Axioms.lean` prints only `propext`, `Classical.choice`, `Quot.sound`. |

## ERRORS

**E1. Order-9 reach sentence (lines 761–764).**

The text says: "At order 9, 593 … have no simple pairing at all, and 315 more have simple pairings but no base. For the others, and for all but one random graph …, Theorem 8.2 reduces STL(J,z,r) at **every** r ∈ N(z) …"

- "The others" are 1,819 − 593 − 315 = 911 graphs.
- Only 509 of them have every r covered. The coverage histogram, from `d6_cover.py` and reproduced here, is {0: 908, 3: 16, 4: 132, 5: 254, 6: 509}.
- So for 402 graphs the reduction holds at only 3–5 of the six neighbours.

The table itself is right ("509/1819"); only the sentence is wrong.

Fix: "For 509 graphs (every r), and for all but one random graph …; for 402 more, at 3 to 5 of the six neighbours." With the weakened Definition 8.1 the numbers become 523, and 391 = 16 + 133 + 242 (N5).

**E2. The far-apart case is presented as a case of the open T(6)-i. Per the project's own records it is already closed.**

Where:
- abstract, l. 65–67 ("this gives the first deletion test at degree six for such neighbourhoods whenever two suitable walks exist");
- Results (6), l. 160–163 ("the first deletion test at z, the open case T(6)-i, holds as soon as suitable chains exist");
- §8, l. 692–693 ("At degree six this is the first deletion test, the open case T(6)-i, for every J whose six neighbours … far apart");
- l. 729–732 ("Conjecture 8.5 implies the first test at every z of degree six with far-apart neighbours");
- ROADMAP commit 9305ff6 ("test1_of_chains3 (T(6)-i case, conditional on chains)").

Why it is already closed:
- Write B = J − z and U = N(z). Pairwise distance ≥ 3 in B means C = B[U] has no edges and every odd x has |S(x)| = |N(x) ∩ U| ≤ 1.
- **RS isolated root.** Six-even-root-shapes: "Failure requires C − r ∈ {K5, K5 − e, K5 − P3}" (reader-six-even-program.md). Here C − r has no edges, so no root fails.
- **INC Thm 1(2).** Six-even-incidence: "if every |S(x)| ≤ 2, every root passes" (connected B).
- Audit A6 graded these steps SOUND (items I6, I7). STATUS.md §3.5(a) lists "odd vertices with 1–2 even neighbours (six-even-incidence)" among the closures.
- The open residual of T(6)-i has D = K6 − B[U] ∈ {∅, K2, P3, K3, C4}, i.e. B[U] has at least 11 of its 15 edges. That is the opposite extreme from far-apart.

Consequence:
- Corollary 8.4's Test1 conclusion, and the Test1 consequence of Conjecture 8.5, are a new and conditional proof of a known case. This is the same situation as `rem:known` at degree four.
- What is new is the star-terminal decomposition with the three transitions F prescribed (pairing-prescribed STL), now Lean-verified, and the method.
- Caveat: the INC and RS results are external (Nov 26 studies; their code is not in the collection). They were audited in A6.

Required: a remark analogous to `rem:known`, and rewording of the four places above. The mathematics of Cor 8.4 is not affected.

## GAPS

**G1. Which N(·)? y3 on P1.**

What the definition and the code say:
- Definition 8.1 writes N(x3) without naming a graph.
- The formalisation reads it in G, the graph with the F-edges. In `AdmChain.nadj₁'` (TerminalMatching3.lean l. 351), `∀ t ∈ initOf y₂ q₁, ¬ G.Adj t x₃`, with G = `lift3 …` containing x3y3.
- `walk3.c` reads it the same way (`GA` contains the F-edges).
- Under that reading y3 ∈ N_G(x3) can never be an inner vertex of P1.

Three places in the text and scripts contradict that reading:
1. l. 577: "P1 may pass through y3" is false under the formalised definition.
2. Conjecture 8.5 puts P1 in H − N_H[x2] − N_H[x3], which contains y3. So "These are exactly the admissible chains with y1 = r" (l. 729) is false for Lean's `AdmChain`. And "by Corollary 8.4, Conjecture 8.5 implies the first test" does not follow from `test1_of_chains3` as stated.
3. `d6_reach.py` (`N3 = set(H[x3])`) and `chain_search.py` (`N3 = H[x3] | {x3}`) also allow y3 on P1. So:
   - l. 746–748 ("[d6_reach.py] use[s] the earlier, stricter form … so their counts are lower bounds") is not accurate on this point;
   - `chain_search.py` does not use "the definition as stated" in the Lean sense.

The paper proof is fine with N(·) taken in G − F:
- In H the edge x3y3 is absent, so y3 ∉ N_H(x3).
- The Z-check of Step 4 only needs adjacency in H.
- I executed the proof with this relaxation: 0 failed claims in 15,009 runs at order 9 and 13,065 at order 11.
- Among 3,604 PEE failures, none has a relaxed chain with a base (table below).

Fix, either way:
- (a) Read Definition 8.1 with N_{G−F}, i.e. exempt y3 from p_i ∉ N(x3), and weaken `nadj₁'` to `t ≠ y₃ → ¬ G.Adj t x₃` (or use adjacency in G − F), adjusting the Z-check in `ptm3_of_base`.
- (b) Keep N_G: delete "P1 may pass through y3", add "− y3" to the P1 graph of Conjecture 8.5, and make `chain_search.py` and `d6_reach.py` strict.

Data impact: none found. Strict and relaxed coverage coincide in every family tested:
- order-19 exhaustive family: 1,000/1,000 both;
- own private-neighbour family: 220/220 both;
- own random far-apart J: 5 at order 41, 21 at 51, 68 at 101, all covered both ways;
- at order 51, two of the relaxed greedy chains used y3 on P1, but strict chains existed for the same r.

**G2. The m-edge remark (l. 643–645) is underspecified.**

The separations it lists are the right ones: I redid the tracking for general m. But "the same argument" leaves out:
1. the order of the walks: P_{m−1}: y_m → x_{m−1} first, …, P_1: y_2 → x_1 last;
2. x_i ∉ V(P_j) for i ≠ j (x_j only as the last vertex of P_j);
3. y_i ∉ V(P_j) for all j ≥ i ≥ 2 (y_i must not be a Fan target before its leaf is attached; this is the analogue of y2 ∉ V(P2), which the proof needs);
4. edge-disjointness of all the walks;
5. the start condition y_{j+1} ∉ N(x_i) for i ≥ j + 2 (the analogue of y2 ∉ N(x3));
6. the base graph.

"What remains" (3) cites the remark, so it should be stated as a definition, or called a sketch.

## NITS

- **N1** (l. 659). "Adjacency in M is adjacency in G − F, except for the edge ℓ1y1" should read "M is a subgraph of (G − F) + ℓ1y1", since the walk edges are deleted. The conclusion is unaffected; Lean `hMss` proves the inclusion.
- **N2** (l. 547, 555). "PTM_3 and PTM(G,F;e@x) … hold" should say PTM(G,F), because PTM_3 is the universal statement. The italic "In short: … every pairing of N(z) satisfies PTM_3(r)" states an empirical finding as a fact; add "in all computed cases", as Results (6) does.
- **N3** (abstract, l. 64). "a chained walk theorem reduces it [every pairing]": the theorem covers simple pairings only. Multigraph pairings are 24,328 of the 27,285 instances at order 9.
- **N4.** The walk3 row "no admissible chain" counts instances where no configuration has both walks *individually*; edge-disjointness is not checked. Recounting with edge-disjointness gives identical numbers at every order, so only the label is loose.
- **N5.** The walk3 table under the weakened Definition 8.1 (y1 free, N in G), computed here with the same shortest-chain search:

  | Order | With a base | No chain | J with every r covered |
  |---|---|---|---|
  | 9 | 2,320 (was 2,269) | 103 (was 120) | 523/1,819 (was 509) |
  | 11 | 1,372 | 1 | 199/200 |
  | 13 | 1,669 | 1 | 200/200 |

  With N in G − F as well, order 9 gives 2,407 and 567/1,819. With chains of every length as well, it gives 2,529 and 613/1,819. With the old definition, chains of every length add nothing at order 9 (still 2,269 and 9,457).
- **N6** (l. 765–768). The cross-check used "a scratch copy of ptm.c" that is not in the repo. I reproduced it independently: 207 simple PEE failures with 54 distinct (graph, short set) keys, none with a base even when chains of every length are allowed. Moreover, each of the 9,457 base configurations yields an explicit, verified decomposition through the executed proof. The remark "about 80 would be expected by chance" was not checked.
- **N7.** `out/chain_search_halves.log` does not record BRIDGES, so "joined by 2 or 4 edges" can be checked only against the commands in E24(J).
- **N8.** In `d6_reach`'s far-apart frequencies, orders 21–51 replicate within noise (mine: 0/200, 0/200, 5/200 at 41, 21/200 at 51; theirs 15/200 at 51). At order 101 the samples are:

  | Source | Far-apart | Rate |
  |---|---|---|
  | My own generator, four runs | 161/620 | 26% |
  | networkx `configuration_model`, as in `d6_reach.py` | 105/320 | 33% |
  | `d6_reach.py` | 69/200 | 34.5% |

  The two generators have the same distribution (uniform stub pairing, rejection of loops and multi-edges, the same 3-connectivity filter; `far_freq.log`). The gap is about 2σ, so probably sampling noise. In every far-apart graph, every r had a chain under both readings. The table is descriptive only.

## (a), (b): the proof of Theorem 8.2, checked step by step

The text's verification of each lemma hypothesis holds. These are the points I checked in particular.

**Parity.**
- In M, x1 loses 2 (x1y1 and the end of P1).
- x2 and y2 each lose 2.
- y3 loses 2, or 4 if it is on P1 in the relaxed reading.
- y1 loses 1 and gains 1 (ℓ1), plus 2 per walk passage.
- Inner vertices lose 2 per walk.
- x3 loses 1.
- So x3 is the only vertex that can have positive even degree. The walk vertices keep odd, hence positive, degree, so "isolated in M" means x3 or isolated in G.

**Step 2** (Lemma 3.4 in K = M + ℓ3y3 + E(P2)).
- The endless vertices of D1 are x3, y3 and isolated vertices.
- y3 = w0 is exempt; x3y3 ∉ K; (i) covers q_i for 0 < i < s.
- x2, y2, x1 and the leaves have ends during the walk.
- x2 needs no condition: it is only a source, at the last step.

**Step 3.**
- y2 ∉ T2, so it keeps its end.
- Q2 ⊆ V(R) ∪ T2 for the D1-path R through y2.
- R ≠ Q3ℓ3 because of {y2, y3}, and R ≠ Q1 because of {ℓ1, y2}.
- So Q2 avoids x2 ({x2, y2}, and x2 = q_s ∉ T2), ℓ1 and ℓ3.

**Step 4** (Lemma 3.4 in H).
- The endless vertices are x3, x2, y2 and isolated vertices.
- p0 = y2: x2y2 ∉ H, and y2 ∉ N(x3) by (ii); (ii) covers the inner vertices.
- The containments for the three leaf paths, and the exclusions x3, ℓ1, ℓ2 / x2, ℓ1 / x1, follow exactly as written.

**Step 5.**
- H = K′⟨x3, y3⟩, K′ = K″⟨x2, y2⟩, K″ = G⟨x1, y1⟩.
- A merge renames only its own leaf, so later merges remain allowed.
- A path that ends at x_i and contains x_iy_i has x_iy_i as its terminal edge.

**Executed proof.** No claim failed in any run:

| Instances | Runs |
|---|---|
| Order 9, every base configuration (shortest chains, 3 seeds) | 28,371 |
| Order 9, chains of every length | 24,854 |
| Order 11 | 26,208 |
| Order 13 | 10,750 |
| Order 19 far-apart family (strict and relaxed) | 12,000 |

**Conditions of Definition 8.1: which are needed.** "Proof breaks" means the executed proof hits a false claim. "Theorem fails" counts PEE failures, i.e. failures of the conclusion of Thm 8.2, that have such a chain with a base. These are actual counterexamples to the weakened theorem. They come from 3,604 simple PEE failures: all 207 at order 9 for d6, all 130 for all-odd connected G at n = 6, and 3,267 from the first part of the n = 8 list (that run was stopped).

| Condition dropped | Proof breaks | Theorem fails |
|---|---|---|
| y1 ∉ V(P1), V(P2) | no (15,368 runs) | 0 (now dropped in the text: correct) |
| N(·) in G − F (y3 on P1) | no (15,009 runs) | 0 |
| y2 ∉ N(x3) | Z(y2) ∋ x3 | 177 |
| p_i ∉ N(x2) | Z ≠ ∅ | 74 |
| p_i ∉ N(x3) | Z ≠ ∅ | 109 |
| q_i ∉ N(x3) | Z ≠ ∅ | 326 + 32 (order 9) |
| x1 ∉ V(P2) | ℓ1-path contains x1 | 2 |
| y2 ∉ V(P2) | y2 ∈ T2 | 0 found |
| any one of the six separations | a claim fails each time (`sep_drop.log`) | not tested |

So no condition is missing. The y1 conditions were the only unnecessary ones, and the N_{G−F} reading is also safe. My earlier finding that the y1 conditions are unnecessary is now resolved by the weakening. **No other finding depends on the y1 conditions.** E1 is a statement about the table; its numbers shift slightly under the new definition (N5) but the error stands.

## (d) `walk3.c`

- `ok1` and `ok2` implement (i) and (ii) of the f0ebc7c definition literally, with neighbourhoods in G (`GA` includes F).
- The last vertex is exempt; y2 ∉ N(x3) is checked in `main`.
- F-edges are excluded (`isF`); edge-disjointness is enforced through `used2`.
- `try_base` builds M = G − F − E(P1) − E(P2) + ℓ1y1, checks the parity, and passes the six pairs {x1,ℓ1}, {x2,y2}, {x3,y3}, {ℓ1,y2}, {ℓ1,y3}, {y2,y3} to `sepq` with N = gn + 1 and profile = degree parity.
- "Shortest" means: P2 of the least constrained length, then P1 of length at most its own least constrained length computed without P2, and edge-disjoint from P2.
- `d6_cover.py` parses the BASE lines correctly: covered r = F minus the short ends.

My replica (`reach.py`) agrees exactly with `walk3_d6_*_all.txt`:
- identical sets of base configurations: 9,457, 13,104, 21,240, 41,268 and 57,257;
- identical instance counts, no-chain counts and coverage histograms;
- identical numbers of base tests (25,391 at order 9, and so on).

## (e) Data, re-derived

- **J counts.** Order 7: 7; order 9: 1,819. Two independent routes agree: `geng -c -d3 n` with my own filters and 3-connectivity test, and `geng -c (n−1)` read as J − z. The canonical-label sets equal the repo's `d6_*.g6`.
- **Instances.** 105 and 27,285, with 95 and 24,328 having an adjacent pair. Simple pairings: 10 and 2,957. Graphs with no simple pairing at order 9: 593.
- **Random J files.** All are 3-connected with the stated degrees. Simple pairings: 1,375, 1,673, 2,614, 2,881. Pairings with a parallel pair: 1,625, 1,327, 1,886, 1,619.
- **PTM(G,F) and PTM(G,F; e@x), own exact oracle, no budget.**
  - Order 7: all 105 instances.
  - Order 9: **all 27,285 instances, 163,710 tests, 0 failures**.
  - Orders 11, 13, 15, 17: all 3,000, 3,000, 4,500 and 4,500 instances, 0 failures.
  - The three order-17 queries that `ptm.c` left undecided at 2·10⁶ are decided positively at once. The text's order-17 claim, now "nothing undecided" after the 10⁸ re-run, is therefore confirmed.
- **PEE at order 9.**
  - Simple instances: exactly 207 failures in 23,656 tests (54 keys).
  - All instances, every 10th graph: 114 failures in 21,840 tests (0.52%), against the repo's 1,156 in 218,280 (0.53%). The full multigraph PEE count was not recomputed.

## Prop 8.3, Cor 8.4, Conj 8.5

**Prop 8.3.** Checked line by line. It is also checked computationally, for every chain used on the far-apart instances (`check_sparse_hyp`):
- X = {x1, x2, x3, y2, y3, ℓ1} is sparse in M;
- the four sets are packed;
- x3 is the only even vertex.

dsolve found the separating decomposition in every order-19 case (12,000), and in 27 of 32 cases at orders 41 and 51. The other 5 hit the solver budget; they are not counterexamples, since `separation_sparse` guarantees existence.

**Cor 8.4.** The un-lift is fine, and `test1_of_stl` only needs degree ≥ 3 at N(z). As mathematics it is correct; for its status see E2.

**Conj 8.5.** Besides G1 (the P1 graph should exclude y3, or Definition 8.1 should be read in G − F):
- **Exhaustive order-19 family.** This is the least possible order with all degrees in N(z) equal to 3: z, the six v_i, private pairs, and any 2-regular graph on the twelve private vertices. It gives 71,829 labelled 3-connected J, **1,000 up to isomorphism**. Every r is covered, always with r = y1, in both the strict and the relaxed form (`conj19.log`).
- **Ring of six triangles** (order 19): covered.
- **Own private-neighbour random family** (orders 19–23 with private degree 3, and order 19 with private degree 5): 220/220, always with r = y1.
- **Own random far-apart J:** 5 at order 41, 21 at 51, 68 at 101, every r covered.

## Scripts and logs (`research/audit/A22c-scripts/`)

| What | Scripts | Logs |
|---|---|---|
| Solver, wrapper, verifier | `dsolve.c`, `dlib.py`, `test_dsolve.py` | `test_dsolve.log` |
| Generators and recounts | `count_J.py`, `count_random.py` | `count_J.log`, `count_random.log` |
| Own PTM oracle | `ptm_check.py`, `und17.py`, `pee_general.py` | `ptm7.log`, `ptm9_all_s4*.log`, `ptm9_simple_all.log`, `ptm9_pee_s10.log`, `ptm_r11/13/r15_s3*/r17.log`, `und17.log`, `pee_gen6.log`, `pee_gen8_partial.log` |
| Definition 8.1, base test, reach | `chain.py`, `reach.py` | `reach_walk3.log`, `reach_variants.log` |
| Executed proof | `construct.py`, `construct_run.py`, `sep_drop.py` | `construct_d6_9.log`, `construct_random.log`, `sep_drop.log` |
| Counterexample search | `thm_check.py` | `thm_check_d6_9.log`, `thm_check_general.log` |
| Far-apart and Conj 8.5 | `far_check.py`, `far_freq.py`, `far19_exec.py`, `conj_check.py`, `conj19.py` | `far_check*.log`, `far_freq.log`, `far19_exec.log`, `conj19.log`, `conj19_canon.txt`, `conj_priv.log` |

## Required corrections

1. **E1:** fix the order-9 sentence at l. 761–764.
2. **E2:** add a `rem:known`-type remark at degree six (the far-apart Test1 case is closed by six-even-incidence Thm 1(2) and the RS isolated-root lemma; the open residual has B[U] nearly complete). Reword the abstract (l. 65–67), Results (6) (l. 160–163), l. 692–693 and l. 729–732, and the ROADMAP line.
3. **G1:** make Definition 8.1, the remark at l. 577, Conjecture 8.5, `d6_reach.py`, `chain_search.py` and Lean `AdmChain.nadj₁'` agree on whether y3 may lie on P1. Either read N in G − F and weaken Lean, or exclude y3 from P1 in the conjecture and the scripts. Then fix l. 729 ("exactly the admissible chains") and l. 746–748 ("lower bounds").
4. **G2:** state the m-edge chain explicitly, or label the remark a sketch.
5. **NITs N1–N8.** The most useful are N1 (wording in the proof of Prop 8.3) and N5 (update the walk3 table to the weakened definition, or say clearly that it uses the old one).
