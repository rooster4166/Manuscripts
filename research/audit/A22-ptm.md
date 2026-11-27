# Audit A22: "Two terminal edges at once" (terminal-matching, branch `claude/ptm`)

Audited: `manuscripts/terminal-matching/terminal-matching.tex` (compiled numbering used below:
Thm 1.1, Def 1.2, Ex 2.1–2.2, Conj 2.3–2.4, Lemma 3.1 Fan, Thm 3.2 sparse separation, Lemma 3.3
lift/merge, Lemma 3.4 walking back, Def 4.1, Thm 4.2, Remark 4.3, Lemma 5.1, Thm 5.2, Thm 6.1,
Thm 7.1, Cor 7.2), `lean/GallaiLean/TerminalMatching.lean`, `scripts/` and `scripts/out/`,
E24 (experiments.md) and §Z (connections.md). Audit scripts: `research/audit/A22-scripts/`.
Nothing under audit was modified.

*Post-audit note.* This report audits the text as of commit 09ce96a. While the audit was running,
commit 53093b4 applied the corrections of §6. I spot-checked items 1–7 in the current tex and all
are addressed. The cleaned-up `TerminalMatching.lean` still elaborates and prints the same axioms
(`A22Axioms.lean`, re-run).

**Verdict.** The mathematics is correct: Theorems 4.2, 5.2, 6.1, 7.1, Corollary 7.2 and Lemmas
3.4, 5.1 are sound, and the Lean statements say what the paper says (sorry-free, standard
axioms only). Every table entry I recounted matches, and an independent brute force reproduces all
the exhaustive simple-graph data at n ≤ 8 exactly. Corrections are needed in the *claims around*
the theorems. (1) The abstract claims n ≤ 10 for two edges, but the n = 10 run is still pending.
(2) Three citations to [STL] give the wrong numbers. (3) "The only known failure of
pairing-prescribed STL" is false without "3-connected". (4) Some summary sentences drop the K4
exception. (5) The base separation problem is called "a case of" an open question with no
counterexample, but the paper's own NOBASE data are failures of the base problem. No ERROR in any
proof.

## 1. Statements

**Thm 1.1 (prescribed end edge, cited [MS]). SOUND.** Background (MS Theorem 14, formalised).

**Def 1.2 and the PEE remark. SOUND.** Def 1.2 is a definition. That PEE₂ is false is confirmed
independently: 36/824 prescribed-end assignments fail at n = 6 and 420/52,100 at n = 8. The stated
reason ("force the edge between them into a single transition at both ends") is only a heuristic.
A contradiction needs more, e.g. a common neighbour of the two ends, which gives a closed transition
w a x w. Suggest: "(e.g. if they also have a common neighbour, the transitions close a triangle)".
Cite as [STL, §6, Table 3] (or E22(F)), not "[STL, E22(F)]".

**Ex 2.1 (K₄). SOUND.** 6 edges and 2 paths of length ≤ 3, so both are Hamiltonian. The
argument is complete. Confirmed by exhaustive search: all 3 perfect matchings of K₄ fail, and so
does every e@x. G − F = C₄ and J = W₄ with the diagonals are correct.

**Ex 2.2 (prism) and the next paragraph. SOUND.** The cited Lemma 3.1 of [STL] (deleting z) gives
|D'| = |D| + #LL − #SS ≤ 3, since a star-terminal decomposition has LL = 0. The direct argument is
simpler: removing terminal F-edges never splits a path. Brute force confirms PTM(prism, rungs)
fails (EUxo with F = {03, 14, 25}; G − F is two triangles).

**Conj 2.3. SOUND (consistent with the data).**
- Checked directly from `s_*.txt`: every PTMFAIL with m = 3 and every RFAIL (m = 2, 3, 4) has
  GFconn=0. The only PTMFAILs with GFconn=1 are the three K₄ lines (s_4_2).
- "|F| = 2 even when G − F is disconnected": the only m = 2 failures at n ≤ 8 are K₄. At n = 10,
  7/24 chunks are done (1.01M classes), with 0 failures so far.
- Caveat: ptm runs the e@x tests only on PTM-positive instances (52,924 = 13,231 × 4; 84,732 =
  14,122 × 6). So K₄, a PTM(e@x) failure with G − F connected, is never counted as one.
  Conj 2.3 excepts it correctly. Three places do not:
  - abstract: "for a prescribed end, every failure has G − F disconnected";
  - Results (1): "PTM_m(r) holds whenever G − F is connected";
  - Table 1 caption.

  Each needs "(other than K₄)" or "among instances where PTM holds".

**Conj 2.4 and the implication paragraph. SOUND (consistent).**
- `analyze.py`, and independently `cmp_multi.py` (networkx articulation points): every pc_6/pc_8
  failure has κ(G') = 1 and κ(J) ≤ 2. The only exception is K₄ (C], κ(G') = 2, κ(J) = 3).
- Every failure other than K₄ has at least one pair parallel to a G'-edge.
- "J 3-connected ⇒ J − z 2-connected ⇒ STL-P" is correct in that direction. But §Z.1's
  "2-connected G − F, i.e. 3-connected J" is not an equivalence.
- "Conjecture 6.4" of [STL] is Conjecture 7.4 in the current stl.tex.

**Lemma 3.1 (Fan with vertex sets). SOUND.** It matches `fan_single_supp`: u = g gains an end,
v = t loses one, and Z is taken in K − gt. It also matches [RD, Lemma 2.2] (checked: that is
Lemma 2.2 of route-descent.tex).

**Thm 3.2 (sparse separation). SOUND.** It matches `separation_sparse`/`SparseFam`. "Sparse"
includes vertices of X themselves, as in Lean.

**Lemma 3.3 (lift and merge). SOUND.** It matches `PathDecomp.liftLeaf` and `leaf_merge`:
`apex (delEdge G u x) {u}` is (K − xy) + ℓy.

**Lemma 3.4 (walking back). SOUND.**
- Fan steps: at step i the target is w_i and the source is w_{i+1}. Before step i the end counts
  are b_D + 1_{w_0} − 1_{w_i}.
- So the only new zero is at the target itself, w_0 has gained an end, and w_{i+1} still has
  b_D(w_{i+1}) ≥ 1. This uses the hypothesis, because w_{i+1} is adjacent to w_i and differs
  from w_0.
- So Z(w_i) = ∅ < b(w_{i+1}) at every step.
- The Lean proof follows the same induction (recursion on the list, `delChain`).

**Def 4.1 and the parity paragraph. SOUND.**
- Degree changes in M: a, y and the inner vertices lose 2 each; b loses 1 and gains 1; x loses 1.
  The case k = 1 is the same.
- A vertex of degree 0 in G stays at degree 0. So x is the only vertex that can have positive even
  degree, and d_M(x) = d_G(x) − 1 is even (possibly 0).
- This is `baseG_parity`.

**Thm 4.2 (walk theorem). SOUND.** I checked every moment of the proof.
- **D₀ on M.** Zero ends only at x and at vertices isolated in G. Every v ≠ x with d_G(v) > 0
  has odd d_M(v), hence one end. This includes y, a, b and every vertex of P: d_M(y) = d_G(y) − 2
  is odd and d_G(y) ≥ 3.
- **D₁ (Step 1).** Q_y exists because d_M(y) is odd. Zero ends: x, y, G-isolated vertices.
  Q_y avoids x and ℓ₁ by hypothesis. So {x,ℓ₂}, {ℓ₁,ℓ₂}, {a,ℓ₁} are separated.
- **Step 2, first step** (target y, source p₁). N(y) in M + ℓ₂y is ℓ₂ (1 end) and
  N_G(y) − {x, p₁}, all with one end. So Z(y) = ∅ and b(p₁) = 1 (= b(a) if k = 1).
- **Intermediate step i** (target p_i, source p_{i+1}). Zero ends: x, p_i, G-isolated vertices.
  So Z(p_i) = ∅: x ∉ N_H(p_i) by admissibility (i > 0) or because xy was deleted (i = 0), and
  G-isolated vertices are adjacent to nothing. b(p_{i+1}) = 1.
- **Last step** (target p_{k−1}, source a). b(a) = 1, untouched until then.
- **End of Step 2.** Zero ends exactly at x and a (and G-isolated vertices), as stated. Remark 4.3
  is right that both have even degree in H.
- **Separations.** The targets p₀,…,p_{k−1} avoid x (x ∉ P), a (P is simple) and the leaves. New
  paths lie in an old path plus the target, so all three separations survive.
- **Step 3.** The first merge needs {x,ℓ₂}. The second needs {a,ℓ₁} in D₃, which transfers
  because the merge only renames ℓ₂ → x and x ∉ {a, ℓ₁}. End counts: a gets 0+1, x gets 0+1, the
  rest are unchanged.
- **Distinctness.** The only preimage of ba in K is bℓ₁, so a common path would put ℓ₁ and ℓ₂ on
  one path of D₂.
- *Minor exposition (no gap in substance).* "A vertex with no end in D₁ is x, y, or isolated"
  should read "isolated in G". The proof also uses, without saying so, that no vertex of P is
  isolated in M (parity). Lean argues this through G-degree parity (`hZH`).

**Remark 4.3. SOUND.**

**Lemma 5.1. SOUND.**
- In K − gv: g has odd degree (d(g) is even and ≥ 2 because v ∈ N(g)). v had odd positive degree
  in K, so it is now even (possibly 0) and is the only possible positive even vertex.
- Every neighbour of v in K − gv keeps its odd positive degree, so Z(v) = ∅ and b(g) = 1.
- End counts after the Fan step: b(v) = 1 (odd) and b(g) = 0 (even), as required.

**Thm 5.2. SOUND.**
- The parity claims are correct (see Def 4.1).
- Packedness and sparseness are required in the same graph (M, or M − xv). The proof uses this,
  and so does `SparseFam`.

**Thm 6.1 (girth five). SOUND.** Every case checked by hand.
- **Admissibility** (b ∈ P, x ∈ P, p_i ~ x): each gives a shorter walk, or a triangle when i = 1.
- **Short distances:** b ~ x gives the 4-cycle a y x b, and b ~ y gives the triangle a b y.
- **Sparseness:** b has exactly one X-neighbour (ℓ₁). For v ≠ b with two neighbours in
  {x, y, a}:
  - v ~ x, y: triangle.
  - v ~ y, a: triangle (k = 1), or the 4-cycle y v a p₁ with v ≠ p₁ (k = 2).
  - v ~ x, a:
    - k = 1: 4-cycle. This also needs v ≠ y, which holds because ya ∈ E(P) is not in M. Say so.
    - k = 2: the allowed 5-cycle a v x y p₁. Its v is unique (two would give a 4-cycle) and lies
      outside X.
- **Packedness of the three pairs:** correct, and preserved in M − xv.
- **Orientation u = b:** the relabelling (a,b,x,y) := (w, w', a, b) with the reversed path
  satisfies the same minimality. The four Lean branches of `ptm2_girth5` match.
- **Computation (`girth5proof.py`):** all 7,616 cases at n = 6–12 (all orientations, all
  shortest walks) are admissible and satisfy the sparse hypotheses.
- **GAP (minor), the sentence "PTM₂ and PTM₂(r) hold for all graphs of girth ≥ 5 with all degrees
  odd".** This needs the two edges in one component (as the theorem assumes). Otherwise apply
  Thm 1.1 in each component. Add one clause.

**Thm 7.1. SOUND.**
- The un-lifts are legal: z is isolated in J*, the paths are distinct, and unlifting cd changes
  only the cd-path.
- Star-terminality and the long-side or length-two alternative are correct.
- Lean (`stl_of_ptm2`) does not even need z to be the only even vertex.

**Cor 7.2. SOUND.**
- The labelling argument is correct; Lean handles it with the seven `liftJ` identities e1–e7.
- The reachability hypothesis is in fact removable: if a, c lie in different components of J*,
  Thm 1.1 applies componentwise. It is harmless.

**Girth criterion after Cor 7.2. SOUND.**
- Case analysis: cycles of length ≤ 4 through ab alone need d_{J−z}(a,b) ≤ 3. Through both ab and
  cd they are exactly a b c d or a b d c, i.e. a sum of distances equal to 2.
- `girthcrit.py`: 2,533 random tests, 0 mismatches.

**§8 claims (computations).** SOUND except the abstract's n ≤ 10 (see §3).

**§9 item 4 (EE). GAP (minor).** PTM(G,M; uu'@u) gives EE at u only if the complementary pair is
also non-adjacent. Otherwise G is a multigraph, which is outside Def 1.2 and Thm 4.2. So "a full
proof of PTM₂(r) would settle the open case of EE at d(z) = 4" overclaims. It holds for u having a
pairing {uu', cd} with uu', cd ∉ E(J), or with the multigraph PTM.

## 2. Lean (`TerminalMatching.lean`)

**Build and axioms.**
- No `sorry`/`admit`/`axiom`/`native_decide`.
- `lake env lean GallaiLean/TerminalMatching.lean` re-elaborates from source in 22 s, exit 0.
  Only deprecation and linter warnings: `if_neg`/`if_pos`, `length_bypass_le`,
  `isPath_iff_eq_nil`.
- `PTMAxioms.lean` and my extended `A22-scripts/A22Axioms.lean` add `walk_back`,
  `sep_sparse_fix`, `baseG_parity`, `ptm2_girth_core` and `test1_of_stl`. They print only
  `[propext, Classical.choice, Quot.sound]`.

**Statements vs manuscript.**
- `walk_back` = Lemma 3.4. The hypothesis is quantified over `initOf` = w₀…w_{k−1}, with v ≠ w₀
  (same as the paper).
- `baseG` = ((G − ab) + ℓ₁b) − xy − E(P), with ℓ₁ = `none`. `leafG` = `apex (G − ba) {b}`.
- `ptm2_of_base` = Thm 4.2. The path is a `Nodup` `ChainAdj` list y::q ending at a, with b, x ∉ it
  and `hZ` only for interior vertices (t ≠ y, t ≠ a). The three `Separates` are exactly the pairs
  {x,y}, {a,ℓ₁}, {ℓ₁,y}. No hypothesis is stronger than the paper's.
- `PTM2At G a b x y` (Lovász ends; P₁ ≠ P₂; P₁ has end a and contains ab; P₂ has end x and contains
  xy) means "ab terminal at a, xy terminal at x, different paths":
  - a path ending at a and containing an edge at a has it as its terminal edge;
  - P₁ ≠ P₂ as `GPath` values means distinct list entries, because every path has an edge and
    edges are `Nodup`.
- `sep_sparse_fix` = Lemma 5.1. `ptm2_of_sparse` = Thm 5.2: `v ∉ baseX` excludes ℓ₁, and
  `SparseFam` bundles packedness.
- `NoTriangle`, `NoSquare` are correct. Simple-graph adjacency forces consecutive vertices to be
  distinct; u ≠ w and v ≠ t make the 4 vertices distinct.
- `ptm2_girth5`: hypotheses are no positive even vertex, no C₃/C₄, reachability, disjointness.
  The conclusion is `PTM2At G a b c d ∨ PTM2At G a b d c`, as in Thm 6.1.
- `swapG K z c d` = K − zc − zd + cd. `liftJ` = two swaps, which equals (J − z) + ab + cd given
  `hN`; `stl_of_ptm2` proves that z is isolated.
- `STL`/`StarAt`/`LongAt`/`HasShortShort`/`Test1` are the library definitions and match the paper.
- `stl_of_girth5`, `test1_of_girth5` = Cor 7.2. Hypotheses are satisfiable (non-vacuous): take
  the Petersen graph minus two disjoint edges ab, cd, plus z joined to a, b, c, d.

**Cosmetic.**
- The module docstring mentions a non-existent `base_of_fix`.
- `liftG`, `liftG_comm`, `liftG_swap` are unused.
- The deprecated names will break on the next Mathlib bump.

## 3. Computations

Independent checker `A22-scripts/bf.py`.
- Written from scratch: it builds Lovász decompositions of G itself path by path, from each
  unfinished vertex. It does not go through J.
- Pruning: failure memo, a component test, and the degree bound d(v) ≤ 2P − [v needs an end].
- Constraints: forced terminal edges (vertex-level, or edge-level for multigraphs), forbidden end
  pairs, separated pairs.
- Every witness is re-verified.

PTM(G,F) holds iff some short-end assignment is feasible with no path joining two short ends;
e@x and PEE are read off the same 2^m assignments.

| check | result |
|---|---|
| `cmp_ptm.py`, simple, all instances, n = 4, 6, 8, m = 2, 3, 4 (geng -c) | all six SUMMARY rows (inst, ptm_fail, r_tests, r_fail, pee_tests, pee_fail) and the exact sets of PTMFAIL/RFAIL lines **identical** to `s_*.txt` (e.g. n = 8, m = 3: 14,077 / 1 / 84,456 / 13 / 112,608 / 3,259) |
| girth ≥ 5, n = 6, 8, 10 (geng -ctf) | 4 + 20 + 221 instances, 980 e@x tests, 0 failures, matches `g5_*` |
| multigraph n = 4, 6 (`cmp_multi.py`) | identical to pc_4/pc_6 (6 and 299 instances, 236 with parallel pairs, 1 and 16 failures). Only K₄ lacks a cut vertex |
| multigraph n = 8 | identical to pc_8: 76,327 instances, 65,712 with parallel pairs, 28 PTMFAIL and 1,926 RFAIL, same sets. Every one has a cut vertex in G' |
| K₄, prism | both fail by exhaustive search (inside the rows above) |
| iso classes n = 8 (`isocount.py`, orbit counting with networkx automorphisms) | 13,025 instances → **3,913** classes = `iso8_2.txt`. Validates the encode/labelg/decode reduction |
| n = 10 iso classes, chunk f2_00 (144,775 classes, all, `cmp_f.py`) | all 144,775 positive (PTM and every e@x), 0 disagreements with `f2_00.out` |
| walk reach (`walkcheck.py`, own walk enumeration and base graphs) | n = 6: 206 / 1 / 160 / 31; n = 8 with excess 3: 13,025 / 68 / – / 3,093. n = 8, base hypothesis: a random sample of 400 instances (`walksample.py`) agrees instance by instance with `walk_8_0.txt` (380 base, 20 NOBASE). The full n = 8 base recount (`walkcheck.py 8 0`) was stopped after 48 CPU-minutes. `walk 0 1` and `walk 3 1` re-run: 2,288 and 3,093 (these outputs are not saved in `out/`) |
| consistency (theorem checks) | at n = 6 (base and sparse) and n = 8 (sparse, excess ≤ 3), every success for (a,b,x,y) has the assignment (a, x) feasible by bf; sparse ⇒ base always; 0 violations |
| random undecided (`out/rnd_und_*.in`, 120 instances, `und_bf.py`) | `ptm` left these undecided. bf decides 82 of them as positive for PTM and every e@x (all 23 with m = 2, 39/40 with m = 3, 20/57 with m = 4). One m = 3 instance (``OAdCiI?HMc@?KqaKB`laP``) is still open after 8 × 120 s, and the rest were not reached. No failure found |

`ptm.c` is a verbatim copy of `tools/stl.c` (`extend`, `prune_ok`, `solve`, `classify`, `term_ok`
are byte-identical), and its independent verifier is genuinely independent. The `.inc` files in
`scripts/` are tracked but not used by any build.

**The n = 10 claim (ERROR in the abstract).** The abstract says "for two edges, K₄ is the only
failure among all instances on at most 10 vertices". Table 1, E24(B) and §Z.1 all say *pending*.
At audit time 7/24 chunks were finished (≈1.01M of 3,474,599 classes, 0 failures). Either state
n ≤ 8 (plus partial n = 10), or wait for the run.

**"Case of the class-separation questions … where no counterexample is known" (§8, UNCLEAR).**
- With shortest walks, the base hypothesis fails for every orientation in 832 instances at n = 8
  (NOBASE lines). 764 of them have an admissible walk, so the base problem as stated has
  counterexamples.
- It is an instance of MS's packed-pair question only when the three pairs are packed in M.
- `packedbase.py`: n = 6: 200 of 1,298 base graphs have packed pairs. n = 8: 11,810 of 85,608.
  All of them are separable, so the packed version has no counterexample here.
- Rephrase: "When the three pairs are packed, this is a case of …".

## 4. Literature and attribution

- Lovász [L68] strong form, Fan [Fan05] (JCTB 93 (2005) 117–125) and the vertex-set version
  [RD, Lemma 2.2] are used correctly.
- Sparse separation [MS] (MS Thm 21 / `separation_sparse`) is used within its hypotheses.
- [PE, Lemma 4.1] (protected end) and [PE, Theorem 5.1] (one common neighbour) are correct.
- [STL, Theorem 3.2] (criterion ⇒ T1) and [STL, Lemma 3.1] (deleting z) are correct.
- **Wrong numbers** (current stl.tex, compiled):
  - [STL, Proposition 3.4] → **Proposition 4.4** (3.4 is a corollary);
  - [STL, Example 3.7] → **Example 4.5**;
  - [STL, Conjecture 6.4] → **Conjecture 7.4**.
- **Overclaim (ERROR, Results (1)).** W₄ is called "the only known failure of the
  pairing-prescribed form of STL". The prism (m = 3), the order-8 m = 3 failure and the 28
  multigraph failures at n = 8 are all STL-P failures of their J. Correct: "the only known
  failure with J 3-connected".

## 5. Summary of grades

| item | grade |
|---|---|
| Thm 1.1, Def 1.2 (PEE remark) | SOUND (heuristic explanation; citation form) |
| Ex 2.1 K₄, Ex 2.2 prism | SOUND |
| Conj 2.3 / data consistency | SOUND (consistent); K₄ caveat missing in 3 summaries |
| Conj 2.4 / data consistency | SOUND (consistent); wrong STL conjecture number |
| Lemma 3.1, Thm 3.2, Lemma 3.3 | SOUND |
| Lemma 3.4 (walking back) | SOUND |
| Def 4.1 + parity | SOUND |
| Thm 4.2 (walk theorem) | SOUND (minor wording: "isolated in G") |
| Remark 4.3 | SOUND |
| Lemma 5.1, Thm 5.2 | SOUND |
| Thm 6.1 | SOUND; PTM₂(r) sentence GAP (one component) |
| Thm 7.1, Cor 7.2, girth criterion | SOUND |
| §8 base-problem sentence | UNCLEAR |
| §9 item 4 (EE) | GAP (minor) |
| Abstract n ≤ 10 claim | ERROR |
| Results (1) "only known failure of STL-P" | ERROR (needs "3-connected") |
| Lean statements | faithful; sorry-free; standard axioms |
| Computations | reproduced exactly |

## 6. Required corrections

1. Abstract: replace "at most 10 vertices" by "at most 8 vertices (order 10 in progress)", or
   complete the n = 10 run first. Same in §Z.1 ("and n = 10 up to isomorphism").
2. Fix the [STL] numbers: Prop 3.4 → 4.4 (line 105), Ex 3.7 → 4.5 (159), Conj 6.4 → 7.4 (195).
   Cite the PEE data as [STL, §6, Table 3].
3. Results (1): "the only known failure … of STL" → "the only known failure with J 3-connected".
4. Add the K₄ exception to:
   - the abstract ("for a prescribed end, every failure other than K₄ …"; "when … parallel …,
     every failure other than K₄ has a cut vertex");
   - Results (1) ("PTM_m(r) holds whenever G − F is connected, except K₄");
   - E24(A)/(C) and §Z.1 ("never fails").

   State in Table 1 that e@x tests are run on PTM-positive instances.
5. §6, after Thm 6.1: "for all graphs … whose two edges lie in one component (otherwise
   Thm 1.1 componentwise)". In the k = 1 sub-case of v ∼ x, a, note v ≠ y.
6. §8: qualify the class-separation sentence by "when the three pairs are packed", and mention
   the NOBASE instances.
7. §9 item 4: require the complementary pair to be non-adjacent (or the multigraph PTM).
8. Optional:
   - Step 2 wording "isolated in G";
   - Lean docstring `base_of_fix`; remove the unused `liftG`; replace the deprecated lemma names;
   - save the `walk … 1` outputs in `out/`; drop the unused `.inc` files.
