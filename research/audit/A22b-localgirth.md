# Audit A22b: the local-girth strengthening (commit 4b85187, branch `claude/ptm`)

**Verdict: SOUND. The local form of Theorem 6.1 and Corollary 7.2 is correct, and the Lean statements say exactly what the paper says (sorry-free, standard axioms). Every short cycle the proof rules out passes through a, b, x or y. Lean checks this mechanically, and about 2.5 million stress cases built to break it all pass. There is no ERROR. There are two minor statement-level GAPs, in the abstract and Results (5): hypotheses are left out. Three further fixes are optional wording or precision. None affects a proof.**

## Scope and method

**What was audited.** `git diff 70c1eb8 4b85187` of:
- `terminal-matching.tex`: abstract, Results (4)/(5), Honest status, §6, §7, §8 table, §10 list;
- `TerminalMatching.lean` and `PTMAxioms.lean`;
- `scripts/localgirth_stat.py` and `scripts/out/localgirth.log`;
- E24(I) in `research/experiments.md`;
- §Z.2/§Z.3 in `research/connections.md`.

Nothing under audit was modified. My scripts and logs are in `research/audit/A22b-scripts/`.

**Note on the branch.** Other sessions committed while this audit was running. HEAD is now 8012e50, and commit 186953f swept in early copies of `crit_local.py` and `localproof.py` from this folder; I made no commits.
- The commits after 4b85187 touch only the §8 NOBASE paragraph and §9 item 1.
- They do not touch §6, §7, the Lean files, the statistics script or its log, or §Z.2/§Z.3.
- So the findings below apply unchanged to HEAD.
- The one later addition in scope is a ROADMAP bullet; see item 5.

## 1. Mathematics: Theorem 6.1 (local girth five). SOUND

**Labels.** After the orientation step, (a, b, x, y) is (a, b, w̄, w) if u = a, and (w, w̄, a, b) if u = b, where w̄ is the other end of cd. In both cases {a, b, x, y} = {a, b, c, d}.

The relabelled data satisfy the proof's standing assumptions:
- P runs from y to a: in the case u = b it is the reversed path b → w;
- the minimality "every walk between {a,b} and {x,y} has length ≥ k" is symmetric in the two edges.

**Every excluded short cycle.** I re-derived each one by hand, with k the length of P.

| place in the proof | excluded cycle | it passes through |
|---|---|---|
| admissibility, inner p₁ ~ x | triangle x p₁ y | x, y |
| short distances, b ~ x (forces k = 1, P = ya) | 4-cycle a y x b | all four |
| short distances, b ~ y | triangle a b y | a, b, y |
| sparseness, v ~ x, y | triangle v x y | x, y |
| sparseness, v ~ y, a, k = 1 | triangle v y a | y, a |
| sparseness, v ~ y, a, k = 2 (v ≠ p₁) | 4-cycle y v a p₁ | y, a |
| sparseness, v ~ x, a, k = 1 (v ≠ y) | 4-cycle a v x y | a, x, y |
| uniqueness of the exceptional v (k = 2) | 4-cycle x v a v′ | x, a |
| X has no inner adjacency: xa ∈ E(G) (forces k = 1) | triangle a x y | a, x, y |
| packedness of {x, y} | triangle x y w | x, y |

**No hidden use of global girth.**
- Inner vertices of P are excluded from N(x) by minimality (k − i + 1 < k for i ≥ 2), except p₁, which is excluded by the triangle x p₁ y. No cycle through inner vertices alone is ever used.
- The exceptional v is used only through the 5-cycle a v x y p₁, which is not excluded. Its uniqueness uses x v a v′. Whether v ∉ X is decided by adjacency (ya ∈ E(G) forces k = 1), not by girth.
- Packedness of {a, ℓ₁} and {ℓ₁, y} uses only N_M(ℓ₁) = {b} and b ≁ a, y in M.
- The degree counts and the use of Theorem 5.2 / Lemma 5.1 involve no cycles.

**Mechanical confirmation (Lean).**
- `ptm2_girth_core` now takes only `hS : NoShortCycleAt G (fun v => v = a ∨ v = b ∨ v = x ∨ v = y)`.
- Each of its seven uses of `hS.1`/`hS.2` must supply a proof that a named vertex lies in {a, b, x, y}, and Lean accepts each one: x, a, a, x, x, y, y (lines 1207, 1217, 1221, 1228, 1232, 1238, 1245).
- The file elaborates (§3). So the statement with only the local hypothesis is formally proved, and the prose proof matches it case by case.

**Computational stress test** (`localproof.py`, written from scratch; base graph and sparse test re-implemented).

For every pair of disjoint edges whose four ends lie on no triangle or 4-cycle, for every prescribed end, and for every shortest walk over all minimal (u, w), oriented as in the proof, the script checks:
- (A) admissibility;
- (S) the hypothesis of Theorem 5.2 (X sparse and the three pairs packed, in M or in M − xv with v ∈ N_M(x) ∖ X);
- (C) the conclusion of Theorem 6.1 itself, by the A22 brute force `bf.py`, where noted.

| family | instances | of which G not girth 5 | proof cases | (A) fail | (S) fail | inner P-vertex on a short cycle | exceptional v used / v on a short cycle | (C) brute force |
|---|---|---|---|---|---|---|---|---|
| all connected all-odd, n = 6, 8 | 100 | 4 | 100 | 0 | 0 | 0 | 0 / 0 | 100/100 ok |
| connected all-odd, n = 10, Δ ≤ 5 (1.16M graphs, 8,860 all-odd) | 1,136 | 300 | 1,360 | 0 | 0 | 80 | 260 / 0 | 1,136/1,136 ok |
| connected {1,3}-graphs, n = 12 | 8,120 | 4,900 | 10,248 | 0 | 0 | 1,016 | 1,384 / 0 | 8,120/8,120 ok |
| cubic, n = 14 | 15,180 | 9,132 | 21,220 | 0 | 0 | 196 | 3,232 / 0 | 15,180/15,180 ok |
| cubic, n = 16 | 223,280 | 178,592 | 306,568 | 0 | 0 | 7,312 | 33,880 / 0 | 223,280/223,280 ok |
| adversarial, 20,000 graphs (`adversarial.py 20000 2`) | 1,720,732 | 1,712,060 | 1,888,628 | 0 | 0 | 645,384 | 47,008 / 18,942 | – |
| adversarial with brute force, 1,500 graphs (`adversarial.py 1500 1 bf`; first instance of each graph of order ≤ 18) | 132,096 | 131,360 | 145,304 | 0 | 0 | 51,608 | 3,392 / 1,444 | 274/274 ok |
| random all-odd, degrees in {1,3,5}, possibly disconnected, 0–2 isolated vertices, 1,000 graphs of order 12–26 | 72,672 | 69,972 | 95,480 | 0 | 0 | 23,680 | 3,352 / 328 | – |
| same model, 300 graphs of order 10–16, brute force on 2 instances per graph | 3,384 | 3,144 | 4,148 | 0 | 0 | 580 | 340 / 8 | 192/192 ok |
| **total** | | | **2,473,056** | **0** | **0** | | | **248,282 ok, 0 fail, 0 timeout** |

**What `adversarial.py` builds.** It starts from the k = 1, 2, 3 configurations and the k = 2 five-cycle a v x y p₁. It then hangs triangles, 4-cycles and K₄ or K₄⁻ pieces on vertices next to the ends (inner path vertices, the exceptional v, other neighbours of a, b, x, y). It also adds random edges kept only while the local hypothesis survives.

In cubic graphs the exceptional v cannot lie on a short cycle: every cycle through v uses vx or va. That is why the column is 0 in the geng rows, and why the adversarial family was needed. Neither the theorem nor its proof fails anywhere.

**The new sentence "More generally PTM(G,F;e@x) holds for every pair F none of whose ends lies on a cycle of length three or four". SOUND.**
- In Def 1.2, G has no vertex of positive even degree, and F is a matching.
- If the two edges lie in one component, this is Theorem 6.1 applied with the right labelling. The hypothesis and reachability are symmetric in the four ends and in the two edges.
- If they lie in different components, Theorem 1.1 in each component gives it, and the two edges are automatically on different paths. This argument is in the preceding sentence ("otherwise apply Theorem 1.1 in each component").
- So the sentence is true as written, with no one-component assumption needed.
- *Wording (optional):* the "More generally" sentence reads as if it inherits "when the two edges lie in one component". Better: "… for every pair F none of whose ends lies on a cycle of length three or four (Theorem 6.1 if the edges lie in one component, Theorem 1.1 componentwise otherwise)."

**Results (4).** "F is a pair of disjoint edges in one component … all degrees odd" matches the theorem; the theorem is slightly more general, allowing isolated vertices. The clause "in particular for every F when G is connected and has girth ≥ 5" is correct.

## 2. Corollary 7.2 (local form) and the criterion after it. SOUND

**Corollary.** Its proof only needs Theorem 6.1 applied to J* with each of the four labellings. The local hypothesis on J* and the reachability of c from a in J* are both symmetric under these relabellings. J* has no vertex of positive even degree, since z is isolated and the other degrees are unchanged. So the corollary follows.

**Criterion, by hand.** Let C be a cycle of length ≤ 4 in J* = H + ab + cd with H = J − z (z is isolated, so irrelevant). There are three cases.
1. C uses neither ab nor cd. Then C is a cycle of H, and it is counted exactly when it meets {a, b, c, d}. This gives condition (i).
2. C uses exactly one of them, say ab. Then C − ab is an a–b path of H of length 2 or 3, so d_H(a,b) ≤ 3. Conversely, d_H(a,b) ∈ {2, 3} gives such a cycle, and it passes through a. Distance 1 is impossible since ab ∉ E(J). This gives condition (ii).
3. C uses both. Then |C| = 4 on {a, b, c, d}, and its other two edges are {ac, bd} or {ad, bc}, both in H. That happens exactly when one of the sums d(a,c) + d(b,d), d(a,d) + d(b,c) equals 2. This gives condition (iii).

So the equivalence holds. Cycles in cases 2 and 3 pass through a, b, c or d anyway, so replacing (i) by "girth(H) ≥ 5" characterises girth(J*) ≥ 5, as the parenthesis says. "Each pairing gives its own condition, and one suffices" is right: one pairing gives STL at all four neighbours.

**Criterion, by computation** (`crit_local.py`). It uses three independent short-cycle detectors, cross-checked with an assertion:
- explicit tuple enumeration;
- edge-deletion distance ≤ 3;
- the neighbour-pair test of `localgirth_stat.py`.

| test | tests | local hypothesis true | local true, global false | mismatches (local / global) |
|---|---|---|---|---|
| exhaustive: every labelled H on 4–7 vertices, (a,b,c,d) = (0,1,2,3), 01, 23 ∉ E | 532,752 | 4,632 | 185 | 0 / 0 |
| random, n = 4–14, six edge densities, random a, b, c, d | 200,000 | 96,968 | 2,419 | 0 / 0 |

The labelled exhaustive run covers every placement of a, b, c, d by symmetry. At n ≤ 6 local and global coincide: with four of at most six vertices in S, every short cycle meets S.

## 3. Lean. SOUND

**Build.**
- `lake env lean GallaiLean/TerminalMatching.lean`: exit 0 in 25 s.
  - Only linter warnings (unused section variables, the known deprecations).
  - No `sorry`, `admit`, `axiom` or `native_decide`.
- The built `.olean` (10:31:06) postdates the source (10:29:33), and the source has not changed since.
- `lake env lean ../manuscripts/terminal-matching/PTMAxioms.lean`: all 11 theorems print only `[propext, Classical.choice, Quot.sound]`. They include `ptm2_localgirth`, `stl_of_localgirth` and `test1_of_localgirth`.

**`NoShortCycleAt G S`** is the conjunction of two clauses:
- (∀ u v w, S u → u~v → v~w → w~u → False);
- (∀ u v w t, S u → u~v → v~w → w~t → t~u → u ≠ w → v ≠ t → False).

Why this is exactly "no C₃ or C₄ through S":
- Simple-graph adjacency is irreflexive, so the triangle clause covers exactly the triangles through u.
- In the 4-cycle clause, irreflexivity gives u≠v, v≠w, w≠t, t≠u, and u ≠ w, v ≠ t give the remaining two of the six inequalities. So the four vertices are distinct, and the clause covers exactly the genuine 4-cycles.
- The only closed 4-walks excluded by the side conditions are u v u v, u v u t and u v w v, which are not cycles.
- Any C₃ or C₄ through s ∈ S can be rotated to start at u = s.
- The predicate is a universally quantified negation, so it is never vacuous as a hypothesis (any forest satisfies it). It is also not weaker than intended.

I proved this formally. `A22b-scripts/A22bSemantics.lean` (elaborates, standard axioms) proves:
- `noShortCycleAt_iff_based`: `NoShortCycleAt G S ↔ ∀ u, S u → ∀ c : G.Walk u u, c.IsCycle → 5 ≤ c.length`;
- `noShortCycleAt_iff`: `NoShortCycleAt G S ↔ ∀ v (c : G.Walk v v), c.IsCycle → (∃ u ∈ c.support, S u) → 5 ≤ c.length`.

So the predicate is exactly "every cycle (Mathlib's `Walk.IsCycle`) through a vertex of S has length at least 5".

**The helper lemmas.**
- `NoShortCycleAt.mono` (shrinking S) is correct.
- `noShortCycleAt_of_girth` (global ⇒ local, for any S) is correct.

**Statements against the manuscript.**
- `ptm2_girth_core`: hypothesis `hS` at {a, b, x, y}, plus minimality over u ∈ {a,b}, w ∈ {x,y}. This is the "situation which we now treat" of the proof.
- `ptm2_localgirth` matches Theorem 6.1 exactly:
  - no positive even vertex;
  - `hS` at {a, b, c, d};
  - `G.Reachable c a`;
  - the two edges, disjoint;
  - conclusion `PTM2At G a b c d ∨ PTM2At G a b d c`.
- Its four orientation branches pass `hS.mono` to subsets of {a, b, c, d}.
- `ptm2_girth5` is now a one-line corollary, through `noShortCycleAt_of_girth`.
- `stl_of_localgirth` matches Cor 7.2 (STL part).
  - `hS` is on `liftJ J z a b c d`, which given `hN` is (J − z) + ab + cd on V(J) with z isolated (`liftJ` = two `swapG`s).
  - It needs no degree ≥ 3 hypothesis, so it is slightly stronger than the paper.
  - The four `ptm2_localgirth` calls use `hS.mono` with the labellings e1–e7 that A22 checked.
- `test1_of_localgirth` matches Cor 7.2 (test part): it adds `hdeg`, and `hev` is the antecedent of `Test1`.
- `stl_of_girth5` and `test1_of_girth5` are corollaries through `noShortCycleAt_of_girth`.
- The hypotheses are jointly satisfiable. The Petersen example of A22 satisfies the global form, hence the local one. There are also local instances that are not of global girth five (§4).

**Cosmetic.** The module docstring (lines 27–32) still describes only `ptm2_girth5`, `stl_of_girth5` and `test1_of_girth5`, so it should mention the local forms. The `\lean{…}` pointers in the tex and the §10 list are correct.

## 4. Statistics. SOUND (with one remark on precision)

**The script implements the corollary's hypothesis correctly.**
- `short_cycle_through(G, S)` returns true exactly when some s ∈ S has two neighbours u, v that are adjacent (triangle) or have a common neighbour w ≠ s (4-cycle s u w v; w ≠ u, v since w ∈ N(u) ∩ N(v)).
  - This is exactly "a C₃ or C₄ through S". It agrees with my two other detectors on all 732,752 tests of §2.
- Pairings are skipped when a pair is adjacent in J.
- J* = J − z + pq + rs.
- Reachability is `has_path(H, p, r)`. It is trivially true here, since J − z is 2-connected.
- `girth_ge5` = no short cycle through any vertex.
- The table counts graphs with at least one qualifying pairing.

**Reproducibility.**
- `python3 localgirth_stat.py 300 7 11 15` reproduces the first two log lines exactly (2 s).
- The full command `300 7 11 15 21 31 51` (from E24(I)) reproduces `out/localgirth.log` **byte for byte** (11.5 s).
- The §8 table (5/29/73/138/210 and 5/3/6/11/14), E24(I) (all seven columns), §Z.3 (5/300, 210/300, 5/300, 14/300), the Honest-status percentages (5/300 ≈ 2%, 210/300 = 70%, 5/300 ≈ 2%, 14/300 ≈ 5%) and the commit message all match the log.

**The description is accurate.**
- `nx.configuration_model` pairs a uniformly shuffled stub list, which gives a uniform random matching of stubs.
- Rejecting every multigraph (collapse, drop loops, then compare degree sequences) gives the uniform distribution on labelled simple graphs with degrees (4, 3, …, 3).
- Then node connectivity ≥ 3 is imposed.
- So "random 3-connected graphs with degree sequence 4,3,…,3 (configuration model, simple graphs kept)" is a correct description. It means the uniform labelled model conditioned on 3-connectivity. Orders are odd, as parity requires.

**Independent re-derivation** (`stat_check.py`).
- It uses its own pairing sampler, its own 3-connectivity test (no vertex pair separates), the J − z criterion of §2 instead of building J*, and new seeds.
- 300 per order (seed 2026), local: 3, 31, 74, 159, 215; global: 3, 4, 9, 13, 11. This agrees with the paper's sample within sampling error.
- 3,000 per order (seed 77):

| order | local | global girth 5 |
|---|---|---|
| 11 | 19 (0.6%) | 19 (0.6%) |
| 51 | 2,042 (68.1%) | 111 (3.7%) |
| 101 | 2,507 (83.6%) | 106 (3.5%) |

**Remark.** "2% of the graphs of order 11" is 5/300. The rate itself is about 0.6% (19/3000; the 95% interval from 5/300 alone is about 0.5–3.8%). It is correct as a description of the sample, but imprecise. Order 51 (70% against 68%) is fine.

As n grows, the local fraction tends to 1 and the global one stays near e^{−10/3} ≈ 3.6%. This is because a random cubic-like graph has O(1) short cycles in all. So the 70% measures sparseness of this random model, not how often hard (dense or minimal) spine instances are covered. The paper's caveat "the consequence for the spine needs sparse graphs" covers this.

## 5. Claims about the local version

**Abstract. GAP (minor).** "… the first deletion test, for every vertex z of degree four with a pairing ab, cd of N(z) such that no cycle of length at most four of the lifted graph (J−z)+ab+cd passes through a neighbour of z".
- It omits that the pairs must be **non-adjacent in J** (ab, cd ∉ E(J)). If ab ∈ E(J), then (J − z) + ab + cd is a multigraph (or, read simply, the lift is not the one of Theorem 7.1), and the corollary does not apply.
- The same omission was in the pre-strengthening abstract.
- Correction: "with a pairing ab, cd of N(z) into pairs non-adjacent in J such that …".
- That z is the only even vertex and that its neighbours have degree ≥ 3 are implied by "the first deletion test" (3-connected J).
- Reachability is not needed for the claim (Theorem 1.1 componentwise, then Theorem 7.1), so its omission is harmless.

**Abstract, "in particular for every pair when the girth is at least five".** SOUND (for edges in different components Theorem 1.1 gives it anyway).

**Results (4).** SOUND.

**Results (5). GAP (minor, contextual).** It omits "z the only even vertex of J" and, for the test, "every neighbour of z of degree ≥ 3". Both are hypotheses of Cor 7.2 and of `test1_of_localgirth`; the motivation paragraph supplies the first. Correction: begin "If z is the only even vertex of J, has degree four, …" and add "(and every neighbour of z has degree ≥ 3)" before "the first deletion test holds".

**Honest status.** SOUND; no overclaim. It states that the spine consequence needs sparse graphs and gives the reach on a stated random model. Optional: give the counts ("5/300 … 210/300") instead of percentages, or use the 3,000-sample figures (0.6% and 68% local; 0.6% and 3.7% global). As written, "2%" at order 11 reads as a rate, which it is not.

**§Z.2.** SOUND. "Every short cycle the proof excludes passes through one of the four ends" is verified above, mechanically in Lean.

**§Z.3.** SOUND. The three bullets restate the criterion and the counts correctly, and "This still needs sparse graphs around z" is the right caveat.

**Outside the listed scope: ROADMAP.md** (commit 82e27e4). "`test1_of_localgirth`: spine Test1 at d(z) = 4 holds whenever no cycle of length ≤ 4 of (J − z) + ab + cd passes through N(z)" has the same omission as the abstract: add "for a pairing ab, cd of N(z) with ab, cd ∉ E(J)".

**Cosmetic.**
- The §6 title is still "Girth five"; the theorem is "local girth five".
- §9 item 1 "PTM₂ beyond girth five" could read "beyond local girth five".
- The Lean module docstring (item 3).

## Summary of grades

| item | grade |
|---|---|
| Thm 6.1 (local) and its proof | SOUND; every excluded C₃/C₄ passes through a, b, x or y (by hand, Lean, 2.47M stress cases) |
| "More generally PTM(G,F;e@x) …" sentence | SOUND (componentwise via Thm 1.1); optional wording |
| Cor 7.2 (local) | SOUND |
| Criterion after Cor 7.2 (local and global) | SOUND; 0 mismatches in 732,752 tests |
| `NoShortCycleAt` and the Lean statements | SOUND; equivalence with Mathlib `IsCycle` proved; elaborates; standard axioms |
| `localgirth_stat.py`, log, §8 table, E24(I), §Z.3 | SOUND; byte-identical re-run; independent re-derivation agrees |
| Abstract | GAP (minor): non-adjacent pairing omitted |
| Results (5) | GAP (minor): "z the only even vertex", deg ≥ 3 omitted |
| Honest status | SOUND; order-11 percentage imprecise (small sample) |
| §Z.2, §Z.3 | SOUND |

## Required corrections

1. **Abstract:** "with a pairing ab, cd of N(z)" → "with a pairing ab, cd of N(z) into pairs non-adjacent in J". Apply the same fix to the ROADMAP bullet for `test1_of_localgirth`.
2. **Results (5):** start with "If z is the only even vertex of J and has degree four, …", and state the test part under "every neighbour of z has degree at least three" (as in Cor 7.2).
3. **§6, after Theorem 6.1:** make the "More generally" sentence self-contained: "… (by Theorem 6.1 when the two edges lie in one component, and by Theorem 1.1 componentwise otherwise)".
4. **Honest status / §8:** report the order-11 figure as a count (5/300) or from a larger sample (≈ 0.6%; order 51: ≈ 68% local, ≈ 3.7% global from 3,000 graphs, `A22b-scripts/stat_check.py`).
5. **Cosmetic:**
   - §6 title "Local girth five";
   - §9 item 1 "beyond local girth five";
   - update the `TerminalMatching.lean` module docstring (lines 27–32) to name `NoShortCycleAt`, `ptm2_localgirth`, `stl_of_localgirth`, `test1_of_localgirth`.

## Scripts and logs (`research/audit/A22b-scripts/`)

| file | what it is |
|---|---|
| `crit_local.py`; `crit_local_exh7.log`, `crit_local_rnd.log` | criterion test (§2) |
| `localproof.py`; `localproof_runs.log` (geng families; ignore its last two lines, an interrupted run), `localproof_adv.log` (adversarial, 20,000 graphs), `localproof_adv_bf.log` (adversarial with brute force), `localproof_rnd.log`, `localproof_rnd_bf.log` (random all-odd) | proof stress test (§1) |
| `adversarial.py` | generator of short cycles next to the ends |
| `stat_check.py`; `stat_check.log`, `stat_check_3000.log` | independent statistics (§4) |
| `A22bSemantics.lean` | `NoShortCycleAt` ⇔ cycles through S have length ≥ 5 |

To run the Lean file: `cd lean && lake env lean ../research/audit/A22b-scripts/A22bSemantics.lean`.
