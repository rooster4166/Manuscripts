# A27 — Audit of the `claude/clt` session (constrained Lovász decompositions)

Auditor: independent audit session, 2026-11-27.

**Version audited.** Branch `claude/clt` at commit `6dbbc03`, which includes the two addenda of the
brief (`csys_case_adj`, move (M2); `csys_case_leaf` with `CSys.liftLeaf`, move (M4)):
`manuscripts/clt/clt.tex`, `lean/GallaiLean/ConstrainedLovasz.lean`, `research/experiments.md`
§E30, `research/connections.md` §AE, `manuscripts/clt/scripts/*`. The findings below refer to that
version. While the audit was running the clt session read the draft of this report and produced a
revision (commits up to `9aff2a3` plus uncommitted working-tree edits at hand-back time). The last
section says which findings that revision resolves and what remains. Commits `921fd2a`/`9aff2a3`
(triangle-base data, E30(G), `tb_all.py`, `tb_ls.py`) came after the brief and were not audited.

Scratch scripts of this audit are in `/tmp/claude-0/audit/` (not committed). No file other than
this report was modified.

## Summary verdict

* **Lean: sound and faithful.** The module compiles with no errors, warnings or `sorry`. Every
  listed theorem, including the new `csys_case_adj` and `csys_case_leaf`, depends only on
  `propext, Classical.choice, Quot.sound`. The full `lake build` is green (18,406 jobs). The
  definitions `Tracks`, `CSys.Sat`, `CSys.Good`, `BLocal`, `CrossLocal`, `CLTB`, `CLTB1`, `LN` and
  `CSys.liftLeaf` say what the manuscript says. No hypothesis is vacuous, and none makes a theorem
  trivial.
* **Section 4 (the boundary): every hand proof is correct.** An independent brute force confirms
  each example: the system is unsatisfiable, and every proper subsystem is satisfiable (except the
  confinement system, which contains the transitive triangle). **But the blanket claim that the
  examples are "minimal in the data (no smaller graph or system fails)" is false for the in-degree
  example**: cross-local bipartite failures of in-degree two already exist on 5 vertices
  (finding 1).
* **Section 5: correct.** The paper statements match the Lean statements.
* **Section 6: the transfers of (M1)–(M5) are correct.** I checked them by hand for several tails.
  Proposition 6.1 (a), (b) follows for CLT-B1. But the move list is not "the exact list": the
  leaf-tail move (`l1_case_leaf`) is missing, so "for k = 1 the residual is exactly the blocked
  configuration" is false as written (finding 2). The proposition minimises the wrong quantity
  (finding 3), and several "iff" instance conditions are incomplete or inexact (finding 4).
* **The data reproduce, with small count errors.**
  - The E30(A) rows reproduce exactly for n ≤ 7 (star, bip1, bipx, match, bip, in1, lin, any) and
    for n = 8 (star, bip1, bipx, match, bip, bipx2). The exception is "any" at n = 8: 222, not 221
    (finding 14).
  - `enum.c` agrees exactly with an independent brute force (decomposition counts and all minimal
    violation sets) on all 152 graphs of order ≤ 7 and on 139 of the 224 of order 8.
  - My own maximal-system search confirms CLT-B1 and CLT-B (d(g) ≠ 2) on every graph of order ≤ 7.
  - At order 9 I completed the d(g) = 2 slice (all 2,805 graphs). CLT-B1 has 0 failures, as
    claimed, but 44 graphs (not 42) have a B-local failure (finding 13).
  - The two requested random runs reproduce, and so do E30(C), E30(E) and the t6 base on three
    residual graphs (all 1,712 labellings, checked with my own checker).
  - Reporting issues: findings 9 and 10.
* **Overclaims** in the abstract, introduction and §7 (findings 5–8).

No finding invalidates a theorem, a Lean statement, or the conjectures CLT-B and CLT-B1: no
counterexample was found. Findings 1–4 need text changes in §4 and §6, and finding 13 changes
Table 2.

## Findings (against `6dbbc03`)

1. **ERROR (low impact) — §4, opening sentence and Example 4.3 (`EEiW`); E30(B).** "The examples
   are minimal in the data (no smaller graph or system fails)." For the in-degree relaxation this is
   false. Example 4.3 is presented as a cross-local bipartite system, that is, a relaxation of
   CLT-B1 that drops (B1), on 6 vertices.
   - On 5 vertices there are three such failures, all of size 2 and all with d(g) = 2. They are the
     `bip` hits at n = 5 in E30(A) itself:
     - `DEk` (N(0) = {3,4}, N(1) = {3}, N(2) = {4}, N(3) = {0,1,4}, N(4) = {0,2,3}, g = 0) with
       av(1,2), av(3,2);
     - `DTw` with av(2,1), av(0,1);
     - `D]w` with av(2,3), av(4,3).
   - Brute force confirms `DEk`: it has 4 decompositions, the system is unsatisfiable, and each atom
     alone is satisfiable. CLT-B1 has no degree condition, so `DEk` is the minimal witness that (B1)
     is needed in CLT-B1.
   - `EEiW` is minimal only among graphs with d(g) ≠ 2. I checked that at n ≤ 5 with d(g) ≠ 2 no
     bipartite local system of unrestricted in-degree fails, cross-local or not.
   - Example 4.4 (chains) needs the same qualification. Chain failures (in-degree ≤ 1,
     out-degree ≤ 1, acyclic) exist at n = 5: `DCw` and `DEk`, both with d(g) = 2 and neither
     cross-local. The net is minimal among graphs with d(g) ≠ 2, which is the right frame for 4.4
     since 4.4 is about CLT-B.
   - Example 4.2 (path c g a) has d(g) = 2.
   - The confinement system of Example 4.5 is not minimal: it contains the transitive triangle.

   **Fix:** say "minimal among graphs with d(g) ≠ 2" for 4.3 and 4.4. Give `DEk` as the minimal
   (B1) example for CLT-B1. Exempt 4.2 and the confinement system.

2. **GAP — §6, move list and the paragraph after Proposition 6.1; Introduction item (4); abstract
   ("We locate exactly where Lovász's induction for CLT-B stops").**
   - **The missing move.** The list (M1)–(M5) omits the leaf-tail move that `l1star` uses
     (`l1_case_leaf`: no even vertex, deg c = 1, take the edge cy as P_c and decompose G − cy).
   - **Why the k = 1 claim fails.** Without that move, an all-odd graph with deg c = 1 can be an
     instance where none of (M1)–(M5) applies. Example: K_{1,3}, with c a leaf and A the other two
     leaves. (M4) needs deg c ≥ 3. (M5) needs a vertex outside N[c] ∪ A ∪ N(A), and here that set
     is all of V. So "For k = 1 the residual is exactly the blocked configuration of [L1S]
     (`l1starGen_of_blocked`)" is false for the moves as listed: `l1starGen_of_blocked` uses four
     reductions, and one of them is not in the list.
   - **The all-odd case for k ≥ 2.** Proposition 6.1 says nothing about the all-odd residual.
   - **The multi-tail leaf move exists, with conditions.** Let c_1 be a leaf at y in an all-odd
     graph. Take P_{c_1} = c_1y and decompose the child G − c_1y, where y is the new even vertex.
     The transfer adds the one-edge path c_1y, which avoids A_1 because y ∈ N(c_1); the other paths
     do not change. If y is a tail, then P_y = c_1y avoids A_y because c_1 is not avoided, and y's
     constraint must also be dropped from the child. The child is an instance iff A_j ∩ N(y) = ∅
     for every remaining j; for CLT-B also deg y ≠ 3.
   - **Also missing, but harmless.** Lovász's Cases III and IV (all positive degrees 1; no edges),
     where every local system holds trivially.

   **Fix:** add (M0) and drop "exact" and "every move". Restrict the k = 1 sentence to the list
   with (M0). Say that the all-odd residual for k ≥ 2 is not analysed. In the abstract, write
   "where ... stops when g exists".

3. **GAP (easy) — Proposition 6.1, hypothesis "with ∑deg smallest".** The children of (M4) and
   (M5) have the same ∑deg as G: one edge is moved to a new leaf. If only ∑deg is minimal, a child
   with the same ∑deg could itself be a counterexample, so "none of (M4), (M5) applies" does not
   follow. **Fix:** use ∑deg + [no even vertex], the measure in the §6 preamble and in
   `Lovasz.lean`.

4. **ERROR (minor) — §6, instance conditions stated as "iff".**
   (a) **Degree-two condition for CLT-B.** For the CLT-B (non-cross-local) form, the new even
   vertex must not have degree 2 unless the child is cross-local. That means deg c_1 ≠ 3 in (M2),
   (M3) and (M4), and deg x ≠ 3 in (M5). Only (M1) states it. So the "iff" in (M2) and (M4), and
   "same instance conditions as (M2)" in (M3), are wrong for CLT-B. (M5) states no instance
   condition at all. The correct one is N(x) ∩ A ⊆ {u}, where u is the chosen neighbour, plus
   deg x ≠ 3 for CLT-B.
   (b) **(M4), cross-local form.** "c_1 adjacent to no other tail" is sufficient but not necessary.
   If c_1 has exactly one tail neighbour c_j, take y = c_j. The edge c_1y is deleted, c_1 is no
   longer adjacent to a tail, and the child is cross-local. The correct condition is that c_1 has
   no tail neighbour other than y.
   (c) **Prop 6.1(b) and the last paragraph of §6.** Under CLT-B1, if a tail c lies in N(g), the
   disjunct "g ∈ A" is impossible:
   - g ∈ A_1 would contradict locality (g ∉ N[c]);
   - g ∈ A_j for j ≠ 1 would contradict cross-locality.

   So (b) just says "c is adjacent to another tail". In the last paragraph, "g ∈ A if a tail is
   adjacent to g" means "no tail is adjacent to g". This is not wrong, but it is misleading.
   (d) **The list of obstructions.** The "two new obstructions" for k ≥ 2 omit the one that
   Prop 6.1(a) actually records: a non-tail u ∈ N(g) with two tail neighbours, so the tails are at
   distance two. There (M3) fails because Theorem 5.2 cannot carry the second tail. Conversely,
   "heads of one tail next to another tail" cannot occur in a CLT-B1 instance, by cross-locality.
   **Fix:** state the degree condition for CLT-B in every move, correct the condition of (M4),
   simplify (b), and list three obstructions:
   - adjacent tails;
   - two tails with a common neighbour in N(g);
   - for CLT-B only, heads adjacent to other tails.

   **For the record, the transfers are correct.** I checked each with several tails:
   - (M1) is `csys_caseI`.
   - (M2) is `csys_case_adj`: the path ending at g gains c_1, which no A_j contains.
   - (M3) works as sketched, including when c_1 ∈ N(g). The Fan step in H + uℓ has no endless
     neighbour of u. The leaf constraint is carried in vertex-set form and the other tails by
     Theorem 5.2. The merge changes only the leaf path.
   - (M4) is `csys_case_leaf`.
   - (M5) is correct in both sub-cases of Lovász's Case II. If b'(u) = 0, the new path ux has no
     tail end. If b'(u) = 2, Theorem 5.2 with target x and source u needs only that no tail lies in
     N[x] and that x ∉ A. The condition x ∉ N(A) is used only for the child's locality.
   - Proposition 6.1 (a) follows from (M1) (no tail in N(u)) and (M3) (one tail, not adjacent to
     another tail; the child is cross-local because the parent is). (b) follows from (M2).

5. **MINOR (overclaim) — §7, first sentence.** "The t6 base system violates every condition of
   CLT-B." It does not violate (B1): its av-digraph is the directed path
   z → x_1 → y_2 → x_2 → y_3 → x_3, so every vertex is avoided at most once. It does violate (B2)
   (it is a chain) and (B3) (in the dense shapes its heads lie in N(x_3)), and it uses ne atoms,
   which are outside the language of CLT-B.

6. **MINOR (overclaim) — abstract.**
   1. "by an exact search over all Lovász decompositions of every graph of order at most nine":
      order 9 was covered for only 10,719 of the 11,936 graphs (see the dagger in Table 2).
   2. "we give minimal counterexamples, with hand proofs, to every relaxation": `EErw` and `FCRV?`
      are exhaustive computer checks, not hand proofs, and minimality fails as in finding 1.
   3. "in the dense residual *every* labelling has a base" is a statement about the computed
      residual graphs only.
   4. "a Fan transfer keeps every end that is not a chain vertex on a path with the same vertex
      set, plus the target": the theorem (and the Lean) excludes all of {u, v} ∪ N(u), not only the
      chain vertices, and gives V(Q) ⊆ V(Q′) ∪ {u}, not equality.
   5. The abstract's "CLT-B" includes the cross-local clause for d(g) = 2, but in §3 that clause is
      CLT-B1.
   6. "exactly where ... stops": see finding 2.

7. **MINOR (mis-citation) — Introduction, first bullet.** "with the tight transfer conjecture TR
   it is equivalent to the some-target conjecture ST of [L1I]". l1-induction proves TR ∧ ST ⇒
   L1Blocked (hence L1*), and that, given ST, L1Blocked ⟺ TR_adm. It does not prove L1* ⇒ ST.

8. **MINOR — §5, Theorems 5.2 and 5.3 use "constrained vertex", which is never defined.** In Lean
   (`CSys.Touched`) a constrained vertex is a tail of an avoidance atom or an end of a distinctness
   atom. Heads are deliberately excluded: they may lie in N(u), and only u itself must not be
   avoided.

9. **DATA (reporting) — §3 Evidence "Random", E30(D).** Many of the random "maximal" CLT-B1
   systems are empty or have only one non-empty tail. I re-ran the generator of `rand_clt.py`
   (same code, three seeds per order 11–16, 1,800 instances):

   | form | empty systems | at least two tails with nonempty avoid sets |
   |---|---|---|
   | bip1 | 470 (26%) | 495 (27%) |
   | bipx | 39 | 1,221 |

   In the requested run `rand_clt.py bip1 13 50 998`, 11 of the 50 systems are empty. So the 1,800
   bip1 instances test the multi-tail statement much less than the count suggests. **Fix:** report
   per form the number of nonempty and of multi-tail systems, or redraw.

10. **MINOR — Remark after Example 4.6; E30(A) last row ("bip1 + ne atoms between non-avoided
    vertices: every graph fails").** This is trivial. The set of all ne(u, v) over the odd vertices
    is unsatisfiable in every graph that has an odd vertex, because every path has two ends.
    `trans bip1 10 net` at n = 5 returns pure ne systems, for example ne(0,1), ne(0,2), ne(0,3) on
    `D?{`.

11. **MINOR — wording in Examples 4.4 and 4.6.**
    - Example 4.4 (the net), proof: the step "So the leaves are paired ... as (1,4),(3,0),(2,5) or
      as (1,0),(3,5),(2,4)" uses av(1,5), av(2,0), av(3,4). These give P_1 ∈ {14, 140},
      P_2 ∈ {25, 254} and P_3 ∈ {30, 305}; the text should say so. The conclusion is right
      (verified).
    - Example 4.6 (`FCRV?`): besides 6 ~ 0, the head 1 is also adjacent to the tail 4.

12. **MINOR — cross-references and the scope of `csys_case_leaf`.**
    - `manuscripts/clt/README.md` says "experiments E29" and the `CLTB1` docstring says
      "experiment E29". The experiment is E30. (This was fixed in `e495344`.) The `CLTB1` docstring
      also says "every graph ... to order 9" (finding 6.1).
    - `csys_case_leaf` is a transfer for a given decomposition of the leaf graph. Its hypotheses are
      `hc0` and `hn1`, and its conclusion is `D.ends w = DH.ends (some w)`. The degree bookkeeping
      that turns `CSys.Good` of the leaf graph into `CSys.Good G` is not part of it. That is a
      routine lemma, but "(M4) is formalised" should read "the transfer of (M4) is formalised".

13. **DATA — order 9, d(g) = 2 (Table 2 column "B-local, deg g = 2"; §3 Evidence; Example 4.6;
    E30(A)).** The reported 42 counts only the 10,719 graphs that the session enumerated.
    - **Complete count.** I ran `enum -v 1` with `trans bipx 8` and `trans bip1 8` on all 2,805
      graphs of order 9 with d(g) = 2; each finishes in under 60 s. 44 of them have an
      unsatisfiable B-local system, and none has an unsatisfiable CLT-B1 system.
    - **The two extra graphs.**
      - `HCdbMKv`: g = 4, N(g) = {0,3}, 17 edges, with av(1,8), av(3,7).
      - `HQhTVQx`: g = 5, N(g) = {1,3}, 18 edges, with av(6,7), av(1,8).

      Both lie in the session's not-yet-enumerated remainder, and both have g on a triangle.
    - **Confirmation.** `lsearch` returns NONE on all 44 failing systems. My brute force confirms
      the 33 of them whose graphs have at most 16 edges.
    - **Corrections.**
      - The n = 9 entry becomes 44.
      - "2 at n = 7, 42 at n = 9" becomes "2, 44".
      - "All 44 failures ... at orders 7 and 9" becomes 46.
      - E30(A)'s "(40 in a triangle)" is also off. Of the session's own 44 failures (n = 7, 9), 42
        have g on a triangle. With the complete n = 9 slice it is 44 of 46.
    - **"The densest".** The 1,217 graphs left over are not "the densest". They are the last part
      of each of the four geng slices: 15–32 edges, including 85 graphs with d(g) = 2.

14. **DATA (minor) — E30(A), row "any", n = 8: reported 221, exact value 222.**
    - **Exact count.** A graph has an unsatisfiable local avoidance system of some size iff no
      minimal violation set consists of ne atoms only. Counting this directly in the `-v 1` output
      gives 1, 4, 12, 105, 222 for n = 4..8.
    - **Why 221.** `trans any 10` also gives 222, and one of those graphs needs exactly 10 atoms. So
      221 is an artefact of a smaller K.
    - **The row is not exhaustive.** An unrestricted system can have up to n(n−1) atoms. Compute the
      row by the direct criterion.

## What I verified, and how

### Lean (`lean/GallaiLean/ConstrainedLovasz.lean`)
* **Build.** `lake env lean GallaiLean/ConstrainedLovasz.lean` prints nothing: no errors, warnings
  or `sorry`. `lake build GallaiLean.ConstrainedLovasz` and the full `lake build` (18,406 jobs) are
  green. The file contains no `sorry`, `admit`, `native_decide` or `axiom`. `GallaiLean.lean`
  imports the module.
* **Axioms.** I ran `#print axioms` from the scratch file `/tmp/claude-0/AuditAx.lean` on
  `fan_single_track`, `csys_fan_transfer`, `csys_caseI`, `l1StarGen_of_cltB1`, `lInfty_of_cltB1`,
  `ee_of_cltB1`, `lN_of_cltB`, `csys_good_of_packed`, `csys_good_of_sparse`, `CSys.sat_of_tracks`,
  `csys_case_adj` and `csys_case_leaf`. All give `[propext, Classical.choice, Quot.sound]`.
* **Faithfulness**, read against §§2–6:
  - `Tracks D D' S u`: every new path has a source path with V(new) ⊆ V(old) ∪ {u}, and every end of
    the new path outside S is an end of the old one. `fan_single_track` uses
    S = {u, v} ∪ N_{G'}(u), as Theorem 5.1 states, and its count hypothesis is Fan's condition.
    Not vacuous.
  - `CSys.Sat`: avoidance means every path with an end at c misses A, which is P_c missing A under
    Lovász ends. Distinctness means no path has both ends. `CSys.Good` is ends = deg mod 2 together
    with Sat. Correct.
  - `BLocal` matches Definition 3.1:
    - tails are distinct and odd;
    - (B1) avoid sets are pairwise disjoint;
    - (B2) no tail is in any avoid set;
    - (B3) `Admissible`: a ≠ c, a ∉ N(c), and a ∉ N(g) for every positive-even g, so g ∈ A is
      allowed.
  - `CrossLocal`: A_i ∩ N(c_j) = ∅ for all i, j.
  - `CLTB` = (evenSet).card ≤ 1, d(g) ≠ 2 and BLocal. `CLTB1` = (evenSet).card ≤ 1, BLocal and
    CrossLocal. These are exactly Conjectures 3.2 and 3.3.
  - `LN`: no positive-even vertex, all 2k vertices of the pairs distinct, c_i odd, c_i ≁ a_i. This
    is L_N, and CLT-B restricted to matchings in all-odd graphs is equivalent to it.
  - `csys_caseI`: the hypotheses are those of Theorem 5.3 (constrained vertices outside
    N[u] ∪ {g}, u not avoided, child good, no admissibility).
  - `csys_case_adj` is (M2): child system (g, A ∪ {c}) :: S on G − gc, with S not touching g or c
    and not avoiding c; conclusion (c, A) :: S on G.
  - `csys_case_leaf` with `CSys.liftLeaf` (the leaf `none` avoids {c} ∪ A, the rest is lifted along
    `some`) is the transfer of (M4); see finding 12 for its scope.
  - `csys_good_of_packed` and `csys_good_of_sparse` are as stated in §5. Packed: tails, heads and ne
    ends lie in X. Sparse: every vertex has at most one neighbour in X ⊇ tails ∪ heads, and heads
    lie outside N[c].
  - The k = 1 corollaries go through `bLocal_single` (an admissible single constraint is B-local
    and cross-local). Correct.

### Manuscript, checked by hand (§§2–7)
* Leaf reductions (§2): both equivalences hold (the bijection D ↔ D + cℓ, and te via G − vw + wℓ).
* §4 hand proofs:
  - K_{2m}: m paths of total length m(2m−1) must all be Hamiltonian.
  - The path c g a.
  - `EEiW`: the case analysis (P_1 = 13, P_2 ∈ {24, 245}, and the two impossibilities) is right.
  - The net: correct (finding 11).
  - K_{1,3}: all three pairings, for the directed and transitive triangles and the confinement
    system.
  - `EErw` and `FCRV?` were checked by computer (below).
* §5: the proofs of Theorems 5.1–5.3 match the Lean proofs, and the packed and sparse statements
  match Lean.
* §6: every move with several tails, and Proposition 6.1 (findings 2–4).
* §7: the t6 system against t6-dense Definition 2.1 matches Table 1 and `t6probe.system`:
  - (E1): av(z, x_1), ne(z, y_2), ne(z, y_3);
  - (E2): av(y_2, x_2);
  - (E3): av(y_3, x_3);
  - (E4): ne(y_2, y_3);
  - (E5): av(x_2, y_3);
  - (E7): av(x_1, y_2).
* Intro: the citations to l1-induction (finding 7) and route-descent (L_N ⇒ Gallai when the even
  vertices induce a subgraph with a perfect matching: correct).

### Independent brute force (`/tmp/claude-0/audit/bf.py`, own code)
The method is my own graph6 decoder, all paths of G, and an exact cover of E(G) by paths with ends
= deg mod 2. Each decomposition is produced once, because the path covering the smallest uncovered
edge is chosen.
* **Small graphs.** K_4 has 6 decompositions and K_6 has 960, all with Hamiltonian paths. P_3 has
  one.
* **The examples.** All of the following are unsatisfiable, every proper subsystem is satisfiable
  (the confinement system excepted), and the graphs are as described in the text:
  - `EEiW`: av(1,{0,5}), av(2,0).
  - `ECqg`: av(2,0), av(0,1), av(1,5), av(3,4).
  - `CF`: the directed and the transitive triangle.
  - `EErw`: the two 2-cycles. Each single 2-cycle and every 3-atom subsystem is satisfiable. 0 and
    1 are twins at distance 2, and no decomposition separates them.
  - `FCRV?`: av(0,1), av(4,6).
  - `FCdcw`: av(2,0), av(5,3), av(1,4). The heads all lie in N(6), d(6) = 4, and each atom alone is
    satisfiable.
* **`enum.c` against brute force.** The decomposition counts and the complete families of
  inclusion-minimal violation sets (local av atoms and ne atoms, `-v 1`) agree on all
  2 + 7 + 13 + 130 graphs of orders 4–7, and on the 139 graphs of order 8 with at most 15 edges.
  There are 0 mismatches.
* **Maximal-system search** (`maxsys.py`, own code, does not use `trans.c`). For every tail set C
  and every total assignment of admissible heads, I tested the system against all decompositions.
  For bip1 the heads lie outside N[C] ∪ N(g); for bipx locality is per tail. On orders 4–7, CLT-B1
  never fails. B-local systems fail exactly in `FCRV?` and `FCZUO` (n = 7), both with d(g) = 2.
  This matches E30(A) and Table 2.
* **Minimal orders** (`minimal.py`):
  - cross-local bipartite systems with unrestricted in-degree first fail at n = 5 (`DEk`, `DTw`,
    `D]w`, all with d(g) = 2), which is finding 1;
  - without cross-locality and with d(g) ≠ 2 they first fail at n = 6 (7 graphs, including `EEiW`,
    `ECqg`, `EErw`);
  - chains fail at n = 5 only with d(g) = 2.
* **L1* + EE** (`l1ee.py`, own code).
  - n = 5: 60 instances and 4 failures.
  - n = 7: 2,210 instances and 39 failures, every one with N(x) ∩ (A − g) ≠ ∅.
  - The existential form never fails.

  This matches E30(E) and §7. The implication L1E ⇒ ST is correct: removing the terminal edge xg
  from P_x gives a decomposition of G − gx in which P_c only shrinks. In the revision's n = 9 data
  (`/tmp/claude-0/l1ee_9.txt`), the failure list agrees exactly with my brute force on the 891
  graphs of order 9 with one even vertex and at most 13 edges (18,606 instances, 449 failures, 0
  mismatches).

### Code review of `enum.c` and `trans.c`
* **`enum.c`.**
  - Each decomposition is produced once. The DFS grows the path from a deterministic vertex with a
    remaining end, and closes it at any vertex with a remaining end (also continuing past it).
  - The pruning tests are valid necessary conditions:
    - the parity of Σb;
    - d(v) ≤ 2P − b(v);
    - the parity of d(v) − b(v);
    - at least 2 ends in each component of the remaining edges.
  - The dead-state memo is keyed by (remaining edges, remaining end profile), which determines
    whether a completion exists, and it stores only states with no completion.
  - Violation sets: av(c, a) for every a ≠ c on P_c, and ne(c, p) for the two ends of a path,
    intersected with the universe. Minimality is a subset test after sorting by size.
  - Limits: 64 edges (u64) and 256 atom bits. These are fine for n ≤ 11 but not for n = 12 (2n²
    exceeds 256 for the ne bits, and K_12 has 66 edges), although `MAXN` is 12. This does not
    affect the reported data (n ≤ 9).
* **`trans.c`.**
  - A system is a hitting set of the minimal violation sets iff it is unsatisfiable. This stays
    correct after restricting members to av atoms or by the degree filters.
  - The search branches on the unhit member with the fewest admissible atoms. It is complete for
    these shapes: every shape predicate is hereditary, and `ok_add` tests exactly the shape on
    X ∪ {a}.
  - Iterative deepening goes to K = 10 for n ≤ 8 and K = 8 for n = 9. That exceeds the maximal size
    n − 1 of a B-local system, and also of a bipx2 system for odd n.
  - Shapes checked:
    - `bip1`: in-degree ≤ 1, tails are not heads, heads are not adjacent to their own or other
      tails.
    - `bipx`: in-degree ≤ 1 and bipartite. Locality comes from the `-v 1` universe, which allows
      a = g.
    - `match`, `bip`, `in1`, `lin`, `bipx2`: as documented.
    - `gdeg=3` skips exactly the graphs with d(g) = 2.
    - `h1` (atoms unsatisfiable alone) means atoms in every minimal violation set. Correct.
* **Sanity checks.** `lsearch` returns NONE on every example system above, and OK with a valid
  witness on satisfiable ones. `clt_lib.check` rejects a witness with a path removed.

### Reproduced numbers (E30(A), Table 2)
`nauty-geng -cq n | audit_enum -v 1` gives 2, 7, 13, 130, 224 graphs with at most one even vertex
for n = 4..8. Then `audit_trans SHAPE 10` gives:

| shape | n=4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|
| star | 0 | 0 | 0 | 0 | 0 |
| bip1 | 0 | 0 | 0 | 0 | 0 |
| bipx (all d(g)) | 0 | 0 | 0 | 2 | 0 |
| bipx, gdeg=3 (d(g) ≠ 2) | 0 | 0 | 0 | 0 | 0 |
| bipx2, d(g) ≠ 2 | 0 | 0 | 0 | 0 | 0 |
| match | 0 | 0 | 0 | 2 | 0 |
| bip | 0 | 3 | 1 | 46 | 16 |
| in1 | 1 | 2 | 10 | 34 | – |
| lin | 0 | 2 | 3 | 14 | – |
| any | 1 | 4 | 12 | 105 | 222 |

All entries are as reported, except "any" at n = 8 (finding 14).
* **The n = 7 bipx and match hits** are `FCRV?` (av(0,1), av(4,6)) and `FCZUO` (av(2,1), av(5,6)).
  Both have d(g) = 2 with g on a triangle, and a head adjacent to another tail.
* **E30(C).** With `enum -v 0` and `trans match 10 h1`, there is nothing at n ≤ 6 and there are 18
  graphs at n = 7, including `FCdcw` with av(2,0), av(5,3), av(1,4).

### Order 9
* **Graph count.** `nauty-geng -cq 9` has 11,936 connected graphs with at most one even vertex, as
  stated; 2,805 of them have d(g) = 2.
* **d(g) = 2 slice, complete (own enum runs).** 44 graphs have a B-local failure, and none has a
  CLT-B1 failure (finding 13). One caveat: `xargs` corrupted graph6 strings that contain `\`, so
  those 68 graphs and the graph after each one (128 in all) were re-run with `xargs -d '\n'`.
* **The remaining 1,217 graphs (the session's `v1_9_*_rest.txt`).** These files contain all
  1,217 graphs and end cleanly. `trans bip1 8` finds 0 failures. `trans bipx 8 gdeg=3` finds 0
  failures. `trans bipx 8` finds exactly the two d(g) = 2 graphs above.
* **Own enum runs on the remainder with d(g) ≠ 2** (20 s limit). 239 of the 1,132 graphs finished,
  with 0 failures of either kind; 4 hit the time limit, and the run was stopped there.
* **A random sample of 125 graphs with d(g) ≠ 2 (own enum runs).** 0 failures.
* **Conclusion.** Given the reviewed `enum.c`, the revised Table 2 row (11,936 graphs; 0, 0, 44, 0)
  is supported. Note that the column "+ 2-cycles" for the remainder was not re-run.

### Random tests
* **`python3 rand_clt.py bipx 12 50 999 500000`:** ok = 50 (2 by local search), fail = 0,
  undecided = 0.
* **`python3 rand_clt.py bip1 13 50 998 500000`:** ok = 50, fail = 0, undecided = 0.
* **Witnesses are checked.** `clt_lib.check` checks every exact-DFS witness, and `lsls.search`
  returns only after `assert check(...)`.
* **`clt_lib.check` is genuinely independent.** It is pure Python and shares no code with
  `lsearch.c`. It checks simple paths on edges of G, every edge used exactly once with all edges
  covered, ends = deg mod 2, and every av, ne, es and sep condition.
* **Generator review.** bipx uses per-tail locality, heads may be adjacent to other tails, and
  graphs with d(g) = 2 are redrawn. bip1 puts heads outside N[C] ∪ N(g). Both are B-local and
  maximal as claimed; finding 9 is about what they contain.

### t6 base
* **The requested run.** `head -1 /tmp/claude-0/resid_K2.g6 | python3 t6all.py 20000 3000` prints
  `M^~~\zYV{Znfx~~u_ labellings 624 found 624 none 0 unknown 0` (15 s).
* **Regenerating the input.** `gen_resid.py 1 8 2 7 K2` regenerates exactly this graph, and
  `gen_resid.py 1 8 2 13 C4` gave `MQ~~a}cjwFj~~~}F_`.
* **My own checker** (`t6check.py`):
  - it builds J = B + z with N(z) = U and asserts that z is the only even vertex of J;
  - it builds M = J − {zx_1, zx_2, zx_3, zy_2, zy_3, x_1y_2, x_2y_3};
  - it checks (E1)–(E5) and (E7) of t6-dense Definition 2.1 directly on the witness.

  With it, all 624 + 368 labellings of these two graphs, and all 720 of the first ∅-shape graph with
  |O| = 10, have a verified (E7) base.
* **`t6probe` builds the same M.** `t6probe.base_graph` adds z as a new vertex joined only to y_1
  and removes the edges x_1y_2 and x_2y_3; its assertion that x_3 is the only even vertex holds.
  `t6probe.system` is (E1)–(E5), (E7).
* **The counts are consistent.** The labellings per shape (368, 432, 528, 624, 720) and the totals
  16,032, 8,016, 2,208 and 26,256 all agree.

## Status of the clt session's revision (working tree on top of `9aff2a3`, at hand-back)

The revision is not committed at the time of writing. Against it:

**Resolved:**
* Finding 1: the minimality now holds among graphs with d(g) ≠ 2, `DEk` is given, and confinement
  is exempted.
* Finding 2: (M0) is added, and "exact" is dropped.
* Finding 3: the proposition now minimises ν.
* Finding 4 (a)–(d).
* Finding 5.
* Finding 6: items 1–5, and item 6 in the form "when g exists". Item 1 is now justified by the
  completed order 9 (see Order 9 above).
* Finding 7.
* Finding 8: defined after Definition 2.1.
* Finding 9: the instance counts are reported, and a new form bip1m was added.
* Finding 10.
* Finding 11.
* Finding 12: `csys_case_leaf` is now described as a transfer.
* Finding 13: Table 2 now reads 44, and the text reads 46 and "44 of 46 on a triangle".

**Remaining points:**
* **(M0) text.** "The child (with the constraint of c_1 dropped)". If y is a tail, y becomes even in
  G − c_1y, so its constraint must be dropped too. That constraint is satisfied by P_y = c_1y, as
  the text says. Write "with the constraints of c_1 and, if y is a tail, of y dropped".
* **§4 opening.** "Each example below is minimal among graphs with deg g ≠ 2", but Example 4.2
  (the path c g a) has deg g = 2. Exempt 4.2 as well; it is minimal outright.
* **Finding 14** is not fixed: E30(A) still has "any ... 221".
* **connections.md §AE.1** still says "Every relaxation fails, minimally (manuscript §4, hand
  proofs)" and lists "unrestricted ne atoms (every graph)" without "trivially". **§AE.4's
  heading** still says "exactly where it stops". **E30(B)** still says "Minimal counterexamples
  (manuscript §4, hand proofs)". All three should be qualified the way §4 now is.
* **Not re-audited.** The new random form bip1m and its counts, and the triangle-base data
  (E30(G), commits `921fd2a`/`9aff2a3`).

## Response of the clt session (applied after hand-back)

All findings are applied in the committed revision:
* **Remaining points above:** (M0) now drops the constraints of c_1 and, if y is a tail, of y
  (y is even in the child); §4 now says Examples 4.3–4.5 are minimal among graphs with
  d(g) ≠ 2 (4.1, 4.2 are minimal outright, 4.6 is the smallest failure at d(g) = 2); E30(A) "any"
  is marked K = 6 with the n = 8 value 222 at K = 10; connections §AE.1 ("every relaxation fails",
  small examples, most with hand proofs, minimal among d(g) ≠ 2; ne atoms "trivially"), §AE.4
  ("where it stops when g exists") and E30(B) ("small counterexamples") are qualified.
* **Order 9:** the enumeration of the remaining 1,217 graphs finished; all 11,936 graphs of order 9
  are covered: CLT-B1 0, CLT-B (d(g) ≠ 2) 0, B-local with d(g) = 2: 44 graphs (`HCdbMKv`,
  `HQhTVQx` among them), all with g on a triangle and a head next to another tail; together with
  n = 7, 46 failures, 44 with g on a triangle.
* **Random (finding 9):** bip1m (bip1 redrawn until at least two avoid sets are nonempty): 1,200
  instances at orders 11–14, 0 failures (counts in E30(D)); not re-audited, as noted.
* **L1* + EE at n = 9** (all 11,936 graphs): 897 of 341,950 fixed-x instances fail, all with
  N(x) ∩ (A − g) ≠ ∅; the existential form (L1E) has 0 failures.
