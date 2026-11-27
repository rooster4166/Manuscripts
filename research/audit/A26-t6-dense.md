# A26 — Audit of t6-dense (manuscript, `T6Dense.lean`, E28)

Date: 2026-11-27. Referee stance: adversarial. Grades: **SOUND**, **GAP** (fixable), **ERROR** (false as stated), **OVERCLAIM** (true content, overstated).

**Versions.** The audit started at 61476a5. The branch moved four times during it:
- 21df0c5: `LovaszBase`;
- 6898ade: order-9 data;
- 09a6999/e92bd89: the L1* subsection and scripts README;
- 8ba3391: lean-mode cells for ∅ and |O| = 10.

Everything below was re-checked at **8ba3391**. Line numbers refer to `t6-dense.tex` at 8ba3391 (672 lines), and "TM l." to `terminal-matching.tex`.

**Auditor scripts** (not committed; in the session scratchpad): `relabel.py` (dense cores from TM's order-9 list) and `equiv.py` (the equivalence check of §2.1).

---

## 0. Headline

1. **The mathematics is correct.** I checked every step of Theorems 2.2 and 2.3 by hand: the legality of each append, the classification after steps 1–3, the leaf conditions, the transport of the static condition, and the identification. Lemma 2.5, Lemma 3.1 and Lemma 4.1 are SOUND. Proposition 4.2 is **true**, but its one-line proof sketch is incomplete (GAP).
2. **The Lean is faithful.**
   - `lake build` is green (18,398 jobs), with no `sorry`.
   - The ten main declarations use only `propext`, `Classical.choice` and `Quot.sound`.
   - `splBase` is M plus two isolated vertices, `baseM`/`LovaszBase` are Definition 2.1 verbatim, and the Lean (E6) matches the paper's (E6) exactly.
3. **Main novelty finding.** The (E7) branch of Theorem 2.2 is an **equivalence**, not a reduction. An (E7)-base exists iff J has a star-terminal Lovász decomposition with transitions x_i z y_i in which, in addition, **x1y2 is terminal at y2 and x2y3 is terminal at y3**. I proved the converse (§2.1) and confirmed it on all 14,144 labellings at order 9 (0 disagreements).
   - So Conjecture 5.1 is, up to the (E6) escape, **STL-P plus two extra prescribed terminal edges**. That is a *strengthening* of the known sufficient condition STL ⇒ Test1, not a weaker or different-kind statement.
   - The paper never says this. Its "one even vertex / Lovász setting" framing does not distinguish Conjecture 5.1 from STL itself.
4. **Further novelty overclaims.**
   - End-path tracking was proposed verbatim in TM §9(1).
   - "No earlier reduction ... to a statement with one even vertex" is false: STL / `test1_of_stl`, and TM Theorem 8.2.
5. **One ERROR.** The new paragraph after Conjecture 5.1 (l. 462–465) mis-states the root-shape theorem for isolated roots. Isolated-root failures have D ∉ {∅, K2, P3, K3, C4}, so "Conj 5.1 implies T(6)-i" needs MR Thm 144 as well.
6. **Data reproduce.**
   - The spot check matches.
   - An independent exhaustive order-9 run gives 168/168 roots.
   - The data are overstated in four places: "every root" (16 roots are undecided); the missing K2 lean-mode cell; undefined modes; the "failures" column.

## 1. Verdict per claim

| Claim | Verdict | Notes |
|---|---|---|
| Def 2.1, degrees of M (l. 180–204) | SOUND | z has degree 1, x3 drops by 1, x1, x2, y2, y3 drop by 2. `baseM_parity` proves it. |
| Thm 2.2 (append chain) | SOUND | §1.1. The Lean conclusion omits "the three paths through z are x_i z y_i ⋯" (L1). |
| Thm 2.3 (protected step) | SOUND | §1.2. (E6) is slightly stronger than needed (O1). |
| Cor 2.4 | SOUND | `test1_of_stl` needs exactly d ≥ 3 at N(z); d(z) = 6 follows from hN. |
| Lemma 2.5 (labellings) | SOUND | All three cases checked. Not formalised (O2). |
| Lemma 3.1 (transport) | SOUND | Equals `fanPred_append`/`fanPred_self`, statement for statement. |
| Lemma 4.1 (Fan with end paths) | SOUND | Reroutes keep the vertex set and the far end; new ends arise only at chain vertices (in N(u)) and at u. v = t = x0 is harmless. |
| Prop 4.2 | TRUE; GAP in proof | §1.3. The sketch "replace every path through y2 by P_{y2}" misses three of the replacements. |
| Remark 3.2, §4 commentary | SOUND | Nit: l. 450 says "whenever q0 = y3 is a target", but q0 is always a target. |
| §5 L1* subsection (l. 473–497) | Informal; no error found | It is heuristic ("joint statement"). The DTw citation is to L1S. |
| Conj 5.1 ⇒ T(6)-i (l. 462–465) | **ERROR** | F1. |
| Conj 5.1 as "base" / "Lovász setting" (l. 150–154, 465–471) | **OVERCLAIM** | F2: it is STL-P plus two terminal edges. |
| Novelty, §1 and §7 (l. 160–169, 595–624) | **OVERCLAIM** | F3, F4. |
| Data claims (l. 53–57, 145–148, 581–586, 622–623) | **OVERCLAIM** | F5, F6. |
| "follows from one Lovász decomposition" (l. 45) | OVERCLAIM | One base gives STL at y1, y2, y3 only. Test1 needs bases for labellings covering all six roots (F7). |

### 1.1 Theorem 2.2, step by step

- **Step 1.** ℓ3 is isolated in M ⊕ {ℓ2, ℓ3}, so P_{y3} avoids it. The append is legal.
- **Step 2.** The path ending at x2 in D1 cannot be P_{y3}ℓ3: its other end would be x2, and then P_{x2} ∋ y3, against (E5). So it is the copy of P_{x2}, which avoids y3. Legal.
- **Step 3.** The path ending at y2 is not P_{x2}+y3 (that would put x2 on P_{y2}, against E2) and not P_{y3}ℓ3 (against E4). ℓ2 is isolated. Legal.
- **Classification (`split_abc`).** Each path of the base is extended at most once, since the three extended paths are distinct by the arguments above. The four-case classification is exact.
- **Leaf conditions (`leafOK_three`).** I checked all twelve cases, each from E1–E3 plus isolation of the leaves.
- **Step 4.**
  - R ends at x1 and is in one of the four classes.
  - In the ℓ2-class, Q has ends y2 and x1 and contains y2, against (E7).
  - In the other classes the added vertex ≠ y2.
  - `LeafOK.of_cover` applies because y2 ∉ {z, x1, x2, x3, ℓ2, ℓ3}.
- **Steps 5–7.**
  - The z-path avoids x1, ℓ2 and ℓ3.
  - The ℓ2-path is not the z-path (that one avoids ℓ2), and it avoids x2 and ℓ3.
  - The ℓ3-path is neither of these two.
  - All appends are legal.
- **Step 8.**
  - Each leaf lies on exactly one path (`idz`/`id0`/`id1`), each S_i carries one leaf, so the collapse is injective on supports.
  - `collapse_hE/hEinj/hcov` give the edge bijection, and the end counts come out right.
  - If S_i ends at y_i, the leaf path was the single edge ℓ_i y_i (ℓ_i has the single neighbour y_i in `spl … []`). Then the image is x_i z y_i (`HasShortShort`); otherwise `LongAt`.

### 1.2 Theorem 2.3

- **The transport.** It yields exactly three outcomes for FanPred D3 (y2) x p with p ∉ {ℓ2, y3, ℓ3}: pred in D0; x = ℓ3 with pred read from y3; x = y3 with pred read from x2. These match l. 382–386 and `split_abc`'s last clause.
- **The cases of x.**
  - x2 has no end in D3.
  - ℓ3 is not adjacent to y2.
  - ℓ2 has no end in D0.
  - Every other x is in N_J(y2) ∖ {z, x2}.
- **The hypotheses of `walk_step_protected`.** hB, hZ and hb are discharged as on l. 373–378.
- **A redundant clause.** (E6) at w = y3 is not needed. The outcome "pred in D0, read from y3" arises only through FanPred D1 (y2) y3 p, and D1 has no end at y3. So that branch is vacuous, and (E6) could drop w = y3 (O1). Mode `endA` is exactly this weaker (E6).

### 1.3 Proposition 4.2 and the separations of TM Thm 8.2

I listed every use of the six separations in the proof of TM Thm 8.2 (TM l. 600–647):

| Separation | Used in | What replaces it |
|---|---|---|
| {x1, ℓ1} | Step 4, ℓ1-path avoids x1 | "ℓ1-path avoids x1" (kept) |
| {x3, y3} | Step 1, Q3 avoids x3 | "P_{y3} avoids x3" |
| {ℓ1, y3} | Step 1, Q3 ≠ Q1 | "ℓ1-path does not end at y3" |
| {y2, y3} | Step 1, "Q3 avoids y2", used in Step 3 to exclude Q3ℓ3 as the origin of Q2 | P_{y2} ≠ P_{y3}, **plus** Lemma 4.1: the origin has an *end* at y2 |
| {x2, y2} | Step 3, origin of Q2 avoids x2 | "P_{y2} avoids x2", via tracking |
| {ℓ1, y2} | Step 3/4, Q2 and the ℓ2-path avoid ℓ1 | "ℓ1-path does not end at y2" |

- With y2 ∉ V(P2) ∪ N(T2), Lemma 4.1 gives Q2 ⊆ V(P_{y2}^{D1}) ∪ T2. Every remaining step of TM's proof (Steps 4–5, distinctness) then goes through. So **Prop 4.2 is true**.
- The proof description on l. 429–431 ("every path through y2 replaced by P_{y2}") is incomplete. Step 1's three separations and the Step 3 origin argument must also be replaced as in the table (F8).
- **Scope.** y2 ∉ N(T2) with q0 = y3 forces y2y3 ∈ D. Admissibility (ii) forces y2x3 ∈ D. So Prop 4.2 reaches only shapes with a D-path x3 y2 y3. The paper does not claim more.

## 2. Novelty versus known T(6)-i reductions

### 2.1 The (E7) theorem is reversible (the triviality question)

**Claim (auditor).** For a fixed labelling with x1y2, x2y3 ∈ E(J), the following are equivalent:

- (a) M has a Lovász decomposition with (E1)–(E5), (E7);
- (b) J has a Lovász decomposition D (b(z) = 0) such that:
  - every path through z is S_i = x_i z y_i ⋯ with x_i an end;
  - the path ending at y2 ends with the edge x1y2;
  - the path ending at y3 ends with x2y3.

**Proof sketch.**

- **(a) ⇒ (b).** This is Theorem 2.2. Step 4 creates the y2-end with terminal edge x1y2, and step 2 the y3-end with terminal edge x2y3. Later appends happen at other ends, so these terminal edges survive.
- **(b) ⇒ (a).** Undo the appends: delete x_i z from each S_i, then the terminal edges x1y2 and x2y3, then zy2 and zy3.
  - Each deletion removes an end-edge.
  - S2 and S3 are not short, because y2 and y3 end on other edges.
  - The path T ending at y2 and the path T′ ending at y3 have length ≥ 2, since x1 and x2 already end on S1 and S2.
  - The cases T = S3, T′ = S1 and T = T′ are harmless.
  - The result decomposes exactly M, with one end everywhere except x3.
  - Each of E1–E5, E7 holds *automatically*:
    - P_{x1} = T − y2 avoids y2, and P_{x2} = T′ − y3 avoids y3;
    - P_{y2} and P_{y3} descend from S2 and S3, so they are different and avoid x2 and x3;
    - the far end of S1 is not y2, and if it is y3 it is cut back to x2.

**Computational confirmation (exact search).**

- Left side: `dense.py`'s `endT` query on M.
- Right side: an `lsearch` query on J♯ with:
  - b = 0 at z, ℓ2, ℓ3;
  - `sep` on the three split vertices;
  - `es (x_i, ℓ_i, V∖{x_i})`, `es (y2, x1, V∖{y2})` and `es (y3, x2, V∖{y3})`.
- Run over all 14,144 labellings with chain edges of the 28 dense-core J of order 9: **14,128 OK/OK, 16 NONE/NONE, 0 disagreements.**

**Consequences.**

- Conj 5.1 restricted to (E7) is the statement "STL-P for some pairing, with x_i short, plus two prescribed terminal edges forming the alternating Hamiltonian path y1 x1 y2 x2 y3 x3 in G = (J−z)+F, each edge terminal at its forward end".
- It implies STL-P ⇒ STL ⇒ Test1, with nothing in the converse direction.
- (E6) relaxes the terminal-edge requirement at y2, but in the data it is almost never needed:
  - 2 of 144 lean-mode residual roots;
  - 0 of 168 roots at order 9;
  - 24 of 42,432 (root, labelling) pairs.
- So the "reduction" is correct and uniform, but it is a *re-encoding of a strengthening*. The six-separation obstruction disappears because nothing is being reduced, not because a finer mechanism closes a gap.
- Conj 5.1 is **not** obviously equivalent to Test1, so the reduction is not circular. But nothing in the paper argues that Conj 5.1 is easier than STL-P, and the "one even vertex" framing does not distinguish them: STL is already a condition on one Lovász decomposition of J, which has one even vertex (synthesis §19).

### 2.2 Is anything claimed as new already known?

- **End-path tracking (novelty item 2, l. 165–166): already in TM.** TM §9(1) (TM l. 957–960) says: "For the other shapes it needs a finer tracking than vertex sets: what must avoid x_i is only the path *ending* at y_i, not every path through y_i. Alternatively, a chain design whose walks use the edges ... would do." Synthesis §22 (ptm, 14:04) says the same.
  - Remark 3.2 (l. 401) credits this correctly.
  - The §1 bullet presents it as a new observation: OVERCLAIM (F3).
  - What *is* new: the length-one chain design on the cross edges x1y2, x2y3 (Lemma 2.5), the exact end conditions, the (E6) transport, and the Lean.
- **"The six-separation base cannot be met for D ≠ C4" is correctly attributed.**
  - It is TM §9(1) (TM l. 936–946) and §Z.4, from ptm commit 4cc426d (14:05, before this session).
  - Two refinements are worth stating:
    - it depends on Def 8.1's exclusions y2 ∉ V(P2), x2, x3 ∉ V(P1) and y3 ∉ P1 (§Z.4 says so; l. 108–111 does not);
    - with (ii) y2 ∉ N(x3) as well, **Thm 8.2 as stated applies to no dense shape at all**, since C4 violates (ii). The paper says this for C4 (l. 112–114), which is consistent.
- **"No earlier reduction of the dense shapes to a statement with one even vertex" (l. 623–624): false as worded.**
  - `test1_of_stl` reduces all of T(6)-i to STL, a condition on Lovász decompositions of J (one even vertex).
  - TM Thm 8.2 reduces to a base with one even vertex x3, even though it is unsatisfiable here.
  - The §7 list (l. 597–608) also omits:
    - STL/STL-P (synthesis §§19–20);
    - B3 ⇔ T(6)-i (endpoint-structure Cor 30, `rooted_six_of_bstmt3`; ROADMAP l. 425);
    - the d6-frontier hub transfers (A9).
- **Closures.** The paper claims none, which is correct. Nothing it calls new is a known closure. The dense shapes remain open per STATUS §3.5(a), the reader notes and A6.

**Verdict on novelty.**
- New: a correct, fully formalised reformulation of the dense T(6)-i residual. It shows that a strengthened STL-P (two extra terminal edges, or the (E6) relaxation) suffices, uniformly over the five shapes, with no chain hypothesis.
- Known before: the key idea (end-path tracking) and the obstruction analysis are TM §9(1).
- Overclaimed: the claim to a new kind of reduction ("single base statement in Lovász's setting"). The paper must state the equivalence of §2.1 and present Conj 5.1 as a strengthening of STL-P.

## 3. Lean faithfulness

- **Build and axioms.**
  - `lake build`: green at 61476a5, e92bd89 and 8ba3391, with no `sorry`/`admit` (grep and build log).
  - `T6DenseAxioms.lean` prints the three standard axioms for `star_of_appendBase`, `star_of_protectedBase`, `stl_of_appendBase`, `test1_of_appendBases`, `append_full`, `baseM_parity`, `appendBase_of_lovaszBase`, `stl_of_lovaszBase` and `test1_of_lovaszBases`. `fanPred_append` uses only `propext` and `Quot.sound`.
  - `GallaiLean.lean` imports `T6Dense`.
- **`splBase` is M ⊕ {ℓ2, ℓ3}.**
  - On the `inl` side it removes zx2, zy2, zx3, zy3 (in `splitG`), zx1 (in `spl`), x2y3 and x1y2: the seven edges of M. With hN, z keeps only zy1.
  - `inr 0` and `inr 1` lose both their edges (`splBase_iso`).
  - `baseM` is literally `delList J [7 edges]`.
  - `LovaszBase` asks ends = degree mod 2 and E1–E7 on V, i.e. Def 2.1 verbatim. `appendBase_of_lovaszBase` transfers it correctly via `pushOn Sum.inl`.
- **(E6).**
  - `∀ p ∈ {x2, x3}, (∀ w, J.Adj y2 w → w ≠ z → w ≠ x2 → ¬FanPred D0 y2 w p) ∧ (J.Adj y2 y3 → ¬FanPred D0 y2 x2 p)`.
  - `FanPred D u x z` means "read from the end x, z is just before u", i.e. pred_u(x) = z. This is exactly the paper's (E6), l. 199–202.
- **(E1).** It is stated for both ends of the z-path. That is equivalent to the paper's, since z is an end.
- **Definitions.**
  - `STL`, `StarAt`, `LongAt` and `HasShortShort` are used exactly as in `StarTerminal.lean` l. 68–79 and 352–354.
  - `Test1` is as in `ThreeConnected.lean` l. 186. `test1_of_appendBases` matches `test1_of_stl`'s hypotheses (hdeg, the parity premise).
- **No hypothesis is vacuous or hidden.** hN, Nodup and the chain edges are all stated in the paper, and `AppendBase` is not stronger than Def 2.1. The data (§4) show the hypotheses are satisfiable.
- **Gaps.**
  - **L1.** `star_of_*` conclude only StarAt plus (LongAt ∨ HasShortShort) at y_i. Thm 2.2's "the three paths through z are x_i z y_i ⋯ with x_i an end" carries a Lean tag (l. 215–217) but is not in any Lean statement. Either strengthen the conclusion (S1, S2 and P7 are at hand in `split_finish`) or restrict the tag to "In particular".
  - **L2.** Stale names and numbering (non-mathematical):
    - `T6Dense.lean` l. 25 and 37 cite `stl_of_protectedBase`, which does not exist;
    - l. 1469, 1537 and 1677 say "Theorem 2.1", "Theorem 2.2" and "Corollary 2.3" for Thm 2.2, Thm 2.3 and the STL corollary;
    - the header step 5 has push and appends in the wrong order;
    - `dense.py` l. 18–23 says "Theorem 3.1/3.3/2.1" and "endZ is the form proved in Lean" (false: Lean's form is `leanE6`);
    - `c4.py` l. 19 cites `c4_walk`, which does not exist.
  - **L3.** Lemma 2.5, the per-root form of Cor 2.4, and the RS/Thm 144 step from Conj 5.1 to T(6)-i are unformalised. The paper says so for Lemma 2.5.

## 4. Data

- **Spot check.**
  - Compile `lsearch.c`.
  - `gen_resid.py 2 8 2 5 C4 | dense.py lean 2 2000000` gives `roots=12 roots_ok=12 … bad=0 notok=0 … via_endT=12` (1.6 s), as expected.
- **Independent exhaustive order 9.**
  - `relabel.py` on TM's `d6_9.g6` keeps 28 dense J: 2 ∅, 6 K2, 8 P3, 5 K3, 7 C4.
  - `dense.py lean 2 0` certifies 168/168 roots, all via (E7), with an empty stderr.
  - This agrees with the E28(B′) the session added during the audit.
- **Code faithfulness.**
  - `base_query` builds M exactly (it asserts that x3 is the only even vertex).
  - `lsearch` checks `ef`/`ep`/`es` on closed paths only (`close_ok`), so the memo stays exact. `es` reads the start end for an occurrence p→q and the last end for q→p, which is correct.
  - Mode `lean` runs `endT` (E1–E5 + E7), then `leanE6`, whose mask is (N_B(y2) − x2) ∪ {x2 if y2y3}. This is exactly `AppendBase`.
  - `walksim.fan` is Fan's forced chain: it excludes the just-rerouted path and fails when a blank is hit. `static_pred_ok` is `walk_step_protected`'s hB.
  - `run_walk` uses distinct leaves (the split graph), then `unlift_J`. `check_decomp` checks simple paths, every edge of J once and the end profile; `star_ok` checks star-terminality.
  - LongAt/short is not checked, but it is automatic.
  - `endZ` is *stronger* than Lean's (E6), so endZ bases are AppendBases.
- **Mismatches and overstatements.**
  - **D1. Mode `endA` is weaker than the paper's (E6).** Its mask omits y3, i.e. the redundant clause of §1.2. Mode `end` drops E5/E6 and runs Fan walks. The six-separation mode is not the hypothesis of any theorem here.
    - So the table rows with these modes (l. 566–568) are not instances of Thms 2.2/2.3. §6 "Method" defines only `lean` and `endZ`.
    - "Failures" (l. 581) counts only verification failures of conforming bases. Per E28(A), the protected step failed for 216/1,050 six-separation bases and 288/1,280 `end` bases. The 0 in row l. 566 hides this.
  - **D2. K2 has no lean-mode residual cell.**
    - At 8ba3391, `out/lean_*.log` covers:
      - C4, K3, P3 and ∅ at |O| = 8 (∅: 42/48);
      - C4 and P3 at |O| = 10 (P3: 44/48, 3 via E6).
    - `out/lean_K2_8.log` is still empty.
    - For K2, the evidence of append bases is order 9 (6 graphs) plus endZ on 3 residual graphs. The row at l. 568 does not say "3 per shape".
    - "Further cells are logged in E28" (l. 586) is vague. The E28 row "(K2, P3, C4 subset)" is unexplained.
  - **D3. "Every root" is false.**
    - It appears in the abstract l. 53, §1 l. 145–146, §7 l. 622–623 and connections AD.3.
    - 16 roots in three graphs are undecided: endZ P3 6, lean* ∅ 6, lean* P3 |O| = 10 4. §6 l. 583–586 says so correctly.
    - l. 582–583 "(E6) was needed for 2 of the 144 roots" predates the new rows; it is now 5 of 278.
  - **D4. "Carrying the residual conditions of a smallest failure" (l. 54, 146–147).** `gen_resid.py` imposes a subset. It omits:
    - C4 twins of degree ≥ 8 (degree-6 twins are a closed case);
    - MR Thm 144's d(r) ≥ 8 and ≥ 3 T-neighbours;
    - the bad-vertex table of the reader notes.
  - **D5. The six-separation comparison (l. 56–57, 588–593)** covers 5 C4 graphs, and every search was undecided. That is not evidence of absence. The abstract should say "within the budget" (the body does).

## 5. Required fixes

- **F1 (ERROR, l. 462–465).**
  - "If it is isolated in D, then D − r ∈ {∅, K2, P3}" confuses C = B[U] with D. RS's isolated root (A6 RS9) has no neighbour in U, so D ⊇ K_{1,5} at r and D is **not** one of the five shapes. Conjecture 5.1 does not cover it.
  - Fix: write "isolated in C", and invoke MR Thm 144 (failing roots may be taken with ≥ 3 neighbours in T; Shaik-free per ROADMAP) to exclude isolated roots. Alternatively, extend Conj 5.1 to D = K_{1,5} ∪ D′ with labellings y1 = r (Lemma 2.5's y1-case still works).
  - Also fix l. 85–86 to say that RS needs a core neighbour, and add a per-root Cor 2.4 to support "only the roots not already closed need a base".
- **F2 (framing).**
  - State the converse of §2.1 as a proposition: (E7)-base ⇔ star-terminal Lovász decomposition with transitions x_i z y_i and x1y2@y2, x2y3@y3.
  - Present Conj 5.1 as a strengthening of STL-P (implied by nothing weaker, implying STL-P).
  - Reword the abstract l. 57–59, §1 l. 150–154, §5 l. 465–471 and §7 l. 616–624 accordingly.
- **F3 (novelty, l. 165–166).** End-path tracking was proposed in TM §9(1) (TM l. 957–960). Say that this paper carries it out. Credit the new parts: the length-one cross-edge chain design and the (E6) transport.
- **F4 (novelty, l. 597–608, 623–624).** Delete or correct "no earlier reduction ... one even vertex". STL/`test1_of_stl`, STL-P ⇔ PTM3 and TM Thm 8.2 are such reductions. Add them, B3 ⇔ T(6)-i and d6-frontier to the list of known reductions.
- **F5 (data, l. 53, 145–146, 622–623; connections AD.3).**
  - Replace "every root" by "every root except 16 undecided ones in three graphs (budget or labelling cap)".
  - Update "(E6) was needed for 2 of the 144 roots" (l. 582–583). With the new rows it is 5 of 278.
- **F6 (data table).**
  - Define modes `end`/`endA`/six-separation, and note that `endA` is (E6) without w = y3.
  - Report the 216/288 protected-step failures in the six-separation/`end` row, or drop those modes from the failures column.
  - Say "3 graphs per shape" for l. 568.
  - Add the missing lean-mode K2 residual cell (`lean_K2_8.log` is empty), or say that K2 is covered only at order 9 and by endZ on 3 graphs.
  - Make "Further cells are logged in E28" specific.
- **F7 (l. 45).** "Hence the first deletion test at z, follows from one Lovász decomposition": one base gives STL at three roots. Say "from bases for labellings covering all six roots".
- **F8 (Prop 4.2, l. 429–431).** Replace the one-line proof description by the table of §1.3. The Step 1 separations {ℓ1,y3}, {y2,y3}, {x3,y3} and the Step 3 origin argument also need replacing.
- **F9 (Lean tag, l. 215–217).** Either add the transitions to the `star_of_*` conclusion, or restrict the tag to the "In particular" STL part (L1).
- **F10 (staleness).** Fix L2: Lean doc names and numbering, the `dense.py` and `c4.py` docstrings.

## 6. Optional suggestions

- **O1.** Drop w = y3 from (E6). It is redundant (§1.2). In Lean, refine `split_abc`'s transport: FanPred D1 y2 y3 p is impossible because D1 has no end at y3. This weakens Conj 5.1, and `endA` then becomes the exact hypothesis.
- **O2.** Formalise Lemma 2.5 (a finite check on D with Δ ≤ 2) and a per-root `test1`-from-STL lemma.
- **O3.** Measure the cost of the strengthening:
  - how often STL-P holds for a labelling while neither (E7) nor (E6) has a base;
  - at order 9, 16 labellings have no (E7)-base and 8 have neither; whether STL-P holds for those pairings is not recorded;
  - better, look for J where STL-P holds for every pairing but some root has no base.
- **O4.** l. 251–253: the length-one chain violates TM Def 8.1(ii) whenever y2x3 ∈ B, and TM Conj 8.6 concerns far-apart N(z) only. "Never needed" is true but slightly misleading; say "not used".
- **O5.** The §5 L1* subsection should say that the (E7) conditions are exactly the reversibility conditions of §2.1. That explains why each is "binding" when dropped.
