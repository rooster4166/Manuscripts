# A25. Audit: "Lovász's induction for the avoidance conjecture L1*: unconditional transfers, a two-sided reduction of the blocked case, and where the candidate induction hypotheses fail"

- **Date:** 2026-11-27
- **Auditor:** fresh subagent (adversarial referee). I made no edits to the manuscript, the Lean files or the authors' scripts and outputs, and I committed and pushed nothing. I created only `research/audit/A25-l1-induction.md` and `research/audit/A25-scripts/`.
- **Scope:**
  - `manuscripts/l1-induction/l1-induction.tex`, compiled twice with `pdflatex` in a scratch copy (`/tmp/claude-0/a25/ms/`). There were no errors, no undefined references and no overfull boxes. The committed PDF has the same text (`pdftotext` diff empty).
    - Numbering of the fresh PDF: Lemmas 2.1, 2.2; Theorem 3.1, Definition 3.2, Proposition 3.3, Corollary 3.4; Conjecture 4.1 (TR), Lemma 4.2, Example 4.3, Conjecture 4.4 (ST), Definition 4.5 (ST′), Theorem 4.6, Proposition 4.7, Remark 4.8; Example 5.1, Proposition 5.2; Table 1.
    - I checked every statement and proof, the abstract, "Results", "Honest status", Table 1 and Sections 6–8.
  - The citations of L1S (`manuscripts/l1star/l1star.tex`), TF (`manuscripts/tight-fan/tight-fan.tex`) and RD, against those sources (compiled for their numbering).
  - `lean/GallaiLean/L1Induction.lean`, and the definitions it uses (`Admissible`, `AvoidDecomp`, `L1Blocked`, `L1StarGen`, `L1Star`, `LInfty`, `delEdge`, `evenSet`).
  - `manuscripts/l1-induction/scripts/` (all `.cpp`, `.h`, `.py`) and `scripts/out/`, `manuscripts/l1-induction/README.md`, `research/experiments.md` E27, `research/connections.md` §AC.
- **Out of scope:**
  - Commits after the audited one, made by the authors' concurrent session while I worked: `8f6ef3c`, `acfbe3b`, `587b14b`, `e817922`, `1138198`, `f6a25b7`.
    - They change `randtest.cpp` and `stprime.cpp`.
    - They add `stprime9_v2.txt`, `rand_*_v3.txt`, `slice11_{0,1,2,3}of100.txt` and a `.gitignore`.
    - They extend `l1e_check13.txt`.
  - `70a4122` ("audit A25 (in progress): auditor scripts snapshot") was also committed by another session. It is a snapshot of my unfinished `A25-scripts/`. I committed nothing. The files in this directory supersede that snapshot (`t_calc.cpp` now also counts tests with c ∉ A).
  - None of these touches the manuscript, the PDF, the Lean file, `README.md`, E27, §AC, or any script or output that I audited below, except `l1e_check13.txt`, which I audited at `cca465c`.
  - The order-10 Rec run was not re-run in full. I re-ran only the failing graphs (§5).
- **Audit scripts:** `research/audit/A25-scripts/` (outputs in `A25-scripts/out/`).
  - **Independent library `a25.h`.** I wrote it for this audit. It uses none of the authors' code. It contains:
    - an own graph6 decoder;
    - an enumerator of path decompositions with prescribed end counts by **transition systems**. At each vertex it chooses b(v) end edges and pairs the rest, and keeps union-find chains that must stay paths. This is a different algorithm from the authors' path growing in `lind.h`/`dec.h`;
    - an avoidance oracle pruned on the component that carries c's end;
    - an own forced-chain simulation.
  - **Validation** (`v_enum.cpp` against the pure-Python path-growing enumerator `v_enum.py`): 636 (graph, b) cases, 0 mismatches. Every decomposition is checked, and none is duplicated (`out/v_enum.txt`).
    - The cases are: orders 3–5 with Lovász b and three random feasible b each; all of order 6 with Lovász b; 400 graphs of order 7 with Lovász b (9,087 decompositions).
    - Every count I re-derived below also agrees with the authors' code, which uses a different algorithm.
  - **Drivers using only `a25.h`:**
    - `t_calc.cpp`: every move of Theorem 3.1 as stated, every A;
    - `t_inst.cpp`: the explicit instances;
    - `t_trst.cpp`: TR, trall, ST, ST′, by full enumeration (orders 5 and 7);
    - `t_trst9.cpp`: TR, ST, ST′ at order 9 with the pruned oracle, a node budget and monotone inference over A, on a 1-in-10 sample;
    - `t_exch.cpp`: Lemma 4.2 and the coverage counts;
    - `t_walk.cpp`: the Proposition 3.3 and Fan-route census;
    - `t_walklift.cpp`: executes the proof of Proposition 3.3;
    - `t_rec.cpp`: an independent implementation of Rec, with Definition 3.2's moves as stated and flags for the code's variants;
    - `t_hff.cpp`: TF's H??FFf}.
  - **Analyses of the committed lists:** `a_lists.py`, `a_twoeven.py` (networkx only).
  - **Drivers that `#include` the authors' `moves.h` or `lind.h` unmodified,** to test or classify their implementation: `t_recadm.cpp`, `t_recroute.cpp`, `t_gaproute.cpp`, `t_trsplit.cpp`. They need `-I<snapshot>/manuscripts/l1-induction/scripts`.
  - `A25AxiomCheck.lean`: run from `lean/` with `lake env lean`, then deleted from `lean/`. Its output is `out/A25AxiomCheck.out`.
  - The authors' tools were rebuilt with `g++ -O2` from a `git archive` copy of `cca465c` in `/tmp/claude-0/a25/snap/`. The re-run log is `out/rerun_authors.txt`.
- **Version audited:** branch `claude/l1-induction`, commit `cca465c` (as instructed).

| file (at `cca465c`) | md5 |
|---|---|
| `manuscripts/l1-induction/l1-induction.tex` | `866927533b9dd0d1caebbf051c48787d` |
| `manuscripts/l1-induction/l1-induction.pdf` (committed) | `4fbdb77e354c811adea5deb64f07ac6b` |
| `manuscripts/l1-induction/README.md` | `1f78afc5abf4bb0d50accc16969f619e` |
| `lean/GallaiLean/L1Induction.lean` | `a2076b5c067f9efb32eea63d03ee094b` |
| `manuscripts/l1-induction/scripts/lind.h` | `c9eb724194a2d80e943d39d1dd368cd2` |
| `manuscripts/l1-induction/scripts/orc2.h` | `2cdf878587adc57e247835002d750083` |
| `manuscripts/l1-induction/scripts/dec.h` | `a5834e6d3ce3ff935352753a09b121bc` |
| `manuscripts/l1-induction/scripts/moves.h` | `f987f59c97d28320f34050a0c5f6cd1b` |
| `manuscripts/l1-induction/scripts/rec2.cpp` | `e9ed331e78a50d9b28a0f6c24d83b4ed` |
| `manuscripts/l1-induction/scripts/rec.cpp` | `b897cc9022ba2498e0d14d7f265c04b9` |
| `manuscripts/l1-induction/scripts/tr2.cpp` | `2e206feb1b33033bb6aa8d37de877772` |
| `manuscripts/l1-induction/scripts/trall.cpp` | `b2c03e15949ef1f5385c7b7a4332698f` |
| `manuscripts/l1-induction/scripts/stprime.cpp` | `b392de4adf2a73c160c0e50cbddb7dc3` |
| `manuscripts/l1-induction/scripts/tt.cpp` | `8a4a5e1b950bbf6228d0289ee489ceed` |
| `manuscripts/l1-induction/scripts/rechoice.cpp` | `c995d50f0cce7a6d971d651113219079` |
| `manuscripts/l1-induction/scripts/exch.cpp` | `6c31596f899cc08f4dfcf4356a62358a` |
| `manuscripts/l1-induction/scripts/l1e.cpp` | `3f22a8ce4b06fb4c5f71945a4a86dc13` |
| `manuscripts/l1-induction/scripts/targets.cpp` | `5701015cdb747858dcae3a6cbdad95ce` |
| `manuscripts/l1-induction/scripts/alltarget.cpp` | `4def088e624976bdebe6208d55ab9606` |
| `manuscripts/l1-induction/scripts/gap.cpp` | `cd41943ef34032e94de324750ed1baf7` |
| `manuscripts/l1-induction/scripts/minobs.cpp` | `7a860c1222c19fbd43e7ae05eee9348c` |
| `manuscripts/l1-induction/scripts/walk2.cpp` | `144eace83cc77589a91bbb942ec59863` |
| `manuscripts/l1-induction/scripts/walkadm.cpp` | `be5dc278d7dc7c499fa55fa56aecf691` |
| `manuscripts/l1-induction/scripts/xcheck2.cpp` | `d93a233e279f7b6c53186776aee7f30a` |
| `manuscripts/l1-induction/scripts/randtest.cpp` | `47ed3c6cac81d406549ddafadc46ef62` |
| `manuscripts/l1-induction/scripts/randg.py` | `6587f3eb67cc6bc8f92dc98c06f3d04d` |
| `manuscripts/l1-induction/scripts/example.cpp` | `64b7879e302ebb8d4df0dd5fabf14145` |
| `research/experiments.md` | `d2c22516d40833f5c5e203a18e53b239` |
| `research/connections.md` | `0a8a6a9c75835ac2340373a871aa95f3` |
| `manuscripts/l1star/l1star.tex` (cited) | `243c540236f89f0a0fb33ebdb560c4d3` |
| `manuscripts/tight-fan/tight-fan.tex` (cited) | `0555290fe0638e2ecac6530ef0da0082` |

## 0. Verdict

**The main mathematics is correct: Proposition 3.3, Lemma 4.2, Theorem 4.6, Proposition 4.7, Example 4.3 and Proposition 5.2. The Lean file is faithful. But Theorem 3.1 is false as stated in a degenerate case (c ∈ A). The census claims about the Fan route and the TR walks are wrong. The Rec counts describe the code, not Definition 3.2.**

- **Sound.** The following hold, each checked by hand and computationally:
  - Proposition 3.3, including the parity bookkeeping for trails that revisit vertices. The proof was executed on 50,878 lifts with 0 failures.
  - Lemma 4.2. All 375 exchanges at order 7 were performed and verified.
  - Theorem 4.6 and Proposition 4.7, by hand, and with my own oracle for both A.
  - Example 4.3, Example 5.1 (all six stuck instances), Proposition 5.2, Corollary 3.4.
  - With `c ∉ A`, every move of Theorem 3.1, including the claimed relaxations, transfers goodness on every instance to order 7 (0 violations in 109,875 child-good tests with c ∉ A), and the measure always decreases.
- **F1 (ERROR, Theorem 3.1).** The theorem says "no admissibility is assumed", and the definition of an instance allows c ∈ A. With c ∈ A, moves **(d)** and **(h)** do not transfer goodness. Example: K_{1,3} with centre c and A = {c}, move (d). There are 26,365 violations to order 7, every one with c ∈ A. The first base case of Rec also fails for c ∈ A.
  - The fix is one hypothesis (c ∉ A).
  - The code never meets c ∈ A, so no computation is affected.
- **F2 (ERROR, data).** "The Fan route of [L1S, Prop. 5.3] applies to none of them" is false. The census never tests Prop 5.3's d(c) = 1 clause. Prop 5.3 applies to **149** of the 15,277 blocked Amax instances at order 9, and 45 of these have no Proposition 3.3 walk.
- **F3 (ERROR, data).** The "tight targets allowed (valid under TR)" walk counts (12,980 / 4,283 / 13,259 = 87%; walkadm 24/83 and 4,283) count trails that TR does not license: two consecutive tight vertices, or an end split that makes G* inadmissible. Restricted to what TR licenses, the counts are **6,552 / 2,325 / 7,506 (49%)**, and 12/83 at order 7.
- **F4 (ERROR, citation).** G?Bvvo is in L1S §8, not §7.
- **Gaps** (F5–F7):
  - The implemented Rec is not Definition 3.2's Rec. It uses (b), (c) also for c ∈ N(g), which is valid but not stated; with the moves as stated, **301** order-9 instances are not certified, not 209 (Rec_T: 203, not 56). It also restricts (h) to at most 8 shortest routes; with every route, one or two more instances are certified (208, 55).
  - The definition of move (t) omits c ∉ N(g).
  - The proof of Theorem 3.1 is a one-paragraph sketch.
  - The `lind.h` port is not validated in the manuscript. The audit closes this.
- **Wording and overclaims** (F8–F16):
  - TR is used in Theorem 4.6 only where its conclusion is L1* itself. The random TR tests are all in that regime.
  - "A local repair is not enough".
  - "Minimal shape": only 619 of the 1,238 have it.
  - The two-even core: none of the 476 bad d(c) = 1 targets is a two-even instance at distance ≥ 3.
  - "No class within k steps … is closed" does not follow from the gap data.
  - "L1E does not supply ST".
  - "Exactly the condition under which TR holds".
  - The DEk dead end is mislabelled in Table 1.
  - "Every reduction of L1S".
- **Data.**
  - **Every number quoted from a committed output is reproduced.** Re-running the authors' tools gives byte-identical files (tr2 9, stprime 9, rechoice 9, l1e 9, stuck0 9, rec_adm9_MBT, rec_sub9_MBT, explore9_MBT, tt_stuck0_9, rand_11_13_v2, rand_15). rec2 reproduces rec.cpp's NOREC list exactly.
  - Every number without a committed output that I re-ran also reproduces.
  - Independently, with my own oracle, I re-derived:
    - TR, trall, ST and ST′ exhaustively at orders 5 and 7, and TR, ST and ST′ on a 1-in-10 sample of order 9 (1,194 graphs). ST/ST′ agree exactly with the authors' tools on the same graphs (12,666 / 12,666 / 12,516). TR has 0 violations in 173,138 decided tests (175,435 child-good, 2,430 budget-undecided; the authors' tr2 gives 175,568 on the same graphs);
    - the exch coverage counts at order 7;
    - the 3,969 walk count;
    - Rec at orders 6–9 (an own implementation gives the authors' order-9 failure lists exactly, in their move set);
    - the six stuck instances and their per-target counts;
    - Example 4.3, Proposition 4.7, DEk and H??FFf}.
  - E27 has one false data sentence (F17).
- **Lean.** `L1Induction.lean` has no `sorry`. All eight theorems use only `propext`, `Classical.choice`, `Quot.sound`, and the library is up to date. `TightTransfer`, `SomeTarget` and `SomeTargetLocal` state exactly Conjecture 4.1, Conjecture 4.4 and Definition 4.5 (§4).

| class | findings |
|---|---|
| ERROR | F1 (Thm 3.1 (d), (h), Rec base case with c ∈ A), F2 (Fan route "none": 149), F3 (TR-walk counts not licensed by TR), F4 (L1S §7 → §8) |
| GAP | F5 (implemented Rec ≠ Def 3.2: unstated (b), (c) with c ∈ N(g), so 301 vs 209 at order 9; (h) restricted to ≤ 8 shortest routes), F6 (Def 3.2 (t) lacks c ∉ N(g); Thm 3.1 proof is a sketch), F7 (`lind.h` not validated in the manuscript; closed by audit) |
| WORDING | F8 (TR used only in L1*'s own regime), F9 ("local repair not enough"), F10 ("minimal shape"), F11 (two-even core), F12 (gap ⇒ "no class within k steps"), F13 (L1E "does not supply ST"), F14 ("exactly the condition"), F15 (DEk dead end), F16 ("every reduction of L1S"; unannounced relaxations) |
| DATA | F17 (E27 "0 for d(c) ≥ 5 or d(g) ≥ 6" false), F18 (committed outputs incomplete), F19 ("K_{3,3} needs the split (e)" false) |
| NIT | N1–N9 |

## 1. Findings

### Errors

**F1 (ERROR, statement; Thm 3.1 l.163–203, Def 3.2 l.209–215; abstract l.42–44; README "Proved on paper"; §AC.2).** Theorem 3.1 says "No admissibility is assumed of either instance". The definition of an instance (l.85) is "G with at most one even vertex, c odd, and A ⊆ V(G)", so c ∈ A is allowed. The proof says (l.193–194) that the consequences of admissibility "that some vertex lies outside A" are replaced by "c ∉ A in (a) and (c), and x ∉ A in (b) and (c)". That list is incomplete.
- **(d) needs c ∉ A.** The merge (L1S Lemma 2.2) needs A ∌ x = c. The merged Q_c is Q_ℓ with ℓ replaced by c, so it contains c.
  - **Counterexample:** G = K_{1,3} with centre c and leaves y, a, b; A = {c}; move (d) at y.
  - H(G; c, y) has edges ca, cb, yℓ, and c is even. The decomposition {ℓy, acb} is Lovász, and Q_ℓ = ℓy avoids A ∪ {c}. So the child is good.
  - (G, c, {c}) is not good, since every Q_c contains c.
- **(h) needs c ∉ A.** The new Q_c = Q′_g ∪ R contains c. The child's avoidance set A ∪ (V(R) ∖ {g}) contains c whether or not c ∈ A, so the child's goodness does not see c ∈ A.
  - **Counterexample:** vertices g, r, c, a, b; edges gr, rc, ga, rb; d(g) = 2, so g is the only even vertex.
  - R = g r c, A = {c}. The child G − E(R) = {ga, rb} with terminal g is good (Q_g = ga). The parent is not.
- **(i)** is undefined for c ∈ A ("the component of c in G − A").
- **Base case 1 of Definition 3.2** ("no even vertex, d(c) = 1, and the neighbour of c is not in A") certifies (K₂, c, {c}), which is not good. So "every instance in Rec is good" (l.221) fails as stated.
- **Exhaustive test** (`t_calc.cpp`, orders 3–7, every A ⊆ V, `out/t_calc_3_7.txt`). Violations of "child good ⇒ parent good":
  - (d): 2,302;
  - (h): 10,207, plus 13,856 for routes with c ∈ N(g).
  - **Every violation has c ∈ A.** With c ∉ A there are 0 violations for every move (table in §3.1).
- **No computational consequence.** `moves.h` `base_case` returns 0 for c ∈ A, and `rec()` rejects c ∈ A. From an admissible root, every move keeps c ∉ A: (a), (c), (d), (h) put the old terminal into A but never the new one, and (e), (g), (i) add only vertices ≠ c.
- **Fix:** require c ∉ A in the definition of an instance (l.85), or add c ∉ A to (d), (h), (i) and to the first base case. Correct the sentence at l.193–194.

**F2 (ERROR, data claim; l.271–272; abstract l.65–68; E27(E); §AC.2).** The text says: "At order 9, with A = V∖(N[c]∪N(g)), Proposition 3.3 applies to 3,969 of the 15,277 blocked instances. The Fan route of [L1S, Prop. 5.3] applies to none of them." The abstract says "where the Fan route of [L1S] applies to none".
- **What L1S Prop 5.3 says.** The path R = g e_1 ⋯ e_k must satisfy c ∉ V(R), e_i ∉ A, and N(e_k) ∩ A ⊆ {e_{k−1}}, with "e_i ∉ N(c) for i = 1, …, k, **or d(c) = 1**".
- **What the script tests.** `walk2.cpp` mode 0 forbids N[c] on the route (`FORB = closed_nbhd(G, c)`), so it never tests the d(c) = 1 clause. In mode 0 its "Fan route" can never succeed at a blocked Amax instance: every route vertex is in N(g) ∖ N(c) and keeps its A-neighbour.
- **Independent census** (`t_walk.cpp`, unbounded): Prop 5.3 as stated applies to **149** of the 15,277 blocked Amax instances at order 9, all with d(c) = 1.
  - 104 of them are also among the 3,969 with a Proposition 3.3 walk, and 45 are not (`out/t_walk_9.txt`, `FANROUTE` lines).
  - Order 7: 4 of 83.
- **Example (order 7):** F?q_w, edges 04 05 14 25 36 46 56, g = 0, c = 3, A = Amax = {0,1,2}.
  - Blocked: 4 is adjacent to 1 ∈ A, and 5 is adjacent to 2 ∈ A.
  - d(c) = 1. R = 0 4 6 has N(6) ∩ A = ∅.
- **Consequences.**
  - "applies to none" is false under either reading: none of the 15,277, or none of the 3,969.
  - "It extends … the Fan route (Proposition 5.3 there)" (l.261–263) is also wrong. The end conditions are incomparable (remaining degree two with non-adjacent neighbours, against no A-neighbour), Prop 5.3's d(c) = 1 clause is not covered, and 45 Fan-route instances have no walk.
- **Fix:** "Proposition 3.3 applies to 3,969 and Prop 5.3 to 149 (all with d(c) = 1; 45 of them without a walk)". Say that the walk complements Prop 5.3, generalising it from paths to trails and replacing the end condition, rather than extending it. Correct the abstract, E27(E) and §AC.2.

**F3 (ERROR, data claim; l.273–274; §6 l.639–641; E27(D), (E); §AC.2 "With TR it applies to 87%").** The text says: "If tight targets are allowed on the trail (valid under TR), the walk applies to 12,980 and the Fan route to 4,283; together they cover 13,259 (87%)", and "walks to admissibility (walkadm.cpp, assuming TR: 24 of 83 … 4,283 of 15,277)".
- **What TR licenses.**
  - Restoring w_{i−1}w_i at a tight w_i applies TR to K_{i−1}, whose even vertex is w_{i−1}. TR (Conj. 4.1) needs c ∉ N(w_{i−1}). Edges at c are never removed, so this means w_{i−1} ∉ N(c).
  - If w_{i−1} is also tight, the even vertex of K_{i−1} is adjacent to c. No proved lemma or conjecture covers that step.
  - A non-tight step after a tight one is fine, by L1S Lemma 2.4. That lemma needs only c ∉ N(w) ∪ {t, w}.
- **What the scripts do.**
  - `walk2.cpp` mode 1 and `walkadm.cpp` allow any trail with w_i ∉ A ∪ {c}, so they allow two consecutive tight vertices.
  - For the split at a tight end w_k (mode 1), c is one of w_k's two remaining neighbours. G* gains the edge c–y, so (G*, c, A) is admissible only if y ∉ A. This is not checked.
- **Independent census** (`t_walk.cpp`, unbounded trails, `out/t_walk_9.txt`). The unrestricted counts reproduce the authors' exactly: 12,980 / 4,283 / 13,259, and 24 at order 7. Restricted to trails TR licenses:

| order 9, blocked, Amax | split (walk) | Fan trail | either |
|---|---|---|---|
| as computed (walk2 mode 1 / walkadm) | 12,980 | 4,283 | 13,259 (87%) |
| licensed by TR | **6,552** | **2,325** | **7,506 (49%)** |

  At order 7 the TR-walks to admissibility (walkadm) number **12**, not 24, of 83.
- Rec_T is not affected: its move (t) in `moves.h` checks `!G.has(g, c)`.
- **Fix:** correct the counts, or state the additional transfer they need (a tight step whose source is adjacent to c). Correct E27(D), (E) and §AC.2.

**F4 (ERROR, citation; l.456).** "H is the two-even example G?Bvvo of [L1S, §7]". L1S §7 is "Formalisation". G?Bvvo appears in L1S **§8** (Open problems, item 2: `G?Bvvo`, `te3walk.py`).
- The identification itself is correct: H?ABvrw minus its leaf 5 is isomorphic to G?Bvvo (networkx, `out/a_lists.txt`). G?Bvvo has even vertices of degrees 2 and 4, and the leaf of H is hung at the one of degree 2.
- **Fix:** [L1S, §8].

### Gaps

**F5 (GAP/DATA; Def 3.2 l.209–219; §5 l.437–441, l.462–465; §6 l.590–611; E27(A)).** The certificate class that the code computes is not the Rec of Definition 3.2.
- **Move (h).** Definition 3.2 uses the moves of Theorem 3.1. There (h) allows any g–c path with interior outside A, and the text stresses that chordless or shortest paths are not needed. `moves.h` implements (h) only for up to 8 *shortest* g–c paths in G − A. `MV_ROUTE_ALL = 0` in every reported run, and the code also requires c ∉ N(g).
  - With every simple route (`t_recroute.cpp`, which sets `moves.h`'s own globals `MV_ROUTE_ALL = 1`, `ROUTE_MAXLEN = 64`):

| order 9, A = Amax | implementation (reported) | Rec with every route |
|---|---|---|
| Rec (MB) | 209 not certified (163 blocked) | **208 (162)**; `H?bm~z\|` c = 3 is certified |
| Rec_T (MBT) | 56 (35) | **55 (34)**; `H?zfVzv` c = 5 |
| Rec_T, every admissible A | 57 (36) | **55 (34)**; `H?zfVzv` c = 5 with A = {3,4,6} and {4,6} |

  - Order 10 (the 29 and 17 failing graphs): unchanged, 54 and 33.
  - The gap table is unchanged with every route (`t_gaproute.cpp`, `out/t_gaproute_7_8.txt`).
  - The six stuck instances are unaffected: g ∈ A, so (h) never applies.
- **Moves more general than stated.** The code applies (b) and (c) also when c ∈ N(g); Theorem 3.1(b), (c) assume c ∉ N(g).
  - These transfers are valid: (b) by L1S Lemma 2.4, which needs only c ∉ N(w) ∪ {t, w}, and (c) by L1S Theorem 4.2(c), which has no such hypothesis. `t_calc.cpp` finds 0 violations in 10,556 and 7,264 child-good tests. But they are not the moves the manuscript lists.
  - **They matter.** My own implementation of Rec (`t_rec.cpp`, Theorem 3.1's moves as stated, own move generator) gives at order 9 with A = Amax:

| moves | (h) routes | not in Rec (blocked) |
|---|---|---|
| (b), (c) only for c ∉ N(g), as stated | every route | **301 (162)** |
| (b), (c) also for c ∈ N(g), as `moves.h` | at most 8 shortest, c ∉ N(g), as `moves.h` | **209 (163)**, = the authors' count |
| (b), (c) also for c ∈ N(g) | every route | **208 (162)** |
| (b), (c) only for c ∉ N(g), plus (t) (Rec_T as stated) | every route | **203 (103)** |
| (b), (c) also for c ∈ N(g), plus (t) (Rec_T) | at most 8 shortest, as `moves.h` | **56 (35)**, = the authors' count |
| the same plus (t) (Rec_T) | every route | **55 (34)** |

  - Orders ≤ 8 are unaffected in every variant: all 1,792 Amax and 27,837 subset instances of order 8, and all 2,150 of order 7, are certified even with the stated moves.
  - So the 209/56 of the manuscript is exactly reproduced by an independent implementation of the moves *as coded*. Rec and Rec_T with Theorem 3.1's moves as written miss 301 and 203 at order 9.
- **Soundness of the implementation.** Every (G, c, A) with c ∉ A and A arbitrary at orders 4–7 that `moves.h` certifies is good by my oracle: 22,133 instances, with and without TR (`t_recadm.cpp`, `out/t_recadm_sound_4_7.txt`). So the transfers are sound as implemented. The gap concerns only which class the numbers describe.
- **Fix:**
  - State (b), (c) without c ∉ N(g) in Theorem 3.1, citing L1S Lemma 2.4 and Thm 4.2(c), since the counts depend on them (301 against 209; 203 against 56).
  - Either say "(h) restricted to at most 8 shortest routes in G − A, and to c ∉ N(g)" next to the counts, or re-run with every route and correct 209/163, 56/35, 57/36 to 208/162, 55/34, 55/34.

**F6 (GAP; Def 3.2 l.216–218; proof of Thm 3.1 l.186–203).**
- **(a) The move (t).** It is defined as "a tight target x ∈ N(g) ∩ N(c) with A ∩ N[c] = ∅, x ∉ A". TR also needs c ∉ N(g) and g the only even vertex. `moves.h` checks `!G.has(g, c)`, so the code is right, but the definition is not.
- **(b) The proof of Theorem 3.1.** It is a sketch: "these are the reductions of L1S … admissibility is used for exactly two things". There is no per-move check, and the list of replaced consequences is wrong (F1).
  - I checked every move by hand against L1S (§3.1) and computationally. With c ∉ A all are correct, including the relaxations: (g) without c ∉ N(g) or y_1 ∉ N(g); (h) with non-chordless routes and with c ∈ N(g); (e) with any w ∈ {u, v} ∖ {c}; (f) even with c ∈ N(g).
  - Two of these relaxations are not announced: (h) also drops L1S's c ∉ N(g), and (g) also drops y_1 ∉ N(g).
- **Fix:** add c ∉ N(g) to (t). Replace the proof by a short per-move list. Mention all dropped hypotheses.

**F7 (GAP, validation; §6 "Tools and validation" l.580–587; E27 "Tooling").** Every exhaustive test except the dec.h-based ones uses `lind.h`. The manuscript says it is "a port of `l1s.c` [L1S], which was validated there against brute force". But the port itself is not validated here. `xcheck2.cpp` checks `orc2.h` against `dec.h`, and both are new code. `orc2` shares `orc::solve` with `lind.h` but not its first-path search (`orc::extend` from c with `f`).
- **Closed by this audit.** My transition-system oracle reproduces:
  - every TR, trall, ST and ST′ count at orders 5 and 7 exhaustively, and TR, ST, ST′ on a 1-in-10 sample of order 9 (§5);
  - the coverage counts;
  - the walk counts;
  - the stuck instances and all per-target D′ counts of `tt_stuck0_9.txt`.
- **Fix:** add a direct cross-check of `orc::avoid`, or cite this audit.

### Wording and overclaims

**F8 (WORDING, interpretation of the reduction and of the TR data; Thm 4.6 l.360–378; abstract l.45–53; §4.1; §6 l.619–622 and random tests l.644–658; §AC.1).** In the proof of Theorem 4.6, TR is applied to the blocked admissible instance (G, c, A) itself. So A is admissible for G, and TR's conclusion "(G, c, A) good" is the very L1Blocked instance to be proved.
- **What the reduction needs.** Theorem 4.6 needs only TR_adm: TR for A with A ∩ N(g) = ∅. TR_adm is implied by L1Blocked. The part of TR beyond L1* (A meeting N(g)) is used only by Rec_T and Proposition 5.2. The reduction is correct, but its "transfer side" is, as used, a sub-case of the goal.
- **Consequences for the data.**
  - Of the 3,764 TR tests at order 7, **2,156** have A admissible for G. Those test L1* itself, which L1S verified exhaustively to order 11. Only **1,608** test TR beyond L1* (`t_trst.cpp`). At order 9 the split is **637,572** admissible (82,812 of them with A = ∅) against **1,097,584** meeting N(g) (`t_trsplit.cpp`, which is tr2's loop with each test classified; `out/t_trsplit_9.txt`).
  - The random TR tests (`randtest.cpp`: A = Amax only; 32,267 + 10,460 tests) are **all** in the admissible regime. They test L1*, not TR beyond it. The abstract's "Both held on random graphs of orders 11, 13 and 15" and §AC.1's "random n = 11, 13, 15: 42,727 tests" should say so.
- **Fix:** add "Theorem 4.6 uses TR only for A admissible for G (TR_adm, implied by L1Blocked)". Report the admissible/inadmissible split of the TR tests, and say that the random TR tests use A = Amax.

**F9 (WORDING, overclaim; l.326–327; §8 item 2 l.692–694; E27(B) "So a proof of TR must re-choose D′"; §AC.2; §AC.4 "but not by repairing a given D′").** The text says "So a proof of TR must in general re-choose D′; a local repair of a given D′ is not enough."
- **What the data show.** Conditions (1) and (4) miss 9,665 of the 34,778 good D′ (A = Amax, order 7), and 8,841 of those have a bad *plain* Fan image.
- No other repair was tested, and the exchange lemma is itself a local repair of the Fan image. So the data do not show that local repairs fail.
- **Two further imprecisions.**
  - (2) and (3) are special cases of (1), which should be said. (2) ⇒ (1) is stated. (3) ⇒ (1) holds because chain vertices lie in {g} ∪ N(x): the static condition held for 18,058 D′, none with the chain through c (`t_exch.cpp`).
  - The counts are for A = Amax and all tight pairs with c ∉ N(g), not only blocked instances. That should be said.
- **Fix:** "conditions (1) and (4) do not cover all good D′; for most of the rest the plain Fan image is bad, so a proof must either re-choose D′ or repair the image by another argument".

**F10 (WORDING; l.404–407; §8 item 1 l.688–689; E27(C) "This is the d(g) = 2 minimal shape"; §AC.1).** The text says: "Of these, 1,238 have d(g) = 2, which is the minimal shape of [L1S, Corollary 5.6(5)]."
- **What the minimal shape is.** In L1S Cor 5.6(5), the shape for d(g) = 2 with N(g) ⊆ N(c) is uv ∉ E **and g ∈ A**.
- **The counts** (`a_lists.py` on `stprime9.txt`):
  - all 1,238 have N(g) = {u, v} independent;
  - only **619** have g ∈ A;
  - the other 619 have g ∉ A, and there the split (e) gives an admissible all-odd child of smaller ν.
- At order 7, 10 of the 20 ST′ failures have g ∈ A.
- In Proposition 4.7, FEhv? with A = {3,5} has g = 4 ∉ A, so it is *not* the minimal shape. With A = {3,4,5} it is.
- **Fix:** "d(g) = 2 and N(g) ⊆ N(c) independent; in 619 of them g ∈ A (the minimal shape of [L1S, Cor 5.6(5)])". Correct E27(C) and §AC.1 for A = {3,5}.

**F11 (WORDING/UNCLEAR, the "two-even core"; l.527–532, l.568–569, §8 items 1 and 3; §AC.1).**
- **(a) Distance.** "If d(c) = 1 with neighbour y, and y has no neighbour in N(g), then … G − c, which has two even vertices y and g, has a decomposition with no ends at either. This is the two-even conjecture [L1S, Conj 3.2]."
  - Conj 3.2 is about even vertices at distance ≥ 3, which needs also y ∉ N(g). If y ∈ N(g), the two even vertices are adjacent. There the statement is false in general (L1S §3: 22,100 failures at order 10, distance 1).
- **(b) The 96% inference.** "96% of the bad targets above have d(c) = 1. So the hypothesis side of L1* contains the two-even problem" does not follow. The relevant instance is the bad child (G − gu, c, A), whose even vertex is u. Classification of the 476 bad d(c) = 1 children (`a_twoeven.py`):
  - **442**: the target u is the neighbour y of c, so y is even in the child and Q_c = cy is not forced;
  - **29**: Q_c = cy is not forced;
  - **5**: Q_c = cy is forced, with the two even vertices y, u of (G − gu) − c at distance **2**;
  - **0** are instances of the two-even conjecture.
- That L1* contains the two-even conjecture is L1S Proposition 3.3 (hang a leaf at y). That is true, but it is unrelated to these data.
- **Fix:** add y ∉ N(g) in (a). In (b), replace the inference by a citation of L1S Prop 3.3, and report the classification.

**F12 (WORDING/UNCLEAR; l.467–469, l.491–493; abstract l.61–62; §AC.3).** The text says: "A class of the form 'admissible, or at most k moves from an admissible instance' is closed only if gap ≤ k always suffices", and "No class 'within k steps of admissibility' with k ≤ 4 is closed".
- **What `gap.cpp` measures.** It measures the run of inadmissible states since the last admissible *ancestor in the certificate*.
- **Why the inference fails.** A state five moves after its last admissible ancestor may still be at most four moves from some *other* admissible instance. It is then in the class "within 4 moves of an admissible instance". So the least-gap data do not show that this class fails closure.
- **What is shown** (and reproduced: gap table, the three gap-5 certificates printed by `gap 6 5`): with these moves, no certificate of (K₈ − K₃, c, A) has all inadmissible runs of length ≤ 4.
  - The certificate description at l.485–490 is exactly right: (d); four (b)-steps 0 → 4 → 5 → 6 → 4; (h); (g).
  - Order 8 is the smallest order with gap 5 (orders 4–6 all have gap 0).
  - The run of five inadmissible states begins after the leaf move (d), whose child is admissible. "The some-target instance (G − gx, c, A) itself needs a long excursion" is loose: K₈ − K₃ is all-odd and is not a blocked instance.
- **Fix:** define "within k" along certificates, or weaken the claim to the certificate statement.

**F13 (UNCLEAR; Remark 4.8 l.418–419; §5(iii)).** The text says: "It strengthens the conclusion, but it does not supply the hypothesis ST."
- For a blocked instance, L1E-goodness gives a target x with (G − gx, c, A) good. That is ST for the instance.
- "Every blocked admissible instance is L1E-good" implies ST, and L1Blocked outright.
- Presumably what is meant is that L1E, a statement about admissible instances, cannot serve as an inductive hypothesis for the inadmissible child.
- **Fix:** say that.

**F14 (WORDING; l.509–510).** "It is exactly the condition under which TR holds."
- TR is a conjecture, and A ∩ N[c] = ∅ is its hypothesis.
- Example 4.3 shows only that A ∩ N(c) ≠ ∅ cannot be allowed in general.
- **Fix:** "It is the hypothesis of TR."

**F15 (PRESENTATION; l.520–524 and Table 1 l.558–559; E27(D)).** The dead end is not DEk.
- (DEk, 1, {0,2}) with g = 0 is **admissible**, not merely c-admissible.
- It has two good Case I children: G − 03 (tight target 3; admissible) and G − 04.
- The dead end is the child **(DEk − 04, 1, {0,2}) with even vertex g = 4**. That is a tree: 3 is adjacent to 0, 1, 4, and 4 to 2. `minobs` reports it as `g=4`.
  - Its only target outside A, 3, is **tight**.
  - Its instance-level children: (c) bad, (h) bad, (e) good (`t_inst.cpp`).
- Table 1's row "DEk, g = 0" names the parent.
- **Fix:** "the child DEk − 04 (g = 4)".

**F16 (WORDING; abstract l.42–43 "Every reduction of [L1S]"; proof l.187; §AC.2).**
- L1S Prop 5.3 (Fan route) is not in Theorem 3.1. Its transfer is unconditional too: it is a composite of (b) steps and, at the neighbour y of c when d(c) = 1, of a (c) step. When d(c) = 1, (K, c, A) is good exactly when its (c)-child at y is. This should be stated.
- Two relaxations are not announced (F6): (h) drops c ∉ N(g), and (g) drops y_1 ∉ N(g).
- "The certificate class built from all known reductions" (l.59) omits the packed base cases of `cert.py` (RD Theorems 6.1 and 6.3). `moves.h` has them only under flag `S`, which no reported run uses.

### Data

**F17 (DATA, E27(D), experiments.md l.1331).** "There are 0 for d(c) ≥ 5 or d(g) ≥ 6 (n = 9 only)" is false.
- `alltarget` gives 41 bad targets for d(g) ≥ 6, d(c) = 1, and 28 for d(g) = 2, d(c) ≥ 5.
- The true statement is: 0 bad targets when d(g) ≥ 4 and d(c) ≥ 5, or when d(g) ≥ 6 and d(c) ≥ 3.
- The manuscript itself (l.518–519) states only the correct 16/50,516.

**F18 (DATA, completeness of `out/`).**
- `badtargets9.txt` and `atfail9.txt` hold only the BADT and ATFAIL lines. The quoted 41,074 pairs, the rule counts and the (d(g), d(c)) table are not committed.
- These quoted numbers have no committed output at all:
  - order-7 TR (3,764), trall (6,672 / 8,066 / 14), ST/ST′ at order 7 (406 / 386);
  - exch (34,778 / 24,738 / 375 / 9,665 / 824), xcheck2 (31,704);
  - gap, minobs, walk2, walkadm;
  - l1e and rechoice at orders 5 and 7;
  - the `subsets` counts at orders 4–8, the |A| ≤ 2 run, the "(a)–(d) only" run.
- `rec_adm*_MB.txt` were written by the superseded `rec.cpp`.
- I re-ran all of these, and every number reproduces (`out/rerun_authors.txt`). rec2 gives exactly rec.cpp's NOREC list at order 9.
- **Fix:** commit the outputs.

**F19 (DATA; l.610 "K_{3,3} needs the split (e)"; E27(A) "K_{3,3} needs the d(g) = 2 split").** False.
- K_{3,3} (sides {0,1,2}, {3,4,5}) with c = 0 and A = Amax = {1,2} is certified by **one move (g)**: split 0 from 3 and 4, add 34, A′ = {1,2,3}.
  - The new graph is all-odd, and c is a leaf whose neighbour 5 ∉ A′. That is base case 1.
  - (e) can only enter after the leaf move (d), which creates an even vertex of degree 2. It is not needed.
- My Rec without (e) certifies all six K_{3,3} instances and all 78 of order 6 (`t_rec.cpp`, flag `E`).
- What is true is that (a)–(d) alone fail on K_{3,3} (all six instances), and on 26 of 78 at order 6 (reproduced with both implementations).
- **Fix:** "K_{3,3} needs the split (g) at c".

### Nits

- **N1 (l.147–150).** "x_{i+1} is the vertex before w on the path ending at x_i": say "on the path of 𝒟 ending at x_i". The chain is read on the original paths; a re-routed path also ends at the next chain vertex.
- **N2 (Lemma 4.2, l.302).** "for every A ∌ x": "for every A with c, x ∉ A". Here c ∉ A holds in the setting of TR.
- **N3 (Prop 3.3 proof, l.242–243).** "So w_i is the only even vertex of K_i; when w_i = g, K_i has none." The second clause is wrong. When w_i = g (a closed trail), no vertex changes parity, and g, if not isolated, is the even vertex of K_i, which the first clause already says. The rest of the parity argument is right.
- **N4 (l.457).** "five graphs, not all isomorphic": `geng` output is pairwise non-isomorphic. The six instances come from five non-isomorphic graphs. H?ABvrw with c = 7 and with c = 8 are equivalent under the automorphism 7 ↔ 8.
- **N5 (l.205–207).** "They need x ∉ A instead of A ∩ N(g) = ∅, and c ∉ A": c ∉ A is needed only for (c). `avoid_of_target_child` correctly has no such hypothesis.
- **N6 (Lean module docstring).** "each Case I reduction of L1Star.lean transfers goodness unconditionally": only (b) and (c) are re-proved here. (a) (`l1_case_adj`) and (d) (`l1_case_big`) are not.
- **N7 (Thm 3.1(f)).** The hypothesis c ∉ N(g) is not needed (0 violations in 808 child-good tests with c ∈ N(g)).
- **N8 (abstract l.50–53).** "held in all … tests": the random runs have undecided cases (ST 2 + 11, TR 150 + 146, L1E 3 + 13). They are listed in §6 but not in the abstract.
- **N9 (l.84–87).** The definition of "blocked" should say "G has an even vertex g", as L1S Definition 4.1 does.

## 2. Item-by-item grades

| # | Item (lines) | Grade | Key checks |
|---|---|---|---|
| 1 | Definitions (instance, admissible, good, blocked, target), l.84–90 | SOUND (N9; source of F1) | Match L1S Defs 1.1 and 4.1, except that A is unrestricted. |
| 2 | Lemma 2.1 (Fan with vertex sets), l.141–145 | SOUND | = RD Lemma 2.2 = L1S Lemma 2.1. |
| 3 | Forced chain, l.147–150 | SOUND (N1) | TF Prop 2.1 (`prop:forced` = 2.1). |
| 4 | Lemma 2.2 = TF Lemma 3.2, l.152–156 | SOUND | Same hypotheses as TF Lemma 3.2 (`lem:avoidc` = 3.2). Proof: c is never a chain vertex, Q_c is untouched or re-routed at its far end, or gains x ∉ A. |
| 5 | Thm 3.1 (a) | SOUND | Append gc to Q′_g. Needs c ∉ A (listed). |
| 6 | Thm 3.1 (b) | SOUND | L1S Lemma 2.4 with t = g, w = x: Z(x) = ∅, c ∉ N(x) ∪ {g, x}, x ∉ A. Also valid with c ∈ N(g) (F5). |
| 7 | Thm 3.1 (c) | SOUND | Leaf graph H(G − gx; c, x). Z(x) = ∅ (ℓ has an end; other neighbours odd, unchanged). Fan with t = g. Separations kept since x ∉ A ∪ {c, ℓ}. Merge needs c ∉ A. c ∉ N(g) is not needed. |
| 8 | Thm 3.1 (d) | **ERROR** (F1) | Correct only with c ∉ A (merge with A ∌ c). |
| 9 | Thm 3.1 (e) | SOUND | Subdivide uv by g. If the path is Q′_c it gains g, and w ∈ A′ excludes this when g ∈ A. c ∈ {u, v} is allowed. ν drops by 1. |
| 10 | Thm 3.1 (f) | SOUND (N7) | L1S Prop 5.4(ii) exchange; no admissibility used. |
| 11 | Thm 3.1 (g) and the claimed relaxation | SOUND | c is a leaf of G′, so the path through y_1y_2 avoids c, since Q′_c avoids y_1. Neither c ∉ N(g) nor y_1 ∉ N(g) is needed. 15,280 tests with c ∈ N(g), 0 violations. |
| 12 | Thm 3.1 (h) and the claimed relaxation | **ERROR** (F1) | Correct with c ∉ A, for any route (not chordless or shortest, c ∈ N(g) allowed). Then Q′_g ∩ V(R) = {g}, so Q′_g ∪ R is a path. |
| 13 | Thm 3.1 (i) | SOUND (needs c ∉ A to be defined) | A path from c avoiding ∂C stays in C. |
| 14 | Thm 3.1 measure, l.181–183 | SOUND | Checked for every move application at orders ≤ 7: 0 failures. (d): ν drops by 1; (e): by 1; (f): \|A\| drops. |
| 15 | Proof of Thm 3.1, l.186–203 | GAP (F1, F6, F16) | A sketch with an incomplete list. Every move re-verified here. |
| 16 | Def 3.2 Rec, Rec_T | GAP (F1 base case, F6(a), F5) | Rec is the largest class with (2) and (3). |
| 17 | "every instance in Rec is good"; cert.py's 35, l.221–224 | SOUND (with F1 fix) | Rec with admissible-only intermediates fails on exactly **35** of the 1,868 (`t_recadm.cpp`). Unrestricted, it certifies all 1,868. So the causal claim is supported. |
| 18 | Prop 3.3 | SOUND (N3) | Parity, admissibility of G* (c ∉ {x, y} and no edge at c touched), measure 2\|E\| − 2k − 1, the lift, the protected transfers (w_i ∉ N[c] ∪ A, t ≠ c). Revisiting trails are covered, including returns to g when g ∉ A. Proof executed: 32,590 lifts at order 7 over every admissible A (1,081 of the 2,830 trails revisit a vertex; there are 691 returns to g), and 18,288 at order 9; 0 failures. |
| 19 | Remark after Prop 3.3, l.261–263 | SOUND (k = 1 composite) / WORDING ("extends" the Fan route: F2) | |
| 20 | Cor 3.4 | SOUND | Minimality and Prop 3.3. |
| 21 | Census l.271–274 | **ERROR** (F2, F3) | 3,969 reproduced (unbounded trails). "Fan route none" is false (149). The TR-allowed counts are not licensed by TR. |
| 22 | Conj 4.1 (TR) | statement CLEAR | Lean `TightTransfer` is identical. |
| 23 | Sufficient conditions (1)–(4), l.288–296 | SOUND | (2) ⇔ (c)-child: Q′_c ≠ cx because b′(x) = 0. (3) ⇒ (1) is not stated (F9). |
| 24 | Lemma 4.2 | SOUND (N2) | The chain stops at c; Q′_c is untouched earlier; a re-route at P's far end keeps the segment x_{i−1}…x; f ≠ q because V(P) ∩ V(Q′_c) = {c} and q ≠ c. All 375 EX cases at order 7 executed: valid Lovász decomposition with Q_c = cx. |
| 25 | Coverage paragraph, l.324–330 | SOUND data / WORDING (F9) | 34,778 / 24,738 / 375 / 9,665 / 824 reproduced independently. |
| 26 | Example 4.3 | SOUND | Hand check of the edges and of D′ = {05, 1453062, 361524}: chain 4 → 1 → 0, image Q_0 = 0354162 ∋ 1, 3, 4. Oracle: (G − 46, 0, A) good, (G, 0, A) not good; all 8 good D′ have the chain through c. 14 / 8,066 violations, all meeting N(c), reproduced. Order 5 has none, so 7 is smallest. |
| 27 | Conj 4.4 (ST), Def 4.5 (ST′) | CLEAR | Lean identical. |
| 28 | Thm 4.6 | SOUND (F8) | Hypotheses of TR and of Thm 3.1(b), (c) verified. Lean proof matches. |
| 29 | Prop 4.7 | SOUND | Full hand check (§3.4), and oracle for A = {3,5}, {3,4,5}. |
| 30 | Text after Prop 4.7, l.399–410 | SOUND data / WORDING (F10) | 1,262 = 1,238 + 24 (d(g) = 4, d(c) = 5), all N(g) ⊆ N(c); 1,208; 760: reproduced (`a_lists.py`). |
| 31 | Remark 4.8 | SOUND (equivalence needs x ∉ A, true for admissible A) / UNCLEAR (F13) | 46,638 / 15,277 reproduced. |
| 32 | §5 framework (1)–(3); "largest class" | SOUND | By well-founded induction any class with (2) and (3) lies in Rec. |
| 33 | §5(i) "instance-level moves not enough", l.437–441 | SOUND data for Rec as coded / GAP (F5) | 209 / 6 reproduced; the failure list is identical with my own Rec in the coded mode. Stated moves: 301. Rec contains every admissible instance of order ≤ 8 (every A), with stated or coded moves. |
| 34 | Example 5.1 | SOUND (F4, N4) | All six: admissible, blocked, good; own move generator (a superset of Thm 3.1's moves) gives exactly four (c)-children, all bad. Mechanism holds for all six; all five edges cx can be Q_c; per-target D′ counts equal `tt_stuck0_9.txt`; 76–92%. |
| 35 | Rec_T misses, stuck states, l.462–465 | SOUND (F5) | 56 / 35, 33, 1,296, 1,184; every no-move state has N(g) ⊆ A, none admissible. |
| 36 | Gap table, K₈ − K₃ | SOUND data / UNCLEAR conclusion (F12) | Table reproduced, also with every route. |
| 37 | Prop 5.2 | SOUND / WORDING (F14) | N[c] is unchanged since c ∉ {g, x}. Upward propagation by (b) and TR. |
| 38 | Bad children, every-target, dead ends, l.512–525 | SOUND data / PRESENTATION (F15) | 496 = 476 + 20; 16 / 50,516; DEk verified. Smallest dead end at order 5. |
| 39 | Two-even core, l.527–532 | GAP/UNCLEAR (F11) | |
| 40 | §5(iii), l.534–544 | UNCLEAR wording (F13) | 82,079 and L1E reproduced. |
| 41 | Table 1 | SOUND with fixes (F10, F15) | Smallest orders confirmed: ST′ 7 (no blocked instance at order 5); stuck 9; gap 5 at 8; dead end 5; TR-sharp 7. |
| 42 | §6 Computations | SOUND with fixes (F2, F3, F5, F7, F8, F18) | All numbers reproduced (§5). |
| 43 | §7 Formalisation | SOUND (N6) | §4. |
| 44 | §8 What remains | WORDING (F9, F10, F11) | |
| 45 | Abstract, Results, Honest status | ERROR in two claims (F1 "every reduction … without any admissibility"; F2 "Fan route applies to none"), otherwise SOUND with fixes (F8, F12) | |
| 46 | E27, §AC, README | ERROR (F2, F3), DATA (F17), WORDING (F9–F12) | |

## 3. Details

### 3.1 Theorem 3.1, move by move (`t_calc.cpp`, orders 3–7, every A ⊆ V, every applicable move)

Moves exactly as stated in the manuscript, plus the more general forms used by `moves.h` (rows marked ′):

| move | child-good tests | of which c ∉ A | violations | violations with c ∉ A | measure failures |
|---|---|---|---|---|---|
| (a) | 6,885 | 6,885 | 0 | 0 | 0 |
| (b) | 6,692 | 6,692 | 0 | 0 | 0 |
| (b′) c ∈ N(g) (moves.h) | 10,556 | 10,556 | 0 | 0 | 0 |
| (c) | 6,946 | 6,946 | 0 | 0 | 0 |
| (c′) c ∈ N(g) (moves.h) | 7,264 | 7,264 | 0 | 0 | 0 |
| **(d)** | 4,604 | 2,302 | **2,302** | **0** | 0 |
| (e) | 7,632 | 7,632 | 0 | 0 | 0 |
| (f) | 1,340 | 1,340 | 0 | 0 | 0 |
| (f′) c ∈ N(g) | 808 | 808 | 0 | 0 | 0 |
| (g) | 15,640 | 15,640 | 0 | 0 | 0 |
| (g) c ∈ N(g) | 15,280 | 15,280 | 0 | 0 | 0 |
| **(h)** any route | 20,414 | 10,207 | **10,207** | **0** | 0 |
| **(h)** any route, c ∈ N(g) | 27,712 | 13,856 | **13,856** | **0** | 0 |
| (i) | 4,467 | 4,467 | 0 | 0 | 0 |
| total | 136,240 | 109,875 | 26,365 | 0 | 0 |

For (d) and (h), every child-good test with c ∈ A is the twin of one with c ∉ A, and fails. For the other moves, either the move itself requires c ∉ A ((a), (c), (i)), or the child keeps c in its avoidance set and so is never good.

Hand checks against L1S:
- (a), (c), (d) use the leaf merge (L1S Lemma 2.2), which needs A ∌ c.
- (b) uses L1S Lemma 2.4.
- (e), (f) are L1S Prop 5.4. Its hypotheses c ∉ N(g) and u ∉ N(c) serve only admissibility.
- (g) is L1S Prop 5.5. Its hypotheses c ∉ N(g) and y_1 ∉ N(g) serve only admissibility.
- (h) is L1S Prop 5.2. "Shortest in G − A" and c ∉ N(g) serve only admissibility. The path property of Q′_g ∪ R needs only that Q′_g avoids V(R) ∖ {g}.
- (i) is L1S Lemma 5.1.

### 3.2 Proposition 3.3

- **Parity.** In K_i every vertex other than g and w_i is met an even number of times by the first i trail edges. g is met an odd number of times if w_i ≠ g, and w_i likewise. So w_i is the only even vertex, also when w_i = g (N3).
- **The restore step.** It uses Fan with t = w_{i−1}, which is odd (b = 1), and w = w_i, whose neighbours are all odd or of positive odd degree, so Z = ∅.
  - The protected transfer needs c ∉ N(w_i) ∪ {w_{i−1}, w_i} and w_i ∉ A. This holds since w_i ∉ N[c] ∪ A, and w_{i−1} is g or a trail vertex ∉ N[c].
  - In the plain graph the forced chain equals the leaf-graph chain, because c ∉ N(w_i) is never a chain vertex. I used this to execute the proof.
- **G\*.** c ∉ {x, y}, no edge at c is touched, x and y keep their parity, and w_k becomes isolated.
- **Tests.** Structural checks of all found trails (3,969 at order 9): 0 failures. Lifts: 50,878, 0 failures.

### 3.3 Lemma 4.2

- **The chain stops at c.** Q′_c is the original path ending at c. Its far end q is not an earlier chain vertex, since otherwise the chain would have stopped there.
- **The path P.** c is the predecessor of x on P read from x_{i−1}, so c is interior to P.
- **Re-routing of P.** If P was re-routed at its far end x_j (j < i − 1), the segment x_{i−1} … x is unchanged, and the step at x_{i−1} turns P into P′ with ends c and f. I checked this against the chain execution: re-routing keeps vertex sets and changes only the re-routed end.
- **The exchange.** S = P′ ∪ Q′_c is a path because the vertex sets meet only in c. f ≠ q because q ∉ V(P). The edges and the end multiset are preserved.
- **Computation.** All 375 cases at order 7 give a valid decomposition with Q_c = cx (`t_exch.cpp`, `out/t_exch_7.txt`).

### 3.4 Proposition 4.7 by hand

- **The graph.** FEhv? has edges 03 04 06 13 15 16 24 25 26 35 (decoded independently). Degrees are (3,3,3,3,2,3,3), so g = 4. N(g) = {0, 2} ⊆ N(6) = {0, 1, 2}.
- **Admissible and blocked.** A = {3,5} and {3,4,5} miss N[6] ∪ N(4). 0 ~ 3 and 2 ~ 5, so the instance is blocked.
- **ST′ fails.**
  - In G − 06 − 04 the only neighbour of 0 is 3 ∈ A.
  - In G − 26 − 24 the only neighbour of 2 is 5 ∈ A.
  - The map 0 ↔ 2, 3 ↔ 5 is an automorphism fixing both A's.
- **ST holds.**
  - D′ = {61, 260315, 3524} covers the 9 edges of G − 40 with ends 6|1, 2|5, 3|4. That is Lovász, since 0 has degree 2 in G − 40.
  - The path ending at 4 avoids 0. Appending 40 gives {61, 260315, 04253}, Lovász for G, with Q_6 = 61.
- **The bad D″.** D″ = {61, 2513, 426035} is valid. The chain is 4 → 6, and the image has Q_6 = 624035 ∋ 3, 5.
- **Exchange.** D″ meets Lemma 4.2 (V(426035) ∩ V(61) = {6}, and 0 ∉ 61). The exchange gives {60, 5304261, 2513}, which is good.
- **Oracle.** For each target, A = {3,5}: 12 good D′, 9 with the chain avoiding c (all transfer), 3 through c (none transfers). A = {3,4,5}: 8, 5, 3.
- **Minimality.** No blocked instance exists at order 5, so order 7 is the smallest (`t_trst.cpp`).

### 3.5 Citations

| citation | target | status |
|---|---|---|
| [L1S] Def. (instance, blocked) | L1S Defs 1.1, 4.1 | correct |
| [L1S, Lemma 2.4] | protected transfer | correct |
| [L1S, Theorem 4.2, Lemma 5.1, Props 5.2, 5.4, 5.5] | thm:reductions = 4.2, boundary = 5.1, route = 5.2, deg2 = 5.4, deg3 = 5.5 | correct |
| [L1S, Prop 5.3] Fan route; [L1S, Prop 5.4(i)] | | correct numbers; content misdescribed (F2) |
| [L1S, Corollary 5.6], 5.6(5) | | correct |
| [L1S, §6] (`cert.py`, 35 of 1,868) | L1S §6 Computations | correct |
| [L1S, §7] (G?Bvvo) | L1S §8 Open problems | **wrong (F4)** |
| [L1S, Conj 3.2] two-even | conj:te3 = 3.2 | correct number; applicability F11 |
| [TF, Prop 2.1], [TF, Lemma 3.2], [TF, Theorem 3.3], [TF, Theorem 2.2], [TF, §7] | prop:forced, lem:avoidc, thm:l1tight, thm:protected, sec:open | correct; TF §7 item 3 poses the task |
| `H??FFf}` of [TF] | TF after Lemma 3.2 | reproduced with my chain: 3 → 6 → 0, Q_0 = 06728 |
| [RD, Lemma 2.2] | lem:fan = 2.2 | correct |
| `l1starGen_of_blocked` [L1S], `lInfty_of_l1Blocked` [TF] | Lean | exist, with these statements |

## 4. Lean

- **Build.** `lake build --no-build`: "All targets up-to-date (18396 jobs)". `GallaiLean.lean` l.72 imports `L1Induction`. `lake env lean A25AxiomCheck.lean` runs in 7 s.
- **No sorry.** grep for `sorry|admit|^axiom|native_decide|implemented_by|unsafe|@[extern` finds nothing.
- **Axioms.** Each of the following depends only on `[propext, Classical.choice, Quot.sound]` (`out/A25AxiomCheck.out`): `avoid_of_target_child`, `avoid_of_target_adj_child`, `l1Blocked_of_someTarget`, `l1Blocked_of_someTargetLocal`, `l1starGen_of_ST_TR`, `l1star_of_ST_TR`, `ee_of_ST_TR`, `lInfty_of_ST_TR`.
- **Fidelity** (from `#print`):

| Lean | manuscript | verdict |
|---|---|---|
| `TightTransfer` | Conj 4.1 | Exact. card(evenSet) ≤ 1 and g ∈ evenSet mean "g the only even vertex"; c odd, ¬Adj g c; Adj g x, Adj c x; c ∉ A, x ∉ A, ∀ a ∈ A, ¬Adj c a, i.e. A ∩ (N[c] ∪ {x}) = ∅. A may contain g or meet N(g). Graph `delEdge G g x`. Stronger than Theorem 4.6 needs (F8), but faithful. |
| `SomeTarget` | Conj 4.4 | Exact. Admissible A (`Admissible` = A misses {c} ∪ N(c) ∪ N(evenSet)), g ∈ evenSet, ¬Adj g c, blocked; ∃ x ∈ N(g) with `AvoidDecomp (delEdge G g x) c A`. |
| `SomeTargetLocal` | Def 4.5 (ST′) | Exact: (¬Adj c x ∧ good (G − gx, c, A)) ∨ (Adj c x ∧ good (G − xc − gx, x, A ∪ {c})). False (Prop 4.7, not formalised), so `l1Blocked_of_someTargetLocal` is vacuous, as the docstring says. |
| `avoid_of_target_child` | Thm 3.1(b) | Exact: g ∈ evenSet, ¬Adj g c, Adj g x, ¬Adj c x, c odd, x ∉ A. No admissibility and no c ∉ A, correctly (vacuous for c ∈ A). The proof is the leaf at c (`apex G {c}`), `fan_single_supp`, `avoid_of_apexSep`, as described. |
| `avoid_of_target_adj_child` | Thm 3.1(c) | Exact: adds Adj c x, c ∉ A, x ∉ A; child `AvoidDecomp (delEdge (delEdge G x c) g x) x (insert c A)`. Proof: leaf graph `apex (G − xc) {x}`, Fan, `avoid_of_leafSep`. Assumes ¬Adj g c, which is not needed mathematically. |
| `l1Blocked_of_someTarget` etc. | Thm 4.6 and consequences | Exact. `AvoidDecomp` = ∃ Lovász D with every path ending at c avoiding A. |

- **Docstrings.**
  - "each Case I reduction of L1Star.lean" (N6).
  - "TR … Exhaustive to order 9 in the manuscript" and "ST … every admissible A" are correct descriptions.
  - SomeTargetLocal's "an instance of order 7 with d(g) = 2 and N(g) ⊆ N(c)" is correct.

## 5. Computations

**Re-runs of the authors' tools** (`out/rerun_authors.txt`):
- **Byte-identical to the committed files:** `tr2_9`, `stprime9`, `rechoice9`, `l1e9`, `stuck0_9`, `rec_adm9_MBT`, `rec_sub9_MBT`, `explore9_MBT`, `tt_stuck0_9`. `rand_11_13_v2` and `rand_15` are identical after regenerating the graphs with `randg.py`, which is deterministic.
- **Same lines:** `rec2 adm MB` at order 9 gives exactly the NOREC list of `rec_adm9_MB.txt` (written by `rec.cpp`). `targets` and `alltarget` give identical BADT and ATFAIL lines.
- **Order 10:** `rec2` on the 29 and 17 failing graphs gives 54 and 33.
- **Not committed by the authors, re-run here; every manuscript number reproduces:**
  - tr2 at order 7 (3,764), trall (6,672 / 0; 8,066 / 14), stprime at order 7 (406 / 386);
  - exch (34,778 / 24,738 / 375 / 9,665 / 824);
  - xcheck2 (90 + 312 + 3,126 + 28,176 = 31,704, 0 mismatches);
  - rechoice (8, 457), l1e (8, 338);
  - walkadm (24 at order 7; 4,283 at order 9), walk2 (3,969 / 0; 12,980 / 4,283 / 13,259);
  - minobs (2 dead ends at order 5, both DEk; 314 at order 7);
  - gap (orders 4–6 all gap 0; order 7 760/11/5/4 and 764/11/5/0; order 8 1,589/68/112/20/0/3 with and without TR);
  - subsets (9, 23, 405, 2,150 with 406 blocked, 27,837, all in Rec); |A| ≤ 2 (1,868, all in Rec); "(a)–(d) only" (26 of 78).

**Independent re-derivations** (my code, `a25.h`):

| claim | manuscript / E27 | independent (audit) |
|---|---|---|
| TR, order 7, every A ⊆ V ∖ (N[c] ∪ {x}) | 3,764 tests, 0 violations | **3,764, 0**; 2,156 with A admissible for G, 1,608 meeting N(g) (F8) |
| TR, order 9 | 1,735,156, 0 | 1-in-10 sample (1,194 graphs; pruned oracle with a 2·10⁷-node budget, `t_trst9.cpp`): **0 violations** in 175,435 child-good tests (2,430 undecided: 133 children, 2,297 parents). The authors' tr2 on the same graphs: 175,568, of which 62,822 have A admissible for G. Full independent enumeration at order 9 is infeasible: the densest graphs, e.g. K₉ minus four disjoint edges, have too many Lovász decompositions. |
| trall, order 7 | 6,672 / 0 non-tight; 8,066 / 14 tight, all meeting N(c) | **identical** |
| ST / ST′, order 7, every admissible A | 406 blocked; ST 406; ST′ 386 | **identical**; the 20 ST′ failures all have d(g) = 2 and N(g) ⊆ N(c), and 10 have g ∈ A |
| ST / ST′, order 9 | 135,188; 135,188; 133,926 | same sample: **12,666 blocked; ST 12,666; ST′ 12,516**, 0 undecided, identical to the authors' stprime on these graphs |
| order 5 | no blocked instance | **confirmed** (TR 28 tests, trall 20 + 32, 0 violations) |
| coverage (1)/(4), order 7 | 34,778 / 24,738 / 375 / 9,665 / 824 | **identical**; 375/375 exchanges valid |
| Prop 3.3 walk, order 9 | 3,969 | **3,969** (unbounded trails; structure of G* verified) |
| Fan route L1S Prop 5.3, order 9 | 0 | **149** (F2) |
| TR-walks (split / Fan trail / either) | 12,980 / 4,283 / 13,259 | same unrestricted; **6,552 / 2,325 / 7,506** licensed by TR (F3) |
| stuck instances, order 9 | 6; mechanism; 5 edges cx; 84%, 76–92% | **all confirmed**; per-target D′ counts identical to `tt` |
| Ex 4.3, Prop 4.7, DEk, H??FFf} | | **confirmed** (§3.4, `out/t_inst.txt`, `out/t_hff.txt`); DEk's dead end is DEk − 04, g = 4 (F15) |
| ST′ failure shapes, order 9 (from the committed list) | 1,262 = 1,238 + 24; 1,208; 760 | **confirmed**; 619 of the 1,238 have g ∈ A (F10) |
| bad targets | 496 = 476 (d(c) = 1) + 20 | **confirmed**; none is a two-even instance at distance ≥ 3 (F11) |
| explore9_MBT | 1,296 stuck, none admissible, 1,184 without moves | **confirmed**; all 1,184 have N(g) ⊆ A |
| Rec soundness | — | every certified (G, c, A), c ∉ A, any A, orders 4–7: 22,133, all good (Rec and Rec_T) |
| cert.py's 35 due to admissible intermediates | claimed | **confirmed**: Rec with admissible-only intermediates misses exactly 35 of 1,868 |
| Rec, own implementation (`t_rec.cpp`) | 209 (163) / 56 (35) at order 9 | coded moves: **identical lists**; every route: **208 / 55** (and 55 for subsets); moves as stated in Thm 3.1: **301 (162) / 203 (103)**; order 10 unchanged with every route (F5) |
| Rec, orders 6–8, own implementation | all admissible instances certified; 26/78 with (a)–(d) | **confirmed** (stated and coded moves; every admissible A); K_{3,3} certified without (e) (F19) |

- **Random tests.** These are by the authors' code only (not my oracle): budgets of 2·10⁶, and only A = Amax, so TR is tested only in the admissible regime (F8). The re-run is identical.
- The earlier L1E "failures" (`rand_11_13.txt`) are explained correctly. `l1e_check13.txt` at `cca465c` shows L1E for every target of the first instance and for u = 1, 5 of the second. One target suffices.

## 6. Verdict and required corrections

**Verdict.** The mathematics of the manuscript is essentially correct.
- **Correct, and checked by hand and computationally:**
  - Proposition 3.3 (the walk to a degree-two vertex), including its parity bookkeeping for trails that revisit vertices or return to g, and the lift;
  - Lemma 4.2 (the exchange at c), including the chain description, the re-routing of P, the path property of S and the end counts;
  - Theorem 4.6, Proposition 4.7, Example 4.3, Proposition 5.2 and Corollary 3.4.
- **Theorem 3.1** is correct for every move and every claimed relaxation once c ∉ A is assumed. As stated ("no admissibility", with instances allowing c ∈ A) it is false for (d) and (h), and Rec's first base case is wrong. The repair is one hypothesis and has no computational consequence.
- **The Lean file is faithful.** It builds, has no `sorry`, uses only standard axioms, and states exactly (b), (c), TR, ST and ST′. TR as used in Theorem 4.6 is only needed in the regime where its conclusion is L1* itself.
- **The data reproduce.** Every committed output re-runs byte for byte. Every central count is re-derived independently with a different algorithm, and an own implementation of Rec gives the authors' order-9 failure lists exactly.
- **What is wrong is confined to census and interpretation claims:**
  - the Fan route "applies to none" (it applies to 149);
  - the TR-walk coverage (49%, not 87%, under what TR licenses);
  - the Rec counts, which depend on unstated generalisations of (b), (c) (301 against 209 with the moves as written) and on a restricted route move;
  - one wrong citation;
  - several overstated conclusions (F8–F16) and two false data sentences (F17, F19).

None of this affects the formal reduction TR ∧ ST ⇒ L1Blocked or the refutation of ST′.

**Required corrections:**
1. **F1:** add c ∉ A to the definition of an instance (or to (d), (h), (i) and the first base case of Rec), and correct l.193–194.
2. **F2:** L1S Prop 5.3 applies to 149 blocked Amax instances at order 9, not 0. Drop "extends the Fan route", and correct the abstract, E27(E) and §AC.2.
3. **F3:** the "valid under TR" walk counts must exclude consecutive tight trail vertices and inadmissible tight-end splits (6,552 / 2,325 / 7,506 = 49%; walkadm 12 at order 7). Alternatively, state the extra transfer they use. Correct §6, E27 and §AC.
4. **F4:** [L1S, §8].
5. **F5, F6, F7:**
   - State (b), (c) without c ∉ N(g), as the code uses them; with the stated moves Rec misses 301, not 209, and Rec_T 203, not 56, at order 9.
   - Say that (h) is restricted to at most 8 shortest routes, or re-run (208 / 55 / 55 at order 9).
   - Add c ∉ N(g) to move (t).
   - Give a per-move proof of Theorem 3.1 and announce every dropped hypothesis.
   - F7: add a direct cross-check of `lind.h`'s `orc::avoid`, or cite this audit.
6. **F8:** say that Theorem 4.6 uses TR only for A admissible for G, report the admissible/inadmissible split of the TR tests, and say that the random TR tests are all admissible.
7. **F9–F16:** tone down "a local repair is not enough", "minimal shape" (619/1,238), the two-even core (needs y ∉ N(g); the 96% inference is unsupported), "no class within k steps", "L1E does not supply ST", "exactly the condition", the DEk naming and "every reduction of L1S".
8. **F17, F18, F19:** correct E27(D), commit the missing outputs and summaries, and replace "needs the split (e)" by "(g)".

## Authors' response (added by the authoring session after the audit; not part of the audit)

Every finding was accepted. The corrections are in the manuscript (now dated "audit A25 applied"), E27, §AC, the README, `L1Induction.lean` and the scripts.

| finding | resolution |
|---|---|
| F1 | The definition of an instance now requires c ∉ A. Thm 3.1 starts "Let (G, c, A) be an instance (so c ∉ A)". The proof's incomplete list is replaced by a per-move proof. |
| F2 | The census now reads: "Prop 5.3 applies to 149, all with d(c) = 1; 45 of these have no such trail". "Extends" is replaced by "complements". `walk2.cpp` mode 3 implements Prop 5.3 as stated and reproduces 149 (order 9) and 4 (order 7). Abstract, E27(E) and §AC.2 are corrected. |
| F3 | `walk2.cpp` mode 1 and `walkadm.cpp` now allow only what TR licenses: no tight step out of a tight vertex, and a split at a tight end only if its other neighbour is outside A. They reproduce 6,552 / 2,325 / 7,506 (49%) and 12 / 83. The old counts are kept as mode 2 and labelled as not licensed. |
| F4 | Changed to [L1S, §8]. |
| F5 | Thm 3.1(b), (c) are stated without c ∉ N(g), and the proof says why. The computations section states the implementation's (h) restriction. It adds the every-route reruns, which reproduce 208 (162) and 55 (34) (`out/rec_adm9_MBR.txt`, `out/rec_adm9_MBTR.txt`), and the 301 / 203 counts with (b), (c) restricted to c ∉ N(g) (cited to A25). |
| F6 | (t) now requires g even and c ∉ N(g). Thm 3.1 has a per-move proof that names every dropped hypothesis: c ∉ N(g) in (b), (f), (g), (h); chordlessness in (h); y₁ ∉ N(g) in (g). |
| F7 | The validation paragraph cites this audit's independent oracle. |
| F8 | New Corollary 4.7. (1) TR_adm ∧ ST ⇒ L1Blocked ⇒ TR_adm, so given ST, L1Blocked ⟺ TR_adm. (2) ST_out plus the all-tight case ⇒ L1Blocked. Both are in Lean: `l1Blocked_iff_tightTransferAdm`, `l1Blocked_of_out_tight`, `l1BlockedTight_of_ST_TR`. The TR split (2,156 / 1,608 at order 7; 637,572 / 1,097,584 at order 9) is reported. The random and order-11 TR tests are labelled as TR_adm, i.e. L1* itself. |
| F9 | Reworded: "(2) and (3) are special cases of (1)"; "a proof must either re-choose D′ or repair the Fan image by an argument other than these". The scope of the counts is stated. |
| F10 | "1,238 have d(g) = 2 with N(g) independent; in 619 of them g ∈ A (the minimal shape)". A new paragraph after Prop 4.8 says that FEhv? with A = {3,5} has g ∉ A and is settled by (e). |
| F11 | The two-even paragraph adds y ∉ N(g), cites [L1S, Prop 3.3] for the containment, and reports the classification 442 / 29 / 5 / 0. |
| F12 | Weakened to the certificate statement, with an explicit caveat. |
| F13 | Remark 4.9: L1E for all blocked admissible instances would imply ST and L1Blocked, but L1E cannot serve as the hypothesis for the inadmissible child. |
| F14 | "It is the hypothesis of TR." |
| F15 | The dead end is the child (DEk − 04, 1, {0,2}) with g = 4. Its only target outside A is tight; its (c)-child and (h)-child are bad. Table 1 is corrected. |
| F16 | Abstract: "Every reduction of [L1S] that we use … only c ∉ A". The proof of Thm 3.1 adds that Prop 5.3 is a composite of (b)-steps (and the leaf-graph step when d(c) = 1). Def 3.2 notes that the packed base cases are not used. |
| F17 | E27(D) corrected. |
| F18 | `regen.sh` regenerates every short run. All quoted outputs are now committed: `out/xcheck2_4_7.txt`, `rec_ad_only_6_8.txt`, `rec_subsets_4_8.txt`, `rec_small7.txt`, `tr2_7.txt`, `trall_5_7.txt`, `rechoice_5_7.txt`, `exch7.txt`, `stprime7.txt`, `l1e_5_9.txt`, `targets9_summary.txt`, `alltarget9.txt`, `gap_6_8*.txt`, `minobs_5_7.txt`, `walk2_7_9.txt`, `walkadm_7_9.txt`, `example_*.txt`, `qedge_stuck9.txt`. |
| F19 | "K_{3,3} needs the split (g) at c". |
| N1–N9 | All applied. N1: forced chain "on the path of 𝒟". N2: Lemma 4.2 "for every A with c, x ∉ A". N3: parity remark. N4: "five pairwise non-isomorphic graphs" with the automorphism. N5: c ∉ A needed only for (c). N6: Lean docstring. N7: (f) without c ∉ N(g). N8: the abstract mentions undecided cases. N9: "blocked" requires an even vertex g. |

Theorem numbering after the revision: Cor 4.7 (new), Prop 4.8 (ST′ false; was 4.7), Remark 4.9 (was 4.8). Everything else is unchanged.
