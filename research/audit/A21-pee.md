# A21. Audit: "Prescribed end edges in Lovász decompositions with one even vertex"

- **Date:** 2026-11-27
- **Auditor:** fresh subagent (adversarial referee); no edits to the manuscript, the Lean files or the authors' scripts.
- **Scope:** `manuscripts/prescribed-end/prescribed-end.tex` (and its PDF, which matches the .tex: same statement numbering and numbers); `lean/GallaiLean/PrescribedEnd.lean` (theorems `sep_atMostOneCommon`, `ee_atMostOneCommon`, `ee_deg_two`, `PathDecomp.append_move_exact`, `PathDecomp.liftLeaf`, `endEdge_of_leafSep`, `pee_adjEven`, `ee_of_triangle`); the outputs in `manuscripts/prescribed-end/scripts/out/`; the citations to RD, MS and STL. Background results from RD/MS/STL are taken as established; only how they are cited and used is checked.
- **Out of scope:** `lean/GallaiLean/PrescribedEndOutside.lean` (`ee_of_outside`, `L1Star`, `ee_of_L1Star`), committed at 07:19 during this audit (commit 7e063c7). The audited manuscript (§9, l.526–527) still says that Proposition 7.1 is "proved here only"; if that file is meant to formalise Proposition 7.1 and Corollary 7.4, §9 must be updated and the file audited separately.
- **Audit scripts:** `research/audit/A21-scripts/` (independent code; none of it calls `pee.c` or `brute.py`).
- **Version audited:** the committed manuscript, commit b35be83 (md5 below). During the audit another session began an *uncommitted* revision of the working tree: `.tex` md5 `689786be7026e8dec0db6d8de573dada`, plus changes to `pee.c` and `rand_test.py` and about 15 new files in `scripts/out/`. That revision was not audited. Its diff appears to address F1–F5 and N1–N3, N6, N7. I checked only two of its new data claims, both consistent: the order-11 EE total and the reachability of the random failures in `rand_A2.txt` (see §5).

md5 of the files audited:

| file | md5 |
|---|---|
| `manuscripts/prescribed-end/prescribed-end.tex` | `e8833ae9b72e660ddf9c18c5340b8803` |
| `manuscripts/prescribed-end/prescribed-end.pdf` | `ce2a1be1217fa907133789b77ae131b9` |
| `lean/GallaiLean/PrescribedEnd.lean` | `be391440b3b36c5f29a43ef738ec01c3` |
| `scripts/out/exh5.txt` | `8e5c83e03c62be12bdab2b0d863debf6` |
| `scripts/out/exh7.txt` | `4a5a1e0a12cbc7eb39abbee00d6ca59e` |
| `scripts/out/exh9.txt` | `02d094135344de0046eb94f3f95980b1` |
| `scripts/out/l1s2_9.txt` | `3ba05515f9ef63ec34c8a0231f4362c7` |
| `scripts/out/rand_A.txt` | `fb9196b274788d1691abea661a3e2509` |
| `scripts/out/exh11_away_partial_fails.txt.gz` | `d8d3a484052e10c6f85ce257b0274bb0` |
| `scripts/out/ee11_{0,1,2}.txt` | written during the audit; final versions `4a135e54…`, `32bc6990…`, `90c012e1…` (all three SUMMARY lines present at the end of the audit) |

## 1. Verdict table

| # | Item (lines) | Verdict | One-line reason |
|---|---|---|---|
| 1 | Thm 1.3, prescribed end edge [MS] (l.79–81) | SOUND WITH FIXES | Correct citation of MS Thm 14, but stated for "all degrees odd"; Prop 6.4 applies it to a graph with an isolated vertex (F4). |
| 2 | Lemma 2.1, Fan with vertex sets (l.131–136) | SOUND | Weaker than RD Lemma 2.2, which it follows; Z uses N_K(g) as in RD. |
| 3 | Thm 2.2, separation (l.138–141) | SOUND | Matches RD Thm 6.1 (no restriction on which vertex is even; dist ≥ 3 includes ∞). |
| 4 | Prop 2.3 (l.143–147) | SOUND | = MS Prop 16 without classes. |
| 5 | Lemma 2.4, leaf merge (l.152–157) | SOUND | = MS Lemma 12. |
| 6 | Lemma 2.5, leaf witness (l.159–171) | SOUND | Both directions checked; R may be empty, fine. |
| 7 | Prop 3.1, counterexample (l.179–190) | SOUND | Proof correct; example verified by full enumeration (4 Lovász decompositions, none with xy terminal at x). |
| 8 | Lemma 4.1, protected end (l.200–217) | SOUND | Leaf passage legitimate; Z_H(g) ⊆ Z_D(g) and b_H(t)=b_D(t) checked; t,g ∉ {x,ℓ}. |
| 9 | Remark 4.2 (l.219–227) | SOUND (sketch) | Consistent with RD's chain proof; unformalised, not used. |
| 10 | Thm 5.1 (l.232–256) | SOUND | All degree/parity claims and both Fan hypotheses checked. |
| 11 | Cor 5.2 (l.258–267) | SOUND | STL Prop "d(z)=2 is EE": STL(J,z,r) ⟺ EE at the other neighbour u. |
| 12 | Remark 5.3 (l.269–277) | SOUND | Contains MS Prop 18(a)(b)(c) and STL Thm "d(z)=2" (both cases). |
| 13 | Thm 6.1 (l.281–303) | SOUND | Each K_i has exactly one positive even vertex e_i; Lemma 4.1 hypotheses hold at every step. |
| 14 | "reachable" (l.305–306) | SOUND | Equivalent to the path condition of Thm 6.1 (both implemented, same counts). |
| 15 | Cor 6.2 (l.308–319) | SOUND | Common-neighbour bookkeeping in K_1 and K_k correct. |
| 16 | Cor 6.3 (l.321–324) | SOUND | Immediate from Thm 6.1; no proof written (N8). |
| 17 | Prop 6.4, pendant neighbour (l.331–342) | SOUND WITH FIXES | Correct, but uses Thm 1.3 on K−zv, which has the isolated vertex v (F4). |
| 18 | Question 6.5 (l.344–347) | UNCLEAR (data claim) | "Both hold in all our data" not checked by the authors for the 56,739 order-11 failures (F3); my sample supports it. |
| 19 | Prop 7.1 (l.355–369) | SOUND | Z(w)=∅ (z ∉ N(w)); leaf path nonempty after deleting ℓ. |
| 20 | Thm 7.2, triangle reduction (l.371–389) | SOUND | Leaf at w stands for z; b_D(z)=0+1; the unique path ending at z is the image of the leaf path. |
| 21 | Conj 7.3 L1* (l.397–401) | statement; nit | N(g) undefined when there is no even vertex (N4). |
| 22 | Cor 7.4 (l.409–420) | SOUND | Both cases satisfy the hypotheses of Conj 7.3. |
| 23 | Remark 7.5 (l.422–429) | SOUND | Order-7 numbers 99/135, 65/65, 267/622 reproduced independently. |
| 24 | §8 computations (l.433–507) | SOUND WITH FIXES | All numbers I recomputed agree (orders 5, 7 and 9, order-8 all-odd, order-11 list); status of the n=11 run, random-failure reachability and missing output files need fixing (F1, F2, N7). |
| 25 | §9 / Lean (l.511–529) | SOUND WITH FIXES | Builds, no sorry, standard axioms, statements faithful; the list of unformalised results is incomplete (F5). |
| 26 | Abstract / introduction | SOUND WITH FIXES | "Every one of the failures found" overclaims (F1); d(x), d(z) ranges hold only to order 9 (F3); minor wording (N1, N2). The novelty and STL claims check out. |

No ERROR or GAP was found in any proof.

## 2. Details by item

**Thm 1.3 (l.79–81).** MS Thm 14 is stated for "no vertex of positive even degree", which allows isolated vertices. PE restates it as "all degrees odd". The only use with an isolated vertex is Prop 6.4 (l.337–338: "K−zv has all degrees odd or zero"). Fix: state Thm 1.3 as in MS, or delete v first.

**Lemma 2.1 (l.131–136).** RD Lemma 2.2 gives a bijection φ with V(φ(Q))=V(Q) except for one path, which gains u. PE's "every path lies in V(Q)∪{g} for some Q" follows from that. RD defines Z_D(u) with N_K(u) (before adding tu), and PE does the same at l.129. Every application below uses only the weaker form.

**Prop 2.3 (l.143–147).** Direction ⇐: z is odd in K−uz, u ∉ Q_z, so appending zu gives a path; z becomes interior. Direction ⇒: z is interior to Q_u, since b(z)=0, so R is nonempty. Both correct.

**Lemma 2.5 (l.159–171).** Q_x=Ryx with x only at the end. Ryℓ avoids x, and no other path contains ℓ. The end counts are as stated (d_H(x)=d(x)−1 and d_H(y)=d(y)). The converse is Lemma 2.4: the path through yℓ ends at the leaf ℓ, and b_D(x)=1 makes it Q_x. The sentence at l.173–175 ("preserves it whenever the target is neither x nor ℓ") also needs t ≠ ℓ (N6). It is informal and every use satisfies it.

**Prop 3.1 (l.179–190).** Tried hard to break it; no gap. b(x)=1 and d(x)=3 force the edges xz and xt to be consecutive on one path P ≠ Q_x. Since d(z)=2 and b(z)=0, zx and zt are consecutive on the path through zx, which is P. So P ⊇ t x z t, a contradiction. In the example the degrees are x,t,y = 3, z = 2, p = 1, so z is the only even vertex. Independent full enumeration (`naive.py`): the example has exactly 4 Lovász decompositions; in all of them the end edge at x is xt or xz; xy is terminal at y in two of them. "Smallest counterexample has five vertices" (l.107–108) is correct. A connected graph with exactly one even vertex has odd order, and order 3 has no away edges. The order-5 count (5 failures) is reproduced.

**Lemma 4.1 (l.200–217).** Checked line by line.
- (i) Passage to H: Q_x is the unique path with an end at x. R y ℓ uses only edges of K−xy. The other paths avoid xy and ℓ, so D_H decomposes H, with b(x)=0, b(ℓ)=1 and no path containing both x and ℓ.
- (ii) Fan's inequality transfers. N_H(g) equals N_K(g) when g ≠ y (and x ∉ N_K(g) by hypothesis). It equals N_K(y)∖{x}∪{ℓ} when g = y. In both cases x ∉ N_H(g), and ℓ has an end, so Z_{D_H}(g) ⊆ Z_D(g). Also b_H(t)=b_D(t), since t ≠ x and t ≠ ℓ.
- (iii) Non-adjacency: t,g ∈ V(K), and H−ℓ ⊆ K.
- (iv) H+tg = H(K+tg;x,y), since tg ≠ xy because x ∉ {t,g}.
- (v) After Fan's lemma, g ∉ {x,ℓ}, so separation survives; t,g ∉ {x,ℓ}, so b(x)=0 and b(ℓ)=1 survive. ℓ is still a leaf, so the path through yℓ ends at ℓ.
- (vi) Merge: b(x)=1, and that path is Q_x through xy.

Sound. The hypothesis x ≠ t is essential (if x=t its end moves). It is in the lemma but missing from the abstract and the introduction (N1).

**Remark 4.2 (l.219–227).** Checked against RD's proof of Lemma 2.2. The chain vertices after t are values π(x_i,Q_i) ∈ N(g). If xg is the end edge of Q_x, then x precedes g only when Q_x is read from x, and π(x,Q_x)=x is not a new chain vertex. Re-routing preserves the path read from its other end up to u. The append is at x_k ≠ x. Correct as a sketch.

**Thm 5.1 (l.232–256).**
- |T|=0: in K−uz, u is the only possible even vertex (degree d(u)−1, possibly 0), and dist(u,z) ≥ 3. RD Thm 6.1 places no condition on which vertex is even.
- |T|=1, K_0=K−uz−uw: d(u) ≥ 2 and odd, so d(u)−2 ≥ 1 is odd; d(w) ≥ 3 and odd, so d(w)−1 ≥ 2 is even; d(z)−1 is odd. So w is the only positive even vertex. dist_{K_0}(u,z) ≥ 3.
- Fan with t=u, g=w: uw ∉ E(K_0); every neighbour of w in K_0 is odd and so has an end, giving Z=∅ < 1 = b(u). The result has the Lovász counts of K−uz, and paths lie in old paths plus w ∉ {u,z}.

Sound.

**Cor 5.2 / Remark 5.3 / STL claim (l.258–277, l.110–111).**
- STL (stl.tex, Prop "d(z)=2 is EE"): with N(z)={u,r}, STL(J,z,r) holds iff uz is terminal at u. The single transition u z r is star-terminal with r long, or SS, exactly when u is short. So "STL at d(z)=2 is EE at the other neighbour" is correct.
- With N(z)={u,w}, the only possible common neighbour of u and z is w, so Thm 5.1 applies for every configuration. STL Conj requires J−z connected and d(r) ≥ 3, so Cor 5.2 proves more than STL conjectures.
- STL Thm "d(z)=2" covers uw ∉ E, and uw ∈ E with no further common neighbour of u and w. Both have |N(u)∩N(z)| ≤ 1. The configuration with two triangles zuw, tuw is the one STL left open (stl.tex l.425–427; STL now cites PE for it).
- MS Prop 18 covers (a) no triangle (|T|=0), (b) zb ∉ E (T ⊆ {a}), and (c) u the only common neighbour of a and b (z is not adjacent to both). All three have |T| ≤ 1. MS's two open d(u)=3 configurations are "z ~ a,b" (|T|=2) and "ab ∈ E, z adjacent to one of a,b, second common neighbour". The second has |T|=1 and is newly covered.
- So "contains all earlier partial results" and "completes STL at d(z)=2" are correct. I also checked MS Lemma 19 (certified Case I): without classes it is the separation case, which is contained.

**Thm 6.1 (l.281–303).**
- Path conditions: x ∉ {e_0,…,e_k}, since x ≠ z, x ≠ y, and e_i ∉ N[x]. So xy is not a path edge and x ∈ N_{K_k}(y).
- Degrees in K_i: z loses 1 (odd); e_j with 0<j<i loses 2 (it had degree ≥ 3, so it stays odd and positive); e_i loses 1. For 0<i<k, e_i has two path neighbours; for i=k, y has neighbours e_{k−1} ≠ x and x. So d ≥ 3 and the new degree is even and ≥ 2.
- Hence each K_i (i ≥ 1) has exactly one positive even vertex, e_i. Checked.
- Step i: t=e_{i−1}, g=e_i are non-adjacent in K_i, and b(t)=1. Z(e_i)=∅, since its neighbours are odd in a Lovász decomposition. For i<k, x ∉ N(g); for i=k, y=g. x ∉ {t,g}.
- The new counts are Lovász for K_{i−1}: e_{i−1} gets 0 (it is the even vertex, or z for i=1), and e_i gets 1 (its degree in K_{i−1} is d(e_i), odd).

Sound.

**Reachability (l.305–306).** Equivalent to the path condition. A shortest z–v path inside the component, with y ∉ C because y ∈ N(x)∖{z}, gives the path; the converse is immediate. My `exhaust.py` implements the path condition directly (an induced subgraph on V∖N[x] ∪ {z,y}). The authors' `block_check.py` implements the component form. The counts agree (n=7: 1,451/459).

**Cor 6.2 (l.308–319).** k=1: N_{K_1}(x)=N(x) and N_{K_1}(y)=N(y)∖{z}, so the common neighbours are those of K other than z. Thm 5.1 then holds in K_1, with y the only even vertex and x ∈ N_{K_1}(y). k ≥ 2: e_{k−1} ∉ N(x), so the common neighbours are unchanged. Sound.

**Prop 6.4 (l.331–342).** x=v is trivial (Lovász's theorem gives a decomposition). Otherwise xy ≠ zv, and K−zv has v isolated and z odd. Theorem 1.3 applies, in MS's form (F4). v ∉ Q_z, so Q_z+zv is a path. If Q_x=Q_z, it is extended at its z end, and z ≠ x. Sound.

**Prop 7.1 (l.355–369).** In K_0, d(u)−2 is odd ≥ 1, d(z)−1 is odd, and d(w)−1 is even (possibly 0). z ∉ N(w), u ∉ N(w) and ℓ ∉ N(w), so Z(w)=∅ < b(u)=1. The leaf path P is not just zℓ, since b(z)=0, so P−ℓ ends at z. The counts are Lovász for K−uz. Sound.

**Thm 7.2 (l.371–389).** Tried hard to break the "leaf stands for z" step.
- H=H(F;z,w)=K−uz−zw+wℓ, so H−uw=K_1+wℓ. Q_w avoids u and z, so Q_wℓ avoids them.
- The neighbours of w in K_1+wℓ are N(w)∖{u,z} (odd, with an end) and ℓ (with an end), so Z(w)=∅ < b(u)=1. Fan's lemma with t=u, g=w applies, and w ∉ {ℓ,u,z} keeps both separations.
- Lemma 2.4 with x=z: b_D(z)=b_{D_H}(z)+b_{D_H}(ℓ)=0+1. Here b_{D_1}(z)=0 since z is even (or isolated) in K_1, and z ∉ {t,g}.
- b_D(u)=0, b_D(w)=1, and the other counts are Lovász for F=K−uz.
- The image of the leaf path ends at z and avoids u. Since b_D(z)=1 it is the unique path ending at z.

Sound. Also checked the degenerate case d(z)=2, where z is isolated in K_1.

**Cor 7.4 (l.409–420).** Case w ∉ N[z]: K_0 has at most the even vertex w; c=z is odd; u ∉ N_{K_0}[z] ∪ N_{K_0}(w). Triangle case: c=w is odd in K_1, u,z ∉ N_{K_1}[w], u ∉ N_{K_1}(z), and g=z ∈ A is allowed. Sound. The remark "for A={g} it is EE" (l.403) is an equivalence (add the edge cg).

**L1 citations (l.403–407).** RD Thm 6.3 is L1 for a ∉ N[c] with no even vertex. RD Remark 6.7 is the path c z a. Both are correct.

## 3. Lean

- `lake env lean GallaiLean/PrescribedEnd.lean`: exit 0, no errors and no warnings from this file. `lake build GallaiLean.PrescribedEnd` completed: 18,315 jobs, with one deprecation warning, which is in `MultiSep.lean`. The full library was not built, so "the full library builds" (l.512–513) was not verified.
- `grep sorry|admit|axiom|native_decide|implemented_by|unsafe`: no hits.
- `#print axioms` (scratch file importing `GallaiLean.PrescribedEnd`) on all eight theorems: each gives `[propext, Classical.choice, Quot.sound]`.
- Fidelity of the statements:
  - `evenSet` is the set of vertices of positive even degree. `hev : card ≤ 1` together with `hz : z ∈ evenSet` says exactly that "z is the only vertex of positive even degree".
  - `PathDecomp` consists of simple paths of positive length, edge-disjoint and covering the edges. `ends` counts src and tgt. "Lovász" is `ends v = degree v % 2`.
  - "Terminal at u" is ∃P, u ∈ {src, tgt} ∧ s(u,z) ∈ P.edges. This is equivalent to Def 1.2, since u is an end of exactly one path and occurs once on it.
  - `sep_atMostOneCommon` / `ee_atMostOneCommon`: `hcom` says any two common neighbours are equal, which is "at most one". This matches Thm 5.1 exactly.
  - `ee_deg_two`: `degree z = 2`, for each neighbour u. This matches the first part of Cor 5.2.
  - `pee_adjEven`: `hcom` excludes z, and `x ≠ z`. This matches the first sentence of Cor 6.2. The proof runs `sep_atMostOneCommon` in G−zy, lifts to the leaf graph and applies Fan with t=z, g=y. That is Thm 5.1 + Prop 2.3 + the proof of Lemma 4.1 merged, which is the same argument.
  - `ee_of_triangle`: the hypothesis "every path with an end at w avoids u and z" is Q_w ∩ {u,z}=∅ (b(w)=1). This matches Thm 7.2 exactly.
  - `endEdge_of_leafSep` is the ⇐ direction of Lemma 2.5 (with Lemma 2.4). It is more general than needed (no even-vertex hypothesis).
  - `liftLeaf` / `append_move_exact` are the "extend a path by a leaf edge" step used in Prop 7.1, Thm 7.2 and Lemma 4.1. They are not literally the ⇒ direction of Lemma 2.5, but that direction is never needed in Lean.
  - No hypothesis is weaker or stronger than in the manuscript.
- **F5 (coverage).** §9 l.526–527 lists as unformalised only "Thm 6.1 for k ≥ 2, Prop 6.4, Prop 7.1, Prop 3.1". The following are also not in `PrescribedEnd.lean`:
  - Lemma 4.1 in its stated generality (only the instance t=z, g=y inside `pee_adjEven`);
  - Thm 6.1 as a conditional statement, even for k=1;
  - the second sentence of Cor 6.2;
  - Cor 6.3 and Cor 7.4.

  The abstract's "The main results are formalised" (l.56) should be qualified, since the protected-end lemma is a headline result of the abstract.

## 4. Independent computations (`research/audit/A21-scripts/`)

Solver `ts.c`, written from scratch:
- It searches transition systems vertex by vertex: at each vertex it pairs the incident edges, leaving d(v) mod 2 unpaired.
- It keeps chains in a union-find with vertex masks. A pairing at v is rejected unless the two chains differ and meet only in v, so every chain is always a path and every complete assignment is a Lovász decomposition.
- Query types: T (xy terminal at x), A (Q_c avoids a set), S (separation of given pairs).
- It shares no code or algorithm with `pee.c`, which builds Q_x first and then searches paths with memoised failures.

Validation:
- `naive.py` enumerates the full product of per-vertex pairings with no pruning and traces the trails afterwards.
- `crosscheck.py` compares `ts` with `naive.py` on all 136 connected graphs of order 3–7 with at most one even vertex and naive space ≤ 4·10⁵, over all T, S, A(|A|=1,2) and L queries: **20,869 queries, 0 mismatches**.
- Order 9 (`exhaust.py`, `exact_part.py`, `tail9.py`):
  - Exact `ts`, without a budget, ran on the first 6,499 and 4,499 graphs of the geng slices 0/2 and 1/2 (10,998 graphs).
  - The remaining 938 dense graphs used `ts` with a node budget and shuffled restarts. Its answers 0 and 1 are exact; the single answer 2 is settled above by counting.
  - The L1, |A|=2 and Remark 7.5 invariants were checked independently at n=7 only. The order-9 values (161,652/0, 170,782/6,423, 203,658/0, 88,356/0) are confirmed only against the authors' files.
- `ts2.c` (frontier memo) and `ts3.c` (forward checking) are speed experiments. Both agree with `ts`/`naive` (`cmp_ts.py`: 8,952 order-9 queries, 0 mismatches), but neither was faster, so all reported counts use `ts`.

| claim | manuscript / E23 | independent result |
|---|---|---|
| (i) Prop 3.1 example | no decomposition with xy terminal at x | 4 Lovász decompositions; none has xy terminal at x; yx terminal at y in two of them |
| n=5: graphs, EE tests/fail, away tests/fail | 7, 14/0, 37/5 | 7, 14/0, 37/5 |
| n=5 failures unreachable | not stated (l.477 lists only 7, 9) | 5/5 unreachable |
| n=7: graphs, EE tests/fail, away tests/fail | 130, 401/0, 1,910/54 | 130, 401/0, 1,910/54 (31 graphs) |
| n=7 reachable / unreachable away edges | 1,451 / 459 (E23) | 1,451 / 459; failures: 0 reachable, 54 unreachable |
| n=5, 7 failure structure | y ∉ N(z), dist ≤ 2, terminal at y | all hold; d(x) ∈ {3,5}, d(z) ∈ {2,4} |
| (iv) Rem 7.5: sep(u,z) in K−uz, n=7 | 99/135 (|T|=2), 65/65 (|T|≥3) | 99/135, 65/65; |T|≤1: 0/242 fail |
| (iv) Rem 7.5: sep(w; u,z) in K_1, n=7 | 267/622 | 267/622 |
| Thm 7.2 hypothesis, n=7 | 622/0 (E23) | 622/0 |
| L1 with even vertex, n=7 | g≁a 792/0, g~a 1,102/158 (E23) | 792/0, 1,102/158 |
| |A|=2 avoidance, n=7 | 738/0 (E23) | 738/0 |
| all-odd order 8 (l.450–451) | 224 graphs, 6,359 queries, 0 fail | 224, 6,359, 0 fail |
| (ii)+(iii) n=9: graphs, EE tests/fail, away tests/fail | 11,936, 47,688/0, 330,449/1,410 (abstract l.37–39, table l.465) | 11,936, 47,688/0, 330,449/1,410. 1,409 failures were decided by search. The one query `ts` left undecided (`HTm||~}`, z=7, x=8, y=1) is a failure by counting: y is a leaf, so the path 81 is forced; G−81 is K₈−e (27 edges) plus an isolated vertex, and the other 3 paths cover at most 21 edges. **The failure set equals the FAIL list of `exh9.txt`.** |
| n=9 reachable / unreachable away edges | 270,875 / 59,574 (l.329, l.479–480) | 270,875 / 59,574; all 1,410 failures unreachable; no reachable edge fails |
| n=9 failure structure | y ∉ N(z), dist ≤ 2, terminal at y; d(x) ∈ {3,5,7}, d(z) ∈ {2,4,6}; 1,049 graphs | all confirmed: terminal at y 1,410/1,410 (584 with d(y)=1); dist 982×1, 428×2; d(x)=3/5/7: 843/410/157; d(z)=2/4/6: 855/414/141; 1,049 graphs |
| order-11 partial list (56,739 lines) | all unreachable | all 56,739 well-formed, unreachable, y ∉ N(z); dist(x,z): 40,979×1, 15,760×2; **d(x) ∈ {3,5,7,9}, d(z) ∈ {2,4,6,8}** (1,763 with d(x)=9; 964 with d(z)=8) |
| order-11 partial list: random sample of 150 lines (`check11.py`, 30 s per query) | failures | xy terminal at x: 130 confirmed failures, 20 undecided, 0 contradicted; xy terminal at y: 149 yes, 1 undecided, 0 no |

Reproduction (from `research/audit/A21-scripts/`; logs of the order-9 and order-11 runs are in `out/`):
```
gcc -O2 -o ts ts.c                       # ts2.c / ts3.c likewise (speed experiments only)
python3 naive.py                         # (i) Proposition 3.1 by full enumeration
python3 crosscheck.py 400000 ts          # ts vs naive, n = 3..7
python3 exhaust.py 5 ./ts --extra        # n = 5 (also sepee, tri, l1p, l1s2)
python3 exhaust.py 7 ./ts --extra        # n = 7: (ii), (iii), (iv)
python3 exhaust.py 9 ./ts --slice 0/2    # n = 9, exact (stopped at graph 6,500; see exact_part.py)
python3 exhaust.py 9 ./ts --slice 1/2    # n = 9, exact (stopped at graph 4,500)
python3 tail9.py 0/2 6500 W 3 300000 100 2000000000   # W = 0,1,2: dense tail of slice 0
python3 tail9.py 1/2 4500 0 1 300000 100 2000000000   # dense tail of slice 1
python3 feat9.py ../../../manuscripts/prescribed-end/scripts/out/exh9.txt
python3 revcheck.py ../../../manuscripts/prescribed-end/scripts/out/exh9.txt
python3 allodd8.py
python3 check11.py ../../../manuscripts/prescribed-end/scripts/out/exh11_away_partial_fails.txt.gz 150 2021 30
```

Numbers in the manuscript compared with `scripts/out/`:
- `exh5/7/9.txt` SUMMARY lines match the table at l.463–465. They also match the abstract (1,410; 330,449; 11,936).
- `l1s2_9.txt` matches l.484–486 (203,658/0; 88,356/0).
- `rand_A.txt` FINAL matches every row of the table at l.498–504. No P1/P2/P3/EE/L1S/TRI failure lines are present, consistent with the "0" row at l.501.
- `exh11_away_partial_fails.txt.gz` has 56,739 lines, matching l.328 and l.474.
- `ee11_*.txt`: at audit time slices 1 and 2 had finished (SUMMARY: 3,664,237 and 3,963,178 graphs; 18,237,059 and 19,947,865 EE tests; 0 failures). Slice 0 was still running (last PARTIAL in the file: 3.2M graphs, 15,253,455 tests, 0 failures). In total that is more than 53.4 million (z,u) tests with no failure, consistent with "more than 30 million" (l.41, l.472).
- No output file existed in the audited version for: l1p order 9 (161,652/0; 170,782/6,423 at l.406, l.482–483), sepee order 7, tri_sep order 7, sharp.py order 9 (270,875/59,574 at l.329, l.479–480), feat.py, the brute.py validation (2,279), the route_ext cross-check (47,688/47,738), or the order-8 all-odd run. They are recorded only in E23 (N7). Files with matching names (`l1p_9.txt`, `sepee_5_7.txt`, `tri_sep_5_7.txt`, `sharp_7_9.txt`, `feat_9.txt`, `brute_4_7.txt`, `xcheck_route_ext_9.txt`, `allodd_4_8.txt`, …) appeared in the working tree during the audit; they were not audited.

## 5. Required fixes

- **F1 (overclaim; abstract l.50–51, l.121–123, l.326–328, l.477–478).** "Every one of the failures found by computation lies outside the reach of this reduction" is not supported for the 99 random failures.
  - `rand_test.py` checks P1/P2/P3 but not reachability.
  - It does not even print a line for an ordinary away failure, so those instances cannot be rechecked.

  Either restrict the claim to the exhaustive runs (n ≤ 9) and the partial n=11 list, or record and test the random failures. Also add n=5 at l.477 (it holds: 5/5).

  *Post-audit-start data:* the new `scripts/out/rand_A2.txt` (same seed, same FINAL counts) records the 99 random failures. My own reachability code finds all 99 unreachable, so the claim is now supported once the revised text cites that file.
- **F2 (status of the n=11 EE run; l.471–474).** "At order 11 the EE run covers every connected graph with one even vertex" is in the present tense while the run was unfinished. During the audit slice 0 was still running and slices 1–2 had just completed. Give the final count in the paper itself rather than in `research/experiments.md`, or say plainly that the run is partial and give its coverage. Give the partial order-11 away run a denominator: graphs and tests (l.473–474).

  *Post-audit-start data:* all three slices have now finished (SUMMARY lines): 11,959,367 graphs, 59,688,458 (z,u) tests, 0 failures. The revised text uses 59,688,458, which matches.
- **F3 (data claims beyond what was checked; l.192–196, l.346).**
  - "Many more failures … with d(x)∈{3,5,7} and d(z)∈{2,4,6}" is false for the failures the paper itself reports at order 11. There, d(x)=9 occurs 1,763 times and d(z)=8 occurs 964 times. Restrict the statement to n ≤ 9, as E23 does.
  - "In every failure found … xy is terminal at y" and "Both hold in all our data" (Q 6.5) were not checked by the authors for the 56,739 order-11 failures. E23 (B) covers n ≤ 9 only, and the partial run checked unreachability only. Restrict the wording, or run the reverse query.
  - My random sample of 150 order-11 failures supports both claims, but does not replace a full check. In the sample, 130 are confirmed failures, 20 are undecided within 30 s, and none is contradicted. The reverse prescription holds in 149, with 1 undecided and none failing.
- **F4 (citation hypothesis; l.79–81 vs l.337–338).** State Thm 1.3 as MS Thm 14 ("no vertex of positive even degree"), or remove the isolated vertex v in Prop 6.4 before applying it.
- **F5 (Lean coverage; l.56, l.124, l.526–529).** Complete the list of results not formalised (Lemma 4.1 in general, Thm 6.1 including k=1 as a conditional statement, Cor 6.2 second sentence, Cor 6.3, Cor 7.4), and qualify "the main results are formalised". If `PrescribedEndOutside.lean` (added during this audit) is meant to cover Prop 7.1 and Cor 7.4, update §9 and have it audited.

## 6. Nits

- **N1** (l.45–47, l.112–113, l.540–541). The protected-end statement omits x ≠ t: the end at t itself does move. "Fan's transfer lemma never moves the end" describes the procedure (only sketched in Remark 4.2), whereas Lemma 4.1 is existential and is proved through the leaf graph. Say "some Fan transfer keeps …" or cite Remark 4.2.
- **N2** (l.122). "exactly confined" should be "confined": failures are a proper subset of the unreachable edges (1,410 of 59,574 at order 9).
- **N3.** Cite MS and STL by their printed numbers: MS Lemma 12, Thm 14, Prop 16 ("Proposition EE"), Conj 17, Prop 18 ("EE3"); STL's Prop "d(z)=2 is EE" and Thm "d(z)=2" have no number in PE. The label names "Proposition EE" and "EE3" do not appear in the MS PDF.
- **N4** (l.397–401). Conj 7.3: say that N(g)=∅ when G has no vertex of positive even degree.
- **N5** (l.352). "delete edges at u": Thm 7.2 also deletes wz.
- **N6** (l.173–175). Fan's lemma preserves a leaf witness when g ∉ {x,ℓ} and t ≠ ℓ. t ≠ x holds automatically, since b(x)=0.
- **N7** (§8). Add output files for every quoted number (list in §4), and record which commit of `pee.c` produced each output. The README says that `pee`, `pee2` and `pee3` were compiled while the source changed. The `pee.c` header (l.12) also lists only one pruning rule, whereas the manuscript (l.441) and the code (l.119, l.137) have two.
- **N8** (l.321–324). Cor 6.3 has no proof line. Add "Theorem 6.1 with EE for K_k (whose even vertex is y)".
- **N9** (l.445–446). The brute.py validation counts graphs "with at most one even vertex" of order ≤ 7 (2,279 queries), while the tables count connected graphs with exactly one. Say which family was used.

## 7. Summary

**Verdict: the mathematics is sound.** I found no ERROR or GAP in any proof. Every lemma, theorem, proposition and corollary is SOUND or SOUND WITH FIXES; the fixes are to statements and citations, not to arguments.

Points that were hardest to break:
- Lemma 4.1: the leaf passage is legitimate, and Fan's inequality transfers because Z_H(g) ⊆ Z_D(g).
- Theorem 6.1: every K_i has exactly one positive even vertex.
- Theorem 7.2: the leaf at w stands for z, and the unique path ending at z is the image of the leaf path.
- Proposition 3.1.

**Citations.** RD Lemma 2.2, Theorem 6.1, Theorem 6.3 and Remark 6.7 are cited and used correctly, and so are MS Lemma 12, Theorem 14, Proposition 16 and Proposition 18. The novelty claims hold:
- Theorem 5.1 contains MS Prop 18(a)–(c) and both d(z)=2 cases of STL.
- STL at d(z)=2 is exactly EE at the other neighbour (STL Prop "d(z)=2 is EE"), so Cor 5.2 completes it.

**Lean.** `PrescribedEnd.lean` elaborates with no errors; the module builds; there is no `sorry`; all eight theorems use only propext, Classical.choice and Quot.sound; the statements match the manuscript (Thm 5.1, Cor 5.2(i), Cor 6.2(i), Thm 7.2, Lemma 2.5 ⇐). The list of unformalised results is incomplete (F5).

**Independent computations.** All checks requested in the brief, plus order 9, agree with the manuscript and its output files:
- (i) the five-vertex example;
- (ii) EE, 0 failures at n ≤ 7, and also at n=9;
- (iii) away failures 5/37 at n=5, 54/1,910 at n=7 and 1,410/330,449 at n=9, all unreachable, with the identical failure set at n=9;
- (iv) Remark 7.5 at n=7: 99/135, 65/65, 267/622;
- the all-odd order-8 validation;
- the 56,739-line order-11 list, all unreachable.

**Required fixes for the audited version** (F1–F5):
- F1: drop the unsupported claim that the random failures are unreachable. Data supporting it appeared during the audit.
- F2: state the true status and final counts of the order-11 EE run (now complete: 59,688,458 tests, 0 failures).
- F3: restrict the d(x), d(z) ranges and the "terminal at y" claim to the data actually checked. Order 11 has d(x)=9 and d(z)=8.
- F4: state Thm 1.3 for "no vertex of positive even degree" (Prop 6.4 uses an isolated vertex).
- F5: complete the Lean coverage statement.

An uncommitted revision in the working tree appears to address most of these. It needs its own audit, together with `PrescribedEndOutside.lean`.

## 8. Author response (claude/ee session, after the audit)

All required fixes and nits were applied in the revision that follows the audited commit b35be83:
- **F1.** `rand_test.py` now prints every away failure with its reachability. A re-run with the same seed (`out/rand_A2.txt`) reproduces every count, and all 99 failures are unreachable. Abstract and §6 now state the scope of the claim.
- **F2.** The order-11 EE run finished: 11,959,367 graphs, 59,688,458 tests, 0 failures. The counts are in the table of §8.
  - A part of the residue class 0 mod 100 (its first 84,002 graphs, all edges) was added, with exact denominators and a reachability split.
  - The stopped all-edge run is described as an initial segment of unrecorded size.
- **F3.** Degree ranges corrected (n = 11: d(x) up to 9, d(z) up to 8). The reverse prescription was checked on all 56,739 order-11 failures (`out/analyze_fail_11partial.txt`): 56,739 hold.
- **F4.** Theorem 1.3 is now stated for "no vertex of positive even degree", citing MS Theorem 14.
- **F5.** §9 lists what is formalised and what is not. The abstract is qualified. `PrescribedEndOutside.lean` (`ee_of_outside`, `L1Star`, `ee_of_L1Star`) is listed, noting that it was not covered by this audit.
- **Nits:**
  - N1: x ≠ t is added, with "can be made to keep".
  - N2: "exactly" is removed.
  - N3: MS and STL are cited by printed numbers.
  - N4: N(g) = ∅ when there is no even vertex.
  - N5: wz is mentioned.
  - N6: t ≠ ℓ is added.
  - N7: every quoted number has an output file; `regen.sh` regenerates them; the `pee.c` header lists the pruning rules.
  - N8: Corollary 6.3 now has a proof line.
  - N9: the brute-force family is stated.
