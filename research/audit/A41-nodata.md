# A41: Audit of nodata (manuscript, `NoData.lean`, scripts, data)

Date: 2026-11-28. Referee stance: adversarial. Grades: **SOUND**; **ERROR** (false as stated);
**GAP** (missing argument, missing provenance, or an overclaim that changes how a result reads;
fixable); **UNCLEAR**; **NIT** (wording). Findings are numbered F1, F2, ... (§2).

**Version.** I started at **9b5035b**. Five commits landed during the audit:
- **7177aea** (author): `CherryLN` now assumes `(evenSet H).card = 0` (the `LN` convention);
  new `lN_of_cherryLN`, `test1At_of_LN_matching`; manuscript mentions them.
- **2c4d726** (author): new `forestLN_far_chain` (replacing the §5 sentence about
  `avoid_packed_of_reach`); `ndsolve.h` fail-first branching and a 2^22 memo; `scripts/rm.c` and
  `data/rootmove_t1_11_all.txt` (order-11 root moves, quoted in the abstract and §4);
  `scripts/xcheck_fl.py`, `data/xcheck_fl_order6.txt` (quoted in §5.1); `VERIFYSAMPLE` filled.
- **c2b57ca** (author): `fl.c` strikes sets with every phase-2 solution; `data/fl_10_s.txt`.
- **c3aa970**, **22fe14d**: another session's snapshots of my scripts. I committed nothing.

All of these are audited. Final text audited: `nodata.tex` md5 `480132c8…` (569 lines; unchanged
since 2c4d726), `NoData.lean` md5 `55095c87…` (975 lines). Cells still marked "(pending)"
(`\FLKPTEN`, `\FLKKTEN`, `\FLCTEN`, `\FLSTEN`, `\FLSTARTEN`) are skipped, as instructed.

**Numbering.** As in the PDF: Definition 1.1, Conjecture 1.2 ($L_N$), Observation 2.1, Lemma 3.1,
Theorems 3.2, 3.3, Lemma 4.1, Theorem 4.2, Corollary 4.3, Conjecture 5.1 (CL), Proposition 5.2,
Examples 5.3 (net), 5.4 (routes), **Lemma 5.5** (star Hall condition; the brief's "Lemma 5.4"),
Example 5.6 (claw). "l." is a line of `nodata.tex` at 22fe14d.

**Auditor files** (`research/audit/A41-scripts/`; outputs in the session scratchpad, not committed):
- `runs.sh`: every command I ran.
- `a41.cpp`: my own exact constrained-Lovász solver (written from the definitions; no code from
  `ndsolve.h`, `nd.c`, `fl.c` or `route_ext.c`), with three modes: `tiers` (the (T1)
  classification: own 3-connectivity, matching, linkage enumeration, forest $T$-joins by the cycle
  space, rootings), `univ` (every structure, as Observation 2.1(b)), `fam` (the abstract families of
  §5.1). Every solution it finds is re-verified from scratch before it is counted.
- `a41rm.cpp`: own root-move closure (exact visited set, no queue cap); it also checks at every
  generated state the parity and $N(z)$ claims of Theorem 4.2.
- `a41nd.cpp`: own order-11 census ($J=B+z$ from all 2-connected $B$ of order 10).
- `a41odd.cpp`: filter for connected graphs with every degree odd.
- `examples_bruteforce.py`: enumerates **all** Lovász decompositions of the graphs of
  Examples 5.3, 5.4, 5.6 and of $K_{1,3}$ by plain recursion, and tests the constraints on each.
- `fat_theta_explicit.py`: the explicit decomposition after Theorem 3.3, $t=4,\dots,40$.
- `univ_h1.py`: (H1) split of the tier-3 structures.
- `axioms.lean`: `#print axioms` for the 15 theorems.

---

## 0. Verdict

1. **The mathematics is correct.** I re-derived every proof in the note: Lemma 3.1, Theorem 3.2,
   Theorem 3.3 and its explicit construction, Lemma 4.1 as used, Theorem 4.2 (zero-end counts,
   parities of $J'$, the change of $N(z)$), Corollary 4.3, Proposition 5.2, Lemma 5.5, the
   spine-induction paragraph after Theorem 3.2, and the new 2-chain case. No step is false. The
   only mathematical omission is the hypothesis $d_J(r)\ge3$ in the (T2) half of Proposition 5.2
   (F5), which holds automatically on the 3-connected instances.
2. **The Lean is faithful and clean.** `lake build` is green (18,440 jobs); `NoData.lean`
   re-elaborates from source with no warning; no `sorry`/`admit`/`native_decide`/`axiom`; all 15
   audited theorems depend only on `propext`, `Classical.choice`, `Quot.sound`. Every statement says
   what the paper claims; where Lean differs it is more general (F14 lists the differences).
3. **Every computed number I could test reproduces with independent code**, most of them exactly
   and root by root:
   - (T1) $n\le9$: graphs, roots, no-data roots, tiers 7,802 / 166 / 135 / 3 / 6, deficiencies,
     twin flags and least sibling excess agree at **all 8,112 roots**;
   - root moves: 6,532 / 8,112 (per root identical), 3,467 single M1, per tier 6,367 / 141 / 24 / 0,
     coverage 642 / 928 / 10; at order 11 my own full census and closure give **exactly**
     8,738,914 graphs, 47,072,398 roots, 12,824,990 no-data roots, the deficiency and twin counts,
     and **10,016,763** roots reached, with the quoted 326,442 / 2,466,905 / 14,115 / 765 split;
   - all 75 order-11 roots of tier 4–5 re-classified from scratch (34 / 41);
   - the abstract families at orders 4–8: every set count and failure count of the table;
   - the three examples, by enumerating every Lovász decomposition.
4. **Findings.** No ERROR in a theorem. The problems are overclaims about verification and
   provenance, and wording:
   - **F1 (GAP).** "every base lifted and checked independently" (abstract) and "every base
     verified" (summary table) are false at order 11, where 97.5% of the tier-1 bases are unchecked;
     "every negative tier claim is confirmed independently" (`\VERIFYSTATUS`) is not what the shipped
     cross-check does (it covers tiers 1–2 only). My runs now supply the missing negatives.
   - **F2 (GAP).** Observation 2.1(a), second sentence, is not produced by the cited script.
   - **F3 (GAP).** Solver-validation counts and the order-10 2-chain row have no committed data.
   - **F4–F16 (NIT).** Wording, a missing hypothesis, scripts.

**Recommendation.** Minor revision. Fix F1–F3 before the numbers are cited elsewhere; the rest are
wording.

---

## 1. Graded items

### 1.1 Lean (check 1)

| Item | Grade | Notes |
|---|---|---|
| `lake build` | SOUND | Green, 18,440 jobs, after each of 7177aea and 2c4d726. `lake env lean GallaiLean/NoData.lean` from source: no output. |
| `sorry` etc. | SOUND | None in `NoData.lean` (also no `admit`, `native_decide`, `axiom`, `unsafe`). |
| `#print axioms` | SOUND | `PathDecomp.twin_insert`, `theta_decomp`, `theta_rooted`, `test1_fatTheta`, `test1At_of_twins`, `test2At_of_twins`, `test1At_of_cherryLN`, `fan_root_move`, `test1At_of_move1`, `test1At_of_move2`, `test1At_of_move1'`, `test1At_of_move2'`, `lN_of_cherryLN`, `test1At_of_LN_matching`, `forestLN_far_chain`: each `[propext, Classical.choice, Quot.sound]` (`axioms.lean`). |
| `Test1At` / `Test2At` | SOUND | Budgets `(card V − 1)/2` with `2 ≤ ends r`, and `card V / 2` with `3 ≤ ends r`, on `delVert J z`, for every `hr : J.Adj z r`. They are the decomposition clause only; the parity hypotheses of Definition 1.1 are separate arguments (`hz`) of the theorems (F14). |
| `twin_insert` vs Lemma 3.1 | SOUND | Same hypotheses ($a\ne b$, $x\ne y$, $x,y\notin\{a,b\}$, no $K$-edge at $x,y$, $a$ has a $K$-edge, $E(G)=E(K)\cup\{ax,xb,ay,yb\}$); conclusion size $+1$, ends $+2$ at $x$ only. |
| `theta`, `fatTheta`, `test1_fatTheta` vs Thm 3.3 | SOUND | `fatTheta z a b L` is $K_{3,\|L\|}+ab$ with hubs $z,a,b$ ($z=h_1$ not adjacent to $a,b$); `hV` says every vertex is a hub or a leaf; `Even L.card`, `2 ≤ L.card`. Conclusion `Test1`, i.e. for every root a decomposition with `n + 2 = t/2 + 1` paths and two ends at $r$. Lean does not use 3-connectivity or the parity hypothesis (stronger, as its docstring says). |
| `test1At_of_twins`, `test2At_of_twins` vs Thm 3.2 | SOUND | `hx`, `hy`: $N_J(x)=N_J(y)=\{z,a,b\}$; `ha`: $a$ has a neighbour outside $\{z,x,y\}$; `twinDel` removes exactly the four twin edges; budgets $(\|J\|-1)/2-1$ and $\|J\|/2-1$; the exception $r\in\{x,y\}$ only for Test1, as in the paper. |
| `CherryList`, `CherryLN` vs Conj. 5.1 | SOUND | Children distinct, parents distinct, no chain of three pairs, non-edges, irreflexive. This excludes cycles (a 2-cycle or longer cycle contains a chain of three pairs) and siblings, so the components are exactly pairs and 2-chains rooted at an end. Since 7177aea isolated vertices are allowed; constraints touching an isolated vertex are vacuous, so this is equivalent to the paper's CL (the text now says so). |
| `test1At_of_cherryLN` vs Prop. 5.2 (T1) | SOUND | `OddData` (forest $N(z)$-join, $r$ root or child with $\ge2$ children) + parents distinct + depth $\le2$ is exactly "cherry data": $r$ cannot be a child (it would need two children), components are paths of $\le2$ edges rooted at an end; $x\notin T$ and $a,b\in T$ follow from the $T$-join parity. |
| `lN_of_cherryLN` | SOUND | Disjoint non-adjacent pairs form a `CherryList` (no parent is a child). Matches `LN` of `ConstrainedLovasz.lean` (pairs disjoint, child of odd degree, non-adjacent). |
| `test1At_of_LN_matching` | SOUND | `LN` applied to $H=(J-z)-M$ with all pairs of the perfect matching $(a_0,r)::L$; then `test1At_of_matchingOdd`. No 3-connectivity, as Corollary 4.3 needs. |
| `fan_root_move`, `test1At_of_move1(')` vs Thm 4.2 (M1) | SOUND | `hone`: at most one neighbour of $r$ in $N(z)$; `hrw`; conclusion from a $(\|J\|-1)/2$-path decomposition of $(J-z)-rw$ with two ends at $w$. Lean does not need $w\notin T$ (more general). `move1'` takes `Test1At J' z w` for any $J'$ agreeing with $J$ off $z$ except $rw$, plus `J'.Adj z w`. |
| `test1At_of_move2(')` (M2) | SOUND | `htwo`: the $T$-neighbours of $r$ lie in $\{u,v\}$, with $u$ one of them. Lean needs neither $v\in N(r)\cap T$ nor $u\ne v$ (more general). |
| `forestLN_far_chain` vs §5 "Relation to $L_N$" | SOUND | `Packed G {a, x}`, $b$ adjacent to neither, $b$ odd; conclusion `ForestLN G [(x, a), (b, x)]`, i.e. $a\notin Q(x)$, $x\notin Q(b)$. Matches the 2c4d726 text exactly. |
| Lean coverage of "Lean" claims | SOUND | The parts that are not in Lean are labelled as such: the parity of $J'$ in Theorem 4.2 and the chaining of Corollary 4.3 (the paragraph after Cor 4.3), the (T2) half of Prop 5.2, 3-connectivity in Thm 3.3. Other names cited (`ends_mod_two`, `gallai_iff_spineTests'` (unconditional), `test1At_of_oddBase`, `test2At_of_forestBase2`, `test1At_of_matchingOdd`, `gallai_of_spineTestsNMC`, `avoid_packed_of_reach`, `fan_single`) exist with the cited content. |

### 1.2 Proofs on paper (check 2)

| Item | Grade | Notes |
|---|---|---|
| §1, all-odd lift and (T2) form | SOUND / NIT | Matches [T2, Thm 7.1] and [T2, Thm 4.5]; the latter needs $d_J(r)\ge3$ (F5). |
| Lemma 3.1 | SOUND | It is EC Lemma 5.2 with $C=a\,y\,b\,x\,a$ ($c_1=y$, $c_2=b$ the one old vertex, $c_3=x$ new). Case "$a$ ends some $P$": $P$ becomes $P\,x$ and $x\,b\,y\,a$ is added; $a$ keeps one end, $x$ gains two. Case "$a$ interior to $Q$": $X\,y\,b\,x$ and $x\,a\,Y$ are paths since $b\notin X-a$ and $x,y$ are new. |
| Theorem 3.2 | SOUND | $K=B^-$, $G=J-z$; $a$ keeps an edge $aw$ in $B^-$ ($w\ne z,x,y$). |
| Spine-induction paragraph | SOUND | In `gallai_of_spineTestsNMC` the order-$n$ step has `RootedAt` for every member of $\mathcal C$ of smaller order and `MarkedBoundUpTo (n−2)`. $\|B-x-y\|=\|B\|-2$ is even and $d_{B-x-y}(r)$ is even (it is $d_B(r)$ or $d_B(r)-2$), so `RootedAt`$(B-x-y,r)$ gives $\le(\|B\|-2)/2$ paths with two ends at $r$, which is the hypothesis of Thm 3.2(a). For $r\in\{x,y\}$ the marked bound gives Gallai's bound when $B-x-y$ is connected. In the spine, $N(z)$ is the even set of $B$, so the twins are there. The claim is stated as "not formalised" and limited to $B-x-y\in\mathcal C$, which is right. |
| Theorem 3.3 | SOUND | Induction by Lemma 3.1 with $a=h_2$ (it keeps $h_2h_3$); the rooted step takes $r$ as the twin $x$. |
| Explicit construction after Thm 3.3 | SOUND | Checked by `fat_theta_explicit.py` for $t=4,6,\dots,40$ ($q=0$, $q=1$ and $q\ge2$): a path partition of $\Theta_L$ into $t/2+1$ paths with two ends at $r$. For $t=2$, $h_1$ is also the unique even vertex but $J$ is only 2-connected, as the theorem says. |
| Lemma 4.1 | SOUND | Statement identical to `fan_single`. |
| Theorem 4.2, parities and $N(z)$ | SOUND | M1: $r$ loses $rw,zr$; $w$ trades $rw$ for $zw$; $z$ trades $zr$ for $zw$. M2: $r,u,z$ each lose two. $N(z)$ becomes $T-r+w$, $T-\{r,u\}$. `a41rm` checked both claims at every state generated in all closures (8,112 roots at $n\le9$, all 12,824,990 at order 11): no violation. |
| Theorem 4.2, zero-end counts | SOUND | M1: even vertices of $G-rw$ are $(T-r)\cup\{w\}$, $w$ no longer adjacent to $r$, so $\le1$ neighbour of $r$ can lack an end, and $b_{D'}(w)\ge2$. M2: even vertices of $G-ru$ are $T-\{r,u\}$; the only even neighbour $v$ has $\ge2$ ends; $u$ is odd so $b_{D'}(u)\ge1>0$. In both, $r$ is odd in the smaller graph, so $b_D(r)=b_{D'}(r)+1\ge2$. |
| Attribution to MR Thm 145 | SOUND | MR p. 158–159: "The one-edge step" (at most one other even neighbour, an odd neighbour $w$, Fan restores $rw$) and "A second even neighbor" ($u,v$, delete $ru$). The note uses only these steps, not the minimality argument, and says so. A single M2 can never reach matching data ($J'[T-r-u]=J[T-r-u]$, and a perfect matching there plus $ru$ would match $J[T]$); the data agree (no path "M2" alone). |
| Corollary 4.3 | SOUND | Moves keep the budget and need no connectivity; $H^*=(J^*-z)-M^*$ has no even and no isolated vertex; `LN` has no connectivity hypothesis. |
| Proposition 5.2 | SOUND (T1) / NIT (T2) | (T2) needs $d_J(r)\ge3$ for [T2, Thm 4.5] (F5). |
| Lemma 5.5 | SOUND | Each edge $uc$ ($c\in C$) gives exactly one end in $C$ on a path through $u$ (two such edges on one path give its two ends); the other $\|C\|-e_F(u,C)$ ends are on paths inside $C$, two each; the $Q(x)$, $x\in X\cap C$, avoid $u$, lie in $C$ and are distinct by (ii). |
| Example 5.3 (net) | SOUND | Brute force: the net has 20 Lovász decompositions, none satisfies the 3-chain $0\leftarrow1\leftarrow5\leftarrow3$ plus the pair $2\leftarrow4$; each condition alone is satisfiable. It is `fl.c`'s first order-6 `cp` failure, `ECqg`, with the same labels. |
| Example 5.4 (routes) | SOUND / NIT | 9 decompositions, none has $Q(2)$ avoiding $\{0,4\}$; of the 52 route triples on the double star 8 are infeasible, all with $cb\in E$, while every 2-chain on the same triples is satisfiable. The example is trivial ($Q(c)$ of a leaf contains its neighbour) and the notation switches from $Q(a)$ to $Q(c)$ (F12). |
| $K_{1,3}$ star | SOUND | 3 decompositions, none satisfies $u\leftarrow\{x,y\}$; (H1) fails ($2>(3-1)/2$). |
| Example 5.6 (claw + 2-chain) | SOUND | 228 Lovász decompositions, none satisfies both units (36 satisfy the claw alone, 75 the 2-chain alone); degrees $(3,1,1,1,1,3,3,5)$ and (H1) at 6 ($C=\{0,1,3,4,5,7\}$: $2\le(6-2)/2$; $C=\{2\}$) as stated. It is `fl.c`'s `lk` failure `G?BDC{ L 5 6 3 4 K 7 1 2 H1=1`. |
| One 2-chain far apart (2c4d726) | SOUND | With $Y=\{a,x\}$ packed and $b$ adjacent to neither, the set form of $L_1$ gives $D$ with every path meeting $Y$ once and $Q(b)\cap Y=\emptyset$; $Q(x)\ni x$ then misses $a$. The 9b5035b version ("$a,x,b$ pairwise at distance $\ge3$ ... follows from `avoid_packed_of_reach`") was also correct, with a stronger hypothesis than needed; the new statement is the sharp form of the same argument, and it is in Lean. Since $b$ has no neighbour in $Y$ this is already `lovasz_avoid_set`; `avoid_packed_of_reach` is used with the trivial walk. |

### 1.3 Computation (check 3)

| Claim (location) | Grade | My result |
|---|---|---|
| (T1) $n\le9$ table row, §2.2 | SOUND | `a41 tiers`: 1 + 28 + 5,231 graphs, 4 + 126 + 25,210 roots, 8,112 no-data roots (38 at $n=7$, 8,074 at $n=9$, none at $n=5$), tiers **7,802 / 166 / 135 / 3 / 6**. Root-by-root identical to `nd_t1_le9.txt` in tier, deficiency, twin flags and, at tiers 3–4, least excess (0 mismatches). |
| Tier-1 share 96.2 / 98.85 / 98.7% | SOUND | Arithmetic. |
| Sibling excess 1 at 128 / 135, 21,937 / 22,421, 586 / 614 | SOUND | $n\le9$ recomputed (7 roots need excess 2); order 11 and (T2) from the data files. |
| "Every excess-1 base found at $n\le9$ is a claw" | SOUND | All 128; it is forced: at a root with no linkage some vertex has $\Phi$-degree $\ge3$, and with excess 1 that vertex must be a child with two children. |
| Deficiencies 7,694 / 412 / 6; order 11: 12,381,258 / 441,436 / 2,288 / 8 | SOUND | Both recomputed (order 11 by `a41nd`). The 6 are the leaf roots of $K_{3,6}+h_2h_3$ (`H??F~z}`). |
| Obs 2.1(a), sentences 1 and 3 | SOUND | No root of tier $\ge3$ has a linkage (0 of 144). |
| Obs 2.1(a), sentence 2 | GAP | F2. |
| Obs 2.1(b) universality | [UNIV] |
| Obs 2.1(c) | SOUND | $n\le9$: all 144 roots of tier $\ge3$ have a twin pair (recomputed). Order 11: 75 / 75 at tiers 4–5, 906 twin-free at tier 3, 500 of them cones (data file). |
| Obs 2.1(d) | SOUND | $d(z)=4$: tiers 1–2 only, at $n\le9$ (5,324 / 136, recomputed) and order 11 (data). |
| Order 11 table row | SOUND | `a41nd` on all of `geng -C 10`: **8,738,914** graphs, **47,072,398** roots, **12,824,990** no-data roots, 765,548 with a twin pair; $d(z)$ distribution equal to `nd_t1_11_agg.txt`. Tiers 4–5: all 75 roots re-classified from scratch, 34 tier 4 and 41 tier 5, identical. Tier 1 vs $\ge2$ on a systematic 1/300 sample: [SAMPLE]. |
| (T2) row | SOUND (not recomputed) | Consistent with `verify_t2_le10.txt`, `xcheck_t2_le10.txt` and with [T2] (717,942 instances, 4 roots with $r$ a child). I did not re-run (T2). |
| Theorem 3.2 data: 84 roots certified | SOUND | `twin_cert.py`'s final `check()` is a complete certificate check (paths, edge partition, budget, ends at $r$), independent of `nd.c`; data 9 + 75. |
| Root moves, $n\le9$ | SOUND | `a41rm` (exact closure, depth 6): **6,532** reached, root by root identical to `rootmove_t1_le9_perroot.txt`; **3,467** by one M1; per tier 6,367 / 141 / 24 / 0; not reached: 928 twin-free tier 1, 10 twin-free tier 2, 642 with twins. |
| Root moves, order 11 | SOUND | Tier $\ge2$ roots of `nd_t1_11_ge2.txt.gz` (147,070): every count of `rootmove_t1_11_all.txt` and `rootmove_t1_11_ge3.txt` at tiers 2–5 reproduced (e.g. tier 3: 141 + 2,927 reached, 765 + 18,588 not). All 12,824,990 roots: **10,016,763** reached; not reached 326,442 with twins and 2,481,785 = 2,466,905 + 14,115 + 765 twin-free. |
| `fl.c` unit encodings | SOUND | Pair, 2-chain, 3-chain, star, route, claw: the generators, `sat_unit` and the `crv` masks match the §5 table. The `crv` encoding forbids only what (i)–(ii) forbid (a path with ends $s,w$ is rejected iff $p(s)$ or $p(w)$ lies on it or $s,w$ are siblings). The c2b57ca change (striking with every phase-2 solution) only adds certificates checked by `sat_unit`. |
| §5.1 table, orders 4–8 | SOUND | `a41 fam`: one 2-chain 18,190 / 0; 2-chain + pair [KP]; two 2-chains 130,560 / 0; 2-chain + two pairs 250,720 / 0; one 3-chain 45,268 / 0; 3-chain + pair 260,176 / 18 (order 6) + 4 (order 8); route 18,190 / 558, all with $cb\in E$; claw 22,932 / 16 and claw + pair 131,160 / 140, all violating (H1); claw + 2-chain 129,804 / 199, 9 with (H1); two stars 32,640 / 3,955, every failure with a star violating (H1); star 9,095, star + pair 87,160, star + 2-chain 130,560: 682 / 5,812 / 8,594 sets violate (H1) (exactly `fl.c`'s failure counts), and **0 failures** among the rest. |
| xcheck_fl (§5.1, order 6) | SOUND | My order-6 counts agree (2-chain + pair 776 / 0, 3-chain + pair 256 / 18, star 153 / 45, claw 216 / 0). |
| Order 10, one 2-chain | GAP | 5,937,582 sets recounted; the failure count has no data file (F3). |
| (H1) split at real instances, §5.2 | [H1] |

### 1.4 Claims and attributions (check 4)

| Item | Grade | Notes |
|---|---|---|
| Abstract "Computed (... every base lifted and checked independently)" | GAP | F1. |
| Summary table "exhaustive; every base verified" | GAP | F1. |
| `\VERIFYSTATUS` "every negative tier claim is confirmed independently" | GAP | F1. |
| Abstract (b) "a graph with one edge fewer" | NIT | F6. |
| Abstract (a) "cost exactly one path" | NIT | F7. |
| MR Thm 145 | SOUND | See 1.2. |
| EC Prop 5.5 | NIT | F8. |
| Spine induction | SOUND | See 1.2. |
| §5 packed 2-chain | SOUND | See 1.2. |
| Coverage paragraph and §6 | NIT | F10. |

---

## 2. Findings

- **F1 (GAP; abstract l. 52, summary table l. 140, `\VERIFYSTATUS` in `cells.tex`).**
  - The abstract says "Computed (validated exact solver, **every base lifted and checked
    independently**)" for all orders $\le11$, and the summary table says "exhaustive; every base
    verified". At order 11 `verify_nd.py` checked the 147,029 bases of tier $\ge2$ and a 2.5%
    sample of the tier-1 bases (317,148 of 12,677,920). `\VERIFYSTATUS` says exactly this; the
    abstract and the table do not.
  - `\VERIFYSTATUS` ends "every negative tier claim is confirmed independently". The shipped
    cross-check, `xcheck_tiers.py`, confirms only "no tier-1 base" (level $\ge2$) and "no linkage
    base" (level $\ge3$), as §2.1 correctly says. The tier-3 $\to$ 4 and 4 $\to$ 5 negatives
    (3 + 6 roots at $n\le9$, 34 + 41 at order 11) rest on `nd.c` alone. (For (T2) the 4 tier-4
    roots are [T2]'s, decided there by `route_ext`.)
  - **What I checked.** With independent code I re-derived every tier at $n\le9$ (all negatives
    included) and re-classified all 75 order-11 roots of tier 4–5 from scratch (identical). So the
    negatives are now confirmed, by this audit.
  - **Fix.** Abstract: "every base at order $\le9$ and for (T2) is lifted and checked, and at order
    11 every base of tier $\ge2$ and a 2.5% sample of tier 1". Table: the same. `\VERIFYSTATUS`:
    "the negative claims of tiers 1–2 are confirmed by `xcheck_tiers.py`; those of tiers 3–4 were
    re-derived independently in audit A41 ($n\le9$ and the 75 order-11 roots of tiers 4–5)".
- **F2 (GAP; Observation 2.1(a), l. 219–221).**
  - "At every root of tier 1 or 2, the first rooted linkage tried by the independent enumeration of
    `xcheck_tiers.py` is already a base." `xcheck_tiers.py` skips level-1 roots (`if level < 2:
    continue`), and at level-2 roots it runs only the tier-1 negative check. No shipped output
    records a positive linkage test, so the sentence is unsupported. It is also order-dependent.
  - **What the data do support** (`univ_t1_le9_tier2_failures.txt`, my universality run): every
    cherry structure is a base (0 of 179,152), and the 88 failing linkage structures lie at 19
    roots, **all of tier 1**. So at every tier-2 root every rooted linkage is a base, and the tier
    of every root at $n\le9$ is decided by structure alone: tier 1 iff a cherry linkage exists, tier
    $\le2$ iff a linkage exists.
  - **Fix.** Replace the sentence by that statement.
- **F3 (GAP, provenance; §2.1 l. 177–179, §5.1 table l. 438, README).**
  - (a) "all 36,947 queries issued at order $\le9$ agree with `route_ext` (28,879 infeasible,
    8,068 feasible), and so do 3,000 random forest queries": no output file is committed. These
    runs also predate the 2c4d726 change to `ndsolve.h`. My independent solver agrees with every
    $n\le9$ tier, so the conclusion stands, but the quoted counts cannot be reproduced from the
    repository.
  - (b) The order-10 entry "one 2-chain: 5,937,582 sets, 0 failures" is printed directly, not as a
    pending cell, and the README lists `fl_10_*.txt`, but only `fl_10_s.txt` exists. I recounted
    the **5,937,582** sets (32,851 graphs); the "0 failures" has no data.
  - **Fix.** Commit the solver cross-check output and `fl_10_k.txt` (or mark the cell pending).
- **F4 (NIT; Obs 2.1(b), l. 224–226).** "Forests with siblings fail at 32,706 of 88,148
  structures": these are the tier-3 structures ($r$ a root, excess $\ge1$). The 779,400 tier-4
  structures ($r$ a child) fail 124,925 times (`univ_t1_le9_summary.txt`). Say which. "Linkages
  with a path of length 3 or 4" should read "linkages with a path of length $\ge3$ (the failures
  have paths of length 3 or 4)".
- **F5 (NIT; §1 l. 101–102 and Proposition 5.2).** [T2, Theorem 4.5] assumes $d_J(r)\ge3$. The
  (T2) lift in §1 and the (T2) half of Prop 5.2 omit it. On the 3-connected instances $d_J(r)\ge4$,
  so nothing breaks. **Fix.** Add "($J$ 3-connected, or $d_J(r)\ge3$)".
- **F6 (NIT; abstract (b), l. 47–49).** "Each step turns (T1) at one root into (T1) at another root
  of a graph with one edge fewer": in M2, $J'$ has three edges fewer than $J$ ($ru$, $zr$, $zu$); it
  is $J'-z$ that has one edge fewer. The implication also runs from the moved instance back to the
  original. **Fix.** "(T1) at the moved root, in a graph whose deletion graph $J'-z$ has one edge
  fewer, implies (T1) at the original root".
- **F7 (NIT; abstract (a), l. 43–44).** "cost exactly one path": Lemma 3.1 is an upper bound,
  $p(G)\le p(K)+1$. **Fix.** "cost at most one path".
- **F8 (NIT; l. 253–254).** "The same insertion settles twins ... [EC, Proposition 5.5]": EC uses the
  cycle insertion there only when $ab\in E$; for $ab\notin E$ it uses suppression (EC Lemma 5.1).
  **Fix.** "The same insertion settles twins with adjacent neighbours in ...".
- **F9 (NIT; §5.2, l. 504–505).** "Stars ... never help at tier 3": at a tier-3 root a forest can
  contain a star component next to a claw. What is true: a forest whose sibling sets are all stars
  is a linear forest, hence a linkage, and there is none at tier 3. **Fix.** Say that.
- **F10 (NIT; §4 "Coverage" l. 371–378, §6 l. 521–523).**
  - "covered by ... a twin reduction (642)": these roots are covered only modulo the rooted floor
    for $B-x-y$, which is open item (2) when $B-x-y\notin\mathcal C$.
  - 507 of the 642 have cherry data and 15 are of tier 2, so CL covers 507 of them as well.
  - **Fix.** Give the twin class as "642 (507 also with cherry data)" and add "modulo (2)".
- **F11 (NIT; Theorem 3.3 remark and abstract l. 45–46).** "at $t=6$ that family is where the
  all-odd lift has no base": at order 11 the eight leaf roots of $K_{3,8}+h_2h_3$ are of tier 5 as
  well (`xcheck_t1_11_ge2.txt`: "level 5 fat theta 8"). **Fix.** "at $t=6$ and $t=8$".
- **F12 (NIT; §5, l. 398–399 and Example 5.4).** The route is introduced as "$x,b\notin Q(a)$" and
  the example uses "$x,b\notin Q(c)$". The example is trivial: whenever $c$ is a leaf at $b$,
  $b\in Q(c)$. **Fix.** One notation; say the 558 failures all have $cb\in E$ (verified) and that
  routes with $cb\notin E$ had no failure.
- **F13 (NIT; §7 l. 542, README "Reproduce").** The recipe omits order 5, but the table counts its
  1 graph and 4 roots (5,260 / 25,340); the recipe gives 5,259 / 25,336. Order 5 has no no-data
  root, so the other columns are unaffected. **Fix.** Add `nauty-geng -q -C -d3 5`.
- **F14 (NIT; Definition 1.1, Lean descriptions).**
  - Definition 1.1 cites "Lean `Test1At`, `Test2At`", which are the decomposition clauses only.
  - Lean is more general than the paper in harmless ways: `test1At_of_move1` does not need
    $w\notin T$; `test1At_of_move2` needs neither $u\ne v$ nor $v\in N(r)\cap T$; `CherryLN` allows
    isolated vertices; the twin and theta theorems need neither the parity hypothesis nor
    3-connectivity.
  - **Fix.** One sentence in §1.
- **F15 (NIT; scripts).**
  - `fl.c` reports (H1) for the **first** unit only. For `ss` at order 8 it prints "H1 holds at
    3,386 of them", which reads as a contradiction of §5.2; with both stars all 3,955 failures
    violate (H1) (my run). Report (H1) over all units.
  - `rm.c` caps the BFS queue at 200,000 states with a silent `break`, and deduplicates states by a
    64-bit hash. Both can only lose "reached" roots. My exact closure (no cap, full-state set) gives
    identical totals on all 12,824,990 order-11 roots, so the data are unaffected. Add an overflow
    counter.
  - §2.1 still describes `ndsolve.h` as branching "from the unended vertex of least degree"; since
    2c4d726 it branches on constrained vertices first.
- **F16 (NIT; §5.2 l. 491–493).** [H1-18]

---

## 3. Independent re-derivations (details)

[DETAILS]

## 4. Reproduction

`runs.sh` lists every command. Build: `g++ -O2 -std=gnu++17`. Timings on this machine (4 cores,
shared with the author's order-10 `fl` runs): (T1) $n\le9$ tiers 0.9 s; order-11 census and closure
3 min; universality $n\le9$ [UNIVTIME].
