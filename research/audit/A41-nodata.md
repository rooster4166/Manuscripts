# A41: Audit of nodata (manuscript, `NoData.lean`, scripts, data)

Date: 2026-11-28. Referee stance: adversarial. Grades: **SOUND**; **ERROR** (false as stated);
**GAP** (missing argument, missing provenance, or an overclaim that changes how a result reads;
fixable); **UNCLEAR**; **NIT** (wording). Findings are numbered F1, F2, ... (§2).

**Version.** I started at **9b5035b**. Seven commits landed during the audit, and all of them are
covered here:

| Commit | Author | What changed |
|---|---|---|
| 7177aea | author | `CherryLN` uses `(evenSet H).card = 0`; new `lN_of_cherryLN`, `test1At_of_LN_matching` |
| 2c4d726 | author | `forestLN_far_chain`; `ndsolve.h` fail-first with a 2^22 memo; `rm.c` and the order-11 root-move data; `xcheck_fl.py`; `\VERIFYSAMPLE` |
| c2b57ca | author | `fl.c` strikes sets with every phase-2 solution; `fl_10_s.txt` |
| c3aa970, 22fe14d, ef600f6 | another session | snapshots of my scripts and of my **draft** report (F1–F16); I committed nothing |
| a9a289d | author | applies draft findings F1–F15; adds `solver_xcheck*.txt`, `fl_10_c.txt`; fills `\FLCTEN`, `\FLSTEN` |
| 057b5f5 | author | drops compiled binaries |

The draft's finding numbers are kept. Each finding carries its status at **057b5f5**:
`nodata.tex` md5 `fcc82855…`, `NoData.lean` md5 `55095c87…` (unchanged since 2c4d726).

**Two findings are new since the draft, and both are ERRORs that a9a289d does not address:**
- **F17.** The tier-3 universality numbers are produced by a truncated enumeration in `nd.c -U`.
- **F18.** The §5.2 "star version" of CL has an explicit order-8 counterexample.

Cells still "(pending)" (`\FLKPTEN`, `\FLKKTEN`, `\FLSTARTEN`) are skipped, as instructed.

**Numbering.** As in the PDF:
- §1: Definition 1.1, Conjecture 1.2 ($L_N$).
- §2: Observation 2.1.
- §3: Lemma 3.1, Theorems 3.2, 3.3.
- §4: Lemma 4.1, Theorem 4.2, Corollary 4.3.
- §5: Conjecture 5.1 (CL), Proposition 5.2, Examples 5.3 (net) and 5.4 (routes), **Lemma 5.5**
  (star Hall condition; the brief's "Lemma 5.4"), Example 5.6 (claw).

"l." is a line of `nodata.tex` at 057b5f5.

**Auditor files** (`research/audit/A41-scripts/`; outputs are in the session scratchpad, not
committed):
- `runs.sh`: every command I ran.
- `a41.cpp`: my own exact constrained-Lovász solver, written from the definitions; it shares no
  code with `ndsolve.h`, `nd.c`, `fl.c` or `route_ext.c`. It has three modes:
  - `tiers`: the (T1) classification, with its own 3-connectivity test, matching, linkage
    enumeration, forest $T$-joins (cycle space) and rootings;
  - `univ`: every structure, as in Observation 2.1(a);
  - `fam`: the abstract families of §5.1.
  - Every solution found is re-verified from scratch before it is counted.
  - Options: `A41_PRUNE` (two sound prunings; its tier output is byte-identical to the plain
    run), `A41_MAXTIER=2`, `A41_COUNTONLY`, `A41_SKIP_H1`.
- `a41rm.cpp`: my own root-move closure (exact visited set, no queue cap). It also checks the
  parity and $N(z)$ claims of Theorem 4.2 at every state it generates.
- `a41nd.cpp`: my own order-11 census ($J=B+z$ over all 2-connected $B$ of order 10).
- `a41odd.cpp`: filter for connected graphs with every degree odd.
- `examples_bruteforce.py`: enumerates **every** Lovász decomposition of a small graph by plain
  recursion and tests the constraints on each one. Used for Examples 5.3, 5.4, 5.6 and $K_{1,3}$.
- `star_chain_pair.py`, `star_chain_pair_example.py`: the F18 counterexamples, by full enumeration.
- `fat_theta_explicit.py`: the explicit decomposition after Theorem 3.3, for $t=4,\dots,40$.
- `univ_h1.py`: the (H1) split of tier-3 structures.
- `cmp_sample11.py`: compares the order-11 sample with the authors' data.
- `count10.py`: order-10 set counts.
- `axioms.lean`: the axiom check for the 15 theorems.

---

## 0. Verdict

1. **The theorems are correct.**
   - I re-derived every proof:
     - Lemma 3.1, Theorem 3.2, Theorem 3.3 and its explicit construction;
     - Lemma 4.1 as used, and Theorem 4.2: the zero-end counts, the parities of $J'$, the change
       of $N(z)$;
     - Corollary 4.3, Proposition 5.2, Lemma 5.5;
     - the spine-induction paragraph after Theorem 3.2, and the far-apart 2-chain.
   - No step is false. The only mathematical omission, $d_J(r)\ge3$ for (T2) (F5), is fixed in
     a9a289d.
2. **The Lean is faithful and clean.**
   - `lake build` is green (18,440 jobs).
   - `NoData.lean` re-elaborates from source without a warning.
   - There is no `sorry`, `admit`, `native_decide` or `axiom`.
   - All 15 audited theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.
   - Each statement says what the paper claims. Where Lean differs it is more general (F14, now
     stated in the text).
3. **Almost every computed number reproduces with independent code, most of them root by root.**
   - **(T1), $n\le9$.**
     - Tiers 7,802 / 166 / 135 / 3 / 6.
     - Deficiencies, twin flags and least excess agree at all 8,112 roots.
   - **Root moves.**
     - $n\le9$: 6,532 roots reached, identical root by root; 3,467 by a single M1; by tier
       6,367 / 141 / 24 / 0; coverage 642 / 928 / 10.
     - Order 11: my own census of all 8,738,914 graphs gives exactly 47,072,398 roots,
       12,824,990 no-data roots, and the deficiency, $d(z)$ and twin counts.
     - My exact closure reaches **10,016,763** roots, with the quoted split
       326,442 / 2,466,905 / 14,115 / 765.
   - **Order-11 tiers.**
     - All 75 roots of tier 4–5 are re-classified from scratch.
     - A systematic 1/300 sample (43,132 no-data roots) agrees at every root.
   - **Universality.** The counts for tiers 1, 2 and 4 agree.
   - **Abstract families.** Every order-$\le8$ count in the §5.1 table agrees.
   - **Order 10.** All three set totals agree.
   - **Examples.** The three examples hold, checked over all their Lovász decompositions.
4. **Findings.**
   - **F17 (ERROR).** Observation 2.1(a) says "tier-3 structures fail at 32,706 of 88,148". There
     are **1,239,486** tier-3 structures at $n\le9$, and **278,296** of them fail. The cause is a
     bug in `nd.c -U`: it abandons a root's tier-3 enumeration at the first linkage that is a base.
     The same truncated set underlies the §5.2 sentence "(H1) explains 786 of the 804 ... the other
     18 come from a claw interacting with 2-chains". Over all structures (H1) explains 59,953 of
     60,920, and among the 967 others 295 contain no claw at all.
   - **F18 (ERROR).** §5.2 says the data support "pairs, 2-chains and stars, every star satisfying
     (H1)", with "no failure at order $\le8$". On the connected all-odd order-8 graph $F$ with edges
     $05,06,07,15,25,37,46,67$, take the star $7\leftarrow\{1,2\}$, the 2-chain
     $5\leftarrow6\leftarrow3$ and the pair $4\leftarrow0$. (H1) holds at 7, and none of the 60
     Lovász decompositions satisfies all three. Every two of the units are satisfiable together.
     Six such structures occur at real $n=9$ roots. CL itself (pairs and 2-chains) is not affected.
   - **F1–F16 (draft).**
     - F1 and F2 (GAP), F4–F12 and F14–F15 (NIT) are fixed in a9a289d.
     - F3(b) (the order-10 2-chain data) and the README part of F13 remain open.
     - F16 is superseded by F17.

**Recommendation.** Minor revision. No theorem is wrong, but F17 and F18 change two quoted
computational statements and one recommendation of §5.2, and they must be fixed before the note is
cited.

---

## 1. Graded items

### 1.1 Lean (check 1)

| Item | Grade | Notes |
|---|---|---|
| `lake build` | SOUND | Green, 18,440 jobs, after 7177aea and after 2c4d726. `lake env lean GallaiLean/NoData.lean` from source prints nothing. |
| `sorry` etc. | SOUND | None in `NoData.lean`: no `sorry`, `admit`, `native_decide`, `axiom` or `unsafe`. |
| `#print axioms` | SOUND | Each of the following gives `[propext, Classical.choice, Quot.sound]` (`axioms.lean`): `PathDecomp.twin_insert`, `theta_decomp`, `theta_rooted`, `test1_fatTheta`, `test1At_of_twins`, `test2At_of_twins`, `test1At_of_cherryLN`, `fan_root_move`, `test1At_of_move1`, `test1At_of_move2`, `test1At_of_move1'`, `test1At_of_move2'`, `lN_of_cherryLN`, `test1At_of_LN_matching`, `forestLN_far_chain`. |
| `Test1At`, `Test2At` | SOUND | Budget `(card V − 1)/2` with `2 ≤ ends r`, and budget `card V / 2` with `3 ≤ ends r`, on `delVert J z`, for every `hr : J.Adj z r`. These are the decomposition clauses only; the parity hypotheses are separate arguments (F14, now said in §1). |
| `twin_insert` vs Lemma 3.1 | SOUND | Same hypotheses: $a\ne b$, $x\ne y$, $x,y\notin\{a,b\}$, no $K$-edge at $x$ or $y$, $a$ has a $K$-edge, and $E(G)=E(K)\cup\{ax,xb,ay,yb\}$. Conclusion: size $+1$, and $+2$ ends at $x$ only. |
| `theta`, `fatTheta`, `test1_fatTheta` vs Thm 3.3 | SOUND | `fatTheta z a b L` is $K_{3,\|L\|}+ab$ with hubs $z,a,b$; $z=h_1$ is not adjacent to $a$ or $b$. `hV` says every vertex is a hub or a leaf. Hypotheses: `Even L.card` and `2 ≤ L.card`. Conclusion: `Test1`, with $n+2=t/2+1$ paths and two ends at every leaf root. Lean uses neither 3-connectivity nor the parity hypothesis, so it is more general. |
| `test1At_of_twins`, `test2At_of_twins` vs Thm 3.2 | SOUND | `hx`, `hy` give $N_J(x)=N_J(y)=\{z,a,b\}$. `ha` says $a$ has a neighbour outside $\{z,x,y\}$. `twinDel` removes exactly the four twin edges. Budgets are $(\|J\|-1)/2-1$ and $\|J\|/2-1$. As in the paper, the exception $r\in\{x,y\}$ is allowed for Test1 only. |
| `CherryList`, `CherryLN` vs Conj 5.1 | SOUND | The conditions: children distinct, parents distinct, no chain of three pairs, non-edges, irreflexive. These exclude cycles (any cycle contains a chain of three pairs) and siblings, so the components are exactly pairs and 2-chains rooted at an end. Isolated vertices are allowed since 7177aea. Constraints touching an isolated vertex are vacuous, so this is equivalent to the paper's CL; the text says so. |
| `test1At_of_cherryLN` vs Prop 5.2 (T1) | SOUND | `OddData` together with distinct parents and depth $\le2$ is exactly cherry data. $r$ cannot be a child, since it would need two children. $x\notin T$ and $a,b\in T$ follow from the $T$-join parity. |
| `lN_of_cherryLN` | SOUND | Disjoint non-adjacent pairs form a `CherryList`. `LN` is the statement of `ConstrainedLovasz.lean`. |
| `test1At_of_LN_matching` | SOUND | Applies `LN` to $(J-z)-M$, then `test1At_of_matchingOdd`. It needs no 3-connectivity, as Corollary 4.3 requires. |
| `fan_root_move`, `test1At_of_move1(')` (M1) | SOUND | `hone`: $r$ has at most one neighbour in $N(z)$. The hypothesis is a $(\|J\|-1)/2$-path decomposition of $(J-z)-rw$ with two ends at $w$. Lean does not need $w\notin T$. `move1'` takes `Test1At J' z w` for any $J'$ that agrees with $J$ off $z$ except at $rw$. |
| `test1At_of_move2(')` (M2) | SOUND | `htwo`: the $T$-neighbours of $r$ lie in $\{u,v\}$, and $u$ is one of them. Lean needs neither $u\ne v$ nor $v\in N(r)$. |
| `forestLN_far_chain` | SOUND | Hypotheses: `Packed G {a, x}`, $b$ adjacent to neither, $b$ odd. Conclusion: `ForestLN G [(x, a), (b, x)]`. This matches the 2c4d726 text. |
| Claims labelled "Lean" | SOUND | The parts not in Lean are labelled as such: the parity of $J'$ in Thm 4.2, the chaining in Cor 4.3, the (T2) half of Prop 5.2, and 3-connectivity in Thm 3.3. The other cited names exist with the cited content: `ends_mod_two`, `gallai_iff_spineTests'` (unconditional), `test1At_of_oddBase`, `test2At_of_forestBase2`, `test1At_of_matchingOdd`, `gallai_of_spineTestsNMC`, `avoid_packed_of_reach`, `fan_single`. |

### 1.2 Proofs on paper (check 2)

| Item | Grade | Notes |
|---|---|---|
| §1: the all-odd lift and its (T2) form | SOUND | Matches [T2, Thm 7.1] and [T2, Thm 4.5]. The latter's $d_J(r)\ge3$ is now stated (F5, fixed). |
| Lemma 3.1 | SOUND | It is EC Lemma 5.2 with $C=a\,y\,b\,x\,a$: $c_2=b$ is the one old vertex and $c_3=x$ is new. If $a$ ends some $P$: $P$ becomes $Px$ and $x\,b\,y\,a$ is added. If $a$ is interior to $Q$: $X\,y\,b\,x$ and $x\,a\,Y$ are paths, because $b\notin X-a$ and $x,y$ are new. |
| Theorem 3.2 | SOUND | $K=B^-$ and $G=J-z$. The edge $aw$ ($w\ne z,x,y$) stays in $B^-$. |
| Spine-induction paragraph | SOUND | In `gallai_of_spineTestsNMC` the order-$n$ step has `RootedAt` for smaller members of $\mathcal C$ and `MarkedBoundUpTo (n−2)`. $\|B-x-y\|$ is even, and $d_{B-x-y}(r)\in\{d_B(r),d_B(r)-2\}$ is even. So `RootedAt`$(B-x-y,r)$ is the hypothesis of Thm 3.2(a). For $r\in\{x,y\}$ the marked bound gives Gallai's bound when $B-x-y$ is connected. In the spine $N(z)$ is the even set of $B$, so the twins lie in it. The claim is limited to $B-x-y\in\mathcal C$ and marked "not formalised", correctly. |
| Theorem 3.3 | SOUND | Induction by Lemma 3.1 with $a=h_2$, which keeps the edge $h_2h_3$; $r$ is the twin $x$. |
| Explicit construction after Thm 3.3 | SOUND | `fat_theta_explicit.py` checks $t=4,6,\dots,40$, covering $q=0$, $q=1$ and $q\ge2$: $t/2+1$ paths, two ends at $r$. |
| Lemma 4.1 | SOUND | The statement is identical to `fan_single`. |
| Thm 4.2: parities and $N(z)$ | SOUND | In M1, $r$ loses $rw$ and $zr$, $w$ trades $rw$ for $zw$, and $z$ trades $zr$ for $zw$. In M2, $r$, $u$ and $z$ each lose two edges. `a41rm` checked both claims at every state generated, for all $n\le9$ roots and all 12,824,990 order-11 roots. |
| Thm 4.2: zero-end counts | SOUND | M1: the even vertices of $G-rw$ are $(T-r)\cup\{w\}$, and $w$ is no longer a neighbour of $r$. So at most one neighbour of $r$ has no end, while $b_{D'}(w)\ge2$. M2: the even vertices of $G-ru$ are $T-\{r,u\}$, and the only even neighbour $v$ has at least two ends; $b_{D'}(u)\ge1$. In both cases $b_D(r)=b_{D'}(r)+1\ge2$. |
| MR Thm 145 attribution | SOUND | MR p. 158–159: "The one-edge step" and "A second even neighbor". The note uses only these two steps and says so. A lone M2 can never reach data: $J'[T-r-u]=J[T-r-u]$, and a perfect matching there plus $ru$ would match $J[T]$. The data agree. |
| Corollary 4.3 | SOUND | $H^*$ has no even vertex and no isolated vertex, and `LN` has no connectivity hypothesis. |
| Prop 5.2 | SOUND | The (T2) hypothesis $d_J(r)\ge3$ is now stated. |
| Lemma 5.5 | SOUND | Each edge $uc$ ($c\in C$) gives exactly one end in $C$ on a path through $u$. The remaining $\|C\|-e_F(u,C)$ ends lie on paths inside $C$. The paths $Q(x)$, $x\in X\cap C$, lie in $C$ and are distinct by (ii). |
| Example 5.3 (net) | SOUND | 20 Lovász decompositions; none satisfies both units, while each condition alone is satisfiable. It is `fl.c`'s first order-6 `cp` failure (`ECqg`), with the same labels. |
| Example 5.4 (routes) | SOUND | 9 decompositions, none with $Q(2)$ avoiding $\{0,4\}$. Of the 52 route triples, 8 are infeasible, all with $cb\in E$; every 2-chain on the same triples is satisfiable. |
| $K_{1,3}$ star | SOUND | 3 decompositions, none satisfies the star; (H1) fails. |
| Example 5.6 | SOUND | 228 decompositions; none satisfies both units (36 satisfy the claw, 75 the 2-chain). The degrees and (H1) at 6 are as stated. It is `fl.c`'s `lk` failure `G?BDC{ L 5 6 3 4 K 7 1 2`. |
| Far-apart 2-chain | SOUND | Take $Y=\{a,x\}$, which is packed. Then every path meets $Y$ at most once and $Q(b)\cap Y=\emptyset$. Since $x\in Q(x)$, $a\notin Q(x)$. The 9b5035b sentence ("pairwise at distance $\ge3$") was also correct, with a stronger hypothesis than needed; 2c4d726 states the sharp form and proves it in Lean. Because $b$ has no neighbour in $Y$, this is already `lovasz_avoid_set`. |
| §5.2 "star version" of CL | ERROR | F18. |

### 1.3 Computation (check 3)

| Claim (location) | Grade | My result |
|---|---|---|
| (T1) $n\le9$ row (§2.2) | SOUND | `a41 tiers`: 1 + 28 + 5,231 graphs; 4 + 126 + 25,210 roots; 8,112 no-data roots (38 at $n=7$, 8,074 at $n=9$, none at $n=5$). Tiers **7,802 / 166 / 135 / 3 / 6**, identical root by root to `nd_t1_le9.txt`: 0 mismatches in tier, deficiency, twin flags, and least excess at tiers 3–4. |
| Tier-1 shares | SOUND | 96.2%, 98.85% and 98.7% are correct arithmetic. |
| Excess 1 at 128 / 135, 21,937 / 22,421, 586 / 614 | SOUND | The $n\le9$ count is recomputed. The order-11 and (T2) counts come from the data files. |
| "Every excess-1 base at $n\le9$ is a claw" | SOUND | All 128 are. It is also forced: a root of tier $\ge3$ has no linkage. |
| Deficiencies | SOUND | Recomputed at $n\le9$ (7,694 / 412 / 6) and at order 11 (12,381,258 / 441,436 / 2,288 / 8). The six roots of deficiency 6 are the leaf roots of $K_{3,6}+h_2h_3$. |
| Obs 2.1(a), tiers 1, 2, 4 | SOUND | 0 / 179,152; 88 / 351,032; 124,925 / 779,400. The 88 failures lie in 6 graphs with $d(z)=4$, at 19 roots, all of tier 1. |
| Obs 2.1(a), tier 3 | ERROR | **278,296 / 1,239,486**, not 32,706 / 88,148 (F17). |
| Obs 2.1(b) | SOUND | No root of tier $\ge3$ has a linkage. At every tier-2 root every rooted linkage is a base. Tier 1 holds iff a cherry linkage exists. |
| Obs 2.1(c), (d) | SOUND | Twins: all 144 tier-$\ge3$ roots at $n\le9$ have a twin pair; at order 11, 75 of 75 tier-4–5 roots do, and there are 906 twin-free tier-3 roots, 500 of them cones. At $d(z)=4$ only tiers 1–2 occur (recomputed at $n\le9$; order 11 from the data). |
| Order-11 row | SOUND | `a41nd` gives **8,738,914** graphs, **47,072,398** roots, **12,824,990** no-data roots and 765,548 roots with twins; the $d(z)$ distribution equals `nd_t1_11_agg.txt`. All 75 roots of tier 4–5 re-classified: 34 / 41. A systematic sample (every 300th graph of `geng -C 10`: 29,164 graphs, 43,132 no-data roots) gives tiers 1 / 2 / $\ge3$ = 42,568 / 478 / 86, identical at every root. |
| (T2) row | SOUND (not re-run) | Consistent with `verify_t2_le10.txt`, `xcheck_t2_le10.txt` and [T2]. |
| 84 twin certificates | SOUND | The final `check()` in `twin_cert.py` is a complete certificate check. |
| Solver cross-check (§2.1) | SOUND | It now cites 9,376 queries (1,270 / 8,106) and 3,000 random queries; `data/solver_xcheck.txt` supports both. |
| Root moves, $n\le9$ | SOUND | 6,532, identical root by root; 3,467 by a single M1; by tier 6,367 / 141 / 24 / 0; coverage 928 / 10 / 642. |
| Root moves, order 11 | SOUND | All tier-$\ge2$ counts of `rootmove_t1_11_all.txt` and `rootmove_t1_11_ge3.txt` reproduce. Over all 12,824,990 roots, **10,016,763** are reached. Not reached: 326,442 with twins, and 2,481,785 = 2,466,905 + 14,115 + 765 twin-free. |
| `fl.c` encodings | SOUND | The units, `sat_unit` and the `crv` masks match the §5 table. The c2b57ca and a9a289d changes are sound. |
| §5.1 table, orders $\le8$ | SOUND | `a41 fam` results (sets / failures): see the list after this table. |
| `xcheck_fl` (order 6) | SOUND | 776 / 0, 256 / 18, 153 / 45 and 216 / 0 agree with my counts. |
| Order 10 | SOUND / GAP | I recounted 5,937,582 one-2-chain sets, 20,980,976 one-3-chain sets, and 2,968,791 one-star sets, of which 50,675 violate (H1); these match `\FLCTEN`, `\FLSTEN` and the printed entry. The 2-chain's "0 failures" still has no data file (F3(b)). I did not re-solve at order 10. |
| (H1) at real instances (§5.2) | ERROR | F17. |

`a41 fam` results at orders 4–8 (sets / failures):
- one 2-chain: 18,190 / 0;
- 2-chain + pair: 174,320 / 0;
- two 2-chains: 130,560 / 0;
- 2-chain + two pairs: 250,720 / 0;
- one 3-chain: 45,268 / 0;
- 3-chain + pair: 260,176 / 18 + 4;
- route: 18,190 / 558, all with $cb\in E$;
- claw: 22,932 / 16; claw + pair: 131,160 / 140; all of these failures violate (H1);
- claw + 2-chain: 129,804 / 199, of which 9 satisfy (H1);
- two stars: 32,640 / 3,955, every failure with a star that violates (H1);
- star, star + pair, star + 2-chain: 9,095, 87,160 and 130,560 sets. Of these, 682, 5,812 and
  8,594 violate (H1), which is exactly `fl.c`'s failure count; the rest have **0** failures.

### 1.4 Claims and attributions (check 4)

| Item | Grade | Notes |
|---|---|---|
| Verification scope (abstract, summary table, `\VERIFYSTATUS`) | SOUND | Fixed in a9a289d (F1). |
| Abstract (a), (b) wording | SOUND | Fixed (F6, F7, F11). |
| Abstract l. 68–69: "stars or claws ... without a Hall condition" | NIT | This suggests that stars *with* (H1) are fine. F18 shows that they are not, in combination with a 2-chain and a pair. |
| MR Thm 145, EC Prop 5.5 | SOUND | EC wording fixed (F8). |
| Spine induction; far-apart 2-chain | SOUND | See §1.2. |
| Coverage paragraph, §6 | SOUND | Fixed (F10). |

---

## 2. Findings

### New since the draft (not addressed in a9a289d)

- **F17 (ERROR). The tier-3 universality data are truncated.**
  - **Where.** Observation 2.1(a) (a9a289d numbering), l. 233–235: "Tier-3 structures ($r$ a root, sibling excess
    $\ge1$) fail at $32{,}706$ of $88{,}148$". §5.2, l. 508–510: "(H1) explains $786$ of the $804$
    failing structures with one vertex of two children ($n\le9$). The other $18$ come from a claw
    interacting with 2-chains". The data files `univ_t1_le9_summary.txt` (tier-3 entry) and
    `star_hall_t1_le9.txt`.
  - **Cause.** In `nd.c` the tier-3 universality pass uses `fe_excess = -2` (l. 434). In
    `forest_rootings` (l. 290), a rooting of excess 0 (a linkage) fails the `univ` test
    `exc >= 1`. It then falls through to
    `else if ((fe_excess < 0 || exc == fe_excess) && base_ok(phim)) { ...; return 1; }`.
    Since $-2<0$, the whole tier-3 enumeration of that root stops at the first linkage that is a
    base. At every tier-1 or tier-2 root only a prefix of the forests is counted. The tier-1, 2 and
    4 passes are unaffected, and so is the classification mode, where `fe_excess` $\ge1$.
  - **Evidence.**
    - `a41 univ` gives tier 1: 0 / 179,152; tier 2: 88 / 351,032; tier 4: 124,925 / 779,400, as
      published. Tier 3 gives **278,296 / 1,239,486**; the population alone is confirmed by a
      count-only run.
    - At the 144 roots of tier $\ge3$, where nd.c's pass runs to the end, my counts equal nd.c's
      exactly.
    - Running `nd.c -UU` and my (H1) script on its output reproduces `star_hall_t1_le9.txt`
      exactly (18 / 786 / 32,707 / ...). So the published (H1) numbers describe this truncated
      subset.
  - **Correct numbers ($n\le9$, every structure).**
    - Excess 1: 735,993 structures, 60,920 failures.
    - (H1) is violated in **59,953** of the failures and holds in **967**.
    - Shapes of the 967: a single claw-type tree alone, 558; a claw plus one path, 114; **no claw
      at all**, 295. The no-claw cases are paths rooted at an interior vertex next to other paths,
      e.g. a 4-path rooted at its middle with a 2-path. Six of them are star + 2-chain + pair
      (F18).
    - So "the other 18 come from a claw interacting with 2-chains" is false for the full
      population. Within nd.c's subset the 18 all contain a claw: with a 2-chain 10, with a
      3-chain 4, with a pair 2, alone 2.
    - All of the 967 lie at roots of tier $\le2$. At the 144 roots of tier $\ge3$, every
      excess-1 failure violates (H1): 48 of 5,400 structures fail.
  - **Fix.**
    - In `nd.c` l. 290, guard the `else if` with `!univ`.
    - Re-run `-U` / `-UU` and `star_hall.py`.
    - Quote the full counts: tier 3 fails at 278,296 of 1,239,486; (H1) explains 59,953 of the
      60,920 excess-1 failures.
    - Replace "the other 18 come from a claw interacting with 2-chains" by the shape statistics,
      or restrict the sentence explicitly to roots of tier $\ge3$. There, (H1) explains all 48
      excess-1 failures; at excess $\ge2$ some (H1)-satisfying failures remain (12 at excess 2,
      36 at excess 3).
- **F18 (ERROR). The "star version" of CL in §5.2 is false at order 8.**
  - **Where.** §5.2, l. 518–520: "For stars, the data support the version 'pairs, 2-chains and
    stars, every star satisfying (H1)'. At order $\le8$ it has no failure". The abstract
    (l. 68–69) has the same reading.
  - **Counterexample** (`star_chain_pair_example.py`, full enumeration):
    - $F$ on $\{0,\dots,7\}$ with edges $05,06,07,15,25,37,46,67$. It is connected, with degrees
      $(3,1,1,1,1,3,3,3)$.
    - Units: the star $7\leftarrow\{1,2\}$, the 2-chain $5\leftarrow6\leftarrow3$ and the pair
      $4\leftarrow0$. All lie on non-edges and are vertex-disjoint.
    - (H1) at 7: $C=\{0,1,2,4,5,6\}$ with $2\le(6-2)/2$, and $C=\{3\}$.
    - Of the 60 Lovász decompositions, none satisfies all three units. Star + 2-chain: 4;
      star + pair: 8; 2-chain + pair: 9.
    - This is $H=(J-z)-\Phi$ at the real instance `H?bc~f{`, $z=8$, $r=0$. Six such structures
      occur at $n=9$, at `H?bc~f{` and `H?qu\v{`, and each was decided by enumerating every
      decomposition (60 or 108).
  - The order-$\le8$ `fl` runs tested star alone, star + pair, star + 2-chain and two stars, never
    three units. Those runs do have no failure satisfying (H1), as I confirmed.
  - CL itself (pairs and 2-chains only) is not affected.
  - **Fix.** Restrict the statement to the tested two-unit families. Record this example as a
    limit, as for Example 5.6: (H1) is not sufficient for stars once a pair and a 2-chain are
    present. Adjust the abstract.

### Draft findings (status at 057b5f5)

- **F1 (GAP) — fixed.** Verification-scope overclaims in the abstract, the summary table and
  `\VERIFYSTATUS` (97.5% of the order-11 tier-1 bases are unchecked; the tier-3/4 negatives were
  not independently confirmed). The a9a289d wording is accurate, and the tier-3/4 negatives are now
  confirmed by this audit: every $n\le9$ root, the 75 order-11 roots of tier 4–5, and the order-11
  sample.
- **F2 (GAP) — fixed.** The old Observation 2.1(a), sentence 2 ("the first rooted linkage tried by
  `xcheck_tiers.py` is already a base") was not produced by that script, which skips level-1 roots.
  It is replaced by the structural statement, which I confirmed: 0 / 179,152 cherry failures, and
  the 88 linkage failures all at tier-1 roots.
- **F3 (GAP, provenance) — (a) fixed, (b) open.**
  - (a) The solver cross-check now has `data/solver_xcheck.txt` and quotes the counts it contains.
  - (b) The order-10 entry "one 2-chain: 5,937,582 sets, 0 failures" (l. 454) still has no data
    file (`fl_10_k.txt`). I recounted the sets; the "0 failures" is unverified. **Fix:** commit the
    run or mark the entry pending.
- **F4 (NIT) — fixed in wording** (the tier-3 and tier-4 populations are now named), but the
  tier-3 numbers are wrong (F17).
- **F5 (NIT) — fixed.** $d_J(r)\ge3$ for the (T2) lift and for Prop 5.2.
- **F6 (NIT) — fixed.** "a graph with one edge fewer" (M2 removes three edges of $J$).
- **F7 (NIT) — fixed.** "cost exactly one path" is now "at most".
- **F8 (NIT) — fixed.** EC Prop 5.5 uses the insertion only when $ab\in E$.
- **F9 (NIT) — fixed.** "Stars never help at tier 3" now has the correct reason.
- **F10 (NIT) — fixed.** The 642 twin roots are covered only modulo the rooted floor; 507 of them
  also have cherry data.
- **F11 (NIT) — fixed.** $t=8$ also has no all-odd base (8 roots at order 11).
- **F12 (NIT) — fixed.** Route notation and the triviality of Example 5.4.
- **F13 (NIT) — partly fixed.** The §7 recipe now includes order 5. The README "Reproduce" block
  (l. 66) still omits it, which gives 5,259 / 25,336 graphs / roots instead of 5,260 / 25,340.
  **Fix:** the same one-line change in the README.
- **F14 (NIT) — fixed.** §1 now says what `Test1At` / `Test2At` are and where Lean is more general.
- **F15 (NIT) — fixed.** Three script issues:
  - `fl.c` now reports (H1) over all units; the earlier `ss` summary counted the first star only,
    and with both stars every failure violates (H1).
  - `rm.c` now counts queue overflows. Its cap and its 64-bit hash could only undercount, and my
    exact closure gives identical totals.
  - The §2.1 description of `ndsolve.h` is updated.
- **F16 — superseded by F17.**

---

## 3. Independent re-derivations (details)

- **The solver.**
  - It searches paths from the unended vertex of least remaining degree and never enters
    `avoid[s]`.
  - A path is closed at $w$ only if `avoid[w]` misses the path and $\{s,w\}$ is not a sibling
    pair.
  - Failures are memoised under the remaining edge set and the ended set.
  - It prunes on: an unended vertex with no remaining edge; a component with edges but no unended
    vertex; and, under `A41_PRUNE`, $d(v)\le2P-[v\text{ unended}]$ and an even number of unended
    vertices per component. Both bounds hold because every remaining path meets $v$ at most once.
  - The pruned and plain versions agree on all 901,618 universality structures that both decided.
  - Every solution is re-verified before it is counted: paths, edge partition, one end per odd
    vertex, constraints.
- **Forest $T$-joins.** I enumerate them as $J_0\oplus$(fundamental cycles), keeping the acyclic
  ones and checking the parity of each. This differs from `nd.c`'s edge recursion.
- **Rootings.**
  - Tier 3: $r$'s component is rooted at $r$, the other components at any vertex.
  - Tier 4: $r$'s component is rooted at any vertex other than $r$, and $d_\Phi(r)\ge3$ is
    required.
- **Linkages.** For the smallest unlinked $a\in T$, I search through unused non-$T$ vertices to
  an unlinked $b\in T$, with the length bound 2 for tier 1.
- **Root moves.**
  - M1 and M2 are applied exactly as in Theorem 4.2, with breadth-first search to depth 6 over an
    exact visited set (adjacency array plus root).
  - At most 7,897 states were visited at any order-11 root of tier $\ge2$.
  - No single M2 reaches data, as the paper's logic predicts.
- **Timings** on 4 cores shared with the author's order-10 runs:
  - (T1) $n\le9$ tiers: 0.9 s;
  - order-11 census and closure: 3 min;
  - universality at $n\le9$ with pruning: 1 min 49 s;
  - order-11 sample: about 40 min.

## 4. Summary table

| Item | Grade |
|---|---|
| Lean build, `sorry`, axioms (15 theorems) | SOUND |
| Lean faithfulness: `Test1At`/`Test2At`, twin insertion, theta / fat theta, twin reductions, `CherryList`/`CherryLN`, CL ⇒ (T1), CL ⇒ $L_N$, $L_N$ ⇒ (T1) at matching data, root moves, far-apart 2-chain | SOUND |
| Lemma 3.1, Thm 3.2, Thm 3.3 and the explicit construction | SOUND |
| Spine-induction paragraph | SOUND |
| Lemma 4.1, Thm 4.2 (zero ends, parities, $N(z)$), Cor 4.3, MR Thm 145 attribution | SOUND |
| Prop 5.2 | SOUND (the (T2) hypothesis is fixed) |
| Lemma 5.5; Examples 5.3, 5.4, 5.6 (brute force) | SOUND |
| (T1) $n\le9$ tiers, deficiencies, twins, excess | SOUND (root by root) |
| Order-11 census, tiers 4–5, systematic sample | SOUND |
| Root moves $n\le9$ and order 11 | SOUND (exact) |
| Universality tiers 1, 2, 4 | SOUND |
| Universality tier 3 and the (H1) statistics at real instances | **ERROR (F17)** |
| §5.2 star version of CL | **ERROR (F18)** |
| §5.1 table at orders $\le8$; order-6 `xcheck_fl` | SOUND |
| Order-10 table cells | counts SOUND; 2-chain failures GAP (F3(b)) |
| Verification scope and provenance (F1–F3(a)) | fixed |
| Wording F4–F15 | fixed, except the README part of F13 |

## 5. Required fixes

1. **F17.**
   - Fix `nd.c` (guard l. 290 with `!univ`), and re-run `-U`, `-UU` and `star_hall.py`.
   - Replace "32,706 of 88,148" by "278,296 of 1,239,486", and update the data files.
   - Rewrite the §5.2 (H1) sentence: 59,953 of 60,920 excess-1 failures, and 295 of the rest
     contain no claw. Alternatively, restrict it to tier-$\ge3$ roots.
2. **F18.** Withdraw "pairs, 2-chains and stars, every star satisfying (H1) ... no failure at order
   $\le8$". Add the order-8 counterexample as a limit, and adjust the abstract (l. 68–69).
3. **F3(b).** Commit the order-10 one-2-chain run, or mark the cell pending.
4. **F13.** Add order 5 to the README recipe.
