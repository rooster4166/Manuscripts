# GallaiLean

## Conjecture 31: profile form (cloud session, branch `claude/conj31`)

Manuscript `manuscripts/conj31`. Two files, no `sorry`. Every theorem below depends only on `propext`, `Classical.choice` and `Quot.sound` (`manuscripts/conj31/data/axioms.txt`). The full library builds (18,450 jobs). Conjecture 31 and PC are **not** proved.

| File | Content |
|---|---|
| `Conj31.lean` | **Profiles and the degree bound.** `RealisesProfile G b` (some decomposition has exactly `b v` ends at every `v`). `tight_iff_realisesProfile`. **`degree_add_le_sum_of_realises`**: (DB) `d(x) + b(x) ≤ ∑ b` is necessary. `sum_profile_mod_two`. **`universal_of_not_degreeBound`** (manuscript lemma "where (DB) fails", forward direction without the clause `b = 1` elsewhere): with `b ≡ d (mod 2)` and `b ≥ 1` off a set `Z`, `\|Z\| ≤ 2`, (DB) fails at `x` only if `\|Z\| = 2`, `Z ⊆ N(x)` and `x` is adjacent to every other vertex. **Reduction moves, realisation step:** **`realisesProfile_transfer`** (TR, Fan's lemma), **`realisesProfile_newPath`** (NEW), **`realisesProfile_suppress`** (SUP, via `splitOff_supp`), **`realisesProfile_tri`** (TRI: delete `xy`, suppress `u` with `N(u) = {x, y}`, Fan at `y`). **Conjectures as propositions:** `ProfileConj V` (Conjecture PC) and `Conj31On V` (Conjecture 31), both using the project's `TwoConnected`. **`conj31_of_profileConj`**: PC ⇒ Conjecture 31. Helper `degree_of_adj_all`. |
| `Conj31Up.lean` | **Upward closure.** `PathDecomp.exists_interior` (fewer ends than edges ⇒ an interior vertex of some path), `PathDecomp.split_at_interior` (split there: two more ends), **`realisesProfile_up`**, `realisesProfile_of_le` (raise a realisable `m ≤ b`, `m ≡ b`, `b ≤ d`). **PC with ≤ 1 zero**: **`realisesProfile_of_no_zero`** and **`realisesProfile_of_one_zero`**: every profile `b ≡ d (mod 2)`, `b ≤ d`, `b ≥ 1` except at most at one even vertex, is realisable in any graph without isolated vertices (one zero: even order, via `realisable_evenSet_erase'`). |

## Multi-token steering (cloud session, branch `claude/multi-token`)

Manuscript `manuscripts/multi-token`. Two files, no `sorry`; every theorem below depends only on `propext`, `Classical.choice` and `Quot.sound` (`manuscripts/multi-token/data/axioms.txt`). The full library builds (18,428 jobs).

| File | Content |
|---|---|
| `MultiToken.lean` | Tails `(c, w, x)` (a leaf `c` at `w`, a vertex `x` its path avoids; live while `cw ∈ K`): `OffTails`, `OneLive`, `SuppOK`, `TailSys` (static), `TailInv` (dynamic), `TailGood` (a parity decomposition meeting every live `{c, x}` at most once). **`SteerK`** (inductive; tokens = the even set): `move` (a token to an odd `u ∉ {c, x}` of live tails, not adjacent to another token after the deletion), `drop` (delete the leaf edge of a live tail with odd stem), `supp` (suppress a degree-2 token with non-adjacent neighbours), `fin` (≤ 1 token and ≤ 1 live tail). **`fan_step_multi`** (Fan's step with many even vertices, no blank), `evenSet_move`, `evenSet_drop`, `evenSet_supp`, `tailInv_*`, `live_*`, `tailGood_move`, **`tailGood_drop`**, **`splitOff_supp`** (cover form of `avoid_of_splitOff`), `tailGood_supp`, **`tailGood_fin`** (the multi-tail leaf lemma, from `avoid_leafTail` and `lovasz_ends`), **`steerK_good`** (the transfer theorem). Triangle base: `leafSet`, `triTails`, `triLeaf` (`leaves M Y` on `V ⊕ V`), `triTails_sys`, `triTails_inv`, **`triangleBase_of_steerK`** (a schedule in `M⁺` gives a triangle base), **`test1At_of_steerK`**. |
| `MultiTokenObstruct.lean` | The obstruction (manuscript Props 6.1, 7.2). `nonNbr` (non-neighbours of `r` that can host a removal), `liveSet`, `rLive` (live tails avoiding `r`), `ObstrInv` (`r` odd, leaves only at their stems, `|A| + 2 ≤ #tokens + ρ`, `|A| + 3 ≤ #tokens + #live`), `obstr_no_entry`, `obstr_move`, `obstr_drop`, `obstr_supp`, **`not_steerK`** (no schedule under the invariant), **`not_steerK_triangle`** (triangle data: a root with fewer than `k` non-neighbours in `J − r` has no `k`-token schedule for any orientation; at `d(z) = 6`, every root of degree `|J| − 2`). |

## Neighbour avoidance NA: proved (cloud session, branch `claude/na`)

Manuscript `manuscripts/na`. One file, no `sorry`; every theorem below depends only on `propext`, `Classical.choice` and `Quot.sound`. The full library builds (18,420 jobs).

| File | Content |
|---|---|
| `NeighbourAvoid.lean` | **`neighbourAvoid`**, **`neighbourAvoidOn : NeighbourAvoidOn V`** (conj-n Conjecture 4.2, now a theorem). **`avoid_packed_of_reach`** (set form, extending `lovasz_avoid_set`): `Y` packed, `y ∉ Y` odd, a vertex `w` of positive degree with no neighbour in `Y` joined to `y` by a walk avoiding `Y` ⇒ a Lovász decomposition meeting `Y` at most once per path with `Q(y) ∩ Y = ∅`; `avoid_of_reach` (single vertex). **`avoid_iff_reach`** (the exact boundary: `Q(y)` can avoid `x` iff the component of `y` in `G − x` is not inside `N(x)`), with the converse **`mem_pathEndingAt_of_component_sub`** (count ends in the component against edges from `x`). Consequences: **`conjNDegTwoOn`** (degree-two case of N, unconditional), **`conjN_of_tightTransferN`** (TRN ⇒ N), **`conjN_of_TR`** (TR ∧ `TightTransferAdj` ⇒ N). Machinery: `Steer` (steered Case-I chain, inductive), `fan_step_meetsOnce` (one Fan step keeping `MeetsOnce X` for a target `∉ X`; the body of `sep_case_even`), `steer_meetsOnce` (the chain, for any edge-deletion-stable base property), `steer_of_inv` (walking along a subgraph `S` with odd vertices in a set `A` of free vertices), `exists_toggle_walk`, `even_card_odd_reachable`, `exists_inv_subgraph` (farthest odd vertex `t`, toggled shortest paths), `offX`/`offX_degree` (`K` minus the edges at `X`), `apexSep_meetsOnce` (deleting the leaf of `apex G {c}` keeping a packed set), `list_sum_lt_sum`, `list_sum_finset_sum`. |
## The tight transfer TRN: the core that Conjecture N needs, and two-token steering (cloud session, branch `claude/trn`)

Manuscript `manuscripts/trn`. Two files, no `sorry`; every theorem below depends only on `propext`, `Classical.choice` and `Quot.sound` (`manuscripts/trn/data/axioms.txt`). The full library builds (18,424 jobs). TRN itself is **not** proved: N is reduced to TRN on the core instances that have no two-token schedule (`conjN_of_core2`).

| `TRN.lean` | **`avoid_of_separating_child`** (manuscript Lemma 4.1): if `G − gu` (`g` the even vertex, `u ∉ {x, y}`) has a Lovász decomposition in which no path contains both `y` and `x`, then `AvoidDecomp G y {x}` (Fan's lemma with vertex sets, `fan_single_supp`). Outright cases of the conclusion of TRN, with no hypothesis on `G − gu`: **`avoid_of_farApart`** (`x, y` at distance `≥ 3`, by `separation`) and **`avoid_of_degTwo_indep`** (`N(g) = {a, b}`, `a ≁ b`, `{x, y} ≠ {a, b}`; split off and `L₁`). `ConjNBelow V n` (Conjecture N below degree sum `n`) and **`TightTransferNCore`** (manuscript Definition 5.1: TRN with N available on smaller graphs, all-tight, the child keeping a witness, `x, y` with a common neighbour, `N(g)` not an independent pair). **`conjN_of_core`** (manuscript Theorem 5.2): the core of TRN and the degree-two case imply N; **`conjN_of_core_neighbourAvoid`** (with NA); **`tightTransferNCore_of`** (TRN ⇒ core), so this strengthens `conjN_of_tight_degTwo`. |
| File | Content |
|---|---|
| `TRN.lean` | **`avoid_of_separating_child`** (manuscript Lemma 4.1): if `G − gu` (`g` the even vertex, `u ∉ {x, y}`) has a Lovász decomposition in which no path contains both `y` and `x`, then `AvoidDecomp G y {x}` (Fan's lemma with vertex sets, `fan_single_supp`). Outright cases of the conclusion of TRN, with no hypothesis on `G − gu`: **`avoid_of_farApart`** (`x, y` at distance `≥ 3`, by `separation`) and **`avoid_of_degTwo_indep`** (`N(g) = {a, b}`, `a ≁ b`, `{x, y} ≠ {a, b}`; split off and `L₁`). `ConjNBelow V n` (Conjecture N below degree sum `n`) and **`TightTransferNCore`** (manuscript Definition 5.1: TRN where `(G, y, x)` is an instance of N, N is available on smaller graphs, all-tight, the child keeps a witness, `x, y` have a common neighbour, `N(g)` is not an independent pair). **`conjN_of_core`** (manuscript Theorem 5.2): the core of TRN and the degree-two case imply N; **`conjN_of_core_neighbourAvoid`** (with NA); **`tightTransferNCore_of`** (TRN ⇒ core), so this strengthens `conjN_of_tight_degTwo`. |
| `TRNSteer.lean` | Two-token steering (manuscript §6). **`avoid_leafTail`** (Lemma 6.1): a leaf `c` at `w`, `x ∉ {c, w}` odd, `x ≁ w` ⇒ `AvoidDecomp G c {x}`; `w` may be the even vertex (induction of N with no tight target). **`fan_step_two`** (Lemma 6.2): Fan's step when the even vertices lie in `{z, o}` and the target `u ∉ X ∪ {o}` is not adjacent to `o` after the deletion; keeps `MeetsOnce X`. **`Steer2`** (Definition 6.3, inductive: two tokens, a move goes to `u ∉ X`, not the other token, not adjacent to it after the deletion; ends when a token reaches an isolated vertex). **`steer2_meetsOnce`** (Lemma 6.4). **`avoid_of_steer2`** (Theorem 6.5): a schedule in `apex G {y}` from `(some g, some y)` avoiding `leafX x = {none, some x}` ⇒ `AvoidDecomp G y {x}`, with no hypothesis on `G − gu`. **`TightTransferNCore2`** (Definition 6.8: the core plus `¬ Steer2 …`), **`tightTransferNCore_of_core2`**, **`tightTransferNCore2_of`**, **`conjN_of_core2`** (Theorem 6.9): `TightTransferNCore2 V → ConjNOn V`, using `conjNDegTwoOn` (NA). |

## Conjecture N: reduction to the tight transfer and neighbour avoidance (cloud session, branch `claude/conj-n`)

Manuscript `manuscripts/conj-n`. Two files, no `sorry`; every theorem below depends only on `propext`, `Classical.choice` and `Quot.sound`. The full library builds.

| File | Content |
|---|---|
| `ConjN.lean` | `ConjNOn V` (Conjecture N of dl-one: `x, y` odd, non-adjacent, `y` has a neighbour that is not even and not adjacent to `x`; then `AvoidDecomp G y {x}`), `TightTransferNOn` (TR of l1-induction for `A = {x}`, tail allowed adjacent to `g`), `ConjNDegTwoOn` (N with `N(g) = {x, y}`), `NeighbourAvoidOn` (NA: no even vertex, `x ~ y`, `y` has a neighbour `w ≠ x` not adjacent to `x`), `TightTransferAdj` (`TightTransfer` with `G.Adj g c`). **`conjN_of_tight_degTwo`** (manuscript Thm 4.6): TRN and the degree-two case imply N, by induction on the degree sum (`conjN_strong`): no even vertex → L₁ (`lovasz_avoid_nonadj`); a non-tight target → the child is an N-instance (the witness survives) and `avoid_free_target`; a tight target whose child keeps a witness → TRN; otherwise parity of `d(g)` leaves `N(g) = {x, w₀}` (split off, L₁) or `N(g) = {x, y}`. **`conjNDegTwo_of_neighbourAvoid`** (NA implies the degree-two case; manuscript Lemma 4.4, first sentence), **`conjN_of_tight_neighbourAvoid`**, **`tightTransferNOn_of`**, **`conjN_of_TR_neighbourAvoid`** (TR ∧ TR-adjacent ∧ NA ⇒ N). **`avoid_of_splitOff`** (move (e): `N(g) = {a, b}`, `ab ∉ E`, subdivide `ab` by `g`). Helpers `evenSet_delEdge_sub`, `evenSet_delEdge_card`, `avoidDecomp_singleton_iff`, `delEdge_adj_of_ne`. |
| `ConjNFar.lean` | **`fan_single_protected_path`** (manuscript Lemma 3.2: Fan's lemma keeping a path `P` of the old decomposition, when no end of `P` lies in `{t, u} ∪ N_{G'}(u)`), via **`PathDecomp.erase_path`** (remove a path: a decomposition of `delEdgeList K P.edges`) and **`PathDecomp.add_path`** (add it back); `exists_decomp_of_edgesM_both`. `AvoidFarDecomp G c A B` (the path ending at `c` avoids `A`, its far end is outside `B`) and **`avoidFar_target`** (Theorem 3.3, move (x): Case I across a target `u ∈ N(g) ∖ N[c]` that may lie in `A`, with child far-end set `B ∪ N_G(u)`). |

## Cones: Test1 at the apex is rooted Gallai for Eulerian graphs (cloud session, branch `claude/eulerian-cone`)

Manuscript `manuscripts/eulerian-cone`. Two files, no `sorry`; every theorem below depends only on `propext`, `Classical.choice` and `Quot.sound`. The full library builds (18,406 jobs).

| File | Content |
|---|---|
| `EulerianCone.lean` | `fullCone B` (the apex `none` joined to every vertex; equal to `cone B univ` of `Marked.lean`), `fullCone_degree_none/some`, **`fullCone_onlyEven_iff`** (the apex is the only even vertex iff `|B|` is even and `B` Eulerian), **`fullConeDelIso`** (`B ≃g cone − z`), `PathDecomp.exists_of_iso`. `RootedDecomp B r` (at most `|B|/2` paths, at least two ends at `r`). **`test1At_fullCone_iff`**, **`test1_fullCone_iff`**: Test1 at the apex ⇔ `RootedDecomp B r` for every `r` when `B` is Eulerian of even order. **`kConnected_three_fullCone_iff`** (cone 3-connected ⇔ `B` 2-connected), `HasMatchingCut.of_iso`, **`hasMatchingCut_delVert_fullCone_iff`**. Vacuous tests: `test2_fullCone_apex`, `test1_fullCone_some`, `test2_fullCone_some_of_even` (via `not_unique_odd`). **`rootedDecomp_of_spineTestsNMC`** (the cone instances of `SpineTestsNMC` are RE for 2-connected Eulerian graphs of even order without a matching cut), **`fullConeTests_iff`**, **`rootedDecomp_of_gallai`** (Gallai ⇒ RE for connected Eulerian graphs of even order), **`rootedDecomp_iff_addLeaf`** (RE ⇔ `p(B + leaf at r) ≤ |B|/2`), **`rootedDecomp_of_dbl`** (Gallai's bound for the double gives RE). |
| `CycleInsert.lean` | **`PathDecomp.cycle_insert`** (manuscript Lemma 5.2, both cases): a cycle `a c₁ ⋯ c_l a`, given as a path `R : a → c` plus the edge `ca`, edge-disjoint from `K`, with `c` and all `cᵢ` but one designated vertex without `K`-edges, is inserted into any decomposition of `K` at the cost of one path, with unchanged ends except `+2` at `c`. **`PathDecomp.ear_insert`** (the triangle ear, Prop. 5.3). Tools: `PathDecomp.replaceList` (replace a path by a list of paths in a larger graph), `GPath.exists_split_avoid` (split at `a` with the piece ending at `a` avoiding `b`), `GPath.liftTo`, `GPath.adj_of_mem_support`. |

## Direct lift to Test1 through triangles at z (cloud session, branch `claude/triangle-base`)

Manuscript `manuscripts/direct-test1`. Three files, no `sorry`; every theorem below depends only on `propext`, `Classical.choice` and `Quot.sound`. The full library builds (18,404 jobs).

| File | Content |
|---|---|
| `DirectTest1.lean` | **`test1At_of_triangleBase`** (manuscript Thm 2.1, general `m`): if `z` is the only even vertex of `J`, `d(r) ≥ 3`, `(w, L)` are triangle data at `(J, z, r)` (`TriangleData`: `L` a list of pairs that are edges of `J` and partition `N(z) − {r, w}`), and the auxiliary graph `triM J z w L = J − zw − {zaᵢ, zbᵢ, aᵢbᵢ}` has a Lovász decomposition satisfying every disjunction `aᵢ ∉ V(Q₀(bᵢ)) ∨ bᵢ ∉ V(Q₀(aᵢ))` (`TriangleDisj`), then `Test1At J z r`. **`append_pairs`**: appending a matching at ends chosen by the disjunctions keeps the size (induction with `append_full`; `avoid_of_append` carries the remaining disjunctions). The leaf `z` is removed by identifying `J − zw − {zaᵢ, zbᵢ}` with `addLeaf (J − z) r` (`leafMap`, `PathDecomp.mapInj`) and `trim_ends` + `exists_two_ends`. **`triM_parity`**, `triM_size` (manuscript Lemma 1.2). **`test1_of_triangleBases`**; `TriangleBaseConj` (Conj 3.1, restricted to roots with data) and **`test1_of_triangleBaseConj`**. |
| `TriangleBase.lean` | The cases of the triangle base conjecture reached by the single-vertex tools. **`triangleBase_of_packed`** (any `m`): if the pair vertices are pairwise at distance `≥ 3` in `M`, `separation_set` gives a base. **`triangleBase_of_farApart`** (one pair, `d(z) = 4`): `a, b` with no common neighbour in `M`, by `separation`. **`triangleBase_of_L1Star`** / **`triangleBase_of_L1Blocked`** (one pair): if `a ≁ w` or `b ≁ w`, the avoidance conjecture `L1Star` (hence its blocked case `L1Blocked`) gives a base. `TriangleData.triM_evenSet`; `test1At_of_packed`, `test1At_of_farApart`, `test1At_of_L1Star`. **`DisjL1`** (Conjecture DL, disjunctive avoidance: disjoint non-adjacent odd pairs, none universal twins of its component) with `UnivTwins`, `TriangleData.not_univTwins`, `triangleBase_of_disjL1`, **`test1At_of_disjL1`** (DL ⇒ Test1 at every root whose `M` is connected). **`triangleBase_of_E5_E7`**, `triangleBase_of_lovaszBase_E7` (audit A28): at m = 3 the base graph of t6-dense is `triM`, and (E5), (E7) are disjuncts of the triangle condition, so every (E7)-branch base of t6-dense Conj 5.1 is a triangle base. |
| `ForestLift.lean` | **`test1At_of_forestBase`** (manuscript Thm 4.2, the forest lift), `test1_of_forestBases`. `ForestData`: `w`, `T = N(z) − {r, w}` and a list `L` of (child, parent) pairs of edges of `J − {z, r}`, with distinct children and edges, `w` never a child, parent-first order (`L.Pairwise (·.2 ≠ ·.1)`), and the `T`-join parity of `Φ`. `forM` = J − zw − zT − Φ. `ForestBase` asks for a Lovász decomposition of `forM` with (i) every path ending at a child avoiding its parent and (ii) no path with two siblings as ends. **`append_forest`**: the appends in parent-first order keep the size (manuscript Lemma 4.1, one direction); acyclicity is not needed. `test1At_of_leafDecomp`: the deletion step for any leaf graph. `delList_degree_count`. |

## Prescribed end edges (cloud session, branch `claude/ee`)

Manuscript `manuscripts/prescribed-end`. Two files, no `sorry`; every theorem below depends only on `propext`, `Classical.choice` and `Quot.sound`. The full library builds.

| File | Content |
|---|---|
| `PrescribedEnd.lean` | **`sep_atMostOneCommon`**, **`ee_atMostOneCommon`**: if `z` is the only vertex of positive even degree and `u ∈ N(z)` has at most one common neighbour with `z`, then `G − uz` has a Lovász decomposition separating `u` and `z`, and `uz` is the terminal edge at `u` of some Lovász decomposition of `G` (separation in `G − uz − uw`, Fan with target `w`, append). **`ee_deg_two`**: EE whenever `d(z) = 2`. Leaf-graph infrastructure: **`PathDecomp.append_move_exact`**, **`PathDecomp.liftLeaf`** (lift to `apex K {r}`, extending one path by the leaf edge, with exact supports), **`endEdge_of_leafSep`** (a decomposition of `apex (G − xy) {y}` separating `x` from the leaf gives `xy` terminal at `x`). **`pee_adjEven`**: if `y ∈ N(z)`, `x ≠ z` and `x, y` have at most one common neighbour besides `z`, then `xy` is terminal at `x` (EE at `y` in `G − zy`, then Fan with target `y` in the leaf graph). **`ee_of_triangle`**: for a common neighbour `w`, EE at `u` follows from a Lovász decomposition of `G − {uz, uw, wz}` whose path ending at `w` avoids `u` and `z`. |
| `PrescribedEndOutside.lean` | **`ee_of_outside`**: for `w ∈ N(u)` not adjacent to `z`, EE at `u` follows from a Lovász decomposition of `G − uz − uw` whose path ending at `z` avoids `u` (leaf graph at `z`, Fan with target `w`). **`L1Star`** (the avoidance conjecture: odd `c`, `|A| ≤ 2`, `A` disjoint from `N[c]` and from the neighbours of the even vertex) and **`ee_of_L1Star`**: `L1Star → EE`. |

## Multi-pair separation (cloud session, branch `claude/multi-sep`)

Manuscript `manuscripts/multi-sep`. One file, no `sorry`; every theorem below depends only on `propext`, `Classical.choice` and `Quot.sound`. The full library builds.

| File | Content |
|---|---|
| `MultiSep.lean` | `PathDecomp.pushOn` (push a decomposition along a map injective on each path and on edges). **`leaf_merge`**: a decomposition of `(G − ux) + leaf at u` with no path through both `x` and the leaf becomes one of `G` (leaf ↦ `x`), ends at `x` adding up. **`lovasz_endEdge_set`**, **`lovasz_endEdge`**: if all degrees are odd, every edge `xu` is the terminal edge at `x` of some Lovász decomposition, which can also meet a given packed set `∋ x` at most once per path. `ClassFam`, `ClassSep`, **`caseII_lift`**, **`classSep_allOdd`**: class separation for graphs with one positive even vertex implies it for all-odd graphs (the leaf joins the class of `x`). **`classSep_caseI`**: the certified Case I step (`z` joins the classes of `u`, then append `zu`). `SparseFam`, **`separation_sparse`**: overlapping packed classes whose union has at most one neighbour at every vertex can all be separated (generalises `separation_set`). **`realisable_of_separating`**, **`realisable_of_lovasz_separating`**: if the even vertices of `G` are paired by edges and `G` minus the pairing edges has a Lovász decomposition separating every pair, every transversal is realisable (via `append_routes`). |
| `MultiSepEE.lean` | Conjecture EE without classes at degree three (multi-sep Proposition "EE3"). **`ee_of_avoid`**: if `z` is the only positive even vertex, `u ∈ N(z)`, and `G − uz` has a Lovász decomposition whose paths ending at `z` avoid `u`, then appending `zu` makes `uz` the terminal edge at `u`. **`ee_noTriangle`** (`uz` in no triangle), **`ee_split`** (`N(u) = {z, a, b}`, `ab, zb ∉ E`: suppress `u`, apply `L₁`, put `u` back with `exists_subst_path`), **`ee_triangle`** (`ab ∈ E`, `u` the only common neighbour of `a, b`: separate `a` from `b` in `G − uz − ua − ub − ab` and extend two paths). **`separation_sparse_set`**: if every vertex has at most one neighbour in `X`, some Lovász decomposition has any two vertices of `X` on a common path adjacent. |

## Route descent and separation (cloud session, branch `claude/route-descent`)

Manuscript `manuscripts/route-descent`. Three files, no `sorry`; every main theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. The full library builds.

| File | Content |
|---|---|
| `RouteDescent.lean` | **`gallai_of_pairingTRC`**: abstract TRC ⇒ Gallai. If every connected even-order graph has a pairing of its even vertices (`IsEvenPairing`, a fixed-point-free involution of `evenSet`) all of whose transversals are realisable, Gallai holds. **`gallai_of_pairingTRCExists`**: it suffices to have, for each even `y`, one realisable transversal containing `y`. Via `gallai_of_rootedHalfSets` / `branchBase_of_rootedHalfSets`: a realisable `M ∋ y` with `2|M| ≤ |Ev|` gives `Desc H k y ∅` for every `k`, hence `BranchBase k` without its side hypotheses. `exists_transversal`, `two_mul_card_transversal`. `IsEvenPairing.of_isPairing`: the pairings of `cs_all` qualify, so `cs_all` supplies the cut-feasibility half of TRC. **`realisable_of_even_matching`**: TRC for one-edge routes when every even vertex has exactly one even neighbour (`G[Ev]` a perfect matching): every transversal is realisable (Fan descent via `realisable_transfer`). **`PathDecomp.route_append`**: the inductive step of route descent: if `D'` decomposes `G − E(R)` for a path `R` from `c` to `a`, and the path of `D'` ending at `c` meets `R` only in `c`, appending `R` gives a decomposition of `G` of the same size with one end moved from `c` to `a`, in which `R` is a terminal segment of a path. **`realisable_two_even_adj`** (`OnePair.lean`): if the only even vertices are `c ~ a`, then `{a}` is realisable with `ca` terminal at `a`: L₁ (`lovasz_avoid_nonadj`) on `G − ca` is the base and `route_append` is the step. T-joins: `IsTJoin`, `IsMinTJoin`; **`isMinTJoin_sdiff`** (deleting a subset of a minimum T-join leaves a minimum join of `G − R`: heredity of minimality under route deletion); `card_le_two_mul_of_isTJoin`, `isMinTJoin_of_two_mul_card_le` (a matching T-join is minimum). |
| `FanSupport.lean` | **Fan's lemma with vertex sets.** `fan_single_supp`, `fan_grouped_supp`, `fan_exec_supp`: as `fan_single` etc., plus *every path of the new decomposition lies in a path of the old one, together with the target vertex `u`*. Supporting copies `replace_supp`, `append_move_supp`, `reroute_core_supp`, `reroute_move_supp` (re-routing keeps vertex sets; the append adds `u`). The originals are untouched. |
| `RouteSystem.lean` | **`append_routes`** (manuscript Prop. "rr"): for pairwise edge-disjoint paths `L` of `G` with distinct tails and no head a tail, a decomposition `D` of `delPaths G L` that is `Compatible` (RR1: a path with an end at a tail meets that route only there; RR2: a path joining two tails has their routes vertex-disjoint) and has an end at every tail gives a decomposition of `G` whose ends are those of `D` minus the tails plus the heads. **`realisable_of_compatible`**: for a `RouteSystem` of an even pairing and a transversal `M`, such a `D` with at most one end everywhere makes `M` realisable. **`gallai_of_routeRR`** / **`gallai_of_routeRRExists`**: `RouteRR` (every connected even-order graph has a routed pairing whose transversals all admit compatible Lovász decompositions of the free graph), or its existential form, implies Gallai. Proof: routes appended one at a time by `PathDecomp.route_append_cls` (`route_append` with the list of new paths, via the strengthened `replace_supp`), compatibility passing to each intermediate decomposition; the final profile follows from the parity lemma. |
| `Separation.lean` | **`separation_set`**: if `(evenSet G).card ≤ 1` and `X` is `Packed` (pairwise distance ≥ 3), some decomposition with `ends v = deg v % 2` has every path meeting `X` at most once (`MeetsOnce`). **`separation`**: the case `X = {c, a}`: if `(evenSet G).card ≤ 1` and `FarApart G c a` (distinct, non-adjacent, no common neighbour), then `G` has a decomposition with `ends v = deg v % 2` in which no path contains both `c` and `a` (`Separates`). **`lovasz_avoid`**: the path ending at `c` avoids `a`. **`lovasz_avoid_set`** / **`lovasz_avoid_nonadj`** (conjecture L₁, now proved): if no vertex has positive even degree, `c` is odd and `a` is not adjacent to `c` (more generally, `Y` is packed and avoids `N[c]`), some Lovász decomposition has the path ending at `c` avoiding `a` (resp. `Y`). Proof: attach a leaf at `c` (apex on `{c}`); `c` becomes the only even vertex and the leaf is at distance ≥ 3 from `a`; apply `separation_set` and delete the leaf (`Retract.delete_supp`, which now also returns each new path as the kept part of an old one). Proof: Lovász's induction (cases I–IV of `Lovasz.lean`) with the invariant carried by `fan_single_supp`, `Retract.delete_supp` (leaf deletion with supports, from `project_full`'s pieces and `PathDecomp.eq_of_mem_edges`) and `PathDecomp.add_edge_supp`. Case III of Lovász's proof is replaced by deleting a leaf outside `{c, a}`. |

## Theorem 59 (cloud session, branch `claude/lean-thm59`)

**`thm59 : Thm59Statement`** is proved, so Theorem 114 now holds with no hypothesis:
**`gallai_iff_spineTests' : (Gallai ↔ SpineTests) ∧ (Gallai ↔ SpineTestsNMC)`** (`Separator.lean`).
`#print axioms` on both shows only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`.
The dependency tree is in `GallaiLean/THM59_PLAN.md`; the audit note is
`research/audit/A14-thm59-lean.md`.

| File | Content |
|---|---|
| `MarkedBlocks.lean` (edited) | `SmallerMB G U` ranges over restrictions of `G`; order-bounded tests `MarkedTwoConnTestUpTo`, `ThreeEndsTestUpTo`; `SmallOn`; **`mbOn_of_testsUpTo`** (block transfer inside graphs with blocks of order `≤ m`). `mbOn_of_tests` and all Theorem 1 statements are unchanged. |
| `Thm59Transfer.lean` | `TwoConnOn (restrict F U) U → KConnected 2 (F.induce U)`, `TwoConnected.kConnected`; **`markedBoundUpTo_of_tests`** |
| `Thm59Hall.lean` | **`markedNumber_add_card_le`**: if every mark has an end of `D` and marks outside `O` have two, `q(F,T) + \|T\| ≤ \|D\| + ⌊\|O\|/2⌋` (Hall's theorem with `⌊\|O\|/2⌋` dummy slots). Replaces both the private-leaf identity and the odd-mark rank inequality of §2.1. |
| `Thm59ClassC.lean` | step [C]: the cone over `≥ 2` marks of `B ∈ C` is in `C` (`apex_inClassC`); cone identity `\|S\| + 2q + b_D(z) ≤ 2\|D\|`; **`markedBound_of_classC`**, **`threeEnds_of_classC`** |
| `Thm59Lemma6.lean` | **`lemma6`**: Lemma 6 for a matching cut, by PMP surgery (one replacement per crossing edge) |
| `Thm59Leaves.lean` | `leafGraph B A` on `V ⊕ V` (private leaves at `A`); **`leafGraph_trim`**: `\|D'\| + #{a ∈ A : b_{D'}(a) = 0} ≤ \|D\|` |
| `Thm59MatchingCut.lean` | matching cuts with connected shores; shores with leaves are connected with blocks `≤ n − 1`; **`matchingCut_markedBound`** (Theorem 7, matching-cut case: connected `B` with a matching cut and `MarkedBoundUpTo (n−1)` ⇒ `q(B,S) ≤ ⌊(n−\|S\|)/2⌋` for all `S`, including `S = ∅`) |
| `Thm59.lean` | **`thm59`**: strong induction on the block order |

## Spine 113/114 (cloud session)

Branch `claude/lean-spine-113-114`. Marked-reduction Theorems 113 and 114 (ROADMAP node N4).
Every file below is sorry-free. `#print axioms` on `separatorStatement`, `gallai_iff_spineTests`,
`spineTests_of_gallai` and `rootedAt_evenComp_evenPorts` shows only `propext`,
`Classical.choice` and `Quot.sound`.

**Bottom line.**

* **Theorem 113 (separator theorem) is proved outright:** `separatorStatement : SeparatorStatement`.
  It uses Lovász's theorem as proved in `GallaiLean/Lovasz.lean` (`lovaszStatement`).
* **Theorem 114 is proved modulo Theorem 59 alone** (and Theorem 59 is now proved, see the
  section above, giving `gallai_iff_spineTests'`):
  `gallai_iff_spineTests (h59 : Thm59Statement) : (Gallai ↔ SpineTests) ∧ (Gallai ↔ SpineTestsNMC)`.
  * The forward direction, `spineTests_of_gallai`, uses no hypothesis.
  * The converse needs the single explicit hypothesis `Thm59Statement`.
* All four priorities are done: (a) Gallai ⇒ both tests, (b) the apex construction is
  3-connected, (c) the separator theorem, (d) the converse.

**The remaining hypothesis.** `Thm59Statement` is Theorem 59 in the finite-order form recommended
by audit A2 (finding F1). It says: if both rooted assertions (`RootedAt`) hold for every member of
`C` (two-connected, no matching cut) with at most `m + 1` vertices, then the marked bound (1) holds
on every connected graph whose two-connected blocks have order at most `m` (`MarkedBoundUpTo m`).

* `MarkedBlocks.lean` (base branch) proves Theorem 1 (`gallai_iff_tests`): the 2-connected marked
  bound plus the three-end test.
* What Theorem 59 still needs on top of that is
  * the matching-cut reduction (Thms 7, 57), and
  * the step from the rooted tests to the marked tests.

**Statements and faithfulness.**

* **k-connectivity.** `KConnected k G` means `k + 1 ≤ |V|` and `G.induce Xᶜ` is connected for
  every `|X| < k`. `J − z` is `delVert J z`, the graph induced on `{v | v ≠ z}`.
* **`Test1 J z`.** If `z` is the only even vertex, then for each `r ∈ N(z)` some decomposition of
  `J − z` has `≤ (|J| − 1)/2` paths and `D.ends r ≥ 2`. A path has at most one end at `r`, so this
  is "at least two paths ending at `r`".
* **`Test2 J z`.** If `z, r` are the only even vertices and are adjacent, then some decomposition
  has `≤ |J|/2` paths and `D.ends r ≥ 3`.
* **`SpineTests` / `SpineTestsNMC`.** Both tests for every 3-connected `J`. The `NMC` version adds
  the hypothesis that `J − z` has no matching cut (`HasMatchingCut`).
* **Theorem 113 in the A2 audit's F7 form (`SeparatorStatement`).** This is stronger than the
  manuscript's statement.
  * The hypotheses are: `B` two-connected, and the marked bound on graphs whose blocks have order
    `≤ n − 2`. At a least-order failure, Theorem 59 provides the latter.
  * Neither minimality nor the absence of a matching cut is assumed.
  * The conclusion: if `C` is a component of `B − {x, y}` (`IsSepComponent`, with `{x, y}`
    separating), `r ∉ C`, and every vertex of `C` is odd, then `RootedAt B r`.
* **Blocks.** `SmallBlocks F m` means every two-connected induced subgraph has at most `m`
  vertices, i.e. the two-connected blocks have order `≤ m`.

**Files.**

| File | Content |
|---|---|
| `ThreeConnected.lean` | definitions above; **`spineTests_of_gallai`**; `PathDecomp.trim_ends`, `exists_two_ends`, `exists_three_ends`; **`apex_kConnected_three`** (`B` 2-connected, `\|S\| ≥ 3`, every component of `B − {x,y}` meets `S` ⇒ `B + z(S)` 3-connected); statements `Thm59Statement`, `SeparatorStatement`; `rootedAt_of_few_even`; **`gallai_of_spineTestsNMC`** (Lovász + Thm 59 + Thm 113 + tests ⇒ Gallai, by strong induction on the order of a failure in `C`) |
| `PathSurgery.lean` | paths of the complete graph (`TPath`), edge multisets `edgesM`, `endsL`, `exists_decomp_of_edgesM`, `plusEdge`, `joinT`, `exists_subst_list` (substitute a path for an edge), `exists_graft` (cut at a vertex, attach two paths), `exists_cut_edge` |
| `SmallBounds.lean` | `lovasz_on` / `lovasz_tight` on a vertex set; a single mark is a private leaf; `R2_on`, `R3_on`, `floor_on`: the smaller rooted bounds of the proof of Thm 113, from `MarkedBoundUpTo` |
| `SeparatorSetup.lean` | sides `sideA` (= `B[C ∪ {x,y}]` + `xy`) and `sideE` (= `B − C − xy`); `E` connected on `V ∖ C`; port degrees positive on both sides; parity of `A`; **`rootedAt_of_lift`** (the root analysis shared by all cases, including the floor-plus-split when an odd root drops to degree one) |
| `SeparatorOdd.lean` | `rootedAt_oddComp`: odd `\|C\|`, `W = E + xc` (or `E + xy + yc` when the `x`-ended local path visits `y`) |
| `SeparatorEvenOdd.lean` | `rootedAt_evenComp_oddPorts`: `W = E + xy`, substitute or cut and attach |
| `SeparatorEvenEven.lean` | `rootedAt_evenComp_evenPorts`: `W = E`; graft with the two `x`-ended local paths, or the subdivided-edge Lovász decomposition and up to two grafts. Written by a sub-agent of this session and verified here. |
| `Separator.lean` | `separator_theorem`, **`separatorStatement`**, **`gallai_iff_spineTests`** |

**Deviations from the manuscript proof (the mathematics is unchanged).**

* All graphs live on the vertex type of `B`. Exterior graphs `W` reuse a vertex `c ∈ C` as the
  private leaf (`W = E + xc`), so no new vertex is created.
* Every case supplies a "lift" (each decomposition of `W` gives one of `B` with `s` more paths and
  the same ends at `r`). The root analysis is then done once, in `rootedAt_of_lift`.
* In the even/even case with `y` on the chosen row, the four sub-cases of the manuscript are
  realised as at most two successive grafts. The sub-case `X = Y` needs no separate argument.
* The local decomposition with two ends at `x` and none at `y` comes from Lovász on
  `A + leaf at x` via the private-leaf formula, with counting replacing the trimming argument.

Lean 4 + Mathlib (v4.36.0) formalization of foundational lemmas for the Gallai path
decomposition program. Everything listed below is proved with no `sorry`; `#print axioms`
shows only the standard `propext`, `Classical.choice`, `Quot.sound`.

Build: `export PATH=$HOME/.elan/bin:$PATH && lake build` from this directory. `GallaiLean/Doubling.lean`
is the slowest file, at about 40 s wall clock on an idle machine, because of its case analyses on
`Sum`/`Option`.

## Definitions (`GallaiLean/Basic.lean`, unchanged)

`GPath`, `PathDecomp` (edge lists concatenate to a duplicate-free list covering exactly
`G.edgeSet`), `PathDecomp.size`, `PathDecomp.ends`, `pathNumber` (`sInf` of sizes) and
`GallaiConjecture` (for every `W : Type u`, `[Fintype W]`, connected `G`,
`pathNumber G ≤ (card W + 1) / 2`). I did not change any definition.

## `GallaiLean/Parity.lean`: parity of ends; `pathNumber` is attained

| Lean name | Statement |
|---|---|
| `Walk.countP_add_ends` | For a path `p` from `a` to `b`: `#(edges of p at v) + [a = v] + [b = v] = 2·[v ∈ p]` |
| `Walk.even_countP_add_ends` | The same sum is even for any walk |
| `GPath.incid_of_internal` / `incid_of_end` / `incid_of_not_mem` | A path has 2 edges at an internal vertex, 1 at an end, 0 off the path |
| `PathDecomp.degree_eq_sum` | `deg v = ∑_{P ∈ D} #(edges of P at v)` (needs only `Fintype (G.neighborSet v)`) |
| `PathDecomp.ends_mod_two` | **`D.ends v % 2 = G.degree v % 2`** |
| `PathDecomp.sum_ends` | `∑_v D.ends v = 2·|D|` |
| `PathDecomp.card_odd_le` | `#{v : deg v odd} ≤ 2·|D|` |
| `card_odd_le_two_mul_pathNumber` | `#{v : deg v odd} ≤ 2·p(G)` |
| `PathDecomp.singleEdges`, `PathDecomp.nonempty` | Every graph on a finite vertex type has a decomposition (into single edges) |
| `pathNumber_spec`, `pathNumber_le`, `le_pathNumber` | `p(G)` is attained (`[Finite V]`) and is at most the size of every decomposition |

## `GallaiLean/Project.lean`: moving decompositions between graphs

* `pushWalk`: push a walk along a vertex map `f` that sends each of its edges to an edge
  (`pushWalk_edges/support/length/isPath`). `GPath.push`, `GPath.reverse`.
* `Walk.exists_append_cons_of_mem_edges`: split a walk at an edge.
* `HasPiece G' f S P`: there is an optional path of `G'` whose edges are, up to order, the
  `f`-images of the `S`-edges of `P`.
* **`PathDecomp.project` / `project_spec`** (projection lemma): suppose `f` is injective on a
  set `T` holding every vertex of every kept edge, the images of the kept edges are exactly
  `G'.edgeSet`, and every path has a piece. Then `G'` has a decomposition with at most
  `#{P ∈ D : P has a kept edge}` paths. Each path with a kept edge has its piece among the
  new paths.
* `PathDecomp.map_of_injective`: a decomposition maps along an injective vertex map whose image
  of `G.edgeSet` is `G'.edgeSet`.
* `PathDecomp.ofPerm`: a decomposition from any list of paths whose edges are a permutation of a
  duplicate-free list of all edges.

## `GallaiLean/Doubling.lean`: Gallai ⇔ rooted private-leaf test

* `addLeaf G r : SimpleGraph (Option W)`: `some a ~ some b ↔ G.Adj a b`, and `none` (the new
  leaf) is adjacent exactly to `some r`.
* `PathDecomp.trim`, **`pathNumber_le_addLeaf`**: `p(G) ≤ p(addLeaf G r)` (delete the pendant
  edge; a path through the leaf has the leaf as an end, `addLeaf_none_end`).
* `addLeaf_connected`: adding a leaf keeps a graph connected.
* `dbl H r : SimpleGraph (W ⊕ W)`: two copies of `H` plus the bridge `inl r — inr r`.
  `dbl_connected`. `dbl_walk_side`: a walk that avoids the bridge stays on one side.
* `PathDecomp.views`, **`two_mul_pathNumber_addLeaf_le`**:
  `2·p(addLeaf H r) ≤ p(dbl H r) + 1`. The left view collapses the right copy onto the leaf and
  the right view is its mirror image (via `Sum.swap`). Only the path through the bridge
  contributes to both.
* `RootedTest`: `∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W), G.Connected →
  Even (card W) → ∀ r, pathNumber (addLeaf G r) ≤ card W / 2`.
* `rootedTest_of_gallai`, `gallai_of_rootedTest`,
  **`gallai_iff_rootedTest : GallaiConjecture.{u} ↔ RootedTest.{u}`**. This holds at every
  universe `u`. The doubled graph `W ⊕ W` and `Option W` stay in `Type u`. The odd-order case
  adds a leaf, applies the test at the new vertex and trims twice.

## `GallaiLean/PrivateLeaf.lean`: the private-leaf formula

Let `leafCost D x = |D| + [D.ends x = 0]`, that is, `|D| + [x is not an end of D]`.

* `pathNumber_addLeaf_le`: `p(addLeaf G x) ≤ leafCost D x` for every decomposition `D` of `G`.
  If `x` is an end of `D`, extend that path by the leaf edge (`GPath.extendLeaf`). Otherwise add
  the leaf edge as a new path.
* `exists_leafCost_le` (`[Finite W]`): some `D` has `leafCost D x ≤ p(addLeaf G x)`. Trim an
  optimal decomposition. If the leaf path is only the leaf edge, the size drops by one. If not,
  its trimmed piece has exactly one edge at `x`, so `x` is an end of it.
* **`pathNumber_addLeaf_eq`**:
  `p(addLeaf G x) = sInf {k | ∃ D : PathDecomp G, leafCost D x = k}`.
* `PathDecomp.exists_end`: if `deg x > 0`, splitting a path at an internal visit of `x` gives a
  decomposition with at most one more path that has an end at `x`.
* `exists_end_of_pathNumber_lt`: if `p(G) < k` and `deg x > 0`, some decomposition of `G` has
  size `≤ k` and an end at `x`.
* `pathNumber_addLeaf_le_of_lt`: if `p(G) < k` and `deg x > 0`, then `p(addLeaf G x) ≤ k`.
* `pathNumber_addLeaf_le_succ`: `p(addLeaf G x) ≤ p(G) + 1` for any `x`. Hence the previous
  bound does not actually need `deg x > 0`. The positive degree matters only for having a
  decomposition of `G` itself with an end at `x`.

## `GallaiLean/Surgery.lean`: exact surgery on decompositions

* `PathDecomp.split_at`, **`PathDecomp.exists_split`**: splitting a path at an internal vertex
  `x` adds one path and two ends at `x`. Nothing else changes.
* `PathDecomp.exists_internal`, `exists_split_of_ends_eq_zero`: a vertex of positive degree with no
  ends is interior to some path, so it can be split.
* `PathDecomp.exists_split_set`: split at every vertex of a finite set of such vertices, giving
  `ends' v = ends v + 2·[v ∈ Z]`.
* `PathDecomp.exists_split_all`: split until `z` is an end of every path through it. Ends at
  `v ≠ z` are unchanged.
* **`PathDecomp.ends_eq_of_tight`**: if `2|D| ≤ #Od(G)`, then `D` has exactly one end at every odd
  vertex and none at every even vertex.
* `PathDecomp.sum_count_le_one`: an edge lies on at most one path.
* (In `Project.lean`) `GPath.endsAt_eq_ite`: the number of ends of a path at `v` is
  `[#edges at v = 1]`. **`PathDecomp.project_full`** strengthens the projection lemma. Pieces are
  needed only for paths of `D`, and the new end counts are given path by path from the images of
  the kept edges.

## `GallaiLean/Retract.lean`: deleting vertices outside an induced copy of `G`

* `Retract K G`: `G` is the subgraph of `K` induced by the kept vertices `ι '' V`, with a
  retraction `f`. `bothKept` marks the kept edges.
* `Retract.hasPiece`: a path whose non-kept vertices are among its ends has a single-path piece.
* **`Retract.delete`**: suppose that in `D` the non-kept vertices are only ever ends of paths.
  Deleting them gives `D'` on `G` with `D'.ends v = D.ends (ι v)` when `ι v` has no non-kept
  edge, and `D'.ends v ≤ D.ends (ι v) + 1` when it has at most one.

## `GallaiLean/Realisable.lean`: realisable sets (endpoint-structure manuscript, §2)

With `[Fintype V] [DecidableEq V] [DecidableRel G.Adj]`:

* `oddSet G` (`Od`), `evenSet G` (`Ev`, even and positive degree),
  `profile G S v = if deg v odd then 1 else if v ∈ S then 2 else 0`,
  `Realises G D S := ∀ v, D.ends v = profile G S v`,
  **`Realisable G S := S ⊆ evenSet G ∧ ∃ D, Realises G D S`**.
* **`Realises.size_eq`**: a realisation of `S` has `#Od/2 + |S|` paths.
* **`Realisable.insert`, `Realisable.mono`** (Lemma 1, up-closure): split a path at an interior
  visit of the new vertex.
* **`LovaszStatement`**:
  `∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
  #{v | Even (deg v)} ≤ 1 → pathNumber G ≤ card W / 2`. Isolated vertices count as even.
  `card W / 2` is `⌊N/2⌋` in both cases. It is now a theorem: `lovaszStatement` in
  `GallaiLean/Lovasz.lean`.
* `apex G T : SimpleGraph (Option V)` has an apex `none` adjacent to `T`.
  `apex_degree_some`, `apex_degree_none`.
* `realisable_of_apex`: if the apex graph has at most one even vertex, then, under Lovász, `T` is
  realisable. The proof runs Lovász on the apex graph and applies tightness, so each vertex has one
  end exactly when it is odd. It then splits at the apex so the apex only ever ends paths, deletes
  the apex (`Retract.delete`), and uses parity and the bound to get 0 or 2 ends on `T`. Finally it
  splits the zeros. This is the case analysis of Lemma 2's proof, done by counting.
* **`realisable_evenSet`** (Lemma 2, faithful partitions): `LovaszStatement → (∀ v, 0 < deg v) →
  Realisable G (evenSet G)`.
* **`realisable_evenSet_erase`** (Lemma 3): `LovaszStatement → (∀ v, 0 < deg v) →
  Even (card V) → u ∈ evenSet G → Realisable G ((evenSet G).erase u)`.

## `GallaiLean/LeafDictionary.lean`: the leaf dictionary (Lemma 4)

* `leaves G S : SimpleGraph (V ⊕ V)` is `G` on `inl` with a private leaf `inr s` at each
  `s ∈ S`. The other `inr v` are isolated, which is harmless.
  `leaves_degree_inl/inr`, and `card_oddSet_leaves`: `#Od(G^S) = #Od(G) + 2|S|`.
* `PathDecomp.extend_pendant`: attach a pendant edge at an end. The size is unchanged and one
  end moves to the new leaf.
* `realisable_of_retract`: the general repair step (delete, then split the zeros) behind both
  Lemma 2/3 and Lemma 4.
* `leaves_decomp_of_realises`: a realisation of `S` gives a decomposition of `G^S` of the same
  size.
* **`realisable_iff_leaves`**: for `S ⊆ evenSet G`,
  `Realisable G S ↔ pathNumber (leaves G S) = (oddSet (leaves G S)).card / 2`.

## `GallaiLean/Marked.lean`: marked partitions and the apex reduction (marked-reduction manuscript, §1)

This file covers the paragraph "Equivalence of the marked and ordinary bounds" on p. 3. Sites are
a `Finset`, `S : Finset V`. The file builds in about 30 s.

Definitions:

* `MarkedPartition F S` is a list of pairs (path of `F`, optional site). Its edges partition `E(F)`,
  with the same `nodup_edges`/`covers` fields as `PathDecomp`. Each site lies in `S` and is an end
  of its own path (`site_ok`), and no site occurs twice (`sites_nodup`). A path carries at most
  one site because each pair holds a single `Option`. See also `MarkedPartition.decomp` and
  `MarkedPartition.ofDecomp`.
* `markedCost M` is the number of unassigned paths. `markedNumber F S` is `q(F, S)`, defined as an
  `sInf` of costs (`markedNumber_le`, `markedNumber_spec`).
* `cone F S : SimpleGraph (Option V)` is the cone `X = F + z`. The apex `none` is adjacent exactly
  to `S`. `mem_cone_edgeSet_iff` describes its edges, and `cone_walk_lift` turns walks that avoid
  the apex into walks of `F`.
* `PathDecomp.outEnds D := ∑ v, D.ends (some v)` counts the ends away from the apex. It is defined
  for any graph on `Option U`. `outEnds_eq_sum` writes it as the sum over paths of
  `GPath.outEndsAt`, the number of ends of a path other than the apex. `two_mul_size_eq` states
  `2|D| = D.ends none + D.outEnds`.
* `minOutEnds F S` is `h`, the `sInf` of `outEnds` over the decompositions of the cone.
* `doubleCone F S := cone (twoCopies F) (univ ×ˢ S)` lives on `Option (Bool × V)`. It is two
  copies of `X` with their apices identified. `wGraph F S := addLeaf (doubleCone F S) none` is
  `W(F, S)`.

| Lean name | Statement |
|---|---|
| `exists_outEnds_eq` | A marked partition of cost `c` gives a decomposition of the cone with `outEnds = \|S\| + 2c`. Spokes are prepended to assigned paths and each unused spoke is used singly. |
| `exists_marked_of_split` | If the apex is only ever an end, a decomposition of the cone gives a marked partition with `\|S\| + 2·cost = outEnds`. The continuation of each spoke path is assigned to its site. |
| `le_outEnds` | Every decomposition of the cone has `\|S\| + 2 q(F,S) ≤ outEnds`. The proof splits at the apex with `exists_split_all` and then applies the previous row. |
| **`minOutEnds_eq`** | **Identity A**: `h(F,S) = \|S\| + 2 q(F,S)` |
| `card_wGraph`, `wGraph_connected` | `\|V(W)\| = 2\|V\| + 2`. `W` is connected if `F` is connected and `S ≠ ∅`. |
| `exists_double` | If the apex is only ever an end, a decomposition of `X` doubles to a decomposition of `doubleCone` of size `outEnds`. Each apex path is glued to its mirror image, and every other path is copied into both copies. |
| `exists_side` | If the apex is only ever an end, a decomposition of `doubleCone` restricts (`project_full`) to a decomposition of `X` with the same ends in copy `β`. |
| `pathNumber_wGraph_le` | `p(W) ≤ h + 1` |
| `le_leafCost`, `le_pathNumber_wGraph` | `p(W) ≥ \|S\| + 2q + 1`. This uses `exists_leafCost_le`, and needs `2h` ends away from the apex plus one at the leaf. |
| **`pathNumber_wGraph`** | **Identity B**: `p(W(F,S)) = \|S\| + 2 q(F,S) + 1`. Also `pathNumber_wGraph_eq_minOutEnds : p(W) = h + 1`. |
| **`markedNumber_le_of_gallai`** | `GallaiConjecture.{u} → F.Connected → S.Nonempty → q(F,S) ≤ (card V - \|S\|) / 2`. This is the "Gallai ⇒ marked bound" direction of Theorem 1. |
| `pathNumber_le_markedNumber_add` | `p(F) ≤ q(F,S) + \|S\|`: at most `\|S\|` paths are assigned. |
| `gallai_iff_markedBound` | `GallaiConjecture.{u} ↔ MarkedBound.{u}`. `MarkedBound` is the marked bound for all connected `F` and nonempty `S`. The backward direction uses a single mark. |

The file reuses `exists_split_all` (Surgery), `project_full`, `hasPiece_of_walk`, `pushWalk` and
`ofPerm` (Project), and `addLeaf`, `leafCost`, `exists_leafCost_le`,
`pathNumber_addLeaf_le_succ` and `addLeaf_connected` (Doubling/PrivateLeaf).

What is proved: targets 1–4 and the single-mark converse have no `sorry`. `#print axioms` on
`minOutEnds_eq`, `pathNumber_wGraph`, `markedNumber_le_of_gallai` and `gallai_iff_markedBound`
shows only `propext`, `Classical.choice` and `Quot.sound`.

Not formalized from Theorem 1: the reduction to two-connected graphs and even-degree sites, and
assertion 2.

## `GallaiLean/FanMoves.lean`, `GallaiLean/Fan.lean`: Fan's addible-edge lemmas

Fan (2005), Lemmas 3.3–3.4, as quoted by Botler–Sambinelli (Lemma 6) and in the six-clique
paper (Lemma 2). Here `b(w) = D.ends w`.

* `PathDecomp.replace` replaces one path by a path of a graph whose edge set differs only on that
  path. The other paths are transferred unchanged, with the same ends and support.
* `PathDecomp.append_move`: a path ending at `t` that avoids `u` absorbs the new edge `tu`.
* `PathDecomp.reroute_move`: a path read from its end `t` reaches `u` via the edge `yu`. Reverse
  the segment from `t` to `y` and trade `yu` for the new edge `tu`, so the end moves from `t` to
  `y`. Readings from the path's other end are preserved.
* `FanPred D u x z` holds when `z` is the vertex before `u` on a path of `D` read from its end
  `x`. `FanChain` is a chain `t = x₀, x₁, …, x_k` of such steps, ending at a vertex that has a
  path end avoiding `u`.
* `fan_exec`: along a duplicate-free chain from a non-neighbour `t` of `u`, the edge `tu` can be
  added. The proof is an induction that applies one reroute per step on intermediate graphs
  `K + tu − yu`, then the append. Size is unchanged, `t` loses an end and `u` gains one.
* `fan_exists_chain`: the counting/injection argument. Assume `R`, the set reachable from `T`,
  has no end on a path avoiding `u`. Then the end occurrences at `R` inject into the edges from
  `u` to `R`, which gives `∑_T b ≤ #{w ∈ N(u) : b(w) = 0}`.
* **`fan_grouped`** (grouped transfer): if `u ∉ T`, no `t ∈ T` is adjacent to `u`, and
  `#{w ∈ N(u) : b(w) = 0} < ∑_{t ∈ T} b(t)`, then for some `t ∈ T`, every graph `K'` with
  `E(K') = E(K) ∪ {tu}` has a decomposition of the same size with
  `ends' w + [t = w] = ends w + [u = w]`.
* **`fan_single`** (Lemma 3.4): let `uv ∈ E(G)`, let `G'` have edge set `E(G) \ {uv}`, and let
  `D'` decompose `G'`. If `#{w ∈ N_{G'}(u) : b(w) = 0} < D'.ends v`, then `G` has `D` with
  `|D| = |D'|`, `D.ends u = D'.ends u + 1`, `D.ends v + 1 = D'.ends v`, and `D.ends w = D'.ends w`
  for all other `w`. `fan_single_deleteEdges` is the same statement for
  `G' = G.deleteEdges {s(u,v)}`.

## `GallaiLean/Lovasz.lean`: Lovász's theorem (1968)

* **`lovasz_ends`** (strong form): if at most one vertex has *positive* even degree, then some
  path decomposition has `D.ends v = deg v % 2` for every `v`. That is, every odd vertex has
  exactly one end and every other vertex has none.
* **`lovaszStatement : LovaszStatement`**, and **`lovasz`**: if at most one vertex has even
  degree (isolated vertices included), then `pathNumber G ≤ card W / 2`.
* **`realisable_evenSet'`**, **`realisable_evenSet_erase'`**: Lemmas 2 and 3 of the
  endpoint-structure manuscript, with no Lovász hypothesis.
* The proof is a self-contained strong induction on `∑ deg + [no positive-even vertex]`. Its
  only engines are Fan's lemma (`fan_single`), deleting a pendant vertex (`Retract.delete` on
  `apex (G − ux) {u}`), and adding an edge as a new path (`PathDecomp.add_edge`). The file's
  header comment gives the full paper proof.
  - Case I (a positive-even vertex `z`): delete an edge `uz` and apply induction. `u` has no
    zero-end neighbours, so Fan's lemma moves an end from `z` to `u`.
  - Case II (all positive degrees odd, some degree at `x` is `≥ 3`): detach the edge `ux` onto a
    new leaf at `u`. This keeps the edge count and leaves exactly one even vertex, `x`. Apply
    induction and delete the leaf, which leaves 0 or 2 ends at `u`. Then either add `ux` as a
    new path or use Fan's lemma to move an end from `u` to `x`.
  - Case III (a matching): delete an edge and re-add it as a path.
  - Case IV: no edges.
* Helpers: `delEdge G a b` (with `delEdge_edgeSet`, `delEdge_degree`, `delEdge_sum_degree`),
  `apex_none_pendant`, `LovaszStrong`, and the case lemmas `lovasz_case_even/big/matching/empty`.
## `GallaiLean/EMCFour.lean`: two descent steps; the endpoint matroid for four even vertices

Endpoint-structure manuscript, section "Two descent steps, and four even vertices". Lovász enters
only as `LovaszStatement`; Fan's transfers are `fan_single` and `fan_grouped` from `Fan.lean`.

* `delE G F` (`G.deleteEdges ↑F` with decidable adjacency), `degree_delE`,
  `degree_delE_single`, `delE_single_facts`: degree bookkeeping for edge deletion.
* **`realisable_of_edge`** (transfer across an even edge): if `s, t, u'` are distinct even
  vertices, `G.Adj s t` and `¬ G.Adj s u'`, then `Ev ∖ {t, u'}` is realisable (even order,
  no isolated vertices). Lemma 3 on `G − st`, then one single transfer.
* **`realisable_of_star`** (star lemma): if the even vertex `y` is adjacent to the even vertices
  `w, x, z`, then `Ev ∖ {w, x}` or `Ev ∖ {w, z}` is realisable. Lemma 2 on `G − yw − yx − yz`,
  then a single transfer, a grouped transfer, and a single transfer away from `y`
  (`star_finish`).
* **`realisable_lift`**: for an odd neighbour `t` of an even `y`, a realisation of `S ∋ t` in
  `G − yt` whose unexposed even vertices avoid `N(y)` lifts to `S − t + y` in `G`.
* `two_step_base`, `two_step_aux` (induction on the length of a path from `y` to another even
  vertex), **`two_step_descent`**: `G` connected, even order, `4 ≤ |Ev|`, `y ≠ w` even ⇒
  `∃ v ∈ Ev, v ≠ y ∧ v ≠ w ∧ Realisable G ((Ev.erase w).erase v)`.
* **`emc_four`**: with `|Ev| = 4`, for distinct even `y, x, z`, `Realisable G {y, x} ∨
  Realisable G {y, z}`.
* `half_le_card_of_critical` (Corollary 5, first half): in a critical graph every realisable set
  has at least `|Ev|/2` elements. `exists_pair_subset`, **`minimal_realisable_iff`**:
  `Minimal (Realisable G) S ↔ S.card = 2 ∧ Realisable G S` for critical `G` with `|Ev| = 4`.
* `pair_exchange` and **`endpoint_matroid_four`**: for connected critical `G` with `|Ev| = 4`
  there is `M : Matroid V` with `M.E = Ev`, `M.Loopless`, bases exactly the realisable pairs,
  and `Minimal (Realisable G) S ↔ M.IsBase S`. This is the endpoint matroid conjecture for
  `e = 4`.
* **`rooted_four`**: `G` connected of even order with `|Ev| = 4` ⇒
  `pathNumber (addLeaf G r) ≤ card V / 2` for every `r` (the floor bound `BP_3`), without
  Botler–Sambinelli. `rooted_le_four` extends this to at most four even vertices (Lemmas 2
  and 3 for zero and two), using `pathNumber_addLeaf_le_of_realises`.

`#print axioms` on `two_step_descent`, `emc_four`, `endpoint_matroid_four`, `rooted_four` and
`rooted_le_four`
shows only `propext`, `Classical.choice` and `Quot.sound`.

## `GallaiLean/KStep.lean`: k-step descent

`Desc G k y W₀`: some `k`-set `R` of even vertices with `W₀ ⊆ R`, `y ∉ R` and `Ev ∖ R` realisable.

* `realisable_transfer`: for adjacent even `s, t`, `S` realisable in `G − st` with `N(s)`
  disjoint from the unexposed even vertices gives `insert s S` realisable in `G`.
* `delE_reach_or_reach`, `connected_delE_of_not_isBridge`, `evenSet_delE_odd`,
  `evenSet_delE_even`, `card_edgeFinset_delE_lt`: bookkeeping for deleting one edge.
* **`desc_reduction`**: `Desc · k y W₀` in connected graphs with `≥ m` even vertices reduces to
  the cases where `y` has an even neighbour or every edge at `y` is a bridge (`IsBridge`).
* **`desc_succ_of_unique`**: if `y` has exactly one even neighbour `t`, then `Desc G (k+1) y {w}`
  follows from `k`-step descent (`k ≥ 2`) in graphs where the kept vertex is joined to another
  even vertex. `desc_two_of_reachable` supplies `k = 2` from `two_step_aux`.
* **`desc_three_of_unique`**, **`desc_three_reduction`** (and primed forms without the Lovász
  hypothesis): three-step descent at an even vertex with exactly one even neighbour; reduction of
  three-step descent to the two residual cases.

## `GallaiLean/Bridge.lean`: bridges, and the reduction to the branching case

No hypotheses (Lovász is `lovaszStatement`). `DStmt j` (`D_j`): every connected even-order graph with
`≥ 2j` even vertices has `j`-step descent at `(y, {w})` for all distinct even `y, w`. `BStmt j`
(`B_j`): the same for vertices `y` with at least two even neighbours.

* **`gallai_of_branching`**: `(∀ j ≥ 3, BStmt j) → GallaiConjecture`.
* **`rooted_six_of_bstmt3`**: `BStmt 3` gives the rooted test for six even vertices.
* **`dstmt_of_branching`** (`B_3..B_K ⇒ D_1..D_K`), `dstmt_one`, `dstmt_two`, **`dstmtE_succ`**
  (one level, by strong induction on the number of edges).
* **`glue_bridge`** (concatenate the two paths through a bridge edge shared by two pieces) and
  **`glue_append`** (union, then extend a path ending at `t` by `ty`).
* `bridge_odd`, `bridge_even`: the bridge cases with pieces `G[A ∪ {t}]`, `G[Aᶜ ∪ {y}]`, resp.
  `G[A]`, `G[Aᶜ]`, as `restr G C` graphs on the same vertex type.
* Infrastructure: `PathDecomp.mapInj`, `realisable_of_induce`, `desc_of_induce`,
  `PathDecomp.exists_union`, `PathDecomp.exists_erase`, `restr`, `degree_restr_*`,
  `realisable_evenSet_ni` (Lemma 2 with isolated vertices), `piece_desc`.

`#print axioms gallai_of_branching` shows only `propext`, `Classical.choice` and `Quot.sound`.

## `GallaiLean/BranchBase.lean`: Gallai from one named hypothesis

**`BranchBase k`**: in every connected graph of even order with at least `2k` even vertices, every
even `y` with at least two even neighbours and no bridge to a vertex of degree ≥ 2 has
`Desc H k y ∅`, i.e. lies in a realisable set `Ev ∖ R` with `|R| = k`. No vertex is prescribed for
removal.

* **`rootedTest_of_branchBase : (∀ k, BranchBase k) → RootedTest`** and
  **`gallai_of_branchBase : (∀ k, BranchBase k) → GallaiConjecture`** (through
  `gallai_iff_rootedTest`). `branchBase_one` and `branchBase_two` are theorems, so
  `gallai_of_branchBase_three` needs only `k ≥ 3`.
* `branchBase_of_bstmt`: `BStmt k → BranchBase k`, so `BranchBase` is the weaker hypothesis.
* `dstmt0E_succ`: the one-level reduction for descent keeping `y` (`DStmt0`). Bridges are handled
  first (`bridge_odd0`, `bridge_even0`), so `BranchBase` only sees vertices without a non-pendant
  bridge.

`#print axioms gallai_of_branchBase` shows only `propext`, `Classical.choice` and `Quot.sound`.

## `GallaiLean/FanBarrier.lean`: three even neighbours, and the last-edge barrier

Manuscript: endpoint-structure §7.

* `desc_succ_of_transfer_two`: let `y` have exactly two even neighbours `a ≠ b`. Then descent in
  `G − ya` keeping `b` transfers to descent in `G` keeping `y`, one level up.
* **`BranchBase3 k`** is `BranchBase k` restricted to `y` with three distinct even neighbours.
  * `branchBase_of_three`: `DStmt0 k ∧ BranchBase3 (k+1) → BranchBase (k+1)`.
  * `branchBase_of_branchBase3`: from `BranchBase3` for all `k ≥ 3` to `BranchBase` for all `k ≥ 3`.
  * **`gallai_of_branchBase3 : (∀ k ≥ 3, BranchBase3 k) → GallaiConjecture`**.
* **`fan_transfer_barrier`**: let `D` partition `H`, with `ut ∉ E(H)`, and suppose Fan's condition
  `#{w ∈ N_H(u) : ends w = 0} < ends t` holds. Then
  `ends u + 2·#{w ∈ N_H(u) : deg_H w even} + 2 ≤ 3·|D|`.
  * Helper lemmas: `PathDecomp.ends_le_size` and `card_edgeFinset_le_size_mul` (`|E(H)| ≤ |D|(n−1)`).
* `fan_transfer_barrier_regular` (`2d + 1 ≤ 3|D|`), `newpath_barrier_regular` and
  `insertion_barrier_regular` (`n·d ≤ 2(|D|(n−1) + |F|)`): the bounds for `d`-regular `G`, with `d`
  even for the first.
* `cocktail m` is `K_{2m}` minus a perfect matching, on `Fin m × Bool`. `cocktail_degree`: it is
  `(2m−2)`-regular.
* **`cocktail_fan_barrier`** (`m ≥ 4`): every partition of `CP(m) − ut` has at least `m` paths, and
  more than `m` paths when Fan's condition towards `u` holds.
* **`cocktail_insertion_barrier`**: a partition of `CP(m) − F` into at most `m − 1` paths needs
  `|F| ≥ m − 1`.

No hypotheses. `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`.

## `GallaiLean/Flower.lean`: the flower move

Manuscript: endpoint-structure §7 ("The flower move"); missing-move Lemma 5.4 and Prop 5.5.

* `exists_close_cut`: close a path `P` into its cycle and cut at an edge `e` of the cycle. The result
  is a path whose ends are the ends of `e`.
* **`flower_decomp`**: suppose the cycles of the pairs `(P, e)` are the edges of `G`, and `L` is a
  path whose edges are the cut edges `e`. Then `G` has a decomposition into `|ps| + 1` paths, with
  two ends on `L` and none elsewhere.
* **`hub_cycles`** (equality forces a flower): let `D` have `|T|` ends at `s`, one on each vertex of
  `T`, and none elsewhere. Then the paths, read from `s`, end once at each vertex of `T` and carry
  the edges of `H`.
* `Transversal`, **`RainbowTransversal k`**: every system of `k` Hamiltonian cycles through `s`, on
  `2k + 2` vertices, has a path through `s` with one edge of each cycle.
  * `card_cnbr`: two cycle-neighbours per vertex.
  * `rainbowTransversal_three` (greedy), `rainbowTransversal_four` (greedy plus one rotation).
* **`cocktail_passes_of_rt`**, `cocktail_rooted_of_rt`: for `m ≥ 4`, `RainbowTransversal (m − 1)`
  gives the two-end test, and the rooted test, at every vertex of `CP(m)`. The proof runs Lovász
  (`lovasz_ends`) on `isolate (cocktail m) s`, then `m − 1` receipts (`Ach.receiveMany`), then
  `hub_cycles`, Hamiltonicity by an edge count, and finally `flower_decomp`.
* **`cocktail_passes_four`, `cocktail_passes_five`**: unconditional.
* **`flower_decomp_rest`**: the flower with untouched extra paths. It is the recombination step of
  receipt-or-flower (endpoint-structure Thm 67), used by hand for B′ (Prop 68).

No hypotheses. `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`.

## `GallaiLean/MarkedSurgery.lean`, `GallaiLean/MarkedBlocks.lean`: Theorem 1 of the marked-reduction manuscript

**Main result: Theorem 1 holds as a full equivalence.**
`gallai_iff_tests : GallaiConjecture.{u} ↔ MarkedTwoConnTest.{u} ∧ ThreeEndsTest.{u}`.
`#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`.

The two tests are:

* `MarkedTwoConnTest`: for every `TwoConnected G` and nonempty `S`,
  `markedNumber G S ≤ (card V - |S|) / 2`.
* `ThreeEndsTest`: if `J` is `TwoConnected`, `card V = 2k + 1`, `pathNumber J = k + 1` and
  `J.degree x` is odd, then some decomposition `D` has `D.size = k + 1` and `3 ≤ D.ends x`.

`TwoConnected G` is defined as `TwoConnOn G univ`. That means at least three vertices, connected,
and no cut vertex. A cut vertex is formalized as `CutSep G U x C`: a nonempty part `C` of
`U - x` and a nonempty rest, with no edge between them.

**`MarkedSurgery.lean`.** A partial marked partition `PMP G E S` is a list of paths of `G` with
optional sites whose edges are exactly `E`. Operations, all with exact cost bookkeeping:

* `replace`, `replaceSub`, `append`, `forget`, `forgetAll`, `mono`, `castE`;
* `exists_join`: join two paths at a common end;
* `exists_split`: split a path at an internal vertex;
* `exists_extend`: extend a path by a pendant edge;
* `addPath`, `exists_assign`;
* `exists_trim`: delete a pendant edge, with three outcomes;
* `push`: transport along an injective map.

**`MarkedBlocks.lean`.** The induction runs in one vertex type. An instance is a graph whose
edges lie in a finite set `U`.

* Gluing at a cut vertex: `glue0`, `glue1`, `glueJ`, `glueU`, `glueEnd`, `glueSplit`.
* **`cutStep`**: the cut-vertex reduction of p. 5, in all five of the manuscript's cases. Its
  input is `CutSides`: two connected sides of order at least three that meet only at `x`.
* **`leafStep`**: the four leaf deletions of pp. 4–5. **`doubleLeafStep`**: two leaves at the
  only mark.
* **`pendantStep`**: the residual configuration. It is a leaf at the only mark of an even-order
  graph whose core is two-connected. This is the only use of `ThreeEndsTest`, and only when the
  root has odd degree. An even-degree root gets its two ends from parity.
* `residue_sep`: every other configuration reduces to the cases above.
* `mbOn_of_tests`, **`markedBound_of_tests`**, **`gallai_of_tests`**: sufficiency.
* `markedTwoConnTest_of_gallai`, **`threeEndsTest_of_gallai`**: necessity. Attach a leaf, use
  the marked bound with one mark, trim, and use parity.

**About the bridge formula (target 1).** The exact formula `q = α₁ + α₂ + 1[…]` is **not
formalized**. The reduction does not need it. Take a bridge whose sides both have at least two
vertices. Either one side is a single edge, which ends in a leaf, or the bridge's end is a cut
vertex with sides of order at least three. The first case is handled by `leafStep`, the second
by `cutStep`. The manuscript also uses bridges to show that the pendant core is bridgeless.
Here `residue_sep` does that job instead.

## `GallaiLean/Critical.lean`

**`pathNumber_gt_of_low_degree`**: if `2 ≤ card V`, `k (card V - 1) ≤ |E(G)|` and some vertex
has `degree < k`, then `k + 1 ≤ pathNumber G`. The hypothesis `k ≥ 1` is automatic, so it is
dropped. Helpers: `PathDecomp.sum_length_eq_card` and `GPath.one_le_incid`.

## `GallaiLean/BP3.lean`: BP₃ and realisable pairs, a second argument

This is an alternative to `rooted_four` in `EMCFour.lean`, under distinct names. It needs no
even-order hypothesis and calls Lovász only through `lovasz_ends`.

* **`two_even`**: if `deg u` is even and at most one other vertex has positive even degree,
  then some `D` has `D.ends w = deg w % 2` for all `w ≠ u` and `D.ends u ∈ {0, 2}`. The proof
  attaches a leaf at `u`, applies Lovász, and deletes the leaf.
* **`four_even_pair`**: suppose `evenSet G = {r} ∪ T` with `|T| = 3`, and some path joins `r`
  to `T`. Then `{r, w}` is realisable for some `w ∈ T`. The proof has three cases: `r` adjacent
  to part of `T`, to all of `T`, or to none (recurse along a shortest path).
* **`realisable_pair_of_four`**: if `G` is connected and `|Ev| = 4`, every even `r` lies in a
  realisable pair. There is no parity hypothesis on `|V|`.
* **`bp3`**, **`bp3_pathNumber`**: if `W` is connected, has a leaf, and has exactly three even
  vertices, then `W` realises some `S` with `|S| ≤ 1`, so `pathNumber W ≤ ⌊|W|/2⌋`.
* Helpers: `delEdge_degree_of_ne/left/right`, `realises_of`, `ends_of_realises`,
  `PathDecomp.exists_end_of_pos`.

## `GallaiLean/EMCFourFree.lean`: the four-even results with no hypothesis

`EMCFour.lean`'s results take `(hL : LovaszStatement)`. That hypothesis is now discharged by
`lovaszStatement`, giving `two_step_descent'`, `emc_four'`, `exists_pair_subset'`,
`minimal_realisable_iff'`, `pair_exchange'`, `endpoint_matroid_four'` and `rooted_four'`. Their
statements are otherwise identical to the originals.

## `GallaiLean/Pyber.lean`: Pyber's theorem (1996)

* **`pyber`**: if every cycle of `G` passes through a vertex of odd degree (equivalently, the
  even-degree vertices induce a forest), then `pathNumber G ≤ card V / 2`. No connectivity is
  needed. **`pyber_of_indep`** is the special case where the even vertices are independent.
* **`pyber_claim`** (realisable form): under the same hypothesis (`OddOnCycles G`), some
  `S ⊆ Ev` with `|S| ≤ ⌊|Ev|/2⌋` is realisable.
* The proof is a strong induction on `4|Ev| + ∑ deg`, using only `lovasz_ends`,
  `fan_single` and `fan_grouped`. The file header gives the paper proof.
  - Leaf case (`pyber_case_leaf`): `G[Ev]` has an edge. Then some even vertex has exactly
    one even neighbour (`exists_even_leaf`, by a longest-path argument). Delete that edge,
    apply induction, and restore the edge by Fan.
  - Independent case (`pyber_case_indep`): take an odd `o` next to `Ev`. Cut all edges from `o`
    to `Y = N(o) ∩ Ev` (`cut G o Y`), apply induction, and put the edges back. First come
    `(|Y| + 1 − b(o))/2` grouped transfers into `o` (`cut_phase1`), then single transfers out of
    `o` (`cut_phase2`).
* Helpers: `cut`, `cut_adj`, `cut_empty`, `cut_edgeSet_erase`, `cut_degree`, `cut_sum_degree`,
  `oddOnCycles_of_indep`, `oddOnCycles_delEdge`, `PathDecomp.ends_cast`.

`#print axioms` on `pyber`, `pyber_claim`, `bp3_pathNumber`, `realisable_pair_of_four`,
`rooted_four'`, `endpoint_matroid_four'` and `two_step_descent'` shows only `propext`,
`Classical.choice` and `Quot.sound`.
## `GallaiLean/KStep.lean`: k-step descent

`Desc G k y W₀`: some `k`-set `R` of even vertices with `W₀ ⊆ R`, `y ∉ R` and `Ev ∖ R` realisable.

* `realisable_transfer`: for adjacent even `s, t`, `S` realisable in `G − st` with `N(s)`
  disjoint from the unexposed even vertices gives `insert s S` realisable in `G`.
* `delE_reach_or_reach`, `connected_delE_of_not_isBridge`, `evenSet_delE_odd`,
  `evenSet_delE_even`, `card_edgeFinset_delE_lt`: bookkeeping for deleting one edge.
* **`desc_reduction`**: `Desc · k y W₀` in connected graphs with `≥ m` even vertices reduces to
  the cases where `y` has an even neighbour or every edge at `y` is a bridge (`IsBridge`).
* **`desc_succ_of_unique`**: if `y` has exactly one even neighbour `t`, then `Desc G (k+1) y {w}`
  follows from `k`-step descent (`k ≥ 2`) in graphs where the kept vertex is joined to another
  even vertex. `desc_two_of_reachable` supplies `k = 2` from `two_step_aux`.
* **`desc_three_of_unique`**, **`desc_three_reduction`** (and primed forms without the Lovász
  hypothesis): three-step descent at an even vertex with exactly one even neighbour; reduction of
  three-step descent to the two residual cases.

## Six-clique theorem (cloud session)

Theorem 1 of *Prescribed path ends at a clique of six even vertices*
(`gallai/04-research-studies/six-clique-prescribed-ends.pdf`; audit A6 §1.3) is **fully
formalized**. There is no `sorry`, and `#print axioms Gallai.six_clique_prescribed_ends` shows only
`propext`, `Classical.choice` and `Quot.sound`. The finite bookkeeping of the paper's Section 4 is
checked by `decide +kernel`, which is kernel evaluation (no `native_decide`, no extra axiom).
`SixCliqueModel.lean` takes about 30 s to build, and each of the other new files a few seconds.
`Basic.lean` and `Fan.lean` are unchanged.

**Statement** (`GallaiLean/SixClique.lean`):

```lean
theorem six_clique_prescribed_ends (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (hU : U.card = 6) (hclique : ∀ a ∈ U, ∀ b ∈ U, a ≠ b → G.Adj a b)
    (heven : ∀ u ∈ U, Even (G.degree u)) (hodd : ∀ x ∉ U, Odd (G.degree x))
    (hfive : ∀ x ∉ U, (U.filter (G.Adj x)).card = 5)
    (T : Finset V) (hTU : T ⊆ U) (hT : T.card = 3) :
    ∃ D : PathDecomp G, 2 * D.size = Uᶜ.card + 6 ∧
      ∀ v, D.ends v = if v ∈ T then 2 else if v ∈ U then 0 else 1
```

The paper's hypothesis "`|X|` even" is derived from the handshake lemma rather than assumed.
The module docstring of `SixClique.lean` writes out the whole proof. It also expands the two
points the audit asked for: Lemma 2's chain step (F10) and Corollary 5's triple rectangle (F11).

### `GallaiLean/Insertion.lean`: decompositions as (edge set, end vector)

* `Ach E b`: `fromEdgeSet E` has a path decomposition with exactly `b v` ends at every `v`. The
  number of paths is not tracked, because `PathDecomp.sum_ends` recovers it.
* `blankNbrs E b u`: the number of neighbours of `u` with no end. `mv b t u` moves one end from
  `t` to `u`.
* **`Ach.grouped`**: Fan's grouped transfer in edge-set form (from `fan_grouped`). If
  `blankNbrs E b u < ∑_{t ∈ T} b t` and no `t ∈ T` is adjacent to `u`, then some `t ∈ T` with
  `b t ≥ 1` gives `Ach (insert s(t,u) E) (mv b t u)`. `Ach.transfer` is the case of one donor.
* `lEdges a l`, `lastOf a l`, `mem_lEdges_iff`: vertex lists and their consecutive edges.
  **`Ach.addPath`** adds a new row from a duplicate-free vertex list whose edges are all new.

### `GallaiLean/Schedule.lean`: the insertion-schedule lemma (reusable)

* `Prog n`: a program of transfers on a finite model `Fin n`. `offer ds r k` offers the donors
  `ds` to the receiver `r` and continues with `k t` for the returned donor `t`. `tr` is a single
  transfer and `ofList` a list of them.
* `Prog.ok T tgt adj ins c`: a Boolean checker. `adj` is an *upper bound* for the present edges
  among model vertices; unknown edges may be included, which only raises blank counts. At an
  offer, the receiver's model blank count must be below the total supply. Every branch with a
  positive donor is checked. At a leaf, the inserted edges must be exactly `T` and the end vector
  must be `tgt`.
* **`Prog.sound`** (and `Prog.sound₀`, starting with nothing inserted): let `ι : Fin n → V` be
  injective, let every vertex outside the image of `ι` have an end, and let every present edge
  between model vertices be allowed by `adj`. Then a checked program inserts `ι(T)` into any
  state, with end vector `tgt` on the model and unchanged elsewhere. Each offer is one
  `Ach.grouped`. Real blank neighbours inject into model blank neighbours
  (`blankNbrs_le_mblank`).
* So a finite certificate of grouped transfers (as in the six-clique, incidence and root-shape
  papers) can be verified on its model with `decide` and applied to graphs of any size.

### `GallaiLean/EvenInsert.lean`: Lemma 3 of the paper

* `Ach.chain`: the transfers `x → c₁ → ⋯ → z` along a list, under local blank-count hypotheses.
* `Ach.insert_cycle`: inserting a cycle none of whose vertex pairs is present. Offer the two
  cycle neighbours of `a` to `a`, then carry the extra end back around the other arc. When the
  other neighbour is returned, use the reversed cycle.
* `exists_cyc`, `exists_chordless`: an even finite edge set with an edge contains a cycle, and a
  shortest cycle has no chord (`shorter_of_chord`). `even_cycle_degree`: every vertex meets an
  even number of edges of a cycle.
* **`Ach.insert_even`** (Lemma 3): let `S` be independent in `E`, and let every `v ∈ S` have at
  least one end and at most one blank neighbour. Then any finite even graph on `S` can be inserted
  with the end vector unchanged. The proof is a strong induction that peels off a shortest cycle.

### `GallaiLean/SixCliqueModel.lean`: the finite core (Section 4)

On `Fin 12`, clique vertices are `0..5` and the representative of type `i` is `6 + i`.
`mpaths` holds the five seed paths and `seedE` their 24 edges. `seg1`, `seg2` and `seg3` are the
2 + 8 + 6 single transfers. `E1..E4` and `c1..c4` give the core edges and core end vectors at
each stage. `finalE` is the final path `(0,5,1,2,4,3)` and `cfin = (2,0,2,2,0,0 | 1⁶)`.
On `Fin 14`, `pairProg h` is Lemma 4 for a pair `12, 13` of type `h`: its two rectangles, with
`(j,u,v,w)` read from a table. All 18 finite facts are proved by `decide +kernel`. They cover the
seed, the segment and rectangle programs (`seg*_ok`, `pair_ok`, 4 leaves per type), the
completeness and soundness of the core edge set, and the final vector.

### `GallaiLean/SixCliqueBuild.lean`: the construction on labelled data

* `SixData V`: the graph with `ι : Fin 12 → V` (clique, then representatives), the type function,
  the list of pairs, and the hypotheses of Theorem 1 in labelled form.
* `St L A`: the state edge set. It consists of the core edges `ι(L)`, every pair's seed spoke,
  the whole exterior graph `F`, and all spokes of the completed vertices `A`. `B c` is `c` on the
  core and `1` elsewhere.
* `seed` (five model paths via `Ach.addMapPaths`, plus one row `x, p, y` per pair), `after_F`
  (Lemma 3), `pair_step` and `stage` (Lemma 4 for every pair of a stage, via `Prog.sound₀` on
  `Fin 14`), `segment` (the core transfers, via `Prog.sound₀` on `Fin 12`), `final_edges` (the
  resulting edge set is exactly `E(G)`), **`SixData.main`**.

### `GallaiLean/SixClique.lean`

`exists_pairing` splits an even finite set into disjoint pairs. The main theorem labels `U` with
`T` at `0, 2, 3`. It then derives the type function, uses the handshake lemma for `m` even and
`d(h) = 5 + m − n_h` for `n_h` odd, chooses representatives and pairings, builds `SixData`, and
reads off the ends and the size.

**Not formalized from this paper:** Corollary 5 (other proper neighbourhoods; its triple
rectangle is written out in the docstring) and Theorem 6 (its 31,442 certificate records are not
in the repository; `Prog` is the natural format for replaying them).
## `GallaiLean/TwoEven.lean`: the second descent step and the Fan calculus (endpoint-structure §5)

`delEdge G a b` is `G` without the edge `ab` (`delEdge_edgeSet`, degree lemmas
`delEdge_degree_left/right/of_ne`, `evenSet_delEdge`, `evenSet_delEdge_odd`).

| Lean name | Statement |
|---|---|
| **`realisable_erase_of_fan`** | **Fan descent.** `u, w ∈ S ⊆ Ev`, `uw ∈ E(G)`, every even neighbour of `w` lies in `S`, and `S \ {u, w}` is realisable in `G − uw` ⇒ `S \ {u}` is realisable in `G`. One application of `fan_single` (gainer `w`, loser `u`). |
| **`realisable_of_fan_transfer`** | **Fan transfer.** `u ∈ Ev \ S`, `w` odd, `uw ∈ E(G)`, every even neighbour `x ≠ u` of `w` lies in `S`, and `S` is realisable in `G − uw` ⇒ `S` is realisable in `G`. |
| **`realisable_evenSet_erase_pair`** | **Second descent step** (needs `LovaszStatement`, even order, no isolated vertex): distinct even `a, b, w` with `aw ∈ E`, `bw ∉ E` ⇒ `Ev \ {a, b}` is realisable. Lemma 3 in `G − aw`, then Fan descent. |
| **`etwin_of_not_realisable`** | If `Ev \ {a, b}` is not realisable then `a, b` have the same neighbours among the other even vertices (E-twins). |
| `fd_second_step` | The second step of faithful descent from `Ev \ {u}` keeping a root `r`, given a non-twin `v`. |
| `FanSchedule`, **`realisable_of_fanSchedule`** | Iterated Fan descent with even steps only (semi-induced matchings in `G[Ev]`). |
| `FanCert`, **`realisable_of_fanCert`** | **Soundness of the Fan calculus**: a list of even steps and odd transfers (odd partner of degree ≥ 3) ending with at most one vertex certifies that `Ev \ X` is realisable. |
| `Tight`, `tight_of_transfer`, `tight_of_fanCert` | The two-even-vertex problem: `Tight H := Realisable H ∅` (the parity bound `#odd/2`); the transfer lemma for graphs with `evenSet H = {u, v}`. |
| `PathDecomp.degree_add_ends_le`, `degree_le_of_tight` | `deg v + ends v ≤ 2|D|`; obstruction (O1): in a tight graph every odd vertex has degree ≤ `#odd − 1`. |
| **`realisable_pair`** (with `pair_core`, `pair_finish`, `degree_delEdge₂`, `edgeSet_readd`) | **Pair step** (Thm 26): `u, a, a'` distinct even, `w ≠ u` adjacent to `a, a'`; if `w` is even of degree ≥ 4, or odd with `aa' ∉ E` or `a, a' ≁ u`, then `Ev \ {u, a}` or `Ev \ {u, a'}` is realisable. Lemma 3 in `G − aw − a'w`, then `fan_grouped` at `w` and `fan_single` for the other edge. |
| `pathMoves`, `OddPath`, `fanCert_of_oddPath`, **`realisable_of_oddPath`** | **Path transfer** (the step in Thm 28): a path from `a` through odd vertices of degree ≥ 3 not adjacent to `u`, ending at an even `t ≠ u`, `t ≁ u`, gives `Ev \ {a, u}`. |
| `PathDecomp.ends_le_degree`, **`realisable_leaves_singleton`**, **`tight_leaves_of_lovasz`** | Move (L) for a pendant vertex at an odd vertex (in the `leaves` encoding); the leaf case of the two-even problem: `G` with at most one even vertex plus a pendant vertex at an odd `x` is tight. |

`#print axioms` on all of these: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`. Lovász enters
only as `LovaszStatement`. Not formalized from §5: the reductions (S) and (C) of Proposition 29 (they delete a vertex),
move (L) beyond the single-pendant form above, the combinatorial assembly of Corollary 27 and
Theorem 28 (twin classes, a shortest path between even vertices), and the obstructions (O2), (O3)
and the cut-vertex rule.

## `GallaiLean/MissingMove.lean`: Lovász's spare path at a hub (missing-move manuscript)

The Fan game of connections §R lost on five graphs of order 8. The missing move is *path insertion*
(a new path of any length made of held edges), paid for by the spare path that Lovász's theorem
leaves when `G − F` has an isolated vertex. Manuscript `manuscripts/missing-move`.

| Lean name | Statement |
|---|---|
| `isolate G s`, `isolate_edgeSet`, `isolate_degree`, `isolate_degree_self` | `G` with every edge at `s` removed, and its degrees |
| `Ach.decomp_of_edgeSet`, `Ach.of_decomp` | `Ach G.edgeSet b` ⇔ a decomposition of `G` with end vector `b` |
| `blankNbrs_eq_zero_of_isolated` | an isolated receiver has no blank neighbour |
| `Ach.hub_close` | the last two steps of the hub: the new path `y' s x` |
| **`Ach.hub_four`** | **Hub lemma** (Lemma 2.1). If `s` meets no edge of `E`, and `a, c, d` have ends, then inserting `sa, sc, sd, sx` costs one extra path. For some `{y, y'} = {c, d}`: `b' v + [v=a] + [v=y] = b v + 2[v=s] + [v=y'] + [v=x]`. The steps are `Ach.transfer`, then `Ach.grouped`, then `Ach.addPath`. |
| **`hub_four_ends`** | **Degree-four hubs** (Thm 2.2). Even order, `d(s) = 4`, all neighbours of `s` even, `#{v ∈ Ev : v ≠ s, sv ∉ E} ≤ 1` ⇒ for every neighbour `x` there is a decomposition with `2·size ≤ n`, `ends s = 2`, `ends x = 2`. Lovász is `lovasz_ends`, so this is unconditional. |
| **`hub_four_rooted`** | the same hypotheses ⇒ `pathNumber (addLeaf G r) ≤ n/2` for `r = s` and for every neighbour `r` of `s` |
| `Ach.hub_close_tail`, **`Ach.hub_four_tail`** | the hub lemma with one more held edge `xz`: the new path is `y' s x z`; profile `+2` at `s`, `−1` at `a, y`, `+1` at `y', z` |
| **`hub_four_odd_ends`**, `hub_four_odd_rooted` | **degree-four hub with one odd neighbour** (Thm 2.5): `d(s) = 4`, neighbours `a, c, d` even, `x` odd, `z ∉ N[s]` an even neighbour of `x`, ≤ 1 even vertex outside `N[s] ∪ {z}` ⇒ ≤ n/2 paths with `ends s = ends z = 2` |
| **`gqz_rooted_three`** | the critical order-8 graph `Gqz~vw` (`gqzGraph` on `Fin 8`) satisfies `pathNumber (addLeaf gqzGraph 3) ≤ 4`; hypotheses by `decide` |
| `blankNbrs_insert_le` | receiving `ts` at `s` creates at most one new blank neighbour of `s` (only when `b t = 1`) |
| **`Ach.hub_receipts`** | **receipts at a hub, any number** (Lemma 6.1) (generalises `Ach.receiveMany` of `Relay.lean`, which has `b = 1` on the donors). `s ∉ T`, no edge `ts` in `E`, `1 ≤ b ≤ 2` on `T`, `r ≤ |T|`, `blankNbrs E b s + 2r ≤ ∑_T b + 1` ⇒ some `R ⊆ T`, `|R| = r`, with `Ach (E ∪ {ts : t ∈ R}) b'` and `b' v + [v∈R] = b v + r[v=s]` (induction on `r`; each step is `Ach.grouped`) |
| **`Ach.hub_general`** | **general hub lemma** (Lemma 6.2). `s` isolated in `E`, `s ∉ N`, `1 ≤ b ≤ 2` on `N`, `|N| ≥ 2`, `2|N| ≤ ∑_N b + 5` ⇒ `Ach (E ∪ sN) b'` with `b' v + [v∈R] = b v + (|N|−2)[v=s] + [v=y] + [v=y']`, `R ⊆ N`, `|R| = |N| − 2`, `N \ R = {y, y'}`: one extra path |
| **`Ach.two_hub`** | **two-hub lemma** (Lemma 6.5). `s₁ ≠ s₂` isolated, `N₁, N₂` disjoint, common neighbour `m ∉ N₁ ∪ N₂`, `1 ≤ b ≤ 2` on `N_i`, `|N_i| ≥ 1`, `2|N_i| ≤ ∑_{N_i} b + 3` ⇒ `Ach (E ∪ s₁N₁ ∪ s₂N₂ ∪ {s₁m, s₂m}) b'` with `b' v + [v∈R₁] + [v∈R₂] = b v + (|N₁|−1)[v=s₁] + (|N₂|−1)[v=s₂] + [v=y₁] + [v=y₂]`: one extra path for both stars, the path `y₁ s₁ m s₂ y₂` |
| **`Ach.relays`** | **forward relays** (Lemma 6.3). `z` injective on `X`, `z x ∉ X`, `b (z x) = 1`, `s(z x, x) ∉ E`, and no `x ∈ X` has an `E`-neighbour `w` with `b w = 0` or `w = z x'` ⇒ the single transfers `z x → x` succeed in any order: `b' v + [v ∈ z(X)] = b v + [v ∈ X]` |
| **`Ach.relay_hub`** | **relays, then a hub** (the step of Theorem 6.4 after the seed). `s` isolated, `b = 1` on `N ∌ s`, relays into `X ⊆ N` from `z x ∉ N ∪ {s}`, `|N| ≤ |X| + 5` ⇒ the star `sN` and the relay edges cost one path; profile `+[v∈X] − [v∈z(X)] + (|N|−2)[v=s] − [v∈R] + [v=y] + [v=y']` |
| `fanPre_transport`, **`fan_reroute_exec`** | executing a partial chain: along a duplicate-free predecessor sequence `t = x₀, …, x_k = z` (`k ≥ 1`), `K + tu − zu` has a decomposition of the same size with an end moved from `t` to `z` (the reroutes of `fan_exec` without its final append) |
| `fan_alt_count` | either some chain from `T` terminates, or `∑_T ends ≤ #{blank neighbours of u reachable from T}` (the counting of `fan_exists_chain`, stopped before the contradiction) |
| **`fan_alternative`** | **Fan's alternative** (Lemma 4.2): either some `t ∈ T` gives an end to `u`, or a set `W` of blank neighbours of `u` with `∑_T ends ≤ |W|` can each be activated (`K + tu − zu`, end `t → z`) |

`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`. Not formalized:
Lemma 4.1 (rotation; it is the one-step case of `fan_reroute_exec` plus `append_move`), the
hand arguments of §5 (Proposition 5.2, the degree-six hub of `A_{6,2}`; the flower Lemma 5.4 and
Proposition 5.5, `K₈` minus a perfect matching), and the Lovász wrappers of Theorem 6.4 (relay
hub) and Corollary 6.6 (two hubs), i.e. the graph-level statements; their profile-level steps are
`Ach.relay_hub` and `Ach.two_hub`.

## `GallaiLean/EmmTemplate.lean`: cut feasibility and the leaf reduction (missing-move §7, track C4)

| Lean name | Statement |
|---|---|
| `cutCount G W` | `∑_{u ∈ W} #{y ∉ W : G.Adj u y}` = `|δ(W)|` |
| `CutOK G b p` | (L) `b v ≤ d v ∧ d v + b v ≤ 2p`; (C) `∀ v W, v ∉ W → b(W) + d v + b v ≤ cutCount G W + 2p` (ED §12.4 (1), general profiles) |
| `cutCount_delEdge` | deleting `xw` lowers `cutCount W` by `[x ∈ W ∌ w] + [w ∈ W ∌ x]` |
| `cutCount_insert_leaf` | for a leaf `w` at `x ∈ W`: `cutCount (insert w W) + 1 = cutCount W` |
| **`cutOK_leaf`** | leaf `w` at `x`, `b w = 1`, `b x + 2 ≤ d x`: `CutOK G b p → CutOK (delEdge G x w) (leafProfile b x w) p` |
| **`ach_of_leaf`** | `Ach (G − xw) (leafProfile b x w) → Ach G b` (`Ach.transfer`; `w` isolated) |
| **`leaf_step`** | the minimal-counterexample step: the leaf reduction (Lemma 7.8(c)) |

No `sorry`; `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`.

## Open / not formalized

Nothing from targets 1–3 or from the endpoint-structure lemmas (Definition and Lemmas 1–4) is
left open. Lovász's theorem is proved (`lovaszStatement`), so Lemmas 2 and 3 hold
unconditionally (`realisable_evenSet'`, `realisable_evenSet_erase'`). The section "Two descent
steps, and four even vertices" is formalized in full (`EMCFour.lean`, `KStep.lean`). Sections 3–4
of the manuscript are not formalized (the first half of Corollary 5 is
`half_le_card_of_critical`). Fan's single-edge and grouped lemmas are proved in full, with no
special-case restriction. Not formalized: an `ℕ∞`/`iInf` form of the formula (it is stated with
`sInf` over a set of naturals), and versions of the results for infinite vertex types
(`pathNumber` is `sInf ∅ = 0` there, so the statements assume `Finite`/`Fintype`).

**Fan (2005)** is not formalized: each block of the even subgraph triangle-free with `Δ ≤ 3` ⇒
`p ≤ ⌊n/2⌋`. Mathlib has no block decomposition, and the primary text was not available. The
`Pyber.lean` method does not extend directly. When `G[Ev]` has a cycle, cut the two cycle edges
at a vertex `o`. If induction returns `b(o) = 0`, the second restored edge can fail Fan's
zero-end test at the cycle neighbour. So Fan's proof needs a stronger inductive invariant than
"some realisable `S` with `|S| ≤ ⌊e/2⌋`".

## d6-frontier hub closures (cloud session, branch `claude/lean-d6-frontier`)

Manuscript `manuscripts/d6-frontier`: Lemma 2.3, Lemma 3.2, Theorem 4.1(i), Theorem 5.2 and
**Theorem 6.1 at every deletion degree `d`**. Sorry-free; `#print axioms` on every main result
shows only `propext`, `Classical.choice`, `Quot.sound`. Lovász enters through the theorem
`lovaszStatement`, so the results are unconditional. Audit notes:
`research/audit/d6-frontier-lean-audit.md`.

### `GallaiLean/Relay.lean`: relays, carries and hub transfers (in `Ach` form)

| Lean name | Statement |
|---|---|
| **`Ach.forwardRelay`** | Lemma 2.3(a): along `v₀ v₁ ⋯ v_m` with new edges, `v₀ → v₁ → ⋯ → v_m` moves one end from `v₀` to `v_m`, if `b(v₀) > bl(v₁)`, internal vertices have an end, and later receivers have `≤ 1` blank neighbour (for `mv b v₀ v₁`, which is the partition current at that moment) |
| **`Ach.carry`** | Lemma 2.3(b): `v₁ → v₀, …, v_m → v_{m-1}` moves one end from `v_m` to `v₀`, if `v₁..v_m` have ends and no receiver is adjacent in `E` to a blank vertex other than `v₀` (weaker than the paper) |
| `mv_mv_back`, `blankNbrs_eq_zero` | bookkeeping |
| `hubSpokes h Z`, `recvEnds`, `giveEnds` | the spokes from a hub; end vectors after receipts / donations |
| **`Ach.receiveMany`** | `m` grouped receipts at `h` from a set `S` of non-neighbours with one end each, if `bl(h) + j < |S| − j` for `j < m`; the donor set `Z` is existential |
| **`Ach.giveAll`** | donations from `h` to every vertex of `R`, in any order, if every receiver has `≤ c` blank neighbours outside `R` and `c + |R| ≤ b(h)` (covers donations and paybacks) |

### `GallaiLean/HubPhases.lean`: held edges, seeds, phases

* `hubHeld h X C` (spokes `h–X` plus edges `C`), `hst h N B D` (hub `N`, blank `B`, doubled `D`,
  one elsewhere), `batChords L`, **`PassesAt G r`** (a decomposition with `≤ |V|/2` paths and
  `≥ 2` ends at `r`).
* `mem_hubE`, `hubE_union_spokes` (inserting spokes un-holds them), `ach_of_deleteEdges`,
  `pathDecomp_of_ach`.
* **`seed_pair`**, **`seed_odd`**: Lemma 3.2(b), (a) (from `realisable_evenSet_erase'`,
  `lovasz_ends`). **`degree_hubDel`**: degrees after deleting the held spokes and battery chords.
* Phases, each keeping the form `Ach (G.edgeSet \ hubHeld h X C) (hst h N B D)`:
  `hub_take` (single receipt), `hub_receive` (grouped receipts), `hub_give` (donations),
  `hub_payback` (paybacks to quiet blank vertices), `hub_pay_one` (one payback with a blank
  count), `blankNbrs_hub_le`.

### `GallaiLean/D6Frontier.lean`: the theorems

| Lean name | Statement |
|---|---|
| `hub_batteries` | carry a list of batteries `(a, b)` in order (`b → h`, `a → b`) |
| **`hub_run`** | seed → batteries → `m` receipts from `T` → donations to `Q ∪ (T \ Z)` → paybacks to the pendant and parked vertices; ends with all edges, `Z` blank, `Q ∪ (T \ Z)` doubled |
| `hub_seed_deg`, `card_hubX`, `root_hub_seed` | seed degrees and parities |
| `passesAt_of_realisable` | realisable `S ∋ r` with `2|S| ≤ #even` ⇒ `r` passes |
| **`root_hub_uniform`** (`_passes`) | **Thm 6.1(a)**, every `d`: `r` adjacent to `T = U − r`, quiet odd pendant `y` (`d(y) ≥ 3`), `β ≥ d/2 − 3` quiet batteries (`L.Pairwise`: `a_i b_j ∉ E` for `i < j`; `b_i ∉ N(y)`), `d(r) ≥ d + 2 + 2β` ⇒ some `S ∋ r`, `|S| = d/2`, is realisable |
| **`full_hub_uniform`** (`_passes`) | **Thm 6.1(b)**, every `d`: `x` adjacent to all of `U`, `β ≥ d/2 − 1` quiet batteries ⇒ every `r ∈ U` |
| **`full_hub_pendant_uniform`** (`_passes`) | **Thm 6.1(b)** with `β ≥ d/2 − 2` batteries, a quiet pendant and a further neighbour of `x` |
| **`full_hub_six`**, **`full_hub_six_pendant`** | **Thm 5.2** (`d = 6`), in the paper's wording |
| **`root_hub_six`** (`_passes`) | **Thm 4.1(i)** (`d = 6`): `r` adjacent to `T`, `d(r) ≥ 8`, odd `y ∈ N(r)` with `d(y) ≥ 3`, `|N(y) ∩ T| ≤ 2` ⇒ some `S ∋ r`, `|S| = 3`, realisable. Controlled first receipt `p → r`, two grouped receipts, receivers ordered after the fact |
| **`root_hub_six_Q1`**, **`root_hub_six_Q2`** (`_passes`) | **Thm 4.1(ii), (iii)** (`d = 6`): one or two core non-neighbours `q` of `r` (assumed non-isolated, audit F1), a triangle `r a b` of odd vertices with `|N(a) ∩ T| ≤ 2` and `bq ∉ E` (resp. `|N(a) ∩ N_T(r)| ≤ 1` and `bq₂ ∉ E`) |

No lower bound on `d` is assumed in Theorem 6.1 (the paper's `d ≥ 4` is not used). Not
formalized from the manuscript: Theorems 3.1/3.2 (terminal step), 4.2, 4.4, Corollary 4.5,
Proposition 7.1.
## `GallaiLean/FiveEven.lean`, `GallaiLean/FiveEvenCerts.lean`: five even vertices, one universal vertex

Manuscript `manuscripts/bs-prescribed` (Theorem 1). This removes Shaik's preprint from marked-reduction
Cor 106 and Thm 144. The work was done in a cloud session on branch `claude/bs-prescribed`.
`FiveEvenCerts.lean` is generated by `manuscripts/bs-prescribed/scripts/gen_lean.py`.

| `FiveEven.okS`, `FiveEven.soundS` | the `Prog.ok` checker with free leaf vectors; soundness by `Ach.grouped`; the sum of ends is preserved |
| `FiveEven.seed` | the Lovász seed of a certificate: `W − H` has no end at the unique even model vertex and one elsewhere (`lovasz_ends`, `delE`) |
| `FiveEven.floor_of_cert` | a checked program on an exact model of `W` gives `D` with `2|D| + 1 = |V|` |
| `FiveEven.local_ok`, `FiveEven.bow_ok` | the 38 local and 93 bowtie certificates check (`decide +kernel`) |
| `FiveEven.five_even_local` | five even vertices `ι 0..4`; `ι 0` is adjacent to the others; no other is universal; the rim is not a perfect matching ⇒ floor |
| `FiveEven.five_even_bowtie` | the bowtie, given odd adjacent `u = ι 5`, `v = ι 6` with `N(u) ∩ T ≠ ∅ = N(v) ∩ T` ⇒ floor |
| `FiveEven.exists_uv` | a shortest walk from a leaf with an odd neighbour to `T` gives such `u, v` |
| **`FiveEven.five_even_floor`** | `W` connected, even set `T` with `|T| = 5`, exactly one vertex of `T` adjacent to the rest, and a leaf at an odd support ⇒ `∃ D : PathDecomp W, 2 * D.size + 1 = card V` |

Sorry-free. `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`.

## Cut selection (endpoint-min-max Thm 21; cloud session, branch `claude/emc-four-even`)

`PairingLemma.lean` and `CutSelection.lean`, 1,237 lines, no `sorry`. **`cs_all` depends only on `propext`, `Classical.choice` and `Quot.sound`.** The full library builds.

- **`cs_all`**: `G.Connected → Even (card V) → ∃ P, IsPairing (evenSet G) P ∧ ∀ M ⊆ evenSet G, (∀ a ∈ evenSet G, a ∈ M ↔ P a ∉ M) → CutOK G (profile G M) (card V / 2)`.
  - Every connected graph of even order has a pairing of its even vertices all of whose transversal half-sets satisfy the cut conditions of even-degrees §12.4.
  - `CutOK` is the definition from `EmmTemplate.lean`; `profile` and `evenSet` come from `Realisable.lean`.
- **`pairing_lemma`** (`PairingLemma.lean`): the odd vertices of any finite graph pair up with `splitCount ≤ crossCount` for every vertex set. The proof is by edge deletion with the triangle inequality of `sep`.
- **`exists_tjoin`**: T-joins in connected graphs, built from paths and symmetric differences of edge sets.
- **Auxiliary graph B.** `auxB` lives on `V × V`, with `freeStar` (F^v) and `starComp` (G^v).
  - `odd_degree_auxB`: Odd(B) is the diagonal over the even vertices.
  - `crossCount_auxB_le`: an injection of the crossing edges of B into those of G^v.
  - `pairing_transfer`.
- **`cutOK_of_pairing`**: the pairing criterion implies `CutOK`, via `key_identity` (|δ(W)| + |Y| = |δ_{G^v}(Y)| + d(v)).

This formalises the manuscript's second, shorter proof: the pairing lemma applied once to B. It independently checks Thm 21.
## NearDirac (cloud session `dense-near-dirac`)

File: `GallaiLean/NearDirac.lean`. It is sorry-free. `#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`. It holds the two finite lemmas of `manuscripts/near-dirac` (balanced return theorem):

* `NearDirac.matrix_cut_ineq` proves 0.6x + 0.6y − 0.4 − xy + 0.03·min(x,y) < 0 on [0, 0.65]². This closes the max-flow cut check of the membership-matrix lemma (manuscript Lemma 3.1, SP Lemma 14.28).
* `NearDirac.dense_bipartite_hall`: if |L| = |R| = k ≥ 4M and every vertex on either side is related to at least k − 2M vertices of the other, then there is an injective matching L → R. This is the Hall step of the weaving lemma (manuscript Lemma 3.2, SP Lemma 14.29), derived from Mathlib's `Finset.all_card_le_biUnion_card_iff_exists_injective`.
