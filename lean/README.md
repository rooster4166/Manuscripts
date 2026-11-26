# GallaiLean

## Spine 113/114 (cloud session)

Branch `claude/lean-spine-113-114`. New file `GallaiLean/ThreeConnected.lean` (sorry-free;
`#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`).

**Status (interim):** (a) Gallai ⇒ both tests: **proved**. (b) apex construction and its
3-connectivity: **proved**. (d) converse: **proved modulo explicit hypotheses** `LovaszStatement`,
`Thm59Statement`, `SeparatorStatement`. (c) Theorem 113 (`SeparatorStatement`): in progress.

| Lean name | Statement |
|---|---|
| `KConnected k G` | `k + 1 ≤ \|V\|` and `G.induce Xᶜ` is connected for every `X` with `\|X\| < k` |
| `delVert J z` | `J − z` (induced on `{v \| v ≠ z}`) |
| `HasMatchingCut`, `InClassC` | matching cut; the class `C` (2-connected, no matching cut) |
| `Test1 J z`, `Test2 J z` | assertions 1 and 2 of marked-reduction Thm 114 |
| `SpineTests`, `SpineTestsNMC` | both tests on every 3-connected `J` (resp. only when `J − z` has no matching cut) |
| **`spineTests_of_gallai`** | `GallaiConjecture → SpineTests` (forward direction of Thm 114) |
| `PathDecomp.trim_ends` | trimming the private leaf: same size and `+1` end at `x`, or one path less and `−1` end |
| `exists_two_ends`, `exists_three_ends` | `F₂` from leaf cost, `F₃` from any decomposition (split at an internal visit) |
| **`apex_kConnected_three`** | `B` 2-connected, `\|S\| ≥ 3`, every component of `B − {x,y}` meets `S` ⇒ `apex B S` is 3-connected |
| `RootedAt B x` | the two rooted assertions of Thm 59 at `x` |
| `SmallBlocks F m`, `MarkedBoundUpTo m` | blocks of order `≤ m` (2-connected induced subgraphs); marked bound (1) on such graphs |
| `Thm59Statement` | **hypothesis**: Thm 59, finite-order form (audit F1) |
| `IsSepComponent`, `SeparatorStatement` | Thm 113 in the audit's F7 form (hypothesis until proved) |
| `rootedAt_of_few_even` | `\|{even} ∪ {r}\| ≤ 2` ⇒ rooted test at `r` (Lovász) |
| **`gallai_of_spineTestsNMC`** | `LovaszStatement → Thm59Statement → SeparatorStatement → SpineTestsNMC → GallaiConjecture` |

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

## Open / not formalized

Nothing from targets 1–3 or from the endpoint-structure lemmas (Definition and Lemmas 1–4) is
left open. Lovász's theorem is proved (`lovaszStatement`), so Lemmas 2 and 3 hold
unconditionally (`realisable_evenSet'`, `realisable_evenSet_erase'`).
Corollary 5 and Sections 3–4 of the manuscript are not formalized. Fan's single-edge and grouped
left open. The section "Two descent steps, and four even vertices" is formalized in full
(`EMCFour.lean`). Lovász's theorem enters only as the explicit hypothesis `LovaszStatement`.
Sections 3–4 of the manuscript are not formalized (the first half of Corollary 5 is `half_le_card_of_critical`). Fan's single-edge and grouped
lemmas are proved in full, with no special-case restriction. Not formalized: an `ℕ∞`/`iInf` form of the formula (it
is stated with `sInf` over a set of naturals), and versions of the results for infinite vertex
types (`pathNumber` is `sInf ∅ = 0` there, so the statements assume `Finite`/`Fintype`).
