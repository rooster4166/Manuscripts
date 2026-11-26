# GallaiLean

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
  `card W / 2` is `⌊N/2⌋` in both cases. It is a hypothesis and is not proved here.
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

## Open / not formalized

Nothing from targets 1–3 or from the endpoint-structure lemmas (Definition and Lemmas 1–4) is
left open. Lovász's theorem enters only as the explicit hypothesis `LovaszStatement`.
Corollary 5 and Sections 3–4 of the manuscript are not formalized. Fan's single-edge and grouped
lemmas are proved in full, with no special-case restriction. Not formalized: an `ℕ∞`/`iInf` form of the formula (it
is stated with `sInf` over a set of naturals), and versions of the results for infinite vertex
types (`pathNumber` is `sInf ∅ = 0` there, so the statements assume `Finite`/`Fintype`).
