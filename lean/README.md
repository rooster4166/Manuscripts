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

## Open / not formalized

Nothing from targets 1–3 or from the endpoint-structure lemmas (Definition and Lemmas 1–4) is
left open. Lovász's theorem enters only as the explicit hypothesis `LovaszStatement`.
Corollary 5 and Sections 3–4 of the manuscript are not formalized. Not formalized: an `ℕ∞`/`iInf` form of the formula (it
is stated with `sInf` over a set of naturals), and versions of the results for infinite vertex
types (`pathNumber` is `sInf ∅ = 0` there, so the statements assume `Finite`/`Fintype`).
