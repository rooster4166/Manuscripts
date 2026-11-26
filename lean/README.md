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

## Open / not formalized

Nothing from targets 1–3 or from the endpoint-structure lemmas (Definition and Lemmas 1–4) is
left open. Lovász's theorem enters only as the explicit hypothesis `LovaszStatement`.
Corollary 5 and Sections 3–4 of the manuscript are not formalized. Fan's single-edge and grouped
lemmas are proved in full, with no special-case restriction. Not formalized: an `ℕ∞`/`iInf` form of the formula (it
is stated with `sInf` over a set of naturals), and versions of the results for infinite vertex
types (`pathNumber` is `sInf ∅ = 0` there, so the statements assume `Finite`/`Fintype`).
