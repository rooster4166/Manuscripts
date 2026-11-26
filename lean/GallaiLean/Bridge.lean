import GallaiLean.KStep
import GallaiLean.EMCFourFree

/-!
# Bridges, and the reduction of k-step descent to the branching case

Endpoint-structure manuscript, subsection "Bridges, and reduction to the branching case"
(Lemma 28, Theorem 29, Corollary 30). No hypotheses: Lovász's theorem is `lovaszStatement`.

`DStmt j` (`D_j`): every connected graph of even order with at least `2j` even vertices has
`j`-step descent at `(y, {w})` for all distinct even `y, w`. `BStmt j` (`B_j`): the same for
vertices `y` with at least two even neighbours.

## Main results

* **`gallai_of_branching`**: `(∀ j ≥ 3, BStmt j) → GallaiConjecture`.
* **`rooted_six_of_bstmt3`**: `BStmt 3` gives the rooted test for every connected graph of even
  order with exactly six even vertices (test (i) at deletion degree 6).
* **`dstmt_of_branching`**: `B_3, …, B_K` imply `D_1, …, D_K`; `dstmt_one` (Lemma 3),
  `dstmt_two` (two-step descent).
* **`dstmtE_succ`**: `D_1, …, D_k` and `B_{k+1}` imply `D_{k+1}` (`k ≥ 2`). Strong induction on the
  number of edges with four cases: two even neighbours (`B_{k+1}`); a non-pendant bridge at `y`
  (`bridge_odd`, `bridge_even`); exactly one even neighbour through a non-bridge
  (`desc_succ_of_transfer`); otherwise a non-bridge edge to an odd neighbour
  (`desc_lift_of_no_even_nbr`).
* **`glue_bridge`**, **`glue_append`**: the two bridge gluings (Lemma 28).

## Infrastructure

* Part 1: `GPath.mapInj`, `PathDecomp.mapInj`, `realisable_of_induce`, `desc_of_induce`
  (transport from `H.induce s` to `H` when `s` contains every edge).
* Part 2: `DStmt`, `BStmt`, `nonIso`, `NIConn`, `desc_of_dstmt`, `desc_of_bstmt` (the statements
  applied to graphs with isolated vertices, through the induced graph on the non-isolated ones).
* Part 3: `PathDecomp.exists_union`, `PathDecomp.exists_erase`, `GPath.end_of_unique_edge`,
  `GPath.exists_first_step`, `glue_bridge`, `glue_append`.
* Part 4: `restr G C` (edges inside `C`), its degrees, `realisable_evenSet_ni`,
  `DStmtE` (bounded edge count), `desc_of_dstmtE`, `piece_desc` (descent in a piece).
* Parts 5–7: the bridge cases, the reduction, and the consequences.
-/

open SimpleGraph

namespace Gallai

universe u v

section transport

variable {V : Type u} {V' : Type v} [DecidableEq V] [DecidableEq V']

/-- A path pushed along an injective map. -/
def GPath.mapInj {G : SimpleGraph V} {G' : SimpleGraph V'} (f : V → V')
    (hf : Function.Injective f) (hE : ∀ e ∈ G.edgeSet, e.map f ∈ G'.edgeSet) (P : GPath G) :
    GPath G' where
  src := f P.src
  tgt := f P.tgt
  walk := pushWalk f P.walk (fun e he => hE e (P.walk.edges_subset_edgeSet he))
  isPath := pushWalk_isPath f P.walk _ P.isPath (fun _ _ _ _ h => hf h)
  pos := by rw [pushWalk_length]; exact P.pos

omit [DecidableEq V] [DecidableEq V'] in
@[simp] theorem GPath.mapInj_edges {G : SimpleGraph V} {G' : SimpleGraph V'} (f : V → V')
    (hf : Function.Injective f) (hE : ∀ e ∈ G.edgeSet, e.map f ∈ G'.edgeSet) (P : GPath G) :
    (P.mapInj f hf hE).edges = P.edges.map (Sym2.map f) := by
  simp [GPath.mapInj, GPath.edges]

theorem GPath.mapInj_endsAt {G : SimpleGraph V} {G' : SimpleGraph V'} (f : V → V')
    (hf : Function.Injective f) (hE : ∀ e ∈ G.edgeSet, e.map f ∈ G'.edgeSet) (P : GPath G)
    (x : V) : (P.mapInj f hf hE).endsAt (f x) = P.endsAt x := by
  simp [GPath.endsAt, GPath.mapInj, hf.eq_iff]

omit [DecidableEq V] in
theorem GPath.mapInj_endsAt_out {G : SimpleGraph V} {G' : SimpleGraph V'} (f : V → V')
    (hf : Function.Injective f) (hE : ∀ e ∈ G.edgeSet, e.map f ∈ G'.edgeSet) (P : GPath G)
    {x : V'} (hx : ∀ v, f v ≠ x) : (P.mapInj f hf hE).endsAt x = 0 := by
  simp [GPath.endsAt, GPath.mapInj, hx]

omit [DecidableEq V] [DecidableEq V'] in
theorem flatMap_mapInj {G : SimpleGraph V} {G' : SimpleGraph V'} (f : V → V')
    (hf : Function.Injective f) (hE : ∀ e ∈ G.edgeSet, e.map f ∈ G'.edgeSet)
    (L : List (GPath G)) :
    (L.map (GPath.mapInj f hf hE)).flatMap GPath.edges =
      (L.flatMap GPath.edges).map (Sym2.map f) := by
  induction L with
  | nil => simp
  | cons P L ih => simp [ih]

/-- A decomposition pushed along an injective map onto a graph whose edges are exactly the
images. -/
def PathDecomp.mapInj {G : SimpleGraph V} {G' : SimpleGraph V'} (D : PathDecomp G) (f : V → V')
    (hf : Function.Injective f) (hE : ∀ e ∈ G.edgeSet, e.map f ∈ G'.edgeSet)
    (hcov : ∀ e' ∈ G'.edgeSet, ∃ e ∈ G.edgeSet, e.map f = e') : PathDecomp G' where
  paths := D.paths.map (GPath.mapInj f hf hE)
  nodup_edges := by
    rw [flatMap_mapInj]
    exact D.nodup_edges.map (Sym2.map.injective hf)
  covers := by
    intro e'
    rw [flatMap_mapInj, List.mem_map]
    constructor
    · intro he'
      obtain ⟨e, he, rfl⟩ := hcov e' he'
      exact ⟨e, (D.covers e).1 he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact hE e ((D.covers e).2 he)

omit [DecidableEq V] [DecidableEq V'] in
@[simp] theorem PathDecomp.mapInj_size {G : SimpleGraph V} {G' : SimpleGraph V'}
    (D : PathDecomp G) (f : V → V') (hf : Function.Injective f)
    (hE : ∀ e ∈ G.edgeSet, e.map f ∈ G'.edgeSet)
    (hcov : ∀ e' ∈ G'.edgeSet, ∃ e ∈ G.edgeSet, e.map f = e') :
    (D.mapInj f hf hE hcov).size = D.size := by
  simp [PathDecomp.mapInj, PathDecomp.size]

theorem PathDecomp.mapInj_ends {G : SimpleGraph V} {G' : SimpleGraph V'} (D : PathDecomp G)
    (f : V → V') (hf : Function.Injective f) (hE : ∀ e ∈ G.edgeSet, e.map f ∈ G'.edgeSet)
    (hcov : ∀ e' ∈ G'.edgeSet, ∃ e ∈ G.edgeSet, e.map f = e') (x : V) :
    (D.mapInj f hf hE hcov).ends (f x) = D.ends x := by
  simp only [PathDecomp.ends, PathDecomp.mapInj, List.map_map]
  congr 1
  apply List.map_congr_left
  intro P _
  exact GPath.mapInj_endsAt f hf hE P x

omit [DecidableEq V] in
theorem PathDecomp.mapInj_ends_out {G : SimpleGraph V} {G' : SimpleGraph V'} (D : PathDecomp G)
    (f : V → V') (hf : Function.Injective f) (hE : ∀ e ∈ G.edgeSet, e.map f ∈ G'.edgeSet)
    (hcov : ∀ e' ∈ G'.edgeSet, ∃ e ∈ G.edgeSet, e.map f = e') {x : V'} (hx : ∀ v, f v ≠ x) :
    (D.mapInj f hf hE hcov).ends x = 0 := by
  simp only [PathDecomp.ends, PathDecomp.mapInj, List.map_map]
  apply List.sum_eq_zero
  intro n hn
  obtain ⟨P, -, rfl⟩ := List.mem_map.mp hn
  exact GPath.mapInj_endsAt_out f hf hE P hx

end transport

section induce

variable {V : Type u} [Fintype V] [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj]
variable {s : Set V} [DecidablePred (· ∈ s)]

omit [Fintype V] [DecidableEq V] [DecidableRel H.Adj] [DecidablePred (· ∈ s)] in
theorem induce_edge_map (_hs : ∀ a b, H.Adj a b → a ∈ s) :
    ∀ e ∈ (H.induce s).edgeSet, e.map Subtype.val ∈ H.edgeSet := by
  intro e he
  induction e using Sym2.inductionOn with
  | hf a b => simpa using he

omit [Fintype V] [DecidableEq V] [DecidableRel H.Adj] [DecidablePred (· ∈ s)] in
theorem induce_edge_cov (hs : ∀ a b, H.Adj a b → a ∈ s) :
    ∀ e' ∈ H.edgeSet, ∃ e ∈ (H.induce s).edgeSet, e.map Subtype.val = e' := by
  intro e' he'
  induction e' using Sym2.inductionOn with
  | hf a b =>
    have ha := hs a b he'
    have hb := hs b a he'.symm
    exact ⟨s(⟨a, ha⟩, ⟨b, hb⟩), by simpa using he', rfl⟩

omit [DecidableEq V] in
theorem degree_induce_of_closed (hs : ∀ a b, H.Adj a b → a ∈ s) (v : s) :
    (H.induce s).degree v = H.degree v.1 := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
    ← Finset.card_map (Function.Embedding.subtype (· ∈ s))]
  congr 1
  ext x
  simp only [Finset.mem_map, mem_neighborFinset, Function.Embedding.subtype_apply, comap_adj]
  constructor
  · rintro ⟨w, hw, rfl⟩; exact hw
  · intro h; exact ⟨⟨x, hs x v.1 h.symm⟩, h, rfl⟩

omit [DecidableEq V] [DecidablePred (· ∈ s)] in
theorem degree_eq_zero_of_not_mem (hs : ∀ a b, H.Adj a b → a ∈ s) {x : V}
    (hx : x ∉ s) : H.degree x = 0 := by
  rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro b hb
  exact hx (hs x b ((mem_neighborFinset _ _ _).mp hb))

omit [DecidableEq V] in
theorem mem_evenSet_induce (hs : ∀ a b, H.Adj a b → a ∈ s) (v : s) :
    v ∈ evenSet (H.induce s) ↔ v.1 ∈ evenSet H := by
  rw [mem_evenSet_iff_even, mem_evenSet_iff_even, degree_induce_of_closed hs]

theorem evenSet_induce_map (hs : ∀ a b, H.Adj a b → a ∈ s) :
    (evenSet (H.induce s)).map (Function.Embedding.subtype (· ∈ s)) = evenSet H := by
  ext x
  simp only [Finset.mem_map, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact (mem_evenSet_induce hs v).1 hv
  · intro hx
    have hxs : x ∈ s := by
      by_contra h
      have := (mem_evenSet_iff_even.mp hx).1
      rw [degree_eq_zero_of_not_mem hs h] at this
      exact absurd this (lt_irrefl 0)
    exact ⟨⟨x, hxs⟩, (mem_evenSet_induce hs ⟨x, hxs⟩).2 hx, rfl⟩

/-- Realisable sets of `H.induce s` transport to `H` when `s` contains every edge of `H`. -/
theorem realisable_of_induce (hs : ∀ a b, H.Adj a b → a ∈ s) {S : Finset s}
    (hS : Realisable (H.induce s) S) :
    Realisable H (S.map (Function.Embedding.subtype (· ∈ s))) := by
  obtain ⟨hSE, D, hD⟩ := hS
  let D' := D.mapInj Subtype.val Subtype.val_injective (induce_edge_map hs)
    (induce_edge_cov hs)
  refine ⟨?_, D', fun x => ?_⟩
  · intro x hx
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact (mem_evenSet_induce hs v).1 (hSE hv)
  by_cases hx : x ∈ s
  · have := PathDecomp.mapInj_ends D Subtype.val Subtype.val_injective (induce_edge_map hs)
      (induce_edge_cov hs) ⟨x, hx⟩
    have hmem : x ∈ S.map (Function.Embedding.subtype (· ∈ s)) ↔ (⟨x, hx⟩ : s) ∈ S :=
      Finset.mem_map' (Function.Embedding.subtype (· ∈ s)) (a := ⟨x, hx⟩)
    change D'.ends (⟨x, hx⟩ : s).1 = _
    rw [this, hD]
    unfold profile
    rw [degree_induce_of_closed hs]
    simp only [hmem]
  · rw [PathDecomp.mapInj_ends_out D Subtype.val Subtype.val_injective (induce_edge_map hs)
      (induce_edge_cov hs) (fun v h => hx (by rw [← h]; exact v.2))]
    unfold profile
    rw [degree_eq_zero_of_not_mem hs hx]
    simp only [Nat.not_odd_zero, ite_false]
    rw [ite_eq_right]
    intro hmem
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hmem
    obtain ⟨v, -, rfl⟩ := hmem
    exact absurd v.2 hx

/-- Descent in `H.induce s` transports to `H` when `s` contains every edge of `H`. -/
theorem desc_of_induce (hs : ∀ a b, H.Adj a b → a ∈ s) {k : ℕ} {y : s} {W₀ : Finset s}
    (h : Desc (H.induce s) k y W₀) :
    Desc H k y.1 (W₀.map (Function.Embedding.subtype (· ∈ s))) := by
  obtain ⟨R, hRE, hRc, hWR, hyR, hreal⟩ := h
  refine ⟨R.map (Function.Embedding.subtype (· ∈ s)), ?_, by simp [hRc], Finset.map_subset_map.mpr hWR,
    ?_, ?_⟩
  · rw [← evenSet_induce_map hs]; exact Finset.map_subset_map.mpr hRE
  · simp only [Finset.mem_map, Function.Embedding.coe_subtype, not_exists, not_and]
    intro v hv hvy
    exact hyR (Subtype.ext hvy ▸ hv)
  · have := realisable_of_induce hs hreal
    rwa [Finset.map_sdiff, evenSet_induce_map hs] at this

end induce

/-! ## Part 2: the statements `DStmt`, `BStmt` and their form on graphs with isolated vertices -/

/-- `D_j`: `j`-step descent at `(y, {w})` for all distinct even `y, w` in every connected graph of
even order with at least `2j` even vertices (all vertex types in universe `u`). -/
def DStmt (j : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
    H.Connected → Even (Fintype.card W) → 2 * j ≤ (evenSet H).card →
    ∀ y w, y ∈ evenSet H → w ∈ evenSet H → y ≠ w → Desc H j y {w}

/-- `B_j`: `D_j` restricted to vertices `y` with at least two even neighbours. -/
def BStmt (j : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
    H.Connected → Even (Fintype.card W) → 2 * j ≤ (evenSet H).card →
    ∀ y w, y ∈ evenSet H → w ∈ evenSet H → y ≠ w →
    (∃ v₁ ∈ evenSet H, ∃ v₂ ∈ evenSet H, v₁ ≠ v₂ ∧ H.Adj y v₁ ∧ H.Adj y v₂) → Desc H j y {w}

section general

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The non-isolated vertices. -/
def nonIso (H : SimpleGraph V) [DecidableRel H.Adj] : Finset V :=
  Finset.univ.filter (fun v => 0 < H.degree v)

/-- `H` is connected on its non-isolated vertices. -/
def NIConn (H : SimpleGraph V) [DecidableRel H.Adj] : Prop :=
  ∀ a b, 0 < H.degree a → 0 < H.degree b → H.Reachable a b

omit [Fintype V] [DecidableEq V] in
theorem walk_support_pos {H : SimpleGraph V} [DecidableRel H.Adj] [Fintype V] {a b : V}
    (p : H.Walk a b) (ha : 0 < H.degree a) : ∀ x ∈ p.support, 0 < H.degree x := by
  induction p with
  | nil => intro x hx; rw [Walk.support_nil, List.mem_singleton] at hx; exact hx ▸ ha
  | @cons a c b h q ih =>
    intro x hx
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ha
    · exact ih (by rw [degree_pos_iff_exists_adj]; exact ⟨a, h.symm⟩) x hx

variable {H : SimpleGraph V} [DecidableRel H.Adj]

theorem induce_nonIso_connected (hconn : NIConn H) {y : V} (hy : 0 < H.degree y) :
    (H.induce {v | 0 < H.degree v}).Connected := by
  have : Nonempty {v | 0 < H.degree v} := ⟨⟨y, hy⟩⟩
  refine ⟨fun a b => ?_⟩
  obtain ⟨p⟩ := hconn a.1 b.1 a.2 b.2
  exact ⟨Walk.induce {v | 0 < H.degree v} p (walk_support_pos p a.2)⟩

/-- Conversion: `DStmt j` gives descent on a graph that may have isolated vertices. -/
theorem desc_of_dstmt {j : ℕ} (hD : DStmt.{u} j) (hconn : NIConn H) (hev : Even (nonIso H).card)
    (h2j : 2 * j ≤ (evenSet H).card) {y w : V} (hy : y ∈ evenSet H) (hw : w ∈ evenSet H)
    (hyw : y ≠ w) : Desc H j y {w} := by
  have hs : ∀ a b, H.Adj a b → a ∈ {v | 0 < H.degree v} := fun a b h => by
    simp only [Set.mem_ofPred_eq]; rw [degree_pos_iff_exists_adj]; exact ⟨b, h⟩
  have hy' : y ∈ {v | 0 < H.degree v} := (mem_evenSet_iff_even.mp hy).1
  have hw' : w ∈ {v | 0 < H.degree v} := (mem_evenSet_iff_even.mp hw).1
  have hcard : Fintype.card {v | 0 < H.degree v} = (nonIso H).card := by
    rw [Fintype.card_subtype]; rfl
  have hEv : (evenSet (H.induce {v | 0 < H.degree v})).card = (evenSet H).card := by
    rw [← evenSet_induce_map hs, Finset.card_map]
  have h := hD _ (H.induce {v | 0 < H.degree v}) (induce_nonIso_connected hconn hy')
    (hcard ▸ hev) (hEv ▸ h2j) ⟨y, hy'⟩ ⟨w, hw'⟩ ((mem_evenSet_induce hs _).2 hy)
    ((mem_evenSet_induce hs _).2 hw) (fun h => hyw (congrArg Subtype.val h))
  have := desc_of_induce hs h
  simpa using this

/-- Conversion: `BStmt j` gives descent on a graph that may have isolated vertices. -/
theorem desc_of_bstmt {j : ℕ} (hB : BStmt.{u} j) (hconn : NIConn H) (hev : Even (nonIso H).card)
    (h2j : 2 * j ≤ (evenSet H).card) {y w : V} (hy : y ∈ evenSet H) (hw : w ∈ evenSet H)
    (hyw : y ≠ w)
    (h2 : ∃ v₁ ∈ evenSet H, ∃ v₂ ∈ evenSet H, v₁ ≠ v₂ ∧ H.Adj y v₁ ∧ H.Adj y v₂) :
    Desc H j y {w} := by
  have hs : ∀ a b, H.Adj a b → a ∈ {v | 0 < H.degree v} := fun a b h => by
    simp only [Set.mem_ofPred_eq]; rw [degree_pos_iff_exists_adj]; exact ⟨b, h⟩
  have hy' : y ∈ {v | 0 < H.degree v} := (mem_evenSet_iff_even.mp hy).1
  have hw' : w ∈ {v | 0 < H.degree v} := (mem_evenSet_iff_even.mp hw).1
  have hcard : Fintype.card {v | 0 < H.degree v} = (nonIso H).card := by
    rw [Fintype.card_subtype]; rfl
  have hEv : (evenSet (H.induce {v | 0 < H.degree v})).card = (evenSet H).card := by
    rw [← evenSet_induce_map hs, Finset.card_map]
  obtain ⟨v₁, hv₁, v₂, hv₂, h12, ha₁, ha₂⟩ := h2
  have hv₁' : v₁ ∈ {v | 0 < H.degree v} := (mem_evenSet_iff_even.mp hv₁).1
  have hv₂' : v₂ ∈ {v | 0 < H.degree v} := (mem_evenSet_iff_even.mp hv₂).1
  have h := hB _ (H.induce {v | 0 < H.degree v}) (induce_nonIso_connected hconn hy')
    (hcard ▸ hev) (hEv ▸ h2j) ⟨y, hy'⟩ ⟨w, hw'⟩ ((mem_evenSet_induce hs _).2 hy)
    ((mem_evenSet_induce hs _).2 hw) (fun h => hyw (congrArg Subtype.val h))
    ⟨⟨v₁, hv₁'⟩, (mem_evenSet_induce hs _).2 hv₁, ⟨v₂, hv₂'⟩, (mem_evenSet_induce hs _).2 hv₂,
      fun h => h12 (congrArg Subtype.val h), ha₁, ha₂⟩
  have := desc_of_induce hs h
  simpa using this

end general

/-! ## Part 3: union, erasing a path, and the two bridge gluings -/

section glue

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Union** of decompositions of two edge-disjoint graphs. Every path of either decomposition
survives (as a path of the union with the same ends, support and edges). -/
theorem PathDecomp.exists_union {G₁ G₂ K : SimpleGraph V} (D₁ : PathDecomp G₁)
    (D₂ : PathDecomp G₂) (hdisj : ∀ e, e ∈ G₁.edgeSet → e ∉ G₂.edgeSet)
    (hK : ∀ e, e ∈ K.edgeSet ↔ e ∈ G₁.edgeSet ∨ e ∈ G₂.edgeSet) :
    ∃ D : PathDecomp K, D.size = D₁.size + D₂.size ∧ (∀ v, D.ends v = D₁.ends v + D₂.ends v) ∧
      (∀ P ∈ D₁.paths, ∃ Q ∈ D.paths, Q.src = P.src ∧ Q.tgt = P.tgt ∧
        Q.walk.support = P.walk.support ∧ Q.edges = P.edges) ∧
      (∀ P ∈ D₂.paths, ∃ Q ∈ D.paths, Q.src = P.src ∧ Q.tgt = P.tgt ∧
        Q.walk.support = P.walk.support ∧ Q.edges = P.edges) := by
  have H₁ : ∀ Q ∈ D₁.paths, ∀ e ∈ Q.edges, e ∈ K.edgeSet := fun Q hQ e he =>
    (hK e).2 (Or.inl ((D₁.covers e).2 (List.mem_flatMap.mpr ⟨Q, hQ, he⟩)))
  have H₂ : ∀ Q ∈ D₂.paths, ∀ e ∈ Q.edges, e ∈ K.edgeSet := fun Q hQ e he =>
    (hK e).2 (Or.inr ((D₂.covers e).2 (List.mem_flatMap.mpr ⟨Q, hQ, he⟩)))
  let L₁ := D₁.paths.pmap (fun Q hQ => Q.transfer hQ) H₁
  let L₂ := D₂.paths.pmap (fun Q hQ => Q.transfer hQ) H₂
  have hflat : (L₁ ++ L₂).flatMap GPath.edges =
      D₁.paths.flatMap GPath.edges ++ D₂.paths.flatMap GPath.edges := by
    rw [List.flatMap_append, flatMap_pmap_transfer, flatMap_pmap_transfer]
  let D : PathDecomp K :=
    { paths := L₁ ++ L₂
      nodup_edges := by
        rw [hflat, List.nodup_append]
        refine ⟨D₁.nodup_edges, D₂.nodup_edges, ?_⟩
        intro a ha b hb hab
        subst hab
        exact hdisj a ((D₁.covers a).2 ha) ((D₂.covers a).2 hb)
      covers := by
        intro e
        rw [hflat, List.mem_append, hK, D₁.covers, D₂.covers] }
  refine ⟨D, by simp [D, PathDecomp.size, L₁, L₂], fun v => ?_, ?_, ?_⟩
  · simp only [PathDecomp.ends, D, List.map_append, List.sum_append, L₁, L₂,
      sum_endsAt_pmap_transfer]
  · intro P hP
    refine ⟨P.transfer (H₁ P hP), List.mem_append_left _ ?_, rfl, rfl,
      by simp [GPath.transfer], by simp⟩
    exact List.mem_pmap.mpr ⟨P, hP, rfl⟩
  · intro P hP
    refine ⟨P.transfer (H₂ P hP), List.mem_append_right _ ?_, rfl, rfl,
      by simp [GPath.transfer], by simp⟩
    exact List.mem_pmap.mpr ⟨P, hP, rfl⟩

/-- **Erasing a path**: the other paths decompose the graph without its edges. -/
theorem PathDecomp.exists_erase {K K' : SimpleGraph V} (D : PathDecomp K) {P : GPath K}
    (hP : P ∈ D.paths) (hK' : ∀ e, e ∈ K'.edgeSet ↔ e ∈ K.edgeSet ∧ e ∉ P.edges) :
    ∃ D' : PathDecomp K', D'.size + 1 = D.size ∧ (∀ v, D'.ends v + P.endsAt v = D.ends v) := by
  obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hP
  have hnd := D.nodup_edges
  rw [hl, List.flatMap_append, List.flatMap_cons] at hnd
  have hnd' := List.nodup_append.mp hnd
  have hnd'' := List.nodup_append.mp hnd'.2.1
  -- disjointness facts
  have h1P : ∀ e ∈ l₁.flatMap GPath.edges, e ∉ P.edges := fun e he hPe =>
    hnd'.2.2 e he e (List.mem_append_left _ hPe) rfl
  have h2P : ∀ e ∈ l₂.flatMap GPath.edges, e ∉ P.edges := fun e he hPe =>
    hnd''.2.2 e hPe e he rfl
  have hmemK : ∀ e, e ∈ K.edgeSet ↔
      e ∈ l₁.flatMap GPath.edges ∨ e ∈ P.edges ∨ e ∈ l₂.flatMap GPath.edges := by
    intro e
    rw [D.covers, hl, List.flatMap_append, List.flatMap_cons, List.mem_append, List.mem_append]
  have H : ∀ Q ∈ l₁ ++ l₂, ∀ e ∈ Q.edges, e ∈ K'.edgeSet := by
    intro Q hQ e he
    rcases List.mem_append.mp hQ with hQ | hQ
    · have hm : e ∈ l₁.flatMap GPath.edges := List.mem_flatMap.mpr ⟨Q, hQ, he⟩
      exact (hK' e).2 ⟨(hmemK e).2 (Or.inl hm), h1P e hm⟩
    · have hm : e ∈ l₂.flatMap GPath.edges := List.mem_flatMap.mpr ⟨Q, hQ, he⟩
      exact (hK' e).2 ⟨(hmemK e).2 (Or.inr (Or.inr hm)), h2P e hm⟩
  let L := (l₁ ++ l₂).pmap (fun Q hQ => Q.transfer hQ) H
  let D' : PathDecomp K' :=
    { paths := L
      nodup_edges := by
        rw [flatMap_pmap_transfer, List.flatMap_append, List.nodup_append]
        refine ⟨hnd'.1, hnd''.2.1, ?_⟩
        intro a ha b hb hab
        exact hnd'.2.2 a ha b (List.mem_append_right _ hb) hab
      covers := by
        intro e
        rw [flatMap_pmap_transfer, hK', hmemK, List.flatMap_append, List.mem_append]
        constructor
        · rintro ⟨h | h | h, h'⟩
          · exact Or.inl h
          · exact absurd h h'
          · exact Or.inr h
        · rintro (h | h)
          · exact ⟨Or.inl h, h1P e h⟩
          · exact ⟨Or.inr (Or.inr h), h2P e h⟩ }
  refine ⟨D', ?_, fun v => ?_⟩
  · simp only [D', PathDecomp.size, L, List.length_pmap, hl, List.length_append,
      List.length_cons]
    omega
  · simp only [PathDecomp.ends, D', L, sum_endsAt_pmap_transfer, hl, List.map_append,
      List.map_cons, List.sum_append, List.sum_cons]
    omega

/-- A vertex of a path all of whose path edges equal one edge is an end of the path. -/
theorem GPath.end_of_unique_edge {K : SimpleGraph V} (P : GPath K) {x : V} {e₀ : Sym2 V}
    (hx : x ∈ P.walk.support) (huniq : ∀ e ∈ P.edges, x ∈ e → e = e₀) :
    P.src = x ∨ P.tgt = x := by
  have hinc : P.incid x ≤ 1 := by
    unfold GPath.incid
    have hnd : (P.edges.filter (fun e => decide (x ∈ e))).Nodup :=
      P.isPath.isTrail.edges_nodup.filter _
    rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup hnd]
    calc _ ≤ ({e₀} : Finset (Sym2 V)).card := by
          apply Finset.card_le_card
          intro e he
          simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at he
          simp [huniq e he.1 he.2]
      _ = 1 := Finset.card_singleton _
  have h := P.incid_add_endsAt x
  simp only [hx, ite_true] at h
  have : 1 ≤ P.endsAt x := by omega
  unfold GPath.endsAt at this
  by_contra hne
  push Not at hne
  simp [hne.1, hne.2] at this

/-- The first step of a path from a vertex whose only neighbour is `z`. -/
theorem GPath.exists_first_step {K : SimpleGraph V} (Q : GPath K) {x z : V} (hx : Q.src = x)
    (huniq : ∀ c, K.Adj x c → c = z) :
    ∃ (b : V) (R : K.Walk z b), K.Adj x z ∧ Q.tgt = b ∧ Q.walk.support = x :: R.support ∧
      Q.edges = s(x, z) :: R.edges ∧ R.IsPath ∧ x ∉ R.support := by
  obtain ⟨src, tgt, walk, hpath, hpos⟩ := Q
  simp only at hx
  subst hx
  cases walk with
  | nil => exact absurd hpos (by simp)
  | cons h R =>
    obtain rfl := huniq _ h
    rw [Walk.cons_isPath_iff] at hpath
    exact ⟨tgt, R, h, rfl, rfl, rfl, hpath.1, hpath.2⟩

omit [Fintype V] [DecidableEq V] in
/-- A walk that starts in `C`, never visits `X`, and can only leave `C` through `X`, stays in
`C`. -/
theorem walk_support_subset {K : SimpleGraph V} {C X : Set V} {a b : V} (p : K.Walk a b)
    (ha : a ∈ C) (hstep : ∀ x c, K.Adj x c → x ∈ C → c ∉ X → c ∈ C)
    (hX : ∀ c ∈ p.support, c ∉ X) : ∀ c ∈ p.support, c ∈ C := by
  induction p with
  | nil => intro c hc; rw [Walk.support_nil, List.mem_singleton] at hc; exact hc ▸ ha
  | @cons a d b h q ih =>
    intro c hc
    rw [Walk.support_cons, List.mem_cons] at hc
    have hd : d ∈ C := hstep a d h ha (hX d (by simp))
    rcases hc with rfl | hc
    · exact ha
    · exact ih hd (fun c hc' => hX c (by simp [hc'])) c hc

/-- **Bridge gluing (1)**: concatenate the two paths through the shared bridge edge `yt`. Here
`GA` is the `y`-side plus the pendant edge `yt` and `GB` the `t`-side plus `yt`. -/
theorem glue_bridge {GA GB G : SimpleGraph V} (DA : PathDecomp GA) (DB : PathDecomp GB)
    {y t : V} {A B : Set V} (hyA : y ∈ A) (htB : t ∈ B) (hAB : ∀ x, x ∈ A → x ∉ B)
    (hGAyt : GA.Adj y t) (hGByt : GB.Adj y t)
    (hGA : ∀ a b, GA.Adj a b → s(a, b) ≠ s(y, t) → a ∈ A ∧ b ∈ A)
    (hGB : ∀ a b, GB.Adj a b → s(a, b) ≠ s(y, t) → a ∈ B ∧ b ∈ B)
    (hG : ∀ e, e ∈ G.edgeSet ↔ e ∈ GA.edgeSet ∨ e ∈ GB.edgeSet) :
    ∃ D : PathDecomp G, D.size + 1 = DA.size + DB.size ∧
      ∀ v, D.ends v + (if t = v then 1 else 0) + (if y = v then 1 else 0) =
        DA.ends v + DB.ends v := by
  have htA : t ∉ A := fun h => hAB t h htB
  have hyB : y ∉ B := fun h => hAB y hyA h
  have hyt : y ≠ t := hGAyt.ne
  -- the two paths through `yt`
  obtain ⟨QA, hQA, hytA⟩ := List.mem_flatMap.mp ((DA.covers s(y, t)).1 hGAyt)
  obtain ⟨QB, hQB, hytB⟩ := List.mem_flatMap.mp ((DB.covers s(y, t)).1 hGByt)
  -- `t` is an end of `QA`, `y` an end of `QB`
  have hAuniq : ∀ c, GA.Adj t c → c = y := by
    intro c h
    by_contra hc
    have := hGA t c h (by
      intro he; rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact hyt h1.symm
      · exact hc h2)
    exact htA this.1
  have hBuniq : ∀ c, GB.Adj y c → c = t := by
    intro c h
    by_contra hc
    have := hGB y c h (by
      intro he; rcases Sym2.eq_iff.mp he with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact hc h2
      · exact hyt h1)
    exact hyB this.1
  have hendA : QA.src = t ∨ QA.tgt = t := by
    refine QA.end_of_unique_edge (e₀ := s(y, t))
      (QA.walk.snd_mem_support_of_mem_edges hytA) ?_
    intro e he hte
    induction e using Sym2.inductionOn with
    | hf a b =>
      have hadj : GA.Adj a b := QA.walk.edges_subset_edgeSet he
      rcases Sym2.mem_iff.mp hte with rfl | rfl
      · obtain rfl := hAuniq b hadj; exact Sym2.eq_swap
      · obtain rfl := hAuniq a hadj.symm; rfl
  have hendB : QB.src = y ∨ QB.tgt = y := by
    refine QB.end_of_unique_edge (e₀ := s(y, t))
      (QB.walk.fst_mem_support_of_mem_edges hytB) ?_
    intro e he hye
    induction e using Sym2.inductionOn with
    | hf a b =>
      have hadj : GB.Adj a b := QB.walk.edges_subset_edgeSet he
      rcases Sym2.mem_iff.mp hye with rfl | rfl
      · obtain rfl := hBuniq b hadj; rfl
      · obtain rfl := hBuniq a hadj.symm; exact Sym2.eq_swap
  obtain ⟨QA', hQA's, hQA'perm, hQA'ends, hQA'supp⟩ := QA.exists_orient hendA
  obtain ⟨QB', hQB's, hQB'perm, hQB'ends, hQB'supp⟩ := QB.exists_orient hendB
  obtain ⟨a, RA, hty, hQA't, hQA'support, hQA'edges, hRA, htRA⟩ :=
    QA'.exists_first_step hQA's hAuniq
  obtain ⟨b, RB, hyt', hQB't, hQB'support, hQB'edges, hRB, hyRB⟩ :=
    QB'.exists_first_step hQB's hBuniq
  -- supports
  have hRAA : ∀ c ∈ RA.support, c ∈ A := walk_support_subset RA hyA (X := {t})
    (fun x c h hx hc => by
      refine (hGA x c h ?_).2
      intro he; rcases Sym2.eq_iff.mp he with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact hc h2
      · exact htA (h1 ▸ hx))
    (fun c hc hct => htRA (by rw [Set.mem_singleton_iff] at hct; exact hct ▸ hc))
  have hRBB : ∀ c ∈ RB.support, c ∈ B := walk_support_subset RB htB (X := {y})
    (fun x c h hx hc => by
      refine (hGB x c h ?_).2
      intro he; rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact hyB (h1 ▸ hx)
      · exact hc h2)
    (fun c hc hcy => hyRB (by rw [Set.mem_singleton_iff] at hcy; exact hcy ▸ hc))
  -- the glued path
  have hRAG : ∀ e ∈ RA.edges, e ∈ G.edgeSet := fun e he =>
    (hG e).2 (Or.inl (RA.edges_subset_edgeSet he))
  have hRBG : ∀ e ∈ RB.edges, e ∈ G.edgeSet := fun e he =>
    (hG e).2 (Or.inr (RB.edges_subset_edgeSet he))
  have hytG : G.Adj y t := by
    rw [← mem_edgeSet, hG]; exact Or.inl hGAyt
  let W : G.Walk a b := (RA.transfer G hRAG).reverse.append (Walk.cons hytG (RB.transfer G hRBG))
  have hWpath : W.IsPath := by
    rw [Walk.isPath_def]
    simp only [W, Walk.support_append, Walk.support_reverse, Walk.support_cons,
      Walk.support_transfer, List.tail_cons]
    rw [List.nodup_append]
    refine ⟨List.nodup_reverse.mpr hRA.support_nodup, hRB.support_nodup, ?_⟩
    intro c hc d hd hcd
    subst hcd
    rw [List.mem_reverse] at hc
    exact hAB c (hRAA c hc) (hRBB c hd)
  have hWedges : W.edges = RA.edges.reverse ++ s(y, t) :: RB.edges := by
    simp [W, Walk.edges_append, Walk.edges_reverse, Walk.edges_transfer]
  let P' : GPath G := ⟨a, b, W, hWpath, by
    simp only [W, Walk.length_append, Walk.length_reverse, Walk.length_cons]; omega⟩
  -- erase `QB`, take the union with `DA`, and replace `QA` by the glued path
  obtain ⟨DB', hDB'size, hDB'ends⟩ := DB.exists_erase (K' := GB.deleteEdges {e | e ∈ QB.edges})
    hQB (fun e => by simp [edgeSet_deleteEdges])
  have hRBe : ∀ e ∈ RB.edges, e ∈ QB.edges := fun e he =>
    hQB'perm.mem_iff.mp (by rw [hQB'edges]; exact List.mem_cons_of_mem _ he)
  have hytRB : s(y, t) ∉ RB.edges := by
    have := hQB'perm.nodup_iff.mpr QB.isPath.isTrail.edges_nodup
    rw [hQB'edges] at this
    exact (List.nodup_cons.mp this).1
  have hGAinside : ∀ e ∈ GA.edgeSet, e ≠ s(y, t) → ∀ c ∈ e, c ∈ A := by
    intro e he hne c hc
    induction e using Sym2.inductionOn with
    | hf p q =>
      have := hGA p q he hne
      rcases Sym2.mem_iff.mp hc with rfl | rfl
      · exact this.1
      · exact this.2
  have hGBinside : ∀ e ∈ GB.edgeSet, e ≠ s(y, t) → ∀ c ∈ e, c ∈ B := by
    intro e he hne c hc
    induction e using Sym2.inductionOn with
    | hf p q =>
      have := hGB p q he hne
      rcases Sym2.mem_iff.mp hc with rfl | rfl
      · exact this.1
      · exact this.2
  obtain ⟨D₀, hD₀size, hD₀ends, hD₀A, -⟩ := PathDecomp.exists_union (K := G.deleteEdges
      {e | e ∈ RB.edges}) DA DB'
    (by
      intro e heA heB
      simp only [edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_ofPred_eq] at heB
      have hne : e ≠ s(y, t) := fun h => heB.2 (h ▸ hytB)
      obtain ⟨c, hc⟩ : ∃ c, c ∈ e := ⟨e.out.1, Sym2.out_fst_mem e⟩
      exact hAB c (hGAinside e heA hne c hc) (hGBinside e heB.1 hne c hc))
    (by
      intro e
      simp only [edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_ofPred_eq]
      rw [hG]
      constructor
      · rintro ⟨hA | hB, hR⟩
        · exact Or.inl hA
        · by_cases hQ : e ∈ QB.edges
          · left
            have hQ' := hQB'perm.mem_iff.mpr hQ
            rw [hQB'edges, List.mem_cons] at hQ'
            rcases hQ' with rfl | h
            · exact hGAyt
            · exact absurd h hR
          · exact Or.inr ⟨hB, hQ⟩
      · rintro (hA | ⟨hB, hQ⟩)
        · refine ⟨Or.inl hA, fun hR => ?_⟩
          have hne : e ≠ s(y, t) := fun h => hytRB (h ▸ hR)
          obtain ⟨c, hc⟩ : ∃ c, c ∈ e := ⟨e.out.1, Sym2.out_fst_mem e⟩
          exact hAB c (hGAinside e hA hne c hc)
            (hGBinside e (RB.edges_subset_edgeSet hR) hne c hc)
        · exact ⟨Or.inr hB, fun hR => hQ (hRBe e hR)⟩)
  obtain ⟨Q₀, hQ₀, hQ₀s, hQ₀t, -, hQ₀e⟩ := hD₀A QA hQA
  have hQAe : ∀ e, e ∈ QA.edges ↔ e = s(y, t) ∨ e ∈ RA.edges := by
    intro e
    rw [← hQA'perm.mem_iff, hQA'edges, List.mem_cons, Sym2.eq_swap]
  obtain ⟨D, hDsize, -, hDends, -⟩ := D₀.replace hQ₀ P'
    (by
      intro e
      simp only [edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_ofPred_eq, hQ₀e]
      change e ∈ G.edgeSet ↔ _ ∨ e ∈ W.edges
      rw [hWedges, List.mem_append, List.mem_reverse, List.mem_cons]
      constructor
      · intro he
        by_cases hR : e ∈ RB.edges
        · exact Or.inr (Or.inr (Or.inr hR))
        · by_cases hQ : e ∈ QA.edges
          · rcases (hQAe e).1 hQ with h | h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inl h)
          · exact Or.inl ⟨⟨he, hR⟩, hQ⟩
      · rintro (⟨⟨he, -⟩, -⟩ | h | rfl | h)
        · exact he
        · exact hRAG e h
        · exact hytG
        · exact hRBG e h)
    (by
      intro e he
      change e ∈ W.edges at he
      rw [hWedges, List.mem_append, List.mem_reverse, List.mem_cons] at he
      rw [hQ₀e]
      rcases he with h | rfl | h
      · exact Or.inl ((hQAe e).2 (Or.inr h))
      · exact Or.inl ((hQAe _).2 (Or.inl rfl))
      · right
        simp only [edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_ofPred_eq, not_and, not_not]
        exact fun _ => h)
  refine ⟨D, by omega, fun v => ?_⟩
  have h1 := hDends v
  have h2 := hD₀ends v
  have h3 := hDB'ends v
  have hQ₀ends : Q₀.endsAt v = QA.endsAt v := by simp [GPath.endsAt, hQ₀s, hQ₀t]
  rw [hQ₀ends, ← hQA'ends v] at h1
  rw [← hQB'ends v] at h3
  simp only [GPath.endsAt, hQA's, hQA't, hQB's, hQB't, P'] at h1 h3
  split_ifs at h1 h3 ⊢ <;> omega

/-- **Bridge gluing (2)**: realisations of the two sides of `G − yt` glue by extending a path
of the `t`-side that ends at `t` with the edge `ty`. -/
theorem glue_append {GA GB K G : SimpleGraph V} (DA : PathDecomp GA) (DB : PathDecomp GB)
    {y t : V} (hdisj : ∀ e, e ∈ GA.edgeSet → e ∉ GB.edgeSet)
    (hK : ∀ e, e ∈ K.edgeSet ↔ e ∈ GA.edgeSet ∨ e ∈ GB.edgeSet)
    (hG : ∀ e, e ∈ G.edgeSet ↔ e ∈ K.edgeSet ∨ e = s(t, y)) (hKty : ¬ K.Adj t y)
    (hBy : ∀ P ∈ DB.paths, y ∉ P.walk.support) (ht : 0 < DB.ends t) :
    ∃ D : PathDecomp G, D.size = DA.size + DB.size ∧
      ∀ v, D.ends v + (if t = v then 1 else 0) = DA.ends v + DB.ends v + (if y = v then 1 else 0) := by
  obtain ⟨D₀, hD₀size, hD₀ends, -, hD₀B⟩ := PathDecomp.exists_union DA DB hdisj hK
  obtain ⟨P, hP, hPt⟩ : ∃ P ∈ DB.paths, 0 < P.endsAt t := by
    by_contra h
    push Not at h
    have : DB.ends t = 0 := by
      unfold PathDecomp.ends
      apply List.sum_eq_zero
      intro n hn
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hn
      exact Nat.le_zero.mp (h Q hQ)
    omega
  obtain ⟨Q, hQ, hQs, hQt, hQsupp, -⟩ := hD₀B P hP
  have hend : Q.src = t ∨ Q.tgt = t := by
    unfold GPath.endsAt at hPt
    by_contra hne
    push Not at hne
    rw [hQs, hQt] at hne
    simp [hne.1, hne.2] at hPt
  obtain ⟨D, hDsize, hDends⟩ := D₀.append_move hKty hG hQ hend (by rw [hQsupp]; exact hBy P hP)
  exact ⟨D, by omega, fun v => by have := hDends v; rw [hD₀ends] at this; omega⟩

end glue

/-! ## Part 4: restricted graphs, pieces, and descent in a piece -/

/-- `D_j` for graphs with at most `N` edges. -/
def DStmtE (j N : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
    H.edgeFinset.card ≤ N → H.Connected → Even (Fintype.card W) → 2 * j ≤ (evenSet H).card →
    ∀ y w, y ∈ evenSet H → w ∈ evenSet H → y ≠ w → Desc H j y {w}

section restr

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The edges of `G` with both ends in `C`; the other vertices are isolated. -/
def restr (G : SimpleGraph V) (C : Finset V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ∈ C ∧ b ∈ C
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩

instance restr.decRel (C : Finset V) : DecidableRel (restr G C).Adj := fun a b =>
  inferInstanceAs (Decidable (G.Adj a b ∧ a ∈ C ∧ b ∈ C))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem restr_adj {C : Finset V} {a b : V} :
    (restr G C).Adj a b ↔ G.Adj a b ∧ a ∈ C ∧ b ∈ C := Iff.rfl

theorem degree_restr (C : Finset V) (v : V) : (restr G C).degree v =
    if v ∈ C then ((G.neighborFinset v).filter (· ∈ C)).card else 0 := by
  rw [← card_neighborFinset_eq_degree]
  split_ifs with hv
  · congr 1; ext b; simp [hv]
  · rw [Finset.card_eq_zero]; ext b; simp [hv]

theorem degree_restr_full {C : Finset V} {v : V} (hv : v ∈ C) (hN : ∀ b, G.Adj v b → b ∈ C) :
    (restr G C).degree v = G.degree v := by
  rw [degree_restr, ite_eq_left hv, Finset.filter_true_of_mem (fun b hb => hN b
    ((mem_neighborFinset _ _ _).mp hb)), card_neighborFinset_eq_degree]

theorem degree_restr_minus {C : Finset V} {v x : V} (hv : v ∈ C) (hx : G.Adj v x) (hxC : x ∉ C)
    (hN : ∀ b, G.Adj v b → b ≠ x → b ∈ C) : (restr G C).degree v + 1 = G.degree v := by
  rw [degree_restr, ite_eq_left hv, ← card_neighborFinset_eq_degree]
  have : (G.neighborFinset v).filter (· ∈ C) = (G.neighborFinset v).erase x := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_erase, mem_neighborFinset]
    constructor
    · rintro ⟨h, hb⟩; exact ⟨fun h' => hxC (h' ▸ hb), h⟩
    · rintro ⟨hbx, h⟩; exact ⟨h, hN b h hbx⟩
  rw [this, Finset.card_erase_of_mem ((mem_neighborFinset _ _ _).mpr hx)]
  have : 0 < (G.neighborFinset v).card := Finset.card_pos.mpr ⟨x, (mem_neighborFinset _ _ _).mpr hx⟩
  omega

theorem degree_restr_one {C : Finset V} {v x : V} (hv : v ∈ C) (hx : G.Adj v x) (hxC : x ∈ C)
    (hN : ∀ b, G.Adj v b → b ∈ C → b = x) : (restr G C).degree v = 1 := by
  rw [degree_restr, ite_eq_left hv, Finset.card_eq_one]
  refine ⟨x, ?_⟩
  ext b
  simp only [Finset.mem_filter, mem_neighborFinset, Finset.mem_singleton]
  constructor
  · rintro ⟨h, hb⟩; exact hN b h hb
  · rintro rfl; exact ⟨hx, hxC⟩

theorem degree_restr_out {C : Finset V} {v : V} (hv : v ∉ C) : (restr G C).degree v = 0 := by
  rw [degree_restr, ite_eq_right hv]

theorem restr_edge_le {C : Finset V} {e : Sym2 V} (he : e ∈ (restr G C).edgeSet) :
    e ∈ G.edgeSet := by
  induction e using Sym2.inductionOn with
  | hf a b => exact he.1

theorem card_edgeFinset_restr_lt {C : Finset V} {a b : V} (hab : G.Adj a b)
    (hnot : ¬ (a ∈ C ∧ b ∈ C)) :
    (restr G C).edgeFinset.card < G.edgeFinset.card := by
  apply Finset.card_lt_card
  refine ⟨fun e he => mem_edgeFinset.mpr (restr_edge_le (mem_edgeFinset.mp he)), fun h => ?_⟩
  have := h (mem_edgeFinset.mpr (show s(a, b) ∈ G.edgeSet from hab))
  exact hnot (mem_edgeFinset.mp this).2

/-- In a graph with an even number of non-isolated vertices, the number of even vertices is
even. -/
theorem even_card_evenSet_of_nonIso {H : SimpleGraph V} [DecidableRel H.Adj]
    (hev : Even (nonIso H).card) : Even (evenSet H).card := by
  have hsplit : nonIso H = evenSet H ∪ oddSet H := by
    ext v
    simp only [nonIso, evenSet, oddSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    constructor
    · intro h
      rcases Nat.even_or_odd (H.degree v) with he | ho
      · exact Or.inl ⟨h, he⟩
      · exact Or.inr ho
    · rintro (h | h)
      · exact h.1
      · exact h.pos
  have hdisj : Disjoint (evenSet H) (oddSet H) := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    exact (Nat.not_even_iff_odd.mpr (Finset.mem_filter.mp h2).2) (mem_evenSet_iff_even.mp h1).2
  rw [hsplit, Finset.card_union_of_disjoint hdisj] at hev
  obtain ⟨m, hm⟩ := H.even_card_odd_degree_vertices
  have : (oddSet H).card = m + m := hm
  rw [Nat.even_add] at hev
  exact hev.mpr ⟨m, this⟩

/-- Lemma 2 for graphs that may have isolated vertices. -/
theorem realisable_evenSet_ni (H : SimpleGraph V) [DecidableRel H.Adj] :
    Realisable H (evenSet H) := by
  have hs : ∀ a b, H.Adj a b → a ∈ {v | 0 < H.degree v} := fun a b h => by
    simp only [Set.mem_ofPred_eq]; rw [degree_pos_iff_exists_adj]; exact ⟨b, h⟩
  have h := realisable_of_induce hs (realisable_evenSet' (G := H.induce {v | 0 < H.degree v})
    (fun v => by rw [degree_induce_of_closed hs]; exact v.2))
  rwa [evenSet_induce_map hs] at h

theorem card_edgeFinset_induce_le {H : SimpleGraph V} [DecidableRel H.Adj] {s : Set V}
    [DecidablePred (· ∈ s)] (hs : ∀ a b, H.Adj a b → a ∈ s) :
    (H.induce s).edgeFinset.card ≤ H.edgeFinset.card := by
  apply Finset.card_le_card_of_injOn (Sym2.map Subtype.val)
  · intro e he
    exact mem_edgeFinset.mpr (induce_edge_map hs e (mem_edgeFinset.mp he))
  · intro a _ b _ h
    exact Sym2.map.injective Subtype.val_injective h

/-- Conversion for `DStmtE`. -/
theorem desc_of_dstmtE {j N : ℕ} (hD : DStmtE.{u} j N) {H : SimpleGraph V} [DecidableRel H.Adj]
    (hE : H.edgeFinset.card ≤ N) (hconn : NIConn H) (hev : Even (nonIso H).card)
    (h2j : 2 * j ≤ (evenSet H).card) {y w : V} (hy : y ∈ evenSet H) (hw : w ∈ evenSet H)
    (hyw : y ≠ w) : Desc H j y {w} := by
  have hs : ∀ a b, H.Adj a b → a ∈ {v | 0 < H.degree v} := fun a b h => by
    simp only [Set.mem_ofPred_eq]; rw [degree_pos_iff_exists_adj]; exact ⟨b, h⟩
  have hy' : y ∈ {v | 0 < H.degree v} := (mem_evenSet_iff_even.mp hy).1
  have hw' : w ∈ {v | 0 < H.degree v} := (mem_evenSet_iff_even.mp hw).1
  have hcard : Fintype.card {v | 0 < H.degree v} = (nonIso H).card := by
    rw [Fintype.card_subtype]; rfl
  have hEv : (evenSet (H.induce {v | 0 < H.degree v})).card = (evenSet H).card := by
    rw [← evenSet_induce_map hs, Finset.card_map]
  have h := hD _ (H.induce {v | 0 < H.degree v}) ((card_edgeFinset_induce_le hs).trans hE)
    (induce_nonIso_connected hconn hy') (hcard ▸ hev) (hEv ▸ h2j) ⟨y, hy'⟩ ⟨w, hw'⟩
    ((mem_evenSet_induce hs _).2 hy) ((mem_evenSet_induce hs _).2 hw)
    (fun h => hyw (congrArg Subtype.val h))
  have := desc_of_induce hs h
  simpa using this

/-- **Descent in a piece**: `r`-step descent in a graph with isolated vertices, keeping `kept`
(when it is even) and removing the at most one vertex of `W₀`, from the lower levels or from the
same level with fewer edges. -/
theorem piece_desc {P : SimpleGraph V} [DecidableRel P.Adj] {k M r : ℕ}
    (hlow : ∀ j, 1 ≤ j → j ≤ k → DStmt.{u} j) (hIH : DStmtE.{u} (k + 1) M)
    (hEP : P.edgeFinset.card ≤ M) (hr : r ≤ k + 1) (hconn : NIConn P)
    (hev : Even (nonIso P).card) (h2r : 2 * r ≤ (evenSet P).card) (kept : V) (W₀ : Finset V)
    (hW₀ : W₀ ⊆ evenSet P) (hW₀c : W₀.card ≤ 1) (hkW : kept ∉ W₀)
    (hW₀r : W₀.Nonempty → 1 ≤ r) :
    ∃ R ⊆ evenSet P, R.card = r ∧ W₀ ⊆ R ∧ kept ∉ R ∧ Realisable P (evenSet P \ R) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr1
  · have hW : W₀ = ∅ := by
      by_contra h
      have := hW₀r (Finset.nonempty_iff_ne_empty.mpr h)
      omega
    subst hW
    exact ⟨∅, Finset.empty_subset _, rfl, Finset.empty_subset _, by simp,
      by simpa using realisable_evenSet_ni P⟩
  have hdesc : ∀ y' w', y' ∈ evenSet P → w' ∈ evenSet P → y' ≠ w' → Desc P r y' {w'} := by
    intro y' w' hy' hw' hyw'
    by_cases hrk : r ≤ k
    · exact desc_of_dstmt (hlow r hr1 hrk) hconn hev h2r hy' hw' hyw'
    · have : r = k + 1 := by omega
      subst this
      exact desc_of_dstmtE hIH hEP hconn hev h2r hy' hw' hyw'
  have hE2 : 1 < (evenSet P).card := by omega
  -- choose the kept vertex `y'` and the prescribed vertex `w'`
  obtain ⟨y', w', hy', hw', hyw', hW₀w', hky'⟩ : ∃ y' w', y' ∈ evenSet P ∧ w' ∈ evenSet P ∧
      y' ≠ w' ∧ W₀ ⊆ {w'} ∧ (kept ∈ evenSet P → y' = kept) := by
    rcases Finset.eq_empty_or_nonempty W₀ with hW | ⟨w₀, hw₀⟩
    · subst hW
      by_cases hk : kept ∈ evenSet P
      · obtain ⟨w', hw', hw'k⟩ := Finset.exists_mem_ne hE2 kept
        exact ⟨kept, w', hk, hw', Ne.symm hw'k, Finset.empty_subset _, fun _ => rfl⟩
      · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hE2
        exact ⟨a, b, ha, hb, hab, Finset.empty_subset _, fun h => absurd h hk⟩
    · have hW : W₀ = {w₀} := by
        rw [Finset.eq_singleton_iff_unique_mem]
        refine ⟨hw₀, fun x hx => ?_⟩
        by_contra hne
        have := Finset.card_le_card (show {x, w₀} ⊆ W₀ by
          intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption)
        rw [Finset.card_pair hne] at this
        omega
      subst hW
      have hw₀E := hW₀ (Finset.mem_singleton_self w₀)
      by_cases hk : kept ∈ evenSet P
      · exact ⟨kept, w₀, hk, hw₀E, fun h => hkW (by simp [h]), le_rfl, fun _ => rfl⟩
      · obtain ⟨y', hy', hy'w⟩ := Finset.exists_mem_ne hE2 w₀
        exact ⟨y', w₀, hy', hw₀E, hy'w, le_rfl, fun h => absurd h hk⟩
  obtain ⟨R, hRE, hRc, hwR, hyR, hreal⟩ := hdesc y' w' hy' hw' hyw'
  refine ⟨R, hRE, hRc, hW₀w'.trans hwR, fun hkR => ?_, hreal⟩
  have hkE := hRE hkR
  exact hyR (hky' hkE ▸ hkR)

end restr

/-! ## Part 5: the bridge cases -/

section bridge

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem split_cap (T c₁ c₂ : ℕ) (h : T ≤ c₁ + c₂) (hc₁ : 1 ≤ c₁) (hT : 1 ≤ T) :
    ∃ r₁ r₂, r₁ + r₂ = T ∧ r₁ ≤ c₁ ∧ r₂ ≤ c₂ ∧ 1 ≤ r₁ := by
  by_cases h' : c₁ ≤ T
  · exact ⟨c₁, T - c₁, by omega, le_rfl, by omega, hc₁⟩
  · exact ⟨T, 0, by omega, by omega, by omega, hT⟩

theorem profile_zero_of_degree {H : SimpleGraph V} [DecidableRel H.Adj] {S : Finset V} {v : V}
    (hS : S ⊆ evenSet H) (hd : H.degree v = 0) : profile H S v = 0 := by
  have hv : v ∉ S := fun h => by
    have := (mem_evenSet_iff_even.mp (hS h)).1; omega
  unfold profile
  rw [hd]
  simp [hv]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem restr_walk_support {C : Finset V} {a b : V} (p : (restr G C).Walk a b)
    (hp : 0 < p.length) : ∀ x ∈ p.support, x ∈ C := by
  induction p with
  | nil => simp at hp
  | @cons a c b h q ih =>
    intro x hx
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h.2.1
    · cases q with
      | nil =>
        rw [Walk.support_nil, List.mem_singleton] at hx
        exact hx ▸ h.2.2
      | cons h' q' => exact ih (by simp) x hx

omit [Fintype V] [DecidableRel G.Adj] in
/-- Every vertex of a path of `restr G C` lies in `C`. -/
theorem restr_path_support {C : Finset V} (P : GPath (restr G C)) :
    ∀ x ∈ P.walk.support, x ∈ C :=
  restr_walk_support P.walk P.pos

/-- **Bridge case, odd side.** `yt` is a bridge, `A` the vertex set of the side of `y`, with
`|A|` odd. Descend in `A⁺ = G[A ∪ {t}]` keeping `y` and in `B⁺ = G[Aᶜ ∪ {y}]`, and glue. -/
theorem bridge_odd {k M : ℕ} (hlow : ∀ j, 1 ≤ j → j ≤ k → DStmt.{u} j)
    (hIH : DStmtE.{u} (k + 1) M) (hG : ∀ v, 0 < G.degree v) (hn : Even (Fintype.card V))
    (hEM : G.edgeFinset.card ≤ M + 1) (h2k : 2 * (k + 1) ≤ (evenSet G).card) {y w t : V}
    (hy : y ∈ evenSet G) (hw : w ∈ evenSet G) (hyw : y ≠ w) (hyt : G.Adj y t)
    (hdt : 2 ≤ G.degree t) {A : Finset V} (hyA : y ∈ A) (htA : t ∉ A)
    (hcross : ∀ a b, G.Adj a b → a ∈ A → b ∉ A → a = y ∧ b = t)
    (hreachA : ∀ v ∈ A, (restr G A).Reachable y v)
    (hreachB : ∀ v ∉ A, (restr G Aᶜ).Reachable t v) (hAodd : Odd A.card) :
    Desc G (k + 1) y {w} := by
  have hyt' : y ≠ t := hyt.ne
  have nbrA : ∀ v ∈ A, v ≠ y → ∀ b, G.Adj v b → b ∈ A := fun v hv hvy b h => by
    by_contra hb; exact hvy (hcross v b h hv hb).1
  have nbrB : ∀ v, v ∉ A → v ≠ t → ∀ b, G.Adj v b → b ∉ A := fun v hv hvt b h hb =>
    hvt (hcross b v h.symm hb hv).2
  have nbrY : ∀ b, G.Adj y b → b ≠ t → b ∈ A := fun b h hbt => by
    by_contra hb; exact hbt (hcross y b h hyA hb).2
  have nbrT : ∀ b, G.Adj t b → b ≠ y → b ∉ A := fun b h hby hb =>
    hby (hcross b t h.symm hb htA).1
  -- degrees in the pieces
  have dA_A : ∀ v ∈ A, (restr G (insert t A)).degree v = G.degree v := by
    intro v hv
    refine degree_restr_full (Finset.mem_insert_of_mem hv) (fun b h => ?_)
    by_cases hvy : v = y
    · subst hvy
      by_cases hbt : b = t
      · exact hbt ▸ Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (nbrY b h hbt)
    · exact Finset.mem_insert_of_mem (nbrA v hv hvy b h)
  have dA_t : (restr G (insert t A)).degree t = 1 := degree_restr_one (Finset.mem_insert_self _ _) hyt.symm
    (Finset.mem_insert_of_mem hyA) (fun b h hb => by
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact absurd h (G.loopless.irrefl _)
      · by_contra hby; exact nbrT b h hby hb)
  have dA_out : ∀ v, v ∉ A → v ≠ t → (restr G (insert t A)).degree v = 0 := fun v hv hvt =>
    degree_restr_out (by simp [hv, hvt])
  have dB_B : ∀ v, v ∉ A → (restr G (insert y Aᶜ)).degree v = G.degree v := by
    intro v hv
    refine degree_restr_full (Finset.mem_insert_of_mem (Finset.mem_compl.mpr hv))
      (fun b h => ?_)
    by_cases hvt : v = t
    · subst hvt
      by_cases hby : b = y
      · exact hby ▸ Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_compl.mpr (nbrT b h hby))
    · exact Finset.mem_insert_of_mem (Finset.mem_compl.mpr (nbrB v hv hvt b h))
  have dB_y : (restr G (insert y Aᶜ)).degree y = 1 := degree_restr_one (Finset.mem_insert_self _ _) hyt
    (Finset.mem_insert_of_mem (Finset.mem_compl.mpr htA)) (fun b h hb => by
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact absurd h (G.loopless.irrefl _)
      · by_contra hbt; exact Finset.mem_compl.mp hb (nbrY b h hbt))
  have dB_out : ∀ v ∈ A, v ≠ y → (restr G (insert y Aᶜ)).degree v = 0 := fun v hv hvy =>
    degree_restr_out (by simp [hv, hvy])
  -- even vertices of the pieces
  have EvA : evenSet (restr G (insert t A)) = (evenSet G).filter (· ∈ A) := by
    ext v
    simp only [Finset.mem_filter]
    by_cases hv : v ∈ A
    · rw [mem_evenSet_iff_even, mem_evenSet_iff_even, dA_A v hv]; simp [hv]
    · simp only [hv, and_false, iff_false]
      by_cases hvt : v = t
      · subst hvt; rw [mem_evenSet_iff_even, dA_t]; decide
      · rw [mem_evenSet_iff_even, dA_out v hv hvt]; simp
  have EvB : evenSet (restr G (insert y Aᶜ)) = (evenSet G).filter (· ∉ A) := by
    ext v
    simp only [Finset.mem_filter]
    by_cases hv : v ∈ A
    · simp only [hv, not_true_eq_false, and_false, iff_false]
      by_cases hvy : v = y
      · subst hvy; rw [mem_evenSet_iff_even, dB_y]; decide
      · rw [mem_evenSet_iff_even, dB_out v hv hvy]; simp
    · rw [mem_evenSet_iff_even, mem_evenSet_iff_even, dB_B v hv]; simp [hv]
  have hEvsum : (evenSet (restr G (insert t A))).card + (evenSet (restr G (insert y Aᶜ))).card = (evenSet G).card := by
    rw [EvA, EvB]; exact Finset.card_filter_add_card_filter_not (fun v => v ∈ A)
  -- non-isolated vertices, connectivity, parity
  have nonA : nonIso (restr G (insert t A)) = insert t A := by
    ext v
    simp only [nonIso, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hv : v ∈ A
    · rw [dA_A v hv]; simp [hv, hG v]
    · by_cases hvt : v = t
      · subst hvt; rw [dA_t]; simp
      · rw [dA_out v hv hvt]; simp [hv, hvt]
  have nonB : nonIso (restr G (insert y Aᶜ)) = insert y Aᶜ := by
    ext v
    simp only [nonIso, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_compl]
    by_cases hv : v ∈ A
    · by_cases hvy : v = y
      · subst hvy; rw [dB_y]; simp
      · rw [dB_out v hv hvy]; simp [hv, hvy]
    · rw [dB_B v hv]; simp [hv, hG v]
  have hevA : Even (nonIso (restr G (insert t A))).card := by
    rw [nonA, Finset.card_insert_of_notMem htA]; exact hAodd.add_one
  have hevB : Even (nonIso (restr G (insert y Aᶜ))).card := by
    rw [nonB, Finset.card_insert_of_notMem (by simp [hyA]), Finset.card_compl]
    have := Finset.card_le_univ A
    obtain ⟨m, hm⟩ := hn
    obtain ⟨j, hj⟩ := hAodd
    exact ⟨m - j, by omega⟩
  have hconnA : NIConn (restr G (insert t A)) := by
    have key : ∀ v, 0 < (restr G (insert t A)).degree v → (restr G (insert t A)).Reachable y v := by
      intro v hv
      by_cases hvA : v ∈ A
      · exact (hreachA v hvA).mono (by
          intro a b h; exact ⟨h.1, Finset.mem_insert_of_mem h.2.1, Finset.mem_insert_of_mem h.2.2⟩)
      · by_cases hvt : v = t
        · rw [hvt]
          exact (show (restr G (insert t A)).Adj y t from ⟨hyt, Finset.mem_insert_of_mem hyA,
            Finset.mem_insert_self _ _⟩).reachable
        · rw [dA_out v hvA hvt] at hv; exact absurd hv (lt_irrefl 0)
    exact fun a b ha hb => (key a ha).symm.trans (key b hb)
  have hconnB : NIConn (restr G (insert y Aᶜ)) := by
    have key : ∀ v, 0 < (restr G (insert y Aᶜ)).degree v → (restr G (insert y Aᶜ)).Reachable t v := by
      intro v hv
      by_cases hvA : v ∈ A
      · by_cases hvy : v = y
        · rw [hvy]
          exact (show (restr G (insert y Aᶜ)).Adj t y from ⟨hyt.symm, Finset.mem_insert_of_mem
            (Finset.mem_compl.mpr htA), Finset.mem_insert_self _ _⟩).reachable
        · rw [dB_out v hvA hvy] at hv; exact absurd hv (lt_irrefl 0)
      · exact (hreachB v hvA).mono (by
          intro a b h; exact ⟨h.1, Finset.mem_insert_of_mem h.2.1, Finset.mem_insert_of_mem h.2.2⟩)
    exact fun a b ha hb => (key a ha).symm.trans (key b hb)
  -- fewer edges
  obtain ⟨c, hc, hcy⟩ : ∃ c, G.Adj t c ∧ c ≠ y := by
    have : 1 < (G.neighborFinset t).card := by rw [card_neighborFinset_eq_degree]; omega
    obtain ⟨c, hc, hcy⟩ := Finset.exists_mem_ne this y
    exact ⟨c, (mem_neighborFinset _ _ _).mp hc, hcy⟩
  obtain ⟨d, hd, hdt'⟩ : ∃ d, G.Adj y d ∧ d ≠ t := by
    have hdy : 2 ≤ G.degree y := by
      obtain ⟨hp, j, hj⟩ := mem_evenSet_iff_even.mp hy; omega
    have : 1 < (G.neighborFinset y).card := by rw [card_neighborFinset_eq_degree]; omega
    obtain ⟨d, hd, hdt'⟩ := Finset.exists_mem_ne this t
    exact ⟨d, (mem_neighborFinset _ _ _).mp hd, hdt'⟩
  have hEA : (restr G (insert t A)).edgeFinset.card ≤ M := by
    have := card_edgeFinset_restr_lt (C := insert t A) hc (fun h => by
      have := h.2; simp only [Finset.mem_insert] at this
      rcases this with rfl | h'
      · exact G.loopless.irrefl _ hc
      · exact nbrT c hc hcy h')
    omega
  have hEB : (restr G (insert y Aᶜ)).edgeFinset.card ≤ M := by
    have := card_edgeFinset_restr_lt (C := insert y Aᶜ) hd (fun h => by
      have := h.2; simp only [Finset.mem_insert, Finset.mem_compl] at this
      rcases this with rfl | h'
      · exact G.loopless.irrefl _ hd
      · exact h' (nbrY d hd hdt'))
    omega
  -- distribute the `k + 1` removals
  have hyEA : y ∈ evenSet (restr G (insert t A)) := by rw [EvA]; simp [hy, hyA]
  obtain ⟨a2, ha2⟩ := even_card_evenSet_of_nonIso hevA
  obtain ⟨b2, hb2⟩ := even_card_evenSet_of_nonIso hevB
  obtain ⟨rA, rB, hsum, hrA, hrB, hwr⟩ : ∃ rA rB, rA + rB = k + 1 ∧ rA ≤ a2 ∧ rB ≤ b2 ∧
      (w ∈ A → 1 ≤ rA) ∧ (w ∉ A → 1 ≤ rB) := by
    by_cases hwA : w ∈ A
    · have hc1 : 1 ≤ a2 := by
        have : 2 ≤ (evenSet (restr G (insert t A))).card := by
          rw [EvA]
          have : ({y, w} : Finset V) ⊆ (evenSet G).filter (· ∈ A) := by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl <;> simp [*]
          have := Finset.card_le_card this
          rwa [Finset.card_pair hyw] at this
        omega
      obtain ⟨r₁, r₂, h1, h2, h3, h4⟩ := split_cap (k + 1) a2 b2 (by omega) hc1 (by omega)
      exact ⟨r₁, r₂, h1, h2, h3, fun _ => h4, fun h => absurd hwA h⟩
    · have hc1 : 1 ≤ b2 := by
        have : w ∈ evenSet (restr G (insert y Aᶜ)) := by rw [EvB]; simp [hw, hwA]
        have := Finset.card_pos.mpr ⟨w, this⟩
        omega
      obtain ⟨r₁, r₂, h1, h2, h3, h4⟩ := split_cap (k + 1) b2 a2 (by omega) hc1 (by omega)
      exact ⟨r₂, r₁, by omega, h3, h2, fun h => absurd h hwA, fun _ => h4⟩
  -- descents in the pieces
  obtain ⟨RA, hRAE, hRAc, hwRA, hyRA, -, DA, hDA⟩ := by
    classical
    exact piece_desc (r := rA) hlow hIH hEA (by omega) hconnA hevA (by omega) y
      ((({w} : Finset V)).filter (· ∈ A))
      (fun x hx => by
        simp only [Finset.mem_filter, Finset.mem_singleton] at hx
        rw [EvA]; simp [hx.1 ▸ hw, hx.2])
      (by apply (Finset.card_filter_le _ _).trans; simp)
      (by simp [hyw])
      (fun ⟨x, hx⟩ => by
        simp only [Finset.mem_filter, Finset.mem_singleton] at hx
        exact hwr.1 (hx.1 ▸ hx.2))
  obtain ⟨RB, hRBE, hRBc, hwRB, -, -, DB, hDB⟩ := by
    classical
    exact piece_desc (r := rB) hlow hIH hEB (by omega) hconnB hevB (by omega) y
      ((({w} : Finset V)).filter (· ∉ A))
      (fun x hx => by
        simp only [Finset.mem_filter, Finset.mem_singleton] at hx
        rw [EvB]; simp [hx.1 ▸ hw, hx.2])
      (by apply (Finset.card_filter_le _ _).trans; simp)
      (by simp [hyw])
      (fun ⟨x, hx⟩ => by
        simp only [Finset.mem_filter, Finset.mem_singleton] at hx
        exact hwr.2 (hx.1 ▸ hx.2))
  -- glue
  obtain ⟨D, -, hD⟩ := glue_bridge DA DB (A := (A : Set V)) (B := ((Aᶜ : Finset V) : Set V))
    hyA (by simp [htA]) (fun x hx => by simpa using hx)
    ⟨hyt, Finset.mem_insert_of_mem hyA, Finset.mem_insert_self _ _⟩
    ⟨hyt, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_compl.mpr htA)⟩
    (fun a b h hne => by
      obtain ⟨hab, ha, hb⟩ := h
      simp only [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact absurd hab (G.loopless.irrefl _)
        · obtain ⟨rfl, -⟩ := hcross b a hab.symm hb htA
          exact absurd Sym2.eq_swap hne
      rcases hb with rfl | hb
      · obtain ⟨rfl, -⟩ := hcross a b hab ha htA
        exact absurd rfl hne
      exact ⟨ha, hb⟩)
    (fun a b h hne => by
      obtain ⟨hab, ha, hb⟩ := h
      simp only [Finset.mem_insert, Finset.mem_compl] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact absurd hab (G.loopless.irrefl _)
        · obtain ⟨-, rfl⟩ := hcross a b hab hyA hb
          exact absurd rfl hne
      rcases hb with rfl | hb
      · obtain ⟨-, rfl⟩ := hcross b a hab.symm hyA ha
        exact absurd Sym2.eq_swap hne
      exact ⟨by simpa using ha, by simpa using hb⟩)
    (fun e => by
      induction e using Sym2.inductionOn with
      | hf a b =>
        simp only [mem_edgeSet, restr_adj, Finset.mem_insert, Finset.mem_compl]
        constructor
        · intro h
          by_cases ha : a ∈ A
          · by_cases hb : b ∈ A
            · exact Or.inl ⟨h, Or.inr ha, Or.inr hb⟩
            · obtain ⟨rfl, rfl⟩ := hcross a b h ha hb
              exact Or.inl ⟨h, Or.inr ha, Or.inl rfl⟩
          · by_cases hb : b ∈ A
            · obtain ⟨rfl, rfl⟩ := hcross b a h.symm hb ha
              exact Or.inl ⟨h, Or.inl rfl, Or.inr hb⟩
            · exact Or.inr ⟨h, Or.inr ha, Or.inr hb⟩
        · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h)
  -- the result
  refine ⟨RA ∪ RB, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · have := hRAE h; rw [EvA] at this; exact (Finset.mem_filter.mp this).1
    · have := hRBE h; rw [EvB] at this; exact (Finset.mem_filter.mp this).1
  · rw [Finset.card_union_of_disjoint (by
      rw [Finset.disjoint_left]
      intro x h1 h2
      have := hRAE h1; rw [EvA] at this
      have := hRBE h2; rw [EvB] at this
      simp_all), hRAc, hRBc, hsum]
  · intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    by_cases hwA : x ∈ A
    · exact Finset.mem_union_left _ (hwRA (by simp [hwA]))
    · exact Finset.mem_union_right _ (hwRB (by simp [hwA]))
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · exact hyRA h
    · have := hRBE h; rw [EvB] at this; exact (Finset.mem_filter.mp this).2 hyA
  · refine ⟨Finset.sdiff_subset, D, fun v => ?_⟩
    have h1 := hD v
    have hA' := hDA v
    have hB' := hDB v
    have hRAA : ∀ x ∈ RA, x ∈ A := fun x hx => by
      have := hRAE hx; rw [EvA] at this; exact (Finset.mem_filter.mp this).2
    have hRBB : ∀ x ∈ RB, x ∉ A := fun x hx => by
      have := hRBE hx; rw [EvB] at this; exact (Finset.mem_filter.mp this).2
    by_cases hvy : v = y
    · subst hvy
      rw [profile_even_mem (mem_evenSet_iff_even.mp hyEA).2 (Finset.mem_sdiff.mpr ⟨hyEA, hyRA⟩)]
        at hA'
      rw [profile_odd (by rw [dB_y]; decide)] at hB'
      rw [profile_even_mem (mem_evenSet_iff_even.mp hy).2 (Finset.mem_sdiff.mpr ⟨hy, by
        simp only [Finset.mem_union, not_or]; exact ⟨hyRA, fun h => hRBB v h hyA⟩⟩)]
      simp only [Ne.symm hyt', ite_false, ite_true] at h1
      omega
    by_cases hvt : v = t
    · subst hvt
      rw [profile_odd (by rw [dA_t]; decide)] at hA'
      have : D.ends v = DB.ends v := by
        simp only [hvy, Ne.symm hvy, ite_false, ite_true] at h1; omega
      rw [this, hB']
      apply profile_congr (dB_B v htA)
      rw [EvB]
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_union, not_or]
      constructor
      · rintro ⟨⟨h, -⟩, h'⟩; exact ⟨h, fun h'' => htA (hRAA v h''), h'⟩
      · rintro ⟨h, -, h'⟩; exact ⟨⟨h, htA⟩, h'⟩
    simp only [Ne.symm hvy, Ne.symm hvt, ite_false, add_zero] at h1
    by_cases hvA : v ∈ A
    · rw [profile_zero_of_degree Finset.sdiff_subset (dB_out v hvA hvy)] at hB'
      rw [h1, hA', hB', add_zero]
      apply profile_congr (dA_A v hvA)
      rw [EvA]
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_union, not_or]
      constructor
      · rintro ⟨⟨h, -⟩, h'⟩; exact ⟨h, h', fun h'' => hRBB v h'' hvA⟩
      · rintro ⟨h, h', -⟩; exact ⟨⟨h, hvA⟩, h'⟩
    · rw [profile_zero_of_degree Finset.sdiff_subset (dA_out v hvA hvt)] at hA'
      rw [h1, hA', hB', zero_add]
      apply profile_congr (dB_B v hvA)
      rw [EvB]
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_union, not_or]
      constructor
      · rintro ⟨⟨h, -⟩, h'⟩; exact ⟨h, fun h'' => hvA (hRAA v h''), h'⟩
      · rintro ⟨h, -, h'⟩; exact ⟨⟨h, hvA⟩, h'⟩

theorem split_any (T c₁ c₂ : ℕ) (h : T ≤ c₁ + c₂) :
    ∃ r₁ r₂, r₁ + r₂ = T ∧ r₁ ≤ c₁ ∧ r₂ ≤ c₂ := by
  by_cases h' : c₁ ≤ T
  · exact ⟨c₁, T - c₁, by omega, le_rfl, by omega⟩
  · exact ⟨T, 0, by omega, by omega, by omega⟩

/-- **Bridge case, even side.** `yt` is a bridge, `A` the vertex set of the side of `y`, with
`|A|` even. Descend in `G[A]` and `G[Aᶜ]` (keeping `t` if it is odd in `G`), and glue by extending
a path ending at `t` with the edge `ty`. -/
theorem bridge_even {k M : ℕ} (hk : 1 ≤ k) (hlow : ∀ j, 1 ≤ j → j ≤ k → DStmt.{u} j)
    (hIH : DStmtE.{u} (k + 1) M) (hG : ∀ v, 0 < G.degree v) (hn : Even (Fintype.card V))
    (hEM : G.edgeFinset.card ≤ M + 1) (h2k : 2 * (k + 1) ≤ (evenSet G).card) {y w t : V}
    (hy : y ∈ evenSet G) (hw : w ∈ evenSet G) (hyw : y ≠ w) (hyt : G.Adj y t)
    (hdt : 2 ≤ G.degree t) {A : Finset V} (hyA : y ∈ A) (htA : t ∉ A)
    (hcross : ∀ a b, G.Adj a b → a ∈ A → b ∉ A → a = y ∧ b = t)
    (hreachA : ∀ v ∈ A, (restr G A).Reachable y v)
    (hreachB : ∀ v ∉ A, (restr G Aᶜ).Reachable t v) (hAeven : Even A.card) :
    Desc G (k + 1) y {w} := by
  have hyt' : y ≠ t := hyt.ne
  have nbrA : ∀ v ∈ A, v ≠ y → ∀ b, G.Adj v b → b ∈ A := fun v hv hvy b h => by
    by_contra hb; exact hvy (hcross v b h hv hb).1
  have nbrB : ∀ v, v ∉ A → v ≠ t → ∀ b, G.Adj v b → b ∉ A := fun v hv hvt b h hb =>
    hvt (hcross b v h.symm hb hv).2
  have nbrY : ∀ b, G.Adj y b → b ≠ t → b ∈ A := fun b h hbt => by
    by_contra hb; exact hbt (hcross y b h hyA hb).2
  have nbrT : ∀ b, G.Adj t b → b ≠ y → b ∉ A := fun b h hby hb =>
    hby (hcross b t h.symm hb htA).1
  obtain ⟨hy0, jy, hjy⟩ := mem_evenSet_iff_even.mp hy
  -- degrees
  have dA_A : ∀ v ∈ A, v ≠ y → (restr G A).degree v = G.degree v := fun v hv hvy =>
    degree_restr_full hv (nbrA v hv hvy)
  have dA_y : (restr G A).degree y + 1 = G.degree y :=
    degree_restr_minus hyA hyt htA (fun b h hbt => nbrY b h hbt)
  have dA_out : ∀ v, v ∉ A → (restr G A).degree v = 0 := fun v hv => degree_restr_out hv
  have dB_B : ∀ v, v ∉ A → v ≠ t → (restr G Aᶜ).degree v = G.degree v := fun v hv hvt =>
    degree_restr_full (Finset.mem_compl.mpr hv)
      (fun b h => Finset.mem_compl.mpr (nbrB v hv hvt b h))
  have dB_t : (restr G Aᶜ).degree t + 1 = G.degree t :=
    degree_restr_minus (Finset.mem_compl.mpr htA) hyt.symm (by simp [hyA])
      (fun b h hby => Finset.mem_compl.mpr (nbrT b h hby))
  have dB_out : ∀ v ∈ A, (restr G Aᶜ).degree v = 0 := fun v hv =>
    degree_restr_out (by simp [hv])
  have hyodd : Odd ((restr G A).degree y) := ⟨jy - 1, by omega⟩
  -- even vertices
  have EvA : evenSet (restr G A) = ((evenSet G).filter (· ∈ A)).erase y := by
    ext v
    simp only [Finset.mem_erase, Finset.mem_filter]
    by_cases hv : v ∈ A
    · by_cases hvy : v = y
      · rw [hvy]
        simp only [ne_eq, not_true_eq_false, false_and, iff_false]
        exact fun h => (Nat.not_even_iff_odd.mpr hyodd) (mem_evenSet_iff_even.mp h).2
      · rw [mem_evenSet_iff_even, mem_evenSet_iff_even, dA_A v hv hvy]; simp [hv, hvy]
    · rw [mem_evenSet_iff_even, dA_out v hv]; simp [hv]
  have hEvA_card : (evenSet (restr G A)).card + 1 = ((evenSet G).filter (· ∈ A)).card := by
    rw [EvA, Finset.card_erase_of_mem (by simp [hy, hyA])]
    have : 0 < ((evenSet G).filter (· ∈ A)).card := Finset.card_pos.mpr ⟨y, by simp [hy, hyA]⟩
    omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := evenSet G) (fun v => v ∈ A)
  -- non-isolated vertices, connectivity, parity
  have nonA : nonIso (restr G A) = A := by
    ext v
    simp only [nonIso, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hv : v ∈ A
    · by_cases hvy : v = y
      · rw [hvy]; simp [hyA]; omega
      · rw [dA_A v hv hvy]; simp [hv, hG v]
    · rw [dA_out v hv]; simp [hv]
  have nonB : nonIso (restr G Aᶜ) = Aᶜ := by
    ext v
    simp only [nonIso, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
    by_cases hv : v ∈ A
    · rw [dB_out v hv]; simp [hv]
    · by_cases hvt : v = t
      · rw [hvt]; simp [htA]; omega
      · rw [dB_B v hv hvt]; simp [hv, hG v]
  have hevA : Even (nonIso (restr G A)).card := by rw [nonA]; exact hAeven
  have hevB : Even (nonIso (restr G Aᶜ)).card := by
    rw [nonB, Finset.card_compl]
    have := Finset.card_le_univ A
    obtain ⟨m, hm⟩ := hn
    obtain ⟨j, hj⟩ := hAeven
    exact ⟨m - j, by omega⟩
  have hconnA : NIConn (restr G A) := by
    have key : ∀ v, 0 < (restr G A).degree v → (restr G A).Reachable y v := by
      intro v hv
      by_cases hvA : v ∈ A
      · exact hreachA v hvA
      · rw [dA_out v hvA] at hv; exact absurd hv (lt_irrefl 0)
    exact fun a b ha hb => (key a ha).symm.trans (key b hb)
  have hconnB : NIConn (restr G Aᶜ) := by
    have key : ∀ v, 0 < (restr G Aᶜ).degree v → (restr G Aᶜ).Reachable t v := by
      intro v hv
      by_cases hvA : v ∈ A
      · rw [dB_out v hvA] at hv; exact absurd hv (lt_irrefl 0)
      · exact hreachB v hvA
    exact fun a b ha hb => (key a ha).symm.trans (key b hb)
  have hEA : (restr G A).edgeFinset.card ≤ M := by
    have := card_edgeFinset_restr_lt (C := A) hyt (fun h => htA h.2); omega
  have hEB : (restr G Aᶜ).edgeFinset.card ≤ M := by
    have := card_edgeFinset_restr_lt (C := Aᶜ) hyt (fun h => (Finset.mem_compl.mp h.1) hyA)
    omega
  -- gluing data
  have hdisj : ∀ e, e ∈ (restr G A).edgeSet → e ∉ (restr G Aᶜ).edgeSet := by
    intro e h1 h2
    induction e using Sym2.inductionOn with
    | hf a b => exact (Finset.mem_compl.mp h2.2.1) h1.2.1
  have hK : ∀ e, e ∈ (delE G {s(y, t)}).edgeSet ↔
      e ∈ (restr G A).edgeSet ∨ e ∈ (restr G Aᶜ).edgeSet := by
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      rw [delE_edgeSet, Finset.mem_singleton]
      simp only [mem_edgeSet, restr_adj, Finset.mem_compl]
      constructor
      · rintro ⟨h, hne⟩
        by_cases ha : a ∈ A
        · by_cases hb : b ∈ A
          · exact Or.inl ⟨h, ha, hb⟩
          · obtain ⟨rfl, rfl⟩ := hcross a b h ha hb; exact absurd rfl hne
        · by_cases hb : b ∈ A
          · obtain ⟨rfl, rfl⟩ := hcross b a h.symm hb ha; exact absurd Sym2.eq_swap hne
          · exact Or.inr ⟨h, ha, hb⟩
      · rintro (⟨h, ha, hb⟩ | ⟨h, ha, hb⟩)
        · refine ⟨h, fun he => ?_⟩
          rcases Sym2.eq_iff.mp he with ⟨-, rfl⟩ | ⟨rfl, -⟩
          · exact htA hb
          · exact htA ha
        · refine ⟨h, fun he => ?_⟩
          rcases Sym2.eq_iff.mp he with ⟨rfl, -⟩ | ⟨-, rfl⟩
          · exact ha hyA
          · exact hb hyA
  have hGK : ∀ e, e ∈ G.edgeSet ↔ e ∈ (delE G {s(y, t)}).edgeSet ∨ e = s(t, y) := by
    intro e
    rw [delE_edgeSet, Finset.mem_singleton, Sym2.eq_swap (a := t)]
    constructor
    · intro h; by_cases he : e = s(y, t)
      · exact Or.inr he
      · exact Or.inl ⟨h, he⟩
    · rintro (⟨h, -⟩ | rfl)
      · exact h
      · exact hyt
  have hKty : ¬ (delE G {s(y, t)}).Adj t y := fun h =>
    (delE_adj.mp h).2 (by simp [Sym2.eq_swap])
  -- the final check, shared by both parities of `t`
  have hfinal : ∀ (RA RB : Finset V) (DA : PathDecomp (restr G A))
      (DB : PathDecomp (restr G Aᶜ)) (D : PathDecomp G),
      RA ⊆ evenSet (restr G A) → RB ⊆ evenSet (restr G Aᶜ) →
      Realises (restr G A) DA (evenSet (restr G A) \ RA) →
      Realises (restr G Aᶜ) DB (evenSet (restr G Aᶜ) \ RB) →
      (∀ v, D.ends v + (if t = v then 1 else 0) =
        DA.ends v + DB.ends v + (if y = v then 1 else 0)) →
      ∀ R : Finset V, (∀ v ∈ A, v ∈ R ↔ v ∈ RA) → (∀ v, v ∉ A → v ≠ t → (v ∈ R ↔ v ∈ RB)) →
      y ∉ R → (t ∈ evenSet G → t ∈ R) → (t ∉ evenSet G → t ∈ evenSet (restr G Aᶜ) \ RB) →
      Realises G D (evenSet G \ R) := by
    intro RA RB DA DB D hRA hRB hDA hDB hD R hRA' hRB' hyR htR htR'
    intro v
    have h1 := hD v
    have hA' := hDA v
    have hB' := hDB v
    by_cases hvy : v = y
    · rw [hvy] at h1 hA' hB' ⊢
      rw [profile_odd hyodd] at hA'
      rw [profile_zero_of_degree Finset.sdiff_subset (dB_out y hyA)] at hB'
      rw [profile_even_mem (mem_evenSet_iff_even.mp hy).2 (Finset.mem_sdiff.mpr ⟨hy, hyR⟩)]
      simp only [hyt', Ne.symm hyt', ite_false, ite_true] at h1
      omega
    by_cases hvt : v = t
    · rw [hvt] at h1 hA' hB' ⊢
      rw [profile_zero_of_degree Finset.sdiff_subset (dA_out t htA)] at hA'
      simp only [hyt', Ne.symm hyt', ite_false, ite_true] at h1
      by_cases htE : t ∈ evenSet G
      · have htodd : Odd ((restr G Aᶜ).degree t) := by
          obtain ⟨-, i, hi⟩ := mem_evenSet_iff_even.mp htE; exact ⟨i - 1, by omega⟩
        rw [profile_odd htodd] at hB'
        rw [profile_even_not_mem (mem_evenSet_iff_even.mp htE).2
          (fun h => (Finset.mem_sdiff.mp h).2 (htR htE))]
        omega
      · have htev := htR' htE
        rw [profile_even_mem (mem_evenSet_iff_even.mp (Finset.mem_sdiff.mp htev).1).2 htev]
          at hB'
        rw [profile_odd (odd_of_not_mem_evenSet hG htE)]
        omega
    simp only [Ne.symm hvy, Ne.symm hvt, ite_false, add_zero] at h1
    by_cases hvA : v ∈ A
    · rw [profile_zero_of_degree Finset.sdiff_subset (dB_out v hvA)] at hB'
      rw [h1, hA', hB', add_zero]
      apply profile_congr (dA_A v hvA hvy)
      rw [EvA]
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_filter]
      rw [hRA' v hvA]
      constructor
      · rintro ⟨⟨-, h, -⟩, h'⟩; exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨⟨hvy, h, hvA⟩, h'⟩
    · rw [profile_zero_of_degree Finset.sdiff_subset (dA_out v hvA)] at hA'
      rw [h1, hA', hB', zero_add]
      apply profile_congr (dB_B v hvA hvt)
      simp only [Finset.mem_sdiff]
      rw [hRB' v hvA hvt]
      have : v ∈ evenSet (restr G Aᶜ) ↔ v ∈ evenSet G := by
        rw [mem_evenSet_iff_even, mem_evenSet_iff_even, dB_B v hvA hvt]
      rw [this]
  have hRAA : ∀ (RA : Finset V), RA ⊆ evenSet (restr G A) → ∀ x ∈ RA, x ∈ A ∧ x ≠ y := by
    intro RA hRA x hx
    have := hRA hx; rw [EvA] at this
    simp only [Finset.mem_erase, Finset.mem_filter] at this
    exact ⟨this.2.2, this.1⟩
  have hRBB : ∀ (RB : Finset V), RB ⊆ evenSet (restr G Aᶜ) → ∀ x ∈ RB, x ∉ A := by
    intro RB hRB x hx
    have := hRB hx
    by_contra hxA
    have := (mem_evenSet_iff_even.mp this).1
    rw [dB_out x hxA] at this
    exact lt_irrefl 0 this
  have hBpaths : ∀ DB : PathDecomp (restr G Aᶜ), ∀ P ∈ DB.paths, y ∉ P.walk.support :=
    fun DB P _ hyP => (Finset.mem_compl.mp (restr_path_support P y hyP)) hyA
  by_cases htE : t ∈ evenSet G
  · -- `t` even in `G`: remove `t`, and `k` further vertices
    obtain ⟨-, jt, hjt⟩ := mem_evenSet_iff_even.mp htE
    have htodd : Odd ((restr G Aᶜ).degree t) := ⟨jt - 1, by omega⟩
    have EvB : evenSet (restr G Aᶜ) = ((evenSet G).filter (· ∉ A)).erase t := by
      ext v
      simp only [Finset.mem_erase, Finset.mem_filter]
      by_cases hv : v ∈ A
      · rw [mem_evenSet_iff_even, dB_out v hv]; simp [hv]
      · by_cases hvt : v = t
        · rw [hvt]
          simp only [ne_eq, not_true_eq_false, false_and, iff_false]
          exact fun h => (Nat.not_even_iff_odd.mpr htodd) (mem_evenSet_iff_even.mp h).2
        · rw [mem_evenSet_iff_even, mem_evenSet_iff_even, dB_B v hv hvt]; simp [hv, hvt]
    have hEvB_card : (evenSet (restr G Aᶜ)).card + 1 =
        ((evenSet G).filter (· ∉ A)).card := by
      rw [EvB, Finset.card_erase_of_mem (by simp [htE, htA])]
      have : 0 < ((evenSet G).filter (· ∉ A)).card := Finset.card_pos.mpr ⟨t, by simp [htE, htA]⟩
      omega
    obtain ⟨a2, ha2⟩ := even_card_evenSet_of_nonIso hevA
    obtain ⟨b2, hb2⟩ := even_card_evenSet_of_nonIso hevB
    obtain ⟨rA, rB, hsum, hrA, hrB, hwr⟩ : ∃ rA rB, rA + rB = k ∧ rA ≤ a2 ∧ rB ≤ b2 ∧
        (w ∈ evenSet (restr G A) → 1 ≤ rA) ∧ (w ∈ evenSet (restr G Aᶜ) → 1 ≤ rB) := by
      have hk2 : k ≤ a2 + b2 := by omega
      by_cases hwA : w ∈ evenSet (restr G A)
      · have : 1 ≤ a2 := by have := Finset.card_pos.mpr ⟨w, hwA⟩; omega
        obtain ⟨r₁, r₂, h1, h2, h3, h4⟩ := split_cap k a2 b2 hk2 this (by omega)
        refine ⟨r₁, r₂, h1, h2, h3, fun _ => h4, fun h => ?_⟩
        exact absurd (hRAA _ (le_refl _) w hwA).1 ((hRBB _ (le_refl _)) w h)
      · by_cases hwB : w ∈ evenSet (restr G Aᶜ)
        · have : 1 ≤ b2 := by have := Finset.card_pos.mpr ⟨w, hwB⟩; omega
          obtain ⟨r₁, r₂, h1, h2, h3, h4⟩ := split_cap k b2 a2 (by omega) this (by omega)
          exact ⟨r₂, r₁, by omega, h3, h2, fun h => absurd h hwA, fun _ => h4⟩
        · obtain ⟨r₁, r₂, h1, h2, h3⟩ := split_any k a2 b2 hk2
          exact ⟨r₁, r₂, h1, h2, h3, fun h => absurd h hwA, fun h => absurd h hwB⟩
    obtain ⟨RA, hRAE, hRAc, hwRA, -, -, DA, hDA⟩ := by
      classical
      exact piece_desc (r := rA) hlow hIH hEA (by omega) hconnA hevA (by omega) y
        (({w} : Finset V).filter (· ∈ evenSet (restr G A)))
        (fun x hx => (Finset.mem_filter.mp hx).2)
        (by apply (Finset.card_filter_le _ _).trans; simp)
        (by simp [hyw])
        (fun ⟨x, hx⟩ => by
          simp only [Finset.mem_filter, Finset.mem_singleton] at hx
          exact hwr.1 (hx.1 ▸ hx.2))
    obtain ⟨RB, hRBE, hRBc, hwRB, -, -, DB, hDB⟩ := by
      classical
      exact piece_desc (r := rB) hlow hIH hEB (by omega) hconnB hevB (by omega) y
        (({w} : Finset V).filter (· ∈ evenSet (restr G Aᶜ)))
        (fun x hx => (Finset.mem_filter.mp hx).2)
        (by apply (Finset.card_filter_le _ _).trans; simp)
        (by simp [hyw])
        (fun ⟨x, hx⟩ => by
          simp only [Finset.mem_filter, Finset.mem_singleton] at hx
          exact hwr.2 (hx.1 ▸ hx.2))
    obtain ⟨D, -, hD⟩ := glue_append DA DB hdisj hK hGK hKty (hBpaths DB)
      (by rw [hDB t, profile_odd htodd]; exact Nat.one_pos)
    have htRA : t ∉ RA := fun h => htA (hRAA RA hRAE t h).1
    have htRB : t ∉ RB := fun h => by
      have := hRBE h; rw [EvB] at this; simp at this
    have hdisjAB : Disjoint RA RB := by
      rw [Finset.disjoint_left]
      exact fun x h1 h2 => hRBB RB hRBE x h2 (hRAA RA hRAE x h1).1
    refine ⟨insert t (RA ∪ RB), ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact htE
      rcases Finset.mem_union.mp hx with h | h
      · have := hRAE h; rw [EvA] at this; exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase this)).1
      · have := hRBE h; rw [EvB] at this; exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase this)).1
    · rw [Finset.card_insert_of_notMem (by simp [htRA, htRB]),
        Finset.card_union_of_disjoint hdisjAB, hRAc, hRBc]
      omega
    · intro x hx
      rw [Finset.mem_singleton] at hx
      rw [hx]
      by_cases hwt : w = t
      · rw [hwt]; exact Finset.mem_insert_self _ _
      by_cases hwA : w ∈ A
      · have : w ∈ evenSet (restr G A) := by rw [EvA]; simp [hw, hwA, Ne.symm hyw]
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hwRA (by simp [this])))
      · have : w ∈ evenSet (restr G Aᶜ) := by rw [EvB]; simp [hw, hwA, hwt]
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (hwRB (by simp [this])))
    · intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact hyt' h
      rcases Finset.mem_union.mp h with h | h
      · exact (hRAA RA hRAE y h).2 rfl
      · exact hRBB RB hRBE y h hyA
    · refine ⟨Finset.sdiff_subset, D, ?_⟩
      apply hfinal RA RB DA DB D hRAE hRBE hDA hDB hD
      · intro v hv
        simp only [Finset.mem_insert, Finset.mem_union]
        constructor
        · rintro (rfl | h | h)
          · exact absurd hv htA
          · exact h
          · exact absurd hv (hRBB RB hRBE v h)
        · intro h; exact Or.inr (Or.inl h)
      · intro v hv hvt
        simp only [Finset.mem_insert, Finset.mem_union, hvt, false_or]
        constructor
        · rintro (h | h)
          · exact absurd (hRAA RA hRAE v h).1 hv
          · exact h
        · intro h; exact Or.inr h
      · intro h
        rcases Finset.mem_insert.mp h with h | h
        · exact hyt' h
        rcases Finset.mem_union.mp h with h | h
        · exact (hRAA RA hRAE y h).2 rfl
        · exact hRBB RB hRBE y h hyA
      · intro _; exact Finset.mem_insert_self _ _
      · intro h; exact absurd htE h
  · -- `t` odd in `G`: keep `t` in `G[Aᶜ]`, remove `k + 1` vertices
    have htev : Even ((restr G Aᶜ).degree t) := by
      obtain ⟨i, hi⟩ := odd_of_not_mem_evenSet hG htE; exact ⟨i, by omega⟩
    have htEB : t ∈ evenSet (restr G Aᶜ) := mem_evenSet_iff_even.mpr ⟨by omega, htev⟩
    have EvB : evenSet (restr G Aᶜ) = insert t ((evenSet G).filter (· ∉ A)) := by
      ext v
      simp only [Finset.mem_insert, Finset.mem_filter]
      by_cases hvt : v = t
      · rw [hvt]; simp [htEB]
      · by_cases hv : v ∈ A
        · rw [mem_evenSet_iff_even, dB_out v hv]; simp [hv, hvt]
        · rw [mem_evenSet_iff_even, mem_evenSet_iff_even, dB_B v hv hvt]; simp [hv, hvt]
    have hEvB_card : (evenSet (restr G Aᶜ)).card = ((evenSet G).filter (· ∉ A)).card + 1 := by
      rw [EvB, Finset.card_insert_of_notMem (by simp [htE])]
    obtain ⟨a2, ha2⟩ := even_card_evenSet_of_nonIso hevA
    obtain ⟨b2, hb2⟩ := even_card_evenSet_of_nonIso hevB
    have hwt : w ≠ t := fun h => htE (h ▸ hw)
    obtain ⟨rA, rB, hsum, hrA, hrB, hwr⟩ : ∃ rA rB, rA + rB = k + 1 ∧ rA ≤ a2 ∧ rB ≤ b2 ∧
        (w ∈ A → 1 ≤ rA) ∧ (w ∉ A → 1 ≤ rB) := by
      have hk2 : k + 1 ≤ a2 + b2 := by omega
      by_cases hwA : w ∈ A
      · have hwEA : w ∈ evenSet (restr G A) := by rw [EvA]; simp [hw, hwA, Ne.symm hyw]
        have : 1 ≤ a2 := by have := Finset.card_pos.mpr ⟨w, hwEA⟩; omega
        obtain ⟨r₁, r₂, h1, h2, h3, h4⟩ := split_cap (k + 1) a2 b2 hk2 this (by omega)
        exact ⟨r₁, r₂, h1, h2, h3, fun _ => h4, fun h => absurd hwA h⟩
      · have : 1 ≤ b2 := by
          have : 2 ≤ (evenSet (restr G Aᶜ)).card := by
            have hsub : ({t, w} : Finset V) ⊆ evenSet (restr G Aᶜ) := by
              intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rw [EvB]; rcases hx with rfl | rfl <;> simp [*]
            have := Finset.card_le_card hsub
            rwa [Finset.card_pair (Ne.symm hwt)] at this
          omega
        obtain ⟨r₁, r₂, h1, h2, h3, h4⟩ := split_cap (k + 1) b2 a2 (by omega) this (by omega)
        exact ⟨r₂, r₁, by omega, h3, h2, fun h => absurd h hwA, fun _ => h4⟩
    obtain ⟨RA, hRAE, hRAc, hwRA, -, -, DA, hDA⟩ := by
      classical
      exact piece_desc (r := rA) hlow hIH hEA (by omega) hconnA hevA (by omega) y
        (({w} : Finset V).filter (· ∈ A))
        (fun x hx => by
          simp only [Finset.mem_filter, Finset.mem_singleton] at hx
          rw [EvA]; simp [hx.1 ▸ hw, hx.2, hx.1 ▸ Ne.symm hyw])
        (by apply (Finset.card_filter_le _ _).trans; simp)
        (by simp [hyw])
        (fun ⟨x, hx⟩ => by
          simp only [Finset.mem_filter, Finset.mem_singleton] at hx
          exact hwr.1 (hx.1 ▸ hx.2))
    obtain ⟨RB, hRBE, hRBc, hwRB, htRB, -, DB, hDB⟩ := by
      classical
      exact piece_desc (r := rB) hlow hIH hEB (by omega) hconnB hevB (by omega) t
        (({w} : Finset V).filter (· ∉ A))
        (fun x hx => by
          simp only [Finset.mem_filter, Finset.mem_singleton] at hx
          rw [EvB]; simp [hx.1 ▸ hw, hx.2])
        (by apply (Finset.card_filter_le _ _).trans; simp)
        (by simp [Ne.symm hwt])
        (fun ⟨x, hx⟩ => by
          simp only [Finset.mem_filter, Finset.mem_singleton] at hx
          exact hwr.2 (hx.1 ▸ hx.2))
    have htS : t ∈ evenSet (restr G Aᶜ) \ RB := Finset.mem_sdiff.mpr ⟨htEB, htRB⟩
    obtain ⟨D, -, hD⟩ := glue_append DA DB hdisj hK hGK hKty (hBpaths DB)
      (by rw [hDB t, profile_even_mem htev htS]; exact Nat.two_pos)
    have hdisjAB : Disjoint RA RB := by
      rw [Finset.disjoint_left]
      exact fun x h1 h2 => hRBB RB hRBE x h2 (hRAA RA hRAE x h1).1
    refine ⟨RA ∪ RB, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · have := hRAE h; rw [EvA] at this
        exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase this)).1
      · have := hRBE h; rw [EvB] at this
        rcases Finset.mem_insert.mp this with rfl | h'
        · exact absurd h htRB
        · exact (Finset.mem_filter.mp h').1
    · rw [Finset.card_union_of_disjoint hdisjAB, hRAc, hRBc, hsum]
    · intro x hx
      rw [Finset.mem_singleton] at hx
      rw [hx]
      by_cases hwA : w ∈ A
      · exact Finset.mem_union_left _ (hwRA (by simp [hwA]))
      · exact Finset.mem_union_right _ (hwRB (by simp [hwA]))
    · intro h
      rcases Finset.mem_union.mp h with h | h
      · exact (hRAA RA hRAE y h).2 rfl
      · exact hRBB RB hRBE y h hyA
    · refine ⟨Finset.sdiff_subset, D, ?_⟩
      apply hfinal RA RB DA DB D hRAE hRBE hDA hDB hD
      · intro v hv
        simp only [Finset.mem_union]
        constructor
        · rintro (h | h)
          · exact h
          · exact absurd hv (hRBB RB hRBE v h)
        · intro h; exact Or.inl h
      · intro v hv hvt
        simp only [Finset.mem_union]
        constructor
        · rintro (h | h)
          · exact absurd (hRAA RA hRAE v h).1 hv
          · exact h
        · intro h; exact Or.inr h
      · intro h
        rcases Finset.mem_union.mp h with h | h
        · exact (hRAA RA hRAE y h).2 rfl
        · exact hRBB RB hRBE y h hyA
      · intro h; exact absurd h htE
      · intro _; exact htS

end bridge

/-! ## Part 6: the reduction theorem -/

section reduction

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Lifting a descent at an odd neighbour `t` of `y` (when `y` has no even neighbour). -/
theorem desc_lift_of_no_even_nbr (hG : ∀ v, 0 < G.degree v) {k : ℕ} {y t : V}
    {W₀ : Finset V} (hy : y ∈ evenSet G) (hnoev : ∀ v ∈ evenSet G, ¬ G.Adj y v)
    (hyt : G.Adj y t) (htK : 0 < (delE G {s(y, t)}).degree t) (hW : W₀ ⊆ evenSet G)
    (hyW : y ∉ W₀) (h : Desc (delE G {s(y, t)}) k t W₀) : Desc G k y W₀ := by
  have htE : t ∉ evenSet G := fun h => hnoev t h hyt
  have hEvK := evenSet_delE_odd hG hy htE hyt htK
  obtain ⟨R, hRK, hRc, hWR, htR, hreal⟩ := h
  have htKE : t ∈ evenSet (delE G {s(y, t)}) := by rw [hEvK]; exact Finset.mem_insert_self _ _
  have htS : t ∈ evenSet (delE G {s(y, t)}) \ R := Finset.mem_sdiff.mpr ⟨htKE, htR⟩
  have hRE : ∀ a ∈ R, a ∈ evenSet G ∧ a ≠ y := by
    intro a ha
    have := hRK ha
    rw [hEvK] at this
    rcases Finset.mem_insert.mp this with rfl | h
    · exact absurd ha htR
    · exact ⟨Finset.mem_of_mem_erase h, Finset.ne_of_mem_erase h⟩
  have hlift := realisable_lift hG hy htE hyt hreal htS (by
    intro a ha haS
    have haR : a ∈ R := by
      by_contra h; exact haS (Finset.mem_sdiff.mpr ⟨ha, h⟩)
    exact hnoev a (hRE a haR).1)
  have hyR : y ∉ R := fun h => (hRE y h).2 rfl
  refine ⟨R, fun a ha => (hRE a ha).1, hRc, hWR, hyR, ?_⟩
  convert hlift using 1
  ext a
  rw [hEvK]
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
  by_cases h1 : a = y
  · rw [h1]; simp [hy, hyR]
  by_cases h2 : a = t
  · rw [h2]; simp [htE, Ne.symm hyt.ne]
  simp [h1, h2]

/-- Transfer from `k`-step descent in `G − yt`, where `t` is the only even neighbour of `y`. -/
theorem desc_succ_of_transfer (hG : ∀ v, 0 < G.degree v) {k : ℕ} {y w t y' w' : V}
    (hy : y ∈ evenSet G) (hw : w ∈ evenSet G) (hyw : y ≠ w) (ht : t ∈ evenSet G)
    (hyt : G.Adj y t) (huniq : ∀ v ∈ evenSet G, G.Adj y v → v = t)
    (hdesc : Desc (delE G {s(y, t)}) k y' {w'}) (hww' : w = t ∨ w = w') :
    Desc G (k + 1) y {w} := by
  have hyt' : y ≠ t := hyt.ne
  have hEvK := evenSet_delE_even hy ht hyt
  obtain ⟨W, hWK, hWc, hw'W, -, hreal⟩ := hdesc
  have hWE : ∀ a ∈ W, a ∈ evenSet G ∧ a ≠ y ∧ a ≠ t := by
    intro a ha
    have := hWK ha
    rw [hEvK] at this
    simp only [Finset.mem_erase] at this
    exact ⟨this.2.2, this.2.1, this.1⟩
  have htrans := realisable_transfer hy ht hyt hreal (by
    intro u hu huS hadj
    have huW : u ∈ W := by
      by_contra h; exact huS (Finset.mem_sdiff.mpr ⟨hu, h⟩)
    exact (hWE u huW).2.2 (huniq u (hWE u huW).1 hadj))
  have htW : t ∉ W := fun h => (hWE t h).2.2 rfl
  have hyW : y ∉ W := fun h => (hWE y h).2.1 rfl
  refine ⟨insert t W, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ht
    · exact (hWE a ha).1
  · rw [Finset.card_insert_of_notMem htW, hWc]
  · intro a ha
    rw [Finset.mem_singleton] at ha
    rw [ha]
    rcases hww' with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · rw [h]; exact Finset.mem_insert_of_mem (hw'W (Finset.mem_singleton_self _))
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hyt' h
    · exact hyW h
  · convert htrans using 1
    ext a
    rw [hEvK]
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    by_cases h1 : a = y
    · rw [h1]; simp [hy, hyt', hyW]
    by_cases h2 : a = t
    · rw [h2]; simp [Ne.symm hyt']
    simp [h1, h2]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A walk in `G − yt` that stays inside a vertex set `C` is a walk of `restr G C`. -/
theorem restr_reachable_of_walk {C : Finset V} {y t a b : V}
    (p : (delE G {s(y, t)}).Walk a b) (hp : ∀ x ∈ p.support, x ∈ C) :
    (restr G C).Reachable a b := by
  refine ⟨p.transfer (restr G C) (fun e he => ?_)⟩
  induction e using Sym2.inductionOn with
  | hf c d =>
    have hcd : (delE G {s(y, t)}).Adj c d := p.edges_subset_edgeSet he
    exact ⟨delE_le hcd, hp c (p.fst_mem_support_of_mem_edges he),
      hp d (p.snd_mem_support_of_mem_edges he)⟩

/-- **Reduction to the branching case** (one level). If `D_1, …, D_k` hold (`k ≥ 2`) and
`B_{k+1}` holds, then `D_{k+1}` holds for graphs with any number of edges. -/
theorem dstmtE_succ (k : ℕ) (hk : 2 ≤ k) (hlow : ∀ j, 1 ≤ j → j ≤ k → DStmt.{u} j)
    (hB : BStmt.{u} (k + 1)) : ∀ N, DStmtE.{u} (k + 1) N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro W _ _ G _ hN hconn hn h2k y w hy hw hyw
  have hG := degree_pos_of_connected hconn hyw
  -- Case 1: two even neighbours
  by_cases h1 : ∃ v₁ ∈ evenSet G, ∃ v₂ ∈ evenSet G, v₁ ≠ v₂ ∧ G.Adj y v₁ ∧ G.Adj y v₂
  · exact hB W G hconn hn h2k y w hy hw hyw h1
  have huniq : ∀ t ∈ evenSet G, G.Adj y t → ∀ v ∈ evenSet G, G.Adj y v → v = t := by
    intro t ht hyt v hv hyv
    by_contra hvt
    exact h1 ⟨t, ht, v, hv, Ne.symm hvt, hyt, hyv⟩
  -- Case 2: a non-pendant bridge at `y`
  by_cases h2 : ∃ t, G.Adj y t ∧ G.IsBridge s(y, t) ∧ 2 ≤ G.degree t
  · obtain ⟨t, hyt, hbr, hdt⟩ := h2
    have hN1 : 1 ≤ N := by
      have : 0 < G.edgeFinset.card := Finset.card_pos.mpr ⟨s(y, t), mem_edgeFinset.mpr hyt⟩
      omega
    have hIH : DStmtE.{u} (k + 1) (N - 1) := ih (N - 1) (by omega)
    have hEM : G.edgeFinset.card ≤ (N - 1) + 1 := by omega
    classical
    have hnr : ¬ (delE G {s(y, t)}).Reachable y t := by
      rw [isBridge_iff] at hbr; simpa [delE] using hbr
    let A : Finset W := Finset.univ.filter (fun v => (delE G {s(y, t)}).Reachable y v)
    have hmemA : ∀ v, v ∈ A ↔ (delE G {s(y, t)}).Reachable y v := by simp [A]
    have hyA : y ∈ A := (hmemA y).2 (Reachable.refl _)
    have htA : t ∉ A := fun h => hnr ((hmemA t).1 h)
    have hcross : ∀ a b, G.Adj a b → a ∈ A → b ∉ A → a = y ∧ b = t := by
      intro a b hab ha hb
      by_cases he : s(a, b) = s(y, t)
      · rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1, h2⟩
        · exact absurd (h1 ▸ ha) htA
      · exact absurd ((hmemA b).2 (((hmemA a).1 ha).trans
          (delE_adj.mpr ⟨hab, by simpa using he⟩).reachable)) hb
    have hreachA : ∀ v ∈ A, (restr G A).Reachable y v := by
      intro v hv
      obtain ⟨p⟩ := (hmemA v).1 hv
      exact restr_reachable_of_walk p (fun x hx => (hmemA x).2 ⟨p.takeUntil x hx⟩)
    have hreachB : ∀ v ∉ A, (restr G Aᶜ).Reachable t v := by
      intro v hv
      have hvt : (delE G {s(y, t)}).Reachable t v :=
        ((delE_reach_or_reach hconn y t v).resolve_left (fun h => hv ((hmemA v).2 h.symm))).symm
      obtain ⟨p⟩ := hvt
      refine restr_reachable_of_walk p (fun x hx => Finset.mem_compl.mpr (fun hxA => ?_))
      exact hnr (((hmemA x).1 hxA).trans ⟨(p.takeUntil x hx).reverse⟩)
    rcases Nat.even_or_odd A.card with hAe | hAo
    · exact bridge_even (by omega) hlow hIH hG hn hEM h2k hy hw hyw hyt hdt hyA htA hcross
        hreachA hreachB hAe
    · exact bridge_odd hlow hIH hG hn hEM h2k hy hw hyw hyt hdt hyA htA hcross hreachA
        hreachB hAo
  -- Case 3: the only even neighbour, through a non-bridge
  by_cases h3 : ∃ t ∈ evenSet G, G.Adj y t ∧ ¬ G.IsBridge s(y, t)
  · obtain ⟨t, ht, hyt, hnb⟩ := h3
    have hKconn := connected_delE_of_not_isBridge hconn hnb
    have hEvK := evenSet_delE_even hy ht hyt
    have hcardK : 2 * k ≤ (evenSet (delE G {s(y, t)})).card := by
      rw [hEvK, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hyt.ne.symm, ht⟩),
        Finset.card_erase_of_mem hy]
      omega
    have hE2 : 1 < (evenSet (delE G {s(y, t)})).card := by omega
    by_cases hwt : w = t
    · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hE2
      exact desc_succ_of_transfer hG hy hw hyw ht hyt (huniq t ht hyt)
        (hlow k (by omega) le_rfl W _ hKconn hn hcardK a b ha hb hab) (Or.inl hwt)
    · have hwK : w ∈ evenSet (delE G {s(y, t)}) := by
        rw [hEvK]; exact Finset.mem_erase.mpr ⟨hwt, Finset.mem_erase.mpr ⟨Ne.symm hyw, hw⟩⟩
      obtain ⟨a, ha, haw⟩ := Finset.exists_mem_ne hE2 w
      exact desc_succ_of_transfer hG hy hw hyw ht hyt (huniq t ht hyt)
        (hlow k (by omega) le_rfl W _ hKconn hn hcardK a w ha hwK haw) (Or.inr rfl)
  -- Case 4: no even neighbour; delete a non-bridge edge to an odd neighbour
  have hnoev : ∀ v ∈ evenSet G, ¬ G.Adj y v := by
    intro t ht hyt
    have hbr : G.IsBridge s(y, t) := by
      by_contra h; exact h3 ⟨t, ht, hyt, h⟩
    obtain ⟨-, j, hj⟩ := mem_evenSet_iff_even.mp ht
    have := hG t
    exact h2 ⟨t, hyt, hbr, by omega⟩
  obtain ⟨t, hyt, hnb⟩ : ∃ t, G.Adj y t ∧ ¬ G.IsBridge s(y, t) := by
    by_contra hall
    push Not at hall
    -- every neighbour of `y` is a leaf
    have hleaf : ∀ c, G.Adj y c → ∀ d, G.Adj c d → d = y := by
      intro c hyc d hcd
      have hdeg : G.degree c ≤ 1 := by
        by_contra h; exact h2 ⟨c, hyc, hall c hyc, by omega⟩
      by_contra hdy
      have : 2 ≤ G.degree c := by
        rw [← card_neighborFinset_eq_degree]
        have hsub : ({y, d} : Finset W) ⊆ G.neighborFinset c := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact (mem_neighborFinset _ _ _).mpr hyc.symm
          · exact (mem_neighborFinset _ _ _).mpr hcd
        have := Finset.card_le_card hsub
        rwa [Finset.card_pair (Ne.symm hdy)] at this
      omega
    obtain ⟨p⟩ := hconn.preconnected y w
    have hpp := p.bypass_isPath
    cases hq : p.bypass with
    | nil => exact hyw rfl
    | @cons _ c _ hyc q =>
      rw [hq, Walk.cons_isPath_iff] at hpp
      cases q with
      | nil =>
        obtain ⟨-, j, hj⟩ := mem_evenSet_iff_even.mp hw
        have := hleaf w hyc
        have hdw : G.degree w ≤ 1 := by
          rw [← card_neighborFinset_eq_degree]
          apply Finset.card_le_one.mpr
          intro a ha b hb
          rw [hleaf w hyc a ((mem_neighborFinset _ _ _).mp ha),
            hleaf w hyc b ((mem_neighborFinset _ _ _).mp hb)]
        have := hG w
        omega
      | cons hcd q' =>
        have := hleaf c hyc _ hcd
        subst this
        exact hpp.2 (by simp)
  have htE : t ∉ evenSet G := fun h => hnoev t h hyt
  have hKconn := connected_delE_of_not_isBridge hconn hnb
  have hKpos := degree_pos_of_connected hKconn hyt.ne
  have hEvK := evenSet_delE_odd hG hy htE hyt (hKpos t)
  have hlt := card_edgeFinset_delE_lt hyt
  have hwK : w ∈ evenSet (delE G {s(y, t)}) := by
    rw [hEvK]; exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hyw, hw⟩)
  have htK : t ∈ evenSet (delE G {s(y, t)}) := by rw [hEvK]; exact Finset.mem_insert_self _ _
  have hcardK : 2 * (k + 1) ≤ (evenSet (delE G {s(y, t)})).card := by
    rw [hEvK, Finset.card_insert_of_notMem (fun h => htE (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem hy]
    have : 0 < (evenSet G).card := Finset.card_pos.mpr ⟨y, hy⟩
    omega
  have hdesc := ih _ (by omega) W _ le_rfl hKconn hn hcardK t w htK hwK
    (fun h => htE (h ▸ hw))
  exact desc_lift_of_no_even_nbr hG hy hnoev hyt (hKpos t) (by simpa using hw)
    (by simpa using hyw) hdesc

end reduction

/-! ## Part 7: consequences -/

/-- `D_1` is Lemma 3. -/
theorem dstmt_one : DStmt.{u} 1 := by
  intro W _ _ H _ hconn hn h2 y w hy hw hyw
  have hG := degree_pos_of_connected hconn hyw
  refine ⟨{w}, by simpa using hw, by simp, le_rfl, by simpa using hyw, ?_⟩
  have := realisable_evenSet_erase' hG hn hw
  rwa [Finset.erase_eq] at this

/-- `D_2` is two-step descent. -/
theorem dstmt_two : DStmt.{u} 2 := by
  intro W _ _ H _ hconn hn h4 y w hy hw hyw
  obtain ⟨s, hs, hsy, ⟨p⟩⟩ : ∃ s ∈ evenSet H, s ≠ y ∧ H.Reachable y s :=
    ⟨w, hw, Ne.symm hyw, hconn.preconnected y w⟩
  exact desc_two_of_reachable lovaszStatement hn H y w
    (degree_pos_of_connected hconn hyw) hy hw hyw (by omega) ⟨s, hs, hsy, ⟨p⟩⟩

/-- **Reduction to the branching case.** `B_3, …, B_K` imply `D_1, …, D_K`. -/
theorem dstmt_of_branching (K : ℕ) (hB : ∀ j, 3 ≤ j → j ≤ K → BStmt.{u} j) :
    ∀ k, 1 ≤ k → k ≤ K → DStmt.{u} k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk1 hkK
  rcases (show k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | hk3
  · exact dstmt_one
  · exact dstmt_two
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hD := dstmtE_succ m (by omega) (fun j hj1 hjm => ih j (by omega) hj1 (by omega))
      (hB (m + 1) hk3 hkK)
    intro W _ _ H _ hconn hn h2 y w hy hw hyw
    exact hD _ W H le_rfl hconn hn h2 y w hy hw hyw

/-- The rooted test at a graph with `2k` even vertices follows from `D_k`. -/
theorem rooted_of_dstmt {W : Type u} [Fintype W] [DecidableEq W] {H : SimpleGraph W}
    [DecidableRel H.Adj] (hconn : H.Connected) (hn : Even (Fintype.card W)) (r : W)
    (hD : ∀ k, 1 ≤ k → 2 * k = (evenSet H).card → DStmt.{u} k) :
    pathNumber (addLeaf H r) ≤ Fintype.card W / 2 := by
  have h2 : 1 < Fintype.card W := by
    have := Fintype.card_pos_iff.mpr ⟨r⟩
    obtain ⟨m, hm⟩ := hn
    omega
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card h2
  have hG := degree_pos_of_connected hconn hab
  have hc := card_oddSet_add_card_evenSet hG
  obtain ⟨m, hm⟩ := H.even_card_odd_degree_vertices
  have hm' : (oddSet H).card = m + m := hm
  obtain ⟨e2, he2⟩ : Even (evenSet H).card := by
    obtain ⟨c, hc'⟩ := hn; exact ⟨c - m, by omega⟩
  rcases Nat.eq_zero_or_pos e2 with he | he
  · obtain ⟨hSE, D, hDr⟩ := realisable_evenSet' hG
    have := pathNumber_addLeaf_le_of_realises hG hSE hDr (r := r) (fun h => h)
    omega
  · obtain ⟨y, w, hy, hw, hyw, hry⟩ : ∃ y w, y ∈ evenSet H ∧ w ∈ evenSet H ∧ y ≠ w ∧
        (r ∈ evenSet H → y = r) := by
      have h1 : 1 < (evenSet H).card := by omega
      by_cases hr : r ∈ evenSet H
      · obtain ⟨w, hw, hwr⟩ := Finset.exists_mem_ne h1 r
        exact ⟨r, w, hr, hw, Ne.symm hwr, fun _ => rfl⟩
      · obtain ⟨y, hy, w, hw, hyw⟩ := Finset.one_lt_card.mp h1
        exact ⟨y, w, hy, hw, hyw, fun h => absurd h hr⟩
    obtain ⟨R, hRE, hRc, -, hyR, hSE, D, hDr⟩ :=
      hD e2 he (by omega) W H hconn hn (by omega) y w hy hw hyw
    have := pathNumber_addLeaf_le_of_realises hG hSE hDr (r := r) (fun h => by
      rw [← hry h]; exact Finset.mem_sdiff.mpr ⟨hy, hyR⟩)
    rw [Finset.card_sdiff_of_subset hRE] at this
    omega

/-- **`B_3` gives the rooted test for six even vertices** (test (i) at deletion degree 6). -/
theorem rooted_six_of_bstmt3 (hB3 : BStmt.{u} 3) {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] (hconn : H.Connected) (hn : Even (Fintype.card W))
    (h6 : (evenSet H).card = 6) (r : W) :
    pathNumber (addLeaf H r) ≤ Fintype.card W / 2 := by
  apply rooted_of_dstmt hconn hn r
  intro k hk1 hk
  exact dstmt_of_branching 3 (fun j hj3 hj => by
    obtain rfl : j = 3 := by omega
    exact hB3) k hk1 (by omega)

/-- **Gallai's conjecture follows from `B_k` for every `k ≥ 3`**: k-step descent at even
vertices with at least two even neighbours. -/
theorem gallai_of_branching (hB : ∀ j, 3 ≤ j → BStmt.{u} j) : GallaiConjecture.{u} := by
  rw [gallai_iff_rootedTest]
  intro W _ _ H hconn hn r
  classical
  exact rooted_of_dstmt hconn hn r (fun k hk1 _ =>
    dstmt_of_branching k (fun j hj3 _ => hB j hj3) k hk1 le_rfl)

end Gallai
