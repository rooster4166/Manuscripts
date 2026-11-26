import GallaiLean.KStep

/-!
# Bridges, and the reduction of k-step descent to the branching case

Endpoint-structure manuscript, subsection "Bridges, and reduction to the branching case".

## Part 1: transport along an injective map, and induced graphs

* `GPath.mapInj`, `PathDecomp.mapInj`: push paths and decompositions along an injective vertex
  map whose image of the edge set is exactly the target edge set; end counts are preserved at
  images and vanish off the image.
* `realisable_of_induce`, `desc_of_induce`: a set `s` containing every edge of `H`; realisations
  and descents in `H.induce s` transport to `H`.
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

end Gallai
