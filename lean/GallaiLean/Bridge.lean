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

end glue

end Gallai
