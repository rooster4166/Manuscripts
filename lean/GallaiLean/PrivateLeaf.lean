import GallaiLean.Doubling

/-!
# The private-leaf formula

For a graph `G`, a vertex `x` and a decomposition `D` of `G`, let
`leafCost D x = |D| + [x is not an end of D]`.

* `pathNumber_addLeaf_le`: `p(G + leaf at x) ≤ leafCost D x` for every `D`
  (extend a path ending at `x` by the leaf edge, or add the leaf edge as a new path).
* `exists_leafCost_le`: some `D` has `leafCost D x ≤ p(G + leaf at x)` (trim the leaf edge; if
  the leaf path had other edges, its trimmed piece ends at `x`).
* `pathNumber_addLeaf_eq`: `p(G + leaf at x) = min_D leafCost D x`.
* `PathDecomp.exists_end`: splitting a path at an internal visit of `x` (for `deg x > 0`) makes
  `x` an end at the cost of one extra path.
* `exists_end_of_pathNumber_lt`, `pathNumber_addLeaf_le_of_lt`: if `p(G) < k` then `G` has a
  decomposition of size `≤ k` with an end at `x` (for `deg x > 0`), hence `p(G + leaf at x) ≤ k`.
-/

open SimpleGraph

namespace Gallai

universe u

variable {W : Type u} {G : SimpleGraph W} {x : W}

/-! ### Copying paths of `G` into `addLeaf G x` -/

theorem some_map_mem {P : GPath G} {e : Sym2 W} (he : e ∈ P.walk.edges) :
    e.map some ∈ (addLeaf G x).edgeSet := by
  have heG := P.walk.edges_subset_edgeSet he
  induction e using Sym2.inductionOn with
  | hf a b => simpa using heG

/-- The copy of a path of `G` in `addLeaf G x`. -/
def GPath.toAddLeaf (P : GPath G) (x : W) : GPath (addLeaf G x) :=
  P.push some (fun _ he => some_map_mem he) (fun _ _ _ _ h => Option.some_injective _ h)

@[simp] theorem GPath.toAddLeaf_edges (P : GPath G) (x : W) :
    (P.toAddLeaf x).edges = P.edges.map (Sym2.map some) := GPath.push_edges ..

/-- The leaf edge as a path. -/
def leafPath (G : SimpleGraph W) (x : W) : GPath (addLeaf G x) :=
  GPath.ofAdj (show (addLeaf G x).Adj none (some x) from rfl)

@[simp] theorem leafPath_edges : (leafPath G x).edges = [s(none, some x)] := rfl

/-- A path of `G` starting at `x`, extended by the leaf edge. -/
def GPath.extendLeaf (P : GPath G) (hP : P.src = x) : GPath (addLeaf G x) where
  src := none
  tgt := some P.tgt
  walk := Walk.cons (show (addLeaf G x).Adj none (some P.src) from hP)
    (pushWalk some P.walk (fun _ he => some_map_mem he))
  isPath := by
    rw [Walk.cons_isPath_iff]
    refine ⟨pushWalk_isPath _ _ _ P.isPath (fun _ _ _ _ h => Option.some_injective _ h), ?_⟩
    simp
  pos := by simp

@[simp] theorem GPath.extendLeaf_edges (P : GPath G) (hP : P.src = x) :
    (P.extendLeaf hP).edges = s(none, some x) :: P.edges.map (Sym2.map some) := by
  simp [GPath.extendLeaf, GPath.edges, hP]

theorem mem_addLeaf_edgeSet_iff {e : Sym2 (Option W)} :
    e ∈ (addLeaf G x).edgeSet ↔ e = s(none, some x) ∨ ∃ e' ∈ G.edgeSet, e'.map some = e := by
  induction e using Sym2.inductionOn with
  | hf a b =>
  rw [mem_edgeSet]
  rcases a with _ | a <;> rcases b with _ | b
  · simp only [addLeaf_not_adj_none_none, false_iff, not_or, not_exists, not_and]
    refine ⟨by simp, fun e' _ h => ?_⟩
    have : none ∈ e'.map some := h ▸ Sym2.mem_mk_left _ _
    simp [Sym2.mem_map] at this
  · rw [addLeaf_adj_none_some]
    constructor
    · rintro rfl; exact Or.inl rfl
    · rintro (h | ⟨e', _, h⟩)
      · simpa using h
      · have : none ∈ e'.map some := h ▸ Sym2.mem_mk_left _ _
        simp [Sym2.mem_map] at this
  · rw [addLeaf_adj_some_none]
    constructor
    · rintro rfl; exact Or.inl Sym2.eq_swap
    · rintro (h | ⟨e', _, h⟩)
      · rw [Sym2.eq_swap] at h; simpa using h
      · have : none ∈ e'.map some := h ▸ Sym2.mem_mk_right _ _
        simp [Sym2.mem_map] at this
  · rw [addLeaf_adj_some_some]
    constructor
    · intro h; exact Or.inr ⟨s(a, b), h, rfl⟩
    · rintro (h | ⟨e', he', h⟩)
      · simp at h
      · induction e' using Sym2.inductionOn with
        | hf c d =>
        simp only [Sym2.map_mk, Sym2.eq_iff, Option.some.injEq] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact he'
        · exact G.symm.symm _ _ he'

/-- The edge list `leaf :: (edges of D, copied)`. -/
def leafEdges (D : PathDecomp G) (x : W) : List (Sym2 (Option W)) :=
  s(none, some x) :: (D.paths.flatMap GPath.edges).map (Sym2.map some)

theorem leafEdges_nodup (D : PathDecomp G) (x : W) : (leafEdges D x).Nodup := by
  rw [leafEdges, List.nodup_cons]
  refine ⟨fun h => ?_, D.nodup_edges.map (Sym2.map.injective (Option.some_injective _))⟩
  obtain ⟨e, _, he⟩ := List.mem_map.mp h
  have : none ∈ e.map some := he ▸ Sym2.mem_mk_left _ _
  simp [Sym2.mem_map] at this

theorem leafEdges_cov (D : PathDecomp G) (x : W) :
    ∀ e, e ∈ (addLeaf G x).edgeSet ↔ e ∈ leafEdges D x := by
  intro e
  rw [mem_addLeaf_edgeSet_iff, leafEdges, List.mem_cons, List.mem_map]
  simp only [← D.covers]

/-! ### The upper bound -/

/-- `|D| + [x is not an end of D]`. -/
def leafCost [DecidableEq W] (D : PathDecomp G) (x : W) : ℕ :=
  D.size + if D.ends x = 0 then 1 else 0

theorem pathNumber_addLeaf_le [DecidableEq W] (D : PathDecomp G) (x : W) :
    pathNumber (addLeaf G x) ≤ leafCost D x := by
  unfold leafCost
  split_ifs with h
  · -- add the leaf edge as its own path
    let L := leafPath G x :: D.paths.map (·.toAddLeaf x)
    have hperm : (L.flatMap GPath.edges).Perm (leafEdges D x) := by
      simp [L, leafEdges, List.flatMap_map, List.map_flatMap]
    have := pathNumber_le (PathDecomp.ofPerm L _ hperm (leafEdges_nodup D x) (leafEdges_cov D x))
    simpa [PathDecomp.size, L] using this
  · -- extend a path with an end at `x`
    obtain ⟨Q, hQ, hQx⟩ : ∃ Q ∈ D.paths, Q.endsAt x ≠ 0 := by
      by_contra hc
      push Not at hc
      apply h
      unfold PathDecomp.ends
      exact List.sum_eq_zero_iff_forall_eq_nat.mpr (by simpa using hc)
    obtain ⟨Q', hQ's, hQ'e⟩ : ∃ Q' : GPath G, Q'.src = x ∧ Q'.edges.Perm Q.edges := by
      unfold GPath.endsAt at hQx
      by_cases hs : Q.src = x
      · exact ⟨Q, hs, List.Perm.refl _⟩
      · have ht : Q.tgt = x := by
          by_contra ht; simp [hs, ht] at hQx
        exact ⟨Q.reverse, ht, by simp [List.reverse_perm]⟩
    obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hQ
    let L := l₁.map (·.toAddLeaf x) ++ Q'.extendLeaf hQ's :: l₂.map (·.toAddLeaf x)
    have hperm : (L.flatMap GPath.edges).Perm (leafEdges D x) := by
      simp only [L, leafEdges, hl, List.flatMap_append, List.flatMap_cons, List.flatMap_map,
        GPath.toAddLeaf_edges, GPath.extendLeaf_edges, List.map_append, List.map_flatMap]
      refine List.perm_middle.trans ?_
      refine List.Perm.cons _ ?_
      refine List.Perm.append_left _ ?_
      exact (hQ'e.map _).append_right _
    have := pathNumber_le (PathDecomp.ofPerm L _ hperm (leafEdges_nodup D x) (leafEdges_cov D x))
    simpa [PathDecomp.size, L, hl] using this

/-! ### The lower bound -/

/-- On a path through the leaf edge with some other edge, exactly one of the remaining edges
meets `x`. -/
theorem leaf_path_count [DecidableEq W] (Q : GPath (addLeaf G x)) (hl : s(none, some x) ∈ Q.edges)
    (hS : Q.edges.any bothSome = true) :
    (Q.edges.filter bothSome).countP (fun e => decide (x ∈ e.map (unSome x))) = 1 := by
  have key : ∀ Q : GPath (addLeaf G x), Q.src = none → Q.edges.any bothSome = true →
      (Q.edges.filter bothSome).countP (fun e => decide (x ∈ e.map (unSome x))) = 1 := by
    rintro ⟨s, t, w, hw, hpos⟩ (rfl : s = none) hS
    obtain ⟨c, h, q, rfl⟩ := Walk.exists_eq_cons_of_length_pos w hpos
    rw [Walk.cons_isPath_iff] at hw
    cases c with
    | none => exact absurd h addLeaf_not_adj_none_none
    | some c =>
    have hc : c = x := h
    subst hc
    have hfilt : (s(none, some c) :: q.edges).filter bothSome = q.edges := by
      rw [List.filter_cons, filter_bothSome_of_avoid q hw.2]; simp
    change ((s(none, some c) :: q.edges).filter bothSome).countP _ = 1
    change (s(none, some c) :: q.edges).any bothSome = true at hS
    rw [hfilt]
    have hqne : q.edges ≠ [] := by
      intro h0
      rw [h0] at hS
      simp at hS
    have hqpos : 0 < q.length := by
      rw [← Walk.length_edges]
      exact List.length_pos_iff.mpr hqne
    have hne : some c ≠ t := GPath.src_ne_tgt ⟨_, _, q, hw.1, hqpos⟩
    have hcount := Walk.countP_add_ends q hw.1 (some c)
    simp only [q.start_mem_support, ite_true, hne.symm, ite_false] at hcount
    rw [List.countP_congr (q := fun e => decide (some c ∈ e))]
    · omega
    · intro e he
      induction e using Sym2.inductionOn with
      | hf a b =>
      have ha := q.fst_mem_support_of_mem_edges he
      have hb := q.snd_mem_support_of_mem_edges he
      cases a with
      | none => exact absurd ha hw.2
      | some a =>
      cases b with
      | none => exact absurd hb hw.2
      | some b => simp [unSome, Sym2.mem_iff]
  have hn : none ∈ Q.walk.support := Q.walk.fst_mem_support_of_mem_edges hl
  rcases addLeaf_none_end Q hn with h | h
  · exact key Q h hS
  · have := key Q.reverse h (by simpa [List.any_reverse] using hS)
    simpa [List.filter_reverse] using this

theorem exists_leafCost_le [Finite W] [DecidableEq W] (G : SimpleGraph W) (x : W) :
    ∃ D : PathDecomp G, leafCost D x ≤ pathNumber (addLeaf G x) := by
  obtain ⟨D', hD'⟩ := pathNumber_spec (addLeaf G x)
  have hleaf : s(none, some x) ∈ (addLeaf G x).edgeSet := by
    rw [mem_edgeSet]; rfl
  obtain ⟨Q₀, hQ₀, hlQ₀⟩ := List.mem_flatMap.mp ((D'.covers _).1 hleaf)
  obtain ⟨D, hsize, hloc⟩ :=
    D'.project_spec (unSome x) bothSome _ trim_injOn trim_hT trim_hcov trim_hasPiece
  refine ⟨D, ?_⟩
  unfold leafCost
  by_cases hS : Q₀.edges.any bothSome = true
  · obtain ⟨R, hR, hRe⟩ := hloc Q₀ hQ₀ hS
    have hinc : R.incid x = 1 := by
      unfold GPath.incid
      rw [hRe.countP_eq, List.countP_map]
      simpa only [Function.comp_def] using leaf_path_count Q₀ hlQ₀ hS
    have hend : R.endsAt x = 1 := by
      have := R.incid_add_endsAt x
      split_ifs at this <;> omega
    have hpos : 0 < D.ends x := by
      unfold PathDecomp.ends
      have : R.endsAt x ≤ (D.paths.map (fun P => P.endsAt x)).sum :=
        List.le_sum_of_mem (List.mem_map_of_mem hR)
      omega
    simp only [hpos.ne', ite_false, add_zero]
    have := hsize.trans (List.countP_le_length)
    rw [← hD']
    exact this
  · have hlt : D'.paths.countP (fun P => P.edges.any bothSome) < D'.paths.length := by
      rw [List.countP_eq_length_filter]
      exact List.length_filter_lt_length_iff_exists.mpr ⟨Q₀, hQ₀, by simpa using hS⟩
    rw [← hD']
    unfold PathDecomp.size at *
    split_ifs <;> omega

/-- **The private-leaf formula**: `p(G + leaf at x) = min_D (|D| + [x is not an end of D])`. -/
theorem pathNumber_addLeaf_eq [Finite W] [DecidableEq W] (G : SimpleGraph W) (x : W) :
    pathNumber (addLeaf G x) = sInf {k | ∃ D : PathDecomp G, leafCost D x = k} := by
  apply le_antisymm
  · obtain ⟨D₀⟩ := PathDecomp.nonempty G
    obtain ⟨D, hD⟩ := Nat.sInf_mem (s := {k | ∃ D : PathDecomp G, leafCost D x = k})
      ⟨_, D₀, rfl⟩
    rw [← hD]
    exact pathNumber_addLeaf_le D x
  · obtain ⟨D, hD⟩ := exists_leafCost_le G x
    exact (Nat.sInf_le (s := {k | ∃ D : PathDecomp G, leafCost D x = k}) ⟨D, rfl⟩).trans hD

/-! ### Splitting a path at an internal visit -/

/-- If `deg x > 0`, some decomposition with at most one more path has an end at `x`. -/
theorem PathDecomp.exists_end [DecidableEq W] (D : PathDecomp G) [Fintype (G.neighborSet x)]
    (hx : 0 < G.degree x) : ∃ D' : PathDecomp G, D'.size ≤ D.size + 1 ∧ 0 < D'.ends x := by
  by_cases h : 0 < D.ends x
  · exact ⟨D, by omega, h⟩
  have h0 : ∀ Q ∈ D.paths, Q.endsAt x = 0 := by
    intro Q hQ
    have : D.ends x = 0 := by omega
    unfold PathDecomp.ends at this
    exact List.sum_eq_zero_iff_forall_eq_nat.mp this _ (List.mem_map_of_mem hQ)
  obtain ⟨y, hy⟩ := (G.degree_pos_iff_exists_adj x).mp hx
  obtain ⟨Q, hQ, hxyQ⟩ := List.mem_flatMap.mp ((D.covers _).1 (G.mem_edgeSet.mpr hy))
  have hxQ : x ∈ Q.walk.support := Q.walk.fst_mem_support_of_mem_edges hxyQ
  have hQ0 := h0 Q hQ
  unfold GPath.endsAt at hQ0
  have hs : Q.src ≠ x := by intro hs; simp [hs] at hQ0
  have ht : Q.tgt ≠ x := by intro ht; simp [ht] at hQ0
  obtain ⟨q₁, q₂, hq⟩ := Walk.mem_support_iff_exists_append.mp hxQ
  have hpath : (q₁.append q₂).IsPath := hq ▸ Q.isPath
  have h₁ : 0 < q₁.length := by
    by_contra hc
    exact hs (Walk.eq_of_length_eq_zero (p := q₁) (by omega))
  have h₂ : 0 < q₂.length := by
    by_contra hc
    exact ht (Walk.eq_of_length_eq_zero (p := q₂) (by omega)).symm
  let Q₁ : GPath G := ⟨_, _, q₁, Walk.isPath_of_append_left hpath, h₁⟩
  let Q₂ : GPath G := ⟨_, _, q₂, Walk.isPath_of_append_right hpath, h₂⟩
  obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hQ
  let L := l₁ ++ Q₁ :: Q₂ :: l₂
  have hperm : (L.flatMap GPath.edges).Perm (D.paths.flatMap GPath.edges) := by
    have : Q.edges = Q₁.edges ++ Q₂.edges := by
      show Q.walk.edges = q₁.edges ++ q₂.edges
      rw [hq, Walk.edges_append]
    simp only [L, hl, List.flatMap_append, List.flatMap_cons, this, List.append_assoc]
    exact List.Perm.refl _
  refine ⟨PathDecomp.ofPerm L _ hperm D.nodup_edges D.covers, ?_, ?_⟩
  · simp only [PathDecomp.size, PathDecomp.ofPerm_paths, L, hl, List.length_append,
      List.length_cons]
    omega
  · have : Q₁.endsAt x ≤ (L.map (fun P => P.endsAt x)).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem (by simp [L]))
    have h1 : Q₁.endsAt x = 1 := by
      simp only [GPath.endsAt, Q₁, hs, ite_false, ite_true]
    unfold PathDecomp.ends
    simp only [PathDecomp.ofPerm_paths]
    omega

/-- If `p(G) < k` and `deg x > 0`, then `G` has a decomposition of size `≤ k` with an end at
`x`. -/
theorem exists_end_of_pathNumber_lt [Finite W] [DecidableEq W] [Fintype (G.neighborSet x)]
    {k : ℕ} (hk : pathNumber G < k) (hx : 0 < G.degree x) :
    ∃ D : PathDecomp G, D.size ≤ k ∧ 0 < D.ends x := by
  obtain ⟨D, hD⟩ := pathNumber_spec G
  obtain ⟨D', h₁, h₂⟩ := D.exists_end hx
  exact ⟨D', by omega, h₂⟩

/-- If `p(G) < k` and `deg x > 0`, then `G` with a private leaf at `x` has a decomposition of
size `≤ k` (extend the path ending at `x` by the leaf edge). -/
theorem pathNumber_addLeaf_le_of_lt [Finite W] [Fintype (G.neighborSet x)]
    {k : ℕ} (hk : pathNumber G < k) (hx : 0 < G.degree x) : pathNumber (addLeaf G x) ≤ k := by
  classical
  obtain ⟨D, h₁, h₂⟩ := exists_end_of_pathNumber_lt hk hx
  have := pathNumber_addLeaf_le D x
  unfold leafCost at this
  simp only [h₂.ne', ite_false, add_zero] at this
  omega

/-- The trivial bound `p(G + leaf) ≤ p(G) + 1` (any vertex). -/
theorem pathNumber_addLeaf_le_succ [Finite W] (G : SimpleGraph W) (x : W) :
    pathNumber (addLeaf G x) ≤ pathNumber G + 1 := by
  classical
  obtain ⟨D, hD⟩ := pathNumber_spec G
  have := pathNumber_addLeaf_le D x
  unfold leafCost at this
  split_ifs at this <;> omega

end Gallai
