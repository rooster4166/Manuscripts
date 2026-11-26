import GallaiLean.Surgery

/-!
# Deleting the vertices outside a retract

A `Retract K G` presents `G` as the subgraph of `K` induced by the *kept* vertices `ι '' V`,
together with a retraction `f` (`f ∘ ι = id`). Edges with both ends kept are the kept edges.

* `Retract.hasPiece`: a path of `K` whose non-kept vertices are among its ends has a piece in
  `G` (its kept edges form a single sub-path).
* `Retract.delete`: from a decomposition of `K` in which non-kept vertices are only ever ends of
  paths, deleting the non-kept vertices gives a decomposition `D'` of `G` with
  `D'.ends v = D.ends (ι v)` if `ι v` has no non-kept edge in `K`, and
  `D'.ends v ≤ D.ends (ι v) + 1` if `ι v` has at most one non-kept edge in `K`.

Both the apex extension (`Option V`, `ι = some`) and the private-leaf extension (`V ⊕ V`,
`ι = inl`) are instances.
-/

open SimpleGraph

namespace Gallai

universe u v

variable {U : Type v} {V : Type u}

/-- Edges with both ends kept. -/
def bothKept (k : U → Bool) : Sym2 U → Bool :=
  Sym2.lift ⟨fun x y => k x && k y, fun _ _ => Bool.and_comm _ _⟩

@[simp] theorem bothKept_mk (k : U → Bool) (x y : U) : bothKept k s(x, y) = (k x && k y) := rfl

theorem bothKept_iff (k : U → Bool) (e : Sym2 U) :
    bothKept k e = true ↔ ∀ x ∈ e, k x = true := by
  induction e using Sym2.inductionOn with
  | hf x y =>
    simp only [bothKept_mk, Bool.and_eq_true, Sym2.mem_iff]
    constructor
    · rintro ⟨h1, h2⟩ z (rfl | rfl) <;> assumption
    · intro h; exact ⟨h x (Or.inl rfl), h y (Or.inr rfl)⟩

theorem filter_bothKept_of_kept {K : SimpleGraph U} (k : U → Bool) {a b : U} (w : K.Walk a b)
    (hsupp : ∀ x ∈ w.support, k x = true) : w.edges.filter (bothKept k) = w.edges :=
  List.filter_eq_self.2 fun e he =>
    (bothKept_iff k e).2 fun x hx => hsupp x (Walk.mem_support_of_mem_edge w he hx)

theorem countP_le_one_of_nodup {α : Type*} {l : List α} (hl : l.Nodup) (p : α → Bool)
    (h : ∀ x ∈ l, ∀ y ∈ l, p x = true → p y = true → x = y) : l.countP p ≤ 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    have ih := ih hl.2 (fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y
      (List.mem_cons_of_mem _ hy))
    rw [List.countP_cons]
    by_cases hpa : p a = true
    · have : l.countP p = 0 := by
        rw [List.countP_eq_zero]
        intro y hy hpy
        have := h a List.mem_cons_self y (List.mem_cons_of_mem _ hy) hpa hpy
        subst this
        exact hl.1 hy
      simp [hpa, this]
    · simp only [hpa, Bool.false_eq_true, ite_false, add_zero]
      exact ih

/-- Strip a non-kept first vertex. -/
theorem strip_start {K : SimpleGraph U} (k : U → Bool) {a b : U} (p : K.Walk a b)
    (hp : p.IsPath) (hk : ∀ x ∈ p.support, k x = false → x = a ∨ x = b) :
    ∃ (a' : U) (q : K.Walk a' b), q.IsPath ∧ (∀ x ∈ q.support, k x = false → x = b) ∧
      p.edges.filter (bothKept k) = q.edges.filter (bothKept k) := by
  cases hka : k a
  · cases p with
    | nil => exact ⟨_, Walk.nil, hp, fun x hx _ => by simpa using hx, rfl⟩
    | cons h q =>
      rw [Walk.cons_isPath_iff] at hp
      refine ⟨_, q, hp.1, fun x hx hkx => ?_, ?_⟩
      · rcases hk x (by simp [hx]) hkx with rfl | rfl
        · exact absurd hx hp.2
        · rfl
      · rw [Walk.edges_cons, List.filter_cons]
        simp [hka]
  · refine ⟨a, p, hp, fun x hx hkx => ?_, rfl⟩
    rcases hk x hx hkx with rfl | rfl
    · rw [hka] at hkx; exact absurd hkx (by simp)
    · rfl

/-- `G` is the subgraph of `K` induced by the kept vertices `ι '' V`, with retraction `f`. -/
structure Retract (K : SimpleGraph U) (G : SimpleGraph V) where
  ι : V → U
  f : U → V
  kept : U → Bool
  f_ι : ∀ a, f (ι a) = a
  kept_iff : ∀ x, kept x = true ↔ ∃ a, ι a = x
  adj_iff : ∀ a b, K.Adj (ι a) (ι b) ↔ G.Adj a b

namespace Retract

variable {K : SimpleGraph U} {G : SimpleGraph V} (R : Retract K G)

theorem ι_injective : Function.Injective R.ι := fun a b h => by
  rw [← R.f_ι a, h, R.f_ι]

theorem kept_ι (a : V) : R.kept (R.ι a) = true := (R.kept_iff _).2 ⟨a, rfl⟩

theorem injOn : Set.InjOn R.f {x | R.kept x = true} := by
  intro x hx y hy h
  obtain ⟨a, rfl⟩ := (R.kept_iff x).1 hx
  obtain ⟨b, rfl⟩ := (R.kept_iff y).1 hy
  rw [R.f_ι, R.f_ι] at h
  rw [h]

theorem hT : ∀ e ∈ K.edgeSet, bothKept R.kept e = true → ∀ x ∈ e, x ∈ {x | R.kept x = true} :=
  fun e _ hS x hx => (bothKept_iff _ e).1 hS x hx

theorem hcov : ∀ e', e' ∈ G.edgeSet ↔
    ∃ e ∈ K.edgeSet, bothKept R.kept e = true ∧ e.map R.f = e' := by
  intro e'
  induction e' using Sym2.inductionOn with
  | hf a b =>
  constructor
  · intro h
    refine ⟨s(R.ι a, R.ι b), (R.adj_iff a b).2 h, by simp [R.kept_ι], by simp [R.f_ι]⟩
  · rintro ⟨e, he, hS, hmap⟩
    induction e using Sym2.inductionOn with
    | hf x y =>
    simp only [bothKept_mk, Bool.and_eq_true] at hS
    obtain ⟨c, rfl⟩ := (R.kept_iff x).1 hS.1
    obtain ⟨d, rfl⟩ := (R.kept_iff y).1 hS.2
    simp only [Sym2.map_mk, R.f_ι] at hmap
    rw [← hmap]
    exact (R.adj_iff c d).1 he

theorem hasPiece_of_core {P : GPath K} {a b : U} (w : K.Walk a b) (hw : w.IsPath)
    (hsupp : ∀ x ∈ w.support, R.kept x = true)
    (hperm : w.edges.Perm (P.edges.filter (bothKept R.kept))) :
    HasPiece G R.f (bothKept R.kept) P := by
  refine hasPiece_of_walk w hw ?_ ?_ hperm
  · intro e he
    refine (R.hcov _).2 ⟨e, w.edges_subset_edgeSet he, ?_, rfl⟩
    exact (bothKept_iff _ e).2 (fun x hx => hsupp x (Walk.mem_support_of_mem_edge w he hx))
  · intro x hx y hy h
    exact R.injOn (hsupp x hx) (hsupp y hy) h

/-- A path whose non-kept vertices are among its ends has a piece in `G`. -/
theorem hasPiece (P : GPath K)
    (hP : ∀ x ∈ P.walk.support, R.kept x = false → x = P.src ∨ x = P.tgt) :
    HasPiece G R.f (bothKept R.kept) P := by
  obtain ⟨a', q, hq, hqk, hfilt⟩ := strip_start R.kept P.walk P.isPath hP
  cases hkt : R.kept P.tgt
  · rcases Nat.eq_zero_or_pos q.length with h0 | hpos
    · apply hasPiece_none
      rw [GPath.edges, hfilt]
      have : q.edges = [] := by
        rw [← List.length_eq_zero_iff, Walk.length_edges]; exact h0
      rw [this]; rfl
    · obtain ⟨d, h, q'', hq''⟩ :=
        Walk.exists_eq_cons_of_length_pos q.reverse (by simpa using hpos)
      have hqr : q.reverse.IsPath := hq.reverse
      rw [hq'', Walk.cons_isPath_iff] at hqr
      have hsupp : ∀ x ∈ q''.support, R.kept x = true := by
        intro x hx
        by_contra hkx
        rw [Bool.not_eq_true] at hkx
        have hxq : x ∈ q.reverse.support := by rw [hq'']; simp [hx]
        rw [Walk.support_reverse, List.mem_reverse] at hxq
        have := hqk x hxq hkx
        subst this
        exact hqr.2 hx
      refine R.hasPiece_of_core q'' hqr.1 hsupp ?_
      have e1 : q.edges = (s(P.tgt, d) :: q''.edges).reverse := by
        rw [← Walk.edges_cons h q'', ← hq'', Walk.edges_reverse, List.reverse_reverse]
      rw [GPath.edges, hfilt, e1, List.filter_reverse, List.filter_cons]
      simp only [bothKept_mk, hkt, Bool.false_and, Bool.false_eq_true, ite_false,
        filter_bothKept_of_kept R.kept q'' hsupp]
      exact (List.reverse_perm _).symm
  · have hsupp : ∀ x ∈ q.support, R.kept x = true := by
      intro x hx
      by_contra hkx
      rw [Bool.not_eq_true] at hkx
      have := hqk x hx hkx
      subst this
      rw [hkt] at hkx
      exact absurd hkx (by simp)
    refine R.hasPiece_of_core q hq hsupp ?_
    rw [GPath.edges, hfilt, filter_bothKept_of_kept R.kept q hsupp]

theorem count_split [DecidableEq U] [DecidableEq V] (v : V) (l : List (Sym2 U)) :
    (l.filter (bothKept R.kept)).countP (fun e => decide (v ∈ e.map R.f)) +
      (l.filter (fun e => !bothKept R.kept e)).countP (fun e => decide (R.ι v ∈ e)) =
    l.countP (fun e => decide (R.ι v ∈ e)) := by
  rw [List.countP_eq_countP_filter_add l (fun e => decide (R.ι v ∈ e)) (bothKept R.kept)]
  congr 1
  apply List.countP_congr
  intro e he
  rw [List.mem_filter] at he
  have hk := (bothKept_iff _ e).1 he.2
  induction e using Sym2.inductionOn with
  | hf x y =>
  obtain ⟨c, rfl⟩ := (R.kept_iff x).1 (hk _ (Sym2.mem_mk_left _ _))
  obtain ⟨d, rfl⟩ := (R.kept_iff y).1 (hk _ (Sym2.mem_mk_right _ _))
  simp [Sym2.mem_iff, R.f_ι, R.ι_injective.eq_iff]

/-- **Deleting the non-kept vertices**, with control of the end counts. -/
theorem delete [DecidableEq U] [DecidableEq V] (D : PathDecomp K)
    (hD : ∀ P ∈ D.paths, ∀ x ∈ P.walk.support, R.kept x = false → x = P.src ∨ x = P.tgt) :
    ∃ D' : PathDecomp G, ∀ v,
      ((∀ e ∈ K.edgeSet, bothKept R.kept e = false → R.ι v ∉ e) →
        D'.ends v = D.ends (R.ι v)) ∧
      ((∀ e₁ ∈ K.edgeSet, ∀ e₂ ∈ K.edgeSet, bothKept R.kept e₁ = false →
          bothKept R.kept e₂ = false → R.ι v ∈ e₁ → R.ι v ∈ e₂ → e₁ = e₂) →
        D'.ends v ≤ D.ends (R.ι v) + 1) := by
  obtain ⟨D', -, -, hends⟩ := D.project_full R.f (bothKept R.kept) _ R.injOn R.hT R.hcov
    (fun P hP => R.hasPiece P (hD P hP))
  refine ⟨D', fun v => ?_⟩
  let c : GPath K → ℕ := fun P =>
    (P.edges.filter (bothKept R.kept)).countP (fun e => decide (v ∈ e.map R.f))
  let k : GPath K → ℕ := fun P =>
    (P.edges.filter (fun e => !bothKept R.kept e)).countP (fun e => decide (R.ι v ∈ e))
  have hid : ∀ P : GPath K, c P + k P = P.incid (R.ι v) := fun P => R.count_split v P.edges
  have hD' : D'.ends v = (D.paths.map (fun P => if c P = 1 then 1 else 0)).sum := by
    rw [hends v]
    congr 1
    apply List.map_congr_left
    intro P _
    simp only [c, List.countP_map, Function.comp_def]
  have hDι : D.ends (R.ι v) = (D.paths.map (fun P => if c P + k P = 1 then 1 else 0)).sum := by
    unfold PathDecomp.ends
    congr 1
    apply List.map_congr_left
    intro P _
    rw [GPath.endsAt_eq_ite, hid]
  constructor
  · intro hno
    rw [hD', hDι]
    congr 1
    apply List.map_congr_left
    intro P _
    have : k P = 0 := by
      simp only [k]
      rw [List.countP_eq_zero]
      intro e he hve
      rw [List.mem_filter] at he
      have heK := P.walk.edges_subset_edgeSet he.1
      exact hno e heK (by simpa using he.2) (by simpa using hve)
    rw [this, add_zero]
  · intro hone
    rw [hD', hDι]
    have hk1 : (D.paths.map k).sum ≤ 1 := by
      have h1 : (D.paths.map k).sum = (D.paths.flatMap GPath.edges).countP
          (fun e => decide (R.ι v ∈ e) && !bothKept R.kept e) := by
        rw [List.countP_flatMap]
        congr 1
        apply List.map_congr_left
        intro P _
        simp only [k, List.countP_filter, Function.comp_apply]
        rfl
      rw [h1]
      apply countP_le_one_of_nodup D.nodup_edges
      intro x hx y hy hpx hpy
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hpx hpy
      exact hone x ((D.covers x).2 hx) y ((D.covers y).2 hy) hpx.2 hpy.2 hpx.1 hpy.1
    calc (D.paths.map (fun P => if c P = 1 then 1 else 0)).sum
        ≤ (D.paths.map (fun P => (if c P + k P = 1 then 1 else 0) + k P)).sum :=
          sum_map_le_sum_map _ _ _ (fun P _ => by split_ifs <;> omega)
      _ = (D.paths.map (fun P => if c P + k P = 1 then 1 else 0)).sum + (D.paths.map k).sum :=
          sum_map_add' _ _ _
      _ ≤ _ := by omega

end Retract

end Gallai
