import GallaiLean.DirectTest1

/-! Auditor check (A28): an (E7)-branch append base of t6-dense at a labelling
`(x₁, y₁, x₂, y₂, x₃, y₃)` is, verbatim, a triangle base at the root `y₁`, with `w = x₃` and
`L = [(x₁, y₂), (x₂, y₃)]`. Only (E5) and (E7) are used; (E1)–(E4) are not. -/

namespace Gallai
open SimpleGraph

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

theorem pd_transport {K K' : SimpleGraph V} (h : K = K') (D : PathDecomp K) :
    ∃ D' : PathDecomp K', D'.paths.map (fun P => (P.src, P.tgt, P.walk.support)) =
      D.paths.map (fun P => (P.src, P.tgt, P.walk.support)) := by
  subst h; exact ⟨D, rfl⟩

theorem ends_eq_of_map {K K' : SimpleGraph V} {D : PathDecomp K} {D' : PathDecomp K'}
    (h : D'.paths.map (fun P => (P.src, P.tgt, P.walk.support)) =
      D.paths.map (fun P => (P.src, P.tgt, P.walk.support))) (v : V) : D'.ends v = D.ends v := by
  have h2 := congrArg (fun l => (l.map (fun t : V × V × List V =>
    (if t.1 = v then 1 else 0) + (if t.2.1 = v then 1 else 0))).sum) h
  simpa [PathDecomp.ends, GPath.endsAt, List.map_map, Function.comp_def] using h2

theorem avoid_of_map {K K' : SimpleGraph V} {D : PathDecomp K} {D' : PathDecomp K'}
    (h : D'.paths.map (fun P => (P.src, P.tgt, P.walk.support)) =
      D.paths.map (fun P => (P.src, P.tgt, P.walk.support))) {x y : V}
    (hD : ∀ P ∈ D.paths, (P.src = x ∨ P.tgt = x) → y ∉ P.walk.support) :
    ∀ P ∈ D'.paths, (P.src = x ∨ P.tgt = x) → y ∉ P.walk.support := by
  intro P hP hx
  have hm : (P.src, P.tgt, P.walk.support) ∈
      D.paths.map (fun P => (P.src, P.tgt, P.walk.support)) := by
    rw [← h]; exact List.mem_map_of_mem hP
  obtain ⟨Q, hQ, hQe⟩ := List.mem_map.mp hm
  simp only [Prod.mk.injEq] at hQe
  obtain ⟨h1, h2, h3⟩ := hQe
  rw [← h3]
  exact hD Q hQ (by rw [h1, h2]; exact hx)

/-- **(E5) + (E7) on the t6-dense base graph give a triangle base at `y₁`.** -/
theorem triangleBase_of_E5_E7 (J : SimpleGraph V) [DecidableRel J.Adj]
    {z x₁ y₁ x₂ y₂ x₃ y₃ : V}
    (hne : [z, x₁, y₁, x₂, y₂, x₃, y₃].Nodup)
    (hN : ∀ v, J.Adj z v ↔ v = x₁ ∨ v = y₁ ∨ v = x₂ ∨ v = y₂ ∨ v = x₃ ∨ v = y₃)
    (h₁₂ : J.Adj x₁ y₂) (h₂₃ : J.Adj x₂ y₃)
    (D₀ : PathDecomp (baseM J z x₁ x₂ y₂ x₃ y₃))
    (hD₀ : ∀ v, D₀.ends v = (baseM J z x₁ x₂ y₂ x₃ y₃).degree v % 2)
    (E5 : ∀ P ∈ D₀.paths, (P.src = x₂ ∨ P.tgt = x₂) → y₃ ∉ P.walk.support)
    (E7 : ∀ P ∈ D₀.paths, (P.src = x₁ ∨ P.tgt = x₁) → y₂ ∉ P.walk.support) :
    TriangleBase J z y₁ := by
  obtain ⟨hzx₁, hzy₁, hzx₂, hzy₂, hzx₃, hzy₃, hx₁y₁, hx₁x₂, hx₁y₂, hx₁x₃, hx₁y₃, hy₁x₂, hy₁y₂,
    hy₁x₃, hy₁y₃, hx₂y₂, hx₂x₃, hx₂y₃, hy₂x₃, hy₂y₃, hx₃y₃⟩ := nodup7 hne
  -- the two auxiliary graphs are the same graph
  have hEq : baseM J z x₁ x₂ y₂ x₃ y₃ = triM J z x₃ [(x₁, y₂), (x₂, y₃)] := by
    ext a b
    simp only [delList_adj, triDel, zDel, pairEdge, List.flatMap_cons, List.flatMap_nil,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false]
    tauto
  refine ⟨x₃, [(x₁, y₂), (x₂, y₃)], ⟨?_, ?_, ?_⟩, ?_⟩
  · simp only [pairVerts, List.flatMap_cons, List.flatMap_nil, List.cons_append,
      List.nil_append, List.append_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or, List.nodup_nil, and_true]
    exact ⟨⟨hy₁x₃, hx₁y₁.symm, hy₁y₂, hy₁x₂, hy₁y₃⟩,
      ⟨hx₁x₃.symm, hy₂x₃.symm, hx₂x₃.symm, hx₃y₃⟩, ⟨hx₁y₂, hx₁x₂, hx₁y₃⟩, ⟨hx₂y₂.symm, hy₂y₃⟩,
      hx₂y₃, not_false⟩
  · intro v
    rw [hN v]
    simp only [pairVerts, List.flatMap_cons, List.flatMap_nil, List.cons_append,
      List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact h₁₂
    · exact h₂₃
  · obtain ⟨D, hD⟩ := pd_transport hEq D₀
    refine ⟨D, fun v => ?_, ?_⟩
    · rw [ends_eq_of_map hD v, hD₀ v]
      congr 1
      exact degree_congr (fun w => by rw [hEq])
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact Or.inr (avoid_of_map hD E7)
      · exact Or.inr (avoid_of_map hD E5)

/-- The same, stated from `LovaszBase` whose last clause is the (E7) branch. -/
theorem triangleBase_of_lovaszBase_E7 (J : SimpleGraph V) [DecidableRel J.Adj]
    {z x₁ y₁ x₂ y₂ x₃ y₃ : V}
    (h : [z, x₁, y₁, x₂, y₂, x₃, y₃].Nodup ∧
      (∀ v, J.Adj z v ↔ v = x₁ ∨ v = y₁ ∨ v = x₂ ∨ v = y₂ ∨ v = x₃ ∨ v = y₃) ∧
      J.Adj x₁ y₂ ∧ J.Adj x₂ y₃ ∧
      ∃ D₀ : PathDecomp (baseM J z x₁ x₂ y₂ x₃ y₃),
        (∀ v, D₀.ends v = (baseM J z x₁ x₂ y₂ x₃ y₃).degree v % 2) ∧
        (∀ P ∈ D₀.paths, (P.src = x₂ ∨ P.tgt = x₂) → y₃ ∉ P.walk.support) ∧
        (∀ P ∈ D₀.paths, (P.src = x₁ ∨ P.tgt = x₁) → y₂ ∉ P.walk.support)) :
    TriangleBase J z y₁ := by
  obtain ⟨hne, hN, h₁₂, h₂₃, D₀, hD₀, E5, E7⟩ := h
  exact triangleBase_of_E5_E7 J hne hN h₁₂ h₂₃ D₀ hD₀ E5 E7

end Gallai

#print axioms Gallai.triangleBase_of_E5_E7
#print axioms Gallai.triangleBase_of_lovaszBase_E7
