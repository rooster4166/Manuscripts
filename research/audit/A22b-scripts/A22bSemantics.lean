import GallaiLean.TerminalMatching
/-! Audit A22b: `NoShortCycleAt G S` is exactly "every cycle (in Mathlib's sense, `Walk.IsCycle`)
through a vertex of `S` has length at least five".  Run:
`cd lean && lake env lean ../research/audit/A22b-scripts/A22bSemantics.lean` -/
open SimpleGraph

namespace Gallai

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Based form: cycles starting at a vertex of `S`. -/
theorem noShortCycleAt_iff_based (G : SimpleGraph W) (S : W → Prop) :
    NoShortCycleAt G S ↔ ∀ u, S u → ∀ c : G.Walk u u, c.IsCycle → 5 ≤ c.length := by
  constructor
  · intro h u hu c hc
    by_contra hlt
    have hl3 := hc.three_le_length
    cases c with
    | nil => simp at hl3
    | cons h1 c =>
      cases c with
      | nil => simp at hl3
      | cons h2 c =>
        cases c with
        | nil => simp at hl3
        | cons h3 c =>
          cases c with
          | nil => exact h.1 _ _ _ hu h1 h2 h3
          | cons h4 c =>
            cases c with
            | nil =>
              have hn := hc.support_nodup
              simp only [Walk.support_cons, Walk.support_nil, List.tail_cons, List.nodup_cons,
                List.mem_cons, List.not_mem_nil] at hn
              exact h.2 _ _ _ _ hu h1 h2 h3 h4 (fun e => by subst e; tauto) (fun e => by subst e; tauto)
            | cons h5 c => simp at hlt
  · intro h
    refine ⟨fun u v w hu h1 h2 h3 => ?_, fun u v w t hu h1 h2 h3 h4 huw hvt => ?_⟩
    · have n1 := h1.ne; have n2 := h2.ne; have n3 := h3.ne
      have n1' := h1.ne.symm; have n2' := h2.ne.symm; have n3' := h3.ne.symm
      have hc : (Walk.cons h1 (Walk.cons h2 (Walk.cons h3 Walk.nil))).IsCycle := by
        rw [Walk.cons_isCycle_iff]
        simp [Walk.cons_isPath_iff]
        tauto
      have := h u hu _ hc
      simp at this
    · have n1 := h1.ne; have n2 := h2.ne; have n3 := h3.ne; have n4 := h4.ne
      have n1' := h1.ne.symm; have n2' := h2.ne.symm; have n3' := h3.ne.symm
      have n4' := h4.ne.symm; have huw' := huw.symm; have hvt' := hvt.symm
      have hc : (Walk.cons h1 (Walk.cons h2 (Walk.cons h3 (Walk.cons h4 Walk.nil)))).IsCycle := by
        rw [Walk.cons_isCycle_iff]
        simp [Walk.cons_isPath_iff]
        tauto
      have := h u hu _ hc
      simp at this

/-- Unbased form: every cycle whose support meets `S` has length at least five. -/
theorem noShortCycleAt_iff (G : SimpleGraph W) (S : W → Prop) :
    NoShortCycleAt G S ↔
      ∀ v (c : G.Walk v v), c.IsCycle → (∃ u ∈ c.support, S u) → 5 ≤ c.length := by
  rw [noShortCycleAt_iff_based]
  constructor
  · rintro h v c hc ⟨u, hu, hSu⟩
    have := h u hSu (c.rotate u hu) (hc.rotate hu)
    simpa using this
  · intro h u hu c hc
    exact h u c hc ⟨u, c.start_mem_support, hu⟩

end Gallai

#print axioms Gallai.noShortCycleAt_iff
