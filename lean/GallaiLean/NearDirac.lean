import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Finite lemmas for `manuscripts/near-dirac`

The manuscript `manuscripts/near-dirac/near-dirac.tex` proves the *balanced return theorem*.
These two finite lemmas from it are cleanly separable from the asymptotic argument.

* `NearDirac.matrix_cut_ineq`: the real inequality that closes the max-flow cut check in the
  membership-matrix lemma (Lemma 3.1; SP Lemma 14.28). For `0 ≤ x, y ≤ 0.65`,
  `0.6x + 0.6y - 0.4 - xy + 0.03 min(x, y) < 0`.
* `NearDirac.dense_bipartite_hall`: the Hall step of the weaving lemma (Lemma 3.2; SP Lemma 14.29).
  If `|L| = |R| = k ≥ 4M` and every vertex on either side is related to at least `k - 2M`
  vertices of the other side, then `L` has a matching into `R`.
-/

namespace NearDirac

/-- One half of `matrix_cut_ineq`, on the region `y ≤ x`, where `min x y = y`. -/
theorem cut_ineq_aux (x y : ℝ) (hy0 : 0 ≤ y) (hyx : y ≤ x) (hx1 : x ≤ 13 / 20) :
    3 / 5 * x + 63 / 100 * y - 2 / 5 - x * y < 0 := by
  rcases le_total x (63 / 100) with h | h
  · -- `x ≤ 0.63`: use `(x - y)(0.63 - x) ≥ 0` and `(x - 0.615)^2 ≥ 0`.
    nlinarith [mul_nonneg (sub_nonneg.mpr hyx) (sub_nonneg.mpr h), sq_nonneg (x - 123 / 200)]
  · -- `x ≥ 0.63`: use `y (x - 0.63) ≥ 0` and `(x - 0.615)^2 ≥ 0`.
    nlinarith [mul_nonneg hy0 (sub_nonneg.mpr h), sq_nonneg (x - 123 / 200)]

/-- The inequality closing the cut check in the membership-matrix lemma (Lemma 3.1). -/
theorem matrix_cut_ineq (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 13 / 20) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 13 / 20) :
    3 / 5 * x + 3 / 5 * y - 2 / 5 - x * y + 3 / 100 * min x y < 0 := by
  rcases le_total y x with h | h
  · rw [min_eq_right h]
    have := cut_ineq_aux x y hy0 h hx1
    linarith
  · rw [min_eq_left h]
    have := cut_ineq_aux y x hx0 h hy1
    nlinarith [this]

/-- The Hall step of the weaving lemma (Lemma 3.2): a dense balanced bipartite relation has a
matching saturating `L`. -/
theorem dense_bipartite_hall {L R : Type*} [Fintype L] [Fintype R] [DecidableEq R]
    (r : L → R → Prop) [DecidableRel r] (k M : ℕ) (hL : Fintype.card L = k)
    (hR : Fintype.card R = k) (hk : 4 * M ≤ k)
    (hl : ∀ l : L, k - 2 * M ≤ (Finset.univ.filter (r l)).card)
    (hr : ∀ ρ : R, k - 2 * M ≤ (Finset.univ.filter (fun l => r l ρ)).card) :
    ∃ f : L → R, Function.Injective f ∧ ∀ l, r l (f l) := by
  classical
  let t : L → Finset R := fun l => Finset.univ.filter (r l)
  have hall : ∀ s : Finset L, s.card ≤ (s.biUnion t).card := by
    intro s
    by_cases hs : s.card ≤ k - 2 * M
    · -- Small `s`: one member already has enough neighbours.
      rcases s.eq_empty_or_nonempty with h0 | ⟨l, hl0⟩
      · simp [h0]
      · calc s.card ≤ k - 2 * M := hs
          _ ≤ (t l).card := hl l
          _ ≤ (s.biUnion t).card := Finset.card_le_card (Finset.subset_biUnion_of_mem t hl0)
    · -- Large `s`: every `ρ` has a neighbour in `s`, so the union is everything.
      push Not at hs
      have hfull : s.biUnion t = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro ρ
        by_contra hρ
        -- No member of `s` is related to `ρ`.
        have hsub : s ⊆ Finset.univ.filter (fun l => ¬ r l ρ) := by
          intro l hl'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro hlr
          exact hρ (Finset.mem_biUnion.mpr ⟨l, hl', by simp [t, hlr]⟩)
        have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset L))
          (fun l => r l ρ)
        rw [Finset.card_univ, hL] at hsplit
        have h1 := Finset.card_le_card hsub
        have h2 := hr ρ
        omega
      rw [hfull, Finset.card_univ, hR]
      calc s.card ≤ (Finset.univ : Finset L).card := Finset.card_le_univ s
        _ = k := by rw [Finset.card_univ, hL]
  obtain ⟨f, hf, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
  refine ⟨f, hf, fun l => ?_⟩
  have := hft l
  simpa [t] using this

end NearDirac
