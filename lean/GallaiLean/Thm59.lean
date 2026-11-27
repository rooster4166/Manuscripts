import GallaiLean.Thm59Transfer
import GallaiLean.Thm59MatchingCut

/-!
# Theorem 59 of the marked-reduction manuscript

**`thm59 : Thm59Statement`.** Fix `m`, and suppose both rooted assertions (`RootedAt`) hold on
every member of `C` (two-connected, no matching cut) with at most `m + 1` vertices. Then the
marked bound holds on every connected graph whose two-connected blocks have order at most `m`
(`MarkedBoundUpTo m`). This is the finite-order form recommended by audit A2, finding F1.

Proof. By strong induction on `j ≤ m`, show `MarkedBoundUpTo j`. By the finite-order block
transfer (`markedBoundUpTo_of_tests`) it suffices to give the two assertions of Theorem 1 on every
two-connected `B` of order `n ≤ j`.

* If `B ∈ C`, use step [C] (`markedBound_of_classC`, `threeEnds_of_classC`). It applies the
  rooted tests on `B` and on cones over `B`, all of order `≤ n + 1 ≤ m + 1`.
* If `B` has a matching cut, use step [M] (`matchingCut_markedBound`) with
  `MarkedBoundUpTo (n − 1)` from the induction. This gives every marked bound, and with no mark
  `p(B) ≤ ⌊n/2⌋`, so `B` cannot meet the premise of the three-end test.
-/

namespace Gallai

universe u

/-- **Theorem 59** (marked-reduction, p. 84), finite-order form. -/
theorem thm59 : Thm59Statement.{u} := by
  intro m hRT
  have hRT' : RootedTestsUpTo.{u} (m + 1) := hRT
  have key : ∀ j, j ≤ m → MarkedBoundUpTo.{u} j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
    intro hj
    apply markedBoundUpTo_of_tests
    · intro V _ _ G hG hcard S hS
      classical
      have hK := hG.kConnected
      have h3 := hK.1
      by_cases hmc : HasMatchingCut G
      · exact matchingCut_markedBound (hK.connected (by norm_num)) hmc
          (ih (Fintype.card V - 1) (by omega) (by omega)) S
      · exact markedBound_of_classC hRT' ⟨hK, hmc⟩ (by omega) S hS
    · intro V _ _ J _ hJ hcard k hk hp x hx
      have hK := hJ.kConnected
      have h3 := hK.1
      by_cases hmc : HasMatchingCut J
      · exfalso
        have h1 := matchingCut_markedBound (hK.connected (by norm_num)) hmc
          (ih (Fintype.card V - 1) (by omega) (by omega)) ∅
        have h2 := pathNumber_le_markedNumber_add J ∅
        simp only [Finset.card_empty, Nat.sub_zero, add_zero] at h1 h2
        omega
      · exact threeEnds_of_classC hRT' ⟨hK, hmc⟩ (by omega) k hk hp x hx
  exact key m le_rfl

end Gallai
