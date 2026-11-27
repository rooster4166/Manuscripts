import GallaiLean.SeparatorEvenOdd
import GallaiLean.SeparatorEvenEven
import GallaiLean.Lovasz
import GallaiLean.Thm59

/-!
# The separator theorem and Theorem 114 (marked-reduction)

* **`separator_theorem`** (marked-reduction Theorem 113, in the A2 audit's F7 form): Lovász's
  theorem implies `SeparatorStatement`. The case split: `|C|` odd (exactly one port odd in `A`,
  `rootedAt_oddComp`, after swapping the ports if needed), `|C|` even with both ports odd
  (`rootedAt_evenComp_oddPorts`) or both even (`rootedAt_evenComp_evenPorts`).
* `separatorStatement`: Theorem 113 with no hypothesis, using Lovász's theorem as proved in
  `GallaiLean/Lovasz.lean` (`lovaszStatement`).
* **`gallai_iff_spineTests`** (Theorem 114): under Theorem 59 (explicit hypothesis
  `Thm59Statement`), Gallai's conjecture is equivalent to the two deletion tests on
  three-connected graphs, with or without the restriction that `J − z` has no matching cut.
* **`gallai_iff_spineTests'`**: the same equivalences with no hypothesis, using Theorem 59 as
  proved in `GallaiLean/Thm59.lean` (`thm59`).
-/

open SimpleGraph

namespace Gallai

universe u

/-- **Theorem 113 (separator theorem).** -/
theorem separator_theorem (hL : LovaszStatement.{u}) : SeparatorStatement.{u} := by
  intro V _ _ B _ hMB hB x y C hC r hr hodd
  have hpar := sideA_parity hC hodd
  rcases Nat.even_or_odd C.card with hCe | hCo
  · rcases Nat.even_or_odd ((sideA B C x y).degree x) with hxe | hxo
    · have hye : Even ((sideA B C x y).degree y) := by
        by_contra hyo
        rw [Nat.not_even_iff_odd] at hyo
        simp only [Nat.not_odd_iff_even.mpr hxe, hyo, ite_true, ite_false, add_zero] at hpar
        obtain ⟨a, ha⟩ := hCe; obtain ⟨b, hb⟩ := hpar; omega
      exact rootedAt_evenComp_evenPorts hL hMB hB hC hodd hr hCe hxe hye
    · have hyo : Odd ((sideA B C x y).degree y) := by
        by_contra hye
        rw [Nat.not_odd_iff_even] at hye
        simp only [hxo, Nat.not_odd_iff_even.mpr hye, ite_true, ite_false, add_zero] at hpar
        obtain ⟨a, ha⟩ := hCe; obtain ⟨b, hb⟩ := hpar; omega
      exact rootedAt_evenComp_oddPorts hL hMB hB hC hodd hr hCe hxo hyo
  · rcases Nat.even_or_odd ((sideA B C x y).degree x) with hxe | hxo
    · have hyo : Odd ((sideA B C x y).degree y) := by
        by_contra hye
        rw [Nat.not_odd_iff_even] at hye
        simp only [Nat.not_odd_iff_even.mpr hxe, Nat.not_odd_iff_even.mpr hye, ite_false,
          add_zero] at hpar
        exact (Nat.not_even_iff_odd.mpr hCo) hpar
      have hyo' : Odd ((sideA B C y x).degree y) := by rw [degree_sideA_swap]; exact hyo
      have hxe' : Even ((sideA B C y x).degree x) := by rw [degree_sideA_swap]; exact hxe
      exact rootedAt_oddComp hL hMB hB hC.swap hodd hr hCo hyo' hxe'
    · have hye : Even ((sideA B C x y).degree y) := by
        by_contra hyo
        rw [Nat.not_even_iff_odd] at hyo
        simp only [hxo, hyo, ite_true] at hpar
        obtain ⟨a, ha⟩ := hCo; obtain ⟨b, hb⟩ := hpar; omega
      exact rootedAt_oddComp hL hMB hB hC hodd hr hCo hxo hye

/-- **Theorem 113**, unconditionally (Lovász's theorem is proved in `GallaiLean/Lovasz.lean`). -/
theorem separatorStatement : SeparatorStatement.{u} := separator_theorem lovaszStatement

/-- **Theorem 114** (marked-reduction), modulo Theorem 59 (explicit hypothesis `Thm59Statement`;
Theorem 113 and Lovász's theorem are proved). Gallai's conjecture is equivalent to the two
deletion tests on three-connected graphs, and also to the tests restricted to `J − z` without a
matching cut. The forward direction (`spineTests_of_gallai`) uses no hypothesis. -/
theorem gallai_iff_spineTests (h59 : Thm59Statement.{u}) :
    (GallaiConjecture.{u} ↔ SpineTests.{u}) ∧ (GallaiConjecture.{u} ↔ SpineTestsNMC.{u}) := by
  have hback := gallai_of_spineTestsNMC lovaszStatement h59 separatorStatement
  exact ⟨⟨spineTests_of_gallai, fun h => hback h.nmc⟩,
    ⟨fun h => (spineTests_of_gallai h).nmc, hback⟩⟩

/-- **Theorem 114** (marked-reduction), unconditionally: Gallai's conjecture is equivalent to the
two deletion tests on three-connected graphs, and also to the tests restricted to `J − z` without a
matching cut. Theorem 59 (`thm59`), Theorem 113 (`separatorStatement`) and Lovász's theorem
(`lovaszStatement`) are all proved in this library. -/
theorem gallai_iff_spineTests' :
    (GallaiConjecture.{u} ↔ SpineTests.{u}) ∧ (GallaiConjecture.{u} ↔ SpineTestsNMC.{u}) :=
  gallai_iff_spineTests thm59

end Gallai
