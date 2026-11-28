import GallaiLean.TRN
import GallaiLean.NeighbourAvoid
/-! Audit A34: the core with the N-witness of G itself added as hypothesis (C0).
The proof of `conjN_of_core` goes through with a one-line change. -/
open SimpleGraph
namespace Gallai.AuditA34
open Gallai
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
def TightTransferNCoreW (V : Type u) [Fintype V] [DecidableEq V] : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj], (evenSet G).card ≤ 1 → ∀ g ∈ evenSet G,
    ∀ x y u : V, G.degree x % 2 = 1 → G.degree y % 2 = 1 → x ≠ y → ¬ G.Adj x y →
    G.Adj g u → G.Adj y u → u ≠ x →
    ConjNBelow V (∑ w, G.degree w) →
    (∃ w, G.Adj y w ∧ w ∉ evenSet G ∧ ¬ G.Adj x w) →
    (∀ v, G.Adj g v → v ≠ x → v ≠ y → G.Adj y v) →
    (∃ w, G.Adj y w ∧ w ≠ u ∧ ¬ G.Adj x w) →
    (∃ c, G.Adj y c ∧ G.Adj c x) →
    ¬ (∃ a b, a ≠ b ∧ ¬ G.Adj a b ∧ ∀ v, G.Adj g v ↔ v = a ∨ v = b) →
    AvoidDecomp (delEdge G g u) y {x} → AvoidDecomp G y {x}

theorem tightTransferNCoreW_of (hT : TightTransferNOn V) : TightTransferNCoreW V :=
  fun G _ hev g hg x y u hx hy hxy hnxy hgu hyu hux _ _ _ _ _ _ hchild =>
    hT G hev g hg x y u hx hy hxy hnxy hgu hyu hux hchild

/-- **The core of TRN suffices for Conjecture N** (manuscript Theorem 5.2). The induction of
`conjN_strong`, with the tight step routed through `TightTransferNCore`: if `x, y` are at
distance at least three, separation finishes (`avoid_of_farApart`); if `N(g)` is an independent
pair, split off and `L₁` (`avoid_of_degTwo_indep`); otherwise the core applies, with the
induction hypothesis as its first extra hypothesis. -/
theorem conjN_of_coreW (hT : TightTransferNCoreW V) (hR : ConjNDegTwoOn V) : ConjNOn V := by
  suffices h : ∀ n, ∀ (G : SimpleGraph V) [DecidableRel G.Adj], (∑ w, G.degree w) = n →
      (evenSet G).card ≤ 1 → ∀ x y : V, G.degree x % 2 = 1 → G.degree y % 2 = 1 → x ≠ y →
      ¬ G.Adj x y → (∃ w, G.Adj y w ∧ w ∉ evenSet G ∧ ¬ G.Adj x w) → AvoidDecomp G y {x} by
    intro G _ hev x y hx hy hxy hnxy hw
    exact h _ G rfl hev x y hx hy hxy hnxy hw
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ hn hev x y hx hy hxy hnxy hw
  classical
  have hbelow : ConjNBelow V n := by
    intro G' _ hlt hev' x' y' hx' hy' hxy' hnxy' hw'
    exact ih _ hlt G' rfl hev' x' y' hx' hy' hxy' hnxy' hw'
  obtain ⟨w0, hyw0, hw0e, hxw0⟩ := hw
  by_cases hz : ∃ g, g ∈ evenSet G
  swap
  · have h0 : (evenSet G).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun g hg => hz ⟨g, hg⟩)
    exact avoidDecomp_singleton_iff.mpr
      (lovasz_avoid_nonadj G h0 hy (Ne.symm hxy) (fun h => hnxy h.symm))
  obtain ⟨g, hg⟩ := hz
  have huniq : ∀ w ∈ evenSet G, w = g := fun w hw => Finset.card_le_one.mp hev w hw g hg
  have hgdeg := mem_evenSet_iff.mp hg
  have hxg : x ≠ g := by rintro rfl; omega
  have hyg : y ≠ g := by rintro rfl; omega
  have hw0g : w0 ≠ g := by rintro rfl; exact hw0e hg
  have hw0x : w0 ≠ x := by rintro rfl; exact hnxy hyw0.symm
  have hw0y : w0 ≠ y := hyw0.ne.symm
  -- the child of a target `u ∉ {x, y}` is an instance of N
  have child : ∀ u, G.Adj g u → u ≠ x → u ≠ y → ∀ w, G.Adj y w → w ≠ u → ¬ G.Adj x w →
      AvoidDecomp (delEdge G g u) y {x} := by
    intro u hgu hux huy w hyw hwu hxw
    have hsum := delEdge_sum_degree G hgu
    have hdx := delEdge_degree G hgu x
    have hdy := delEdge_degree G hgu y
    simp only [hxg, Ne.symm hux, hyg, Ne.symm huy, ite_false, add_zero] at hdx hdy
    refine ih _ (by omega) (delEdge G g u) rfl (evenSet_delEdge_card hev hg hgu) x y
      (by rw [hdx]; exact hx) (by rw [hdy]; exact hy) hxy (fun h => hnxy h.1) ⟨w, ?_, ?_, ?_⟩
    · exact delEdge_adj_of_ne hyw hyg (Ne.symm huy)
    · exact fun h => hwu (evenSet_delEdge_sub hev hg hgu w h)
    · exact fun h => hxw h.1
  -- (1) a non-tight target
  by_cases h1 : ∃ u, G.Adj g u ∧ u ≠ x ∧ u ≠ y ∧ ¬ G.Adj y u
  · obtain ⟨u, hgu, hux, huy, hyu⟩ := h1
    have hc := child u hgu hux huy w0 hyw0 (by rintro rfl; exact hyu hyw0) hxw0
    exact avoidDecomp_singleton_iff.mpr (avoid_free_target hev hg hgu hux huy hyu hyg
      (avoidDecomp_singleton_iff.mp hc))
  simp only [not_exists, not_and, not_not] at h1
  -- (2) a tight target whose child keeps a witness: the core of TRN
  by_cases h2 : ∃ u, G.Adj g u ∧ u ≠ x ∧ u ≠ y ∧ ∃ w, G.Adj y w ∧ w ≠ u ∧ ¬ G.Adj x w
  · obtain ⟨u, hgu, hux, huy, w, hyw, hwu, hxw⟩ := h2
    have hyu : G.Adj y u := h1 u hgu hux huy
    by_cases hfar : FarApart G y x
    · exact avoid_of_farApart hev hfar
    have hcn : ∃ c, G.Adj y c ∧ G.Adj c x := by
      by_contra hno
      push Not at hno
      exact hfar ⟨Ne.symm hxy, fun h => hnxy h.symm, fun c hc => hno c hc.1 hc.2⟩
    by_cases hind : ∃ a b, a ≠ b ∧ ¬ G.Adj a b ∧ ∀ v, G.Adj g v ↔ v = a ∨ v = b
    · obtain ⟨a, b, hab, hnab, hNg⟩ := hind
      refine avoid_of_degTwo_indep hev hg hNg hab hnab hx hy hxy hnxy ?_
      -- `u ∈ {a, b}` and `u ∉ {x, y}`, so `{x, y} ≠ {a, b}`
      have hu := (hNg u).mp hgu
      intro hp
      rcases hp with ⟨hya, hxb⟩ | ⟨hyb, hxa⟩
      · rcases hu with hua | hub
        · exact huy (hua.trans hya.symm)
        · exact hux (hub.trans hxb.symm)
      · rcases hu with hua | hub
        · exact hux (hua.trans hxa.symm)
        · exact huy (hub.trans hyb.symm)
    exact hT G hev g hg x y u hx hy hxy hnxy hgu hyu hux (by rw [hn]; exact hbelow) ⟨w0, hyw0, hw0e, hxw0⟩ h1 ⟨w, hyw, hwu, hxw⟩
      hcn hind (child u hgu hux huy w hyw hwu hxw)
  simp only [not_exists, not_and, not_not] at h2
  -- (3) every target outside `{x, y}` is the witness `w0`
  have hT0 : ∀ u, G.Adj g u → u ≠ x → u ≠ y → u = w0 := by
    intro u hgu hux huy
    by_contra h
    exact hxw0 (h2 u hgu hux huy w0 hyw0 (fun e => h e.symm))
  have hsub : G.neighborFinset g ⊆ {x, y, w0} := by
    intro v hv
    rw [mem_neighborFinset] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hvx : v = x
    · exact Or.inl hvx
    · by_cases hvy : v = y
      · exact Or.inr (Or.inl hvy)
      · exact Or.inr (Or.inr (hT0 v hv hvx hvy))
  have hdg : (G.neighborFinset g).card = G.degree g := card_neighborFinset_eq_degree G g
  by_cases hgw0 : G.Adj g w0
  · have hyx : G.Adj g y → G.Adj g x := by
      intro hgy
      by_contra hgx
      exact hgx (h2 w0 hgw0 hw0x hw0y g hgy.symm (Ne.symm hw0g)).symm
    by_cases hgx : G.Adj g x
    · have hgy : ¬ G.Adj g y := by
        intro hgy
        have : G.neighborFinset g = {x, y, w0} := by
          refine Finset.Subset.antisymm hsub fun v hv => ?_
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rw [mem_neighborFinset]
          rcases hv with rfl | rfl | rfl
          · exact hgx
          · exact hgy
          · exact hgw0
        have h3 : ({x, y, w0} : Finset V).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_pair hw0y.symm]
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hxy, hw0x.symm⟩
        rw [this, h3] at hdg
        omega
      have hNg : ∀ v, G.Adj g v ↔ v = x ∨ v = w0 := by
        intro v
        constructor
        · intro hv
          have := hsub (by rw [mem_neighborFinset]; exact hv)
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with h | h | h
          · exact Or.inl h
          · exact absurd (h ▸ hv) hgy
          · exact Or.inr h
        · rintro (rfl | rfl)
          · exact hgx
          · exact hgw0
      exact avoid_of_degTwo_indep hev hg hNg hw0x.symm hxw0 hx hy hxy hnxy
        (by
          rintro (⟨h, -⟩ | ⟨h, -⟩)
          · exact hxy h.symm
          · exact hw0y h.symm)
    · have hgy : ¬ G.Adj g y := fun h => hgx (hyx h)
      have : G.neighborFinset g ⊆ {w0} := by
        intro v hv
        have h := hsub hv
        rw [mem_neighborFinset] at hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
        rcases h with rfl | rfl | h
        · exact absurd hv hgx
        · exact absurd hv hgy
        · exact h
      have := Finset.card_le_card this
      rw [Finset.card_singleton, hdg] at this
      omega
  · have hsub' : G.neighborFinset g ⊆ {x, y} := by
      intro v hv
      have h := hsub hv
      rw [mem_neighborFinset] at hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
      rcases h with h | h | rfl
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd hv hgw0
    have heq : G.neighborFinset g = {x, y} := by
      refine Finset.eq_of_subset_of_card_le hsub' ?_
      have h2 := Finset.card_le_card hsub'
      rw [Finset.card_pair hxy] at h2 ⊢
      rw [hdg] at h2 ⊢
      omega
    have hNg : ∀ v, G.Adj g v ↔ v = x ∨ v = y := by
      intro v
      rw [← mem_neighborFinset, heq]
      simp
    exact hR G hev g hg x y hNg hx hy hxy hnxy ⟨w0, hyw0, hw0g, hxw0⟩


theorem conjN_of_coreW_alone (hT : TightTransferNCoreW V) : ConjNOn V :=
  conjN_of_coreW hT (conjNDegTwo_of_neighbourAvoid neighbourAvoidOn)
end Gallai.AuditA34
#print axioms Gallai.AuditA34.conjN_of_coreW
#print axioms Gallai.AuditA34.conjN_of_coreW_alone
#print axioms Gallai.AuditA34.tightTransferNCoreW_of
