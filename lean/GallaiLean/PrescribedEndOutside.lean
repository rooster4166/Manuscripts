import GallaiLean.PrescribedEnd

/-!
# EE from an outside neighbour

Manuscript `manuscripts/prescribed-end/prescribed-end.tex`, Proposition "an outside neighbour".

* **`ee_of_outside`**: let `z` be the only vertex of positive even degree, `u ∈ N(z)`, and
  `w ∈ N(u)` not adjacent to `z`. If `G − uz − uw` has a Lovász decomposition whose path ending
  at `z` avoids `u`, then `uz` is terminal at `u` in some Lovász decomposition of `G`.

Proof: lift to the leaf graph `apex (G − uz) {z}` (the leaf stands for `u`) by extending the path
ending at `z`; restore `uw` by Fan's lemma with target `w` (since `w ≁ z`, the vertex `z`, which
now has no end, is not a neighbour of the target); merge (`endEdge_of_leafSep`).

* **`L1Star`**, **`ee_of_L1Star`**: the avoidance conjecture `L₁*` (sets of at most two vertices)
  implies Conjecture EE, through `ee_noTriangle` and `ee_of_triangle`.
-/

open SimpleGraph

namespace Gallai

universe u

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- **EE from an outside neighbour** (manuscript Proposition "an outside neighbour"). -/
theorem ee_of_outside (G : SimpleGraph W) [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1)
    {z u w : W} (hz : z ∈ evenSet G) (hzu : G.Adj z u) (huw : G.Adj u w) (hwz : ¬ G.Adj w z)
    (hwz' : w ≠ z)
    (D₀ : PathDecomp (delEdge (delEdge G u z) u w))
    (hD₀ : ∀ v, D₀.ends v = (delEdge (delEdge G u z) u w).degree v % 2)
    (hav : ∀ P ∈ D₀.paths, (P.src = z ∨ P.tgt = z) → u ∉ P.walk.support) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∃ P ∈ D.paths, (P.src = u ∨ P.tgt = u) ∧ s(u, z) ∈ P.edges := by
  classical
  have hzu' : z ≠ u := hzu.ne
  have hwu : w ≠ u := huw.ne.symm
  have huniq : ∀ v ∈ evenSet G, v = z := fun v hv => Finset.card_le_one.mp hev v hv z hz
  have hodd : ∀ v, v ≠ z → 0 < G.degree v → G.degree v % 2 = 1 := by
    intro v hvz hpos
    have : v ∉ evenSet G := fun h => hvz (huniq v h)
    rw [mem_evenSet_iff] at this
    omega
  have hzd := mem_evenSet_iff.mp hz
  have hFuw : (delEdge G u z).Adj u w := ⟨huw, fun h => by
    rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h, -⟩
    · exact hwz' h
    · exact hzu' h.symm⟩
  have hd₁ := delEdge_degree G hzu.symm
  have hd₂ := delEdge_degree (delEdge G u z) hFuw
  have hdeg : ∀ v, (delEdge (delEdge G u z) u w).degree v + 2 * (if v = u then 1 else 0) +
      (if v = w then 1 else 0) + (if v = z then 1 else 0) = G.degree v := by
    intro v; have := hd₁ v; have := hd₂ v; omega
  have hupos : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).mpr ⟨z, hzu.symm⟩
  have huodd := hodd u hzu'.symm hupos
  -- the path ending at `z`
  have hD₀z : D₀.ends z = 1 := by
    rw [hD₀]
    have := hdeg z
    simp only [hzu', hwz'.symm, ite_true, ite_false] at this
    omega
  obtain ⟨P, hP, hPend⟩ := D₀.exists_end_of_pos (by rw [hD₀z]; omega)
  have huP := hav P hP hPend
  obtain ⟨D₃, hD₃some, hD₃none, hD₃cov⟩ := D₀.liftLeaf hP hPend
  have hsep₃ : Separates D₃ (some u) none := by
    intro Q' hQ' ⟨hx, hn⟩
    rcases hD₃cov Q' hQ' with h | ⟨Q, hQ, hs⟩
    · rcases h (some u) hx with h | ⟨y', hy', h⟩
      · exact Option.some_ne_none _ h
      · rw [Option.some.injEq] at h
        subst h
        exact huP hy'
    · rw [hs, List.mem_map] at hn
      obtain ⟨_, _, h⟩ := hn
      exact Option.some_ne_none _ h
  -- Fan's lemma in the leaf graph `apex (G − uz) {z}`: restore `uw`, end from `u` to `w`
  have hHwu : (apex (delEdge G z u) {z}).Adj (some w) (some u) := by
    rw [apex_adj_some_some]
    refine ⟨huw.symm, fun h => ?_⟩
    rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨h, -⟩
    · exact hwz' h
    · exact hwu h
  have hedges : ∀ e, e ∈ (apex (delEdge (delEdge G u z) u w) {z}).edgeSet ↔
      e ∈ (apex (delEdge G z u) {z}).edgeSet ∧ e ≠ s(some w, some u) := by
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      rw [mem_edgeSet, mem_edgeSet]
      cases a with
      | none =>
        cases b with
        | none => simp
        | some b => simp
      | some a =>
        cases b with
        | none => simp
        | some b =>
          simp only [apex_adj_some_some, delEdge, ne_eq, Sym2.eq_iff, Option.some.injEq]
          constructor
          · rintro ⟨⟨hab, h1⟩, h2⟩
            refine ⟨⟨hab, fun h => h1 ?_⟩, fun h => h2 ?_⟩
            · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · right; exact ⟨rfl, rfl⟩
              · left; exact ⟨rfl, rfl⟩
            · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · right; exact ⟨rfl, rfl⟩
              · left; exact ⟨rfl, rfl⟩
          · rintro ⟨⟨hab, h1⟩, h2⟩
            refine ⟨⟨hab, fun h => h1 ?_⟩, fun h => h2 ?_⟩
            · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · right; exact ⟨rfl, rfl⟩
              · left; exact ⟨rfl, rfl⟩
            · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · right; exact ⟨rfl, rfl⟩
              · left; exact ⟨rfl, rfl⟩
  have hD₃u : D₃.ends (some u) = 1 := by
    have := hD₃some u
    simp only [hzu'.symm, ite_false, add_zero] at this
    rw [this, hD₀]
    have := hdeg u
    simp only [hwu.symm, hzu'.symm, ite_true, ite_false] at this
    omega
  have hcount : (Finset.univ.filter (fun v => (apex (delEdge (delEdge G u z) u w) {z}).Adj
      (some w) v ∧ D₃.ends v = 0)).card < D₃.ends (some u) := by
    have hempty : Finset.univ.filter (fun v => (apex (delEdge (delEdge G u z) u w) {z}).Adj
        (some w) v ∧ D₃.ends v = 0) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
      rw [Finset.mem_filter] at hv
      obtain ⟨-, hadj, h0⟩ := hv
      cases v with
      | none =>
        rw [apex_adj_some_none, Finset.mem_singleton] at hadj
        exact hwz' hadj
      | some v =>
        rw [apex_adj_some_some] at hadj
        have hvw : v ≠ w := hadj.ne.symm
        have hvu : v ≠ u := fun h => hadj.2 (by rw [h, Sym2.eq_swap])
        have hvz : v ≠ z := fun h => hwz (h ▸ hadj.1.1)
        have := hD₃some v
        simp only [hvz, ite_false, add_zero] at this
        rw [this, hD₀] at h0
        have hdv := hdeg v
        simp only [hvu, hvw, hvz, ite_false, add_zero, mul_zero] at hdv
        have hpos : 0 < G.degree v := (G.degree_pos_iff_exists_adj v).mpr ⟨w, hadj.1.1.symm⟩
        have := hodd v hvz hpos
        omega
    rw [hempty, Finset.card_empty, hD₃u]
    omega
  obtain ⟨DH, -, hDHw, hDHu, hDHrest, hcovH⟩ :=
    fan_single_supp (G := apex (delEdge G z u) {z}) hHwu hedges D₃ hcount
  have hsepH : Separates DH (some u) none :=
    separates_of_cover (g := some w) (by simp [hwu]) (by simp) hsep₃ hcovH
  have hHdeg : ∀ v, (apex (delEdge G z u) {z}).degree (some v) + (if v = u then 1 else 0) =
      G.degree v := by
    intro v
    rw [apex_degree_some]
    have := delEdge_degree G hzu v
    by_cases hvz : v = z
    · subst hvz; simp only [Finset.mem_singleton, hzu', ite_true, ite_false] at this ⊢; omega
    · simp only [Finset.mem_singleton, hvz, ite_false, add_zero] at this ⊢; omega
  have hDH : ∀ v, DH.ends v = (apex (delEdge G z u) {z}).degree v % 2 := by
    intro v
    cases v with
    | none =>
      rw [hDHrest none (by simp) (by simp), hD₃none, apex_degree_none]
      simp
    | some v =>
      have hH := hHdeg v
      have hS := hD₃some v
      have hdv := hdeg v
      rw [hD₀] at hS
      by_cases hvw : v = w
      · subst hvw
        simp only [hwu, hwz', ite_true, ite_false] at hH hS hdv
        rw [hDHw]
        have := hodd v hwz' ((G.degree_pos_iff_exists_adj v).mpr ⟨u, huw.symm⟩)
        omega
      · by_cases hvu : v = u
        · subst hvu
          simp only [hzu'.symm, ite_true, ite_false] at hH hS hdv
          have := hDHu
          omega
        · rw [hDHrest (some v) (by simp [hvw]) (by simp [hvu])]
          by_cases hvz : v = z
          · subst hvz
            simp only [hzu', hwz'.symm, ite_true, ite_false] at hH hS hdv
            omega
          · simp only [hvu, hvw, hvz, ite_false, add_zero, mul_zero] at hH hS hdv
            omega
  exact endEdge_of_leafSep G hzu.symm huodd DH hDH hsepH

/-- **Conjecture `L₁*`** (manuscript Conjecture "L₁*"), as a proposition. In a graph with at most
one vertex of positive even degree, for an odd vertex `c` and a set `A` of at most two vertices,
none of them `c`, a neighbour of `c`, or a neighbour of an even vertex, some Lovász decomposition
has its paths ending at `c` disjoint from `A`. -/
def L1Star : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (evenSet G).card ≤ 1 → ∀ c : V, G.degree c % 2 = 1 → ∀ A : Finset V, A.card ≤ 2 →
    (∀ a ∈ A, a ≠ c ∧ ¬ G.Adj c a ∧ ∀ g ∈ evenSet G, ¬ G.Adj g a) →
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∀ P ∈ D.paths, (P.src = c ∨ P.tgt = c) → ∀ a ∈ A, a ∉ P.walk.support

/-- **`L₁*` implies EE** (manuscript Corollary "L₁* ⇒ EE"). If `u` and `z` have no common
neighbour, use `ee_noTriangle`; otherwise apply `L₁*` to `G − {uz, uw, wz}` for a common neighbour
`w`, with `c = w` and `A = {u, z}`, and use `ee_of_triangle`. -/
theorem ee_of_L1Star (hL : L1Star.{u}) (G : SimpleGraph W) [DecidableRel G.Adj]
    (hev : (evenSet G).card ≤ 1) {z u : W} (hz : z ∈ evenSet G) (hzu : G.Adj z u) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∃ P ∈ D.paths, (P.src = u ∨ P.tgt = u) ∧ s(u, z) ∈ P.edges := by
  classical
  by_cases hT : ∃ w, G.Adj u w ∧ G.Adj w z
  swap
  · exact ee_noTriangle G hev hz hzu (fun w hw => hT ⟨w, hw⟩)
  obtain ⟨w, huw, hwz⟩ := hT
  have hzu' : z ≠ u := hzu.ne
  have hwu : w ≠ u := huw.ne.symm
  have hwz' : w ≠ z := hwz.ne
  have huniq : ∀ v ∈ evenSet G, v = z := fun v hv => Finset.card_le_one.mp hev v hv z hz
  have hFuw : (delEdge G u z).Adj u w := ⟨huw, fun h => by
    rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h, -⟩
    · exact hwz' h
    · exact hzu' h.symm⟩
  have hK₀wz : (delEdge (delEdge G u z) u w).Adj w z := ⟨⟨hwz, fun h => by
    rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨h, -⟩
    · exact hwu h
    · exact hwz' h⟩, fun h => by
    rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨-, h⟩
    · exact hwu h
    · exact hzu' h⟩
  have hd₁ := delEdge_degree G hzu.symm
  have hd₂ := delEdge_degree (delEdge G u z) hFuw
  have hd₃ := delEdge_degree (delEdge (delEdge G u z) u w) hK₀wz
  have hdeg : ∀ v, (delEdge (delEdge (delEdge G u z) u w) w z).degree v +
      2 * ((if v = u then 1 else 0) + (if v = w then 1 else 0) + (if v = z then 1 else 0)) =
      G.degree v := by
    intro v; have := hd₁ v; have := hd₂ v; have := hd₃ v; omega
  have hevsub : evenSet (delEdge (delEdge (delEdge G u z) u w) w z) ⊆ {z} := by
    intro v hv
    rw [mem_evenSet_iff] at hv
    rw [Finset.mem_singleton]
    have h := hdeg v
    exact huniq v (mem_evenSet_iff.mpr ⟨by omega, by omega⟩)
  have hev₁ : (evenSet (delEdge (delEdge (delEdge G u z) u w) w z)).card ≤ 1 :=
    (Finset.card_le_card hevsub).trans (by simp)
  have hwodd : (delEdge (delEdge (delEdge G u z) u w) w z).degree w % 2 = 1 := by
    have h := hdeg w
    have hpos : 0 < G.degree w := (G.degree_pos_iff_exists_adj w).mpr ⟨u, huw.symm⟩
    have : w ∉ evenSet G := fun h' => hwz' (huniq w h')
    rw [mem_evenSet_iff] at this
    simp only [hwu, hwz', ite_true, ite_false] at h
    omega
  have hA : ∀ a ∈ ({u, z} : Finset W), a ≠ w ∧
      ¬ (delEdge (delEdge (delEdge G u z) u w) w z).Adj w a ∧
      ∀ g ∈ evenSet (delEdge (delEdge (delEdge G u z) u w) w z),
        ¬ (delEdge (delEdge (delEdge G u z) u w) w z).Adj g a := by
    intro a ha
    rw [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · refine ⟨hwu.symm, fun h => h.1.2 Sym2.eq_swap, fun g hg h => ?_⟩
      rw [Finset.mem_singleton.mp (hevsub hg)] at h
      exact h.1.1.2 Sym2.eq_swap
    · refine ⟨hwz'.symm, fun h => h.2 rfl, fun g hg h => ?_⟩
      rw [Finset.mem_singleton.mp (hevsub hg)] at h
      exact h.1.1.1.ne rfl
  obtain ⟨D₁, hD₁, hav⟩ := hL W _ hev₁ w hwodd {u, z} (Finset.card_le_two) hA
  exact ee_of_triangle G hev hz hzu huw hwz D₁ hD₁ fun P hP hend =>
    ⟨hav P hP hend u (by simp), hav P hP hend z (by simp)⟩

end Gallai
