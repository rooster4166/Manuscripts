import GallaiLean.MissingMove

/-!
# The inductive template for EMM: cut feasibility and the leaf reduction

Manuscript: `manuscripts/missing-move`, Section 7 (track C4 of `research/synthesis.md`).

For a graph `G`, a profile `b : V → ℕ` and a number of paths `p`, the cut conditions of
even-degrees §12.4 (inequality (1)), extended from half-sets to general profiles, are
* (L) `b v ≤ d v` and `d v + b v ≤ 2p` for every `v`;
* (C) `b(W) + d v + b v ≤ |δ(W)| + 2p` for every `v` and every `W ⊆ V − v`.
`CutOK G b p` packages them, with `|δ(W)|` counted as `cutCount G W = ∑_{u ∈ W} #{y ∉ W : uy ∈ E}`.

The conjecture EMM⁺ (manuscript, Conjecture 7.3) says that for connected `G` and `p ≥ ⌈n/2⌉`
these conditions are also sufficient. In a counterexample with the fewest edges, a leaf `w` whose
neighbour `x` has `b x + 2 ≤ d x` cannot exist:
* **`cutOK_leaf`**: deleting the leaf edge and moving the end of `w` to `x` keeps (L) and (C);
* **`ach_of_leaf`**: a partition of `G − xw` with that profile gives one of `G`, by appending `xw`
  to a path ending at `x` (`Ach.transfer`; `w` is isolated, so it has no blank neighbour);
* **`leaf_step`**: the two together, in the form used by the minimal-counterexample argument.
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

section cut

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The number of edges of `G` leaving `W`, counted at their ends in `W`. -/
def cutCount (W : Finset V) : ℕ :=
  ∑ u ∈ W, (Finset.univ.filter (fun y => G.Adj u y ∧ y ∉ W)).card

/-- The cut conditions (L) and (C) for the profile `b` in `p` paths. -/
def CutOK (b : V → ℕ) (p : ℕ) : Prop :=
  (∀ v, b v ≤ G.degree v ∧ G.degree v + b v ≤ 2 * p) ∧
    ∀ v (W : Finset V), v ∉ W → ∑ u ∈ W, b u + G.degree v + b v ≤ cutCount G W + 2 * p

end cut

section leaf

variable {G : SimpleGraph V} [DecidableRel G.Adj] {x w : V}

omit [DecidableEq V] in
/-- The only neighbour of a leaf. -/
theorem adj_leaf_iff (hxw : G.Adj x w) (hw : G.degree w = 1) (y : V) : G.Adj w y ↔ y = x := by
  constructor
  · intro hy
    rw [← card_neighborFinset_eq_degree, Finset.card_eq_one] at hw
    obtain ⟨a, ha⟩ := hw
    have h1 : y ∈ G.neighborFinset w := (mem_neighborFinset G w y).mpr hy
    have h2 : x ∈ G.neighborFinset w := (mem_neighborFinset G w x).mpr hxw.symm
    rw [ha, Finset.mem_singleton] at h1 h2
    rw [h1, h2]
  · rintro rfl
    exact hxw.symm

/-- Deleting the edge `xw` lowers the cut of `W` by one exactly when it separates `x` from `w`. -/
theorem cutCount_delEdge (hxw : G.Adj x w) (W : Finset V) :
    cutCount (delEdge G x w) W + ((if x ∈ W ∧ w ∉ W then 1 else 0) +
      (if w ∈ W ∧ x ∉ W then 1 else 0)) = cutCount G W := by
  have hne : x ≠ w := hxw.ne
  unfold cutCount
  have hterm : ∀ u ∈ W, (Finset.univ.filter (fun y => G.Adj u y ∧ y ∉ W)).card =
      (Finset.univ.filter (fun y => (delEdge G x w).Adj u y ∧ y ∉ W)).card +
        ((if u = x ∧ w ∉ W then 1 else 0) + (if u = w ∧ x ∉ W then 1 else 0)) := by
    intro u _
    rw [Finset.card_filter, Finset.card_filter]
    have key : ∀ y, (if G.Adj u y ∧ y ∉ W then 1 else 0) =
        (if (delEdge G x w).Adj u y ∧ y ∉ W then 1 else 0) +
          (if (u = x ∧ y = w ∧ w ∉ W) ∨ (u = w ∧ y = x ∧ x ∉ W) then 1 else 0) := by
      intro y
      have hd : (delEdge G x w).Adj u y ↔ G.Adj u y ∧ ¬ ((u = x ∧ y = w) ∨ (u = w ∧ y = x)) := by
        show G.Adj u y ∧ ¬ s(u, y) = s(x, w) ↔ _
        rw [Sym2.eq_iff]
      by_cases h1 : (u = x ∧ y = w) ∨ (u = w ∧ y = x)
      · have hadj : G.Adj u y := by
          rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hxw
          · exact hxw.symm
        have h3 : ¬ (delEdge G x w).Adj u y := fun h => (hd.mp h).2 h1
        rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp [hadj, h3, hne]
        · simp [hadj, h3, hne, Ne.symm hne]
      · have h4 : ¬ ((u = x ∧ y = w ∧ w ∉ W) ∨ (u = w ∧ y = x ∧ x ∉ W)) := by
          rintro (⟨a, b, -⟩ | ⟨a, b, -⟩)
          · exact h1 (Or.inl ⟨a, b⟩)
          · exact h1 (Or.inr ⟨a, b⟩)
        by_cases hadj : G.Adj u y
        · have h3 : (delEdge G x w).Adj u y := hd.mpr ⟨hadj, h1⟩
          simp only [hadj, h3, true_and, h4, ite_false, add_zero]
        · have h3 : ¬ (delEdge G x w).Adj u y := fun h => hadj (hd.mp h).1
          simp only [hadj, h3, false_and, h4, ite_false, add_zero]
    rw [Finset.sum_congr rfl (fun y _ => key y), Finset.sum_add_distrib]
    congr 1
    by_cases hux : u = x
    · subst hux
      by_cases hwW : w ∈ W
      · simp [hne, hwW]
      · simp [hne, hwW]
    · by_cases huw : u = w
      · subst huw
        by_cases hxW : x ∈ W
        · simp [hux, hxW]
        · simp [hux, hxW]
      · simp [hux, huw]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_ite, Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
  have e1 : (W.filter (fun u => u = x ∧ w ∉ W)).card = if x ∈ W ∧ w ∉ W then 1 else 0 := by
    by_cases h : x ∈ W ∧ w ∉ W
    · rw [ite_eq_left_iff.mpr (fun h' => absurd h h'), Finset.card_eq_one]
      exact ⟨x, by ext u; simp only [Finset.mem_filter, Finset.mem_singleton]; constructor <;>
        [exact fun h' => h'.2.1; exact fun h' => ⟨h' ▸ h.1, h', h.2⟩]⟩
    · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro u hu ⟨rfl, h2⟩
      exact h ⟨hu, h2⟩
  have e2 : (W.filter (fun u => u = w ∧ x ∉ W)).card = if w ∈ W ∧ x ∉ W then 1 else 0 := by
    by_cases h : w ∈ W ∧ x ∉ W
    · rw [ite_eq_left_iff.mpr (fun h' => absurd h h'), Finset.card_eq_one]
      exact ⟨w, by ext u; simp only [Finset.mem_filter, Finset.mem_singleton]; constructor <;>
        [exact fun h' => h'.2.1; exact fun h' => ⟨h' ▸ h.1, h', h.2⟩]⟩
    · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro u hu ⟨rfl, h2⟩
      exact h ⟨hu, h2⟩
  rw [e1, e2]

/-- Adding the leaf `w` to a set containing its neighbour removes the edge `xw` from the cut. -/
theorem cutCount_insert_leaf (hxw : G.Adj x w) (hw : G.degree w = 1) {W : Finset V}
    (hx : x ∈ W) (hwW : w ∉ W) : cutCount G (insert w W) + 1 = cutCount G W := by
  have hne : x ≠ w := hxw.ne
  unfold cutCount
  rw [Finset.sum_insert hwW]
  have h0 : (Finset.univ.filter (fun y => G.Adj w y ∧ y ∉ insert w W)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro y - ⟨hy, hyW⟩
    rw [adj_leaf_iff hxw hw] at hy
    exact hyW (Finset.mem_insert_of_mem (hy ▸ hx))
  rw [h0, zero_add]
  have hterm : ∀ u ∈ W, (Finset.univ.filter (fun y => G.Adj u y ∧ y ∉ insert w W)).card +
      (if u = x then 1 else 0) = (Finset.univ.filter (fun y => G.Adj u y ∧ y ∉ W)).card := by
    intro u _
    rw [Finset.card_filter, Finset.card_filter]
    have key : ∀ y, (if G.Adj u y ∧ y ∉ W then 1 else 0) =
        (if G.Adj u y ∧ y ∉ insert w W then 1 else 0) + (if u = x ∧ y = w then 1 else 0) := by
      intro y
      by_cases hyw : y = w
      · subst hyw
        have hiff : G.Adj u y ↔ u = x := by
          rw [G.adj_comm]; exact adj_leaf_iff hxw hw u
        by_cases hux : u = x
        · subst hux; simp [hxw, hwW]
        · have : ¬ G.Adj u y := fun h => hux (hiff.mp h)
          simp [hux, this]
      · simp [hyw, Finset.mem_insert]
    rw [Finset.sum_congr rfl (fun y _ => key y), Finset.sum_add_distrib]
    congr 1
    by_cases hux : u = x
    · subst hux; simp
    · simp [hux]
  rw [← Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_ite_eq' W x (fun _ => 1)]
  simp [hx]

/-- The profile after deleting the leaf edge `xw`: the end of `w` moves to `x`. -/
def leafProfile (b : V → ℕ) (x w : V) (u : V) : ℕ :=
  if u = x then b x + 1 else if u = w then 0 else b u

omit [Fintype V] in
theorem sum_leafProfile {b : V → ℕ} (hxw : x ≠ w) (hbw : b w = 1) (W : Finset V) :
    ∑ u ∈ W, leafProfile b x w u + (if w ∈ W then 1 else 0) =
      ∑ u ∈ W, b u + (if x ∈ W then 1 else 0) := by
  have hpt : ∀ u, leafProfile b x w u + (if u = w then 1 else 0) =
      b u + (if u = x then 1 else 0) := by
    intro u
    unfold leafProfile
    by_cases hux : u = x
    · subst hux; simp [hxw]
    · by_cases huw : u = w
      · subst huw; simp [hux, hbw]
      · simp [hux, huw]
  have := Finset.sum_congr rfl (fun u (_ : u ∈ W) => hpt u)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq' W w (fun _ => 1),
    Finset.sum_ite_eq' W x (fun _ => 1)] at this
  simpa using this

/-- **The leaf reduction keeps the cut conditions.** Let `w` be a leaf at `x` with one end, and
let `x` have at least two more edges than ends. Then `G − xw`, with the end of `w` moved to `x`,
satisfies (L) and (C) whenever `G` does. -/
theorem cutOK_leaf {b : V → ℕ} {p : ℕ} (hxw : G.Adj x w) (hw : G.degree w = 1) (hbw : b w = 1)
    (hbx : b x + 2 ≤ G.degree x) (h : CutOK G b p) :
    CutOK (delEdge G x w) (leafProfile b x w) p := by
  have hne : x ≠ w := hxw.ne
  obtain ⟨hL, hC⟩ := h
  have hdeg : ∀ v, (delEdge G x w).degree v + (if v = x then 1 else 0) +
      (if v = w then 1 else 0) = G.degree v := delEdge_degree G hxw
  have hb : ∀ v, leafProfile b x w v + (if v = w then 1 else 0) =
      b v + (if v = x then 1 else 0) := by
    intro v; unfold leafProfile
    by_cases hvx : v = x
    · subst hvx; simp [hne]
    · by_cases hvw : v = w
      · subst hvw; simp [hvx, hbw]
      · simp [hvx, hvw]
  refine ⟨fun v => ?_, fun v W hvW => ?_⟩
  · have h1 := hdeg v; have h2 := hb v; have h3 := hL v
    by_cases hvx : v = x
    · subst hvx; simp [hne] at h1 h2; omega
    · by_cases hvw : v = w
      · subst hvw; simp [hvx] at h1 h2; omega
      · simp [hvx, hvw] at h1 h2; omega
  · have hcut := cutCount_delEdge hxw W
    have hsum := sum_leafProfile hne hbw W
    have h1 := hdeg v; have h2 := hb v
    by_cases hxW : x ∈ W
    · by_cases hwW : w ∈ W
      · -- both inside: nothing changes
        have := hC v W hvW
        have hvx : v ≠ x := fun h' => hvW (h' ▸ hxW)
        have hvw : v ≠ w := fun h' => hvW (h' ▸ hwW)
        simp [hxW, hwW, hvx, hvw] at hcut hsum h1 h2
        omega
      · by_cases hvw : v = w
        · -- `v = w`: the condition of `G` at `w` itself
          subst hvw
          have := hC v W hvW
          have hvx : v ≠ x := Ne.symm hne
          simp [hxW, hwW, hvx] at hcut hsum h1 h2
          rw [hw, hbw] at this
          omega
        · -- `x ∈ W ∌ w`: the condition of `G` for `W ∪ {w}`
          have hvW' : v ∉ insert w W := by
            rw [Finset.mem_insert]; rintro (h' | h')
            · exact hvw h'
            · exact hvW h'
          have := hC v (insert w W) hvW'
          rw [Finset.sum_insert hwW, hbw] at this
          have hins := cutCount_insert_leaf hxw hw hxW hwW
          have hvx : v ≠ x := fun h' => hvW (h' ▸ hxW)
          simp [hxW, hwW, hvx, hvw] at hcut hsum h1 h2
          omega
    · by_cases hwW : w ∈ W
      · have := hC v W hvW
        have hvw : v ≠ w := fun h' => hvW (h' ▸ hwW)
        by_cases hvx : v = x
        · subst hvx
          simp [hxW, hwW, hvw] at hcut hsum h1 h2
          omega
        · simp [hxW, hwW, hvx, hvw] at hcut hsum h1 h2
          omega
      · have := hC v W hvW
        by_cases hvx : v = x
        · subst hvx
          simp [hxW, hwW, hne] at hcut hsum h1 h2
          omega
        · by_cases hvw : v = w
          · subst hvw
            simp [hxW, hwW, hvx] at hcut hsum h1 h2
            omega
          · simp [hxW, hwW, hvx, hvw] at hcut hsum h1 h2
            omega

/-- **Re-inserting the leaf edge.** A partition of `G − xw` in which the end of `w` sits at `x`
gives a partition of `G` with profile `b`: append `xw` to a path ending at `x`. -/
theorem ach_of_leaf {b : V → ℕ} (hxw : G.Adj x w) (hw : G.degree w = 1) (hbw : b w = 1)
    (h : Ach (delEdge G x w).edgeSet (leafProfile b x w)) : Ach G.edgeSet b := by
  have hne : x ≠ w := hxw.ne
  have hiso : ∀ y, s(w, y) ∉ (delEdge G x w).edgeSet := by
    intro y hy
    rw [delEdge_edgeSet] at hy
    have hy' : G.Adj w y := hy.1
    rw [adj_leaf_iff hxw hw] at hy'
    subst hy'
    exact hy.2 (Sym2.eq_swap)
  have hE : s(x, w) ∉ (delEdge G x w).edgeSet := fun h' => hiso x (by rw [Sym2.eq_swap]; exact h')
  have h2 := h.transfer hne hE (by
    rw [blankNbrs_eq_zero_of_isolated hiso]
    unfold leafProfile; simp)
  refine h2.congr ?_ (fun v => ?_)
  · ext e
    induction e using Sym2.inductionOn with
    | hf a c =>
      rw [Set.mem_insert_iff, delEdge_edgeSet]
      constructor
      · rintro (h' | ⟨h', -⟩)
        · rw [h']; exact hxw
        · exact h'
      · intro h'
        by_cases hac : s(a, c) = s(x, w)
        · exact Or.inl hac
        · exact Or.inr ⟨h', hac⟩
  · unfold mv leafProfile
    by_cases hvw : v = w
    · subst hvw; simp [Ne.symm hne, hbw]
    · by_cases hvx : v = x
      · subst hvx; simp [hvw]
      · simp [hvw, hvx]

/-- **Leaf step of the minimal counterexample.** If the cut conditions on `G − xw` (with the end of
the leaf moved to its neighbour) imply realisability there, then they imply it on `G`. -/
theorem leaf_step {b : V → ℕ} {p : ℕ} (hxw : G.Adj x w) (hw : G.degree w = 1) (hbw : b w = 1)
    (hbx : b x + 2 ≤ G.degree x)
    (hmin : CutOK (delEdge G x w) (leafProfile b x w) p →
      Ach (delEdge G x w).edgeSet (leafProfile b x w))
    (h : CutOK G b p) : Ach G.edgeSet b :=
  ach_of_leaf hxw hw hbw (hmin (cutOK_leaf hxw hw hbw hbx h))

end leaf

end Gallai
