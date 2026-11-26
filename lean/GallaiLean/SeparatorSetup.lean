import GallaiLean.SmallBounds

/-!
# Setup for the separator theorem (marked-reduction, Theorem 113)

Let `B` be two-connected, `{x, y}` a separating pair and `C` a component of `B − {x, y}`.

* `sideA B C x y`: the local side `A = B[C ∪ {x, y}]`, with the edge `xy` when present.
* `sideE B C x y`: the exterior side `E = B − C − xy`.
* `edgeFinset_sides`, `degree_sides`: `B` is the edge-disjoint union of `A` and `E`.
* `sideE_induce_connected`: `E` is connected on `V ∖ C` (two-connectivity of `B`).
* `sideE_port_pos`, `sideA_port_pos`: both ports have positive degree in both sides.
* `sideA_parity`: `|C| + [d_A(x) odd] + [d_A(y) odd]` is even when every vertex of `C` is odd.
* **`rootedAt_of_lift`**: the root analysis shared by all cases of the proof. If an exterior graph
  `W` on `n − 2s` vertices (`s ≥ 1`) keeps the parity and positivity of the root degree, and every
  decomposition of `W` lifts to `B` with `s` more paths and the same ends at `r`, then `B` passes
  the rooted test at `r`.
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u}

/-! ### Induced connectivity helpers -/

section helpers

theorem induce_connected_mono {G H : SimpleGraph V} (hGH : G ≤ H) {U : Set V}
    (h : (G.induce U).Connected) : (H.induce U).Connected := by
  obtain ⟨hne, hw⟩ := induce_connected_iff.mp h
  refine induce_connected_iff.mpr ⟨hne, fun a ha b hb => ?_⟩
  obtain ⟨p, hp⟩ := hw a ha b hb
  exact ⟨p.mapLe hGH, by simpa using hp⟩

theorem induce_connected_insert [DecidableEq V] {H : SimpleGraph V} {U : Finset V}
    (h : (H.induce (U : Set V)).Connected) {a b : V} (ha : a ∈ U) (hab : H.Adj a b) :
    (H.induce ((insert b U : Finset V) : Set V)).Connected := by
  obtain ⟨-, hw⟩ := induce_connected_iff.mp h
  have hto : ∀ v ∈ insert b U, ∃ p : H.Walk v a, ∀ w ∈ p.support, w ∈ insert b U := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · refine ⟨Walk.cons hab.symm Walk.nil, fun w hw => ?_⟩
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem ha
    · obtain ⟨p, hp⟩ := hw v hv a ha
      exact ⟨p, fun w hw => Finset.mem_insert_of_mem (hp w hw)⟩
  refine induce_connected_iff.mpr ⟨⟨b, by simp⟩, fun p hp q hq => ?_⟩
  obtain ⟨w₁, h₁⟩ := hto p hp
  obtain ⟨w₂, h₂⟩ := hto q hq
  refine ⟨w₁.append w₂.reverse, fun w hw => ?_⟩
  rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hw
  rcases hw with hw | hw
  · exact h₁ w hw
  · exact h₂ w hw

theorem degree_pos_of_reachable [Fintype V] [DecidableRel (H : SimpleGraph V).Adj] {a b : V}
    (h : H.Reachable a b) (hab : a ≠ b) : 0 < H.degree b := by
  obtain ⟨p⟩ := h
  have : 0 < p.reverse.length := by
    rw [Walk.length_reverse]
    by_contra h0
    exact hab (Walk.eq_of_length_eq_zero (p := p) (by omega))
  obtain ⟨c, hc, -, -⟩ := Walk.exists_eq_cons_of_length_pos p.reverse this
  exact (H.degree_pos_iff_exists_adj b).mpr ⟨c, hc⟩

end helpers

/-! ### The two sides -/

/-- The local side `A = B[C ∪ {x, y}]`, with the edge `xy` if present. -/
def sideA (B : SimpleGraph V) (C : Finset V) (x y : V) : SimpleGraph V where
  Adj a b := B.Adj a b ∧ (a ∈ C ∨ b ∈ C ∨ (a = x ∧ b = y) ∨ (a = y ∧ b = x))
  symm := ⟨fun _ _ h => ⟨h.1.symm, by tauto⟩⟩
  loopless := ⟨fun a h => B.loopless.irrefl a h.1⟩

/-- The exterior side `E = B − C − xy`. -/
def sideE (B : SimpleGraph V) (C : Finset V) (x y : V) : SimpleGraph V where
  Adj a b := B.Adj a b ∧ a ∉ C ∧ b ∉ C ∧ ¬((a = x ∧ b = y) ∨ (a = y ∧ b = x))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2.1, h.2.1, by tauto⟩⟩
  loopless := ⟨fun a h => B.loopless.irrefl a h.1⟩

section sides

variable {B : SimpleGraph V} {C : Finset V} {x y : V}

theorem sideA_adj {a b : V} : (sideA B C x y).Adj a b ↔
    B.Adj a b ∧ (a ∈ C ∨ b ∈ C ∨ (a = x ∧ b = y) ∨ (a = y ∧ b = x)) := Iff.rfl

theorem sideE_adj {a b : V} : (sideE B C x y).Adj a b ↔
    B.Adj a b ∧ a ∉ C ∧ b ∉ C ∧ ¬((a = x ∧ b = y) ∨ (a = y ∧ b = x)) := Iff.rfl

instance sideA.decRel [DecidableEq V] (B : SimpleGraph V) [DecidableRel B.Adj] (C : Finset V)
    (x y : V) : DecidableRel (sideA B C x y).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

instance sideE.decRel [DecidableEq V] (B : SimpleGraph V) [DecidableRel B.Adj] (C : Finset V)
    (x y : V) : DecidableRel (sideE B C x y).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem sideA_le : sideA B C x y ≤ B := fun _ _ h => h.1
theorem sideE_le : sideE B C x y ≤ B := fun _ _ h => h.1

theorem adj_iff_sides {a b : V} :
    B.Adj a b ↔ (sideA B C x y).Adj a b ∨ (sideE B C x y).Adj a b := by
  simp only [sideA_adj, sideE_adj]; tauto

theorem not_sides {a b : V} : ¬ ((sideA B C x y).Adj a b ∧ (sideE B C x y).Adj a b) := by
  simp only [sideA_adj, sideE_adj]; tauto

theorem sideE_notMem {a b : V} (h : (sideE B C x y).Adj a b) : a ∉ C := h.2.1

/-- An `E`-walk from outside `C` stays outside `C`. -/
theorem sideE_walk_notMem : ∀ {a b : V} (p : (sideE B C x y).Walk a b), a ∉ C →
    ∀ w ∈ p.support, w ∉ C
  | _, _, .nil, ha, w, hw => by simp at hw; subst hw; exact ha
  | _, _, .cons h p, ha, w, hw => by
    rw [Walk.support_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact ha
    · exact sideE_walk_notMem p (sideE_notMem h.symm) w hw

section fin

variable [Fintype V] [DecidableEq V] [DecidableRel B.Adj]

theorem edgeFinset_sides :
    B.edgeFinset.val = (sideA B C x y).edgeFinset.val + (sideE B C x y).edgeFinset.val := by
  refine edgeFinset_val_eq_add _ (sideE B C x y).edgeFinset.nodup ?_ ?_
  · intro e he hA
    rw [Finset.mem_val, mem_edgeFinset] at he
    induction e using Sym2.inductionOn with
    | hf a b => exact not_sides ⟨hA, he⟩
  · intro e
    rw [Finset.mem_val, mem_edgeFinset]
    induction e using Sym2.inductionOn with
    | hf a b => exact adj_iff_sides

theorem degree_sides (v : V) :
    (sideA B C x y).degree v + (sideE B C x y).degree v = B.degree v := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
    ← card_neighborFinset_eq_degree, ← Finset.card_union_of_disjoint]
  · congr 1
    ext w
    simp only [Finset.mem_union, mem_neighborFinset]
    exact adj_iff_sides.symm
  · rw [Finset.disjoint_left]
    intro w h1 h2
    rw [mem_neighborFinset] at h1 h2
    exact not_sides ⟨h1, h2⟩

theorem sideE_degree_of_mem {c : V} (hc : c ∈ C) : (sideE B C x y).degree c = 0 := by
  rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro w hw
  rw [mem_neighborFinset] at hw
  exact sideE_notMem hw hc

theorem sideA_degree_of_mem {c : V} (hc : c ∈ C) : (sideA B C x y).degree c = B.degree c := by
  have := degree_sides (C := C) (x := x) (y := y) (B := B) c
  rw [sideE_degree_of_mem hc] at this
  omega

end fin

variable (hC : IsSepComponent B x y C)
include hC

theorem sideA_support {a b : V} (h : (sideA B C x y).Adj a b) : a ∈ C ∨ a = x ∨ a = y := by
  rcases h.2 with h' | h' | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl h'
  · rcases hC.closed b h' a h.1.symm with h'' | h'' | h''
    · exact Or.inl h''
    · exact Or.inr (Or.inl h'')
    · exact Or.inr (Or.inr h'')
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem sideA_degree_of_ext [Fintype V] [DecidableEq V] [DecidableRel B.Adj] {v : V}
    (hv : v ∉ C) (hvx : v ≠ x) (hvy : v ≠ y) : (sideA B C x y).degree v = 0 := by
  rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro w hw
  rw [mem_neighborFinset] at hw
  rcases sideA_support hC hw with h | h | h
  · exact hv h
  · exact hvx h
  · exact hvy h

/-- Inside `B − q`, a walk from outside `C` either reaches the other port `p` in `E` first, or
stays in `E` all the way. -/
theorem sideE_reach_aux {p q : V} (hpq : (p = x ∧ q = y) ∨ (p = y ∧ q = x)) :
    ∀ {v t : V} (w : B.Walk v t), v ∉ C → q ∉ w.support →
      (sideE B C x y).Reachable v p ∨ (t ∉ C ∧ (sideE B C x y).Reachable v t)
  | _, _, .nil, hv, _ => Or.inr ⟨hv, Reachable.refl _⟩
  | v, _, .cons (v := w₁) h w', hv, hq => by
    by_cases hvp : v = p
    · subst hvp; exact Or.inl (Reachable.refl _)
    have hvq : v ≠ q := fun h' => hq (by rw [Walk.support_cons, h']; exact List.mem_cons_self)
    have hvxy : v ≠ x ∧ v ≠ y := by
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hvp, hvq⟩
      · exact ⟨hvq, hvp⟩
    have hw₁ : w₁ ∉ C := by
      intro hw₁
      rcases hC.closed w₁ hw₁ v h.symm with h' | h' | h'
      · exact hv h'
      · exact hvxy.1 h'
      · exact hvxy.2 h'
    have hE : (sideE B C x y).Adj v w₁ := ⟨h, hv, hw₁, by tauto⟩
    have hq' : q ∉ w'.support := fun h' => hq (by
      rw [Walk.support_cons]; exact List.mem_cons_of_mem _ h')
    rcases sideE_reach_aux hpq w' hw₁ hq' with h' | ⟨ht, h'⟩
    · exact Or.inl (hE.reachable.trans h')
    · exact Or.inr ⟨ht, hE.reachable.trans h'⟩

theorem sideE_reach [Fintype V] (hB : KConnected 2 B) {p q : V}
    (hpq : (p = x ∧ q = y) ∨ (p = y ∧ q = x)) {v : V} (hv : v ∉ C) (hvq : v ≠ q) :
    (sideE B C x y).Reachable v p := by
  have hpq' : p ≠ q := by rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hC.ne; exact hC.ne.symm]
  obtain ⟨w, hw⟩ := hB.walk (X := {q}) (by simp) (a := v) (b := p) (by simpa using hvq)
    (by simpa using hpq')
  rcases sideE_reach_aux hC hpq w hv (fun h => hw q h (Finset.mem_singleton_self q)) with h | ⟨-, h⟩
  · exact h
  · exact h

theorem sideE_reach_all [Fintype V] (hB : KConnected 2 B) {a b : V} (ha : a ∉ C) (hb : b ∉ C) :
    (sideE B C x y).Reachable a b := by
  obtain ⟨w, hwC, hwx, hwy⟩ := hC.sep
  have hto : ∀ v, v ∉ C → (sideE B C x y).Reachable v w := by
    intro v hv
    by_cases hvy : v = y
    · subst hvy
      exact (sideE_reach hC hB (Or.inr ⟨rfl, rfl⟩) hwC hwx).symm
    · exact (sideE_reach hC hB (Or.inl ⟨rfl, rfl⟩) hv hvy).trans
        (sideE_reach hC hB (Or.inl ⟨rfl, rfl⟩) hwC hwy).symm
  exact (hto a ha).trans (hto b hb).symm

theorem sideE_induce_connected [Fintype V] [DecidableEq V] (hB : KConnected 2 B) :
    ((sideE B C x y).induce ((Cᶜ : Finset V) : Set V)).Connected := by
  obtain ⟨w, hwC, -, -⟩ := hC.sep
  refine induce_connected_iff.mpr ⟨⟨w, by simpa using hwC⟩, fun a ha b hb => ?_⟩
  have ha' : a ∉ C := by simpa using ha
  have hb' : b ∉ C := by simpa using hb
  obtain ⟨p⟩ := sideE_reach_all hC hB ha' hb'
  exact ⟨p, fun v hv => by simpa using sideE_walk_notMem p ha' v hv⟩

theorem sideE_port_pos [Fintype V] [DecidableEq V] [DecidableRel B.Adj] (hB : KConnected 2 B) :
    0 < (sideE B C x y).degree x ∧ 0 < (sideE B C x y).degree y := by
  obtain ⟨w, hwC, hwx, hwy⟩ := hC.sep
  exact ⟨degree_pos_of_reachable (sideE_reach_all hC hB hwC hC.x_notMem) hwx,
    degree_pos_of_reachable (sideE_reach_all hC hB hwC hC.y_notMem) hwy⟩

theorem sideA_port_pos [Fintype V] [DecidableEq V] [DecidableRel B.Adj] (hB : KConnected 2 B) :
    0 < (sideA B C x y).degree x ∧ 0 < (sideA B C x y).degree y := by
  obtain ⟨w, hwC, hwx, hwy⟩ := hC.sep
  obtain ⟨c, hc⟩ := hC.nonempty
  have key : ∀ p q, (p = x ∧ q = y) ∨ (p = y ∧ q = x) → 0 < (sideA B C x y).degree p := by
    intro p q hpq
    have hwq : w ≠ q := by rcases hpq with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
    have hcq : c ≠ q := by
      rcases hpq with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact fun h => hC.y_notMem (h ▸ hc)
      · exact fun h => hC.x_notMem (h ▸ hc)
    obtain ⟨wk, hwk⟩ := hB.walk (X := {q}) (by simp) (a := c) (b := w) (by simpa using hcq)
      (by simpa using hwq)
    obtain ⟨d, hd, hd1, hd2⟩ := wk.exists_boundary_dart (C : Set V) hc hwC
    have hd2' : d.snd = x ∨ d.snd = y := by
      rcases hC.closed d.fst hd1 d.snd d.adj with h | h | h
      · exact absurd h hd2
      · exact Or.inl h
      · exact Or.inr h
    have hdq : d.snd ≠ q := fun h =>
      hwk q (h ▸ wk.dart_snd_mem_support_of_mem_darts hd) (Finset.mem_singleton_self q)
    have hdp : d.snd = p := by
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
    rw [← hdp]
    exact (sideA B C x y).degree_pos_iff_exists_adj _ |>.mpr
      ⟨d.fst, (show (sideA B C x y).Adj d.fst d.snd from ⟨d.adj, Or.inl hd1⟩).symm⟩
  exact ⟨key x y (Or.inl ⟨rfl, rfl⟩), key y x (Or.inr ⟨rfl, rfl⟩)⟩

/-- Parity in `A`: `|C| + [d_A(x) odd] + [d_A(y) odd]` is even. -/
theorem sideA_parity [Fintype V] [DecidableEq V] [DecidableRel B.Adj]
    (hodd : ∀ c ∈ C, Odd (B.degree c)) :
    Even (C.card + (if Odd ((sideA B C x y).degree x) then 1 else 0) +
      (if Odd ((sideA B C x y).degree y) then 1 else 0)) := by
  have hh := (sideA B C x y).even_card_odd_degree_vertices
  set P : V → Prop := fun v => Odd ((sideA B C x y).degree v)
  have hfil : Finset.univ.filter P = C ∪ ({x, y} : Finset V).filter P := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hv
      by_cases hvC : v ∈ C
      · exact Or.inl hvC
      · right
        refine ⟨?_, hv⟩
        by_contra hxy
        push Not at hxy
        rw [show P v ↔ Odd ((sideA B C x y).degree v) from Iff.rfl,
          sideA_degree_of_ext hC hvC hxy.1 hxy.2] at hv
        exact absurd hv (by decide)
    · rintro (hvC | ⟨-, hv⟩)
      · show Odd _
        rw [sideA_degree_of_mem hvC]; exact hodd v hvC
      · exact hv
  have hdisj : Disjoint C (({x, y} : Finset V).filter P) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hv'
    rcases hv'.1 with rfl | rfl
    · exact hC.x_notMem hv
    · exact hC.y_notMem hv
  rw [hfil, Finset.card_union_of_disjoint hdisj] at hh
  have hxy : (({x, y} : Finset V).filter P).card =
      (if P x then 1 else 0) + (if P y then 1 else 0) := by
    rw [Finset.filter_insert, Finset.filter_singleton]
    by_cases hx : P x <;> by_cases hy : P y <;>
      simp [hx, hy, Finset.card_insert_of_notMem, hC.ne]
  rw [hxy] at hh
  simpa only [add_assoc] using hh

end sides

/-! ### The root analysis -/

section root

variable [Fintype V] [DecidableEq V] {B : SimpleGraph V} [DecidableRel B.Adj]

/-- **The root analysis of Theorem 113.** Let `W` be a graph with all its edges inside `U`,
connected on `U`, with `|U| = n − 2s` and `s ≥ 1`. If the root `r ∈ U` has positive `W`-degree of
the same parity as in `B`, and every decomposition of `W` lifts to one of `B` with at most `s` more
paths and the same number of ends at `r`, then `B` passes the rooted test at `r`: the smaller
rooted bound (`F₂`, `F₃`), or the floor plus a split when the odd root drops to degree one. -/
theorem rootedAt_of_lift (hMB : MarkedBoundUpTo.{u} (Fintype.card V - 2)) (hB : KConnected 2 B)
    (r : V) (W : SimpleGraph V) [DecidableRel W.Adj] (U : Finset V) (s : ℕ) (hs : 1 ≤ s)
    (hWU : ∀ a b, W.Adj a b → a ∈ U) (hWc : (W.induce (U : Set V)).Connected)
    (hcard : U.card + 2 * s = Fintype.card V) (hrU : r ∈ U)
    (hpar : W.degree r % 2 = B.degree r % 2) (hpos : 0 < W.degree r)
    (hlift : ∀ D : PathDecomp W,
      ∃ D' : PathDecomp B, D'.size ≤ D.size + s ∧ D'.ends r = D.ends r) :
    RootedAt B r := by
  have hUm : U.card ≤ Fintype.card V - 2 := by omega
  have h2 := hB.le_degree r
  constructor
  · intro hn hr
    have hev : Even U.card := by obtain ⟨a, ha⟩ := hn; exact ⟨a - s, by omega⟩
    have hWr : Even (W.degree r) := by rw [Nat.even_iff] at hr ⊢; omega
    obtain ⟨D, hD1, hD2⟩ := R2_on hMB hWU hWc hUm hev hrU hWr hpos
    obtain ⟨D', h1, h2⟩ := hlift D
    refine ⟨D', ?_, by omega⟩
    obtain ⟨a, ha⟩ := hev
    omega
  · intro hn hr
    have hodd : Odd U.card := by obtain ⟨a, ha⟩ := hn; exact ⟨a - s, by omega⟩
    have hWr : Odd (W.degree r) := by rw [Nat.odd_iff] at hr ⊢; omega
    obtain ⟨j, hj⟩ := hodd
    by_cases h3 : 3 ≤ W.degree r
    · obtain ⟨D, hD1, hD2⟩ := R3_on hMB hWU hWc hUm ⟨j, hj⟩ hrU hWr h3
      obtain ⟨D', h1, h2⟩ := hlift D
      exact ⟨D', by omega, by omega⟩
    · have h1 : W.degree r = 1 := by
        rw [Nat.odd_iff] at hWr; omega
      obtain ⟨D, hD1⟩ := floor_on hMB hWU hWc hUm ⟨j, hj⟩ hrU h1
      obtain ⟨D', h1', -⟩ := hlift D
      have h3B : 3 ≤ B.degree r := by
        rw [Nat.odd_iff] at hr; omega
      obtain ⟨D'', h1'', h2''⟩ := exists_three_ends D' (k := Fintype.card V / 2) (by omega) hr h3B
      exact ⟨D'', h1'', h2''⟩

end root

end Gallai
