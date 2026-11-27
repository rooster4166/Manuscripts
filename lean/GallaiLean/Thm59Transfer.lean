import GallaiLean.MarkedBlocks
import GallaiLean.ThreeConnected

/-!
# Theorem 59, step [T]: the finite-order block transfer

Marked-reduction manuscript, §2 ("Transfer through a block tree"), in the finite-order form used
by Theorem 59.

* `TwoConnOn.exists_walk_avoid`: in a two-connected instance, deleting at most one vertex leaves
  any two vertices joined.
* `kConnected_induce_of_twoConnOn`, `TwoConnected.kConnected`: the two-connectivity notion of
  `MarkedBlocks.lean` (`TwoConnOn`, no cut vertex) gives `KConnected 2`.
* `smallOn_of_smallBlocks`: `SmallBlocks F m` gives `SmallOn F m`.
* **`markedBoundUpTo_of_tests`**: the marked bound on two-connected graphs of order `≤ m` and the
  three-end test on two-connected graphs of order `≤ m` give `MarkedBoundUpTo m`.
-/

open SimpleGraph

set_option linter.unusedSectionVars false

namespace Gallai

universe u

section conversions

variable {V : Type u} [DecidableEq V]

/-- A walk of `G` inside `s` lifts to a walk of `G.induce s` with the same support. -/
theorem exists_induce_walk {G : SimpleGraph V} {s : Set V} :
    ∀ {a b : V} (p : G.Walk a b) (hp : ∀ v ∈ p.support, v ∈ s),
      ∃ q : (G.induce s).Walk ⟨a, hp a p.start_mem_support⟩ ⟨b, hp b p.end_mem_support⟩,
        q.support.map Subtype.val = p.support
  | _, _, .nil, _ => ⟨Walk.nil, rfl⟩
  | _, _, @Walk.cons _ _ a c _ h p, hp => by
    have hp' : ∀ v ∈ p.support, v ∈ s := fun v hv => hp v (by simp [hv])
    obtain ⟨q, hq⟩ := exists_induce_walk p hp'
    have hadj : (G.induce s).Adj ⟨a, hp a (by simp)⟩ ⟨c, hp' c p.start_mem_support⟩ := h
    exact ⟨Walk.cons hadj q, by simp [hq]⟩

/-- **Deleting at most one vertex** from a two-connected instance leaves any two of its vertices
joined. -/
theorem TwoConnOn.exists_walk_avoid {H : SimpleGraph V} {U : Finset V} (h : TwoConnOn H U)
    (hE : EdgesIn H U) {X : Finset V} (hX : X.card < 2) {a b : V} (ha : a ∈ U) (hb : b ∈ U)
    (haX : a ∉ X) (hbX : b ∉ X) : ∃ p : H.Walk a b, ∀ v ∈ p.support, v ∉ X := by
  classical
  rcases Nat.lt_or_ge X.card 1 with h0 | h1
  · have : X = ∅ := Finset.card_eq_zero.mp (by omega)
    subst this
    obtain ⟨p⟩ := h.2.1 a ha b hb
    exact ⟨p, fun v _ => Finset.notMem_empty v⟩
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (by omega : X.card = 1)
  simp only [Finset.mem_singleton] at haX hbX ⊢
  by_cases hxU : x ∉ U
  · obtain ⟨p⟩ := h.2.1 a ha b hb
    exact ⟨p, fun v hv hvx => hxU (hvx ▸ hE.walk_mem p ha v hv)⟩
  push Not at hxU
  by_contra hno
  push Not at hno
  set C := (U.erase x).filter (fun c => ∃ p : H.Walk a c, ∀ v ∈ p.support, v ≠ x) with hCdef
  have memC : ∀ c, c ∈ C ↔ c ∈ U.erase x ∧ ∃ p : H.Walk a c, ∀ v ∈ p.support, v ≠ x := by
    intro c; rw [hCdef, Finset.mem_filter]
  apply h.2.2 x C
  refine ⟨hxU, fun c hc => ((memC c).mp hc).1,
    ⟨a, (memC a).mpr ⟨Finset.mem_erase.mpr ⟨haX, ha⟩, Walk.nil, by simpa using haX⟩⟩,
    ⟨b, Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hbX, hb⟩, fun hbC => ?_⟩⟩, ?_⟩
  · obtain ⟨-, p, hp⟩ := (memC b).mp hbC
    obtain ⟨v, hv, hvx⟩ := hno p
    exact hp v hv hvx
  · intro c hc d hcd
    by_cases hdx : d = x
    · exact Or.inr hdx
    left
    obtain ⟨hcU, p, hp⟩ := (memC c).mp hc
    refine (memC d).mpr ⟨Finset.mem_erase.mpr ⟨hdx, (hE c d hcd).2⟩, p.concat hcd, ?_⟩
    intro v hv
    rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact hp v hv
    · exact hdx

variable [Fintype V]

omit [Fintype V] in
/-- A two-connected restriction (in the sense of `MarkedBlocks.lean`) is `KConnected 2`. -/
theorem kConnected_induce_of_twoConnOn {F : SimpleGraph V} {U : Finset V}
    (h : TwoConnOn (restrict F U) U) : KConnected 2 (F.induce (U : Set V)) := by
  classical
  refine kConnected_of_walks ?_ ?_
  · have hc : Fintype.card (U : Set V) = U.card := by simp
    rw [hc]; exact h.1
  intro X hX a b ha hb
  set X' : Finset V := X.map (Function.Embedding.subtype _) with hX'
  have hX'c : X'.card < 2 := by rw [hX', Finset.card_map]; exact hX
  have haX' : a.1 ∉ X' := by
    intro h'; obtain ⟨a', ha', h''⟩ := Finset.mem_map.mp h'
    exact ha (by rwa [show a = a' from Subtype.ext h''.symm])
  have hbX' : b.1 ∉ X' := by
    intro h'; obtain ⟨b', hb', h''⟩ := Finset.mem_map.mp h'
    exact hb (by rwa [show b = b' from Subtype.ext h''.symm])
  obtain ⟨p, hp⟩ := h.exists_walk_avoid (edgesIn_restrict U) hX'c a.2 b.2 haX' hbX'
  have hsub : ∀ v ∈ (p.mapLe (restrict_le U)).support, v ∈ (U : Set V) := by
    rw [Walk.support_mapLe_eq_support]
    exact (edgesIn_restrict U).walk_mem p a.2
  obtain ⟨q, hq⟩ := exists_induce_walk (p.mapLe (restrict_le U)) hsub
  refine ⟨q, fun v hv hvX => ?_⟩
  have h1 : v.1 ∈ p.support := by
    rw [← Walk.support_mapLe_eq_support (restrict_le U), ← hq]
    exact List.mem_map_of_mem hv
  exact hp v.1 h1 (Finset.mem_map_of_mem _ hvX)

/-- A two-connected graph (no cut vertex, `MarkedBlocks.lean`) is `KConnected 2`. -/
theorem TwoConnected.kConnected {G : SimpleGraph V} (h : TwoConnected G) : KConnected 2 G := by
  have hE : EdgesIn G Finset.univ := fun _ _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  refine kConnected_of_walks ?_ ?_
  · have := h.1; rw [Finset.card_univ] at this; exact this
  intro X hX a b ha hb
  exact h.exists_walk_avoid hE hX (Finset.mem_univ a) (Finset.mem_univ b) ha hb

theorem smallOn_of_smallBlocks {F : SimpleGraph V} {m : ℕ} (h : SmallBlocks F m) : SmallOn F m :=
  fun U' hU' => h U' (kConnected_induce_of_twoConnOn hU')

end conversions

/-- **Block transfer, finite-order form**: the marked bound and the three-end test on
two-connected graphs of order `≤ m` give the marked bound on every connected graph whose
two-connected blocks have order `≤ m`. -/
theorem markedBoundUpTo_of_tests {m : ℕ} (hA : MarkedTwoConnTestUpTo.{u} m)
    (hB : ThreeEndsTestUpTo.{u} m) : MarkedBoundUpTo.{u} m := by
  intro V _ _ F hF hSB S hS
  have := mbOn_of_testsUpTo hA hB _ F Finset.univ rfl
    (fun _ _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
    (fun a _ b _ => hF.preconnected a b) (smallOn_of_smallBlocks hSB) S
    (Finset.subset_univ _) hS
  rwa [Finset.card_univ] at this

end Gallai
