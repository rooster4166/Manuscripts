import GallaiLean.TwoEven
import GallaiLean.Lovasz
import GallaiLean.MultiToken

/-!
# Conjecture 31 (two-even tightness) and its profile form PC

Manuscript `manuscripts/conj31`. An *end profile* of `G` is a function `b : V → ℕ`; it is
*realisable* (`RealisesProfile G b`) if some path decomposition has exactly `b v` ends at every
vertex `v`. Tightness of a graph with two even vertices is realisability of the parity profile
(`tight_iff_realisesProfile`).

* `degree_add_le_sum_of_realises` (**degree bound (DB)**, necessary): `d(x) + b(x) ≤ ∑ b`.
* `universal_of_not_degreeBound` (manuscript Lemma 2.3): if `b ≡ d (mod 2)`, `b ≥ 1` off a set `Z`
  with `|Z| ≤ 2`, and (DB) fails at `x`, then `|Z| = 2`, `Z ⊆ N(x)` and `x` is adjacent to every
  other vertex. (With `|Z| ≤ 1`, (DB) always holds.)
* `ProfileConj` (Conjecture PC, as a proposition) and `Conj31On` (Conjecture 31);
  **`conj31_of_profileConj`**: PC implies Conjecture 31.
* Reduction moves of PC (manuscript Section 4), profile form:
  `realisesProfile_transfer` (**TR**, Fan's lemma), `realisesProfile_newPath` (**NEW**),
  `realisesProfile_suppress` (**SUP**, subdividing back), `realisesProfile_tri` (**TRI**: delete
  `xy`, suppress the degree-two vertex `u` with `N(u) = {x, y}`, Fan's lemma at `y`).
-/

open SimpleGraph Finset

namespace Gallai

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- `b` is a realisable end profile of `G`. -/
def RealisesProfile (G : SimpleGraph V) (b : V → ℕ) : Prop :=
  ∃ D : PathDecomp G, ∀ v, D.ends v = b v

section moves

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Tightness is realisability of the parity profile `d mod 2`. -/
theorem tight_iff_realisesProfile : Tight G ↔ RealisesProfile G (fun v => G.degree v % 2) := by
  have key : ∀ v, profile G ∅ v = G.degree v % 2 := by
    intro v
    unfold profile
    rcases Nat.even_or_odd (G.degree v) with h | h
    · have h' : ¬ Odd (G.degree v) := Nat.not_odd_iff_even.mpr h
      rw [if_neg h', if_neg (Finset.notMem_empty v), Nat.even_iff.mp h]
    · rw [if_pos h, Nat.odd_iff.mp h]
  constructor
  · rintro ⟨-, D, hD⟩
    exact ⟨D, fun v => by rw [hD v, key v]⟩
  · rintro ⟨D, hD⟩
    exact ⟨Finset.empty_subset _, D, fun v => by rw [hD v, key v]⟩

/-- **(DB) is necessary.** A path has at most two edges at `x`, and one fewer for each of its ends
at `x`; and there are `∑ b / 2` paths. -/
theorem degree_add_le_sum_of_realises {b : V → ℕ} (h : RealisesProfile G b) (x : V) :
    G.degree x + b x ≤ ∑ v, b v := by
  obtain ⟨D, hD⟩ := h
  have h1 := D.degree_add_ends_le x
  have h2 := D.sum_ends
  have h3 : ∑ v, D.ends v = ∑ v, b v := Finset.sum_congr rfl (fun v _ => hD v)
  rw [hD x] at h1
  omega

/-- The sum of a profile congruent to the degrees is even. -/
theorem sum_profile_mod_two {b : V → ℕ} (hpar : ∀ v, b v % 2 = G.degree v % 2) :
    (∑ v, b v) % 2 = 0 := by
  rw [Finset.sum_nat_mod, Finset.sum_congr rfl (fun v _ => hpar v), ← Finset.sum_nat_mod,
    sum_degrees_eq_twice_card_edges]
  omega

/-- **Where (DB) can fail** (manuscript Lemma 2.3). Let `b ≡ d (mod 2)` with `b ≥ 1` outside a
set `Z` of at most two vertices. If `∑ b < d(x) + b(x)`, then `|Z| = 2`, both vertices of `Z` are
neighbours of `x`, and `x` is adjacent to every other vertex. The slack `∑_{y ≠ x} b(y) − d(x)` is
even and at least `−|N(x) ∩ Z|`. -/
theorem universal_of_not_degreeBound {b : V → ℕ} {Z : Finset V} (hZ : Z.card ≤ 2)
    (hpos : ∀ v, v ∉ Z → 1 ≤ b v) (hpar : ∀ v, b v % 2 = G.degree v % 2) {x : V}
    (hx : ∑ v, b v < G.degree x + b x) :
    Z.card = 2 ∧ Z ⊆ G.neighborFinset x ∧ ∀ y, y ≠ x → G.Adj x y := by
  set N := G.neighborFinset x with hN
  set R := (univ.erase x) \ N with hR
  have hNsub : N ⊆ univ.erase x := by
    intro y hy
    rw [Finset.mem_erase]
    exact ⟨(G.ne_of_adj ((G.mem_neighborFinset x y).mp hy)).symm, Finset.mem_univ _⟩
  -- the split of the sum
  have hsplit : ∑ v, b v = b x + (∑ y ∈ N, b y + ∑ y ∈ R, b y) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), ← Finset.sum_sdiff hNsub, add_comm
      (∑ y ∈ R, b y)]
  -- lower bounds
  have hlow : ∀ s : Finset V, (s \ Z).card ≤ ∑ y ∈ s, b y := by
    intro s
    calc (s \ Z).card = ∑ y ∈ s \ Z, 1 := by rw [Finset.card_eq_sum_ones]
      _ ≤ ∑ y ∈ s \ Z, b y := Finset.sum_le_sum (fun y hy => hpos y (Finset.mem_sdiff.mp hy).2)
      _ ≤ ∑ y ∈ s, b y := Finset.sum_le_sum_of_subset Finset.sdiff_subset
  have hN1 := hlow N
  have hR1 := hlow R
  have hNcard : (N \ Z).card + (N ∩ Z).card = G.degree x := by
    rw [Finset.card_sdiff_add_card_inter, hN, card_neighborFinset_eq_degree]
  have hNZ : (N ∩ Z).card ≤ Z.card := Finset.card_le_card Finset.inter_subset_right
  have hS := sum_profile_mod_two hpar
  have hpx := hpar x
  have hB : (N ∩ Z).card = 2 ∧ (R \ Z).card = 0 := by omega
  have hZN : N ∩ Z = Z :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  have hZsub : Z ⊆ N := by rw [← hZN]; exact Finset.inter_subset_left
  refine ⟨by omega, hZsub, ?_⟩
  intro y hyx
  by_contra hadj
  have hyN : y ∉ N := fun h => hadj ((G.mem_neighborFinset x y).mp h)
  have hyR : y ∈ R := Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hyx, Finset.mem_univ _⟩, hyN⟩
  have hyZ : y ∉ Z := fun h => hyN (hZsub h)
  have : y ∈ R \ Z := Finset.mem_sdiff.mpr ⟨hyR, hyZ⟩
  have hpos' : 0 < (R \ Z).card := Finset.card_pos.mpr ⟨y, this⟩
  omega

/-- **Move TR** (Fan's lemma, profile form). If `G − ac` realises `b'` and fewer than `b'(c)`
neighbours of `a` in `G − ac` have no end, then `G` realises the profile with one more end at `a`
and one fewer at `c`. -/
theorem realisesProfile_transfer {a c : V} (hac : G.Adj a c) {b' : V → ℕ}
    (h' : RealisesProfile (delEdge G a c) b')
    (hcnt : (univ.filter (fun w => (delEdge G a c).Adj a w ∧ b' w = 0)).card < b' c) :
    RealisesProfile G (fun w => if w = a then b' a + 1 else if w = c then b' c - 1 else b' w) := by
  obtain ⟨D', hD'⟩ := h'
  have hcnt' : (univ.filter (fun w => (delEdge G a c).Adj a w ∧ D'.ends w = 0)).card <
      D'.ends c := by
    simp only [hD']
    exact hcnt
  obtain ⟨D, -, h1, h2, h3⟩ := fan_single hac (delEdge_edgeSet G a c) D' hcnt'
  refine ⟨D, fun w => ?_⟩
  dsimp only
  by_cases hwa : w = a
  · rw [if_pos hwa, hwa, h1, hD']
  · by_cases hwc : w = c
    · rw [if_neg hwa, if_pos hwc, hwc]
      rw [hD'] at h2
      omega
    · rw [if_neg hwa, if_neg hwc, h3 w hwa hwc, hD']

/-- **Move NEW**: the edge `ac` as a path of its own. -/
theorem realisesProfile_newPath {a c : V} (hac : G.Adj a c) {b' : V → ℕ}
    (h' : RealisesProfile (delEdge G a c) b') :
    RealisesProfile G (fun w => b' w + (if a = w then 1 else 0) + (if c = w then 1 else 0)) := by
  obtain ⟨D', hD'⟩ := h'
  obtain ⟨D, hD⟩ := PathDecomp.add_edge hac (delEdge_edgeSet G a c) D'
  exact ⟨D, fun w => by rw [hD w, hD' w]⟩

/-- **Move SUP**: a vertex `g` with `N(g) = {a, c}`, `ac ∉ E`; a realisation of `G − ga − gc + ac`
gives one of `G` with the same profile (`g` has no end). -/
theorem realisesProfile_suppress {g a c : V} (hNg : ∀ v, G.Adj g v ↔ v = a ∨ v = c)
    (hac : a ≠ c) (hnadj : ¬ G.Adj a c) {b : V → ℕ}
    (h : RealisesProfile (plusEdge (delEdge (delEdge G g a) g c) a c) b) :
    RealisesProfile G b := by
  obtain ⟨DH, hDH⟩ := h
  obtain ⟨D, hD, -⟩ := splitOff_supp hNg hac hnadj DH
  exact ⟨D, fun v => by rw [hD v, hDH v]⟩

/-- **Move TRI**: `N(u) = {x, y}` with `xy ∈ E`. Delete `xy`; in `G − xy` the vertex `u` can be
suppressed, which gives back the graph `G − u` (with `xy`). A realisation `b₁` of that graph, and
Fan's count at `y` in `G − xy`, give a realisation of `G` with one more end at `y` and one fewer
at `x`. -/
theorem realisesProfile_tri {u x y : V} (hNu : ∀ v, G.Adj u v ↔ v = x ∨ v = y)
    (hyx : G.Adj y x) {b₁ : V → ℕ}
    (h₁ : RealisesProfile (plusEdge (delEdge (delEdge (delEdge G y x) u x) u y) x y) b₁)
    (hcnt : (univ.filter (fun w => (delEdge G y x).Adj y w ∧ b₁ w = 0)).card < b₁ x) :
    RealisesProfile G (fun w => if w = y then b₁ y + 1 else if w = x then b₁ x - 1 else b₁ w) := by
  have hux : u ≠ x := ((hNu x).mpr (Or.inl rfl)).ne
  have huy : u ≠ y := ((hNu y).mpr (Or.inr rfl)).ne
  have hNu' : ∀ v, (delEdge G y x).Adj u v ↔ v = x ∨ v = y := by
    intro v
    constructor
    · intro h
      exact (hNu v).mp h.1
    · intro h
      refine ⟨(hNu v).mpr h, ?_⟩
      intro heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact huy h1
      · exact hux h1
  have hnadj : ¬ (delEdge G y x).Adj x y := by
    rintro ⟨-, h⟩
    exact h Sym2.eq_swap
  exact realisesProfile_transfer hyx
    (realisesProfile_suppress hNu' hyx.ne.symm hnadj h₁) hcnt

end moves

/-! ### Conjecture PC implies Conjecture 31

`TwoConnected` is the project's notion (`MarkedBlocks.lean`: no cut vertex); the implication below
does not use it beyond passing it on. -/

/-- **Conjecture PC** (profile form of Conjecture 31). In a 2-connected graph, a profile with at
most two zeros, `b ≡ d (mod 2)` and `1 ≤ b ≤ d` off the zeros, is realisable iff (DB) holds. -/
def ProfileConj (V : Type u) [Fintype V] [DecidableEq V] : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj], TwoConnected G → ∀ (Z : Finset V) (b : V → ℕ),
    Z.card ≤ 2 → (∀ z ∈ Z, b z = 0) → (∀ v, v ∉ Z → 1 ≤ b v) → (∀ v, b v ≤ G.degree v) →
    (∀ v, b v % 2 = G.degree v % 2) → (∀ x, G.degree x + b x ≤ ∑ v, b v) → RealisesProfile G b

/-- **Conjecture 31.** A 2-connected graph with exactly two even vertices `u, v` and no odd vertex
of degree `n − 1` is tight. -/
def Conj31On (V : Type u) [Fintype V] [DecidableEq V] : Prop :=
  ∀ (H : SimpleGraph V) [DecidableRel H.Adj], TwoConnected H → ∀ u v : V, u ≠ v →
    evenSet H = {u, v} → (∀ w, 0 < H.degree w) →
    (∀ w, Odd (H.degree w) → H.degree w + 1 < Fintype.card V) → Tight H

/-- A vertex adjacent to all others has degree `n − 1`. -/
theorem degree_of_adj_all {G : SimpleGraph V} [DecidableRel G.Adj] {x : V}
    (h : ∀ y, y ≠ x → G.Adj x y) : G.degree x + 1 = Fintype.card V := by
  have hN : G.neighborFinset x = univ.erase x := by
    ext y
    rw [mem_neighborFinset, Finset.mem_erase]
    constructor
    · intro hxy
      exact ⟨fun h' => G.loopless.irrefl x (h' ▸ hxy), Finset.mem_univ _⟩
    · rintro ⟨hyx, -⟩
      exact h y hyx
  rw [← card_neighborFinset_eq_degree, hN, Finset.card_erase_of_mem (Finset.mem_univ x),
    Finset.card_univ]
  have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
  omega

/-- **PC implies Conjecture 31.** -/
theorem conj31_of_profileConj (hPC : ProfileConj V) : Conj31On V := by
  intro H _ h2 u v huv hEv hdeg huniv
  rw [tight_iff_realisesProfile]
  have hZ : ∀ w, w ∈ ({u, v} : Finset V) ↔ Even (H.degree w) := by
    intro w
    rw [← hEv]
    simp [evenSet, hdeg w]
  have hpos : ∀ w, w ∉ ({u, v} : Finset V) → 1 ≤ H.degree w % 2 := by
    intro w hw
    have h' : ¬ Even (H.degree w) := fun h => hw ((hZ w).mpr h)
    rw [Nat.not_even_iff_odd] at h'
    rw [Nat.odd_iff.mp h']
  have hpar : ∀ w, H.degree w % 2 % 2 = H.degree w % 2 := fun w => Nat.mod_mod _ _
  refine hPC H h2 {u, v} _ Finset.card_le_two ?_ hpos (fun w => Nat.mod_le _ _) hpar ?_
  · intro z hz
    exact Nat.even_iff.mp ((hZ z).mp hz)
  · intro x
    by_contra hcon'
    have hcon := Nat.lt_of_not_le hcon'
    obtain ⟨-, -, hall⟩ := universal_of_not_degreeBound Finset.card_le_two hpos hpar hcon
    have hdx := degree_of_adj_all hall
    -- the order is even: the odd vertices are the vertices outside `{u, v}`
    have hcardEv : (univ.filter (fun w => ¬ Odd (H.degree w))).card = 2 := by
      have : univ.filter (fun w => ¬ Odd (H.degree w)) = ({u, v} : Finset V) := by
        ext w
        rw [Finset.mem_filter, hZ w, Nat.not_odd_iff_even]
        simp
      rw [this, Finset.card_pair huv]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset V)) (fun w => Odd (H.degree w))
    obtain ⟨r, hr⟩ := H.even_card_odd_degree_vertices
    rw [Finset.card_univ] at hsplit
    rcases Nat.even_or_odd (H.degree x) with he | ho
    · obtain ⟨s, hs⟩ := he
      omega
    · have := huniv x ho
      omega

end Gallai
