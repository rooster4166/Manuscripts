import GallaiLean.Thm59Hall
import GallaiLean.ThreeConnected
import GallaiLean.Lovasz

/-!
# Theorem 59, step [C]: the marked tests on blocks without a matching cut

Marked-reduction manuscript, §17, first paragraph of the proof of Theorem 59.

Let `B ∈ C` (two-connected, no matching cut) have order `n`, and assume both rooted assertions
(`RootedAt`) on every member of `C` of order at most `n + 1`. Then:

* **`markedBound_of_classC`**: `q(B, S) ≤ ⌊(n − |S|)/2⌋` for every nonempty `S`;
* **`threeEnds_of_classC`**: the three-end condition of Theorem 1 at every odd root.

Ingredients:

* `apex_inClassC`: the cone `X = B + z` over `|S| ≥ 2` marks is in `C`. It is two-connected, and a
  matching cut would have `B` on one side and `z` on the other, with two edges at `z`.
* `apex_outEnds_bound`: the cone identity of §1 (`le_outEnds`) as
  `|S| + 2 q(B, S) + b_D(z) ≤ 2|D|` for every decomposition `D` of `X`.
* `cone_step`: if `n − |S|` is odd, the rooted test at the apex gives
  `2|D| − b_D(z) ≤ n − 1`: test 2 at even `n`, test 1 at odd `n`.
* `singleton_step`: at even order, test 1 at `x`, or at another even vertex, or Lovász's theorem
  (all degrees odd), and then parity gives an end at `x`. At odd order, use
  `q(B, {x}) ≤ q(B, {x, y}) + 1` and the two-mark case.
* If `n − |S|` is even, removing a mark keeps the bound (`markedNumber_anti`).
-/

open SimpleGraph

namespace Gallai

universe u

section markedMono

variable {V : Type u} {F : SimpleGraph V}

/-- More marks can only lower the marked number. -/
theorem markedNumber_anti [Finite V] {S S' : Finset V} (h : S' ⊆ S) :
    markedNumber F S ≤ markedNumber F S' := by
  obtain ⟨M, hM⟩ := markedNumber_spec F S'
  let M' : MarkedPartition F S := ⟨M.paths, M.nodup_edges, M.covers,
    fun x hx s hs => ⟨h (M.site_ok x hx s hs).1, (M.site_ok x hx s hs).2⟩, M.sites_nodup⟩
  have : markedNumber F S ≤ markedCost M' := markedNumber_le M'
  rw [← hM]; exact this

/-- A marked partition as a partial marked partition of all edges. -/
def MarkedPartition.toPMP {S : Finset V} (M : MarkedPartition F S) : PMP F F.edgeSet S :=
  ⟨M.paths, M.nodup_edges, M.covers, M.site_ok, M.sites_nodup⟩

/-- Removing one mark costs at most one path. -/
theorem markedNumber_le_insert [Finite V] [DecidableEq V] (S : Finset V) (y : V) :
    markedNumber F S ≤ markedNumber F (insert y S) + 1 := by
  obtain ⟨M, hM⟩ := markedNumber_spec F (insert y S)
  have h1 := ((M.toPMP.forget y).mono (Finset.erase_insert_subset y S)).markedNumber_le_cost
  have h2 := M.toPMP.forget_cost_le y
  have h3 : M.toPMP.cost = markedCost M := rfl
  have h4 : ((M.toPMP.forget y).mono (Finset.erase_insert_subset y S)).cost =
    (M.toPMP.forget y).cost := rfl
  omega

/-- An end at `x` can be assigned to `x`. -/
theorem markedNumber_singleton_add_one [DecidableEq V] (D : PathDecomp F) {x : V}
    (h : 1 ≤ D.ends x) : markedNumber F {x} + 1 ≤ D.size := by
  have := markedNumber_add_card_le D {x} {x} (by simpa using h)
    (fun v hv hv' => absurd hv hv')
  simpa using this

end markedMono

section apexC

variable {V : Type u} [Fintype V] [DecidableEq V] {B : SimpleGraph V} [DecidableRel B.Adj]
  {S : Finset V}

omit [Fintype V] [DecidableEq V] [DecidableRel B.Adj] in
theorem apex_eq_cone : apex B S = cone B S := by
  ext x y; cases x <;> cases y <;> rfl

omit [DecidableRel B.Adj] in
/-- **The cone identity** (§1, Identity A) in the form used by Theorem 59:
`|S| + 2 q(B, S) + b_D(z) ≤ 2|D|` for every decomposition of the cone. -/
theorem apex_outEnds_bound (D : PathDecomp (apex B S)) :
    S.card + 2 * markedNumber B S + D.ends none ≤ 2 * D.size := by
  have h2 := D.two_mul_size_eq
  have key : ∀ (G : SimpleGraph (Option V)), G = cone B S → ∀ D : PathDecomp G,
      S.card + 2 * markedNumber B S ≤ D.outEnds := by
    rintro _ rfl D; exact le_outEnds D
  have := key _ apex_eq_cone D
  omega

omit [DecidableRel B.Adj] in
/-- The cone over at least two marks of a two-connected graph is two-connected. -/
theorem apex_kConnected_two (hB : KConnected 2 B) (hS : 2 ≤ S.card) :
    KConnected 2 (apex B S) := by
  refine kConnected_of_walks ?_ ?_
  · rw [Fintype.card_option]; have := hB.1; omega
  intro X hX a b ha hb
  by_cases hn : none ∈ X
  · have hX' : X.eraseNone.card < 2 := by rw [Finset.card_eraseNone_of_mem hn]; omega
    cases a with
    | none => exact absurd hn ha
    | some a =>
    cases b with
    | none => exact absurd hn hb
    | some b =>
    obtain ⟨p, hp⟩ := hB.walk hX' (by simpa [Finset.mem_eraseNone] using ha)
      (by simpa [Finset.mem_eraseNone] using hb)
    obtain ⟨q, hq⟩ := apex_walk_of_walk (S := S) p
    refine ⟨q, fun w hw => ?_⟩
    rw [hq, List.mem_map] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    simpa [Finset.mem_eraseNone] using hp w' hw'
  · have key : ∀ v, v ∉ X → ∃ q : (apex B S).Walk v none, ∀ w ∈ q.support, w ∉ X := by
      intro v hv
      cases v with
      | none => exact ⟨.nil, by simpa using hn⟩
      | some v =>
      have hv' : v ∉ X.eraseNone := by simpa [Finset.mem_eraseNone] using hv
      have hcard : X.eraseNone.card < 2 := by
        rw [Finset.card_eraseNone_of_notMem hn]; omega
      obtain ⟨t, htS, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := X.eraseNone) (t := S) (by omega)
      obtain ⟨p, hp⟩ := hB.walk hcard hv' ht
      obtain ⟨q, hq⟩ := apex_walk_of_walk (S := S) p
      refine ⟨q.concat (show (apex B S).Adj (some t) none from htS), fun w hw => ?_⟩
      rw [Walk.support_concat, List.mem_append, List.mem_singleton, hq, List.mem_map] at hw
      rcases hw with ⟨w', hw', rfl⟩ | rfl
      · simpa [Finset.mem_eraseNone] using hp w' hw'
      · exact hn
    obtain ⟨qa, hqa⟩ := key a ha
    obtain ⟨qb, hqb⟩ := key b hb
    refine ⟨qa.append qb.reverse, fun w hw => ?_⟩
    rw [Walk.support_append, List.mem_append] at hw
    rcases hw with hw | hw
    · exact hqa w hw
    · exact hqb w (by
        rw [← List.mem_reverse, ← Walk.support_reverse]; exact List.mem_of_mem_tail hw)

omit [Fintype V] [DecidableEq V] [DecidableRel B.Adj] in
/-- The cone over at least two marks of a graph without a matching cut has none. -/
theorem not_hasMatchingCut_apex (hB : ¬ HasMatchingCut B) (hS : 2 ≤ S.card) :
    ¬ HasMatchingCut (apex B S) := by
  rintro ⟨X, hXne, hXcne, hm⟩
  obtain ⟨s₁, hs₁, s₂, hs₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  have hside : (∀ v, some v ∈ X) ∨ (∀ v, some v ∉ X) := by
    by_contra hc
    rw [not_or] at hc
    push Not at hc
    obtain ⟨⟨v₁, hv₁⟩, ⟨v₂, hv₂⟩⟩ := hc
    apply hB
    refine ⟨{v | some v ∈ X}, ⟨v₂, hv₂⟩, ⟨v₁, hv₁⟩, fun a b c hab hac h1 h2 => ?_⟩
    exact Option.some_injective _ (hm (some a) (some b) (some c) hab hac h1 h2)
  have hsp₁ : (apex B S).Adj none (some s₁) := hs₁
  have hsp₂ : (apex B S).Adj none (some s₂) := hs₂
  rcases hside with hall | hall
  · have hn : none ∉ X := by
      obtain ⟨w, hw⟩ := hXcne
      cases w with
      | none => exact hw
      | some w => exact absurd (hall w) hw
    exact hne (Option.some_injective _
      (hm none (some s₁) (some s₂) hsp₁ hsp₂ (by simp [hn, hall]) (by simp [hn, hall])))
  · have hn : none ∈ X := by
      obtain ⟨w, hw⟩ := hXne
      cases w with
      | none => exact hw
      | some w => exact absurd hw (hall w)
    exact hne (Option.some_injective _
      (hm none (some s₁) (some s₂) hsp₁ hsp₂ (by simp [hn, hall]) (by simp [hn, hall])))

omit [DecidableRel B.Adj] in
theorem apex_inClassC (hC : InClassC B) (hS : 2 ≤ S.card) : InClassC (apex B S) :=
  ⟨apex_kConnected_two hC.1 hS, not_hasMatchingCut_apex hC.2 hS⟩

end apexC

/-- Both rooted assertions on every member of `C` of order at most `n`. -/
def RootedTestsUpTo (n : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (B : SimpleGraph W) [DecidableRel B.Adj],
    InClassC B → Fintype.card W ≤ n → ∀ x, RootedAt B x

section classC

variable {V : Type u} [Fintype V] [DecidableEq V] {B : SimpleGraph V} [DecidableRel B.Adj]
  {m : ℕ}

/-- **The cone step**: if `n − |S|` is odd and `|S| ≥ 2`, the rooted test at the apex of the cone
gives the marked bound. -/
theorem cone_step (hRT : RootedTestsUpTo.{u} (m + 1)) (hC : InClassC B)
    (hn : Fintype.card V ≤ m) {S : Finset V} (hS : 2 ≤ S.card)
    (hodd : Odd (Fintype.card V - S.card)) :
    markedNumber B S ≤ (Fintype.card V - S.card) / 2 := by
  have hJ := apex_inClassC (S := S) hC hS
  have hcard : Fintype.card (Option V) = Fintype.card V + 1 := Fintype.card_option
  have hR := hRT (Option V) (apex B S) hJ (by omega) none
  have hdeg : (apex B S).degree none = S.card := apex_degree_none
  have hSV : S.card ≤ Fintype.card V := Finset.card_le_univ S
  obtain ⟨j, hj⟩ := hodd
  rcases Nat.even_or_odd (Fintype.card V) with ⟨a, ha⟩ | ⟨a, ha⟩
  · obtain ⟨D, hD1, hD2⟩ := hR.2 (by rw [hcard]; exact ⟨a, by omega⟩)
      (by rw [hdeg]; exact ⟨a - j - 1, by omega⟩)
    have := apex_outEnds_bound D
    rw [hcard] at hD1
    omega
  · obtain ⟨D, hD1, hD2⟩ := hR.1 (by rw [hcard]; exact ⟨a + 1, by omega⟩)
      (by rw [hdeg]; exact ⟨a - j, by omega⟩)
    have := apex_outEnds_bound D
    rw [hcard] at hD1
    omega

/-- **A single mark.** -/
theorem singleton_step (hRT : RootedTestsUpTo.{u} (m + 1)) (hC : InClassC B)
    (hn : Fintype.card V ≤ m) (x : V) :
    markedNumber B {x} ≤ (Fintype.card V - 1) / 2 := by
  have h3 := hC.1.1
  rcases Nat.even_or_odd (Fintype.card V) with hev | hod
  · obtain ⟨a, ha⟩ := hev
    have hev : Even (Fintype.card V) := ⟨a, ha⟩
    by_cases hx : Even (B.degree x)
    · obtain ⟨D, hD1, hD2⟩ := (hRT V B hC (by omega) x).1 hev hx
      have := markedNumber_singleton_add_one D (x := x) (by omega)
      omega
    · obtain ⟨D, hD⟩ : ∃ D : PathDecomp B, D.size ≤ Fintype.card V / 2 := by
        by_cases hy : ∃ y, Even (B.degree y)
        · obtain ⟨y, hy⟩ := hy
          obtain ⟨D, hD1, -⟩ := (hRT V B hC (by omega) y).1 hev hy
          exact ⟨D, hD1⟩
        · push Not at hy
          have hL := lovaszStatement V B (by
            rw [Finset.card_le_one]
            intro a ha'
            exact absurd (Finset.mem_filter.mp ha').2 (Nat.not_even_iff_odd.mpr (hy a)))
          obtain ⟨D, hD⟩ := pathNumber_spec B
          exact ⟨D, hD ▸ hL⟩
      have hpar := D.ends_mod_two x
      rw [Nat.not_even_iff_odd, Nat.odd_iff] at hx
      have := markedNumber_singleton_add_one D (x := x) (by omega)
      omega
  · obtain ⟨a, ha⟩ := hod
    obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card (by omega) x
    have h2 : (insert y ({x} : Finset V)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using hy), Finset.card_singleton]
    have hc := cone_step hRT hC hn (S := insert y {x}) (by omega)
      (by rw [h2]; exact ⟨a - 1, by omega⟩)
    have := markedNumber_le_insert (F := B) {x} y
    rw [h2] at hc
    omega

/-- **Theorem 59, marked tests on `C`**: the rooted tests through order `n + 1` give the marked
bound on every member of `C` of order `n`, for every nonempty marking. -/
theorem markedBound_of_classC (hRT : RootedTestsUpTo.{u} (m + 1)) (hC : InClassC B)
    (hn : Fintype.card V ≤ m) (S : Finset V) (hS : S.Nonempty) :
    markedNumber B S ≤ (Fintype.card V - S.card) / 2 := by
  have hS1 : 1 ≤ S.card := Finset.card_pos.mpr hS
  have hSV : S.card ≤ Fintype.card V := Finset.card_le_univ S
  rcases Nat.lt_or_ge S.card 2 with hlt | hge
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (by omega : S.card = 1)
    rw [Finset.card_singleton]
    exact singleton_step hRT hC hn x
  by_cases hodd : Odd (Fintype.card V - S.card)
  · exact cone_step hRT hC hn hge hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨j, hj⟩ := hodd
  obtain ⟨s, hs⟩ := hS
  have hcard' : (S.erase s).card = S.card - 1 := Finset.card_erase_of_mem hs
  have hanti := markedNumber_anti (F := B) (Finset.erase_subset s S)
  rcases Nat.lt_or_ge (S.erase s).card 2 with hlt | hge'
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (by omega : (S.erase s).card = 1)
    have := singleton_step hRT hC hn x
    rw [hx] at hanti
    omega
  · have := cone_step hRT hC hn hge' (by rw [hcard']; exact ⟨j, by omega⟩)
    rw [hcard'] at this
    omega

/-- **Theorem 59, three ends on `C`**: test 2 directly. -/
theorem threeEnds_of_classC (hRT : RootedTestsUpTo.{u} (m + 1)) (hC : InClassC B)
    (hn : Fintype.card V ≤ m) (k : ℕ) (hk : Fintype.card V = 2 * k + 1)
    (hp : pathNumber B = k + 1) (x : V) (hx : Odd (B.degree x)) :
    ∃ D : PathDecomp B, D.size = k + 1 ∧ 3 ≤ D.ends x := by
  obtain ⟨D, hD1, hD2⟩ := (hRT V B hC (by omega) x).2 ⟨k, hk⟩ hx
  have := pathNumber_le D
  refine ⟨D, ?_, hD2⟩
  rw [hk] at hD1
  omega

end classC

end Gallai
