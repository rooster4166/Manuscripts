import GallaiLean.Thm59Lemma6
import GallaiLean.Thm59Leaves
import GallaiLean.Thm59ClassC

/-!
# Theorem 59, step [M]: graphs with a matching cut (Theorem 7)

Marked-reduction manuscript, Theorem 7 and Lemma 6 (pp. 12–13), together with the even-mark
reduction of §2.1.

**`matchingCut_markedBound`.** Let `B` be a connected graph of order `n` with a matching cut.
Assume the marked bound on every connected graph whose two-connected blocks have order `≤ n − 1`.
Then `q(B, S) ≤ ⌊(n − |S|)/2⌋` for every `S`. With `S = ∅` this says `p(B) ≤ ⌊n/2⌋`, so the
three-end test is vacuous on `B`.

Proof.
1. Choose a matching cut whose shores `X, Xᶜ` both induce connected graphs
   (`exists_connected_matchingCut`): a component of the complement of a component.
2. Split `S = A ∪ O` into even- and odd-degree marks. In `L_A(B) = leafGraph B A`, each shore
   carries its own private leaves. Every two-connected block of a shore lies inside the shore, so
   it has order at most `n − 1`. The hypothesis therefore gives the marked bound on each shore,
   with the crossing ends as marks. Lemma 6 then gives `p(L_A(B)) ≤ ⌊(n + |A|)/2⌋`.
3. Trim the leaves (`leafGraph_trim`). Every even mark whose leaf path was longer than the leaf
   edge gets an end, and hence two by parity. Every odd mark has an end by parity.
4. The assignment lemma (`markedNumber_add_card_le`) finishes:
   `q(B, A ∪ O) ≤ ⌊(n + a)/2⌋ − a − ⌈o/2⌉ ≤ ⌊(n − a − o)/2⌋`.
-/

open SimpleGraph

set_option linter.unusedSectionVars false

namespace Gallai

universe u

variable {V : Type u} [DecidableEq V] {B : SimpleGraph V}

/-! ### Matching cuts with connected shores -/

section shores

/-- The matching property of a vertex set. -/
def MatchingProp (B : SimpleGraph V) (Y : Set V) : Prop :=
  ∀ a b c, B.Adj a b → B.Adj a c → (a ∈ Y ↔ b ∉ Y) → (a ∈ Y ↔ c ∉ Y) → b = c

theorem MatchingProp.compl {Y : Set V} (h : MatchingProp B Y) : MatchingProp B Yᶜ := by
  intro a b c hab hac h1 h2
  apply h a b c hab hac
  · simp only [Set.mem_compl_iff] at h1; tauto
  · simp only [Set.mem_compl_iff] at h2; tauto

/-- A part closed inside `Y` inherits the matching property. -/
theorem MatchingProp.of_closed {Y C : Set V} (h : MatchingProp B Y) (hCY : C ⊆ Y)
    (hcl : ∀ a ∈ C, ∀ b ∈ Y, B.Adj a b → b ∈ C) : MatchingProp B C := by
  intro a b c hab hac h1 h2
  by_cases ha : a ∈ C
  · have hb : b ∉ C := h1.mp ha
    have hc : c ∉ C := h2.mp ha
    have hbY : b ∉ Y := fun hbY => hb (hcl a ha b hbY hab)
    have hcY : c ∉ Y := fun hcY => hc (hcl a ha c hcY hac)
    exact h a b c hab hac (iff_of_true (hCY ha) hbY) (iff_of_true (hCY ha) hcY)
  · have hb : b ∈ C := by by_contra hb; exact ha (h1.mpr hb)
    have hc : c ∈ C := by by_contra hc; exact ha (h2.mpr hc)
    have haY : a ∉ Y := fun haY => ha (hcl b hb a haY hab.symm)
    exact h a b c hab hac (iff_of_false haY (not_not.mpr (hCY hb)))
      (iff_of_false haY (not_not.mpr (hCY hc)))

/-- The vertices reachable from `y₀` inside `Y`. -/
def compIn (B : SimpleGraph V) (Y : Set V) (y₀ : V) : Set V :=
  {v | ∃ p : B.Walk y₀ v, ∀ w ∈ p.support, w ∈ Y}

theorem compIn_sub {Y : Set V} {y₀ : V} : compIn B Y y₀ ⊆ Y := by
  rintro v ⟨p, hp⟩; exact hp v p.end_mem_support

theorem mem_compIn_self {Y : Set V} {y₀ : V} (h : y₀ ∈ Y) : y₀ ∈ compIn B Y y₀ :=
  ⟨Walk.nil, by simpa using h⟩

theorem compIn_closed {Y : Set V} {y₀ : V} :
    ∀ a ∈ compIn B Y y₀, ∀ b ∈ Y, B.Adj a b → b ∈ compIn B Y y₀ := by
  rintro a ⟨p, hp⟩ b hb hab
  refine ⟨p.concat hab, fun w hw => ?_⟩
  rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · exact hp w hw
  · exact hb

/-- Every vertex of a walk from `y₀` inside `Y` is in the component. -/
theorem compIn_of_walk {Y : Set V} {y₀ v : V} (p : B.Walk y₀ v) (hp : ∀ w ∈ p.support, w ∈ Y) :
    ∀ w ∈ p.support, w ∈ compIn B Y y₀ := by
  intro w hw
  exact ⟨p.takeUntil w hw, fun x hx => hp x (p.support_takeUntil_subset_support hw hx)⟩

theorem compIn_walk {Y : Set V} {y₀ : V} {a b : V} (ha : a ∈ compIn B Y y₀)
    (hb : b ∈ compIn B Y y₀) : ∃ p : B.Walk a b, ∀ v ∈ p.support, v ∈ compIn B Y y₀ := by
  obtain ⟨pa, hpa⟩ := ha
  obtain ⟨pb, hpb⟩ := hb
  refine ⟨pa.reverse.append pb, fun v hv => ?_⟩
  rw [Walk.support_append, List.mem_append] at hv
  rcases hv with hv | hv
  · rw [Walk.support_reverse, List.mem_reverse] at hv
    exact compIn_of_walk pa hpa v hv
  · exact compIn_of_walk pb hpb v (List.mem_of_mem_tail hv)

/-- Walking towards a vertex of `C` while avoiding a part `D` closed outside `C`. -/
theorem walk_avoid {C D : Set V} {y₀ : V} (hy₀ : y₀ ∈ C)
    (hCwalk : ∀ v ∈ C, ∃ p : B.Walk v y₀, ∀ x ∈ p.support, x ∉ D)
    (hcl : ∀ a ∈ D, ∀ b ∈ Cᶜ, B.Adj a b → b ∈ D) :
    ∀ {v : V} (_ : B.Walk v y₀), v ∉ D → ∃ p : B.Walk v y₀, ∀ x ∈ p.support, x ∉ D
  | _, .nil, hv => ⟨Walk.nil, fun x hx => by rw [Walk.mem_support_nil_iff] at hx; subst hx; exact hv⟩
  | v, @Walk.cons _ _ _ u _ huv w, hv => by
    by_cases hvC : v ∈ C
    · exact hCwalk v hvC
    have huD : u ∉ D := fun huD => hv (hcl u huD v hvC huv.symm)
    obtain ⟨p, hp⟩ := walk_avoid hy₀ hCwalk hcl w huD
    refine ⟨Walk.cons huv p, fun x hx => ?_⟩
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hv
    · exact hp x hx

/-- **Matching cuts with connected shores.** A connected graph with a matching cut has one whose
two shores are connected. -/
theorem exists_connected_matchingCut [Fintype V] (hB : B.Connected) (h : HasMatchingCut B) :
    ∃ X : Finset V, X.Nonempty ∧ Xᶜ.Nonempty ∧
      (∀ a ∈ X, ∀ b ∈ X, ∃ p : B.Walk a b, ∀ v ∈ p.support, v ∈ X) ∧
      (∀ a ∈ Xᶜ, ∀ b ∈ Xᶜ, ∃ p : B.Walk a b, ∀ v ∈ p.support, v ∈ Xᶜ) ∧
      MatchingProp B (X : Set V) := by
  classical
  obtain ⟨Y, ⟨y₀, hy₀⟩, ⟨z₀, hz₀⟩, hM⟩ := h
  set C := compIn B Y y₀ with hC
  have hMC : MatchingProp B C := MatchingProp.of_closed hM compIn_sub compIn_closed
  have hz₀C : z₀ ∈ Cᶜ := fun h' => hz₀ (compIn_sub h')
  set D := compIn B Cᶜ z₀ with hD
  have hMD : MatchingProp B D := MatchingProp.of_closed hMC.compl compIn_sub compIn_closed
  have hy₀C : y₀ ∈ C := mem_compIn_self hy₀
  -- the complement of `D` is connected through `y₀`
  have hreach : ∀ v (w : B.Walk v y₀), v ∉ D → ∃ p : B.Walk v y₀, ∀ x ∈ p.support, x ∉ D :=
    fun v w hv => walk_avoid hy₀C
      (fun c hc => by obtain ⟨p, hp⟩ := compIn_walk hc hy₀C
                      exact ⟨p, fun x hx hxD => compIn_sub hxD (hp x hx)⟩)
      (fun a ha b hb hab => compIn_closed a ha b hb hab) w hv
  refine ⟨Finset.univ.filter (· ∈ D), ⟨z₀, by simpa using mem_compIn_self hz₀C⟩,
    ⟨y₀, by simpa using fun h' => absurd hy₀C (compIn_sub h')⟩, ?_, ?_, ?_⟩
  · intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    obtain ⟨p, hp⟩ := compIn_walk ha hb
    exact ⟨p, fun v hv => by simpa using hp v hv⟩
  · intro a ha b hb
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    obtain ⟨pa, hpa⟩ := hreach a (hB.preconnected a y₀).some ha
    obtain ⟨pb, hpb⟩ := hreach b (hB.preconnected b y₀).some hb
    refine ⟨pa.append pb.reverse, fun v hv => ?_⟩
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Walk.support_append, List.mem_append] at hv
    rcases hv with hv | hv
    · exact hpa v hv
    · rw [Walk.support_reverse] at hv
      exact hpb v (List.mem_reverse.mp (List.mem_of_mem_tail hv))
  · intro a b c hab hac h1 h2
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.ofPred_mem_eq] at h1 h2
    exact hMD a b c hab hac h1 h2

/-- A walk from inside `X` to outside crosses. -/
theorem exists_cross_of_walk {X : Finset V} :
    ∀ {a b : V} (_ : B.Walk a b), a ∈ X → b ∉ X → ∃ x ∈ X, ∃ y, y ∉ X ∧ B.Adj x y
  | _, _, .nil, ha, hb => absurd ha hb
  | a, _, @Walk.cons _ _ _ c _ h p, ha, hb => by
    by_cases hc : c ∈ X
    · exact exists_cross_of_walk p hc hb
    · exact ⟨a, ha, c, hc, h⟩

end shores

/-! ### The private-leaf graph across a matching cut -/

section leafCut

variable {A : Finset V}

/-- The leaf graph as a graph homomorphism target. -/
def leafInl (B : SimpleGraph V) (A : Finset V) : B →g leafGraph B A := ⟨Sum.inl, fun h => h⟩

/-- A walk inside `U` is a walk of the induced instance on `U`. -/
theorem reach_onSub_restrict {W : Type*} [DecidableEq W] {H : SimpleGraph W} {U : Finset W} :
    ∀ {a b : W} (p : H.Walk a b) (hp : ∀ v ∈ p.support, v ∈ U),
      (onSub (restrict H U) U).Reachable ⟨a, hp a p.start_mem_support⟩
        ⟨b, hp b p.end_mem_support⟩
  | _, _, .nil, _ => Reachable.refl _
  | _, _, @Walk.cons _ _ a c _ h p, hp => by
    have hp' : ∀ v ∈ p.support, v ∈ U := fun v hv => hp v (by simp [hv])
    have hadj : (onSub (restrict H U) U).Adj ⟨a, hp a (by simp)⟩ ⟨c, hp' c p.start_mem_support⟩ :=
      ⟨h, hp a (by simp), hp' c p.start_mem_support⟩
    exact hadj.reachable.trans (reach_onSub_restrict p hp')

/-- A shore together with its private leaves. -/
def shoreSet (Y A : Finset V) : Finset (V ⊕ V) := Y.disjSum (A.filter (· ∈ Y))

@[simp] theorem inl_mem_shoreSet {Y : Finset V} {v : V} : Sum.inl v ∈ shoreSet Y A ↔ v ∈ Y := by
  simp [shoreSet]

@[simp] theorem inr_mem_shoreSet {Y : Finset V} {v : V} :
    Sum.inr v ∈ shoreSet Y A ↔ v ∈ A ∧ v ∈ Y := by
  simp [shoreSet]

theorem card_shoreSet (Y A : Finset V) :
    (shoreSet Y A).card = Y.card + (A.filter (· ∈ Y)).card := Finset.card_disjSum _ _

/-- A connected shore with its leaves is connected. -/
theorem shore_connected {Y : Finset V} (hYne : Y.Nonempty)
    (hYc : ∀ a ∈ Y, ∀ b ∈ Y, ∃ p : B.Walk a b, ∀ v ∈ p.support, v ∈ Y) :
    (onSub (restrict (leafGraph B A) (shoreSet Y A)) (shoreSet Y A)).Connected := by
  obtain ⟨y₀, hy₀⟩ := hYne
  have hy₀' : Sum.inl y₀ ∈ shoreSet Y A := by simpa using hy₀
  have hreach : ∀ z : {x // x ∈ shoreSet Y A},
      (onSub (restrict (leafGraph B A) (shoreSet Y A)) (shoreSet Y A)).Reachable ⟨_, hy₀'⟩ z := by
    have hinl : ∀ v (hv : v ∈ Y),
        (onSub (restrict (leafGraph B A) (shoreSet Y A)) (shoreSet Y A)).Reachable ⟨_, hy₀'⟩
          ⟨Sum.inl v, by simpa using hv⟩ := by
      intro v hv
      obtain ⟨p, hp⟩ := hYc y₀ hy₀ v hv
      have hp' : ∀ w ∈ (p.map (leafInl B A)).support, w ∈ shoreSet Y A := by
        intro w hw
        rw [Walk.support_map, List.mem_map] at hw
        obtain ⟨w', hw', rfl⟩ := hw
        show Sum.inl w' ∈ shoreSet Y A
        simpa using hp w' hw'
      exact reach_onSub_restrict (p.map (leafInl B A)) hp'
    rintro ⟨z, hz⟩
    cases z with
    | inl v => exact hinl v (by simpa using hz)
    | inr v =>
      have hv : v ∈ A ∧ v ∈ Y := by simpa using hz
      refine (hinl v hv.2).trans (Adj.reachable ?_)
      exact ⟨⟨rfl, hv.1⟩, by simpa using hv.2, hz⟩
  have : Nonempty {x // x ∈ shoreSet Y A} := ⟨⟨_, hy₀'⟩⟩
  exact ⟨fun a b => (hreach a).symm.trans (hreach b)⟩

/-- A two-connected graph has no vertex with at most one neighbour. -/
theorem KConnected.not_pendant {W : Type*} [Fintype W] {G : SimpleGraph W} (h : KConnected 2 G)
    (v : W) (hv : ∀ x y, G.Adj v x → G.Adj v y → x = y) : False := by
  classical
  have h2 := h.le_degree v
  have h1 : G.degree v ≤ 1 := by
    rw [← card_neighborFinset_eq_degree]
    exact Finset.card_le_one.mpr (fun x hx y hy =>
      hv x y ((mem_neighborFinset _ _ _).mp hx) ((mem_neighborFinset _ _ _).mp hy))
  omega

/-- The two-connected blocks of a shore with leaves lie inside the shore. -/
theorem shore_smallBlocks [Fintype V] {Y : Finset V} :
    SmallBlocks (onSub (restrict (leafGraph B A) (shoreSet Y A)) (shoreSet Y A)) Y.card := by
  intro S' hS'
  have hinl : ∀ s ∈ S', ∃ v ∈ Y, s.1 = Sum.inl v := by
    intro s hs
    obtain ⟨z, hz⟩ := s
    cases z with
    | inl v => exact ⟨v, by simpa using hz, rfl⟩
    | inr a =>
      exfalso
      apply hS'.not_pendant ⟨⟨Sum.inr a, hz⟩, hs⟩
      intro x y hx hy
      have key : ∀ w : (S' : Set {x // x ∈ shoreSet Y A}),
          ((onSub (restrict (leafGraph B A) (shoreSet Y A)) (shoreSet Y A)).induce
            (S' : Set _)).Adj ⟨⟨Sum.inr a, hz⟩, hs⟩ w → w.1.1 = Sum.inl a := by
        rintro ⟨⟨w, hw⟩, hw'⟩ hadj
        have h' : (leafGraph B A).Adj (Sum.inr a) w := hadj.1
        cases w with
        | inr w => exact absurd h' leafGraph_not_adj_inr_inr
        | inl w => exact congrArg Sum.inl h'.1.symm
      exact Subtype.ext (Subtype.ext ((key x hx).trans (key y hy).symm))
  calc S'.card ≤ Y.card := by
        refine Finset.card_le_card_of_injOn (fun s => unSum s.1) (fun s hs => ?_) ?_
        · obtain ⟨v, hv, h'⟩ := hinl s hs
          simp [h', unSum, hv]
        · intro s hs t ht hst
          obtain ⟨v, -, hv⟩ := hinl s hs
          obtain ⟨w, -, hw⟩ := hinl t ht
          simp only [hv, hw, unSum, Sum.elim_inl, id] at hst
          exact Subtype.ext (hv.trans (hst ▸ hw.symm))

/-- **Local bounds** from the marked bound on graphs with small blocks. -/
theorem local_pmp [Fintype V] {m : ℕ} (hMB : MarkedBoundUpTo.{u} m) {U T : Finset (V ⊕ V)}
    {H : SimpleGraph (V ⊕ V)} (hTU : T ⊆ U) (hT : T.Nonempty)
    (hconn : (onSub (restrict H U) U).Connected)
    (hsmall : SmallBlocks (onSub (restrict H U) U) m) :
    ∃ M : PMP H (restrict H U).edgeSet T, M.cost ≤ (U.card - T.card) / 2 := by
  have hT' : (T.subtype (· ∈ U)).Nonempty := by
    obtain ⟨t, ht⟩ := hT
    exact ⟨⟨t, hTU ht⟩, Finset.mem_subtype.mpr ht⟩
  have hq := hMB {x // x ∈ U} (onSub (restrict H U) U) hconn hsmall _ hT'
  rw [card_sub, card_subtype_of_subset hTU] at hq
  have h1 := markedNumber_le_onSub (edgesIn_restrict (G := H) U) T
  obtain ⟨M, hM⟩ := exists_pmp_le (G := H) (restrict H U) (restrict_le U) T
  exact ⟨M, by omega⟩

end leafCut

/-! ### The matching-cut step -/

/-- **Theorem 7, matching-cut case** (with Lemma 6 and §2.1): a connected graph with a matching
cut satisfies the marked bound for every marking, given the marked bound on all connected graphs
whose two-connected blocks are smaller. -/
theorem matchingCut_markedBound [Fintype V] (hB : B.Connected) (hMC : HasMatchingCut B)
    (hMB : MarkedBoundUpTo.{u} (Fintype.card V - 1)) (S : Finset V) :
    markedNumber B S ≤ (Fintype.card V - S.card) / 2 := by
  classical
  obtain ⟨X, hXne, hXcne, hXc, hXcc, hM⟩ := exists_connected_matchingCut hB hMC
  set n := Fintype.card V with hn
  have hXn : X.card + Xᶜ.card = n := Finset.card_add_card_compl X
  have hX1 : 0 < Xᶜ.card := Finset.card_pos.mpr hXcne
  have hX2 : 0 < X.card := Finset.card_pos.mpr hXne
  set A := S.filter (fun v => Even (B.degree v)) with hA
  set O := S.filter (fun v => ¬ Even (B.degree v)) with hO
  set H := leafGraph B A with hH
  set U₁ := shoreSet X A with hU₁
  set U₂ := shoreSet Xᶜ A with hU₂
  -- crossing data
  let partner : V → V := fun a => if h : ∃ b, b ∉ X ∧ B.Adj a b then h.choose else a
  have hpartner : ∀ a, (∃ b, b ∉ X ∧ B.Adj a b) → partner a ∉ X ∧ B.Adj a (partner a) := by
    intro a h
    simp only [partner, h, dite_true]
    exact h.choose_spec
  set E₁ := X.filter (fun a => ∃ b, b ∉ X ∧ B.Adj a b) with hE₁
  set A₁ := E₁.map ⟨Sum.inl, Sum.inl_injective⟩ with hA₁
  let φ : V ⊕ V → V ⊕ V := Sum.elim (fun a => Sum.inl (partner a)) Sum.inr
  have hd : CrossData H U₁ U₂ A₁ φ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro z h1 h2
      cases z with
      | inl v => simp [hU₁, hU₂] at h1 h2; exact h2 h1
      | inr v => simp [hU₁, hU₂] at h1 h2; exact h2.2 h1.2
    · intro x y hxy
      cases x with
      | inl u =>
        cases y with
        | inl v =>
          refine ⟨?_, ?_⟩ <;> rw [Finset.mem_union] <;>
            first
            | (by_cases h : u ∈ X
               · exact Or.inl (by simpa [hU₁] using h)
               · exact Or.inr (by simpa [hU₂] using h))
            | (by_cases h : v ∈ X
               · exact Or.inl (by simpa [hU₁] using h)
               · exact Or.inr (by simpa [hU₂] using h))
        | inr v =>
          obtain ⟨rfl, hvA⟩ := (show u = v ∧ v ∈ A from hxy)
          by_cases h : u ∈ X
          · exact ⟨Finset.mem_union_left _ (by simpa [hU₁] using h),
              Finset.mem_union_left _ (by simpa [hU₁] using ⟨hvA, h⟩)⟩
          · exact ⟨Finset.mem_union_right _ (by simpa [hU₂] using h),
              Finset.mem_union_right _ (by simpa [hU₂] using ⟨hvA, h⟩)⟩
      | inr u =>
        cases y with
        | inr v => exact absurd hxy leafGraph_not_adj_inr_inr
        | inl v =>
          obtain ⟨rfl, huA⟩ := (show u = v ∧ u ∈ A from hxy)
          by_cases h : u ∈ X
          · exact ⟨Finset.mem_union_left _ (by simpa [hU₁] using ⟨huA, h⟩),
              Finset.mem_union_left _ (by simpa [hU₁] using h)⟩
          · exact ⟨Finset.mem_union_right _ (by simpa [hU₂] using ⟨huA, h⟩),
              Finset.mem_union_right _ (by simpa [hU₂] using h)⟩
    · intro z hz
      rw [hA₁, Finset.mem_map] at hz
      obtain ⟨a, ha, rfl⟩ := hz
      rw [hE₁, Finset.mem_filter] at ha
      simpa [hU₁] using ha.1
    · intro z hz
      rw [hA₁, Finset.mem_map] at hz
      obtain ⟨a, ha, rfl⟩ := hz
      rw [hE₁, Finset.mem_filter] at ha
      simpa [hU₂, φ] using (hpartner a ha.2).1
    · intro z hz z' hz' hzz
      rw [Finset.coe_map, Set.mem_image] at hz hz'
      obtain ⟨a, ha, rfl⟩ := hz
      obtain ⟨a', ha', rfl⟩ := hz'
      rw [Finset.mem_coe, hE₁, Finset.mem_filter] at ha ha'
      have hpp : partner a = partner a' := by
        simpa [φ] using hzz
      obtain ⟨hp1, hp2⟩ := hpartner a ha.2
      obtain ⟨hp1', hp2'⟩ := hpartner a' ha'.2
      rw [← hpp] at hp2'
      have := hM (partner a) a a' hp2.symm hp2'.symm
        (iff_of_false (by simpa using hp1) (by simpa using ha.1))
        (iff_of_false (by simpa using hp1) (by simpa using ha'.1))
      simp [this]
    · intro z hz
      rw [hA₁, Finset.mem_map] at hz
      obtain ⟨a, ha, rfl⟩ := hz
      rw [hE₁, Finset.mem_filter] at ha
      exact (hpartner a ha.2).2
    · intro x hx y hy hxy
      cases x with
      | inr a =>
        have ha : a ∈ A ∧ a ∈ X := by simpa [hU₁] using hx
        cases y with
        | inr b => exact absurd hxy leafGraph_not_adj_inr_inr
        | inl b =>
          obtain ⟨rfl, -⟩ := (show a = b ∧ a ∈ A from hxy)
          have : a ∉ X := by simpa [hU₂] using hy
          exact absurd ha.2 this
      | inl a =>
        have ha : a ∈ X := by simpa [hU₁] using hx
        cases y with
        | inr b =>
          obtain ⟨rfl, -⟩ := (show a = b ∧ b ∈ A from hxy)
          have : a ∈ A ∧ a ∉ X := by simpa [hU₂] using hy
          exact absurd ha this.2
        | inl b =>
          have hb : b ∉ X := by simpa [hU₂] using hy
          have hadj : B.Adj a b := hxy
          have hex : ∃ b, b ∉ X ∧ B.Adj a b := ⟨b, hb, hadj⟩
          refine ⟨?_, ?_⟩
          · rw [hA₁, Finset.mem_map]
            exact ⟨a, by rw [hE₁, Finset.mem_filter]; exact ⟨ha, hex⟩, rfl⟩
          · obtain ⟨hp1, hp2⟩ := hpartner a hex
            have := hM a b (partner a) hadj hp2 (iff_of_true (by simpa using ha) (by simpa using hb))
              (iff_of_true (by simpa using ha) (by simpa using hp1))
            simp [φ, this]
  -- local bounds
  have hA₁ne : A₁.Nonempty := by
    obtain ⟨x, hx⟩ := hXne
    obtain ⟨y, hy⟩ := hXcne
    obtain ⟨a, ha, b, hb, hab⟩ := exists_cross_of_walk (X := X) (hB.preconnected x y).some hx
      (by simpa using hy)
    exact ⟨Sum.inl a, by rw [hA₁, Finset.mem_map]; exact ⟨a, by
      rw [hE₁, Finset.mem_filter]; exact ⟨ha, b, hb, hab⟩, rfl⟩⟩
  have hsm₁ : SmallBlocks (onSub (restrict H U₁) U₁) (n - 1) := fun S' hS' =>
    (shore_smallBlocks S' hS').trans (by omega)
  have hsm₂ : SmallBlocks (onSub (restrict H U₂) U₂) (n - 1) := fun S' hS' =>
    (shore_smallBlocks S' hS').trans (by omega)
  obtain ⟨M₁, hM₁⟩ := local_pmp hMB hd.sub hA₁ne (shore_connected hXne hXc) hsm₁
  have hA₂sub : A₁.image φ ⊆ U₂ := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    exact hd.maps a ha
  obtain ⟨M₂, hM₂⟩ := local_pmp hMB hA₂sub (hA₁ne.image _) (shore_connected hXcne hXcc) hsm₂
  obtain ⟨D, hD⟩ := lemma6 hd M₁ M₂
  have hA₂card : (A₁.image φ).card = A₁.card := Finset.card_image_of_injOn hd.inj
  have hA₁U : A₁.card ≤ U₁.card := Finset.card_le_card hd.sub
  have hA₂U : (A₁.image φ).card ≤ U₂.card := Finset.card_le_card hA₂sub
  have hU₁c := card_shoreSet X A
  have hU₂c := card_shoreSet Xᶜ A
  have hAsplit : (A.filter (· ∈ X)).card + (A.filter (· ∈ Xᶜ)).card = A.card := by
    have := Finset.card_filter_add_card_filter_not (s := A) (fun v => v ∈ X)
    simpa [Finset.mem_compl] using this
  rw [← hU₁] at hU₁c
  rw [← hU₂] at hU₂c
  have hDsize : D.size ≤ (n + A.card) / 2 := by omega
  -- trimming
  obtain ⟨D', hD'⟩ := leafGraph_trim (B := B) (A := A) D
  set Z := A.filter (fun a => D'.ends a = 0) with hZ
  -- assignment
  set T := (A.filter (fun a => D'.ends a ≠ 0)) ∪ O with hT
  have hT1 : ∀ v ∈ T, 1 ≤ D'.ends v := by
    intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · rw [Finset.mem_filter] at h; omega
    · rw [hO, Finset.mem_filter, Nat.not_even_iff_odd, Nat.odd_iff] at h
      have := D'.ends_mod_two v
      omega
  have hT2 : ∀ v ∈ T, v ∉ O → 2 ≤ D'.ends v := by
    intro v hv hvO
    rcases Finset.mem_union.mp hv with h | h
    · rw [Finset.mem_filter, hA, Finset.mem_filter, Nat.even_iff] at h
      have := D'.ends_mod_two v
      omega
    · exact absurd h hvO
  have hHall := markedNumber_add_card_le D' T O hT1 hT2
  have hTS : T ⊆ S := by
    intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1
    · exact (Finset.mem_filter.mp h).1
  have hanti := markedNumber_anti (F := B) hTS
  have hAO : A.card + O.card = S.card := Finset.card_filter_add_card_filter_not _
  have hTcard : T.card = (A.filter (fun a => D'.ends a ≠ 0)).card + O.card := by
    rw [hT, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro v h1 h2
    rw [Finset.mem_filter, hA, Finset.mem_filter] at h1
    rw [hO, Finset.mem_filter] at h2
    exact h2.2 h1.1.2
  have hAZ : (A.filter (fun a => D'.ends a ≠ 0)).card + Z.card = A.card := by
    have := Finset.card_filter_add_card_filter_not (s := A) (fun a => D'.ends a ≠ 0)
    simpa [hZ] using this
  have hSn : S.card ≤ n := Finset.card_le_univ S
  omega

end Gallai
