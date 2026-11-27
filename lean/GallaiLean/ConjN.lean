import GallaiLean.DLOne
import GallaiLean.L1Induction

/-!
# Conjecture N: a reduction to the tight transfer and the degree-two case

Manuscript `manuscripts/conj-n`, Section 4.

**Conjecture N** (`ConjNOn`). Let `G` have at most one vertex of positive even degree, let `x, y`
be odd and non-adjacent, and let `y` have a neighbour `w` that is not even and not adjacent to `x`.
Then some Lovász decomposition of `G` has the path ending at `y` avoiding `x`.

**Theorem** (`conjN_of_tight_degTwo`). Conjecture N follows from
* `TightTransferNOn`: the tight transfer conjecture TR of l1-induction for one forbidden vertex,
  with the tail allowed to be adjacent to the even vertex; and
* `ConjNDegTwoOn`: Conjecture N in the case `N(g) = {x, y}`.

The degree-two case is equivalent to an all-odd statement (`conjNDegTwo_of_neighbourAvoid`):
`NeighbourAvoidOn`, the path ending at `y` can avoid a *neighbour* `x` when `y` has a neighbour
not adjacent to `x`. It holds when `x, y` have no common neighbour other than `g`
(`avoid_deg_two`).

Proof of the theorem: induction on the number of edges.
* No even vertex: `lovasz_avoid_nonadj` (L₁).
* A target `u ∈ N(g)` with `u ∉ {x, y}`, `u ≁ y`: Lovász's Case I (`avoid_free_target`); the child
  `G − gu` is again an instance of N, the old witness surviving because `u ∉ N(y)`.
* A tight target `u ∈ N(g) ∩ N(y)`, `u ≠ x`, whose child still has a witness: `TightTransferNOn`.
* Otherwise the witness is unique and equals every tight target, and the parity of `d(g)` leaves
  `N(g) = {x, u}` with `x ≁ u` (split `g` off and apply L₁, `avoid_of_splitOff`) or `N(g) = {x, y}`.
-/

open SimpleGraph

namespace Gallai

universe u

section splitOff

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {g a b : V}

/-- **Splitting off a vertex of degree two (move (e))**. Let `N(g) = {a, b}` with `ab ∉ E`, and let
`H = G − ga − gb + ab`. A Lovász decomposition of `H` whose path ending at `c ≠ g` avoids `A ∌ g`
gives one of `G` with the same property: subdivide `ab` by `g`. -/
theorem avoid_of_splitOff (hg : g ∈ evenSet G) (hNg : ∀ v, G.Adj g v ↔ v = a ∨ v = b)
    (hab : a ≠ b) (hnadj : ¬ G.Adj a b) {c : V} (hcg : c ≠ g) {A : Finset V} (hgA : g ∉ A)
    (hH : AvoidDecomp (plusEdge (delEdge (delEdge G g a) g b) a b) c A) : AvoidDecomp G c A := by
  classical
  obtain ⟨hHw, hHg, hHab, -, hval⟩ := splitOff_facts hNg hab hnadj
  set H := plusEdge (delEdge (delEdge G g a) g b) a b with hHdef
  obtain ⟨DH, hDH, hav⟩ := hH
  have hga : G.Adj g a := (hNg a).mpr (Or.inl rfl)
  have hgb : G.Adj g b := (hNg b).mpr (Or.inr rfl)
  have hgA' : g ≠ a := hga.ne
  have hgB' : g ≠ b := hgb.ne
  -- the path of `DH` through `ab`, and its subdivision by `g`
  obtain ⟨R, hR, habR⟩ : ∃ R ∈ DH.paths, s(a, b) ∈ R.edges :=
    List.mem_flatMap.mp ((DH.covers _).mp hHab)
  have hgR : g ∉ R.walk.support := fun h => by
    have := GPath.degree_pos_of_mem R h; omega
  have haR : a ∈ R.walk.support := Walk.fst_mem_support_of_mem_edges _ habR
  have hbR : b ∈ R.walk.support := Walk.snd_mem_support_of_mem_edges _ habR
  let T : TPath V := ⟨a, b, Walk.cons (show (⊤ : SimpleGraph V).Adj a g from by simpa using Ne.symm hgA')
      (Walk.cons (show (⊤ : SimpleGraph V).Adj g b from by simpa using hgB') Walk.nil),
    by
      rw [Walk.isPath_def]
      simp [Ne.symm hgA', hab, hgB'],
    by simp⟩
  have hTe : T.edges = [s(a, g), s(g, b)] := rfl
  obtain ⟨R', hR's, hR't, hR'e, hR'supp⟩ := exists_subst_path R.toTop T (by simpa using habR)
    rfl rfl (by
      intro w hw hwR
      simp only [T, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact Or.inl rfl
      · rw [GPath.toTop_support] at hwR
        exact absurd hwR hgR
      · exact Or.inr rfl)
  set rest := DH.paths.erase R with hrest
  have hperm : DH.paths.Perm (R :: rest) := List.perm_cons_erase hR
  let L' : List (TPath V) := R' :: rest.map GPath.toTop
  have hEL : edgesM L' = G.edgeFinset.val := by
    have h1 : edgesM L' + {s(a, b)} = H.edgeFinset.val + T.edges := by
      rw [← DH.edgesM_toTop, edgesM_perm (hperm.map GPath.toTop)]
      simp only [L', edgesM_cons, List.map_cons]
      rw [add_right_comm, hR'e]
      simp only [GPath.toTop_edges]
      abel
    have h2 : (T.edges : Multiset (Sym2 V)) = {s(g, a)} + {s(g, b)} := by
      rw [hTe, Sym2.eq_swap (a := a)]
      rfl
    rw [h2, ← hval] at h1
    exact add_right_cancel h1
  have hendL : ∀ v, endsL L' v = DH.ends v := by
    intro v
    rw [← DH.endsL_toTop, endsL_perm (hperm.map GPath.toTop)]
    simp only [L', endsL_cons, List.map_cons, GPath.toTop_endsAt]
    unfold GPath.endsAt
    rw [hR's, hR't]
    rfl
  obtain ⟨D, hDe, hDp⟩ := exists_decomp_of_edgesM' (G := G) L' hEL
  refine ⟨D, fun v => ?_, fun Q hQ hQc => ?_⟩
  · rw [hDe v, hendL v, hDH v]
    by_cases hvg : v = g
    · subst hvg
      rw [hHg]
      obtain ⟨k, hk⟩ := (mem_evenSet_iff_even.mp hg).2
      omega
    · rw [hHw v hvg]
  · obtain ⟨T', hT', hTs, hTt, hTsupp⟩ := hDp Q hQ
    simp only [L', List.mem_cons, List.mem_map] at hT'
    rcases hT' with rfl | ⟨R₀, hR₀, rfl⟩
    · -- `Q` is the subdivided path: it has the ends of `R`, and its vertices are those of `R`
      -- together with `g`
      have hRc : R.src = c ∨ R.tgt = c := by
        rcases hQc with h | h
        · left; rw [← h, hTs, hR's]; rfl
        · right; rw [← h, hTt, hR't]; rfl
      intro x hx hxQ
      rw [hTsupp] at hxQ
      rcases hR'supp x hxQ with h | h
      · rw [GPath.toTop_support] at h
        exact hav R hR hRc x hx h
      · simp only [T, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
          or_false] at h
        rcases h with rfl | rfl | rfl
        · exact hav R hR hRc _ hx haR
        · exact hgA hx
        · exact hav R hR hRc _ hx hbR
    · rw [hTsupp, GPath.toTop_support]
      have hs : Q.src = R₀.src := hTs
      have ht : Q.tgt = R₀.tgt := hTt
      exact hav R₀ (List.mem_of_mem_erase hR₀) (by rw [← hs, ← ht]; exact hQc)

end splitOff

section conjN

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Conjecture N** on graphs with vertex type `V`: `x, y` odd and non-adjacent, `y` has a
neighbour `w` that is not even and not adjacent to `x`; then `Q(y)` can avoid `x`. -/
def ConjNOn (V : Type u) [Fintype V] [DecidableEq V] : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj], (evenSet G).card ≤ 1 →
    ∀ x y : V, G.degree x % 2 = 1 → G.degree y % 2 = 1 → x ≠ y → ¬ G.Adj x y →
    (∃ w, G.Adj y w ∧ w ∉ evenSet G ∧ ¬ G.Adj x w) → AvoidDecomp G y {x}

/-- **TRN**, the tight transfer for one forbidden vertex (l1-induction Conjecture 4.1 with
`A = {x}`), with the tail `y` allowed to be adjacent to the even vertex `g`: for a target
`u ∈ N(g) ∩ N(y)`, `u ≠ x`, goodness of `(G − gu, y, {x})` implies goodness of `(G, y, {x})`. -/
def TightTransferNOn (V : Type u) [Fintype V] [DecidableEq V] : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj], (evenSet G).card ≤ 1 → ∀ g ∈ evenSet G,
    ∀ x y u : V, G.degree x % 2 = 1 → G.degree y % 2 = 1 → x ≠ y → ¬ G.Adj x y →
    G.Adj g u → G.Adj y u → u ≠ x →
    AvoidDecomp (delEdge G g u) y {x} → AvoidDecomp G y {x}

/-- Conjecture N in the **degree-two case** `N(g) = {x, y}`. -/
def ConjNDegTwoOn (V : Type u) [Fintype V] [DecidableEq V] : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj], (evenSet G).card ≤ 1 → ∀ g ∈ evenSet G,
    ∀ x y : V, (∀ v, G.Adj g v ↔ v = x ∨ v = y) →
    G.degree x % 2 = 1 → G.degree y % 2 = 1 → x ≠ y → ¬ G.Adj x y →
    (∃ w, G.Adj y w ∧ w ≠ g ∧ ¬ G.Adj x w) → AvoidDecomp G y {x}

/-- **NA**, neighbour avoidance in graphs with no even vertex: if `x ~ y` and `y` has a neighbour
`w ≠ x` not adjacent to `x`, then `Q(y)` can avoid `x`. -/
def NeighbourAvoidOn (V : Type u) [Fintype V] [DecidableEq V] : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj], (evenSet G).card = 0 →
    ∀ x y : V, G.degree y % 2 = 1 → G.Adj x y →
    (∃ w, G.Adj y w ∧ w ≠ x ∧ ¬ G.Adj x w) → AvoidDecomp G y {x}

omit [Fintype V] in
theorem avoidDecomp_singleton_iff {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] {c x : V} :
    AvoidDecomp G c {x} ↔ ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∀ P ∈ D.paths, (P.src = c ∨ P.tgt = c) → x ∉ P.walk.support := by
  constructor
  · rintro ⟨D, hD, h⟩
    exact ⟨D, hD, fun P hP hend => h P hP hend x (Finset.mem_singleton_self x)⟩
  · rintro ⟨D, hD, h⟩
    exact ⟨D, hD, fun P hP hend a ha => (Finset.mem_singleton.mp ha) ▸ h P hP hend⟩

/-- In `G − gu`, with `g` the only even vertex of `G`, only `u` can be even. -/
theorem evenSet_delEdge_sub {G : SimpleGraph V} [DecidableRel G.Adj] {g u : V}
    (hev : (evenSet G).card ≤ 1) (hg : g ∈ evenSet G) (hgu : G.Adj g u) :
    ∀ v ∈ evenSet (delEdge G g u), v = u := by
  intro v hv
  have huniq : ∀ w ∈ evenSet G, w = g := fun w hw => Finset.card_le_one.mp hev w hw g hg
  obtain ⟨hpos, hevn⟩ := mem_evenSet_iff.mp hv
  have hd := delEdge_degree G hgu v
  by_contra hvu
  by_cases hvg : v = g
  · subst hvg
    simp only [ite_true, ite_false, add_zero, hvu] at hd
    have := (mem_evenSet_iff.mp hg).2
    omega
  · simp only [hvg, hvu, ite_false, add_zero] at hd
    exact hvg (huniq v (mem_evenSet_iff.mpr ⟨hd ▸ hpos, hd ▸ hevn⟩))

theorem evenSet_delEdge_card {G : SimpleGraph V} [DecidableRel G.Adj] {g u : V}
    (hev : (evenSet G).card ≤ 1) (hg : g ∈ evenSet G) (hgu : G.Adj g u) :
    (evenSet (delEdge G g u)).card ≤ 1 :=
  Finset.card_le_one.mpr fun a ha b hb =>
    (evenSet_delEdge_sub hev hg hgu a ha).trans (evenSet_delEdge_sub hev hg hgu b hb).symm

omit [Fintype V] [DecidableEq V] in
theorem delEdge_adj_of_ne {G : SimpleGraph V} {g u p q : V} (h : G.Adj p q) (hp : p ≠ g)
    (hpu : p ≠ u) : (delEdge G g u).Adj p q := by
  refine ⟨h, fun he => ?_⟩
  rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hp h1
  · exact hpu h1

/-- The induction behind `conjN_of_tight_degTwo`, on the degree sum. -/
theorem conjN_strong (hT : TightTransferNOn V) (hR : ConjNDegTwoOn V) (n : ℕ) :
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj], (∑ w, G.degree w) = n → (evenSet G).card ≤ 1 →
    ∀ x y : V, G.degree x % 2 = 1 → G.degree y % 2 = 1 → x ≠ y → ¬ G.Adj x y →
    (∃ w, G.Adj y w ∧ w ∉ evenSet G ∧ ¬ G.Adj x w) → AvoidDecomp G y {x} := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ hn hev x y hx hy hxy hnxy hw
  classical
  obtain ⟨w0, hyw0, hw0e, hxw0⟩ := hw
  by_cases hz : ∃ g, g ∈ evenSet G
  swap
  · -- no even vertex: L₁
    have h0 : (evenSet G).card = 0 :=
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
  -- the child `G − gu` of a target `u ∉ {x, y}` is an instance of N with a witness `w ≠ u`
  have child : ∀ u, G.Adj g u → u ≠ x → u ≠ y → ∀ w, G.Adj y w → w ≠ u → w ∉ evenSet G ∨ w = g →
      ¬ G.Adj x w → AvoidDecomp (delEdge G g u) y {x} := by
    intro u hgu hux huy w hyw hwu _ hxw
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
    have hc := child u hgu hux huy w0 hyw0 (by rintro rfl; exact hyu hyw0) (Or.inl hw0e) hxw0
    exact avoidDecomp_singleton_iff.mpr (avoid_free_target hev hg hgu hux huy hyu hyg
      (avoidDecomp_singleton_iff.mp hc))
  simp only [not_exists, not_and, not_not] at h1
  -- (2) a tight target whose child keeps a witness: TRN
  by_cases h2 : ∃ u, G.Adj g u ∧ u ≠ x ∧ u ≠ y ∧ ∃ w, G.Adj y w ∧ w ≠ u ∧ ¬ G.Adj x w
  · obtain ⟨u, hgu, hux, huy, w, hyw, hwu, hxw⟩ := h2
    have hyu : G.Adj y u := h1 u hgu hux huy
    have hwe : w ∉ evenSet G ∨ w = g := by
      by_cases hwg : w = g
      · exact Or.inr hwg
      · exact Or.inl fun h => hwg (huniq w h)
    exact hT G hev g hg x y u hx hy hxy hnxy hgu hyu hux (child u hgu hux huy w hyw hwu hwe hxw)
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
  · -- then `g ~ y` forces `g ~ x`
    have hyx : G.Adj g y → G.Adj g x := by
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
      -- `N(g) = {x, w0}`, `x ≁ w0`: split `g` off and apply L₁
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
      obtain ⟨hHw, hHg, -, hHadj, -⟩ := splitOff_facts hNg hw0x.symm hxw0
      set H := plusEdge (delEdge (delEdge G g x) g w0) x w0
      have hH0 : (evenSet H).card = 0 := by
        refine Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun v hv => ?_)
        obtain ⟨hpos, hevn⟩ := mem_evenSet_iff.mp hv
        by_cases hvg : v = g
        · rw [hvg, hHg] at hpos; omega
        · rw [hHw v hvg] at hpos hevn
          exact hvg (huniq v (mem_evenSet_iff.mpr ⟨hpos, hevn⟩))
      have hHyx : ¬ H.Adj y x := by
        intro h
        rcases hHadj y x h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -⟩
        · exact hxy h.symm
        · exact hw0y h.symm
        · exact hnxy h.symm
      have hHy : H.degree y % 2 = 1 := by rw [hHw y hyg]; exact hy
      have hgood : AvoidDecomp H y {x} := avoidDecomp_singleton_iff.mpr
        (lovasz_avoid_nonadj H hH0 hHy (Ne.symm hxy) hHyx)
      exact avoid_of_splitOff hg hNg hw0x.symm hxw0 hyg
        (by rw [Finset.mem_singleton]; exact Ne.symm hxg) hgood
    · -- `N(g) ⊆ {w0}`: impossible, as `d(g)` is even and positive
      have hgy : ¬ G.Adj g y := fun h => hgx (hyx h)
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
  · -- `N(g) ⊆ {x, y}`, hence `N(g) = {x, y}`: the degree-two case
    have hsub' : G.neighborFinset g ⊆ {x, y} := by
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

/-- **Theorem (manuscript Theorem 4.1).** The tight transfer for one forbidden vertex and the
degree-two case imply Conjecture N. -/
theorem conjN_of_tight_degTwo (hT : TightTransferNOn V) (hR : ConjNDegTwoOn V) : ConjNOn V :=
  fun G _ hev x y hx hy hxy hnxy hw => conjN_strong hT hR _ G rfl hev x y hx hy hxy hnxy hw

/-- **The degree-two case is neighbour avoidance.** Split `g` off: in `H = G − gx − gy + xy` there is
no even vertex and `x ~ y`; NA gives `Q(y) ∌ x` there, and subdividing `xy` by `g` keeps it. -/
theorem conjNDegTwo_of_neighbourAvoid (hNA : NeighbourAvoidOn V) : ConjNDegTwoOn V := by
  intro G _ hev g hg x y hNg hx hy hxy hnxy hw
  classical
  obtain ⟨w, hyw, hwg, hxw⟩ := hw
  have huniq : ∀ w ∈ evenSet G, w = g := fun w hw => Finset.card_le_one.mp hev w hw g hg
  have hgdeg := mem_evenSet_iff.mp hg
  have hxg : x ≠ g := by rintro rfl; omega
  have hyg : y ≠ g := by rintro rfl; omega
  obtain ⟨hHw, hHg, hHxy, hHadj, -⟩ := splitOff_facts hNg hxy hnxy
  set H := plusEdge (delEdge (delEdge G g x) g y) x y
  have hH0 : (evenSet H).card = 0 := by
    refine Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun v hv => ?_)
    obtain ⟨hpos, hevn⟩ := mem_evenSet_iff.mp hv
    by_cases hvg : v = g
    · rw [hvg, hHg] at hpos; omega
    · rw [hHw v hvg] at hpos hevn
      exact hvg (huniq v (mem_evenSet_iff.mpr ⟨hpos, hevn⟩))
  have hwx : w ≠ x := by rintro rfl; exact hnxy hyw.symm
  have hwy : w ≠ y := hyw.ne.symm
  have hHyw : H.Adj y w := Or.inl
    (delEdge_adj_of_ne (delEdge_adj_of_ne hyw.symm hwg hwx) hwg hwy).symm
  have hHxw : ¬ H.Adj x w := by
    intro h
    rcases hHadj x w h with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -, -⟩
    · exact hwy h
    · exact hxy h
    · exact hxw h
  have hHy : H.degree y % 2 = 1 := by rw [hHw y hyg]; exact hy
  exact avoid_of_splitOff hg hNg hxy hnxy hyg (by rw [Finset.mem_singleton]; exact Ne.symm hxg)
    (hNA H hH0 x y hHy hHxy ⟨w, hHyw, hwx, hHxw⟩)

/-- **TR for tails adjacent to the even vertex** (`TightTransfer` of l1-induction with
`G.Adj g c` in place of `¬ G.Adj g c`). -/
def TightTransferAdj : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (evenSet G).card ≤ 1 → ∀ g ∈ evenSet G, ∀ c : V, G.degree c % 2 = 1 → G.Adj g c →
    ∀ x : V, G.Adj g x → G.Adj c x → ∀ A : Finset V, c ∉ A → x ∉ A → (∀ a ∈ A, ¬ G.Adj c a) →
    AvoidDecomp (delEdge G g x) c A → AvoidDecomp G c A

/-- `TightTransfer` (l1-induction Conjecture 4.1) and its counterpart for tails adjacent to `g`
give TRN. -/
theorem tightTransferNOn_of (h1 : TightTransfer.{u}) (h2 : TightTransferAdj.{u}) :
    TightTransferNOn V := by
  intro G _ hev g hg x y u _ hy hxy hnxy hgu hyu hux hchild
  have hyA : y ∉ ({x} : Finset V) := by rw [Finset.mem_singleton]; exact Ne.symm hxy
  have huA : u ∉ ({x} : Finset V) := by rw [Finset.mem_singleton]; exact hux
  have hloc : ∀ a ∈ ({x} : Finset V), ¬ G.Adj y a := by
    intro a ha; rw [Finset.mem_singleton.mp ha]; exact fun h => hnxy h.symm
  by_cases hgy : G.Adj g y
  · exact h2 V G hev g hg y hy hgy u hgu hyu {x} hyA huA hloc hchild
  · exact h1 V G hev g hg y hy hgy u hgu hyu {x} hyA huA hloc hchild

/-- **Corollary.** TR, its counterpart for tails adjacent to `g`, and NA imply Conjecture N. -/
theorem conjN_of_TR_neighbourAvoid (h1 : TightTransfer.{u}) (h2 : TightTransferAdj.{u})
    (hNA : NeighbourAvoidOn V) : ConjNOn V :=
  conjN_of_tight_degTwo (tightTransferNOn_of h1 h2) (conjNDegTwo_of_neighbourAvoid hNA)

/-- **Corollary.** TRN and NA imply Conjecture N. -/
theorem conjN_of_tight_neighbourAvoid (hT : TightTransferNOn V) (hNA : NeighbourAvoidOn V) :
    ConjNOn V :=
  conjN_of_tight_degTwo hT (conjNDegTwo_of_neighbourAvoid hNA)

end conjN

end Gallai
