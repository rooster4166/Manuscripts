import GallaiLean.ConjN

/-!
# The tight transfer TRN: two transfers, two outright cases, and the core that N needs

Manuscript `manuscripts/trn`.

**TRN** (`TightTransferNOn`, conj-n Conjecture 4.1). Let `g` be the only even vertex of `G`, let
`x, y` be odd and non-adjacent, and let `u ∈ N(g) ∩ N(y)` with `u ≠ x`. If `(G − gu, y, {x})` is
good, then `(G, y, {x})` is good.

Everything below is proved in full.

* `avoid_of_separating_child` (manuscript Lemma 4.1): if some Lovász decomposition of `G − gu`
  has no path through both `x` and `y`, then `(G, y, {x})` is good. Fan's lemma with vertex sets,
  with the target `u ∉ {x, y}`.
* Two cases in which `(G, y, {x})` is good outright, with no hypothesis on `G − gu`:
  * `avoid_of_farApart`: `x` and `y` are at distance at least three (separation);
  * `avoid_of_degTwo_indep`: `d(g) = 2` and the two neighbours of `g` are non-adjacent and are not
    `{x, y}` (split `g` off, then `L₁`).
* `TightTransferNCore` (manuscript Definition 5.1), the restriction of TRN to instances with every
  property that holds where the induction for Conjecture N applies TRN. The extra hypotheses are:
  * `(G, y, {x})` is itself an instance of N: `y` has a neighbour that is not even and not
    adjacent to `x`;
  * Conjecture N holds for every graph on `V` of smaller degree sum;
  * every neighbour of `g` other than `x, y` is adjacent to `y` (all-tight);
  * the child keeps a witness `w ∈ N(y) ∖ N(x)`, `w ≠ u` (`w = g` is allowed);
  * `x` and `y` have a common neighbour;
  * `N(g)` is not an independent pair.
* `conjN_of_core` (manuscript Theorem 5.2): `TightTransferNCore` and the degree-two case imply
  Conjecture N; with `conjNDegTwo_of_neighbourAvoid`, `conjN_of_core_neighbourAvoid`. Since
  `TightTransferNOn` implies `TightTransferNCore` (`tightTransferNCore_of`), this strengthens
  `conjN_of_tight_degTwo`. NA is proved (`neighbourAvoidOn`, `conjNDegTwoOn`), so the core alone
  implies N; `TRNSteer.lean` reduces it further, to the core instances with no two-token schedule.
-/

open SimpleGraph

namespace Gallai

universe u

section trn

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Separation survives Lovász's Case I step** (manuscript Lemma 4.1). Let `g` be the even
vertex and `u ∈ N(g)` with `u ∉ {x, y}`. If `G − gu` has a Lovász decomposition in which no path
contains both `y` and `x`, then `G` has a Lovász decomposition whose path ending at `y` avoids
`x`. Every path of Fan's decomposition lies in an old path together with `u`. -/
theorem avoid_of_separating_child {G : SimpleGraph V} [DecidableRel G.Adj]
    (hev : (evenSet G).card ≤ 1) {g u x y : V} (hg : g ∈ evenSet G) (hgu : G.Adj g u)
    (hux : u ≠ x) (huy : u ≠ y)
    (D' : PathDecomp (delEdge G g u)) (hD' : ∀ v, D'.ends v = (delEdge G g u).degree v % 2)
    (hsep : Separates D' y x) : AvoidDecomp G y {x} := by
  classical
  have hgu' : g ≠ u := hgu.ne
  have huniq : ∀ w ∈ evenSet G, w = g := fun w hw => Finset.card_le_one.mp hev w hw g hg
  have hodd : ∀ w, w ≠ g → 0 < G.degree w → G.degree w % 2 = 1 := by
    intro w hwg hpos
    have : w ∉ evenSet G := fun h => hwg (huniq w h)
    rw [mem_evenSet_iff] at this
    omega
  have hgd := mem_evenSet_iff.mp hg
  have hdeg := delEdge_degree G hgu
  have hG' : ∀ e, e ∈ (delEdge G g u).edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(u, g) := by
    intro e
    rw [delEdge_edgeSet, Sym2.eq_swap (a := u)]
  have hD'g : D'.ends g = 1 := by
    rw [hD']
    have := hdeg g
    simp only [hgu', ite_true, ite_false] at this
    omega
  have hcount : (Finset.univ.filter (fun w => (delEdge G g u).Adj u w ∧ D'.ends w = 0)).card <
      D'.ends g := by
    have hempty : Finset.univ.filter (fun w => (delEdge G g u).Adj u w ∧ D'.ends w = 0) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun w hw => ?_
      rw [Finset.mem_filter] at hw
      obtain ⟨-, hadj, h0⟩ := hw
      have hwg : w ≠ g := fun h => hadj.2 (by rw [h, Sym2.eq_swap])
      have hwu : w ≠ u := hadj.ne.symm
      rw [hD'] at h0
      have hdw := hdeg w
      simp only [hwg, hwu, ite_false, add_zero] at hdw
      have := hodd w hwg ((G.degree_pos_iff_exists_adj w).mpr ⟨u, hadj.1.symm⟩)
      omega
    rw [hempty, Finset.card_empty, hD'g]
    omega
  obtain ⟨D, -, hDu, hDg, hDrest, hcov⟩ := fan_single_supp hgu.symm hG' D' hcount
  refine ⟨D, fun w => ?_, fun Q hQ hQy a ha => ?_⟩
  · by_cases hwu : w = u
    · subst hwu
      rw [hDu, hD']
      have := hdeg w
      simp only [hgu'.symm, ite_true, ite_false] at this
      have := hodd w hgu'.symm ((G.degree_pos_iff_exists_adj w).mpr ⟨g, hgu.symm⟩)
      omega
    · by_cases hwg : w = g
      · subst hwg
        rw [hD'g] at hDg
        rw [show D.ends w = 0 by omega, hgd.2]
      · rw [hDrest w hwu hwg, hD']
        have := hdeg w
        simp only [hwg, hwu, ite_false, add_zero] at this
        rw [this]
  · rw [Finset.mem_singleton] at ha
    rw [ha]
    intro hxQ
    obtain ⟨Q', hQ', hsub⟩ := hcov Q hQ
    have hyQ : y ∈ Q.walk.support := by
      rcases hQy with h | h
      · rw [← h]; exact Q.walk.start_mem_support
      · rw [← h]; exact Q.walk.end_mem_support
    have hyQ' : y ∈ Q'.walk.support := (hsub y hyQ).resolve_right (Ne.symm huy)
    have hxQ' : x ∈ Q'.walk.support := (hsub x hxQ).resolve_right (Ne.symm hux)
    exact hsep Q' hQ' ⟨hyQ', hxQ'⟩

/-- **Outright case: distance at least three.** If `y` and `x` are distinct, non-adjacent and
have no common neighbour, some Lovász decomposition separates them (`separation`), so its path
ending at `y` avoids `x`. No hypothesis on `G − gu` is needed. -/
theorem avoid_of_farApart {G : SimpleGraph V} [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1)
    {x y : V} (hfar : FarApart G y x) : AvoidDecomp G y {x} := by
  obtain ⟨D, hD, hsep⟩ := separation G hev hfar
  refine ⟨D, hD, fun Q hQ hQy a ha => ?_⟩
  rw [Finset.mem_singleton] at ha
  rw [ha]
  intro hxQ
  have hyQ : y ∈ Q.walk.support := by
    rcases hQy with h | h
    · rw [← h]; exact Q.walk.start_mem_support
    · rw [← h]; exact Q.walk.end_mem_support
  exact hsep Q hQ ⟨hyQ, hxQ⟩

/-- **Outright case: an even vertex of degree two with independent neighbours.** Let
`N(g) = {a, b}` with `a ≁ b`, and let `x, y` be odd and non-adjacent with `{x, y} ≠ {a, b}`.
Splitting `g` off leaves a graph with no even vertex in which `x ≁ y`; `L₁` and subdividing `ab`
by `g` give `(G, y, {x})` good. No hypothesis on `G − gu` is needed. -/
theorem avoid_of_degTwo_indep {G : SimpleGraph V} [DecidableRel G.Adj]
    (hev : (evenSet G).card ≤ 1) {g a b : V} (hg : g ∈ evenSet G)
    (hNg : ∀ v, G.Adj g v ↔ v = a ∨ v = b) (hab : a ≠ b) (hnadj : ¬ G.Adj a b)
    {x y : V} (hx : G.degree x % 2 = 1) (hy : G.degree y % 2 = 1) (hxy : x ≠ y)
    (hnxy : ¬ G.Adj x y) (hpair : ¬ ((y = a ∧ x = b) ∨ (y = b ∧ x = a))) :
    AvoidDecomp G y {x} := by
  classical
  have huniq : ∀ w ∈ evenSet G, w = g := fun w hw => Finset.card_le_one.mp hev w hw g hg
  have hgdeg := mem_evenSet_iff.mp hg
  have hxg : x ≠ g := by rintro rfl; omega
  have hyg : y ≠ g := by rintro rfl; omega
  obtain ⟨hHw, hHg, -, hHadj, -⟩ := splitOff_facts hNg hab hnadj
  set H := plusEdge (delEdge (delEdge G g a) g b) a b
  have hH0 : (evenSet H).card = 0 := by
    refine Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun v hv => ?_)
    obtain ⟨hpos, hevn⟩ := mem_evenSet_iff.mp hv
    by_cases hvg : v = g
    · rw [hvg, hHg] at hpos; omega
    · rw [hHw v hvg] at hpos hevn
      exact hvg (huniq v (mem_evenSet_iff.mpr ⟨hpos, hevn⟩))
  have hHyx : ¬ H.Adj y x := by
    intro h
    rcases hHadj y x h with h | h | ⟨h, -, -⟩
    · exact hpair (Or.inl h)
    · exact hpair (Or.inr h)
    · exact hnxy h.symm
  have hHy : H.degree y % 2 = 1 := by rw [hHw y hyg]; exact hy
  have hgood : AvoidDecomp H y {x} := avoidDecomp_singleton_iff.mpr
    (lovasz_avoid_nonadj H hH0 hHy (Ne.symm hxy) hHyx)
  exact avoid_of_splitOff hg hNg hab hnadj hyg
    (by rw [Finset.mem_singleton]; exact Ne.symm hxg) hgood

/-- Conjecture N on the graphs with vertex type `V` and degree sum less than `n`. -/
def ConjNBelow (V : Type u) [Fintype V] [DecidableEq V] (n : ℕ) : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj], (∑ w, G.degree w) < n → (evenSet G).card ≤ 1 →
    ∀ x y : V, G.degree x % 2 = 1 → G.degree y % 2 = 1 → x ≠ y → ¬ G.Adj x y →
    (∃ w, G.Adj y w ∧ w ∉ evenSet G ∧ ¬ G.Adj x w) → AvoidDecomp G y {x}

/-- **The core of TRN** (manuscript Definition 5.1): TRN restricted to instances with every property
that holds where the induction for Conjecture N applies TRN, with Conjecture N available on smaller
graphs. The extra
hypotheses, in order:
* (C0) `(G, y, {x})` is an instance of N: some neighbour of `y` is not even and not adjacent to `x`;
* N holds below the degree sum of `G`;
* all-tight: every neighbour of `g` other than `x, y` is adjacent to `y`;
* the child keeps a witness: some `w ∈ N(y)`, `w ≠ u`, is not adjacent to `x`;
* `x` and `y` have a common neighbour;
* `N(g)` is not a pair of non-adjacent vertices. -/
def TightTransferNCore (V : Type u) [Fintype V] [DecidableEq V] : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj], (evenSet G).card ≤ 1 → ∀ g ∈ evenSet G,
    ∀ x y u : V, G.degree x % 2 = 1 → G.degree y % 2 = 1 → x ≠ y → ¬ G.Adj x y →
    G.Adj g u → G.Adj y u → u ≠ x →
    (∃ w, G.Adj y w ∧ w ∉ evenSet G ∧ ¬ G.Adj x w) →
    ConjNBelow V (∑ w, G.degree w) →
    (∀ v, G.Adj g v → v ≠ x → v ≠ y → G.Adj y v) →
    (∃ w, G.Adj y w ∧ w ≠ u ∧ ¬ G.Adj x w) →
    (∃ c, G.Adj y c ∧ G.Adj c x) →
    ¬ (∃ a b, a ≠ b ∧ ¬ G.Adj a b ∧ ∀ v, G.Adj g v ↔ v = a ∨ v = b) →
    AvoidDecomp (delEdge G g u) y {x} → AvoidDecomp G y {x}

/-- TRN implies its core. -/
theorem tightTransferNCore_of (hT : TightTransferNOn V) : TightTransferNCore V :=
  fun G _ hev g hg x y u hx hy hxy hnxy hgu hyu hux _ _ _ _ _ _ hchild =>
    hT G hev g hg x y u hx hy hxy hnxy hgu hyu hux hchild

/-- **The core of TRN suffices for Conjecture N** (manuscript Theorem 5.2). The induction of
`conjN_strong`, with the tight step routed through `TightTransferNCore`: if `x, y` are at
distance at least three, separation finishes (`avoid_of_farApart`); if `N(g)` is an independent
pair, split off and `L₁` (`avoid_of_degTwo_indep`); otherwise the core applies, with the
induction hypothesis as its first extra hypothesis. -/
theorem conjN_of_core (hT : TightTransferNCore V) (hR : ConjNDegTwoOn V) : ConjNOn V := by
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
    exact hT G hev g hg x y u hx hy hxy hnxy hgu hyu hux ⟨w0, hyw0, hw0e, hxw0⟩ (by rw [hn]; exact hbelow) h1 ⟨w, hyw, hwu, hxw⟩
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

/-- **Corollary.** The core of TRN and NA imply Conjecture N. -/
theorem conjN_of_core_neighbourAvoid (hT : TightTransferNCore V) (hNA : NeighbourAvoidOn V) :
    ConjNOn V :=
  conjN_of_core hT (conjNDegTwo_of_neighbourAvoid hNA)

end trn

end Gallai
