import GallaiLean.PathSurgery

/-!
# Bounds on small graphs used in the separator theorem

All graphs here live on a fixed vertex type `V` with all their edges inside a finite set `U`;
statements about them are proved on the induced subtype and transported back.

* `decomp_of_induce`, `degree_induce_eq`, `degree_eq_zero_of_notMem`: transport.
* `lovasz_on`, `lovasz_tight`: Lovász's theorem on `U`, and its tight form (one end at every odd
  vertex, none at the even one).
* `exists_leafCost_le_markedNumber`: a single mark is a private leaf.
* `smallBlocks_addLeaf`: a private leaf creates no new two-connected block.
* `induce_erase_connected`: deleting a vertex of degree one keeps the graph connected.
* `R2_on`, `R3_on`, `floor_on`: from the marked bound on graphs of order `≤ m`: `F₂` at a positive
  even root (even order), `F₃` at an odd root of degree `≥ 3` (odd order), and the floor bound at
  odd order with a vertex of degree one. These are the "smaller rooted bounds" of the proof of
  Theorem 113.
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} {U : Finset V}

/-- A decomposition of `G` restricted to a vertex set containing all its edges is one of `G`. -/
theorem decomp_of_induce (hU : ∀ a b, G.Adj a b → a ∈ U)
    (D : PathDecomp (G.induce (U : Set V))) :
    ∃ D' : PathDecomp G, D'.size ≤ D.size ∧ ∀ v : (U : Set V), D'.ends v = D.ends v := by
  obtain ⟨D', h1, h2⟩ := D.map_injective_ends Subtype.val Subtype.val_injective (by
    intro e'
    constructor
    · intro he'
      induction e' using Sym2.inductionOn with
      | hf a b =>
      exact ⟨s(⟨a, hU a b he'⟩, ⟨b, hU b a (G.adj_symm he')⟩), he', rfl⟩
    · rintro ⟨e, he, rfl⟩
      induction e using Sym2.inductionOn with
      | hf c d => exact he)
  exact ⟨D', h1, h2⟩

theorem degree_induce_eq [Fintype V] [DecidableRel G.Adj] (hU : ∀ a b, G.Adj a b → a ∈ U)
    (v : (U : Set V)) [Fintype ((G.induce (U : Set V)).neighborSet v)] :
    (G.induce (U : Set V)).degree v = G.degree v := by
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  exact Fintype.card_congr
    { toFun := fun w => ⟨w.1.1, w.2⟩
      invFun := fun w => ⟨⟨w.1, hU w.1 v (G.adj_symm w.2)⟩, w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

omit [DecidableEq V] in
theorem degree_eq_zero_of_notMem [Fintype V] [DecidableRel G.Adj]
    (hU : ∀ a b, G.Adj a b → a ∈ U) {v : V} (hv : v ∉ U) : G.degree v = 0 := by
  rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro w hw
  exact hv (hU v w (by simpa using hw))

/-- **Lovász on a vertex set**: if at most one vertex of `U` has even degree, `G` has a
decomposition into at most `|U| / 2` paths. -/
theorem lovasz_on [Fintype V] (hL : LovaszStatement.{u}) [DecidableRel G.Adj]
    (hU : ∀ a b, G.Adj a b → a ∈ U)
    (heven : (U.filter (fun v => Even (G.degree v))).card ≤ 1) :
    ∃ D : PathDecomp G, 2 * D.size ≤ U.card := by
  set F := G.induce (U : Set V)
  have hcnt : (Finset.univ.filter (fun v : (U : Set V) => Even (F.degree v))).card ≤ 1 := by
    have : (Finset.univ.filter (fun v : (U : Set V) => Even (F.degree v))).map
        (Function.Embedding.subtype _) = U.filter (fun v => Even (G.degree v)) := by
      ext v
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w.2, by rwa [degree_induce_eq hU] at hw⟩
      · rintro ⟨hv, he⟩
        exact ⟨⟨v, hv⟩, by rwa [degree_induce_eq hU], rfl⟩
    rw [← Finset.card_map, this]
    exact heven
  have hp := hL _ F hcnt
  obtain ⟨DF, hDF⟩ := pathNumber_spec F
  obtain ⟨D, h1, -⟩ := decomp_of_induce hU DF
  refine ⟨D, ?_⟩
  have : Fintype.card (U : Set V) = U.card := by simp
  rw [this] at hp
  omega

/-- **Lovász, tight form**: if `|U|` is odd and exactly one vertex of `U` is even, some
decomposition has `(|U| − 1)/2` paths, one end at every odd vertex and none elsewhere. -/
theorem lovasz_tight [Fintype V] (hL : LovaszStatement.{u}) [DecidableRel G.Adj]
    (hU : ∀ a b, G.Adj a b → a ∈ U) (hodd : Odd U.card)
    (heven : (U.filter (fun v => Even (G.degree v))).card = 1) :
    ∃ D : PathDecomp G, 2 * D.size + 1 = U.card ∧
      ∀ v, D.ends v = if Odd (G.degree v) then 1 else 0 := by
  obtain ⟨D, hD⟩ := lovasz_on hL hU heven.le
  have hodd_eq : Finset.univ.filter (fun v => Odd (G.degree v)) =
      U.filter (fun v => Odd (G.degree v)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      refine ⟨?_, h⟩
      by_contra hv
      rw [degree_eq_zero_of_notMem hU hv] at h
      exact absurd h (by decide)
    · exact fun h => h.2
  have hsplit := Finset.card_filter_add_card_filter_not (s := U) (fun v => Even (G.degree v))
  have hneg : U.filter (fun v => ¬ Even (G.degree v)) = U.filter (fun v => Odd (G.degree v)) := by
    ext v; simp [Nat.not_even_iff_odd]
  rw [hneg, heven] at hsplit
  obtain ⟨k, hk⟩ := hodd
  have htight : 2 * D.size ≤ (Finset.univ.filter (fun v => Odd (G.degree v))).card := by
    rw [hodd_eq]; omega
  have hends := D.ends_eq_of_tight htight
  refine ⟨D, ?_, hends⟩
  have hsum := D.sum_ends
  have : ∑ v, D.ends v = (Finset.univ.filter (fun v => Odd (G.degree v))).card := by
    rw [Finset.card_filter]; exact Finset.sum_congr rfl (fun v _ => hends v)
  rw [hodd_eq] at this
  omega

/-- **A single mark is a private leaf**: some decomposition has leaf cost at most `q(F, {a}) + 1`. -/
theorem exists_leafCost_le_markedNumber {W : Type u} [Finite W] [DecidableEq W]
    (F : SimpleGraph W) (a : W) : ∃ D : PathDecomp F, leafCost D a ≤ markedNumber F {a} + 1 := by
  obtain ⟨M, hM⟩ := markedNumber_spec F {a}
  refine ⟨M.decomp, ?_⟩
  have hlen := length_eq_cost_add_sites M
  have hsz : M.decomp.size = M.paths.length := by simp [MarkedPartition.decomp, PathDecomp.size]
  have hsites : (M.paths.filterMap Prod.snd).length ≤ 1 := by
    rw [← List.toFinset_card_of_nodup M.sites_nodup]
    calc _ ≤ ({a} : Finset W).card :=
          Finset.card_le_card (fun s hs => M.sites_mem (List.mem_toFinset.mp hs))
      _ = 1 := Finset.card_singleton a
  unfold leafCost
  rcases Nat.eq_zero_or_pos (M.paths.filterMap Prod.snd).length with h0 | hpos
  · split_ifs <;> omega
  · obtain ⟨s, hs⟩ := List.exists_mem_of_length_pos hpos
    obtain ⟨x, hx, hxs⟩ := List.mem_filterMap.mp hs
    obtain ⟨hsS, hend⟩ := M.site_ok x hx s hxs
    have hsa : s = a := Finset.mem_singleton.mp hsS
    subst hsa
    have hpos' : 0 < M.decomp.ends s := by
      have hmem : x.1 ∈ M.decomp.paths := List.mem_map_of_mem (f := Prod.fst) hx
      have h1 : x.1.endsAt s ≤ M.decomp.ends s := List.le_sum_of_mem (List.mem_map_of_mem hmem)
      have h2 : 1 ≤ x.1.endsAt s := by
        unfold GPath.endsAt; rcases hend with h | h <;> simp [h]
      omega
    simp only [hpos'.ne', ite_false]
    omega

/-- A private leaf creates no new two-connected block. -/
theorem smallBlocks_addLeaf {W : Type u} [Fintype W] [DecidableEq W] (F : SimpleGraph W)
    [DecidableRel F.Adj] (a : W) : SmallBlocks (addLeaf F a) (Fintype.card W) := by
  intro S hS
  by_cases hn : none ∈ S
  · exfalso
    have h2 := hS.le_degree (⟨none, hn⟩ : (S : Set (Option W)))
    have h1 : ((addLeaf F a).induce (S : Set (Option W))).degree ⟨none, hn⟩ ≤
        (addLeaf F a).degree none := by
      rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
      exact Fintype.card_le_of_injective (fun w => ⟨w.1.1, w.2⟩)
        (fun w₁ w₂ h => by
          have h' := congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext h'))
    rw [addLeaf_degree_none] at h1
    omega
  · have hsub : S ⊆ Finset.univ.erase none :=
      fun v hv => Finset.mem_erase.mpr ⟨fun h => hn (h ▸ hv), Finset.mem_univ v⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_option]
      at this
    simpa using this

/-- Deleting a vertex of degree one keeps an induced subgraph connected. -/
theorem induce_erase_connected [Fintype V] [DecidableRel G.Adj]
    (hc : (G.induce (U : Set V)).Connected) {r : V} (hr1 : G.degree r = 1)
    (hne : (U.erase r).Nonempty) : (G.induce ((U.erase r : Finset V) : Set V)).Connected := by
  obtain ⟨-, hwalk⟩ := induce_connected_iff.mp hc
  have hN : (G.neighborFinset r).card = 1 := by rw [card_neighborFinset_eq_degree]; exact hr1
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hN
  have huniq : ∀ b, G.Adj r b → b = t := fun b hb =>
    Finset.mem_singleton.mp (ht ▸ (mem_neighborFinset _ _ _).mpr hb)
  refine induce_connected_iff.mpr ⟨Finset.coe_nonempty.mpr hne, fun p hp q hq => ?_⟩
  rw [Finset.mem_coe, Finset.mem_erase] at hp hq
  obtain ⟨w, hw⟩ := hwalk p hp.2 q hq.2
  refine ⟨w.bypass, fun v hv => ?_⟩
  rw [Finset.mem_coe, Finset.mem_erase]
  refine ⟨?_, hw v (w.support_bypass_subset_support hv)⟩
  rintro rfl
  obtain ⟨w₁, w₂, hsplit⟩ := Walk.mem_support_iff_exists_append.mp hv
  have hnd := (Walk.isPath_def _).mp w.bypass_isPath
  rw [hsplit] at hnd
  have hd := ((nodup_support_append w₁ w₂).mp hnd).2.2
  have h1 : 0 < w₁.reverse.length := by
    rw [Walk.length_reverse]
    by_contra h0
    exact hp.1 (Walk.eq_of_length_eq_zero (p := w₁) (by omega))
  have h2 : 0 < w₂.length := by
    by_contra h0
    exact hq.1 (Walk.eq_of_length_eq_zero (p := w₂) (by omega)).symm
  obtain ⟨c, hc', w₁', hw₁⟩ := Walk.exists_eq_cons_of_length_pos w₁.reverse h1
  obtain ⟨d, hd', w₂', hw₂⟩ := Walk.exists_eq_cons_of_length_pos w₂ h2
  have hcd : c = d := (huniq c hc').trans (huniq d hd').symm
  have hc1 : c ∈ w₁.support := by
    rw [← List.mem_reverse, ← Walk.support_reverse, hw₁, Walk.support_cons]
    exact List.mem_cons_of_mem _ w₁'.start_mem_support
  have hc2 : c ∈ w₂.support := by
    rw [hw₂, Walk.support_cons, hcd]
    exact List.mem_cons_of_mem _ w₂'.start_mem_support
  exact hc'.ne (hd c hc1 hc2).symm

section rooted

variable [Fintype V] {m : ℕ} {W : SimpleGraph V} [DecidableRel W.Adj]

/-- **`F₂` on a smaller graph**: even order, positive even root. -/
theorem R2_on (hMB : MarkedBoundUpTo.{u} m) (hWU : ∀ a b, W.Adj a b → a ∈ U)
    (hWc : (W.induce (U : Set V)).Connected) (hUm : U.card ≤ m) (hev : Even U.card) {r : V}
    (hrU : r ∈ U) (hr : Even (W.degree r)) (hpos : 0 < W.degree r) :
    ∃ D : PathDecomp W, D.size ≤ U.card / 2 ∧ 2 ≤ D.ends r := by
  set F := W.induce (U : Set V)
  set r' : (U : Set V) := ⟨r, hrU⟩
  have hcard : Fintype.card (U : Set V) = U.card := by simp
  have hq := hMB (U : Set V) F hWc
    (fun S _ => (Finset.card_le_univ S).trans (by rw [hcard]; exact hUm)) {r'}
    (Finset.singleton_nonempty _)
  rw [hcard, Finset.card_singleton] at hq
  obtain ⟨D₀, hD₀⟩ := exists_leafCost_le_markedNumber F r'
  have hdeg : F.degree r' = W.degree r := degree_induce_eq hWU r'
  have hU1 : 1 ≤ U.card := Finset.card_pos.mpr ⟨r, hrU⟩
  obtain ⟨D₁, h1, h2⟩ := exists_two_ends D₀ (x := r') (k := U.card / 2)
    (by obtain ⟨j, hj⟩ := hev; omega) (hdeg ▸ hr) (hdeg ▸ hpos)
  obtain ⟨D, hD1, hD2⟩ := decomp_of_induce hWU D₁
  exact ⟨D, hD1.trans h1, h2.trans_eq (hD2 r').symm⟩

/-- **`F₃` on a smaller graph**: odd order, odd root of degree `≥ 3` (private leaf, mark, trim). -/
theorem R3_on (hMB : MarkedBoundUpTo.{u} m) (hWU : ∀ a b, W.Adj a b → a ∈ U)
    (hWc : (W.induce (U : Set V)).Connected) (hUm : U.card ≤ m) (hodd : Odd U.card) {r : V}
    (hrU : r ∈ U) (hr : Odd (W.degree r)) (h3 : 3 ≤ W.degree r) :
    ∃ D : PathDecomp W, D.size ≤ U.card / 2 + 1 ∧ 3 ≤ D.ends r := by
  set F := W.induce (U : Set V)
  set r' : (U : Set V) := ⟨r, hrU⟩
  have hcard : Fintype.card (U : Set V) = U.card := by simp
  have hdegF : F.degree r' = W.degree r := degree_induce_eq hWU r'
  set F' := addLeaf F r'
  have hF'c : F'.Connected := addLeaf_connected hWc r'
  have hsb : SmallBlocks F' m := fun S hS =>
    (smallBlocks_addLeaf F r' S hS).trans (by rw [hcard]; exact hUm)
  have hq := hMB _ F' hF'c hsb {some r'} (Finset.singleton_nonempty _)
  rw [Fintype.card_option, hcard, Finset.card_singleton] at hq
  obtain ⟨D₀, hD₀⟩ := exists_leafCost_le_markedNumber F' (some r')
  have hdeg : F'.degree (some r') = W.degree r + 1 := by
    rw [addLeaf_degree_some, hdegF]; simp
  obtain ⟨j, hj⟩ := hodd
  obtain ⟨D₁, h11, h12⟩ := exists_two_ends D₀ (x := some r') (k := U.card / 2 + 1) (by omega)
    (by rw [hdeg, Nat.even_add_one, Nat.not_even_iff_odd]; exact hr) (by omega)
  obtain ⟨D₂, hD₂ | hD₂⟩ := PathDecomp.trim_ends D₁
  · obtain ⟨D, hD1, hD2⟩ := decomp_of_induce hWU D₂
    refine ⟨D, hD1.trans (hD₂.1.trans h11), ?_⟩
    calc 3 ≤ D₂.ends r' := by omega
      _ = D.ends r := (hD2 r').symm
  · obtain ⟨D₃, h31, h32⟩ := exists_three_ends D₂ (k := U.card / 2) (by omega)
      (hdegF ▸ hr) (by omega)
    obtain ⟨D, hD1, hD2⟩ := decomp_of_induce hWU D₃
    exact ⟨D, hD1.trans h31, h32.trans_eq (hD2 r').symm⟩

/-- **The floor bound on a smaller graph**: odd order and a vertex of degree one. -/
theorem floor_on (hMB : MarkedBoundUpTo.{u} m) (hWU : ∀ a b, W.Adj a b → a ∈ U)
    (hWc : (W.induce (U : Set V)).Connected) (hUm : U.card ≤ m) (hodd : Odd U.card) {r : V}
    (hrU : r ∈ U) (hr1 : W.degree r = 1) : ∃ D : PathDecomp W, D.size ≤ U.card / 2 := by
  have hN : (W.neighborFinset r).card = 1 := by rw [card_neighborFinset_eq_degree]; exact hr1
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hN
  have huniq : ∀ b, W.Adj r b → b = a := fun b hb =>
    Finset.mem_singleton.mp (ha ▸ (mem_neighborFinset _ _ _).mpr hb)
  have hra : W.Adj r a := by
    rw [← mem_neighborFinset, ha]; exact Finset.mem_singleton_self a
  set T := U.erase r
  have haT : a ∈ T := Finset.mem_erase.mpr ⟨hra.ne', hWU a r hra.symm⟩
  have hTc : (W.induce (T : Set V)).Connected := induce_erase_connected hWc hr1 ⟨a, haT⟩
  set F := W.induce (T : Set V)
  set a' : (T : Set V) := ⟨a, haT⟩
  have hcardT : Fintype.card (T : Set V) = U.card - 1 := by
    rw [Fintype.card_of_subtype (U.erase r) (fun x => Finset.mem_coe.symm),
      Finset.card_erase_of_mem hrU]
  have hTpos : 1 ≤ U.card - 1 := by
    rw [← hcardT]; exact Fintype.card_pos_iff.mpr ⟨a'⟩
  have hq := hMB _ F hTc (fun S _ => (Finset.card_le_univ S).trans (by rw [hcardT]; omega)) {a'}
    (Finset.singleton_nonempty _)
  rw [hcardT, Finset.card_singleton] at hq
  obtain ⟨D₀, hD₀⟩ := exists_leafCost_le_markedNumber F a'
  have hp := pathNumber_addLeaf_le D₀ a'
  obtain ⟨D₁, hD₁⟩ := pathNumber_spec (addLeaf F a')
  let g : Option (T : Set V) → V := fun o => o.elim r Subtype.val
  have hrT : r ∉ T := Finset.notMem_erase r U
  have hginj : Function.Injective g := by
    rintro (_ | ⟨b, hb⟩) (_ | ⟨c, hc⟩) h
    · rfl
    · simp only [g, Option.elim_none, Option.elim_some] at h
      exact absurd (by rw [h]; exact hc) hrT
    · simp only [g, Option.elim_none, Option.elim_some] at h
      exact absurd (by rw [← h]; exact hb) hrT
    · simp only [g, Option.elim_some] at h; subst h; rfl
  obtain ⟨D, hD1, -⟩ := D₁.map_injective_ends g hginj (by
    intro e'
    constructor
    · intro hpq
      induction e' using Sym2.inductionOn with
      | hf p q =>
      rw [mem_edgeSet] at hpq
      by_cases hpr : p = r
      · subst hpr
        have hq' := huniq q hpq
        subst hq'
        exact ⟨s(none, some a'), by rw [mem_edgeSet]; rfl, rfl⟩
      by_cases hqr : q = r
      · subst hqr
        have hp' := huniq p hpq.symm
        subst hp'
        exact ⟨s(some a', none), by rw [mem_edgeSet]; rfl, rfl⟩
      · have hpT : p ∈ T := Finset.mem_erase.mpr ⟨hpr, hWU p q hpq⟩
        have hqT : q ∈ T := Finset.mem_erase.mpr ⟨hqr, hWU q p hpq.symm⟩
        exact ⟨s(some ⟨p, hpT⟩, some ⟨q, hqT⟩), hpq, rfl⟩
    · rintro ⟨e, he, rfl⟩
      induction e using Sym2.inductionOn with
      | hf o₁ o₂ =>
      rw [mem_edgeSet] at he
      cases o₁ with
      | none =>
        cases o₂ with
        | none => exact absurd he addLeaf_not_adj_none_none
        | some b =>
          rw [addLeaf_adj_none_some] at he
          subst he
          exact hra
      | some b =>
        cases o₂ with
        | none =>
          rw [addLeaf_adj_some_none] at he
          subst he
          exact hra.symm
        | some c => exact he)
  refine ⟨D, ?_⟩
  obtain ⟨j, hj⟩ := hodd
  have : D₁.size ≤ U.card / 2 := by
    rw [hD₁]; omega
  omega

end rooted

end Gallai
