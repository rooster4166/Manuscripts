import GallaiLean.MultiSepEE

/-!
# Prescribed end edges at the even vertex

Manuscript `manuscripts/prescribed-end/prescribed-end.tex`.

Let `z` be the only vertex of positive even degree of `G` and `u ∈ N(z)`. Conjecture EE asks for
a Lovász decomposition (`ends v = deg v mod 2`) in which `uz` is the terminal edge at `u`, that is,
the path ending at `u` contains `uz`.

* **`ee_atMostOneCommon`**: EE holds whenever `u` and `z` have at most one common neighbour.
  If there is none, this is `ee_noTriangle`. If `w` is the only one, `u` and `z` are at distance
  at least three in `G − uz − uw`, where `w` is the only vertex of positive even degree; separate
  them there (`separation`), restore `uw` by Fan's lemma with target `w` (`fan_single_supp`: the
  only vertex set that changes gains `w`, so the separation survives), and append `zu`
  (`ee_of_avoid`).
* **`ee_deg_two`**: in particular EE holds whenever `d(z) = 2`, in every configuration.

This contains `ee_noTriangle`, `ee_split` and `ee_triangle` (multi-sep Proposition "EE3") and the
degree-two cases of the star-terminal session.
-/

open SimpleGraph

namespace Gallai

universe u

variable {W : Type u} [Fintype W] [DecidableEq W]

section commonNbr

/-- **Separation in `G − uz` when `u` and `z` have at most one common neighbour.** Let `z` be the
only vertex of positive even degree of `G`, let `u ∈ N(z)`, and suppose `u` and `z` have at most
one common neighbour. Then `G − uz` has a Lovász decomposition in which no path contains both `u`
and `z`. -/
theorem sep_atMostOneCommon (G : SimpleGraph W) [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1)
    {z u : W} (hz : z ∈ evenSet G) (hzu : G.Adj z u)
    (hcom : ∀ w w', G.Adj u w → G.Adj w z → G.Adj u w' → G.Adj w' z → w = w') :
    ∃ D₁ : PathDecomp (delEdge G u z), (∀ v, D₁.ends v = (delEdge G u z).degree v % 2) ∧
      Separates D₁ u z := by
  classical
  obtain ⟨hsub, hzodd, hrest⟩ := delEdge_even_facts hev hz hzu
  by_cases hT : ∃ w, G.Adj u w ∧ G.Adj w z
  swap
  · have hev' : (evenSet (delEdge G u z)).card ≤ 1 :=
      (Finset.card_le_card hsub).trans (by simp)
    have hfar : FarApart (delEdge G u z) u z :=
      ⟨hzu.ne.symm, fun h => h.2 rfl, fun w hw => hT ⟨w, hw.1.1, hw.2.1⟩⟩
    exact separation _ hev' hfar
  obtain ⟨w, huw, hwz⟩ := hT
  have hwu : w ≠ u := huw.ne.symm
  have hwz' : w ≠ z := hwz.ne
  have hzu' : z ≠ u := hzu.ne
  have huniq : ∀ x ∈ evenSet G, x = z := fun x hx => Finset.card_le_one.mp hev x hx z hz
  -- `G₁ = G − uz` and `G₀ = G₁ − uw`
  have h₁uw : (delEdge G u z).Adj u w := ⟨huw, fun h => by
    rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h, -⟩
    · exact hwz' h
    · exact hzu' h.symm⟩
  have hd₀ := delEdge_degree (delEdge G u z) h₁uw
  have hd₁ := delEdge_degree G hzu.symm
  -- degrees of `u` in `G`
  have hupos : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).mpr ⟨z, hzu.symm⟩
  have huodd : G.degree u % 2 = 1 := by
    have : u ∉ evenSet G := fun h => hzu' (huniq u h).symm
    rw [mem_evenSet_iff] at this
    omega
  have hu3 : 2 ≤ G.degree u := by
    have hsub2 : ({z, w} : Finset W) ⊆ G.neighborFinset u := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [mem_neighborFinset]
      rcases hx with rfl | rfl
      · exact hzu.symm
      · exact huw
    have := Finset.card_le_card hsub2
    rw [card_neighborFinset_eq_degree, Finset.card_pair (Ne.symm hwz')] at this
    exact this
  -- degree bookkeeping in `G₀`
  have hdu₀ : (delEdge (delEdge G u z) u w).degree u + 2 = G.degree u := by
    have h1 := hd₀ u
    have h2 := hd₁ u
    simp only [hwu.symm, hzu'.symm, ite_true, ite_false, add_zero] at h1 h2
    omega
  have hdw₀ : (delEdge (delEdge G u z) u w).degree w + 1 = G.degree w := by
    have h1 := hd₀ w
    have h2 := hd₁ w
    simp only [hwu, hwz', ite_true, ite_false, add_zero] at h1 h2
    omega
  have hdz₀ : (delEdge (delEdge G u z) u w).degree z + 1 = G.degree z := by
    have h1 := hd₀ z
    have h2 := hd₁ z
    simp only [hzu', hwz'.symm, ite_true, ite_false, add_zero] at h1 h2
    omega
  have hdx₀ : ∀ x, x ≠ u → x ≠ w → x ≠ z →
      (delEdge (delEdge G u z) u w).degree x = G.degree x := by
    intro x hxu hxw hxz
    have h1 := hd₀ x
    have h2 := hd₁ x
    simp only [hxu, hxw, hxz, ite_false, add_zero] at h1 h2
    omega
  -- `w` is the only vertex of positive even degree of `G₀`
  have hev₀sub : evenSet (delEdge (delEdge G u z) u w) ⊆ {w} := by
    intro x hx
    rw [mem_evenSet_iff] at hx
    rw [Finset.mem_singleton]
    by_contra hxw
    by_cases hxu : x = u
    · subst hxu; omega
    · by_cases hxz : x = z
      · subst hxz
        have hzd := mem_evenSet_iff.mp hz
        omega
      · rw [hdx₀ x hxu hxw hxz] at hx
        exact hxz (huniq x (mem_evenSet_iff.mpr hx))
  have hev₀ : (evenSet (delEdge (delEdge G u z) u w)).card ≤ 1 :=
    (Finset.card_le_card hev₀sub).trans (by simp)
  -- `u` and `z` are at distance at least three in `G₀`
  have hfar : FarApart (delEdge (delEdge G u z) u w) u z := by
    refine ⟨hzu'.symm, fun h => h.1.2 rfl, fun x hx => ?_⟩
    obtain ⟨⟨⟨hux, hux1⟩, hux2⟩, ⟨⟨hxz, -⟩, -⟩⟩ := hx
    have hxw : x ≠ w := fun h => hux2 (by rw [h])
    exact hxw (hcom x w hux hxz huw hwz)
  obtain ⟨D₀, hD₀, hsep⟩ := separation _ hev₀ hfar
  -- Fan's lemma: restore `uw`, moving the end at `u` to `w`
  have hedges : ∀ e, e ∈ (delEdge (delEdge G u z) u w).edgeSet ↔
      e ∈ (delEdge G u z).edgeSet ∧ e ≠ s(w, u) := by
    intro e
    rw [delEdge_edgeSet, Sym2.eq_swap (a := w)]
  have hcount : (Finset.univ.filter
      (fun x => (delEdge (delEdge G u z) u w).Adj w x ∧ D₀.ends x = 0)).card < D₀.ends u := by
    have hempty : Finset.univ.filter
        (fun x => (delEdge (delEdge G u z) u w).Adj w x ∧ D₀.ends x = 0) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
      rw [Finset.mem_filter] at hx
      obtain ⟨-, hadj, hx0⟩ := hx
      have hxw : x ≠ w := hadj.ne.symm
      have hpos : 0 < (delEdge (delEdge G u z) u w).degree x :=
        ((delEdge (delEdge G u z) u w).degree_pos_iff_exists_adj x).mpr ⟨w, hadj.symm⟩
      have hnot : x ∉ evenSet (delEdge (delEdge G u z) u w) := fun h =>
        hxw (Finset.mem_singleton.mp (hev₀sub h))
      rw [mem_evenSet_iff] at hnot
      rw [hD₀] at hx0
      omega
    rw [hempty, Finset.card_empty, hD₀]
    omega
  obtain ⟨D₁, -, hD₁w, hD₁u, hD₁x, hcov⟩ :=
    fan_single_supp (G := delEdge G u z) h₁uw.symm hedges D₀ hcount
  have hD₁ : ∀ v, D₁.ends v = (delEdge G u z).degree v % 2 := by
    intro v
    by_cases hvw : v = w
    · subst hvw
      rw [hD₁w, hD₀]
      have h1 := hd₀ v
      simp only [hwu, ite_true, ite_false] at h1
      have hwodd : G.degree v % 2 = 1 := by
        have hpos : 0 < G.degree v := (G.degree_pos_iff_exists_adj v).mpr ⟨u, huw.symm⟩
        have : v ∉ evenSet G := fun h => hwz' (huniq v h)
        rw [mem_evenSet_iff] at this
        omega
      omega
    · by_cases hvu : v = u
      · subst hvu
        have h1 := hd₀ v
        simp only [hwu.symm, ite_true, ite_false, add_zero] at h1
        have := hD₀ v
        omega
      · rw [hD₁x v hvw hvu, hD₀]
        have h1 := hd₀ v
        simp only [hvu, hvw, ite_false, add_zero] at h1
        rw [h1]
  exact ⟨D₁, hD₁, separates_of_cover hwu hwz' hsep hcov⟩

/-- **EE when `u` and `z` have at most one common neighbour.** Let `z` be the only vertex of
positive even degree of `G`, let `u ∈ N(z)`, and suppose `u` and `z` have at most one common
neighbour. Then some Lovász decomposition of `G` has its path ending at `u` through `uz`. -/
theorem ee_atMostOneCommon (G : SimpleGraph W) [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1)
    {z u : W} (hz : z ∈ evenSet G) (hzu : G.Adj z u)
    (hcom : ∀ w w', G.Adj u w → G.Adj w z → G.Adj u w' → G.Adj w' z → w = w') :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∃ P ∈ D.paths, (P.src = u ∨ P.tgt = u) ∧ s(u, z) ∈ P.edges := by
  obtain ⟨D₁, hD₁, hsep₁⟩ := sep_atMostOneCommon G hev hz hzu hcom
  refine ee_of_avoid G hev hz hzu D₁ hD₁ fun P hP hend hu => hsep₁ P hP ⟨hu, ?_⟩
  have hmem : ∀ y, (P.src = y ∨ P.tgt = y) → y ∈ P.walk.support := by
    rintro y (h | h)
    · rw [← h]; exact P.walk.start_mem_support
    · rw [← h]; exact P.walk.end_mem_support
  exact hmem z hend

/-- **EE at a vertex of degree two.** If the only vertex `z` of positive even degree has degree
two, then for each neighbour `u` of `z` some Lovász decomposition has its path ending at `u`
through `uz`. (The two neighbours may be adjacent and may have further common neighbours.) -/
theorem ee_deg_two (G : SimpleGraph W) [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1)
    {z u : W} (hz : z ∈ evenSet G) (hzu : G.Adj z u) (hz2 : G.degree z = 2) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∃ P ∈ D.paths, (P.src = u ∨ P.tgt = u) ∧ s(u, z) ∈ P.edges := by
  classical
  refine ee_atMostOneCommon G hev hz hzu fun w w' huw hwz huw' hw'z => ?_
  by_contra hne
  have hsub : ({u, w, w'} : Finset W) ⊆ G.neighborFinset z := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_neighborFinset]
    rcases hx with rfl | rfl | rfl
    · exact hzu
    · exact hwz.symm
    · exact hw'z.symm
  have hcard := Finset.card_le_card hsub
  rw [card_neighborFinset_eq_degree, hz2, Finset.card_insert_of_notMem, Finset.card_pair hne]
    at hcard
  · omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨huw.ne, huw'.ne⟩

end commonNbr

/-! ### The leaf graph

For an edge `xy`, the leaf graph `apex (G − xy) {y}` replaces `xy` by a pendant edge `y ℓ`
(`ℓ = none`). By `leaf_merge`, a decomposition of it in which no path contains both `x` and `ℓ`
and with the right end counts gives one of `G` in which `xy` is the terminal edge at `x`
(`endEdge_of_leafSep`). In the leaf graph the terminal edge is a vertex-set property, so Fan's
lemma with vertex sets (`fan_single_supp`) carries it whenever the target is neither `x` nor `ℓ`.
-/

section leaf

omit [Fintype W] in
/-- `append_move`, recording exact supports: the extended path lies in the old one plus `u`,
and every other path has the vertex set of an old path. -/
theorem PathDecomp.append_move_exact {K K' : SimpleGraph W} (D : PathDecomp K) {t u : W}
    (hadj : ¬ K.Adj t u) (hK' : ∀ e, e ∈ K'.edgeSet ↔ e ∈ K.edgeSet ∨ e = s(t, u))
    {P : GPath K} (hP : P ∈ D.paths) (hend : P.src = t ∨ P.tgt = t)
    (hu : u ∉ P.walk.support) :
    ∃ D' : PathDecomp K',
      (∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if u = w then 1 else 0)) ∧
      ∀ Q' ∈ D'.paths, (∀ x ∈ Q'.walk.support, x ∈ P.walk.support ∨ x = u) ∨
        ∃ Q ∈ D.paths, Q'.walk.support = Q.walk.support := by
  obtain ⟨Q, hQs, hQe, hQends, hQsupp⟩ := P.exists_orient hend
  have hQK : ∀ e ∈ Q.walk.edges, e ∈ K'.edgeSet := fun e he =>
    (hK' e).2 (Or.inl (Q.walk.edges_subset_edgeSet he))
  have hs : s(u, Q.src) = s(t, u) := by rw [hQs, Sym2.eq_swap]
  have hut : K'.Adj u Q.src := by
    rw [← mem_edgeSet, hK', hs]; exact Or.inr rfl
  have huQ : u ∉ Q.walk.support := fun h => hu ((hQsupp u).1 h)
  let P' : GPath K' :=
    ⟨u, Q.tgt, Walk.cons hut (Q.walk.transfer K' hQK),
      by
        rw [Walk.cons_isPath_iff]
        exact ⟨by simpa using Q.isPath, by simpa using huQ⟩,
      by simp⟩
  have hP'e : P'.edges = s(t, u) :: Q.edges := by
    show (Walk.cons hut (Q.walk.transfer K' hQK)).edges = _
    rw [Walk.edges_cons, Walk.edges_transfer, hs]
    rfl
  have hPK : ∀ e ∈ P.edges, e ∈ K.edgeSet := fun e he => P.walk.edges_subset_edgeSet he
  have htuK : s(t, u) ∉ K.edgeSet := hadj
  obtain ⟨D', -, -, hends, -, hcovr⟩ := D.replace_supp hP P' (by
      intro e
      rw [hK' e, hP'e, List.mem_cons, hQe.mem_iff]
      constructor
      · rintro (h | h)
        · by_cases heP : e ∈ P.edges
          · exact Or.inr (Or.inr heP)
          · exact Or.inl ⟨h, heP⟩
        · exact Or.inr (Or.inl h)
      · rintro (⟨h, -⟩ | h | h)
        · exact Or.inl h
        · exact Or.inr h
        · exact Or.inl (hPK e h))
    (by
      intro e he
      rw [hP'e, List.mem_cons, hQe.mem_iff] at he
      rcases he with rfl | he
      · exact Or.inr htuK
      · exact Or.inl he)
  refine ⟨D', fun w => ?_, fun Q' hQ' => ?_⟩
  · have h1 := hends w
    have h2 : P'.endsAt w = (if u = w then 1 else 0) + (if Q.tgt = w then 1 else 0) := rfl
    have h3 : P.endsAt w = (if t = w then 1 else 0) + (if Q.tgt = w then 1 else 0) := by
      rw [← hQends]; simp only [GPath.endsAt, hQs]
    omega
  · rcases hcovr Q' hQ' with rfl | ⟨Q₀, hQ₀, -, -, hs₀⟩
    · refine Or.inl fun x hx => ?_
      have : x ∈ (Walk.cons hut (Q.walk.transfer K' hQK)).support := hx
      rw [Walk.support_cons, Walk.support_transfer, List.mem_cons] at this
      rcases this with rfl | h
      · exact Or.inr rfl
      · exact Or.inl ((hQsupp x).1 h)
    · exact Or.inr ⟨Q₀, hQ₀, hs₀⟩

omit [Fintype W] [DecidableEq W] in
/-- Edges of `apex K ∅` are the images of edges of `K`. -/
theorem apex_empty_edge_iff {K : SimpleGraph W} (e : Sym2 (Option W)) :
    e ∈ (apex K ∅).edgeSet ↔ ∃ e₀ ∈ K.edgeSet, e₀.map some = e := by
  induction e using Sym2.inductionOn with
  | hf a b =>
    rw [mem_edgeSet]
    cases a with
    | none =>
      cases b with
      | none =>
        simp only [apex_not_adj_none_none, false_iff, not_exists, not_and]
        intro e₀ _ h
        induction e₀ using Sym2.inductionOn with
        | hf c d => simp [Sym2.map_mk] at h
      | some b =>
        simp only [apex_adj_none_some, Finset.notMem_empty, false_iff, not_exists, not_and]
        intro e₀ _ h
        induction e₀ using Sym2.inductionOn with
        | hf c d =>
          simp only [Sym2.map_mk, Sym2.eq_iff] at h
          rcases h with ⟨h, -⟩ | ⟨-, h⟩ <;> exact Option.some_ne_none _ h
    | some a =>
      cases b with
      | none =>
        simp only [apex_adj_some_none, Finset.notMem_empty, false_iff, not_exists, not_and]
        intro e₀ _ h
        induction e₀ using Sym2.inductionOn with
        | hf c d =>
          simp only [Sym2.map_mk, Sym2.eq_iff] at h
          rcases h with ⟨-, h⟩ | ⟨h, -⟩ <;> exact Option.some_ne_none _ h
      | some b =>
        rw [apex_adj_some_some]
        constructor
        · intro h; exact ⟨s(a, b), h, rfl⟩
        · rintro ⟨e₀, he₀, h⟩
          induction e₀ using Sym2.inductionOn with
          | hf c d =>
            simp only [Sym2.map_mk, Sym2.eq_iff, Option.some.injEq] at h
            rw [mem_edgeSet] at he₀
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact he₀
            · exact he₀.symm

omit [Fintype W] [DecidableEq W] in
/-- Edges of `apex K {r}`: those of `apex K ∅` and the leaf edge. -/
theorem apex_single_edge_iff {K : SimpleGraph W} (r : W) (e : Sym2 (Option W)) :
    e ∈ (apex K {r}).edgeSet ↔ e ∈ (apex K ∅).edgeSet ∨ e = s(some r, none) := by
  induction e using Sym2.inductionOn with
  | hf a b =>
    rw [mem_edgeSet, mem_edgeSet]
    cases a with
    | none =>
      cases b with
      | none => simp
      | some b =>
        simp only [apex_adj_none_some, Finset.mem_singleton, Finset.notMem_empty, false_or,
          Sym2.eq_iff, reduceCtorEq, false_and, Option.some.injEq, true_and]
    | some a =>
      cases b with
      | none =>
        simp only [apex_adj_some_none, Finset.mem_singleton, Finset.notMem_empty, false_or,
          Sym2.eq_iff, Option.some.injEq, and_true, reduceCtorEq, and_false, or_false]
      | some b =>
        simp only [apex_adj_some_some, Sym2.eq_iff, reduceCtorEq, and_false, false_and,
          or_self, or_false]

omit [Fintype W] in
/-- **Lifting into the leaf graph.** A decomposition of `K` with a path `P` ending at `r` gives one
of `apex K {r}` in which `P` is extended by the leaf edge: the end at `r` moves to the leaf, and
every path either lies in `P` plus the leaf or has the vertex set of an old path. -/
theorem PathDecomp.liftLeaf {K : SimpleGraph W} (D : PathDecomp K) {r : W} {P : GPath K}
    (hP : P ∈ D.paths) (hend : P.src = r ∨ P.tgt = r) :
    ∃ D' : PathDecomp (apex K {r}),
      (∀ w, D'.ends (some w) + (if w = r then 1 else 0) = D.ends w) ∧ D'.ends none = 1 ∧
      ∀ Q' ∈ D'.paths, (∀ x ∈ Q'.walk.support, x = none ∨ ∃ y ∈ P.walk.support, x = some y) ∨
        ∃ Q ∈ D.paths, Q'.walk.support = Q.walk.support.map some := by
  have hE : ∀ e ∈ K.edgeSet, e.map some ∈ (apex K ∅).edgeSet := fun e he =>
    (apex_empty_edge_iff _).2 ⟨e, he, rfl⟩
  have hEinj : ∀ e₁ ∈ K.edgeSet, ∀ e₂ ∈ K.edgeSet, e₁.map some = e₂.map some → e₁ = e₂ :=
    fun e₁ _ e₂ _ h => Sym2.map.injective (Option.some_injective W) h
  have hcov : ∀ e' ∈ (apex K ∅).edgeSet, ∃ e ∈ K.edgeSet, e.map some = e' := fun e' he' =>
    (apex_empty_edge_iff e').1 he'
  have hinj : ∀ P ∈ D.paths, ∀ x ∈ P.walk.support, ∀ y ∈ P.walk.support,
      (some x : Option W) = some y → x = y := fun _ _ _ _ _ _ h => Option.some_injective W h
  let D₀ := D.pushOn some hE hEinj hcov hinj
  have hD₀some : ∀ w, D₀.ends (some w) = D.ends w := by
    intro w
    rw [PathDecomp.pushOn_ends D some hE hEinj hcov hinj (some w) (fun P => P.endsAt w)
      (fun P _ => by simp [GPath.endsAt])]
    rfl
  have hD₀none : D₀.ends none = 0 := by
    rw [PathDecomp.pushOn_ends D some hE hEinj hcov hinj none (fun _ => 0)
      (fun P _ => by simp)]
    simp
  let P₀ := P.pushOn some hE (hinj P hP)
  have hP₀ : P₀ ∈ D₀.paths := PathDecomp.pushOn_mem.2 ⟨P, hP, rfl⟩
  have hP₀end : P₀.src = some r ∨ P₀.tgt = some r := by
    rcases hend with h | h
    · left; simp [P₀, h]
    · right; simp [P₀, h]
  have hP₀supp : P₀.walk.support = P.walk.support.map some :=
    GPath.pushOn_support some hE P (hinj P hP)
  have hnone : (none : Option W) ∉ P₀.walk.support := by
    rw [hP₀supp, List.mem_map]
    rintro ⟨_, _, h⟩
    exact Option.some_ne_none _ h
  obtain ⟨D', hends, hcov'⟩ := D₀.append_move_exact (K' := apex K {r}) (t := some r)
    (u := none) (by simp) (apex_single_edge_iff r) hP₀ hP₀end hnone
  refine ⟨D', fun w => ?_, ?_, fun Q' hQ' => ?_⟩
  · have := hends (some w)
    rw [hD₀some] at this
    simp only [Option.some.injEq, reduceCtorEq, ite_false, add_zero] at this
    rw [← this]
    by_cases hw : w = r
    · subst hw; simp
    · simp [Ne.symm hw, hw]
  · have := hends none
    rw [hD₀none] at this
    simpa using this
  · rcases hcov' Q' hQ' with h | ⟨Q₀, hQ₀, hs⟩
    · refine Or.inl fun x hx => ?_
      rcases h x hx with h | h
      · rw [hP₀supp, List.mem_map] at h
        obtain ⟨y, hy, rfl⟩ := h
        exact Or.inr ⟨y, hy, rfl⟩
      · exact Or.inl h
    · obtain ⟨Q, hQ, rfl⟩ := PathDecomp.pushOn_mem.1 hQ₀
      exact Or.inr ⟨Q, hQ, by rw [hs]; exact GPath.pushOn_support some hE Q (hinj Q hQ)⟩

/-- **From the leaf graph back to `G`.** Let `xy` be an edge with `deg x` odd. A decomposition of
the leaf graph `apex (G − xy) {y}` with `ends = deg mod 2` in which no path contains both `x` and
the leaf gives a Lovász decomposition of `G` whose path ending at `x` contains `xy`. -/
theorem endEdge_of_leafSep (G : SimpleGraph W) [DecidableRel G.Adj] {x y : W} (hxy : G.Adj x y)
    (hx : G.degree x % 2 = 1) (DH : PathDecomp (apex (delEdge G y x) {y}))
    (hDH : ∀ v, DH.ends v = (apex (delEdge G y x) {y}).degree v % 2)
    (hsep : Separates DH (some x) none) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∃ P ∈ D.paths, (P.src = x ∨ P.tgt = x) ∧ s(x, y) ∈ P.edges := by
  classical
  have hxy' : x ≠ y := hxy.ne
  have hdeg := delEdge_degree G hxy.symm
  have hHnone : (apex (delEdge G y x) {y}).degree none = 1 := by rw [apex_degree_none]; simp
  have hHsome : ∀ v, (apex (delEdge G y x) {y}).degree (some v) =
      (delEdge G y x).degree v + if v = y then 1 else 0 := by
    intro v; rw [apex_degree_some]; simp [Finset.mem_singleton]
  obtain ⟨D, hDx, hDw, -, hfwd⟩ := leaf_merge G hxy DH hsep
  refine ⟨D, fun v => ?_, ?_⟩
  · by_cases hvx : v = x
    · subst hvx
      rw [hDx, hDH, hDH, hHnone, hHsome]
      have := hdeg v
      simp only [hxy', ite_true, ite_false, add_zero] at this ⊢
      omega
    · rw [hDw v hvx, hDH, hHsome]
      have := hdeg v
      by_cases hvy : v = y
      · subst hvy
        simp only [hvx, ite_true, ite_false, add_zero] at this ⊢
        rw [this]
      · simp only [hvx, hvy, ite_false, add_zero] at this ⊢
        rw [this]
  · have hpos : 0 < DH.ends none := by rw [hDH, hHnone]; omega
    obtain ⟨P, hP, hPend⟩ := DH.exists_end_of_pos hpos
    obtain ⟨Q, hQ, hQs, hQt, hQe⟩ := hfwd P hP
    have hleaf : s(some y, none) ∈ P.edges := by
      have key : ∀ e ∈ P.edges, (none : Option W) ∈ e → s(some y, none) ∈ P.edges := by
        intro e he hne
        have heH := P.walk.edges_subset_edgeSet he
        rw [apex_none_pendant e heH hne, Sym2.eq_swap] at he
        exact he
      rcases hPend with h | h
      · obtain ⟨e, he, hx⟩ := P.exists_edge_at_src
        exact key e he (h ▸ hx)
      · obtain ⟨e, he, hx⟩ := P.exists_edge_at_tgt
        exact key e he (h ▸ hx)
    refine ⟨Q, hQ, ?_, ?_⟩
    · rcases hPend with h | h
      · left; rw [hQs, h, mergeMap_none]
      · right; rw [hQt, h, mergeMap_none]
    · rw [hQe, List.mem_map]
      exact ⟨_, hleaf, by simp [Sym2.map_mk, Sym2.eq_swap]⟩

end leaf

/-! ### Edges at a neighbour of the even vertex -/

section adjEven

/-- **Prescribed end edge at a neighbour of the even vertex.** Let `z` be the only vertex of
positive even degree, let `y ∈ N(z)`, and let `xy` be an edge with `x ≠ z` (so `deg x` is odd).
If `x` and `y` have at most one common neighbour other than `z`, then some Lovász decomposition
of `G` has its path ending at `x` through `xy`.

Proof: in `G − zy` the vertex `y` is the only even vertex, and `sep_atMostOneCommon` separates
`x` from `y` in `G − zy − xy`. Lift to the leaf graph by appending the leaf edge `yℓ` to the path
ending at `y`; then no path contains `x` and `ℓ`. Restore `zy` by Fan's lemma with target `y`
(no neighbour of `y` lacks an end), which keeps the separation of `x` and `ℓ`; merge `ℓ` into
`x` (`endEdge_of_leafSep`). -/
theorem pee_adjEven (G : SimpleGraph W) [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1)
    {z x y : W} (hz : z ∈ evenSet G) (hzy : G.Adj z y) (hxy : G.Adj x y) (hxz : x ≠ z)
    (hcom : ∀ w w', G.Adj x w → G.Adj w y → w ≠ z → G.Adj x w' → G.Adj w' y → w' ≠ z → w = w') :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∃ P ∈ D.paths, (P.src = x ∨ P.tgt = x) ∧ s(x, y) ∈ P.edges := by
  classical
  have hxy' : x ≠ y := hxy.ne
  have hyz : y ≠ z := hzy.ne.symm
  have huniq : ∀ v ∈ evenSet G, v = z := fun v hv => Finset.card_le_one.mp hev v hv z hz
  have hodd : ∀ v, v ≠ z → 0 < G.degree v → G.degree v % 2 = 1 := by
    intro v hvz hpos
    have : v ∉ evenSet G := fun h => hvz (huniq v h)
    rw [mem_evenSet_iff] at this
    omega
  have hzd := mem_evenSet_iff.mp hz
  -- `G₁ = G − zy`: there `y` is the only even vertex
  obtain ⟨hsub₁, -, hrest₁⟩ := delEdge_even_facts hev hz hzy
  have hd₁ := delEdge_degree G hzy.symm
  have hdy : 2 ≤ G.degree y := by
    have hsub2 : ({z, x} : Finset W) ⊆ G.neighborFinset y := by
      intro v hv
      rw [Finset.mem_insert, Finset.mem_singleton] at hv
      rw [mem_neighborFinset]
      rcases hv with rfl | rfl
      · exact hzy.symm
      · exact hxy.symm
    have := Finset.card_le_card hsub2
    rw [card_neighborFinset_eq_degree, Finset.card_pair (Ne.symm hxz)] at this
    exact this
  have hyodd := hodd y hyz (by omega)
  have hy₁ : y ∈ evenSet (delEdge G y z) := by
    rw [mem_evenSet_iff]
    have := hd₁ y
    simp only [hyz, ite_true, ite_false, add_zero] at this
    omega
  have hev₁ : (evenSet (delEdge G y z)).card ≤ 1 := (Finset.card_le_card hsub₁).trans (by simp)
  have h₁yx : (delEdge G y z).Adj y x := ⟨hxy.symm, fun h => by
    rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h, -⟩
    · exact hxz h
    · exact hyz h⟩
  have hcom₁ : ∀ w w', (delEdge G y z).Adj x w → (delEdge G y z).Adj w y →
      (delEdge G y z).Adj x w' → (delEdge G y z).Adj w' y → w = w' := by
    intro w w' hxw hwy hxw' hw'y
    have hwz : w ≠ z := fun h => hwy.2 (by rw [h, Sym2.eq_swap])
    have hw'z : w' ≠ z := fun h => hw'y.2 (by rw [h, Sym2.eq_swap])
    exact hcom w w' hxw.1 hwy.1 hwz hxw'.1 hw'y.1 hw'z
  obtain ⟨D₂, hD₂, hsep₂⟩ := sep_atMostOneCommon (delEdge G y z) hev₁ hy₁ h₁yx hcom₁
  -- degrees in `G₂ = G − zy − xy`
  have hd₂ := delEdge_degree (delEdge G y z) h₁yx.symm
  have hdeg₂ : ∀ v, (delEdge (delEdge G y z) x y).degree v + (if v = x then 1 else 0) +
      2 * (if v = y then 1 else 0) + (if v = z then 1 else 0) = G.degree v := by
    intro v
    have h1 := hd₁ v
    have h2 := hd₂ v
    by_cases hvy : v = y
    · subst hvy
      simp only [hxy'.symm, hyz, ite_true, ite_false] at h1 h2 ⊢
      omega
    · simp only [hvy, ite_false] at h1 h2 ⊢
      omega
  -- the path ending at `y`
  have hD₂y : D₂.ends y = 1 := by
    rw [hD₂]
    have := hdeg₂ y
    simp only [hxy'.symm, hyz, ite_true, ite_false] at this
    omega
  obtain ⟨P, hP, hPend⟩ := D₂.exists_end_of_pos (by rw [hD₂y]; omega)
  have hyP : y ∈ P.walk.support := by
    have hmem : ∀ v, (P.src = v ∨ P.tgt = v) → v ∈ P.walk.support := by
      rintro v (h | h)
      · rw [← h]; exact P.walk.start_mem_support
      · rw [← h]; exact P.walk.end_mem_support
    exact hmem y hPend
  obtain ⟨D₃, hD₃some, hD₃none, hD₃cov⟩ := D₂.liftLeaf hP hPend
  have hsep₃ : Separates D₃ (some x) none := by
    intro Q' hQ' ⟨hx, hn⟩
    rcases hD₃cov Q' hQ' with h | ⟨Q, hQ, hs⟩
    · rcases h (some x) hx with h | ⟨y', hy', h⟩
      · exact Option.some_ne_none _ h
      · rw [Option.some.injEq] at h
        subst h
        exact hsep₂ P hP ⟨hy', hyP⟩
    · rw [hs, List.mem_map] at hn
      obtain ⟨_, _, h⟩ := hn
      exact Option.some_ne_none _ h
  -- Fan's lemma in the leaf graph: restore `zy`, moving the end at `z` to `y`
  have hHyz : (apex (delEdge G y x) {y}).Adj (some y) (some z) := by
    rw [apex_adj_some_some]
    refine ⟨hzy.symm, fun h => ?_⟩
    rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h, -⟩
    · exact hxz h.symm
    · exact hxy' h.symm
  have hedges : ∀ e, e ∈ (apex (delEdge (delEdge G y z) x y) {y}).edgeSet ↔
      e ∈ (apex (delEdge G y x) {y}).edgeSet ∧ e ≠ s(some y, some z) := by
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
            refine ⟨⟨hab, fun h => h2 ?_⟩, fun h => h1 ?_⟩
            · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · right; exact ⟨rfl, rfl⟩
              · left; exact ⟨rfl, rfl⟩
            · exact h
          · rintro ⟨⟨hab, h1⟩, h2⟩
            refine ⟨⟨hab, fun h => h2 h⟩, fun h => h1 ?_⟩
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · right; exact ⟨rfl, rfl⟩
            · left; exact ⟨rfl, rfl⟩
  have hcount : (Finset.univ.filter (fun v => (apex (delEdge (delEdge G y z) x y) {y}).Adj
      (some y) v ∧ D₃.ends v = 0)).card < D₃.ends (some z) := by
    have hz₃ : D₃.ends (some z) = 1 := by
      have := hD₃some z
      simp only [hyz.symm, ite_false, add_zero] at this
      rw [this, hD₂]
      have := hdeg₂ z
      simp only [hxz.symm, hyz.symm, ite_true, ite_false] at this
      omega
    have hempty : Finset.univ.filter (fun v => (apex (delEdge (delEdge G y z) x y) {y}).Adj
        (some y) v ∧ D₃.ends v = 0) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
      rw [Finset.mem_filter] at hv
      obtain ⟨-, hadj, h0⟩ := hv
      cases v with
      | none => rw [hD₃none] at h0; exact one_ne_zero h0
      | some v =>
        rw [apex_adj_some_some] at hadj
        have hvy : v ≠ y := hadj.ne.symm
        have hvx : v ≠ x := fun h => hadj.2 (by rw [h, Sym2.eq_swap])
        have hvz : v ≠ z := fun h => hadj.1.2 (by rw [h])
        have := hD₃some v
        simp only [hvy, ite_false, add_zero] at this
        rw [this, hD₂] at h0
        have hdv := hdeg₂ v
        simp only [hvx, hvy, hvz, ite_false, add_zero, mul_zero] at hdv
        have hpos : 0 < G.degree v := (G.degree_pos_iff_exists_adj v).mpr ⟨y, hadj.1.1.symm⟩
        have := hodd v hvz hpos
        omega
    rw [hempty, Finset.card_empty, hz₃]
    omega
  obtain ⟨DH, -, hDHy, hDHz, hDHrest, hcovH⟩ :=
    fan_single_supp (G := apex (delEdge G y x) {y}) hHyz hedges D₃ hcount
  have hsepH : Separates DH (some x) none :=
    separates_of_cover (g := some y) (by simp [hxy'.symm]) (by simp) hsep₃ hcovH
  have hHdeg : ∀ v, (apex (delEdge G y x) {y}).degree (some v) +
      (if v = x then 1 else 0) = G.degree v := by
    intro v
    rw [apex_degree_some]
    have := delEdge_degree G hxy.symm v
    by_cases hvy : v = y
    · subst hvy; simp only [Finset.mem_singleton, hxy'.symm, ite_true, ite_false] at this ⊢; omega
    · simp only [Finset.mem_singleton, hvy, ite_false, add_zero] at this ⊢; omega
  have hDH : ∀ v, DH.ends v = (apex (delEdge G y x) {y}).degree v % 2 := by
    intro v
    cases v with
    | none =>
      rw [hDHrest none (by simp) (by simp), hD₃none, apex_degree_none]
      simp
    | some v =>
      have hH := hHdeg v
      have hS := hD₃some v
      have hdv := hdeg₂ v
      rw [hD₂] at hS
      by_cases hvy : v = y
      · subst hvy
        simp only [hxy'.symm, hyz, ite_true, ite_false] at hH hS hdv
        rw [hDHy]
        omega
      · by_cases hvz : v = z
        · subst hvz
          simp only [hxz.symm, hyz.symm, ite_true, ite_false] at hH hS hdv
          have := hDHz
          omega
        · rw [hDHrest (some v) (by simp [hvy]) (by simp [hvz])]
          by_cases hvx : v = x
          · subst hvx
            simp only [hxy', hxz, ite_true, ite_false] at hH hS hdv
            have := hodd v hxz (by omega)
            omega
          · simp only [hvx, hvy, hvz, ite_false, add_zero, mul_zero] at hH hS hdv
            omega
  have hxodd : G.degree x % 2 = 1 :=
    hodd x hxz ((G.degree_pos_iff_exists_adj x).mpr ⟨y, hxy⟩)
  exact endEdge_of_leafSep G hxy hxodd DH hDH hsepH

end adjEven

end Gallai
