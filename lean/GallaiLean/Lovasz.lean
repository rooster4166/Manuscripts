import GallaiLean.Fan

/-!
# Lovász's theorem (1968)

**Theorem.** A finite simple graph `G` on `N` vertices with at most one vertex of even degree
(isolated vertices count as even) can be decomposed into at most `⌊N/2⌋` paths.

We prove the following stronger statement (`lovasz_ends`).

> If at most one vertex of `G` has *positive* even degree, then `G` has a path decomposition
> `D` with `ends_D(v) = deg(v) mod 2` for every vertex `v`.

Such a `D` has `#odd / 2 ≤ ⌊N/2⌋` paths, which gives `LovaszStatement`.

## Proof

Strong induction on `ν(G) = ∑_v deg(v) + [G has no vertex of positive even degree]`. Write
`b = ends_D` and `G' = G − ux` for the graph with one edge removed. Two facts are used
throughout. In `G'` only the degrees of `u` and `x` drop, each by one. A vertex of positive
degree that is not the exceptional even vertex has odd degree.

**Case I** (some vertex `z` has positive even degree). Pick a neighbour `u` of `z` and set
`G' = G − uz`. In `G'` the vertex `z` is odd. The vertex `u` was odd in `G`, so in `G'` it is
even or isolated, and every other vertex keeps its parity. Hence `u` is the only possible
positive-even vertex of `G'`, and `ν(G') < ν(G)`. By induction, `G'` has a decomposition `D'`
with `b' = deg' mod 2`, so `b'(u) = 0` and `b'(z) = 1`. Every neighbour of `u` in `G'` has
positive degree and is not `u`, so it is odd and has an end. Hence
`#{w ∈ N_{G'}(u) : b'(w) = 0} = 0 < 1 = b'(z)`. Fan's lemma (`fan_single`) adds `uz` while
moving an end from `z` to `u`. This gives `b(u) = 1`, `b(z) = 0`, and the other ends
unchanged.

**Case II** (every vertex of positive degree is odd, and some `x` has `deg(x) ≥ 3`). Pick a
neighbour `u` of `x`. Let `H` be `G − ux` plus a new leaf at `u` (`apex (G − ux) {u}`). Then
`H` has the same number of edges and exactly one positive-even vertex, namely `x` (of degree
`deg(x) − 1 ≥ 2`). So `ν(H) = ν(G) − 1`. Induction gives `D_H` with `b_H = deg_H mod 2`. The
leaf has degree 1, so it is an end of its path. Deleting it (`Retract.delete`) gives a
decomposition `D'` of `G' = G − ux` with `b'(w) = deg'(w) mod 2` for `w ≠ u`, and with
`b'(u) ≤ 2` and `b'(u)` even, i.e. `b'(u) ∈ {0, 2}`.
* If `b'(u) = 0`, add `ux` as a new one-edge path. Then `b(u) = 1` and `b(x) = 0 + 1 = 1`.
* If `b'(u) = 2`, no neighbour of `x` in `G'` has zero ends. The vertex `u` has two, and every
  other neighbour is odd. So `0 < 2 = b'(u)`, and Fan's lemma adds `ux` while moving an end
  from `u` to `x`.

**Case III** (every positive degree is `1`, and some edge `ux` exists). `G − ux` has no
positive-even vertex and two fewer degree units. Apply induction and add `ux` as a new path.

**Case IV** (no edges). Every decomposition is empty, and all degrees are `0`.
-/

open SimpleGraph

namespace Gallai

universe u

/-! ### Deleting one edge -/

section delEdge

variable {W : Type u} (G : SimpleGraph W)

/-- `G` with the edge `ab` removed. -/
def delEdge (a b : W) : SimpleGraph W where
  Adj x y := G.Adj x y ∧ ¬ s(x, y) = s(a, b)
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩

instance delEdge.decRel [DecidableEq W] [DecidableRel G.Adj] (a b : W) :
    DecidableRel (G.delEdge a b).Adj := fun x y =>
  inferInstanceAs (Decidable (G.Adj x y ∧ ¬ s(x, y) = s(a, b)))

theorem delEdge_edgeSet (a b : W) :
    ∀ e, e ∈ (G.delEdge a b).edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(a, b) := by
  intro e
  induction e using Sym2.inductionOn with
  | hf x y => exact Iff.rfl

variable [Fintype W] [DecidableEq W] [DecidableRel G.Adj]

theorem delEdge_degree {a b : W} (hab : G.Adj a b) (w : W) :
    (G.delEdge a b).degree w + (if w = a then 1 else 0) + (if w = b then 1 else 0) =
      G.degree w := by
  have hne : a ≠ b := hab.ne
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree, neighborFinset_eq_filter,
    neighborFinset_eq_filter (G := G), Finset.card_filter, Finset.card_filter]
  have hy : ∀ y, (if G.Adj w y then 1 else 0) =
      (if (G.delEdge a b).Adj w y then 1 else 0) +
        (if (w = a ∧ y = b) ∨ (w = b ∧ y = a) then 1 else 0) := by
    intro y
    have hiff : (G.delEdge a b).Adj w y ↔ G.Adj w y ∧ ¬ ((w = a ∧ y = b) ∨ (w = b ∧ y = a)) := by
      show G.Adj w y ∧ ¬ s(w, y) = s(a, b) ↔ _
      rw [Sym2.eq_iff]
    by_cases h1 : (w = a ∧ y = b) ∨ (w = b ∧ y = a)
    · have hadj : G.Adj w y := by
        rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hab
        · exact hab.symm
      have h3 : ¬ (G.delEdge a b).Adj w y := fun h => (hiff.mp h).2 h1
      simp only [hadj, h1, h3, ite_true, ite_false, zero_add]
    · by_cases hadj : G.Adj w y
      · have h3 : (G.delEdge a b).Adj w y := hiff.mpr ⟨hadj, h1⟩
        simp only [hadj, h1, h3, ite_true, ite_false, add_zero]
      · have h3 : ¬ (G.delEdge a b).Adj w y := fun h => hadj (hiff.mp h).1
        simp only [hadj, h1, h3, ite_false, add_zero]
  rw [Finset.sum_congr rfl (fun y _ => hy y), Finset.sum_add_distrib]
  by_cases hwa : w = a
  · subst hwa
    simp [hne]
  · by_cases hwb : w = b
    · subst hwb
      simp [hwa]
    · simp [hwa, hwb]

theorem delEdge_sum_degree {a b : W} (hab : G.Adj a b) :
    (∑ w, (G.delEdge a b).degree w) + 2 = ∑ w, G.degree w := by
  rw [← Finset.sum_congr rfl (fun w _ => delEdge_degree G hab w), Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  simp

end delEdge

/-! ### Adding one edge as a new path -/

theorem PathDecomp.add_edge {W : Type u} [DecidableEq W] {G G' : SimpleGraph W} {a b : W}
    (hab : G.Adj a b) (hG' : ∀ e, e ∈ G'.edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(a, b))
    (D' : PathDecomp G') :
    ∃ D : PathDecomp G, ∀ w,
      D.ends w = D'.ends w + (if a = w then 1 else 0) + (if b = w then 1 else 0) := by
  have h₁ : ∀ Q ∈ D'.paths, ∀ e ∈ Q.edges, e ∈ G.edgeSet := fun Q hQ e he =>
    ((hG' e).1 ((D'.covers e).2 (List.mem_flatMap.mpr ⟨Q, hQ, he⟩))).1
  let L := D'.paths.pmap (fun Q hQ => Q.transfer hQ) h₁ ++ [GPath.ofAdj hab]
  have hL : L.flatMap GPath.edges = D'.paths.flatMap GPath.edges ++ [s(a, b)] := by
    simp only [L, List.flatMap_append, flatMap_pmap_transfer, List.flatMap_cons,
      List.flatMap_nil, GPath.ofAdj_edges, List.append_nil]
  have hnd : (L.flatMap GPath.edges).Nodup := by
    rw [hL, List.nodup_append]
    refine ⟨D'.nodup_edges, List.nodup_singleton _, ?_⟩
    intro e he f hf hef
    rw [List.mem_singleton] at hf
    subst hf hef
    exact ((hG' _).1 ((D'.covers _).2 he)).2 rfl
  have hcov : ∀ e, e ∈ G.edgeSet ↔ e ∈ L.flatMap GPath.edges := by
    intro e
    rw [hL, List.mem_append, List.mem_singleton, ← D'.covers, hG']
    constructor
    · intro he
      by_cases h : e = s(a, b)
      · exact Or.inr h
      · exact Or.inl ⟨he, h⟩
    · rintro (⟨he, -⟩ | rfl)
      · exact he
      · exact hab
  refine ⟨⟨L, hnd, hcov⟩, fun w => ?_⟩
  unfold PathDecomp.ends
  simp only [L, List.map_append, List.sum_append, sum_endsAt_pmap_transfer, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have : (GPath.ofAdj hab).endsAt w = (if a = w then 1 else 0) + (if b = w then 1 else 0) := rfl
  rw [this]
  omega

/-! ### The induction -/

section induction

variable {W : Type u} [Fintype W] [DecidableEq W]

theorem mem_evenSet_iff {G : SimpleGraph W} [DecidableRel G.Adj] {w : W} :
    w ∈ evenSet G ↔ 0 < G.degree w ∧ G.degree w % 2 = 0 := by
  simp [evenSet, Nat.even_iff]

omit [Fintype W] [DecidableEq W] in
theorem apex_none_pendant {G : SimpleGraph W} {r : W} :
    ∀ e ∈ (apex G {r}).edgeSet, (none : Option W) ∈ e → e = s(none, some r) := by
  intro e he hne
  induction e using Sym2.inductionOn with
  | hf a b =>
  rw [mem_edgeSet] at he
  rcases Sym2.mem_iff.mp hne with rfl | rfl
  · cases b with
    | none => exact absurd he apex_not_adj_none_none
    | some c =>
      rw [apex_adj_none_some, Finset.mem_singleton] at he
      rw [he]
  · cases a with
    | none => exact absurd he apex_not_adj_none_none
    | some c =>
      rw [apex_adj_some_none, Finset.mem_singleton] at he
      rw [he, Sym2.eq_swap]

/-- The statement proved by strong induction on `n = ν(G)`. -/
def LovaszStrong (n : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    (evenSet G).card ≤ 1 →
    (∑ w, G.degree w) + (if (evenSet G).card = 0 then 1 else 0) = n →
    ∃ D : PathDecomp G, ∀ v, D.ends v = G.degree v % 2

/-- Case I: there is a vertex of positive even degree. -/
theorem lovasz_case_even {n : ℕ} (ih : ∀ m < n, LovaszStrong.{u} m)
    (G : SimpleGraph W) [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1)
    (hn : (∑ w, G.degree w) + (if (evenSet G).card = 0 then 1 else 0) = n)
    {z : W} (hz : z ∈ evenSet G) :
    ∃ D : PathDecomp G, ∀ v, D.ends v = G.degree v % 2 := by
  have hzd := mem_evenSet_iff.mp hz
  obtain ⟨u, hzu⟩ := (G.degree_pos_iff_exists_adj z).mp hzd.1
  have huz : G.Adj u z := hzu.symm
  have hne : u ≠ z := huz.ne
  have huniq : ∀ w ∈ evenSet G, w = z := fun w hw => Finset.card_le_one.mp hev w hw z hz
  have hdeg := delEdge_degree G huz
  have hupos : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).mpr ⟨z, huz⟩
  have huodd : G.degree u % 2 = 1 := by
    have : u ∉ evenSet G := fun h => hne (huniq u h)
    rw [mem_evenSet_iff] at this
    omega
  have hdu := hdeg u
  have hdz := hdeg z
  simp only [hne, hne.symm, ite_true, ite_false, add_zero] at hdu hdz
  have hev' : evenSet (G.delEdge u z) ⊆ {u} := by
    intro w hw
    rw [Finset.mem_singleton]
    obtain ⟨hpos, heven⟩ := mem_evenSet_iff.mp hw
    by_contra hwu
    by_cases hwz : w = z
    · subst hwz
      omega
    · have h := hdeg w
      simp only [hwu, hwz, ite_false, add_zero] at h
      exact hwz (huniq w (mem_evenSet_iff.mpr ⟨h ▸ hpos, h ▸ heven⟩))
  have hcard' : (evenSet (G.delEdge u z)).card ≤ 1 :=
    (Finset.card_le_card hev').trans (by simp)
  have hsum := delEdge_sum_degree G huz
  have hlt : (∑ w, (G.delEdge u z).degree w) +
      (if (evenSet (G.delEdge u z)).card = 0 then 1 else 0) < n := by
    have : (evenSet G).card ≠ 0 := Finset.card_ne_zero.mpr ⟨z, hz⟩
    simp only [this, ite_false, add_zero] at hn
    split_ifs <;> omega
  obtain ⟨D', hD'⟩ := ih _ hlt W (G.delEdge u z) hcard' rfl
  have hD'z : D'.ends z = 1 := by rw [hD' z]; omega
  obtain ⟨D, -, hDu, hDz, hDo⟩ := fan_single huz (delEdge_edgeSet G u z) D' (by
    rw [hD'z]
    have : Finset.univ.filter (fun w => (G.delEdge u z).Adj u w ∧ D'.ends w = 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro w - ⟨hadj, h0⟩
      have hwu : w ≠ u := hadj.ne.symm
      have hpos : 0 < (G.delEdge u z).degree w :=
        ((G.delEdge u z).degree_pos_iff_exists_adj w).mpr ⟨u, hadj.symm⟩
      rw [hD' w] at h0
      exact hwu (Finset.mem_singleton.mp (hev' (mem_evenSet_iff.mpr ⟨hpos, h0⟩)))
    rw [this, Finset.card_empty]
    exact Nat.one_pos)
  refine ⟨D, fun w => ?_⟩
  by_cases hwu : w = u
  · subst hwu
    rw [hDu, hD' w]
    omega
  · by_cases hwz : w = z
    · subst hwz
      omega
    · rw [hDo w hwu hwz, hD' w]
      have h := hdeg w
      simp only [hwu, hwz, ite_false, add_zero] at h
      rw [h]

/-- Case II: every vertex of positive degree is odd and some vertex has degree `≥ 3`. -/
theorem lovasz_case_big {n : ℕ} (ih : ∀ m < n, LovaszStrong.{u} m)
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hn : (∑ w, G.degree w) + (if (evenSet G).card = 0 then 1 else 0) = n)
    (hnone : ∀ z, z ∉ evenSet G) {x : W} (hx : 3 ≤ G.degree x) :
    ∃ D : PathDecomp G, ∀ v, D.ends v = G.degree v % 2 := by
  obtain ⟨u, hxu⟩ := (G.degree_pos_iff_exists_adj x).mp (by omega)
  have hux : G.Adj u x := hxu.symm
  have hne : u ≠ x := hux.ne
  have hpar : ∀ w, 0 < G.degree w → G.degree w % 2 = 1 := fun w hw => by
    have := hnone w
    rw [mem_evenSet_iff] at this
    omega
  have hdeg := delEdge_degree G hux
  have hupos : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).mpr ⟨x, hux⟩
  have hdu := hdeg u
  have hdx := hdeg x
  simp only [hne, hne.symm, ite_true, ite_false, add_zero] at hdu hdx
  have hux_odd := hpar u hupos
  have hx_odd := hpar x (by omega)
  have hHsome : ∀ w, (apex (G.delEdge u x) {u}).degree (some w) =
      (G.delEdge u x).degree w + (if w = u then 1 else 0) := by
    intro w
    rw [apex_degree_some]
    simp [Finset.mem_singleton]
  have hHnone : (apex (G.delEdge u x) {u}).degree none = 1 := by
    rw [apex_degree_none]; simp
  have hevH : evenSet (apex (G.delEdge u x) {u}) ⊆ {some x} := by
    intro w hw
    rw [mem_evenSet_iff] at hw
    rw [Finset.mem_singleton]
    cases w with
    | none => rw [hHnone] at hw; omega
    | some y =>
      rw [hHsome] at hw
      by_contra hyx
      have hyx' : y ≠ x := fun h => hyx (h ▸ rfl)
      by_cases hyu : y = u
      · subst hyu
        simp only [ite_true] at hw
        omega
      · have h := hdeg y
        simp only [hyu, hyx', ite_false, add_zero] at h hw
        have := hpar y (h ▸ hw.1)
        omega
  have hxH : some x ∈ evenSet (apex (G.delEdge u x) {u}) := by
    rw [mem_evenSet_iff, hHsome]
    simp only [hne.symm, ite_false, add_zero]
    omega
  have hcardH : (evenSet (apex (G.delEdge u x) {u})).card ≤ 1 :=
    (Finset.card_le_card hevH).trans (by simp)
  have hsumH : ∑ w, (apex (G.delEdge u x) {u}).degree w = ∑ w, G.degree w := by
    rw [Fintype.sum_option, hHnone, ← delEdge_sum_degree G hux]
    simp only [hHsome, Finset.sum_add_distrib]
    simp
    omega
  have hlt : (∑ w, (apex (G.delEdge u x) {u}).degree w) +
      (if (evenSet (apex (G.delEdge u x) {u})).card = 0 then 1 else 0) < n := by
    have h1 : (evenSet (apex (G.delEdge u x) {u})).card ≠ 0 :=
      Finset.card_ne_zero.mpr ⟨_, hxH⟩
    have h2 : (evenSet G).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem hnone)
    simp only [h2, ite_true] at hn
    simp only [h1, ite_false, add_zero, hsumH]
    omega
  obtain ⟨DH, hDH⟩ := ih _ hlt (Option W) (apex (G.delEdge u x) {u}) hcardH rfl
  -- delete the new leaf
  obtain ⟨D', hD'⟩ := (apexRetract (G.delEdge u x) {u} x).delete DH (by
    intro P _ y hy hky
    cases y with
    | some _ => simp [apexRetract] at hky
    | none => exact (P.end_of_pendant apex_none_pendant hy).imp Eq.symm Eq.symm)
  have hD'w : ∀ w, w ≠ u → D'.ends w = (G.delEdge u x).degree w % 2 := by
    intro w hwu
    rw [(hD' w).1 (fun e he hk hwe => hwu (Finset.mem_singleton.mp (apex_nonkept he hk hwe).2))]
    change DH.ends (some w) = _
    rw [hDH, hHsome]
    simp [hwu]
  have hD'u : D'.ends u = 0 ∨ D'.ends u = 2 := by
    have hle := (hD' u).2 (fun e₁ he₁ e₂ he₂ hk₁ hk₂ hv₁ hv₂ => by
      rw [(apex_nonkept he₁ hk₁ hv₁).1, (apex_nonkept he₂ hk₂ hv₂).1])
    change D'.ends u ≤ DH.ends (some u) + 1 at hle
    rw [hDH, hHsome] at hle
    simp only [ite_true] at hle
    have hp := D'.ends_mod_two u
    omega
  rcases hD'u with h0 | h2
  · -- `u` has no end: add `ux` as a new path
    obtain ⟨D, hD⟩ := PathDecomp.add_edge hux (delEdge_edgeSet G u x) D'
    refine ⟨D, fun w => ?_⟩
    rw [hD w]
    by_cases hwu : w = u
    · subst hwu
      simp only [h0, hne, ite_true, ite_false]
      omega
    · rw [hD'w w hwu]
      by_cases hwx : w = x
      · subst hwx
        simp only [Ne.symm hwu, ite_true, ite_false]
        omega
      · have h := hdeg w
        simp only [hwu, hwx, Ne.symm hwu, Ne.symm hwx, ite_false, add_zero] at h ⊢
        rw [h]
  · -- `u` has two ends: Fan's transfer `u → x`
    have hG'x : ∀ e, e ∈ (G.delEdge u x).edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(x, u) := by
      intro e
      rw [delEdge_edgeSet, Sym2.eq_swap]
    obtain ⟨D, -, hDx, hDu, hDo⟩ := fan_single hxu hG'x D' (by
      rw [h2]
      have : Finset.univ.filter (fun w => (G.delEdge u x).Adj x w ∧ D'.ends w = 0) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        rintro w - ⟨hadj, h0⟩
        by_cases hwu : w = u
        · subst hwu; omega
        · have hwx : w ≠ x := hadj.ne.symm
          have hpos : 0 < (G.delEdge u x).degree w :=
            ((G.delEdge u x).degree_pos_iff_exists_adj w).mpr ⟨x, hadj.symm⟩
          have h := hdeg w
          simp only [hwu, hwx, ite_false, add_zero] at h
          rw [hD'w w hwu, h] at h0
          have := hpar w (h ▸ hpos)
          omega
      rw [this, Finset.card_empty]
      omega)
    refine ⟨D, fun w => ?_⟩
    by_cases hwx : w = x
    · subst hwx
      rw [hDx, hD'w w (Ne.symm hne)]
      omega
    · by_cases hwu : w = u
      · subst hwu
        omega
      · rw [hDo w hwx hwu, hD'w w hwu]
        have h := hdeg w
        simp only [hwu, hwx, ite_false, add_zero] at h
        rw [h]

/-- Case III: every positive degree is `1`. -/
theorem lovasz_case_matching {n : ℕ} (ih : ∀ m < n, LovaszStrong.{u} m)
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hn : (∑ w, G.degree w) + (if (evenSet G).card = 0 then 1 else 0) = n)
    (hnone : ∀ z, z ∉ evenSet G) (hsmall : ∀ x, G.degree x < 3) {u : W}
    (hu : 0 < G.degree u) :
    ∃ D : PathDecomp G, ∀ v, D.ends v = G.degree v % 2 := by
  obtain ⟨x, hux⟩ := (G.degree_pos_iff_exists_adj u).mp hu
  have hne : u ≠ x := hux.ne
  have hpar : ∀ w, 0 < G.degree w → G.degree w % 2 = 1 := fun w hw => by
    have := hnone w
    rw [mem_evenSet_iff] at this
    omega
  have hxpos : 0 < G.degree x := (G.degree_pos_iff_exists_adj x).mpr ⟨u, hux.symm⟩
  have hdu1 : G.degree u = 1 := by have := hpar u hu; have := hsmall u; omega
  have hdx1 : G.degree x = 1 := by have := hpar x hxpos; have := hsmall x; omega
  have hdeg := delEdge_degree G hux
  have hdu := hdeg u
  have hdx := hdeg x
  simp only [hne, hne.symm, ite_true, ite_false, add_zero] at hdu hdx
  have hev' : evenSet (G.delEdge u x) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro w hw
    obtain ⟨hpos, heven⟩ := mem_evenSet_iff.mp hw
    by_cases hwu : w = u
    · subst hwu; omega
    · by_cases hwx : w = x
      · subst hwx; omega
      · have h := hdeg w
        simp only [hwu, hwx, ite_false, add_zero] at h
        have := hpar w (h ▸ hpos)
        omega
  have hsum := delEdge_sum_degree G hux
  have hlt : (∑ w, (G.delEdge u x).degree w) +
      (if (evenSet (G.delEdge u x)).card = 0 then 1 else 0) < n := by
    have h2 : (evenSet G).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem hnone)
    simp only [h2, ite_true] at hn
    simp only [hev', Finset.card_empty, ite_true]
    omega
  obtain ⟨D', hD'⟩ := ih _ hlt W (G.delEdge u x) (by simp [hev']) rfl
  obtain ⟨D, hD⟩ := PathDecomp.add_edge hux (delEdge_edgeSet G u x) D'
  refine ⟨D, fun w => ?_⟩
  rw [hD w, hD' w]
  by_cases hwu : w = u
  · subst hwu
    simp only [hne, ite_true, ite_false]
    omega
  · by_cases hwx : w = x
    · subst hwx
      simp only [Ne.symm hwu, ite_true, ite_false]
      omega
    · have h := hdeg w
      simp only [hwu, hwx, Ne.symm hwu, Ne.symm hwx, ite_false, add_zero] at h ⊢
      rw [h]

omit [DecidableEq W] in
/-- Case IV: no edges. -/
theorem lovasz_case_empty [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (hzero : ∀ x, G.degree x = 0) :
    ∃ D : PathDecomp G, ∀ v, D.ends v = G.degree v % 2 := by
  obtain ⟨D⟩ := PathDecomp.nonempty G
  refine ⟨D, fun v => ?_⟩
  have hnil : D.paths = [] := by
    rcases hD : D.paths with _ | ⟨P, l⟩
    · rfl
    · exfalso
      have hP : P ∈ D.paths := by rw [hD]; exact List.mem_cons_self
      obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ P.edges_ne_nil
      have heG := (D.covers e).2 (List.mem_flatMap.mpr ⟨P, hP, he⟩)
      induction e using Sym2.inductionOn with
      | hf a b =>
        have : 0 < G.degree a := (G.degree_pos_iff_exists_adj a).mpr ⟨b, heG⟩
        rw [hzero a] at this
        exact absurd this (lt_irrefl 0)
  unfold PathDecomp.ends
  rw [hnil, hzero v]
  rfl

theorem lovasz_strong (n : ℕ) : LovaszStrong.{u} n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W _ _ G _ hev hn
  by_cases hz : ∃ z, z ∈ evenSet G
  · obtain ⟨z, hz⟩ := hz
    exact lovasz_case_even ih G hev hn hz
  · simp only [not_exists] at hz
    by_cases hx : ∃ x, 3 ≤ G.degree x
    · obtain ⟨x, hx⟩ := hx
      exact lovasz_case_big ih G hn hz hx
    · simp only [not_exists, not_le] at hx
      by_cases hu : ∃ u, 0 < G.degree u
      · obtain ⟨u, hu⟩ := hu
        exact lovasz_case_matching ih G hn hz hx hu
      · simp only [not_exists, not_lt, Nat.le_zero] at hu
        exact lovasz_case_empty G hu

end induction

/-! ### Lovász's theorem -/

/-- **Lovász's theorem, strong form**: if at most one vertex has positive even degree, then some
path decomposition has exactly one end at each odd vertex and none elsewhere. -/
theorem lovasz_ends {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1) :
    ∃ D : PathDecomp G, ∀ v, D.ends v = G.degree v % 2 :=
  lovasz_strong _ W G hev rfl

/-- **Lovász's theorem** (1968): `LovaszStatement` holds. -/
theorem lovaszStatement : LovaszStatement.{u} := by
  intro W _ _ G _ hev
  have hsub : evenSet G ⊆ Finset.univ.filter (fun v => Even (G.degree v)) := fun v hv => by
    rw [evenSet, Finset.mem_filter] at hv
    rw [Finset.mem_filter]
    exact ⟨hv.1, hv.2.2⟩
  obtain ⟨D, hD⟩ := lovasz_ends G ((Finset.card_le_card hsub).trans hev)
  have h1 := pathNumber_le D
  have h2 := D.sum_ends
  have h3 : ∑ v, D.ends v ≤ Fintype.card W := by
    calc ∑ v, D.ends v = ∑ v, G.degree v % 2 := Finset.sum_congr rfl (fun v _ => hD v)
      _ ≤ ∑ _v : W, 1 := Finset.sum_le_sum (fun v _ => Nat.le_of_lt_succ (Nat.mod_lt _ two_pos))
      _ = Fintype.card W := by simp
  omega

/-- **Lovász's theorem** in path-number form: at most one even vertex (isolated vertices
included) gives `p(G) ≤ ⌊N/2⌋`. -/
theorem lovasz {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (hev : (Finset.univ.filter (fun v => Even (G.degree v))).card ≤ 1) :
    pathNumber G ≤ Fintype.card W / 2 :=
  lovaszStatement W G hev

/-- Lemma 2 of the endpoint-structure manuscript (faithful partitions), now unconditional. -/
theorem realisable_evenSet' {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hG : ∀ v, 0 < G.degree v) : Realisable G (evenSet G) :=
  realisable_evenSet lovaszStatement hG

/-- Lemma 3 of the endpoint-structure manuscript, now unconditional. -/
theorem realisable_evenSet_erase' {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hG : ∀ v, 0 < G.degree v) (hn : Even (Fintype.card V)) {u : V}
    (hu : u ∈ evenSet G) : Realisable G ((evenSet G).erase u) :=
  realisable_evenSet_erase lovaszStatement hG hn hu

end Gallai
