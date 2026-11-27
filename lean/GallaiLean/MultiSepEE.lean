import GallaiLean.MultiSep
import GallaiLean.PathSurgery

/-!
# Conjecture EE without classes at degree three; sparse sets

Manuscript `manuscripts/multi-sep/multi-sep.tex`, Proposition "EE3" and Theorem "sparse"(ii).

Let `z` be the only vertex of positive even degree and `u ∈ N(z)`. Conjecture EE (without classes)
asks for a Lovász decomposition in which `uz` is the terminal edge at `u`.

* `ee_of_avoid` (Proposition "EE", (ii) ⇒ (i), no classes): if `G − uz` has a Lovász decomposition
  whose paths ending at `z` avoid `u`, then appending `zu` gives a Lovász decomposition of `G` whose
  path ending at `u` contains `uz`.
* `ee_noTriangle` (EE3(a)): `uz` lies in no triangle. By `lovasz_avoid` (separation at distance
  three in `G − uz`).
* `ee_split` (EE3(b)): `N(u) = {z, a, b}`, `ab ∉ E`, `zb ∉ E`. Suppress `u` (delete `ua, ub`, add
  `ab`), apply `L₁` (`lovasz_avoid_nonadj`) to keep `b` off the end path of `z`, and put `u` back
  into the path through `ab` (`exists_subst_path`).
* `ee_triangle` (EE3(c)): `N(u) = {z, a, b}`, `ab ∈ E`, and `u` is the only common neighbour of `a`
  and `b`. Delete `ua, ub, ab`, separate `a` from `b`, extend the path ending at `b` by `b u a` and
  the path ending at `a` by `a b` (or the other way round, so that the path through `u` does not end
  at `z`).
* `separation_sparse_set` (Theorem "sparse"(ii)): if every vertex has at most one neighbour in `X`,
  some Lovász decomposition has any two distinct vertices of `X` on a common path adjacent.
-/

open SimpleGraph

namespace Gallai

universe u

variable {W : Type u} [Fintype W] [DecidableEq W]

section helpers

omit [Fintype W] [DecidableEq W] in
/-- Every vertex of a walk of positive length has a neighbour. -/
theorem Walk.exists_adj_of_mem_support {G : SimpleGraph W} {a b : W} (p : G.Walk a b)
    (hp : 0 < p.length) {x : W} (hx : x ∈ p.support) : ∃ y, G.Adj x y := by
  induction p with
  | nil => simp at hp
  | cons h q ih =>
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨_, h⟩
    · cases q with
      | nil =>
        simp only [Walk.support_nil, List.mem_singleton] at hx
        subst hx
        exact ⟨_, h.symm⟩
      | cons h' q' => exact ih (by simp) hx

omit [Fintype W] [DecidableEq W] in
/-- An isolated vertex lies on no path. -/
theorem GPath.not_mem_of_isolated {G : SimpleGraph W} (P : GPath G) {x : W}
    (hx : ∀ y, ¬ G.Adj x y) : x ∉ P.walk.support := fun h => by
  obtain ⟨y, hy⟩ := Walk.exists_adj_of_mem_support P.walk P.pos h
  exact hx y hy

omit [Fintype W] in
/-- Two different paths ending at `v` give `v` at least two ends. -/
theorem PathDecomp.two_le_ends {G : SimpleGraph W} (D : PathDecomp G) {P Q : GPath G}
    (hP : P ∈ D.paths) (hQ : Q ∈ D.paths) (hPQ : P ≠ Q) {v : W}
    (hPv : P.src = v ∨ P.tgt = v) (hQv : Q.src = v ∨ Q.tgt = v) : 2 ≤ D.ends v := by
  have h1 : ∀ R : GPath G, (R.src = v ∨ R.tgt = v) → 1 ≤ R.endsAt v := by
    intro R hR
    unfold GPath.endsAt
    rcases hR with h | h <;> simp [h]
  obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hP
  have hQ' : Q ∈ l₁ ∨ Q ∈ l₂ := by
    rw [hl, List.mem_append, List.mem_cons] at hQ
    rcases hQ with h | h | h
    · exact Or.inl h
    · exact absurd h.symm hPQ
    · exact Or.inr h
  unfold PathDecomp.ends
  rw [hl, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  have hP1 := h1 P hPv
  have hQ1 := h1 Q hQv
  rcases hQ' with h | h
  · have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun R => R.endsAt v) h)
    omega
  · have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun R => R.endsAt v) h)
    omega

/-- Degrees in `G − uz` when `z` is the only vertex of positive even degree of `G`. -/
theorem delEdge_even_facts {G : SimpleGraph W} [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1)
    {z u : W} (hz : z ∈ evenSet G) (hzu : G.Adj z u) :
    evenSet (delEdge G u z) ⊆ {u} ∧ (delEdge G u z).degree z % 2 = 1 ∧
      ∀ w, w ≠ u → w ≠ z → (delEdge G u z).degree w = G.degree w := by
  have hne : u ≠ z := hzu.ne.symm
  have hzd := mem_evenSet_iff.mp hz
  have huniq : ∀ w ∈ evenSet G, w = z := fun w hw => Finset.card_le_one.mp hev w hw z hz
  have hdeg := delEdge_degree G hzu.symm
  have hdz := hdeg z
  simp only [hne.symm, ite_true, ite_false] at hdz
  have hrest : ∀ w, w ≠ u → w ≠ z → (delEdge G u z).degree w = G.degree w := by
    intro w hwu hwz
    have := hdeg w
    simp only [hwu, hwz, ite_false, add_zero] at this
    exact this
  refine ⟨fun w hw => ?_, by omega, hrest⟩
  rw [Finset.mem_singleton]
  by_contra hwu
  rw [mem_evenSet_iff] at hw
  by_cases hwz : w = z
  · subst hwz; omega
  · rw [hrest w hwu hwz] at hw
    exact hwz (huniq w (mem_evenSet_iff.mpr hw))

end helpers

/-! ### Proposition "EE", (ii) ⇒ (i), without classes -/

section ee

/-- **Appending the edge at the even vertex.** Let `z` be the only vertex of positive even degree
and `u ∈ N(z)`. If `G − uz` has a Lovász decomposition whose paths ending at `z` avoid `u`, then `G`
has a Lovász decomposition in which the path ending at `u` contains `uz` (its terminal edge). -/
theorem ee_of_avoid (G : SimpleGraph W) [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1)
    {z u : W} (hz : z ∈ evenSet G) (hzu : G.Adj z u) (D' : PathDecomp (delEdge G u z))
    (hD' : ∀ v, D'.ends v = (delEdge G u z).degree v % 2)
    (hav : ∀ P ∈ D'.paths, (P.src = z ∨ P.tgt = z) → u ∉ P.walk.support) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∃ P ∈ D.paths, (P.src = u ∨ P.tgt = u) ∧ s(u, z) ∈ P.edges := by
  have huz' : G.Adj u z := hzu.symm
  have hne : u ≠ z := huz'.ne
  have hzd := mem_evenSet_iff.mp hz
  have hdeg := delEdge_degree G huz'
  have huniq : ∀ w ∈ evenSet G, w = z := fun w hw => Finset.card_le_one.mp hev w hw z hz
  have hupos : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).mpr ⟨z, huz'⟩
  have huodd : G.degree u % 2 = 1 := by
    have : u ∉ evenSet G := fun h => hne (huniq u h)
    rw [mem_evenSet_iff] at this
    omega
  have hdu := hdeg u
  have hdz := hdeg z
  simp only [hne, hne.symm, ite_true, ite_false, add_zero] at hdu hdz
  have hzpos : 0 < D'.ends z := by rw [hD']; omega
  obtain ⟨P, hP, hPend⟩ := D'.exists_end_of_pos hzpos
  have huP : u ∉ P.walk.support := hav P hP hPend
  have hK' : ∀ e, e ∈ G.edgeSet ↔ e ∈ (delEdge G u z).edgeSet ∨ e = s(z, u) := by
    intro e
    rw [delEdge_edgeSet]
    constructor
    · intro he
      by_cases h : e = s(u, z)
      · right; rw [h, Sym2.eq_swap]
      · left; exact ⟨he, h⟩
    · rintro (⟨he, -⟩ | rfl)
      · exact he
      · exact hzu
  have hadj : ¬ (delEdge G u z).Adj z u := fun h => h.2 Sym2.eq_swap
  obtain ⟨Q, hQs, hQe, hQends, hQsupp⟩ := P.exists_orient hPend
  have hQK : ∀ e ∈ Q.walk.edges, e ∈ G.edgeSet := fun e he =>
    (hK' e).2 (Or.inl (Q.walk.edges_subset_edgeSet he))
  have hs : s(u, Q.src) = s(z, u) := by rw [hQs, Sym2.eq_swap]
  have hut : G.Adj u Q.src := by rw [hQs]; exact huz'
  have huQ : u ∉ Q.walk.support := fun h => huP ((hQsupp u).1 h)
  let P' : GPath G :=
    ⟨u, Q.tgt, Walk.cons hut (Q.walk.transfer G hQK),
      by
        rw [Walk.cons_isPath_iff]
        exact ⟨by simpa using Q.isPath, by simpa using huQ⟩,
      by simp⟩
  have hP'e : P'.edges = s(z, u) :: Q.edges := by
    show (Walk.cons hut (Q.walk.transfer G hQK)).edges = _
    rw [Walk.edges_cons, Walk.edges_transfer, hs]
    rfl
  have hPK : ∀ e ∈ P.edges, e ∈ (delEdge G u z).edgeSet := fun e he =>
    P.walk.edges_subset_edgeSet he
  have hzuK : s(z, u) ∉ (delEdge G u z).edgeSet := hadj
  obtain ⟨D, -, hP'D, hends, -, -⟩ := D'.replace_supp hP P' (by
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
      · exact Or.inr hzuK
      · exact Or.inl he)
  refine ⟨D, fun w => ?_, P', hP'D, Or.inl rfl, ?_⟩
  · have h1 := hends w
    have h2 : P'.endsAt w = (if u = w then 1 else 0) + (if Q.tgt = w then 1 else 0) := rfl
    have h3 : P.endsAt w = (if z = w then 1 else 0) + (if Q.tgt = w then 1 else 0) := by
      rw [← hQends]; simp only [GPath.endsAt, hQs]
    rw [hD'] at h1
    by_cases hwz : w = z
    · subst hwz
      simp only [hne, ite_true, ite_false] at h1 h2 h3
      omega
    · by_cases hwu : w = u
      · subst hwu
        simp only [Ne.symm hne, ite_true, ite_false] at h1 h2 h3
        omega
      · simp only [Ne.symm hwz, Ne.symm hwu, ite_false] at h1 h2 h3
        have h := hdeg w
        simp only [hwu, hwz, ite_false, add_zero] at h
        omega
  · rw [hP'e, Sym2.eq_swap]; exact List.mem_cons_self

/-- **EE3(a).** If `uz` lies in no triangle, `uz` is the terminal edge at `u` of some Lovász
decomposition. -/
theorem ee_noTriangle (G : SimpleGraph W) [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1)
    {z u : W} (hz : z ∈ evenSet G) (hzu : G.Adj z u) (hnt : ∀ w, ¬ (G.Adj u w ∧ G.Adj w z)) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∃ P ∈ D.paths, (P.src = u ∨ P.tgt = u) ∧ s(u, z) ∈ P.edges := by
  obtain ⟨hsub, -, -⟩ := delEdge_even_facts hev hz hzu
  have hev' : (evenSet (delEdge G u z)).card ≤ 1 :=
    (Finset.card_le_card hsub).trans (by simp)
  have hfar : FarApart (delEdge G u z) z u :=
    ⟨hzu.ne, fun h => h.2 Sym2.eq_swap, fun w hw => hnt w ⟨hw.2.1.symm, hw.1.1.symm⟩⟩
  obtain ⟨D', hD', hav⟩ := lovasz_avoid (delEdge G u z) hev' hfar
  exact ee_of_avoid G hev hz hzu D' hD' hav

end ee

/-! ### EE3(b): suppressing a vertex of degree three -/

section split

omit [Fintype W] in
/-- Multiset bookkeeping for an edge substitution `A + {x} = B + C`. -/
theorem mem_subst_edges {A B C : List (Sym2 W)} {x : Sym2 W}
    (h : (A : Multiset (Sym2 W)) + {x} = B + C) (hB : B.Nodup) (hxB : x ∈ B) (hxC : x ∉ C)
    (e : Sym2 W) : e ∈ A ↔ (e ∈ B ∨ e ∈ C) ∧ e ≠ x := by
  have hc := congrArg (Multiset.count e) h
  simp only [Multiset.count_add, Multiset.coe_count, Multiset.count_singleton] at hc
  constructor
  · intro he
    have hA : 0 < A.count e := List.count_pos_iff.mpr he
    refine ⟨?_, fun hex => ?_⟩
    · by_contra hn
      rw [not_or] at hn
      rw [List.count_eq_zero.mpr hn.1, List.count_eq_zero.mpr hn.2] at hc
      omega
    · subst hex
      rw [List.count_eq_one_of_mem hB hxB, List.count_eq_zero.mpr hxC] at hc
      simp at hc
      omega
  · rintro ⟨he, hex⟩
    simp only [hex, ite_false, add_zero] at hc
    rcases he with he | he
    · have := List.count_pos_iff.mpr he
      exact List.count_pos_iff.mp (by omega)
    · have := List.count_pos_iff.mpr he
      exact List.count_pos_iff.mp (by omega)

/-- **EE3(b).** Let `z` be the only vertex of positive even degree, `u ∈ N(z)` with
`N(u) = {z, a, b}`, `ab ∉ E` and `zb ∉ E`. Then `uz` is the terminal edge at `u` of some Lovász
decomposition. Proof: in `K'' = G − uz − ua − ub + ab` (no positive even vertex), `L₁` keeps `b` off
the end path of `z`; then `u` is put back into the path through `ab`. -/
theorem ee_split (G : SimpleGraph W) [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1)
    {z u a b : W} (hz : z ∈ evenSet G) (hzu : G.Adj z u) (hua : G.Adj u a) (hub : G.Adj u b)
    (hab : a ≠ b) (haz : a ≠ z) (hbz : b ≠ z)
    (hN : ∀ w, G.Adj u w → w = z ∨ w = a ∨ w = b) (hnab : ¬ G.Adj a b) (hnzb : ¬ G.Adj z b) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∃ P ∈ D.paths, (P.src = u ∨ P.tgt = u) ∧ s(u, z) ∈ P.edges := by
  classical
  obtain ⟨hsub, hzodd, -⟩ := delEdge_even_facts hev hz hzu
  have hau : a ≠ u := hua.ne.symm
  have hbu : b ≠ u := hub.ne.symm
  have hzu' : z ≠ u := hzu.ne
  have hK'ua : (delEdge G u z).Adj u a := ⟨hua, fun h => by
    rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h, -⟩
    · exact haz h
    · exact hzu' h.symm⟩
  have hK₁ub : (delEdge (delEdge G u z) u a).Adj u b := ⟨⟨hub, fun h => by
    rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h, -⟩
    · exact hbz h
    · exact hzu' h.symm⟩, fun h => by
    rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h, -⟩
    · exact hab h.symm
    · exact hau h.symm⟩
  have hK₂ab : ¬ (delEdge (delEdge (delEdge G u z) u a) u b).Adj a b := fun h => hnab h.1.1.1
  -- `u` is isolated in `K''`
  have hiso : ∀ w, ¬ (plusEdge (delEdge (delEdge (delEdge G u z) u a) u b) a b).Adj u w := by
    intro w h
    rcases h with h | ⟨-, h⟩
    · rcases hN w h.1.1.1 with rfl | rfl | rfl
      · exact h.1.1.2 rfl
      · exact h.1.2 rfl
      · exact h.2 rfl
    · rcases h with ⟨h, -⟩ | ⟨h, -⟩
      · exact hau h.symm
      · exact hbu h.symm
  -- degrees
  have hdeq : ∀ w, w ≠ u →
      (plusEdge (delEdge (delEdge (delEdge G u z) u a) u b) a b).degree w =
        (delEdge G u z).degree w := by
    intro w hwu
    have h2 := delEdge_degree (delEdge G u z) hK'ua w
    have h3 := delEdge_degree (delEdge (delEdge G u z) u a) hK₁ub w
    have h4 := plusEdge_degree (G := delEdge (delEdge (delEdge G u z) u a) u b) hab hK₂ab w
    simp only [hwu, ite_false, add_zero] at h2 h3
    by_cases hwa : w = a
    · subst hwa
      simp only [hab, ite_true, ite_false, true_or, add_zero] at h2 h3 h4
      omega
    · by_cases hwb : w = b
      · subst hwb
        simp only [hwa, ite_true, ite_false, or_true, add_zero] at h2 h3 h4
        omega
      · simp only [hwa, hwb, ite_false, or_self, add_zero] at h2 h3 h4
        omega
  have hdu : (plusEdge (delEdge (delEdge (delEdge G u z) u a) u b) a b).degree u + 2 =
      (delEdge G u z).degree u := by
    have h2 := delEdge_degree (delEdge G u z) hK'ua u
    have h3 := delEdge_degree (delEdge (delEdge G u z) u a) hK₁ub u
    have h4 := plusEdge_degree (G := delEdge (delEdge (delEdge G u z) u a) u b) hab hK₂ab u
    simp only [hau.symm, hbu.symm, ite_true, ite_false, or_self, add_zero] at h2 h3 h4
    omega
  have hdu0 : (plusEdge (delEdge (delEdge (delEdge G u z) u a) u b) a b).degree u = 0 := by
    by_contra h
    obtain ⟨w, hw⟩ := (SimpleGraph.degree_pos_iff_exists_adj _ u).mp (Nat.pos_of_ne_zero h)
    exact hiso w hw
  have hmod : ∀ w, (plusEdge (delEdge (delEdge (delEdge G u z) u a) u b) a b).degree w % 2 =
      (delEdge G u z).degree w % 2 := by
    intro w
    by_cases hwu : w = u
    · subst hwu; omega
    · rw [hdeq w hwu]
  have hev0 : (evenSet (plusEdge (delEdge (delEdge (delEdge G u z) u a) u b) a b)).card = 0 := by
    rw [Finset.card_eq_zero]
    refine Finset.eq_empty_of_forall_notMem fun w hw => ?_
    rw [mem_evenSet_iff] at hw
    by_cases hwu : w = u
    · subst hwu; omega
    · rw [hdeq w hwu] at hw
      exact hwu (Finset.mem_singleton.mp (hsub (mem_evenSet_iff.mpr hw)))
  have hzK : (plusEdge (delEdge (delEdge (delEdge G u z) u a) u b) a b).degree z % 2 = 1 := by
    rw [hdeq z hzu']; exact hzodd
  have hnzbK : ¬ (plusEdge (delEdge (delEdge (delEdge G u z) u a) u b) a b).Adj z b := by
    rintro (h | ⟨-, h⟩)
    · exact hnzb h.1.1.1
    · rcases h with ⟨h, -⟩ | ⟨h, -⟩
      · exact haz h.symm
      · exact hbz h.symm
  obtain ⟨D'', hD'', hav''⟩ := lovasz_avoid_nonadj _ hev0 hzK hbz.symm hnzbK
  -- the path through `ab`
  have habK : s(a, b) ∈ (plusEdge (delEdge (delEdge (delEdge G u z) u a) u b) a b).edgeSet :=
    (plusEdge_edgeSet hab).mpr (Or.inr rfl)
  obtain ⟨R, hR, habR⟩ := List.mem_flatMap.mp ((D''.covers _).mp habK)
  -- the path `a u b` of the complete graph
  have htau : (⊤ : SimpleGraph W).Adj a u := hau
  have htub : (⊤ : SimpleGraph W).Adj u b := hbu.symm
  let T : TPath W := ⟨a, b, Walk.cons htau (Walk.cons htub Walk.nil),
    by simp [hau, hab, hbu.symm], by simp⟩
  have hTe : T.edges = [s(a, u), s(u, b)] := by simp [T, GPath.edges]
  have hTs : ∀ w, w ∈ T.walk.support ↔ w = a ∨ w = u ∨ w = b := by
    intro w; simp [T]
  obtain ⟨R'', hR''s, hR''t, hR''e, -⟩ := exists_subst_path R.toTop T (by simpa using habR)
    rfl rfl (by
      intro w hw hwR
      rcases (hTs w).mp hw with rfl | rfl | rfl
      · exact Or.inl rfl
      · rw [GPath.toTop_support] at hwR
        exact absurd hwR (R.not_mem_of_isolated hiso)
      · exact Or.inr rfl)
  rw [GPath.toTop_edges, hTe] at hR''e
  have hxC : s(a, b) ∉ [s(a, u), s(u, b)] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Sym2.eq_iff, not_or, not_and]
    exact ⟨⟨fun _ h => hbu h, fun h => absurd h hau⟩, ⟨fun h => absurd h hau, fun h => absurd h hab⟩⟩
  have hmem := mem_subst_edges hR''e R.isPath.isTrail.edges_nodup habR hxC
  -- edge sets
  have hK'e : ∀ e, e ∈ (delEdge G u z).edgeSet ↔
      e ∈ (delEdge (delEdge (delEdge G u z) u a) u b).edgeSet ∨ e = s(u, a) ∨ e = s(u, b) := by
    intro e
    rw [delEdge_edgeSet (delEdge (delEdge G u z) u a) u b e, delEdge_edgeSet (delEdge G u z) u a e]
    constructor
    · intro he
      by_cases h1 : e = s(u, a)
      · exact Or.inr (Or.inl h1)
      · by_cases h2 : e = s(u, b)
        · exact Or.inr (Or.inr h2)
        · exact Or.inl ⟨⟨he, h1⟩, h2⟩
    · rintro (⟨⟨he, -⟩, -⟩ | rfl | rfl)
      · exact he
      · exact hK'ua
      · exact hK₁ub.1
  have hK''e : ∀ e, e ∈ (plusEdge (delEdge (delEdge (delEdge G u z) u a) u b) a b).edgeSet ↔
      e ∈ (delEdge (delEdge (delEdge G u z) u a) u b).edgeSet ∨ e = s(a, b) :=
    fun e => plusEdge_edgeSet hab
  have hK₂G : ∀ e ∈ (delEdge (delEdge (delEdge G u z) u a) u b).edgeSet, e ∈ G.edgeSet := by
    intro e he
    rw [delEdge_edgeSet, delEdge_edgeSet, delEdge_edgeSet] at he
    exact he.1.1.1
  have habG : s(a, b) ∉ G.edgeSet := hnab
  have hR''K : ∀ e ∈ R''.walk.edges, e ∈ (delEdge G u z).edgeSet := by
    intro e he
    obtain ⟨hRT, hne⟩ := (hmem e).mp he
    rcases hRT with hRe | hTe'
    · rcases (hK''e _).mp (R.walk.edges_subset_edgeSet hRe) with h | h
      · exact (hK'e e).mpr (Or.inl h)
      · exact absurd h hne
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hTe'
      rcases hTe' with rfl | rfl
      · exact (hK'e _).mpr (Or.inr (Or.inl Sym2.eq_swap))
      · exact (hK'e _).mpr (Or.inr (Or.inr rfl))
  let R' : GPath (delEdge G u z) := R''.ofTop (delEdge G u z) hR''K
  have hR'e : R'.edges = R''.edges := GPath.ofTop_edges _ _
  have hsua : s(u, a) ≠ s(a, b) := fun h => by
    rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨h, -⟩
    · exact hau h.symm
    · exact hbu h.symm
  have hsub' : s(u, b) ≠ s(a, b) := fun h => by
    rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨h, -⟩
    · exact hau h.symm
    · exact hbu h.symm
  obtain ⟨D', -, -, hends, -, hcovr⟩ := D''.replace_supp hR R' (by
      intro e
      rw [hR'e]
      constructor
      · intro he
        rcases (hK'e e).mp he with h | rfl | rfl
        · by_cases heR : e ∈ R.edges
          · exact Or.inr ((hmem e).mpr ⟨Or.inl heR, fun h' => habG (h' ▸ hK₂G e h)⟩)
          · exact Or.inl ⟨(hK''e _).mpr (Or.inl h), heR⟩
        · exact Or.inr ((hmem _).mpr ⟨Or.inr (by simp [Sym2.eq_swap]), hsua⟩)
        · exact Or.inr ((hmem _).mpr ⟨Or.inr (by simp), hsub'⟩)
      · rintro (⟨h1, h2⟩ | h)
        · rcases (hK''e _).mp h1 with h | rfl
          · exact (hK'e e).mpr (Or.inl h)
          · exact absurd habR h2
        · exact hR''K e h)
    (by
      intro e he
      rw [hR'e] at he
      obtain ⟨hRT, -⟩ := (hmem e).mp he
      rcases hRT with hRe | hTe'
      · exact Or.inl hRe
      · right
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hTe'
        rcases hTe' with rfl | rfl
        · exact fun h => hiso a ((SimpleGraph.mem_edgeSet _).mp h).symm
        · exact fun h => hiso b ((SimpleGraph.mem_edgeSet _).mp h))
  have hR'ends : ∀ v, R'.endsAt v = R.endsAt v := by
    intro v
    have hs : R'.src = R.src := hR''s
    have ht : R'.tgt = R.tgt := hR''t
    simp only [GPath.endsAt, hs, ht]
  have hD' : ∀ v, D'.ends v = (delEdge G u z).degree v % 2 := by
    intro v
    have := hends v
    rw [hR'ends v, hD'' v, hmod v] at this
    omega
  refine ee_of_avoid G hev hz hzu D' hD' (fun P hP hPz => ?_)
  rcases hcovr P hP with rfl | ⟨Q, hQ, hQs, hQt, hQsupp⟩
  · have hs : R'.src = R.src := hR''s
    have ht : R'.tgt = R.tgt := hR''t
    rw [hs, ht] at hPz
    exact absurd (R.walk.snd_mem_support_of_mem_edges habR) (hav'' R hR hPz)
  · rw [hQsupp]
    exact Q.not_mem_of_isolated hiso

end split

/-! ### EE3(c): a triangle at `u` -/

section triangle

omit [Fintype W] in
theorem GPath.end_of_endsAt_pos {G : SimpleGraph W} (P : GPath G) {v : W} (h : 0 < P.endsAt v) :
    P.src = v ∨ P.tgt = v := by
  unfold GPath.endsAt at h
  by_cases hs : P.src = v
  · exact Or.inl hs
  · by_cases ht : P.tgt = v
    · exact Or.inr ht
    · simp [hs, ht] at h

omit [Fintype W] in
/-- The two extensions of EE3(c). `K₃` is `G − uz − ua − ub − ab`, given by its edge set. If the
path `Pb` ending at `b` does not end at `z`, extend it by `b u a` and the path ending at `a` by
`a b`. The result decomposes `G − uz`, has the end counts of `D₃`, and its paths ending at `z` avoid
`u`. -/
theorem ee_triangle_aux (G : SimpleGraph W) {z u a b : W}
    (hzu : G.Adj z u) (hua : G.Adj u a) (hub : G.Adj u b) (habG : G.Adj a b)
    (haz : a ≠ z) (hbz : b ≠ z)
    (K₃ : SimpleGraph W)
    (hK₃ : ∀ e, e ∈ K₃.edgeSet ↔
      e ∈ (delEdge G u z).edgeSet ∧ e ≠ s(u, a) ∧ e ≠ s(u, b) ∧ e ≠ s(a, b))
    (hiso : ∀ w, ¬ K₃.Adj u w)
    (D₃ : PathDecomp K₃) (hsep : Separates D₃ a b)
    {Pa Pb : GPath K₃} (hPa : Pa ∈ D₃.paths) (hPb : Pb ∈ D₃.paths)
    (hPae : Pa.src = a ∨ Pa.tgt = a) (hPbe : Pb.src = b ∨ Pb.tgt = b)
    (hPbz : ¬ (Pb.src = z ∨ Pb.tgt = z)) :
    ∃ D' : PathDecomp (delEdge G u z), (∀ v, D'.ends v = D₃.ends v) ∧
      ∀ P ∈ D'.paths, (P.src = z ∨ P.tgt = z) → u ∉ P.walk.support := by
  have hau : a ≠ u := hua.ne.symm
  have hbu : b ≠ u := hub.ne.symm
  have hzu' : z ≠ u := hzu.ne
  have hab : a ≠ b := habG.ne
  have hmemP : ∀ (P : GPath K₃) y, (P.src = y ∨ P.tgt = y) → y ∈ P.walk.support := by
    rintro P y (rfl | rfl)
    · exact P.walk.start_mem_support
    · exact P.walk.end_mem_support
  have haPa := hmemP Pa a hPae
  have hbPb := hmemP Pb b hPbe
  have hbPa : b ∉ Pa.walk.support := fun h => hsep Pa hPa ⟨haPa, h⟩
  have haPb : a ∉ Pb.walk.support := fun h => hsep Pb hPb ⟨h, hbPb⟩
  have hPab : Pa ≠ Pb := fun h => haPb (h ▸ haPa)
  -- the intermediate graph `K₁ = G − uz − ab`
  have hsuz : ∀ {x : W}, x ≠ z → x ≠ u → s(u, x) ≠ s(u, z) := fun hx _ h => by
    rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h, -⟩
    · exact hx h
    · exact hzu' h.symm
  have hsab_uz : s(a, b) ≠ s(u, z) := fun h => by
    rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨h, -⟩
    · exact hau h
    · exact haz h
  have hK₁ : ∀ e, e ∈ (delEdge (delEdge G u z) a b).edgeSet ↔
      e ∈ (delEdge G u z).edgeSet ∧ e ≠ s(a, b) := fun e => delEdge_edgeSet _ a b e
  have hK' : ∀ e, e ∈ (delEdge G u z).edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(u, z) :=
    fun e => delEdge_edgeSet G u z e
  have hua₁ : (delEdge (delEdge G u z) a b).Adj a u := by
    refine ⟨⟨hua.symm, fun h => hsuz haz hau ?_⟩, fun h => ?_⟩
    · rw [Sym2.eq_swap]; exact h
    · rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h, -⟩
      · exact hbu h.symm
      · exact hab h
  have hub₁ : (delEdge (delEdge G u z) a b).Adj u b := by
    refine ⟨⟨hub, hsuz hbz hbu⟩, fun h => ?_⟩
    rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨h, -⟩
    · exact hau h.symm
    · exact hbu h.symm
  have hK₃K₁ : ∀ e ∈ K₃.edgeSet, e ∈ (delEdge (delEdge G u z) a b).edgeSet := fun e he => by
    obtain ⟨h1, -, -, h4⟩ := (hK₃ e).mp he
    exact (hK₁ e).mpr ⟨h1, h4⟩
  -- step 1: `Pb` becomes `a u b ⋯`
  obtain ⟨Qb, hQbs, hQbe, hQbends, hQbsupp⟩ := Pb.exists_orient hPbe
  have hQbK : ∀ e ∈ Qb.walk.edges, e ∈ (delEdge (delEdge G u z) a b).edgeSet := fun e he =>
    hK₃K₁ e (Qb.walk.edges_subset_edgeSet he)
  have hub₁' : (delEdge (delEdge G u z) a b).Adj u Qb.src := by rw [hQbs]; exact hub₁
  have huQb : u ∉ Qb.walk.support := fun h => Pb.not_mem_of_isolated hiso ((hQbsupp u).1 h)
  have haQb : a ∉ Qb.walk.support := fun h => haPb ((hQbsupp a).1 h)
  let Pb' : GPath (delEdge (delEdge G u z) a b) :=
    ⟨a, Qb.tgt, Walk.cons hua₁ (Walk.cons hub₁' (Qb.walk.transfer _ hQbK)),
      by
        rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff]
        refine ⟨⟨by simpa using Qb.isPath, by simpa using huQb⟩, ?_⟩
        simp only [Walk.support_cons, Walk.support_transfer, List.mem_cons, not_or]
        exact ⟨hau, haQb⟩,
      by simp⟩
  have hPb'e : Pb'.edges = s(a, u) :: s(u, b) :: Qb.edges := by
    show (Walk.cons hua₁ (Walk.cons hub₁' (Qb.walk.transfer _ hQbK))).edges = _
    have hsb : s(u, Qb.src) = s(u, b) := by rw [hQbs]
    rw [Walk.edges_cons, Walk.edges_cons, Walk.edges_transfer, hsb]
    rfl
  have hPb'supp : ∀ y, y ∈ Pb'.walk.support ↔ y = a ∨ y = u ∨ y ∈ Pb.walk.support := by
    intro y
    show y ∈ (Walk.cons hua₁ (Walk.cons hub₁' (Qb.walk.transfer _ hQbK))).support ↔ _
    rw [Walk.support_cons, Walk.support_cons, Walk.support_transfer, List.mem_cons, List.mem_cons,
      hQbsupp]
  obtain ⟨D₁, -, -, hends₁, hkeep₁, hcovr₁⟩ := D₃.replace_supp hPb Pb' (by
      intro e
      rw [hPb'e, List.mem_cons, List.mem_cons, hQbe.mem_iff, hK₁ e]
      constructor
      · rintro ⟨he, hne⟩
        by_cases h1 : e = s(u, a)
        · exact Or.inr (Or.inl (h1.trans Sym2.eq_swap))
        · by_cases h2 : e = s(u, b)
          · exact Or.inr (Or.inr (Or.inl h2))
          · by_cases heP : e ∈ Pb.edges
            · exact Or.inr (Or.inr (Or.inr heP))
            · exact Or.inl ⟨(hK₃ e).mpr ⟨he, h1, h2, hne⟩, heP⟩
      · rintro (⟨h, -⟩ | rfl | rfl | h)
        · exact (hK₁ e).mp (hK₃K₁ e h)
        · exact (hK₁ _).mp hua₁
        · exact (hK₁ _).mp hub₁
        · exact (hK₁ e).mp (hK₃K₁ e (Pb.walk.edges_subset_edgeSet h)))
    (by
      intro e he
      rw [hPb'e, List.mem_cons, List.mem_cons, hQbe.mem_iff] at he
      rcases he with rfl | rfl | he
      · right; intro h; exact ((hK₃ _).mp h).2.1 Sym2.eq_swap
      · right; intro h; exact ((hK₃ _).mp h).2.2.1 rfl
      · exact Or.inl he)
  obtain ⟨Pa1, hPa1, hPa1s, hPa1t, hPa1supp⟩ := hkeep₁ Pa hPa hPab
  -- step 2: `Pa` becomes `b a ⋯`
  have hPa1e : Pa1.src = a ∨ Pa1.tgt = a := by rw [hPa1s, hPa1t]; exact hPae
  obtain ⟨Qa, hQas, hQae, hQaends, hQasupp⟩ := Pa1.exists_orient hPa1e
  have hK₁K' : ∀ e ∈ (delEdge (delEdge G u z) a b).edgeSet, e ∈ (delEdge G u z).edgeSet :=
    fun e he => ((hK₁ e).mp he).1
  have hQaK : ∀ e ∈ Qa.walk.edges, e ∈ (delEdge G u z).edgeSet := fun e he =>
    hK₁K' e (Qa.walk.edges_subset_edgeSet he)
  have hba' : (delEdge G u z).Adj b Qa.src := by
    rw [hQas]
    refine ⟨habG.symm, fun h => hsab_uz ?_⟩
    rw [Sym2.eq_swap]; exact h
  have hbQa : b ∉ Qa.walk.support := fun h => hbPa (hPa1supp ▸ (hQasupp b).1 h)
  let Pa' : GPath (delEdge G u z) :=
    ⟨b, Qa.tgt, Walk.cons hba' (Qa.walk.transfer _ hQaK),
      by
        rw [Walk.cons_isPath_iff]
        exact ⟨by simpa using Qa.isPath, by simpa using hbQa⟩,
      by simp⟩
  have hPa'e : Pa'.edges = s(b, a) :: Qa.edges := by
    show (Walk.cons hba' (Qa.walk.transfer _ hQaK)).edges = _
    have hsa : s(b, Qa.src) = s(b, a) := by rw [hQas]
    rw [Walk.edges_cons, Walk.edges_transfer, hsa]
    rfl
  have hPa'supp : ∀ y, y ∈ Pa'.walk.support ↔ y = b ∨ y ∈ Pa.walk.support := by
    intro y
    show y ∈ (Walk.cons hba' (Qa.walk.transfer _ hQaK)).support ↔ _
    rw [Walk.support_cons, Walk.support_transfer, List.mem_cons, hQasupp, hPa1supp]
  obtain ⟨D', -, -, hends', -, hcovr'⟩ := D₁.replace_supp hPa1 Pa' (by
      intro e
      rw [hPa'e, List.mem_cons, hQae.mem_iff]
      constructor
      · intro he
        by_cases h1 : e = s(a, b)
        · exact Or.inr (Or.inl (h1.trans Sym2.eq_swap))
        · by_cases heP : e ∈ Pa1.edges
          · exact Or.inr (Or.inr heP)
          · exact Or.inl ⟨(hK₁ e).mpr ⟨he, h1⟩, heP⟩
      · rintro (⟨h, -⟩ | rfl | h)
        · exact hK₁K' e h
        · exact (hK' _).mpr ⟨habG.symm, fun h => hsab_uz (Sym2.eq_swap.trans h)⟩
        · exact hK₁K' e (Pa1.walk.edges_subset_edgeSet h))
    (by
      intro e he
      rw [hPa'e, List.mem_cons, hQae.mem_iff] at he
      rcases he with rfl | he
      · right; intro h; exact ((hK₁ _).mp h).2 Sym2.eq_swap
      · exact Or.inl he)
  refine ⟨D', fun v => ?_, fun P hP hPz => ?_⟩
  · have h1 := hends₁ v
    have h2 := hends' v
    have e1 : Pb.endsAt v = (if b = v then 1 else 0) + (if Qb.tgt = v then 1 else 0) := by
      rw [← hQbends]; simp only [GPath.endsAt, hQbs]
    have e2 : Pb'.endsAt v = (if a = v then 1 else 0) + (if Qb.tgt = v then 1 else 0) := rfl
    have e3 : Pa1.endsAt v = (if a = v then 1 else 0) + (if Qa.tgt = v then 1 else 0) := by
      rw [← hQaends]; simp only [GPath.endsAt, hQas]
    have e4 : Pa'.endsAt v = (if b = v then 1 else 0) + (if Qa.tgt = v then 1 else 0) := rfl
    rw [e1, e2] at h1
    rw [e3, e4] at h2
    omega
  · rcases hcovr' P hP with rfl | ⟨S, hS, hSs, hSt, hSsupp⟩
    · rw [hPa'supp]
      rintro (h | h)
      · exact hbu h.symm
      · exact Pa.not_mem_of_isolated hiso h
    · rw [hSsupp]
      rw [hSs, hSt] at hPz
      rcases hcovr₁ S hS with rfl | ⟨Q, hQ, hQs, hQt, hQsupp⟩
      · exfalso
        rcases hPz with h | h
        · exact haz h
        · apply hPbz
          apply Pb.end_of_endsAt_pos
          rw [← hQbends]
          have : Qb.tgt = z := h
          simp [GPath.endsAt, this]
      · rw [hQsupp]
        exact Q.not_mem_of_isolated hiso

/-- **EE3(c).** Let `z` be the only vertex of positive even degree, `u ∈ N(z)` with
`N(u) = {z, a, b}`, `ab ∈ E`, and `u` the only common neighbour of `a` and `b`. Then `uz` is the
terminal edge at `u` of some Lovász decomposition. -/
theorem ee_triangle (G : SimpleGraph W) [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1)
    {z u a b : W} (hz : z ∈ evenSet G) (hzu : G.Adj z u) (hua : G.Adj u a) (hub : G.Adj u b)
    (haz : a ≠ z) (hbz : b ≠ z)
    (hN : ∀ w, G.Adj u w → w = z ∨ w = a ∨ w = b) (habG : G.Adj a b)
    (hcom : ∀ w, G.Adj a w → G.Adj w b → w = u) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∃ P ∈ D.paths, (P.src = u ∨ P.tgt = u) ∧ s(u, z) ∈ P.edges := by
  classical
  obtain ⟨hsub, hzodd, hrest⟩ := delEdge_even_facts hev hz hzu
  have hau : a ≠ u := hua.ne.symm
  have hbu : b ≠ u := hub.ne.symm
  have hzu' : z ≠ u := hzu.ne
  have hab : a ≠ b := habG.ne
  have hzd := mem_evenSet_iff.mp hz
  have huniq : ∀ w ∈ evenSet G, w = z := fun w hw => Finset.card_le_one.mp hev w hw z hz
  have hK'ua : (delEdge G u z).Adj u a := ⟨hua, fun h => by
    rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h, -⟩
    · exact haz h
    · exact hzu' h.symm⟩
  have hK₁ub : (delEdge (delEdge G u z) u a).Adj u b := ⟨⟨hub, fun h => by
    rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h, -⟩
    · exact hbz h
    · exact hzu' h.symm⟩, fun h => by
    rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h, -⟩
    · exact hab h.symm
    · exact hau h.symm⟩
  have hK₂ab : (delEdge (delEdge (delEdge G u z) u a) u b).Adj a b := by
    refine ⟨⟨⟨habG, fun h => ?_⟩, fun h => ?_⟩, fun h => ?_⟩
    · rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨h, -⟩
      · exact hau h
      · exact haz h
    · rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨-, h⟩
      · exact hau h
      · exact hbu h
    · rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨h, -⟩
      · exact hau h
      · exact hab h
  -- `u` is isolated in `K₃`
  have hiso : ∀ w,
      ¬ (delEdge (delEdge (delEdge (delEdge G u z) u a) u b) a b).Adj u w := by
    intro w h
    rcases hN w h.1.1.1.1 with rfl | rfl | rfl
    · exact h.1.1.1.2 rfl
    · exact h.1.1.2 rfl
    · exact h.1.2 rfl
  -- degrees
  have hdeg : ∀ w,
      (delEdge (delEdge (delEdge (delEdge G u z) u a) u b) a b).degree w +
        2 * ((if w = u then 1 else 0) + (if w = a then 1 else 0) + (if w = b then 1 else 0)) =
        (delEdge G u z).degree w := by
    intro w
    have h2 := delEdge_degree (delEdge G u z) hK'ua w
    have h3 := delEdge_degree (delEdge (delEdge G u z) u a) hK₁ub w
    have h4 := delEdge_degree (delEdge (delEdge (delEdge G u z) u a) u b) hK₂ab w
    omega
  have hmod : ∀ w, (delEdge (delEdge (delEdge (delEdge G u z) u a) u b) a b).degree w % 2 =
      (delEdge G u z).degree w % 2 := fun w => by have := hdeg w; omega
  have hdu0 : (delEdge (delEdge (delEdge (delEdge G u z) u a) u b) a b).degree u = 0 := by
    by_contra h
    obtain ⟨w, hw⟩ := (SimpleGraph.degree_pos_iff_exists_adj _ u).mp (Nat.pos_of_ne_zero h)
    exact hiso w hw
  have hev₃ : (evenSet (delEdge (delEdge (delEdge (delEdge G u z) u a) u b) a b)).card ≤ 1 := by
    have : evenSet (delEdge (delEdge (delEdge (delEdge G u z) u a) u b) a b) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun w hw => ?_
      rw [mem_evenSet_iff] at hw
      by_cases hwu : w = u
      · subst hwu; omega
      · have h := hdeg w
        have hK' : w ∈ evenSet (delEdge G u z) := mem_evenSet_iff.mpr ⟨by omega, by omega⟩
        exact hwu (Finset.mem_singleton.mp (hsub hK'))
    rw [this]; simp
  have hfar : FarApart (delEdge (delEdge (delEdge (delEdge G u z) u a) u b) a b) a b := by
    refine ⟨hab, fun h => h.2 rfl, fun w hw => ?_⟩
    have := hcom w hw.1.1.1.1.1 hw.2.1.1.1.1
    subst this
    exact hiso a hw.1.symm
  obtain ⟨D₃, hD₃, hsep⟩ := separation _ hev₃ hfar
  -- the paths ending at `a` and at `b`
  have hodd : ∀ x, x ≠ u → x ≠ z → G.Adj u x →
      D₃.ends x = 1 := by
    intro x hxu hxz hux
    rw [hD₃, hmod, hrest x hxu hxz]
    have hpos : 0 < G.degree x := (G.degree_pos_iff_exists_adj x).mpr ⟨u, hux.symm⟩
    have : x ∉ evenSet G := fun h => hxz (huniq x h)
    rw [mem_evenSet_iff] at this
    omega
  obtain ⟨Pa, hPa, hPae⟩ := D₃.exists_end_of_pos (by rw [hodd a hau haz hua]; omega)
  obtain ⟨Pb, hPb, hPbe⟩ := D₃.exists_end_of_pos (by rw [hodd b hbu hbz hub]; omega)
  have hK₃ : ∀ e, e ∈ (delEdge (delEdge (delEdge (delEdge G u z) u a) u b) a b).edgeSet ↔
      e ∈ (delEdge G u z).edgeSet ∧ e ≠ s(u, a) ∧ e ≠ s(u, b) ∧ e ≠ s(a, b) := by
    intro e
    rw [delEdge_edgeSet, delEdge_edgeSet, delEdge_edgeSet]
    tauto
  have hfinish : ∀ D' : PathDecomp (delEdge G u z), (∀ v, D'.ends v = D₃.ends v) →
      (∀ P ∈ D'.paths, (P.src = z ∨ P.tgt = z) → u ∉ P.walk.support) →
      ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
        ∃ P ∈ D.paths, (P.src = u ∨ P.tgt = u) ∧ s(u, z) ∈ P.edges := by
    intro D' hD' hav
    exact ee_of_avoid G hev hz hzu D' (fun v => by rw [hD', hD₃, hmod]) hav
  by_cases hPbz : Pb.src = z ∨ Pb.tgt = z
  · -- then `Pa` does not end at `z`; swap the roles of `a` and `b`
    have hPaz : ¬ (Pa.src = z ∨ Pa.tgt = z) := by
      intro hPaz
      have hne : Pa ≠ Pb := by
        intro h
        subst h
        have hmemP : ∀ y, (Pa.src = y ∨ Pa.tgt = y) → y ∈ Pa.walk.support := by
          rintro y (h | h)
          · rw [← h]; exact Pa.walk.start_mem_support
          · rw [← h]; exact Pa.walk.end_mem_support
        exact hsep Pa hPa ⟨hmemP a hPae, hmemP b hPbe⟩
      have h2 := D₃.two_le_ends hPa hPb hne hPaz hPbz
      rw [hD₃] at h2
      omega
    obtain ⟨D', hD', hav⟩ := ee_triangle_aux G hzu hub hua habG.symm hbz haz _
      (fun e => by rw [hK₃ e, Sym2.eq_swap (a := a) (b := b)]; tauto) hiso D₃
      (fun P hP h => hsep P hP ⟨h.2, h.1⟩) hPb hPa hPbe hPae hPaz
    exact hfinish D' hD' hav
  · obtain ⟨D', hD', hav⟩ := ee_triangle_aux G hzu hua hub habG haz hbz _ hK₃ hiso D₃ hsep
      hPa hPb hPae hPbe hPbz
    exact hfinish D' hD' hav

end triangle

/-! ### Theorem "sparse"(ii) -/

section sparseSet

/-- **Sparse sets.** If every vertex has at most one neighbour in `X`, then some Lovász
decomposition has any two distinct vertices of `X` on a common path adjacent (so a path meets `X`
in at most one vertex or in the two ends of an edge). -/
theorem separation_sparse_set (G : SimpleGraph W) [DecidableRel G.Adj]
    (hev : (evenSet G).card ≤ 1) {X : Finset W}
    (hone : ∀ v p q, G.Adj v p → G.Adj v q → p ∈ X → q ∈ X → p = q) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∀ P ∈ D.paths, ∀ x ∈ X, ∀ y ∈ X, x ∈ P.walk.support → y ∈ P.walk.support →
        x = y ∨ G.Adj x y := by
  classical
  let 𝒜 : Finset (Finset W) :=
    ((X ×ˢ X).filter (fun p => Packed G {p.1, p.2})).image (fun p => {p.1, p.2})
  have hfam : SparseFam G X 𝒜 := by
    refine ⟨fun A hA => ?_, fun A hA => ?_, hone⟩
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hA
      exact (Finset.mem_filter.mp hp).2
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hA
      have h := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1)
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact h.1
      · exact h.2
  obtain ⟨D, hD, hm⟩ := separation_sparse G hev hfam
  refine ⟨D, hD, fun P hP x hx y hy hxP hyP => ?_⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hxy, hnadj⟩ := hcon
  have hpk : Packed G {x, y} := by
    intro p hp q hq hpq
    rw [Finset.mem_insert, Finset.mem_singleton] at hp hq
    have hno : ∀ w, ¬ (G.Adj x w ∧ G.Adj w y) := fun w hw =>
      hxy (hone w x y hw.1.symm hw.2 hx hy)
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact absurd rfl hpq
    · exact ⟨hnadj, hno⟩
    · exact ⟨fun h => hnadj h.symm, fun w hw => hno w ⟨hw.2.symm, hw.1.symm⟩⟩
    · exact absurd rfl hpq
  have hA : ({x, y} : Finset W) ∈ 𝒜 :=
    Finset.mem_image.mpr ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hpk⟩, rfl⟩
  exact hxy (hm _ hA P hP x (by simp) y (by simp) hxP hyP)

end sparseSet

end Gallai
