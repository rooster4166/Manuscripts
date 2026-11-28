import GallaiLean.ForestLift

/-!
# The forest lift to Test2 (session `claude/test2`)

Manuscript: `manuscripts/test2/test2.tex`, §3 (the forest lift for the three-end test).

Let `z, r` be the only even vertices of `J`, adjacent, with `d(r) ≥ 3`. Put `T = N(z) − r` (a list)
and let `Φ` be a set of edges of `J − z` whose odd-degree vertices are exactly `N(z) = T ∪ {r}`,
given as a list `L` of (child, parent) pairs `(v, p(v))` in parent-first order, with distinct
children and edges and **`r` never a child** (so `r` is a root of its component of `Φ`).
Put `M = J − zT − Φ` (`forM2`): `z` is a leaf at `r`, and every vertex of `M` has odd degree.
If `M` has a Lovász decomposition with
* (i) the path ending at each child `v` avoids `p(v)`, and
* (ii) no path has two siblings as its two ends,
then Test2 holds at `(z, r)` (**`test2At_of_forestBase2`**).

Compared with the Test1 lift (`test1At_of_forestBase`) there is no vertex `w`: the odd set of `Φ`
is all of `N(z)`, and `r` itself is in it. The leaf `z` gives `r` one extra end when it is trimmed,
the own Lovász end of `r` gives one, and the children of `r` give `d_Φ(r) ≥ 1` more.

## Main results

* **`append_forest_ends`**: `append_forest` with the ends tracked: a child loses its end, a parent
  gains one per child.
* `Test2At`, `test2_of_test2At`.
* **`test2At_of_leafDecomp`**: a decomposition of `J − z` with `z` re-attached as a leaf at `r`, of
  size `≤ |J|/2` and with at least two ends at `r`, gives `Test2At` (trim the leaf, or drop the
  path `zr` and split once).
* `zDel2`, `forM2`, `leafT2`, `ForestData2`, `ForestBase2`.
* **`test2At_of_forestBase2`** (manuscript Theorem 3.2), **`test2_of_forestBases2`**.
-/

open SimpleGraph

namespace Gallai

universe u

/-! ### Appending a forest, with the ends tracked -/

section appendForestEnds

variable {U : Type*} [DecidableEq U]

/-- **Appending a forest, with ends** (manuscript Lemma 3.1). As `append_forest`, and moreover every
vertex `x` loses one end for each pair with child `x` and gains one for each pair with parent `x`. -/
theorem append_forest_ends [Fintype U] {G : SimpleGraph U} :
    ∀ (L : List (U × U)) (K : SimpleGraph U),
      (∀ e, e ∈ G.edgeSet ↔ e ∈ K.edgeSet ∨ e ∈ L.map pairEdge) →
      (∀ p ∈ L, ¬ K.Adj p.1 p.2) → (L.map Prod.fst).Nodup → (L.map pairEdge).Nodup →
      L.Pairwise (fun p q => p.2 ≠ q.1) →
      ∀ D : PathDecomp K, (∀ p ∈ L, 1 ≤ D.ends p.1) →
      (∀ p ∈ L, ∀ P ∈ D.paths, (P.src = p.1 ∨ P.tgt = p.1) → p.2 ∉ P.walk.support) →
      (∀ p ∈ L, ∀ q ∈ L, p.1 ≠ q.1 → p.2 = q.2 → ∀ P ∈ D.paths,
        ¬ ((P.src = p.1 ∨ P.tgt = p.1) ∧ (P.src = q.1 ∨ P.tgt = q.1))) →
      ∃ D' : PathDecomp G, D'.size = D.size ∧ ∀ x,
        D'.ends x + L.countP (fun p => decide (p.1 = x)) =
          D.ends x + L.countP (fun p => decide (p.2 = x))
  | [], K, hG, _, _, _, _, D, _, _, _ => by
      obtain ⟨D', hD'⟩ := D.congrGraph (G := G) (fun e => by rw [hG e]; simp)
      refine ⟨D', ?_, fun x => by simp [hD' x]⟩
      have h1 := D'.sum_ends
      have h2 := D.sum_ends
      simp only [hD'] at h1
      omega
  | p :: L', K, hG, hK, hndc, hnde, hpw, D, hend, havoid, hsib => by
      rw [List.map_cons, List.nodup_cons] at hndc hnde
      rw [List.pairwise_cons] at hpw
      obtain ⟨hpw1, hpw'⟩ := hpw
      set K₁ := delList G (L'.map pairEdge) with hK₁def
      have hnotL' : ∀ e ∈ L'.map pairEdge, e ∈ G.edgeSet := fun e he =>
        (hG e).2 (Or.inr (List.mem_cons_of_mem _ he))
      have hKL' : ∀ e ∈ K.edgeSet, e ∉ L'.map pairEdge := by
        intro e he hm
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        exact hK q (List.mem_cons_of_mem _ hq) he
      have hK₁ : ∀ e, e ∈ K₁.edgeSet ↔ e ∈ K.edgeSet ∨ e = s(p.1, p.2) := by
        intro e
        rw [hK₁def, delList_edgeSet, hG e, List.map_cons, List.mem_cons]
        constructor
        · rintro ⟨h | h | h, hn⟩
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h hn
        · rintro (h | rfl)
          · exact ⟨Or.inl h, hKL' e h⟩
          · exact ⟨Or.inr (Or.inl rfl), hnde.1⟩
      have hG' : ∀ e, e ∈ G.edgeSet ↔ e ∈ K₁.edgeSet ∨ e ∈ L'.map pairEdge := by
        intro e
        rw [hK₁def, delList_edgeSet]
        constructor
        · intro h
          by_cases hm : e ∈ L'.map pairEdge
          · exact Or.inr hm
          · exact Or.inl ⟨h, hm⟩
        · rintro (⟨h, -⟩ | h)
          · exact h
          · exact hnotL' e h
      have hK' : ∀ q ∈ L', ¬ K₁.Adj q.1 q.2 := fun q hq h => h.2 (List.mem_map_of_mem hq)
      have hp : p ∈ p :: L' := List.mem_cons_self
      have hadj : ¬ K.Adj p.1 p.2 := hK p hp
      obtain ⟨P, hP, hPt⟩ := D.exists_path_of_ends_pos (hend p hp)
      obtain ⟨D₁, hends₁, P', -, hP'src, hP'case, hcls, -⟩ :=
        append_full D hadj hK₁ hP hPt (havoid p hp P hP hPt)
      have hc1 : ∀ q ∈ L', q.1 ≠ p.1 := fun q hq h =>
        hndc.1 (h ▸ List.mem_map_of_mem (f := Prod.fst) hq)
      have hc2 : ∀ q ∈ L', q.1 ≠ p.2 := fun q hq h => hpw1 q hq h.symm
      have hcopy : ∀ q ∈ L', ∀ Q' ∈ D₁.paths, (Q'.src = q.1 ∨ Q'.tgt = q.1) →
          (∃ Q ∈ D.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧ Q'.walk.support = Q.walk.support) ∨
          (Q' = P' ∧ (P.src = q.1 ∨ P.tgt = q.1) ∧
            ∀ x, x ∈ Q'.walk.support ↔ x = p.2 ∨ x ∈ P.walk.support) := by
        intro q hq Q' hQ' hq'
        rcases hcls Q' hQ' with hEq | hc
        · subst hEq
          refine Or.inr ⟨rfl, ?_, ?_⟩
          · rcases hq' with h | h
            · exact absurd (hP'src.symm.trans h) (Ne.symm (hc2 q hq))
            · rcases hP'case with ⟨-, ht, -⟩ | ⟨-, ht, -⟩
              · exact Or.inr (ht.symm.trans h)
              · exact Or.inl (ht.symm.trans h)
          · intro x
            rcases hP'case with ⟨-, -, hs⟩ | ⟨-, -, hs⟩
            · rw [hs, List.mem_cons]
            · rw [hs, List.mem_cons, List.mem_reverse]
        · exact Or.inl hc
      have hend' : ∀ q ∈ L', 1 ≤ D₁.ends q.1 := by
        intro q hq
        have h1 := hends₁ q.1
        have := hend q (List.mem_cons_of_mem _ hq)
        simp only [Ne.symm (hc1 q hq), ite_false, add_zero] at h1
        omega
      have havoid' : ∀ q ∈ L', ∀ Q' ∈ D₁.paths, (Q'.src = q.1 ∨ Q'.tgt = q.1) →
          q.2 ∉ Q'.walk.support := by
        intro q hq Q' hQ' hq'
        have hqL : q ∈ p :: L' := List.mem_cons_of_mem _ hq
        rcases hcopy q hq Q' hQ' hq' with ⟨Q, hQ, hs, ht, hsupp⟩ | ⟨-, hPq, hsupp⟩
        · rw [hsupp]
          rw [hs, ht] at hq'
          exact havoid q hqL Q hQ hq'
        · rw [hsupp]
          rintro (h | h)
          · exact hsib p hp q hqL (Ne.symm (hc1 q hq)) h.symm P hP ⟨hPt, hPq⟩
          · exact havoid q hqL P hP hPq h
      have hsib' : ∀ q ∈ L', ∀ q' ∈ L', q.1 ≠ q'.1 → q.2 = q'.2 → ∀ Q' ∈ D₁.paths,
          ¬ ((Q'.src = q.1 ∨ Q'.tgt = q.1) ∧ (Q'.src = q'.1 ∨ Q'.tgt = q'.1)) := by
        intro q hq q' hq' hne hpar Q' hQ' ⟨h1, h2⟩
        have hqL : q ∈ p :: L' := List.mem_cons_of_mem _ hq
        have hq'L : q' ∈ p :: L' := List.mem_cons_of_mem _ hq'
        rcases hcopy q hq Q' hQ' h1 with ⟨Q, hQ, hs, ht, -⟩ | ⟨hQP, -, -⟩
        · rw [hs, ht] at h1 h2
          exact hsib q hqL q' hq'L hne hpar Q hQ ⟨h1, h2⟩
        · subst hQP
          rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
          · exact hne (h1.symm.trans h2)
          · exact hc2 q hq (h1.symm.trans hP'src)
          · exact hc2 q' hq' (h2.symm.trans hP'src)
          · exact hne (h1.symm.trans h2)
      obtain ⟨D', hD', hD'e⟩ :=
        append_forest_ends L' K₁ hG' hK' hndc.2 hnde.2 hpw' D₁ hend' havoid' hsib'
      have hsum : ∑ x, (D₁.ends x + (if p.1 = x then 1 else 0)) =
          ∑ x, (D.ends x + (if p.2 = x then 1 else 0)) :=
        Finset.sum_congr rfl (fun x _ => hends₁ x)
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hsum
      rw [D₁.sum_ends, D.sum_ends] at hsum
      refine ⟨D', by rw [hD']; omega, fun x => ?_⟩
      have h1 := hD'e x
      have h2 := hends₁ x
      rw [List.countP_cons, List.countP_cons]
      by_cases h₁ : p.1 = x <;> by_cases h₂ : p.2 = x <;> simp [h₁, h₂] at h1 h2 ⊢ <;> omega

end appendForestEnds

/-! ### The three-end test at one root, and the deletion step -/

section leaf2

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Test2 at `(z, r)`** (the conclusion of `Test2` at one root): `J − z` has a decomposition into
at most `|J|/2` paths with at least three ends at `r`. -/
def Test2At (J : SimpleGraph V) [DecidableRel J.Adj] (z r : V) : Prop :=
  ∀ hr : J.Adj z r, ∃ D : PathDecomp (delVert J z),
    D.size ≤ Fintype.card V / 2 ∧ 3 ≤ D.ends ⟨r, hr.ne'⟩

theorem test2_of_test2At (J : SimpleGraph V) [DecidableRel J.Adj] (z : V)
    (h : ∀ r, J.Adj z r → (∀ v, Even (J.degree v) ↔ v = z ∨ v = r) → Test2At J z r) :
    Test2 J z :=
  fun r hr hzr => h r hr hzr hr

/-- **The deletion step for Test2.** Let `r` have even degree `≥ 3` in `J`. If `G` is `J − z` with `z`
re-attached as a leaf at `r`, a decomposition of `G` into at most `|J|/2` paths with at least two
ends at `r` gives Test2 at `(z, r)`. -/
theorem test2At_of_leafDecomp (J : SimpleGraph V) [DecidableRel J.Adj] {G : SimpleGraph V}
    {z r : V} (hrev : J.degree r % 2 = 0) (hr3 : 3 ≤ J.degree r)
    (hz : ∀ x, G.Adj z x ↔ x = r) (hne : ∀ a b, a ≠ z → b ≠ z → (G.Adj a b ↔ J.Adj a b))
    (D₁ : PathDecomp G) (hsize : D₁.size ≤ Fintype.card V / 2) (hends : 2 ≤ D₁.ends r) :
    Test2At J z r := by
  intro hr
  let r' : {v | v ≠ z} := ⟨r, hr.ne'⟩
  let D₂ := D₁.mapInj (leafMap z) (leafMap_injective z) (leafMap_edge_gen hr.ne' hz hne)
    (leafMap_cov_gen hr.ne' hz hne)
  have hD₂ : D₂.size = D₁.size := PathDecomp.mapInj_size _ _ _ _ _
  have hD₂e : D₂.ends (some r') = D₁.ends r := by
    have h := PathDecomp.mapInj_ends D₁ (leafMap z) (leafMap_injective z)
      (leafMap_edge_gen hr.ne' hz hne) (leafMap_cov_gen hr.ne' hz hne) r
    rwa [show leafMap z r = some r' from leafMap_val z r'] at h
  obtain ⟨D₃, hD₃⟩ := PathDecomp.trim_ends (x := r') D₂
  have hdr : (delVert J z).degree r' + 1 = J.degree r := by
    have := delVert_degree (J := J) z r'
    simp only [show J.Adj (r' : V) z from hr.symm, ite_true] at this
    exact this
  have hodd : Odd ((delVert J z).degree r') := by rw [Nat.odd_iff]; omega
  have h3 : 3 ≤ (delVert J z).degree r' := by omega
  rcases hD₃ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨D₃, by omega, ?_⟩
    show 3 ≤ D₃.ends r'
    omega
  · obtain ⟨D, hDs, hDe⟩ := exists_three_ends (x := r') D₃ (k := Fintype.card V / 2 - 1)
      (by omega) hodd h3
    exact ⟨D, by omega, hDe⟩

end leaf2

/-! ### The forest data for Test2 and the lift -/

section forest2

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The edges `zv` (`v ∈ T`) at `z`. -/
def zDel2 (z : V) (T : List V) : List (Sym2 V) := T.map (fun v => s(z, v))

/-- **The Test2 forest base graph** `M = J − zT − Φ` (manuscript Definition 3.1). -/
abbrev forM2 (J : SimpleGraph V) (z : V) (T : List V) (L : List (V × V)) : SimpleGraph V :=
  delList J (zDel2 z T ++ L.map pairEdge)

/-- `J − zT`: the graph `J − z` with `z` attached as a leaf at `r`. -/
abbrev leafT2 (J : SimpleGraph V) (z : V) (T : List V) : SimpleGraph V := delList J (zDel2 z T)

/-- **Test2 forest data** at `(J, z, r)`: the list `T = N(z) − r`, and a forest `Φ` of `J − z` whose
odd-degree vertices are exactly `N(z)`, given by (child, parent) pairs in parent-first order,
with `r` never a child. -/
structure ForestData2 (J : SimpleGraph V) (z r : V) (T : List V) (L : List (V × V)) : Prop where
  nodup : (r :: T).Nodup
  nbr : ∀ v, J.Adj z v ↔ v = r ∨ v ∈ T
  edge : ∀ p ∈ L, J.Adj p.1 p.2
  avoid_z : ∀ p ∈ L, p.1 ≠ z ∧ p.2 ≠ z
  child_ne_r : ∀ p ∈ L, p.1 ≠ r
  children : (L.map Prod.fst).Nodup
  edges : (L.map pairEdge).Nodup
  parent_first : L.Pairwise (fun p q => p.2 ≠ q.1)
  tjoin : ∀ v, (L.map pairEdge).countP (fun e => decide (v ∈ e)) % 2 =
    if v = r ∨ v ∈ T then 1 else 0

/-- **A Test2 forest base**: forest data and a Lovász decomposition of `M` with (i) and (ii). -/
def ForestBase2 (J : SimpleGraph V) [DecidableRel J.Adj] (z r : V) : Prop :=
  ∃ T L, ForestData2 J z r T L ∧ ∃ D₀ : PathDecomp (forM2 J z T L),
    (∀ v, D₀.ends v = (forM2 J z T L).degree v % 2) ∧
    (∀ p ∈ L, ∀ P ∈ D₀.paths, (P.src = p.1 ∨ P.tgt = p.1) → p.2 ∉ P.walk.support) ∧
    (∀ p ∈ L, ∀ q ∈ L, p.1 ≠ q.1 → p.2 = q.2 → ∀ P ∈ D₀.paths,
      ¬ ((P.src = p.1 ∨ P.tgt = p.1) ∧ (P.src = q.1 ∨ P.tgt = q.1)))

section data

variable {J : SimpleGraph V} {z r : V} {T : List V} {L : List (V × V)}
  (hF : ForestData2 J z r T L)
include hF

omit [Fintype V] in
theorem ForestData2.facts : z ≠ r ∧ z ∉ T ∧ r ∉ T ∧ T.Nodup := by
  have hz := hF.nbr z
  simp only [SimpleGraph.irrefl, false_iff, not_or] at hz
  obtain ⟨h1, h2⟩ := hz
  have hnd := hF.nodup
  rw [List.nodup_cons] at hnd
  exact ⟨h1, h2, hnd.1, hnd.2⟩

omit [Fintype V] in
theorem ForestData2.mem_zDel2 {x y : V} :
    s(x, y) ∈ zDel2 z T ↔ (x = z ∧ y ∈ T) ∨ (y = z ∧ x ∈ T) := by
  simp only [zDel2, List.mem_map, Sym2.eq_iff]
  constructor
  · rintro ⟨v, hv, h⟩
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1 h2; exact Or.inl ⟨rfl, hv⟩
    · subst h1 h2; exact Or.inr ⟨rfl, hv⟩
  · rintro (⟨rfl, hy⟩ | ⟨rfl, hx⟩)
    · exact ⟨y, hy, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨x, hx, Or.inr ⟨rfl, rfl⟩⟩

omit [Fintype V] in
theorem ForestData2.pair_not_mem_zDel2 {p : V × V} (hp : p ∈ L) : pairEdge p ∉ zDel2 z T := by
  rw [pairEdge, hF.mem_zDel2]
  obtain ⟨h1, h2⟩ := hF.avoid_z p hp
  rintro (⟨h, -⟩ | ⟨h, -⟩)
  · exact h1 h
  · exact h2 h

omit [Fintype V] in
theorem ForestData2.leafT2_adj_z {x : V} : (leafT2 J z T).Adj z x ↔ x = r := by
  obtain ⟨hzr, hzT, hrT, -⟩ := hF.facts
  show J.Adj z x ∧ s(z, x) ∉ zDel2 z T ↔ x = r
  rw [hF.mem_zDel2, hF.nbr x]
  constructor
  · rintro ⟨h | h, hn⟩
    · exact h
    · exact absurd (Or.inl ⟨rfl, h⟩) hn
  · rintro rfl
    refine ⟨Or.inl rfl, ?_⟩
    rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact hrT h
    · exact hzr h.symm

omit [Fintype V] in
theorem ForestData2.leafT2_adj_ne {a b : V} (ha : a ≠ z) (hb : b ≠ z) :
    (leafT2 J z T).Adj a b ↔ J.Adj a b := by
  show J.Adj a b ∧ s(a, b) ∉ zDel2 z T ↔ J.Adj a b
  rw [hF.mem_zDel2]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rintro (⟨h, -⟩ | ⟨h, -⟩)
  · exact ha h
  · exact hb h

omit [Fintype V] in
theorem ForestData2.leafT2_edgeSet (e : Sym2 V) :
    e ∈ (leafT2 J z T).edgeSet ↔ e ∈ (forM2 J z T L).edgeSet ∨ e ∈ L.map pairEdge := by
  rw [delList_edgeSet, delList_edgeSet, List.mem_append]
  constructor
  · rintro ⟨he, hn⟩
    by_cases hm : e ∈ L.map pairEdge
    · exact Or.inr hm
    · exact Or.inl ⟨he, by tauto⟩
  · rintro (⟨he, hn⟩ | hm)
    · exact ⟨he, fun h => hn (Or.inl h)⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
      exact ⟨hF.edge p hp, hF.pair_not_mem_zDel2 hp⟩

variable [DecidableRel J.Adj]

omit [Fintype V] [DecidableRel J.Adj] in
/-- The edges deleted from `J` to form `M` are distinct edges of `J`. -/
theorem ForestData2.del_facts :
    (zDel2 z T ++ L.map pairEdge).Nodup ∧ ∀ e ∈ zDel2 z T ++ L.map pairEdge, e ∈ J.edgeSet := by
  obtain ⟨hzr, hzT, hrT, hTnd⟩ := hF.facts
  refine ⟨?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨?_, hF.edges, ?_⟩
    · refine hTnd.map_on ?_
      intro a _ b _ h
      rcases Sym2.eq_iff.1 h with ⟨-, h⟩ | ⟨h1, h2⟩
      · exact h
      · exact h2.trans h1
    · intro e he e' he' hee
      subst hee
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he'
      exact hF.pair_not_mem_zDel2 hp he
  · intro e he
    rcases List.mem_append.1 he with he | he
    · rw [zDel2, List.mem_map] at he
      obtain ⟨v, hv, rfl⟩ := he
      exact (hF.nbr v).2 (Or.inr hv)
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
      exact hF.edge p hp

omit [Fintype V] [DecidableRel J.Adj] in
/-- The number of deleted edges at `v`. -/
theorem ForestData2.count_del (v : V) :
    (zDel2 z T ++ L.map pairEdge).countP (fun e => decide (v ∈ e)) =
      (if v = z then T.length else 0) + (if v ∈ T then 1 else 0) +
        (L.map pairEdge).countP (fun e => decide (v ∈ e)) := by
  obtain ⟨hzr, hzT, hrT, hTnd⟩ := hF.facts
  rw [List.countP_append, zDel2, List.countP_map]
  by_cases hvz : v = z
  · subst hvz
    have hall : T.countP ((fun e => decide (v ∈ e)) ∘ fun x => s(v, x)) = T.length :=
      List.countP_eq_length.mpr (fun x _ => by simp)
    rw [hall]
    simp [hzT]
  · have hcnt : T.countP ((fun e => decide (v ∈ e)) ∘ fun x => s(z, x)) = T.count v := by
      rw [List.count]
      apply List.countP_congr
      intro x _
      simp only [Function.comp_apply, decide_eq_true_eq, beq_iff_eq, Sym2.mem_iff, hvz,
        false_or]
      exact eq_comm
    rw [hcnt]
    by_cases hvT : v ∈ T
    · rw [List.count_eq_one_of_mem hTnd hvT]
      simp [hvz, hvT]
    · rw [List.count_eq_zero_of_not_mem hvT]
      simp [hvz, hvT]

theorem ForestData2.forM2_degree (v : V) :
    (forM2 J z T L).degree v + ((if v = z then T.length else 0) + (if v ∈ T then 1 else 0) +
      (L.map pairEdge).countP (fun e => decide (v ∈ e))) = J.degree v := by
  rw [← hF.count_del v]
  exact delList_degree_count J _ hF.del_facts.1 hF.del_facts.2 v

/-- In `M`, every child has odd degree. -/
theorem ForestData2.forM2_odd_child (hzr : ∀ v, Even (J.degree v) ↔ v = z ∨ v = r)
    {p : V × V} (hp : p ∈ L) : (forM2 J z T L).degree p.1 % 2 = 1 := by
  obtain ⟨h1, -⟩ := hF.avoid_z p hp
  have hr := hF.child_ne_r p hp
  have h := hF.forM2_degree p.1
  have ht := hF.tjoin p.1
  simp only [h1, hr, ite_false, zero_add, false_or] at h ht
  have hodd : J.degree p.1 % 2 = 1 :=
    Nat.odd_iff.mp (Nat.not_even_iff_odd.mp (fun he => by
      rcases (hzr p.1).1 he with h' | h'
      · exact h1 h'
      · exact hr h'))
  split_ifs at h ht <;> omega

/-- In `M`, the root `r` has odd degree. -/
theorem ForestData2.forM2_odd_r (hzr : ∀ v, Even (J.degree v) ↔ v = z ∨ v = r) :
    (forM2 J z T L).degree r % 2 = 1 := by
  obtain ⟨hzr', -, hrT, -⟩ := hF.facts
  have h := hF.forM2_degree r
  have ht := hF.tjoin r
  simp only [Ne.symm hzr', hrT, ite_false, ite_true, zero_add, true_or] at h ht
  have hev : J.degree r % 2 = 0 := Nat.even_iff.mp ((hzr r).2 (Or.inr rfl))
  omega

omit [Fintype V] [DecidableRel J.Adj] in
/-- `r` is the parent of at least one pair (it has odd degree in `Φ` and is never a child). -/
theorem ForestData2.one_le_children_r : 1 ≤ L.countP (fun p => decide (p.2 = r)) := by
  have ht := hF.tjoin r
  simp only [true_or, ite_true] at ht
  have hpos : 0 < (L.map pairEdge).countP (fun e => decide (r ∈ e)) := by omega
  obtain ⟨e, he, hre⟩ := List.countP_pos_iff.mp hpos
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
  have hr : r ∈ s(p.1, p.2) := by simpa [pairEdge] using hre
  rcases Sym2.mem_iff.mp hr with h | h
  · exact absurd h.symm (hF.child_ne_r p hp)
  · exact List.countP_pos_iff.mpr ⟨p, hp, by simp [h]⟩

omit [Fintype V] [DecidableRel J.Adj] in
theorem ForestData2.no_child_r : L.countP (fun p => decide (p.1 = r)) = 0 :=
  List.countP_eq_zero.mpr (fun p hp => by simpa using hF.child_ne_r p hp)

/-- Every decomposition of a graph on `V` with at most one end per vertex has at most `|V|/2` paths;
in particular every Lovász decomposition of `M` does. -/
theorem ForestData2.forM2_size (D₀ : PathDecomp (forM2 J z T L))
    (hD₀ : ∀ v, D₀.ends v = (forM2 J z T L).degree v % 2) :
    D₀.size ≤ Fintype.card V / 2 := by
  have h2 : 2 * D₀.size ≤ Fintype.card V := by
    rw [← D₀.sum_ends]
    have h1 : ∑ v, D₀.ends v ≤ ∑ _v : V, 1 :=
      Finset.sum_le_sum fun v _ => by
        rw [hD₀ v]
        exact Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    simpa using h1
  omega

end data

/-- **The forest lift for Test2** (manuscript Theorem 3.2). If `z, r` are the only even vertices of
`J`, `d(r) ≥ 3`, and `(J, z, r)` has a Test2 forest base, then Test2 holds at `(z, r)`. -/
theorem test2At_of_forestBase2 (J : SimpleGraph V) [DecidableRel J.Adj] {z r : V}
    (hzr : ∀ v, Even (J.degree v) ↔ v = z ∨ v = r) (hr3 : 3 ≤ J.degree r)
    (h : ForestBase2 J z r) : Test2At J z r := by
  obtain ⟨T, L, hF, D₀, hD₀, hi, hii⟩ := h
  have hend : ∀ p ∈ L, 1 ≤ D₀.ends p.1 := fun p hp => by
    rw [hD₀, hF.forM2_odd_child hzr hp]
  have hnotM : ∀ p ∈ L, ¬ (forM2 J z T L).Adj p.1 p.2 := fun p hp h =>
    h.2 (List.mem_append_right _ (List.mem_map_of_mem hp))
  obtain ⟨D₁, hD₁, hD₁e⟩ := append_forest_ends (G := leafT2 J z T) L (forM2 J z T L)
    hF.leafT2_edgeSet hnotM hF.children hF.edges hF.parent_first D₀ hend hi hii
  have hr1 : D₀.ends r = 1 := by rw [hD₀, hF.forM2_odd_r hzr]
  have hends : 2 ≤ D₁.ends r := by
    have := hD₁e r
    rw [hF.no_child_r, hr1] at this
    have := hF.one_le_children_r
    omega
  have hrev : J.degree r % 2 = 0 := Nat.even_iff.mp ((hzr r).2 (Or.inr rfl))
  exact test2At_of_leafDecomp J hrev hr3 (fun _ => hF.leafT2_adj_z)
    (fun _ _ ha hb => hF.leafT2_adj_ne ha hb) D₁ (hD₁ ▸ hF.forM2_size D₀ hD₀) hends

/-- **Test2 from forest bases**: if every neighbour of `z` has degree at least three and every root
`r` at which `z, r` are the only even vertices has a Test2 forest base, then `Test2 J z`. -/
theorem test2_of_forestBases2 (J : SimpleGraph V) [DecidableRel J.Adj] (z : V)
    (hdeg : ∀ r, J.Adj z r → 3 ≤ J.degree r)
    (h : ∀ r, J.Adj z r → (∀ v, Even (J.degree v) ↔ v = z ∨ v = r) → ForestBase2 J z r) :
    Test2 J z :=
  test2_of_test2At J z fun r hr hzr => test2At_of_forestBase2 J hzr (hdeg r hr) (h r hr hzr)

end forest2

end Gallai
