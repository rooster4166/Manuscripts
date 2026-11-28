import GallaiLean.ForestLift
import GallaiLean.TriangleBase
import GallaiLean.TRNSteer

/-!
# The forest lift to Test2 (session `claude/test2`)

Manuscript: `manuscripts/test2/test2.tex`, §3 (the forest lift for the three-end test).

Let `z, r` be the only even vertices of `J`, adjacent, with `d(r) ≥ 3`. Put `T = N(z) − r` (a list)
and let `Φ` be a set of edges of `J − z` whose odd-degree vertices are exactly `N(z) = T ∪ {r}`,
given as a list `L` of (child, parent) pairs `(v, p(v))` in parent-first order, with distinct
children and edges, and **if `r` is a child then `r` has at least two children**.
Put `M = J − zT − Φ` (`forM2`): `z` is a leaf at `r`, and every vertex of `M` has odd degree.
If `M` has a Lovász decomposition with
* (i) the path ending at each child `v` avoids `p(v)`, and
* (ii) no path has two siblings as its two ends,
then Test2 holds at `(z, r)` (**`test2At_of_forestBase2`**).

Compared with the Test1 lift (`test1At_of_forestBase`) there is no vertex `w`: the odd set of `Φ`
is all of `N(z)`, and `r` itself is in it. In `M` the vertex `r` has odd degree, so it ends one
path; after the appends it ends `1 − [r is a child] + c(r) ≥ 2` paths, and trimming the leaf `z`
gives one more.

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
odd-degree vertices are exactly `N(z)`, given by (child, parent) pairs in parent-first order;
if `r` is a child, it has at least two children. -/
structure ForestData2 (J : SimpleGraph V) (z r : V) (T : List V) (L : List (V × V)) : Prop where
  nodup : (r :: T).Nodup
  nbr : ∀ v, J.Adj z v ↔ v = r ∨ v ∈ T
  edge : ∀ p ∈ L, J.Adj p.1 p.2
  avoid_z : ∀ p ∈ L, p.1 ≠ z ∧ p.2 ≠ z
  r_child : (∃ p ∈ L, p.1 = r) → 2 ≤ L.countP (fun p => decide (p.2 = r))
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

/-- In `M`, the vertex `r` has odd degree. -/
theorem ForestData2.forM2_odd_r (hzr : ∀ v, Even (J.degree v) ↔ v = z ∨ v = r) :
    (forM2 J z T L).degree r % 2 = 1 := by
  obtain ⟨hzr', -, hrT, -⟩ := hF.facts
  have h := hF.forM2_degree r
  have ht := hF.tjoin r
  simp only [Ne.symm hzr', hrT, ite_false, ite_true, zero_add, true_or] at h ht
  have hev : J.degree r % 2 = 0 := Nat.even_iff.mp ((hzr r).2 (Or.inr rfl))
  omega

/-- In `M`, every child has odd degree. -/
theorem ForestData2.forM2_odd_child (hzr : ∀ v, Even (J.degree v) ↔ v = z ∨ v = r)
    {p : V × V} (hp : p ∈ L) : (forM2 J z T L).degree p.1 % 2 = 1 := by
  obtain ⟨h1, -⟩ := hF.avoid_z p hp
  by_cases hr : p.1 = r
  · rw [hr]; exact hF.forM2_odd_r hzr
  have h := hF.forM2_degree p.1
  have ht := hF.tjoin p.1
  simp only [h1, hr, ite_false, zero_add, false_or] at h ht
  have hodd : J.degree p.1 % 2 = 1 :=
    Nat.odd_iff.mp (Nat.not_even_iff_odd.mp (fun he => by
      rcases (hzr p.1).1 he with h' | h'
      · exact h1 h'
      · exact hr h'))
  split_ifs at h ht <;> omega

omit [Fintype V] [DecidableRel J.Adj] in
/-- If `r` is not a child, it is the parent of at least one pair (it has odd degree in `Φ`). -/
theorem ForestData2.one_le_children_r (hnc : ∀ p ∈ L, p.1 ≠ r) :
    1 ≤ L.countP (fun p => decide (p.2 = r)) := by
  have ht := hF.tjoin r
  simp only [true_or, ite_true] at ht
  have hpos : 0 < (L.map pairEdge).countP (fun e => decide (r ∈ e)) := by omega
  obtain ⟨e, he, hre⟩ := List.countP_pos_iff.mp hpos
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
  have hr : r ∈ s(p.1, p.2) := by simpa [pairEdge] using hre
  rcases Sym2.mem_iff.mp hr with h | h
  · exact absurd h.symm (hnc p hp)
  · exact List.countP_pos_iff.mpr ⟨p, hp, by simp [h]⟩

omit [Fintype V] [DecidableRel J.Adj] in
/-- `r` is a child at most once (children are distinct). -/
theorem ForestData2.child_r_le_one : L.countP (fun p => decide (p.1 = r)) ≤ 1 := by
  have h := List.nodup_iff_count_le_one.mp hF.children r
  rw [List.count, List.countP_map] at h
  refine le_trans (le_of_eq ?_) h
  apply List.countP_congr
  intro p _
  simp [Function.comp_def]

omit [Fintype V] [DecidableRel J.Adj] in
/-- `r` ends at least two paths after the appends: its own end, minus one if it is a child, plus
one per child. -/
theorem ForestData2.two_le_r_count :
    2 ≤ 1 + L.countP (fun p => decide (p.2 = r)) - L.countP (fun p => decide (p.1 = r)) := by
  by_cases hc : ∃ p ∈ L, p.1 = r
  · have h2 := hF.r_child hc
    have h1 := hF.child_r_le_one
    omega
  · have hnc : ∀ p ∈ L, p.1 ≠ r := fun p hp h => hc ⟨p, hp, h⟩
    have h1 := hF.one_le_children_r hnc
    have h0 : L.countP (fun p => decide (p.1 = r)) = 0 :=
      List.countP_eq_zero.mpr (fun p hp => by simpa using hnc p hp)
    omega

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
    rw [hr1] at this
    have := hF.two_le_r_count
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

/-! ### The floor lift -/

section floor

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **Floor forest data** on a graph `B` whose even vertices are `w` and the list `T`: a forest `Φ` of
`B` whose odd-degree vertices are exactly `T`, given by (child, parent) pairs in parent-first order,
with `w` never a child. -/
structure FloorData (B : SimpleGraph W) (w : W) (T : List W) (L : List (W × W)) : Prop where
  edge : ∀ p ∈ L, B.Adj p.1 p.2
  w_not_mem : w ∉ T
  child_ne_w : ∀ p ∈ L, p.1 ≠ w
  children : (L.map Prod.fst).Nodup
  edges : (L.map pairEdge).Nodup
  parent_first : L.Pairwise (fun p q => p.2 ≠ q.1)
  tjoin : ∀ v, (L.map pairEdge).countP (fun e => decide (v ∈ e)) % 2 = if v ∈ T then 1 else 0

/-- **A floor base**: floor data and a Lovász decomposition of `B − Φ` with (i) and (ii). -/
def FloorBase (B : SimpleGraph W) [DecidableRel B.Adj] (w : W) (T : List W) : Prop :=
  ∃ L, FloorData B w T L ∧ ∃ D₀ : PathDecomp (delList B (L.map pairEdge)),
    (∀ v, D₀.ends v = (delList B (L.map pairEdge)).degree v % 2) ∧
    (∀ p ∈ L, ∀ P ∈ D₀.paths, (P.src = p.1 ∨ P.tgt = p.1) → p.2 ∉ P.walk.support) ∧
    (∀ p ∈ L, ∀ q ∈ L, p.1 ≠ q.1 → p.2 = q.2 → ∀ P ∈ D₀.paths,
      ¬ ((P.src = p.1 ∨ P.tgt = p.1) ∧ (P.src = q.1 ∨ P.tgt = q.1)))

/-- **The floor lift** (manuscript Theorem 4.1). If the even vertices of `B` are exactly `w` and the
vertices of `T`, a floor base gives a decomposition of `B` into at most `(|B| − 1)/2` paths. -/
theorem floor_of_floorBase (B : SimpleGraph W) [DecidableRel B.Adj] {w : W} {T : List W}
    (hev : ∀ v, Even (B.degree v) ↔ v = w ∨ v ∈ T) (h : FloorBase B w T) :
    ∃ D : PathDecomp B, D.size ≤ (Fintype.card W - 1) / 2 := by
  obtain ⟨L, hF, D₀, hD₀, hi, hii⟩ := h
  have hnd : (L.map pairEdge).Nodup := hF.edges
  have hin : ∀ e ∈ L.map pairEdge, e ∈ B.edgeSet := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    exact hF.edge p hp
  have hdeg := delList_degree_count B (L.map pairEdge) hnd hin
  -- children are odd in `B − Φ`
  have hend : ∀ p ∈ L, 1 ≤ D₀.ends p.1 := by
    intro p hp
    rw [hD₀]
    have h1 := hdeg p.1
    have ht := hF.tjoin p.1
    have hw := hF.child_ne_w p hp
    have hpar := hev p.1
    by_cases hT : p.1 ∈ T
    · have he : Even (B.degree p.1) := hpar.2 (Or.inr hT)
      rw [Nat.even_iff] at he
      simp only [hT, ite_true] at ht
      omega
    · have ho : ¬ Even (B.degree p.1) := fun he => by
        rcases hpar.1 he with h' | h'
        · exact hw h'
        · exact hT h'
      rw [Nat.not_even_iff] at ho
      simp only [hT, ite_false] at ht
      omega
  have hnotK : ∀ p ∈ L, ¬ (delList B (L.map pairEdge)).Adj p.1 p.2 := fun p hp h =>
    h.2 (List.mem_map_of_mem hp)
  have hG : ∀ e, e ∈ B.edgeSet ↔ e ∈ (delList B (L.map pairEdge)).edgeSet ∨ e ∈ L.map pairEdge := by
    intro e
    rw [delList_edgeSet]
    constructor
    · intro he
      by_cases hm : e ∈ L.map pairEdge
      · exact Or.inr hm
      · exact Or.inl ⟨he, hm⟩
    · rintro (⟨he, -⟩ | hm)
      · exact he
      · exact hin e hm
  obtain ⟨D, hD⟩ := append_forest (G := B) L (delList B (L.map pairEdge)) hG hnotK hF.children
    hF.edges hF.parent_first D₀ hend hi hii
  refine ⟨D, ?_⟩
  -- `w` is even in `B − Φ`, every vertex has at most one end
  have hw0 : D₀.ends w = 0 := by
    rw [hD₀]
    have h1 := hdeg w
    have ht := hF.tjoin w
    have he : Even (B.degree w) := (hev w).2 (Or.inl rfl)
    rw [Nat.even_iff] at he
    simp only [hF.w_not_mem, ite_false] at ht
    omega
  have h2 : 2 * D₀.size ≤ Fintype.card W - 1 := by
    rw [← D₀.sum_ends]
    have h1 : ∑ v, D₀.ends v ≤ ∑ v, (if v ≠ w then 1 else 0) :=
      Finset.sum_le_sum fun v _ => by
        by_cases hv : v = w
        · subst hv; simp [hw0]
        · simp only [hv, ne_eq, not_false_eq_true, ite_true]
          rw [hD₀ v]
          exact Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    refine h1.trans (le_of_eq ?_)
    rw [← Finset.card_filter, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
  omega

end floor

section floorT2

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **The floor gives Test2.** If `r` has even degree `≥ 3` in `J` and `J − z` has a decomposition
into at most `(|J| − 2)/2` paths, then Test2 holds at `(z, r)` (split once at `r`). -/
theorem test2At_of_floor (J : SimpleGraph V) [DecidableRel J.Adj] {z r : V}
    (hrev : J.degree r % 2 = 0) (hr3 : 3 ≤ J.degree r)
    (h : ∃ D : PathDecomp (delVert J z), D.size ≤ (Fintype.card V - 2) / 2) : Test2At J z r := by
  intro hr
  obtain ⟨D, hD⟩ := h
  let r' : {v | v ≠ z} := ⟨r, hr.ne'⟩
  have hdr : (delVert J z).degree r' + 1 = J.degree r := by
    have := delVert_degree (J := J) z r'
    simp only [show J.Adj (r' : V) z from hr.symm, ite_true] at this
    exact this
  have hodd : Odd ((delVert J z).degree r') := by rw [Nat.odd_iff]; omega
  have h3 : 3 ≤ (delVert J z).degree r' := by omega
  have hcard : 2 ≤ Fintype.card V := by
    have := Finset.card_le_univ ({z, r} : Finset V)
    rw [Finset.card_pair hr.ne] at this; exact this
  obtain ⟨D', h1, h2⟩ := exists_three_ends (x := r') D (k := (Fintype.card V - 2) / 2) hD hodd h3
  exact ⟨D', by omega, h2⟩

/-- In a Test2 instance, the even vertices of `J − z` are exactly the neighbours of `z` other
than `r`. -/
theorem even_delVert_iff (J : SimpleGraph V) [DecidableRel J.Adj] {z r : V}
    (hzr : ∀ v, Even (J.degree v) ↔ v = z ∨ v = r) (hr : J.Adj z r) (v : {v | v ≠ z}) :
    Even ((delVert J z).degree v) ↔ J.Adj z v ∧ (v : V) ≠ r := by
  have hd := delVert_degree (J := J) z v
  have hvz : (v : V) ≠ z := v.2
  have hpar := hzr v
  rw [Nat.even_iff, ← J.adj_comm]
  by_cases ha : J.Adj (v : V) z
  · simp only [ha, ite_true] at hd
    by_cases hvr : (v : V) = r
    · have : J.degree v % 2 = 0 := Nat.even_iff.mp (hpar.2 (Or.inr hvr))
      simp only [hvr, ne_eq, not_true_eq_false, and_false, iff_false]
      omega
    · have : J.degree v % 2 = 1 :=
        Nat.odd_iff.mp (Nat.not_even_iff_odd.mp (fun he => by
          rcases hpar.1 he with h | h
          · exact hvz h
          · exact hvr h))
      simp only [ha, ne_eq, hvr, not_false_eq_true, and_self, iff_true]
      omega
  · simp only [ha, ite_false, add_zero] at hd
    simp only [ha, false_and, iff_false]
    by_cases hvr : (v : V) = r
    · exact absurd (hvr ▸ hr.symm) ha
    · have : J.degree v % 2 = 1 :=
        Nat.odd_iff.mp (Nat.not_even_iff_odd.mp (fun he => by
          rcases hpar.1 he with h | h
          · exact hvz h
          · exact hvr h))
      omega

/-- **The floor lift for Test2** (manuscript Corollary 4.2). Let `z, r` be the only even vertices
of `J`, adjacent, `d(r) ≥ 3`, and let `w`, `T` list the even vertices of `J − z` (that is,
`N(z) − r`). A floor base of `J − z` gives Test2 at `(z, r)`. -/
theorem test2At_of_floorBase (J : SimpleGraph V) [DecidableRel J.Adj] {z r : V}
    (hzr : ∀ v, Even (J.degree v) ↔ v = z ∨ v = r) (hr3 : 3 ≤ J.degree r)
    {w : {v | v ≠ z}} {T : List {v | v ≠ z}}
    (hT : ∀ v : {v | v ≠ z}, (J.Adj z v ∧ (v : V) ≠ r) ↔ v = w ∨ v ∈ T)
    (h : FloorBase (delVert J z) w T) : Test2At J z r := by
  intro hr
  have hev : ∀ v, Even ((delVert J z).degree v) ↔ v = w ∨ v ∈ T := fun v =>
    (even_delVert_iff J hzr hr v).trans (hT v)
  obtain ⟨D, hD⟩ := floor_of_floorBase (delVert J z) hev h
  have hcard := card_delVert (W := V) z
  have hrev : J.degree r % 2 = 0 := Nat.even_iff.mp ((hzr r).2 (Or.inr rfl))
  exact test2At_of_floor J hrev hr3 ⟨D, by rw [hcard] at hD; omega⟩ hr

end floorT2

/-! ### The matching case of the floor lift, and DL -/

section floorMatching

variable {W : Type*} [Fintype W] [DecidableEq W]

omit [Fintype W] in
/-- The edges of a list of disjoint pairs are distinct. -/
theorem nodup_map_pairEdge :
    ∀ (L : List (W × W)), (pairVerts L).Nodup → (L.map pairEdge).Nodup
  | [], _ => List.nodup_nil
  | p :: L', hnd => by
    rw [pairVerts_cons, List.nodup_cons, List.nodup_cons] at hnd
    obtain ⟨hp1, hp2, hnd'⟩ := hnd
    rw [List.mem_cons, not_or] at hp1
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_pairEdge L' hnd'⟩
    intro hm
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hm
    have h1 : p.1 ∈ pairEdge q := by rw [hqe]; simp [pairEdge]
    simp only [pairEdge, Sym2.mem_iff] at h1
    rcases h1 with h | h
    · exact hp1.2 (h ▸ fst_mem_pairVerts hq)
    · exact hp1.2 (h ▸ snd_mem_pairVerts hq)

omit [Fintype W] in
/-- A list of disjoint pairs meets each vertex of its support in exactly one edge. -/
theorem countP_pairEdge_of_nodup :
    ∀ (L : List (W × W)), (pairVerts L).Nodup → ∀ v,
      (L.map pairEdge).countP (fun e => decide (v ∈ e)) = if v ∈ pairVerts L then 1 else 0
  | [], _, v => by simp [pairVerts]
  | p :: L', hnd, v => by
    rw [pairVerts_cons, List.nodup_cons, List.nodup_cons] at hnd
    obtain ⟨hp1, hp2, hnd'⟩ := hnd
    rw [List.mem_cons, not_or] at hp1
    have ih := countP_pairEdge_of_nodup L' hnd' v
    rw [List.map_cons, List.countP_cons, ih]
    simp only [pairVerts_cons, List.mem_cons, pairEdge, Sym2.mem_iff]
    by_cases h1 : v = p.1
    · subst h1
      simp [hp1.2]
    · by_cases h2 : v = p.2
      · subst h2
        simp [hp2, h1]
      · simp [h1, h2]

/-- **The floor lift, matching case** (manuscript Theorem 4.1 with `Φ` a matching). If the even
vertices of `B` are `w` and the vertices of the disjoint pairs `L` (edges of `B`), a Lovász
decomposition of `B − L` satisfying the disjunction of every pair gives a decomposition of `B` into
at most `(|B| − 1)/2` paths. -/
theorem floor_of_matchingBase (B : SimpleGraph W) [DecidableRel B.Adj] {w : W} {L : List (W × W)}
    (hev : ∀ v, Even (B.degree v) ↔ v = w ∨ v ∈ pairVerts L) (hnd : (pairVerts L).Nodup)
    (hw : w ∉ pairVerts L) (hedge : ∀ p ∈ L, B.Adj p.1 p.2)
    (D₀ : PathDecomp (delList B (L.map pairEdge)))
    (hD₀ : ∀ v, D₀.ends v = (delList B (L.map pairEdge)).degree v % 2)
    (hdisj : TriangleDisj D₀ L) :
    ∃ D : PathDecomp B, D.size ≤ (Fintype.card W - 1) / 2 := by
  have hin : ∀ e ∈ L.map pairEdge, e ∈ B.edgeSet := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    exact hedge p hp
  have hnde : (L.map pairEdge).Nodup := nodup_map_pairEdge L hnd
  have hdeg := delList_degree_count B (L.map pairEdge) hnde hin
  have hcnt := countP_pairEdge_of_nodup L hnd
  have hodd : ∀ v ∈ pairVerts L, (delList B (L.map pairEdge)).degree v % 2 = 1 := by
    intro v hv
    have h1 := hdeg v
    rw [hcnt v, if_pos hv] at h1
    have he := (hev v).2 (Or.inr hv)
    rw [Nat.even_iff] at he
    omega
  have hnotK : ∀ p ∈ L, ¬ (delList B (L.map pairEdge)).Adj p.1 p.2 := fun p hp h =>
    h.2 (List.mem_map_of_mem hp)
  have hG : ∀ e, e ∈ B.edgeSet ↔ e ∈ (delList B (L.map pairEdge)).edgeSet ∨ e ∈ L.map pairEdge := by
    intro e
    rw [delList_edgeSet]
    constructor
    · intro he
      by_cases hm : e ∈ L.map pairEdge
      · exact Or.inr hm
      · exact Or.inl ⟨he, hm⟩
    · rintro (⟨he, -⟩ | hm)
      · exact he
      · exact hin e hm
  obtain ⟨D, hD⟩ := append_pairs (G := B) L (delList B (L.map pairEdge)) hG hnotK hnd D₀
    (fun p hp => ⟨by rw [hD₀, hodd p.1 (fst_mem_pairVerts hp)],
      by rw [hD₀, hodd p.2 (snd_mem_pairVerts hp)]⟩) hdisj
  refine ⟨D, ?_⟩
  have hw0 : D₀.ends w = 0 := by
    rw [hD₀]
    have h1 := hdeg w
    rw [hcnt w, if_neg hw] at h1
    have he := (hev w).2 (Or.inl rfl)
    rw [Nat.even_iff] at he
    omega
  have h2 : 2 * D₀.size ≤ Fintype.card W - 1 := by
    rw [← D₀.sum_ends]
    have h1 : ∑ v, D₀.ends v ≤ ∑ v, (if v ≠ w then 1 else 0) :=
      Finset.sum_le_sum fun v _ => by
        by_cases hv : v = w
        · subst hv; simp [hw0]
        · simp only [hv, ne_eq, not_false_eq_true, ite_true]
          rw [hD₀ v]
          exact Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    refine h1.trans (le_of_eq ?_)
    rw [← Finset.card_filter, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
  omega

end floorMatching

section floorDL

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **DL gives Test2** (manuscript Corollary 4.4). Let `z, r` be the only even vertices of `J`,
adjacent, `d(r) ≥ 3`; let `w ∈ N(z) − r` and let `L` be disjoint pairs, edges of `J − z`, covering
exactly `N(z) − {r, w}`. If no pair is a pair of universal twins of its component of
`(J − z) − L`, then Conjecture DL gives Test2 at `(z, r)` (through the floor of `J − z`). -/
theorem test2At_of_disjL1 (hDL : DisjL1.{u}) (J : SimpleGraph V) [DecidableRel J.Adj] {z r : V}
    (hzr : ∀ v, Even (J.degree v) ↔ v = z ∨ v = r) (hr3 : 3 ≤ J.degree r)
    {w : {v | v ≠ z}} {L : List ({v | v ≠ z} × {v | v ≠ z})}
    (hT : ∀ v : {v | v ≠ z}, (J.Adj z v ∧ (v : V) ≠ r) ↔ v = w ∨ v ∈ pairVerts L)
    (hnd : (pairVerts L).Nodup) (hw : w ∉ pairVerts L)
    (hedge : ∀ p ∈ L, (delVert J z).Adj p.1 p.2)
    (htw : ∀ p ∈ L, ¬ UnivTwins (delList (delVert J z) (L.map pairEdge)) p.1 p.2) :
    Test2At J z r := by
  intro hr
  set B := delVert J z with hB
  have hev : ∀ v, Even (B.degree v) ↔ v = w ∨ v ∈ pairVerts L := fun v =>
    (even_delVert_iff J hzr hr v).trans (hT v)
  -- parities in `G = B − L`
  have hin : ∀ e ∈ L.map pairEdge, e ∈ B.edgeSet := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    exact hedge p hp
  have hnde : (L.map pairEdge).Nodup := nodup_map_pairEdge L hnd
  have hdeg := delList_degree_count B (L.map pairEdge) hnde hin
  have hcnt := countP_pairEdge_of_nodup L hnd
  have hpar : ∀ v, (delList B (L.map pairEdge)).degree v % 2 = if v = w then 0 else 1 := by
    intro v
    have h1 := hdeg v
    rw [hcnt v] at h1
    by_cases hvw : v = w
    · subst hvw
      rw [if_neg hw] at h1
      have he := (hev v).2 (Or.inl rfl)
      rw [Nat.even_iff] at he
      simp only [ite_true]
      omega
    · rw [if_neg hvw]
      by_cases hv : v ∈ pairVerts L
      · rw [if_pos hv] at h1
        have he := (hev v).2 (Or.inr hv)
        rw [Nat.even_iff] at he
        omega
      · rw [if_neg hv] at h1
        have ho : ¬ Even (B.degree v) := fun he => by
          rcases (hev v).1 he with h | h
          · exact hvw h
          · exact hv h
        rw [Nat.not_even_iff] at ho
        omega
  have hevG : (evenSet (delList B (L.map pairEdge))).card ≤ 1 := by
    have hsub : evenSet (delList B (L.map pairEdge)) ⊆ {w} := by
      intro v hv
      simp only [evenSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      rw [Finset.mem_singleton]
      by_contra hvw
      have := hpar v
      rw [if_neg hvw] at this
      exact (Nat.not_even_iff.mpr this) hv.2
    exact (Finset.card_le_card hsub).trans (by simp)
  obtain ⟨D₀, hD₀, hdisj⟩ := hDL _ (delList B (L.map pairEdge)) hevG L hnd (by
    intro p hp
    have hw1 : p.1 ≠ w := fun h => hw (h ▸ fst_mem_pairVerts hp)
    have hw2 : p.2 ≠ w := fun h => hw (h ▸ snd_mem_pairVerts hp)
    have h1 := hpar p.1
    have h2 := hpar p.2
    rw [if_neg hw1] at h1
    rw [if_neg hw2] at h2
    exact ⟨h1, h2, fun h => h.2 (List.mem_map_of_mem hp), htw p hp⟩)
  obtain ⟨D, hD⟩ := floor_of_matchingBase B hev hnd hw hedge D₀ hD₀ hdisj
  have hcard := card_delVert (W := V) z
  have hrev : J.degree r % 2 = 0 := Nat.even_iff.mp ((hzr r).2 (Or.inr rfl))
  exact test2At_of_floor J hrev hr3 ⟨D, by rw [hcard] at hD; omega⟩ hr

end floorDL

/-! ### One pair: deletion degree four, from separation and two-token steering -/

section onePair

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Parities after deleting a matching: if the even vertices of `B` are `w` and the vertices of the
disjoint pairs `L`, then in `B − L` only `w` is even. -/
theorem delPairs_degree_mod {W : Type*} [Fintype W] [DecidableEq W] (B : SimpleGraph W)
    [DecidableRel B.Adj] {w : W} {L : List (W × W)}
    (hev : ∀ v, Even (B.degree v) ↔ v = w ∨ v ∈ pairVerts L) (hnd : (pairVerts L).Nodup)
    (hw : w ∉ pairVerts L) (hedge : ∀ p ∈ L, B.Adj p.1 p.2) (v : W) :
    (delList B (L.map pairEdge)).degree v % 2 = if v = w then 0 else 1 := by
  have hin : ∀ e ∈ L.map pairEdge, e ∈ B.edgeSet := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    exact hedge p hp
  have h1 := delList_degree_count B (L.map pairEdge) (nodup_map_pairEdge L hnd) hin v
  rw [countP_pairEdge_of_nodup L hnd v] at h1
  by_cases hvw : v = w
  · subst hvw
    rw [if_neg hw] at h1
    have he := (hev v).2 (Or.inl rfl)
    rw [Nat.even_iff] at he
    simp only [ite_true]
    omega
  · rw [if_neg hvw]
    by_cases hv : v ∈ pairVerts L
    · rw [if_pos hv] at h1
      have he := (hev v).2 (Or.inr hv)
      rw [Nat.even_iff] at he
      omega
    · rw [if_neg hv] at h1
      have ho : ¬ Even (B.degree v) := fun he => by
        rcases (hev v).1 he with h | h
        · exact hvw h
        · exact hv h
      rw [Nat.not_even_iff] at ho
      omega

/-- **One pair suffices at deletion degree four** (manuscript Proposition 5.3). Let `z, r` be the
only even vertices of `J`, adjacent, `d(r) ≥ 3`, and let the even vertices of `J − z` be `w, a, b`
with `ab` an edge. If some Lovász decomposition of `(J − z) − ab` has its path ending at `b` avoiding
`a`, then Test2 holds at `(z, r)`. -/
theorem test2At_of_pairAvoid (J : SimpleGraph V) [DecidableRel J.Adj] {z r : V}
    (hzr : ∀ v, Even (J.degree v) ↔ v = z ∨ v = r) (hr3 : 3 ≤ J.degree r)
    {w a b : {v | v ≠ z}}
    (hT : ∀ v : {v | v ≠ z}, (J.Adj z v ∧ (v : V) ≠ r) ↔ v = w ∨ v ∈ pairVerts [(a, b)])
    (hnd : (pairVerts [(a, b)]).Nodup) (hw : w ∉ pairVerts [(a, b)])
    (hab : (delVert J z).Adj a b)
    (h : AvoidDecomp (delList (delVert J z) ([(a, b)].map pairEdge)) b {a}) : Test2At J z r := by
  intro hr
  have hev : ∀ v, Even ((delVert J z).degree v) ↔ v = w ∨ v ∈ pairVerts [(a, b)] := fun v =>
    (even_delVert_iff J hzr hr v).trans (hT v)
  obtain ⟨D₀, hD₀, hav⟩ := h
  have hdisj : TriangleDisj D₀ [(a, b)] := by
    intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact Or.inl fun P hP hend => hav P hP hend a (Finset.mem_singleton_self a)
  obtain ⟨D, hD⟩ := floor_of_matchingBase (delVert J z) hev hnd hw
    (fun p hp => by rw [List.mem_singleton] at hp; subst hp; exact hab) D₀ hD₀ hdisj
  have hcard := card_delVert (W := V) z
  have hrev : J.degree r % 2 = 0 := Nat.even_iff.mp ((hzr r).2 (Or.inr rfl))
  exact test2At_of_floor J hrev hr3 ⟨D, by rw [hcard] at hD; omega⟩ hr

/-- The graph `(J − z) − ab` has at most one even vertex, namely `w`, which has positive degree when
`d_J(w) ≥ 3`. -/
theorem onePair_evenSet (J : SimpleGraph V) [DecidableRel J.Adj] {z r : V}
    (hzr : ∀ v, Even (J.degree v) ↔ v = z ∨ v = r) (hr : J.Adj z r)
    {w a b : {v | v ≠ z}}
    (hT : ∀ v : {v | v ≠ z}, (J.Adj z v ∧ (v : V) ≠ r) ↔ v = w ∨ v ∈ pairVerts [(a, b)])
    (hnd : (pairVerts [(a, b)]).Nodup) (hw : w ∉ pairVerts [(a, b)])
    (hab : (delVert J z).Adj a b) (hw3 : 3 ≤ J.degree w) :
    (evenSet (delList (delVert J z) ([(a, b)].map pairEdge))).card ≤ 1 ∧
      w ∈ evenSet (delList (delVert J z) ([(a, b)].map pairEdge)) ∧
      (∀ v, v ≠ w → (delList (delVert J z) ([(a, b)].map pairEdge)).degree v % 2 = 1) := by
  have hev : ∀ v, Even ((delVert J z).degree v) ↔ v = w ∨ v ∈ pairVerts [(a, b)] := fun v =>
    (even_delVert_iff J hzr hr v).trans (hT v)
  have hpar := delPairs_degree_mod (delVert J z) hev hnd hw
    (fun p hp => by rw [List.mem_singleton] at hp; subst hp; exact hab)
  refine ⟨?_, ?_, fun v hv => by rw [hpar v, if_neg hv]⟩
  · have hsub : evenSet (delList (delVert J z) ([(a, b)].map pairEdge)) ⊆ {w} := by
      intro v hv
      simp only [evenSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      rw [Finset.mem_singleton]
      by_contra hvw
      have := hpar v
      rw [if_neg hvw] at this
      exact (Nat.not_even_iff.mpr this) hv.2
    exact (Finset.card_le_card hsub).trans (by simp)
  · -- `w` is not in the pair, so it keeps its degree `d_J(w) − 1 ≥ 2`
    have hwa : w ≠ a := fun h => hw (by rw [h]; simp [pairVerts])
    have hwb : w ≠ b := fun h => hw (by rw [h]; simp [pairVerts])
    have hdeg := delList_degree_count (delVert J z) ([(a, b)].map pairEdge)
      (nodup_map_pairEdge _ hnd) (fun e he => by
        rw [List.map_singleton, List.mem_singleton] at he; subst he; exact hab) w
    rw [countP_pairEdge_of_nodup _ hnd w, if_neg hw] at hdeg
    have hzw : J.Adj z w := ((hT w).2 (Or.inl rfl)).1
    have hdz := delVert_degree (J := J) z w
    simp only [show J.Adj (w : V) z from hzw.symm, ite_true] at hdz
    have hev2 := hpar w
    simp only [ite_true] at hev2
    simp only [evenSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by omega, Nat.even_iff.mpr hev2⟩

/-- **Deletion degree four by separation**: if moreover `a, b` have no common neighbour in
`(J − z) − ab`, Test2 holds at `(z, r)` (manuscript Corollary 5.4(a)). -/
theorem test2At_of_pair_farApart (J : SimpleGraph V) [DecidableRel J.Adj] {z r : V}
    (hzr : ∀ v, Even (J.degree v) ↔ v = z ∨ v = r) (hr3 : 3 ≤ J.degree r)
    {w a b : {v | v ≠ z}}
    (hT : ∀ v : {v | v ≠ z}, (J.Adj z v ∧ (v : V) ≠ r) ↔ v = w ∨ v ∈ pairVerts [(a, b)])
    (hnd : (pairVerts [(a, b)]).Nodup) (hw : w ∉ pairVerts [(a, b)])
    (hab : (delVert J z).Adj a b) (hw3 : 3 ≤ J.degree w)
    (hfar : ∀ x, ¬ ((delVert J z).Adj a x ∧ (delVert J z).Adj x b)) : Test2At J z r := by
  intro hr
  obtain ⟨hev1, -, -⟩ := onePair_evenSet J hzr hr hT hnd hw hab hw3
  have hab' : a ≠ b := by
    intro h; rw [pairVerts, List.flatMap_cons, List.flatMap_nil, List.append_nil, h] at hnd; simp at hnd
  have hFar : FarApart (delList (delVert J z) ([(a, b)].map pairEdge)) b a := by
    refine ⟨Ne.symm hab', fun h => h.2 ?_, fun x hx => hfar x ⟨hx.2.1.symm, hx.1.1.symm⟩⟩
    simp [pairEdge, Sym2.eq_swap]
  obtain ⟨D, hD, hav⟩ := lovasz_avoid _ hev1 hFar
  exact test2At_of_pairAvoid J hzr hr3 hT hnd hw hab
    ⟨D, hD, fun P hP hend x hx => by rw [Finset.mem_singleton] at hx; subst hx; exact hav P hP hend⟩ hr

/-- **Deletion degree four by two-token steering**: a two-token schedule for `((J − z) − ab, b, {a})`
gives Test2 at `(z, r)` (manuscript Corollary 5.4(b); `avoid_of_steer2`). -/
theorem test2At_of_pair_steer2 (J : SimpleGraph V) [DecidableRel J.Adj] {z r : V}
    (hzr : ∀ v, Even (J.degree v) ↔ v = z ∨ v = r) (hr3 : 3 ≤ J.degree r)
    {w a b : {v | v ≠ z}}
    (hT : ∀ v : {v | v ≠ z}, (J.Adj z v ∧ (v : V) ≠ r) ↔ v = w ∨ v ∈ pairVerts [(a, b)])
    (hnd : (pairVerts [(a, b)]).Nodup) (hw : w ∉ pairVerts [(a, b)])
    (hab : (delVert J z).Adj a b) (hw3 : 3 ≤ J.degree w)
    (hS : Steer2 (leafX a) (apex (delList (delVert J z) ([(a, b)].map pairEdge)) {b})
      (some w) (some b)) : Test2At J z r := by
  intro hr
  obtain ⟨hev1, hwev, hodd⟩ := onePair_evenSet J hzr hr hT hnd hw hab hw3
  have hwa : a ≠ w := fun h => hw (by rw [← h]; simp [pairVerts])
  have hwb : b ≠ w := fun h => hw (by rw [← h]; simp [pairVerts])
  have hab' : a ≠ b := by
    intro h; rw [pairVerts, List.flatMap_cons, List.flatMap_nil, List.append_nil, h] at hnd; simp at hnd
  have hna : ¬ (delList (delVert J z) ([(a, b)].map pairEdge)).Adj a b := fun h => h.2 (by simp [pairEdge])
  exact test2At_of_pairAvoid J hzr hr3 hT hnd hw hab
    (avoid_of_steer2 _ hev1 hwev (hodd a hwa) (hodd b hwb) hab' hna hS) hr

end onePair

end Gallai
