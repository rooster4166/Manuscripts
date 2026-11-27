import GallaiLean.DirectTest1

/-!
# The forest lift to Test1 (session `claude/triangle-base`)

Manuscript: `manuscripts/direct-test1/direct-test1.tex`, §4 (the forest lift, proposed by an external
collaborator and checked by the coordinator; Lemma 4.1 and Theorem 4.2 there).

Let `z` be the only even vertex of `J`, `r ∈ N(z)`, `w ∈ N(z) − r`, and `T = N(z) − {r, w}`. Let `Φ` be a
set of edges of `J − {z, r}` whose odd-degree vertices are exactly `T`, given as a list `L` of
(child, parent) pairs `(v, p(v))` (each edge `p(v)v` once; children distinct; `w` never a child).
Put `M = J − zw − zT − Φ` (`forM`). If `M` has a Lovász decomposition with
* (i) the path ending at each child `v` avoids `p(v)`, and
* (ii) no path has two siblings (children of a common parent) as its two ends,
then Test1 holds at `r` (**`test1At_of_forestBase`**).

The list is processed **parent first** (`L.Pairwise (fun p q => p.2 ≠ q.1)`: a parent is never a
later child). Then, when `v` is processed, its only end is its original one, and an append creates
a new end only at a parent, which is never a later child. So (i), (ii) and the ends at children are
invariants (`append_forest`). A parent-first order exists for every rooted forest (list the
non-root vertices by depth). Acyclicity is not needed for the lift itself.

## Main results

* `delList_degree_count`: `(K − L).degree v + #{e ∈ L : v ∈ e} = K.degree v`.
* **`append_forest`**: appending the parent edges at the child ends, in parent-first order, keeps
  the size of the decomposition.
* `test1At_of_leafDecomp`: a decomposition of `J − z` with `z` re-attached as a leaf at `r`, of size
  `≤ (|J| − 1)/2`, gives `Test1At` (the deletion step, as in `test1At_of_triangleBase`).
* `zDelT`, `forM`, `leafT`, `ForestData`, `ForestBase`.
* **`test1At_of_forestBase`** (manuscript Theorem 4.2).
-/

open SimpleGraph

namespace Gallai

universe u

/-! ### Degrees after deleting a list of edges -/

section degree

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem delList_degree_count (K : SimpleGraph V) [DecidableRel K.Adj] :
    ∀ (L : List (Sym2 V)), L.Nodup → (∀ e ∈ L, e ∈ K.edgeSet) → ∀ v,
      (delList K L).degree v + L.countP (fun e => decide (v ∈ e)) = K.degree v
  | [], _, _, v => by simp [delList_nil_degree]
  | e :: L, hnd, hL, v => by
    rw [List.nodup_cons] at hnd
    induction e using Sym2.inductionOn with
    | hf a b =>
    have hab : K.Adj a b := hL _ List.mem_cons_self
    have hab' : (delList K L).Adj a b := ⟨hab, hnd.1⟩
    have h1 := delList_cons_degree K hab' v
    have ih := delList_degree_count K L hnd.2 (fun e he => hL e (List.mem_cons_of_mem _ he)) v
    have hne : a ≠ b := K.ne_of_adj hab
    rw [List.countP_cons]
    have hc : (if decide (v ∈ s(a, b)) = true then 1 else 0) =
        (if v = a then 1 else 0) + (if v = b then 1 else 0) := by
      by_cases hva : v = a
      · subst hva; simp [hne]
      · by_cases hvb : v = b
        · subst hvb; simp [hva]
        · simp [hva, hvb]
    rw [hc]
    omega

end degree

/-! ### Appending a forest at the child ends -/

section appendForest

variable {U : Type*} [DecidableEq U]

/-- **Appending a forest** (manuscript Lemma 4.1, one direction). `L` lists (child, parent) pairs in
parent-first order, with distinct children and distinct edges, all missing from `K`; `G` is `K`
plus these edges. If `D` decomposes `K`, every child is an end, (i) every path ending at a child
avoids its parent, and (ii) no path has two siblings as its two ends, then `G` has a
decomposition of the same size. -/
theorem append_forest [Fintype U] {G : SimpleGraph U} :
    ∀ (L : List (U × U)) (K : SimpleGraph U),
      (∀ e, e ∈ G.edgeSet ↔ e ∈ K.edgeSet ∨ e ∈ L.map pairEdge) →
      (∀ p ∈ L, ¬ K.Adj p.1 p.2) → (L.map Prod.fst).Nodup → (L.map pairEdge).Nodup →
      L.Pairwise (fun p q => p.2 ≠ q.1) →
      ∀ D : PathDecomp K, (∀ p ∈ L, 1 ≤ D.ends p.1) →
      (∀ p ∈ L, ∀ P ∈ D.paths, (P.src = p.1 ∨ P.tgt = p.1) → p.2 ∉ P.walk.support) →
      (∀ p ∈ L, ∀ q ∈ L, p.1 ≠ q.1 → p.2 = q.2 → ∀ P ∈ D.paths,
        ¬ ((P.src = p.1 ∨ P.tgt = p.1) ∧ (P.src = q.1 ∨ P.tgt = q.1))) →
      ∃ D' : PathDecomp G, D'.size = D.size
  | [], K, hG, _, _, _, _, D, _, _, _ => by
      obtain ⟨D', hD'⟩ := D.congrGraph (G := G) (fun e => by rw [hG e]; simp)
      refine ⟨D', ?_⟩
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
      -- the children of `L'` are neither `p.1` nor the parent `p.2`
      have hc1 : ∀ q ∈ L', q.1 ≠ p.1 := fun q hq h =>
        hndc.1 (h ▸ List.mem_map_of_mem (f := Prod.fst) hq)
      have hc2 : ∀ q ∈ L', q.1 ≠ p.2 := fun q hq h => hpw1 q hq h.symm
      -- every path of `D₁` with an end at a later child is a copy, or `P'` read from its old end
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
          · -- `q` and `p` are siblings on the path `P`: excluded by (ii)
            exact hsib p hp q hqL (Ne.symm (hc1 q hq)) h.symm P hP ⟨hPt, hPq⟩
          · exact havoid q hqL P hP hPq h
      have hsib' : ∀ q ∈ L', ∀ q' ∈ L', q.1 ≠ q'.1 → q.2 = q'.2 → ∀ Q' ∈ D₁.paths,
          ¬ ((Q'.src = q.1 ∨ Q'.tgt = q.1) ∧ (Q'.src = q'.1 ∨ Q'.tgt = q'.1)) := by
        intro q hq q' hq' hne hpar Q' hQ' ⟨h1, h2⟩
        have hqL : q ∈ p :: L' := List.mem_cons_of_mem _ hq
        have hq'L : q' ∈ p :: L' := List.mem_cons_of_mem _ hq'
        rcases hcopy q hq Q' hQ' h1 with ⟨Q, hQ, hs, ht, -⟩ | ⟨hQP, -, -⟩
        · rw [hs, ht] at h1 h2
          exact hsib q hqL q' hq'L hne hpar Q hQ ⟨h1, h2⟩
        · -- `P'` has ends `p.2` and one old end; `p.2` is not a later child
          subst hQP
          rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
          · exact hne (h1.symm.trans h2)
          · exact hc2 q hq (h1.symm.trans hP'src)
          · exact hc2 q' hq' (h2.symm.trans hP'src)
          · exact hne (h1.symm.trans h2)
      obtain ⟨D', hD'⟩ := append_forest L' K₁ hG' hK' hndc.2 hnde.2 hpw' D₁ hend' havoid' hsib'
      refine ⟨D', hD'.trans ?_⟩
      have hsum : ∑ x, (D₁.ends x + (if p.1 = x then 1 else 0)) =
          ∑ x, (D.ends x + (if p.2 = x then 1 else 0)) :=
        Finset.sum_congr rfl (fun x _ => hends₁ x)
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hsum
      rw [D₁.sum_ends, D.sum_ends] at hsum
      omega

end appendForest

/-! ### The deletion step, for any leaf graph -/

section leaf

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem leafMap_edge_gen {J G : SimpleGraph V} {z r : V} (hrz : r ≠ z)
    (hz : ∀ x, G.Adj z x ↔ x = r) (hne : ∀ a b, a ≠ z → b ≠ z → (G.Adj a b ↔ J.Adj a b)) :
    ∀ e ∈ G.edgeSet, e.map (leafMap z) ∈ (addLeaf (delVert J z) ⟨r, hrz⟩).edgeSet := by
  intro e he
  induction e using Sym2.inductionOn with
  | hf a b =>
  rw [Sym2.map_mk, mem_edgeSet]
  have hab : G.Adj a b := he
  by_cases ha : a = z
  · subst ha
    have hbr := (hz b).1 hab
    subst hbr
    simp only [leafMap, hrz, dite_true, dite_false]
    rfl
  · by_cases hb : b = z
    · subst hb
      have har := (hz a).1 hab.symm
      subst har
      simp only [leafMap, hrz, dite_true, dite_false]
      rfl
    · simp only [leafMap, ha, hb, dite_false]
      exact (hne a b ha hb).1 hab

omit [Fintype V] in
theorem leafMap_cov_gen {J G : SimpleGraph V} {z r : V} (hrz : r ≠ z)
    (hz : ∀ x, G.Adj z x ↔ x = r) (hne : ∀ a b, a ≠ z → b ≠ z → (G.Adj a b ↔ J.Adj a b)) :
    ∀ e' ∈ (addLeaf (delVert J z) ⟨r, hrz⟩).edgeSet,
      ∃ e ∈ G.edgeSet, e.map (leafMap z) = e' := by
  intro e' he'
  induction e' using Sym2.inductionOn with
  | hf x y =>
  rw [mem_edgeSet] at he'
  have hlr : G.Adj z r := (hz r).2 rfl
  cases x with
  | none =>
    cases y with
    | none => exact absurd he' id
    | some b =>
      have hb : b = ⟨r, hrz⟩ := he'
      subst hb
      refine ⟨s(z, r), hlr, ?_⟩
      rw [Sym2.map_mk]
      simp [leafMap, hrz]
  | some a =>
    cases y with
    | none =>
      have ha : a = ⟨r, hrz⟩ := he'
      subst ha
      refine ⟨s(r, z), hlr.symm, ?_⟩
      rw [Sym2.map_mk]
      simp [leafMap, hrz]
    | some b =>
      refine ⟨s(a.1, b.1), (hne a.1 b.1 a.2 b.2).2 he', ?_⟩
      rw [Sym2.map_mk, leafMap_val, leafMap_val]

/-- **The deletion step.** If `G` is `J − z` with `z` re-attached as a leaf at `r` (where `z` is the
only even vertex of `J` and `d(r) ≥ 3`), a decomposition of `G` into at most `(|J| − 1)/2` paths gives
Test1 at `r`. -/
theorem test1At_of_leafDecomp (J : SimpleGraph V) [DecidableRel J.Adj] {G : SimpleGraph V}
    {z r : V} (hzv : ∀ v, Even (J.degree v) ↔ v = z) (hr3 : 3 ≤ J.degree r)
    (hz : ∀ x, G.Adj z x ↔ x = r) (hne : ∀ a b, a ≠ z → b ≠ z → (G.Adj a b ↔ J.Adj a b))
    (D₁ : PathDecomp G) (hsize : D₁.size ≤ (Fintype.card V - 1) / 2) : Test1At J z r := by
  intro hr
  let D₂ := D₁.mapInj (leafMap z) (leafMap_injective z) (leafMap_edge_gen hr.ne' hz hne)
    (leafMap_cov_gen hr.ne' hz hne)
  have hD₂ : D₂.size = D₁.size := PathDecomp.mapInj_size _ _ _ _ _
  obtain ⟨D₃, hD₃⟩ := PathDecomp.trim_ends D₂
  have hcost : leafCost D₃ ⟨r, hr.ne'⟩ ≤ D₁.size := by
    unfold leafCost
    rcases hD₃ with ⟨h1, h2⟩ | ⟨h1, -⟩
    · have : D₃.ends ⟨r, hr.ne'⟩ ≠ 0 := by rw [h2]; exact Nat.succ_ne_zero _
      simp only [this, ite_false]
      omega
    · split_ifs <;> omega
  have hdeg : (delVert J z).degree ⟨r, hr.ne'⟩ + (if J.Adj r z then 1 else 0) = J.degree r :=
    delVert_degree z ⟨r, hr.ne'⟩
  simp only [hr.symm, ite_true] at hdeg
  have hrodd : J.degree r % 2 = 1 :=
    Nat.odd_iff.mp (Nat.not_even_iff_odd.mp (fun he => hr.ne' ((hzv r).1 he)))
  have hev : Even ((delVert J z).degree ⟨r, hr.ne'⟩) := by rw [Nat.even_iff]; omega
  have hpos : 0 < (delVert J z).degree ⟨r, hr.ne'⟩ := by omega
  obtain ⟨D, hDsize, hDends⟩ := exists_two_ends D₃ hcost hev hpos
  exact ⟨D, by omega, hDends⟩

end leaf

/-! ### The forest data and the lift -/

section forest

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The edges `zw` and `zv` (`v ∈ T`) at `z`. -/
def zDelT (z w : V) (T : List V) : List (Sym2 V) := s(z, w) :: T.map (fun v => s(z, v))

/-- **The forest base graph** `M = J − zw − zT − Φ` (manuscript Theorem 4.2). -/
abbrev forM (J : SimpleGraph V) (z w : V) (T : List V) (L : List (V × V)) : SimpleGraph V :=
  delList J (zDelT z w T ++ L.map pairEdge)

/-- `J − zw − zT`: the graph `J − z` with `z` attached as a leaf at `r`. -/
abbrev leafT (J : SimpleGraph V) (z w : V) (T : List V) : SimpleGraph V := delList J (zDelT z w T)

/-- **Forest data** at `(J, z, r)`: `w`, the list `T = N(z) − {r, w}`, and a forest `T`-join `Φ` of
`J − {z, r}` given by (child, parent) pairs in parent-first order, with `w` never a child. -/
structure ForestData (J : SimpleGraph V) (z r w : V) (T : List V) (L : List (V × V)) : Prop where
  nodup : (r :: w :: T).Nodup
  nbr : ∀ v, J.Adj z v ↔ v = r ∨ v = w ∨ v ∈ T
  edge : ∀ p ∈ L, J.Adj p.1 p.2
  avoid_zr : ∀ p ∈ L, p.1 ≠ z ∧ p.2 ≠ z ∧ p.1 ≠ r ∧ p.2 ≠ r
  child_ne_w : ∀ p ∈ L, p.1 ≠ w
  children : (L.map Prod.fst).Nodup
  edges : (L.map pairEdge).Nodup
  parent_first : L.Pairwise (fun p q => p.2 ≠ q.1)
  tjoin : ∀ v, (L.map pairEdge).countP (fun e => decide (v ∈ e)) % 2 = if v ∈ T then 1 else 0

/-- **A forest base**: forest data and a Lovász decomposition of `M` with (i) and (ii). -/
def ForestBase (J : SimpleGraph V) [DecidableRel J.Adj] (z r : V) : Prop :=
  ∃ w T L, ForestData J z r w T L ∧ ∃ D₀ : PathDecomp (forM J z w T L),
    (∀ v, D₀.ends v = (forM J z w T L).degree v % 2) ∧
    (∀ p ∈ L, ∀ P ∈ D₀.paths, (P.src = p.1 ∨ P.tgt = p.1) → p.2 ∉ P.walk.support) ∧
    (∀ p ∈ L, ∀ q ∈ L, p.1 ≠ q.1 → p.2 = q.2 → ∀ P ∈ D₀.paths,
      ¬ ((P.src = p.1 ∨ P.tgt = p.1) ∧ (P.src = q.1 ∨ P.tgt = q.1)))

section data

variable {J : SimpleGraph V} {z r w : V} {T : List V} {L : List (V × V)}
  (hF : ForestData J z r w T L)
include hF

omit [Fintype V] in
theorem ForestData.facts : z ≠ r ∧ z ≠ w ∧ z ∉ T ∧ r ≠ w ∧ r ∉ T ∧ w ∉ T ∧ T.Nodup := by
  have hz := hF.nbr z
  simp only [SimpleGraph.irrefl, false_iff, not_or] at hz
  obtain ⟨h1, h2, h3⟩ := hz
  have hnd := hF.nodup
  simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
  exact ⟨h1, h2, h3, hnd.1.1, hnd.1.2, hnd.2.1, hnd.2.2⟩

omit [Fintype V] in
theorem ForestData.mem_zDelT {x y : V} :
    s(x, y) ∈ zDelT z w T ↔ (x = z ∧ (y = w ∨ y ∈ T)) ∨ (y = z ∧ (x = w ∨ x ∈ T)) := by
  obtain ⟨-, hzw, hzT, -, -, -, -⟩ := hF.facts
  simp only [zDelT, List.mem_cons, List.mem_map, Sym2.eq_iff]
  constructor
  · rintro ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨v, hv, h⟩)
    · exact Or.inl ⟨rfl, Or.inl rfl⟩
    · exact Or.inr ⟨rfl, Or.inl rfl⟩
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1 h2; exact Or.inl ⟨rfl, Or.inr hv⟩
      · subst h1 h2; exact Or.inr ⟨rfl, Or.inr hv⟩
  · rintro (⟨rfl, rfl | hy⟩ | ⟨rfl, rfl | hx⟩)
    · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr ⟨y, hy, Or.inl ⟨rfl, rfl⟩⟩
    · exact Or.inl (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr ⟨x, hx, Or.inr ⟨rfl, rfl⟩⟩

omit [Fintype V] in
theorem ForestData.pair_not_mem_zDelT {p : V × V} (hp : p ∈ L) : pairEdge p ∉ zDelT z w T := by
  rw [pairEdge, hF.mem_zDelT]
  obtain ⟨h1, h2, -, -⟩ := hF.avoid_zr p hp
  rintro (⟨h, -⟩ | ⟨h, -⟩)
  · exact h1 h
  · exact h2 h

omit [Fintype V] in
theorem ForestData.leafT_adj_z {x : V} : (leafT J z w T).Adj z x ↔ x = r := by
  obtain ⟨hzr, hzw, hzT, hrw, hrT, -, -⟩ := hF.facts
  show J.Adj z x ∧ s(z, x) ∉ zDelT z w T ↔ x = r
  rw [hF.mem_zDelT, hF.nbr x]
  constructor
  · rintro ⟨h | h | h, hn⟩
    · exact h
    · exact absurd (Or.inl ⟨rfl, Or.inl h⟩) hn
    · exact absurd (Or.inl ⟨rfl, Or.inr h⟩) hn
  · rintro rfl
    refine ⟨Or.inl rfl, ?_⟩
    rintro (⟨-, h | h⟩ | ⟨h, -⟩)
    · exact hrw h
    · exact hrT h
    · exact hzr h.symm

omit [Fintype V] in
theorem ForestData.leafT_adj_ne {a b : V} (ha : a ≠ z) (hb : b ≠ z) :
    (leafT J z w T).Adj a b ↔ J.Adj a b := by
  show J.Adj a b ∧ s(a, b) ∉ zDelT z w T ↔ J.Adj a b
  rw [hF.mem_zDelT]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rintro (⟨h, -⟩ | ⟨h, -⟩)
  · exact ha h
  · exact hb h

omit [Fintype V] in
theorem ForestData.leafT_edgeSet (e : Sym2 V) :
    e ∈ (leafT J z w T).edgeSet ↔ e ∈ (forM J z w T L).edgeSet ∨ e ∈ L.map pairEdge := by
  rw [delList_edgeSet, delList_edgeSet, List.mem_append]
  constructor
  · rintro ⟨he, hn⟩
    by_cases hm : e ∈ L.map pairEdge
    · exact Or.inr hm
    · exact Or.inl ⟨he, by tauto⟩
  · rintro (⟨he, hn⟩ | hm)
    · exact ⟨he, fun h => hn (Or.inl h)⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
      exact ⟨hF.edge p hp, hF.pair_not_mem_zDelT hp⟩

variable [DecidableRel J.Adj]

omit [Fintype V] [DecidableRel J.Adj] in
/-- The edges deleted from `J` to form `M` are distinct edges of `J`. -/
theorem ForestData.del_facts :
    (zDelT z w T ++ L.map pairEdge).Nodup ∧ ∀ e ∈ zDelT z w T ++ L.map pairEdge, e ∈ J.edgeSet := by
  obtain ⟨hzr, hzw, hzT, hrw, hrT, hwT, hTnd⟩ := hF.facts
  refine ⟨?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨?_, hF.edges, ?_⟩
    · rw [zDelT, List.nodup_cons]
      refine ⟨?_, ?_⟩
      · simp only [List.mem_map, not_exists, not_and]
        intro v hv h
        rcases Sym2.eq_iff.1 h with ⟨-, h⟩ | ⟨h, -⟩
        · exact hwT (h ▸ hv)
        · exact hzw h
      · refine hTnd.map_on ?_
        intro a _ b _ h
        rcases Sym2.eq_iff.1 h with ⟨-, h⟩ | ⟨h1, h2⟩
        · exact h
        · exact h2.trans h1
    · intro e he e' he' hee
      subst hee
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he'
      exact hF.pair_not_mem_zDelT hp he
  · intro e he
    rcases List.mem_append.1 he with he | he
    · rw [zDelT, List.mem_cons, List.mem_map] at he
      rcases he with rfl | ⟨v, hv, rfl⟩
      · exact (hF.nbr w).2 (Or.inr (Or.inl rfl))
      · exact (hF.nbr v).2 (Or.inr (Or.inr hv))
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
      exact hF.edge p hp

omit [Fintype V] [DecidableRel J.Adj] in
/-- The number of deleted edges at `v`. -/
theorem ForestData.count_del (v : V) :
    (zDelT z w T ++ L.map pairEdge).countP (fun e => decide (v ∈ e)) =
      (if v = z then T.length + 1 else 0) + (if v = w then 1 else 0) + (if v ∈ T then 1 else 0) +
        (L.map pairEdge).countP (fun e => decide (v ∈ e)) := by
  obtain ⟨hzr, hzw, hzT, hrw, hrT, hwT, hTnd⟩ := hF.facts
  rw [List.countP_append, zDelT, List.countP_cons, List.countP_map]
  by_cases hvz : v = z
  · subst hvz
    have hall : T.countP ((fun e => decide (v ∈ e)) ∘ fun x => s(v, x)) = T.length :=
      List.countP_eq_length.mpr (fun x _ => by simp)
    rw [hall]
    simp [hzw, hzT]
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
      have hvw : v ≠ w := fun h => hwT (h ▸ hvT)
      simp [hvz, hvw, hvT, Sym2.mem_iff]
    · rw [List.count_eq_zero_of_not_mem hvT]
      by_cases hvw : v = w
      · subst hvw
        simp [hvz, hvT]
      · simp [hvz, hvw, hvT, Sym2.mem_iff]

theorem ForestData.forM_degree (v : V) :
    (forM J z w T L).degree v + ((if v = z then T.length + 1 else 0) + (if v = w then 1 else 0) +
      (if v ∈ T then 1 else 0) + (L.map pairEdge).countP (fun e => decide (v ∈ e))) =
      J.degree v := by
  rw [← hF.count_del v]
  exact delList_degree_count J _ hF.del_facts.1 hF.del_facts.2 v

/-- In `M`, the vertex `w` has even degree. -/
theorem ForestData.forM_even_w (hz : ∀ v, Even (J.degree v) ↔ v = z) :
    (forM J z w T L).degree w % 2 = 0 := by
  obtain ⟨-, hzw, -, -, -, hwT, -⟩ := hF.facts
  have h := hF.forM_degree w
  have ht := hF.tjoin w
  simp only [Ne.symm hzw, hwT, ite_true, ite_false, zero_add, add_zero] at h ht
  have hodd : J.degree w % 2 = 1 :=
    Nat.odd_iff.mp (Nat.not_even_iff_odd.mp (fun he => hzw ((hz w).1 he).symm))
  omega

/-- In `M`, every child has odd degree. -/
theorem ForestData.forM_odd_child (hz : ∀ v, Even (J.degree v) ↔ v = z) {p : V × V}
    (hp : p ∈ L) : (forM J z w T L).degree p.1 % 2 = 1 := by
  obtain ⟨h1, -, -, -⟩ := hF.avoid_zr p hp
  have hw := hF.child_ne_w p hp
  have h := hF.forM_degree p.1
  have ht := hF.tjoin p.1
  simp only [h1, hw, ite_false, zero_add] at h
  have hodd : J.degree p.1 % 2 = 1 :=
    Nat.odd_iff.mp (Nat.not_even_iff_odd.mp (fun he => h1 ((hz p.1).1 he)))
  split_ifs at h ht <;> omega

/-- Every Lovász decomposition of `M` has at most `(|J| − 1)/2` paths. -/
theorem ForestData.forM_size (hz : ∀ v, Even (J.degree v) ↔ v = z)
    (D₀ : PathDecomp (forM J z w T L)) (hD₀ : ∀ v, D₀.ends v = (forM J z w T L).degree v % 2) :
    D₀.size ≤ (Fintype.card V - 1) / 2 := by
  have hw := hF.forM_even_w hz
  have h2 : 2 * D₀.size ≤ Fintype.card V - 1 := by
    rw [← D₀.sum_ends]
    have h1 : ∑ v, D₀.ends v ≤ ∑ v, (if v ≠ w then 1 else 0) :=
      Finset.sum_le_sum fun v _ => by
        rw [hD₀ v]
        by_cases hv : v = w
        · subst hv; simp [hw]
        · simp only [hv, ne_eq, not_false_eq_true, ite_true]
          exact Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    refine h1.trans (le_of_eq ?_)
    rw [← Finset.card_filter, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
  omega

end data

/-- **The forest lift** (manuscript Theorem 4.2). If `z` is the only even vertex of `J`, `d(r) ≥ 3`,
and `(J, z, r)` has a forest base, then Test1 holds at `r`. -/
theorem test1At_of_forestBase (J : SimpleGraph V) [DecidableRel J.Adj] {z r : V}
    (hz : ∀ v, Even (J.degree v) ↔ v = z) (hr3 : 3 ≤ J.degree r) (h : ForestBase J z r) :
    Test1At J z r := by
  obtain ⟨w, T, L, hF, D₀, hD₀, hi, hii⟩ := h
  have hend : ∀ p ∈ L, 1 ≤ D₀.ends p.1 := fun p hp => by
    rw [hD₀, hF.forM_odd_child hz hp]
  have hnotM : ∀ p ∈ L, ¬ (forM J z w T L).Adj p.1 p.2 := fun p hp h =>
    h.2 (List.mem_append_right _ (List.mem_map_of_mem hp))
  obtain ⟨D₁, hD₁⟩ := append_forest (G := leafT J z w T) L (forM J z w T L) hF.leafT_edgeSet
    hnotM hF.children hF.edges hF.parent_first D₀ hend hi hii
  exact test1At_of_leafDecomp J hz hr3 (fun _ => hF.leafT_adj_z)
    (fun _ _ ha hb => hF.leafT_adj_ne ha hb) D₁ (hD₁ ▸ hF.forM_size hz D₀ hD₀)

/-- **Test1 from forest bases**: if every neighbour of `z` has degree at least three and every root
has a forest base, then `Test1 J z`. -/
theorem test1_of_forestBases (J : SimpleGraph V) [DecidableRel J.Adj] (z : V)
    (hdeg : ∀ r, J.Adj z r → 3 ≤ J.degree r)
    (h : (∀ v, Even (J.degree v) ↔ v = z) → ∀ r, J.Adj z r → ForestBase J z r) : Test1 J z :=
  test1_of_test1At J z fun hz r hr => test1At_of_forestBase J hz (hdeg r hr) (h hz r hr)

end forest

end Gallai
