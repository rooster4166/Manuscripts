import GallaiLean.T6Dense

/-!
# The direct lift to the two-end test through triangles at the even vertex

Session `claude/triangle-base`. Manuscript: `manuscripts/direct-test1/direct-test1.tex`.

Let `z` be the only even vertex of `J` and `r ∈ N(z)`. **Triangle data** (manuscript
Definition 1.1) are a vertex `w ∈ N(z) − r` and a list `L = [(a₁, b₁), …]` of pairs that
partition `N(z) − {r, w}`, each pair an edge of `J`. The auxiliary graph is
`M = J − zw − {zaᵢ, zbᵢ, aᵢbᵢ}` (`triM`); in it `z` is a leaf at `r` and `w` is the only even
vertex (`triM_parity`, manuscript Lemma 1.2).

**Theorem (direct lift, manuscript Theorem 2.1).** If `M` has a Lovász decomposition `D₀` with,
for every pair, `aᵢ ∉ V(Q₀(bᵢ))` or `bᵢ ∉ V(Q₀(aᵢ))` (`TriangleDisj`), then `J − z` has a
decomposition into at most `(|J| − 1)/2` paths with at least two ends at `r` (`Test1At`).

The formal proof performs the two steps of the manuscript in the opposite order, which is
equivalent and shorter:
1. append every edge `aᵢbᵢ` at the end chosen by the disjunction (`append_pairs`, by induction
   with `append_full`; the disjunctions are carried as an invariant, which is where `M₀` being a
   matching is used: an append at `t → u` adds only `u` to one path);
2. the result decomposes `J − zw − {zaᵢ, zbᵢ}`, which is `J − z` with `z` a private leaf at `r`
   (`leafJ_iso`); trim the leaf (`PathDecomp.trim_ends`) and, if the leaf path was the single edge
   `zr`, split at `r` (`exists_two_ends`).

## Main results

* `pairEdge`, `pairVerts`, `pair_eq_of_share`: lists of pairs as matchings.
* `avoid_of_append`: end-path avoidance survives an append `t → u` away from `u`.
* **`append_pairs`**: appending a matching at ends chosen by the disjunctions keeps the size.
* `zDel`, `triDel`, `triM`, `leafJ`, `TriangleData`, `TriangleDisj`, `TriangleBase`, `Test1At`.
* `triM_degree_z`, `triM_degree_w`, `triM_degree_fst`, `triM_degree_snd`, `triM_degree_other`,
  **`triM_parity`** (manuscript Lemma 1.2), `triM_size` (every Lovász decomposition of `M` has
  `(|J| − 1)/2` paths).
* **`test1At_of_triangleBase`** (manuscript Theorem 2.1).
* **`test1_of_triangleBases`**, `TriangleBaseConj`, **`test1_of_triangleBaseConj`**
  (manuscript Conjecture 3.1 and the remark after it).
-/

open SimpleGraph

namespace Gallai

universe u

/-! ### Lists of pairs -/

section pairs

variable {U : Type*}

/-- The edge `ab` of a pair `(a, b)`. -/
def pairEdge (p : U × U) : Sym2 U := s(p.1, p.2)

/-- The vertices `a₁, b₁, a₂, b₂, …` of a list of pairs. -/
def pairVerts (L : List (U × U)) : List U := L.flatMap (fun p => [p.1, p.2])

theorem mem_pairVerts {L : List (U × U)} {x : U} :
    x ∈ pairVerts L ↔ ∃ p ∈ L, x = p.1 ∨ x = p.2 := by
  simp [pairVerts]

theorem pairVerts_cons (p : U × U) (L : List (U × U)) :
    pairVerts (p :: L) = p.1 :: p.2 :: pairVerts L := by
  simp [pairVerts]

theorem fst_mem_pairVerts {L : List (U × U)} {p : U × U} (hp : p ∈ L) : p.1 ∈ pairVerts L :=
  mem_pairVerts.2 ⟨p, hp, Or.inl rfl⟩

theorem snd_mem_pairVerts {L : List (U × U)} {p : U × U} (hp : p ∈ L) : p.2 ∈ pairVerts L :=
  mem_pairVerts.2 ⟨p, hp, Or.inr rfl⟩

/-- In a list of pairs with distinct vertices, two pairs sharing a vertex are equal. -/
theorem pair_eq_of_share {L : List (U × U)} (hnd : (pairVerts L).Nodup) {p q : U × U}
    (hp : p ∈ L) (hq : q ∈ L) {x : U} (hxp : x = p.1 ∨ x = p.2) (hxq : x = q.1 ∨ x = q.2) :
    p = q := by
  by_contra hne
  rw [pairVerts, List.nodup_flatMap] at hnd
  have : Std.Symm (Function.onFun List.Disjoint (fun p : U × U => [p.1, p.2])) :=
    ⟨fun _ _ h => List.Disjoint.symm h⟩
  have hdis := hnd.2.forall hp hq hne
  exact hdis (show x ∈ [p.1, p.2] by simpa using hxp) (show x ∈ [q.1, q.2] by simpa using hxq)

/-- The two vertices of a pair are distinct. -/
theorem fst_ne_snd {L : List (U × U)} (hnd : (pairVerts L).Nodup) {p : U × U} (hp : p ∈ L) :
    p.1 ≠ p.2 := by
  rw [pairVerts, List.nodup_flatMap] at hnd
  simpa using hnd.1 p hp

end pairs

/-! ### Appending a matching at path ends -/

section append

variable {U : Type*} [DecidableEq U]

/-- A positive number of ends at `t` means some path ends at `t`. -/
theorem PathDecomp.exists_path_of_ends_pos {K : SimpleGraph U} (D : PathDecomp K) {t : U}
    (h : 1 ≤ D.ends t) : ∃ P ∈ D.paths, P.src = t ∨ P.tgt = t := by
  by_contra hno
  push Not at hno
  have h0 : D.ends t = 0 := by
    unfold PathDecomp.ends
    rw [List.sum_eq_zero]
    intro x hx
    obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hx
    obtain ⟨h1, h2⟩ := hno P hP
    simp [GPath.endsAt, h1, h2]
  omega

omit [DecidableEq U] in
/-- **End-path avoidance survives an append.** Let `D'` arise from `D` by appending the edge
`tu` at the end `t` of `P` (as in `append_full`). If no path of `D` ending at `x` contains `y`,
and `x, y ≠ u`, then no path of `D'` ending at `x` contains `y`. -/
theorem avoid_of_append {K K' : SimpleGraph U} {D : PathDecomp K} {D' : PathDecomp K'}
    {t u : U} {P : GPath K} {P' : GPath K'} (hPD : P ∈ D.paths) (hsrc : P'.src = u)
    (hcase : (P.src = t ∧ P'.tgt = P.tgt ∧ P'.walk.support = u :: P.walk.support) ∨
      (P.tgt = t ∧ P'.tgt = P.src ∧ P'.walk.support = u :: P.walk.support.reverse))
    (hcls : ∀ Q' ∈ D'.paths, Q' = P' ∨ ∃ Q ∈ D.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
      Q'.walk.support = Q.walk.support)
    {x y : U} (hxu : x ≠ u) (hyu : y ≠ u)
    (h : ∀ Q ∈ D.paths, (Q.src = x ∨ Q.tgt = x) → y ∉ Q.walk.support) :
    ∀ Q' ∈ D'.paths, (Q'.src = x ∨ Q'.tgt = x) → y ∉ Q'.walk.support := by
  intro Q' hQ' hx
  rcases hcls Q' hQ' with hEq | ⟨Q, hQ, hs, ht, hsupp⟩
  · subst hEq
    have hx' : Q'.tgt = x := by
      rcases hx with hx | hx
      · exact absurd (hsrc.symm.trans hx) (Ne.symm hxu)
      · exact hx
    rcases hcase with ⟨-, htgt, hsupp⟩ | ⟨-, htgt, hsupp⟩
    · have hy := h P hPD (Or.inr (htgt.symm.trans hx'))
      rw [hsupp, List.mem_cons]
      rintro (h' | h')
      · exact hyu h'
      · exact hy h'
    · have hy := h P hPD (Or.inl (htgt.symm.trans hx'))
      rw [hsupp, List.mem_cons, List.mem_reverse]
      rintro (h' | h')
      · exact hyu h'
      · exact hy h'
  · rw [hsupp]
    rw [hs, ht] at hx
    exact h Q hQ hx

/-- **Appending a matching** (manuscript Theorem 2.1, Step 2). Let `L` be pairs with distinct
vertices, whose edges are missing from `K`, and let `G` be `K` plus these edges. If `D`
decomposes `K`, has an end at every vertex of `L`, and for every pair `(a, b)` the path ending at
`b` avoids `a` or the path ending at `a` avoids `b`, then `G` has a decomposition of the same
size. Each edge is appended at the end chosen by the disjunction; since `L` is a matching, an
append `t → u` adds only `u` to one path, so the remaining disjunctions persist. -/
theorem append_pairs [Fintype U] {G : SimpleGraph U} :
    ∀ (L : List (U × U)) (K : SimpleGraph U),
      (∀ e, e ∈ G.edgeSet ↔ e ∈ K.edgeSet ∨ e ∈ L.map pairEdge) →
      (∀ p ∈ L, ¬ K.Adj p.1 p.2) → (pairVerts L).Nodup →
      ∀ D : PathDecomp K, (∀ p ∈ L, 1 ≤ D.ends p.1 ∧ 1 ≤ D.ends p.2) →
      (∀ p ∈ L, (∀ P ∈ D.paths, (P.src = p.2 ∨ P.tgt = p.2) → p.1 ∉ P.walk.support) ∨
        (∀ P ∈ D.paths, (P.src = p.1 ∨ P.tgt = p.1) → p.2 ∉ P.walk.support)) →
      ∃ D' : PathDecomp G, D'.size = D.size
  | [], K, hG, _, _, D, _, _ => by
      obtain ⟨D', hD'⟩ := D.congrGraph (G := G) (fun e => by rw [hG e]; simp)
      refine ⟨D', ?_⟩
      have h1 := D'.sum_ends
      have h2 := D.sum_ends
      simp only [hD'] at h1
      omega
  | p :: L', K, hG, hK, hnd, D, hend, hdisj => by
      rw [pairVerts_cons, List.nodup_cons, List.nodup_cons] at hnd
      obtain ⟨hp1, ⟨hp2, hnd'⟩⟩ := hnd
      have hp12 : p.1 ≠ p.2 := fun h => hp1 (by rw [h]; exact List.mem_cons_self ..)
      have hp1' : p.1 ∉ pairVerts L' := fun h => hp1 (List.mem_cons_of_mem _ h)
      -- the intermediate graph: `G` minus the remaining matching edges
      set K₁ := delList G (L'.map pairEdge) with hK₁def
      have hnotL' : ∀ e ∈ L'.map pairEdge, e ∈ G.edgeSet := fun e he =>
        (hG e).2 (Or.inr (List.mem_cons_of_mem _ he))
      have hKL' : ∀ e ∈ K.edgeSet, e ∉ L'.map pairEdge := by
        intro e he hm
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        exact hK q (List.mem_cons_of_mem _ hq) he
      have hpL' : pairEdge p ∉ L'.map pairEdge := by
        intro hm
        obtain ⟨q, hq, hpq⟩ := List.mem_map.mp hm
        simp only [pairEdge, Sym2.eq_iff] at hpq
        apply hp1'
        rcases hpq with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact h1 ▸ fst_mem_pairVerts hq
        · exact h2 ▸ snd_mem_pairVerts hq
      have hK₁ : ∀ e, e ∈ K₁.edgeSet ↔ e ∈ K.edgeSet ∨ e = pairEdge p := by
        intro e
        rw [hK₁def, delList_edgeSet, hG e, List.map_cons, List.mem_cons]
        constructor
        · rintro ⟨h | h | h, hn⟩
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h hn
        · rintro (h | rfl)
          · exact ⟨Or.inl h, hKL' e h⟩
          · exact ⟨Or.inr (Or.inl rfl), hpL'⟩
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
      -- one oriented append, then the induction hypothesis
      have step : ∀ t u : U, s(t, u) = pairEdge p → (t = p.1 ∨ t = p.2) → (u = p.1 ∨ u = p.2) →
          (∀ P ∈ D.paths, (P.src = t ∨ P.tgt = t) → u ∉ P.walk.support) → 1 ≤ D.ends t →
          ∃ D' : PathDecomp G, D'.size = D.size := by
        intro t u htu ht hu havoid hendt
        have hadj : ¬ K.Adj t u := by
          intro h
          have he : s(t, u) ∈ K.edgeSet := h
          rw [htu] at he
          exact hK p List.mem_cons_self he
        have hK₁' : ∀ e, e ∈ K₁.edgeSet ↔ e ∈ K.edgeSet ∨ e = s(t, u) := by
          intro e; rw [hK₁ e, htu]
        obtain ⟨P, hP, hPt⟩ := D.exists_path_of_ends_pos hendt
        obtain ⟨D₁, hends₁, P', -, hP'src, hP'case, hcls, -⟩ :=
          append_full D hadj hK₁' hP hPt (havoid P hP hPt)
        -- vertices of the remaining pairs avoid `t` and `u`
        have hfar : ∀ x ∈ pairVerts L', x ≠ t ∧ x ≠ u := by
          intro x hx
          constructor
          · rintro rfl
            rcases ht with rfl | rfl
            · exact hp1' hx
            · exact hp2 hx
          · rintro rfl
            rcases hu with rfl | rfl
            · exact hp1' hx
            · exact hp2 hx
        have hend' : ∀ q ∈ L', 1 ≤ D₁.ends q.1 ∧ 1 ≤ D₁.ends q.2 := by
          intro q hq
          have h1 := hends₁ q.1
          have h2 := hends₁ q.2
          have hq1 := hfar q.1 (fst_mem_pairVerts hq)
          have hq2 := hfar q.2 (snd_mem_pairVerts hq)
          have he := hend q (List.mem_cons_of_mem _ hq)
          simp only [Ne.symm hq1.1, Ne.symm hq2.1, ite_false, add_zero] at h1 h2
          omega
        have hdisj' : ∀ q ∈ L', (∀ P ∈ D₁.paths, (P.src = q.2 ∨ P.tgt = q.2) →
            q.1 ∉ P.walk.support) ∨
            (∀ P ∈ D₁.paths, (P.src = q.1 ∨ P.tgt = q.1) → q.2 ∉ P.walk.support) := by
          intro q hq
          have hq1 := hfar q.1 (fst_mem_pairVerts hq)
          have hq2 := hfar q.2 (snd_mem_pairVerts hq)
          rcases hdisj q (List.mem_cons_of_mem _ hq) with h | h
          · exact Or.inl (avoid_of_append hP hP'src hP'case hcls hq2.2 hq1.2 h)
          · exact Or.inr (avoid_of_append hP hP'src hP'case hcls hq1.2 hq2.2 h)
        obtain ⟨D', hD'⟩ := append_pairs L' K₁ hG' hK' hnd' D₁ hend' hdisj'
        refine ⟨D', hD'.trans ?_⟩
        have hsum : ∑ w, (D₁.ends w + (if t = w then 1 else 0)) =
            ∑ w, (D.ends w + (if u = w then 1 else 0)) :=
          Finset.sum_congr rfl (fun w _ => hends₁ w)
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hsum
        rw [D₁.sum_ends, D.sum_ends] at hsum
        omega
      have hpe : 1 ≤ D.ends p.1 ∧ 1 ≤ D.ends p.2 := hend p List.mem_cons_self
      rcases hdisj p List.mem_cons_self with h | h
      · exact step p.2 p.1 (by simp [pairEdge, Sym2.eq_swap]) (Or.inr rfl) (Or.inl rfl) h hpe.2
      · exact step p.1 p.2 rfl (Or.inl rfl) (Or.inr rfl) h hpe.1

end append

/-! ### The auxiliary graph `M` -/

section lift

variable {V : Type u} [DecidableEq V]

/-- The edges `zw, za₁, zb₁, za₂, zb₂, …` at `z`. -/
def zDel (z w : V) (L : List (V × V)) : List (Sym2 V) :=
  s(z, w) :: L.flatMap (fun p => [s(z, p.1), s(z, p.2)])

/-- The edges deleted from `J` to form `M`: those at `z` (all but `zr`) and the matching `M₀`. -/
def triDel (z w : V) (L : List (V × V)) : List (Sym2 V) := zDel z w L ++ L.map pairEdge

/-- **The auxiliary graph** `M = J − zw − {zaᵢ, zbᵢ, aᵢbᵢ}` (manuscript Definition 1.1). -/
abbrev triM (J : SimpleGraph V) (z w : V) (L : List (V × V)) : SimpleGraph V :=
  delList J (triDel z w L)

/-- `J − zw − {zaᵢ, zbᵢ}`: the graph `J − z` with `z` attached as a leaf at `r`. -/
abbrev leafJ (J : SimpleGraph V) (z w : V) (L : List (V × V)) : SimpleGraph V :=
  delList J (zDel z w L)

/-- **Triangle data** at `(J, z, r)` (manuscript Definition 1.1): `w ∈ N(z) − r`, and the pairs
of `L` are edges of `J` partitioning `N(z) − {r, w}`. -/
structure TriangleData (J : SimpleGraph V) (z r w : V) (L : List (V × V)) : Prop where
  nodup : (r :: w :: pairVerts L).Nodup
  nbr : ∀ v, J.Adj z v ↔ v = r ∨ v = w ∨ v ∈ pairVerts L
  edge : ∀ p ∈ L, J.Adj p.1 p.2

/-- **The disjunctive end-path condition** (manuscript (2.1)): for every pair `(a, b)`, the path
ending at `b` avoids `a`, or the path ending at `a` avoids `b`. -/
def TriangleDisj {K : SimpleGraph V} (D : PathDecomp K) (L : List (V × V)) : Prop :=
  ∀ p ∈ L, (∀ P ∈ D.paths, (P.src = p.2 ∨ P.tgt = p.2) → p.1 ∉ P.walk.support) ∨
    (∀ P ∈ D.paths, (P.src = p.1 ∨ P.tgt = p.1) → p.2 ∉ P.walk.support)

variable [Fintype V]

/-- **A triangle base** at `(J, z, r)`: triangle data and a Lovász decomposition of `M`
satisfying every disjunction (the object of manuscript Conjecture 3.1). -/
def TriangleBase (J : SimpleGraph V) [DecidableRel J.Adj] (z r : V) : Prop :=
  ∃ w L, TriangleData J z r w L ∧ ∃ D₀ : PathDecomp (triM J z w L),
    (∀ v, D₀.ends v = (triM J z w L).degree v % 2) ∧ TriangleDisj D₀ L

/-- **The two-end test at one root**: `J − z` has a decomposition into at most `(|J| − 1)/2` paths
with at least two ends at `r`. `Test1 J z` asks this for every `r ∈ N(z)` (`test1_of_test1At`). -/
def Test1At (J : SimpleGraph V) [DecidableRel J.Adj] (z r : V) : Prop :=
  ∀ hr : J.Adj z r, ∃ D : PathDecomp (delVert J z),
    D.size ≤ (Fintype.card V - 1) / 2 ∧ 2 ≤ D.ends ⟨r, hr.ne'⟩

theorem test1_of_test1At (J : SimpleGraph V) [DecidableRel J.Adj] (z : V)
    (h : (∀ v, Even (J.degree v) ↔ v = z) → ∀ r, J.Adj z r → Test1At J z r) : Test1 J z :=
  fun hz r hr => h hz r hr hr

/-- Removing two edges `ax, ay` at `a`. -/
theorem degree_two_deleted {K K' : SimpleGraph V} [DecidableRel K.Adj] [DecidableRel K'.Adj]
    {a x y : V} (hx : K.Adj a x) (hy : K.Adj a y) (hxy : x ≠ y)
    (h : ∀ v, K'.Adj a v ↔ K.Adj a v ∧ v ≠ x ∧ v ≠ y) : K'.degree a + 2 = K.degree a := by
  have hy' : (delEdge K a x).Adj a y := ⟨hy, fun he => by
    rcases Sym2.eq_iff.1 he with ⟨-, h⟩ | ⟨h, -⟩
    · exact hxy h.symm
    · exact (K.ne_of_adj hx) h⟩
  rw [← delEdge_degree_left K hx, ← delEdge_degree_left (delEdge K a x) hy', add_assoc]
  congr 1
  apply degree_congr
  intro v
  show K'.Adj a v ↔ (K.Adj a v ∧ ¬ s(a, v) = s(a, x)) ∧ ¬ s(a, v) = s(a, y)
  rw [h v]
  have hax : a ≠ x := K.ne_of_adj hx
  have hay : a ≠ y := K.ne_of_adj hy
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, fun he => h2 ?_⟩, fun he => h3 ?_⟩
    · rcases Sym2.eq_iff.1 he with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hax
    · rcases Sym2.eq_iff.1 he with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hay
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, fun he => h2 (by rw [he]), fun he => h3 (by rw [he])⟩

omit [DecidableEq V] [Fintype V] in
theorem mem_zDel {z w : V} {L : List (V × V)} {e : Sym2 V} :
    e ∈ zDel z w L ↔ e = s(z, w) ∨ ∃ p ∈ L, e = s(z, p.1) ∨ e = s(z, p.2) := by
  simp [zDel]

omit [DecidableEq V] [Fintype V] in
theorem mem_triDel {z w : V} {L : List (V × V)} {e : Sym2 V} :
    e ∈ triDel z w L ↔ e ∈ zDel z w L ∨ ∃ p ∈ L, e = s(p.1, p.2) := by
  simp only [triDel, List.mem_append, List.mem_map, pairEdge]
  constructor
  · rintro (h | ⟨p, hp, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨p, hp, rfl⟩
  · rintro (h | ⟨p, hp, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨p, hp, rfl⟩

omit [Fintype V] [DecidableEq V] in
/-- Every edge of `zDel` contains `z`. -/
theorem z_mem_of_mem_zDel {z w : V} {L : List (V × V)} {e : Sym2 V} (he : e ∈ zDel z w L) :
    z ∈ e := by
  rcases mem_zDel.1 he with rfl | ⟨p, -, rfl | rfl⟩ <;> exact Sym2.mem_mk_left _ _

section data

variable {J : SimpleGraph V} {z r w : V} {L : List (V × V)} (hD : TriangleData J z r w L)
include hD

omit [DecidableEq V] [Fintype V] in
theorem TriangleData.facts :
    z ≠ r ∧ z ≠ w ∧ z ∉ pairVerts L ∧ r ≠ w ∧ r ∉ pairVerts L ∧ w ∉ pairVerts L ∧
      (pairVerts L).Nodup := by
  have hz := hD.nbr z
  simp only [SimpleGraph.irrefl, false_iff, not_or] at hz
  obtain ⟨h1, h2, h3⟩ := hz
  have hnd := hD.nodup
  simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
  exact ⟨h1, h2, h3, hnd.1.1, hnd.1.2, hnd.2.1, hnd.2.2⟩

omit [DecidableEq V] [Fintype V] in
theorem TriangleData.adj_r : J.Adj z r := (hD.nbr r).2 (Or.inl rfl)

omit [DecidableEq V] [Fintype V] in
theorem TriangleData.adj_w : J.Adj z w := (hD.nbr w).2 (Or.inr (Or.inl rfl))

omit [DecidableEq V] [Fintype V] in
theorem TriangleData.adj_vert {x : V} (hx : x ∈ pairVerts L) : J.Adj z x :=
  (hD.nbr x).2 (Or.inr (Or.inr hx))

omit [Fintype V] [DecidableEq V] in
/-- At `z`, the deleted edges are those to `w` and to the pair vertices. -/
theorem TriangleData.mem_triDel_z {x : V} :
    s(z, x) ∈ triDel z w L ↔ x = w ∨ x ∈ pairVerts L := by
  obtain ⟨hzr, hzw, hzL, -, -, -, -⟩ := hD.facts
  rw [mem_triDel, mem_zDel]
  constructor
  · rintro ((h | ⟨p, hp, h | h⟩) | ⟨p, hp, h⟩)
    · rcases Sym2.eq_iff.1 h with ⟨-, h⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact absurd h hzw
    · rcases Sym2.eq_iff.1 h with ⟨-, h⟩ | ⟨h, -⟩
      · exact Or.inr (h ▸ fst_mem_pairVerts hp)
      · exact (hzL (by rw [h]; exact fst_mem_pairVerts hp)).elim
    · rcases Sym2.eq_iff.1 h with ⟨-, h⟩ | ⟨h, -⟩
      · exact Or.inr (h ▸ snd_mem_pairVerts hp)
      · exact (hzL (by rw [h]; exact snd_mem_pairVerts hp)).elim
    · rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨h, -⟩
      · exact (hzL (by rw [h]; exact fst_mem_pairVerts hp)).elim
      · exact (hzL (by rw [h]; exact snd_mem_pairVerts hp)).elim
  · rintro (rfl | hx)
    · exact Or.inl (Or.inl rfl)
    · obtain ⟨p, hp, rfl | rfl⟩ := mem_pairVerts.1 hx
      · exact Or.inl (Or.inr ⟨p, hp, Or.inl rfl⟩)
      · exact Or.inl (Or.inr ⟨p, hp, Or.inr rfl⟩)

omit [Fintype V] [DecidableEq V] in
/-- At `w`, only `zw` is deleted. -/
theorem TriangleData.mem_triDel_w {x : V} : s(w, x) ∈ triDel z w L ↔ x = z := by
  obtain ⟨-, hzw, -, -, -, hwL, -⟩ := hD.facts
  rw [mem_triDel, mem_zDel]
  constructor
  · rintro ((h | ⟨p, hp, h | h⟩) | ⟨p, hp, h⟩)
    · rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h.symm hzw
      · exact h
    · rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h.symm hzw
      · exact (hwL (h ▸ fst_mem_pairVerts hp)).elim
    · rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h.symm hzw
      · exact (hwL (h ▸ snd_mem_pairVerts hp)).elim
    · rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨h, -⟩
      · exact (hwL (h ▸ fst_mem_pairVerts hp)).elim
      · exact (hwL (h ▸ snd_mem_pairVerts hp)).elim
  · rintro rfl
    exact Or.inl (Or.inl Sym2.eq_swap)

omit [Fintype V] [DecidableEq V] in
/-- At the first vertex `a` of a pair `(a, b)`, the deleted edges are `za` and `ab`. -/
theorem TriangleData.mem_triDel_fst {p : V × V} (hp : p ∈ L) {x : V} :
    s(p.1, x) ∈ triDel z w L ↔ x = z ∨ x = p.2 := by
  obtain ⟨hzr, hzw, hzL, -, -, hwL, hnd⟩ := hD.facts
  have hp1 := fst_mem_pairVerts hp
  have hz1 : p.1 ≠ z := fun h => hzL (h ▸ hp1)
  have hw1 : p.1 ≠ w := fun h => hwL (h ▸ hp1)
  rw [mem_triDel, mem_zDel]
  constructor
  · rintro ((h | ⟨q, hq, h | h⟩) | ⟨q, hq, h⟩)
    · rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h hz1
      · exact absurd h hw1
    · rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h hz1
      · exact Or.inl h
    · rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h hz1
      · exact Or.inl h
    · rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, -⟩
      · have := pair_eq_of_share hnd hp hq (x := p.1) (Or.inl rfl) (Or.inl h1)
        subst this
        exact Or.inr h2
      · have := pair_eq_of_share hnd hp hq (x := p.1) (Or.inl rfl) (Or.inr h1)
        subst this
        exact absurd h1 (fst_ne_snd hnd hp)
  · rintro (rfl | rfl)
    · exact Or.inl (Or.inr ⟨p, hp, Or.inl Sym2.eq_swap⟩)
    · exact Or.inr ⟨p, hp, rfl⟩

omit [Fintype V] [DecidableEq V] in
/-- At the second vertex `b` of a pair `(a, b)`, the deleted edges are `zb` and `ab`. -/
theorem TriangleData.mem_triDel_snd {p : V × V} (hp : p ∈ L) {x : V} :
    s(p.2, x) ∈ triDel z w L ↔ x = z ∨ x = p.1 := by
  obtain ⟨hzr, hzw, hzL, -, -, hwL, hnd⟩ := hD.facts
  have hp2 := snd_mem_pairVerts hp
  have hz2 : p.2 ≠ z := fun h => hzL (h ▸ hp2)
  have hw2 : p.2 ≠ w := fun h => hwL (h ▸ hp2)
  rw [mem_triDel, mem_zDel]
  constructor
  · rintro ((h | ⟨q, hq, h | h⟩) | ⟨q, hq, h⟩)
    · rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h hz2
      · exact absurd h hw2
    · rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h hz2
      · exact Or.inl h
    · rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h hz2
      · exact Or.inl h
    · rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, h2⟩
      · have := pair_eq_of_share hnd hp hq (x := p.2) (Or.inr rfl) (Or.inl h1)
        subst this
        exact absurd h1.symm (fst_ne_snd hnd hp)
      · have := pair_eq_of_share hnd hp hq (x := p.2) (Or.inr rfl) (Or.inr h1)
        subst this
        exact Or.inr h2
  · rintro (rfl | rfl)
    · exact Or.inl (Or.inr ⟨p, hp, Or.inr Sym2.eq_swap⟩)
    · exact Or.inr ⟨p, hp, Sym2.eq_swap⟩

omit [Fintype V] hD [DecidableEq V] in
/-- Away from `z`, `w` and the pairs, nothing is deleted. -/
theorem not_mem_triDel_other {v : V} (hvz : v ≠ z) (hvw : v ≠ w)
    (hvL : v ∉ pairVerts L) (x : V) : s(v, x) ∉ triDel z w L := by
  rw [mem_triDel, mem_zDel]
  rintro ((h | ⟨p, hp, h | h⟩) | ⟨p, hp, h⟩)
  · rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨h, -⟩
    · exact hvz h
    · exact hvw h
  · rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨h, -⟩
    · exact hvz h
    · exact hvL (h ▸ fst_mem_pairVerts hp)
  · rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨h, -⟩
    · exact hvz h
    · exact hvL (h ▸ snd_mem_pairVerts hp)
  · rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨h, -⟩
    · exact hvL (h ▸ fst_mem_pairVerts hp)
    · exact hvL (h ▸ snd_mem_pairVerts hp)

omit [Fintype V] [DecidableEq V] in
/-- In `M`, `z` is a leaf at `r`. -/
theorem TriangleData.triM_adj_z {x : V} : (triM J z w L).Adj z x ↔ x = r := by
  show J.Adj z x ∧ s(z, x) ∉ triDel z w L ↔ x = r
  rw [hD.mem_triDel_z, hD.nbr x]
  obtain ⟨-, -, -, hrw, hrL, -, -⟩ := hD.facts
  constructor
  · rintro ⟨h | h | h, hn⟩
    · exact h
    · exact absurd (Or.inl h) hn
    · exact absurd (Or.inr h) hn
  · rintro rfl
    refine ⟨Or.inl rfl, ?_⟩
    rintro (h | h)
    · exact hrw h
    · exact hrL h

/-! ### Degrees in `M` (manuscript Lemma 1.2) -/

variable [DecidableRel J.Adj]

theorem TriangleData.triM_degree_z : (triM J z w L).degree z = 1 := by
  rw [← card_neighborFinset_eq_degree]
  have : (triM J z w L).neighborFinset z = {r} := by
    ext x
    rw [mem_neighborFinset, Finset.mem_singleton]
    exact hD.triM_adj_z
  rw [this, Finset.card_singleton]

theorem TriangleData.triM_degree_w : (triM J z w L).degree w + 1 = J.degree w := by
  have hwz : J.Adj w z := hD.adj_w.symm
  rw [← delEdge_degree_left J hwz]
  congr 1
  apply degree_congr
  intro x
  show J.Adj w x ∧ s(w, x) ∉ triDel z w L ↔ J.Adj w x ∧ ¬ s(w, x) = s(w, z)
  rw [hD.mem_triDel_w]
  constructor
  · rintro ⟨h, hn⟩
    refine ⟨h, fun he => hn ?_⟩
    rcases Sym2.eq_iff.1 he with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (J.ne_of_adj hwz)
  · rintro ⟨h, hn⟩
    exact ⟨h, fun he => hn (by rw [he])⟩

theorem TriangleData.triM_degree_fst {p : V × V} (hp : p ∈ L) :
    (triM J z w L).degree p.1 + 2 = J.degree p.1 := by
  obtain ⟨-, -, hzL, -, -, -, hnd⟩ := hD.facts
  have hz1 : z ≠ p.2 := fun h => hzL (h ▸ snd_mem_pairVerts hp)
  refine degree_two_deleted (hD.adj_vert (fst_mem_pairVerts hp)).symm (hD.edge p hp) hz1 ?_
  intro v
  show J.Adj p.1 v ∧ s(p.1, v) ∉ triDel z w L ↔ _
  rw [hD.mem_triDel_fst hp, not_or]

theorem TriangleData.triM_degree_snd {p : V × V} (hp : p ∈ L) :
    (triM J z w L).degree p.2 + 2 = J.degree p.2 := by
  obtain ⟨-, -, hzL, -, -, -, hnd⟩ := hD.facts
  have hz1 : z ≠ p.1 := fun h => hzL (h ▸ fst_mem_pairVerts hp)
  refine degree_two_deleted (hD.adj_vert (snd_mem_pairVerts hp)).symm (hD.edge p hp).symm hz1 ?_
  intro v
  show J.Adj p.2 v ∧ s(p.2, v) ∉ triDel z w L ↔ _
  rw [hD.mem_triDel_snd hp, not_or]

omit hD in
theorem triM_degree_other {v : V} (hvz : v ≠ z) (hvw : v ≠ w)
    (hvL : v ∉ pairVerts L) : (triM J z w L).degree v = J.degree v :=
  degree_congr fun x => ⟨fun h => h.1, fun h => ⟨h, not_mem_triDel_other hvz hvw hvL x⟩⟩

/-- **Manuscript Lemma 1.2.** If `z` is the only even vertex of `J`, then in `M` the vertex `w`
is the only one of even degree (and `z` is a leaf at `r`, `triM_adj_z`). -/
theorem TriangleData.triM_parity (hz : ∀ v, Even (J.degree v) ↔ v = z) :
    ∀ v, (triM J z w L).degree v % 2 = if v = w then 0 else 1 := by
  obtain ⟨-, hzw, -, -, -, -, -⟩ := hD.facts
  have hodd : ∀ v, v ≠ z → J.degree v % 2 = 1 := fun v hv =>
    Nat.odd_iff.mp (Nat.not_even_iff_odd.mp (fun he => hv ((hz v).1 he)))
  intro v
  by_cases hvw : v = w
  · subst hvw
    have := hD.triM_degree_w
    have := hodd v (Ne.symm hzw)
    simp only [ite_true]
    omega
  · simp only [hvw, ite_false]
    by_cases hvz : v = z
    · subst hvz; rw [hD.triM_degree_z]
    · by_cases hvL : v ∈ pairVerts L
      · obtain ⟨p, hp, rfl | rfl⟩ := mem_pairVerts.1 hvL
        · have := hD.triM_degree_fst hp
          have := hodd p.1 hvz
          omega
        · have := hD.triM_degree_snd hp
          have := hodd p.2 hvz
          omega
      · rw [triM_degree_other hvz hvw hvL]
        exact hodd v hvz

/-- **Every Lovász decomposition of `M` has `(|J| − 1)/2` paths** (manuscript Lemma 1.2). -/
theorem TriangleData.triM_size (hz : ∀ v, Even (J.degree v) ↔ v = z)
    (D₀ : PathDecomp (triM J z w L)) (hD₀ : ∀ v, D₀.ends v = (triM J z w L).degree v % 2) :
    2 * D₀.size + 1 = Fintype.card V := by
  have hpar := hD.triM_parity hz
  rw [← D₀.sum_ends]
  have h1 : ∑ v, D₀.ends v = ∑ v, (if v ≠ w then 1 else 0) :=
    Finset.sum_congr rfl fun v _ => by
      rw [hD₀ v, hpar v]; by_cases hv : v = w <;> simp [hv]
  rw [h1, ← Finset.card_filter, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ]
  have : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨w⟩
  omega

/-! ### `J − zw − {zaᵢ, zbᵢ}` is `J − z` with a private leaf at `r` -/

omit [Fintype V] [DecidableRel J.Adj] [DecidableEq V] in
theorem TriangleData.leafJ_adj_z {x : V} : (leafJ J z w L).Adj z x ↔ x = r := by
  have h := hD.triM_adj_z (x := x)
  have hz : ∀ x, s(z, x) ∈ zDel z w L ↔ s(z, x) ∈ triDel z w L := by
    intro x
    rw [mem_triDel]
    constructor
    · exact Or.inl
    · rintro (h | ⟨p, hp, h⟩)
      · exact h
      · obtain ⟨-, -, hzL, -, -, -, -⟩ := hD.facts
        rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨h, -⟩
        · exact (hzL (by rw [h]; exact fst_mem_pairVerts hp)).elim
        · exact (hzL (by rw [h]; exact snd_mem_pairVerts hp)).elim
  show J.Adj z x ∧ s(z, x) ∉ zDel z w L ↔ x = r
  rw [hz x]
  exact h

omit [Fintype V] [DecidableRel J.Adj] hD [DecidableEq V] in
theorem leafJ_adj_of_ne {a b : V} (ha : a ≠ z) (hb : b ≠ z) :
    (leafJ J z w L).Adj a b ↔ J.Adj a b := by
  show J.Adj a b ∧ s(a, b) ∉ zDel z w L ↔ J.Adj a b
  refine ⟨fun h => h.1, fun h => ⟨h, fun hm => ?_⟩⟩
  rcases Sym2.mem_iff.1 (z_mem_of_mem_zDel hm) with h' | h'
  · exact ha h'.symm
  · exact hb h'.symm

omit [Fintype V] [DecidableRel J.Adj] in
/-- `leafJ` is `M` plus the matching edges. -/
theorem TriangleData.leafJ_edgeSet (e : Sym2 V) :
    e ∈ (leafJ J z w L).edgeSet ↔ e ∈ (triM J z w L).edgeSet ∨ e ∈ L.map pairEdge := by
  obtain ⟨-, -, hzL, -, -, -, -⟩ := hD.facts
  rw [delList_edgeSet, delList_edgeSet, mem_triDel]
  constructor
  · rintro ⟨he, hn⟩
    by_cases hm : e ∈ L.map pairEdge
    · exact Or.inr hm
    · refine Or.inl ⟨he, ?_⟩
      rintro (h | ⟨p, hp, rfl⟩)
      · exact hn h
      · exact hm (List.mem_map_of_mem hp)
  · rintro (⟨he, hn⟩ | hm)
    · exact ⟨he, fun h => hn (Or.inl h)⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
      refine ⟨hD.edge p hp, fun h => ?_⟩
      rcases Sym2.mem_iff.1 (z_mem_of_mem_zDel h) with h' | h'
      · exact hzL (h' ▸ fst_mem_pairVerts hp)
      · exact hzL (h' ▸ snd_mem_pairVerts hp)

/-- The identification `V → Option (V − z)`, sending `z` to the leaf. -/
def leafMap (z : V) : V → Option {v | v ≠ z} := fun v => if h : v = z then none else some ⟨v, h⟩

omit [Fintype V] [DecidableRel J.Adj] hD in
theorem leafMap_injective (z : V) : Function.Injective (leafMap z) := by
  intro a b h
  unfold leafMap at h
  by_cases ha : a = z <;> by_cases hb : b = z
  · rw [ha, hb]
  · simp [ha, hb] at h
  · simp [ha, hb] at h
  · simp only [ha, hb, dite_false, Option.some.injEq, Subtype.mk.injEq] at h
    exact h

omit [Fintype V] [DecidableRel J.Adj] hD in
theorem leafMap_val (z : V) (a : {v | v ≠ z}) : leafMap z a.1 = some a := by
  have : a.1 ≠ z := a.2
  simp [leafMap, this]

omit [Fintype V] [DecidableRel J.Adj] in
theorem TriangleData.leafMap_edge (hrz : r ≠ z) :
    ∀ e ∈ (leafJ J z w L).edgeSet,
      e.map (leafMap z) ∈ (addLeaf (delVert J z) ⟨r, hrz⟩).edgeSet := by
  intro e he
  induction e using Sym2.inductionOn with
  | hf a b =>
  rw [Sym2.map_mk, mem_edgeSet]
  have hab : (leafJ J z w L).Adj a b := he
  by_cases ha : a = z
  · subst ha
    have hbr := hD.leafJ_adj_z.1 hab
    subst hbr
    have hb : b ≠ a := hD.adj_r.ne'
    simp only [leafMap, hb, dite_true, dite_false]
    rfl
  · by_cases hb : b = z
    · subst hb
      have har := hD.leafJ_adj_z.1 hab.symm
      subst har
      simp only [leafMap, ha, dite_true, dite_false]
      rfl
    · simp only [leafMap, ha, hb, dite_false]
      exact (leafJ_adj_of_ne ha hb).1 hab

omit [Fintype V] [DecidableRel J.Adj] in
theorem TriangleData.leafMap_cov (hrz : r ≠ z) :
    ∀ e' ∈ (addLeaf (delVert J z) ⟨r, hrz⟩).edgeSet,
      ∃ e ∈ (leafJ J z w L).edgeSet, e.map (leafMap z) = e' := by
  intro e' he'
  induction e' using Sym2.inductionOn with
  | hf x y =>
  rw [mem_edgeSet] at he'
  have hzr : r ≠ z := hrz
  have hlr : (leafJ J z w L).Adj z r := hD.leafJ_adj_z.2 rfl
  cases x with
  | none =>
    cases y with
    | none => exact absurd he' id
    | some b =>
      have hb : b = ⟨r, hzr⟩ := he'
      subst hb
      refine ⟨s(z, r), hlr, ?_⟩
      rw [Sym2.map_mk]
      simp [leafMap, hzr]
  | some a =>
    cases y with
    | none =>
      have ha : a = ⟨r, hzr⟩ := he'
      subst ha
      refine ⟨s(r, z), hlr.symm, ?_⟩
      rw [Sym2.map_mk]
      simp [leafMap, hzr]
    | some b =>
      refine ⟨s(a.1, b.1), (leafJ_adj_of_ne a.2 b.2).2 he', ?_⟩
      rw [Sym2.map_mk, leafMap_val, leafMap_val]

end data

/-! ### The direct lift -/

variable (J : SimpleGraph V) [DecidableRel J.Adj]

/-- **The direct lift** (manuscript Theorem 2.1). Let `z` be the only even vertex of `J`, let
`d(r) ≥ 3`, and let `(w, L)` be triangle data at `(J, z, r)`. If some Lovász decomposition of
`M = J − zw − {zaᵢ, zbᵢ, aᵢbᵢ}` satisfies every disjunction `aᵢ ∉ V(Q₀(bᵢ)) ∨ bᵢ ∉ V(Q₀(aᵢ))`,
then `J − z` has a decomposition into at most `(|J| − 1)/2` paths with at least two ends at `r`. -/
theorem test1At_of_triangleBase {z r : V} (hz : ∀ v, Even (J.degree v) ↔ v = z)
    (hr3 : 3 ≤ J.degree r) (h : TriangleBase J z r) : Test1At J z r := by
  intro hr
  obtain ⟨w, L, hD, D₀, hD₀, hdisj⟩ := h
  obtain ⟨hzr, hzw, hzL, hrw, hrL, hwL, hnd⟩ := hD.facts
  have hpar := hD.triM_parity hz
  -- Step 2 of the manuscript: append the matching at the chosen ends
  have hend : ∀ p ∈ L, 1 ≤ D₀.ends p.1 ∧ 1 ≤ D₀.ends p.2 := by
    intro p hp
    have h1 := hpar p.1
    have h2 := hpar p.2
    have hw1 : p.1 ≠ w := fun h => hwL (h ▸ fst_mem_pairVerts hp)
    have hw2 : p.2 ≠ w := fun h => hwL (h ▸ snd_mem_pairVerts hp)
    simp only [hw1, hw2, ite_false] at h1 h2
    rw [hD₀, hD₀]
    omega
  have hnotM : ∀ p ∈ L, ¬ (triM J z w L).Adj p.1 p.2 := fun p hp h =>
    h.2 (List.mem_append_right _ (List.mem_map_of_mem hp))
  obtain ⟨D₁, hD₁⟩ := append_pairs (G := leafJ J z w L) L (triM J z w L) hD.leafJ_edgeSet hnotM
    hnd D₀ hend hdisj
  -- Step 1 of the manuscript: delete the leaf `z`
  let D₂ := D₁.mapInj (leafMap z) (leafMap_injective z) (hD.leafMap_edge hr.ne')
    (hD.leafMap_cov hr.ne')
  have hD₂ : D₂.size = D₁.size := PathDecomp.mapInj_size _ _ _ _ _
  obtain ⟨D₃, hD₃⟩ := PathDecomp.trim_ends D₂
  have hcost : leafCost D₃ ⟨r, hr.ne'⟩ ≤ D₀.size := by
    unfold leafCost
    rcases hD₃ with ⟨h1, h2⟩ | ⟨h1, -⟩
    · have : D₃.ends ⟨r, hr.ne'⟩ ≠ 0 := by rw [h2]; exact Nat.succ_ne_zero _
      simp only [this, ite_false]
      omega
    · split_ifs <;> omega
  -- the root has positive even degree in `J − z`
  have hdeg : (delVert J z).degree ⟨r, hr.ne'⟩ + (if J.Adj r z then 1 else 0) = J.degree r :=
    delVert_degree z ⟨r, hr.ne'⟩
  simp only [hr.symm, ite_true] at hdeg
  have hrodd : J.degree r % 2 = 1 :=
    Nat.odd_iff.mp (Nat.not_even_iff_odd.mp (fun he => hzr ((hz r).1 he).symm))
  have hev : Even ((delVert J z).degree ⟨r, hr.ne'⟩) := by rw [Nat.even_iff]; omega
  have hpos : 0 < (delVert J z).degree ⟨r, hr.ne'⟩ := by omega
  obtain ⟨D, hDsize, hDends⟩ := exists_two_ends D₃ hcost hev hpos
  have hsize := hD.triM_size hz D₀ hD₀
  exact ⟨D, by omega, hDends⟩

/-- **Test1 from triangle bases**: if every neighbour of `z` has degree at least three and every
`r ∈ N(z)` has a triangle base, then `Test1 J z`. -/
theorem test1_of_triangleBases (z : V) (hdeg : ∀ r, J.Adj z r → 3 ≤ J.degree r)
    (h : (∀ v, Even (J.degree v) ↔ v = z) → ∀ r, J.Adj z r → TriangleBase J z r) :
    Test1 J z :=
  test1_of_test1At J z fun hz r hr => test1At_of_triangleBase J hz (hdeg r hr) (h hz r hr)

end lift

/-- **The triangle base conjecture** (manuscript Conjecture 3.1): in a three-connected graph whose
only even vertex is `z`, every root `r ∈ N(z)` that admits triangle data admits a triangle base. -/
def TriangleBaseConj : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj] (z : V),
    KConnected 3 J → (∀ v, Even (J.degree v) ↔ v = z) → ∀ r, J.Adj z r →
      (∃ w L, TriangleData J z r w L) → TriangleBase J z r

/-- **The triangle base conjecture gives Test1 wherever the data exist.** -/
theorem test1_of_triangleBaseConj (hC : TriangleBaseConj.{u}) {V : Type u} [Fintype V]
    [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj] (z : V) (hJ : KConnected 3 J)
    (hdata : ∀ r, J.Adj z r → ∃ w L, TriangleData J z r w L) : Test1 J z :=
  test1_of_triangleBases J z (fun r _ => hJ.le_degree r)
    fun hz r hr => hC V J z hJ hz r hr (hdata r hr)

end Gallai
