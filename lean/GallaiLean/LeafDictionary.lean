import GallaiLean.Realisable

/-!
# The leaf dictionary (endpoint-structure manuscript, Lemma 4)

`leaves G S` is `G` (on `inl`) with a private leaf `inr s` attached at each `s ∈ S`. The other
`inr v` are isolated and do not affect path decompositions.

* `PathDecomp.extend_pendant`: attach a pendant edge at an end of a decomposition.
* `realisable_of_retract`: a general repair step. Given a decomposition of a graph retracting
  onto `G` with the right end counts on the kept vertices, delete the other vertices and split
  the vertices of `T` left without ends.
* `card_oddSet_leaves`: `#Od(G^S) = #Od(G) + 2|S|`.
* **`realisable_iff_leaves`**: for `S ⊆ Ev(G)`, `S` is realisable iff
  `p(G^S) = #Od(G^S) / 2`.
-/

open SimpleGraph

namespace Gallai

universe u v

/-! ### Pendant edges -/

section pendant

variable {U : Type v} [DecidableEq U] {K : SimpleGraph U}

theorem GPath.exists_edge_of_mem_support (P : GPath K) {x : U} (hx : x ∈ P.walk.support) :
    ∃ e ∈ P.edges, x ∈ e := by
  have h := P.incid_add_endsAt x
  have hne := P.src_ne_tgt
  have hle : P.endsAt x ≤ 1 := by
    rw [P.endsAt_eq_ite]; split_ifs <;> omega
  simp only [hx, ite_true] at h
  have : 0 < P.incid x := by omega
  obtain ⟨e, he, hxe⟩ := List.countP_pos_iff.mp this
  exact ⟨e, he, by simpa using hxe⟩

/-- A vertex all of whose edges equal `e₀` is not interior to any path. -/
theorem GPath.end_of_pendant (P : GPath K) {x : U} {e₀ : Sym2 U}
    (hx : ∀ e ∈ K.edgeSet, x ∈ e → e = e₀) (hmem : x ∈ P.walk.support) :
    P.src = x ∨ P.tgt = x := by
  by_contra hc
  rw [not_or] at hc
  have h2 := P.incid_of_internal hmem hc.1 hc.2
  have hnd : P.edges.Nodup := P.isPath.isTrail.edges_nodup
  have h1 : P.incid x ≤ 1 := by
    unfold GPath.incid
    calc P.edges.countP (fun e => decide (x ∈ e))
        ≤ P.edges.countP (fun e => e == e₀) := by
          apply List.countP_mono_left
          intro e he hxe
          simp only [decide_eq_true_eq] at hxe
          simp [hx e (P.walk.edges_subset_edgeSet he) hxe]
      _ = P.edges.count e₀ := rfl
      _ ≤ 1 := List.nodup_iff_count_le_one.mp hnd _
  omega

/-- **Attaching a pendant edge** `x — y` (with `y` isolated) at an end `x` of a decomposition:
same size, one end moves from `x` to `y`. -/
theorem PathDecomp.extend_pendant {K' : SimpleGraph U} {x y : U}
    (hK' : ∀ e, e ∈ K'.edgeSet ↔ e ∈ K.edgeSet ∨ e = s(x, y)) (hy : ∀ e ∈ K.edgeSet, y ∉ e)
    (hxy : K'.Adj x y) (D : PathDecomp K) (hx : 0 < D.ends x) :
    ∃ D' : PathDecomp K', D'.size = D.size ∧
      ∀ w, D'.ends w + (if x = w then 1 else 0) = D.ends w + (if y = w then 1 else 0) := by
  obtain ⟨Q, hQ, hQx⟩ : ∃ Q ∈ D.paths, Q.endsAt x ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_and, not_not] at hc
    have : D.ends x = 0 := by
      unfold PathDecomp.ends
      exact List.sum_eq_zero_iff_forall_eq_nat.mpr (by simpa using hc)
    omega
  obtain ⟨Q', hQ's, hQ'e, hQ'ends⟩ : ∃ Q' : GPath K, Q'.src = x ∧ Q'.edges.Perm Q.edges ∧
      ∀ w, Q'.endsAt w = Q.endsAt w := by
    unfold GPath.endsAt at hQx
    by_cases hs : Q.src = x
    · exact ⟨Q, hs, List.Perm.refl _, fun _ => rfl⟩
    · have ht : Q.tgt = x := by
        by_contra ht; simp [hs, ht] at hQx
      exact ⟨Q.reverse, ht, by simp [List.reverse_perm],
        fun w => by simp only [GPath.endsAt, GPath.reverse]; exact Nat.add_comm _ _⟩
  have hsub : ∀ e ∈ K.edgeSet, e ∈ K'.edgeSet := fun e he => (hK' e).2 (Or.inl he)
  have htr : ∀ {a b : U} (p : K.Walk a b), ∀ e ∈ p.edges, e ∈ K'.edgeSet :=
    fun p e he => hsub e (p.edges_subset_edgeSet he)
  obtain ⟨up, hup_edges, hup_ends⟩ : ∃ up : GPath K → GPath K',
      (∀ P, (up P).edges = P.edges) ∧ ∀ P w, (up P).endsAt w = P.endsAt w :=
    ⟨fun P => ⟨P.src, P.tgt, P.walk.transfer K' (htr P.walk), P.isPath.transfer _,
      by simpa using P.pos⟩, fun P => by simp [GPath.edges], fun _ _ => rfl⟩
  have hyQ : y ∉ Q'.walk.support := by
    intro hm
    obtain ⟨e, he, hye⟩ := Q'.exists_edge_of_mem_support hm
    exact hy e (Q'.walk.edges_subset_edgeSet he) hye
  obtain ⟨E, hE, hEends⟩ : ∃ E : GPath K', E.edges.Perm (s(x, y) :: Q.edges) ∧
      ∀ w, E.endsAt w = (if y = w then 1 else 0) + (if Q'.tgt = w then 1 else 0) := by
    have hadj : K'.Adj y Q'.src := hQ's ▸ hxy.symm
    have hw' : (Q'.walk.transfer K' (htr Q'.walk)).IsPath := Q'.isPath.transfer _
    refine ⟨⟨y, Q'.tgt, Walk.cons hadj (Q'.walk.transfer K' (htr Q'.walk)), ?_, by simp⟩, ?_,
      fun w => rfl⟩
    · rw [Walk.cons_isPath_iff]
      refine ⟨hw', ?_⟩
      rw [Walk.support_transfer]
      exact hyQ
    · show (Walk.cons hadj (Q'.walk.transfer K' (htr Q'.walk))).edges.Perm _
      have hs : s(y, Q'.src) = s(x, y) := by rw [hQ's, Sym2.eq_swap]
      rw [Walk.edges_cons, Walk.edges_transfer, hs]
      exact List.Perm.cons _ hQ'e
  obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hQ
  let L := l₁.map up ++ E :: l₂.map up
  have hperm : (L.flatMap GPath.edges).Perm (s(x, y) :: D.paths.flatMap GPath.edges) := by
    have h1 : ∀ l : List (GPath K), (l.map up).flatMap GPath.edges = l.flatMap GPath.edges :=
      fun l => by rw [List.flatMap_map]; simp only [hup_edges]
    simp only [L, hl, List.flatMap_append, List.flatMap_cons, h1]
    refine (List.Perm.append_left _ (hE.append_right _)).trans ?_
    rw [List.cons_append]
    exact List.perm_middle
  have hnd : (s(x, y) :: D.paths.flatMap GPath.edges).Nodup := by
    rw [List.nodup_cons]
    refine ⟨fun h => hy _ ((D.covers _).2 h) (Sym2.mem_mk_right x y), D.nodup_edges⟩
  have hcov : ∀ e, e ∈ K'.edgeSet ↔ e ∈ s(x, y) :: D.paths.flatMap GPath.edges := by
    intro e
    rw [hK', List.mem_cons, ← D.covers, or_comm]
  refine ⟨PathDecomp.ofPerm L _ hperm hnd hcov, ?_, fun w => ?_⟩
  · simp [PathDecomp.size, L, hl]
  · unfold PathDecomp.ends
    simp only [PathDecomp.ofPerm_paths, L, hl, List.map_append, List.map_cons, List.sum_append,
      List.sum_cons, List.map_map, Function.comp_def, hup_ends]
    have hEw := hEends w
    have hQw : Q.endsAt w = (if x = w then 1 else 0) + (if Q'.tgt = w then 1 else 0) := by
      rw [← hQ'ends]; simp only [GPath.endsAt, hQ's]
    rw [hEw, hQw]
    omega

end pendant

/-! ### A general repair step -/

section repair

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- From a decomposition of a graph retracting onto `G` with one end at each kept vertex outside
`T` of odd degree, none at the other kept vertices outside `T`, and at most one at the vertices
of `T`, delete the non-kept vertices and split the vertices of `T` left without ends. -/
theorem realisable_of_retract {U : Type v} [DecidableEq U] {K : SimpleGraph U}
    (R : Retract K G) {T : Finset V} (hT : T ⊆ evenSet G) (D : PathDecomp K)
    (hD : ∀ P ∈ D.paths, ∀ x ∈ P.walk.support, R.kept x = false → x = P.src ∨ x = P.tgt)
    (hout : ∀ v ∉ T, (∀ e ∈ K.edgeSet, bothKept R.kept e = false → R.ι v ∉ e) ∧
      D.ends (R.ι v) = if Odd (G.degree v) then 1 else 0)
    (hin : ∀ v ∈ T, (∀ e₁ ∈ K.edgeSet, ∀ e₂ ∈ K.edgeSet, bothKept R.kept e₁ = false →
        bothKept R.kept e₂ = false → R.ι v ∈ e₁ → R.ι v ∈ e₂ → e₁ = e₂) ∧
      D.ends (R.ι v) ≤ 1) :
    Realisable G T := by
  refine ⟨hT, ?_⟩
  obtain ⟨D₂, hD₂⟩ := R.delete D hD
  have h₂T : ∀ v ∈ T, D₂.ends v = 0 ∨ D₂.ends v = 2 := by
    intro v hv
    have hvE := (Finset.mem_filter.mp (hT hv)).2
    have hle := (hD₂ v).2 (hin v hv).1
    have h1 := (hin v hv).2
    have hpar := D₂.ends_mod_two v
    have : G.degree v % 2 = 0 := Nat.even_iff.mp hvE.2
    omega
  have h₂nT : ∀ v ∉ T, D₂.ends v = if Odd (G.degree v) then 1 else 0 := fun v hv =>
    ((hD₂ v).1 (hout v hv).1).trans (hout v hv).2
  obtain ⟨D₃, -, he₃⟩ := D₂.exists_split_set (T.filter (fun v => D₂.ends v = 0)) (by
    intro z hz
    have hzT := Finset.mem_filter.mp hz
    exact ⟨(Finset.mem_filter.mp (hT hzT.1)).2.1, hzT.2⟩)
  refine ⟨D₃, fun v => ?_⟩
  rw [he₃]
  unfold profile
  by_cases hvT : v ∈ T
  · simp only [not_odd_of_mem_evenSet (hT hvT), ite_false, hvT, ite_true, Finset.mem_filter,
      true_and]
    rcases h₂T v hvT with h | h <;> simp [h]
  · have : v ∉ T.filter (fun v => D₂.ends v = 0) := fun hz => hvT (Finset.mem_filter.mp hz).1
    simp only [this, ite_false, add_zero, h₂nT v hvT, hvT]

end repair

/-! ### Private leaves at a set of vertices -/

section leaves

variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `G` (on `inl`) with a private leaf `inr s` at each `s ∈ S`. -/
def leaves (S : Finset V) : SimpleGraph (V ⊕ V) where
  Adj x y := match x, y with
    | .inl a, .inl b => G.Adj a b
    | .inl a, .inr b => a = b ∧ a ∈ S
    | .inr a, .inl b => a = b ∧ a ∈ S
    | .inr _, .inr _ => False
  symm := ⟨fun x y h => by
    rcases x with a | a <;> rcases y with b | b <;> simp only at h ⊢
    · exact h.symm
    · obtain ⟨rfl, h⟩ := h; exact ⟨rfl, h⟩
    · obtain ⟨rfl, h⟩ := h; exact ⟨rfl, h⟩⟩
  loopless := ⟨fun x h => by
    rcases x with a | a <;> simp only at h
    exact G.loopless.irrefl _ h⟩

variable {G} {S : Finset V}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem leaves_adj_inl_inl {a b : V} : (leaves G S).Adj (.inl a) (.inl b) ↔ G.Adj a b :=
  Iff.rfl
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem leaves_adj_inl_inr {a b : V} :
    (leaves G S).Adj (.inl a) (.inr b) ↔ a = b ∧ a ∈ S := Iff.rfl
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem leaves_adj_inr_inl {a b : V} :
    (leaves G S).Adj (.inr a) (.inl b) ↔ a = b ∧ a ∈ S := Iff.rfl
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem leaves_not_adj_inr_inr {a b : V} : ¬ (leaves G S).Adj (.inr a) (.inr b) := id

instance leaves.decRel (S : Finset V) : DecidableRel (leaves G S).Adj := fun x y =>
  match x, y with
  | .inl a, .inl b => inferInstanceAs (Decidable (G.Adj a b))
  | .inl a, .inr b => inferInstanceAs (Decidable (a = b ∧ a ∈ S))
  | .inr a, .inl b => inferInstanceAs (Decidable (a = b ∧ a ∈ S))
  | .inr _, .inr _ => inferInstanceAs (Decidable False)

theorem leaves_degree_inl (v : V) :
    (leaves G S).degree (.inl v) = G.degree v + if v ∈ S then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
    neighborFinset_eq_filter, neighborFinset_eq_filter (G := G), Finset.card_filter,
    Finset.card_filter, Fintype.sum_sum_type]
  simp only [leaves_adj_inl_inl, leaves_adj_inl_inr]
  congr 1
  by_cases hv : v ∈ S <;> simp [hv]

theorem leaves_degree_inr (v : V) : (leaves G S).degree (.inr v) = if v ∈ S then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter,
    Fintype.sum_sum_type]
  simp only [leaves_adj_inr_inl, leaves_not_adj_inr_inr, ite_false, Finset.sum_const_zero,
    add_zero]
  by_cases hv : v ∈ S <;> simp [hv]

/-- `#Od(G^S) = #Od(G) + 2|S|`. -/
theorem card_oddSet_leaves (hS : S ⊆ evenSet G) :
    (oddSet (leaves G S)).card = (oddSet G).card + 2 * S.card := by
  have hv : ∀ v, (if Odd ((leaves G S).degree (.inl v)) then 1 else 0) =
      (if Odd (G.degree v) then 1 else 0) + (if v ∈ S then 1 else 0) := by
    intro v
    rw [leaves_degree_inl]
    by_cases hvS : v ∈ S
    · have := not_odd_of_mem_evenSet (hS hvS)
      simp [hvS, this, Nat.odd_add_one]
    · simp [hvS]
  have hw : ∀ v, (if Odd ((leaves G S).degree (.inr v)) then 1 else 0) =
      (if v ∈ S then 1 else 0) := by
    intro v
    rw [leaves_degree_inr]
    by_cases hvS : v ∈ S <;> simp [hvS]
  unfold oddSet
  rw [Finset.card_filter, Fintype.sum_sum_type, Finset.sum_congr rfl (fun v _ => hv v),
    Finset.sum_congr rfl (fun v _ => hw v), Finset.sum_add_distrib, ← Finset.card_filter,
    Finset.sum_boole]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]
  ring

omit [Fintype V] [DecidableRel G.Adj] in
theorem leaves_insert_edgeSet {s : V} :
    ∀ e, e ∈ (leaves G (insert s S)).edgeSet ↔
      e ∈ (leaves G S).edgeSet ∨ e = s(.inl s, .inr s) := by
  intro e
  induction e using Sym2.inductionOn with
  | hf x y =>
  rw [mem_edgeSet, mem_edgeSet]
  rcases x with a | a <;> rcases y with b | b
  · simp
  · simp only [leaves_adj_inl_inr, Finset.mem_insert, Sym2.eq_iff, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, and_false, or_false]
    constructor
    · rintro ⟨rfl, rfl | h⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, h⟩
    · rintro (⟨rfl, h⟩ | ⟨rfl, rfl⟩)
      · exact ⟨rfl, Or.inr h⟩
      · exact ⟨rfl, Or.inl rfl⟩
  · simp only [leaves_adj_inr_inl, Finset.mem_insert, Sym2.eq_iff, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, false_and, false_or]
    constructor
    · rintro ⟨rfl, rfl | h⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, h⟩
    · rintro (⟨rfl, h⟩ | ⟨rfl, rfl⟩)
      · exact ⟨rfl, Or.inr h⟩
      · exact ⟨rfl, Or.inl rfl⟩
  · simp

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem leaves_inr_isolated {s : V} (hs : s ∉ S) :
    ∀ e ∈ (leaves G S).edgeSet, (.inr s : V ⊕ V) ∉ e := by
  intro e he hse
  induction e using Sym2.inductionOn with
  | hf x y =>
  rw [mem_edgeSet] at he
  rcases Sym2.mem_iff.mp hse with rfl | rfl
  · rcases y with b | b
    · exact hs (he.1 ▸ he.2)
    · exact he
  · rcases x with b | b
    · exact hs (he.1.symm ▸ he.2)
    · exact he

omit [Fintype V] [DecidableRel G.Adj] in
/-- `D` copied onto `leaves G ∅`. -/
theorem leaves_empty_decomp (D : PathDecomp G) :
    ∃ D' : PathDecomp (leaves G ∅), D'.size = D.size ∧ ∀ v, D'.ends (.inl v) = D.ends v := by
  have hf : ∀ P : GPath G, ∀ e ∈ P.walk.edges, e.map Sum.inl ∈ (leaves G ∅).edgeSet := by
    intro P e he
    have heG := P.walk.edges_subset_edgeSet he
    induction e using Sym2.inductionOn with
    | hf a b => simpa using heG
  let L := D.paths.map (fun P => P.push Sum.inl (hf P) (fun _ _ _ _ h => Sum.inl_injective h))
  have hL : L.flatMap GPath.edges = (D.paths.flatMap GPath.edges).map (Sym2.map Sum.inl) := by
    simp [L, List.flatMap_map, List.map_flatMap]
  have hnd := D.nodup_edges.map (Sym2.map.injective (f := (Sum.inl : V → V ⊕ V)) Sum.inl_injective)
  have hcov : ∀ e, e ∈ (leaves G ∅).edgeSet ↔
      e ∈ (D.paths.flatMap GPath.edges).map (Sym2.map Sum.inl) := by
    intro e
    rw [List.mem_map]
    simp only [← D.covers]
    induction e using Sym2.inductionOn with
    | hf x y =>
    rw [mem_edgeSet]
    constructor
    · intro h
      rcases x with a | a <;> rcases y with b | b
      · exact ⟨s(a, b), h, rfl⟩
      · simp at h
      · simp at h
      · exact absurd h leaves_not_adj_inr_inr
    · rintro ⟨e', he', hmap⟩
      induction e' using Sym2.inductionOn with
      | hf c d =>
      simp only [Sym2.map_mk] at hmap
      rcases Sym2.eq_iff.mp hmap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact he'
      · exact (leaves G ∅).symm.symm _ _ he'
  refine ⟨PathDecomp.ofPerm L _ (hL ▸ List.Perm.refl _) hnd hcov, by simp [PathDecomp.size, L],
    fun v => ?_⟩
  unfold PathDecomp.ends
  simp only [PathDecomp.ofPerm_paths, L, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro P _
  simp [GPath.push, GPath.endsAt]

/-- A realisation of `S` gives a decomposition of `G^S` of the same size (attach each leaf at
one of the two ends at its vertex). -/
theorem leaves_decomp_of_realises (hS : S ⊆ evenSet G) {D : PathDecomp G}
    (hD : Realises G D S) : ∃ D' : PathDecomp (leaves G S), D'.size = D.size := by
  have key : ∀ S' : Finset V, S' ⊆ S → ∃ D' : PathDecomp (leaves G S'), D'.size = D.size ∧
      ∀ v ∉ S', D'.ends (.inl v) = D.ends v := by
    intro S'
    induction S' using Finset.induction_on with
    | empty =>
      intro _
      obtain ⟨D', h1, h2⟩ := leaves_empty_decomp D
      exact ⟨D', h1, fun v _ => h2 v⟩
    | @insert s S' hs ih =>
      intro hsub
      obtain ⟨D₁, hs₁, he₁⟩ := ih ((Finset.subset_insert _ _).trans hsub)
      have hsS : s ∈ S := hsub (Finset.mem_insert_self _ _)
      have hpos : 0 < D₁.ends (.inl s) := by
        rw [he₁ s hs, hD s]
        unfold profile
        simp [not_odd_of_mem_evenSet (hS hsS), hsS]
      obtain ⟨D₂, hs₂, he₂⟩ := D₁.extend_pendant leaves_insert_edgeSet
        (leaves_inr_isolated hs) ⟨rfl, Finset.mem_insert_self _ _⟩ hpos
      refine ⟨D₂, hs₂.trans hs₁, fun v hv => ?_⟩
      have hvs : s ≠ v := fun h => hv (h ▸ Finset.mem_insert_self _ _)
      have := he₂ (.inl v)
      simp only [Sum.inl.injEq, hvs, ite_false, add_zero, reduceCtorEq] at this
      rw [this, he₁ v (fun h => hv (Finset.mem_insert_of_mem h))]
  obtain ⟨D', h1, -⟩ := key S (subset_refl _)
  exact ⟨D', h1⟩

variable (G S) in
/-- `G^S` retracts onto `G`. -/
def leavesRetract : Retract (leaves G S) G where
  ι := Sum.inl
  f := Sum.elim id id
  kept := Sum.isLeft
  f_ι _ := rfl
  kept_iff x := by rcases x with a | a <;> simp
  adj_iff _ _ := Iff.rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem leaves_nonkept {e : Sym2 (V ⊕ V)} (he : e ∈ (leaves G S).edgeSet)
    (hk : bothKept Sum.isLeft e = false) {v : V} (hv : (.inl v : V ⊕ V) ∈ e) :
    e = s(.inl v, .inr v) ∧ v ∈ S := by
  induction e using Sym2.inductionOn with
  | hf x y =>
  rw [mem_edgeSet] at he
  rcases Sym2.mem_iff.mp hv with rfl | rfl
  · rcases y with b | b
    · simp at hk
    · obtain ⟨rfl, h⟩ := he; exact ⟨rfl, h⟩
  · rcases x with b | b
    · simp at hk
    · obtain ⟨rfl, h⟩ := he; exact ⟨Sym2.eq_swap, h⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem leaves_inr_pendant (w : V) :
    ∀ e ∈ (leaves G S).edgeSet, (.inr w : V ⊕ V) ∈ e → e = s(.inl w, .inr w) := by
  intro e he hw
  induction e using Sym2.inductionOn with
  | hf x y =>
  rw [mem_edgeSet] at he
  rcases Sym2.mem_iff.mp hw with rfl | rfl
  · rcases y with b | b
    · obtain ⟨rfl, -⟩ := he; exact Sym2.eq_swap
    · exact absurd he leaves_not_adj_inr_inr
  · rcases x with b | b
    · obtain ⟨rfl, -⟩ := he; rfl
    · exact absurd he leaves_not_adj_inr_inr

/-- **Leaf dictionary** (Lemma 4): for `S ⊆ Ev(G)`, `S` is realisable iff the graph `G^S` with
a private leaf at each vertex of `S` satisfies `p(G^S) = #Od(G^S) / 2`. -/
theorem realisable_iff_leaves (hS : S ⊆ evenSet G) :
    Realisable G S ↔ pathNumber (leaves G S) = (oddSet (leaves G S)).card / 2 := by
  have hlow := card_odd_le_two_mul_pathNumber (G := leaves G S)
  have hodd := card_oddSet_leaves hS
  obtain ⟨k, hk⟩ := G.even_card_odd_degree_vertices
  unfold oddSet at hodd ⊢
  constructor
  · rintro ⟨-, D, hD⟩
    have hsize := Realises.size_eq hS hD
    obtain ⟨D', hD'⟩ := leaves_decomp_of_realises hS hD
    have := pathNumber_le D'
    unfold oddSet at hsize
    omega
  · intro hp
    obtain ⟨D, hD⟩ := pathNumber_spec (leaves G S)
    have htight := D.ends_eq_of_tight (by omega)
    refine realisable_of_retract (leavesRetract G S) hS D ?_ ?_ ?_
    · intro P _ x hx hkx
      rcases x with a | w
      · simp [leavesRetract] at hkx
      · exact (P.end_of_pendant (leaves_inr_pendant w) hx).imp Eq.symm Eq.symm
    · intro v hv
      refine ⟨fun e he hk hve => hv (leaves_nonkept he hk hve).2, ?_⟩
      change D.ends (.inl v) = _
      rw [htight, leaves_degree_inl]
      simp [hv]
    · intro v hv
      refine ⟨fun e₁ he₁ e₂ he₂ hk₁ hk₂ hv₁ hv₂ => by
        rw [(leaves_nonkept he₁ hk₁ hv₁).1, (leaves_nonkept he₂ hk₂ hv₂).1], ?_⟩
      change D.ends (.inl v) ≤ 1
      rw [htight]
      split_ifs <;> omega

end leaves

end Gallai
