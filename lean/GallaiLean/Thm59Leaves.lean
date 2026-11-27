import GallaiLean.Doubling
import GallaiLean.ThreeConnected
import GallaiLean.MarkedSurgery

/-!
# Private leaves at a set of marks, and trimming them

Marked-reduction manuscript, §2.1 ("Distinct private leaves for even marks") and the proof of
Theorem 7.

`leafGraph B A` lives on `V ⊕ V`. The vertex `inl v` is `v`. For each mark `a ∈ A`, the vertex
`inr a` is a private leaf at `a`. The other `inr` vertices are isolated.

**`leafGraph_trim`.** Every decomposition `D` of `leafGraph B A` trims to a decomposition `D'` of
`B` with `|D'| + #{a ∈ A : a is not an end of D'} ≤ |D|`.

Proof. Delete the leaf edges from every path. The paths that consisted of one leaf edge
disappear. Every other path through the leaf at `a` keeps exactly one edge at `a`, so `a` becomes
one of its ends. The machinery is `PathDecomp.project_full` along `Sum.elim id id`.
-/

open SimpleGraph

set_option linter.unusedSectionVars false

namespace Gallai

universe u

variable {V : Type u} [DecidableEq V]

/-- `B` on `inl`, with a private leaf `inr a` at every `a ∈ A`. -/
def leafGraph (B : SimpleGraph V) (A : Finset V) : SimpleGraph (V ⊕ V) where
  Adj x y := match x, y with
    | .inl u, .inl v => B.Adj u v
    | .inl u, .inr v => u = v ∧ v ∈ A
    | .inr u, .inl v => u = v ∧ u ∈ A
    | .inr _, .inr _ => False
  symm := ⟨fun x y h => by
    cases x <;> cases y <;> simp only at h ⊢
    · exact h.symm
    · exact ⟨h.1.symm, h.2⟩
    · exact ⟨h.1.symm, h.2⟩⟩
  loopless := ⟨fun x h => by
    cases x <;> simp only at h
    exact B.loopless.irrefl _ h⟩

variable {B : SimpleGraph V} {A : Finset V}

@[simp] theorem leafGraph_adj_inl_inl {u v : V} :
    (leafGraph B A).Adj (.inl u) (.inl v) ↔ B.Adj u v := Iff.rfl
@[simp] theorem leafGraph_adj_inl_inr {u v : V} :
    (leafGraph B A).Adj (.inl u) (.inr v) ↔ u = v ∧ v ∈ A := Iff.rfl
@[simp] theorem leafGraph_adj_inr_inl {u v : V} :
    (leafGraph B A).Adj (.inr u) (.inl v) ↔ u = v ∧ u ∈ A := Iff.rfl
@[simp] theorem leafGraph_not_adj_inr_inr {u v : V} : ¬ (leafGraph B A).Adj (.inr u) (.inr v) :=
  id

/-- Edges with both ends in `inl`. -/
def bothInl : Sym2 (V ⊕ V) → Bool :=
  Sym2.lift ⟨fun x y => x.isLeft && y.isLeft, fun _ _ => Bool.and_comm _ _⟩

@[simp] theorem bothInl_mk (x y : V ⊕ V) : bothInl s(x, y) = (x.isLeft && y.isLeft) := rfl

/-- The trimming map. -/
def unSum : V ⊕ V → V := Sum.elim id id

theorem unSum_injOn : Set.InjOn (unSum : V ⊕ V → V) (Set.range Sum.inl) := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
  simp only [unSum, Sum.elim_inl, id] at h
  rw [h]

theorem leaf_hT : ∀ e ∈ (leafGraph B A).edgeSet, bothInl e = true →
    ∀ x ∈ e, x ∈ Set.range (Sum.inl : V → V ⊕ V) := by
  intro e _ hS x hx
  induction e using Sym2.inductionOn with
  | hf a b =>
  simp only [bothInl_mk, Bool.and_eq_true] at hS
  rcases Sym2.mem_iff.mp hx with rfl | rfl
  · exact ⟨_, (Sum.isLeft_iff.mp hS.1).choose_spec.symm⟩
  · exact ⟨_, (Sum.isLeft_iff.mp hS.2).choose_spec.symm⟩

theorem leaf_hcov : ∀ e', e' ∈ B.edgeSet ↔
    ∃ e ∈ (leafGraph B A).edgeSet, bothInl e = true ∧ e.map unSum = e' := by
  intro e'
  induction e' using Sym2.inductionOn with
  | hf a b =>
  constructor
  · intro h
    exact ⟨s(.inl a, .inl b), h, rfl, rfl⟩
  · rintro ⟨e, he, hS, hmap⟩
    induction e using Sym2.inductionOn with
    | hf x y =>
    cases x with
    | inr x => simp at hS
    | inl x =>
    cases y with
    | inr y => simp at hS
    | inl y =>
    simp only [Sym2.map_mk, unSum, Sum.elim_inl, id] at hmap
    rw [← hmap]
    exact he

/-- The only edge at a leaf. -/
theorem leaf_eq_of_inr_mem {e : Sym2 (V ⊕ V)} (he : e ∈ (leafGraph B A).edgeSet) {a : V}
    (h : .inr a ∈ e) : e = s(.inl a, .inr a) ∧ a ∈ A := by
  induction e using Sym2.inductionOn with
  | hf x y =>
  rw [mem_edgeSet] at he
  rcases Sym2.mem_iff.mp h with rfl | rfl
  · cases y with
    | inr y => exact absurd he leafGraph_not_adj_inr_inr
    | inl y =>
      obtain ⟨rfl, ha⟩ := he
      exact ⟨Sym2.eq_swap, ha⟩
  · cases x with
    | inr x => exact absurd he leafGraph_not_adj_inr_inr
    | inl x =>
      obtain ⟨rfl, ha⟩ := he
      exact ⟨rfl, ha⟩

/-- A path through a leaf has it as an end. -/
theorem leaf_inr_end (P : GPath (leafGraph B A)) {a : V} (hn : .inr a ∈ P.walk.support) :
    P.src = .inr a ∨ P.tgt = .inr a := by
  classical
  by_contra hc
  rw [not_or] at hc
  have h2 := P.incid_of_internal hn hc.1 hc.2
  have hnd : P.edges.Nodup := P.isPath.isTrail.edges_nodup
  have h1 : P.incid (.inr a) ≤ 1 := by
    unfold GPath.incid
    calc P.edges.countP (fun e => decide (.inr a ∈ e))
        ≤ P.edges.countP (fun e => e == s(.inl a, .inr a)) := by
          apply List.countP_mono_left
          intro e he hne
          simp only [decide_eq_true_eq] at hne
          simp [(leaf_eq_of_inr_mem (P.walk.edges_subset_edgeSet he) hne).1]
      _ = P.edges.count s(.inl a, .inr a) := rfl
      _ ≤ 1 := List.nodup_iff_count_le_one.mp hnd _
  omega

/-- A sub-path avoiding the leaves gives a piece. -/
theorem leaf_piece_of_walk {x y : V ⊕ V} (p : (leafGraph B A).Walk x y) (hp : p.IsPath)
    (hn : ∀ v ∈ p.support, v.isLeft = true) {l : List (Sym2 (V ⊕ V))}
    (hperm : p.edges.Perm (l.filter bothInl)) :
    ∃ o : Option (GPath B), (optEdges o).Perm ((l.filter bothInl).map (Sym2.map unSum)) := by
  have hf : ∀ e ∈ p.edges, e.map unSum ∈ B.edgeSet := by
    intro e he
    refine (leaf_hcov _).2 ⟨e, p.edges_subset_edgeSet he, ?_, rfl⟩
    induction e using Sym2.inductionOn with
    | hf a b =>
    simp only [bothInl_mk, Bool.and_eq_true]
    exact ⟨hn a (p.fst_mem_support_of_mem_edges he), hn b (p.snd_mem_support_of_mem_edges he)⟩
  have hinj : ∀ a ∈ p.support, ∀ b ∈ p.support, unSum a = unSum b → a = b := by
    intro a ha b hb h
    obtain ⟨a', rfl⟩ := Sum.isLeft_iff.mp (hn a ha)
    obtain ⟨b', rfl⟩ := Sum.isLeft_iff.mp (hn b hb)
    simp only [unSum, Sum.elim_inl, id] at h
    rw [h]
  refine ⟨GPath.ofWalkOpt (pushWalk unSum p hf) (pushWalk_isPath unSum p hf hp hinj), ?_⟩
  rw [optEdges_ofWalkOpt, pushWalk_edges]
  exact hperm.map _

theorem filter_bothInl_of_avoid {x y : V ⊕ V} (p : (leafGraph B A).Walk x y)
    (hn : ∀ v ∈ p.support, v.isLeft = true) : p.edges.filter bothInl = p.edges := by
  rw [List.filter_eq_self]
  intro e he
  induction e using Sym2.inductionOn with
  | hf a b =>
  simp only [bothInl_mk, Bool.and_eq_true]
  exact ⟨hn a (p.fst_mem_support_of_mem_edges he), hn b (p.snd_mem_support_of_mem_edges he)⟩

/-- Stripping a leaf at the end of a path starting in `inl`. -/
theorem leaf_strip_tgt {a : V} {y : V ⊕ V} (q : (leafGraph B A).Walk (.inl a) y) (hq : q.IsPath)
    (hinr : ∀ v ∈ q.support, v.isLeft = false → v = y) :
    ∃ o : Option (GPath B), (optEdges o).Perm ((q.edges.filter bothInl).map (Sym2.map unSum)) := by
  cases hy : y.isLeft with
  | true =>
    have hn : ∀ v ∈ q.support, v.isLeft = true := by
      intro v hv
      by_contra h
      rw [Bool.not_eq_true] at h
      have := hinr v hv h
      subst this
      rw [hy] at h; exact absurd h (by decide)
    exact leaf_piece_of_walk q hq hn (by rw [filter_bothInl_of_avoid q hn])
  | false =>
    obtain ⟨b, rfl⟩ : ∃ b, y = .inr b := by
      cases y with
      | inl b => simp at hy
      | inr b => exact ⟨b, rfl⟩
    have hpos : 0 < q.reverse.length := by
      rw [Walk.length_reverse]
      by_contra h0
      have := Walk.eq_of_length_eq_zero (p := q) (by omega)
      exact Sum.inl_ne_inr this
    obtain ⟨c, h, q', hq'⟩ := Walk.exists_eq_cons_of_length_pos q.reverse hpos
    have hrev : q.reverse.IsPath := hq.reverse
    rw [hq', Walk.cons_isPath_iff] at hrev
    have hsub : ∀ v ∈ q'.support, v ∈ q.support := by
      intro v hv
      rw [← List.mem_reverse, ← Walk.support_reverse, hq', Walk.support_cons]
      exact List.mem_cons_of_mem _ hv
    have hn : ∀ v ∈ q'.support, v.isLeft = true := by
      intro v hv
      by_contra hc
      rw [Bool.not_eq_true] at hc
      have := hinr v (hsub v hv) hc
      subst this
      exact hrev.2 hv
    refine leaf_piece_of_walk q' hrev.1 hn ?_
    have he : q.edges = (s(.inr b, c) :: q'.edges).reverse := by
      have h1 : q.reverse.edges = s(.inr b, c) :: q'.edges := by rw [hq', Walk.edges_cons]
      rw [← h1, Walk.edges_reverse, List.reverse_reverse]
    have hc : bothInl s(.inr b, c) = false := by simp
    rw [he, List.filter_reverse, List.filter_cons, hc, filter_bothInl_of_avoid q' hn]
    exact (List.reverse_perm _).symm

/-- A path starting at a leaf: the leaf edge followed by a path from its support. -/
theorem leaf_start {Q : GPath (leafGraph B A)} {a : V} (hQ : Q.src = .inr a) :
    ∃ (q : (leafGraph B A).Walk (.inl a) Q.tgt), q.IsPath ∧ .inr a ∉ q.support ∧
      Q.edges = s(.inr a, .inl a) :: q.edges ∧
      (∀ v ∈ q.support, v ∈ Q.walk.support) := by
  obtain ⟨s, t, w, hw, hpos⟩ := Q
  simp only at hQ
  subst hQ
  obtain ⟨c, h, q, rfl⟩ := Walk.exists_eq_cons_of_length_pos w hpos
  have hw' := (Walk.cons_isPath_iff h q).mp hw
  cases c with
  | inr c => exact absurd h leafGraph_not_adj_inr_inr
  | inl c =>
  have hca : a = c := (show a = c ∧ a ∈ A from h).1
  subst hca
  exact ⟨q, hw'.1, hw'.2, rfl, fun v hv => by
    simp only [Walk.support_cons]; exact List.mem_cons_of_mem _ hv⟩

/-- **Every path has a piece** in `B` after deleting its leaf edges. -/
theorem leaf_hasPiece (P : GPath (leafGraph B A)) : HasPiece B unSum bothInl P := by
  have key : ∀ Q : GPath (leafGraph B A), ∀ a, Q.src = .inr a → HasPiece B unSum bothInl Q := by
    intro Q a hQ
    obtain ⟨q, hq, hna, hQe, hsub⟩ := leaf_start hQ
    obtain ⟨o, ho⟩ := leaf_strip_tgt q hq (by
      intro v hv hv'
      obtain ⟨b, rfl⟩ : ∃ b, v = .inr b := by
        cases v with
        | inl b => simp at hv'
        | inr b => exact ⟨b, rfl⟩
      rcases leaf_inr_end Q (hsub _ hv) with h | h
      · rw [hQ] at h; cases h; exact absurd hv hna
      · exact h.symm)
    refine ⟨o, ?_⟩
    rw [hQe, List.filter_cons]
    simpa using ho
  cases hs : P.src with
  | inr a => exact key P a hs
  | inl a =>
    cases ht : P.tgt with
    | inr b => exact HasPiece.of_reverse (key P.reverse b ht)
    | inl b =>
      have hn : ∀ v ∈ P.walk.support, v.isLeft = true := by
        intro v hv
        cases v with
        | inl v => rfl
        | inr v =>
          rcases leaf_inr_end P hv with h | h
          · rw [hs] at h; cases h
          · rw [ht] at h; cases h
      obtain ⟨o, ho⟩ := leaf_piece_of_walk P.walk P.isPath hn (l := P.edges)
        (by rw [GPath.edges, filter_bothInl_of_avoid P.walk hn])
      exact ⟨o, ho⟩

/-- On a path through the leaf edge at `a` with some other edge, exactly one of the remaining
edges meets `a`. -/
theorem leaf_count (P : GPath (leafGraph B A)) {a : V} (hl : s(.inl a, .inr a) ∈ P.edges)
    (hS : P.edges.any bothInl = true) :
    ((P.edges.filter bothInl).map (Sym2.map unSum)).countP (fun e => decide (a ∈ e)) = 1 := by
  have key : ∀ Q : GPath (leafGraph B A), Q.src = .inr a → Q.edges.any bothInl = true →
      ((Q.edges.filter bothInl).map (Sym2.map unSum)).countP (fun e => decide (a ∈ e)) = 1 := by
    intro Q hQ hS
    obtain ⟨q, hq, hna, hQe, -⟩ := leaf_start hQ
    rw [hQe] at hS ⊢
    rw [List.filter_cons]
    simp only [bothInl_mk, Sum.isLeft_inr, Bool.false_and, Bool.false_eq_true, ite_false]
    have hqne : q.edges ≠ [] := by
      intro h0; rw [h0] at hS; simp at hS
    have hqpos : 0 < q.length := by
      rw [← Walk.length_edges]; exact List.length_pos_iff.mpr hqne
    have hne : (Sum.inl a : V ⊕ V) ≠ Q.tgt := GPath.src_ne_tgt ⟨_, _, q, hq, hqpos⟩
    have hcount := Walk.countP_add_ends q hq (.inl a)
    simp only [q.start_mem_support, ite_true, Ne.symm hne, ite_false] at hcount
    rw [List.countP_map, List.countP_filter]
    rw [List.countP_congr (q := fun e => decide (Sum.inl a ∈ e))]
    · omega
    · intro e he
      have heG := q.edges_subset_edgeSet he
      induction e using Sym2.inductionOn with
      | hf x y =>
      cases x with
      | inl x =>
        cases y with
        | inl y => simp [unSum, Sym2.mem_iff]
        | inr y =>
          have hxy : x = y := (show (leafGraph B A).Adj (.inl x) (.inr y) from heG).1
          subst hxy
          have hxa : a ≠ x := by
            rintro rfl
            exact hna (q.snd_mem_support_of_mem_edges he)
          simp [Sym2.mem_iff, hxa]
      | inr x =>
        cases y with
        | inl y =>
          have hxy : x = y := (show (leafGraph B A).Adj (.inr x) (.inl y) from heG).1
          subst hxy
          have hxa : a ≠ x := by
            rintro rfl
            exact hna (q.fst_mem_support_of_mem_edges he)
          simp [Sym2.mem_iff, hxa]
        | inr y => exact (leafGraph_not_adj_inr_inr (B := B) (A := A) (u := x) (v := y) heG).elim
  have hn : (Sum.inr a : V ⊕ V) ∈ P.walk.support := P.walk.snd_mem_support_of_mem_edges hl
  rcases leaf_inr_end P hn with h | h
  · exact key P h hS
  · have := key P.reverse h (by simpa [GPath.reverse_edges, List.any_reverse] using hS)
    simpa [GPath.reverse_edges, List.filter_reverse] using this

/-- A path through a leaf edge with no other kind of edge is that leaf edge. -/
theorem leaf_only (P : GPath (leafGraph B A)) {a : V} (hl : s(.inl a, .inr a) ∈ P.edges)
    (hS : P.edges.any bothInl = false) : P.edges = [s(.inl a, .inr a)] := by
  have key : ∀ Q : GPath (leafGraph B A), Q.src = .inr a → Q.edges.any bothInl = false →
      Q.edges = [s(.inl a, .inr a)] := by
    intro Q hQ hS
    obtain ⟨q, hq, hna, hQe, -⟩ := leaf_start hQ
    rw [hQe] at hS ⊢
    by_cases hql : q.length = 0
    · have : q.edges = [] := List.eq_nil_of_length_eq_zero (by rw [Walk.length_edges]; exact hql)
      rw [this, Sym2.eq_swap]
    · exfalso
      obtain ⟨d, h', q'', hq''⟩ := Walk.exists_eq_cons_of_length_pos q (by omega)
      have hd : d.isLeft = true := by
        cases d with
        | inl _ => rfl
        | inr d =>
          have hda : a = d := (show a = d ∧ d ∈ A from h').1
          exfalso
          apply hna
          rw [hq'', Walk.support_cons, hda]
          exact List.mem_cons_of_mem _ q''.start_mem_support
      have : (s(Sum.inr a, Sum.inl a) :: q.edges).any bothInl = true := by
        rw [hq'', Walk.edges_cons]
        simp [hd]
      rw [this] at hS; cases hS
  have hn : (Sum.inr a : V ⊕ V) ∈ P.walk.support := P.walk.snd_mem_support_of_mem_edges hl
  rcases leaf_inr_end P hn with h | h
  · exact key P h hS
  · have := key P.reverse h (by simpa [GPath.reverse_edges, List.any_reverse] using hS)
    rw [GPath.reverse_edges] at this
    rw [← List.reverse_reverse P.edges, this]; rfl

/-- **Trimming the private leaves.** -/
theorem leafGraph_trim (D : PathDecomp (leafGraph B A)) :
    ∃ D' : PathDecomp B, D'.size + (A.filter (fun a => D'.ends a = 0)).card ≤ D.size := by
  classical
  obtain ⟨D', hsize, -, hends⟩ := D.project_full unSum bothInl (Set.range Sum.inl) unSum_injOn
    leaf_hT leaf_hcov (fun P _ => leaf_hasPiece P)
  refine ⟨D', ?_⟩
  have hex : ∀ a ∈ A, ∃ P ∈ D.paths, s(.inl a, .inr a) ∈ P.edges := by
    intro a ha
    have he : s(Sum.inl a, Sum.inr a) ∈ (leafGraph B A).edgeSet := by
      rw [mem_edgeSet]; exact ⟨rfl, ha⟩
    exact List.mem_flatMap.mp ((D.covers _).1 he)
  have hZ : ∀ a ∈ A, D'.ends a = 0 → ∀ P ∈ D.paths, s(.inl a, .inr a) ∈ P.edges →
      P.edges.any bothInl = false := by
    intro a _ h0 P hP hPe
    by_contra hc
    rw [Bool.not_eq_false] at hc
    have h1 := leaf_count P hPe hc
    have hle := List.le_sum_of_mem (List.mem_map_of_mem (f := fun P =>
      if ((P.edges.filter bothInl).map (Sym2.map unSum)).countP (fun e => decide (a ∈ e)) = 1
      then 1 else 0) hP)
    rw [← hends a, h1] at hle
    simp at hle
    omega
  set N := D.paths.filter (fun P => !(P.edges.any bothInl)) with hN
  have hsub : A.filter (fun a => D'.ends a = 0) ⊆ N.toFinset.image (fun P => unSum P.src) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨P, hP, hPe⟩ := hex a ha.1
    have hno := hZ a ha.1 ha.2 P hP hPe
    have h1 := leaf_only P hPe hno
    rw [Finset.mem_image]
    refine ⟨P, by rw [List.mem_toFinset, hN, List.mem_filter]; exact ⟨hP, by simp [hno]⟩, ?_⟩
    obtain ⟨e, he, hse⟩ := P.exists_mem_edge_of_support P.walk.start_mem_support
    rw [h1, List.mem_singleton] at he
    subst he
    rcases Sym2.mem_iff.mp hse with h | h <;> rw [h] <;> rfl
  have hcard : (A.filter (fun a => D'.ends a = 0)).card ≤ N.toFinset.card :=
    (Finset.card_le_card hsub).trans Finset.card_image_le
  have hN' : N.toFinset.card ≤ D.paths.countP (fun P => !(P.edges.any bothInl)) := by
    rw [List.countP_eq_length_filter]; exact List.toFinset_card_le _
  have hlen := List.length_eq_countP_add_countP (fun P : GPath (leafGraph B A) =>
    P.edges.any bothInl) (l := D.paths)
  have hneg : D.paths.countP (fun P => !(P.edges.any bothInl)) =
      D.paths.countP (fun P => ¬ (P.edges.any bothInl) = true) := by
    apply List.countP_congr; intro P _; simp
  have hDs : D.size = D.paths.length := rfl
  omega

end Gallai
