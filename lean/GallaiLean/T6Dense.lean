import GallaiLean.TerminalMatching3
import GallaiLean.TightFan

/-!
# The dense residual of T(6)-i: the append chain (session `claude/t6-dense`)

Manuscript: `manuscripts/t6-dense/t6-dense.tex`.

Let `z` be the only even vertex of `J`, `N(z) = {x₁, y₁, x₂, y₂, x₃, y₃}`, and suppose
`x₁y₂, x₂y₃ ∈ E(J)` (in the dense residual of T(6)-i, where `B[N(z)] = K₆ − D` with
`D ∈ {∅, K₂, P₃, K₃, C₄}`, such a labelling exists with any prescribed `yᵢ`). The chained walk of
terminal-matching §8 then has two walks of length one, `P₂ = y₃x₂` and `P₁ = y₂x₁`. Every step is
explicit, and the base hypothesis becomes a list of *end-path* conditions on one Lovász
decomposition of the base graph
`M = J − {zx₁, zx₂, zx₃, zy₂, zy₃, x₁y₂, x₂y₃}`
(`z` hangs at `y₁` and plays the leaf `ℓ₁`; `x₃` is the only even vertex).

The construction runs in the split graph on `V ⊕ Fin 2` (`splitG`): `J − z`'s edges, `z` as a
leaf at `y₁`, and new leaves `ℓ₂ = inr 0` at `y₂`, `ℓ₃ = inr 1` at `y₃`. All intermediate graphs
are the split graph minus a list of edges (`delList`):
1. append `y₃ → ℓ₃` (leaf at `y₃`);
2. append `x₂ → y₃` (the first walk);
3. append `y₂ → ℓ₂` (leaf at `y₂`);
4. the second walk `x₁ → y₂`: an append (`stl_of_appendBase`), or a protected Fan step with
   protected set `{x₂, x₃}` (`stl_of_protectedBase`, from `walk_step_protected`);
5. push the leaves onto `z` (`PathDecomp.pushOn`) and append `z → x₁, x₂, x₃`.
The result is a star-terminal Lovász decomposition of `J` with transitions `xᵢ z ·`, hence
`STL J z yᵢ` for `i = 1, 2, 3`.

## Main results

* `delList`, `delList_edgeSet`, `delList_cons`: a graph minus a list of edges.
* `append_full`: the append move with the new path's support made explicit.
* `fanPred_append`, `fanPred_self`: predecessors through an append.
* `splitG`: the split graph.
* **`stl_of_appendBase`**: the base conditions (E1)–(E5), (E7) give STL at `y₁, y₂, y₃`.
* **`stl_of_protectedBase`**: the base conditions (E1)–(E6) give STL at `y₁, y₂, y₃`.
-/

open SimpleGraph

namespace Gallai

universe u

/-! ### A graph minus a list of edges -/

section delList

variable {U : Type*} (K : SimpleGraph U)

/-- `K` minus the edges of the list `L`. -/
def delList (L : List (Sym2 U)) : SimpleGraph U where
  Adj a b := K.Adj a b ∧ s(a, b) ∉ L
  symm := ⟨fun a b h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun a h => K.loopless.irrefl a h.1⟩

instance delList.decRel [DecidableEq U] [DecidableRel K.Adj] (L : List (Sym2 U)) :
    DecidableRel (delList K L).Adj := fun a b =>
  inferInstanceAs (Decidable (K.Adj a b ∧ s(a, b) ∉ L))

theorem delList_adj {L : List (Sym2 U)} {a b : U} :
    (delList K L).Adj a b ↔ K.Adj a b ∧ s(a, b) ∉ L := Iff.rfl

theorem delList_edgeSet (L : List (Sym2 U)) :
    ∀ e, e ∈ (delList K L).edgeSet ↔ e ∈ K.edgeSet ∧ e ∉ L := by
  intro e
  induction e using Sym2.inductionOn with
  | hf a b => exact Iff.rfl

/-- Restoring the head of the list adds one edge. -/
theorem delList_cons {a : Sym2 U} {L : List (Sym2 U)} (ha : a ∈ K.edgeSet) (haL : a ∉ L) :
    ∀ e, e ∈ (delList K L).edgeSet ↔ e ∈ (delList K (a :: L)).edgeSet ∨ e = a := by
  intro e
  rw [delList_edgeSet, delList_edgeSet, List.mem_cons]
  constructor
  · rintro ⟨he, heL⟩
    by_cases h : e = a
    · exact Or.inr h
    · exact Or.inl ⟨he, by tauto⟩
  · rintro (⟨he, h⟩ | rfl)
    · exact ⟨he, fun h' => h (Or.inr h')⟩
    · exact ⟨ha, haL⟩

/-- Restoring the last edge gives `K`. -/
theorem delList_single {a : Sym2 U} (ha : a ∈ K.edgeSet) :
    ∀ e, e ∈ K.edgeSet ↔ e ∈ (delList K [a]).edgeSet ∨ e = a := by
  intro e
  have := delList_cons K ha (List.not_mem_nil (a := a)) e
  rw [delList_edgeSet] at this
  simpa using this

theorem delList_not_adj {t u : U} (L : List (Sym2 U)) : ¬ (delList K (s(t, u) :: L)).Adj t u :=
  fun h => h.2 List.mem_cons_self

end delList

/-! ### The append move with explicit supports, and predecessors through it -/

section append

variable {U : Type*} [DecidableEq U] {K K' : SimpleGraph U}

/-- **Append move, explicit.** A path `P` with an end at `t` avoiding `u` absorbs the new edge
`tu`. The new path `P'` starts at `u`; read from `u` it is `u` followed by `P` read from `t`;
every other path keeps the ends and support of a path of `D`. -/
theorem append_full (D : PathDecomp K) {t u : U} (hadj : ¬ K.Adj t u)
    (hK' : ∀ e, e ∈ K'.edgeSet ↔ e ∈ K.edgeSet ∨ e = s(t, u))
    {P : GPath K} (hP : P ∈ D.paths) (hend : P.src = t ∨ P.tgt = t)
    (hu : u ∉ P.walk.support) :
    ∃ D' : PathDecomp K',
      (∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if u = w then 1 else 0)) ∧
      ∃ P' ∈ D'.paths, P'.src = u ∧
        ((P.src = t ∧ P'.tgt = P.tgt ∧ P'.walk.support = u :: P.walk.support) ∨
          (P.tgt = t ∧ P'.tgt = P.src ∧ P'.walk.support = u :: P.walk.support.reverse)) ∧
        (∀ Q' ∈ D'.paths, Q' = P' ∨ ∃ Q ∈ D.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
          Q'.walk.support = Q.walk.support) ∧
        (∀ Q ∈ D.paths, Q ≠ P → ∃ Q' ∈ D'.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
          Q'.walk.support = Q.walk.support) := by
  -- orient `P` so that it starts at `t`
  have key : ∀ Q : GPath K, Q.src = t → Q.edges.Perm P.edges → (∀ w, Q.endsAt w = P.endsAt w) →
      u ∉ Q.walk.support →
      ∃ D' : PathDecomp K',
        (∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if u = w then 1 else 0)) ∧
        ∃ P' ∈ D'.paths, P'.src = u ∧ P'.tgt = Q.tgt ∧ P'.walk.support = u :: Q.walk.support ∧
          (∀ Q' ∈ D'.paths, Q' = P' ∨ ∃ Q ∈ D.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
            Q'.walk.support = Q.walk.support) ∧
          (∀ Q ∈ D.paths, Q ≠ P → ∃ Q' ∈ D'.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
            Q'.walk.support = Q.walk.support) := by
    intro Q hQs hQe hQends huQ
    have hQK : ∀ e ∈ Q.walk.edges, e ∈ K'.edgeSet := fun e he =>
      (hK' e).2 (Or.inl (Q.walk.edges_subset_edgeSet he))
    have hs : s(u, Q.src) = s(t, u) := by rw [hQs, Sym2.eq_swap]
    have hut : K'.Adj u Q.src := by
      rw [← mem_edgeSet, hK', hs]; exact Or.inr rfl
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
    obtain ⟨D', -, hmem, hends, hkeep, hcovr⟩ := D.replace_supp hP P' (by
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
    refine ⟨D', fun w => ?_, P', hmem, rfl, rfl, ?_, hcovr, hkeep⟩
    · have h1 := hends w
      have h2 : P'.endsAt w = (if u = w then 1 else 0) + (if Q.tgt = w then 1 else 0) := rfl
      have h3 : P.endsAt w = (if t = w then 1 else 0) + (if Q.tgt = w then 1 else 0) := by
        rw [← hQends]; simp only [GPath.endsAt, hQs]
      omega
    · show (Walk.cons hut (Q.walk.transfer K' hQK)).support = _
      rw [Walk.support_cons, Walk.support_transfer]
  rcases hend with h | h
  · obtain ⟨D', h1, P', hP', h2, h3, h4, h5, h6⟩ :=
      key P h (List.Perm.refl _) (fun _ => rfl) hu
    exact ⟨D', h1, P', hP', h2, Or.inl ⟨h, h3, h4⟩, h5, h6⟩
  · have hu' : u ∉ P.reverse.walk.support := by
      simpa [GPath.reverse, Walk.support_reverse] using hu
    obtain ⟨D', h1, P', hP', h2, h3, h4, h5, h6⟩ :=
      key P.reverse h (by
        show P.walk.reverse.edges.Perm P.walk.edges
        rw [Walk.edges_reverse]; exact List.reverse_perm _) (fun w => P.reverse_endsAt w) hu'
    refine ⟨D', h1, P', hP', h2, Or.inr ⟨h, h3, ?_⟩, h5, h6⟩
    rw [h4]
    simp [GPath.reverse, Walk.support_reverse]

omit [DecidableEq U] in
/-- Read from its start, nothing precedes the start of a path. -/
theorem not_infix_pred_start {a b y : U} (p : K.Walk a b) (hp : p.IsPath) :
    ¬ [y, a] <:+: p.support := by
  intro hinf
  have hnd := hp.support_nodup
  rw [← p.cons_tail_support] at hnd hinf
  rcases List.infix_cons_iff.mp hinf with h | h
  · obtain ⟨rfl, h'⟩ := List.cons_prefix_cons.mp h
    exact (List.nodup_cons.mp hnd).1 (h'.subset (List.mem_singleton_self y))
  · exact (List.nodup_cons.mp hnd).1 (h.subset (by simp))

omit [DecidableEq U] in
/-- A vertex is never its own predecessor of itself: read from `w`, no vertex precedes `w`. -/
theorem fanPred_self (D : PathDecomp K) {w y : U} : ¬ FanPred D w w y := by
  rintro ⟨P, -, ⟨hs, hinf⟩ | ⟨ht, hinf⟩⟩
  · subst hs
    exact not_infix_pred_start P.walk P.isPath hinf
  · subst ht
    refine not_infix_pred_start (y := y) P.walk.reverse P.isPath.reverse ?_
    rw [Walk.support_reverse]; simpa using List.reverse_infix.mpr hinf

omit [DecidableEq U] in
/-- **Predecessors through an append.** If `D'` arises from `D` by appending `tu` at the end `t`
of `P` (as in `append_full`), then a predecessor `y ≠ u` of `w ≠ u` read in `D'` from `x` is a
predecessor in `D` read from `x`, or `x = u` and it is read in `D` from `t`. -/
theorem fanPred_append {D : PathDecomp K} {D' : PathDecomp K'} {t u : U} {P : GPath K}
    (hP : P ∈ D.paths) {P' : GPath K'}
    (hsupp : (P.src = t ∧ P'.tgt = P.tgt ∧ P'.walk.support = u :: P.walk.support) ∨
      (P.tgt = t ∧ P'.tgt = P.src ∧ P'.walk.support = u :: P.walk.support.reverse))
    (hP's : P'.src = u)
    (hrest : ∀ Q' ∈ D'.paths, Q' = P' ∨ ∃ Q ∈ D.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
      Q'.walk.support = Q.walk.support)
    {w x y : U} (hwu : w ≠ u) (hyu : y ≠ u) (h : FanPred D' w x y) :
    FanPred D w x y ∨ (x = u ∧ FanPred D w t y) := by
  obtain ⟨R, hR, hocc⟩ := h
  rcases hrest R hR with rfl | ⟨Q, hQ, hs, ht, hsu⟩
  · rcases hocc with ⟨hx, hinf⟩ | ⟨hx, hinf⟩
    · -- read from `u`
      rw [hP's] at hx
      subst hx
      right
      refine ⟨rfl, P, hP, ?_⟩
      rcases hsupp with ⟨hPs, -, hS⟩ | ⟨hPt, -, hS⟩
      · rw [hS] at hinf
        rcases List.infix_cons_iff.mp hinf with h | h
        · exact absurd (List.cons_prefix_cons.mp h).1 hyu
        · exact Or.inl ⟨hPs, h⟩
      · rw [hS] at hinf
        rcases List.infix_cons_iff.mp hinf with h | h
        · exact absurd (List.cons_prefix_cons.mp h).1 hyu
        · exact Or.inr ⟨hPt, by simpa using List.reverse_infix.mpr h⟩
    · -- read from the far end
      left
      refine ⟨P, hP, ?_⟩
      rcases hsupp with ⟨-, hPt, hS⟩ | ⟨-, hPs, hS⟩
      · rw [hS] at hinf
        rcases List.infix_cons_iff.mp hinf with h | h
        · exact absurd (List.cons_prefix_cons.mp h).1 hwu
        · exact Or.inr ⟨hPt ▸ hx, h⟩
      · rw [hS] at hinf
        rcases List.infix_cons_iff.mp hinf with h | h
        · exact absurd (List.cons_prefix_cons.mp h).1 hwu
        · exact Or.inl ⟨hPs ▸ hx, by simpa using List.reverse_infix.mpr h⟩
  · left
    refine ⟨Q, hQ, ?_⟩
    rcases hocc with ⟨hx, hinf⟩ | ⟨hx, hinf⟩
    · exact Or.inl ⟨hs ▸ hx, hsu ▸ hinf⟩
    · exact Or.inr ⟨ht ▸ hx, hsu ▸ hinf⟩

end append

/-! ### Tracking paths through appends -/

section track

variable {U : Type*} [DecidableEq U] {K K' : SimpleGraph U}

/-- `Q'` has the ends and support of `Q`. -/
def SameP (Q' : GPath K') (Q : GPath K) : Prop :=
  Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧ Q'.walk.support = Q.walk.support

/-- `Q'` is `Q` extended at its end `t` by the vertex `u` (it starts at `u`). -/
def ExtP (Q' : GPath K') (Q : GPath K) (t u : U) : Prop :=
  Q'.src = u ∧ ((Q.src = t ∧ Q'.tgt = Q.tgt ∧ Q'.walk.support = u :: Q.walk.support) ∨
    (Q.tgt = t ∧ Q'.tgt = Q.src ∧ Q'.walk.support = u :: Q.walk.support.reverse))

variable {K'' : SimpleGraph U}

omit [DecidableEq U] in
theorem SameP.mem {Q' : GPath K'} {Q : GPath K} (h : SameP Q' Q) {v : U} :
    v ∈ Q'.walk.support ↔ v ∈ Q.walk.support := by rw [h.2.2]

omit [DecidableEq U] in
theorem SameP.ends {Q' : GPath K'} {Q : GPath K} (h : SameP Q' Q) {v : U} :
    (Q'.src = v ∨ Q'.tgt = v) ↔ (Q.src = v ∨ Q.tgt = v) := by rw [h.1, h.2.1]

omit [DecidableEq U] in
theorem SameP.trans {Q'' : GPath K''} {Q' : GPath K'} {Q : GPath K} (h : SameP Q'' Q')
    (h' : SameP Q' Q) : SameP Q'' Q :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.trans h'.2.2⟩

omit [DecidableEq U] in
theorem SameP.ext {Q'' : GPath K''} {Q' : GPath K'} {Q : GPath K} {t u : U} (h : SameP Q'' Q')
    (h' : ExtP Q' Q t u) : ExtP Q'' Q t u := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.trans h'.1, ?_⟩
  rcases h'.2 with ⟨a, b, c⟩ | ⟨a, b, c⟩
  · exact Or.inl ⟨a, h2.trans b, h3.trans c⟩
  · exact Or.inr ⟨a, h2.trans b, h3.trans c⟩

omit [DecidableEq U] in
theorem ExtP.of_same {Q'' : GPath K''} {Q' : GPath K'} {Q : GPath K} {t u : U}
    (h : ExtP Q'' Q' t u) (h' : SameP Q' Q) : ExtP Q'' Q t u := by
  obtain ⟨h1, h2, h3⟩ := h'
  refine ⟨h.1, ?_⟩
  rcases h.2 with ⟨a, b, c⟩ | ⟨a, b, c⟩
  · exact Or.inl ⟨h1 ▸ a, b.trans h2, by rw [c, h3]⟩
  · exact Or.inr ⟨h2 ▸ a, b.trans h1, by rw [c, h3]⟩

omit [DecidableEq U] in
theorem ExtP.mem {Q' : GPath K'} {Q : GPath K} {t u : U} (h : ExtP Q' Q t u) {v : U} :
    v ∈ Q'.walk.support ↔ v = u ∨ v ∈ Q.walk.support := by
  rcases h.2 with ⟨-, -, h3⟩ | ⟨-, -, h3⟩ <;> rw [h3] <;> simp

omit [DecidableEq U] in
/-- `Q` has an end at `t`. -/
theorem ExtP.end_t {Q' : GPath K'} {Q : GPath K} {t u : U} (h : ExtP Q' Q t u) :
    Q.src = t ∨ Q.tgt = t := by
  rcases h.2 with ⟨a, -, -⟩ | ⟨a, -, -⟩
  · exact Or.inl a
  · exact Or.inr a

omit [DecidableEq U] in
/-- An end of `Q'` other than `u` is an end of `Q` other than `t`. -/
theorem ExtP.ends {Q' : GPath K'} {Q : GPath K} {t u : U} (h : ExtP Q' Q t u) {v : U}
    (hv : Q'.src = v ∨ Q'.tgt = v) (hvu : v ≠ u) :
    (Q.src = v ∨ Q.tgt = v) ∧ v ≠ t := by
  have hst : ∀ R : GPath K, R.src ≠ R.tgt := fun R => R.src_ne_tgt
  rcases hv with hv | hv
  · exact absurd (hv.symm.trans h.1) hvu
  · rcases h.2 with ⟨a, b, -⟩ | ⟨a, b, -⟩
    · refine ⟨Or.inr (b.symm.trans hv), ?_⟩
      rintro rfl; exact hst Q (a.trans (b.symm.trans hv).symm)
    · refine ⟨Or.inl (b.symm.trans hv), ?_⟩
      rintro rfl; exact hst Q ((b.symm.trans hv).trans a.symm)

omit [DecidableEq U] in
/-- The support of a path determines its edges. -/
theorem GPath.edges_eq_of_support {Q' : GPath K'} {Q : GPath K}
    (h : Q'.walk.support = Q.walk.support) : Q'.edges = Q.edges := by
  unfold GPath.edges
  rw [Walk.edges_eq_zipWith_support, Walk.edges_eq_zipWith_support, h]

omit [DecidableEq U] in
theorem SameP.edges {Q' : GPath K'} {Q : GPath K} (h : SameP Q' Q) : Q'.edges = Q.edges :=
  GPath.edges_eq_of_support h.2.2

omit [DecidableEq U] in
theorem zipWith_cons_support {a b c : U} (p : K.Walk a b) :
    List.zipWith (s(·, ·)) (c :: p.support) (c :: p.support).tail = s(c, a) :: p.edges := by
  rw [List.tail_cons, Walk.edges_eq_zipWith_support]
  conv_lhs => rw [← p.cons_tail_support]
  rw [List.zipWith_cons_cons, p.cons_tail_support]

omit [DecidableEq U] in
/-- The edges of an extended path: the new edge and the old ones. -/
theorem ExtP.edges_mem {Q' : GPath K'} {Q : GPath K} {t u : U} (h : ExtP Q' Q t u) (e : Sym2 U) :
    e ∈ Q'.edges ↔ e = s(u, t) ∨ e ∈ Q.edges := by
  unfold GPath.edges
  rw [Walk.edges_eq_zipWith_support]
  have hst : ∀ a : U, a = t → s(u, a) = s(u, t) := fun a h => by rw [h]
  rcases h.2 with ⟨a, -, c⟩ | ⟨a, -, c⟩
  · rw [c, zipWith_cons_support, List.mem_cons, hst _ a]
  · have : u :: Q.walk.support.reverse = u :: Q.walk.reverse.support := by
      rw [Walk.support_reverse]
    rw [c, this, zipWith_cons_support, List.mem_cons, Walk.edges_reverse, List.mem_reverse,
      hst _ a]

omit [DecidableEq U] in
/-- `FanPred` read through a path with the same ends and support. -/
theorem fanPred_of_same {D : PathDecomp K} {Q : GPath K} (hQ : Q ∈ D.paths) {Q' : GPath K'}
    (h : SameP Q' Q) {w x y : U}
    (hocc : (Q'.src = x ∧ [y, w] <:+: Q'.walk.support) ∨ (Q'.tgt = x ∧ [w, y] <:+: Q'.walk.support)) :
    FanPred D w x y := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [h3] at hocc
  rw [h1, h2] at hocc
  exact ⟨Q, hQ, hocc⟩

/-- A predecessor read from `x` gives `x` an end. -/
theorem ends_pos_of_fanPred (D : PathDecomp K) {w x y : U} (h : FanPred D w x y) :
    1 ≤ D.ends x := by
  obtain ⟨P, hP, hocc⟩ := h
  have h1 : 1 ≤ P.endsAt x := by
    unfold GPath.endsAt
    rcases hocc with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun P : GPath K => P.endsAt x) hP)
  unfold PathDecomp.ends
  omega

end track

/-! ### The split graph -/

section split

variable {V : Type u}

/-- Adjacency of the split graph. -/
def splitAdj (J : SimpleGraph V) (z x₂ y₂ x₃ y₃ : V) : V ⊕ Fin 2 → V ⊕ Fin 2 → Prop
  | .inl a, .inl b => J.Adj a b ∧ s(a, b) ∉ [s(z, x₂), s(z, y₂), s(z, x₃), s(z, y₃)]
  | .inl a, .inr i => if i = 0 then a = x₂ ∨ a = y₂ else a = x₃ ∨ a = y₃
  | .inr i, .inl b => if i = 0 then b = x₂ ∨ b = y₂ else b = x₃ ∨ b = y₃
  | .inr _, .inr _ => False

/-- **The split graph** `J♯` on `V ⊕ Fin 2`. When `N(z) = {x₁, y₁, x₂, y₂, x₃, y₃}`, the vertex `z`
is split into three vertices of degree two: `z ∼ x₁, y₁`, `ℓ₂ = inr 0 ∼ x₂, y₂` and
`ℓ₃ = inr 1 ∼ x₃, y₃`. -/
def splitG (J : SimpleGraph V) (z x₂ y₂ x₃ y₃ : V) : SimpleGraph (V ⊕ Fin 2) where
  Adj := splitAdj J z x₂ y₂ x₃ y₃
  symm := ⟨fun a b h => by
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have h' : J.Adj a b ∧ s(a, b) ∉ [s(z, x₂), s(z, y₂), s(z, x₃), s(z, y₃)] := h
        show J.Adj b a ∧ s(b, a) ∉ [s(z, x₂), s(z, y₂), s(z, x₃), s(z, y₃)]
        exact ⟨h'.1.symm, by rw [show s(b, a) = s(a, b) from Sym2.eq_swap]; exact h'.2⟩
      | inr i => exact h
    | inr i =>
      cases b with
      | inl b => exact h
      | inr j => exact h⟩
  loopless := ⟨fun a h => by
    cases a with
    | inl a => exact J.loopless.irrefl a h.1
    | inr i => exact h⟩

instance splitG.decRel [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]
    (z x₂ y₂ x₃ y₃ : V) : DecidableRel (splitG J z x₂ y₂ x₃ y₃).Adj
  | .inl a, .inl b => inferInstanceAs
      (Decidable (J.Adj a b ∧ s(a, b) ∉ [s(z, x₂), s(z, y₂), s(z, x₃), s(z, y₃)]))
  | .inl a, .inr i => inferInstanceAs
      (Decidable (if i = 0 then a = x₂ ∨ a = y₂ else a = x₃ ∨ a = y₃))
  | .inr i, .inl b => inferInstanceAs
      (Decidable (if i = 0 then b = x₂ ∨ b = y₂ else b = x₃ ∨ b = y₃))
  | .inr _, .inr _ => inferInstanceAs (Decidable False)

variable (J : SimpleGraph V) (z x₂ y₂ x₃ y₃ : V)

theorem splitG_ll {a b : V} : (splitG J z x₂ y₂ x₃ y₃).Adj (.inl a) (.inl b) ↔
    J.Adj a b ∧ s(a, b) ∉ [s(z, x₂), s(z, y₂), s(z, x₃), s(z, y₃)] := Iff.rfl

theorem splitG_l0 {a : V} : (splitG J z x₂ y₂ x₃ y₃).Adj (.inl a) (.inr 0) ↔ a = x₂ ∨ a = y₂ :=
  Iff.rfl

theorem splitG_l1 {a : V} : (splitG J z x₂ y₂ x₃ y₃).Adj (.inl a) (.inr 1) ↔ a = x₃ ∨ a = y₃ :=
  Iff.rfl

theorem splitG_rr {i j : Fin 2} : ¬ (splitG J z x₂ y₂ x₃ y₃).Adj (.inr i) (.inr j) := id

end split

/-! ### Steps 1–3: three appends -/

section main

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem nodup7 {a b c d e f g : V} (h : [a, b, c, d, e, f, g].Nodup) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ f ∧ a ≠ g ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧ b ≠ g ∧
      c ≠ d ∧ c ≠ e ∧ c ≠ f ∧ c ≠ g ∧ d ≠ e ∧ d ≠ f ∧ d ≠ g ∧ e ≠ f ∧ e ≠ g ∧ f ≠ g := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at h
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, ⟨h7, h8, h9, h10, h11⟩, ⟨h12, h13, h14, h15⟩, ⟨h16, h17, h18⟩,
    ⟨h19, h20⟩, h21⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21⟩

/-- `J♯` minus the list `L` and minus the three edges from the split vertices to `x₁, x₂, x₃`. -/
abbrev spl (J : SimpleGraph V) (z x₁ x₂ y₂ x₃ y₃ : V) (L : List (Sym2 (V ⊕ Fin 2))) :
    SimpleGraph (V ⊕ Fin 2) :=
  delList (splitG J z x₂ y₂ x₃ y₃)
    (L ++ [s(Sum.inl z, Sum.inl x₁), s(Sum.inr 0, Sum.inl x₂), s(Sum.inr 1, Sum.inl x₃)])

/-- The base graph in the split form: `M = J − {zx₁, zx₂, zx₃, zy₂, zy₃, x₁y₂, x₂y₃}` on the
`inl` side, and the two leaves `inr 0`, `inr 1` isolated. -/
abbrev splBase (J : SimpleGraph V) (z x₁ x₂ y₂ x₃ y₃ : V) : SimpleGraph (V ⊕ Fin 2) :=
  spl J z x₁ x₂ y₂ x₃ y₃ [s(Sum.inl y₃, Sum.inr 1), s(Sum.inl x₂, Sum.inl y₃),
    s(Sum.inl y₂, Sum.inr 0), s(Sum.inl x₁, Sum.inl y₂)]

omit [Fintype V] in
theorem sym2_inl_ne_inr {a b : V} {i : Fin 2} {c : V ⊕ Fin 2} :
    s(Sum.inl a, Sum.inl b) ≠ s(Sum.inr i, c) := by
  intro h
  rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact Sum.inl_ne_inr h1
  · exact Sum.inl_ne_inr h2

omit [Fintype V] in
theorem sym2_inl_inr_ne {a b : V} {i j : Fin 2} (h : a ≠ b ∨ i ≠ j) :
    s(Sum.inl a, Sum.inr i) ≠ (s(Sum.inl b, Sum.inr j) : Sym2 (V ⊕ Fin 2)) := by
  intro he
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, -⟩
  · rcases h with h | h
    · exact h (Sum.inl_injective h1)
    · exact h (Sum.inr_injective h2)
  · exact Sum.inl_ne_inr h1

omit [Fintype V] in
theorem sym2_inl_ne {a b c d : V} (h : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    s(Sum.inl a, Sum.inl b) ≠ (s(Sum.inl c, Sum.inl d) : Sym2 (V ⊕ Fin 2)) := by
  intro he
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h (Or.inl ⟨Sum.inl_injective h1, Sum.inl_injective h2⟩)
  · exact h (Or.inr ⟨Sum.inl_injective h1, Sum.inl_injective h2⟩)

omit [Fintype V] in
/-- Two different ends of a path are its two ends. -/
theorem ends_pair {W : Type*} {K : SimpleGraph W} (P : GPath K) {a b : W} (hab : a ≠ b)
    (ha : P.src = a ∨ P.tgt = a) (hb : P.src = b ∨ P.tgt = b) :
    (P.src = a ∧ P.tgt = b) ∨ (P.src = b ∧ P.tgt = a) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact absurd (ha.symm.trans hb) hab
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨hb, ha⟩
  · exact absurd (ha.symm.trans hb) hab

/-- An isolated vertex has no end. -/
theorem ends_eq_zero_of_isolated {W : Type*} [DecidableEq W] {K : SimpleGraph W}
    (D : PathDecomp K) {v : W} (hv : ∀ w, ¬ K.Adj v w) : D.ends v = 0 := by
  by_contra h
  obtain ⟨P, -, hP⟩ := D.exists_end_of_pos (Nat.pos_of_ne_zero h)
  exact P.not_mem_of_isolated hv (mem_support_of_end hP)

/-- **Steps 1–3**: append `y₃ → ℓ₃` (a leaf at `y₃`), `x₂ → y₃` (the first walk) and
`y₂ → ℓ₂` (a leaf at `y₂`). Every path of the result is a path of the base decomposition, or one
of them extended once; predecessors of `y₂` are read back in the base decomposition. -/
theorem split_abc (J : SimpleGraph V) [DecidableRel J.Adj] {z x₁ y₁ x₂ y₂ x₃ y₃ : V}
    (hne : [z, x₁, y₁, x₂, y₂, x₃, y₃].Nodup) (h₂₃ : J.Adj x₂ y₃)
    (D₀ : PathDecomp (splBase J z x₁ x₂ y₂ x₃ y₃))
    (hD₀ : ∀ v, D₀.ends (Sum.inl v) = if v = x₃ then 0 else 1)
    (E1 : ∀ P ∈ D₀.paths, Sum.inl z ∈ P.walk.support →
      P.src ≠ Sum.inl y₂ ∧ P.tgt ≠ Sum.inl y₂ ∧ P.src ≠ Sum.inl y₃ ∧ P.tgt ≠ Sum.inl y₃)
    (E2 : ∀ P ∈ D₀.paths, (P.src = Sum.inl y₂ ∨ P.tgt = Sum.inl y₂) →
      Sum.inl x₂ ∉ P.walk.support)
    (E4 : ∀ P ∈ D₀.paths, ¬ ((P.src = Sum.inl y₂ ∧ P.tgt = Sum.inl y₃) ∨
      (P.src = Sum.inl y₃ ∧ P.tgt = Sum.inl y₂)))
    (E5 : ∀ P ∈ D₀.paths, (P.src = Sum.inl x₂ ∨ P.tgt = Sum.inl x₂) →
      Sum.inl y₃ ∉ P.walk.support) :
    ∃ D₃ : PathDecomp (spl J z x₁ x₂ y₂ x₃ y₃ [s(Sum.inl x₁, Sum.inl y₂)]),
      (∀ v, D₃.ends (Sum.inl v) = if v = x₃ ∨ v = x₂ ∨ v = y₂ then 0 else 1) ∧
      D₃.ends (Sum.inr 0) = 1 ∧ D₃.ends (Sum.inr 1) = 1 ∧
      (∀ R ∈ D₃.paths, ∃ Q ∈ D₀.paths, SameP R Q ∨ ExtP R Q (Sum.inl y₃) (Sum.inr 1) ∨
        ExtP R Q (Sum.inl x₂) (Sum.inl y₃) ∨ ExtP R Q (Sum.inl y₂) (Sum.inr 0)) ∧
      (∀ x p, p ≠ Sum.inr 0 → p ≠ Sum.inl y₃ → p ≠ Sum.inr 1 → FanPred D₃ (Sum.inl y₂) x p →
        FanPred D₀ (Sum.inl y₂) x p ∨ (x = Sum.inr 1 ∧ FanPred D₀ (Sum.inl y₂) (Sum.inl y₃) p) ∨
        (x = Sum.inl y₃ ∧ FanPred D₀ (Sum.inl y₂) (Sum.inl x₂) p)) := by
  obtain ⟨hzx₁, hzy₁, hzx₂, hzy₂, hzx₃, hzy₃, hx₁y₁, hx₁x₂, hx₁y₂, hx₁x₃, hx₁y₃, hy₁x₂, hy₁y₂,
    hy₁x₃, hy₁y₃, hx₂y₂, hx₂x₃, hx₂y₃, hy₂x₃, hy₂y₃, hx₃y₃⟩ := nodup7 hne
  have hr01 : (Sum.inr 0 : V ⊕ Fin 2) ≠ Sum.inr 1 := by simp
  -- the leaves are isolated in the base graph
  have iso0 : ∀ (i : Fin 2) w, ¬ (splBase J z x₁ x₂ y₂ x₃ y₃).Adj (Sum.inr i) w := by
    intro i w h
    obtain ⟨h1, h2⟩ := h
    cases w with
    | inr j => exact h1
    | inl b =>
      fin_cases i
      · rcases (show b = x₂ ∨ b = y₂ from h1) with rfl | rfl
        · exact h2 (by simp)
        · exact h2 (by simp [Sym2.eq_swap])
      · rcases (show b = x₃ ∨ b = y₃ from h1) with rfl | rfl
        · exact h2 (by simp)
        · exact h2 (by simp [Sym2.eq_swap])
  have hD₀r : ∀ i, D₀.ends (Sum.inr i) = 0 := fun i => ends_eq_zero_of_isolated D₀ (iso0 i)
  -- Step 1: a leaf at `y₃`
  have eA : s(Sum.inl y₃, Sum.inr 1) ∈ (splitG J z x₂ y₂ x₃ y₃).edgeSet :=
    (splitG_l1 J z x₂ y₂ x₃ y₃).2 (Or.inr rfl)
  have nA : s(Sum.inl y₃, Sum.inr 1) ∉ [s(Sum.inl x₂, Sum.inl y₃), s(Sum.inl y₂, Sum.inr 0),
      s(Sum.inl x₁, Sum.inl y₂)] ++
      [s(Sum.inl z, Sum.inl x₁), s(Sum.inr 0, Sum.inl x₂), s(Sum.inr (1 : Fin 2), Sum.inl x₃)] := by
    simp [Sym2.eq_iff, hy₂y₃.symm, hx₃y₃.symm]
  have hK₁ := delList_cons (splitG J z x₂ y₂ x₃ y₃) eA nA
  obtain ⟨PA, hPA, hPAe⟩ := D₀.exists_end_of_pos (show 0 < D₀.ends (Sum.inl y₃) by
    rw [hD₀, if_neg (Ne.symm hx₃y₃)]; omega)
  obtain ⟨D₁, hD₁e, P₁, hP₁, hP₁s, hP₁x, hrest₁, -⟩ := append_full D₀ (delList_not_adj _ _) hK₁ hPA
    hPAe (PA.not_mem_of_isolated (iso0 1))
  have ext₁ : ExtP P₁ PA (Sum.inl y₃) (Sum.inr 1) := ⟨hP₁s, hP₁x⟩
  -- Step 2: the first walk `x₂ → y₃`
  have eB : s(Sum.inl x₂, Sum.inl y₃) ∈ (splitG J z x₂ y₂ x₃ y₃).edgeSet := by
    refine (splitG_ll J z x₂ y₂ x₃ y₃).2 ⟨h₂₃, ?_⟩
    simp [Sym2.eq_iff, hzx₂.symm, hzy₃.symm, hzx₂, hzy₃]
  have nB : s(Sum.inl x₂, Sum.inl y₃) ∉ [s(Sum.inl y₂, Sum.inr 0), s(Sum.inl x₁, Sum.inl y₂)] ++
      [s(Sum.inl z, Sum.inl x₁), s(Sum.inr 0, Sum.inl x₂), s(Sum.inr (1 : Fin 2), Sum.inl x₃)] := by
    simp [Sym2.eq_iff, hx₁x₂.symm, hy₂y₃.symm, hzx₂.symm, hx₂y₂]
  have hK₂ := delList_cons (splitG J z x₂ y₂ x₃ y₃) eB nB
  have hD₁x₂ : 0 < D₁.ends (Sum.inl x₂) := by
    have h1 := hD₁e (Sum.inl x₂)
    have h2 := hD₀ x₂
    simp only [Sum.inl.injEq, reduceCtorEq, ite_false, add_zero] at h1
    split_ifs at h1 h2 with c1 c2 <;> first | omega | exact absurd c1.symm hx₂y₃ | exact absurd c2 hx₂x₃
  obtain ⟨RB, hRB, hRBe⟩ := D₁.exists_end_of_pos hD₁x₂
  obtain ⟨QB, hQB, sB⟩ : ∃ Q ∈ D₀.paths, SameP RB Q := by
    rcases hrest₁ RB hRB with h | h
    · exfalso
      subst h
      obtain ⟨hPAx₂, -⟩ := ext₁.ends hRBe (by simp)
      exact E5 PA hPA hPAx₂ (mem_support_of_end hPAe)
    · exact h
  obtain ⟨D₂, hD₂e, P₂, hP₂, hP₂s, hP₂x, hrest₂, -⟩ := append_full D₁ (delList_not_adj _ _) hK₂ hRB
    hRBe (by rw [sB.mem]; exact E5 QB hQB (sB.ends.mp hRBe))
  have ext₂ : ExtP P₂ QB (Sum.inl x₂) (Sum.inl y₃) := ExtP.of_same ⟨hP₂s, hP₂x⟩ sB
  -- Step 3: a leaf at `y₂`
  have eC : s(Sum.inl y₂, Sum.inr 0) ∈ (splitG J z x₂ y₂ x₃ y₃).edgeSet :=
    (splitG_l0 J z x₂ y₂ x₃ y₃).2 (Or.inr rfl)
  have nC : s(Sum.inl y₂, Sum.inr 0) ∉ [s(Sum.inl x₁, Sum.inl y₂)] ++
      [s(Sum.inl z, Sum.inl x₁), s(Sum.inr 0, Sum.inl x₂), s(Sum.inr (1 : Fin 2), Sum.inl x₃)] := by
    simp [Sym2.eq_iff, hx₂y₂.symm]
  have hK₃ := delList_cons (splitG J z x₂ y₂ x₃ y₃) eC nC
  have hD₂y₂ : 0 < D₂.ends (Sum.inl y₂) := by
    have h1 := hD₂e (Sum.inl y₂)
    have h2 := hD₁e (Sum.inl y₂)
    have h3 := hD₀ y₂
    simp only [Sum.inl.injEq, reduceCtorEq, ite_false, add_zero, hx₂y₂, hy₂y₃.symm, hy₂x₃,
      ite_false] at h1 h2 h3
    omega
  obtain ⟨RC, hRC, hRCe⟩ := D₂.exists_end_of_pos hD₂y₂
  have iso2 : ∀ w, ¬ (spl J z x₁ x₂ y₂ x₃ y₃ [s(Sum.inl y₂, Sum.inr 0),
      s(Sum.inl x₁, Sum.inl y₂)]).Adj (Sum.inr 0) w := by
    intro w h
    obtain ⟨h1, h2⟩ := h
    cases w with
    | inr j => exact h1
    | inl b =>
      rcases (show b = x₂ ∨ b = y₂ from h1) with rfl | rfl
      · exact h2 (by simp)
      · exact h2 (by simp [Sym2.eq_swap])
  obtain ⟨QC, hQC, sC⟩ : ∃ Q ∈ D₀.paths, SameP RC Q := by
    rcases hrest₂ RC hRC with h | ⟨R₁, hR₁, s₁⟩
    · exfalso
      subst h
      obtain ⟨hQBy₂, -⟩ := ext₂.ends hRCe (by simpa using hy₂y₃)
      exact E2 QB hQB hQBy₂ (mem_support_of_end ext₂.end_t)
    · have s₁ : SameP RC R₁ := s₁
      rcases hrest₁ R₁ hR₁ with h | ⟨Q, hQ, s⟩
      · exfalso
        subst h
        obtain ⟨hPAy₂, -⟩ := ext₁.ends (s₁.ends.mp hRCe) (by simp)
        exact E4 PA hPA (ends_pair PA (by simpa using hy₂y₃) hPAy₂ hPAe)
      · exact ⟨Q, hQ, s₁.trans (show SameP R₁ Q from s)⟩
  obtain ⟨D₃, hD₃e, P₃, hP₃, hP₃s, hP₃x, hrest₃, -⟩ := append_full D₂ (delList_not_adj _ _) hK₃ hRC
    hRCe (RC.not_mem_of_isolated iso2)
  have ext₃ : ExtP P₃ QC (Sum.inl y₂) (Sum.inr 0) := ExtP.of_same ⟨hP₃s, hP₃x⟩ sC
  refine ⟨D₃, fun v => ?_, ?_, ?_, fun R hR => ?_, fun x p hp0 hp3 hp1 h => ?_⟩
  · have h1 := hD₃e (Sum.inl v)
    have h2 := hD₂e (Sum.inl v)
    have h3 := hD₁e (Sum.inl v)
    have h4 := hD₀ v
    simp only [Sum.inl.injEq, reduceCtorEq, ite_false, add_zero] at h1 h2 h3
    by_cases a : v = x₃
    · subst a
      simp only [hx₂x₃, hy₂x₃, hx₃y₃.symm, ite_true, ite_false, true_or, add_zero] at h1 h2 h3 h4 ⊢
      omega
    · by_cases b : v = x₂
      · subst b
        simp only [hx₂y₂.symm, hx₂y₃.symm, hx₂x₃, a, ite_true, ite_false, true_or, or_true,
          add_zero] at h1 h2 h3 h4 ⊢
        omega
      · by_cases c : v = y₂
        · subst c
          simp only [hx₂y₂, hy₂y₃.symm, a, b, ite_true, ite_false, or_true, add_zero] at h1 h2 h3 h4 ⊢
          omega
        · have c' : ¬ (v = x₃ ∨ v = x₂ ∨ v = y₂) := fun h => h.elim a (fun h => h.elim b c)
          rw [if_neg (Ne.symm c)] at h1
          rw [if_neg (Ne.symm b)] at h2
          rw [if_neg a] at h4
          rw [if_neg c']
          by_cases d : y₃ = v
          · rw [if_pos d] at h2 h3; omega
          · rw [if_neg d] at h2 h3; omega
  · have h1 := hD₃e (Sum.inr 0)
    have h2 := hD₂e (Sum.inr 0)
    have h3 := hD₁e (Sum.inr 0)
    have h4 := hD₀r 0
    simp only [reduceCtorEq, ite_false, ite_true, add_zero, Sum.inr.injEq] at h1 h2 h3
    simp only [show ((1 : Fin 2) = 0) = False by decide, ite_false, add_zero] at h3
    omega
  · have h1 := hD₃e (Sum.inr 1)
    have h2 := hD₂e (Sum.inr 1)
    have h3 := hD₁e (Sum.inr 1)
    have h4 := hD₀r 1
    simp only [reduceCtorEq, ite_false, ite_true, add_zero, Sum.inr.injEq] at h1 h2 h3
    simp only [show ((0 : Fin 2) = 1) = False by decide, ite_false, add_zero] at h1
    omega
  · rcases hrest₃ R hR with rfl | ⟨R₂, hR₂, s₂⟩
    · exact ⟨QC, hQC, Or.inr (Or.inr (Or.inr ext₃))⟩
    · have s₂ : SameP R R₂ := s₂
      rcases hrest₂ R₂ hR₂ with rfl | ⟨R₁, hR₁, s₁⟩
      · exact ⟨QB, hQB, Or.inr (Or.inr (Or.inl (s₂.ext ext₂)))⟩
      · have s₁ : SameP R₂ R₁ := s₁
        rcases hrest₁ R₁ hR₁ with rfl | ⟨Q, hQ, s⟩
        · exact ⟨PA, hPA, Or.inr (Or.inl ((s₂.trans s₁).ext ext₁))⟩
        · exact ⟨Q, hQ, Or.inl (s₂.trans (s₁.trans s))⟩
  · rcases fanPred_append hRC hP₃x hP₃s hrest₃ (by simp) hp0 h with h | ⟨-, h⟩
    · rcases fanPred_append hRB hP₂x hP₂s hrest₂ (by simpa using hy₂y₃) hp3 h with h | ⟨hx, h⟩
      · rcases fanPred_append hPA hP₁x hP₁s hrest₁ (by simp) hp1 h with h | ⟨hx, h⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨hx, h⟩)
      · rcases fanPred_append hPA hP₁x hP₁s hrest₁ (by simp) hp1 h with h | ⟨hx', -⟩
        · exact Or.inr (Or.inr ⟨hx, h⟩)
        · exact absurd hx' (by simp)
    · exact absurd h (fanPred_self _)

/-- The leaf conditions: the path through `z` (the leaf `ℓ₁`) avoids `x₁`, the path through
`ℓ₂ = inr 0` avoids `x₂`, the one through `ℓ₃ = inr 1` avoids `x₃`, and no path contains two
leaves. -/
def LeafOK {K : SimpleGraph (V ⊕ Fin 2)} (D : PathDecomp K) (z x₁ x₂ x₃ : V) : Prop :=
  (∀ P ∈ D.paths, Sum.inl z ∈ P.walk.support →
    Sum.inl x₁ ∉ P.walk.support ∧ Sum.inr 0 ∉ P.walk.support ∧ Sum.inr 1 ∉ P.walk.support) ∧
  (∀ P ∈ D.paths, Sum.inr 0 ∈ P.walk.support →
    Sum.inl x₂ ∉ P.walk.support ∧ Sum.inr 1 ∉ P.walk.support) ∧
  (∀ P ∈ D.paths, Sum.inr 1 ∈ P.walk.support → Sum.inl x₃ ∉ P.walk.support)

omit [Fintype V] in
/-- The leaf conditions survive a step whose new paths lie in old ones together with `y`, if
`y` is none of `z, x₁, x₂, x₃`. -/
theorem LeafOK.of_cover {K K' : SimpleGraph (V ⊕ Fin 2)} {D : PathDecomp K} {D' : PathDecomp K'}
    {z x₁ x₂ x₃ y : V} (h : LeafOK D z x₁ x₂ x₃)
    (hcov : ∀ Q ∈ D'.paths, ∃ Q' ∈ D.paths, ∀ v ∈ Q.walk.support,
      v ∈ Q'.walk.support ∨ v = Sum.inl y)
    (hyz : y ≠ z) (hy₁ : y ≠ x₁) (hy₂ : y ≠ x₂) (hy₃ : y ≠ x₃) : LeafOK D' z x₁ x₂ x₃ := by
  have key : ∀ Q ∈ D'.paths, ∃ Q' ∈ D.paths, ∀ v, v ≠ Sum.inl y →
      (v ∈ Q.walk.support → v ∈ Q'.walk.support) := by
    intro Q hQ
    obtain ⟨Q', hQ', h'⟩ := hcov Q hQ
    exact ⟨Q', hQ', fun v hv hvQ => (h' v hvQ).resolve_right hv⟩
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun Q hQ hz => ?_, fun Q hQ h0 => ?_, fun Q hQ h1' => ?_⟩
  · obtain ⟨Q', hQ', k⟩ := key Q hQ
    obtain ⟨a, b, c⟩ := h1 Q' hQ' (k _ (by simpa using hyz.symm) hz)
    exact ⟨fun h => a (k _ (by simpa using hy₁.symm) h), fun h => b (k _ (by simp) h),
      fun h => c (k _ (by simp) h)⟩
  · obtain ⟨Q', hQ', k⟩ := key Q hQ
    obtain ⟨a, b⟩ := h2 Q' hQ' (k _ (by simp) h0)
    exact ⟨fun h => a (k _ (by simpa using hy₂.symm) h), fun h => b (k _ (by simp) h)⟩
  · obtain ⟨Q', hQ', k⟩ := key Q hQ
    exact fun h => h3 Q' hQ' (k _ (by simp) h1') (k _ (by simpa using hy₃.symm) h)

omit [Fintype V] in
/-- The leaf conditions after steps 1–3, read off the base decomposition. -/
theorem leafOK_three {K₀ K₃ : SimpleGraph (V ⊕ Fin 2)} {D₀ : PathDecomp K₀} {D₃ : PathDecomp K₃}
    {z x₁ x₂ x₃ y₂ y₃ : V} (hzy₃ : z ≠ y₃) (hx₁y₃ : x₁ ≠ y₃)
    (hiso : ∀ P ∈ D₀.paths, ∀ i : Fin 2, Sum.inr i ∉ P.walk.support)
    (hcl : ∀ R ∈ D₃.paths, ∃ Q ∈ D₀.paths, SameP R Q ∨ ExtP R Q (Sum.inl y₃) (Sum.inr 1) ∨
      ExtP R Q (Sum.inl x₂) (Sum.inl y₃) ∨ ExtP R Q (Sum.inl y₂) (Sum.inr 0))
    (E1 : ∀ P ∈ D₀.paths, Sum.inl z ∈ P.walk.support → Sum.inl x₁ ∉ P.walk.support ∧
      P.src ≠ Sum.inl y₂ ∧ P.tgt ≠ Sum.inl y₂ ∧ P.src ≠ Sum.inl y₃ ∧ P.tgt ≠ Sum.inl y₃)
    (E2 : ∀ P ∈ D₀.paths, (P.src = Sum.inl y₂ ∨ P.tgt = Sum.inl y₂) →
      Sum.inl x₂ ∉ P.walk.support)
    (E3 : ∀ P ∈ D₀.paths, (P.src = Sum.inl y₃ ∨ P.tgt = Sum.inl y₃) →
      Sum.inl x₃ ∉ P.walk.support) :
    LeafOK D₃ z x₁ x₂ x₃ := by
  have nz : ∀ Q ∈ D₀.paths, Sum.inl z ∈ Q.walk.support → ∀ c, (Q.src = c ∨ Q.tgt = c) →
      c ≠ Sum.inl y₂ ∧ c ≠ Sum.inl y₃ := by
    intro Q hQ hz c hc
    obtain ⟨-, a, b, c', d⟩ := E1 Q hQ hz
    rcases hc with rfl | rfl
    · exact ⟨a, c'⟩
    · exact ⟨b, d⟩
  refine ⟨fun R hR hz => ?_, fun R hR h0 => ?_, fun R hR h1 => ?_⟩
  · obtain ⟨Q, hQ, hs | he | he | he⟩ := hcl R hR
    · rw [hs.mem] at hz ⊢; rw [hs.mem, hs.mem]
      exact ⟨(E1 Q hQ hz).1, hiso Q hQ 0, hiso Q hQ 1⟩
    · rw [he.mem] at hz
      rcases hz with h | h
      · exact absurd h (by simp)
      · exact absurd rfl (nz Q hQ h _ he.end_t).2
    · rw [he.mem] at hz
      rcases hz with h | hz
      · exact absurd (Sum.inl_injective h) hzy₃
      · rw [he.mem, he.mem, he.mem]
        refine ⟨?_, ?_, ?_⟩
        · rintro (h | h)
          · exact hx₁y₃ (Sum.inl_injective h)
          · exact (E1 Q hQ hz).1 h
        · rintro (h | h); exact absurd h (by simp); exact hiso Q hQ 0 h
        · rintro (h | h); exact absurd h (by simp); exact hiso Q hQ 1 h
    · rw [he.mem] at hz
      rcases hz with h | h
      · exact absurd h (by simp)
      · exact absurd rfl (nz Q hQ h _ he.end_t).1
  · obtain ⟨Q, hQ, hs | he | he | he⟩ := hcl R hR
    · rw [hs.mem] at h0; exact absurd h0 (hiso Q hQ 0)
    · rw [he.mem] at h0
      rcases h0 with h | h
      · exact absurd h (by simp)
      · exact absurd h (hiso Q hQ 0)
    · rw [he.mem] at h0
      rcases h0 with h | h
      · exact absurd h (by simp)
      · exact absurd h (hiso Q hQ 0)
    · rw [he.mem, he.mem]
      refine ⟨?_, ?_⟩
      · rintro (h | h); exact absurd h (by simp); exact E2 Q hQ he.end_t h
      · rintro (h | h); exact absurd h (by simp); exact hiso Q hQ 1 h
  · obtain ⟨Q, hQ, hs | he | he | he⟩ := hcl R hR
    · rw [hs.mem] at h1; exact absurd h1 (hiso Q hQ 1)
    · rw [he.mem]
      rintro (h | h); exact absurd h (by simp); exact E3 Q hQ he.end_t h
    · rw [he.mem] at h1
      rcases h1 with h | h
      · exact absurd h (by simp)
      · exact absurd h (hiso Q hQ 1)
    · rw [he.mem] at h1
      rcases h1 with h | h
      · exact absurd h (by simp)
      · exact absurd h (hiso Q hQ 1)

omit [Fintype V] in
/-- A path starting at a vertex whose only neighbour is its other end is a single edge. -/
theorem walk_leaf_edges {W : Type*} {K : SimpleGraph W} {a b : W} (hab : a ≠ b)
    (hnb : ∀ w, K.Adj a w → w = b) (p : K.Walk a b) (hp : p.IsPath) : ∀ e ∈ p.edges, a ∈ e := by
  cases p with
  | nil => exact absurd rfl hab
  | cons h q =>
    obtain rfl := hnb _ h
    have hq : q = Walk.nil := Walk.isPath_iff_eq_nil.mp ((Walk.cons_isPath_iff h q).mp hp).1
    subst hq
    intro e he
    simp only [Walk.edges_cons, Walk.edges_nil, List.mem_singleton] at he
    rw [he]; exact Sym2.mem_mk_left _ _

omit [Fintype V] in
theorem gpath_leaf_edges {W : Type*} {K : SimpleGraph W} (P : GPath K) {a b : W} (hab : a ≠ b)
    (hnb : ∀ w, K.Adj a w → w = b) (hends : (P.src = a ∧ P.tgt = b) ∨ (P.src = b ∧ P.tgt = a)) :
    ∀ e ∈ P.edges, a ∈ e := by
  have key : ∀ (a' b' : W) (p : K.Walk a' b'), a' = a → b' = b → p.IsPath → ∀ e ∈ p.edges, a ∈ e := by
    intro a' b' p ha hb hp
    subst ha; subst hb
    exact walk_leaf_edges hab hnb p hp
  rcases hends with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact key _ _ P.walk hs ht P.isPath
  · intro e he
    refine key _ _ P.walk.reverse ht hs P.isPath.reverse e ?_
    rw [Walk.edges_reverse, List.mem_reverse]; exact he

variable (J : SimpleGraph V) [DecidableRel J.Adj] {z x₁ y₁ x₂ y₂ x₃ y₃ : V}

omit [Fintype V] in
/-- The edges of the split graph at the split vertex `z`. -/
theorem splitG_edge_z (hne : [z, x₁, y₁, x₂, y₂, x₃, y₃].Nodup)
    (hN : ∀ v, J.Adj z v ↔ v = x₁ ∨ v = y₁ ∨ v = x₂ ∨ v = y₂ ∨ v = x₃ ∨ v = y₃)
    {e : Sym2 (V ⊕ Fin 2)} (he : e ∈ (splitG J z x₂ y₂ x₃ y₃).edgeSet) (hz : Sum.inl z ∈ e) :
    e = s(Sum.inl z, Sum.inl x₁) ∨ e = s(Sum.inl z, Sum.inl y₁) := by
  obtain ⟨hzx₁, hzy₁, hzx₂, hzy₂, hzx₃, hzy₃, -⟩ := nodup7 hne
  have key : ∀ b, (splitG J z x₂ y₂ x₃ y₃).Adj (Sum.inl z) b →
      b = Sum.inl x₁ ∨ b = Sum.inl y₁ := by
    intro b hb
    cases b with
    | inl b =>
      obtain ⟨h1, h2⟩ := (splitG_ll J z x₂ y₂ x₃ y₃).mp hb
      rcases (hN b).mp h1 with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      all_goals exact absurd (by simp) h2
    | inr i =>
      have : (if i = 0 then z = x₂ ∨ z = y₂ else z = x₃ ∨ z = y₃) := hb
      split_ifs at this <;> rcases this with h | h <;> simp_all
  induction e using Sym2.inductionOn with
  | hf a b =>
    rcases Sym2.mem_iff.mp hz with rfl | rfl
    · rcases key b he with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rcases key a ((SimpleGraph.mem_edgeSet _).mp he).symm with rfl | rfl
      · exact Or.inl Sym2.eq_swap
      · exact Or.inr Sym2.eq_swap

omit [Fintype V] in
/-- The edges of the split graph at the leaf `inr i`. -/
theorem splitG_edge_r {i : Fin 2} {e : Sym2 (V ⊕ Fin 2)}
    (he : e ∈ (splitG J z x₂ y₂ x₃ y₃).edgeSet) (hi : Sum.inr i ∈ e) :
    (i = 0 ∧ (e = s(Sum.inr 0, Sum.inl x₂) ∨ e = s(Sum.inr 0, Sum.inl y₂))) ∨
      (i = 1 ∧ (e = s(Sum.inr 1, Sum.inl x₃) ∨ e = s(Sum.inr 1, Sum.inl y₃))) := by
  have key : ∀ b, (splitG J z x₂ y₂ x₃ y₃).Adj (Sum.inr i) b →
      (i = 0 ∧ (b = Sum.inl x₂ ∨ b = Sum.inl y₂)) ∨ (i = 1 ∧ (b = Sum.inl x₃ ∨ b = Sum.inl y₃)) := by
    intro b hb
    cases b with
    | inr j => exact absurd hb (splitG_rr J z x₂ y₂ x₃ y₃)
    | inl b =>
      have : (if i = 0 then b = x₂ ∨ b = y₂ else b = x₃ ∨ b = y₃) := hb
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, ite_true] at this
        rcases this with rfl | rfl <;> simp
      · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ite_false] at this
        rcases this with rfl | rfl <;> simp
  induction e using Sym2.inductionOn with
  | hf a b =>
    rcases Sym2.mem_iff.mp hi with rfl | rfl
    · rcases key b he with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> simp
    · rcases key a ((SimpleGraph.mem_edgeSet _).mp he).symm with
        ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;>
        simp [Sym2.eq_swap]

/-- Collapse the split vertices onto `z`. -/
def collapse (z : V) : V ⊕ Fin 2 → V := Sum.elim id (fun _ => z)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem collapse_inl (z v : V) : collapse z (Sum.inl v) = v := rfl
omit [Fintype V] [DecidableEq V] in
@[simp] theorem collapse_inr (z : V) (i : Fin 2) : collapse z (Sum.inr i) = z := rfl

omit [Fintype V] in
theorem collapse_eq_iff {z v : V} (hv : v ≠ z) {x : V ⊕ Fin 2} :
    collapse z x = v ↔ x = Sum.inl v := by
  cases x with
  | inl a => simp
  | inr i => simp only [collapse_inr, reduceCtorEq, iff_false]; exact Ne.symm hv

omit [Fintype V] in
theorem collapse_hE (hne : [z, x₁, y₁, x₂, y₂, x₃, y₃].Nodup)
    (hN : ∀ v, J.Adj z v ↔ v = x₁ ∨ v = y₁ ∨ v = x₂ ∨ v = y₂ ∨ v = x₃ ∨ v = y₃) :
    ∀ e ∈ (splitG J z x₂ y₂ x₃ y₃).edgeSet, e.map (collapse z) ∈ J.edgeSet := by
  intro e he
  induction e using Sym2.inductionOn with
  | hf a b =>
    rw [Sym2.map_mk, mem_edgeSet]
    cases a with
    | inl a =>
      cases b with
      | inl b => exact ((splitG_ll J z x₂ y₂ x₃ y₃).mp he).1
      | inr i =>
        have h : (if i = 0 then a = x₂ ∨ a = y₂ else a = x₃ ∨ a = y₃) := he
        refine ((hN a).2 ?_).symm
        split_ifs at h <;> rcases h with rfl | rfl <;> simp
    | inr i =>
      cases b with
      | inl b =>
        have h : (if i = 0 then b = x₂ ∨ b = y₂ else b = x₃ ∨ b = y₃) := he
        refine (hN b).2 ?_
        split_ifs at h <;> rcases h with rfl | rfl <;> simp
      | inr j => exact absurd he (splitG_rr (i := i) (j := j) J z x₂ y₂ x₃ y₃)

omit [Fintype V] in
theorem collapse_hEinj (hne : [z, x₁, y₁, x₂, y₂, x₃, y₃].Nodup)
    (hN : ∀ v, J.Adj z v ↔ v = x₁ ∨ v = y₁ ∨ v = x₂ ∨ v = y₂ ∨ v = x₃ ∨ v = y₃) :
    ∀ e₁ ∈ (splitG J z x₂ y₂ x₃ y₃).edgeSet, ∀ e₂ ∈ (splitG J z x₂ y₂ x₃ y₃).edgeSet,
      e₁.map (collapse z) = e₂.map (collapse z) → e₁ = e₂ := by
  obtain ⟨hzx₁, hzy₁, hzx₂, hzy₂, hzx₃, hzy₃, hx₁y₁, hx₁x₂, hx₁y₂, hx₁x₃, hx₁y₃, hy₁x₂, hy₁y₂,
    hy₁x₃, hy₁y₃, hx₂y₂, hx₂x₃, hx₂y₃, hy₂x₃, hy₂y₃, hx₃y₃⟩ := nodup7 hne
  -- every edge is `s(inl a, inl b)` avoiding `z`'s removed edges, or `s(inl a, inr i)`
  have shape : ∀ e ∈ (splitG J z x₂ y₂ x₃ y₃).edgeSet,
      (∃ a b, e = s(Sum.inl a, Sum.inl b) ∧ J.Adj a b ∧
        (a = z → b = x₁ ∨ b = y₁) ∧ (b = z → a = x₁ ∨ a = y₁)) ∨
      (∃ a, e = s(Sum.inl a, Sum.inr 0) ∧ (a = x₂ ∨ a = y₂)) ∨
      (∃ a, e = s(Sum.inl a, Sum.inr 1) ∧ (a = x₃ ∨ a = y₃)) := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf a b =>
      cases a with
      | inl a =>
        cases b with
        | inl b =>
          obtain ⟨h1, h2⟩ := (splitG_ll J z x₂ y₂ x₃ y₃).mp he
          refine Or.inl ⟨a, b, rfl, h1, fun ha => ?_, fun hb => ?_⟩
          · subst ha
            rcases (hN b).mp h1 with rfl | rfl | rfl | rfl | rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr rfl
            all_goals exact absurd (by simp) h2
          · subst hb
            rcases (hN a).mp h1.symm with rfl | rfl | rfl | rfl | rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr rfl
            all_goals exact absurd (by simp [Sym2.eq_swap]) h2
        | inr i =>
          have h : (if i = 0 then a = x₂ ∨ a = y₂ else a = x₃ ∨ a = y₃) := he
          fin_cases i
          · exact Or.inr (Or.inl ⟨a, rfl, by simpa using h⟩)
          · exact Or.inr (Or.inr ⟨a, rfl, by simpa using h⟩)
      | inr i =>
        cases b with
        | inl b =>
          have h : (if i = 0 then b = x₂ ∨ b = y₂ else b = x₃ ∨ b = y₃) := he
          fin_cases i
          · exact Or.inr (Or.inl ⟨b, Sym2.eq_swap, by simpa using h⟩)
          · exact Or.inr (Or.inr ⟨b, Sym2.eq_swap, by simpa using h⟩)
        | inr j => exact absurd he (splitG_rr (i := i) (j := j) J z x₂ y₂ x₃ y₃)
  intro e₁ he₁ e₂ he₂ heq
  rcases shape e₁ he₁ with ⟨a, b, rfl, hab, ha, hb⟩ | ⟨a, rfl, ha⟩ | ⟨a, rfl, ha⟩ <;>
    rcases shape e₂ he₂ with ⟨c, d, rfl, hcd, hc, hd⟩ | ⟨c, rfl, hc⟩ | ⟨c, rfl, hc⟩ <;>
    simp only [Sym2.map_mk, collapse_inl, collapse_inr, Sym2.eq_iff] at heq
  · rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Sym2.eq_swap
  · rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hb rfl with rfl | rfl <;> rcases hc with h | h <;> simp_all
    · rcases ha rfl with rfl | rfl <;> rcases hc with h | h <;> simp_all
  · rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hb rfl with rfl | rfl <;> rcases hc with h | h <;> simp_all
    · rcases ha rfl with rfl | rfl <;> rcases hc with h | h <;> simp_all
  · rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hd rfl with rfl | rfl <;> rcases ha with h | h <;> simp_all
    · rcases hc rfl with rfl | rfl <;> rcases ha with h | h <;> simp_all
  · rcases heq with ⟨rfl, -⟩ | ⟨h, -⟩
    · rfl
    · rcases ha with rfl | rfl <;> simp_all
  · rcases heq with ⟨rfl, -⟩ | ⟨h, -⟩ <;> rcases ha with rfl | rfl <;> rcases hc with h' | h' <;>
      simp_all
  · rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hd rfl with rfl | rfl <;> rcases ha with h | h <;> simp_all
    · rcases hc rfl with rfl | rfl <;> rcases ha with h | h <;> simp_all
  · rcases heq with ⟨rfl, -⟩ | ⟨h, -⟩ <;> rcases ha with rfl | rfl <;> rcases hc with h' | h' <;>
      simp_all
  · rcases heq with ⟨rfl, -⟩ | ⟨h, -⟩
    · rfl
    · rcases ha with rfl | rfl <;> simp_all

omit [Fintype V] in
theorem collapse_hcov (hne : [z, x₁, y₁, x₂, y₂, x₃, y₃].Nodup)
    (hN : ∀ v, J.Adj z v ↔ v = x₁ ∨ v = y₁ ∨ v = x₂ ∨ v = y₂ ∨ v = x₃ ∨ v = y₃) :
    ∀ e' ∈ J.edgeSet, ∃ e ∈ (splitG J z x₂ y₂ x₃ y₃).edgeSet, e.map (collapse z) = e' := by
  obtain ⟨hzx₁, hzy₁, hzx₂, hzy₂, hzx₃, hzy₃, hx₁y₁, hx₁x₂, hx₁y₂, hx₁x₃, hx₁y₃, hy₁x₂, hy₁y₂,
    hy₁x₃, hy₁y₃, hx₂y₂, hx₂x₃, hx₂y₃, hy₂x₃, hy₂y₃, hx₃y₃⟩ := nodup7 hne
  -- the edge from `z` to `b`
  have atz : ∀ b, J.Adj z b → ∃ e ∈ (splitG J z x₂ y₂ x₃ y₃).edgeSet,
      e.map (collapse z) = s(z, b) := by
    intro b hb
    rcases (hN b).mp hb with h | h | h | h | h | h <;> subst b
    · exact ⟨s(Sum.inl z, Sum.inl x₁), (splitG_ll J z x₂ y₂ x₃ y₃).2 ⟨hb, by
        simp [Sym2.eq_iff, hx₁x₂, hx₁y₂, hx₁x₃, hx₁y₃, hzx₂, hzy₂, hzx₃, hzy₃]⟩, rfl⟩
    · exact ⟨s(Sum.inl z, Sum.inl y₁), (splitG_ll J z x₂ y₂ x₃ y₃).2 ⟨hb, by
        simp [Sym2.eq_iff, hy₁x₂, hy₁y₂, hy₁x₃, hy₁y₃, hzx₂, hzy₂, hzx₃, hzy₃]⟩, rfl⟩
    · exact ⟨s(Sum.inr 0, Sum.inl x₂), (splitG_l0 J z x₂ y₂ x₃ y₃).2 (Or.inl rfl) |>.symm,
        by simp [Sym2.map_mk]⟩
    · exact ⟨s(Sum.inr 0, Sum.inl y₂), (splitG_l0 J z x₂ y₂ x₃ y₃).2 (Or.inr rfl) |>.symm,
        by simp [Sym2.map_mk]⟩
    · exact ⟨s(Sum.inr 1, Sum.inl x₃), (splitG_l1 J z x₂ y₂ x₃ y₃).2 (Or.inl rfl) |>.symm,
        by simp [Sym2.map_mk]⟩
    · exact ⟨s(Sum.inr 1, Sum.inl y₃), (splitG_l1 J z x₂ y₂ x₃ y₃).2 (Or.inr rfl) |>.symm,
        by simp [Sym2.map_mk]⟩
  intro e' he'
  induction e' using Sym2.inductionOn with
  | hf a b =>
    rw [mem_edgeSet] at he'
    by_cases ha : a = z
    · subst ha; exact atz b he'
    · by_cases hb : b = z
      · subst hb
        obtain ⟨e, he, hm⟩ := atz a he'.symm
        exact ⟨e, he, hm.trans Sym2.eq_swap⟩
      · refine ⟨s(Sum.inl a, Sum.inl b), (splitG_ll J z x₂ y₂ x₃ y₃).2 ⟨he', ?_⟩, rfl⟩
        simp [Sym2.eq_iff, ha, hb, Ne.symm ha, Ne.symm hb]

end main

end Gallai
