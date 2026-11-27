import GallaiLean.Separation
import GallaiLean.BP3

/-!
# Multi-pair separation: the leaf merge, prescribed end edges, and class separation

Manuscript `manuscripts/multi-sep/multi-sep.tex`.

* `PathDecomp.pushOn`: push a decomposition along a vertex map that is injective on the vertex
  set of every path and on the edge set.
* `leaf_merge`: if `H` is `G − ux` with a new leaf at `u`, and no path of a decomposition of `H`
  contains both `x` and the leaf, then identifying the leaf with `x` gives a decomposition of `G`.
  The ends at `x` add up, all other ends are kept, and every vertex set is the image of an old
  one.
* `lovasz_endEdge_set` (**prescribed end edge**): if all degrees of `G` are odd or zero,
  `X` is packed and `x ∈ X`, then for every edge `xu` some Lovász decomposition meets `X` at most
  once per path and its path ending at `x` contains `xu` (so `xu` is its terminal edge).
  `lovasz_endEdge` is the case `X = {x}`.
* `ClassSep`, `classSep_allOdd`: class separation for every graph with exactly one vertex of
  positive even degree implies it for every graph with none (Lovász's Case II costs nothing:
  the new leaf joins every class of `x`).
* `classSep_caseI`: the certified Case I step. If `z` is the even vertex, `u` a neighbour, and
  `G − uz` has a Lovász decomposition that is rainbow for the family in which `z` joins every
  class of `u` and `{u, z}` is a class, then appending `zu` gives a rainbow Lovász decomposition
  of `G`.
-/

open SimpleGraph

namespace Gallai

universe u v

section pushOn

variable {V : Type u} {V' : Type v} [DecidableEq V] [DecidableEq V']
variable {G : SimpleGraph V} {G' : SimpleGraph V'}

/-- A path pushed along a map that is injective on its vertex set. -/
def GPath.pushOn (f : V → V') (hE : ∀ e ∈ G.edgeSet, e.map f ∈ G'.edgeSet) (P : GPath G)
    (hinj : ∀ x ∈ P.walk.support, ∀ y ∈ P.walk.support, f x = f y → x = y) : GPath G' where
  src := f P.src
  tgt := f P.tgt
  walk := pushWalk f P.walk (fun e he => hE e (P.walk.edges_subset_edgeSet he))
  isPath := pushWalk_isPath f P.walk _ P.isPath hinj
  pos := by rw [pushWalk_length]; exact P.pos

omit [DecidableEq V] [DecidableEq V'] in
@[simp] theorem GPath.pushOn_edges (f : V → V') (hE : ∀ e ∈ G.edgeSet, e.map f ∈ G'.edgeSet)
    (P : GPath G) (hinj : ∀ x ∈ P.walk.support, ∀ y ∈ P.walk.support, f x = f y → x = y) :
    (P.pushOn f hE hinj).edges = P.edges.map (Sym2.map f) := by
  simp [GPath.pushOn, GPath.edges]

omit [DecidableEq V] [DecidableEq V'] in
@[simp] theorem GPath.pushOn_support (f : V → V') (hE : ∀ e ∈ G.edgeSet, e.map f ∈ G'.edgeSet)
    (P : GPath G) (hinj : ∀ x ∈ P.walk.support, ∀ y ∈ P.walk.support, f x = f y → x = y) :
    (P.pushOn f hE hinj).walk.support = P.walk.support.map f := by
  simp [GPath.pushOn]

omit [DecidableEq V] [DecidableEq V'] in
@[simp] theorem GPath.pushOn_src (f : V → V') (hE : ∀ e ∈ G.edgeSet, e.map f ∈ G'.edgeSet)
    (P : GPath G) (hinj : ∀ x ∈ P.walk.support, ∀ y ∈ P.walk.support, f x = f y → x = y) :
    (P.pushOn f hE hinj).src = f P.src := rfl

omit [DecidableEq V] [DecidableEq V'] in
@[simp] theorem GPath.pushOn_tgt (f : V → V') (hE : ∀ e ∈ G.edgeSet, e.map f ∈ G'.edgeSet)
    (P : GPath G) (hinj : ∀ x ∈ P.walk.support, ∀ y ∈ P.walk.support, f x = f y → x = y) :
    (P.pushOn f hE hinj).tgt = f P.tgt := rfl

omit [DecidableEq V] [DecidableEq V'] in
theorem flatMap_pmap_pushOn (f : V → V') (hE : ∀ e ∈ G.edgeSet, e.map f ∈ G'.edgeSet)
    (L : List (GPath G))
    (hinj : ∀ P ∈ L, ∀ x ∈ P.walk.support, ∀ y ∈ P.walk.support, f x = f y → x = y) :
    (L.pmap (fun P hP => P.pushOn f hE hP) hinj).flatMap GPath.edges =
      (L.flatMap GPath.edges).map (Sym2.map f) := by
  induction L with
  | nil => simp
  | cons P L ih =>
    simp only [List.pmap_cons, List.flatMap_cons, List.map_append, GPath.pushOn_edges]
    rw [ih]

/-- A decomposition pushed along a map that is injective on every vertex set of a path and on
the edge set, onto a graph whose edges are exactly the images. -/
def PathDecomp.pushOn (D : PathDecomp G) (f : V → V')
    (hE : ∀ e ∈ G.edgeSet, e.map f ∈ G'.edgeSet)
    (hEinj : ∀ e₁ ∈ G.edgeSet, ∀ e₂ ∈ G.edgeSet, e₁.map f = e₂.map f → e₁ = e₂)
    (hcov : ∀ e' ∈ G'.edgeSet, ∃ e ∈ G.edgeSet, e.map f = e')
    (hinj : ∀ P ∈ D.paths, ∀ x ∈ P.walk.support, ∀ y ∈ P.walk.support, f x = f y → x = y) :
    PathDecomp G' where
  paths := D.paths.pmap (fun P hP => P.pushOn f hE hP) hinj
  nodup_edges := by
    rw [flatMap_pmap_pushOn]
    refine D.nodup_edges.map_on ?_
    intro a ha b hb hab
    exact hEinj a ((D.covers a).2 ha) b ((D.covers b).2 hb) hab
  covers := by
    intro e'
    rw [flatMap_pmap_pushOn, List.mem_map]
    constructor
    · intro he'
      obtain ⟨e, he, rfl⟩ := hcov e' he'
      exact ⟨e, (D.covers e).1 he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact hE e ((D.covers e).2 he)

theorem PathDecomp.pushOn_mem {D : PathDecomp G} {f : V → V'}
    {hE : ∀ e ∈ G.edgeSet, e.map f ∈ G'.edgeSet}
    {hEinj : ∀ e₁ ∈ G.edgeSet, ∀ e₂ ∈ G.edgeSet, e₁.map f = e₂.map f → e₁ = e₂}
    {hcov : ∀ e' ∈ G'.edgeSet, ∃ e ∈ G.edgeSet, e.map f = e'}
    {hinj : ∀ P ∈ D.paths, ∀ x ∈ P.walk.support, ∀ y ∈ P.walk.support, f x = f y → x = y}
    {Q : GPath G'} :
    Q ∈ (D.pushOn f hE hEinj hcov hinj).paths ↔
      ∃ P, ∃ hP : P ∈ D.paths, Q = P.pushOn f hE (hinj P hP) := by
  change Q ∈ D.paths.pmap _ hinj ↔ _
  rw [List.mem_pmap]
  constructor
  · rintro ⟨P, hP, rfl⟩; exact ⟨P, hP, rfl⟩
  · rintro ⟨P, hP, rfl⟩; exact ⟨P, hP, rfl⟩

theorem PathDecomp.pushOn_ends (D : PathDecomp G) (f : V → V')
    (hE : ∀ e ∈ G.edgeSet, e.map f ∈ G'.edgeSet)
    (hEinj : ∀ e₁ ∈ G.edgeSet, ∀ e₂ ∈ G.edgeSet, e₁.map f = e₂.map f → e₁ = e₂)
    (hcov : ∀ e' ∈ G'.edgeSet, ∃ e ∈ G.edgeSet, e.map f = e')
    (hinj : ∀ P ∈ D.paths, ∀ x ∈ P.walk.support, ∀ y ∈ P.walk.support, f x = f y → x = y)
    (y : V') (c : GPath G → ℕ)
    (hc : ∀ P ∈ D.paths, (if f P.src = y then 1 else 0) + (if f P.tgt = y then 1 else 0) = c P) :
    (D.pushOn f hE hEinj hcov hinj).ends y = (D.paths.map c).sum := by
  unfold PathDecomp.ends
  change ((D.paths.pmap (fun P hP => P.pushOn f hE hP) hinj).map (fun Q => Q.endsAt y)).sum = _
  have key : ∀ (L : List (GPath G))
      (h : ∀ P ∈ L, ∀ x ∈ P.walk.support, ∀ y ∈ P.walk.support, f x = f y → x = y),
      (∀ P ∈ L, (if f P.src = y then 1 else 0) + (if f P.tgt = y then 1 else 0) = c P) →
      ((L.pmap (fun P hP => P.pushOn f hE hP) h).map (fun Q => Q.endsAt y)).sum =
        (L.map c).sum := by
    intro L
    induction L with
    | nil => intro _ _; simp
    | cons P L ih =>
      intro h hcP
      simp only [List.pmap_cons, List.map_cons, List.sum_cons]
      rw [ih _ (fun Q hQ => hcP Q (List.mem_cons_of_mem _ hQ))]
      congr 1
      rw [← hcP P List.mem_cons_self]
      rfl
  exact key D.paths hinj hc

end pushOn

/-! ### The leaf merge -/

section merge

variable {W : Type u} [DecidableEq W]

/-- Identify the new vertex `none` with `x`. -/
def mergeMap (x : W) : Option W → W := fun o => o.getD x

@[simp] theorem mergeMap_some (x w : W) : mergeMap x (some w) = w := rfl
@[simp] theorem mergeMap_none (x : W) : mergeMap x none = x := rfl

theorem mergeMap_eq_iff {x w : W} {o : Option W} :
    mergeMap x o = w ↔ o = some w ∨ (o = none ∧ w = x) := by
  cases o with
  | none => simp [mergeMap, eq_comm]
  | some a => simp [mergeMap]

variable (G : SimpleGraph W)

theorem merge_hE {x u : W} (hxu : G.Adj x u) :
    ∀ e ∈ (apex (delEdge G u x) {u}).edgeSet, e.map (mergeMap x) ∈ G.edgeSet := by
  intro e he
  induction e using Sym2.inductionOn with
  | hf a b =>
  rw [mem_edgeSet] at he
  cases a with
  | none =>
    cases b with
    | none => exact absurd he apex_not_adj_none_none
    | some b =>
      rw [apex_adj_none_some, Finset.mem_singleton] at he
      subst he
      exact hxu
  | some a =>
    cases b with
    | none =>
      rw [apex_adj_some_none, Finset.mem_singleton] at he
      subst he
      exact hxu.symm
    | some b =>
      rw [apex_adj_some_some] at he
      exact he.1

theorem merge_hEinj {x u : W} (hxu : G.Adj x u) :
    ∀ e₁ ∈ (apex (delEdge G u x) {u}).edgeSet, ∀ e₂ ∈ (apex (delEdge G u x) {u}).edgeSet,
      e₁.map (mergeMap x) = e₂.map (mergeMap x) → e₁ = e₂ := by
  have hux : u ≠ x := hxu.ne.symm
  -- an edge of `H` through `none` is the leaf edge; others avoid `none` and miss `{u, x}`
  have hleaf := @apex_none_pendant W (delEdge G u x) u
  have hsome : ∀ a b : W, (apex (delEdge G u x) {u}).Adj (some a) (some b) →
      s(a, b) ≠ s(u, x) := fun a b h => h.2
  intro e₁ he₁ e₂ he₂ heq
  by_cases h₁ : (none : Option W) ∈ e₁
  · by_cases h₂ : (none : Option W) ∈ e₂
    · rw [hleaf e₁ he₁ h₁, hleaf e₂ he₂ h₂]
    · exfalso
      rw [hleaf e₁ he₁ h₁] at heq
      induction e₂ using Sym2.inductionOn with
      | hf a b =>
      cases a with
      | none => exact h₂ (Sym2.mem_mk_left _ _)
      | some a =>
        cases b with
        | none => exact h₂ (Sym2.mem_mk_right _ _)
        | some b =>
          rw [mem_edgeSet] at he₂
          simp only [Sym2.map_mk, mergeMap_none, mergeMap_some] at heq
          exact hsome a b he₂ (by rw [← heq, Sym2.eq_swap])
  · by_cases h₂ : (none : Option W) ∈ e₂
    · exfalso
      rw [hleaf e₂ he₂ h₂] at heq
      induction e₁ using Sym2.inductionOn with
      | hf a b =>
      cases a with
      | none => exact h₁ (Sym2.mem_mk_left _ _)
      | some a =>
        cases b with
        | none => exact h₁ (Sym2.mem_mk_right _ _)
        | some b =>
          rw [mem_edgeSet] at he₁
          simp only [Sym2.map_mk, mergeMap_none, mergeMap_some] at heq
          exact hsome a b he₁ (by rw [heq, Sym2.eq_swap])
    · induction e₁ using Sym2.inductionOn with
      | hf a b =>
      induction e₂ using Sym2.inductionOn with
      | hf c d =>
      cases a with
      | none => exact absurd (Sym2.mem_mk_left _ _) h₁
      | some a =>
      cases b with
      | none => exact absurd (Sym2.mem_mk_right _ _) h₁
      | some b =>
      cases c with
      | none => exact absurd (Sym2.mem_mk_left _ _) h₂
      | some c =>
      cases d with
      | none => exact absurd (Sym2.mem_mk_right _ _) h₂
      | some d =>
      simp only [Sym2.map_mk, mergeMap_some] at heq
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap

theorem merge_hcov {x u : W} (hxu : G.Adj x u) :
    ∀ e' ∈ G.edgeSet, ∃ e ∈ (apex (delEdge G u x) {u}).edgeSet, e.map (mergeMap x) = e' := by
  intro e' he'
  induction e' using Sym2.inductionOn with
  | hf a b =>
  by_cases hab : s(a, b) = s(u, x)
  · refine ⟨s(some u, none), ?_, ?_⟩
    · rw [mem_edgeSet, apex_adj_some_none, Finset.mem_singleton]
    · simp only [Sym2.map_mk, mergeMap_some, mergeMap_none]
      exact hab.symm
  · refine ⟨s(some a, some b), ?_, by simp⟩
    rw [mem_edgeSet, apex_adj_some_some]
    exact ⟨he', hab⟩

/-- **Leaf merge.** Let `H` be `G − ux` with a new leaf `none` at `u`. If no path of `DH`
contains both `some x` and `none`, identifying `none` with `x` gives a decomposition of `G`:
the ends at `x` add up, the other ends are kept, and paths correspond to paths with the merged
vertex sets and ends. -/
theorem leaf_merge {x u : W} (hxu : G.Adj x u) (DH : PathDecomp (apex (delEdge G u x) {u}))
    (hsep : Separates DH (some x) none) :
    ∃ D : PathDecomp G,
      D.ends x = DH.ends (some x) + DH.ends none ∧
      (∀ w, w ≠ x → D.ends w = DH.ends (some w)) ∧
      (∀ Q ∈ D.paths, ∃ P ∈ DH.paths,
        Q.walk.support = P.walk.support.map (mergeMap x)) ∧
      (∀ P ∈ DH.paths, ∃ Q ∈ D.paths, Q.src = mergeMap x P.src ∧ Q.tgt = mergeMap x P.tgt ∧
        Q.edges = P.edges.map (Sym2.map (mergeMap x))) := by
  have hinj : ∀ P ∈ DH.paths, ∀ a ∈ P.walk.support, ∀ b ∈ P.walk.support,
      mergeMap x a = mergeMap x b → a = b := by
    intro P hP a ha b hb hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b =>
        exfalso
        simp only [mergeMap_none, mergeMap_some] at hab
        subst hab
        exact hsep P hP ⟨hb, ha⟩
    | some a =>
      cases b with
      | none =>
        exfalso
        simp only [mergeMap_none, mergeMap_some] at hab
        subst hab
        exact hsep P hP ⟨ha, hb⟩
      | some b =>
        simp only [mergeMap_some] at hab
        rw [hab]
  let D := DH.pushOn (mergeMap x) (merge_hE G hxu) (merge_hEinj G hxu) (merge_hcov G hxu) hinj
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · rw [PathDecomp.pushOn_ends _ _ _ _ _ _ x (fun P => P.endsAt (some x) + P.endsAt none)]
    · unfold PathDecomp.ends
      rw [← sum_map_add']
    · intro P _
      simp only [GPath.endsAt, mergeMap_eq_iff]
      cases P.src <;> cases P.tgt <;> simp <;> omega
  · intro w hw
    rw [PathDecomp.pushOn_ends _ _ _ _ _ _ w (fun P => P.endsAt (some w))]
    · rfl
    · intro P _
      simp only [GPath.endsAt, mergeMap_eq_iff, hw, and_false, or_false]
  · intro Q hQ
    obtain ⟨P, hP, rfl⟩ := PathDecomp.pushOn_mem.mp hQ
    exact ⟨P, hP, GPath.pushOn_support _ _ _ _⟩
  · intro P hP
    refine ⟨P.pushOn (mergeMap x) (merge_hE G hxu) (hinj P hP),
      PathDecomp.pushOn_mem.mpr ⟨P, hP, rfl⟩, rfl, rfl, GPath.pushOn_edges _ _ _ _⟩

end merge

/-! ### Small facts about paths -/

section paths

variable {W : Type u} {G : SimpleGraph W}

/-- A path has an edge at each of its ends. -/
theorem GPath.exists_edge_at_src (P : GPath G) : ∃ e ∈ P.edges, P.src ∈ e := by
  obtain ⟨src, tgt, w, hw, hpos⟩ := P
  cases w with
  | nil => simp at hpos
  | cons h q => exact ⟨_, List.mem_cons_self, Sym2.mem_mk_left _ _⟩

theorem GPath.exists_edge_at_tgt (P : GPath G) : ∃ e ∈ P.edges, P.tgt ∈ e := by
  obtain ⟨e, he, hx⟩ := P.reverse.exists_edge_at_src
  refine ⟨e, ?_, hx⟩
  have : e ∈ P.reverse.edges := he
  rw [GPath.reverse_edges, List.mem_reverse] at this
  exact this

/-- In a graph of maximum degree at most one, every path is a single edge. -/
theorem Walk.two_le_degree [Fintype W] [DecidableRel G.Adj] :
    ∀ {a b : W} (p : G.Walk a b), p.IsPath → 2 ≤ p.length → ∃ v, 2 ≤ G.degree v
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons _ .nil, _, h => by simp at h
  | a, _, .cons (v := v) h₁ (.cons (v := w) h₂ q), hp, _ => by
    classical
    refine ⟨v, ?_⟩
    have haw : a ≠ w := by
      intro haw
      rw [Walk.cons_isPath_iff] at hp
      apply hp.2
      rw [Walk.support_cons, List.mem_cons]
      right
      rw [haw]
      exact q.start_mem_support
    have hsub : ({a, w} : Finset W) ⊆ G.neighborFinset v := by
      intro y hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rw [mem_neighborFinset]
      rcases hy with rfl | rfl
      · exact h₁.symm
      · exact h₂
    have := Finset.card_le_card hsub
    rw [Finset.card_pair haw, card_neighborFinset_eq_degree] at this
    exact this

theorem GPath.support_of_degree_le_one [Fintype W] [DecidableRel G.Adj] (P : GPath G)
    (hdeg : ∀ v, G.degree v ≤ 1) :
    G.Adj P.src P.tgt ∧ ∀ x ∈ P.walk.support, x = P.src ∨ x = P.tgt := by
  obtain ⟨src, tgt, w, hw, hpos⟩ := P
  cases w with
  | nil => simp at hpos
  | cons h q =>
    cases q with
    | nil =>
      refine ⟨h, fun x hx => ?_⟩
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      exact hx
    | cons h' q' =>
      exfalso
      obtain ⟨v, hv⟩ := Walk.two_le_degree _ hw (by simp)
      have := hdeg v
      omega

end paths

/-! ### Prescribed end edges -/

section endEdge

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- Degree bookkeeping for `H = (G − ux) + leaf at u` when `G` has no positive even vertex. -/
theorem merge_degrees (G : SimpleGraph W) [DecidableRel G.Adj] (hodd : ∀ z, z ∉ evenSet G)
    {x u : W} (hxu : G.Adj x u) :
    (apex (delEdge G u x) {u}).degree none = 1 ∧
    (apex (delEdge G u x) {u}).degree (some x) + 1 = G.degree x ∧
    (∀ w, w ≠ x → (apex (delEdge G u x) {u}).degree (some w) = G.degree w) ∧
    G.degree x % 2 = 1 ∧ evenSet (apex (delEdge G u x) {u}) ⊆ {some x} := by
  have hux : G.Adj u x := hxu.symm
  have hne : u ≠ x := hux.ne
  have hpar : ∀ w, 0 < G.degree w → G.degree w % 2 = 1 := fun w hw => by
    have := hodd w
    rw [mem_evenSet_iff] at this
    omega
  have hdeg := delEdge_degree G hux
  have hHsome : ∀ w, (apex (delEdge G u x) {u}).degree (some w) =
      (delEdge G u x).degree w + (if w = u then 1 else 0) := by
    intro w
    rw [apex_degree_some]
    simp [Finset.mem_singleton]
  have hHnone : (apex (delEdge G u x) {u}).degree none = 1 := by
    rw [apex_degree_none]; simp
  have hxpos : 0 < G.degree x := (G.degree_pos_iff_exists_adj x).mpr ⟨u, hxu⟩
  have hx1 : (apex (delEdge G u x) {u}).degree (some x) + 1 = G.degree x := by
    rw [hHsome]
    have := hdeg x
    simp only [hne.symm, ite_false, ite_true, add_zero] at this ⊢
    omega
  have hw : ∀ w, w ≠ x → (apex (delEdge G u x) {u}).degree (some w) = G.degree w := by
    intro w hwx
    rw [hHsome]
    have := hdeg w
    simp only [hwx, ite_false, add_zero] at this
    by_cases hwu : w = u
    · subst hwu; simp only [ite_true] at this ⊢; omega
    · simp only [hwu, ite_false, add_zero] at this ⊢; omega
  refine ⟨hHnone, hx1, hw, hpar x hxpos, ?_⟩
  intro w hw'
  rw [mem_evenSet_iff] at hw'
  rw [Finset.mem_singleton]
  cases w with
  | none => rw [hHnone] at hw'; omega
  | some y =>
    by_contra hyx
    have hyx' : y ≠ x := fun h => hyx (h ▸ rfl)
    rw [hw y hyx'] at hw'
    have := hpar y hw'.1
    omega

/-- Lifting packedness to `H`: `A` (if `x ∉ A`) or `A ∪ {leaf}` (if `x ∈ A`). -/
theorem packed_lift (G : SimpleGraph W) {x u : W} (hxu : G.Adj x u) {A : Finset W}
    (hA : Packed G A) :
    Packed (apex (delEdge G u x) {u})
      (if x ∈ A then insert none (A.image some) else A.image some) := by
  have hsome : ∀ p ∈ A, ∀ q ∈ A, p ≠ q →
      ¬ (apex (delEdge G u x) {u}).Adj (some p) (some q) ∧
      ∀ w, ¬ ((apex (delEdge G u x) {u}).Adj (some p) w ∧
        (apex (delEdge G u x) {u}).Adj w (some q)) := by
    intro p hp q hq hpq
    refine ⟨fun h => (hA p hp q hq hpq).1 h.1, fun w hw => ?_⟩
    cases w with
    | none =>
      obtain ⟨h1, h2⟩ := hw
      rw [apex_adj_some_none, Finset.mem_singleton] at h1
      rw [apex_adj_none_some, Finset.mem_singleton] at h2
      exact hpq (h1.trans h2.symm)
    | some w' => exact (hA p hp q hq hpq).2 w' ⟨hw.1.1, hw.2.1⟩
  split_ifs with hxA
  · -- the leaf against `some q`, `q ∈ A`
    have hleaf : ∀ q ∈ A, ¬ (apex (delEdge G u x) {u}).Adj none (some q) ∧
        ∀ w, ¬ ((apex (delEdge G u x) {u}).Adj none w ∧
          (apex (delEdge G u x) {u}).Adj w (some q)) := by
      intro q hq
      refine ⟨fun h => ?_, fun w hw => ?_⟩
      · rw [apex_adj_none_some, Finset.mem_singleton] at h
        subst h
        by_cases hqx : q = x
        · subst hqx; exact hxu.ne rfl
        · exact (hA x hxA q hq (Ne.symm hqx)).1 hxu
      · cases w with
        | none => exact apex_not_adj_none_none hw.1
        | some w' =>
          obtain ⟨h1, h2⟩ := hw
          rw [apex_adj_none_some, Finset.mem_singleton] at h1
          subst h1
          rw [apex_adj_some_some] at h2
          by_cases hqx : q = x
          · subst hqx
            exact h2.2 rfl
          · exact (hA x hxA q hq (Ne.symm hqx)).2 w' ⟨hxu, h2.1⟩
    intro p hp q hq hpq
    rw [Finset.mem_insert, Finset.mem_image] at hp hq
    rcases hp with rfl | ⟨p', hp', rfl⟩ <;> rcases hq with rfl | ⟨q', hq', rfl⟩
    · exact absurd rfl hpq
    · exact hleaf q' hq'
    · refine ⟨fun h => (hleaf p' hp').1 h.symm, fun w hw => (hleaf p' hp').2 w ⟨hw.2.symm, hw.1.symm⟩⟩
    · exact hsome p' hp' q' hq' (fun h => hpq (h ▸ rfl))
  · intro p hp q hq hpq
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
    exact hsome p' hp' q' hq' (fun h => hpq (h ▸ rfl))

/-- `MeetsOnce` descends through the merge. -/
theorem meetsOnce_merge {G : SimpleGraph W} {x : W} {H : SimpleGraph (Option W)}
    {DH : PathDecomp H} {D : PathDecomp G}
    (hcov : ∀ Q ∈ D.paths, ∃ P ∈ DH.paths, Q.walk.support = P.walk.support.map (mergeMap x))
    {A : Finset W}
    (hA : MeetsOnce DH (if x ∈ A then insert none (A.image some) else A.image some)) :
    MeetsOnce D A := by
  intro Q hQ a ha b hb haQ hbQ
  obtain ⟨P, hP, hsupp⟩ := hcov Q hQ
  rw [hsupp, List.mem_map] at haQ hbQ
  obtain ⟨a', ha'P, rfl⟩ := haQ
  obtain ⟨b', hb'P, rfl⟩ := hbQ
  have hmem : ∀ c : Option W, mergeMap x c ∈ A →
      c ∈ (if x ∈ A then insert none (A.image some) else A.image some) := by
    intro c hc
    cases c with
    | none =>
      simp only [mergeMap_none] at hc
      simp [hc]
    | some c =>
      simp only [mergeMap_some] at hc
      split_ifs <;> simp [hc]
  rw [hA P hP a' (hmem a' ha) b' (hmem b' hb) ha'P hb'P]

/-- **Prescribed end edge.** If every vertex of `G` has odd degree or degree zero, `X` is packed
and `x ∈ X`, then for every edge `xu` some Lovász decomposition meets `X` at most once per path,
and its path ending at `x` contains `xu`. -/
theorem lovasz_endEdge_set (G : SimpleGraph W) [DecidableRel G.Adj]
    (hodd : ∀ z, z ∉ evenSet G) {X : Finset W} (hX : Packed G X) {x u : W} (hxX : x ∈ X)
    (hxu : G.Adj x u) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ MeetsOnce D X ∧
      ∃ P ∈ D.paths, (P.src = x ∨ P.tgt = x) ∧ s(x, u) ∈ P.edges := by
  obtain ⟨hHnone, hHx, hHw, hxodd, hevH⟩ := merge_degrees G hodd hxu
  have hcardH : (evenSet (apex (delEdge G u x) {u})).card ≤ 1 :=
    (Finset.card_le_card hevH).trans (by simp)
  have hXH := packed_lift G hxu hX
  rw [if_pos hxX] at hXH
  obtain ⟨DH, hDH, hmeet⟩ := separation_set _ hcardH hXH
  have hsep : Separates DH (some x) none := by
    intro P hP ⟨h1, h2⟩
    have := hmeet P hP (some x) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hxX))
      none (Finset.mem_insert_self _ _) h1 h2
    exact Option.some_ne_none _ this
  obtain ⟨D, hDx, hDw, hcov, hfwd⟩ := leaf_merge G hxu DH hsep
  refine ⟨D, fun v => ?_, ?_, ?_⟩
  · by_cases hvx : v = x
    · subst hvx
      rw [hDx, hDH, hDH, hHnone]
      omega
    · rw [hDw v hvx, hDH, hHw v hvx]
  · have : MeetsOnce DH (if x ∈ X then insert none (X.image some) else X.image some) := by
      rw [if_pos hxX]; exact hmeet
    exact meetsOnce_merge hcov this
  · -- the path through the leaf
    have hpos : 0 < DH.ends none := by rw [hDH, hHnone]; omega
    obtain ⟨P, hP, hPend⟩ := DH.exists_end_of_pos hpos
    obtain ⟨Q, hQ, hQs, hQt, hQe⟩ := hfwd P hP
    have hleaf : s(some u, none) ∈ P.edges := by
      have key : ∀ e ∈ P.edges, (none : Option W) ∈ e → s(some u, none) ∈ P.edges := by
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

/-- **Prescribed end edge**, without a packed set. -/
theorem lovasz_endEdge (G : SimpleGraph W) [DecidableRel G.Adj]
    (hodd : ∀ z, z ∉ evenSet G) {x u : W} (hxu : G.Adj x u) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∃ P ∈ D.paths, (P.src = x ∨ P.tgt = x) ∧ s(x, u) ∈ P.edges := by
  have hX : Packed G {x} := by
    intro p hp q hq hpq
    rw [Finset.mem_singleton] at hp hq
    exact absurd (hp.trans hq.symm) hpq
  obtain ⟨D, hD, -, hP⟩ := lovasz_endEdge_set G hodd hX (Finset.mem_singleton_self x) hxu
  exact ⟨D, hD, hP⟩

end endEdge

/-! ### Class separation -/

section classSep

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- A family of pairwise disjoint packed sets ("classes"). -/
def ClassFam (G : SimpleGraph W) (𝒜 : Finset (Finset W)) : Prop :=
  (∀ A ∈ 𝒜, Packed G A) ∧ ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → Disjoint A B

/-- **Class separation** for `G`: for every family of pairwise disjoint packed sets there is a
Lovász decomposition meeting each of them at most once per path. (For overlapping families the
statement is false in general.) -/
def ClassSep (G : SimpleGraph W) [DecidableRel G.Adj] : Prop :=
  ∀ 𝒜 : Finset (Finset W), ClassFam G 𝒜 →
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ ∀ A ∈ 𝒜, MeetsOnce D A

/-- **Case II costs nothing (one instance).** Let `G` have no vertex of positive even degree, let
`xu` be an edge, and `H = (G − ux) + leaf at u`. If `H` has a Lovász decomposition meeting every
lifted class (`A`, or `A ∪ {leaf}` when `x ∈ A`) at most once per path, and no path contains both
`x` and the leaf, then `G` has a Lovász decomposition meeting every class at most once per path. -/
theorem caseII_lift (G : SimpleGraph W) [DecidableRel G.Adj] (hodd : ∀ z, z ∉ evenSet G)
    {x u : W} (hxu : G.Adj x u) (𝒜 : Finset (Finset W))
    (DH : PathDecomp (apex (delEdge G u x) {u}))
    (hDH : ∀ v, DH.ends v = (apex (delEdge G u x) {u}).degree v % 2)
    (hsep : Separates DH (some x) none)
    (hmeet : ∀ A ∈ 𝒜, MeetsOnce DH (if x ∈ A then insert none (A.image some) else A.image some)) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ ∀ A ∈ 𝒜, MeetsOnce D A := by
  obtain ⟨hHnone, hHx, hHw, hxodd, -⟩ := merge_degrees G hodd hxu
  obtain ⟨D, hDx, hDw, hcov, -⟩ := leaf_merge G hxu DH hsep
  refine ⟨D, fun v => ?_, fun A hA => meetsOnce_merge hcov (hmeet A hA)⟩
  by_cases hvx : v = x
  · subst hvx
    rw [hDx, hDH, hDH, hHnone]
    omega
  · rw [hDw v hvx, hDH, hHw v hvx]

/-- **Case II costs nothing.** If class separation holds for every graph with exactly one vertex
of positive even degree, it holds for every graph with none: the new leaf of Lovász's Case II
joins the class of `x`, and the merge `leaf ↦ x` is the lift. -/
theorem classSep_allOdd
    (h1 : ∀ (W' : Type u) [Fintype W'] [DecidableEq W'] (G' : SimpleGraph W')
      [DecidableRel G'.Adj], (evenSet G').card = 1 → ClassSep G')
    (G : SimpleGraph W) [DecidableRel G.Adj] (hodd : ∀ z, z ∉ evenSet G) : ClassSep G := by
  intro 𝒜 h𝒜
  by_cases hbig : ∃ x, 3 ≤ G.degree x
  · obtain ⟨x, hx⟩ := hbig
    obtain ⟨u, hxu⟩ := (G.degree_pos_iff_exists_adj x).mp (by omega)
    obtain ⟨hHnone, hHx, hHw, hxodd, hevH⟩ := merge_degrees G hodd hxu
    have hxH : some x ∈ evenSet (apex (delEdge G u x) {u}) := by
      rw [mem_evenSet_iff]; omega
    have hcardH : (evenSet (apex (delEdge G u x) {u})).card = 1 := by
      have h := Finset.card_le_card hevH
      have h' : 0 < (evenSet (apex (delEdge G u x) {u})).card := Finset.card_pos.mpr ⟨_, hxH⟩
      simp at h; omega
    let lift : Finset W → Finset (Option W) := fun A =>
      if x ∈ A then insert none (A.image some) else A.image some
    have hlift_some : ∀ A a, some a ∈ lift A ↔ a ∈ A := by
      intro A a
      simp only [lift]
      split_ifs <;> simp
    have hlift_none : ∀ A, none ∈ lift A ↔ x ∈ A := by
      intro A
      simp only [lift]
      split_ifs with h <;> simp [h]
    have hpx : Packed G {x} := by
      intro p hp q hq hpq
      rw [Finset.mem_singleton] at hp hq
      exact absurd (hp.trans hq.symm) hpq
    have hpair : Packed (apex (delEdge G u x) {u}) ({some x, none} : Finset (Option W)) := by
      have := packed_lift G hxu hpx
      rw [if_pos (Finset.mem_singleton_self x)] at this
      have he : (insert none (({x} : Finset W).image some)) = ({some x, none} : Finset _) := by
        ext c; cases c <;> simp
      rw [he] at this
      exact this
    by_cases hxin : ∃ A ∈ 𝒜, x ∈ A
    · -- `x` lies in a class: lift every class
      obtain ⟨A₀, hA₀, hxA₀⟩ := hxin
      have hfam : ClassFam (apex (delEdge G u x) {u}) (𝒜.image lift) := by
        refine ⟨fun B hB => ?_, fun B₁ hB₁ B₂ hB₂ hne => ?_⟩
        · obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
          exact packed_lift G hxu (h𝒜.1 A hA)
        · obtain ⟨A₁, hA₁, rfl⟩ := Finset.mem_image.mp hB₁
          obtain ⟨A₂, hA₂, rfl⟩ := Finset.mem_image.mp hB₂
          have hA : A₁ ≠ A₂ := fun h => hne (h ▸ rfl)
          have hd := h𝒜.2 A₁ hA₁ A₂ hA₂ hA
          rw [Finset.disjoint_left]
          intro c hc1 hc2
          cases c with
          | none =>
            rw [hlift_none] at hc1 hc2
            exact Finset.disjoint_left.mp hd hc1 hc2
          | some a =>
            rw [hlift_some] at hc1 hc2
            exact Finset.disjoint_left.mp hd hc1 hc2
      obtain ⟨DH, hDH, hmeet⟩ := h1 (Option W) (apex (delEdge G u x) {u}) hcardH _ hfam
      have hsep : Separates DH (some x) none := by
        intro P hP ⟨h1', h2'⟩
        have := hmeet _ (Finset.mem_image_of_mem _ hA₀) P hP (some x) ((hlift_some _ _).2 hxA₀)
          none ((hlift_none _).2 hxA₀) h1' h2'
        exact Option.some_ne_none _ this
      exact caseII_lift G hodd hxu 𝒜 DH hDH hsep
        (fun A hA => hmeet _ (Finset.mem_image_of_mem _ hA))
    · -- `x` lies in no class: add the class `{x, leaf}`
      push_neg at hxin
      have hfam : ClassFam (apex (delEdge G u x) {u})
          (insert {some x, none} (𝒜.image lift)) := by
        refine ⟨fun B hB => ?_, fun B₁ hB₁ B₂ hB₂ hne => ?_⟩
        · rw [Finset.mem_insert, Finset.mem_image] at hB
          rcases hB with rfl | ⟨A, hA, rfl⟩
          · exact hpair
          · exact packed_lift G hxu (h𝒜.1 A hA)
        · have hdisj : ∀ A ∈ 𝒜, Disjoint ({some x, none} : Finset (Option W)) (lift A) := by
            intro A hA
            rw [Finset.disjoint_left]
            intro c hc1 hc2
            rw [Finset.mem_insert, Finset.mem_singleton] at hc1
            rcases hc1 with rfl | rfl
            · exact hxin A hA ((hlift_some _ _).1 hc2)
            · exact hxin A hA ((hlift_none _).1 hc2)
          rw [Finset.mem_insert, Finset.mem_image] at hB₁ hB₂
          rcases hB₁ with rfl | ⟨A₁, hA₁, rfl⟩ <;> rcases hB₂ with rfl | ⟨A₂, hA₂, rfl⟩
          · exact absurd rfl hne
          · exact hdisj A₂ hA₂
          · exact (hdisj A₁ hA₁).symm
          · have hA : A₁ ≠ A₂ := fun h => hne (h ▸ rfl)
            have hd := h𝒜.2 A₁ hA₁ A₂ hA₂ hA
            rw [Finset.disjoint_left]
            intro c hc1 hc2
            cases c with
            | none =>
              rw [hlift_none] at hc1 hc2
              exact Finset.disjoint_left.mp hd hc1 hc2
            | some a =>
              rw [hlift_some] at hc1 hc2
              exact Finset.disjoint_left.mp hd hc1 hc2
      obtain ⟨DH, hDH, hmeet⟩ := h1 (Option W) (apex (delEdge G u x) {u}) hcardH _ hfam
      have hsep : Separates DH (some x) none := by
        intro P hP ⟨h1', h2'⟩
        have := hmeet _ (Finset.mem_insert_self _ _) P hP (some x) (by simp) none (by simp) h1' h2'
        exact Option.some_ne_none _ this
      exact caseII_lift G hodd hxu 𝒜 DH hDH hsep
        (fun A hA => hmeet _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hA)))
  · -- every degree is at most one: every path is a single edge
    push_neg at hbig
    have hle : ∀ v, G.degree v ≤ 1 := by
      intro v
      have h := hodd v
      rw [mem_evenSet_iff] at h
      have := hbig v
      omega
    have hcard : (evenSet G).card ≤ 1 := by
      rw [Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem hodd)]; omega
    obtain ⟨D, hD⟩ := lovasz_ends G hcard
    refine ⟨D, hD, fun A hA P hP a ha b hb haP hbP => ?_⟩
    obtain ⟨hadj, hsupp⟩ := P.support_of_degree_le_one hle
    by_contra hab
    rcases hsupp a haP with rfl | rfl <;> rcases hsupp b hbP with rfl | rfl
    · exact hab rfl
    · exact (h𝒜.1 A hA _ ha _ hb hab).1 hadj
    · exact (h𝒜.1 A hA _ ha _ hb hab).1 hadj.symm
    · exact hab rfl

/-- **Certified Case I.** Let `z` be the vertex of positive even degree and `u` a neighbour. If
`G − uz` has a Lovász decomposition `D'` meeting `{u, z}` at most once per path, meeting
`A ∪ {z}` at most once per path for every class `A ∋ u`, and meeting every other class at most
once per path, then appending `zu` to the path ending at `z` gives a Lovász decomposition of `G`
meeting every class at most once per path. -/
theorem classSep_caseI (G : SimpleGraph W) [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1)
    {z u : W} (hz : z ∈ evenSet G) (hzu : G.Adj z u) (𝒜 : Finset (Finset W))
    (h𝒜 : ∀ A ∈ 𝒜, Packed G A) (D' : PathDecomp (delEdge G u z))
    (hD' : ∀ v, D'.ends v = (delEdge G u z).degree v % 2)
    (hin : ∀ A ∈ 𝒜, u ∈ A → MeetsOnce D' (insert z A))
    (hout : ∀ A ∈ 𝒜, u ∉ A → MeetsOnce D' A) (huz : MeetsOnce D' {u, z}) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ ∀ A ∈ 𝒜, MeetsOnce D A := by
  have huz' : G.Adj u z := hzu.symm
  have hne : u ≠ z := huz'.ne
  have hzd := mem_evenSet_iff.mp hz
  have hdeg := delEdge_degree G huz'
  have hupos : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).mpr ⟨z, huz'⟩
  have huniq : ∀ w ∈ evenSet G, w = z := fun w hw => Finset.card_le_one.mp hev w hw z hz
  have huodd : G.degree u % 2 = 1 := by
    have : u ∉ evenSet G := fun h => hne (huniq u h)
    rw [mem_evenSet_iff] at this
    omega
  have hdu := hdeg u
  have hdz := hdeg z
  simp only [hne, hne.symm, ite_true, ite_false, add_zero] at hdu hdz
  -- the path ending at `z`
  have hzpos : 0 < D'.ends z := by rw [hD']; omega
  obtain ⟨P, hP, hPend⟩ := D'.exists_end_of_pos hzpos
  have hzP : z ∈ P.walk.support := by
    have key : ∀ y, P.src = y ∨ P.tgt = y → y ∈ P.walk.support := by
      rintro y (rfl | rfl)
      · exact P.walk.start_mem_support
      · exact P.walk.end_mem_support
    exact key z hPend
  have huP : u ∉ P.walk.support := fun h =>
    hne (huz P hP u (by simp) z (by simp) h hzP)
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
  -- append `zu`, keeping track of supports
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
  have hP'supp : ∀ y, y ∈ P'.walk.support ↔ y = u ∨ y ∈ P.walk.support := by
    intro y
    show y ∈ (Walk.cons hut (Q.walk.transfer G hQK)).support ↔ _
    rw [Walk.support_cons, Walk.support_transfer, List.mem_cons, hQsupp]
  have hPK : ∀ e ∈ P.edges, e ∈ (delEdge G u z).edgeSet := fun e he =>
    P.walk.edges_subset_edgeSet he
  have hzuK : s(z, u) ∉ (delEdge G u z).edgeSet := hadj
  obtain ⟨D, -, -, hends, -, hcovr⟩ := D'.replace_supp hP P' (by
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
  refine ⟨D, fun w => ?_, fun A hA => ?_⟩
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
  · intro R hR a ha b hb haR hbR
    have hzA : u ∈ A → z ∉ A := fun huA hzA =>
      (h𝒜 A hA u huA z hzA hne).1 huz'
    rcases hcovr R hR with rfl | ⟨S, hS, hRS⟩
    · rw [hP'supp] at haR hbR
      by_cases huA : u ∈ A
      · have hP1 := hin A hA huA P hP
        have key : ∀ c ∈ A, c = u ∨ c ∈ P.walk.support → c = u := by
          intro c hc hcR
          rcases hcR with h | h
          · exact h
          · exfalso
            have := hP1 c (Finset.mem_insert_of_mem hc) z (Finset.mem_insert_self _ _) h hzP
            subst this
            exact hzA huA hc
        rw [key a ha haR, key b hb hbR]
      · have ha' : a ∈ P.walk.support := haR.resolve_left (fun h => huA (h ▸ ha))
        have hb' : b ∈ P.walk.support := hbR.resolve_left (fun h => huA (h ▸ hb))
        exact hout A hA huA P hP a ha b hb ha' hb'
    · rw [hRS] at haR hbR
      by_cases huA : u ∈ A
      · exact hin A hA huA S hS a (Finset.mem_insert_of_mem ha) b
          (Finset.mem_insert_of_mem hb) haR hbR
      · exact hout A hA huA S hS a ha b hb haR hbR

end classSep


/-! ### Several classes whose union is sparse -/

section sparse

variable {W : Type u}

/-- Every path of `D` meets every set of `𝒜` at most once. -/
def MeetsAll {G : SimpleGraph W} (D : PathDecomp G) (𝒜 : Finset (Finset W)) : Prop :=
  ∀ A ∈ 𝒜, MeetsOnce D A

/-- A family of packed sets contained in `X`, where every vertex has at most one neighbour in
`X`. -/
structure SparseFam (G : SimpleGraph W) (X : Finset W) (𝒜 : Finset (Finset W)) : Prop where
  packed : ∀ A ∈ 𝒜, Packed G A
  sub : ∀ A ∈ 𝒜, A ⊆ X
  one : ∀ v p q, G.Adj v p → G.Adj v q → p ∈ X → q ∈ X → p = q

variable {X : Finset W} {𝒜 : Finset (Finset W)}

theorem SparseFam.mono {G H : SimpleGraph W} (h : SparseFam G X 𝒜)
    (hle : ∀ x y, H.Adj x y → G.Adj x y) : SparseFam H X 𝒜 :=
  ⟨fun A hA => (h.packed A hA).mono hle, h.sub,
    fun v p q hp hq => h.one v p q (hle _ _ hp) (hle _ _ hq)⟩

/-- `MeetsAll` passes to a decomposition whose paths lie in old paths plus a vertex `g ∉ X`. -/
theorem meetsAll_of_cover {G G' : SimpleGraph W} {D : PathDecomp G} {D' : PathDecomp G'}
    (hsub : ∀ A ∈ 𝒜, A ⊆ X) {g : W} (hg : g ∉ X) (hD' : MeetsAll D' 𝒜)
    (hcov : ∀ Q ∈ D.paths, ∃ Q' ∈ D'.paths, ∀ x ∈ Q.walk.support, x ∈ Q'.walk.support ∨ x = g) :
    MeetsAll D 𝒜 := fun A hA =>
  meetsOnce_of_cover (fun h => hg (hsub A hA h)) (hD' A hA) hcov

theorem SparseFam.exists_adj_not_mem [Fintype W] {G : SimpleGraph W} [DecidableRel G.Adj]
    (hX : SparseFam G X 𝒜) {z : W} (hz : 2 ≤ G.degree z) : ∃ u, G.Adj z u ∧ u ∉ X := by
  classical
  by_contra hno
  simp only [not_exists, not_and, not_not] at hno
  have h1 : 1 < (G.neighborFinset z).card := by rw [card_neighborFinset_eq_degree]; omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h1
  rw [mem_neighborFinset] at hp hq
  exact hpq (hX.one z p q hp hq (hno p hp) (hno q hq))

/-- The statement proved by strong induction on `n = ν(G)`. -/
def SpStrong (n : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (X : Finset W) (𝒜 : Finset (Finset W)), (evenSet G).card ≤ 1 → SparseFam G X 𝒜 →
    (∑ w, G.degree w) + (if (evenSet G).card = 0 then 1 else 0) = n →
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ MeetsAll D 𝒜

variable [Fintype W] [DecidableEq W]

/-- Case I: there is a vertex of positive even degree. -/
theorem sp_case_even {n : ℕ} (ih : ∀ m < n, SpStrong.{u} m)
    (G : SimpleGraph W) [DecidableRel G.Adj] {X : Finset W} (hev : (evenSet G).card ≤ 1)
    (hfar : SparseFam G X 𝒜)
    (hn : (∑ w, G.degree w) + (if (evenSet G).card = 0 then 1 else 0) = n)
    {z : W} (hz : z ∈ evenSet G) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ MeetsAll D 𝒜 := by
  have hzd := mem_evenSet_iff.mp hz
  obtain ⟨u, hzu, huX⟩ := hfar.exists_adj_not_mem (by omega : 2 ≤ G.degree z)
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
  have hev' : evenSet (delEdge G u z) ⊆ {u} := by
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
  have hcard' : (evenSet (delEdge G u z)).card ≤ 1 :=
    (Finset.card_le_card hev').trans (by simp)
  have hsum := delEdge_sum_degree G huz
  have hlt : (∑ w, (delEdge G u z).degree w) +
      (if (evenSet (delEdge G u z)).card = 0 then 1 else 0) < n := by
    have : (evenSet G).card ≠ 0 := Finset.card_ne_zero.mpr ⟨z, hz⟩
    simp only [this, ite_false, add_zero] at hn
    split_ifs <;> omega
  have hfar' : SparseFam (delEdge G u z) X 𝒜 := hfar.mono (fun _ _ h => h.1)
  obtain ⟨D', hD', hsep'⟩ := ih _ hlt W (delEdge G u z) X 𝒜 hcard' hfar' rfl
  have hD'z : D'.ends z = 1 := by rw [hD' z]; omega
  obtain ⟨D, -, hDu, hDz, hDo, hcov⟩ := fan_single_supp huz (delEdge_edgeSet G u z) D' (by
    rw [hD'z]
    have : Finset.univ.filter (fun w => (delEdge G u z).Adj u w ∧ D'.ends w = 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro w - ⟨hadj, h0⟩
      have hwu : w ≠ u := hadj.ne.symm
      have hpos : 0 < (delEdge G u z).degree w :=
        ((delEdge G u z).degree_pos_iff_exists_adj w).mpr ⟨u, hadj.symm⟩
      rw [hD' w] at h0
      exact hwu (Finset.mem_singleton.mp (hev' (mem_evenSet_iff.mpr ⟨hpos, h0⟩)))
    rw [this, Finset.card_empty]
    exact Nat.one_pos)
  refine ⟨D, fun w => ?_, meetsAll_of_cover hfar.sub huX hsep' hcov⟩
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

/-- Case II: every vertex of positive degree is odd and some `x ∉ {c, a}` has degree `≥ 3`. -/
theorem sp_case_big {n : ℕ} (ih : ∀ m < n, SpStrong.{u} m)
    (G : SimpleGraph W) [DecidableRel G.Adj] {X : Finset W} (hfar : SparseFam G X 𝒜)
    (hn : (∑ w, G.degree w) + (if (evenSet G).card = 0 then 1 else 0) = n)
    (hnone : ∀ z, z ∉ evenSet G) {x : W} (hxX : x ∉ X) (hx : 3 ≤ G.degree x) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ MeetsAll D 𝒜 := by
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
  have hHsome : ∀ w, (apex (delEdge G u x) {u}).degree (some w) =
      (delEdge G u x).degree w + (if w = u then 1 else 0) := by
    intro w
    rw [apex_degree_some]
    simp [Finset.mem_singleton]
  have hHnone : (apex (delEdge G u x) {u}).degree none = 1 := by
    rw [apex_degree_none]; simp
  have hevH : evenSet (apex (delEdge G u x) {u}) ⊆ {some x} := by
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
  have hxH : some x ∈ evenSet (apex (delEdge G u x) {u}) := by
    rw [mem_evenSet_iff, hHsome]
    simp only [hne.symm, ite_false, add_zero]
    omega
  have hcardH : (evenSet (apex (delEdge G u x) {u})).card ≤ 1 :=
    (Finset.card_le_card hevH).trans (by simp)
  have hsumH : ∑ w, (apex (delEdge G u x) {u}).degree w = ∑ w, G.degree w := by
    rw [Fintype.sum_option, hHnone, ← delEdge_sum_degree G hux]
    simp only [hHsome, Finset.sum_add_distrib]
    simp
    omega
  have hlt : (∑ w, (apex (delEdge G u x) {u}).degree w) +
      (if (evenSet (apex (delEdge G u x) {u})).card = 0 then 1 else 0) < n := by
    have h1 : (evenSet (apex (delEdge G u x) {u})).card ≠ 0 :=
      Finset.card_ne_zero.mpr ⟨_, hxH⟩
    have h2 : (evenSet G).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem hnone)
    simp only [h2, ite_true] at hn
    simp only [h1, ite_false, add_zero, hsumH]
    omega
  have hfarH : SparseFam (apex (delEdge G u x) {u}) (X.image some)
      (𝒜.image (fun A => A.image some)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro B hB
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
      intro p hp q hq hpq
      obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
      have hpq' : p' ≠ q' := fun h => hpq (h ▸ rfl)
      have hfA := hfar.packed A hA
      refine ⟨fun h => (hfA p' hp' q' hq' hpq').1 h.1, fun w hw => ?_⟩
      cases w with
      | none =>
        obtain ⟨h1, h2⟩ := hw
        rw [apex_adj_some_none, Finset.mem_singleton] at h1
        rw [apex_adj_none_some, Finset.mem_singleton] at h2
        exact hpq' (h1.trans h2.symm)
      | some w' => exact (hfA p' hp' q' hq' hpq').2 w' ⟨hw.1.1, hw.2.1⟩
    · intro B hB
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
      exact Finset.image_subset_image (hfar.sub A hA)
    · intro v p q hp hq hpX hqX
      obtain ⟨p', -, rfl⟩ := Finset.mem_image.mp hpX
      obtain ⟨q', -, rfl⟩ := Finset.mem_image.mp hqX
      cases v with
      | none =>
        rw [apex_adj_none_some, Finset.mem_singleton] at hp hq
        rw [hp, hq]
      | some v' =>
        rw [apex_adj_some_some] at hp hq
        rw [hfar.one v' p' q' hp.1 hq.1 (by
          obtain ⟨p'', hp'', h⟩ := Finset.mem_image.mp hpX; exact Option.some.inj h ▸ hp'')
          (by obtain ⟨q'', hq'', h⟩ := Finset.mem_image.mp hqX; exact Option.some.inj h ▸ hq'')]
  obtain ⟨DH, hDH, hsepH⟩ :=
    ih _ hlt (Option W) (apex (delEdge G u x) {u}) (X.image some)
      (𝒜.image (fun A => A.image some)) hcardH hfarH rfl
  -- delete the new leaf
  obtain ⟨D', hD', hcovD'⟩ := (apexRetract (delEdge G u x) {u} x).delete_supp DH (by
    intro P _ y hy hky
    cases y with
    | some _ => simp [apexRetract] at hky
    | none => exact (P.end_of_pendant apex_none_pendant hy).imp Eq.symm Eq.symm)
  have hsep' : MeetsAll D' 𝒜 := by
    intro A hA Q hQ p hp q hq hpQ hqQ
    obtain ⟨P, hP, hPs⟩ := hcovD' Q hQ
    exact Option.some.inj (hsepH _ (Finset.mem_image_of_mem _ hA) P hP (some p)
      (Finset.mem_image_of_mem _ hp) (some q)
      (Finset.mem_image_of_mem _ hq) (hPs p hpQ) (hPs q hqQ))
  have hD'w : ∀ w, w ≠ u → D'.ends w = (delEdge G u x).degree w % 2 := by
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
    obtain ⟨D, hD, hcovD⟩ := PathDecomp.add_edge_supp hux (delEdge_edgeSet G u x) D'
    refine ⟨D, fun w => ?_, ?_⟩
    · rw [hD w]
      by_cases hwu : w = u
      · subst hwu
        simp only [h0, Ne.symm hne, ite_true, ite_false]
        omega
      · rw [hD'w w hwu]
        by_cases hwx : w = x
        · subst hwx
          simp only [Ne.symm hwu, ite_true, ite_false]
          omega
        · have h := hdeg w
          simp only [hwu, hwx, Ne.symm hwu, Ne.symm hwx, ite_false, add_zero] at h ⊢
          rw [h]
    · intro A hA Q hQ p hp q hq hpQ hqQ
      rcases hcovD Q hQ with hsmall | ⟨Q', hQ', hs⟩
      · rcases hsmall p hpQ with h1 | h1
        · rcases hsmall q hqQ with h2 | h2
          · exact h1.trans h2.symm
          · exact absurd (hfar.sub A hA (h2 ▸ hq)) hxX
        · exact absurd (hfar.sub A hA (h1 ▸ hp)) hxX
      · exact hsep' A hA Q' hQ' p hp q hq (hs p hpQ) (hs q hqQ)
  · -- `u` has two ends: Fan's transfer `u → x`
    have hG'x : ∀ e, e ∈ (delEdge G u x).edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(x, u) := by
      intro e
      rw [delEdge_edgeSet, Sym2.eq_swap]
    obtain ⟨D, -, hDx, hDu, hDo, hcov⟩ := fan_single_supp hxu hG'x D' (by
      rw [h2]
      have : Finset.univ.filter (fun w => (delEdge G u x).Adj x w ∧ D'.ends w = 0) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        rintro w - ⟨hadj, h0⟩
        by_cases hwu : w = u
        · subst hwu; omega
        · have hwx : w ≠ x := hadj.ne.symm
          have hpos : 0 < (delEdge G u x).degree w :=
            ((delEdge G u x).degree_pos_iff_exists_adj w).mpr ⟨x, hadj.symm⟩
          have h := hdeg w
          simp only [hwu, hwx, ite_false, add_zero] at h
          rw [hD'w w hwu, h] at h0
          have := hpar w (h ▸ hpos)
          omega
      rw [this, Finset.card_empty]
      omega)
    refine ⟨D, fun w => ?_, meetsAll_of_cover hfar.sub hxX hsep' hcov⟩
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

/-- Case III: all degrees odd or zero, every vertex outside `{c, a}` has degree `< 3`, and some
vertex `v ∉ {c, a}` has positive degree (so it is a leaf). -/
theorem sp_case_leaf {n : ℕ} (ih : ∀ m < n, SpStrong.{u} m)
    (G : SimpleGraph W) [DecidableRel G.Adj] {X : Finset W} (hfar : SparseFam G X 𝒜)
    (hn : (∑ w, G.degree w) + (if (evenSet G).card = 0 then 1 else 0) = n)
    (hnone : ∀ z, z ∉ evenSet G) (hsmall : ∀ x, x ∉ X → G.degree x < 3)
    {v : W} (hvX : v ∉ X) (hv : 0 < G.degree v) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ MeetsAll D 𝒜 := by
  obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp hv
  have hne : v ≠ w := hvw.ne
  have hpar : ∀ y, 0 < G.degree y → G.degree y % 2 = 1 := fun y hy => by
    have := hnone y
    rw [mem_evenSet_iff] at this
    omega
  have hwpos : 0 < G.degree w := (G.degree_pos_iff_exists_adj w).mpr ⟨v, hvw.symm⟩
  have hdv1 : G.degree v = 1 := by have := hpar v hv; have := hsmall v hvX; omega
  have hdwo := hpar w hwpos
  have hdeg := delEdge_degree G hvw
  have hdv := hdeg v
  have hdw := hdeg w
  simp only [hne, hne.symm, ite_true, ite_false, add_zero] at hdv hdw
  have hev' : evenSet (delEdge G v w) ⊆ {w} := by
    intro y hy
    rw [Finset.mem_singleton]
    obtain ⟨hpos, heven⟩ := mem_evenSet_iff.mp hy
    by_contra hyw
    by_cases hyv : y = v
    · subst hyv; omega
    · have h := hdeg y
      simp only [hyv, hyw, ite_false, add_zero] at h
      have := hpar y (h ▸ hpos)
      omega
  have hcard' : (evenSet (delEdge G v w)).card ≤ 1 :=
    (Finset.card_le_card hev').trans (by simp)
  have hsum := delEdge_sum_degree G hvw
  have hlt : (∑ y, (delEdge G v w).degree y) +
      (if (evenSet (delEdge G v w)).card = 0 then 1 else 0) < n := by
    have h2 : (evenSet G).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem hnone)
    simp only [h2, ite_true] at hn
    split_ifs <;> omega
  have hfar' : SparseFam (delEdge G v w) X 𝒜 := hfar.mono (fun _ _ h => h.1)
  obtain ⟨D', hD', hsep'⟩ := ih _ hlt W (delEdge G v w) X 𝒜 hcard' hfar' rfl
  obtain ⟨D, hD, hcovD⟩ := PathDecomp.add_edge_supp hvw (delEdge_edgeSet G v w) D'
  refine ⟨D, fun y => ?_, ?_⟩
  · rw [hD y, hD' y]
    by_cases hyv : y = v
    · subst hyv
      simp only [Ne.symm hne, ite_true, ite_false]
      omega
    · by_cases hyw : y = w
      · subst hyw
        simp only [Ne.symm hyv, ite_true, ite_false]
        omega
      · have h := hdeg y
        simp only [hyv, hyw, Ne.symm hyv, Ne.symm hyw, ite_false, add_zero] at h ⊢
        rw [h]
  · intro A hA Q hQ p hp q hq hpQ hqQ
    rcases hcovD Q hQ with hsm | ⟨Q', hQ', hs⟩
    · rcases hsm p hpQ with h1 | h1
      · exact absurd (hfar.sub A hA (h1 ▸ hp)) hvX
      · rcases hsm q hqQ with h2 | h2
        · exact absurd (hfar.sub A hA (h2 ▸ hq)) hvX
        · exact h1.trans h2.symm
    · exact hsep' A hA Q' hQ' p hp q hq (hs p hpQ) (hs q hqQ)

/-- Case IV: no vertex outside `X` has positive degree; then every degree is at most one and
every path is a single edge. -/
theorem sp_case_empty (G : SimpleGraph W) [DecidableRel G.Adj] {X : Finset W}
    (hfar : SparseFam G X 𝒜) (hzero : ∀ x, x ∉ X → G.degree x = 0) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ MeetsAll D 𝒜 := by
  have hinX : ∀ x y, G.Adj x y → x ∈ X := by
    intro x y hxy
    by_contra hx
    have := hzero x hx
    have : 0 < G.degree x := (G.degree_pos_iff_exists_adj x).mpr ⟨y, hxy⟩
    omega
  have hle : ∀ v, G.degree v ≤ 1 := by
    intro v
    by_contra h
    have h1 : 1 < (G.neighborFinset v).card := by rw [card_neighborFinset_eq_degree]; omega
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h1
    rw [mem_neighborFinset] at hp hq
    exact hpq (hfar.one v p q hp hq (hinX p v hp.symm) (hinX q v hq.symm))
  have hcard : (evenSet G).card ≤ 1 := by
    have : evenSet G = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro w hw
      rw [mem_evenSet_iff] at hw
      have := hle w
      omega
    rw [this]; simp
  obtain ⟨D, hD⟩ := lovasz_ends G hcard
  refine ⟨D, hD, fun A hA P hP a ha b hb haP hbP => ?_⟩
  obtain ⟨hadj, hsupp⟩ := P.support_of_degree_le_one hle
  by_contra hab
  rcases hsupp a haP with rfl | rfl <;> rcases hsupp b hbP with rfl | rfl
  · exact hab rfl
  · exact (hfar.packed A hA _ ha _ hb hab).1 hadj
  · exact (hfar.packed A hA _ ha _ hb hab).1 hadj.symm
  · exact hab rfl

theorem sp_strong (n : ℕ) : SpStrong.{u} n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W _ _ G _ X 𝒜 hev hfar hn
  by_cases hz : ∃ z, z ∈ evenSet G
  · obtain ⟨z, hz⟩ := hz
    exact sp_case_even ih G hev hfar hn hz
  · simp only [not_exists] at hz
    by_cases hx : ∃ x, x ∉ X ∧ 3 ≤ G.degree x
    · obtain ⟨x, hxX, hx⟩ := hx
      exact sp_case_big ih G hfar hn hz hxX hx
    · have hsmall : ∀ x, x ∉ X → G.degree x < 3 := fun x hxX => by
        by_contra h
        exact hx ⟨x, hxX, by omega⟩
      by_cases hv : ∃ v, v ∉ X ∧ 0 < G.degree v
      · obtain ⟨v, hvX, hv⟩ := hv
        exact sp_case_leaf ih G hfar hn hz hsmall hvX hv
      · have hzero : ∀ x, x ∉ X → G.degree x = 0 := fun x hxX => by
          by_contra h
          exact hv ⟨x, hxX, Nat.pos_of_ne_zero h⟩
        exact sp_case_empty G hfar hzero

end sparse

/-- **Sparse class separation.** Let `G` have at most one vertex of positive even degree, and let
`𝒜` be a family of packed sets (they may overlap) whose union `X` is sparse: every vertex has at
most one neighbour in `X`. Then some Lovász decomposition meets every set of `𝒜` at most once per
path. For `𝒜 = {X}` with `X` packed this is `separation_set`. -/
theorem separation_sparse {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1) {X : Finset W} {𝒜 : Finset (Finset W)}
    (h : SparseFam G X 𝒜) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ ∀ A ∈ 𝒜, MeetsOnce D A :=
  sp_strong _ W G X 𝒜 hev h rfl

end Gallai
