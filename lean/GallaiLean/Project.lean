import GallaiLean.Parity

/-!
# Transporting path decompositions between graphs

The main tool is `PathDecomp.project`: given a decomposition `D` of `G`, a vertex map
`f : V → V'`, and a Boolean predicate `S` selecting the edges of `G` to keep, suppose

* `f` is injective on a set `T` containing every vertex of every kept edge,
* the images of the kept edges are exactly the edges of `G'`, and
* every path `P` of `G` has a *piece*: an optional path of `G'` whose edge list is, up to order,
  the image of the kept edges of `P` (`HasPiece`).

Then `G'` has a decomposition with at most `#{P ∈ D | P has a kept edge}` paths.  Mapping along
an embedding, deleting a pendant edge and the left/right views of a doubled graph are all
instances.

Walk utilities: `pushWalk` (push a walk along a vertex map that sends its edges to edges),
`Walk.exists_append_cons_of_mem_edges` (split a walk at an edge),
`Walk.exists_eq_cons_of_length_pos`.
-/

open SimpleGraph

namespace Gallai

universe u v

variable {V : Type u} {V' : Type v} {G : SimpleGraph V} {G' : SimpleGraph V'}

/-! ### Walk utilities -/

theorem Walk.exists_eq_cons_of_length_pos {a b : V} (p : G.Walk a b) (h : 0 < p.length) :
    ∃ (c : V) (h : G.Adj a c) (q : G.Walk c b), p = Walk.cons h q := by
  cases p with
  | nil => simp at h
  | cons hadj q => exact ⟨_, hadj, q, rfl⟩

/-- Split a walk at an occurrence of an edge. -/
theorem Walk.exists_append_cons_of_mem_edges {a b x y : V} (p : G.Walk a b)
    (h : s(x, y) ∈ p.edges) :
    ∃ (c d : V) (hcd : G.Adj c d) (q : G.Walk a c) (q' : G.Walk d b),
      s(c, d) = s(x, y) ∧ p = q.append (Walk.cons hcd q') := by
  induction p with
  | nil => simp at h
  | @cons a c b hac p ih =>
    rw [Walk.edges_cons, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨a, c, hac, Walk.nil, p, h.symm, rfl⟩
    · obtain ⟨c', d', hcd, q, q', he, rfl⟩ := ih h
      exact ⟨c', d', hcd, Walk.cons hac q, q', he, rfl⟩

theorem Walk.isPath_of_append_left {a b c : V} {p : G.Walk a b} {q : G.Walk b c}
    (h : (p.append q).IsPath) : p.IsPath := by
  rw [Walk.isPath_def, Walk.support_append] at h
  exact Walk.IsPath.mk' (h.sublist (List.sublist_append_left _ _))

theorem Walk.isPath_of_append_right {a b c : V} {p : G.Walk a b} {q : G.Walk b c}
    (h : (p.append q).IsPath) : q.IsPath := by
  have := Walk.isPath_of_append_left (p := q.reverse) (q := p.reverse)
    (by rw [← Walk.reverse_append]; exact h.reverse)
  simpa using this.reverse

/-- Every vertex of an edge of a walk is on the walk. -/
theorem Walk.mem_support_of_mem_edge {a b : V} (p : G.Walk a b) {e : Sym2 V} (he : e ∈ p.edges)
    {x : V} (hx : x ∈ e) : x ∈ p.support := by
  induction e using Sym2.inductionOn with
  | hf y z =>
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · exact p.fst_mem_support_of_mem_edges he
    · exact p.snd_mem_support_of_mem_edges he

/-- Push a walk forward along a vertex map that sends each of its edges to an edge. -/
def pushWalk (f : V → V') : ∀ {a b : V} (p : G.Walk a b),
    (∀ e ∈ p.edges, e.map f ∈ G'.edgeSet) → G'.Walk (f a) (f b)
  | _, _, .nil, _ => .nil
  | _, _, @Walk.cons _ _ a c _ h p, hp =>
    .cons (by have h' : s(a, c).map f ∈ G'.edgeSet := hp _ (by simp)
              simpa using h')
      (pushWalk f p (fun e he => hp e (by simp [he])))

section push

variable (f : V → V')

@[simp] theorem pushWalk_edges {a b : V} (p : G.Walk a b)
    (hp : ∀ e ∈ p.edges, e.map f ∈ G'.edgeSet) :
    (pushWalk f p hp).edges = p.edges.map (Sym2.map f) := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [pushWalk, ih]

@[simp] theorem pushWalk_support {a b : V} (p : G.Walk a b)
    (hp : ∀ e ∈ p.edges, e.map f ∈ G'.edgeSet) :
    (pushWalk f p hp).support = p.support.map f := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [pushWalk, ih]

@[simp] theorem pushWalk_length {a b : V} (p : G.Walk a b)
    (hp : ∀ e ∈ p.edges, e.map f ∈ G'.edgeSet) :
    (pushWalk f p hp).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [pushWalk, ih]

theorem pushWalk_isPath {a b : V} (p : G.Walk a b)
    (hp : ∀ e ∈ p.edges, e.map f ∈ G'.edgeSet) (hpath : p.IsPath)
    (hinj : ∀ x ∈ p.support, ∀ y ∈ p.support, f x = f y → x = y) :
    (pushWalk f p hp).IsPath := by
  rw [Walk.isPath_def, pushWalk_support]
  exact ((Walk.isPath_def _).mp hpath).map_on hinj

end push

/-! ### Paths -/

namespace GPath

/-- The reverse path. -/
def reverse (P : GPath G) : GPath G :=
  ⟨P.tgt, P.src, P.walk.reverse, P.isPath.reverse, by simpa using P.pos⟩

@[simp] theorem reverse_edges (P : GPath G) : P.reverse.edges = P.edges.reverse :=
  Walk.edges_reverse _

/-- A path from a walk, if the walk is a path of positive length. -/
def ofWalkOpt {a b : V} (p : G.Walk a b) (hp : p.IsPath) : Option (GPath G) :=
  if h : 0 < p.length then some ⟨a, b, p, hp, h⟩ else none

/-- Push a path along a vertex map that is injective on it and sends its edges to edges. -/
def push (P : GPath G) (f : V → V') (hf : ∀ e ∈ P.walk.edges, e.map f ∈ G'.edgeSet)
    (hinj : ∀ x ∈ P.walk.support, ∀ y ∈ P.walk.support, f x = f y → x = y) : GPath G' :=
  ⟨f P.src, f P.tgt, pushWalk f P.walk hf, pushWalk_isPath f _ hf P.isPath hinj,
    by rw [pushWalk_length (G' := G')]; exact P.pos⟩

@[simp] theorem push_edges (P : GPath G) (f : V → V') (hf) (hinj) :
    (P.push (G' := G') f hf hinj).edges = P.edges.map (Sym2.map f) :=
  pushWalk_edges f _ hf

end GPath

/-- Edges of an optional path (`[]` for `none`). -/
def optEdges : Option (GPath G) → List (Sym2 V)
  | none => []
  | some P => P.edges

@[simp] theorem optEdges_none : optEdges (none : Option (GPath G)) = [] := rfl
@[simp] theorem optEdges_some (P : GPath G) : optEdges (some P) = P.edges := rfl

theorem optEdges_ofWalkOpt {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    optEdges (GPath.ofWalkOpt p hp) = p.edges := by
  unfold GPath.ofWalkOpt
  split_ifs with h
  · rfl
  · have : p.edges.length = 0 := by rw [Walk.length_edges]; omega
    simp only [optEdges_none]
    exact (List.length_eq_zero_iff.mp this).symm

/-! ### Pieces and the projection lemma -/

/-- `P` has a *piece* in `G'` along `f` and `S`: an optional path of `G'` whose edges are, up to
order, the images under `f` of the `S`-edges of `P`. -/
def HasPiece (G' : SimpleGraph V') (f : V → V') (S : Sym2 V → Bool) (P : GPath G) : Prop :=
  ∃ o : Option (GPath G'), (optEdges o).Perm ((P.edges.filter S).map (Sym2.map f))

theorem HasPiece.of_reverse {f : V → V'} {S : Sym2 V → Bool} {P : GPath G}
    (h : HasPiece G' f S P.reverse) : HasPiece G' f S P := by
  obtain ⟨o, ho⟩ := h
  refine ⟨o, ho.trans ?_⟩
  rw [GPath.reverse_edges, List.filter_reverse, List.map_reverse]
  exact List.reverse_perm _

theorem hasPiece_none {f : V → V'} {S : Sym2 V → Bool} {P : GPath G}
    (h : P.edges.filter S = []) : HasPiece G' f S P :=
  ⟨none, by simp [h]⟩

/-- A piece given by pushing a sub-path. -/
theorem hasPiece_of_walk {f : V → V'} {S : Sym2 V → Bool} {P : GPath G} {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) (hf : ∀ e ∈ p.edges, e.map f ∈ G'.edgeSet)
    (hinj : ∀ x ∈ p.support, ∀ y ∈ p.support, f x = f y → x = y)
    (hperm : p.edges.Perm (P.edges.filter S)) : HasPiece G' f S P := by
  refine ⟨GPath.ofWalkOpt (pushWalk f p hf) (pushWalk_isPath f p hf hp hinj), ?_⟩
  rw [optEdges_ofWalkOpt, pushWalk_edges]
  exact hperm.map _

theorem Sym2.map_injOn' {f : V → V'} {T : Set V} (hinj : Set.InjOn f T) {e₁ e₂ : Sym2 V}
    (h₁ : ∀ x ∈ e₁, x ∈ T) (h₂ : ∀ x ∈ e₂, x ∈ T) (h : e₁.map f = e₂.map f) : e₁ = e₂ := by
  induction e₁ using Sym2.inductionOn with
  | hf a b =>
  induction e₂ using Sym2.inductionOn with
  | hf c d =>
  simp only [Sym2.map_mk, Sym2.eq_iff] at h ⊢
  have ha := h₁ a (Sym2.mem_mk_left a b)
  have hb := h₁ b (Sym2.mem_mk_right a b)
  have hc := h₂ c (Sym2.mem_mk_left c d)
  have hd := h₂ d (Sym2.mem_mk_right c d)
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hinj ha hc h1, hinj hb hd h2⟩
  · exact Or.inr ⟨hinj ha hd h1, hinj hb hc h2⟩

theorem filterMap_flatMap_perm (f : V → V') (S : Sym2 V → Bool)
    (g : GPath G → Option (GPath G'))
    (hg : ∀ P, (optEdges (g P)).Perm ((P.edges.filter S).map (Sym2.map f)))
    (l : List (GPath G)) :
    ((l.filterMap g).flatMap GPath.edges).Perm
      (((l.flatMap GPath.edges).filter S).map (Sym2.map f)) := by
  induction l with
  | nil => simp
  | cons P l ih =>
    have h1 := hg P
    rw [List.filterMap_cons, List.flatMap_cons, List.filter_append, List.map_append]
    cases hP : g P with
    | none =>
      rw [hP, optEdges_none] at h1
      rw [← h1.nil_eq, List.nil_append]
      exact ih
    | some Q =>
      rw [hP, optEdges_some] at h1
      simp only [List.flatMap_cons]
      exact h1.append ih

/-- **Projection lemma.** -/
theorem PathDecomp.project (D : PathDecomp G) (f : V → V') (S : Sym2 V → Bool) (T : Set V)
    (hinj : Set.InjOn f T) (hT : ∀ e ∈ G.edgeSet, S e = true → ∀ x ∈ e, x ∈ T)
    (hcov : ∀ e', e' ∈ G'.edgeSet ↔ ∃ e ∈ G.edgeSet, S e = true ∧ e.map f = e')
    (hpiece : ∀ P : GPath G, HasPiece G' f S P) :
    ∃ D' : PathDecomp G', D'.size ≤ D.paths.countP (fun P => P.edges.any S) := by
  choose g hg using hpiece
  have key := filterMap_flatMap_perm f S g hg D.paths
  have hnd : (((D.paths.flatMap GPath.edges).filter S).map (Sym2.map f)).Nodup := by
    refine (D.nodup_edges.filter _).map_on ?_
    intro x hx y hy hxy
    rw [List.mem_filter] at hx hy
    have hxG := (D.covers x).2 hx.1
    have hyG := (D.covers y).2 hy.1
    exact Sym2.map_injOn' hinj (hT x hxG hx.2) (hT y hyG hy.2) hxy
  refine ⟨⟨D.paths.filterMap g, key.nodup_iff.mpr hnd, ?_⟩, ?_⟩
  · intro e'
    rw [key.mem_iff, hcov]
    simp only [List.mem_map, List.mem_filter, ← D.covers]
    constructor
    · rintro ⟨e, he, hS, rfl⟩; exact ⟨e, ⟨he, hS⟩, rfl⟩
    · rintro ⟨e, ⟨he, hS⟩, rfl⟩; exact ⟨e, he, hS, rfl⟩
  · show (D.paths.filterMap g).length ≤ _
    rw [List.length_filterMap_eq_countP]
    apply List.countP_mono_left
    intro P _ hP
    obtain ⟨Q, hQ⟩ := Option.isSome_iff_exists.mp hP
    have h1 := hg P
    rw [hQ, optEdges_some] at h1
    have hne : P.edges.filter S ≠ [] := by
      intro h
      rw [h, List.map_nil] at h1
      exact Q.edges_ne_nil h1.eq_nil
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
    rw [List.mem_filter] at he
    exact List.any_eq_true.mpr ⟨e, he⟩

/-- **Mapping along an embedding**: a decomposition of `G` maps to one of `G'` of the same size
whenever `f` is injective and the image of `G.edgeSet` is `G'.edgeSet`. -/
theorem PathDecomp.map_of_injective (D : PathDecomp G) (f : V → V')
    (hinj : Function.Injective f)
    (hcov : ∀ e', e' ∈ G'.edgeSet ↔ ∃ e ∈ G.edgeSet, e.map f = e') :
    ∃ D' : PathDecomp G', D'.size ≤ D.size := by
  have hpiece : ∀ P : GPath G, HasPiece G' f (fun _ => true) P := by
    intro P
    refine hasPiece_of_walk P.walk P.isPath ?_ (fun x _ y _ h => hinj h) (by simp [GPath.edges])
    intro e he
    exact (hcov _).2 ⟨e, P.walk.edges_subset_edgeSet he, rfl⟩
  obtain ⟨D', hD'⟩ := D.project f (fun _ => true) Set.univ (hinj.injOn) (by simp)
    (by simpa using hcov) hpiece
  exact ⟨D', hD'.trans (List.countP_le_length)⟩

end Gallai
