import GallaiLean.Surgery
import GallaiLean.Doubling

/-!
# Marked partitions and the apex reduction

Marked-reduction manuscript, §1, "Equivalence of the marked and ordinary bounds".

For a graph `F` on `V` and a finite set `S` of *sites*, a *marked partition* is a path
decomposition of `F` in which some paths are assigned to sites: a path may only be assigned to
one of its own ends that lies in `S`, every path gets at most one site and every site at most one
path. Its *cost* is the number of unassigned paths, and `markedNumber F S` (the manuscript's
`q(F, S)`) is the least cost.

* `cone F S` (`X = F + z`): `F` on `Option V` with a new apex `none` adjacent exactly to `S`.
* `PathDecomp.outEnds D = ∑ v, D.ends (some v)`: the number of path ends away from the apex.
* `minOutEnds F S` (`h`): the least `outEnds` over the decompositions of the cone.
* **Identity A** (`minOutEnds_eq`): `h = |S| + 2 q(F, S)`.
* `wGraph F S` (`W(F, S)`): two copies of the cone with their apices identified, plus a leaf at
  the common apex. `card_wGraph`: `|V(W)| = 2|V| + 2`.
* **Identity B** (`pathNumber_wGraph`): `p(W(F, S)) = |S| + 2 q(F, S) + 1`.
* **Corollary** (`markedNumber_le_of_gallai`): Gallai's conjecture implies the marked bound
  `q(F, S) ≤ (|V| - |S|) / 2` for connected `F` and nonempty `S`.
-/

open SimpleGraph

namespace Gallai

universe u

/-! ### The cone -/

section cone

variable {U : Type u}

/-- The cone over `G` with apex `none` adjacent exactly to the sites `S`. -/
def cone (G : SimpleGraph U) (S : Finset U) : SimpleGraph (Option U) where
  Adj x y := match x, y with
    | some a, some b => G.Adj a b
    | none, some b => b ∈ S
    | some a, none => a ∈ S
    | none, none => False
  symm := ⟨fun x y h => by
    cases x <;> cases y <;> simp only at h ⊢
    · exact h
    · exact h
    · exact h.symm⟩
  loopless := ⟨fun x h => by
    cases x <;> simp only at h
    exact G.loopless.irrefl _ h⟩

variable {G : SimpleGraph U} {S : Finset U}

@[simp] theorem cone_adj_some_some {a b : U} : (cone G S).Adj (some a) (some b) ↔ G.Adj a b :=
  Iff.rfl
@[simp] theorem cone_adj_none_some {b : U} : (cone G S).Adj none (some b) ↔ b ∈ S := Iff.rfl
@[simp] theorem cone_adj_some_none {a : U} : (cone G S).Adj (some a) none ↔ a ∈ S := Iff.rfl
@[simp] theorem cone_not_adj_none_none : ¬ (cone G S).Adj none none := id

theorem mem_cone_edgeSet_iff {e : Sym2 (Option U)} :
    e ∈ (cone G S).edgeSet ↔ (∃ e' ∈ G.edgeSet, e'.map some = e) ∨ ∃ s ∈ S, e = s(none, some s) := by
  induction e using Sym2.inductionOn with
  | hf a b =>
  rw [mem_edgeSet]
  rcases a with _ | a <;> rcases b with _ | b
  · simp only [cone_not_adj_none_none, false_iff, not_or, not_exists, not_and]
    refine ⟨fun e' _ h => ?_, fun s _ h => ?_⟩
    · have : none ∈ e'.map some := h ▸ Sym2.mem_mk_left _ _
      simp [Sym2.mem_map] at this
    · simp at h
  · rw [cone_adj_none_some]
    constructor
    · intro h; exact Or.inr ⟨b, h, rfl⟩
    · rintro (⟨e', _, h⟩ | ⟨s, hs, h⟩)
      · have : none ∈ e'.map some := h ▸ Sym2.mem_mk_left _ _
        simp [Sym2.mem_map] at this
      · simp only [Sym2.eq_iff, Option.some.injEq, reduceCtorEq, and_false, or_false,
          true_and] at h
        rw [h]; exact hs
  · rw [cone_adj_some_none]
    constructor
    · intro h; exact Or.inr ⟨a, h, Sym2.eq_swap⟩
    · rintro (⟨e', _, h⟩ | ⟨s, hs, h⟩)
      · have : none ∈ e'.map some := h ▸ Sym2.mem_mk_right _ _
        simp [Sym2.mem_map] at this
      · simp only [Sym2.eq_iff, reduceCtorEq, false_and, Option.some.injEq,
          false_or] at h
        rw [h.1]; exact hs
  · rw [cone_adj_some_some]
    constructor
    · intro h; exact Or.inl ⟨s(a, b), h, rfl⟩
    · rintro (⟨e', he', h⟩ | ⟨s, _, h⟩)
      · induction e' using Sym2.inductionOn with
        | hf c d =>
        simp only [Sym2.map_mk, Sym2.eq_iff, Option.some.injEq] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact he'
        · exact G.symm.symm _ _ he'
      · simp at h

/-- A walk of the cone avoiding the apex is a walk of the base graph. -/
theorem cone_walk_lift : ∀ {x y : Option U} (q : (cone G S).Walk x y), none ∉ q.support →
    ∃ (a b : U) (q' : G.Walk a b), x = some a ∧ y = some b ∧
      q'.support.map some = q.support ∧ q'.edges.map (Sym2.map some) = q.edges
  | x, _, .nil, hn => by
    cases x with
    | none => exact absurd (Walk.start_mem_support _) hn
    | some a => exact ⟨a, a, Walk.nil, rfl, rfl, rfl, rfl⟩
  | x, _, @Walk.cons _ _ _ c _ h q, hn => by
    rw [Walk.support_cons, List.mem_cons, not_or] at hn
    obtain ⟨a', b, q', rfl, rfl, hs, he⟩ := cone_walk_lift q hn.2
    cases x with
    | none => exact absurd rfl hn.1
    | some a =>
      refine ⟨a, b, Walk.cons (show G.Adj a a' from h) q', rfl, rfl, ?_, ?_⟩
      · simp [hs]
      · simp [he]

theorem cone_lift_isPath {a b : U} {x y : Option U} {q : (cone G S).Walk x y} {q' : G.Walk a b}
    (hs : q'.support.map some = q.support) (hq : q.IsPath) : q'.IsPath := by
  rw [Walk.isPath_def] at hq ⊢
  rw [← hs] at hq
  exact (List.nodup_map_iff (Option.some_injective U)).mp hq

theorem cone_lift_length {a b : U} {x y : Option U} {q : (cone G S).Walk x y} {q' : G.Walk a b}
    (he : q'.edges.map (Sym2.map some) = q.edges) : q'.length = q.length := by
  rw [← Walk.length_edges, ← Walk.length_edges, ← he, List.length_map]

/-- A path of the cone starting at the apex: a spoke followed by a path avoiding the apex. -/
theorem cone_path_from_none (P : GPath (cone G S)) (h : P.src = none) :
    ∃ (s : U) (q : (cone G S).Walk (some s) P.tgt), s ∈ S ∧ q.IsPath ∧ none ∉ q.support ∧
      P.edges = s(none, some s) :: q.edges ∧ P.walk.support = none :: q.support := by
  obtain ⟨src, tgt, w, hw, hpos⟩ := P
  simp only at h
  subst h
  cases w with
  | nil => simp at hpos
  | @cons _ c _ hadj q =>
    rw [Walk.cons_isPath_iff] at hw
    cases c with
    | none => exact absurd hadj cone_not_adj_none_none
    | some s => exact ⟨s, q, hadj, hw.1, hw.2, rfl, rfl⟩

end cone

/-! ### Ends away from the apex -/

section outEnds

variable {U : Type u} {G : SimpleGraph (Option U)}

/-- Number of ends of a path away from the apex `none`. -/
def GPath.outEndsAt (P : GPath G) : ℕ :=
  (if P.src = none then 0 else 1) + (if P.tgt = none then 0 else 1)

theorem GPath.outEndsAt_reverse (P : GPath G) : P.reverse.outEndsAt = P.outEndsAt := by
  simp only [GPath.outEndsAt, GPath.reverse]; exact Nat.add_comm _ _

/-- Number of path ends away from the apex `none`. -/
def PathDecomp.outEnds [Fintype U] [DecidableEq U] (D : PathDecomp G) : ℕ :=
  ∑ v : U, D.ends (some v)

theorem GPath.sum_endsAt_some [Fintype U] [DecidableEq U] (P : GPath G) :
    ∑ v : U, P.endsAt (some v) = P.outEndsAt := by
  have key : ∀ x : Option U, (∑ v : U, if x = some v then 1 else 0) = if x = none then 0 else 1 := by
    intro x
    cases x with
    | none => simp
    | some a => simp
  simp only [GPath.endsAt, Finset.sum_add_distrib, GPath.outEndsAt, key]

theorem PathDecomp.outEnds_eq_sum [Fintype U] [DecidableEq U] (D : PathDecomp G) :
    D.outEnds = (D.paths.map GPath.outEndsAt).sum := by
  unfold PathDecomp.outEnds PathDecomp.ends
  generalize D.paths = l
  induction l with
  | nil => simp
  | cons P l ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih, P.sum_endsAt_some]

theorem PathDecomp.two_mul_size_eq [Fintype U] [DecidableEq U] (D : PathDecomp G) :
    2 * D.size = D.ends none + D.outEnds := by
  rw [← D.sum_ends, Fintype.sum_option]
  rfl

end outEnds

end Gallai
