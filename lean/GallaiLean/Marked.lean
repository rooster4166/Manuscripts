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

/-! ### List utilities -/

section lists

theorem countP_eq_sum_ite {α : Type*} (p : α → Bool) (l : List α) :
    l.countP p = (l.map (fun a => if p a then 1 else 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons, ih, List.map_cons, List.sum_cons]
    split_ifs <;> omega

theorem flatMap_toList_map {α β γ : Type*} (l : List (α × Option β)) (φ : β → γ) :
    l.flatMap (fun x => x.2.toList.map φ) = (l.filterMap Prod.snd).map φ := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨a, o⟩ := x
    cases o <;> simp [ih]

theorem sum_ite_isNone {α β : Type*} (l : List (α × Option β)) :
    (l.map (fun x => if x.2.isNone then 2 else 1)).sum =
      2 * l.countP (fun x => x.2.isNone) + (l.filterMap Prod.snd).length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    obtain ⟨a, o⟩ := x
    cases o <;> simp [ih] <;> ring

/-- A filterMap whose images have edge lists matching a family, up to a map. -/
theorem filterMap_flatMap_perm' {α β γ δ : Type*} (g : α → Option β) (E : β → List γ)
    (E' : α → List δ) (φ : γ → δ) (l : List α)
    (h : ∀ a ∈ l, ((((g a).map E).getD []).map φ).Perm (E' a)) :
    (((l.filterMap g).flatMap E).map φ).Perm (l.flatMap E') := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := h a List.mem_cons_self
    have ih := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    rw [List.filterMap_cons, List.flatMap_cons]
    cases hga : g a with
    | none =>
      rw [hga] at h1
      simp only [Option.map_none, Option.getD_none, List.map_nil] at h1
      rw [← h1.nil_eq, List.nil_append]
      exact ih
    | some b =>
      rw [hga] at h1
      simp only [Option.map_some, Option.getD_some] at h1
      rw [List.flatMap_cons, List.map_append]
      exact h1.append ih

end lists

/-! ### Marked partitions -/

section marked

variable {V : Type u} {F : SimpleGraph V} {S : Finset V}

/-- A **marked partition** of `(F, S)`: a path decomposition of `F` in which each path carries an
optional site. A site must be in `S` and be an end of its path, and no site is used twice. -/
structure MarkedPartition (F : SimpleGraph V) (S : Finset V) where
  /-- The paths, each with its optional site. -/
  paths : List (GPath F × Option V)
  nodup_edges : ((paths.map Prod.fst).flatMap GPath.edges).Nodup
  covers : ∀ e, e ∈ F.edgeSet ↔ e ∈ (paths.map Prod.fst).flatMap GPath.edges
  site_ok : ∀ x ∈ paths, ∀ s, x.2 = some s → s ∈ S ∧ (x.1.src = s ∨ x.1.tgt = s)
  sites_nodup : (paths.filterMap Prod.snd).Nodup

namespace MarkedPartition

/-- The underlying path decomposition. -/
def decomp (M : MarkedPartition F S) : PathDecomp F :=
  ⟨M.paths.map Prod.fst, M.nodup_edges, M.covers⟩

/-- A path decomposition with no path assigned. -/
def ofDecomp (D : PathDecomp F) : MarkedPartition F S where
  paths := D.paths.map (fun P => (P, none))
  nodup_edges := by simpa [List.map_map, Function.comp_def] using D.nodup_edges
  covers := by simpa [List.map_map, Function.comp_def] using D.covers
  site_ok := by simp
  sites_nodup := by simp

theorem sites_mem (M : MarkedPartition F S) {s : V} (hs : s ∈ M.paths.filterMap Prod.snd) :
    s ∈ S := by
  obtain ⟨x, hx, hxs⟩ := List.mem_filterMap.mp hs
  exact (M.site_ok x hx s hxs).1

end MarkedPartition

/-- The cost of a marked partition: its number of unassigned paths. -/
def markedCost (M : MarkedPartition F S) : ℕ := M.paths.countP (fun x => x.2.isNone)

/-- `q(F, S)`: the least cost of a marked partition. -/
noncomputable def markedNumber (F : SimpleGraph V) (S : Finset V) : ℕ :=
  sInf {k | ∃ M : MarkedPartition F S, markedCost M = k}

theorem markedNumber_le (M : MarkedPartition F S) : markedNumber F S ≤ markedCost M :=
  Nat.sInf_le ⟨M, rfl⟩

theorem markedNumber_spec [Finite V] (F : SimpleGraph V) (S : Finset V) :
    ∃ M : MarkedPartition F S, markedCost M = markedNumber F S := by
  obtain ⟨D⟩ := PathDecomp.nonempty F
  exact Nat.sInf_mem (s := {k | ∃ M : MarkedPartition F S, markedCost M = k})
    ⟨_, MarkedPartition.ofDecomp D, rfl⟩

/-- `h(F, S)`: the least number of path ends away from the apex over decompositions of the
cone. -/
noncomputable def minOutEnds [Fintype V] [DecidableEq V] (F : SimpleGraph V) (S : Finset V) : ℕ :=
  sInf {k | ∃ D : PathDecomp (cone F S), D.outEnds = k}

theorem minOutEnds_le [Fintype V] [DecidableEq V] (D : PathDecomp (cone F S)) :
    minOutEnds F S ≤ D.outEnds :=
  Nat.sInf_le ⟨D, rfl⟩

theorem minOutEnds_spec [Fintype V] [DecidableEq V] (F : SimpleGraph V) (S : Finset V) :
    ∃ D : PathDecomp (cone F S), D.outEnds = minOutEnds F S := by
  obtain ⟨D⟩ := PathDecomp.nonempty (cone F S)
  exact Nat.sInf_mem (s := {k | ∃ D : PathDecomp (cone F S), D.outEnds = k}) ⟨_, D, rfl⟩

/-! ### Identity A, upper bound: from a marked partition to the cone -/

theorem some_map_mem_cone {e : Sym2 V} (he : e ∈ F.edgeSet) :
    e.map some ∈ (cone F S).edgeSet := by
  induction e using Sym2.inductionOn with
  | hf a b => simpa using he

theorem some_map_mem_cone_iff {e : Sym2 V} :
    e.map some ∈ (cone F S).edgeSet ↔ e ∈ F.edgeSet := by
  refine ⟨fun h => ?_, some_map_mem_cone⟩
  rcases mem_cone_edgeSet_iff.mp h with ⟨e', he', h'⟩ | ⟨s, _, h'⟩
  · rwa [← Sym2.map.injective (Option.some_injective V) h']
  · have : none ∈ e.map some := h' ▸ Sym2.mem_mk_left _ _
    simp [Sym2.mem_map] at this

/-- The copy of a path of `F` in the cone. -/
def GPath.toCone (P : GPath F) (S : Finset V) : GPath (cone F S) :=
  P.push some (fun _ he => some_map_mem_cone (P.walk.edges_subset_edgeSet he))
    (fun _ _ _ _ h => Option.some_injective _ h)

@[simp] theorem GPath.toCone_edges (P : GPath F) :
    (P.toCone S).edges = P.edges.map (Sym2.map some) := GPath.push_edges ..

/-- A path of `F` starting at a site, extended by its spoke. -/
def GPath.coneExtend (P : GPath F) (hs : P.src ∈ S) : GPath (cone F S) where
  src := none
  tgt := some P.tgt
  walk := Walk.cons (show (cone F S).Adj none (some P.src) from hs)
    (pushWalk some P.walk (fun _ he => some_map_mem_cone (P.walk.edges_subset_edgeSet he)))
  isPath := by
    rw [Walk.cons_isPath_iff]
    refine ⟨pushWalk_isPath _ _ _ P.isPath (fun _ _ _ _ h => Option.some_injective _ h), ?_⟩
    simp
  pos := by simp

@[simp] theorem GPath.coneExtend_edges (P : GPath F) (hs : P.src ∈ S) :
    (P.coneExtend hs).edges = s(none, some P.src) :: P.edges.map (Sym2.map some) := by
  simp [GPath.coneExtend, GPath.edges]

/-- The spoke at a site, as a path. -/
def spokePath (s : V) (hs : s ∈ S) : GPath (cone F S) :=
  GPath.ofAdj (show (cone F S).Adj none (some s) from hs)

theorem spokePath_flatMap (l : List V) (h : ∀ s ∈ l, s ∈ S) :
    (l.pmap (spokePath (F := F)) h).flatMap GPath.edges = l.map (fun s => s(none, some s)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.pmap_cons, List.flatMap_cons, List.map_cons]
    rw [ih]
    rfl

theorem spokePath_outEnds (l : List V) (h : ∀ s ∈ l, s ∈ S) :
    ((l.pmap (spokePath (F := F)) h).map GPath.outEndsAt).sum = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.pmap_cons, List.map_cons, List.sum_cons, List.length_cons]
    rw [ih]
    simp [spokePath, GPath.ofAdj, GPath.outEndsAt]
    omega

/-- One marked path becomes one path of the cone: an assigned path gets its spoke. -/
theorem exists_cone_item (x : GPath F × Option V)
    (hx : ∀ s, x.2 = some s → s ∈ S ∧ (x.1.src = s ∨ x.1.tgt = s)) :
    ∃ Q : GPath (cone F S),
      Q.edges.Perm (x.2.toList.map (fun s => s(none, some s)) ++ x.1.edges.map (Sym2.map some)) ∧
      Q.outEndsAt = if x.2.isNone then 2 else 1 := by
  obtain ⟨P, o⟩ := x
  cases o with
  | none =>
    refine ⟨P.toCone S, by simp, ?_⟩
    simp [GPath.outEndsAt, GPath.toCone, GPath.push]
  | some s =>
    obtain ⟨hs, hend⟩ := hx s rfl
    rcases hend with h | h
    · subst h
      refine ⟨P.coneExtend hs, by simp, ?_⟩
      simp [GPath.outEndsAt, GPath.coneExtend]
    · subst h
      refine ⟨P.reverse.coneExtend hs, ?_, ?_⟩
      · simp only [GPath.coneExtend_edges, GPath.reverse_edges, Option.toList_some,
          List.map_cons, List.map_nil, List.cons_append, List.nil_append]
        exact List.Perm.cons _ ((List.reverse_perm _).map _)
      · simp [GPath.outEndsAt, GPath.coneExtend]

/-- **Identity A, upper bound.** A marked partition of cost `c` gives a decomposition of the cone
with exactly `|S| + 2c` ends away from the apex: prepend spokes to assigned paths and use each
unused spoke singly. -/
theorem exists_outEnds_eq [Fintype V] [DecidableEq V] (M : MarkedPartition F S) :
    ∃ D : PathDecomp (cone F S), D.outEnds = S.card + 2 * markedCost M := by
  have hex : ∀ x : GPath F × Option V, ∃ Q : GPath (cone F S), x ∈ M.paths →
      (Q.edges.Perm (x.2.toList.map (fun s => s(none, some s)) ++ x.1.edges.map (Sym2.map some)) ∧
        Q.outEndsAt = if x.2.isNone then 2 else 1) := by
    intro x
    by_cases hx : x ∈ M.paths
    · obtain ⟨Q, hQ⟩ := exists_cone_item x (M.site_ok x hx)
      exact ⟨Q, fun _ => hQ⟩
    · exact ⟨x.1.toCone S, fun h => absurd h hx⟩
  choose g hg using hex
  set labels := M.paths.filterMap Prod.snd with hlabels
  set Us := S.toList.filter (fun s => !decide (s ∈ labels)) with hUs_def
  have hUs : ∀ s ∈ Us, s ∈ S := fun s hs => Finset.mem_toList.mp (List.mem_of_mem_filter hs)
  set spoke : V → Sym2 (Option V) := fun s => s(none, some s) with hspoke
  set Fe := (M.paths.map Prod.fst).flatMap GPath.edges with hFe
  let L := M.paths.map g ++ Us.pmap (spokePath (F := F)) hUs
  let E := Fe.map (Sym2.map some) ++ S.toList.map spoke
  have hsites : (labels ++ Us).Perm S.toList := by
    have h1 : labels.Perm (S.toList.filter (fun s => decide (s ∈ labels))) := by
      rw [List.perm_ext_iff_of_nodup M.sites_nodup (S.nodup_toList.filter _)]
      intro a
      simp only [List.mem_filter, Finset.mem_toList, decide_eq_true_eq]
      exact ⟨fun h => ⟨M.sites_mem h, h⟩, fun h => h.2⟩
    exact (h1.append_right Us).trans (List.filter_append_perm _ _)
  have hperm : (L.flatMap GPath.edges).Perm E := by
    have e1 : (M.paths.map g).flatMap GPath.edges =
        M.paths.flatMap (fun x => (g x).edges) := List.flatMap_map _ _ _
    have p1 : ((M.paths.map g).flatMap GPath.edges).Perm
        (labels.map spoke ++ Fe.map (Sym2.map some)) := by
      rw [e1]
      refine (List.Perm.flatMap_left _ (fun x hx => (hg x hx).1)).trans ?_
      refine (List.flatMap_append_perm _ _ _).symm.trans ?_
      rw [flatMap_toList_map, hFe, List.map_flatMap, List.flatMap_map]
    simp only [L, List.flatMap_append, spokePath_flatMap]
    refine (p1.append_right _).trans ?_
    rw [List.append_assoc]
    refine List.perm_append_comm.trans ?_
    rw [List.append_assoc]
    refine List.Perm.append_left _ ?_
    refine List.perm_append_comm.trans ?_
    rw [← List.map_append]
    exact hsites.map _
  have hnd : E.Nodup := by
    rw [List.nodup_append]
    refine ⟨M.nodup_edges.map (Sym2.map.injective (Option.some_injective V)),
      S.nodup_toList.map (fun a b h => by simpa [spoke] using h), ?_⟩
    intro a ha b hb hab
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp ha
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp hb
    have : none ∈ e.map some := hab ▸ Sym2.mem_mk_left _ _
    simp [Sym2.mem_map] at this
  have hcov : ∀ e, e ∈ (cone F S).edgeSet ↔ e ∈ E := by
    intro e
    rw [mem_cone_edgeSet_iff]
    simp only [E, List.mem_append, List.mem_map, Finset.mem_toList, spoke, ← M.covers, Fe]
    constructor
    · rintro (h | ⟨s, hs, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨s, hs, rfl⟩
    · rintro (h | ⟨s, hs, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨s, hs, rfl⟩
  refine ⟨PathDecomp.ofPerm L E hperm hnd hcov, ?_⟩
  rw [PathDecomp.outEnds_eq_sum]
  simp only [PathDecomp.ofPerm_paths, L, List.map_append, List.sum_append, spokePath_outEnds,
    List.map_map]
  have e2 : (M.paths.map (GPath.outEndsAt ∘ g)).sum =
      (M.paths.map (fun x => if x.2.isNone then 2 else 1)).sum := by
    congr 1
    exact List.map_congr_left (fun x hx => (hg x hx).2)
  rw [e2, sum_ite_isNone]
  have := hsites.length_eq
  rw [List.length_append, Finset.length_toList] at this
  unfold markedCost
  omega

end marked

end Gallai
