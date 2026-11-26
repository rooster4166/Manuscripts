import GallaiLean.Surgery
import GallaiLean.PrivateLeaf

/-!
# Marked partitions and the apex reduction

Marked-reduction manuscript, §1, "Equivalence of the marked and ordinary bounds".

For a graph `F` on `V` and a finite set `S` of *sites*, a *marked partition*
(`MarkedPartition F S`) is a path decomposition of `F` in which some paths are assigned to sites:
a path may only be assigned to one of its own ends that lies in `S`, every path gets at most one
site and every site at most one path. Its cost (`markedCost`) is the number of unassigned paths,
and `markedNumber F S` (the manuscript's `q(F, S)`) is the least cost (`sInf`).

* `cone F S` (`X = F + z`): `F` on `Option V` with a new apex `none` adjacent exactly to `S`.
* `PathDecomp.outEnds D = ∑ v, D.ends (some v)`: the number of path ends away from the apex
  (`outEnds_eq_sum`: one per apex path, two per other path).
* `minOutEnds F S` (`h`): the least `outEnds` over the decompositions of the cone.
* **Identity A** (`minOutEnds_eq`): `h = |S| + 2 q(F, S)`, from `exists_outEnds_eq` (a marked
  partition of cost `c` gives a decomposition with `outEnds = |S| + 2c`) and `le_outEnds`
  (every decomposition has `outEnds ≥ |S| + 2 q`).
* `doubleCone F S`: two copies of the cone with their apices identified (on `Option (Bool × V)`);
  `wGraph F S` (`W(F, S)`): `addLeaf (doubleCone F S) none`. `card_wGraph`: `|V(W)| = 2|V| + 2`;
  `wGraph_connected`.
* **Identity B** (`pathNumber_wGraph`): `p(W(F, S)) = |S| + 2 q(F, S) + 1`
  (`pathNumber_wGraph_eq_minOutEnds`: `= h + 1`). Upper bound `pathNumber_wGraph_le` via
  `exists_double` (pair apex ends across the copies); lower bound `le_pathNumber_wGraph` via
  `exists_side` (restrict a split decomposition to each copy, keeping its ends there).
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
    have := ih
    cases o <;> simp at this ⊢ <;> omega

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
    dsimp only at hend
    rcases hend with h | h
    · subst h
      refine ⟨P.coneExtend hs, by simp, ?_⟩
      simp [GPath.outEndsAt, GPath.coneExtend]
    · subst h
      have hs' : P.reverse.src ∈ S := hs
      refine ⟨P.reverse.coneExtend hs', ?_, ?_⟩
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
  rw [hlabels] at this
  omega

end marked

/-! ### Identity A, lower bound: from the cone to a marked partition -/

section lower

theorem filter_bothSome_of_not_mem {U : Type*} {G : SimpleGraph (Option U)} {a b : Option U}
    (p : G.Walk a b) (hn : none ∉ p.support) : p.edges.filter bothSome = p.edges := by
  rw [List.filter_eq_self]
  intro e he
  induction e using Sym2.inductionOn with
  | hf x y =>
  have hx := p.fst_mem_support_of_mem_edges he
  have hy := p.snd_mem_support_of_mem_edges he
  cases x with
  | none => exact absurd hx hn
  | some _ =>
  cases y with
  | none => exact absurd hy hn
  | some _ => rfl

theorem sum_map_eq_add_two_mul {α : Type*} (l : List α) (f g h : α → ℕ)
    (H : ∀ a ∈ l, h a = f a + 2 * g a) :
    (l.map h).sum = (l.map f).sum + 2 * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, H a List.mem_cons_self,
      ih (fun b hb => H b (List.mem_cons_of_mem _ hb))]
    ring

variable {V : Type u} {F : SimpleGraph V} {S : Finset V}

theorem spoke_injective : Function.Injective (fun s : V => s(none, some s)) := by
  intro a b h
  simpa using h

/-- Every decomposition of the cone has exactly `|S|` edges at the apex. -/
theorem cone_sum_incid_none [DecidableEq V] (D : PathDecomp (cone F S)) :
    (D.paths.map (fun P => P.incid none)).sum = S.card := by
  have h1 : (D.paths.map (fun P => P.incid none)).sum =
      ((D.paths.flatMap GPath.edges).filter (fun e => decide (none ∈ e))).length := by
    rw [← List.countP_eq_length_filter, List.countP_flatMap]
    rfl
  rw [h1]
  have h2 : ((D.paths.flatMap GPath.edges).filter (fun e => decide (none ∈ e))).Perm
      (S.toList.map (fun s => s(none, some s))) := by
    rw [List.perm_ext_iff_of_nodup (D.nodup_edges.filter _) (S.nodup_toList.map spoke_injective)]
    intro e
    simp only [List.mem_filter, ← D.covers, decide_eq_true_eq, List.mem_map, Finset.mem_toList]
    rw [mem_cone_edgeSet_iff]
    constructor
    · rintro ⟨⟨e', _, rfl⟩ | ⟨s, hs, rfl⟩, hn⟩
      · exfalso
        simp [Sym2.mem_map] at hn
      · exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨Or.inr ⟨s, hs, rfl⟩, Sym2.mem_mk_left _ _⟩
  rw [h2.length_eq, List.length_map, Finset.length_toList]

/-- What a path of the cone contributes to a marked partition of `F`: its edges inside `F` (as a
path or nothing), and the site of its spoke if it has one. -/
def ItemSpec [DecidableEq V] (P : GPath (cone F S)) (o : Option (GPath F × Option V)) : Prop :=
  ((((o.map Prod.fst).map GPath.edges).getD []).map (Sym2.map some)).Perm
      (P.edges.filter bothSome) ∧
    (∀ x, o = some x → ∀ s, x.2 = some s → s ∈ S ∧ x.1.src = s ∧ s(none, some s) ∈ P.edges) ∧
    (o.map (fun x => x.2.isNone)).getD false = decide (none ∉ P.walk.support)

theorem itemSpec_avoid [DecidableEq V] (P : GPath (cone F S)) (hn : none ∉ P.walk.support) :
    ∃ o, ItemSpec P o := by
  obtain ⟨a, b, q', -, -, hs, he⟩ := cone_walk_lift P.walk hn
  let Q : GPath F := ⟨a, b, q', cone_lift_isPath hs P.isPath,
    by rw [cone_lift_length he]; exact P.pos⟩
  refine ⟨some (Q, none), ?_, ?_, ?_⟩
  · simp only [Option.map_some, Option.getD_some]
    show (q'.edges.map (Sym2.map some)).Perm (P.walk.edges.filter bothSome)
    rw [filter_bothSome_of_not_mem P.walk hn, he]
  · rintro x hx s hs
    simp only [Option.some.injEq] at hx
    subst hx
    simp at hs
  · simp [hn]

theorem itemSpec_src [DecidableEq V] (P : GPath (cone F S)) (h : P.src = none) : ∃ o, ItemSpec P o := by
  obtain ⟨s, q, hs, hq, hn, hedges, hsupp⟩ := cone_path_from_none P h
  by_cases hlen : q.length = 0
  · have hqe : q.edges = [] := by
      rw [← List.length_eq_zero_iff, Walk.length_edges]; exact hlen
    refine ⟨none, ?_, ?_, ?_⟩
    · rw [hedges, hqe]
      simp
    · intro x hx
      simp at hx
    · simp [hsupp]
  · obtain ⟨a, b, q', ha, -, hs', he⟩ := cone_walk_lift q hn
    obtain rfl : s = a := Option.some_injective _ ha
    let Q : GPath F := ⟨s, b, q', cone_lift_isPath hs' hq,
      by rw [cone_lift_length he]; omega⟩
    refine ⟨some (Q, some s), ?_, ?_, ?_⟩
    · simp only [Option.map_some, Option.getD_some]
      rw [hedges, List.filter_cons, filter_bothSome_of_not_mem q hn]
      simp only [bothSome_mk, Option.isSome_none, Option.isSome_some, Bool.false_and,
        Bool.false_eq_true, ite_false]
      show (q'.edges.map (Sym2.map some)).Perm q.edges
      rw [he]
    · rintro x hx t ht
      simp only [Option.some.injEq] at hx
      subst hx
      simp only [Option.some.injEq] at ht
      subst ht
      exact ⟨hs, rfl, by rw [hedges]; exact List.mem_cons_self⟩
    · simp [hsupp]

theorem ItemSpec.of_reverse [DecidableEq V] {P : GPath (cone F S)} {o : Option (GPath F × Option V)}
    (h : ItemSpec P.reverse o) : ItemSpec P o := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.trans ?_, ?_, ?_⟩
  · rw [GPath.reverse_edges, List.filter_reverse]
    exact List.reverse_perm _
  · intro x hx s hs
    obtain ⟨a, b, c⟩ := h2 x hx s hs
    refine ⟨a, b, ?_⟩
    rw [GPath.reverse_edges, List.mem_reverse] at c
    exact c
  · rw [h3]
    simp [GPath.reverse, Walk.support_reverse]

/-- Distinct paths of a decomposition carry distinct spokes, so their sites are distinct. -/
theorem sites_nodup_of_spokes (l : List (GPath (cone F S))) (hl : (l.flatMap GPath.edges).Nodup)
    (g : GPath (cone F S) → Option (GPath F × Option V))
    (hg : ∀ P ∈ l, ∀ x, g P = some x → ∀ s, x.2 = some s → s(none, some s) ∈ P.edges) :
    ((l.filterMap g).filterMap Prod.snd).Nodup := by
  rw [List.filterMap_filterMap]
  induction l with
  | nil => simp
  | cons P l ih =>
    rw [List.flatMap_cons, List.nodup_append] at hl
    have ih := ih hl.2.1 (fun Q hQ => hg Q (List.mem_cons_of_mem _ hQ))
    cases h : (g P).bind Prod.snd with
    | none =>
      rw [List.filterMap_cons_none (f := fun x => (g x).bind Prod.snd) h]
      exact ih
    | some s =>
      rw [List.filterMap_cons_some (f := fun x => (g x).bind Prod.snd) h]
      refine List.nodup_cons.mpr ⟨fun hs => ?_, ih⟩
      obtain ⟨x, hx, hxs⟩ := Option.bind_eq_some_iff.mp h
      have hP := hg P List.mem_cons_self x hx s hxs
      obtain ⟨Q, hQ, hQs⟩ := List.mem_filterMap.mp hs
      obtain ⟨y, hy, hys⟩ := Option.bind_eq_some_iff.mp hQs
      have hQ' := hg Q (List.mem_cons_of_mem _ hQ) y hy s hys
      exact hl.2.2 _ hP _ (List.mem_flatMap.mpr ⟨Q, hQ, hQ'⟩) rfl

/-- From a decomposition of the cone in which the apex is only ever an end, a marked partition
with `|S| + 2 · cost = outEnds`: each spoke path's continuation into `F` is assigned to its
site. -/
theorem exists_marked_of_split [Fintype V] [DecidableEq V] (D : PathDecomp (cone F S))
    (hD : ∀ P ∈ D.paths, none ∈ P.walk.support → P.src = none ∨ P.tgt = none) :
    ∃ M : MarkedPartition F S, S.card + 2 * markedCost M = D.outEnds := by
  have hex : ∀ P : GPath (cone F S), ∃ o, P ∈ D.paths → ItemSpec P o := by
    intro P
    by_cases hP : P ∈ D.paths
    · by_cases hn : none ∈ P.walk.support
      · rcases hD P hP hn with h | h
        · obtain ⟨o, ho⟩ := itemSpec_src P h
          exact ⟨o, fun _ => ho⟩
        · obtain ⟨o, ho⟩ := itemSpec_src P.reverse h
          exact ⟨o, fun _ => ho.of_reverse⟩
      · obtain ⟨o, ho⟩ := itemSpec_avoid P hn
        exact ⟨o, fun _ => ho⟩
    · exact ⟨none, fun h => absurd h hP⟩
  choose g hg using hex
  have hperm : ((((D.paths.filterMap g).map Prod.fst).flatMap GPath.edges).map
      (Sym2.map some)).Perm ((D.paths.flatMap GPath.edges).filter bothSome) := by
    rw [List.map_filterMap, List.filter_flatMap]
    exact filterMap_flatMap_perm' (fun P => (g P).map Prod.fst) GPath.edges
      (fun P => P.edges.filter bothSome) (Sym2.map some) D.paths (fun P hP => (hg P hP).1)
  have hinj : Function.Injective (Sym2.map (some : V → Option V)) :=
    Sym2.map.injective (Option.some_injective V)
  let M : MarkedPartition F S :=
    { paths := D.paths.filterMap g
      nodup_edges := (hperm.nodup_iff.mpr (D.nodup_edges.filter _)).of_map _
      covers := by
        intro e
        rw [← some_map_mem_cone_iff (S := S), D.covers, ← List.mem_map_of_injective hinj,
          hperm.mem_iff, List.mem_filter]
        have : bothSome (e.map some) = true := by
          induction e using Sym2.inductionOn with
          | hf a b => rfl
        simp [this]
      site_ok := by
        intro x hx s hs
        obtain ⟨P, hP, hgP⟩ := List.mem_filterMap.mp hx
        obtain ⟨h1, h2, -⟩ := (hg P hP).2.1 x hgP s hs
        exact ⟨h1, Or.inl h2⟩
      sites_nodup := sites_nodup_of_spokes D.paths D.nodup_edges g
        (fun P hP x hx s hs => ((hg P hP).2.1 x hx s hs).2.2) }
  refine ⟨M, ?_⟩
  have hcost : markedCost M = D.paths.countP (fun P => decide (none ∉ P.walk.support)) := by
    unfold markedCost
    rw [List.countP_filterMap]
    exact List.countP_congr (fun P hP => by rw [(hg P hP).2.2])
  rw [hcost, ← cone_sum_incid_none D, countP_eq_sum_ite, PathDecomp.outEnds_eq_sum]
  symm
  apply sum_map_eq_add_two_mul
  intro P hP
  by_cases hn : none ∈ P.walk.support
  · have hend := hD P hP hn
    have hne := P.src_ne_tgt
    rw [P.incid_of_end (hend.imp id id)]
    simp only [hn, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false]
    rcases hend with h | h
    · have : P.tgt ≠ none := fun ht => hne (h.trans ht.symm)
      simp [GPath.outEndsAt, h, this]
    · have : P.src ≠ none := fun hs => hne (hs.trans h.symm)
      simp [GPath.outEndsAt, h, this]
  · rw [P.incid_of_not_mem hn]
    have hs : P.src ≠ none := fun h => hn (h ▸ P.walk.start_mem_support)
    have ht : P.tgt ≠ none := fun h => hn (h ▸ P.walk.end_mem_support)
    simp [GPath.outEndsAt, hs, ht, hn]

/-- **Identity A, lower bound**: every decomposition of the cone has at least `|S| + 2 q(F, S)`
ends away from the apex. Split paths at internal visits of the apex (ends away from it are
unchanged), then assign the continuation of each spoke path to its site. -/
theorem le_outEnds [Fintype V] [DecidableEq V] (D : PathDecomp (cone F S)) :
    S.card + 2 * markedNumber F S ≤ D.outEnds := by
  obtain ⟨D', hends, hz⟩ := D.exists_split_all none
  have h1 : D'.outEnds = D.outEnds :=
    Finset.sum_congr rfl (fun v _ => hends (some v) (Option.some_ne_none v))
  obtain ⟨M, hM⟩ := exists_marked_of_split D' hz
  have := markedNumber_le M
  omega

/-- **Identity A**: `h(F, S) = |S| + 2 q(F, S)`. -/
theorem minOutEnds_eq [Fintype V] [DecidableEq V] (F : SimpleGraph V) (S : Finset V) :
    minOutEnds F S = S.card + 2 * markedNumber F S := by
  apply le_antisymm
  · obtain ⟨M, hM⟩ := markedNumber_spec F S
    obtain ⟨D, hD⟩ := exists_outEnds_eq M
    rw [← hM, ← hD]
    exact minOutEnds_le D
  · obtain ⟨D, hD⟩ := minOutEnds_spec F S
    rw [← hD]
    exact le_outEnds D

end lower

/-! ### The doubled cone and `W(F, S)` -/

section wgraph

variable {V : Type u} {F : SimpleGraph V} {S : Finset V}

theorem cone_edge_has_some {U : Type*} {G : SimpleGraph U} {T : Finset U} {e : Sym2 (Option U)}
    (he : e ∈ (cone G T).edgeSet) : ∃ a, some a ∈ e := by
  induction e using Sym2.inductionOn with
  | hf x y =>
  rw [mem_edgeSet] at he
  rcases x with _ | a
  · rcases y with _ | b
    · exact absurd he (cone_not_adj_none_none (G := G) (S := T))
    · exact ⟨b, Sym2.mem_mk_right _ _⟩
  · exact ⟨a, Sym2.mem_mk_left _ _⟩

/-- Two disjoint copies of `F`, indexed by `Bool`. -/
def twoCopies (F : SimpleGraph V) : SimpleGraph (Bool × V) where
  Adj p q := p.1 = q.1 ∧ F.Adj p.2 q.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => F.loopless.irrefl _ h.2⟩

/-- Two copies of the cone `F + z` with their apices identified (the apex is `none`). -/
def doubleCone (F : SimpleGraph V) (S : Finset V) : SimpleGraph (Option (Bool × V)) :=
  cone (twoCopies F) (Finset.univ ×ˢ S)

/-- `W(F, S)`: the doubled cone with one new leaf at the common apex. -/
def wGraph (F : SimpleGraph V) (S : Finset V) : SimpleGraph (Option (Option (Bool × V))) :=
  addLeaf (doubleCone F S) none

theorem card_wGraph [Fintype V] :
    Fintype.card (Option (Option (Bool × V))) = 2 * Fintype.card V + 2 := by
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_bool]

@[simp] theorem doubleCone_adj_some_some {b b' : Bool} {a a' : V} :
    (doubleCone F S).Adj (some (b, a)) (some (b', a')) ↔ b = b' ∧ F.Adj a a' := Iff.rfl
@[simp] theorem doubleCone_adj_none_some {b : Bool} {a : V} :
    (doubleCone F S).Adj none (some (b, a)) ↔ a ∈ S := by
  show (b, a) ∈ Finset.univ ×ˢ S ↔ a ∈ S
  simp
@[simp] theorem doubleCone_adj_some_none {b : Bool} {a : V} :
    (doubleCone F S).Adj (some (b, a)) none ↔ a ∈ S := by
  show (b, a) ∈ Finset.univ ×ˢ S ↔ a ∈ S
  simp
@[simp] theorem doubleCone_not_adj_none_none : ¬ (doubleCone F S).Adj none none := id

theorem wGraph_connected (hF : F.Connected) (hS : S.Nonempty) : (wGraph F S).Connected := by
  obtain ⟨s, hs⟩ := hS
  have hreach : ∀ x, (doubleCone F S).Reachable none x := by
    intro x
    rcases x with _ | ⟨b, a⟩
    · exact SimpleGraph.Reachable.refl _
    · have h1 : (doubleCone F S).Adj none (some (b, s)) := by simpa using hs
      let φ : F →g doubleCone F S :=
        { toFun := fun c => some (b, c)
          map_rel' := fun h => by simpa using h }
      exact h1.reachable.trans ((hF.preconnected s a).map φ)
  have hc : (doubleCone F S).Connected :=
    { preconnected := fun x y => (hreach x).symm.trans (hreach y), nonempty := ⟨none⟩ }
  exact addLeaf_connected hc none

/-! #### Identity B, upper bound: pair the apex ends across the two copies -/

/-- The copy-`b` embedding of the cone into the doubled cone. -/
def liftC (b : Bool) : Option V → Option (Bool × V) := Option.map (Prod.mk b)

@[simp] theorem liftC_none (b : Bool) : liftC b (none : Option V) = none := rfl
@[simp] theorem liftC_some (b : Bool) (a : V) : liftC b (some a) = some (b, a) := rfl

theorem liftC_injective (b : Bool) : Function.Injective (liftC b : Option V → Option (Bool × V)) := by
  intro x y h
  cases x <;> cases y <;> simp_all

theorem liftC_eq_none {b : Bool} {x : Option V} : liftC b x = none ↔ x = none := by
  cases x <;> simp

theorem liftC_adj {b : Bool} {x y : Option V} (h : (cone F S).Adj x y) :
    (doubleCone F S).Adj (liftC b x) (liftC b y) := by
  rcases x with _ | a <;> rcases y with _ | c <;> simp_all

theorem liftC_map_mem {b : Bool} {e : Sym2 (Option V)} (he : e ∈ (cone F S).edgeSet) :
    e.map (liftC b) ∈ (doubleCone F S).edgeSet := by
  induction e using Sym2.inductionOn with
  | hf x y => exact liftC_adj he

theorem mem_doubleCone_edgeSet_iff {e : Sym2 (Option (Bool × V))} :
    e ∈ (doubleCone F S).edgeSet ↔ ∃ b, ∃ e' ∈ (cone F S).edgeSet, e'.map (liftC b) = e := by
  constructor
  · intro he
    induction e using Sym2.inductionOn with
    | hf x y =>
    rw [mem_edgeSet] at he
    rcases x with _ | ⟨b, a⟩ <;> rcases y with _ | ⟨b', a'⟩
    · exact absurd he doubleCone_not_adj_none_none
    · exact ⟨b', s(none, some a'), by simpa using he, by simp⟩
    · exact ⟨b, s(some a, none), by simpa using he, by simp⟩
    · rw [doubleCone_adj_some_some] at he
      obtain ⟨rfl, he⟩ := he
      exact ⟨b, s(some a, some a'), by simpa using he, by simp⟩
  · rintro ⟨b, e', he', rfl⟩
    exact liftC_map_mem he'

theorem liftC_map_ne {e e' : Sym2 (Option V)} (he : e ∈ (cone F S).edgeSet) :
    e.map (liftC false) ≠ e'.map (liftC true) := by
  intro h
  obtain ⟨a, ha⟩ := cone_edge_has_some he
  have : some (false, a) ∈ e'.map (liftC true) := h ▸ Sym2.mem_map.mpr ⟨_, ha, rfl⟩
  obtain ⟨y, -, hy⟩ := Sym2.mem_map.mp this
  cases y <;> simp at hy

/-- A path of the cone starting at the apex, glued to its mirror image in the other copy. -/
theorem exists_join (P : GPath (cone F S)) (h : P.src = none) :
    ∃ Q : GPath (doubleCone F S),
      Q.edges.Perm (P.edges.map (Sym2.map (liftC false)) ++ P.edges.map (Sym2.map (liftC true))) := by
  obtain ⟨s, q, hs, hq, hn, hedges, -⟩ := cone_path_from_none P h
  have hf : ∀ b, ∀ e ∈ q.edges, e.map (liftC b) ∈ (doubleCone F S).edgeSet :=
    fun b e he => liftC_map_mem (q.edges_subset_edgeSet he)
  have h0 : (doubleCone F S).Adj (liftC false (some s)) none := by simpa using hs
  have h1 : (doubleCone F S).Adj none (liftC true (some s)) := by simpa using hs
  let w := (pushWalk (liftC false) q (hf false)).reverse.append
    (Walk.cons h0 (Walk.cons h1 (pushWalk (liftC true) q (hf true))))
  have hw : w.IsPath := by
    rw [Walk.isPath_def]
    simp only [w, Walk.support_append, Walk.support_reverse, Walk.support_cons, pushWalk_support,
      List.tail_cons]
    have hnd := hq.support_nodup
    rw [List.nodup_append]
    refine ⟨List.nodup_reverse.mpr (hnd.map (liftC_injective false)), ?_, ?_⟩
    · refine List.nodup_cons.mpr ⟨fun hm => ?_, hnd.map (liftC_injective true)⟩
      obtain ⟨x, hx, hx'⟩ := List.mem_map.mp hm
      exact hn (liftC_eq_none.mp hx' ▸ hx)
    · intro a ha b hb hab
      rw [List.mem_reverse] at ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      have hx0 : x ≠ none := fun h0 => hn (h0 ▸ hx)
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hx0 (liftC_eq_none.mp hab)
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
        have hy0 : y ≠ none := fun h0 => hn (h0 ▸ hy)
        rcases x with _ | x
        · exact hx0 rfl
        · rcases y with _ | y
          · exact hy0 rfl
          · simp at hab
  refine ⟨⟨_, _, w, hw, by simp only [w, Walk.length_append, Walk.length_cons]; omega⟩, ?_⟩
  show w.edges.Perm _
  simp only [w, Walk.edges_append, Walk.edges_reverse, Walk.edges_cons, pushWalk_edges, hedges,
    List.map_cons, Sym2.map_mk, liftC_none]
  rw [show s(liftC false (some s), (none : Option (Bool × V))) =
    s(none, liftC false (some s)) from Sym2.eq_swap]
  refine List.perm_middle.trans (List.Perm.cons _ ?_)
  exact (List.reverse_perm _).append_right _

theorem exists_double_item (P : GPath (cone F S))
    (hP : none ∈ P.walk.support → P.src = none ∨ P.tgt = none) :
    ∃ L : List (GPath (doubleCone F S)),
      (L.flatMap GPath.edges).Perm
        (P.edges.map (Sym2.map (liftC false)) ++ P.edges.map (Sym2.map (liftC true))) ∧
      L.length = P.outEndsAt := by
  have hne := P.src_ne_tgt
  by_cases hn : none ∈ P.walk.support
  · rcases hP hn with h | h
    · obtain ⟨Q, hQ⟩ := exists_join P h
      have ht : P.tgt ≠ none := fun ht => hne (h.trans ht.symm)
      refine ⟨[Q], by simpa using hQ, ?_⟩
      simp [GPath.outEndsAt, h, ht]
    · obtain ⟨Q, hQ⟩ := exists_join P.reverse h
      have hs : P.src ≠ none := fun hs => hne (hs.trans h.symm)
      refine ⟨[Q], ?_, ?_⟩
      · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        refine hQ.trans ?_
        rw [GPath.reverse_edges, List.map_reverse, List.map_reverse]
        exact (List.reverse_perm _).append (List.reverse_perm _)
      · simp [GPath.outEndsAt, h, hs]
  · have hs : P.src ≠ none := fun h => hn (h ▸ P.walk.start_mem_support)
    have ht : P.tgt ≠ none := fun h => hn (h ▸ P.walk.end_mem_support)
    let Q (b : Bool) : GPath (doubleCone F S) :=
      P.push (liftC b) (fun e he => liftC_map_mem (P.walk.edges_subset_edgeSet he))
        (fun _ _ _ _ h => liftC_injective b h)
    refine ⟨[Q false, Q true], ?_, ?_⟩
    · simp [Q]
    · simp [GPath.outEndsAt, hs, ht]

/-- **Doubling**: if the apex is only ever an end, the decomposition of the cone doubles to a
decomposition of the doubled cone with `outEnds` paths (apex paths are paired, the others
copied). -/
theorem exists_double [Fintype V] [DecidableEq V] (D : PathDecomp (cone F S))
    (hD : ∀ P ∈ D.paths, none ∈ P.walk.support → P.src = none ∨ P.tgt = none) :
    ∃ D₂ : PathDecomp (doubleCone F S), D₂.size = D.outEnds := by
  have hex : ∀ P : GPath (cone F S), ∃ L : List (GPath (doubleCone F S)), P ∈ D.paths →
      (L.flatMap GPath.edges).Perm
        (P.edges.map (Sym2.map (liftC false)) ++ P.edges.map (Sym2.map (liftC true))) ∧
      L.length = P.outEndsAt := by
    intro P
    by_cases hP : P ∈ D.paths
    · obtain ⟨L, hL⟩ := exists_double_item P (hD P hP)
      exact ⟨L, fun _ => hL⟩
    · exact ⟨[], fun h => absurd h hP⟩
  choose g hg using hex
  set E := D.paths.flatMap GPath.edges with hE
  let M := E.map (Sym2.map (liftC false)) ++ E.map (Sym2.map (liftC true))
  have hperm : ((D.paths.flatMap g).flatMap GPath.edges).Perm M := by
    rw [List.flatMap_assoc]
    refine (List.Perm.flatMap_left _ (fun P hP => (hg P hP).1)).trans ?_
    refine (List.flatMap_append_perm _ _ _).symm.trans ?_
    simp only [M, hE, List.map_flatMap]
    exact List.Perm.refl _
  have hnd : M.Nodup := by
    rw [List.nodup_append]
    refine ⟨D.nodup_edges.map (Sym2.map.injective (liftC_injective false)),
      D.nodup_edges.map (Sym2.map.injective (liftC_injective true)), ?_⟩
    intro a ha b hb hab
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    obtain ⟨e', -, rfl⟩ := List.mem_map.mp hb
    exact liftC_map_ne ((D.covers e).2 he) hab
  have hcov : ∀ e, e ∈ (doubleCone F S).edgeSet ↔ e ∈ M := by
    intro e
    rw [mem_doubleCone_edgeSet_iff]
    simp only [M, List.mem_append, List.mem_map, hE, ← D.covers]
    constructor
    · rintro ⟨b, e', he', rfl⟩
      cases b
      · exact Or.inl ⟨e', he', rfl⟩
      · exact Or.inr ⟨e', he', rfl⟩
    · rintro (⟨e', he', rfl⟩ | ⟨e', he', rfl⟩)
      · exact ⟨false, e', he', rfl⟩
      · exact ⟨true, e', he', rfl⟩
  refine ⟨PathDecomp.ofPerm _ M hperm hnd hcov, ?_⟩
  simp only [PathDecomp.size, PathDecomp.ofPerm_paths, List.length_flatMap,
    PathDecomp.outEnds_eq_sum]
  congr 1
  exact List.map_congr_left (fun P hP => (hg P hP).2)

theorem pathNumber_doubleCone_le [Fintype V] [DecidableEq V] (F : SimpleGraph V) (S : Finset V) :
    pathNumber (doubleCone F S) ≤ minOutEnds F S := by
  obtain ⟨D, hD⟩ := minOutEnds_spec F S
  obtain ⟨D', hends, hz⟩ := D.exists_split_all none
  have h1 : D'.outEnds = D.outEnds :=
    Finset.sum_congr rfl (fun v _ => hends (some v) (Option.some_ne_none v))
  obtain ⟨D₂, h₂⟩ := exists_double D' hz
  have := pathNumber_le D₂
  omega

/-- **Identity B, upper bound**: `p(W(F, S)) ≤ h + 1` (keep the pendant edge singly). -/
theorem pathNumber_wGraph_le [Fintype V] [DecidableEq V] (F : SimpleGraph V) (S : Finset V) :
    pathNumber (wGraph F S) ≤ minOutEnds F S + 1 :=
  (pathNumber_addLeaf_le_succ _ _).trans (Nat.add_le_add_right (pathNumber_doubleCone_le F S) 1)

/-! #### Identity B, lower bound: restrict to each copy -/

/-- The view of copy `β`: the other copy collapses onto the apex. -/
def sideView (β : Bool) : Option (Bool × V) → Option V
  | none => none
  | some p => if p.1 = β then some p.2 else none

/-- Vertices of copy `β`. -/
def onSide (β : Bool) : Option (Bool × V) → Bool
  | none => false
  | some p => decide (p.1 = β)

/-- Edges with a vertex in copy `β`. -/
def keptSide (β : Bool) : Sym2 (Option (Bool × V)) → Bool :=
  Sym2.lift ⟨fun x y => onSide β x || onSide β y, fun _ _ => Bool.or_comm _ _⟩

@[simp] theorem keptSide_mk (β : Bool) (x y : Option (Bool × V)) :
    keptSide β s(x, y) = (onSide β x || onSide β y) := rfl

/-- Vertices seen injectively by the view of copy `β`. -/
def TSide (β : Bool) : Set (Option (Bool × V)) := {x | x = none ∨ onSide β x = true}

theorem view_injOn (β : Bool) : Set.InjOn (sideView β) (TSide β : Set (Option (Bool × V))) := by
  rintro (_ | ⟨b, a⟩) hx (_ | ⟨b', a'⟩) hy h <;> simp_all [sideView, onSide, TSide]

theorem view_map_mem {β : Bool} {e : Sym2 (Option (Bool × V))} (he : e ∈ (doubleCone F S).edgeSet)
    (hT : ∀ x ∈ e, x ∈ TSide β) : e.map (sideView β) ∈ (cone F S).edgeSet := by
  induction e using Sym2.inductionOn with
  | hf x y =>
  have hx := hT x (Sym2.mem_mk_left _ _)
  have hy := hT y (Sym2.mem_mk_right _ _)
  rw [mem_edgeSet] at he
  rw [Sym2.map_mk, mem_edgeSet]
  rcases x with _ | ⟨b, a⟩ <;> rcases y with _ | ⟨b', a'⟩ <;> simp_all [sideView, onSide, TSide]

theorem side_hT (β : Bool) : ∀ e ∈ (doubleCone F S).edgeSet, keptSide β e = true →
    ∀ x ∈ e, x ∈ TSide β := by
  intro e he hk x hx
  induction e using Sym2.inductionOn with
  | hf a b =>
  rw [mem_edgeSet] at he
  rcases Sym2.mem_iff.mp hx with rfl | rfl
  · rcases x with _ | ⟨b1, a1⟩ <;> rcases b with _ | ⟨b2, a2⟩ <;> simp_all [TSide, onSide]
  · rcases a with _ | ⟨b1, a1⟩ <;> rcases x with _ | ⟨b2, a2⟩ <;> simp_all [TSide, onSide]

theorem side_hcov (β : Bool) : ∀ e', e' ∈ (cone F S).edgeSet ↔
    ∃ e ∈ (doubleCone F S).edgeSet, keptSide β e = true ∧ e.map (sideView β) = e' := by
  intro e'
  constructor
  · intro he'
    induction e' using Sym2.inductionOn with
    | hf x y =>
    rw [mem_edgeSet] at he'
    rcases x with _ | a <;> rcases y with _ | b
    · exact absurd he' cone_not_adj_none_none
    · exact ⟨s(none, some (β, b)), by simpa using he', by simp [onSide], by simp [sideView]⟩
    · exact ⟨s(some (β, a), none), by simpa using he', by simp [onSide], by simp [sideView]⟩
    · exact ⟨s(some (β, a), some (β, b)), by simpa using he', by simp [onSide], by simp [sideView]⟩
  · rintro ⟨e, he, hk, rfl⟩
    exact view_map_mem he (side_hT β e he hk)

theorem mem_map_view {β : Bool} {a : V} {e : Sym2 (Option (Bool × V))} :
    some a ∈ e.map (sideView β) ↔ some (β, a) ∈ e := by
  rw [Sym2.mem_map]
  constructor
  · rintro ⟨x, hx, hxa⟩
    rcases x with _ | ⟨b, c⟩
    · simp [sideView] at hxa
    · simp only [sideView] at hxa
      split_ifs at hxa with hb
      · simp only [Option.some.injEq] at hxa
        rw [← hb, ← hxa]
        exact hx
  · intro h
    exact ⟨_, h, by simp [sideView]⟩

theorem keptSide_of_mem {β : Bool} {a : V} {e : Sym2 (Option (Bool × V))}
    (h : some (β, a) ∈ e) : keptSide β e = true := by
  induction e using Sym2.inductionOn with
  | hf x y =>
  rcases Sym2.mem_iff.mp h with rfl | rfl <;> simp [onSide]

theorem twoCopies_walk_side {x y : Bool × V} (p : (twoCopies F).Walk x y) :
    ∀ z ∈ p.support, z.1 = x.1 := by
  induction p with
  | nil => intro z hz; rw [Walk.mem_support_nil_iff] at hz; rw [hz]
  | @cons a c b h p ih =>
    intro z hz
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · rfl
    · rw [ih z hz]; exact h.1.symm

theorem doubleCone_avoid_side {x y : Option (Bool × V)} (q : (doubleCone F S).Walk x y)
    (hn : none ∉ q.support) : ∃ b, ∀ z ∈ q.support, ∃ a, z = some (b, a) := by
  obtain ⟨a, _, q', -, -, hs, -⟩ := cone_walk_lift (G := twoCopies F) q hn
  refine ⟨a.1, fun z hz => ?_⟩
  have hz' : z ∈ q'.support.map some := by rw [hs]; exact hz
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz'
  exact ⟨w.2, by rw [← twoCopies_walk_side q' w hw]⟩

/-- After splitting at the apex, every path lies in one copy (plus possibly the apex). -/
theorem side_of_split (P : GPath (doubleCone F S))
    (hP : none ∈ P.walk.support → P.src = none ∨ P.tgt = none) :
    ∃ b, ∀ z ∈ P.walk.support, z = none ∨ ∃ a, z = some (b, a) := by
  have key : ∀ Q : GPath (doubleCone F S), Q.src = none →
      ∃ b, ∀ z ∈ Q.walk.support, z = none ∨ ∃ a, z = some (b, a) := by
    intro Q h
    obtain ⟨s, q, -, -, hnq, -, hsupp⟩ := cone_path_from_none (G := twoCopies F) Q h
    obtain ⟨b, hb⟩ := doubleCone_avoid_side q hnq
    refine ⟨b, fun z hz => ?_⟩
    have hz' : z ∈ none :: q.support := by rw [← hsupp]; exact hz
    rcases List.mem_cons.mp hz' with rfl | hz
    · exact Or.inl rfl
    · exact Or.inr (hb z hz)
  by_cases hn : none ∈ P.walk.support
  · rcases hP hn with h | h
    · exact key P h
    · obtain ⟨b, hb⟩ := key P.reverse h
      refine ⟨b, fun z hz => hb z ?_⟩
      show z ∈ P.walk.reverse.support
      rw [Walk.support_reverse, List.mem_reverse]
      exact hz
  · obtain ⟨b, hb⟩ := doubleCone_avoid_side P.walk hn
    exact ⟨b, fun z hz => Or.inr (hb z hz)⟩

theorem side_hasPiece (β : Bool) (P : GPath (doubleCone F S))
    (hside : ∃ b, ∀ z ∈ P.walk.support, z = none ∨ ∃ a, z = some (b, a)) :
    HasPiece (cone F S) (sideView β) (keptSide β) P := by
  obtain ⟨b, hb⟩ := hside
  by_cases hbβ : b = β
  · subst hbβ
    have hT : ∀ z ∈ P.walk.support, z ∈ TSide b := by
      intro z hz
      rcases hb z hz with rfl | ⟨a, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (by simp [onSide])
    refine hasPiece_of_walk P.walk P.isPath ?_ ?_ ?_
    · intro e he
      exact view_map_mem (P.walk.edges_subset_edgeSet he)
        (fun x hx => hT x (Walk.mem_support_of_mem_edge P.walk he hx))
    · intro x hx y hy h
      exact view_injOn b (hT x hx) (hT y hy) h
    · rw [GPath.edges, List.filter_eq_self.mpr]
      intro e he
      obtain ⟨a, ha⟩ := cone_edge_has_some (G := twoCopies F) (P.walk.edges_subset_edgeSet he)
      rcases hb _ (Walk.mem_support_of_mem_edge P.walk he ha) with h | ⟨c, hc⟩
      · exact absurd h (Option.some_ne_none a)
      · rw [hc] at ha
        exact keptSide_of_mem ha
  · apply hasPiece_none
    rw [List.filter_eq_nil_iff]
    intro e he hk
    induction e using Sym2.inductionOn with
    | hf x y =>
    have hx := hb x (P.walk.fst_mem_support_of_mem_edges he)
    have hy := hb y (P.walk.snd_mem_support_of_mem_edges he)
    rcases hx with rfl | ⟨a, rfl⟩ <;> rcases hy with rfl | ⟨c, rfl⟩ <;>
      simp [onSide, hbβ] at hk

/-- **Restriction to a copy.** If the apex is only ever an end, the paths of a decomposition of
the doubled cone restrict to a decomposition of the cone with the same ends in copy `β`. -/
theorem exists_side [Fintype V] [DecidableEq V] (D : PathDecomp (doubleCone F S))
    (hD : ∀ P ∈ D.paths, none ∈ P.walk.support → P.src = none ∨ P.tgt = none) (β : Bool) :
    ∃ D' : PathDecomp (cone F S), D'.outEnds = ∑ a : V, D.ends (some (β, a)) := by
  obtain ⟨D', -, -, hends⟩ := D.project_full (sideView β) (keptSide β) (TSide β) (view_injOn β)
    (side_hT β) (side_hcov β) (fun P hP => side_hasPiece β P (side_of_split P (hD P hP)))
  refine ⟨D', Finset.sum_congr rfl (fun a _ => ?_)⟩
  rw [hends (some a)]
  unfold PathDecomp.ends
  congr 1
  apply List.map_congr_left
  intro P _
  rw [GPath.endsAt_eq_ite]
  congr 2
  rw [List.countP_map, List.countP_filter]
  unfold GPath.incid
  apply List.countP_congr
  intro e _
  simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq, mem_map_view]
  exact ⟨fun h => h.1, fun h => ⟨h, keptSide_of_mem h⟩⟩

/-- Every decomposition of the doubled cone has `leafCost ≥ |S| + 2 q(F, S) + 1`. -/
theorem le_leafCost [Fintype V] [DecidableEq V] (D : PathDecomp (doubleCone F S)) :
    S.card + 2 * markedNumber F S + 1 ≤ leafCost D none := by
  obtain ⟨D', hends, hz⟩ := D.exists_split_all none
  obtain ⟨D₀, h₀⟩ := exists_side D' hz false
  obtain ⟨D₁, h₁⟩ := exists_side D' hz true
  have l₀ := le_outEnds D₀
  have l₁ := le_outEnds D₁
  have hsum : D.outEnds = ∑ a : V, D'.ends (some (false, a)) + ∑ a : V, D'.ends (some (true, a)) := by
    unfold PathDecomp.outEnds
    rw [Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
    simp only [hends _ (Option.some_ne_none _)]
  have h2 := D.two_mul_size_eq
  unfold leafCost
  split_ifs <;> omega

/-- **Identity B, lower bound**: `p(W(F, S)) ≥ |S| + 2 q(F, S) + 1`. A global partition restricts
to each copy keeping its ends away from the apex; there are `≥ 2h` such ends, plus one at the
leaf. -/
theorem le_pathNumber_wGraph [Fintype V] [DecidableEq V] (F : SimpleGraph V) (S : Finset V) :
    S.card + 2 * markedNumber F S + 1 ≤ pathNumber (wGraph F S) := by
  obtain ⟨D, hD⟩ := exists_leafCost_le (doubleCone F S) none
  exact (le_leafCost D).trans hD

/-- **Identity B**: `p(W(F, S)) = h + 1 = |S| + 2 q(F, S) + 1`. -/
theorem pathNumber_wGraph [Fintype V] [DecidableEq V] (F : SimpleGraph V) (S : Finset V) :
    pathNumber (wGraph F S) = S.card + 2 * markedNumber F S + 1 := by
  have h1 := pathNumber_wGraph_le F S
  have h2 := le_pathNumber_wGraph F S
  rw [minOutEnds_eq] at h1
  omega

theorem pathNumber_wGraph_eq_minOutEnds [Fintype V] [DecidableEq V] (F : SimpleGraph V)
    (S : Finset V) : pathNumber (wGraph F S) = minOutEnds F S + 1 := by
  rw [pathNumber_wGraph, minOutEnds_eq]

/-- **Gallai implies the marked bound** (the "Gallai ⇒ marked" direction of Theorem 1, for any
connected `F` and nonempty `S`): `W(F, S)` is connected of order `2|V| + 2`, so Gallai gives
`p(W) ≤ |V| + 1`, i.e. `q(F, S) ≤ (|V| - |S|) / 2`. -/
theorem markedNumber_le_of_gallai (hG : GallaiConjecture.{u}) [Fintype V] [DecidableEq V]
    (hF : F.Connected) (hS : S.Nonempty) :
    markedNumber F S ≤ (Fintype.card V - S.card) / 2 := by
  have hW := hG _ (wGraph F S) (wGraph_connected hF hS)
  rw [card_wGraph] at hW
  have h1 := le_pathNumber_wGraph F S
  have h2 : S.card ≤ Fintype.card V := Finset.card_le_univ S
  omega

end wgraph

/-! ### The converse: a single mark -/

section converse

variable {V : Type u} {F : SimpleGraph V} {S : Finset V}

theorem length_eq_cost_add_sites (M : MarkedPartition F S) :
    M.paths.length = markedCost M + (M.paths.filterMap Prod.snd).length := by
  unfold markedCost
  generalize M.paths = l
  induction l with
  | nil => simp
  | cons x l ih =>
    obtain ⟨a, o⟩ := x
    cases o <;> simp [ih] <;> omega

/-- At most `|S|` paths are assigned, so `p(F) ≤ q(F, S) + |S|`. -/
theorem pathNumber_le_markedNumber_add [Finite V] [DecidableEq V] (F : SimpleGraph V)
    (S : Finset V) : pathNumber F ≤ markedNumber F S + S.card := by
  obtain ⟨M, hM⟩ := markedNumber_spec F S
  have h1 : (M.paths.filterMap Prod.snd).length ≤ S.card := by
    rw [← List.toFinset_card_of_nodup M.sites_nodup]
    exact Finset.card_le_card (fun s hs => M.sites_mem (List.mem_toFinset.mp hs))
  have h2 := pathNumber_le M.decomp
  have h3 : M.decomp.size = M.paths.length := by
    simp [MarkedPartition.decomp, PathDecomp.size]
  have h4 := length_eq_cost_add_sites M
  omega

end converse

/-- The marked bound for every connected graph and every nonempty set of sites. -/
def MarkedBound : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (F : SimpleGraph V), F.Connected →
    ∀ S : Finset V, S.Nonempty → markedNumber F S ≤ (Fintype.card V - S.card) / 2

/-- **Gallai's conjecture is equivalent to the marked bound** (on all connected graphs and all
nonempty site sets). Forward: `markedNumber_le_of_gallai`. Backward: use a single mark. -/
theorem gallai_iff_markedBound : GallaiConjecture.{u} ↔ MarkedBound.{u} := by
  constructor
  · intro hG V _ _ F hF S hS
    exact markedNumber_le_of_gallai hG hF hS
  · intro hM W _ G hG
    classical
    obtain ⟨r⟩ := hG.nonempty
    have h1 := hM W G hG {r} (Finset.singleton_nonempty r)
    have h2 := pathNumber_le_markedNumber_add G {r}
    have h3 : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨r⟩
    rw [Finset.card_singleton] at h1 h2
    omega

end Gallai
