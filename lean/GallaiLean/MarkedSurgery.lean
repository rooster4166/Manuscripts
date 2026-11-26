import GallaiLean.Marked

/-!
# Surgery on marked partitions

A *partial marked partition* `PMP G E S` is a list of paths of `G`, each with an optional site, whose
edges are exactly the edge set `E` (each once). Sites lie in `S`, are ends of their paths and are
pairwise distinct. With `E = G.edgeSet` this is a `MarkedPartition G S` (`PMP.toMarked`).

All operations used in the block reduction of the marked bound are provided here, with exact cost
bookkeeping (the cost is the number of unassigned paths):

* `PMP.replace`: replace some paths by others with the same edges plus new ones;
  `PMP.replaceSub`: with some edges removed. `PMP.append`: union over disjoint edge sets.
* `PMP.forget`, `PMP.forgetAll`, `PMP.mono`, `PMP.castE`, `PMP.ofPerm`.
* `PMP.exists_join`: join two paths at a common end `x` when they meet only at `x`.
* `PMP.exists_split`: split a path at an internal vertex.
* `PMP.exists_extend`: extend a path at an end by a pendant edge; `PMP.addPath`: add a path.
* `PMP.exists_assign`: assign an unassigned path to one of its ends.
* `PMP.exists_trim`: delete a pendant edge.
* `PMP.push`: transport a marked partition along an injective graph map.
-/

open SimpleGraph
open scoped List

namespace Gallai

universe u v

variable {W : Type u} {G : SimpleGraph W}

/-! ### Lists of marked paths -/

/-- Edges of a list of marked paths. -/
def mEdges (l : List (GPath G × Option W)) : List (Sym2 W) := (l.map Prod.fst).flatMap GPath.edges

/-- Sites of a list of marked paths. -/
def mSites (l : List (GPath G × Option W)) : List W := l.filterMap Prod.snd

/-- Number of unassigned paths. -/
def mCost (l : List (GPath G × Option W)) : ℕ := l.countP (fun x => x.2.isNone)

@[simp] theorem mEdges_nil : mEdges ([] : List (GPath G × Option W)) = [] := rfl
@[simp] theorem mEdges_cons (y : GPath G × Option W) (l : List (GPath G × Option W)) :
    mEdges (y :: l) = y.1.edges ++ mEdges l := rfl
@[simp] theorem mEdges_append (l₁ l₂ : List (GPath G × Option W)) :
    mEdges (l₁ ++ l₂) = mEdges l₁ ++ mEdges l₂ := by
  simp [mEdges, List.flatMap_append]
@[simp] theorem mSites_nil : mSites ([] : List (GPath G × Option W)) = [] := rfl
@[simp] theorem mSites_cons (y : GPath G × Option W) (l : List (GPath G × Option W)) :
    mSites (y :: l) = y.2.toList ++ mSites l := by
  obtain ⟨P, o⟩ := y
  cases o <;> rfl
@[simp] theorem mSites_append (l₁ l₂ : List (GPath G × Option W)) :
    mSites (l₁ ++ l₂) = mSites l₁ ++ mSites l₂ := by
  simp [mSites, List.filterMap_append]
@[simp] theorem mCost_nil : mCost ([] : List (GPath G × Option W)) = 0 := rfl
@[simp] theorem mCost_cons (y : GPath G × Option W) (l : List (GPath G × Option W)) :
    mCost (y :: l) = mCost l + (if y.2.isNone then 1 else 0) := by
  simp only [mCost, List.countP_cons]
@[simp] theorem mCost_append (l₁ l₂ : List (GPath G × Option W)) :
    mCost (l₁ ++ l₂) = mCost l₁ + mCost l₂ := by
  simp [mCost, List.countP_append]

theorem mEdges_perm {l₁ l₂ : List (GPath G × Option W)} (h : l₁.Perm l₂) :
    (mEdges l₁).Perm (mEdges l₂) :=
  (h.map _).flatMap_right _

theorem mSites_perm {l₁ l₂ : List (GPath G × Option W)} (h : l₁.Perm l₂) :
    (mSites l₁).Perm (mSites l₂) :=
  h.filterMap _

theorem mCost_perm {l₁ l₂ : List (GPath G × Option W)} (h : l₁.Perm l₂) : mCost l₁ = mCost l₂ :=
  h.countP_eq _

theorem length_eq_mCost_add (l : List (GPath G × Option W)) :
    l.length = mCost l + (mSites l).length := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    obtain ⟨P, o⟩ := y
    cases o <;> simp [ih] <;> omega

/-- Sites are in `S` and are ends of their paths. -/
def SiteOK (S : Finset W) (l : List (GPath G × Option W)) : Prop :=
  ∀ y ∈ l, ∀ s, y.2 = some s → s ∈ S ∧ (y.1.src = s ∨ y.1.tgt = s)

theorem nodup_of_subperm {α : Type*} {l₁ l₂ : List α} (h : l₁.Subperm l₂) (h2 : l₂.Nodup) :
    l₁.Nodup := by
  obtain ⟨l, hp, hs⟩ := h
  exact hp.nodup_iff.mp (hs.nodup h2)

theorem SiteOK.of_subset {S : Finset W} {l l' : List (GPath G × Option W)} (h : SiteOK S l)
    (h' : ∀ y ∈ l', y ∈ l) : SiteOK S l' := fun y hy => h y (h' y hy)

theorem SiteOK.mono {S S' : Finset W} {l : List (GPath G × Option W)} (h : SiteOK S l)
    (hS : S ⊆ S') : SiteOK S' l := fun y hy s hs => ⟨hS (h y hy s hs).1, (h y hy s hs).2⟩

/-! ### Partial marked partitions -/

/-- A **partial marked partition** of the edge set `E` of `G` with sites in `S`. -/
structure PMP (G : SimpleGraph W) (E : Set (Sym2 W)) (S : Finset W) where
  /-- The paths, each with an optional site. -/
  paths : List (GPath G × Option W)
  nodup : (mEdges paths).Nodup
  covers : ∀ e, e ∈ E ↔ e ∈ mEdges paths
  site_ok : SiteOK S paths
  sites_nodup : (mSites paths).Nodup

namespace PMP

variable {E E' : Set (Sym2 W)} {S S' : Finset W}

/-- The cost of a partial marked partition. -/
abbrev cost (M : PMP G E S) : ℕ := mCost M.paths

theorem mem_E (M : PMP G E S) {y : GPath G × Option W} (hy : y ∈ M.paths) {e : Sym2 W}
    (he : e ∈ y.1.edges) : e ∈ E :=
  (M.covers e).2 (List.mem_flatMap.mpr ⟨y.1, List.mem_map_of_mem hy, he⟩)

theorem sites_mem (M : PMP G E S) {s : W} (hs : s ∈ mSites M.paths) : s ∈ S := by
  obtain ⟨y, hy, hys⟩ := List.mem_filterMap.mp hs
  exact (M.site_ok y hy s hys).1

theorem sites_length_le [DecidableEq W] (M : PMP G E S) : (mSites M.paths).length ≤ S.card := by
  rw [← List.toFinset_card_of_nodup M.sites_nodup]
  exact Finset.card_le_card (fun s hs => M.sites_mem (List.mem_toFinset.mp hs))

/-- Reorder the paths. -/
def ofPerm (M : PMP G E S) (l : List (GPath G × Option W)) (h : M.paths.Perm l) : PMP G E S where
  paths := l
  nodup := (mEdges_perm h).nodup_iff.mp M.nodup
  covers e := (M.covers e).trans (mEdges_perm h).mem_iff
  site_ok := M.site_ok.of_subset (fun _ hy => h.mem_iff.mpr hy)
  sites_nodup := (mSites_perm h).nodup_iff.mp M.sites_nodup

/-- Change the edge set along an equality. -/
def castE (M : PMP G E S) (h : E = E') : PMP G E' S where
  paths := M.paths
  nodup := M.nodup
  covers e := h ▸ M.covers e
  site_ok := M.site_ok
  sites_nodup := M.sites_nodup

/-- Enlarge the site set. -/
def mono (M : PMP G E S) (h : S ⊆ S') : PMP G E S' where
  paths := M.paths
  nodup := M.nodup
  covers := M.covers
  site_ok := M.site_ok.mono h
  sites_nodup := M.sites_nodup

/-- The empty partial marked partition. -/
def empty (S : Finset W) : PMP G ∅ S where
  paths := []
  nodup := List.nodup_nil
  covers e := by simp
  site_ok := fun _ hy => by simp at hy
  sites_nodup := List.nodup_nil

/-- Union over disjoint edge sets, when no site is used on both sides. -/
def append (M₁ : PMP G E S) (M₂ : PMP G E' S) (hE : ∀ e ∈ E, e ∉ E')
    (hs : ∀ s ∈ mSites M₁.paths, s ∉ mSites M₂.paths) : PMP G (E ∪ E') S where
  paths := M₁.paths ++ M₂.paths
  nodup := by
    rw [mEdges_append, List.nodup_append]
    refine ⟨M₁.nodup, M₂.nodup, fun a ha b hb hab => ?_⟩
    subst hab
    exact hE a ((M₁.covers a).2 ha) ((M₂.covers a).2 hb)
  covers e := by
    rw [Set.mem_union, M₁.covers, M₂.covers, mEdges_append, List.mem_append]
  site_ok := fun y hy => by
    rcases List.mem_append.mp hy with h | h
    · exact M₁.site_ok y h
    · exact M₂.site_ok y h
  sites_nodup := by
    rw [mSites_append, List.nodup_append]
    exact ⟨M₁.sites_nodup, M₂.sites_nodup, fun a ha b hb hab => hs a ha (hab ▸ hb)⟩

theorem replace_perm (M : PMP G E S) {A B rest : List (GPath G × Option W)}
    (hM : M.paths.Perm (A ++ rest)) {X : List (Sym2 W)} (hB : (mEdges B).Perm (mEdges A ++ X)) :
    (mEdges (B ++ rest)).Perm (mEdges M.paths ++ X) := by
  rw [mEdges_append]
  calc (mEdges B ++ mEdges rest).Perm ((mEdges A ++ X) ++ mEdges rest) := hB.append_right _
    _ = mEdges A ++ (X ++ mEdges rest) := List.append_assoc _ _ _
    _ ~ mEdges A ++ (mEdges rest ++ X) := List.perm_append_comm.append_left _
    _ = (mEdges A ++ mEdges rest) ++ X := (List.append_assoc _ _ _).symm
    _ ~ mEdges M.paths ++ X := by
      rw [← mEdges_append]
      exact (mEdges_perm hM).symm.append_right _

/-- Replace the paths `A` by the paths `B`, whose edges are those of `A` plus the new edges `X`. -/
def replace (M : PMP G E S) (A B rest : List (GPath G × Option W)) (hM : M.paths.Perm (A ++ rest))
    (X : List (Sym2 W)) (hB : (mEdges B).Perm (mEdges A ++ X)) (hXnd : X.Nodup)
    (hX : ∀ e ∈ X, e ∉ E) (hok : SiteOK S B) (hs : (mSites B ++ mSites rest).Nodup) :
    PMP G (E ∪ {e | e ∈ X}) S where
  paths := B ++ rest
  nodup := by
    refine (M.replace_perm hM hB).nodup_iff.mpr ?_
    rw [List.nodup_append]
    exact ⟨M.nodup, hXnd, fun a ha b hb hab => hX b hb (hab ▸ (M.covers a).2 ha)⟩
  covers e := by
    rw [(M.replace_perm hM hB).mem_iff, List.mem_append, Set.mem_union, M.covers]
    rfl
  site_ok := fun y hy => by
    rcases List.mem_append.mp hy with h | h
    · exact hok y h
    · exact M.site_ok y (hM.mem_iff.mpr (List.mem_append_right _ h))
  sites_nodup := by rw [mSites_append]; exact hs

@[simp] theorem replace_paths (M : PMP G E S) (A B rest hM X hB hXnd hX hok hs) :
    (M.replace A B rest hM X hB hXnd hX hok hs).paths = B ++ rest := rfl

/-- `replace` without new edges. -/
def replace' (M : PMP G E S) (A B rest : List (GPath G × Option W)) (hM : M.paths.Perm (A ++ rest))
    (hB : (mEdges B).Perm (mEdges A)) (hok : SiteOK S B) (hs : (mSites B ++ mSites rest).Nodup) :
    PMP G E S :=
  (M.replace A B rest hM [] (by simpa using hB) List.nodup_nil (by simp) hok hs).castE
    (by ext e; simp)

@[simp] theorem replace'_paths (M : PMP G E S) (A B rest hM hB hok hs) :
    (M.replace' A B rest hM hB hok hs).paths = B ++ rest := rfl

/-- The site condition for a replacement whose sites are among the replaced ones. -/
theorem sites_nodup_of_subperm (M : PMP G E S) {A B rest : List (GPath G × Option W)}
    (hM : M.paths.Perm (A ++ rest)) (h : (mSites B).Subperm (mSites A)) :
    (mSites B ++ mSites rest).Nodup := by
  have h1 : (mSites (A ++ rest)).Nodup := (mSites_perm hM).nodup_iff.mp M.sites_nodup
  rw [mSites_append] at h1
  exact nodup_of_subperm ((List.subperm_append_right _).mpr h) h1

/-- The site condition for a replacement adding one new site. -/
theorem sites_nodup_of_new (M : PMP G E S) {A B rest : List (GPath G × Option W)}
    (hM : M.paths.Perm (A ++ rest)) {w : W} (hw : w ∉ mSites M.paths)
    (h : (mSites B).Subperm (w :: mSites A)) : (mSites B ++ mSites rest).Nodup := by
  have h1 : (mSites (A ++ rest)).Nodup := (mSites_perm hM).nodup_iff.mp M.sites_nodup
  have hw' : w ∉ mSites (A ++ rest) := fun h => hw ((mSites_perm hM).mem_iff.mpr h)
  rw [mSites_append] at h1 hw'
  exact nodup_of_subperm ((List.subperm_append_right _).mpr h) (List.nodup_cons.mpr ⟨hw', h1⟩)

/-- Replace the paths `A` by `B`, whose edges are those of `A` minus the edges `Y`. -/
def replaceSub (M : PMP G E S) (A B rest : List (GPath G × Option W)) (hM : M.paths.Perm (A ++ rest))
    (Y : List (Sym2 W)) (hB : (mEdges B ++ Y).Perm (mEdges A)) (hok : SiteOK S B)
    (hs : (mSites B ++ mSites rest).Nodup) : PMP G (E \ {e | e ∈ Y}) S where
  paths := B ++ rest
  nodup := by
    have h1 : (mEdges (B ++ rest) ++ Y).Perm (mEdges M.paths) := by
      rw [mEdges_append]
      calc (mEdges B ++ mEdges rest ++ Y).Perm (mEdges B ++ Y ++ mEdges rest) := by
            rw [List.append_assoc, List.append_assoc]
            exact List.perm_append_comm.append_left _
        _ ~ mEdges A ++ mEdges rest := hB.append_right _
        _ ~ mEdges M.paths := by rw [← mEdges_append]; exact (mEdges_perm hM).symm
    exact (List.nodup_append.mp (h1.nodup_iff.mpr M.nodup)).1
  covers e := by
    have h1 : (mEdges (B ++ rest) ++ Y).Perm (mEdges M.paths) := by
      rw [mEdges_append]
      calc (mEdges B ++ mEdges rest ++ Y).Perm (mEdges B ++ Y ++ mEdges rest) := by
            rw [List.append_assoc, List.append_assoc]
            exact List.perm_append_comm.append_left _
        _ ~ mEdges A ++ mEdges rest := hB.append_right _
        _ ~ mEdges M.paths := by rw [← mEdges_append]; exact (mEdges_perm hM).symm
    have hnd := h1.nodup_iff.mpr M.nodup
    rw [Set.mem_sdiff, M.covers, ← h1.mem_iff, List.mem_append]
    constructor
    · rintro ⟨h | h, hY⟩
      · exact h
      · exact absurd h hY
    · intro h
      exact ⟨Or.inl h, fun hY => (List.nodup_append.mp hnd).2.2 _ h _ hY rfl⟩
  site_ok := fun y hy => by
    rcases List.mem_append.mp hy with h | h
    · exact hok y h
    · exact M.site_ok y (hM.mem_iff.mpr (List.mem_append_right _ h))
  sites_nodup := by rw [mSites_append]; exact hs

@[simp] theorem replaceSub_paths (M : PMP G E S) (A B rest hM Y hB hok hs) :
    (M.replaceSub A B rest hM Y hB hok hs).paths = B ++ rest := rfl


theorem exists_mem_of_mem_E (M : PMP G E S) {e : Sym2 W} (he : e ∈ E) :
    ∃ y ∈ M.paths, e ∈ y.1.edges := by
  obtain ⟨P, hP, heP⟩ := List.mem_flatMap.mp ((M.covers e).1 he)
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hP
  exact ⟨y, hy, heP⟩

/-- Forget one site. -/
def forgetOne [DecidableEq W] (s : W) (y : GPath G × Option W) : GPath G × Option W :=
  if y.2 = some s then (y.1, none) else y

@[simp] theorem forgetOne_fst [DecidableEq W] (s : W) (y : GPath G × Option W) : (forgetOne s y).1 = y.1 := by
  unfold forgetOne; split_ifs <;> rfl

theorem mEdges_map_forgetOne [DecidableEq W] (s : W) (l : List (GPath G × Option W)) :
    mEdges (l.map (forgetOne s)) = mEdges l := by
  simp [mEdges, List.map_map, Function.comp_def]

theorem mSites_map_forgetOne [DecidableEq W] (s : W) (l : List (GPath G × Option W)) :
    mSites (l.map (forgetOne s)) = (mSites l).filter (fun t => t ≠ s) := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    obtain ⟨P, o⟩ := y
    cases o with
    | none => simp [forgetOne, ih]
    | some t =>
      by_cases h : t = s
      · subst h; simp [forgetOne, ih]
      · simp [forgetOne, h, ih]

theorem mCost_map_forgetOne [DecidableEq W] (s : W) (l : List (GPath G × Option W)) :
    mCost (l.map (forgetOne s)) = mCost l + (mSites l).count s := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    obtain ⟨P, o⟩ := y
    cases o with
    | none => simp [forgetOne, ih]; omega
    | some t =>
      by_cases h : t = s
      · subst h; simp [forgetOne, ih]; omega
      · simp [forgetOne, h, ih]

/-- Forget the site `s`. -/
def forget [DecidableEq W] (M : PMP G E S) (s : W) : PMP G E (S.erase s) where
  paths := M.paths.map (forgetOne s)
  nodup := by rw [mEdges_map_forgetOne]; exact M.nodup
  covers e := by rw [mEdges_map_forgetOne]; exact M.covers e
  site_ok := by
    intro y hy t ht
    obtain ⟨y₀, hy₀, rfl⟩ := List.mem_map.mp hy
    by_cases h : y₀.2 = some s
    · simp [forgetOne, h] at ht
    · simp only [forgetOne, h, if_false] at ht ⊢
      obtain ⟨h1, h2⟩ := M.site_ok y₀ hy₀ t ht
      refine ⟨Finset.mem_erase.mpr ⟨fun hts => h (hts ▸ ht), h1⟩, h2⟩
  sites_nodup := by
    rw [mSites_map_forgetOne]
    exact M.sites_nodup.filter _

@[simp] theorem forget_paths [DecidableEq W] (M : PMP G E S) (s : W) :
    (M.forget s).paths = M.paths.map (forgetOne s) := rfl

theorem forget_cost_le [DecidableEq W] (M : PMP G E S) (s : W) :
    (M.forget s).cost ≤ M.cost + 1 := by
  show mCost (M.paths.map (forgetOne s)) ≤ mCost M.paths + 1
  rw [mCost_map_forgetOne]
  have := List.nodup_iff_count_le_one.mp M.sites_nodup s
  omega

theorem forget_cost_of_not_mem [DecidableEq W] (M : PMP G E S) {s : W}
    (hs : s ∉ mSites M.paths) : (M.forget s).cost = M.cost := by
  show mCost (M.paths.map (forgetOne s)) = mCost M.paths
  rw [mCost_map_forgetOne, List.count_eq_zero_of_not_mem hs, add_zero]

theorem not_mem_sites_forget [DecidableEq W] (M : PMP G E S) (s : W) :
    s ∉ mSites (M.forget s).paths := by
  simp [mSites_map_forgetOne]

theorem forget_length [DecidableEq W] (M : PMP G E S) (s : W) :
    (M.forget s).paths.length = M.paths.length := by simp

/-- Forget all sites. -/
def forgetAll (M : PMP G E S) (S' : Finset W) : PMP G E S' where
  paths := M.paths.map (fun y => (y.1, none))
  nodup := by simpa [mEdges, List.map_map, Function.comp_def] using M.nodup
  covers e := by simpa [mEdges, List.map_map, Function.comp_def] using M.covers e
  site_ok := by
    intro y hy t ht
    obtain ⟨y₀, -, rfl⟩ := List.mem_map.mp hy
    simp at ht
  sites_nodup := by simp [mSites]

theorem forgetAll_cost (M : PMP G E S) (S' : Finset W) :
    (M.forgetAll S').cost = M.paths.length := by
  simp [cost, forgetAll, mCost, List.countP_map, Function.comp_def]

theorem forgetAll_sites (M : PMP G E S) (S' : Finset W) :
    mSites (M.forgetAll S').paths = [] := by simp [forgetAll, mSites]

end PMP

/-! ### Operations on single paths -/

namespace GPath

theorem exists_orient_tgt (P : GPath G) {x : W} (h : P.src = x ∨ P.tgt = x) :
    ∃ P' : GPath G, P'.tgt = x ∧ P'.edges.Perm P.edges ∧
      (∀ v, v ∈ P'.walk.support ↔ v ∈ P.walk.support) ∧
      (∀ v, (P'.src = v ∨ P'.tgt = v) ↔ (P.src = v ∨ P.tgt = v)) := by
  rcases h with h | h
  · refine ⟨P.reverse, h, by simp [List.reverse_perm], ?_, fun v => ?_⟩
    · intro v; simp [GPath.reverse, Walk.support_reverse]
    · simp only [GPath.reverse]; tauto
  · exact ⟨P, h, List.Perm.refl _, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem exists_orient_src (P : GPath G) {x : W} (h : P.src = x ∨ P.tgt = x) :
    ∃ P' : GPath G, P'.src = x ∧ P'.edges.Perm P.edges ∧
      (∀ v, v ∈ P'.walk.support ↔ v ∈ P.walk.support) ∧
      (∀ v, (P'.src = v ∨ P'.tgt = v) ↔ (P.src = v ∨ P.tgt = v)) := by
  rcases h with h | h
  · exact ⟨P, h, List.Perm.refl _, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  · refine ⟨P.reverse, h, by simp [List.reverse_perm], ?_, fun v => ?_⟩
    · intro v; simp [GPath.reverse, Walk.support_reverse]
    · simp only [GPath.reverse]; tauto

/-- Join two paths meeting only at their common end `x`. -/
theorem exists_join (P Q : GPath G) {x : W} (hP : P.tgt = x) (hQ : Q.src = x)
    (hdisj : ∀ v ∈ P.walk.support, v ∈ Q.walk.support → v = x) :
    ∃ R : GPath G, R.src = P.src ∧ R.tgt = Q.tgt ∧ R.edges = P.edges ++ Q.edges ∧
      ∀ v ∈ R.walk.support, v ∈ P.walk.support ∨ v ∈ Q.walk.support := by
  obtain ⟨a, b, p, hp, hpos⟩ := P
  obtain ⟨c, d, q, hq, hqpos⟩ := Q
  simp only at hP hQ hdisj ⊢
  subst hP
  subst hQ
  have hpq : (p.append q).IsPath := by
    rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
    have hqn := hq.support_nodup
    rw [← Walk.cons_tail_support q, List.nodup_cons] at hqn
    refine ⟨hp.support_nodup, hqn.2, fun v hv w hw hvw => ?_⟩
    subst hvw
    have hvq : v ∈ q.support := by rw [← Walk.cons_tail_support q]; exact List.mem_cons_of_mem _ hw
    have := hdisj v hv hvq
    subst this
    exact hqn.1 hw
  refine ⟨⟨a, d, p.append q, hpq, by simp; omega⟩, rfl, rfl, by simp [GPath.edges], ?_⟩
  intro v hv
  exact (Walk.mem_support_append_iff p q).mp hv

/-- Split a path at an internal vertex. -/
theorem exists_split (P : GPath G) {x : W} (hx : x ∈ P.walk.support) (hs : P.src ≠ x)
    (ht : P.tgt ≠ x) :
    ∃ P₁ P₂ : GPath G, P₁.src = P.src ∧ P₁.tgt = x ∧ P₂.src = x ∧ P₂.tgt = P.tgt ∧
      P.edges = P₁.edges ++ P₂.edges ∧ (∀ v ∈ P₁.walk.support, v ∈ P.walk.support) ∧
      (∀ v ∈ P₂.walk.support, v ∈ P.walk.support) := by
  obtain ⟨q₁, q₂, hq⟩ := Walk.mem_support_iff_exists_append.mp hx
  have hpath : (q₁.append q₂).IsPath := hq ▸ P.isPath
  have h₁ : 0 < q₁.length := by
    by_contra hc
    exact hs (Walk.eq_of_length_eq_zero (p := q₁) (by omega))
  have h₂ : 0 < q₂.length := by
    by_contra hc
    exact ht (Walk.eq_of_length_eq_zero (p := q₂) (by omega)).symm
  refine ⟨⟨_, _, q₁, Walk.isPath_of_append_left hpath, h₁⟩,
    ⟨_, _, q₂, Walk.isPath_of_append_right hpath, h₂⟩, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · show P.walk.edges = q₁.edges ++ q₂.edges
    rw [hq, Walk.edges_append]
  · intro v hv
    rw [hq]
    exact (Walk.mem_support_append_iff _ _).mpr (Or.inl hv)
  · intro v hv
    rw [hq]
    exact (Walk.mem_support_append_iff _ _).mpr (Or.inr hv)

/-- Every vertex of a path lies on one of its edges. -/
theorem exists_edge_of_mem_support (P : GPath G) {v : W} (hv : v ∈ P.walk.support) :
    ∃ e ∈ P.edges, v ∈ e := by
  obtain ⟨a, b, p, hp, hpos⟩ := P
  simp only [GPath.edges] at hv ⊢
  clear hp
  induction p with
  | nil => simp at hpos
  | @cons a c b h q ih =>
    rw [Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ⟨s(v, c), by simp, Sym2.mem_mk_left _ _⟩
    · cases q with
      | nil =>
        rw [Walk.support_nil, List.mem_singleton] at hv
        subst hv
        exact ⟨s(a, v), by simp, Sym2.mem_mk_right _ _⟩
      | cons h' q' =>
        obtain ⟨e, he, hve⟩ := ih (by simp) hv
        exact ⟨e, by simp only [Walk.edges_cons, List.mem_cons] at he ⊢; tauto, hve⟩

theorem support_subset_of_edges (P : GPath G) {U : Set W} (h : ∀ e ∈ P.edges, ∀ v ∈ e, v ∈ U) :
    ∀ v ∈ P.walk.support, v ∈ U := by
  intro v hv
  obtain ⟨e, he, hve⟩ := P.exists_edge_of_mem_support hv
  exact h e he v hve

theorem edges_nodup (P : GPath G) : P.edges.Nodup := P.isPath.isTrail.edges_nodup

end GPath

namespace PMP

variable {E E' : Set (Sym2 W)} {S S' : Finset W}

/-- **Join** an unassigned path `P` and a path `Q` (not assigned at `x`) at their common end `x`,
when they meet only at `x`. -/
theorem exists_join (M : PMP G E S) {P Q : GPath G} {o : Option W}
    {rest : List (GPath G × Option W)} (hM : M.paths.Perm ((P, none) :: (Q, o) :: rest)) {x : W}
    (hP : P.src = x ∨ P.tgt = x) (hQ : Q.src = x ∨ Q.tgt = x) (ho : ∀ s, o = some s → s ≠ x)
    (hdisj : ∀ v ∈ P.walk.support, v ∈ Q.walk.support → v = x) :
    ∃ (M' : PMP G E S) (R : GPath G), M'.paths = (R, o) :: rest := by
  obtain ⟨P', hP't, hP'e, hP's, hP'end⟩ := P.exists_orient_tgt hP
  obtain ⟨Q', hQ's, hQ'e, hQ'sup, hQ'end⟩ := Q.exists_orient_src hQ
  obtain ⟨R, hRs, hRt, hRe, -⟩ := GPath.exists_join P' Q' hP't hQ's
    (fun v h1 h2 => hdisj v ((hP's v).mp h1) ((hQ'sup v).mp h2))
  have hok : SiteOK S [(R, o)] := by
    intro y hy s hs
    rw [List.mem_singleton] at hy
    subst hy
    have h1 := M.site_ok (Q, o) (hM.mem_iff.mpr (by simp)) s hs
    refine ⟨h1.1, Or.inr ?_⟩
    have h2 := (hQ'end s).mpr h1.2
    rcases h2 with h2 | h2
    · exact absurd (hQ's ▸ h2.symm) (ho s hs)
    · exact hRt.trans h2
  have hM' : M.paths.Perm ([(P, none), (Q, o)] ++ rest) := by simpa using hM
  refine ⟨M.replace' [(P, none), (Q, o)] [(R, o)] rest hM' ?_ hok
    (M.sites_nodup_of_subperm hM' (by
      simp only [mSites_cons, mSites_nil, List.append_nil, Option.toList_none, List.nil_append]
      exact (List.Perm.refl _).subperm)), R, rfl⟩
  simp only [mEdges_cons, mEdges_nil, List.append_nil, hRe]
  exact hP'e.append hQ'e

/-- **Split** a path at an internal vertex `x`; the site goes with the half containing it. -/
theorem exists_split (M : PMP G E S) {P : GPath G} {o : Option W}
    {rest : List (GPath G × Option W)} (hM : M.paths.Perm ((P, o) :: rest)) {x : W}
    (hx : x ∈ P.walk.support) (hs : P.src ≠ x) (ht : P.tgt ≠ x) :
    ∃ (M' : PMP G E S) (P₁ P₂ : GPath G) (o₁ o₂ : Option W),
      M'.paths = (P₁, o₁) :: (P₂, o₂) :: rest ∧ P₁.tgt = x ∧ P₂.src = x ∧
      (∀ v ∈ P₁.walk.support, v ∈ P.walk.support) ∧ (∀ v ∈ P₂.walk.support, v ∈ P.walk.support) ∧
      (∀ s, o₁ = some s → s ≠ x) ∧ (∀ s, o₂ = some s → s ≠ x) ∧
      mCost [(P₁, o₁), (P₂, o₂)] = mCost [(P, o)] + 1 := by
  obtain ⟨P₁, P₂, h1s, h1t, h2s, h2t, he, hsup1, hsup2⟩ := P.exists_split hx hs ht
  have hPo : ∀ s, o = some s → s ∈ S ∧ (P.src = s ∨ P.tgt = s) :=
    M.site_ok (P, o) (hM.mem_iff.mpr (by simp))
  -- the site goes to the half containing it
  obtain ⟨o₁, o₂, hok, hsub, hcost, ho₁, ho₂⟩ : ∃ o₁ o₂ : Option W,
      SiteOK S [(P₁, o₁), (P₂, o₂)] ∧ (mSites [(P₁, o₁), (P₂, o₂)]).Subperm (mSites [(P, o)]) ∧
      mCost [(P₁, o₁), (P₂, o₂)] = mCost [(P, o)] + 1 ∧
      (∀ s, o₁ = some s → s ≠ x) ∧ (∀ s, o₂ = some s → s ≠ x) := by
    cases o with
    | none =>
      refine ⟨none, none, ?_, by simp, by simp, by simp, by simp⟩
      intro y hy s hs; simp at hy; rcases hy with rfl | rfl <;> simp at hs
    | some s =>
      obtain ⟨hsS, hsend⟩ := hPo s rfl
      rcases hsend with h | h
      · refine ⟨some s, none, ?_, by simp, by simp, ?_, by simp⟩
        · intro y hy t ht
          simp at hy
          rcases hy with rfl | rfl
          · simp at ht; subst ht; exact ⟨hsS, Or.inl (h1s.trans h)⟩
          · simp at ht
        · intro t ht; simp at ht; subst ht; exact fun h' => hs (h.trans h')
      · refine ⟨none, some s, ?_, by simp, by simp, by simp, ?_⟩
        · intro y hy t ht
          simp at hy
          rcases hy with rfl | rfl
          · simp at ht
          · simp at ht; subst ht; exact ⟨hsS, Or.inr (h2t.trans h)⟩
        · intro t ht; simp at ht; subst ht; exact fun h' => ht (h.trans h')
  have hM' : M.paths.Perm ([(P, o)] ++ rest) := by simpa using hM
  refine ⟨M.replace' [(P, o)] [(P₁, o₁), (P₂, o₂)] rest hM' ?_ hok
    (M.sites_nodup_of_subperm hM' hsub), P₁, P₂, o₁, o₂, rfl, h1t, h2s,
    hsup1, hsup2, ho₁, ho₂, hcost⟩
  simp only [mEdges_cons, mEdges_nil, List.append_nil, he]
  exact List.Perm.refl _

/-- **Assign** an unassigned path to one of its ends. -/
theorem exists_assign (M : PMP G E S) {P : GPath G} {rest : List (GPath G × Option W)}
    (hM : M.paths.Perm ((P, none) :: rest)) {s : W} (hsS : s ∈ S) (hs : P.src = s ∨ P.tgt = s)
    (hnew : s ∉ mSites M.paths) : ∃ M' : PMP G E S, M'.paths = (P, some s) :: rest := by
  have hok : SiteOK S [(P, some s)] := by
    intro y hy t ht
    rw [List.mem_singleton] at hy
    subst hy
    simp only [Option.some.injEq] at ht
    subst ht
    exact ⟨hsS, hs⟩
  have hM' : M.paths.Perm ([(P, none)] ++ rest) := by simpa using hM
  exact ⟨M.replace' [(P, none)] [(P, some s)] rest hM' (by simp) hok
    (M.sites_nodup_of_new hM' hnew (by simp)), rfl⟩

/-- **Add** a path on new edges. -/
def addPath (M : PMP G E S) (P : GPath G) (o : Option W) (hok : SiteOK S [(P, o)])
    (hE : ∀ e ∈ P.edges, e ∉ E) (hnew : ∀ s, o = some s → s ∉ mSites M.paths) :
    PMP G (E ∪ {e | e ∈ P.edges}) S :=
  M.replace [] [(P, o)] M.paths (by simp) P.edges (by simp) P.edges_nodup hE hok (by
    have := M.sites_nodup
    cases o with
    | none => simpa using this
    | some s =>
      simp only [mSites_cons, Option.toList_some, mSites_nil, List.append_nil, List.singleton_append]
      exact List.nodup_cons.mpr ⟨hnew s rfl, this⟩)

@[simp] theorem addPath_paths (M : PMP G E S) (P o hok hE hnew) :
    (M.addPath P o hok hE hnew).paths = (P, o) :: M.paths := rfl

/-- **Extend** an unassigned path with an end at `v` by a pendant edge `wv`. -/
theorem exists_extend (M : PMP G E S) {P : GPath G} {rest : List (GPath G × Option W)}
    (hM : M.paths.Perm ((P, none) :: rest)) {v w : W} (hv : P.src = v ∨ P.tgt = v)
    (hadj : G.Adj w v) (hw : w ∉ P.walk.support) (hwv : s(w, v) ∉ E) (o' : Option W)
    (ho' : o' = none ∨ (o' = some w ∧ w ∈ S ∧ w ∉ mSites M.paths)) :
    ∃ (M' : PMP G (E ∪ {e | e ∈ [s(w, v)]}) S) (P' : GPath G),
      M'.paths = (P', o') :: rest ∧ P'.src = w := by
  obtain ⟨P₁, hP₁s, hP₁e, hP₁sup, -⟩ := P.exists_orient_src hv
  have hw₁ : w ∉ P₁.walk.support := fun h => hw ((hP₁sup w).mp h)
  let P' : GPath G :=
    { src := w
      tgt := P₁.tgt
      walk := Walk.cons (hP₁s ▸ hadj) P₁.walk
      isPath := by rw [Walk.cons_isPath_iff]; exact ⟨P₁.isPath, hw₁⟩
      pos := by simp }
  have hP'e : P'.edges = s(w, P₁.src) :: P₁.edges := rfl
  have hok : SiteOK S [(P', o')] := by
    intro y hy t ht
    rw [List.mem_singleton] at hy
    subst hy
    rcases ho' with h | ⟨h, hwS, -⟩
    · rw [h] at ht; simp at ht
    · rw [h] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      exact ⟨hwS, Or.inl rfl⟩
  have hM' : M.paths.Perm ([(P, none)] ++ rest) := by simpa using hM
  have hs : (mSites [(P', o')] ++ mSites rest).Nodup := by
    rcases ho' with h | ⟨h, -, hwM⟩
    · subst h
      exact M.sites_nodup_of_subperm hM' (by simp)
    · subst h
      exact M.sites_nodup_of_new hM' hwM (by simp)
  refine ⟨M.replace [(P, none)] [(P', o')] rest hM' [s(w, v)] ?_
    (List.nodup_singleton _) (by simpa using hwv) hok hs, P', rfl, rfl⟩
  simp only [mEdges_cons, mEdges_nil, List.append_nil, hP'e, hP₁s]
  exact (List.perm_append_singleton _ _).symm.trans (hP₁e.append_right _)

end PMP

end Gallai
