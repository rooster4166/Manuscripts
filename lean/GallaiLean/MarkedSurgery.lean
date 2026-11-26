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
  site_ok := M.site_ok.of_subset (fun y hy => h.mem_iff.mpr hy)
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

end PMP

end Gallai
