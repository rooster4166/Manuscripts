import GallaiLean.MarkedSurgery

/-!
# Reducing the marked bound to two-connected graphs

Marked-reduction manuscript, §2 and the sufficiency half of Theorem 1.

The induction works inside one vertex type `W`: an instance is a graph `G` all of whose edges lie
in a finite vertex set `U` (`EdgesIn G U`), connected on `U` (`ConnOn G U`). Sub-instances are
restrictions `restrict G U'`. A *separation* `Sep G U x C` is a cut vertex `x` with a nonempty
part `C` of `U - x` that has no edges to the rest `U - x - C`.

This file: restrictions, separations, leaves and the connectivity of the pieces.
-/

open SimpleGraph

set_option linter.unusedSectionVars false

namespace Gallai

universe u

variable {W : Type u} [DecidableEq W] {G : SimpleGraph W}

/-! ### Restrictions -/

/-- `G` restricted to the vertex set `U`. -/
def restrict (G : SimpleGraph W) (U : Finset W) : SimpleGraph W where
  Adj a b := G.Adj a b ∧ a ∈ U ∧ b ∈ U
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩

@[simp] theorem restrict_adj {U : Finset W} {a b : W} :
    (restrict G U).Adj a b ↔ G.Adj a b ∧ a ∈ U ∧ b ∈ U := Iff.rfl

theorem restrict_le (U : Finset W) : ∀ a b, (restrict G U).Adj a b → G.Adj a b :=
  fun _ _ h => h.1

theorem restrict_mono {U U' : Finset W} (h : U ⊆ U') :
    ∀ a b, (restrict G U).Adj a b → (restrict G U').Adj a b :=
  fun _ _ hab => ⟨hab.1, h hab.2.1, h hab.2.2⟩

theorem restrict_restrict {U U' : Finset W} (h : U' ⊆ U) :
    restrict (restrict G U) U' = restrict G U' := by
  ext a b
  simp only [restrict_adj]
  constructor
  · rintro ⟨⟨h1, -, -⟩, h2, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h h2, h h3⟩, h2, h3⟩

theorem mem_restrict_edgeSet {U : Finset W} {e : Sym2 W} :
    e ∈ (restrict G U).edgeSet ↔ e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ U := by
  induction e using Sym2.inductionOn with
  | hf a b =>
  simp only [mem_edgeSet, restrict_adj, Sym2.mem_iff, forall_eq_or_imp, forall_eq]

/-- All edges of `G` lie inside `U`. -/
def EdgesIn (G : SimpleGraph W) (U : Finset W) : Prop := ∀ a b, G.Adj a b → a ∈ U ∧ b ∈ U

/-- `G` is connected on `U`. -/
def ConnOn (G : SimpleGraph W) (U : Finset W) : Prop := ∀ a ∈ U, ∀ b ∈ U, G.Reachable a b

/-- `C` is closed in `G` except through `x`. -/
def Closed (G : SimpleGraph W) (x : W) (C : Finset W) : Prop :=
  ∀ a ∈ C, ∀ b, G.Adj a b → b ∈ C ∨ b = x

/-- A separation of `U` at the cut vertex `x`: `C` and `U - x - C` are nonempty and have no edge
between them. -/
def Sep (G : SimpleGraph W) (U : Finset W) (x : W) (C : Finset W) : Prop :=
  x ∈ U ∧ C ⊆ U.erase x ∧ C.Nonempty ∧ (U.erase x \ C).Nonempty ∧ Closed G x C

/-- Two-connected on `U`: at least three vertices, connected, and no cut vertex. -/
def TwoConnOn (G : SimpleGraph W) (U : Finset W) : Prop :=
  3 ≤ U.card ∧ ConnOn G U ∧ ∀ x C, ¬ Sep G U x C

/-- The marked bound on `U`. -/
def MBOn (G : SimpleGraph W) (U : Finset W) : Prop :=
  ∀ S : Finset W, S ⊆ U → S.Nonempty → markedNumber G S ≤ (U.card - S.card) / 2

/-- `w` is a leaf of `G` with neighbour `v`. -/
def IsLeafAt (G : SimpleGraph W) (w v : W) : Prop := G.Adj w v ∧ ∀ y, G.Adj w y → y = v

theorem edgesIn_restrict (U : Finset W) : EdgesIn (restrict G U) U := fun _ _ h => ⟨h.2.1, h.2.2⟩

theorem EdgesIn.restrict_eq {U : Finset W} (h : EdgesIn G U) : restrict G U = G := by
  ext a b
  simp only [restrict_adj]
  exact ⟨fun h' => h'.1, fun h' => ⟨h', h a b h'⟩⟩

theorem EdgesIn.walk_mem {U : Finset W} (hE : EdgesIn G U) {a b : W} (p : G.Walk a b)
    (ha : a ∈ U) : ∀ v ∈ p.support, v ∈ U := by
  induction p with
  | nil => intro v hv; rw [Walk.mem_support_nil_iff] at hv; rw [hv]; exact ha
  | @cons a c b h q ih =>
    intro v hv
    rw [Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ha
    · exact ih (hE a c h).2 v hv

/-- A walk inside `U'` is a walk of the restriction. -/
theorem reachable_restrict {U' : Finset W} {a b : W} (p : G.Walk a b)
    (h : ∀ v ∈ p.support, v ∈ U') : (restrict G U').Reachable a b := by
  induction p with
  | nil => exact Reachable.refl _
  | @cons a c b hac q ih =>
    have ha := h a (by simp)
    have hq : ∀ v ∈ q.support, v ∈ U' := fun v hv => h v (by simp [hv])
    exact (show (restrict G U').Adj a c from ⟨hac, ha, hq c q.start_mem_support⟩).reachable.trans
      (ih hq)

/-! ### Separations -/

/-- A closed part reaches the cut vertex inside its side. -/
theorem Closed.reach {x : W} {C : Finset W} (hcl : Closed G x C) {a b : W} (p : G.Walk a b)
    (ha : a ∈ C) (hb : b ∉ C) : (restrict G (insert x C)).Reachable a x := by
  induction p with
  | nil => exact absurd ha hb
  | @cons a c b hac q ih =>
    rcases hcl a ha c hac with hc | rfl
    · exact (show (restrict G (insert x C)).Adj a c from
        ⟨hac, Finset.mem_insert_of_mem ha, Finset.mem_insert_of_mem hc⟩).reachable.trans
          (ih hc hb)
    · exact (show (restrict G (insert c C)).Adj a c from
        ⟨hac, Finset.mem_insert_of_mem ha, Finset.mem_insert_self _ _⟩).reachable

namespace Sep

variable {U : Finset W} {x : W} {C : Finset W}

theorem closed_compl (hE : EdgesIn G U) (h : Sep G U x C) : Closed G x (U.erase x \ C) := by
  intro a ha b hab
  rw [Finset.mem_sdiff, Finset.mem_erase] at ha
  by_cases hbx : b = x
  · exact Or.inr hbx
  · left
    rw [Finset.mem_sdiff, Finset.mem_erase]
    refine ⟨⟨hbx, (hE a b hab).2⟩, fun hbC => ?_⟩
    rcases h.2.2.2.2 b hbC a hab.symm with h' | h'
    · exact ha.2 h'
    · exact ha.1.1 h'

theorem symm (hE : EdgesIn G U) (h : Sep G U x C) : Sep G U x (U.erase x \ C) := by
  refine ⟨h.1, Finset.sdiff_subset, h.2.2.2.1, ?_, h.closed_compl hE⟩
  rw [Finset.sdiff_sdiff_eq_self h.2.1]
  exact h.2.2.1

/-- A part with one vertex is a leaf at the cut vertex. -/
theorem leaf_of_card_one (hC : ConnOn G U) (h : Sep G U x C) (h1 : C.card = 1) :
    ∃ a, C = {a} ∧ IsLeafAt G a x := by
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
  refine ⟨a, rfl, ?_, ?_⟩
  · have haU : a ∈ U := (Finset.mem_erase.mp (h.2.1 (Finset.mem_singleton_self a))).2
    have hax : a ≠ x := (Finset.mem_erase.mp (h.2.1 (Finset.mem_singleton_self a))).1
    obtain ⟨p⟩ := hC a haU x h.1
    cases p with
    | nil => exact absurd rfl hax
    | @cons _ c _ hac q =>
      rcases h.2.2.2.2 a (Finset.mem_singleton_self a) c hac with hc | rfl
      · rw [Finset.mem_singleton] at hc
        subst hc
        exact absurd hac (G.loopless.irrefl _)
      · exact hac
  · intro y hy
    rcases h.2.2.2.2 a (Finset.mem_singleton_self a) y hy with hc | hc
    · rw [Finset.mem_singleton] at hc
      subst hc
      exact absurd hy (G.loopless.irrefl _)
    · exact hc

/-- Every edge lies in one of the two sides. -/
theorem edge_cases (hE : EdgesIn G U) (h : Sep G U x C) {a b : W} (hab : G.Adj a b) :
    (a ∈ insert x C ∧ b ∈ insert x C) ∨
      (a ∈ insert x (U.erase x \ C) ∧ b ∈ insert x (U.erase x \ C)) := by
  have hD := h.closed_compl hE
  have haU := (hE a b hab).1
  have hbU := (hE a b hab).2
  by_cases hax : a = x
  · subst hax
    have hbx : b ≠ a := fun h' => G.loopless.irrefl a (h' ▸ hab)
    by_cases hbC : b ∈ C
    · exact Or.inl ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hbC⟩
    · exact Or.inr ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem
        (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hbx, hbU⟩, hbC⟩)⟩
  · by_cases haC : a ∈ C
    · rcases h.2.2.2.2 a haC b hab with hb | hb
      · exact Or.inl ⟨Finset.mem_insert_of_mem haC, Finset.mem_insert_of_mem hb⟩
      · exact Or.inl ⟨Finset.mem_insert_of_mem haC, hb ▸ Finset.mem_insert_self _ _⟩
    · have haD : a ∈ U.erase x \ C := Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hax, haU⟩, haC⟩
      rcases hD a haD b hab with hb | hb
      · exact Or.inr ⟨Finset.mem_insert_of_mem haD, Finset.mem_insert_of_mem hb⟩
      · exact Or.inr ⟨Finset.mem_insert_of_mem haD, hb ▸ Finset.mem_insert_self _ _⟩

theorem sides_inter (_h : Sep G U x C) {v : W} (h1 : v ∈ insert x C)
    (h2 : v ∈ insert x (U.erase x \ C)) : v = x := by
  rcases Finset.mem_insert.mp h1 with h1 | h1
  · exact h1
  · rcases Finset.mem_insert.mp h2 with h2 | h2
    · exact h2
    · exact absurd h1 (Finset.mem_sdiff.mp h2).2

theorem card_sides (h : Sep G U x C) :
    U.card = (insert x C).card + (insert x (U.erase x \ C)).card - 1 := by
  have hxC : x ∉ C := fun hx => (Finset.mem_erase.mp (h.2.1 hx)).1 rfl
  have hxD : x ∉ U.erase x \ C := fun hx => (Finset.mem_erase.mp (Finset.mem_sdiff.mp hx).1).1 rfl
  rw [Finset.card_insert_of_notMem hxC, Finset.card_insert_of_notMem hxD,
    Finset.card_sdiff_of_subset h.2.1, Finset.card_erase_of_mem h.1]
  have := Finset.card_le_card h.2.1
  rw [Finset.card_erase_of_mem h.1] at this
  have := Finset.card_pos.mpr ⟨x, h.1⟩
  omega

theorem conn_side (hC : ConnOn G U) (h : Sep G U x C) :
    ConnOn (restrict G (insert x C)) (insert x C) := by
  have hxC : x ∉ C := fun hx => (Finset.mem_erase.mp (h.2.1 hx)).1 rfl
  have key : ∀ a ∈ insert x C, (restrict G (insert x C)).Reachable a x := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Reachable.refl _
    · have haU := (Finset.mem_erase.mp (h.2.1 ha)).2
      obtain ⟨p⟩ := hC a haU x h.1
      exact h.2.2.2.2.reach p ha hxC
  intro a ha b hb
  exact (key a ha).trans (key b hb).symm

theorem conn_side' (hE : EdgesIn G U) (hC : ConnOn G U) (h : Sep G U x C) :
    ConnOn (restrict G (insert x (U.erase x \ C))) (insert x (U.erase x \ C)) :=
  (h.symm hE).conn_side hC

/-- The edges of `G` are those of the two sides. -/
theorem edgeSet_eq (hE : EdgesIn G U) (h : Sep G U x C) :
    G.edgeSet = (restrict G (insert x C)).edgeSet ∪
      (restrict G (insert x (U.erase x \ C))).edgeSet := by
  ext e
  induction e using Sym2.inductionOn with
  | hf a b =>
  simp only [Set.mem_union, mem_edgeSet, restrict_adj]
  constructor
  · intro hab
    rcases h.edge_cases hE hab with h' | h'
    · exact Or.inl ⟨hab, h'⟩
    · exact Or.inr ⟨hab, h'⟩
  · rintro (h' | h') <;> exact h'.1

theorem edges_disjoint (h : Sep G U x C) :
    ∀ e ∈ (restrict G (insert x C)).edgeSet, e ∉ (restrict G (insert x (U.erase x \ C))).edgeSet := by
  intro e h1 h2
  induction e using Sym2.inductionOn with
  | hf a b =>
  simp only [mem_edgeSet, restrict_adj] at h1 h2
  have ha := h.sides_inter h1.2.1 h2.2.1
  have hb := h.sides_inter h1.2.2 h2.2.2
  subst ha
  subst hb
  exact G.loopless.irrefl _ h1.1

/-- The cut vertex has a neighbour in each part. -/
theorem exists_adj (hC : ConnOn G U) (h : Sep G U x C) : ∃ y ∈ C, G.Adj x y := by
  obtain ⟨c, hc⟩ := h.2.2.1
  have hxC : x ∉ C := fun hx => (Finset.mem_erase.mp (h.2.1 hx)).1 rfl
  obtain ⟨p⟩ := (h.conn_side hC) x (Finset.mem_insert_self _ _) c (Finset.mem_insert_of_mem hc)
  cases p with
  | nil => exact absurd hc hxC
  | @cons _ y _ hxy q =>
    have hy := hxy.2.2
    rcases Finset.mem_insert.mp hy with hy | hy
    · exact absurd hxy.1 (hy ▸ G.loopless.irrefl x)
    · exact ⟨y, hy, hxy.1⟩

end Sep

/-! ### Leaves -/

namespace IsLeafAt

variable {w v : W} {U : Finset W}

theorem ne (h : IsLeafAt G w v) : w ≠ v := h.1.ne

theorem mem (hE : EdgesIn G U) (h : IsLeafAt G w v) : w ∈ U ∧ v ∈ U := hE w v h.1

theorem eq_of_mem {e : Sym2 W} (h : IsLeafAt G w v) (he : e ∈ G.edgeSet) (hw : w ∈ e) :
    e = s(w, v) := by
  induction e using Sym2.inductionOn with
  | hf a b =>
  rw [mem_edgeSet] at he
  rcases Sym2.mem_iff.mp hw with rfl | rfl
  · rw [h.2 b he]
  · rw [h.2 a he.symm, Sym2.eq_swap]

/-- Deleting a leaf keeps connectivity. -/
theorem reach (hE : EdgesIn G U) (hl : IsLeafAt G w v) {a b : W} (p : G.Walk a b)
    (hbw : b ≠ w) (hbU : b ∈ U) :
    (a ≠ w → (restrict G (U.erase w)).Reachable a b) ∧
      (a = w → (restrict G (U.erase w)).Reachable v b) := by
  induction p with
  | nil =>
    exact ⟨fun _ => Reachable.refl _, fun h => absurd h hbw⟩
  | @cons a c b hac q ih =>
    obtain ⟨ih1, ih2⟩ := ih hbw hbU
    constructor
    · intro haw
      by_cases hcw : c = w
      · subst hcw
        have := hl.2 a hac.symm
        subst this
        exact ih2 rfl
      · have h1 := (hE a c hac)
        exact (show (restrict G (U.erase w)).Adj a c from
          ⟨hac, Finset.mem_erase.mpr ⟨haw, h1.1⟩, Finset.mem_erase.mpr ⟨hcw, h1.2⟩⟩).reachable.trans
          (ih1 hcw)
    · intro haw
      subst haw
      have := hl.2 c hac
      subst this
      exact ih1 (fun h => hl.ne h.symm)

theorem conn (hE : EdgesIn G U) (hC : ConnOn G U) (hl : IsLeafAt G w v) :
    ConnOn (restrict G (U.erase w)) (U.erase w) := by
  intro a ha b hb
  rw [Finset.mem_erase] at ha hb
  obtain ⟨p⟩ := hC a ha.2 b hb.2
  exact (hl.reach hE p hb.1 hb.2).1 ha.1

/-- The edges of `G` are those of `G - w` plus the leaf edge. -/
theorem edgeSet_eq (hE : EdgesIn G U) (hl : IsLeafAt G w v) :
    G.edgeSet = (restrict G (U.erase w)).edgeSet ∪ {e | e ∈ [s(v, w)]} := by
  ext e
  simp only [Set.mem_union, mem_restrict_edgeSet, Set.mem_ofPred_eq, List.mem_singleton]
  constructor
  · intro he
    by_cases hw : w ∈ e
    · right; rw [hl.eq_of_mem he hw, Sym2.eq_swap]
    · left
      refine ⟨he, fun x hx => Finset.mem_erase.mpr ⟨fun h => hw (h ▸ hx), ?_⟩⟩
      induction e using Sym2.inductionOn with
      | hf a b =>
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact (hE _ _ he).1
      · exact (hE _ _ he).2
  · rintro (⟨he, -⟩ | rfl)
    · exact he
    · exact hl.1.symm

theorem not_mem_restrict {e : Sym2 W} (he : e ∈ (restrict G (U.erase w)).edgeSet) :
    w ∉ e := by
  intro hw
  have := (mem_restrict_edgeSet.mp he).2 w hw
  simp at this

end IsLeafAt

/-! ### Gluing partial marked partitions at a cut vertex -/

theorem perm_two_of_mem_append {α : Type*} {l₁ l₂ : List α} {a b : α} (ha : a ∈ l₁)
    (hb : b ∈ l₂) : ∃ rest, (l₁ ++ l₂).Perm (a :: b :: rest) := by
  classical
  refine ⟨l₁.erase a ++ l₂.erase b, ?_⟩
  refine ((List.perm_cons_erase ha).append (List.perm_cons_erase hb)).trans ?_
  simp only [List.cons_append]
  exact List.Perm.cons _ List.perm_middle

theorem perm_two_of_mem {α : Type*} [DecidableEq α] {l : List α} {a b : α} (ha : a ∈ l) (hb : b ∈ l.erase a) :
    ∃ rest, l.Perm (a :: b :: rest) := by
  exact ⟨(l.erase a).erase b, (List.perm_cons_erase ha).trans
    (List.Perm.cons _ (List.perm_cons_erase hb))⟩

section glue

variable {E₁ E₂ : Set (Sym2 W)} {U₁ U₂ : Set W} {x : W} {T : Finset W}

/-- Data for gluing at `x`: disjoint edge sets living on vertex sets that meet only at `x`. -/
structure GlueData (E₁ E₂ : Set (Sym2 W)) (U₁ U₂ : Set W) (x : W) : Prop where
  disj : ∀ e ∈ E₁, e ∉ E₂
  on₁ : ∀ e ∈ E₁, ∀ v ∈ e, v ∈ U₁
  on₂ : ∀ e ∈ E₂, ∀ v ∈ e, v ∈ U₂
  inter : ∀ v ∈ U₁, v ∈ U₂ → v = x

theorem GlueData.sites₁ (hg : GlueData E₁ E₂ U₁ U₂ x) (M : PMP G E₁ T) {s : W}
    (hs : s ∈ mSites M.paths) : s ∈ U₁ := by
  obtain ⟨y, hy, hys⟩ := List.mem_filterMap.mp hs
  have hsupp := M.support_subset hg.on₁ hy
  rcases (M.site_ok y hy s hys).2 with h | h
  · exact hsupp s (h ▸ y.1.walk.start_mem_support)
  · exact hsupp s (h ▸ y.1.walk.end_mem_support)

theorem GlueData.sites₂ (hg : GlueData E₁ E₂ U₁ U₂ x) (M : PMP G E₂ T) {s : W}
    (hs : s ∈ mSites M.paths) : s ∈ U₂ := by
  obtain ⟨y, hy, hys⟩ := List.mem_filterMap.mp hs
  have hsupp := M.support_subset hg.on₂ hy
  rcases (M.site_ok y hy s hys).2 with h | h
  · exact hsupp s (h ▸ y.1.walk.start_mem_support)
  · exact hsupp s (h ▸ y.1.walk.end_mem_support)

theorem GlueData.disj_paths (hg : GlueData E₁ E₂ U₁ U₂ x) (M₁ : PMP G E₁ T) (M₂ : PMP G E₂ T)
    {y₁ y₂ : GPath G × Option W} (h₁ : y₁ ∈ M₁.paths) (h₂ : y₂ ∈ M₂.paths) :
    ∀ v ∈ y₁.1.walk.support, v ∈ y₂.1.walk.support → v = x :=
  fun v hv1 hv2 => hg.inter v (M₁.support_subset hg.on₁ h₁ v hv1) (M₂.support_subset hg.on₂ h₂ v hv2)

/-- Union when `x` is not assigned on both sides. -/
theorem glue0 (hg : GlueData E₁ E₂ U₁ U₂ x) (M₁ : PMP G E₁ T) (M₂ : PMP G E₂ T)
    (h : x ∉ mSites M₁.paths ∨ x ∉ mSites M₂.paths) :
    ∃ M : PMP G (E₁ ∪ E₂) T, M.paths = M₁.paths ++ M₂.paths ∧ M.cost = M₁.cost + M₂.cost := by
  refine ⟨M₁.append M₂ hg.disj (fun s hs1 hs2 => ?_), rfl, ?_⟩
  swap
  · show mCost (M₁.paths ++ M₂.paths) = _
    rw [mCost_append]
  have := hg.inter s (hg.sites₁ M₁ hs1) (hg.sites₂ M₂ hs2)
  subst this
  rcases h with h | h
  · exact h hs1
  · exact h hs2

/-- Union in general, at the price of one assignment. -/
theorem glue1 (hg : GlueData E₁ E₂ U₁ U₂ x) (M₁ : PMP G E₁ T) (M₂ : PMP G E₂ T) :
    ∃ M : PMP G (E₁ ∪ E₂) T, M.cost ≤ M₁.cost + M₂.cost + 1 := by
  let M₁' := (M₁.forget x).mono (Finset.erase_subset x T)
  obtain ⟨M, -, hM⟩ := glue0 hg M₁' M₂ (Or.inl (M₁.not_mem_sites_forget x))
  refine ⟨M, ?_⟩
  have := M₁.forget_cost_le x
  have h2 : M₁'.cost = (M₁.forget x).cost := rfl
  omega

/-- Join a path of `M₂` that carries `x` to an `x`-ended path of `M₁` not assigned at `x`. -/
theorem glueJ (hg : GlueData E₁ E₂ U₁ U₂ x) (M₁ : PMP G E₁ T) (M₂ : PMP G E₂ T)
    {P : GPath G} {o : Option W} (hP : (P, o) ∈ M₁.paths) (hPx : P.src = x ∨ P.tgt = x)
    (ho : ∀ s, o = some s → s ≠ x) :
    ∃ M : PMP G (E₁ ∪ E₂) T, M.cost ≤ M₁.cost + M₂.cost := by
  by_cases hx2 : x ∈ mSites M₂.paths
  · obtain ⟨⟨R, oR⟩, hR, hRx⟩ := List.mem_filterMap.mp hx2
    simp only at hRx
    subst hRx
    have hRend := (M₂.site_ok _ hR x rfl).2
    let M₂' := (M₂.forget x).mono (Finset.erase_subset x T)
    have hR' : (R, none) ∈ M₂'.paths := by
      show (R, none) ∈ M₂.paths.map (PMP.forgetOne x)
      exact List.mem_map.mpr ⟨_, hR, by simp [PMP.forgetOne]⟩
    obtain ⟨M, hMp, hMc⟩ := glue0 hg M₁ M₂' (Or.inr (M₂.not_mem_sites_forget x))
    obtain ⟨rest, hrest⟩ := perm_two_of_mem_append hP hR'
    have hperm : M.paths.Perm ((R, none) :: (P, o) :: rest) := by
      rw [hMp]; exact hrest.trans (List.Perm.swap _ _ _)
    obtain ⟨M', R', hM'⟩ := M.exists_join hperm hRend hPx ho
      (fun v h1 h2 => hg.disj_paths M₁ M₂' hP hR' v h2 h1)
    refine ⟨M', ?_⟩
    have h1 : M.cost = mCost ((R, none) :: (P, o) :: rest) := mCost_perm hperm
    have h2 : M'.cost = mCost ((R', o) :: rest) := by rw [PMP.cost, hM']
    have h3 : M₂'.cost = M₂.cost + 1 := by
      show mCost (M₂.paths.map (PMP.forgetOne x)) = mCost M₂.paths + 1
      rw [PMP.mCost_map_forgetOne, List.count_eq_one_of_mem M₂.sites_nodup hx2]
    simp only [mCost_cons, Option.isNone_none, ite_true] at h1 h2
    omega
  · obtain ⟨M, -, hM⟩ := glue0 hg M₁ M₂ (Or.inr hx2)
    exact ⟨M, hM.le⟩

/-- Union after unmarking `x` on both sides: the two `x`-assigned paths are glued. -/
theorem glueU (hg : GlueData E₁ E₂ U₁ U₂ x) (M₁ : PMP G E₁ T) (M₂ : PMP G E₂ T) :
    ∃ M : PMP G (E₁ ∪ E₂) (T.erase x), M.cost ≤ M₁.cost + M₂.cost + 1 := by
  obtain ⟨M, hMp, hMc⟩ := glue0 hg (M₁.forget x) (M₂.forget x)
    (Or.inl (M₁.not_mem_sites_forget x))
  have hc1 := M₁.forget_cost_le x
  have hc2 := M₂.forget_cost_le x
  by_cases h1 : x ∈ mSites M₁.paths
  · by_cases h2 : x ∈ mSites M₂.paths
    · obtain ⟨⟨R₁, o₁⟩, hR₁, hR₁x⟩ := List.mem_filterMap.mp h1
      obtain ⟨⟨R₂, o₂⟩, hR₂, hR₂x⟩ := List.mem_filterMap.mp h2
      simp only at hR₁x hR₂x
      subst hR₁x hR₂x
      have hR₁end := (M₁.site_ok _ hR₁ x rfl).2
      have hR₂end := (M₂.site_ok _ hR₂ x rfl).2
      have hR₁' : (R₁, none) ∈ (M₁.forget x).paths :=
        List.mem_map.mpr ⟨_, hR₁, by simp [PMP.forgetOne]⟩
      have hR₂' : (R₂, none) ∈ (M₂.forget x).paths :=
        List.mem_map.mpr ⟨_, hR₂, by simp [PMP.forgetOne]⟩
      obtain ⟨rest, hrest⟩ := perm_two_of_mem_append hR₁' hR₂'
      have hperm : M.paths.Perm ((R₁, none) :: (R₂, none) :: rest) := by rw [hMp]; exact hrest
      obtain ⟨M', R', hM'⟩ := M.exists_join hperm hR₁end hR₂end (by simp)
        (fun v h1 h2 => hg.disj_paths (M₁.forget x) (M₂.forget x) hR₁' hR₂' v h1 h2)
      refine ⟨M', ?_⟩
      have e1 : M.cost = mCost ((R₁, none) :: (R₂, none) :: rest) := mCost_perm hperm
      have e2 : M'.cost = mCost ((R', none) :: rest) := by rw [PMP.cost, hM']
      simp only [mCost_cons, Option.isNone_none, ite_true] at e1 e2
      omega
    · refine ⟨M, ?_⟩
      rw [hMc, M₂.forget_cost_of_not_mem h2]
      omega
  · refine ⟨M, ?_⟩
    rw [hMc, M₁.forget_cost_of_not_mem h1]
    omega

/-- Join an unassigned `x`-ended path of `M₁` to an `x`-ended path of `M₂`. -/
theorem glueEnd (hg : GlueData E₁ E₂ U₁ U₂ x) (M₁ : PMP G E₁ T) (M₂ : PMP G E₂ T)
    (h : x ∉ mSites M₁.paths ∨ x ∉ mSites M₂.paths) {P : GPath G} (hP : (P, none) ∈ M₁.paths)
    (hPx : P.src = x ∨ P.tgt = x) {R : GPath G} {o : Option W} (hR : (R, o) ∈ M₂.paths)
    (hRx : R.src = x ∨ R.tgt = x) (ho : ∀ s, o = some s → s ≠ x) :
    ∃ M : PMP G (E₁ ∪ E₂) T, M.cost + 1 ≤ M₁.cost + M₂.cost := by
  obtain ⟨M, hMp, hMc⟩ := glue0 hg M₁ M₂ h
  obtain ⟨rest, hrest⟩ := perm_two_of_mem_append hP hR
  have hperm : M.paths.Perm ((P, none) :: (R, o) :: rest) := by rw [hMp]; exact hrest
  obtain ⟨M', R', hM'⟩ := M.exists_join hperm hPx hRx ho (hg.disj_paths M₁ M₂ hP hR)
  refine ⟨M', ?_⟩
  have e1 : M.cost = mCost ((P, none) :: (R, o) :: rest) := mCost_perm hperm
  have e2 : M'.cost = mCost ((R', o) :: rest) := by rw [PMP.cost, hM']
  simp only [mCost_cons, Option.isNone_none, ite_true] at e1 e2
  omega

/-- Split a path of `M₂` through `x` and join its halves to two `x`-ended unassigned paths of
`M₁`. -/
theorem glueSplit (hg : GlueData E₁ E₂ U₁ U₂ x) (M₁ : PMP G E₁ T) (M₂ : PMP G E₂ T)
    (h : x ∉ mSites M₂.paths) {P Q : GPath G} {rest₁ : List (GPath G × Option W)}
    (hM₁ : M₁.paths.Perm ((P, none) :: (Q, none) :: rest₁)) (hPx : P.src = x ∨ P.tgt = x)
    (hQx : Q.src = x ∨ Q.tgt = x) {R : GPath G} {o : Option W} (hR : (R, o) ∈ M₂.paths)
    (hxR : x ∈ R.walk.support) (hRs : R.src ≠ x) (hRt : R.tgt ≠ x) :
    ∃ M : PMP G (E₁ ∪ E₂) T, M.cost + 1 ≤ M₁.cost + M₂.cost := by
  classical
  have hM₂ : M₂.paths.Perm ((R, o) :: M₂.paths.erase (R, o)) := List.perm_cons_erase hR
  obtain ⟨M₂', R₁, R₂, o₁, o₂, hM₂', hR₁t, hR₂s, hR₁sup, hR₂sup, ho₁, ho₂, hcost⟩ :=
    M₂.exists_split hM₂ hxR hRs hRt
  set rest₂ := M₂.paths.erase (R, o) with hrest₂
  have hsites : x ∉ mSites M₂'.paths := by
    rw [hM₂']
    intro hx
    simp only [mSites_cons, List.mem_append, Option.mem_toList] at hx
    rcases hx with hx | hx | hx
    · exact ho₁ x hx rfl
    · exact ho₂ x hx rfl
    · exact h ((mSites_perm hM₂).mem_iff.mpr (by simp [hx]))
  obtain ⟨M, hMp, hMc⟩ := glue0 hg M₁ M₂' (Or.inr hsites)
  have hP : (P, none) ∈ M₁.paths := hM₁.mem_iff.mpr (by simp)
  have hQ : (Q, none) ∈ M₁.paths := hM₁.mem_iff.mpr (by simp)
  have hperm1 : M.paths.Perm
      ((P, none) :: (R₁, o₁) :: ((Q, none) :: rest₁ ++ (R₂, o₂) :: rest₂)) := by
    rw [hMp, hM₂']
    refine (hM₁.append_right _).trans ?_
    simp only [List.cons_append]
    refine List.Perm.cons _ ?_
    have := List.perm_middle (a := (R₁, o₁)) (l₁ := (Q, none) :: rest₁) (l₂ := (R₂, o₂) :: rest₂)
    simpa using this
  obtain ⟨M', J₁, hM'⟩ := M.exists_join hperm1 hPx (Or.inr hR₁t) ho₁
    (fun v h1 h2 => hg.disj_paths M₁ M₂ hP hR v h1 (hR₁sup v h2))
  have hperm2 : M'.paths.Perm ((Q, none) :: (R₂, o₂) :: ((J₁, o₁) :: rest₁ ++ rest₂)) := by
    rw [hM']
    simp only [List.cons_append]
    refine (List.Perm.swap _ _ _).trans (List.Perm.cons _ ?_)
    have := List.perm_middle (a := (R₂, o₂)) (l₁ := (J₁, o₁) :: rest₁) (l₂ := rest₂)
    simpa using this
  obtain ⟨M'', J₂, hM''⟩ := M'.exists_join hperm2 hQx (Or.inl hR₂s) ho₂
    (fun v h1 h2 => hg.disj_paths M₁ M₂ hQ hR v h1 (hR₂sup v h2))
  refine ⟨M'', ?_⟩
  have e1 : M₁.cost = mCost ((P, none) :: (Q, none) :: rest₁) := mCost_perm hM₁
  have e2 : M₂.cost = mCost ((R, o) :: rest₂) := mCost_perm hM₂
  have e3 : M₂'.cost = mCost ((R₁, o₁) :: (R₂, o₂) :: rest₂) := by rw [PMP.cost, hM₂']
  have e4 : M''.cost = mCost ((J₂, o₂) :: ((J₁, o₁) :: rest₁ ++ rest₂)) := by rw [PMP.cost, hM'']
  simp only [mCost_cons, mCost_append, mCost_nil, Option.isNone_none, ite_true] at e1 e2 e3 e4 hcost
  omega

end glue

end Gallai
