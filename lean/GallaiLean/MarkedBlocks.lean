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

theorem perm_two_of_mem {α : Type*} {l : List α} {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    (hne : b ≠ a) : ∃ rest, l.Perm (a :: b :: rest) := by
  classical
  have hb' : b ∈ l.erase a := (List.mem_erase_of_ne hne).mpr hb
  exact ⟨(l.erase a).erase b, (List.perm_cons_erase ha).trans
    (List.Perm.cons _ (List.perm_cons_erase hb'))⟩

/-- Two entries of a partial marked partition at different positions carry different paths. -/
theorem PMP.fst_ne_of_mem_tail {E : Set (Sym2 W)} {S : Finset W} (M : PMP G E S)
    {y z : GPath G × Option W} {rest : List (GPath G × Option W)} (hM : M.paths = y :: rest)
    (hz : z ∈ rest) : z.1 ≠ y.1 := by
  intro h
  have hnd := M.nodup
  rw [hM, mEdges_cons, List.nodup_append] at hnd
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ y.1.edges_ne_nil
  have : e ∈ mEdges rest := List.mem_flatMap.mpr ⟨z.1, List.mem_map_of_mem hz, h ▸ he⟩
  exact hnd.2.2 e he e this rfl

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

/-! ### The two sides of a cut vertex -/

/-- `U` splits at `x` into two connected sides `U₁`, `U₂` of order at least three, meeting only
at `x`, with every edge inside one side. -/
structure CutSides (G : SimpleGraph W) (U : Finset W) (x : W) (U₁ U₂ : Finset W) : Prop where
  hx₁ : x ∈ U₁
  hx₂ : x ∈ U₂
  inter : ∀ v ∈ U₁, v ∈ U₂ → v = x
  union : U = U₁ ∪ U₂
  edges : G.edgeSet = (restrict G U₁).edgeSet ∪ (restrict G U₂).edgeSet
  conn₁ : ConnOn (restrict G U₁) U₁
  conn₂ : ConnOn (restrict G U₂) U₂
  big₁ : 3 ≤ U₁.card
  big₂ : 3 ≤ U₂.card

theorem Sep.cutSides {U : Finset W} {x : W} {C : Finset W} (hE : EdgesIn G U) (hC : ConnOn G U)
    (h : Sep G U x C) (h1 : 2 ≤ C.card) (h2 : 2 ≤ (U.erase x \ C).card) :
    CutSides G U x (insert x C) (insert x (U.erase x \ C)) where
  hx₁ := Finset.mem_insert_self _ _
  hx₂ := Finset.mem_insert_self _ _
  inter := fun v h1 h2 => h.sides_inter h1 h2
  union := by
    ext v
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_erase]
    constructor
    · intro hv
      by_cases hvx : v = x
      · exact Or.inl (Or.inl hvx)
      · by_cases hvC : v ∈ C
        · exact Or.inl (Or.inr hvC)
        · exact Or.inr (Or.inr ⟨⟨hvx, hv⟩, hvC⟩)
    · rintro ((rfl | hv) | (rfl | ⟨⟨-, hv⟩, -⟩))
      · exact h.1
      · exact (Finset.mem_erase.mp (h.2.1 hv)).2
      · exact h.1
      · exact hv
  edges := h.edgeSet_eq hE
  conn₁ := h.conn_side hC
  conn₂ := h.conn_side' hE hC
  big₁ := by
    have hxC : x ∉ C := fun hx => (Finset.mem_erase.mp (h.2.1 hx)).1 rfl
    rw [Finset.card_insert_of_notMem hxC]; omega
  big₂ := by
    have hxD : x ∉ U.erase x \ C := fun hx => (Finset.mem_erase.mp (Finset.mem_sdiff.mp hx).1).1 rfl
    rw [Finset.card_insert_of_notMem hxD]; omega

namespace CutSides

variable {U U₁ U₂ : Finset W} {x : W}

theorem symm (h : CutSides G U x U₁ U₂) : CutSides G U x U₂ U₁ where
  hx₁ := h.hx₂
  hx₂ := h.hx₁
  inter := fun v h1 h2 => h.inter v h2 h1
  union := by rw [h.union, Finset.union_comm]
  edges := by rw [h.edges, Set.union_comm]
  conn₁ := h.conn₂
  conn₂ := h.conn₁
  big₁ := h.big₂
  big₂ := h.big₁

theorem inter_eq (h : CutSides G U x U₁ U₂) : U₁ ∩ U₂ = {x} := by
  ext v
  simp only [Finset.mem_inter, Finset.mem_singleton]
  exact ⟨fun hv => h.inter v hv.1 hv.2, fun hv => hv ▸ ⟨h.hx₁, h.hx₂⟩⟩

theorem card (h : CutSides G U x U₁ U₂) : U.card + 1 = U₁.card + U₂.card := by
  rw [h.union, ← Finset.card_union_add_card_inter, h.inter_eq, Finset.card_singleton]

theorem sub₁ (h : CutSides G U x U₁ U₂) : U₁ ⊆ U := by rw [h.union]; exact Finset.subset_union_left
theorem sub₂ (h : CutSides G U x U₁ U₂) : U₂ ⊆ U := by rw [h.union]; exact Finset.subset_union_right

theorem glue (h : CutSides G U x U₁ U₂) :
    GlueData (restrict G U₁).edgeSet (restrict G U₂).edgeSet (U₁ : Set W) (U₂ : Set W) x where
  disj := by
    intro e h1 h2
    induction e using Sym2.inductionOn with
    | hf a b =>
    simp only [mem_edgeSet, restrict_adj] at h1 h2
    have ha := h.inter a h1.2.1 h2.2.1
    have hb := h.inter b h1.2.2 h2.2.2
    subst ha hb
    exact G.loopless.irrefl _ h1.1
  on₁ := fun e he v hv => (mem_restrict_edgeSet.mp he).2 v hv
  on₂ := fun e he v hv => (mem_restrict_edgeSet.mp he).2 v hv
  inter := fun v h1 h2 => h.inter v h1 h2

theorem exists_adj₂ (h : CutSides G U x U₁ U₂) : ∃ y ∈ U₂, y ≠ x ∧ G.Adj x y := by
  obtain ⟨d, hd, hdx⟩ : ∃ d ∈ U₂, d ≠ x := by
    by_contra hc
    push Not at hc
    have : U₂ ⊆ {x} := fun d hd => Finset.mem_singleton.mpr (hc d hd)
    have := Finset.card_le_card this
    have := h.big₂
    simp at *; omega
  obtain ⟨p⟩ := h.conn₂ x h.hx₂ d hd
  cases p with
  | nil => exact absurd rfl hdx
  | @cons _ y _ hxy q =>
    exact ⟨y, hxy.2.2, fun hyx => G.loopless.irrefl x (hyx ▸ hxy.1), hxy.1⟩

variable {y : W}

theorem plus_edges (h : CutSides G U x U₁ U₂) (hy : y ∈ U₂) (hyx : y ≠ x) (hxy : G.Adj x y) :
    (restrict G (insert y U₁)).edgeSet = (restrict G U₁).edgeSet ∪ {e | e ∈ [s(x, y)]} := by
  have hyU₁ : y ∉ U₁ := fun h' => hyx (h.inter y h' hy)
  ext e
  induction e using Sym2.inductionOn with
  | hf a b =>
  simp only [Set.mem_union, mem_edgeSet, restrict_adj, Finset.mem_insert, Set.mem_ofPred_eq,
    List.mem_singleton, Sym2.eq_iff]
  constructor
  · rintro ⟨hab, ha, hb⟩
    have hE : s(a, b) ∈ G.edgeSet := hab
    rw [h.edges] at hE
    rcases hE with hE | hE
    · exact Or.inl hE
    · simp only [mem_edgeSet, restrict_adj] at hE
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact absurd hab (G.loopless.irrefl _)
        · have := h.inter b hb hE.2.2
          exact Or.inr (Or.inr ⟨rfl, this⟩)
      · have hax := h.inter a ha hE.2.1
        rcases hb with rfl | hb
        · exact Or.inr (Or.inl ⟨hax, rfl⟩)
        · exact Or.inl ⟨hab, ha, hb⟩
  · rintro (⟨hab, ha, hb⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨hab, Or.inr ha, Or.inr hb⟩
    · exact ⟨hxy, Or.inr h.hx₁, Or.inl rfl⟩
    · exact ⟨hxy.symm, Or.inl rfl, Or.inr h.hx₁⟩

theorem plus_conn (h : CutSides G U x U₁ U₂) (hxy : G.Adj x y) :
    ConnOn (restrict G (insert y U₁)) (insert y U₁) := by
  have key : ∀ a ∈ insert y U₁, (restrict G (insert y U₁)).Reachable a x := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact (show (restrict G (insert a U₁)).Adj a x from
        ⟨hxy.symm, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem h.hx₁⟩).reachable
    · exact (h.conn₁ a ha x h.hx₁).mono
        (show restrict G U₁ ≤ restrict G (insert y U₁) from
          fun a b hab => restrict_mono (Finset.subset_insert _ _) a b hab)
  intro a ha b hb
  exact (key a ha).trans (key b hb).symm

theorem plus_leaf (h : CutSides G U x U₁ U₂) (hy : y ∈ U₂) (hyx : y ≠ x) (hxy : G.Adj x y) :
    ∀ e ∈ (restrict G (insert y U₁)).edgeSet, y ∈ e → e = s(x, y) := by
  have hyU₁ : y ∉ U₁ := fun h' => hyx (h.inter y h' hy)
  intro e he hye
  rw [h.plus_edges hy hyx hxy] at he
  rcases he with he | he
  · exact absurd ((mem_restrict_edgeSet.mp he).2 y hye) hyU₁
  · simpa using he

theorem plus_sub (h : CutSides G U x U₁ U₂) (hy : y ∈ U₂) (hyx : y ≠ x) (hxy : G.Adj x y) :
    (restrict G (insert y U₁)).edgeSet \ {e | e ∈ [s(x, y)]} = (restrict G U₁).edgeSet := by
  have hyU₁ : y ∉ U₁ := fun h' => hyx (h.inter y h' hy)
  rw [h.plus_edges hy hyx hxy]
  ext e
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_ofPred_eq, List.mem_singleton]
  constructor
  · rintro ⟨he | he, hne⟩
    · exact he
    · exact absurd he hne
  · intro he
    refine ⟨Or.inl he, fun he' => ?_⟩
    subst he'
    exact hyU₁ ((mem_restrict_edgeSet.mp he).2 y (Sym2.mem_mk_right _ _))

theorem card_sites (h : CutSides G U x U₁ U₂) {S : Finset W} (hSU : S ⊆ U) :
    (S ∩ U₁).card + (S ∩ U₂).card = S.card + if x ∈ S then 1 else 0 := by
  rw [← Finset.card_union_add_card_inter]
  have h1 : S ∩ U₁ ∪ S ∩ U₂ = S := by
    rw [← Finset.inter_union_distrib_left, ← h.union]; exact Finset.inter_eq_left.mpr hSU
  have h2 : S ∩ U₁ ∩ (S ∩ U₂) = if x ∈ S then {x} else ∅ := by
    ext v
    simp only [Finset.mem_inter]
    split_ifs with hx
    · simp only [Finset.mem_singleton]
      exact ⟨fun hv => h.inter v hv.1.2 hv.2.2, fun hv => hv ▸ ⟨⟨hx, h.hx₁⟩, ⟨hx, h.hx₂⟩⟩⟩
    · simp only [Finset.notMem_empty, iff_false]
      rintro ⟨⟨hv, h1⟩, -, h2⟩
      exact hx (h.inter v h1 h2 ▸ hv)
  rw [h1, h2]
  split_ifs <;> simp

end CutSides

/-! ### Partial marked partitions from smaller instances -/

variable [Fintype W]

theorem exists_pmp_le (G' : SimpleGraph W) (hle : ∀ a b, G'.Adj a b → G.Adj a b)
    (S' : Finset W) : ∃ M : PMP G G'.edgeSet S', M.cost = markedNumber G' S' := by
  obtain ⟨M₀, hM₀⟩ := markedNumber_spec G' S'
  let M₁ := PMP.push (G := G) M₀ id Function.injective_id hle
  refine ⟨(M₁.castE (by ext e; simp [Sym2.map_id'])).mono (fun s hs => by simpa using hs), ?_⟩
  rw [← hM₀, ← PMP.push_cost M₀ id Function.injective_id hle]
  rfl

/-- The marked bound on a smaller instance, as a partial marked partition of `G`. -/
theorem exists_pmp_restrict {U' : Finset W} (hMB : MBOn (restrict G U') U') {S' : Finset W}
    (hS'U : S' ⊆ U') (hS' : S'.Nonempty) :
    ∃ M : PMP G (restrict G U').edgeSet S', M.cost ≤ (U'.card - S'.card) / 2 := by
  obtain ⟨M, hM⟩ := exists_pmp_le (G := G) (restrict G U') (restrict_le U') S'
  exact ⟨M, hM ▸ hMB S' hS'U hS'⟩

/-- The induction hypothesis: the marked bound on every smaller instance. -/
def SmallerMB (U : Finset W) : Prop :=
  ∀ (G' : SimpleGraph W) (U' : Finset W), U'.card < U.card → EdgesIn G' U' → ConnOn G' U' →
    MBOn G' U'

/-! ### The cut-vertex reduction -/

section cut

variable {U U₁ U₂ : Finset W} {x : W}

theorem CutSides.lt₁ (h : CutSides G U x U₁ U₂) : U₁.card < U.card := by
  have := h.card; have := h.big₂; omega

theorem CutSides.lt_plus (h : CutSides G U x U₁ U₂) : U₁.card + 1 < U.card := by
  have := h.card; have := h.big₂; omega

theorem CutSides.side_pmp (h : CutSides G U x U₁ U₂) (IH : SmallerMB U) {S' : Finset W}
    (hS' : S' ⊆ U₁) (hne : S'.Nonempty) :
    ∃ M : PMP G (restrict G U₁).edgeSet S', M.cost ≤ (U₁.card - S'.card) / 2 :=
  exists_pmp_restrict (IH _ _ h.lt₁ (edgesIn_restrict U₁) h.conn₁) hS' hne

/-- The final step: a partial marked partition of both sides bounds `q(G, S)`. -/
theorem CutSides.finish (h : CutSides G U x U₁ U₂) {S : Finset W}
    (M : PMP G ((restrict G U₁).edgeSet ∪ (restrict G U₂).edgeSet) S) :
    markedNumber G S ≤ M.cost :=
  (M.castE h.edges.symm).markedNumber_le_cost

theorem cut_xS_odd (h : CutSides G U x U₁ U₂) (IH : SmallerMB U) {S : Finset W} (hSU : S ⊆ U)
    (hxS : x ∈ S) (h1 : Odd (U₁.card - (S ∩ U₁).card)) (h2 : Odd (U₂.card - (S ∩ U₂).card)) :
    markedNumber G S ≤ (U.card - S.card) / 2 := by
  obtain ⟨M₁, hM₁⟩ := h.side_pmp IH (S' := S ∩ U₁) Finset.inter_subset_right
    ⟨x, Finset.mem_inter.mpr ⟨hxS, h.hx₁⟩⟩
  obtain ⟨M₂, hM₂⟩ := h.symm.side_pmp IH (S' := S ∩ U₂) Finset.inter_subset_right
    ⟨x, Finset.mem_inter.mpr ⟨hxS, h.hx₂⟩⟩
  obtain ⟨M, hM⟩ := glue1 h.glue (M₁.mono Finset.inter_subset_left)
    (M₂.mono Finset.inter_subset_left)
  have hq := h.finish M
  have hc := h.card
  have hs := h.card_sites hSU
  simp only [hxS, ite_true] at hs
  have hs₁ := Finset.card_le_card (Finset.inter_subset_right (s₁ := S) (s₂ := U₁))
  have hs₂ := Finset.card_le_card (Finset.inter_subset_right (s₁ := S) (s₂ := U₂))
  have e1 : (M₁.mono Finset.inter_subset_left).cost = M₁.cost := rfl
  have e2 : (M₂.mono Finset.inter_subset_left).cost = M₂.cost := rfl
  rw [Nat.odd_iff] at h1 h2
  omega

theorem cut_xS_even (h : CutSides G U x U₁ U₂) (IH : SmallerMB U) {S : Finset W} (hSU : S ⊆ U)
    (hxS : x ∈ S) (h1 : Even (U₁.card - (S ∩ U₁).card)) :
    markedNumber G S ≤ (U.card - S.card) / 2 := by
  obtain ⟨y, hy, hyx, hxy⟩ := h.exists_adj₂
  have hyU₁ : y ∉ U₁ := fun h' => hyx (h.inter y h' hy)
  have hcardP : (insert y U₁).card = U₁.card + 1 := Finset.card_insert_of_notMem hyU₁
  have hMBp := IH (restrict G (insert y U₁)) (insert y U₁) (by rw [hcardP]; exact h.lt_plus)
    (edgesIn_restrict _) (h.plus_conn hxy)
  obtain ⟨Mp, hMp⟩ := exists_pmp_restrict hMBp (S' := S ∩ U₁)
    (Finset.inter_subset_right.trans (Finset.subset_insert _ _))
    ⟨x, Finset.mem_inter.mpr ⟨hxS, h.hx₁⟩⟩
  have hmem : s(x, y) ∈ (restrict G (insert y U₁)).edgeSet := by
    rw [h.plus_edges hy hyx hxy]; right; simp
  have hyS : y ∉ S ∩ U₁ := fun h' => hyU₁ (Finset.mem_inter.mp h').2
  obtain ⟨M₂, hM₂⟩ := h.symm.side_pmp IH (S' := S ∩ U₂) Finset.inter_subset_right
    ⟨x, Finset.mem_inter.mpr ⟨hxS, h.hx₂⟩⟩
  let M₂' := M₂.mono (Finset.inter_subset_left (s₁ := S) (s₂ := U₂))
  have e2 : M₂'.cost = M₂.cost := rfl
  have hc := h.card
  have hs := h.card_sites hSU
  simp only [hxS, ite_true] at hs
  have hs₁ := Finset.card_le_card (Finset.inter_subset_right (s₁ := S) (s₂ := U₁))
  have hs₂ := Finset.card_le_card (Finset.inter_subset_right (s₁ := S) (s₂ := U₂))
  rw [hcardP] at hMp
  obtain ⟨k, hk⟩ := h1
  rcases Mp.exists_trim (Ne.symm hyx) hmem (h.plus_leaf hy hyx hxy) hyS with
    ⟨M₁, hc₁, -⟩ | ⟨M₁, hc₁, -, hx₁⟩ | ⟨M₁, L, o, rest, hp, hL, ho, hc₁, -⟩
  · let M₁' := (M₁.castE (h.plus_sub hy hyx hxy)).mono (Finset.inter_subset_left (s₁ := S) (s₂ := U₁))
    have e1 : M₁'.cost = M₁.cost := rfl
    obtain ⟨M, hM⟩ := glue1 h.glue M₁' M₂'
    have := h.finish M
    omega
  · let M₁' := (M₁.castE (h.plus_sub hy hyx hxy)).mono (Finset.inter_subset_left (s₁ := S) (s₂ := U₁))
    have e1 : M₁'.cost = M₁.cost := rfl
    obtain ⟨M, -, hM⟩ := glue0 h.glue M₁' M₂' (Or.inl hx₁)
    have := h.finish M
    omega
  · let M₁' := (M₁.castE (h.plus_sub hy hyx hxy)).mono (Finset.inter_subset_left (s₁ := S) (s₂ := U₁))
    have e1 : M₁'.cost = M₁.cost := rfl
    have hP : (L, o) ∈ M₁'.paths := by
      show (L, o) ∈ M₁.paths
      rw [hp]; exact List.mem_cons_self
    obtain ⟨M, hM⟩ := glueJ h.glue M₁' M₂' hP (Or.inl hL) ho
    have := h.finish M
    omega

theorem cut_xnS_odd (h : CutSides G U x U₁ U₂) (IH : SmallerMB U) {S : Finset W} (hSU : S ⊆ U)
    (hxS : x ∉ S)
    (hodd : Odd (U₁.card - 1 - (S ∩ U₁).card) ∨ Odd (U₂.card - 1 - (S ∩ U₂).card)) :
    markedNumber G S ≤ (U.card - S.card) / 2 := by
  have hx1 : x ∉ S ∩ U₁ := fun h' => hxS (Finset.mem_inter.mp h').1
  have hx2 : x ∉ S ∩ U₂ := fun h' => hxS (Finset.mem_inter.mp h').1
  obtain ⟨M₁, hM₁⟩ := h.side_pmp IH (S' := insert x (S ∩ U₁))
    (Finset.insert_subset h.hx₁ Finset.inter_subset_right) (Finset.insert_nonempty _ _)
  obtain ⟨M₂, hM₂⟩ := h.symm.side_pmp IH (S' := insert x (S ∩ U₂))
    (Finset.insert_subset h.hx₂ Finset.inter_subset_right) (Finset.insert_nonempty _ _)
  have hsub : ∀ i : Finset W, insert x (S ∩ i) ⊆ insert x S :=
    fun i => Finset.insert_subset_insert _ Finset.inter_subset_left
  obtain ⟨M, hM⟩ := glueU h.glue (M₁.mono (hsub U₁)) (M₂.mono (hsub U₂))
  have hq := h.finish (M.mono (by rw [Finset.erase_insert hxS]))
  have e1 : (M₁.mono (hsub U₁)).cost = M₁.cost := rfl
  have e2 : (M₂.mono (hsub U₂)).cost = M₂.cost := rfl
  have e3 : (M.mono (by rw [Finset.erase_insert hxS] : (insert x S).erase x ⊆ S)).cost =
    M.cost := rfl
  rw [Finset.card_insert_of_notMem hx1] at hM₁
  rw [Finset.card_insert_of_notMem hx2] at hM₂
  have hc := h.card
  have hs := h.card_sites hSU
  simp only [hxS, ite_false, add_zero] at hs
  have hs₁ := Finset.card_le_card (Finset.insert_subset h.hx₁ (Finset.inter_subset_right (s₁ := S)
    (s₂ := U₁)))
  have hs₂ := Finset.card_le_card (Finset.insert_subset h.hx₂ (Finset.inter_subset_right (s₁ := S)
    (s₂ := U₂)))
  rw [Finset.card_insert_of_notMem hx1] at hs₁
  rw [Finset.card_insert_of_notMem hx2] at hs₂
  rcases hodd with hodd | hodd <;> rw [Nat.odd_iff] at hodd <;> omega

theorem cut_xnS_marked (h : CutSides G U x U₁ U₂) (IH : SmallerMB U) {S : Finset W}
    (hSU : S ⊆ U) (hxS : x ∉ S) (h1 : (S ∩ U₁).Nonempty) (h2 : (S ∩ U₂).Nonempty)
    (he1 : Even (U₁.card - 1 - (S ∩ U₁).card)) (he2 : Even (U₂.card - 1 - (S ∩ U₂).card)) :
    markedNumber G S ≤ (U.card - S.card) / 2 := by
  obtain ⟨M₁, hM₁⟩ := h.side_pmp IH (S' := S ∩ U₁) Finset.inter_subset_right h1
  obtain ⟨M₂, hM₂⟩ := h.symm.side_pmp IH (S' := S ∩ U₂) Finset.inter_subset_right h2
  have hx : x ∉ mSites (M₁.mono (Finset.inter_subset_left (s₁ := S) (s₂ := U₁))).paths :=
    fun h' => hxS (Finset.mem_inter.mp (M₁.sites_mem h')).1
  obtain ⟨M, -, hM⟩ := glue0 h.glue (M₁.mono Finset.inter_subset_left)
    (M₂.mono Finset.inter_subset_left) (Or.inl hx)
  have hq := h.finish M
  have e1 : (M₁.mono (Finset.inter_subset_left (s₁ := S) (s₂ := U₁))).cost = M₁.cost := rfl
  have e2 : (M₂.mono (Finset.inter_subset_left (s₁ := S) (s₂ := U₂))).cost = M₂.cost := rfl
  have hc := h.card
  have hs := h.card_sites hSU
  simp only [hxS, ite_false, add_zero] at hs
  have hx1 : x ∉ S ∩ U₁ := fun h' => hxS (Finset.mem_inter.mp h').1
  have hx2 : x ∉ S ∩ U₂ := fun h' => hxS (Finset.mem_inter.mp h').1
  have hs₁ := Finset.card_le_card (Finset.insert_subset h.hx₁ (Finset.inter_subset_right (s₁ := S)
    (s₂ := U₁)))
  have hs₂ := Finset.card_le_card (Finset.insert_subset h.hx₂ (Finset.inter_subset_right (s₁ := S)
    (s₂ := U₂)))
  rw [Finset.card_insert_of_notMem hx1] at hs₁
  rw [Finset.card_insert_of_notMem hx2] at hs₂
  obtain ⟨a, ha⟩ := he1
  obtain ⟨b, hb⟩ := he2
  omega

theorem cut_xnS_tight (h : CutSides G U x U₁ U₂) (IH : SmallerMB U) {S : Finset W}
    (hSU : S ⊆ U) (hxS : x ∉ S) (hS : S.Nonempty) (h1 : S ∩ U₁ = ∅) (he1 : Even (U₁.card - 1))
    (he2 : Even (U₂.card - 1 - (S ∩ U₂).card)) :
    markedNumber G S ≤ (U.card - S.card) / 2 := by
  classical
  have hc := h.card
  have hs := h.card_sites hSU
  simp only [hxS, ite_false, add_zero, h1, Finset.card_empty, zero_add] at hs
  have hS₂ : (S ∩ U₂).Nonempty := by
    rw [← Finset.card_pos, hs]; exact Finset.card_pos.mpr hS
  obtain ⟨M₂, hM₂⟩ := h.symm.side_pmp IH (S' := S ∩ U₂) Finset.inter_subset_right hS₂
  let M₂' := M₂.mono (Finset.inter_subset_left (s₁ := S) (s₂ := U₂))
  have e2 : M₂'.cost = M₂.cost := rfl
  have hxM₂ : x ∉ mSites M₂'.paths := fun h' => hxS (Finset.mem_inter.mp (M₂.sites_mem h')).1
  have hx2 : x ∉ S ∩ U₂ := fun h' => hxS (Finset.mem_inter.mp h').1
  have hs₂ := Finset.card_le_card (Finset.insert_subset h.hx₂ (Finset.inter_subset_right (s₁ := S)
    (s₂ := U₂)))
  rw [Finset.card_insert_of_notMem hx2] at hs₂
  -- the leaf trick on the unmarked side
  obtain ⟨y, hy, hyx, hxy⟩ := h.exists_adj₂
  have hyU₁ : y ∉ U₁ := fun h' => hyx (h.inter y h' hy)
  have hcardP : (insert y U₁).card = U₁.card + 1 := Finset.card_insert_of_notMem hyU₁
  have hMBp := IH (restrict G (insert y U₁)) (insert y U₁) (by rw [hcardP]; exact h.lt_plus)
    (edgesIn_restrict _) (h.plus_conn hxy)
  obtain ⟨Mp, hMp⟩ := exists_pmp_restrict hMBp (S' := {x})
    (Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem h.hx₁)) (Finset.singleton_nonempty x)
  rw [hcardP, Finset.card_singleton] at hMp
  have hmem : s(x, y) ∈ (restrict G (insert y U₁)).edgeSet := by
    rw [h.plus_edges hy hyx hxy]; right; simp
  have hyS : y ∉ ({x} : Finset W) := by simpa using hyx
  have hsl := Mp.sites_length_le
  rw [Finset.card_singleton] at hsl
  have hlenP : Mp.paths.length = Mp.cost + (mSites Mp.paths).length :=
    length_eq_mCost_add Mp.paths
  -- a cheap partition of the unmarked side, or two `x`-ended paths
  have key : (∃ M₁ : PMP G (restrict G U₁).edgeSet S, M₁.cost ≤ Mp.cost ∧ x ∉ mSites M₁.paths) ∨
      (∃ (M₁ : PMP G (restrict G U₁).edgeSet S) (P Q : GPath G) (rest : List (GPath G × Option W)),
        M₁.paths.Perm ((P, none) :: (Q, none) :: rest) ∧ (P.src = x ∨ P.tgt = x) ∧
        (Q.src = x ∨ Q.tgt = x) ∧ M₁.cost ≤ Mp.cost + 1) := by
    rcases Mp.exists_trim (Ne.symm hyx) hmem (h.plus_leaf hy hyx hxy) hyS with
      ⟨M₁, hc₁, hl₁⟩ | ⟨M₁, hc₁, hl₁, hx₁⟩ | ⟨M₁, L, o, rest, hp, hL, ho, hc₁, hl₁⟩
    · left
      refine ⟨(M₁.castE (h.plus_sub hy hyx hxy)).forgetAll S, ?_, by simp [PMP.forgetAll_sites]⟩
      rw [PMP.forgetAll_cost]
      show M₁.paths.length ≤ _
      omega
    · left
      refine ⟨(M₁.castE (h.plus_sub hy hyx hxy)).forgetAll S, ?_, by simp [PMP.forgetAll_sites]⟩
      rw [PMP.forgetAll_cost]
      show M₁.paths.length ≤ _
      have h0 : mSites M₁.paths = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro s hs
        have := M₁.sites_mem hs
        rw [Finset.mem_singleton] at this
        exact hx₁ (this ▸ hs)
      have : M₁.paths.length = M₁.cost + (mSites M₁.paths).length := length_eq_mCost_add M₁.paths
      rw [h0] at this
      simp at this
      omega
    · have ho' : o = none := by
        cases o with
        | none => rfl
        | some s =>
          have := (M₁.site_ok (L, some s) (by rw [hp]; exact List.mem_cons_self) s rfl).1
          rw [Finset.mem_singleton] at this
          exact absurd this (ho s rfl)
      subst ho'
      have hlen : M₁.paths.length = M₁.cost + (mSites M₁.paths).length :=
        length_eq_mCost_add M₁.paths
      by_cases hx₁ : x ∈ mSites M₁.paths
      · right
        rw [hp] at hx₁
        simp only [mSites_cons, Option.toList_none, List.nil_append] at hx₁
        obtain ⟨⟨Q, oQ⟩, hQ, hQx⟩ := List.mem_filterMap.mp hx₁
        simp only at hQx
        subst hQx
        have hQend := (M₁.site_ok (Q, some x) (by rw [hp]; exact List.mem_cons_of_mem _ hQ) x rfl).2
        let M₁' := (M₁.castE (h.plus_sub hy hyx hxy)).forgetAll S
        have hQ' : (Q, none) ∈ M₁'.paths := by
          show (Q, none) ∈ M₁.paths.map (fun y => (y.1, none))
          rw [hp]
          exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, hQ, rfl⟩)
        have hL' : (L, none) ∈ M₁'.paths := by
          show (L, none) ∈ M₁.paths.map (fun y => (y.1, none))
          rw [hp]; exact List.mem_cons_self
        have hne : ((Q, none) : GPath G × Option W) ≠ (L, none) := by
          intro heq
          exact M₁.fst_ne_of_mem_tail hp hQ (by simpa using congrArg Prod.fst heq)
        obtain ⟨rest', hrest'⟩ := perm_two_of_mem hL' hQ' hne
        refine ⟨M₁', L, Q, rest', hrest', Or.inl hL, hQend, ?_⟩
        rw [PMP.forgetAll_cost]
        show M₁.paths.length ≤ _
        have := M₁.sites_length_le
        rw [Finset.card_singleton] at this
        omega
      · left
        refine ⟨(M₁.castE (h.plus_sub hy hyx hxy)).forgetAll S, ?_, by simp [PMP.forgetAll_sites]⟩
        rw [PMP.forgetAll_cost]
        show M₁.paths.length ≤ _
        have h0 : mSites M₁.paths = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro s hs
          have := M₁.sites_mem hs
          rw [Finset.mem_singleton] at this
          exact hx₁ (this ▸ hs)
        rw [h0] at hlen
        simp at hlen
        omega
  obtain ⟨a, ha⟩ := he1
  obtain ⟨b, hb⟩ := he2
  rcases key with ⟨M₁, hc₁, hx₁⟩ | ⟨M₁, P, Q, rest, hperm, hPx, hQx, hc₁⟩
  · obtain ⟨M, -, hM⟩ := glue0 h.glue M₁ M₂' (Or.inl hx₁)
    have := h.finish M
    omega
  · by_cases hend : ∃ z ∈ M₂'.paths, z.1.src = x ∨ z.1.tgt = x
    · obtain ⟨⟨R, o⟩, hR, hRx⟩ := hend
      have ho : ∀ s, o = some s → s ≠ x := fun s hs hsx =>
        hxM₂ (hsx ▸ List.mem_filterMap.mpr ⟨_, hR, hs⟩)
      obtain ⟨M, hM⟩ := glueEnd h.glue M₁ M₂' (Or.inr hxM₂) (hperm.mem_iff.mpr
        List.mem_cons_self) hPx hR hRx ho
      have := h.finish M
      omega
    · push Not at hend
      have he : s(x, y) ∈ (restrict G U₂).edgeSet := ⟨hxy, h.hx₂, hy⟩
      obtain ⟨⟨R, o⟩, hR, hxR, hRs, hRt⟩ := M₂'.exists_internal he (Sym2.mem_mk_left _ _)
        (fun z hz => ⟨(hend z hz).1, (hend z hz).2⟩)
      obtain ⟨M, hM⟩ := glueSplit h.glue M₁ M₂' hxM₂ hperm hPx hQx hR hxR hRs hRt
      have := h.finish M
      omega

/-- **Cut-vertex reduction** (marked-reduction manuscript, p. 5): if `U` splits at a cut vertex
into two sides of order at least three, the marked bound on smaller instances gives it on `U`. -/
theorem cutStep (h : CutSides G U x U₁ U₂) (IH : SmallerMB U) : MBOn G U := by
  intro S hSU hS
  by_cases hxS : x ∈ S
  · rcases Nat.even_or_odd (U₁.card - (S ∩ U₁).card) with h1 | h1
    · exact cut_xS_even h IH hSU hxS h1
    · rcases Nat.even_or_odd (U₂.card - (S ∩ U₂).card) with h2 | h2
      · exact cut_xS_even h.symm IH hSU hxS h2
      · exact cut_xS_odd h IH hSU hxS h1 h2
  · by_cases hodd : Odd (U₁.card - 1 - (S ∩ U₁).card) ∨ Odd (U₂.card - 1 - (S ∩ U₂).card)
    · exact cut_xnS_odd h IH hSU hxS hodd
    · push Not at hodd
      by_cases h1 : (S ∩ U₁).Nonempty
      · by_cases h2 : (S ∩ U₂).Nonempty
        · exact cut_xnS_marked h IH hSU hxS h1 h2 hodd.1 hodd.2
        · rw [Finset.not_nonempty_iff_eq_empty] at h2
          have := hodd.2
          rw [h2, Finset.card_empty, Nat.sub_zero] at this
          exact cut_xnS_tight h.symm IH hSU hxS hS h2 this hodd.1
      · rw [Finset.not_nonempty_iff_eq_empty] at h1
        have := hodd.1
        rw [h1, Finset.card_empty, Nat.sub_zero] at this
        exact cut_xnS_tight h IH hSU hxS hS h1 this hodd.2

end cut

/-! ### Leaves -/

section leaf

variable {U : Finset W} {w v : W}

/-- Attach the pendant edge `wv` after forgetting the site `v`: extend the path that carried `v`,
or add the edge as a new path. -/
theorem attach_pendant {E : Set (Sym2 W)} {T : Finset W} (M : PMP G E T) (hadj : G.Adj w v)
    (hw : ∀ y ∈ M.paths, w ∉ y.1.walk.support) (hwv : s(w, v) ∉ E) (o' : Option W)
    (ho' : o' = none ∨ (o' = some w ∧ w ∈ T.erase v ∧ w ∉ mSites M.paths)) :
    ∃ M' : PMP G (E ∪ {e | e ∈ [s(w, v)]}) (T.erase v),
      M'.cost = M.cost + (if o' = none then 1 else 0) := by
  classical
  have ho'' : o' = none ∨ (o' = some w ∧ w ∈ T.erase v ∧ w ∉ mSites (M.forget v).paths) := by
    rcases ho' with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · refine Or.inr ⟨h1, h2, fun h => h3 ?_⟩
      rw [PMP.forget_paths, PMP.mSites_map_forgetOne] at h
      exact (List.mem_filter.mp h).1
  by_cases hv : v ∈ mSites M.paths
  · obtain ⟨⟨P, oP⟩, hP, hPv⟩ := List.mem_filterMap.mp hv
    simp only at hPv
    subst hPv
    have hPend := (M.site_ok _ hP v rfl).2
    have hP' : (P, none) ∈ (M.forget v).paths :=
      List.mem_map.mpr ⟨_, hP, by simp [PMP.forgetOne]⟩
    have hperm := List.perm_cons_erase hP'
    obtain ⟨M', P', hM', -⟩ := (M.forget v).exists_extend hperm hPend hadj (hw _ hP) hwv o' ho''
    refine ⟨M', ?_⟩
    have e1 : (M.forget v).cost = mCost ((P, none) :: (M.forget v).paths.erase (P, none)) :=
      mCost_perm hperm
    have e2 : M'.cost = mCost ((P', o') :: (M.forget v).paths.erase (P, none)) := by
      rw [PMP.cost, hM']
    have e3 : (M.forget v).cost = M.cost + 1 := by
      show mCost (M.paths.map (PMP.forgetOne v)) = mCost M.paths + 1
      rw [PMP.mCost_map_forgetOne, List.count_eq_one_of_mem M.sites_nodup hv]
    generalize (M.forget v).paths.erase (P, none) = rest at e1 e2
    simp only [mCost_cons, Option.isNone_none, ite_true] at e1 e2
    rcases ho' with h | ⟨h, -, -⟩ <;> subst h <;>
      simp only [Option.isNone_none, Option.isNone_some, ite_true, ite_false,
        Bool.false_eq_true, reduceCtorEq, add_zero] at e2 ⊢ <;> omega
  · have hok : SiteOK (T.erase v) [(GPath.ofAdj hadj, o')] := by
      intro y hy s hs
      rw [List.mem_singleton] at hy
      subst hy
      rcases ho' with h | ⟨h, h2, -⟩
      · rw [h] at hs; simp at hs
      · rw [h] at hs
        simp only [Option.some.injEq] at hs
        subst hs
        exact ⟨h2, Or.inl rfl⟩
    have hnew : ∀ s, o' = some s → s ∉ mSites (M.forget v).paths := by
      intro s hs
      rcases ho'' with h | ⟨h, -, h3⟩
      · rw [h] at hs; simp at hs
      · rw [h] at hs
        simp only [Option.some.injEq] at hs
        exact hs ▸ h3
    refine ⟨(M.forget v).addPath (GPath.ofAdj hadj) o' hok (by simpa using hwv) hnew, ?_⟩
    show mCost ((GPath.ofAdj hadj, o') :: (M.forget v).paths) = _
    rw [mCost_cons]
    have := M.forget_cost_of_not_mem hv
    rw [PMP.cost] at this
    rw [this]
    rcases ho' with h | ⟨h, -, -⟩ <;> subst h <;> simp

theorem leaf_avoid {T : Finset W} (M : PMP G (restrict G (U.erase w)).edgeSet T) :
    ∀ y ∈ M.paths, w ∉ y.1.walk.support := by
  intro y hy hwy
  have := M.support_subset (U := ((U.erase w : Finset W) : Set W))
    (fun e he v hv => (mem_restrict_edgeSet.mp he).2 v hv) hy w hwy
  simp at this

/-- **Leaf reductions** (marked-reduction manuscript, pp. 4–5): a leaf can be deleted unless the
only site is its neighbour and the order is even. -/
theorem leafStep (IH : SmallerMB U) (hE : EdgesIn G U) (hC : ConnOn G U) (hl : IsLeafAt G w v)
    {S : Finset W} (hSU : S ⊆ U) (hS : S.Nonempty) (hres : ¬ (S = {v} ∧ Even U.card)) :
    markedNumber G S ≤ (U.card - S.card) / 2 := by
  obtain ⟨hwU, hvU⟩ := hl.mem hE
  have hcard : (U.erase w).card + 1 = U.card := Finset.card_erase_add_one hwU
  have hMB := IH (restrict G (U.erase w)) (U.erase w) (by omega) (edgesIn_restrict _)
    (hl.conn hE hC)
  have hvU' : v ∈ U.erase w := Finset.mem_erase.mpr ⟨hl.ne.symm, hvU⟩
  have hedge := hl.edgeSet_eq hE
  have hedge' : G.edgeSet = (restrict G (U.erase w)).edgeSet ∪ {e | e ∈ [s(w, v)]} := by
    rw [hedge, Sym2.eq_swap]
  have hwv : s(w, v) ∉ (restrict G (U.erase w)).edgeSet :=
    fun h => IsLeafAt.not_mem_restrict h (Sym2.mem_mk_left _ _)
  have hsub : ∀ T : Finset W, T ⊆ U → w ∉ T → T ⊆ U.erase w :=
    fun T hT hw x hx => Finset.mem_erase.mpr ⟨fun h => hw (h ▸ hx), hT hx⟩
  have hU2 : 2 ≤ U.card := by
    have := Finset.card_le_card (Finset.insert_subset hwU (Finset.singleton_subset_iff.mpr hvU))
    rw [Finset.card_insert_of_notMem (by simpa using hl.ne), Finset.card_singleton] at this
    exact this
  by_cases hwS : w ∈ S
  · by_cases hS' : (S.erase w).Nonempty
    · -- a marked leaf with another mark: assign its edge singly
      obtain ⟨M, hM⟩ := exists_pmp_restrict hMB (S' := S.erase w)
        (fun x hx => Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, hSU (Finset.mem_of_mem_erase hx)⟩) hS'
      let M₁ := M.mono (Finset.erase_subset w S)
      have hok : SiteOK S [(GPath.ofAdj hl.1, some w)] := by
        intro y hy t ht
        rw [List.mem_singleton] at hy; subst hy
        simp only [Option.some.injEq] at ht; subst ht
        exact ⟨hwS, Or.inl rfl⟩
      have hnew : ∀ t, some w = some t → t ∉ mSites M₁.paths := by
        intro t ht h'
        simp only [Option.some.injEq] at ht; subst ht
        exact (Finset.mem_erase.mp (M.sites_mem h')).1 rfl
      have hwv' : ∀ e ∈ (GPath.ofAdj hl.1).edges, e ∉ (restrict G (U.erase w)).edgeSet := by
        intro e he; rw [GPath.ofAdj_edges, List.mem_singleton] at he; subst he; exact hwv
      let M₂ := M₁.addPath (GPath.ofAdj hl.1) (some w) hok hwv' hnew
      have := (M₂.castE hedge'.symm).markedNumber_le_cost
      have e : (M₂.castE hedge'.symm).cost = M.cost := by
        show mCost ((GPath.ofAdj hl.1, some w) :: M.paths) = mCost M.paths
        simp
      rw [Finset.card_erase_of_mem hwS] at hM
      have := Finset.card_pos.mpr hS
      omega
    · -- the leaf is the only mark: mark its neighbour instead
      have hSw : S = {w} := by
        rw [Finset.not_nonempty_iff_eq_empty] at hS'
        ext x; constructor
        · intro hx; by_contra hxw
          have : x ∈ S.erase w := Finset.mem_erase.mpr ⟨by simpa using hxw, hx⟩
          rw [hS'] at this; simp at this
        · intro hx; rw [Finset.mem_singleton.mp hx]; exact hwS
      subst hSw
      obtain ⟨M, hM⟩ := exists_pmp_restrict hMB (S' := {v})
        (Finset.singleton_subset_iff.mpr hvU') (Finset.singleton_nonempty v)
      let M₀ := M.mono (Finset.subset_insert w {v})
      have hwM : w ∉ mSites M₀.paths := fun h' => by
        have := M.sites_mem h'
        rw [Finset.mem_singleton] at this
        exact hl.ne this
      obtain ⟨M', hM'⟩ := attach_pendant M₀ hl.1 (leaf_avoid M) hwv (some w)
        (Or.inr ⟨rfl, Finset.mem_erase.mpr ⟨hl.ne, Finset.mem_insert_self _ _⟩, hwM⟩)
      have hT : (insert w {v} : Finset W).erase v ⊆ {w} := by
        intro x hx
        simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with ⟨hxv, rfl | rfl⟩
        · simp
        · exact absurd rfl hxv
      have := ((M'.mono hT).castE hedge'.symm).markedNumber_le_cost
      have e : ((M'.mono hT).castE hedge'.symm).cost = M'.cost := rfl
      have e0 : M₀.cost = M.cost := rfl
      simp only [reduceCtorEq, ite_false, add_zero] at hM'
      rw [Finset.card_singleton] at hM
      rw [Finset.card_singleton]
      omega
  · have hSU' := hsub S hSU hwS
    by_cases hvS : v ∈ S
    · by_cases hS' : (S.erase v).Nonempty
      · -- an unmarked leaf at a mark, with another mark: assign the leaf edge to its neighbour
        obtain ⟨M, hM⟩ := exists_pmp_restrict hMB (S' := S.erase v)
          ((Finset.erase_subset v S).trans hSU') hS'
        let M₁ := M.mono (Finset.erase_subset v S)
        have hok : SiteOK S [(GPath.ofAdj hl.1.symm, some v)] := by
          intro y hy t ht
          rw [List.mem_singleton] at hy; subst hy
          simp only [Option.some.injEq] at ht; subst ht
          exact ⟨hvS, Or.inl rfl⟩
        have hnew : ∀ t, some v = some t → t ∉ mSites M₁.paths := by
          intro t ht h'
          simp only [Option.some.injEq] at ht; subst ht
          exact (Finset.mem_erase.mp (M.sites_mem h')).1 rfl
        have hvw : ∀ e ∈ (GPath.ofAdj hl.1.symm).edges, e ∉ (restrict G (U.erase w)).edgeSet := by
          intro e he; rw [GPath.ofAdj_edges, List.mem_singleton] at he; subst he
          rw [Sym2.eq_swap]; exact hwv
        let M₂ := M₁.addPath (GPath.ofAdj hl.1.symm) (some v) hok hvw hnew
        have := (M₂.castE hedge.symm).markedNumber_le_cost
        have e : (M₂.castE hedge.symm).cost = M.cost := by
          show mCost ((GPath.ofAdj hl.1.symm, some v) :: M.paths) = mCost M.paths
          simp
        rw [Finset.card_erase_of_mem hvS] at hM
        have := Finset.card_pos.mpr hS
        omega
      · -- the neighbour is the only mark: then the order is odd
        have hSv : S = {v} := by
          rw [Finset.not_nonempty_iff_eq_empty] at hS'
          ext x; constructor
          · intro hx; by_contra hxv
            have : x ∈ S.erase v := Finset.mem_erase.mpr ⟨by simpa using hxv, hx⟩
            rw [hS'] at this; simp at this
          · intro hx; rw [Finset.mem_singleton.mp hx]; exact hvS
        have hodd : ¬ Even U.card := fun h => hres ⟨hSv, h⟩
        rw [Nat.not_even_iff_odd, Nat.odd_iff] at hodd
        subst hSv
        obtain ⟨M, hM⟩ := exists_pmp_restrict hMB hSU' hS
        obtain ⟨M', hM'⟩ := attach_pendant M hl.1 (leaf_avoid M) hwv none (Or.inl rfl)
        have := ((M'.mono (Finset.erase_subset v {v})).castE hedge'.symm).markedNumber_le_cost
        have e : ((M'.mono (Finset.erase_subset v {v})).castE hedge'.symm).cost = M'.cost := rfl
        simp only [ite_true] at hM'
        rw [Finset.card_singleton] at hM ⊢
        omega
    · -- an unmarked leaf at an unmarked vertex: mark the neighbour temporarily
      obtain ⟨M, hM⟩ := exists_pmp_restrict hMB (S' := insert v S)
        (Finset.insert_subset hvU' hSU') (Finset.insert_nonempty _ _)
      obtain ⟨M', hM'⟩ := attach_pendant M hl.1 (leaf_avoid M) hwv none (Or.inl rfl)
      have hT : (insert v S).erase v ⊆ S := by rw [Finset.erase_insert hvS]
      have := ((M'.mono hT).castE hedge'.symm).markedNumber_le_cost
      have e : ((M'.mono hT).castE hedge'.symm).cost = M'.cost := rfl
      simp only [ite_true] at hM'
      rw [Finset.card_insert_of_notMem hvS] at hM
      have := Finset.card_le_card (Finset.insert_subset hvU' hSU')
      rw [Finset.card_insert_of_notMem hvS] at this
      omega

/-- **Two leaves at the only mark**: delete both and add their edges as one unassigned path. -/
theorem doubleLeafStep (IH : SmallerMB U) (hE : EdgesIn G U) (hC : ConnOn G U) {w w' : W}
    (hl : IsLeafAt G w v) (hl' : IsLeafAt G w' v) (hww : w ≠ w') :
    markedNumber G {v} ≤ (U.card - 1) / 2 := by
  obtain ⟨hwU, hvU⟩ := hl.mem hE
  obtain ⟨hw'U, -⟩ := hl'.mem hE
  set U' := U.erase w with hU'
  have hw'U' : w' ∈ U' := Finset.mem_erase.mpr ⟨Ne.symm hww, hw'U⟩
  have hvU' : v ∈ U' := Finset.mem_erase.mpr ⟨hl.ne.symm, hvU⟩
  have hC' := hl.conn hE hC
  have hl'' : IsLeafAt (restrict G U') w' v :=
    ⟨⟨hl'.1, hw'U', hvU'⟩, fun y hy => hl'.2 y hy.1⟩
  have hC'' := hl''.conn (edgesIn_restrict U') hC'
  rw [restrict_restrict (Finset.erase_subset _ _)] at hC''
  have hcard : (U'.erase w').card + 2 = U.card := by
    rw [Finset.card_erase_of_mem hw'U', hU', Finset.card_erase_of_mem hwU]
    have := Finset.card_le_card (Finset.insert_subset hwU (Finset.singleton_subset_iff.mpr hw'U))
    rw [Finset.card_insert_of_notMem (by simpa using hww), Finset.card_singleton] at this
    omega
  have hMB := IH (restrict G (U'.erase w')) (U'.erase w') (by omega) (edgesIn_restrict _) hC''
  have hvU'' : v ∈ U'.erase w' := Finset.mem_erase.mpr ⟨hl'.ne.symm, hvU'⟩
  obtain ⟨M, hM⟩ := exists_pmp_restrict hMB (Finset.singleton_subset_iff.mpr hvU'')
    (Finset.singleton_nonempty v)
  rw [Finset.card_singleton] at hM
  have hvw : ∀ e ∈ (GPath.ofAdj hl.1.symm).edges, e ∉ (restrict G (U'.erase w')).edgeSet := by
    intro e he h'
    rw [GPath.ofAdj_edges, List.mem_singleton] at he; subst he
    have := (mem_restrict_edgeSet.mp h').2 w (Sym2.mem_mk_right _ _)
    simp [hU'] at this
  let M₁ := M.addPath (GPath.ofAdj hl.1.symm) none
    (by intro y hy t ht; rw [List.mem_singleton] at hy; subst hy; simp at ht) hvw (by simp)
  have hw' : w' ∉ (GPath.ofAdj hl.1.symm).walk.support := by
    simp only [GPath.ofAdj, Walk.support_cons, Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    exact ⟨hl'.ne, Ne.symm hww⟩
  have hwv : s(w', v) ∉ (restrict G (U'.erase w')).edgeSet ∪
      {e | e ∈ (GPath.ofAdj hl.1.symm).edges} := by
    rintro (h' | h')
    · have := (mem_restrict_edgeSet.mp h').2 w' (Sym2.mem_mk_left _ _)
      simp at this
    · simp only [GPath.ofAdj_edges, Set.mem_ofPred_eq, List.mem_singleton, Sym2.eq_iff] at h'
      rcases h' with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hl'.ne h1
      · exact hww h1.symm
  obtain ⟨M₂, P', hM₂, -⟩ := M₁.exists_extend (P := GPath.ofAdj hl.1.symm) (rest := M.paths)
    (List.Perm.refl _) (Or.inl rfl) hl'.1 hw' hwv none (Or.inl rfl)
  have hedge1 := hl.edgeSet_eq hE
  have hedge2 := hl''.edgeSet_eq (edgesIn_restrict U')
  rw [restrict_restrict (Finset.erase_subset _ _)] at hedge2
  have hedge : G.edgeSet = ((restrict G (U'.erase w')).edgeSet ∪
      {e | e ∈ (GPath.ofAdj hl.1.symm).edges}) ∪ {e | e ∈ [s(w', v)]} := by
    rw [hedge1, hedge2, show s(w', v) = s(v, w') from Sym2.eq_swap]
    ext e
    simp only [Set.mem_union, Set.mem_ofPred_eq, List.mem_singleton, GPath.ofAdj_edges]
    tauto
  have := (M₂.castE hedge.symm).markedNumber_le_cost
  have e1 : (M₂.castE hedge.symm).cost = mCost M.paths + 1 := by
    show mCost M₂.paths = _
    rw [hM₂]; simp
  have hpos : 1 ≤ (U'.erase w').card := Finset.card_pos.mpr ⟨v, hvU''⟩
  have : M.cost = mCost M.paths := rfl
  omega

end leaf

/-! ### Base cases -/

theorem baseStep {U : Finset W} (hE : EdgesIn G U) (h2 : U.card ≤ 2) : MBOn G U := by
  intro S hSU hS
  obtain ⟨s, hs⟩ := hS
  by_cases hedge : G.edgeSet = ∅
  · have := ((PMP.empty (G := G) S).castE hedge.symm).markedNumber_le_cost
    have e : ((PMP.empty (G := G) S).castE hedge.symm).cost = 0 := rfl
    omega
  · obtain ⟨e, he⟩ := Set.nonempty_iff_ne_empty.mpr hedge
    induction e using Sym2.inductionOn with
    | hf a b =>
    have hab : G.Adj a b := he
    have hne : a ≠ b := hab.ne
    have hsub : ({a, b} : Finset W) ⊆ U :=
      Finset.insert_subset (hE a b hab).1 (Finset.singleton_subset_iff.mpr (hE a b hab).2)
    have hcard2 : ({a, b} : Finset W).card = 2 := Finset.card_pair hne
    have hU : ({a, b} : Finset W) = U := Finset.eq_of_subset_of_card_le hsub (by omega)
    have hG : G.edgeSet = ∅ ∪ {e | e ∈ (GPath.ofAdj hab).edges} := by
      ext e
      induction e using Sym2.inductionOn with
      | hf p q =>
      simp only [Set.empty_union, GPath.ofAdj_edges, Set.mem_ofPred_eq, List.mem_singleton,
        mem_edgeSet]
      constructor
      · intro hpq
        have hp := (hE p q hpq).1
        have hq := (hE p q hpq).2
        rw [← hU] at hp hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
        have hpq' : p ≠ q := hpq.ne
        rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
        · exact absurd rfl hpq'
        · rfl
        · exact Sym2.eq_swap
        · exact absurd rfl hpq'
      · intro h'
        rcases Sym2.eq_iff.mp h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hab
        · exact hab.symm
    have hsab : s = a ∨ s = b := by
      have := hSU hs
      rw [← hU] at this
      simpa using this
    have hok : SiteOK S [(GPath.ofAdj hab, some s)] := by
      intro y hy t ht
      rw [List.mem_singleton] at hy; subst hy
      simp only [Option.some.injEq] at ht; subst ht
      refine ⟨hs, ?_⟩
      rcases hsab with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    let M := (PMP.empty (G := G) S).addPath (GPath.ofAdj hab) (some s) hok (by simp)
      (fun t _ h => by simp [PMP.empty, mSites] at h)
    have := (M.castE hG.symm).markedNumber_le_cost
    have e : (M.castE hG.symm).cost = 0 := by
      show mCost [(GPath.ofAdj hab, some s)] = 0
      simp
    omega

/-! ### Two-connected instances as graphs on a subtype -/

/-- The graph induced on the subtype of `U`. -/
def onSub (G : SimpleGraph W) (U : Finset W) : SimpleGraph {x // x ∈ U} where
  Adj a b := G.Adj a.1 b.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun a h => G.loopless.irrefl a.1 h⟩

/-- Two-connectedness of a graph on a finite type: no cut vertex. -/
def TwoConnected {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  TwoConnOn G Finset.univ

theorem onSub_reach {U : Finset W} {a b : W} (p : G.Walk a b) (h : ∀ v ∈ p.support, v ∈ U) :
    (onSub G U).Reachable ⟨a, h a p.start_mem_support⟩ ⟨b, h b p.end_mem_support⟩ := by
  induction p with
  | nil => exact Reachable.refl _
  | @cons a c b hac q ih =>
    have hq : ∀ v ∈ q.support, v ∈ U := fun v hv => h v (by simp [hv])
    exact (show (onSub G U).Adj ⟨a, h a (by simp)⟩ ⟨c, hq c q.start_mem_support⟩ from hac).reachable.trans
      (ih hq)

theorem card_sub (U : Finset W) : Fintype.card {x // x ∈ U} = U.card := Fintype.card_coe U

theorem onSub_twoConnected {U : Finset W} (hE : EdgesIn G U) (h : TwoConnOn G U) :
    TwoConnected (onSub G U) := by
  refine ⟨by rw [Finset.card_univ, card_sub]; exact h.1, ?_, ?_⟩
  · intro a _ b _
    obtain ⟨p⟩ := h.2.1 a.1 a.2 b.1 b.2
    exact onSub_reach p (hE.walk_mem p a.2)
  · intro x C hsep
    apply h.2.2 x.1 (C.map (Function.Embedding.subtype _))
    obtain ⟨-, hCsub, hCne, hDne, hcl⟩ := hsep
    refine ⟨x.2, ?_, hCne.map, ?_, ?_⟩
    · intro c hc
      obtain ⟨c', hc', rfl⟩ := Finset.mem_map.mp hc
      have := Finset.mem_erase.mp (hCsub hc')
      exact Finset.mem_erase.mpr ⟨fun h' => this.1 (Subtype.ext h'), c'.2⟩
    · obtain ⟨d, hd⟩ := hDne
      rw [Finset.mem_sdiff, Finset.mem_erase] at hd
      refine ⟨d.1, Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨fun h' => hd.1.1 (Subtype.ext h'),
        d.2⟩, fun h' => hd.2 ?_⟩⟩
      obtain ⟨d', hd', hdd⟩ := Finset.mem_map.mp h'
      rwa [show d' = d from Subtype.ext hdd] at hd'
    · intro a ha b hab
      obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
      have hbU := (hE _ b hab).2
      rcases hcl a' ha' ⟨b, hbU⟩ hab with h' | h'
      · exact Or.inl (Finset.mem_map.mpr ⟨_, h', rfl⟩)
      · exact Or.inr (congrArg Subtype.val h')

theorem onSub_edges {U : Finset W} (hE : EdgesIn G U) :
    {e | ∃ e' ∈ (onSub G U).edgeSet, e'.map Subtype.val = e} = G.edgeSet := by
  ext e
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨e', he', rfl⟩
    induction e' using Sym2.inductionOn with
    | hf a b => exact he'
  · intro he
    induction e using Sym2.inductionOn with
    | hf a b =>
    exact ⟨s(⟨a, (hE a b he).1⟩, ⟨b, (hE a b he).2⟩), he, rfl⟩

/-- A marked partition on the subtype gives one of `G`. -/
theorem markedNumber_le_onSub {U : Finset W} (hE : EdgesIn G U) (S : Finset W) :
    markedNumber G S ≤ markedNumber (onSub G U) (S.subtype (· ∈ U)) := by
  obtain ⟨M₀, hM₀⟩ := markedNumber_spec (onSub G U) (S.subtype (· ∈ U))
  let M₁ := PMP.push (G := G) M₀ Subtype.val Subtype.val_injective (fun _ _ h => h)
  have hsub : (S.subtype (· ∈ U)).map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ S := by
    intro s hs
    obtain ⟨s', hs', rfl⟩ := Finset.mem_map.mp hs
    exact (Finset.mem_subtype.mp hs')
  have := ((M₁.castE (onSub_edges hE)).mono hsub).markedNumber_le_cost
  have e : ((M₁.castE (onSub_edges hE)).mono hsub).cost = markedCost M₀ :=
    PMP.push_cost M₀ _ _ _
  omega

theorem card_subtype_of_subset {U S : Finset W} (hSU : S ⊆ U) :
    (S.subtype (· ∈ U)).card = S.card := by
  rw [Finset.card_subtype, Finset.filter_true_of_mem (fun x hx => hSU hx)]

/-- The first assertion of Theorem 1: the marked bound on every two-connected graph and every
nonempty set of sites. -/
def MarkedTwoConnTest : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V), TwoConnected G →
    ∀ S : Finset V, S.Nonempty → markedNumber G S ≤ (Fintype.card V - S.card) / 2

/-- The second assertion of Theorem 1: in a two-connected graph of order `2k + 1` with path
number `k + 1`, every odd-degree vertex has three ends in some `(k + 1)`-path partition. -/
def ThreeEndsTest : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj],
    TwoConnected J → ∀ k : ℕ, Fintype.card V = 2 * k + 1 → pathNumber J = k + 1 →
      ∀ x, Odd (J.degree x) → ∃ D : PathDecomp J, D.size = k + 1 ∧ 3 ≤ D.ends x

theorem twoConnStep (hA : MarkedTwoConnTest.{u}) {U : Finset W} (hE : EdgesIn G U)
    (h : TwoConnOn G U) : MBOn G U := by
  intro S hSU hS
  have hS' : (S.subtype (· ∈ U)).Nonempty := by
    obtain ⟨s, hs⟩ := hS
    exact ⟨⟨s, hSU hs⟩, Finset.mem_subtype.mpr hs⟩
  have h1 := hA _ (onSub G U) (onSub_twoConnected hE h) _ hS'
  rw [card_sub, card_subtype_of_subset hSU] at h1
  exact (markedNumber_le_onSub hE S).trans h1

end Gallai
