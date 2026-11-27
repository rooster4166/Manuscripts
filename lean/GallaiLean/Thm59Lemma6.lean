import GallaiLean.MarkedBlocks

/-!
# Lemma 6 for a matching cut

Marked-reduction manuscript, Lemma 6 (p. 12), in the two-part case used by Theorem 7 (a matching
cut with the crossing edges as one-edge interpart paths).

All graphs live in one vertex type `W`, inside an ambient graph `H`. The data (`CrossData`):

* two disjoint vertex sets `U₁, U₂` containing every edge;
* a set `A₁ ⊆ U₁` of crossing ends, with a partner map `φ` (injective on `A₁`, into `U₂`);
* the crossing edges, which are exactly the edges `a φ(a)`.

**`lemma6`.** Take partial marked partitions `M₁` of the edges inside `U₁` with sites `A₁`, and
`M₂` of the edges inside `U₂` with sites `φ(A₁)`. Then `H` has a path decomposition with at most
`cost M₁ + cost M₂ + |A₁|` paths.

Proof. For each crossing edge `a φ(a)`, remove the paths assigned to `a` and to `φ(a)` (if any)
and put back their union through the edge (`cross_step`). This is one path, since the two
assigned paths lie inside `U₁` and inside `U₂` respectively. Each step adds one unassigned path.
At the end no site is used.
-/

open SimpleGraph
open scoped List

set_option linter.unusedSectionVars false

namespace Gallai

universe u

variable {W : Type u} [DecidableEq W] {H : SimpleGraph W}

/-- A matching cut between `U₁` and `U₂` with crossing ends `A₁ ⊆ U₁` and partner map `φ`. -/
structure CrossData (H : SimpleGraph W) (U₁ U₂ A₁ : Finset W) (φ : W → W) : Prop where
  disj : Disjoint U₁ U₂
  edges : EdgesIn H (U₁ ∪ U₂)
  sub : A₁ ⊆ U₁
  maps : ∀ a ∈ A₁, φ a ∈ U₂
  inj : Set.InjOn φ A₁
  adj : ∀ a ∈ A₁, H.Adj a (φ a)
  cross : ∀ a ∈ U₁, ∀ b ∈ U₂, H.Adj a b → a ∈ A₁ ∧ b = φ a

/-- The crossing edges at the ends `T`. -/
def crossSet (φ : W → W) (T : Finset W) : Set (Sym2 W) := {e | ∃ a ∈ T, e = s(a, φ a)}

/-- Assigned paths keep to the side of their site. -/
def SuppInv (U₁ U₂ : Finset W) (l : List (GPath H × Option W)) : Prop :=
  ∀ y ∈ l, ∀ s, y.2 = some s → ∀ v ∈ y.1.walk.support, (s ∈ U₁ → v ∈ U₁) ∧ (s ∈ U₂ → v ∈ U₂)

/-- An optional path assigned to `s`. -/
def optSite (o : Option (GPath H)) (s : W) : List (GPath H × Option W) :=
  o.elim [] (fun P => [(P, some s)])

@[simp] theorem mEdges_optSite (o : Option (GPath H)) (s : W) :
    mEdges (optSite o s) = o.elim [] GPath.edges := by
  cases o <;> simp [optSite, mEdges]

@[simp] theorem mCost_optSite (o : Option (GPath H)) (s : W) : mCost (optSite o s) = 0 := by
  cases o <;> simp [optSite]

theorem mSites_optSite (o : Option (GPath H)) (s : W) :
    mSites (optSite o s) = o.elim [] (fun _ => [s]) := by
  cases o <;> simp [optSite]

theorem SuppInv.of_subperm {U₁ U₂ : Finset W} {l l' : List (GPath H × Option W)}
    (h : SuppInv U₁ U₂ l) (hs : l'.Subperm l) : SuppInv U₁ U₂ l' :=
  fun y hy => h y (hs.subset hy)

/-- Split off the path assigned to `s`, if there is one. -/
theorem exists_optSite_split (l : List (GPath H × Option W)) (hnd : (mSites l).Nodup) (s : W) :
    ∃ (o : Option (GPath H)) (rest : List (GPath H × Option W)),
      l.Perm (optSite o s ++ rest) ∧ s ∉ mSites rest ∧ ∀ P, o = some P → (P, some s) ∈ l := by
  classical
  by_cases hs : s ∈ mSites l
  · obtain ⟨y, hy, hys⟩ := List.mem_filterMap.mp hs
    obtain ⟨P, o⟩ := y
    simp only at hys
    subst hys
    refine ⟨some P, l.erase (P, some s), ?_, ?_, fun Q hQ => by cases hQ; exact hy⟩
    · exact List.perm_cons_erase hy
    · have hp := mSites_perm (List.perm_cons_erase hy)
      rw [mSites_cons] at hp
      have := hp.nodup_iff.mp hnd
      simpa using (List.nodup_cons.mp this).1
  · exact ⟨none, l, by simp [optSite], hs, fun P hP => by cases hP⟩

/-- **One crossing edge.** Remove the paths assigned to `a` and `φ a` and replace them by their
union through the crossing edge. -/
theorem cross_step {U₁ U₂ A₁ : Finset W} {φ : W → W} (hd : CrossData H U₁ U₂ A₁ φ)
    {E : Set (Sym2 W)} {S : Finset W} (M : PMP H E S) {a : W} (ha : a ∈ A₁)
    (he : s(a, φ a) ∉ E) (hsupp : SuppInv U₁ U₂ M.paths) :
    ∃ M' : PMP H (E ∪ {e | e ∈ [s(a, φ a)]}) S, M'.cost ≤ M.cost + 1 ∧
      (mSites M'.paths).Subperm (mSites M.paths) ∧ a ∉ mSites M'.paths ∧
      φ a ∉ mSites M'.paths ∧ SuppInv U₁ U₂ M'.paths := by
  set b := φ a with hb
  have hab : H.Adj a b := hd.adj a ha
  have haU : a ∈ U₁ := hd.sub ha
  have hbU : b ∈ U₂ := hd.maps a ha
  have hbU₁ : b ∉ U₁ := fun h => Finset.disjoint_left.mp hd.disj h hbU
  obtain ⟨oa, rest₁, hp₁, hna, hoa⟩ := exists_optSite_split M.paths M.sites_nodup a
  have hnd₁ : (mSites rest₁).Nodup := by
    have := (mSites_perm hp₁).nodup_iff.mp M.sites_nodup
    rw [mSites_append] at this
    exact (List.nodup_append.mp this).2.1
  obtain ⟨ob, rest₂, hp₂, hnb, hob⟩ := exists_optSite_split rest₁ hnd₁ b
  have hM : M.paths.Perm ((optSite oa a ++ optSite ob b) ++ rest₂) := by
    rw [List.append_assoc]; exact hp₁.trans (hp₂.append_left _)
  have hmem₁ : ∀ y ∈ rest₁, y ∈ M.paths := fun y hy =>
    hp₁.symm.subset (List.mem_append_right _ hy)
  -- the joined path
  set R0 := GPath.ofAdj hab with hR0
  have hR0supp : R0.walk.support = [a, b] := rfl
  obtain ⟨J₁, hJ₁t, hJ₁e, hJ₁s⟩ : ∃ J₁ : GPath H, J₁.tgt = b ∧
      J₁.edges.Perm (oa.elim [] GPath.edges ++ [s(a, b)]) ∧
      ∀ v ∈ J₁.walk.support, v ∈ U₁ ∨ v = b := by
    cases oa with
    | none =>
      refine ⟨R0, rfl, by simp [R0], fun v hv => ?_⟩
      rw [hR0supp] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact Or.inl haU
      · exact Or.inr rfl
    | some P =>
      have hPM : (P, some a) ∈ M.paths := hoa P rfl
      have hPend := (M.site_ok _ hPM a rfl).2
      have hPsupp : ∀ v ∈ P.walk.support, v ∈ U₁ := fun v hv =>
        (hsupp _ hPM a rfl v hv).1 haU
      obtain ⟨P', hP't, hP'e, hP's, -⟩ := P.exists_orient_tgt hPend
      obtain ⟨R, -, hRt, hRe, hRs⟩ := GPath.exists_join P' R0 hP't rfl (by
        intro v hv hv'
        rw [hR0supp] at hv'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
        rcases hv' with h | h
        · exact h
        · rw [h] at hv; exact absurd (hPsupp b ((hP's b).mp hv)) hbU₁)
      refine ⟨R, hRt, ?_, fun v hv => ?_⟩
      · rw [hRe]; exact hP'e.append_right _
      · rcases hRs v hv with h | h
        · exact Or.inl (hPsupp v ((hP's v).mp h))
        · rw [hR0supp] at h
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl
          · exact Or.inl haU
          · exact Or.inr rfl
  obtain ⟨J, hJe⟩ : ∃ J : GPath H,
      J.edges.Perm (oa.elim [] GPath.edges ++ [s(a, b)] ++ ob.elim [] GPath.edges) := by
    cases ob with
    | none => exact ⟨J₁, by simpa using hJ₁e⟩
    | some Q =>
      have hQM : (Q, some b) ∈ M.paths := hmem₁ _ (hob Q rfl)
      have hQend := (M.site_ok _ hQM b rfl).2
      have hQsupp : ∀ v ∈ Q.walk.support, v ∈ U₂ := fun v hv =>
        (hsupp _ hQM b rfl v hv).2 hbU
      obtain ⟨Q', hQ's, hQ'e, hQ'sup, -⟩ := Q.exists_orient_src hQend
      obtain ⟨R, -, -, hRe, -⟩ := GPath.exists_join J₁ Q' hJ₁t hQ's (by
        intro v hv hv'
        have hv2 := hQsupp v ((hQ'sup v).mp hv')
        rcases hJ₁s v hv with h | h
        · exact absurd hv2 (Finset.disjoint_left.mp hd.disj h)
        · exact h)
      exact ⟨R, by rw [hRe]; exact hJ₁e.append hQ'e⟩
  -- the replacement
  have hB : (mEdges [(J, (none : Option W))]).Perm
      (mEdges (optSite oa a ++ optSite ob b) ++ [s(a, b)]) := by
    have h1 : mEdges [(J, (none : Option W))] = J.edges := by simp [mEdges]
    rw [h1, mEdges_append, mEdges_optSite, mEdges_optSite]
    refine hJe.trans ?_
    rw [List.append_assoc, List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm
  have hok : SiteOK S [(J, (none : Option W))] := by
    intro y hy s hs
    rw [List.mem_singleton] at hy
    subst hy
    simp at hs
  have hs : (mSites [(J, (none : Option W))] ++ mSites rest₂).Nodup :=
    M.sites_nodup_of_subperm hM (by simp)
  refine ⟨M.replace _ [(J, none)] rest₂ hM [s(a, b)] hB (List.nodup_singleton _)
    (by simpa using he) hok hs, ?_, ?_, ?_, ?_, ?_⟩
  · show mCost ([(J, none)] ++ rest₂) ≤ mCost M.paths + 1
    rw [mCost_perm hM]
    simp only [mCost_append, mCost_optSite]
    simp; omega
  · show (mSites ([(J, none)] ++ rest₂)).Subperm (mSites M.paths)
    refine List.Subperm.trans ?_ (mSites_perm hM).symm.subperm
    simp only [mSites_append, mSites_cons, mSites_nil, Option.toList_none, List.nil_append,
      List.append_nil]
    exact (List.sublist_append_right _ _).subperm
  · show a ∉ mSites ([(J, none)] ++ rest₂)
    simp only [mSites_append, mSites_cons, mSites_nil, Option.toList_none, List.nil_append,
      List.append_nil]
    intro h
    apply hna
    have := (mSites_perm hp₂).mem_iff (a := a)
    rw [mSites_append] at this
    exact this.mpr (List.mem_append_right _ h)
  · show b ∉ mSites ([(J, none)] ++ rest₂)
    simpa using hnb
  · intro y hy s hys v hv
    rcases List.mem_append.mp hy with h | h
    · rw [List.mem_singleton] at h; subst h; simp at hys
    · exact hsupp y (hmem₁ y (hp₂.symm.subset (List.mem_append_right _ h))) s hys v hv

/-- Edges of `H` inside `U₁` or `U₂`, or crossing. -/
theorem CrossData.edgeSet_eq {U₁ U₂ A₁ : Finset W} {φ : W → W} (hd : CrossData H U₁ U₂ A₁ φ) :
    H.edgeSet = (restrict H U₁).edgeSet ∪ (restrict H U₂).edgeSet ∪ crossSet φ A₁ := by
  ext e
  induction e using Sym2.inductionOn with
  | hf x y =>
  simp only [Set.mem_union, mem_edgeSet, restrict_adj, crossSet, Set.mem_ofPred_eq]
  constructor
  · intro hxy
    obtain ⟨hx, hy⟩ := hd.edges x y hxy
    rw [Finset.mem_union] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (Or.inl ⟨hxy, hx, hy⟩)
    · obtain ⟨hxA, rfl⟩ := hd.cross x hx y hy hxy
      exact Or.inr ⟨x, hxA, rfl⟩
    · obtain ⟨hyA, rfl⟩ := hd.cross y hy x hx hxy.symm
      exact Or.inr ⟨y, hyA, Sym2.eq_swap⟩
    · exact Or.inl (Or.inr ⟨hxy, hx, hy⟩)
  · rintro ((⟨h, -, -⟩ | ⟨h, -, -⟩) | ⟨a, ha, he⟩)
    · exact h
    · exact h
    · have h : s(x, y) ∈ H.edgeSet := he ▸ hd.adj a ha
      exact h

theorem CrossData.cross_not_mem {U₁ U₂ A₁ : Finset W} {φ : W → W} (hd : CrossData H U₁ U₂ A₁ φ)
    {T : Finset W} (hT : T ⊆ A₁) {a : W} (ha : a ∈ A₁) (haT : a ∉ T) :
    s(a, φ a) ∉ (restrict H U₁).edgeSet ∪ (restrict H U₂).edgeSet ∪ crossSet φ T := by
  have haU := hd.sub ha
  have hbU := hd.maps a ha
  simp only [Set.mem_union, mem_edgeSet, restrict_adj, crossSet, Set.mem_ofPred_eq, not_or]
  refine ⟨⟨fun h => Finset.disjoint_left.mp hd.disj h.2.2 hbU,
    fun h => Finset.disjoint_left.mp hd.disj haU h.2.1⟩, ?_⟩
  rintro ⟨a', ha', he⟩
  rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact haT (h1 ▸ ha')
  · exact Finset.disjoint_left.mp hd.disj haU (h1 ▸ hd.maps a' (hT ha'))

/-- **Lemma 6 for a matching cut.** -/
theorem lemma6 {U₁ U₂ A₁ : Finset W} {φ : W → W} (hd : CrossData H U₁ U₂ A₁ φ)
    (M₁ : PMP H (restrict H U₁).edgeSet A₁) (M₂ : PMP H (restrict H U₂).edgeSet (A₁.image φ)) :
    ∃ D : PathDecomp H, D.size ≤ M₁.cost + M₂.cost + A₁.card := by
  classical
  set S₀ := A₁ ∪ A₁.image φ with hS₀
  set E₀ := (restrict H U₁).edgeSet ∪ (restrict H U₂).edgeSet with hE₀
  have hsU₁ : ∀ e ∈ (restrict H U₁).edgeSet, ∀ v ∈ e, v ∈ (U₁ : Set W) := by
    intro e he v hv
    induction e using Sym2.inductionOn with
    | hf x y =>
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact he.2.1
    · exact he.2.2
  have hsU₂ : ∀ e ∈ (restrict H U₂).edgeSet, ∀ v ∈ e, v ∈ (U₂ : Set W) := by
    intro e he v hv
    induction e using Sym2.inductionOn with
    | hf x y =>
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact he.2.1
    · exact he.2.2
  have key : ∀ T : Finset W, T ⊆ A₁ → ∃ M : PMP H (E₀ ∪ crossSet φ T) S₀,
      M.cost ≤ M₁.cost + M₂.cost + T.card ∧
      (∀ a ∈ T, a ∉ mSites M.paths ∧ φ a ∉ mSites M.paths) ∧ SuppInv U₁ U₂ M.paths := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      have hE : ∀ e ∈ (restrict H U₁).edgeSet, e ∉ (restrict H U₂).edgeSet := by
        intro e h1 h2
        induction e using Sym2.inductionOn with
        | hf x y => exact Finset.disjoint_left.mp hd.disj h1.2.1 h2.2.1
      have hs : ∀ s ∈ mSites M₁.paths, s ∉ mSites M₂.paths := by
        intro s h1 h2
        have h1' := hd.sub (M₁.sites_mem h1)
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (M₂.sites_mem h2)
        exact Finset.disjoint_left.mp hd.disj h1' (hd.maps a ha)
      let M₀ := (M₁.mono (Finset.subset_union_left (s₂ := A₁.image φ))).append
        (M₂.mono (Finset.subset_union_right (s₁ := A₁))) hE hs
      refine ⟨M₀.castE (by rw [hE₀]; ext e; simp [crossSet]), ?_, by simp, ?_⟩
      · show mCost (M₁.paths ++ M₂.paths) ≤ _
        rw [mCost_append]; simp
      · intro y hy s hys v hv
        rcases List.mem_append.mp hy with h | h
        · have hv1 : v ∈ (U₁ : Set W) := M₁.support_subset hsU₁ h v hv
          have hsend := (M₁.site_ok y h s hys).1
          refine ⟨fun _ => hv1, fun hs2 => absurd hs2 ?_⟩
          exact Finset.disjoint_left.mp hd.disj (hd.sub hsend)
        · have hv2 : v ∈ (U₂ : Set W) := M₂.support_subset hsU₂ h v hv
          have hsend := (M₂.site_ok y h s hys).1
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hsend
          refine ⟨fun hs1 => absurd (hd.maps a ha) ?_, fun _ => hv2⟩
          exact Finset.disjoint_left.mp hd.disj hs1
    | @insert a T haT ih =>
      intro hT
      have hTA : T ⊆ A₁ := (Finset.subset_insert a T).trans hT
      have haA : a ∈ A₁ := hT (Finset.mem_insert_self a T)
      obtain ⟨M, hMc, hMs, hMsupp⟩ := ih hTA
      obtain ⟨M', h1, h2, h3, h4, h5⟩ := cross_step hd M haA (hd.cross_not_mem hTA haA haT) hMsupp
      refine ⟨M'.castE ?_, ?_, ?_, h5⟩
      · ext e
        simp only [Set.mem_union, crossSet, Set.mem_ofPred_eq, List.mem_singleton,
          Finset.mem_insert]
        constructor
        · rintro ((h | ⟨a', ha', rfl⟩) | rfl)
          · exact Or.inl h
          · exact Or.inr ⟨a', Or.inr ha', rfl⟩
          · exact Or.inr ⟨a, Or.inl rfl, rfl⟩
        · rintro (h | ⟨a', rfl | ha', rfl⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inr rfl
          · exact Or.inl (Or.inr ⟨a', ha', rfl⟩)
      · show M'.cost ≤ _
        rw [Finset.card_insert_of_notMem haT]; omega
      · intro a' ha'
        rcases Finset.mem_insert.mp ha' with rfl | ha'
        · exact ⟨h3, h4⟩
        · exact ⟨fun h => (hMs a' ha').1 (h2.subset h), fun h => (hMs a' ha').2 (h2.subset h)⟩
  obtain ⟨M, hMc, hMs, -⟩ := key A₁ (subset_refl _)
  have hnil : mSites M.paths = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro s hs
    rcases Finset.mem_union.mp (M.sites_mem hs) with h | h
    · exact (hMs s h).1 hs
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
      exact (hMs a ha).2 hs
  let M' := M.castE hd.edgeSet_eq.symm
  refine ⟨M'.toMarked.decomp, ?_⟩
  have hlen := length_eq_mCost_add M.paths
  rw [hnil] at hlen
  show (M.paths.map Prod.fst).length ≤ _
  rw [List.length_map]
  simp only [List.length_nil, add_zero] at hlen
  have hc : M.cost = mCost M.paths := rfl
  omega

end Gallai
