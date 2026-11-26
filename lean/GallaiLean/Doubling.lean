import GallaiLean.Project

/-!
# Gallai's conjecture is equivalent to the rooted private-leaf test

* `addLeaf G r`: `G` on `Option W` with a new leaf `none` adjacent exactly to `some r`.
* `pathNumber_le_addLeaf`: `p(G) ≤ p(G + leaf at r)` (trimming a pendant edge).
* `dbl H r`: two disjoint copies of `H` (on `W ⊕ W`) joined by the bridge `inl r — inr r`.
* `two_mul_pathNumber_addLeaf_le`: `2 p(H + leaf at r) ≤ p(dbl H r) + 1`
  (cut the unique path through the bridge).
* `RootedTest`, `gallai_iff_rootedTest`: Gallai's conjecture holds iff every connected graph
  of even order `n` with a private leaf at any vertex has path number `≤ n / 2`.
-/

open SimpleGraph

namespace Gallai

universe u

variable {W : Type u}

/-! ### Adding a leaf -/

/-- `G` with a new leaf `none` attached to `some r`. -/
def addLeaf (G : SimpleGraph W) (r : W) : SimpleGraph (Option W) where
  Adj x y := match x, y with
    | some a, some b => G.Adj a b
    | none, some b => b = r
    | some a, none => a = r
    | none, none => False
  symm := ⟨fun x y h => by
    cases x <;> cases y <;> simp only at h ⊢
    · exact h
    · exact h
    · exact h.symm⟩
  loopless := ⟨fun x h => by
    cases x <;> simp only at h
    exact G.loopless.irrefl _ h⟩

section addLeaf

variable {G : SimpleGraph W} {r : W}

@[simp] theorem addLeaf_adj_some_some {a b : W} : (addLeaf G r).Adj (some a) (some b) ↔ G.Adj a b :=
  Iff.rfl
@[simp] theorem addLeaf_adj_none_some {b : W} : (addLeaf G r).Adj none (some b) ↔ b = r := Iff.rfl
@[simp] theorem addLeaf_adj_some_none {a : W} : (addLeaf G r).Adj (some a) none ↔ a = r := Iff.rfl
@[simp] theorem addLeaf_not_adj_none_none : ¬ (addLeaf G r).Adj none none := id

/-- The only edge at the leaf. -/
theorem addLeaf_eq_of_none_mem {e : Sym2 (Option W)} (he : e ∈ (addLeaf G r).edgeSet)
    (hn : none ∈ e) : e = s(none, some r) := by
  induction e using Sym2.inductionOn with
  | hf x y =>
  rw [mem_edgeSet] at he
  rcases Sym2.mem_iff.mp hn with rfl | rfl
  · cases y with
    | none => exact absurd he addLeaf_not_adj_none_none
    | some b => rw [addLeaf_adj_none_some] at he; rw [he]
  · cases x with
    | none => exact absurd he addLeaf_not_adj_none_none
    | some a => rw [addLeaf_adj_some_none] at he; rw [he, Sym2.eq_swap]

/-- The trimming vertex map `Option W → W`. -/
def unSome (r : W) (x : Option W) : W := x.getD r

/-- Edges of `addLeaf G r` that are edges of `G`. -/
def bothSome : Sym2 (Option W) → Bool :=
  Sym2.lift ⟨fun x y => x.isSome && y.isSome, fun _ _ => Bool.and_comm _ _⟩

@[simp] theorem bothSome_mk (x y : Option W) : bothSome s(x, y) = (x.isSome && y.isSome) := rfl

theorem trim_injOn : Set.InjOn (unSome r) {x : Option W | x.isSome} := by
  rintro (_ | a) ha (_ | b) hb h
  · rfl
  · simp at ha
  · simp at hb
  · simp only [unSome, Option.getD_some] at h
    rw [h]

theorem trim_hT : ∀ e ∈ (addLeaf G r).edgeSet, bothSome e = true →
    ∀ x ∈ e, x ∈ {x : Option W | x.isSome} := by
  intro e _ hS x hx
  induction e using Sym2.inductionOn with
  | hf a b =>
  simp only [bothSome_mk, Bool.and_eq_true] at hS
  rcases Sym2.mem_iff.mp hx with rfl | rfl
  · exact hS.1
  · exact hS.2

theorem trim_hcov : ∀ e', e' ∈ G.edgeSet ↔
    ∃ e ∈ (addLeaf G r).edgeSet, bothSome e = true ∧ e.map (unSome r) = e' := by
  intro e'
  induction e' using Sym2.inductionOn with
  | hf a b =>
  constructor
  · intro h
    exact ⟨s(some a, some b), by simpa using h, by simp, rfl⟩
  · rintro ⟨e, he, hS, hmap⟩
    induction e using Sym2.inductionOn with
    | hf x y =>
    cases x with
    | none => simp at hS
    | some x =>
    cases y with
    | none => simp at hS
    | some y =>
    simp only [Sym2.map_mk, unSome, Option.getD_some] at hmap
    rw [← hmap]
    simpa using he

/-- A path of `addLeaf G r` avoiding the leaf gives a path of `G`. -/
theorem trim_piece_of_avoid {P : GPath (addLeaf G r)} {a b : Option W}
    (p : (addLeaf G r).Walk a b) (hp : p.IsPath) (hn : none ∉ p.support)
    (hperm : p.edges.Perm (P.edges.filter bothSome)) :
    HasPiece G (unSome r) bothSome P := by
  have hsome : ∀ x ∈ p.support, x.isSome := by
    intro x hx
    cases x with
    | none => exact absurd hx hn
    | some _ => rfl
  refine hasPiece_of_walk p hp ?_ ?_ hperm
  · intro e he
    have heG := p.edges_subset_edgeSet he
    refine (trim_hcov _).2 ⟨e, heG, ?_, rfl⟩
    induction e using Sym2.inductionOn with
    | hf x y =>
    simp only [bothSome_mk, Bool.and_eq_true]
    exact ⟨hsome x (p.fst_mem_support_of_mem_edges he), hsome y (p.snd_mem_support_of_mem_edges he)⟩
  · intro x hx y hy h
    exact trim_injOn (hsome x hx) (hsome y hy) h

theorem filter_bothSome_of_avoid {a b : Option W} (p : (addLeaf G r).Walk a b)
    (hn : none ∉ p.support) : p.edges.filter bothSome = p.edges := by
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

/-- A path through the leaf has the leaf as an end. -/
theorem addLeaf_none_end (P : GPath (addLeaf G r)) (hn : none ∈ P.walk.support) :
    P.src = none ∨ P.tgt = none := by
  classical
  by_contra hc
  rw [not_or] at hc
  have h2 := P.incid_of_internal hn hc.1 hc.2
  have hnd : P.edges.Nodup := P.isPath.isTrail.edges_nodup
  have h1 : P.incid none ≤ 1 := by
    unfold GPath.incid
    calc P.edges.countP (fun e => decide (none ∈ e))
        ≤ P.edges.countP (fun e => e == s(none, some r)) := by
          apply List.countP_mono_left
          intro e he hne
          simp only [decide_eq_true_eq] at hne
          simp [addLeaf_eq_of_none_mem (P.walk.edges_subset_edgeSet he) hne]
      _ = P.edges.count s(none, some r) := rfl
      _ ≤ 1 := List.nodup_iff_count_le_one.mp hnd _
  omega

/-- Every path of `addLeaf G r` has a piece in `G` (trimming the leaf edge). -/
theorem trim_hasPiece (P : GPath (addLeaf G r)) : HasPiece G (unSome r) bothSome P := by
  by_cases hn : none ∈ P.walk.support
  · -- the case where the path starts at the leaf
    have key : ∀ Q : GPath (addLeaf G r), Q.src = none → HasPiece G (unSome r) bothSome Q := by
      rintro ⟨s, t, w, hw, hpos⟩ (rfl : s = none)
      obtain ⟨c, h, q, rfl⟩ := Walk.exists_eq_cons_of_length_pos w hpos
      rw [Walk.cons_isPath_iff] at hw
      cases c with
      | none => exact absurd h addLeaf_not_adj_none_none
      | some c =>
      refine trim_piece_of_avoid q hw.1 hw.2 ?_
      show q.edges.Perm ((s(none, some c) :: q.edges).filter bothSome)
      rw [List.filter_cons, filter_bothSome_of_avoid q hw.2]
      simp
    rcases addLeaf_none_end P hn with h | h
    · exact key P h
    · exact HasPiece.of_reverse (key P.reverse h)
  · refine trim_piece_of_avoid P.walk P.isPath hn ?_
    rw [GPath.edges, filter_bothSome_of_avoid P.walk hn]

/-- **Trimming**: deleting the leaf edge from a decomposition of `addLeaf G r`. -/
theorem PathDecomp.trim (D : PathDecomp (addLeaf G r)) : ∃ D' : PathDecomp G, D'.size ≤ D.size := by
  obtain ⟨D', h⟩ := D.project (unSome r) bothSome _ trim_injOn trim_hT trim_hcov trim_hasPiece
  exact ⟨D', h.trans List.countP_le_length⟩

theorem pathNumber_le_addLeaf [Finite W] (G : SimpleGraph W) (r : W) :
    pathNumber G ≤ pathNumber (addLeaf G r) := by
  obtain ⟨D, hD⟩ := pathNumber_spec (addLeaf G r)
  obtain ⟨D', h⟩ := D.trim
  exact (pathNumber_le D').trans (hD ▸ h)

/-- The inclusion `G → addLeaf G r`. -/
def someHom (G : SimpleGraph W) (r : W) : G →g addLeaf G r where
  toFun := some
  map_rel' h := h

theorem addLeaf_connected {G : SimpleGraph W} (hG : G.Connected) (r : W) :
    (addLeaf G r).Connected := by
  have hreach : ∀ x, (addLeaf G r).Reachable (some r) x := by
    intro x
    cases x with
    | none => exact (show (addLeaf G r).Adj (some r) none from rfl).reachable
    | some a => exact (hG.preconnected r a).map (someHom G r)
  exact { preconnected := fun x y => (hreach x).symm.trans (hreach y), nonempty := ⟨some r⟩ }

end addLeaf

/-! ### The doubled graph -/

/-- Two disjoint copies of `H` on `W ⊕ W`, joined by the bridge `inl r — inr r`. -/
def dbl (H : SimpleGraph W) (r : W) : SimpleGraph (W ⊕ W) where
  Adj x y := match x, y with
    | .inl a, .inl b => H.Adj a b
    | .inr a, .inr b => H.Adj a b
    | .inl a, .inr b => a = r ∧ b = r
    | .inr a, .inl b => a = r ∧ b = r
  symm := ⟨fun x y h => by
    cases x <;> cases y <;> simp only at h ⊢
    · exact h.symm
    · exact ⟨h.2, h.1⟩
    · exact ⟨h.2, h.1⟩
    · exact h.symm⟩
  loopless := ⟨fun x h => by
    cases x <;> simp only at h
    · exact H.loopless.irrefl _ h
    · exact H.loopless.irrefl _ h⟩

section dbl

variable {H : SimpleGraph W} {r : W}

@[simp] theorem dbl_adj_inl_inl {a b : W} : (dbl H r).Adj (.inl a) (.inl b) ↔ H.Adj a b := Iff.rfl
@[simp] theorem dbl_adj_inr_inr {a b : W} : (dbl H r).Adj (.inr a) (.inr b) ↔ H.Adj a b := Iff.rfl
@[simp] theorem dbl_adj_inl_inr {a b : W} : (dbl H r).Adj (.inl a) (.inr b) ↔ a = r ∧ b = r :=
  Iff.rfl
@[simp] theorem dbl_adj_inr_inl {a b : W} : (dbl H r).Adj (.inr a) (.inl b) ↔ a = r ∧ b = r :=
  Iff.rfl

/-- The bridge edge. -/
abbrev bridge (r : W) : Sym2 (W ⊕ W) := s(.inl r, .inr r)

theorem dbl_side_of_adj {x y : W ⊕ W} (h : (dbl H r).Adj x y) (hb : s(x, y) ≠ bridge r) :
    x.isLeft = y.isLeft := by
  rcases x with a | a <;> rcases y with b | b
  · rfl
  · obtain ⟨rfl, rfl⟩ := h; exact absurd rfl hb
  · obtain ⟨rfl, rfl⟩ := h; exact absurd Sym2.eq_swap hb
  · rfl

/-- A walk of the doubled graph not using the bridge stays on one side. -/
theorem dbl_walk_side {x y : W ⊕ W} (p : (dbl H r).Walk x y) (hb : bridge r ∉ p.edges) :
    ∀ v ∈ p.support, v.isLeft = x.isLeft := by
  induction p with
  | nil => intro v hv; rw [Walk.mem_support_nil_iff] at hv; rw [hv]
  | @cons a c b h p ih =>
    rw [Walk.edges_cons, List.mem_cons, not_or] at hb
    have hside := dbl_side_of_adj h (Ne.symm hb.1)
    intro v hv
    rw [Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · rfl
    · rw [ih hb.2 v hv, hside]

/-- The left view: `inl a ↦ some a`, the right copy collapses to the leaf. -/
def psiL : W ⊕ W → Option W := Sum.elim some (fun _ => none)

/-- The right view: `inr a ↦ some a`, the left copy collapses to the leaf. -/
def psiR : W ⊕ W → Option W := Sum.elim (fun _ => none) some

/-- Edges with a left end (the left copy and the bridge). -/
def SL : Sym2 (W ⊕ W) → Bool :=
  Sym2.lift ⟨fun x y => x.isLeft || y.isLeft, fun _ _ => Bool.or_comm _ _⟩

/-- Edges with a right end (the right copy and the bridge). -/
def SR : Sym2 (W ⊕ W) → Bool :=
  Sym2.lift ⟨fun x y => x.isRight || y.isRight, fun _ _ => Bool.or_comm _ _⟩

@[simp] theorem SL_mk (x y : W ⊕ W) : SL s(x, y) = (x.isLeft || y.isLeft) := rfl
@[simp] theorem SR_mk (x y : W ⊕ W) : SR s(x, y) = (x.isRight || y.isRight) := rfl

/-- Vertices seen injectively by the left view. -/
def TL (r : W) : Set (W ⊕ W) := {x | x.isLeft ∨ x = .inr r}

/-- Vertices seen injectively by the right view. -/
def TR (r : W) : Set (W ⊕ W) := {x | x.isRight ∨ x = .inl r}

theorem psiL_injOn : Set.InjOn psiL (TL r) := by
  rintro (a | a) ha (b | b) hb h
  · simpa [psiL] using h
  · simp [psiL] at h
  · simp [psiL] at h
  · simp only [TL, Set.mem_ofPred_eq, Sum.isLeft_inr, Bool.false_eq_true, false_or,
      Sum.inr.injEq] at ha hb
    rw [ha, hb]

theorem psiR_injOn : Set.InjOn psiR (TR r) := by
  rintro (a | a) ha (b | b) hb h
  · simp only [TR, Set.mem_ofPred_eq, Sum.isRight_inl, Bool.false_eq_true, false_or,
      Sum.inl.injEq] at ha hb
    rw [ha, hb]
  · simp [psiR] at h
  · simp [psiR] at h
  · simpa [psiR] using h

theorem dbl_hTL : ∀ e ∈ (dbl H r).edgeSet, SL e = true → ∀ x ∈ e, x ∈ TL r := by
  intro e he hS x hx
  induction e using Sym2.inductionOn with
  | hf a b =>
  rw [mem_edgeSet] at he
  rcases Sym2.mem_iff.mp hx with rfl | rfl
  · rcases x with x | x <;> rcases b with b | b <;> simp_all [TL]
  · rcases a with a | a <;> rcases x with x | x <;> simp_all [TL]

theorem dbl_hTR : ∀ e ∈ (dbl H r).edgeSet, SR e = true → ∀ x ∈ e, x ∈ TR r := by
  intro e he hS x hx
  induction e using Sym2.inductionOn with
  | hf a b =>
  rw [mem_edgeSet] at he
  rcases Sym2.mem_iff.mp hx with rfl | rfl
  · rcases x with x | x <;> rcases b with b | b <;> simp_all [TR]
  · rcases a with a | a <;> rcases x with x | x <;> simp_all [TR]

theorem dbl_map_psiL_mem {e : Sym2 (W ⊕ W)} (he : e ∈ (dbl H r).edgeSet)
    (hT : ∀ x ∈ e, x ∈ TL r) : e.map psiL ∈ (addLeaf H r).edgeSet := by
  induction e using Sym2.inductionOn with
  | hf a b =>
  have ha := hT a (Sym2.mem_mk_left a b)
  have hb := hT b (Sym2.mem_mk_right a b)
  rw [mem_edgeSet] at he
  rcases a with a | a <;> rcases b with b | b <;> simp_all [TL, psiL]

theorem dbl_map_psiR_mem {e : Sym2 (W ⊕ W)} (he : e ∈ (dbl H r).edgeSet)
    (hT : ∀ x ∈ e, x ∈ TR r) : e.map psiR ∈ (addLeaf H r).edgeSet := by
  induction e using Sym2.inductionOn with
  | hf a b =>
  have ha := hT a (Sym2.mem_mk_left a b)
  have hb := hT b (Sym2.mem_mk_right a b)
  rw [mem_edgeSet] at he
  rcases a with a | a <;> rcases b with b | b <;> simp_all [TR, psiR]

theorem dbl_hcovL : ∀ e', e' ∈ (addLeaf H r).edgeSet ↔
    ∃ e ∈ (dbl H r).edgeSet, SL e = true ∧ e.map psiL = e' := by
  intro e'
  constructor
  · intro he'
    induction e' using Sym2.inductionOn with
    | hf x y =>
    rw [mem_edgeSet] at he'
    rcases x with _ | a <;> rcases y with _ | b
    · exact absurd he' addLeaf_not_adj_none_none
    · rw [addLeaf_adj_none_some] at he'
      subst he'
      exact ⟨s(.inr b, .inl b), by simp, by simp, by simp [psiL]⟩
    · rw [addLeaf_adj_some_none] at he'
      subst he'
      exact ⟨s(.inl a, .inr a), by simp, by simp, by simp [psiL]⟩
    · exact ⟨s(.inl a, .inl b), by simpa using he', by simp, by simp [psiL]⟩
  · rintro ⟨e, he, hS, rfl⟩
    exact dbl_map_psiL_mem he (dbl_hTL e he hS)

theorem dbl_hcovR : ∀ e', e' ∈ (addLeaf H r).edgeSet ↔
    ∃ e ∈ (dbl H r).edgeSet, SR e = true ∧ e.map psiR = e' := by
  intro e'
  constructor
  · intro he'
    induction e' using Sym2.inductionOn with
    | hf x y =>
    rw [mem_edgeSet] at he'
    rcases x with _ | a <;> rcases y with _ | b
    · exact absurd he' addLeaf_not_adj_none_none
    · rw [addLeaf_adj_none_some] at he'
      subst he'
      exact ⟨s(.inl b, .inr b), by simp, by simp, by simp [psiR]⟩
    · rw [addLeaf_adj_some_none] at he'
      subst he'
      exact ⟨s(.inr a, .inl a), by simp, by simp, by simp [psiR]⟩
    · exact ⟨s(.inr a, .inr b), by simpa using he', by simp, by simp [psiR]⟩
  · rintro ⟨e, he, hS, rfl⟩
    exact dbl_map_psiR_mem he (dbl_hTR e he hS)

theorem filter_SL_of_left {x y : W ⊕ W} (p : (dbl H r).Walk x y)
    (h : ∀ v ∈ p.support, v.isLeft = true) : p.edges.filter SL = p.edges := by
  rw [List.filter_eq_self]
  intro e he
  induction e using Sym2.inductionOn with
  | hf a b =>
  simp [h a (p.fst_mem_support_of_mem_edges he)]

theorem filter_SL_of_right {x y : W ⊕ W} (p : (dbl H r).Walk x y)
    (h : ∀ v ∈ p.support, v.isLeft = false) : p.edges.filter SL = [] := by
  rw [List.filter_eq_nil_iff]
  intro e he
  induction e using Sym2.inductionOn with
  | hf a b =>
  simp [h a (p.fst_mem_support_of_mem_edges he), h b (p.snd_mem_support_of_mem_edges he)]

/-- A path of the doubled graph inside `TL` pushes to the left view. -/
theorem dbl_left_piece_of_walk {P : GPath (dbl H r)} {x y : W ⊕ W} (p : (dbl H r).Walk x y)
    (hp : p.IsPath) (hT : ∀ v ∈ p.support, v ∈ TL r)
    (hperm : p.edges.Perm (P.edges.filter SL)) : HasPiece (addLeaf H r) psiL SL P := by
  refine hasPiece_of_walk p hp ?_ ?_ hperm
  · intro e he
    exact dbl_map_psiL_mem (p.edges_subset_edgeSet he)
      (fun v hv => hT v (Walk.mem_support_of_mem_edge p he hv))
  · intro a ha b hb h
    exact psiL_injOn (hT a ha) (hT b hb) h

/-- The left piece when the bridge is crossed from right to left. -/
theorem dbl_left_piece_rl (P : GPath (dbl H r)) (q₁ : (dbl H r).Walk P.src (.inr r))
    (h : (dbl H r).Adj (.inr r) (.inl r)) (q₂ : (dbl H r).Walk (.inl r) P.tgt)
    (hP : P.walk = q₁.append (Walk.cons h q₂)) : HasPiece (addLeaf H r) psiL SL P := by
  have hpath : (q₁.append (Walk.cons h q₂)).IsPath := hP ▸ P.isPath
  have hedges : P.edges = q₁.edges ++ s(.inr r, .inl r) :: q₂.edges := by
    rw [GPath.edges, hP, Walk.edges_append, Walk.edges_cons]
  have hnd : (q₁.edges ++ s(.inr r, .inl r) :: q₂.edges).Nodup := by
    rw [← hedges]; exact P.isPath.isTrail.edges_nodup
  have hb : bridge r = s(.inr r, .inl r) := Sym2.eq_swap
  have hb₁ : bridge r ∉ q₁.edges := by
    rw [hb]; intro hm
    exact (List.nodup_append.mp hnd).2.2 _ hm _ List.mem_cons_self rfl
  have hb₂ : bridge r ∉ q₂.edges := by
    rw [hb]; intro hm
    exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 hm
  have hs₁ := dbl_walk_side q₁ hb₁
  have hsrc : P.src.isLeft = false := by
    rw [← hs₁ _ q₁.end_mem_support]; rfl
  have hs₂ := dbl_walk_side q₂ hb₂
  have hR : ∀ v ∈ q₁.support, v.isLeft = false := fun v hv => (hs₁ v hv).trans hsrc
  have hL : ∀ v ∈ q₂.support, v.isLeft = true := fun v hv => hs₂ v hv
  refine dbl_left_piece_of_walk (Walk.cons h q₂) (Walk.isPath_of_append_right hpath) ?_ ?_
  · intro v hv
    rw [Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact Or.inr rfl
    · exact Or.inl (hL v hv)
  · rw [hedges, List.filter_append, List.filter_cons, filter_SL_of_right q₁ hR,
      filter_SL_of_left q₂ hL, Walk.edges_cons]
    simp

/-- Every path of the doubled graph has a left piece. -/
theorem dbl_left_hasPiece (P : GPath (dbl H r)) : HasPiece (addLeaf H r) psiL SL P := by
  by_cases hb : bridge r ∈ P.walk.edges
  · obtain ⟨c, d, hcd, q₁, q₂, he, hP⟩ := Walk.exists_append_cons_of_mem_edges P.walk hb
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- crossing left to right: reverse
      have e₁ : P.walk.reverse = q₂.reverse.append (Walk.cons hcd.symm q₁.reverse) := by
        rw [hP, Walk.reverse_append, Walk.reverse_cons, ← Walk.append_assoc]
        rfl
      exact HasPiece.of_reverse (dbl_left_piece_rl P.reverse q₂.reverse hcd.symm q₁.reverse e₁)
    · exact dbl_left_piece_rl P q₁ hcd q₂ hP
  · have hs := dbl_walk_side P.walk hb
    cases hsrc : P.src.isLeft
    · exact hasPiece_none (filter_SL_of_right P.walk (fun v hv => (hs v hv).trans hsrc))
    · refine dbl_left_piece_of_walk P.walk P.isPath
        (fun v hv => Or.inl ((hs v hv).trans hsrc)) ?_
      rw [GPath.edges, filter_SL_of_left P.walk (fun v hv => (hs v hv).trans hsrc)]

/-- `Sum.swap` is an automorphism of the doubled graph. -/
theorem dbl_adj_swap {x y : W ⊕ W} : (dbl H r).Adj x.swap y.swap ↔ (dbl H r).Adj x y := by
  rcases x with a | a <;> rcases y with b | b <;> simp

theorem psiL_comp_swap : (psiL : W ⊕ W → Option W) ∘ Sum.swap = psiR := by
  funext x; rcases x with a | a <;> rfl

theorem SL_comp_map_swap : (SL : Sym2 (W ⊕ W) → Bool) ∘ Sym2.map Sum.swap = SR := by
  funext e
  induction e using Sym2.inductionOn with
  | hf a b => rcases a with a | a <;> rcases b with b | b <;> rfl

/-- Every path of the doubled graph has a right piece (by symmetry). -/
theorem dbl_right_hasPiece (P : GPath (dbl H r)) : HasPiece (addLeaf H r) psiR SR P := by
  let P' : GPath (dbl H r) := P.push Sum.swap
    (fun e he => by
      have heG := P.walk.edges_subset_edgeSet he
      induction e using Sym2.inductionOn with
      | hf a b => simpa [dbl_adj_swap] using heG)
    (fun x _ y _ h => Sum.swap_leftInverse.injective h)
  obtain ⟨o, ho⟩ := dbl_left_hasPiece P'
  refine ⟨o, ho.trans ?_⟩
  rw [GPath.push_edges, List.filter_map, List.map_map, SL_comp_map_swap, ← Sym2.map_comp,
    psiL_comp_swap]

/-- A path with edges on both sides uses the bridge. -/
theorem dbl_both_sides (P : GPath (dbl H r)) (hL : P.edges.any SL = true)
    (hR : P.edges.any SR = true) : bridge r ∈ P.edges := by
  by_contra hb
  have hs := dbl_walk_side P.walk hb
  obtain ⟨e₁, he₁, hS₁⟩ := List.any_eq_true.mp hL
  obtain ⟨e₂, he₂, hS₂⟩ := List.any_eq_true.mp hR
  induction e₁ using Sym2.inductionOn with
  | hf a b =>
  induction e₂ using Sym2.inductionOn with
  | hf c d =>
  have ha := hs a (P.walk.fst_mem_support_of_mem_edges he₁)
  have hb' := hs b (P.walk.snd_mem_support_of_mem_edges he₁)
  have hc := hs c (P.walk.fst_mem_support_of_mem_edges he₂)
  have hd := hs d (P.walk.snd_mem_support_of_mem_edges he₂)
  simp only [SL_mk, SR_mk, Bool.or_eq_true] at hS₁ hS₂
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> rcases d with d | d <;>
    simp_all

/-- The left and right views of a decomposition of `dbl H r`. -/
theorem PathDecomp.views (D : PathDecomp (dbl H r)) :
    ∃ D₁ D₂ : PathDecomp (addLeaf H r), D₁.size + D₂.size ≤ D.size + 1 := by
  classical
  obtain ⟨D₁, h₁⟩ := D.project psiL SL (TL r) psiL_injOn dbl_hTL dbl_hcovL dbl_left_hasPiece
  obtain ⟨D₂, h₂⟩ := D.project psiR SR (TR r) psiR_injOn dbl_hTR dbl_hcovR dbl_right_hasPiece
  have hc : D.paths.countP (fun P => P.edges.any SL) + D.paths.countP (fun P => P.edges.any SR)
      ≤ D.paths.length + D.paths.countP (fun P => decide (bridge r ∈ P.edges)) := by
    have : ∀ l : List (GPath (dbl H r)),
        l.countP (fun P => P.edges.any SL) + l.countP (fun P => P.edges.any SR)
          ≤ l.length + l.countP (fun P => decide (bridge r ∈ P.edges)) := by
      intro l
      induction l with
      | nil => simp
      | cons P l ih =>
        simp only [List.countP_cons, List.length_cons]
        by_cases hL : P.edges.any SL = true <;> by_cases hR : P.edges.any SR = true
        · have := dbl_both_sides P hL hR
          simp only [hL, hR, this, decide_true, ite_true]
          omega
        all_goals
          simp only [hL, hR, Bool.false_eq_true, ite_true, ite_false]
          split_ifs <;> omega
    exact this _
  have h1 : D.paths.countP (fun P => decide (bridge r ∈ P.edges)) ≤ 1 := by
    have : ∀ l : List (GPath (dbl H r)), l.countP (fun P => decide (bridge r ∈ P.edges)) ≤
        (l.flatMap GPath.edges).count (bridge r) := by
      intro l
      induction l with
      | nil => simp
      | cons P l ih =>
        rw [List.countP_cons, List.flatMap_cons, List.count_append]
        by_cases hb : bridge r ∈ P.edges
        · have := List.count_pos_iff.mpr hb
          simp only [hb, decide_true, ite_true]
          omega
        · simp only [hb, decide_false, Bool.false_eq_true, ite_false]
          omega
    exact (this _).trans (List.nodup_iff_count_le_one.mp D.nodup_edges _)
  exact ⟨D₁, D₂, by unfold PathDecomp.size at *; omega⟩

theorem two_mul_pathNumber_addLeaf_le [Finite W] (H : SimpleGraph W) (r : W) :
    2 * pathNumber (addLeaf H r) ≤ pathNumber (dbl H r) + 1 := by
  obtain ⟨D, hD⟩ := pathNumber_spec (dbl H r)
  obtain ⟨D₁, D₂, h⟩ := D.views
  have h₁ := pathNumber_le D₁
  have h₂ := pathNumber_le D₂
  omega

/-- The left copy. -/
def inlHom (H : SimpleGraph W) (r : W) : H →g dbl H r where
  toFun := Sum.inl
  map_rel' h := h

/-- The right copy. -/
def inrHom (H : SimpleGraph W) (r : W) : H →g dbl H r where
  toFun := Sum.inr
  map_rel' h := h

theorem dbl_connected (hH : H.Connected) : (dbl H r).Connected := by
  have hreach : ∀ x, (dbl H r).Reachable (.inl r) x := by
    intro x
    rcases x with a | a
    · exact (hH.preconnected r a).map (inlHom H r)
    · exact (show (dbl H r).Adj (.inl r) (.inr r) from ⟨rfl, rfl⟩).reachable.trans
        ((hH.preconnected r a).map (inrHom H r))
  exact { preconnected := fun x y => (hreach x).symm.trans (hreach y), nonempty := ⟨.inl r⟩ }

end dbl

/-! ### The equivalence -/

/-- The rooted private-leaf test: every connected graph of even order `n`, with a private leaf
attached at any vertex, has path number at most `n / 2`. -/
def RootedTest : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W), G.Connected →
    Even (Fintype.card W) → ∀ r, pathNumber (addLeaf G r) ≤ Fintype.card W / 2

theorem rootedTest_of_gallai (h : GallaiConjecture.{u}) : RootedTest.{u} := by
  intro W _ _ H hH hev r
  have h₁ := h (W ⊕ W) (dbl H r) (dbl_connected hH)
  rw [Fintype.card_sum] at h₁
  have h₂ := two_mul_pathNumber_addLeaf_le H r
  obtain ⟨k, hk⟩ := hev
  omega

theorem gallai_of_rootedTest (h : RootedTest.{u}) : GallaiConjecture.{u} := by
  intro W _ G hG
  classical
  obtain ⟨r⟩ := hG.nonempty
  rcases Nat.even_or_odd (Fintype.card W) with hev | hodd
  · have h₁ := h W G hG hev r
    have h₂ := pathNumber_le_addLeaf G r
    omega
  · have hev' : Even (Fintype.card (Option W)) := by
      rw [Fintype.card_option]; exact hodd.add_one
    have h₁ := h (Option W) (addLeaf G r) (addLeaf_connected hG r) hev' none
    have h₂ := pathNumber_le_addLeaf (addLeaf G r) none
    have h₃ := pathNumber_le_addLeaf G r
    rw [Fintype.card_option] at h₁
    omega

/-- **Gallai's conjecture is equivalent to the rooted private-leaf test.** -/
theorem gallai_iff_rootedTest : GallaiConjecture.{u} ↔ RootedTest.{u} :=
  ⟨rootedTest_of_gallai, gallai_of_rootedTest⟩

end Gallai
