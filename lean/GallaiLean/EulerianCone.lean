import GallaiLean.Separator
import GallaiLean.DirectTest1
import GallaiLean.Bridge

/-!
# Cones: the two-end test at the apex is rooted Gallai for Eulerian graphs

Manuscript: `manuscripts/eulerian-cone`, Section 2.

For a graph `B` on `W`, `fullCone B` (the graph `cone B univ` of `Marked.lean`) is the graph on `Option W` in which the apex `none` is joined to
every `some a`, and `some a, some b` are adjacent iff `a, b` are adjacent in `B`.

* `fullCone_degree_none`, `fullCone_degree_some`: `d(z) = |B|` and `d(a) = d_B(a) + 1`.
* `fullCone_onlyEven_iff`: the apex is the only even vertex iff `|B|` is even and every degree of `B`
  is even.
* `fullConeDelIso`: `B ≃g cone B − z`.
* **`test1At_fullCone_iff`**: `Test1At (fullCone B) z a ↔ RootedDecomp B a`, where `RootedDecomp B a`
  says that `B` has a decomposition into at most `|B|/2` paths with at least two ends at `a`.
* **`test1_fullCone_iff`**: `Test1 (fullCone B) z` iff (`|B|` even and `B` Eulerian ⇒ `RootedDecomp B a`
  for every `a`).
* `test2_fullCone_apex`: `Test2` at the apex always holds (vacuously; handshake).
  `test1_fullCone_some`: `Test1` at any other vertex always holds (vacuously).
  `test2_fullCone_some_of_even`: `Test2` at any other vertex holds (vacuously) when `|B|` is even.
* **`kConnected_three_fullCone_iff`**: `fullCone B` is 3-connected iff `B` is 2-connected.
* `hasMatchingCut_delVert_fullCone_iff`: `cone B − z` has a matching cut iff `B` has one.
* **`rootedDecomp_of_spineTestsNMC`**: the spine (in its weakest form `SpineTestsNMC`) gives
  `RootedDecomp B a` for every 2-connected Eulerian `B` of even order without a matching cut,
  and `rootedDecomp_of_gallai` gives it for every connected Eulerian `B` of even order.
* `rootedDecomp_iff_addLeaf`, `rootedDecomp_of_dbl`: `RootedDecomp B a ⇔ p(B + leaf at a) ≤ |B|/2`,
  and it follows from Gallai's bound `p ≤ |B|` for the doubled graph `dbl B a`.
-/

open SimpleGraph

namespace Gallai

universe u

variable {W : Type u}

/-! ### The cone -/

/-- The cone over `B`: the apex `none` is joined to every vertex `some a`. -/
def fullCone (B : SimpleGraph W) : SimpleGraph (Option W) where
  Adj x y := match x, y with
    | none, none => False
    | none, some _ => True
    | some _, none => True
    | some a, some b => B.Adj a b
  symm := ⟨fun x y h => by
    cases x <;> cases y <;> simp only at h ⊢
    exact h.symm⟩
  loopless := ⟨fun x h => by
    cases x <;> simp only at h
    exact B.loopless.irrefl _ h⟩

section cone

variable {B : SimpleGraph W}

@[simp] theorem fullCone_adj_none_some (a : W) : (fullCone B).Adj none (some a) := trivial
@[simp] theorem fullCone_adj_some_none (a : W) : (fullCone B).Adj (some a) none := trivial
@[simp] theorem fullCone_adj_some_some {a b : W} : (fullCone B).Adj (some a) (some b) ↔ B.Adj a b :=
  Iff.rfl
@[simp] theorem fullCone_not_adj_none_none : ¬ (fullCone B).Adj none none := id

instance fullCone.decAdj [DecidableRel B.Adj] : DecidableRel (fullCone B).Adj
  | none, none => isFalse id
  | none, some _ => isTrue trivial
  | some _, none => isTrue trivial
  | some a, some b => (inferInstance : Decidable (B.Adj a b))

/-- `some` as a graph homomorphism `B →g fullCone B`. -/
def fullConeSomeHom (B : SimpleGraph W) : B →g fullCone B where
  toFun := some
  map_rel' h := h

/-! ### Degrees and parity -/

variable [Fintype W] [DecidableEq W] [DecidableRel B.Adj]

theorem fullCone_neighborFinset_none :
    (fullCone B).neighborFinset none = (Finset.univ : Finset (Option W)).erase none := by
  ext x
  cases x <;> simp

theorem fullCone_neighborFinset_some (a : W) :
    (fullCone B).neighborFinset (some a) =
      insert none ((B.neighborFinset a).map Function.Embedding.some) := by
  ext x
  cases x <;> simp

theorem fullCone_degree_none : (fullCone B).degree none = Fintype.card W := by
  rw [← card_neighborFinset_eq_degree, fullCone_neighborFinset_none,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_option]
  rfl

theorem fullCone_degree_some (a : W) : (fullCone B).degree (some a) = B.degree a + 1 := by
  rw [← card_neighborFinset_eq_degree, fullCone_neighborFinset_some,
    Finset.card_insert_of_notMem (by simp), Finset.card_map, card_neighborFinset_eq_degree]

/-- The apex is the unique even vertex of the cone iff `|B|` is even and `B` is Eulerian. -/
theorem fullCone_onlyEven_iff : (∀ v, Even ((fullCone B).degree v) ↔ v = none) ↔
    Even (Fintype.card W) ∧ ∀ a, Even (B.degree a) := by
  constructor
  · intro h
    refine ⟨by simpa [fullCone_degree_none] using (h none).2 rfl, fun a => ?_⟩
    have h1 := h (some a)
    rw [fullCone_degree_some] at h1
    rcases Nat.even_or_odd (B.degree a) with h2 | h2
    · exact h2
    · exact absurd (h1.1 h2.add_one) (Option.some_ne_none a)
  · rintro ⟨hW, hB⟩ v
    cases v with
    | none => simpa [fullCone_degree_none] using hW
    | some a =>
      simp only [fullCone_degree_some, reduceCtorEq, iff_false]
      exact Nat.not_even_iff_odd.2 (hB a).add_one

/-! ### `fullCone B − z` is `B` -/

/-- `B` is isomorphic to `fullCone B − z`. -/
def fullConeDelIso (B : SimpleGraph W) : B ≃g delVert (fullCone B) none where
  toFun a := ⟨some a, Option.some_ne_none a⟩
  invFun v := v.1.get (Option.ne_none_iff_isSome.mp v.2)
  left_inv a := rfl
  right_inv v := by
    obtain ⟨v, hv⟩ := v
    cases v with
    | none => exact absurd rfl hv
    | some a => rfl
  map_rel_iff' := by
    intro a b
    exact Iff.rfl

/-- Transport of a path decomposition along a graph isomorphism, preserving size and ends. -/
theorem PathDecomp.exists_of_iso {V₁ V₂ : Type*} [DecidableEq V₁] [DecidableEq V₂]
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} (e : G₁ ≃g G₂) (D : PathDecomp G₁) :
    ∃ D' : PathDecomp G₂, D'.size = D.size ∧ ∀ x, D'.ends (e x) = D.ends x := by
  have hE : ∀ f ∈ G₁.edgeSet, f.map e ∈ G₂.edgeSet := by
    intro f hf
    induction f using Sym2.inductionOn with
    | hf a b => rw [Sym2.map_mk, mem_edgeSet]; exact e.map_adj_iff.2 hf
  have hcov : ∀ f' ∈ G₂.edgeSet, ∃ f ∈ G₁.edgeSet, f.map e = f' := by
    intro f' hf'
    induction f' using Sym2.inductionOn with
    | hf a b =>
      refine ⟨s(e.symm a, e.symm b), ?_, by simp⟩
      rw [mem_edgeSet]; exact e.symm.map_adj_iff.2 hf'
  exact ⟨D.mapInj e e.injective hE hcov, D.mapInj_size _ _ _ _, D.mapInj_ends _ _ _ _⟩

/-- **Rooted Gallai at `r`**: `B` has a decomposition into at most `|B|/2` paths with at least
two ends at `r`. -/
def RootedDecomp (B : SimpleGraph W) (r : W) : Prop :=
  ∃ D : PathDecomp B, D.size ≤ Fintype.card W / 2 ∧ 2 ≤ D.ends r

/-- **The two-end test at a root of a cone is rooted Gallai for the base.** -/
theorem test1At_fullCone_iff (r : W) : Test1At (fullCone B) none (some r) ↔ RootedDecomp B r := by
  have hcard : (Fintype.card (Option W) - 1) / 2 = Fintype.card W / 2 := by
    rw [Fintype.card_option, Nat.add_sub_cancel]
  constructor
  · intro h
    obtain ⟨D, hs, he⟩ := h (fullCone_adj_none_some r)
    obtain ⟨D', hs', he'⟩ := D.exists_of_iso (fullConeDelIso B).symm
    refine ⟨D', by rw [hs', ← hcard]; exact hs, ?_⟩
    have := he' ⟨some r, (fullCone_adj_none_some (B := B) r).ne'⟩
    have h3 : (fullConeDelIso B).symm ⟨some r, (fullCone_adj_none_some (B := B) r).ne'⟩ = r :=
      rfl
    rw [h3] at this
    rw [this]
    exact he
  · rintro ⟨D, hs, he⟩ hr
    obtain ⟨D', hs', he'⟩ := D.exists_of_iso (fullConeDelIso B)
    refine ⟨D', by rw [hs', hcard]; exact hs, ?_⟩
    have := he' r
    exact this ▸ he

/-- **`Test1` at the apex of a cone** is rooted Gallai for the base at every vertex, whenever
the base is Eulerian of even order (and holds vacuously otherwise). -/
theorem test1_fullCone_iff : Test1 (fullCone B) none ↔
    (Even (Fintype.card W) → (∀ a, Even (B.degree a)) → ∀ r, RootedDecomp B r) := by
  constructor
  · intro h hW hB r
    exact (test1At_fullCone_iff r).1 (fun hr => h (fullCone_onlyEven_iff.2 ⟨hW, hB⟩) (some r) hr)
  · intro h hz x hx
    cases x with
    | none => exact absurd hx fullCone_not_adj_none_none
    | some r =>
      obtain ⟨hW, hB⟩ := fullCone_onlyEven_iff.1 hz
      exact (test1At_fullCone_iff r).2 (h hW hB r) hx

/-! ### The other tests at a cone are vacuous -/

omit [DecidableEq W] in
/-- No graph has exactly one vertex of odd degree. -/
theorem not_unique_odd (G : SimpleGraph W) [DecidableRel G.Adj] (a : W)
    (h : ∀ b, Odd (G.degree b) ↔ b = a) : False := by
  have hh := G.even_card_odd_degree_vertices
  have : (Finset.univ.filter fun v => Odd (G.degree v)) = {a} := by
    ext b; simp [h b]
  rw [this, Finset.card_singleton] at hh
  exact Nat.not_even_one hh

/-- `Test2` at the apex of a cone holds vacuously: if the apex and `some a` were the only even
vertices, `a` would be the only odd vertex of `B`. -/
theorem test2_fullCone_apex : Test2 (fullCone B) none := by
  intro x hx hz
  exfalso
  cases x with
  | none => exact fullCone_not_adj_none_none hx
  | some a =>
    refine not_unique_odd B a (fun b => ?_)
    have h1 := hz (some b)
    rw [fullCone_degree_some] at h1
    simp only [reduceCtorEq, Option.some.injEq, false_or] at h1
    rw [← h1, Nat.even_add_one, Nat.not_even_iff_odd]

/-- `Test1` at a non-apex vertex of a cone holds vacuously (handshake in the cone). -/
theorem test1_fullCone_some (a : W) : Test1 (fullCone B) (some a) := by
  intro hz
  exfalso
  -- the apex is odd, so `|B|` is odd and the cone has even order; its odd vertices are all
  -- vertices but `some a`, an odd number
  have hn : ¬ Even (Fintype.card W) := by
    intro he
    have := (hz none).1 (by rw [fullCone_degree_none]; exact he)
    exact (Option.some_ne_none a) this.symm
  have hh := (fullCone B).even_card_odd_degree_vertices
  have : (Finset.univ.filter fun v => Odd ((fullCone B).degree v)) =
      (Finset.univ : Finset (Option W)).erase (some a) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    rw [← Nat.not_even_iff_odd, hz v]
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_option, Nat.add_sub_cancel] at hh
  exact hn hh

/-- `Test2` at a non-apex vertex of a cone over a graph of even order holds vacuously. -/
theorem test2_fullCone_some_of_even (a : W) (hW : Even (Fintype.card W)) :
    Test2 (fullCone B) (some a) := by
  intro x hx hz
  exfalso
  have hnone := (hz none).1 (by rw [fullCone_degree_none]; exact hW)
  rcases hnone with h | h
  · exact Option.some_ne_none a h.symm
  · subst h
    refine not_unique_odd B a (fun b => ?_)
    have h1 := hz (some b)
    rw [fullCone_degree_some] at h1
    simp only [Option.some.injEq, reduceCtorEq, or_false] at h1
    rw [← h1, Nat.even_add_one, Nat.not_even_iff_odd]

/-! ### Connectivity and matching cuts -/

omit [DecidableEq W] [DecidableRel B.Adj] in
/-- **`fullCone B` is 3-connected iff `B` is 2-connected.** -/
theorem kConnected_three_fullCone_iff : KConnected 3 (fullCone B) ↔ KConnected 2 B := by
  classical
  constructor
  · intro hJ
    refine kConnected_of_walks (by have := hJ.1; rw [Fintype.card_option] at this; omega) ?_
    intro X hX a b ha hb
    let Y : Finset (Option W) := insert none (X.map Function.Embedding.some)
    have hY : Y.card < 3 := by
      show (insert none (X.map Function.Embedding.some)).card < 3
      have := Finset.card_insert_le none (X.map Function.Embedding.some)
      rw [Finset.card_map] at this; omega
    obtain ⟨p, hp⟩ := hJ.walk hY (a := some a) (b := some b) (by simp [Y, ha]) (by simp [Y, hb])
    -- `p` avoids the apex, so it lives in `fullCone B − z`, i.e. in `B`; it also avoids `X`
    let S : Set W := (X : Set W)ᶜ
    have hS : ∀ v ∈ p.support, v ∈ (some '' S : Set (Option W)) := by
      intro v hv
      have := hp v hv
      cases v with
      | none => simp [Y] at this
      | some c => exact ⟨c, by simpa [Y, S] using this, rfl⟩
    have hreach := induce_reachable_of_walk p hS
    let φ : (fullCone B).induce (some '' S) →g B.induce S :=
      { toFun := fun v => ⟨v.1.get (by obtain ⟨c, -, hc⟩ := v.2; rw [← hc]; rfl), by
          obtain ⟨c, hc, hcv⟩ := v.2
          have : v.1.get (by rw [← hcv]; rfl) = c := by simp [← hcv]
          simpa [this] using hc⟩
        map_rel' := by
          rintro ⟨x, c, hc, rfl⟩ ⟨y, d, hd, rfl⟩ h
          simpa using h }
    have := hreach.map φ
    obtain ⟨q, hq⟩ := walk_of_induce_reachable (s := S) this
    exact ⟨q, fun v hv => by simpa [S] using hq v hv⟩
  · intro hB
    refine kConnected_of_walks (by have := hB.1; rw [Fintype.card_option]; omega) ?_
    intro X hX a b ha hb
    by_cases hz : none ∈ X
    · -- both ends are vertices of `B`; avoid `X' = {c | some c ∈ X}` inside `B`
      cases a with
      | none => exact absurd hz ha
      | some a =>
      cases b with
      | none => exact absurd hz hb
      | some b =>
      let X' : Finset W := Finset.univ.filter fun c => some c ∈ X
      have hX' : X'.card < 2 := by
        have hsub : insert none (X'.map Function.Embedding.some) ⊆ X := by
          intro v hv
          simp only [Finset.mem_insert, Finset.mem_map, Function.Embedding.some_apply] at hv
          rcases hv with rfl | ⟨c, hc, rfl⟩
          · exact hz
          · simpa [X'] using hc
        have := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem (by simp), Finset.card_map] at this
        omega
      obtain ⟨q, hq⟩ := hB.walk hX' (a := a) (b := b) (by simpa [X'] using ha)
        (by simpa [X'] using hb)
      have key : ∀ v ∈ (q.map (fullConeSomeHom B)).support, v ∉ X := by
        intro v hv
        rw [Walk.support_map, List.mem_map] at hv
        obtain ⟨c, hc, rfl⟩ := hv
        have := hq c hc
        simp only [X', Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact this
      exact ⟨q.map (fullConeSomeHom B), key⟩
    · -- go through the apex
      by_cases hab : a = b
      · subst hab; exact ⟨Walk.nil, by simpa using ha⟩
      cases a with
      | none =>
        cases b with
        | none => exact absurd rfl hab
        | some b =>
          exact ⟨Walk.cons (fullCone_adj_none_some b) Walk.nil, by
            intro v hv; simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
              List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl <;> assumption⟩
      | some a =>
        cases b with
        | none =>
          exact ⟨Walk.cons (fullCone_adj_some_none a) Walk.nil, by
            intro v hv; simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
              List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl <;> assumption⟩
        | some b =>
          exact ⟨Walk.cons (fullCone_adj_some_none a) (Walk.cons (fullCone_adj_none_some b) Walk.nil), by
            intro v hv; simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
              List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl | rfl <;> assumption⟩

omit [Fintype W] [DecidableEq W] [DecidableRel B.Adj] in
/-- A matching cut is preserved by graph isomorphisms. -/
theorem HasMatchingCut.of_iso {V₁ V₂ : Type*} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    (e : G₁ ≃g G₂) (h : HasMatchingCut G₁) : HasMatchingCut G₂ := by
  obtain ⟨X, ⟨x, hx⟩, ⟨y, hy⟩, hm⟩ := h
  refine ⟨{v | e.symm v ∈ X}, ⟨e x, by simpa using hx⟩, ⟨e y, by simpa using hy⟩, ?_⟩
  intro a b c hab hac hb hc
  have := hm (e.symm a) (e.symm b) (e.symm c) (e.symm.map_adj_iff.2 hab)
    (e.symm.map_adj_iff.2 hac) (by simpa using hb) (by simpa using hc)
  simpa using this

omit [Fintype W] [DecidableEq W] [DecidableRel B.Adj] in
theorem hasMatchingCut_delVert_fullCone_iff :
    HasMatchingCut (delVert (fullCone B) none) ↔ HasMatchingCut B :=
  ⟨HasMatchingCut.of_iso (fullConeDelIso B).symm, HasMatchingCut.of_iso (fullConeDelIso B)⟩

/-! ### Rooted Gallai, the leaf test and the doubled graph -/

/-- `RootedDecomp B r` iff `p(B + leaf at r) ≤ |B|/2`, at a root of positive even degree. -/
theorem rootedDecomp_iff_addLeaf (r : W) (hev : Even (B.degree r)) (hpos : 0 < B.degree r) :
    RootedDecomp B r ↔ pathNumber (addLeaf B r) ≤ Fintype.card W / 2 := by
  constructor
  · rintro ⟨D, hs, he⟩
    refine (pathNumber_addLeaf_le D r).trans ?_
    have h0 : D.ends r ≠ 0 := by omega
    simp only [leafCost, h0, ite_false, add_zero]
    exact hs
  · intro h
    obtain ⟨D, hD⟩ := exists_leafCost_le B r
    exact exists_two_ends D (hD.trans h) hev hpos

/-- Gallai's bound for the doubled graph at `r` gives rooted Gallai at `r`. -/
theorem rootedDecomp_of_dbl (r : W) (hW : Even (Fintype.card W)) (hev : Even (B.degree r))
    (hpos : 0 < B.degree r) (h : pathNumber (dbl B r) ≤ Fintype.card W) : RootedDecomp B r := by
  rw [rootedDecomp_iff_addLeaf r hev hpos]
  have := two_mul_pathNumber_addLeaf_le B r
  obtain ⟨k, hk⟩ := hW
  omega

end cone

/-! ### What the spine asks of cones -/

/-- **The cone instances of the spine.** `SpineTestsNMC` (equivalent to Gallai's conjecture by
`gallai_iff_spineTests'`) gives rooted Gallai for every 2-connected Eulerian graph of even order
without a matching cut. -/
theorem rootedDecomp_of_spineTestsNMC (h : SpineTestsNMC.{u}) {W : Type u} [Fintype W]
    [DecidableEq W] (B : SimpleGraph W) [DecidableRel B.Adj] (h2 : KConnected 2 B)
    (hm : ¬ HasMatchingCut B) (hW : Even (Fintype.card W)) (hB : ∀ a, Even (B.degree a))
    (r : W) : RootedDecomp B r :=
  test1_fullCone_iff.1 (h (Option W) (fullCone B) none (kConnected_three_fullCone_iff.2 h2)
    (by rwa [hasMatchingCut_delVert_fullCone_iff])).1 hW hB r

/-- Conversely, on a cone over a graph of even order every test of the spine is either vacuous
or rooted Gallai at the apex: `Test1` and `Test2` hold at every vertex of `cone B` iff
`RootedDecomp B r` holds for every `r` whenever `B` is Eulerian. -/
theorem fullConeTests_iff {W : Type u} [Fintype W] [DecidableEq W] (B : SimpleGraph W)
    [DecidableRel B.Adj] (hW : Even (Fintype.card W)) :
    (∀ z, Test1 (fullCone B) z ∧ Test2 (fullCone B) z) ↔
      ((∀ a, Even (B.degree a)) → ∀ r, RootedDecomp B r) := by
  constructor
  · intro h hB r
    exact test1_fullCone_iff.1 (h none).1 hW hB r
  · intro h z
    cases z with
    | none => exact ⟨test1_fullCone_iff.2 (fun _ hB => h hB), test2_fullCone_apex⟩
    | some a => exact ⟨test1_fullCone_some a, test2_fullCone_some_of_even a hW⟩

/-- Gallai's conjecture gives rooted Gallai for every connected Eulerian graph of even order
(through the rooted private-leaf test; 2-connectivity is not needed). -/
theorem rootedDecomp_of_gallai (h : GallaiConjecture.{u}) {W : Type u} [Fintype W]
    [DecidableEq W] (B : SimpleGraph W) [DecidableRel B.Adj] (hc : B.Connected)
    (hW : Even (Fintype.card W)) (hB : ∀ a, Even (B.degree a)) (r : W)
    (hpos : 0 < B.degree r) : RootedDecomp B r :=
  (rootedDecomp_iff_addLeaf r (hB r) hpos).2 (gallai_iff_rootedTest.1 h W B hc hW r)

end Gallai
