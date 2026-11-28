import GallaiLean.MultiSepEE
import GallaiLean.Separation

/-!
# Leaf tails with a sparse set of heads (session `claude/ln`)

Manuscript `manuscripts/ln`, Theorem A.

A *leaf tail* is a pair `(c, A)`: a vertex `c` of degree one and a set `A` of vertices, each at
distance at least three from `c` (`FarApart`). A decomposition *keeps* a family `T` of leaf tails if
no path through the leaf `c` of `(c, A) ∈ T` meets `A` (`KeepsTails`); since `c` is a leaf, the
path through `c` is the path ending at `c`.

**Theorem A** (`leaf_tails`). Let `G` have at most one vertex of positive even degree, let `T` be a
finite family of leaf tails, and suppose the set `heads T` of all avoided vertices is *sparse*: no
vertex has two neighbours in it (`SparseIn`). Then `G` has a Lovász decomposition that keeps `T`.

The leaves are not required to be sparse: several tails may share a stem, a stem may be adjacent to
the heads of other tails, and the even vertex may be a stem or a head. This is what separates the
theorem from `separation_sparse` (MultiSep.lean), which needs the leaves and the heads together to
be sparse, and from the multi-token fin `tailGood_fin`, which allows one live tail.

Proof: Lovász's induction on `ν = Σ deg + [no even vertex]` (`lt_strong`).
* `lt_case_target` (Case I): the even vertex `z` has a neighbour `u` that is neither a head nor a
  tail leaf; delete `zu` and restore it by Fan's lemma towards `u`.
* `lt_case_path` (Case I, residual): `z` has a leaf neighbour `c` and a second neighbour `y`, and
  either `y` is a leaf or `d(z) = 2`; delete `zc, zy` and restore them as the path `c z y`
  (`PathDecomp.add_path2_supp`). Sparseness forces one of the two alternatives whenever every
  neighbour of `z` is a head or a tail leaf.
* `lt_case_leaf` (no even vertex, a leaf `v`): delete the leaf edge and restore it as a path.
* `lt_case_big` (Case II): no even vertex, a vertex `x` outside the heads of degree `≥ 3`; Lovász's
  pendant-leaf trick on `Option W`, then the path `ux` or Fan's lemma towards `x`.
* `lt_case_empty`: otherwise sparseness leaves no edges.
-/

open SimpleGraph

namespace Gallai

universe u

section defs

variable {W : Type u}

/-- A family of *leaf tails* in `G`: each `(c, A) ∈ T` has `c` of degree one and every `a ∈ A` at
distance at least three from `c`. -/
def LeafTails [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (T : Finset (W × Finset W)) : Prop :=
  ∀ t ∈ T, G.degree t.1 = 1 ∧ ∀ a ∈ t.2, FarApart G t.1 a

/-- All the avoided vertices of a family of tails. -/
def heads [DecidableEq W] (T : Finset (W × Finset W)) : Finset W := T.biUnion Prod.snd

/-- `D` keeps every tail of `T`: no path through `c` meets `A`, for `(c, A) ∈ T`. -/
def KeepsTails {G : SimpleGraph W} (D : PathDecomp G) (T : Finset (W × Finset W)) : Prop :=
  ∀ t ∈ T, ∀ P ∈ D.paths, t.1 ∈ P.walk.support → ∀ a ∈ t.2, a ∉ P.walk.support

/-- `X` is sparse in `G`: no vertex has two distinct neighbours in `X`. -/
def SparseIn (G : SimpleGraph W) (X : Finset W) : Prop :=
  ∀ v p q, G.Adj v p → G.Adj v q → p ∈ X → q ∈ X → p = q

theorem mem_heads [DecidableEq W] {T : Finset (W × Finset W)} {t : W × Finset W} (ht : t ∈ T)
    {a : W} (ha : a ∈ t.2) : a ∈ heads T :=
  Finset.mem_biUnion.mpr ⟨t, ht, ha⟩

theorem SparseIn.mono {G H : SimpleGraph W} {X Y : Finset W} (h : SparseIn G X)
    (hle : ∀ x y, H.Adj x y → G.Adj x y) (hYX : Y ⊆ X) : SparseIn H Y :=
  fun v p q hp hq hpY hqY => h v p q (hle _ _ hp) (hle _ _ hq) (hYX hpY) (hYX hqY)

theorem heads_filter_sub [DecidableEq W] (T : Finset (W × Finset W)) (P : W × Finset W → Prop)
    [DecidablePred P] : heads (T.filter P) ⊆ heads T := by
  intro a ha
  obtain ⟨t, ht, hat⟩ := Finset.mem_biUnion.mp ha
  exact mem_heads (Finset.mem_filter.mp ht).1 hat

/-- Keeping tails passes to a decomposition whose paths lie in old paths plus a vertex `g` that is
neither a head nor a tail leaf. -/
theorem keepsTails_of_cover [DecidableEq W] {G G' : SimpleGraph W} {D : PathDecomp G}
    {D' : PathDecomp G'} {T : Finset (W × Finset W)} {g : W} (hgX : g ∉ heads T)
    (hgL : ∀ t ∈ T, t.1 ≠ g) (hD' : KeepsTails D' T)
    (hcov : ∀ Q ∈ D.paths, ∃ Q' ∈ D'.paths, ∀ x ∈ Q.walk.support, x ∈ Q'.walk.support ∨ x = g) :
    KeepsTails D T := by
  intro t ht Q hQ hcQ a ha haQ
  obtain ⟨Q', hQ', h⟩ := hcov Q hQ
  have hag : a ≠ g := fun h' => hgX (h' ▸ mem_heads ht ha)
  exact hD' t ht Q' hQ' ((h _ hcQ).resolve_right (hgL t ht)) a ha ((h a haQ).resolve_right hag)

end defs

/-! ### Adding a path of length two -/

section addPath2

variable {W : Type u}

/-- The path `a m b` of length two. -/
def GPath.ofAdj2 {G : SimpleGraph W} {a m b : W} (h₁ : G.Adj a m) (h₂ : G.Adj m b) (hab : a ≠ b) :
    GPath G where
  src := a
  tgt := b
  walk := Walk.cons h₁ (Walk.cons h₂ Walk.nil)
  isPath := by
    rw [Walk.isPath_def]
    simp only [Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    exact ⟨⟨h₁.ne, hab⟩, h₂.ne, not_false⟩
  pos := by simp

theorem GPath.ofAdj2_edges {G : SimpleGraph W} {a m b : W} (h₁ : G.Adj a m) (h₂ : G.Adj m b)
    (hab : a ≠ b) : (GPath.ofAdj2 h₁ h₂ hab).edges = [s(a, m), s(m, b)] := by
  simp [GPath.ofAdj2, GPath.edges]

theorem GPath.ofAdj2_support {G : SimpleGraph W} {a m b : W} (h₁ : G.Adj a m) (h₂ : G.Adj m b)
    (hab : a ≠ b) : (GPath.ofAdj2 h₁ h₂ hab).walk.support = [a, m, b] := by
  simp [GPath.ofAdj2]

variable [DecidableEq W]

/-- **Adding a path of length two** `a m b` to a decomposition of `G − am − mb`, with control of
the vertex sets: every new path is the new one or lies in an old one. -/
theorem PathDecomp.add_path2_supp {G G' : SimpleGraph W} {a m b : W} (h₁ : G.Adj a m)
    (h₂ : G.Adj m b) (hab : a ≠ b)
    (hG' : ∀ e, e ∈ G'.edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(a, m) ∧ e ≠ s(m, b))
    (D' : PathDecomp G') :
    ∃ D : PathDecomp G, (∀ w,
      D.ends w = D'.ends w + (if a = w then 1 else 0) + (if b = w then 1 else 0)) ∧
      ∀ Q ∈ D.paths, (∀ x ∈ Q.walk.support, x = a ∨ x = m ∨ x = b) ∨
        ∃ Q' ∈ D'.paths, ∀ x ∈ Q.walk.support, x ∈ Q'.walk.support := by
  have h₁' : ∀ Q ∈ D'.paths, ∀ e ∈ Q.edges, e ∈ G.edgeSet := fun Q hQ e he =>
    ((hG' e).1 ((D'.covers e).2 (List.mem_flatMap.mpr ⟨Q, hQ, he⟩))).1
  let L := D'.paths.pmap (fun Q hQ => Q.transfer hQ) h₁' ++ [GPath.ofAdj2 h₁ h₂ hab]
  have hL : L.flatMap GPath.edges = D'.paths.flatMap GPath.edges ++ [s(a, m), s(m, b)] := by
    simp only [L, List.flatMap_append, flatMap_pmap_transfer, List.flatMap_cons,
      List.flatMap_nil, GPath.ofAdj2_edges, List.append_nil]
  have hne : s(a, m) ≠ s(m, b) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact h₁.ne h1
    · exact hab h1
  have hnd : (L.flatMap GPath.edges).Nodup := by
    rw [hL, List.nodup_append]
    refine ⟨D'.nodup_edges, ?_, ?_⟩
    · simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
        List.nodup_nil, and_true]
      exact hne
    · intro e he f hf hef
      subst hef
      have := (hG' e).1 ((D'.covers e).2 he)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl
      · exact this.2.1 rfl
      · exact this.2.2 rfl
  have hcov : ∀ e, e ∈ G.edgeSet ↔ e ∈ L.flatMap GPath.edges := by
    intro e
    rw [hL, List.mem_append, ← D'.covers, hG']
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    constructor
    · intro he
      by_cases h : e = s(a, m)
      · exact Or.inr (Or.inl h)
      · by_cases h' : e = s(m, b)
        · exact Or.inr (Or.inr h')
        · exact Or.inl ⟨he, h, h'⟩
    · rintro (⟨he, -⟩ | rfl | rfl)
      · exact he
      · exact h₁
      · exact h₂
  refine ⟨⟨L, hnd, hcov⟩, fun w => ?_, ?_⟩
  · unfold PathDecomp.ends
    simp only [L, List.map_append, List.sum_append, sum_endsAt_pmap_transfer, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have : (GPath.ofAdj2 h₁ h₂ hab).endsAt w =
        (if a = w then 1 else 0) + (if b = w then 1 else 0) := rfl
    rw [this]
    omega
  · intro Q hQ
    change Q ∈ L at hQ
    simp only [L, List.mem_append, List.mem_pmap, List.mem_singleton] at hQ
    rcases hQ with ⟨Q', hQ', rfl⟩ | rfl
    · exact Or.inr ⟨Q', hQ', fun x hx => by rwa [GPath.transfer_support] at hx⟩
    · left
      intro x hx
      rw [GPath.ofAdj2_support] at hx
      simpa using hx

end addPath2

/-! ### The induction -/

section induction

/-- The statement proved by strong induction on `ν(G) = Σ deg + [no even vertex]`. -/
def LTStrong (n : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (T : Finset (W × Finset W)), (evenSet G).card ≤ 1 → LeafTails G T → SparseIn G (heads T) →
    (∑ w, G.degree w) + (if (evenSet G).card = 0 then 1 else 0) = n →
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ KeepsTails D T

variable {W : Type u} [Fintype W] [DecidableEq W]

omit [DecidableEq W] in
theorem not_adj_of_degree_zero {G : SimpleGraph W} [DecidableRel G.Adj] {x : W}
    (h : G.degree x = 0) (y : W) : ¬ G.Adj x y := fun hxy => by
  have := (G.degree_pos_iff_exists_adj x).mpr ⟨y, hxy⟩
  omega

/-- Case I with a free target: the even vertex `z` has a neighbour `u` that is neither a head nor
a tail leaf. -/
theorem lt_case_target {n : ℕ} (ih : ∀ m < n, LTStrong.{u} m)
    (G : SimpleGraph W) [DecidableRel G.Adj] {T : Finset (W × Finset W)}
    (hev : (evenSet G).card ≤ 1) (hT : LeafTails G T) (hX : SparseIn G (heads T))
    (hn : (∑ w, G.degree w) + (if (evenSet G).card = 0 then 1 else 0) = n)
    {z u : W} (hz : z ∈ evenSet G) (hzu : G.Adj z u) (huX : u ∉ heads T)
    (huL : ∀ t ∈ T, t.1 ≠ u) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ KeepsTails D T := by
  have hzd := mem_evenSet_iff.mp hz
  have huz : G.Adj u z := hzu.symm
  have hne : u ≠ z := huz.ne
  have huniq : ∀ w ∈ evenSet G, w = z := fun w hw => Finset.card_le_one.mp hev w hw z hz
  have hdeg := delEdge_degree G huz
  have hupos : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).mpr ⟨z, huz⟩
  have huodd : G.degree u % 2 = 1 := by
    have : u ∉ evenSet G := fun h => hne (huniq u h)
    rw [mem_evenSet_iff] at this
    omega
  have hdu := hdeg u
  have hdz := hdeg z
  simp only [hne, hne.symm, ite_true, ite_false, add_zero] at hdu hdz
  have hev' : evenSet (delEdge G u z) ⊆ {u} := by
    intro w hw
    rw [Finset.mem_singleton]
    obtain ⟨hpos, heven⟩ := mem_evenSet_iff.mp hw
    by_contra hwu
    by_cases hwz : w = z
    · subst hwz
      omega
    · have h := hdeg w
      simp only [hwu, hwz, ite_false, add_zero] at h
      exact hwz (huniq w (mem_evenSet_iff.mpr ⟨h ▸ hpos, h ▸ heven⟩))
  have hcard' : (evenSet (delEdge G u z)).card ≤ 1 :=
    (Finset.card_le_card hev').trans (by simp)
  have hsum := delEdge_sum_degree G huz
  have hlt : (∑ w, (delEdge G u z).degree w) +
      (if (evenSet (delEdge G u z)).card = 0 then 1 else 0) < n := by
    have : (evenSet G).card ≠ 0 := Finset.card_ne_zero.mpr ⟨z, hz⟩
    simp only [this, ite_false, add_zero] at hn
    split_ifs <;> omega
  have hT' : LeafTails (delEdge G u z) T := by
    intro t ht
    obtain ⟨h1, h2⟩ := hT t ht
    refine ⟨?_, fun a ha => (h2 a ha).mono (fun _ _ h => h.1)⟩
    have htu : t.1 ≠ u := huL t ht
    have htz : t.1 ≠ z := by
      intro h
      rw [h] at h1
      omega
    have h := hdeg t.1
    simp only [htu, htz, ite_false, add_zero] at h
    rw [h, h1]
  have hX' : SparseIn (delEdge G u z) (heads T) := hX.mono (fun _ _ h => h.1) (subset_refl _)
  obtain ⟨D', hD', hk'⟩ := ih _ hlt W (delEdge G u z) T hcard' hT' hX' rfl
  have hD'z : D'.ends z = 1 := by rw [hD' z]; omega
  obtain ⟨D, -, hDu, hDz, hDo, hcov⟩ := fan_single_supp huz (delEdge_edgeSet G u z) D' (by
    rw [hD'z]
    have : Finset.univ.filter (fun w => (delEdge G u z).Adj u w ∧ D'.ends w = 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro w - ⟨hadj, h0⟩
      have hwu : w ≠ u := hadj.ne.symm
      have hpos : 0 < (delEdge G u z).degree w :=
        ((delEdge G u z).degree_pos_iff_exists_adj w).mpr ⟨u, hadj.symm⟩
      rw [hD' w] at h0
      exact hwu (Finset.mem_singleton.mp (hev' (mem_evenSet_iff.mpr ⟨hpos, h0⟩)))
    rw [this, Finset.card_empty]
    exact Nat.one_pos)
  refine ⟨D, fun w => ?_, keepsTails_of_cover huX huL hk' hcov⟩
  by_cases hwu : w = u
  · subst hwu
    rw [hDu, hD' w]
    omega
  · by_cases hwz : w = z
    · subst hwz
      omega
    · rw [hDo w hwu hwz, hD' w]
      have h := hdeg w
      simp only [hwu, hwz, ite_false, add_zero] at h
      rw [h]

/-- Case I, residual: the even vertex `z` has a leaf neighbour `c` and a second neighbour `y`, and
either `y` is a leaf or `d(z) = 2`. Delete `zc` and `zy` and restore them as the path `c z y`. -/
theorem lt_case_path {n : ℕ} (ih : ∀ m < n, LTStrong.{u} m)
    (G : SimpleGraph W) [DecidableRel G.Adj] {T : Finset (W × Finset W)}
    (hev : (evenSet G).card ≤ 1) (hT : LeafTails G T) (hX : SparseIn G (heads T))
    (hn : (∑ w, G.degree w) + (if (evenSet G).card = 0 then 1 else 0) = n)
    {z c y : W} (hz : z ∈ evenSet G) (hzc : G.Adj z c) (hzy : G.Adj z y) (hcy : c ≠ y)
    (hc1 : G.degree c = 1) (hor : G.degree y = 1 ∨ G.degree z = 2) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ KeepsTails D T := by
  have hzd := mem_evenSet_iff.mp hz
  have hzc' : z ≠ c := hzc.ne
  have hzy' : z ≠ y := hzy.ne
  have huniq : ∀ w ∈ evenSet G, w = z := fun w hw => Finset.card_le_one.mp hev w hw z hz
  have hypos : 0 < G.degree y := (G.degree_pos_iff_exists_adj y).mpr ⟨z, hzy.symm⟩
  have hyodd : G.degree y % 2 = 1 := by
    have : y ∉ evenSet G := fun h => hzy' (huniq y h).symm
    rw [mem_evenSet_iff] at this
    omega
  have hzy1 : (delEdge G z c).Adj z y := ⟨hzy, fun h => by
    rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hcy h2.symm
    · exact hzc' h1⟩
  have hdeg1 := delEdge_degree G hzc
  have hdeg2 := delEdge_degree (delEdge G z c) hzy1
  have hsum1 := delEdge_sum_degree G hzc
  have hsum2 := delEdge_sum_degree (delEdge G z c) hzy1
  have hKz : (delEdge (delEdge G z c) z y).degree z + 2 = G.degree z := by
    have h1 := hdeg1 z
    have h2 := hdeg2 z
    rw [if_pos rfl, if_neg hzc'] at h1
    rw [if_pos rfl, if_neg hzy'] at h2
    omega
  have hKc : (delEdge (delEdge G z c) z y).degree c = 0 := by
    have h1 := hdeg1 c
    have h2 := hdeg2 c
    rw [if_neg (Ne.symm hzc'), if_pos rfl] at h1
    rw [if_neg (Ne.symm hzc'), if_neg hcy] at h2
    omega
  have hKy : (delEdge (delEdge G z c) z y).degree y + 1 = G.degree y := by
    have h1 := hdeg1 y
    have h2 := hdeg2 y
    rw [if_neg (Ne.symm hzy'), if_neg (Ne.symm hcy)] at h1
    rw [if_neg (Ne.symm hzy'), if_pos rfl] at h2
    omega
  have hKo : ∀ w, w ≠ z → w ≠ c → w ≠ y → (delEdge (delEdge G z c) z y).degree w = G.degree w := by
    intro w hwz hwc hwy
    have h1 := hdeg1 w
    have h2 := hdeg2 w
    rw [if_neg hwz, if_neg hwc] at h1
    rw [if_neg hwz, if_neg hwy] at h2
    omega
  have hKle : ∀ a b, (delEdge (delEdge G z c) z y).Adj a b → G.Adj a b := fun _ _ h => h.1.1
  have hevK : ∀ a ∈ evenSet (delEdge (delEdge G z c) z y), ∀ b ∈ evenSet (delEdge (delEdge G z c) z y), a = b := by
    have hmem : ∀ w ∈ evenSet (delEdge (delEdge G z c) z y), (w = z ∧ G.degree y = 1) ∨ (w = y ∧ G.degree z = 2) := by
      intro w hw
      obtain ⟨hpos, hevn⟩ := mem_evenSet_iff.mp hw
      by_cases hwz : w = z
      · rw [hwz] at hpos
        left
        refine ⟨hwz, ?_⟩
        rcases hor with h' | h'
        · exact h'
        · omega
      · by_cases hwc : w = c
        · rw [hwc, hKc] at hpos
          omega
        · by_cases hwy : w = y
          · rw [hwy] at hpos
            right
            refine ⟨hwy, ?_⟩
            rcases hor with h' | h'
            · omega
            · exact h'
          · have h := hKo w hwz hwc hwy
            exact absurd (huniq w (mem_evenSet_iff.mpr ⟨h ▸ hpos, h ▸ hevn⟩)) hwz
    intro a ha b hb
    rcases hmem a ha with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;> rcases hmem b hb with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
    · rfl
    · exfalso
      have := (mem_evenSet_iff.mp hb).1
      omega
    · exfalso
      have := (mem_evenSet_iff.mp ha).1
      omega
    · rfl
  have hcardK : (evenSet (delEdge (delEdge G z c) z y)).card ≤ 1 := Finset.card_le_one.mpr hevK
  have hlt : (∑ w, (delEdge (delEdge G z c) z y).degree w) + (if (evenSet (delEdge (delEdge G z c) z y)).card = 0 then 1 else 0) < n := by
    have : (evenSet G).card ≠ 0 := Finset.card_ne_zero.mpr ⟨z, hz⟩
    simp only [this, ite_false, add_zero] at hn
    split_ifs <;> omega
  set T' := T.filter (fun t => t.1 ≠ c ∧ t.1 ≠ y) with hT'def
  have hT' : LeafTails (delEdge (delEdge G z c) z y) T' := by
    intro t ht
    obtain ⟨htT, htc, hty⟩ := Finset.mem_filter.mp ht
    obtain ⟨h1, h2⟩ := hT t htT
    refine ⟨?_, fun a ha => (h2 a ha).mono hKle⟩
    have htz : t.1 ≠ z := by
      intro h
      rw [h] at h1
      omega
    rw [hKo t.1 htz htc hty, h1]
  have hX' : SparseIn (delEdge (delEdge G z c) z y) (heads T') := hX.mono hKle (heads_filter_sub _ _)
  obtain ⟨D', hD', hk'⟩ := ih _ hlt W (delEdge (delEdge G z c) z y) T' hcardK hT' hX' rfl
  have hKe : ∀ e, e ∈ (delEdge (delEdge G z c) z y).edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(c, z) ∧ e ≠ s(z, y) := by
    intro e
    rw [delEdge_edgeSet (delEdge G z c) z y e, delEdge_edgeSet G z c e, Sym2.eq_swap (a := c)]
    tauto
  obtain ⟨D, hDe, hDcov⟩ := PathDecomp.add_path2_supp hzc.symm hzy hcy hKe D'
  refine ⟨D, fun w => ?_, ?_⟩
  · rw [hDe w, hD' w]
    by_cases hwc : w = c
    · rw [hwc, hKc, if_pos rfl, if_neg (Ne.symm hcy), hc1]
    · by_cases hwy : w = y
      · rw [hwy, if_neg hcy, if_pos rfl]
        omega
      · simp only [Ne.symm hwc, Ne.symm hwy, if_false, add_zero]
        by_cases hwz : w = z
        · rw [hwz]
          omega
        · rw [hKo w hwz hwc hwy]
  · intro t ht Q hQ htQ a ha haQ
    obtain ⟨h1, h2⟩ := hT t ht
    have hfa := h2 a ha
    have htz : t.1 ≠ z := by
      intro h
      rw [h] at h1
      omega
    rcases hDcov Q hQ with hsm | ⟨Q', hQ', hsub⟩
    · rcases hsm _ htQ with htc | htz' | hty
      · rcases hsm a haQ with hac | haz | hay
        · exact hfa.1 (htc.trans hac.symm)
        · exact hfa.2.1 (by rw [htc, haz]; exact hzc.symm)
        · exact hfa.2.2 z ⟨by rw [htc]; exact hzc.symm, by rw [hay]; exact hzy⟩
      · exact htz htz'
      · rcases hsm a haQ with hac | haz | hay
        · exact hfa.2.2 z ⟨by rw [hty]; exact hzy.symm, by rw [hac]; exact hzc⟩
        · exact hfa.2.1 (by rw [hty, haz]; exact hzy.symm)
        · exact hfa.1 (hty.trans hay.symm)
    · have htQ' := hsub _ htQ
      by_cases htc : t.1 = c
      · exact Q'.not_mem_of_isolated (not_adj_of_degree_zero (htc ▸ hKc)) htQ'
      · by_cases hty : t.1 = y
        · have hKy0 : (delEdge (delEdge G z c) z y).degree y = 0 := by
            have h := h1
            rw [hty] at h
            omega
          exact Q'.not_mem_of_isolated (not_adj_of_degree_zero (hty ▸ hKy0)) htQ'
        · exact hk' t (Finset.mem_filter.mpr ⟨ht, htc, hty⟩) Q' hQ' htQ' a ha (hsub a haQ)

/-- No even vertex and a leaf `v`: delete the leaf edge and restore it as a path. -/
theorem lt_case_leaf {n : ℕ} (ih : ∀ m < n, LTStrong.{u} m)
    (G : SimpleGraph W) [DecidableRel G.Adj] {T : Finset (W × Finset W)}
    (hT : LeafTails G T) (hX : SparseIn G (heads T))
    (hn : (∑ w, G.degree w) + (if (evenSet G).card = 0 then 1 else 0) = n)
    (hnone : ∀ z, z ∉ evenSet G) {v : W} (hv1 : G.degree v = 1) :
    ∃ D : PathDecomp G, (∀ x, D.ends x = G.degree x % 2) ∧ KeepsTails D T := by
  obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp (by omega)
  have hne : v ≠ w := hvw.ne
  have hpar : ∀ y, 0 < G.degree y → G.degree y % 2 = 1 := fun y hy => by
    have := hnone y
    rw [mem_evenSet_iff] at this
    omega
  have hwpos : 0 < G.degree w := (G.degree_pos_iff_exists_adj w).mpr ⟨v, hvw.symm⟩
  have hdwo := hpar w hwpos
  have hdeg := delEdge_degree G hvw
  have hdv := hdeg v
  have hdw := hdeg w
  simp only [hne, hne.symm, ite_true, ite_false, add_zero] at hdv hdw
  have hev' : evenSet (delEdge G v w) ⊆ {w} := by
    intro y hy
    rw [Finset.mem_singleton]
    obtain ⟨hpos, heven⟩ := mem_evenSet_iff.mp hy
    by_contra hyw
    by_cases hyv : y = v
    · subst hyv; omega
    · have h := hdeg y
      simp only [hyv, hyw, ite_false, add_zero] at h
      have := hpar y (h ▸ hpos)
      omega
  have hcard' : (evenSet (delEdge G v w)).card ≤ 1 :=
    (Finset.card_le_card hev').trans (by simp)
  have hsum := delEdge_sum_degree G hvw
  have hlt : (∑ y, (delEdge G v w).degree y) +
      (if (evenSet (delEdge G v w)).card = 0 then 1 else 0) < n := by
    have h2 : (evenSet G).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem hnone)
    simp only [h2, ite_true] at hn
    split_ifs <;> omega
  set T' := T.filter (fun t => t.1 ≠ v ∧ t.1 ≠ w) with hT'def
  have hle : ∀ a b, (delEdge G v w).Adj a b → G.Adj a b := fun _ _ h => h.1
  have hT' : LeafTails (delEdge G v w) T' := by
    intro t ht
    obtain ⟨htT, htv, htw⟩ := Finset.mem_filter.mp ht
    obtain ⟨h1, h2⟩ := hT t htT
    refine ⟨?_, fun a ha => (h2 a ha).mono hle⟩
    have h := hdeg t.1
    simp only [htv, htw, ite_false, add_zero] at h
    rw [h, h1]
  have hX' : SparseIn (delEdge G v w) (heads T') := hX.mono hle (heads_filter_sub _ _)
  obtain ⟨D', hD', hk'⟩ := ih _ hlt W (delEdge G v w) T' hcard' hT' hX' rfl
  obtain ⟨D, hD, hcovD⟩ := PathDecomp.add_edge_supp hvw (delEdge_edgeSet G v w) D'
  refine ⟨D, fun y => ?_, ?_⟩
  · rw [hD y, hD' y]
    by_cases hyv : y = v
    · subst hyv
      simp only [Ne.symm hne, ite_true, ite_false]
      omega
    · by_cases hyw : y = w
      · subst hyw
        simp only [Ne.symm hyv, ite_true, ite_false]
        omega
      · have h := hdeg y
        simp only [hyv, hyw, Ne.symm hyv, Ne.symm hyw, ite_false, add_zero] at h ⊢
        rw [h]
  · intro t ht Q hQ htQ a ha haQ
    obtain ⟨h1, h2⟩ := hT t ht
    have hfa := h2 a ha
    rcases hcovD Q hQ with hsm | ⟨Q', hQ', hs⟩
    · rcases hsm _ htQ with htv | htw
      · rcases hsm a haQ with hav | haw
        · exact hfa.1 (htv.trans hav.symm)
        · exact hfa.2.1 (by rw [htv, haw]; exact hvw)
      · rcases hsm a haQ with hav | haw
        · exact hfa.2.1 (by rw [htw, hav]; exact hvw.symm)
        · exact hfa.1 (htw.trans haw.symm)
    · have htQ' := hs _ htQ
      by_cases htv : t.1 = v
      · have h0 : (delEdge G v w).degree t.1 = 0 := by rw [htv]; omega
        exact Q'.not_mem_of_isolated (not_adj_of_degree_zero h0) htQ'
      · by_cases htw : t.1 = w
        · have h0 : (delEdge G v w).degree t.1 = 0 := by rw [htw] at h1 ⊢; omega
          exact Q'.not_mem_of_isolated (not_adj_of_degree_zero h0) htQ'
        · exact hk' t (Finset.mem_filter.mpr ⟨ht, htv, htw⟩) Q' hQ' htQ' a ha (hs a haQ)

/-- The tails carried to `Option W`. -/
def liftT (T : Finset (W × Finset W)) : Finset (Option W × Finset (Option W)) :=
  T.image (fun t => (some t.1, t.2.image some))

theorem mem_liftT {T : Finset (W × Finset W)} {t : W × Finset W} (ht : t ∈ T) :
    (some t.1, t.2.image some) ∈ liftT T :=
  Finset.mem_image_of_mem _ ht

theorem exists_of_mem_heads_liftT {T : Finset (W × Finset W)} {b : Option W}
    (hb : b ∈ heads (liftT T)) : ∃ a, b = some a ∧ a ∈ heads T := by
  obtain ⟨t', ht', hbt⟩ := Finset.mem_biUnion.mp hb
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ht'
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hbt
  exact ⟨a, rfl, mem_heads ht ha⟩

/-- Case II: no even vertex, and some `x` outside the heads has degree `≥ 3`. -/
theorem lt_case_big {n : ℕ} (ih : ∀ m < n, LTStrong.{u} m)
    (G : SimpleGraph W) [DecidableRel G.Adj] {T : Finset (W × Finset W)}
    (hT : LeafTails G T) (hX : SparseIn G (heads T))
    (hn : (∑ w, G.degree w) + (if (evenSet G).card = 0 then 1 else 0) = n)
    (hnone : ∀ z, z ∉ evenSet G) {x : W} (hxX : x ∉ heads T) (hx : 3 ≤ G.degree x) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ KeepsTails D T := by
  obtain ⟨u, hxu⟩ := (G.degree_pos_iff_exists_adj x).mp (by omega)
  have hux : G.Adj u x := hxu.symm
  have hne : u ≠ x := hux.ne
  have hpar : ∀ w, 0 < G.degree w → G.degree w % 2 = 1 := fun w hw => by
    have := hnone w
    rw [mem_evenSet_iff] at this
    omega
  have hdeg := delEdge_degree G hux
  have hupos : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).mpr ⟨x, hux⟩
  have hdu := hdeg u
  have hdx := hdeg x
  simp only [hne, hne.symm, ite_true, ite_false, add_zero] at hdu hdx
  have hux_odd := hpar u hupos
  have hx_odd := hpar x (by omega)
  have hxL : ∀ t ∈ T, t.1 ≠ x := fun t ht h => by
    have := (hT t ht).1
    rw [h] at this
    omega
  have hHsome : ∀ w, (apex (delEdge G u x) {u}).degree (some w) =
      (delEdge G u x).degree w + (if w = u then 1 else 0) := by
    intro w
    rw [apex_degree_some]
    simp [Finset.mem_singleton]
  have hHnone : (apex (delEdge G u x) {u}).degree none = 1 := by
    rw [apex_degree_none]; simp
  have hevH : evenSet (apex (delEdge G u x) {u}) ⊆ {some x} := by
    intro w hw
    rw [mem_evenSet_iff] at hw
    rw [Finset.mem_singleton]
    cases w with
    | none => rw [hHnone] at hw; omega
    | some y =>
      rw [hHsome] at hw
      by_contra hyx
      have hyx' : y ≠ x := fun h => hyx (h ▸ rfl)
      by_cases hyu : y = u
      · subst hyu
        simp only [ite_true] at hw
        omega
      · have h := hdeg y
        simp only [hyu, hyx', ite_false, add_zero] at h hw
        have := hpar y (h ▸ hw.1)
        omega
  have hxH : some x ∈ evenSet (apex (delEdge G u x) {u}) := by
    rw [mem_evenSet_iff, hHsome]
    simp only [hne.symm, ite_false, add_zero]
    omega
  have hcardH : (evenSet (apex (delEdge G u x) {u})).card ≤ 1 :=
    (Finset.card_le_card hevH).trans (by simp)
  have hsumH : ∑ w, (apex (delEdge G u x) {u}).degree w = ∑ w, G.degree w := by
    rw [Fintype.sum_option, hHnone, ← delEdge_sum_degree G hux]
    simp only [hHsome, Finset.sum_add_distrib]
    simp
    omega
  have hlt : (∑ w, (apex (delEdge G u x) {u}).degree w) +
      (if (evenSet (apex (delEdge G u x) {u})).card = 0 then 1 else 0) < n := by
    have h1 : (evenSet (apex (delEdge G u x) {u})).card ≠ 0 :=
      Finset.card_ne_zero.mpr ⟨_, hxH⟩
    have h2 : (evenSet G).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem hnone)
    simp only [h2, ite_true] at hn
    simp only [h1, ite_false, add_zero, hsumH]
    omega
  have hTH : LeafTails (apex (delEdge G u x) {u}) (liftT T) := by
    intro t' ht'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ht'
    obtain ⟨h1, h2⟩ := hT t ht
    refine ⟨?_, ?_⟩
    · change (apex (delEdge G u x) {u}).degree (some t.1) = 1
      rw [hHsome]
      by_cases htu : t.1 = u
      · rw [if_pos htu]
        have h := hdeg t.1
        rw [if_pos htu, if_neg (fun h' => hne (htu.symm.trans h'))] at h
        omega
      · rw [if_neg htu]
        have h := hdeg t.1
        rw [if_neg htu, if_neg (hxL t ht)] at h
        omega
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      have hfa := h2 a ha
      refine ⟨fun h => hfa.1 (Option.some.inj h), fun h => hfa.2.1 h.1, fun w hw => ?_⟩
      cases w with
      | none =>
        obtain ⟨h1', h2'⟩ := hw
        rw [apex_adj_some_none, Finset.mem_singleton] at h1'
        rw [apex_adj_none_some, Finset.mem_singleton] at h2'
        exact hfa.1 (h1'.trans h2'.symm)
      | some w' => exact hfa.2.2 w' ⟨hw.1.1, hw.2.1⟩
  have hXH : SparseIn (apex (delEdge G u x) {u}) (heads (liftT T)) := by
    intro v p q hp hq hpX hqX
    obtain ⟨p', rfl, hp'⟩ := exists_of_mem_heads_liftT hpX
    obtain ⟨q', rfl, hq'⟩ := exists_of_mem_heads_liftT hqX
    cases v with
    | none =>
      rw [apex_adj_none_some, Finset.mem_singleton] at hp hq
      rw [hp, hq]
    | some v' =>
      rw [apex_adj_some_some] at hp hq
      rw [hX v' p' q' hp.1 hq.1 hp' hq']
  obtain ⟨DH, hDH, hkH⟩ :=
    ih _ hlt (Option W) (apex (delEdge G u x) {u}) (liftT T) hcardH hTH hXH rfl
  -- delete the new leaf
  obtain ⟨D', hD', hcovD'⟩ := (apexRetract (delEdge G u x) {u} x).delete_supp DH (by
    intro P _ y hy hky
    cases y with
    | some _ => simp [apexRetract] at hky
    | none => exact (P.end_of_pendant apex_none_pendant hy).imp Eq.symm Eq.symm)
  have hk' : KeepsTails D' T := by
    intro t ht Q hQ htQ a ha haQ
    obtain ⟨P, hP, hPs, -⟩ := hcovD' Q hQ
    exact hkH _ (mem_liftT ht) P hP (hPs _ htQ) (some a) (Finset.mem_image_of_mem _ ha)
      (hPs a haQ)
  have hD'w : ∀ w, w ≠ u → D'.ends w = (delEdge G u x).degree w % 2 := by
    intro w hwu
    rw [(hD' w).1 (fun e he hk hwe => hwu (Finset.mem_singleton.mp (apex_nonkept he hk hwe).2))]
    change DH.ends (some w) = _
    rw [hDH, hHsome]
    simp [hwu]
  have hD'u : D'.ends u = 0 ∨ D'.ends u = 2 := by
    have hle := (hD' u).2 (fun e₁ he₁ e₂ he₂ hk₁ hk₂ hv₁ hv₂ => by
      rw [(apex_nonkept he₁ hk₁ hv₁).1, (apex_nonkept he₂ hk₂ hv₂).1])
    change D'.ends u ≤ DH.ends (some u) + 1 at hle
    rw [hDH, hHsome] at hle
    simp only [ite_true] at hle
    have hp := D'.ends_mod_two u
    omega
  rcases hD'u with h0 | h2
  · -- `u` has no end: add `ux` as a new path
    obtain ⟨D, hD, hcovD⟩ := PathDecomp.add_edge_supp hux (delEdge_edgeSet G u x) D'
    refine ⟨D, fun w => ?_, ?_⟩
    · rw [hD w]
      by_cases hwu : w = u
      · subst hwu
        simp only [h0, Ne.symm hne, ite_true, ite_false]
        omega
      · rw [hD'w w hwu]
        by_cases hwx : w = x
        · subst hwx
          simp only [Ne.symm hwu, ite_true, ite_false]
          omega
        · have h := hdeg w
          simp only [hwu, hwx, Ne.symm hwu, Ne.symm hwx, ite_false, add_zero] at h ⊢
          rw [h]
    · intro t ht Q hQ htQ a ha haQ
      obtain ⟨h1, h2⟩ := hT t ht
      have hfa := h2 a ha
      rcases hcovD Q hQ with hsm | ⟨Q', hQ', hs⟩
      · rcases hsm _ htQ with htu | htx
        · rcases hsm a haQ with hau | hax
          · exact hfa.1 (htu.trans hau.symm)
          · exact hfa.2.1 (by rw [htu, hax]; exact hux)
        · exact hxL t ht htx
      · exact hk' t ht Q' hQ' (hs _ htQ) a ha (hs a haQ)
  · -- `u` has two ends: Fan's transfer `u → x`
    have hG'x : ∀ e, e ∈ (delEdge G u x).edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(x, u) := by
      intro e
      rw [delEdge_edgeSet, Sym2.eq_swap]
    obtain ⟨D, -, hDx, hDu, hDo, hcov⟩ := fan_single_supp hxu hG'x D' (by
      rw [h2]
      have : Finset.univ.filter (fun w => (delEdge G u x).Adj x w ∧ D'.ends w = 0) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        rintro w - ⟨hadj, h0⟩
        by_cases hwu : w = u
        · subst hwu; omega
        · have hwx : w ≠ x := hadj.ne.symm
          have hpos : 0 < (delEdge G u x).degree w :=
            ((delEdge G u x).degree_pos_iff_exists_adj w).mpr ⟨x, hadj.symm⟩
          have h := hdeg w
          simp only [hwu, hwx, ite_false, add_zero] at h
          rw [hD'w w hwu, h] at h0
          have := hpar w (h ▸ hpos)
          omega
      rw [this, Finset.card_empty]
      omega)
    refine ⟨D, fun w => ?_, keepsTails_of_cover hxX hxL hk' hcov⟩
    by_cases hwx : w = x
    · subst hwx
      rw [hDx, hD'w w (Ne.symm hne)]
      omega
    · by_cases hwu : w = u
      · subst hwu
        omega
      · rw [hDo w hwx hwu, hD'w w hwu]
        have h := hdeg w
        simp only [hwu, hwx, ite_false, add_zero] at h
        rw [h]

/-- Otherwise there are no edges. -/
theorem lt_case_empty (G : SimpleGraph W) [DecidableRel G.Adj] {T : Finset (W × Finset W)}
    (hX : SparseIn G (heads T)) (hnone : ∀ z, z ∉ evenSet G) (hno1 : ∀ v, G.degree v ≠ 1)
    (hsmall : ∀ x, x ∉ heads T → G.degree x < 3) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ KeepsTails D T := by
  have hpar : ∀ w, 0 < G.degree w → G.degree w % 2 = 1 := fun w hw => by
    have := hnone w
    rw [mem_evenSet_iff] at this
    omega
  have hout : ∀ x, x ∉ heads T → G.degree x = 0 := fun x hxX => by
    have h1 := hsmall x hxX
    have h2 := hno1 x
    rcases Nat.eq_zero_or_pos (G.degree x) with h | h
    · exact h
    · have := hpar x h
      omega
  have hdeg0 : ∀ x, G.degree x = 0 := by
    intro x
    by_cases hxX : x ∈ heads T
    · rcases Nat.eq_zero_or_pos (G.degree x) with h | h
      · exact h
      · exfalso
        have h3 : 3 ≤ G.degree x := by have := hpar x h; have := hno1 x; omega
        have h1 : 1 < (G.neighborFinset x).card := by rw [card_neighborFinset_eq_degree]; omega
        obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h1
        rw [mem_neighborFinset] at hp hq
        have hpX : p ∈ heads T := by
          by_contra hpX
          have := (G.degree_pos_iff_exists_adj p).mpr ⟨x, hp.symm⟩
          rw [hout p hpX] at this
          omega
        have hqX : q ∈ heads T := by
          by_contra hqX
          have := (G.degree_pos_iff_exists_adj q).mpr ⟨x, hq.symm⟩
          rw [hout q hqX] at this
          omega
        exact hpq (hX x p q hp hq hpX hqX)
    · exact hout x hxX
  obtain ⟨D, hD⟩ := lovasz_case_empty G hdeg0
  refine ⟨D, hD, fun t _ P hP _ _ _ _ => ?_⟩
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ P.edges_ne_nil
  have heG := (D.covers e).2 (List.mem_flatMap.mpr ⟨P, hP, he⟩)
  induction e using Sym2.inductionOn with
  | hf a b => exact not_adj_of_degree_zero (hdeg0 a) b heG

theorem lt_strong (n : ℕ) : LTStrong.{u} n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W _ _ G _ T hev hT hX hn
  by_cases hz : ∃ z, z ∈ evenSet G
  · obtain ⟨z, hz⟩ := hz
    by_cases htg : ∃ u, G.Adj z u ∧ u ∉ heads T ∧ ∀ t ∈ T, t.1 ≠ u
    · obtain ⟨u, hzu, huX, huL⟩ := htg
      exact lt_case_target ih G hev hT hX hn hz hzu huX huL
    · by_cases h2 : ∃ c y, G.Adj z c ∧ G.Adj z y ∧ c ≠ y ∧ G.degree c = 1 ∧ G.degree y = 1
      · obtain ⟨c, y, hzc, hzy, hcy, hc1, hy1⟩ := h2
        exact lt_case_path ih G hev hT hX hn hz hzc hzy hcy hc1 (Or.inl hy1)
      · have hzd := mem_evenSet_iff.mp hz
        have hnb : ∀ v, G.Adj z v → v ∈ heads T ∨ G.degree v = 1 := by
          intro v hv
          by_cases hvX : v ∈ heads T
          · exact Or.inl hvX
          · right
            by_contra hv1
            refine htg ⟨v, hv, hvX, fun t ht htv => hv1 ?_⟩
            rw [← htv]
            exact (hT t ht).1
        have h1 : 1 < (G.neighborFinset z).card := by rw [card_neighborFinset_eq_degree]; omega
        obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h1
        rw [mem_neighborFinset] at hp hq
        obtain ⟨c, y, hzc, hzy, hcy, hc1⟩ :
            ∃ c y, G.Adj z c ∧ G.Adj z y ∧ c ≠ y ∧ G.degree c = 1 := by
          rcases hnb p hp with hpX | hp1
          · rcases hnb q hq with hqX | hq1
            · exact absurd (hX z p q hp hq hpX hqX) hpq
            · exact ⟨q, p, hq, hp, Ne.symm hpq, hq1⟩
          · exact ⟨p, q, hp, hq, hpq, hp1⟩
        have hnot1 : ∀ v, G.Adj z v → v ≠ c → G.degree v ≠ 1 := fun v hv hvc hv1 =>
          h2 ⟨c, v, hzc, hv, Ne.symm hvc, hc1, hv1⟩
        have hdz : G.degree z = 2 := by
          have hsub : G.neighborFinset z ⊆ {c, y} := by
            intro v hv
            rw [mem_neighborFinset] at hv
            simp only [Finset.mem_insert, Finset.mem_singleton]
            by_cases hvc : v = c
            · exact Or.inl hvc
            · right
              have hvX := (hnb v hv).resolve_right (hnot1 v hv hvc)
              have hyX := (hnb y hzy).resolve_right (hnot1 y hzy (Ne.symm hcy))
              exact hX z v y hv hzy hvX hyX
          have := Finset.card_le_card hsub
          rw [card_neighborFinset_eq_degree, Finset.card_pair hcy] at this
          omega
        exact lt_case_path ih G hev hT hX hn hz hzc hzy hcy hc1 (Or.inr hdz)
  · simp only [not_exists] at hz
    by_cases hl : ∃ v, G.degree v = 1
    · obtain ⟨v, hv1⟩ := hl
      exact lt_case_leaf ih G hT hX hn hz hv1
    · simp only [not_exists] at hl
      by_cases hx : ∃ x, x ∉ heads T ∧ 3 ≤ G.degree x
      · obtain ⟨x, hxX, hx⟩ := hx
        exact lt_case_big ih G hT hX hn hz hxX hx
      · have hsmall : ∀ x, x ∉ heads T → G.degree x < 3 := fun x hxX => by
          by_contra h
          exact hx ⟨x, hxX, by omega⟩
        exact lt_case_empty G hX hz hl hsmall

end induction

/-- **Theorem A** (multi-tail leaf theorem). Let `G` have at most one vertex of positive even
degree, and let `T` be a finite family of leaf tails `(c, A)`: `c` has degree one and every vertex
of `A` is at distance at least three from `c`. If no vertex has two neighbours among the avoided
vertices `heads T`, then some Lovász decomposition of `G` keeps every tail: no path through `c`
meets `A`. -/
theorem leaf_tails {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1) {T : Finset (W × Finset W)}
    (hT : LeafTails G T) (hX : SparseIn G (heads T)) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ KeepsTails D T :=
  lt_strong _ W G T hev hT hX rfl


end Gallai

namespace Gallai

section corollaries

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- For leaf tails, keeping a tail is the avoidance condition on the path *ending* at its leaf. -/
theorem KeepsTails.avoid {G : SimpleGraph W} {D : PathDecomp G} {T : Finset (W × Finset W)}
    (hk : KeepsTails D T) {t : W × Finset W} (ht : t ∈ T) {P : GPath G} (hP : P ∈ D.paths)
    (hend : P.src = t.1 ∨ P.tgt = t.1) : ∀ a ∈ t.2, a ∉ P.walk.support := by
  have : t.1 ∈ P.walk.support := by
    rcases hend with h | h
    · rw [← h]; exact P.walk.start_mem_support
    · rw [← h]; exact P.walk.end_mem_support
  exact hk t ht P hP this

/-- **Corollary B** (one general tail). Let `G` have no vertex of positive even degree, let `c` be
odd and `a ≠ c` not adjacent to `c`, and let `T` be leaf tails at leaves other than `c`. If no vertex
has two neighbours in `{a} ∪ heads T`, then some Lovász decomposition has the path ending at `c`
avoiding `a` and keeps every tail of `T`. (With `T` empty this is `L₁`.) -/
theorem lovasz_avoid_leafTails (G : SimpleGraph W) [DecidableRel G.Adj]
    (hev : (evenSet G).card = 0) {c a : W} (hc : G.degree c % 2 = 1) (hca : c ≠ a)
    (hadj : ¬ G.Adj c a) {T : Finset (W × Finset W)} (hT : LeafTails G T)
    (hTc : ∀ t ∈ T, t.1 ≠ c) (hX : SparseIn G (insert a (heads T))) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      (∀ P ∈ D.paths, (P.src = c ∨ P.tgt = c) → a ∉ P.walk.support) ∧ KeepsTails D T := by
  classical
  have hHsome : ∀ w, (apex G {c}).degree (some w) = G.degree w + (if w = c then 1 else 0) := by
    intro w; rw [apex_degree_some]; simp [Finset.mem_singleton]
  have hHnone : (apex G {c}).degree none = 1 := by rw [apex_degree_none]; simp
  have hnoev : ∀ w, w ∉ evenSet G := fun w hw => by
    rw [Finset.card_eq_zero] at hev; rw [hev] at hw; simp at hw
  have hpar : ∀ w, 0 < G.degree w → G.degree w % 2 = 1 := fun w hw => by
    have := hnoev w; rw [mem_evenSet_iff] at this; omega
  have hevH : evenSet (apex G {c}) ⊆ {some c} := by
    intro w hw
    rw [mem_evenSet_iff] at hw
    rw [Finset.mem_singleton]
    cases w with
    | none => rw [hHnone] at hw; omega
    | some y =>
      rw [hHsome] at hw
      by_cases hyc : y = c
      · rw [hyc]
      · simp only [hyc, ite_false, add_zero] at hw
        have := hpar y hw.1
        omega
  have hcardH : (evenSet (apex G {c})).card ≤ 1 := (Finset.card_le_card hevH).trans (by simp)
  set t₀ : Option W × Finset (Option W) := (none, {some a}) with ht₀
  set TK := insert t₀ (liftT T) with hTK
  have hTK' : LeafTails (apex G {c}) TK := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · refine ⟨hHnone, fun b hb => ?_⟩
      rw [Finset.mem_singleton] at hb
      subst hb
      refine ⟨by simp, fun h => ?_, fun w hw => ?_⟩
      · rw [apex_adj_none_some, Finset.mem_singleton] at h
        exact hca h.symm
      · cases w with
        | none => exact apex_not_adj_none_none hw.1
        | some w' =>
          obtain ⟨h1, h2⟩ := hw
          rw [apex_adj_none_some, Finset.mem_singleton] at h1
          subst h1
          exact hadj h2
    · obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨h1, h2⟩ := hT t' ht'
      refine ⟨?_, fun b hb => ?_⟩
      · change (apex G {c}).degree (some t'.1) = 1
        rw [hHsome, if_neg (hTc t' ht'), h1]
      · obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hb
        have hfa := h2 a' ha'
        refine ⟨fun h => hfa.1 (Option.some.inj h), fun h => hfa.2.1 h, fun w hw => ?_⟩
        cases w with
        | none =>
          obtain ⟨h1', -⟩ := hw
          rw [apex_adj_some_none, Finset.mem_singleton] at h1'
          exact hTc t' ht' h1'
        | some w' => exact hfa.2.2 w' ⟨hw.1, hw.2⟩
  have hheads : ∀ b ∈ heads TK, ∃ a', b = some a' ∧ a' ∈ insert a (heads T) := by
    intro b hb
    obtain ⟨t, ht, hbt⟩ := Finset.mem_biUnion.mp hb
    rcases Finset.mem_insert.mp ht with rfl | ht
    · rw [Finset.mem_singleton] at hbt
      exact ⟨a, hbt, Finset.mem_insert_self _ _⟩
    · obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hbt
      exact ⟨a', rfl, Finset.mem_insert_of_mem (mem_heads ht' ha')⟩
  have hXK : SparseIn (apex G {c}) (heads TK) := by
    intro v p q hp hq hpX hqX
    obtain ⟨p', rfl, hp'⟩ := hheads p hpX
    obtain ⟨q', rfl, hq'⟩ := hheads q hqX
    cases v with
    | none =>
      rw [apex_adj_none_some, Finset.mem_singleton] at hp hq
      rw [hp, hq]
    | some v' =>
      rw [apex_adj_some_some] at hp hq
      rw [hX v' p' q' hp hq hp' hq']
  obtain ⟨DH, hDH, hkH⟩ := leaf_tails (apex G {c}) hcardH hTK' hXK
  obtain ⟨D, hD, hcov⟩ := (apexRetract G {c} c).delete_supp DH (by
    intro P _ y hy hky
    cases y with
    | some _ => simp [apexRetract] at hky
    | none => exact (P.end_of_pendant apex_none_pendant hy).imp Eq.symm Eq.symm)
  have hDc0 : DH.ends (some c) = 0 := by
    rw [hDH, hHsome]; simp only [ite_true]; omega
  refine ⟨D, fun w => ?_, ?_, ?_⟩
  · by_cases hwc : w = c
    · subst hwc
      have hle := (hD w).2 (fun e₁ he₁ e₂ he₂ hk₁ hk₂ hv₁ hv₂ => by
        rw [(apex_nonkept he₁ hk₁ hv₁).1, (apex_nonkept he₂ hk₂ hv₂).1])
      change D.ends w ≤ DH.ends (some w) + 1 at hle
      have hp := D.ends_mod_two w
      rw [hc] at hp ⊢
      omega
    · rw [(hD w).1 (fun e he hk hwe => hwc (Finset.mem_singleton.mp (apex_nonkept he hk hwe).2))]
      change DH.ends (some w) = _
      rw [hDH, hHsome]
      simp [hwc]
  · intro Q hQ hend hyQ
    obtain ⟨P, hP, hPs, hperm⟩ := hcov Q hQ
    have hyP : some a ∈ P.walk.support := hPs a hyQ
    have hnoneP : none ∉ P.walk.support := fun h =>
      hkH t₀ (Finset.mem_insert_self _ _) P hP h (some a) (Finset.mem_singleton_self _) hyP
    have hsome : ∀ e ∈ P.edges, ∃ x y : W, e = s(some x, some y) := by
      intro e he
      induction e using Sym2.inductionOn with
      | hf x y =>
        have hx : x ∈ P.walk.support := Walk.fst_mem_support_of_mem_edges _ he
        have hy : y ∈ P.walk.support := Walk.snd_mem_support_of_mem_edges _ he
        cases x with
        | none => exact absurd hx hnoneP
        | some x' =>
          cases y with
          | none => exact absurd hy hnoneP
          | some y' => exact ⟨x', y', rfl⟩
    have hfilt : P.edges.filter (bothKept (apexRetract G {c} c).kept) = P.edges := by
      rw [List.filter_eq_self]
      intro e he
      obtain ⟨x, y, rfl⟩ := hsome e he
      simp [apexRetract, bothKept_mk]
    rw [hfilt] at hperm
    have hQc : Q.incid c = 1 := by
      have h := Q.endsAt_eq_ite c
      have h1 : 1 ≤ Q.endsAt c := by
        unfold GPath.endsAt
        rcases hend with h' | h' <;> simp [h']
      split_ifs at h with hh
      · exact hh
      · omega
    have hPc : P.incid (some c) = 1 := by
      rw [← hQc]
      unfold GPath.incid
      rw [hperm.countP_eq, List.countP_map]
      apply List.countP_congr
      intro e he
      obtain ⟨x, y, rfl⟩ := hsome e he
      simp [apexRetract]
    have hPend : P.endsAt (some c) = 1 := by rw [P.endsAt_eq_ite, hPc]; rfl
    have hle : P.endsAt (some c) ≤ DH.ends (some c) := by
      unfold PathDecomp.ends
      exact List.le_sum_of_mem (List.mem_map_of_mem hP)
    omega
  · intro t ht Q hQ htQ b hb hbQ
    obtain ⟨P, hP, hPs, -⟩ := hcov Q hQ
    exact hkH _ (Finset.mem_insert_of_mem (mem_liftT ht)) P hP (hPs _ htQ) (some b)
      (Finset.mem_image_of_mem _ hb) (hPs b hbQ)

end corollaries

end Gallai
