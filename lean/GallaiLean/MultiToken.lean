import GallaiLean.TRNSteer
import GallaiLean.TriangleBase
import GallaiLean.LeafDictionary

/-!
# Multi-token steering (session `claude/multi-token`)

Manuscript `manuscripts/multi-token`.

A *tail* is a triple `t = (c, w, x)`: a leaf `c` hung at `w`, and a vertex `x` that the path through
`c` must avoid. A tail is *live* in `K` while the leaf edge `cw` is present. For a finite set `T` of
tails we look for a *parity decomposition* (`ends v = deg v mod 2` for every `v`) in which, for every
live tail, no path contains both `c` and `x` (`TailGood`). This is a property of vertex sets, and it
is kept by every Fan step whose target is none of the vertices `c, x` of a live tail.

*Tokens* are the even vertices of the current graph (`evenSet`). `SteerK` (manuscript Definition 2.2)
is a schedule of four kinds of moves:
* `move`: a token `p` moves along an edge `pu` to an odd vertex `u` that is not `c` or `x` of a live
  tail and, once `pu` is deleted, is adjacent to no other token (`fan_step_multi`: Fan's step has no
  blank; the token retires if `u` is left isolated);
* `drop`: a live tail whose `w` is odd is dropped by deleting the leaf edge `cw`; the edge comes back
  as the one-edge path `cw` (`tailGood_drop`);
* `supp`: a token of degree two whose neighbours `a, b` are non-adjacent is suppressed
  (`K − pa − pb + ab`; the path through `ab` is subdivided back, `splitOff_supp`);
* `fin`: the schedule ends when at most one token and at most one live tail are left; then the
  *multi-tail leaf lemma* (`tailGood_fin`, from the leaf-tail lemma `avoid_leafTail` and Lovász's
  theorem) gives a good decomposition.

* **`steerK_good`** (manuscript Theorem 2.7, the transfer theorem): a schedule from the even set of
  `K` gives `TailGood T K`, whatever `K` is, provided the static conditions `TailSys T` and the
  dynamic invariant `TailInv T K` hold at the start.
* **`triangleBase_of_steerK`** (Theorem 3.1): for triangle data `(J, z, r, w, L)` with the pairs of
  `L` oriented as `(xᵢ, yᵢ)`, a schedule in `M⁺ = leaves M {yᵢ}` with the tails `(ℓᵢ, yᵢ, xᵢ)` gives
  a triangle base; **`test1At_of_steerK`**: hence Test1 at `(J, z, r)`.
-/

open SimpleGraph

namespace Gallai

universe u

section tokens

variable {U : Type u} [Fintype U] [DecidableEq U]

/-- `u` is none of the vertices `c, x` of a tail `(c, w, x)` of `T` that is live in `K`. -/
def OffTails (T : Finset (U × U × U)) (K : SimpleGraph U) (u : U) : Prop :=
  ∀ t ∈ T, K.Adj t.1 t.2.1 → u ≠ t.1 ∧ u ≠ t.2.2

/-- At most one tail of `T` is live in `K`. -/
def OneLive (T : Finset (U × U × U)) (K : SimpleGraph U) : Prop :=
  ∀ t ∈ T, ∀ t' ∈ T, K.Adj t.1 t.2.1 → K.Adj t'.1 t'.2.1 → t = t'

/-- The suppression of a token with neighbours `a, b` is allowed: neither `a` nor `b` is the leaf
of a tail, and `ab` is not the pair `xw` of a live tail. -/
def SuppOK (T : Finset (U × U × U)) (K : SimpleGraph U) (a b : U) : Prop :=
  ∀ t ∈ T, a ≠ t.1 ∧ b ≠ t.1 ∧
    (K.Adj t.1 t.2.1 → ¬ (a = t.2.2 ∧ b = t.2.1) ∧ ¬ (a = t.2.1 ∧ b = t.2.2))

/-- **Static conditions on a set of tails** (manuscript Definition 2.1). In each tail `x ∉ {c, w}`,
and the vertices of two different tails do not interfere: the leaf of one is neither the leaf nor
the stem of the other, and the avoided vertex of one is neither the leaf nor the stem of the
other. -/
structure TailSys (T : Finset (U × U × U)) : Prop where
  xc : ∀ t ∈ T, t.2.2 ≠ t.1
  xw : ∀ t ∈ T, t.2.2 ≠ t.2.1
  cross : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' →
    t'.1 ≠ t.1 ∧ t'.1 ≠ t.2.1 ∧ t'.2.2 ≠ t.1 ∧ t'.2.2 ≠ t.2.1

/-- **The dynamic invariant**: every live tail `(c, w, x)` has `c` a leaf at `w`, `x` odd, and
`x ≁ w`. -/
def TailInv (T : Finset (U × U × U)) (K : SimpleGraph U) [DecidableRel K.Adj] : Prop :=
  ∀ t ∈ T, K.Adj t.1 t.2.1 →
    (∀ v, K.Adj t.1 v ↔ v = t.2.1) ∧ K.degree t.2.2 % 2 = 1 ∧ ¬ K.Adj t.2.2 t.2.1

/-- A parity decomposition of `K` in which, for every live tail `(c, w, x)`, no path contains both
`c` and `x`. -/
def TailGood (T : Finset (U × U × U)) (K : SimpleGraph U) [DecidableRel K.Adj] : Prop :=
  ∃ D : PathDecomp K, (∀ v, D.ends v = K.degree v % 2) ∧
    ∀ t ∈ T, K.Adj t.1 t.2.1 → MeetsOnce D {t.1, t.2.2}

/-- **A `k`-token schedule** (manuscript Definition 2.2). `SteerK T K τ`: the tokens are the vertices
of `τ` (in use, `τ` is the even set of `K`), and the live tails are those of `T` whose leaf edge is
in `K`.
* `fin`: at most one token and at most one live tail are left.
* `move`: a token `p` moves along `pu` to `u ∉ τ`, where `u` is not `c` or `x` of a live tail and,
  in `K − up`, `u` is adjacent to no token other than `p`. The new tokens are `τ − p`, plus `u`
  unless `u` is left isolated.
* `drop`: a live tail `(c, w, x)` with `w ∉ τ` is dropped: delete `cw`. The new tokens are `τ`, plus
  `w` unless `w` is left isolated.
* `supp`: a token `p` whose neighbours are exactly `a ≠ b`, with `a ≁ b`, is suppressed:
  `K − pa − pb + ab`, and `p` is no longer a token. -/
inductive SteerK (T : Finset (U × U × U)) : SimpleGraph U → Finset U → Prop
  | fin {K : SimpleGraph U} {τ : Finset U} : τ.card ≤ 1 → OneLive T K → SteerK T K τ
  | move {K : SimpleGraph U} {τ τ' : Finset U} {p u : U} : p ∈ τ → K.Adj p u → u ∉ τ →
      OffTails T K u → (∀ v ∈ τ, v ≠ p → ¬ (delEdge K u p).Adj u v) →
      (∀ v, v ∈ τ' ↔ (v ∈ τ ∧ v ≠ p) ∨ (v = u ∧ ∃ q, (delEdge K u p).Adj u q)) →
      SteerK T (delEdge K u p) τ' → SteerK T K τ
  | drop {K : SimpleGraph U} {τ τ' : Finset U} {t : U × U × U} : t ∈ T → K.Adj t.1 t.2.1 →
      t.2.1 ∉ τ →
      (∀ v, v ∈ τ' ↔ v ∈ τ ∨ (v = t.2.1 ∧ ∃ q, (delEdge K t.1 t.2.1).Adj t.2.1 q)) →
      SteerK T (delEdge K t.1 t.2.1) τ' → SteerK T K τ
  | supp {K : SimpleGraph U} {τ : Finset U} {p a b : U} : p ∈ τ →
      (∀ v, K.Adj p v ↔ v = a ∨ v = b) → a ≠ b → ¬ K.Adj a b → SuppOK T K a b →
      SteerK T (plusEdge (delEdge (delEdge K p a) p b) a b) (τ.erase p) → SteerK T K τ

/-! ### One Fan step with many even vertices -/

/-- **Fan's step with many tokens** (manuscript Lemma 2.3). Let `p` be even, `u` an odd neighbour
of `p`, and suppose that in `K − up` the vertex `u` is adjacent to no even vertex of `K` other than
`p`. A parity decomposition of `K − up` gives one of `K`, every path of which lies in a path of the
old one plus `u`. -/
theorem fan_step_multi (K : SimpleGraph U) [DecidableRel K.Adj] {p u : U}
    (hp : p ∈ evenSet K) (hpu : K.Adj p u) (hu : u ∉ evenSet K)
    (hno : ∀ v ∈ evenSet K, v ≠ p → ¬ (delEdge K u p).Adj u v)
    (D' : PathDecomp (delEdge K u p)) (hD' : ∀ v, D'.ends v = (delEdge K u p).degree v % 2) :
    ∃ D : PathDecomp K, (∀ v, D.ends v = K.degree v % 2) ∧
      ∀ Q ∈ D.paths, ∃ Q' ∈ D'.paths, ∀ x ∈ Q.walk.support, x ∈ Q'.walk.support ∨ x = u := by
  have hup : K.Adj u p := hpu.symm
  have hpd := mem_evenSet_iff.mp hp
  have hne : u ≠ p := hup.ne
  have hdeg := delEdge_degree K hup
  have hdu := hdeg u
  have hdp := hdeg p
  simp only [hne, hne.symm, ite_true, ite_false, add_zero] at hdu hdp
  have huodd : K.degree u % 2 = 1 := by
    have hupos : 0 < K.degree u := (K.degree_pos_iff_exists_adj u).mpr ⟨p, hup⟩
    rw [mem_evenSet_iff] at hu
    omega
  have hD'p : D'.ends p = 1 := by rw [hD' p]; omega
  obtain ⟨D, -, hDu, hDp, hDo, hcov⟩ := fan_single_supp hup (delEdge_edgeSet K u p) D' (by
    rw [hD'p]
    have : Finset.univ.filter (fun v => (delEdge K u p).Adj u v ∧ D'.ends v = 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro v - ⟨hadj, h0⟩
      have hvu : v ≠ u := hadj.ne.symm
      by_cases hvp : v = p
      · subst hvp
        exact hadj.2 rfl
      have hpos : 0 < (delEdge K u p).degree v :=
        ((delEdge K u p).degree_pos_iff_exists_adj v).mpr ⟨u, hadj.symm⟩
      rw [hD' v] at h0
      have h := hdeg v
      simp only [hvu, hvp, ite_false, add_zero] at h
      exact hno v (mem_evenSet_iff.mpr ⟨h ▸ hpos, h ▸ h0⟩) hvp hadj
    rw [this, Finset.card_empty]
    exact Nat.one_pos)
  refine ⟨D, fun v => ?_, hcov⟩
  by_cases hvu : v = u
  · subst hvu
    rw [hDu, hD' v]
    omega
  · by_cases hvp : v = p
    · subst hvp
      omega
    · rw [hDo v hvu hvp, hD' v]
      have h := hdeg v
      simp only [hvu, hvp, ite_false, add_zero] at h
      rw [h]

/-! ### The even set after each kind of move -/

theorem evenSet_move (K : SimpleGraph U) [DecidableRel K.Adj] {p u : U} (hp : p ∈ evenSet K)
    (hpu : K.Adj p u) (hu : u ∉ evenSet K) {τ' : Finset U}
    (hτ' : ∀ v, v ∈ τ' ↔ (v ∈ evenSet K ∧ v ≠ p) ∨ (v = u ∧ ∃ q, (delEdge K u p).Adj u q)) :
    evenSet (delEdge K u p) = τ' := by
  have hup : K.Adj u p := hpu.symm
  have hne : u ≠ p := hup.ne
  have hdeg := delEdge_degree K hup
  have hpd := mem_evenSet_iff.mp hp
  have hupos : 0 < K.degree u := (K.degree_pos_iff_exists_adj u).mpr ⟨p, hup⟩
  have huodd : K.degree u % 2 = 1 := by rw [mem_evenSet_iff] at hu; omega
  ext v
  rw [hτ', mem_evenSet_iff]
  have h := hdeg v
  by_cases hvu : v = u
  · subst hvu
    simp only [hne, ite_true, ite_false, add_zero] at h
    rw [← (delEdge K v p).degree_pos_iff_exists_adj v]
    constructor
    · rintro ⟨hpos, -⟩
      exact Or.inr ⟨rfl, hpos⟩
    · rintro (⟨hv, -⟩ | ⟨-, hpos⟩)
      · exact absurd hv hu
      · exact ⟨hpos, by omega⟩
  · by_cases hvp : v = p
    · subst hvp
      simp only [hvu, ite_true, ite_false] at h
      constructor
      · rintro ⟨-, he⟩
        omega
      · rintro (⟨-, hvp⟩ | ⟨hvu', -⟩)
        · exact absurd rfl hvp
        · exact absurd hvu' hvu
    · simp only [hvu, hvp, ite_false, add_zero] at h
      rw [h, ← mem_evenSet_iff]
      constructor
      · intro hv
        exact Or.inl ⟨hv, hvp⟩
      · rintro (⟨hv, -⟩ | ⟨hvu', -⟩)
        · exact hv
        · exact absurd hvu' hvu

theorem evenSet_drop (K : SimpleGraph U) [DecidableRel K.Adj] {c w : U} (hcw : K.Adj c w)
    (hc : ∀ v, K.Adj c v ↔ v = w) (hw : w ∉ evenSet K) {τ' : Finset U}
    (hτ' : ∀ v, v ∈ τ' ↔ v ∈ evenSet K ∨ (v = w ∧ ∃ q, (delEdge K c w).Adj w q)) :
    evenSet (delEdge K c w) = τ' := by
  have hne : c ≠ w := hcw.ne
  have hdeg := delEdge_degree K hcw
  have hwpos : 0 < K.degree w := (K.degree_pos_iff_exists_adj w).mpr ⟨c, hcw.symm⟩
  have hwodd : K.degree w % 2 = 1 := by rw [mem_evenSet_iff] at hw; omega
  have hcdeg : K.degree c = 1 := by
    rw [← card_neighborFinset_eq_degree]
    have : K.neighborFinset c = {w} := by
      ext v
      rw [mem_neighborFinset, Finset.mem_singleton, hc]
    rw [this, Finset.card_singleton]
  have hcE : c ∉ evenSet K := by rw [mem_evenSet_iff]; omega
  ext v
  rw [hτ', mem_evenSet_iff]
  have h := hdeg v
  by_cases hvc : v = c
  · subst hvc
    simp only [hne, ite_true, ite_false, add_zero] at h
    constructor
    · rintro ⟨hpos, -⟩
      omega
    · rintro (hv | ⟨hvw, -⟩)
      · exact absurd hv hcE
      · exact absurd hvw hne
  · by_cases hvw : v = w
    · subst hvw
      simp only [hvc, ite_true, ite_false] at h
      rw [← (delEdge K c v).degree_pos_iff_exists_adj v]
      constructor
      · rintro ⟨hpos, -⟩
        exact Or.inr ⟨rfl, hpos⟩
      · rintro (hv | ⟨-, hpos⟩)
        · exact absurd hv hw
        · exact ⟨hpos, by omega⟩
    · simp only [hvc, hvw, ite_false, add_zero] at h
      rw [h, ← mem_evenSet_iff]
      constructor
      · exact Or.inl
      · rintro (hv | ⟨hvw', -⟩)
        · exact hv
        · exact absurd hvw' hvw

/-! ### Tails -/

omit [DecidableEq U] in
/-- A leaf has degree one. -/
theorem leaf_degree_one (K : SimpleGraph U) [DecidableRel K.Adj] {c w : U}
    (hc : ∀ v, K.Adj c v ↔ v = w) : K.degree c = 1 := by
  rw [← card_neighborFinset_eq_degree]
  have : K.neighborFinset c = {w} := by
    ext v
    rw [mem_neighborFinset, Finset.mem_singleton, hc]
  rw [this, Finset.card_singleton]

omit [DecidableEq U] in
/-- The leaf of a live tail is not a token. -/
theorem leaf_not_mem_evenSet (K : SimpleGraph U) [DecidableRel K.Adj] {c w : U}
    (hc : ∀ v, K.Adj c v ↔ v = w) : c ∉ evenSet K := by
  rw [mem_evenSet_iff, leaf_degree_one K hc]
  omega

omit [DecidableEq U] in
/-- The avoided vertex of a live tail is not a token. -/
theorem odd_not_mem_evenSet (K : SimpleGraph U) [DecidableRel K.Adj] {x : U}
    (hx : K.degree x % 2 = 1) : x ∉ evenSet K := by
  rw [mem_evenSet_iff]
  omega

omit [DecidableEq U] in
/-- A vertex with no edge lies on no path. -/
theorem not_mem_support_of_isolated (K : SimpleGraph U) [DecidableRel K.Adj] {c : U}
    (hc : K.degree c = 0) (P : GPath K) : c ∉ P.walk.support := fun h => by
  have := GPath.degree_pos_of_mem P h
  omega

/-! ### Invariants under the moves -/

omit [DecidableEq U] in
/-- A live tail stays live through a move. -/
theorem live_move (K : SimpleGraph U) [DecidableRel K.Adj] {T : Finset (U × U × U)}
    (hinv : TailInv T K) {p u : U} (hp : p ∈ evenSet K) (hoff : OffTails T K u)
    {t : U × U × U} (ht : t ∈ T) (hl : K.Adj t.1 t.2.1) : (delEdge K u p).Adj t.1 t.2.1 := by
  obtain ⟨hc, -, -⟩ := hinv t ht hl
  obtain ⟨huc, -⟩ := hoff t ht hl
  have hcp : t.1 ≠ p := fun h => leaf_not_mem_evenSet K hc (h ▸ hp)
  refine ⟨hl, ?_⟩
  rw [Sym2.eq_iff]
  rintro (⟨h1, -⟩ | ⟨h1, -⟩)
  · exact huc h1.symm
  · exact hcp h1

theorem tailInv_move (K : SimpleGraph U) [DecidableRel K.Adj] {T : Finset (U × U × U)}
    (hinv : TailInv T K) {p u : U} (hp : p ∈ evenSet K) (hpu : K.Adj p u)
    (hoff : OffTails T K u) : TailInv T (delEdge K u p) := by
  intro t ht hlive
  have hlK : K.Adj t.1 t.2.1 := hlive.1
  obtain ⟨hc, hx, hxw⟩ := hinv t ht hlK
  obtain ⟨-, hux⟩ := hoff t ht hlK
  have hxp : t.2.2 ≠ p := fun h => odd_not_mem_evenSet K hx (h ▸ hp)
  refine ⟨fun v => ⟨fun h => (hc v).mp h.1, fun h => by subst h; exact hlive⟩, ?_,
    fun h => hxw h.1⟩
  have h := delEdge_degree K hpu.symm t.2.2
  simp only [Ne.symm hux, hxp, ite_false, add_zero] at h
  rw [h]
  exact hx

omit [Fintype U] [DecidableEq U] in
/-- A live tail other than the dropped one stays live. -/
theorem live_drop {T : Finset (U × U × U)} (hT : TailSys T) (K : SimpleGraph U)
    {t₀ t : U × U × U} (ht₀ : t₀ ∈ T) (ht : t ∈ T) (htt : t ≠ t₀) (hl : K.Adj t.1 t.2.1) :
    (delEdge K t₀.1 t₀.2.1).Adj t.1 t.2.1 := by
  obtain ⟨hc1, hc2, -, -⟩ := hT.cross t₀ ht₀ t ht (Ne.symm htt)
  refine ⟨hl, ?_⟩
  rw [Sym2.eq_iff]
  rintro (⟨h1, -⟩ | ⟨h1, -⟩)
  · exact hc1 h1
  · exact hc2 h1

theorem tailInv_drop (K : SimpleGraph U) [DecidableRel K.Adj] {T : Finset (U × U × U)}
    (hT : TailSys T) (hinv : TailInv T K) {t₀ : U × U × U} (ht₀ : t₀ ∈ T)
    (hl₀ : K.Adj t₀.1 t₀.2.1) : TailInv T (delEdge K t₀.1 t₀.2.1) := by
  intro t ht hlive
  have hlK : K.Adj t.1 t.2.1 := hlive.1
  have htt : t ≠ t₀ := by
    rintro rfl
    exact hlive.2 rfl
  obtain ⟨-, -, hx1, hx2⟩ := hT.cross t₀ ht₀ t ht (Ne.symm htt)
  obtain ⟨hc, hx, hxw⟩ := hinv t ht hlK
  refine ⟨fun v => ⟨fun h => (hc v).mp h.1, fun h => by subst h; exact hlive⟩, ?_,
    fun h => hxw h.1⟩
  have h := delEdge_degree K hl₀ t.2.2
  simp only [hx1, hx2, ite_false, add_zero] at h
  rw [h]
  exact hx

omit [DecidableEq U] in
/-- A live tail stays live through a suppression. -/
theorem live_supp (K : SimpleGraph U) [DecidableRel K.Adj] {T : Finset (U × U × U)}
    (hinv : TailInv T K) {p a b : U} (hp : p ∈ evenSet K) (hok : SuppOK T K a b)
    {t : U × U × U} (ht : t ∈ T) (hl : K.Adj t.1 t.2.1) :
    (plusEdge (delEdge (delEdge K p a) p b) a b).Adj t.1 t.2.1 := by
  obtain ⟨hc, -, -⟩ := hinv t ht hl
  obtain ⟨hac, hbc, -⟩ := hok t ht
  have hcp : t.1 ≠ p := fun h => leaf_not_mem_evenSet K hc (h ▸ hp)
  refine Or.inl ⟨⟨hl, ?_⟩, ?_⟩
  · rw [Sym2.eq_iff]
    rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · exact hcp h1
    · exact hac h1.symm
  · rw [Sym2.eq_iff]
    rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · exact hcp h1
    · exact hbc h1.symm

theorem tailInv_supp (K : SimpleGraph U) [DecidableRel K.Adj] {T : Finset (U × U × U)}
    (hinv : TailInv T K) {p a b : U} (hp : p ∈ evenSet K)
    (hNg : ∀ v, K.Adj p v ↔ v = a ∨ v = b) (hab : a ≠ b) (hnadj : ¬ K.Adj a b)
    (hok : SuppOK T K a b) : TailInv T (plusEdge (delEdge (delEdge K p a) p b) a b) := by
  obtain ⟨hHw, -, -, hHadj, -⟩ := splitOff_facts hNg hab hnadj
  intro t ht hlive
  obtain ⟨hac, hbc, hxw'⟩ := hok t ht
  have hlK : K.Adj t.1 t.2.1 := by
    rcases hHadj _ _ hlive with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h, -, -⟩
    · exact absurd h1.symm hac
    · exact absurd h1.symm hbc
    · exact h
  obtain ⟨hc, hx, hxw⟩ := hinv t ht hlK
  obtain ⟨hn1, hn2⟩ := hxw' hlK
  have hxp : t.2.2 ≠ p := fun h => odd_not_mem_evenSet K hx (h ▸ hp)
  refine ⟨fun v => ⟨fun h => ?_, fun h => by subst h; exact hlive⟩, by rw [hHw _ hxp]; exact hx,
    fun h => ?_⟩
  · rcases hHadj _ _ h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h', -, -⟩
    · exact absurd h1.symm hac
    · exact absurd h1.symm hbc
    · exact (hc v).mp h'
  · rcases hHadj _ _ h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h', -, -⟩
    · exact hn1 ⟨h1.symm, h2.symm⟩
    · exact hn2 ⟨h2.symm, h1.symm⟩
    · exact hxw h'

theorem evenSet_supp (K : SimpleGraph U) [DecidableRel K.Adj] {p a b : U}
    (hNg : ∀ v, K.Adj p v ↔ v = a ∨ v = b) (hab : a ≠ b) (hnadj : ¬ K.Adj a b) :
    evenSet (plusEdge (delEdge (delEdge K p a) p b) a b) = (evenSet K).erase p := by
  obtain ⟨hHw, hHg, -, -, -⟩ := splitOff_facts hNg hab hnadj
  ext v
  rw [Finset.mem_erase, mem_evenSet_iff, mem_evenSet_iff]
  by_cases hvp : v = p
  · subst hvp
    rw [hHg]
    simp
  · rw [hHw v hvp]
    simp [hvp]

/-! ### The steps of the transfer -/

/-- **The move step.** -/
theorem tailGood_move (K : SimpleGraph U) [DecidableRel K.Adj] {T : Finset (U × U × U)}
    (hinv : TailInv T K) {p u : U} (hp : p ∈ evenSet K) (hpu : K.Adj p u) (hu : u ∉ evenSet K)
    (hoff : OffTails T K u) (hno : ∀ v ∈ evenSet K, v ≠ p → ¬ (delEdge K u p).Adj u v)
    (h' : TailGood T (delEdge K u p)) : TailGood T K := by
  obtain ⟨D', hD', hm'⟩ := h'
  obtain ⟨D, hD, hcov⟩ := fan_step_multi K hp hpu hu hno D' hD'
  refine ⟨D, hD, fun t ht hl => meetsOnce_of_cover ?_ (hm' t ht (live_move K hinv hp hoff ht hl))
    hcov⟩
  obtain ⟨huc, hux⟩ := hoff t ht hl
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨huc, hux⟩

/-- **The drop step** (manuscript Lemma 2.5(b)): if the stem `w` of a live tail `(c, w, x)` is odd,
a good decomposition of `K − cw` plus the one-edge path `cw` is good for `K`. -/
theorem tailGood_drop (K : SimpleGraph U) [DecidableRel K.Adj] {T : Finset (U × U × U)}
    (hT : TailSys T) (hinv : TailInv T K) {t₀ : U × U × U} (ht₀ : t₀ ∈ T)
    (hl₀ : K.Adj t₀.1 t₀.2.1) (hw : t₀.2.1 ∉ evenSet K)
    (h' : TailGood T (delEdge K t₀.1 t₀.2.1)) : TailGood T K := by
  obtain ⟨D', hD', hm'⟩ := h'
  obtain ⟨hc₀, -, -⟩ := hinv t₀ ht₀ hl₀
  have hne : t₀.1 ≠ t₀.2.1 := hl₀.ne
  have hdeg := delEdge_degree K hl₀
  obtain ⟨D, hD, hcov⟩ := PathDecomp.add_edge_supp hl₀ (delEdge_edgeSet K t₀.1 t₀.2.1) D'
  have hcdeg := leaf_degree_one K hc₀
  have hwpos : 0 < K.degree t₀.2.1 := (K.degree_pos_iff_exists_adj _).mpr ⟨t₀.1, hl₀.symm⟩
  have hwodd : K.degree t₀.2.1 % 2 = 1 := by rw [mem_evenSet_iff] at hw; omega
  have hc0 : (delEdge K t₀.1 t₀.2.1).degree t₀.1 = 0 := by
    have h := hdeg t₀.1
    simp only [hne, ite_true, ite_false, add_zero] at h
    omega
  refine ⟨D, fun v => ?_, fun t ht hl => ?_⟩
  · rw [hD v, hD' v]
    have h := hdeg v
    by_cases hvc : v = t₀.1
    · rw [hvc, hc0, hcdeg]
      simp [Ne.symm hne]
    · by_cases hvw : v = t₀.2.1
      · rw [hvw] at h ⊢
        simp only [hne, Ne.symm hne, ite_true, ite_false, add_zero] at h ⊢
        omega
      · simp only [hvc, hvw, Ne.symm hvc, Ne.symm hvw, ite_false, add_zero] at h ⊢
        rw [h]
  · intro Q hQ a ha b hb haQ hbQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    by_cases htt : t = t₀
    · subst htt
      have hxc := hT.xc t ht
      have hxw := hT.xw t ht
      rcases hcov Q hQ with hsub | ⟨Q', hQ', hsub⟩
      · -- `Q` is the edge `cw`: it does not contain `x`
        have hnx : t.2.2 ∉ Q.walk.support := fun h => by
          rcases hsub _ h with h | h
          · exact hxc h
          · exact hxw h
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · rfl
        · exact absurd hbQ hnx
        · exact absurd haQ hnx
        · rfl
      · -- `c` is isolated in `K − cw`, so `Q` does not contain `c`
        have hnc : t.1 ∉ Q.walk.support := fun h =>
          not_mem_support_of_isolated _ hc0 Q' (hsub _ h)
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · rfl
        · exact absurd haQ hnc
        · exact absurd hbQ hnc
        · rfl
    · obtain ⟨hc1, hc2, hx1, hx2⟩ := hT.cross t₀ ht₀ t ht (Ne.symm htt)
      rcases hcov Q hQ with hsub | ⟨Q', hQ', hsub⟩
      · exfalso
        rcases ha with rfl | rfl
        · rcases hsub _ haQ with h | h
          · exact hc1 h
          · exact hc2 h
        · rcases hsub _ haQ with h | h
          · exact hx1 h
          · exact hx2 h
      · have hl' := live_drop hT K ht₀ ht htt hl
        exact hm' t ht hl' Q' hQ' a (by simp only [Finset.mem_insert, Finset.mem_singleton]; exact ha)
          b (by simp only [Finset.mem_insert, Finset.mem_singleton]; exact hb) (hsub a haQ)
          (hsub b hbQ)

/-- **Subdividing back** (the cover form of `avoid_of_splitOff`). Let `N(g) = {a, b}` with
`ab ∉ E`. A decomposition of `G − ga − gb + ab` gives one of `G` with the same ends, every path of
which lies in an old path plus `g`. -/
theorem splitOff_supp {G : SimpleGraph U} [DecidableRel G.Adj] {g a b : U}
    (hNg : ∀ v, G.Adj g v ↔ v = a ∨ v = b) (hab : a ≠ b) (hnadj : ¬ G.Adj a b)
    (DH : PathDecomp (plusEdge (delEdge (delEdge G g a) g b) a b)) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = DH.ends v) ∧
      ∀ Q ∈ D.paths, ∃ Q' ∈ DH.paths, ∀ x ∈ Q.walk.support, x ∈ Q'.walk.support ∨ x = g := by
  classical
  obtain ⟨-, hHg, hHab, -, hval⟩ := splitOff_facts hNg hab hnadj
  have hga : G.Adj g a := (hNg a).mpr (Or.inl rfl)
  have hgb : G.Adj g b := (hNg b).mpr (Or.inr rfl)
  have hgA' : g ≠ a := hga.ne
  have hgB' : g ≠ b := hgb.ne
  obtain ⟨R, hR, habR⟩ : ∃ R ∈ DH.paths, s(a, b) ∈ R.edges :=
    List.mem_flatMap.mp ((DH.covers _).mp hHab)
  have hgR : g ∉ R.walk.support := fun h => by
    have := GPath.degree_pos_of_mem R h; omega
  have haR : a ∈ R.walk.support := Walk.fst_mem_support_of_mem_edges _ habR
  have hbR : b ∈ R.walk.support := Walk.snd_mem_support_of_mem_edges _ habR
  let Tp : TPath U := ⟨a, b, Walk.cons (show (⊤ : SimpleGraph U).Adj a g from by
      simpa using Ne.symm hgA')
      (Walk.cons (show (⊤ : SimpleGraph U).Adj g b from by simpa using hgB') Walk.nil),
    by
      rw [Walk.isPath_def]
      simp [Ne.symm hgA', hab, hgB'],
    by simp⟩
  have hTe : Tp.edges = [s(a, g), s(g, b)] := rfl
  obtain ⟨R', hR's, hR't, hR'e, hR'supp⟩ := exists_subst_path R.toTop Tp (by simpa using habR)
    rfl rfl (by
      intro w hw hwR
      simp only [Tp, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact Or.inl rfl
      · rw [GPath.toTop_support] at hwR
        exact absurd hwR hgR
      · exact Or.inr rfl)
  set rest := DH.paths.erase R with hrest
  have hperm : DH.paths.Perm (R :: rest) := List.perm_cons_erase hR
  let L' : List (TPath U) := R' :: rest.map GPath.toTop
  have hEL : edgesM L' = G.edgeFinset.val := by
    have h1 : edgesM L' + {s(a, b)} =
        (plusEdge (delEdge (delEdge G g a) g b) a b).edgeFinset.val + Tp.edges := by
      rw [← DH.edgesM_toTop, edgesM_perm (hperm.map GPath.toTop)]
      simp only [L', edgesM_cons, List.map_cons]
      rw [add_right_comm, hR'e]
      simp only [GPath.toTop_edges]
      abel
    have h2 : (Tp.edges : Multiset (Sym2 U)) = {s(g, a)} + {s(g, b)} := by
      rw [hTe, Sym2.eq_swap (a := a)]
      rfl
    rw [h2, ← hval] at h1
    exact add_right_cancel h1
  have hendL : ∀ v, endsL L' v = DH.ends v := by
    intro v
    rw [← DH.endsL_toTop, endsL_perm (hperm.map GPath.toTop)]
    simp only [L', endsL_cons, List.map_cons, GPath.toTop_endsAt]
    unfold GPath.endsAt
    rw [hR's, hR't]
    rfl
  obtain ⟨D, hDe, hDp⟩ := exists_decomp_of_edgesM' (G := G) L' hEL
  refine ⟨D, fun v => by rw [hDe v, hendL v], fun Q hQ => ?_⟩
  obtain ⟨T', hT', hTs, hTt, hTsupp⟩ := hDp Q hQ
  simp only [L', List.mem_cons, List.mem_map] at hT'
  rcases hT' with rfl | ⟨R₀, hR₀, rfl⟩
  · refine ⟨R, hR, fun x hxQ => ?_⟩
    rw [hTsupp] at hxQ
    rcases hR'supp x hxQ with h | h
    · rw [GPath.toTop_support] at h
      exact Or.inl h
    · simp only [Tp, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at h
      rcases h with rfl | rfl | rfl
      · exact Or.inl haR
      · exact Or.inr rfl
      · exact Or.inl hbR
  · refine ⟨R₀, List.mem_of_mem_erase hR₀, fun x hxQ => Or.inl ?_⟩
    rw [hTsupp, GPath.toTop_support] at hxQ
    exact hxQ

/-- **The suppression step.** -/
theorem tailGood_supp (K : SimpleGraph U) [DecidableRel K.Adj] {T : Finset (U × U × U)}
    (hinv : TailInv T K) {p a b : U} (hp : p ∈ evenSet K)
    (hNg : ∀ v, K.Adj p v ↔ v = a ∨ v = b) (hab : a ≠ b) (hnadj : ¬ K.Adj a b)
    (hok : SuppOK T K a b) (h' : TailGood T (plusEdge (delEdge (delEdge K p a) p b) a b)) :
    TailGood T K := by
  obtain ⟨hHw, hHg, -, -, -⟩ := splitOff_facts hNg hab hnadj
  obtain ⟨DH, hDH, hm'⟩ := h'
  obtain ⟨D, hD, hcov⟩ := splitOff_supp hNg hab hnadj DH
  have hpd := mem_evenSet_iff.mp hp
  refine ⟨D, fun v => ?_, fun t ht hl => meetsOnce_of_cover ?_
    (hm' t ht (live_supp K hinv hp hok ht hl)) hcov⟩
  · rw [hD v, hDH v]
    by_cases hvp : v = p
    · subst hvp
      rw [hHg]
      omega
    · rw [hHw v hvp]
  · obtain ⟨hc, hx, -⟩ := hinv t ht hl
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => leaf_not_mem_evenSet K hc (h ▸ hp), fun h => odd_not_mem_evenSet K hx (h ▸ hp)⟩

/-- **The multi-tail leaf lemma** (manuscript Lemma 2.6). Let `K` have at most one even vertex,
and let at most one tail be live. Then `K` has a parity decomposition in which no path contains
both the leaf and the avoided vertex of a live tail. (With no live tail this is Lovász's theorem;
with one, it is the leaf-tail lemma `avoid_leafTail`; the even vertex may be the stem.) -/
theorem tailGood_fin (K : SimpleGraph U) [DecidableRel K.Adj] {T : Finset (U × U × U)}
    (hT : TailSys T) (hinv : TailInv T K) (hev : (evenSet K).card ≤ 1) (h1 : OneLive T K) :
    TailGood T K := by
  by_cases hex : ∃ t ∈ T, K.Adj t.1 t.2.1
  · obtain ⟨t, ht, hl⟩ := hex
    obtain ⟨hc, hx, hxw⟩ := hinv t ht hl
    obtain ⟨D, hD, hav⟩ := avoid_leafTail K hev hc hx (hT.xc t ht) (hT.xw t ht) hxw
    refine ⟨D, hD, fun t' ht' hl' => ?_⟩
    obtain rfl := h1 t ht t' ht' hl hl'
    have hpend : ∀ e ∈ K.edgeSet, t.1 ∈ e → e = s(t.1, t.2.1) := by
      intro e he hce
      induction e using Sym2.inductionOn with
      | hf p q =>
        rw [mem_edgeSet] at he
        rcases Sym2.mem_iff.mp hce with rfl | rfl
        · rw [(hc q).mp he]
        · rw [(hc p).mp he.symm, Sym2.eq_swap]
    intro P hP a ha b hb haP hbP
    have key : t.1 ∈ P.walk.support → t.2.2 ∉ P.walk.support := fun hcP hxP =>
      hav P hP (P.end_of_pendant hpend hcP) t.2.2 (Finset.mem_singleton_self _) hxP
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact absurd hbP (key haP)
    · exact absurd haP (key hbP)
    · rfl
  · push Not at hex
    obtain ⟨D, hD⟩ := lovasz_ends K hev
    exact ⟨D, hD, fun t ht hl => absurd hl (hex t ht)⟩


/-! ### The transfer theorem -/

/-- **The transfer theorem** (manuscript Theorem 2.7). If `T` satisfies the static conditions, the
live tails of `K` satisfy the invariant, and `K` has a `k`-token schedule from its even set, then `K`
has a parity decomposition in which no path contains both the leaf and the avoided vertex of a
live tail. -/
theorem steerK_good {T : Finset (U × U × U)} (hT : TailSys T) :
    ∀ {K : SimpleGraph U} {τ : Finset U}, SteerK T K τ → ∀ [DecidableRel K.Adj],
      evenSet K = τ → TailInv T K → TailGood T K := by
  intro K τ hS
  induction hS with
  | fin hτ h1 =>
    intro _ hE hinv
    exact tailGood_fin _ hT hinv (hE ▸ hτ) h1
  | @move K τ τ' p u hp hpu hu hoff hno hτ' _ ih =>
    intro _ hE hinv
    subst hE
    exact tailGood_move K hinv hp hpu hu hoff hno
      (ih (evenSet_move K hp hpu hu hτ') (tailInv_move K hinv hp hpu hoff))
  | @drop K τ τ' t ht hl hw hτ' _ ih =>
    intro _ hE hinv
    subst hE
    obtain ⟨hc, -, -⟩ := hinv t ht hl
    exact tailGood_drop K hT hinv ht hl hw
      (ih (evenSet_drop K hl hc hw hτ') (tailInv_drop K hT hinv ht hl))
  | @supp K τ p a b hp hNg hab hnadj hok _ ih =>
    intro _ hE hinv
    subst hE
    exact tailGood_supp K hinv hp hNg hab hnadj hok
      (ih (evenSet_supp K hNg hab hnadj) (tailInv_supp K hinv hp hNg hab hnadj hok))

end tokens

/-! ### The triangle base -/

section triangle

variable {V : Type u} [Fintype V] [DecidableEq V] {J : SimpleGraph V} [DecidableRel J.Adj]
  {z r w : V} {L : List (V × V)}

/-- The vertices `yᵢ` that carry the leaves: the second components of the oriented pairs. -/
def leafSet (L : List (V × V)) : Finset V := (L.map Prod.snd).toFinset

/-- The tails `(ℓᵢ, yᵢ, xᵢ)` of the oriented pairs `(xᵢ, yᵢ)` of `L`, in `leaves M Y` on `V ⊕ V`,
with `ℓᵢ = inr yᵢ`. -/
def triTails (L : List (V × V)) : Finset ((V ⊕ V) × (V ⊕ V) × (V ⊕ V)) :=
  (L.map (fun p => ((Sum.inr p.2 : V ⊕ V), (Sum.inl p.2 : V ⊕ V), (Sum.inl p.1 : V ⊕ V)))).toFinset

/-- **The leaf graph** `M⁺ = M + {yᵢℓᵢ}` (manuscript §3). -/
abbrev triLeaf (J : SimpleGraph V) (z w : V) (L : List (V × V)) : SimpleGraph (V ⊕ V) :=
  leaves (triM J z w L) (leafSet L)

omit [Fintype V] in
theorem mem_triTails {t : (V ⊕ V) × (V ⊕ V) × (V ⊕ V)} :
    t ∈ triTails L ↔ ∃ p ∈ L, t = (Sum.inr p.2, Sum.inl p.2, Sum.inl p.1) := by
  rw [triTails, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩

omit [Fintype V] in
theorem mem_leafSet {y : V} : y ∈ leafSet L ↔ ∃ p ∈ L, p.2 = y := by
  rw [leafSet, List.mem_toFinset, List.mem_map]

omit [Fintype V] in
/-- The tails of a matching satisfy the static conditions. -/
theorem triTails_sys (hnd : (pairVerts L).Nodup) : TailSys (triTails L) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨p, -, rfl⟩ := mem_triTails.mp ht
    simp
  · intro t ht
    obtain ⟨p, hp, rfl⟩ := mem_triTails.mp ht
    simp only [ne_eq, Sum.inl.injEq]
    exact fst_ne_snd hnd hp
  · intro t ht t' ht' htt
    obtain ⟨p, hp, rfl⟩ := mem_triTails.mp ht
    obtain ⟨q, hq, rfl⟩ := mem_triTails.mp ht'
    have hpq : p ≠ q := by
      rintro rfl
      exact htt rfl
    refine ⟨?_, by simp, by simp, ?_⟩
    · simp only [ne_eq, Sum.inr.injEq]
      intro h
      exact hpq (pair_eq_of_share hnd hp hq (Or.inr h) (Or.inr rfl))
    · simp only [ne_eq, Sum.inl.injEq]
      intro h
      exact hpq (pair_eq_of_share hnd hp hq (Or.inr h) (Or.inl rfl))

omit [Fintype V] in
/-- No `xᵢ` carries a leaf. -/
theorem fst_not_mem_leafSet (hnd : (pairVerts L).Nodup) {p : V × V} (hp : p ∈ L) :
    p.1 ∉ leafSet L := by
  intro h
  obtain ⟨q, hq, hqp⟩ := mem_leafSet.mp h
  have := pair_eq_of_share hnd hq hp (Or.inr rfl) (Or.inl hqp)
  subst this
  exact fst_ne_snd hnd hq hqp.symm

/-- The tails of triangle data satisfy the invariant in `M⁺`. -/
theorem triTails_inv (hz : ∀ v, Even (J.degree v) ↔ v = z) (hD : TriangleData J z r w L) :
    TailInv (triTails L) (triLeaf J z w L) := by
  obtain ⟨-, -, -, -, -, hwL, hnd⟩ := hD.facts
  have hpar := hD.triM_parity hz
  intro t ht _
  obtain ⟨p, hp, rfl⟩ := mem_triTails.mp ht
  have hp2Y : p.2 ∈ leafSet L := mem_leafSet.mpr ⟨p, hp, rfl⟩
  have hw1 : p.1 ≠ w := fun h => hwL (h ▸ fst_mem_pairVerts hp)
  refine ⟨fun v => ?_, ?_, ?_⟩
  · cases v with
    | inl b =>
      simp only [leaves_adj_inr_inl, Sum.inl.injEq]
      constructor
      · rintro ⟨h, -⟩
        exact h.symm
      · rintro rfl
        exact ⟨rfl, hp2Y⟩
    | inr b => simp
  · rw [leaves_degree_inl, ite_eq_right (fst_not_mem_leafSet hnd hp), add_zero, hpar, ite_eq_right hw1]
  · simp only [leaves_adj_inl_inl]
    exact hD.triM_not_adj hp

/-- **A schedule gives a triangle base** (manuscript Theorem 3.1). Let `(J, z, r, w, L)` be triangle
data, `z` the only even vertex of `J`, and orient each pair of `L` as `(xᵢ, yᵢ)`. If the leaf graph
`M⁺` has a `k`-token schedule from its even set, with the tails `(ℓᵢ, yᵢ, xᵢ)`, then some Lovász
decomposition of `M` has, for every `i`, the path ending at `yᵢ` avoiding `xᵢ`; so `J` has a
triangle base at `r`. The statement exported is the last clause, `TriangleBase J z r`; the first is
proved inside (the disjunct `Or.inl` for every pair). -/
theorem triangleBase_of_steerK (hz : ∀ v, Even (J.degree v) ↔ v = z)
    (hD : TriangleData J z r w L)
    (hS : SteerK (triTails L) (triLeaf J z w L) (evenSet (triLeaf J z w L))) :
    TriangleBase J z r := by
  obtain ⟨-, -, -, -, -, hwL, hnd⟩ := hD.facts
  have hpar := hD.triM_parity hz
  obtain ⟨DH, hDH, hm⟩ := steerK_good (triTails_sys hnd) hS rfl (triTails_inv hz hD)
  obtain ⟨D, hD', hcov⟩ := (leavesRetract (triM J z w L) (leafSet L)).delete_supp DH (by
    intro P _ x hx hkx
    cases x with
    | inl _ => simp [leavesRetract] at hkx
    | inr y => exact (P.end_of_pendant (leaves_inr_pendant y) hx).imp Eq.symm Eq.symm)
  -- the end counts of `DH` at the leaf-bearers
  have hDHy : ∀ y ∈ leafSet L, DH.ends (Sum.inl y) = 0 := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := mem_leafSet.mp hy
    have hw2 : p.2 ≠ w := fun h => hwL (h ▸ snd_mem_pairVerts hp)
    rw [hDH, leaves_degree_inl, ite_eq_left hy]
    have := hpar p.2
    rw [ite_eq_right hw2] at this
    omega
  refine ⟨w, L, hD, D, fun v => ?_, fun p hp => Or.inl ?_⟩
  · by_cases hvY : v ∈ leafSet L
    · have hle := (hD' v).2 (fun e₁ he₁ e₂ he₂ hk₁ hk₂ hv₁ hv₂ => by
        rw [(leaves_nonkept he₁ hk₁ hv₁).1, (leaves_nonkept he₂ hk₂ hv₂).1])
      change D.ends v ≤ DH.ends (Sum.inl v) + 1 at hle
      rw [hDHy v hvY] at hle
      have hp2 := D.ends_mod_two v
      obtain ⟨p, hp, rfl⟩ := mem_leafSet.mp hvY
      have hw2 : p.2 ≠ w := fun h => hwL (h ▸ snd_mem_pairVerts hp)
      have := hpar p.2
      rw [ite_eq_right hw2] at this
      rw [this] at hp2 ⊢
      omega
    · rw [(hD' v).1 (fun e he hk hve => hvY (leaves_nonkept he hk hve).2)]
      change DH.ends (Sum.inl v) = _
      rw [hDH, leaves_degree_inl, ite_eq_right hvY, add_zero]
  · intro Q hQ hend hxQ
    obtain ⟨P, hP, hPs, hperm⟩ := hcov Q hQ
    have hxP : (Sum.inl p.1 : V ⊕ V) ∈ P.walk.support := hPs _ hxQ
    have ht : ((Sum.inr p.2 : V ⊕ V), (Sum.inl p.2 : V ⊕ V), (Sum.inl p.1 : V ⊕ V)) ∈
        triTails L := mem_triTails.mpr ⟨p, hp, rfl⟩
    have hp2Y : p.2 ∈ leafSet L := mem_leafSet.mpr ⟨p, hp, rfl⟩
    have hlive : (triLeaf J z w L).Adj (Sum.inr p.2) (Sum.inl p.2) := ⟨rfl, hp2Y⟩
    have hnl : (Sum.inr p.2 : V ⊕ V) ∉ P.walk.support := fun h =>
      Sum.inr_ne_inl (hm _ ht hlive P hP _ (by simp) _ (by simp) h hxP)
    -- `P` has exactly the edges of `Q` at `p.2`
    have hQinc : Q.incid p.2 = 1 := by
      have h := Q.endsAt_eq_ite p.2
      have h1 : 1 ≤ Q.endsAt p.2 := by
        unfold GPath.endsAt
        rcases hend with h' | h' <;> simp [h']
      split_ifs at h with hh
      · exact hh
      · omega
    have hk0 : (P.edges.filter (fun e => !bothKept (leavesRetract (triM J z w L) (leafSet L)).kept
        e)).countP (fun e => decide ((leavesRetract (triM J z w L) (leafSet L)).ι p.2 ∈ e)) = 0 := by
      rw [List.countP_eq_zero]
      intro e he hpe
      rw [List.mem_filter] at he
      have heE : e ∈ (triLeaf J z w L).edgeSet := P.walk.edges_subset_edgeSet he.1
      have hk : bothKept Sum.isLeft e = false := by
        have := he.2
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at this
        exact this
      have hpe' : (Sum.inl p.2 : V ⊕ V) ∈ e := of_decide_eq_true hpe
      obtain ⟨rfl, -⟩ := leaves_nonkept heE hk hpe'
      exact hnl (Walk.snd_mem_support_of_mem_edges _ he.1)
    have hPinc : P.incid (Sum.inl p.2) = 1 := by
      have hs := (leavesRetract (triM J z w L) (leafSet L)).count_split p.2 P.edges
      rw [hk0, add_zero] at hs
      have hc : (P.edges.filter (bothKept (leavesRetract (triM J z w L) (leafSet L)).kept)).countP
          (fun e => decide (p.2 ∈ e.map (leavesRetract (triM J z w L) (leafSet L)).f)) =
          Q.incid p.2 := by
        unfold GPath.incid
        rw [hperm.countP_eq, List.countP_map]
        rfl
      rw [hc, hQinc] at hs
      unfold GPath.incid
      exact hs.symm
    have hPend : P.endsAt (Sum.inl p.2) = 1 := by rw [P.endsAt_eq_ite, hPinc]; rfl
    have hle : P.endsAt (Sum.inl p.2) ≤ DH.ends (Sum.inl p.2) := by
      unfold PathDecomp.ends
      exact List.le_sum_of_mem (List.mem_map_of_mem hP)
    rw [hDHy p.2 hp2Y] at hle
    omega

/-- **Test1 from a schedule** (manuscript Corollary 3.2). -/
theorem test1At_of_steerK (hz : ∀ v, Even (J.degree v) ↔ v = z) (hr3 : 3 ≤ J.degree r)
    (hD : TriangleData J z r w L)
    (hS : SteerK (triTails L) (triLeaf J z w L) (evenSet (triLeaf J z w L))) :
    Test1At J z r :=
  test1At_of_triangleBase J hz hr3 (triangleBase_of_steerK hz hD hS)

end triangle

end Gallai
