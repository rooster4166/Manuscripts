import GallaiLean.TightFan

/-!
# Lovász's induction for `L₁*`: the transfer calculus and a two-sided reduction of `L1Blocked`

Manuscript `manuscripts/l1-induction/l1-induction.tex`.

Lovász's Case I step for `L₁*` deletes an edge `gx` at the even vertex `g`, decomposes `G − gx`
(where `x` is now the even vertex) and restores `gx` by Fan's lemma.  It has two sides.

* **Hypothesis side.** The induction hypothesis must supply a decomposition of `G − gx` whose path
  ending at `c` avoids `A`.  In a blocked instance `(G − gx, c, A)` is never admissible.
* **Transfer side.** The Fan transfer must keep the path ending at `c` off `A`.  This is automatic
  when `x ∉ N(c)` (`avoid_of_target_child`), and is the tight case of `manuscripts/tight-fan` when
  `x ∈ N(c)`.

The point of this file is that the Case I transfers themselves never need admissibility: the two
Case I reductions `l1_case_target` and `l1_case_target_adj` of `L1Star.lean` are re-proved here as
*unconditional* transfers of goodness from the smaller instance to the larger one.  Admissibility
is used only to invoke the induction hypothesis.  (The reductions `l1_case_adj` and `l1_case_big` are
not re-proved here; the manuscript treats them on paper.)

* `avoid_of_target_child`: `x ∈ N(g) ∖ N(c)`, `x ∉ A`, and `(G − gx, c, A)` good ⇒ `(G, c, A)`
  good.  (No condition on `A ∩ N(x)`.)
* `avoid_of_target_adj_child`: `x ∈ N(g) ∩ N(c)`, `c, x ∉ A`, and `(G − xc − gx, x, A ∪ {c})` good
  ⇒ `(G, c, A)` good.
* `TightTransfer` (**TR**, conjecture): for a tight target `x ∈ N(g) ∩ N(c)` and any `A` missing
  `N[c] ∪ {x}`, goodness of `(G − gx, c, A)` implies goodness of `(G, c, A)`.  (Exhaustive to order
  9 in the manuscript; it fails if `A` may meet `N(c)`.)
* `SomeTarget` (**ST**, conjecture): every blocked instance has a target `x ∈ N(g)` with
  `(G − gx, c, A)` good.  (Exhaustive to order 9, every admissible `A`.)
* `SomeTargetLocal` (**ST′**): the same with the instance-level children only (`(G − gx, c, A)` for
  `x ∉ N(c)`, `(G − xc − gx, x, A ∪ {c})` for `x ∈ N(c)`).  It would need no transfer conjecture,
  but it is **false**: the manuscript gives a counterexample of order 7.
* `l1Blocked_of_someTarget : TightTransfer → SomeTarget → L1Blocked`, and hence `L1StarGen`,
  `L1Star`, EE and L∞ (`l1starGen_of_ST_TR`, `l1star_of_ST_TR`, `ee_of_ST_TR`, `lInfty_of_ST_TR`).
* `l1Blocked_of_someTargetLocal : SomeTargetLocal → L1Blocked` (recorded for completeness).
* `TightTransferAdm`: TR for admissible blocked instances only.  This is all that
  `l1Blocked_of_someTarget` uses, and it follows from `L1Blocked` itself
  (`tightTransferAdm_of_l1Blocked`).  Hence, given `SomeTarget`, `L1Blocked ↔ TightTransferAdm`
  (`l1Blocked_iff_tightTransferAdm`): `ST` is the substantive half of the reduction.
* `SomeTargetOut` (**ST_out**): a blocked instance with a non-tight target has a *non-tight*
  target `x` with `(G − gx, c, A)` good; `L1BlockedTight`: `L1Blocked` restricted to
  `N(g) ⊆ N(c)`.  `l1Blocked_of_out_tight : SomeTargetOut → L1BlockedTight → L1Blocked`, and
  `l1BlockedTight_of_ST_TR`.  So the transfer conjecture is needed only when every target is tight.
-/

open SimpleGraph

namespace Gallai

universe u

variable {W : Type u} [Fintype W] [DecidableEq W]

section transfer

/-- **Case I with a non-tight target transfers goodness unconditionally.** Let `g` be the even vertex,
`c ∉ N(g)` odd, `x ∈ N(g) ∖ N(c)` with `x ∉ A`.  If `G − gx` has a Lovász decomposition whose path
ending at `c` avoids `A`, so does `G`.  (Hang a leaf at `c`, restore `gx` by Fan's lemma with vertex
sets, delete the leaf.)  No admissibility of `(G − gx, c, A)` is assumed. -/
theorem avoid_of_target_child (G : SimpleGraph W) [DecidableRel G.Adj]
    (hev : (evenSet G).card ≤ 1)
    {g c x : W} (hg : g ∈ evenSet G) (hgc : ¬ G.Adj g c) (hgx : G.Adj g x) (hcx : ¬ G.Adj c x)
    (hc : G.degree c % 2 = 1) {A : Finset W} (hxA : x ∉ A)
    (hchild : AvoidDecomp (delEdge G g x) c A) : AvoidDecomp G c A := by
  classical
  have hgx' : g ≠ x := hgx.ne
  have huniq : ∀ v ∈ evenSet G, v = g := fun v hv => Finset.card_le_one.mp hev v hv g hg
  have hodd : ∀ v, v ≠ g → 0 < G.degree v → G.degree v % 2 = 1 := by
    intro v hvg hpos
    have : v ∉ evenSet G := fun h => hvg (huniq v h)
    rw [mem_evenSet_iff] at this
    omega
  have hgd := mem_evenSet_iff.mp hg
  have hcg : c ≠ g := fun h => by rw [h] at hc; omega
  have hcx' : c ≠ x := fun h => hgc (h ▸ hgx)
  have hdeg := delEdge_degree G hgx
  have hc' : (delEdge G g x).degree c % 2 = 1 := by
    have h := hdeg c; simp only [hcg, hcx', ite_false, add_zero] at h; omega
  obtain ⟨D', hD', hav'⟩ := hchild
  have hD'c : D'.ends c = 1 := by rw [hD']; exact hc'
  obtain ⟨P, hP, hPend⟩ := D'.exists_end_of_pos (by rw [hD'c]; omega)
  have hPav := hav' P hP hPend
  obtain ⟨D₃, hD₃some, hD₃none, hD₃cov⟩ := D'.liftLeaf hP hPend
  have hsep₃ : ∀ Q' ∈ D₃.paths, (none : Option W) ∈ Q'.walk.support →
      ∀ a ∈ A, some a ∉ Q'.walk.support := by
    intro Q' hQ' hn a ha hx
    rcases hD₃cov Q' hQ' with h | ⟨Q, hQ, hs⟩
    · rcases h (some a) hx with h | ⟨y', hy', h⟩
      · exact Option.some_ne_none _ h
      · rw [Option.some.injEq] at h
        subst h
        exact hPav _ ha hy'
    · rw [hs, List.mem_map] at hn
      obtain ⟨_, _, h⟩ := hn
      exact Option.some_ne_none _ h
  -- Fan's lemma in `apex G {c}`: restore `gx`, moving the end at `g` to `x`
  have hK : (apex G {c}).Adj (some x) (some g) := by
    rw [apex_adj_some_some]; exact hgx.symm
  have hD₃g : D₃.ends (some g) = 1 := by
    have h := hD₃some g
    simp only [hcg.symm, ite_false, add_zero] at h
    rw [h, hD']
    have := hdeg g
    simp only [hgx', ite_true, ite_false] at this
    omega
  have hcount : (Finset.univ.filter (fun v => (apex (delEdge G g x) {c}).Adj (some x) v ∧
      D₃.ends v = 0)).card < D₃.ends (some g) := by
    have hempty : Finset.univ.filter (fun v => (apex (delEdge G g x) {c}).Adj (some x) v ∧
        D₃.ends v = 0) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
      rw [Finset.mem_filter] at hv
      obtain ⟨-, hadj, h0⟩ := hv
      cases v with
      | none =>
        rw [apex_adj_some_none, Finset.mem_singleton] at hadj
        exact hcx' hadj.symm
      | some w =>
        rw [apex_adj_some_some] at hadj
        have hwc : w ≠ c := fun h => hcx (h ▸ hadj.1.symm)
        have hwg : w ≠ g := fun h => hadj.2 (by rw [h, Sym2.eq_swap])
        have hwx : w ≠ x := hadj.ne.symm
        have h := hD₃some w
        simp only [hwc, ite_false, add_zero] at h
        rw [h, hD'] at h0
        have hdw := hdeg w
        simp only [hwg, hwx, ite_false, add_zero] at hdw
        have := hodd w hwg ((G.degree_pos_iff_exists_adj w).mpr ⟨x, hadj.1.symm⟩)
        omega
    rw [hempty, Finset.card_empty, hD₃g]
    omega
  obtain ⟨DH, -, hDHx, hDHg, hDHrest, hcovH⟩ :=
    fan_single_supp (G := apex G {c}) hK (apex_delEdge_edge_iff G {c} g x) D₃ hcount
  have hsepH : ∀ Q ∈ DH.paths, (none : Option W) ∈ Q.walk.support →
      ∀ a ∈ A, some a ∉ Q.walk.support := by
    intro Q hQ hn a ha hx
    obtain ⟨Q', hQ', hsub⟩ := hcovH Q hQ
    have hn' : (none : Option W) ∈ Q'.walk.support :=
      (hsub none hn).resolve_right (by simp)
    rcases hsub (some a) hx with h | h
    · exact hsep₃ Q' hQ' hn' a ha h
    · rw [Option.some.injEq] at h
      exact hxA (by rw [← h]; exact ha)
  refine avoid_of_apexSep G hc DH (fun w hwc => ?_) ?_ hsepH
  · by_cases hwx : w = x
    · subst hwx
      rw [hDHx]
      have h := hD₃some w
      simp only [hwc, ite_false, add_zero] at h
      rw [h, hD']
      have := hdeg w
      simp only [hgx'.symm, ite_true, ite_false] at this
      have := hodd w hgx'.symm ((G.degree_pos_iff_exists_adj w).mpr ⟨g, hgx.symm⟩)
      omega
    · by_cases hwg : w = g
      · subst hwg
        rw [hD₃g] at hDHg
        have : DH.ends (some w) = 0 := by omega
        rw [this, hgd.2]
      · rw [hDHrest (some w) (by simp [hwx]) (by simp [hwg])]
        have h := hD₃some w
        simp only [hwc, ite_false, add_zero] at h
        rw [h, hD']
        have := hdeg w
        simp only [hwg, hwx, ite_false, add_zero] at this
        rw [this]
  · rw [hDHrest (some c) (by simp [hcx']) (by simp [hcg])]
    have h := hD₃some c
    simp only [ite_true] at h
    rw [hD'c] at h
    omega

/-- **The `(c)`-move transfers goodness unconditionally.** Let `g` be the even vertex, `c ∉ N(g)` odd
and `x ∈ N(g) ∩ N(c)`, with `c, x ∉ A`.  If `G − xc − gx` (where `c` is the even vertex) has a
Lovász decomposition whose path ending at `x` avoids `A ∪ {c}`, then `G` has a Lovász decomposition
whose path ending at `c` avoids `A`.  (Lift to the leaf graph at `x`, where the leaf stands for `c`;
restore `gx` by Fan's lemma; merge.)  No admissibility is assumed. -/
theorem avoid_of_target_adj_child (G : SimpleGraph W)
    [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1)
    {g c x : W} (hg : g ∈ evenSet G) (hgc : ¬ G.Adj g c) (hgx : G.Adj g x) (hcx : G.Adj c x)
    (hc : G.degree c % 2 = 1) {A : Finset W} (hcA : c ∉ A) (hxA : x ∉ A)
    (hchild : AvoidDecomp (delEdge (delEdge G x c) g x) x (insert c A)) :
    AvoidDecomp G c A := by
  classical
  have hgx' : g ≠ x := hgx.ne
  have hcx' : c ≠ x := hcx.ne
  have huniq : ∀ v ∈ evenSet G, v = g := fun v hv => Finset.card_le_one.mp hev v hv g hg
  have hodd : ∀ v, v ≠ g → 0 < G.degree v → G.degree v % 2 = 1 := by
    intro v hvg hpos
    have : v ∉ evenSet G := fun h => hvg (huniq v h)
    rw [mem_evenSet_iff] at this
    omega
  have hgd := mem_evenSet_iff.mp hg
  have hcg : c ≠ g := fun h => by rw [h] at hc; omega
  have hF : (delEdge G x c).Adj g x := ⟨hgx, fun h => by
    rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨h, -⟩
    · exact hgx' h
    · exact hcg h.symm⟩
  have hd₁ := delEdge_degree G hcx.symm
  have hd₂ := delEdge_degree (delEdge G x c) hF
  have hdeg : ∀ v, (delEdge (delEdge G x c) g x).degree v + (if v = g then 1 else 0) +
      2 * (if v = x then 1 else 0) + (if v = c then 1 else 0) = G.degree v := by
    intro v; have := hd₁ v; have := hd₂ v; omega
  have hxodd := hodd x hgx'.symm ((G.degree_pos_iff_exists_adj x).mpr ⟨g, hgx.symm⟩)
  have hx' : (delEdge (delEdge G x c) g x).degree x % 2 = 1 := by
    have h := hdeg x
    simp only [hgx'.symm, hcx'.symm, ite_true, ite_false] at h
    omega
  obtain ⟨D', hD', hav'⟩ := hchild
  have hD'x : D'.ends x = 1 := by rw [hD']; exact hx'
  obtain ⟨P, hP, hPend⟩ := D'.exists_end_of_pos (by rw [hD'x]; omega)
  have hPav := hav' P hP hPend
  obtain ⟨D₃, hD₃some, hD₃none, hD₃cov⟩ := D'.liftLeaf hP hPend
  have hsep₃ : ∀ a ∈ insert c A, Separates D₃ (some a) none := by
    intro a ha Q' hQ' ⟨hx, hn⟩
    rcases hD₃cov Q' hQ' with h | ⟨Q, hQ, hs⟩
    · rcases h (some a) hx with h | ⟨y', hy', h⟩
      · exact Option.some_ne_none _ h
      · rw [Option.some.injEq] at h
        subst h
        exact hPav _ ha hy'
    · rw [hs, List.mem_map] at hn
      obtain ⟨_, _, h⟩ := hn
      exact Option.some_ne_none _ h
  -- Fan's lemma in the leaf graph `apex (G − xc) {x}`: restore `gx`
  have hK : (apex (delEdge G x c) {x}).Adj (some x) (some g) := by
    rw [apex_adj_some_some]; exact hF.symm
  have hD₃g : D₃.ends (some g) = 1 := by
    have h := hD₃some g
    simp only [hgx', ite_false, add_zero] at h
    rw [h, hD']
    have := hdeg g
    simp only [hgx', hcg.symm, ite_true, ite_false] at this
    omega
  have hcount : (Finset.univ.filter (fun v => (apex (delEdge (delEdge G x c) g x) {x}).Adj
      (some x) v ∧ D₃.ends v = 0)).card < D₃.ends (some g) := by
    have hempty : Finset.univ.filter (fun v => (apex (delEdge (delEdge G x c) g x) {x}).Adj
        (some x) v ∧ D₃.ends v = 0) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
      rw [Finset.mem_filter] at hv
      obtain ⟨-, hadj, h0⟩ := hv
      cases v with
      | none => rw [hD₃none] at h0; exact one_ne_zero h0
      | some w =>
        rw [apex_adj_some_some] at hadj
        have hwc : w ≠ c := fun h => hadj.1.2 (by rw [h])
        have hwg : w ≠ g := fun h => hadj.2 (by rw [h, Sym2.eq_swap])
        have hwx : w ≠ x := hadj.ne.symm
        have h := hD₃some w
        simp only [hwx, ite_false, add_zero] at h
        rw [h, hD'] at h0
        have hdw := hdeg w
        simp only [hwg, hwx, hwc, ite_false, add_zero, mul_zero] at hdw
        have := hodd w hwg ((G.degree_pos_iff_exists_adj w).mpr ⟨x, hadj.1.1.symm⟩)
        omega
    rw [hempty, Finset.card_empty, hD₃g]
    omega
  obtain ⟨DH, -, hDHx, hDHg, hDHrest, hcovH⟩ :=
    fan_single_supp (G := apex (delEdge G x c) {x}) hK
      (apex_delEdge_edge_iff (delEdge G x c) {x} g x) D₃ hcount
  have hsepH : ∀ a ∈ insert c A, Separates DH (some a) none := by
    intro a ha
    have hxa : some x ≠ some a := by
      rw [Finset.mem_insert] at ha
      rcases ha with rfl | ha
      · simp [Ne.symm hcx']
      · simp only [ne_eq, Option.some.injEq]
        intro h
        exact hxA (by rw [h]; exact ha)
    exact separates_of_cover hxa (by simp) (hsep₃ a ha) hcovH
  have hDHnone : DH.ends none = 1 := by rw [hDHrest none (by simp) (by simp), hD₃none]
  have hc0 : DH.ends (some c) = 0 := by
    rw [hDHrest (some c) (by simp [hcx']) (by simp [hcg])]
    have h := hD₃some c
    simp only [hcx', ite_false, add_zero] at h
    rw [h, hD']
    have := hdeg c
    simp only [hcg, hcx', ite_true, ite_false, add_zero, mul_zero] at this
    omega
  obtain ⟨D, hDc, hDw, hav⟩ := avoid_of_leafSep G hcx DH
    (hsepH c (Finset.mem_insert_self _ _)) hc0 hDHnone (A := A) hcA
    (fun a ha => hsepH a (Finset.mem_insert_of_mem ha))
  refine ⟨D, fun v => ?_, hav⟩
  by_cases hvc : v = c
  · rw [hvc, hDc, hc]
  · rw [hDw v hvc]
    by_cases hvx : v = x
    · subst hvx
      rw [hDHx]
      have h := hD₃some v
      simp only [ite_true] at h
      rw [hD'x] at h
      omega
    · by_cases hvg : v = g
      · subst hvg
        rw [hD₃g] at hDHg
        have : DH.ends (some v) = 0 := by omega
        rw [this, hgd.2]
      · rw [hDHrest (some v) (by simp [hvx]) (by simp [hvg])]
        have h := hD₃some v
        simp only [hvx, ite_false, add_zero] at h
        rw [h, hD']
        have := hdeg v
        simp only [hvg, hvx, hvc, ite_false, add_zero, mul_zero] at this
        rw [this]

end transfer

section reduction

/-- **TR, the tight transfer conjecture.** For a tight target `x ∈ N(g) ∩ N(c)` (with `c ∉ N(g)`)
and any `A` disjoint from `N[c] ∪ {x}`, goodness of `(G − gx, c, A)` implies goodness of `(G, c, A)`.
`A` may meet `N(g)` and may contain `g`.  For `x ∉ N(c)` the same statement is a theorem
(`avoid_of_target_child`). -/
def TightTransfer : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (evenSet G).card ≤ 1 → ∀ g ∈ evenSet G, ∀ c : V, G.degree c % 2 = 1 → ¬ G.Adj g c →
    ∀ x : V, G.Adj g x → G.Adj c x → ∀ A : Finset V, c ∉ A → x ∉ A → (∀ a ∈ A, ¬ G.Adj c a) →
    AvoidDecomp (delEdge G g x) c A → AvoidDecomp G c A

/-- **ST, the some-target conjecture.** Every blocked instance has a target `x ∈ N(g)` for which the
(inadmissible) instance `(G − gx, c, A)` is good. -/
def SomeTarget : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (evenSet G).card ≤ 1 → ∀ c : V, G.degree c % 2 = 1 → ∀ A : Finset V,
    Admissible G c A → ∀ g ∈ evenSet G, ¬ G.Adj g c →
    (∀ w, G.Adj g w → ∃ a ∈ A, a ≠ g ∧ G.Adj w a) →
    ∃ x, G.Adj g x ∧ AvoidDecomp (delEdge G g x) c A

/-- **ST′, the instance-level some-target statement.** Every blocked instance has a target whose
instance-level child is good: `(G − gx, c, A)` if `x ∉ N(c)`, and `(G − xc − gx, x, A ∪ {c})` if
`x ∈ N(c)`.  This would prove `L1Blocked` with no transfer conjecture
(`l1Blocked_of_someTargetLocal`), but it is false (manuscript: an instance of order 7 with
`d(g) = 2` and `N(g) ⊆ N(c)`). -/
def SomeTargetLocal : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (evenSet G).card ≤ 1 → ∀ c : V, G.degree c % 2 = 1 → ∀ A : Finset V,
    Admissible G c A → ∀ g ∈ evenSet G, ¬ G.Adj g c →
    (∀ w, G.Adj g w → ∃ a ∈ A, a ≠ g ∧ G.Adj w a) →
    ∃ x, G.Adj g x ∧ ((¬ G.Adj c x ∧ AvoidDecomp (delEdge G g x) c A) ∨
      (G.Adj c x ∧ AvoidDecomp (delEdge (delEdge G x c) g x) x (insert c A)))

/-- **The two-sided reduction.** The tight transfer conjecture and the some-target conjecture
together imply `L1Blocked`. -/
theorem l1Blocked_of_someTarget (hTR : TightTransfer.{u}) (hST : SomeTarget.{u}) :
    L1Blocked.{u} := by
  intro V _ _ G _ hev c hc A hA g hg hgc hblk
  obtain ⟨x, hgx, hgood⟩ := hST V G hev c hc A hA g hg hgc hblk
  have hxA : x ∉ A := fun h => (hA x h).2.2 g hg hgx
  by_cases hcx : G.Adj c x
  · exact hTR V G hev g hg c hc hgc x hgx hcx A (fun h => (hA c h).1 rfl) hxA
      (fun a ha => (hA a ha).2.1) hgood
  · exact avoid_of_target_child G hev hg hgc hgx hcx hc hxA hgood

/-- The instance-level form ST′ would imply `L1Blocked` outright (it is false, see the
manuscript). -/
theorem l1Blocked_of_someTargetLocal (hST : SomeTargetLocal.{u}) : L1Blocked.{u} := by
  intro V _ _ G _ hev c hc A hA g hg hgc hblk
  obtain ⟨x, hgx, h⟩ := hST V G hev c hc A hA g hg hgc hblk
  have hxA : x ∉ A := fun h => (hA x h).2.2 g hg hgx
  rcases h with ⟨hcx, hgood⟩ | ⟨hcx, hgood⟩
  · exact avoid_of_target_child G hev hg hgc hgx hcx hc hxA hgood
  · exact avoid_of_target_adj_child G hev hg hgc hgx hcx hc (fun h => (hA c h).1 rfl) hxA hgood

/-- `TR ∧ ST ⇒` the general form of `L₁*`. -/
theorem l1starGen_of_ST_TR (hTR : TightTransfer.{u}) (hST : SomeTarget.{u}) : L1StarGen.{u} :=
  l1starGen_of_blocked (l1Blocked_of_someTarget hTR hST)

/-- `TR ∧ ST ⇒ L₁*` (the stated conjecture, `|A| ≤ 2`). -/
theorem l1star_of_ST_TR (hTR : TightTransfer.{u}) (hST : SomeTarget.{u}) : L1Star.{u} :=
  l1star_of_gen (l1starGen_of_ST_TR hTR hST)

/-- `TR ∧ ST ⇒` EE: if `z` is the only even vertex and `x ∈ N(z)`, then `xz` is the terminal edge
at `x` of some Lovász decomposition. -/
theorem ee_of_ST_TR (hTR : TightTransfer.{u}) (hST : SomeTarget.{u}) (G : SimpleGraph W)
    [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1) {z x : W} (hz : z ∈ evenSet G)
    (hzx : G.Adj z x) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∃ P ∈ D.paths, (P.src = x ∨ P.tgt = x) ∧ s(x, z) ∈ P.edges :=
  ee_of_l1Blocked (l1Blocked_of_someTarget hTR hST) G hev hz hzx

/-- `TR ∧ ST ⇒ L∞`. -/
theorem lInfty_of_ST_TR (hTR : TightTransfer.{u}) (hST : SomeTarget.{u}) : LInfty.{u} :=
  lInfty_of_l1Blocked (l1Blocked_of_someTarget hTR hST)

/-- **TR on admissible instances**: the tight transfer for a blocked admissible instance. This is
all that `l1Blocked_of_someTarget` uses of `TightTransfer`. -/
def TightTransferAdm : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (evenSet G).card ≤ 1 → ∀ c : V, G.degree c % 2 = 1 → ∀ A : Finset V,
    Admissible G c A → ∀ g ∈ evenSet G, ¬ G.Adj g c →
    (∀ w, G.Adj g w → ∃ a ∈ A, a ≠ g ∧ G.Adj w a) →
    ∀ x : V, G.Adj g x → G.Adj c x → AvoidDecomp (delEdge G g x) c A → AvoidDecomp G c A

theorem tightTransferAdm_of_tightTransfer (h : TightTransfer.{u}) : TightTransferAdm.{u} := by
  intro V _ _ G _ hev c hc A hA g hg hgc _ x hgx hcx hgood
  exact h V G hev g hg c hc hgc x hgx hcx A (fun h => (hA c h).1 rfl)
    (fun h => (hA x h).2.2 g hg hgx) (fun a ha => (hA a ha).2.1) hgood

/-- `L1Blocked` gives `TR` on admissible instances for free: its conclusion is `L1Blocked`'s. -/
theorem tightTransferAdm_of_l1Blocked (hB : L1Blocked.{u}) : TightTransferAdm.{u} := by
  intro V _ _ G _ hev c hc A hA g hg hgc hblk _ _ _ _
  exact hB V G hev c hc A hA g hg hgc hblk

/-- The two-sided reduction uses only `TR` on admissible instances. -/
theorem l1Blocked_of_someTarget_adm (hTR : TightTransferAdm.{u}) (hST : SomeTarget.{u}) :
    L1Blocked.{u} := by
  intro V _ _ G _ hev c hc A hA g hg hgc hblk
  obtain ⟨x, hgx, hgood⟩ := hST V G hev c hc A hA g hg hgc hblk
  have hxA : x ∉ A := fun h => (hA x h).2.2 g hg hgx
  by_cases hcx : G.Adj c x
  · exact hTR V G hev c hc A hA g hg hgc hblk x hgx hcx hgood
  · exact avoid_of_target_child G hev hg hgc hgx hcx hc hxA hgood

/-- **Given `ST`, `L1Blocked` is equivalent to the tight transfer on admissible instances.** So `ST`
is the substantive half of the two-sided reduction. -/
theorem l1Blocked_iff_tightTransferAdm (hST : SomeTarget.{u}) :
    L1Blocked.{u} ↔ TightTransferAdm.{u} :=
  ⟨tightTransferAdm_of_l1Blocked, fun h => l1Blocked_of_someTarget_adm h hST⟩

/-- **ST_out**: a blocked instance with a non-tight target has a *non-tight* target `x` with
`(G − gx, c, A)` good.  No transfer conjecture is needed for such a target. -/
def SomeTargetOut : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (evenSet G).card ≤ 1 → ∀ c : V, G.degree c % 2 = 1 → ∀ A : Finset V,
    Admissible G c A → ∀ g ∈ evenSet G, ¬ G.Adj g c →
    (∀ w, G.Adj g w → ∃ a ∈ A, a ≠ g ∧ G.Adj w a) → (∃ w, G.Adj g w ∧ ¬ G.Adj c w) →
    ∃ x, G.Adj g x ∧ ¬ G.Adj c x ∧ AvoidDecomp (delEdge G g x) c A

/-- **The all-tight blocked case**: `L1Blocked` restricted to `N(g) ⊆ N(c)`. -/
def L1BlockedTight : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (evenSet G).card ≤ 1 → ∀ c : V, G.degree c % 2 = 1 → ∀ A : Finset V,
    Admissible G c A → ∀ g ∈ evenSet G, ¬ G.Adj g c →
    (∀ w, G.Adj g w → ∃ a ∈ A, a ≠ g ∧ G.Adj w a) → (∀ w, G.Adj g w → G.Adj c w) →
    AvoidDecomp G c A

/-- `ST_out` and the all-tight case give `L1Blocked`. -/
theorem l1Blocked_of_out_tight (hO : SomeTargetOut.{u}) (hT : L1BlockedTight.{u}) :
    L1Blocked.{u} := by
  intro V _ _ G _ hev c hc A hA g hg hgc hblk
  by_cases hout : ∃ w, G.Adj g w ∧ ¬ G.Adj c w
  · obtain ⟨x, hgx, hcx, hgood⟩ := hO V G hev c hc A hA g hg hgc hblk hout
    exact avoid_of_target_child G hev hg hgc hgx hcx hc (fun h => (hA x h).2.2 g hg hgx) hgood
  · refine hT V G hev c hc A hA g hg hgc hblk fun w hw => ?_
    by_contra h
    exact hout ⟨w, hw, h⟩

/-- `ST ∧ TR` give the all-tight case. -/
theorem l1BlockedTight_of_ST_TR (hTR : TightTransfer.{u}) (hST : SomeTarget.{u}) :
    L1BlockedTight.{u} := by
  intro V _ _ G _ hev c hc A hA g hg hgc hblk _
  exact l1Blocked_of_someTarget hTR hST V G hev c hc A hA g hg hgc hblk

end reduction

end Gallai
