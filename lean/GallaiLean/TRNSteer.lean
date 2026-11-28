import GallaiLean.TRN
import GallaiLean.NeighbourAvoid

/-!
# Two-token steering: the conclusion of TRN without the tight Fan step

Manuscript `manuscripts/trn`, Section 6.

Let `g` be the only even vertex of `G`, let `x, y` be odd and non-adjacent. Hang a leaf `ℓ` at `y`
(the apex graph `apex G {y}`, with `ℓ = none`). Its even vertices are `g` and `y`: put a *token*
on each. The condition "no path contains both `ℓ` and `x`" is a property of vertex sets, kept by
every Fan step whose target is not `ℓ` or `x` (`meetsOnce_of_cover`). A token at `a` may move along
an edge `au` to `u` when
* `u ∉ X = {ℓ, x}`,
* `u` is not the other token, and
* after the edge `au` is deleted, `u` is not adjacent to the other token.
Then the Fan step that restores `au` has no blank at all (`fan_step_two`). When one token has been
moved onto a vertex that the deletions leave isolated, the graph has at most one even vertex and
`ℓ` is a leaf at `y`, and the leaf-tail lemma (`avoid_leafTail`) supplies a decomposition whose
`ℓ`-path avoids `x`. Undoing the moves and deleting the leaf gives `(G, y, {x})` good
(`avoid_of_steer2`).

* `avoid_leafTail` (manuscript Lemma 6.1): Conjecture N for a tail that is a leaf `c` at `w`,
  `x ≁ w`. In the induction no tight target ever occurs. The vertex `w` may be the even vertex.
* `fan_step_two` (Lemma 6.2): Lovász's Case I step when the graph has two even vertices `z, o`
  and the target `u` is not adjacent to `o` after the deletion.
* `Steer2` (Definition 6.3), `steer2_meetsOnce` (Lemma 6.4): a two-token schedule carries "every path meets `X` at
  most once" up from a graph with at most one even vertex.
* `avoid_of_steer2` (Theorem 6.5): a schedule from `(g, y)` in `apex G {y}` avoiding `{ℓ, x}`
  gives `AvoidDecomp G y {x}`. No hypothesis on `G − gu` is used.
* `TightTransferNCore2` (Definition 6.8), `conjN_of_core2` (Theorem 6.9): Conjecture N follows from TRN restricted to
  core instances that admit **no** two-token schedule.
-/

open SimpleGraph

namespace Gallai

universe u

section leafTail

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- The induction behind `avoid_leafTail`, on the degree sum. -/
theorem avoid_leafTail_strong (n : ℕ) :
    ∀ (G : SimpleGraph W) [DecidableRel G.Adj], (∑ v, G.degree v) = n → (evenSet G).card ≤ 1 →
    ∀ c w x : W, (∀ v, G.Adj c v ↔ v = w) → G.degree x % 2 = 1 → x ≠ c → x ≠ w →
    ¬ G.Adj x w → AvoidDecomp G c {x} := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ hn hev c w x hc hx hxc hxw hnxw
  classical
  have hcw : G.Adj c w := (hc w).mpr rfl
  have hdc : G.degree c = 1 := by
    rw [← card_neighborFinset_eq_degree]
    have : G.neighborFinset c = {w} := by
      ext v
      rw [mem_neighborFinset, Finset.mem_singleton, hc]
    rw [this, Finset.card_singleton]
  have hcodd : G.degree c % 2 = 1 := by rw [hdc]
  have hnxc : ¬ G.Adj c x := fun h => hxw ((hc x).mp h)
  by_cases hz : ∃ g, g ∈ evenSet G
  swap
  · have h0 : (evenSet G).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun g hg => hz ⟨g, hg⟩)
    exact avoidDecomp_singleton_iff.mpr (lovasz_avoid_nonadj G h0 hcodd (Ne.symm hxc) hnxc)
  obtain ⟨g, hg⟩ := hz
  have hgdeg := mem_evenSet_iff.mp hg
  have hxg : x ≠ g := by rintro rfl; omega
  have hcg : c ≠ g := by rintro rfl; omega
  by_cases h1 : ∃ u, G.Adj g u ∧ u ≠ x ∧ u ≠ c ∧ u ≠ w
  · -- a target that is not tight for the leaf tail: Lovász's Case I
    obtain ⟨u, hgu, hux, huc, huw⟩ := h1
    have hcu : ¬ G.Adj c u := fun h => huw ((hc u).mp h)
    have hsum := delEdge_sum_degree G hgu
    have hdx := delEdge_degree G hgu x
    simp only [hxg, Ne.symm hux, ite_false, add_zero] at hdx
    have hc' : ∀ v, (delEdge G g u).Adj c v ↔ v = w := by
      intro v
      constructor
      · intro h
        exact (hc v).mp h.1
      · intro h
        refine ⟨(hc v).mpr h, ?_⟩
        rw [Sym2.eq_iff]
        rintro (⟨h1, -⟩ | ⟨h1, -⟩)
        · exact hcg h1
        · exact huc h1.symm
    have hchild : AvoidDecomp (delEdge G g u) c {x} :=
      ih _ (by omega) (delEdge G g u) rfl (evenSet_delEdge_card hev hg hgu) c w x hc'
        (by rw [hdx]; exact hx) hxc hxw (fun h => hnxw h.1)
    exact avoidDecomp_singleton_iff.mpr (avoid_free_target hev hg hgu hux huc hcu hcg
      (avoidDecomp_singleton_iff.mp hchild))
  · simp only [not_exists, not_and, not_not] at h1
    have hdg : (G.neighborFinset g).card = G.degree g := card_neighborFinset_eq_degree G g
    by_cases hgw : g = w
    · -- every neighbour of `g = w` is the leaf `c`: impossible, as `d(g)` is even
      have hsub : G.neighborFinset g ⊆ {c} := by
        intro v hv
        rw [mem_neighborFinset] at hv
        rw [Finset.mem_singleton]
        by_contra hvc
        have hvx : v ≠ x := by
          rintro rfl
          exact hnxw (hgw ▸ hv.symm)
        have := h1 v hv hvx hvc
        exact hv.ne (hgw.trans this.symm)
      have := Finset.card_le_card hsub
      rw [Finset.card_singleton, hdg] at this
      omega
    · -- `N(g) = {x, w}` with `x ≁ w`: split `g` off and apply `L₁`
      have hcN : ¬ G.Adj g c := fun h => hgw ((hc g).mp h.symm)
      have hsub : G.neighborFinset g ⊆ {x, w} := by
        intro v hv
        rw [mem_neighborFinset] at hv
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases hvx : v = x
        · exact Or.inl hvx
        · exact Or.inr (h1 v hv hvx (by rintro rfl; exact hcN hv))
      have hle := Finset.card_le_card hsub
      rw [Finset.card_pair hxw, hdg] at hle
      have h2 : G.degree g = 2 := by omega
      have heq : G.neighborFinset g = {x, w} := by
        refine Finset.eq_of_subset_of_card_le hsub ?_
        rw [Finset.card_pair hxw, hdg, h2]
      have hNg : ∀ v, G.Adj g v ↔ v = x ∨ v = w := by
        intro v
        rw [← mem_neighborFinset, heq]
        simp
      refine avoid_of_degTwo_indep hev hg hNg hxw hnxw hx hcodd hxc (fun h => hnxc h.symm) ?_
      rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact hxc h.symm
      · exact hcw.ne h

/-- **The leaf-tail lemma** (manuscript Lemma 6.1). Let `G` have at most one vertex of positive
even degree, let `c` be a leaf whose neighbour is `w`, and let `x ∉ {c, w}` be odd and not
adjacent to `w`. Then some Lovász decomposition has the path ending at `c` avoiding `x`. The vertex
`w` may be the even vertex. The proof is the induction of Conjecture N, in which a leaf tail never
meets a tight target. -/
theorem avoid_leafTail (G : SimpleGraph W) [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1)
    {c w x : W} (hc : ∀ v, G.Adj c v ↔ v = w) (hx : G.degree x % 2 = 1) (hxc : x ≠ c)
    (hxw : x ≠ w) (hnxw : ¬ G.Adj x w) : AvoidDecomp G c {x} :=
  avoid_leafTail_strong _ G rfl hev c w x hc hx hxc hxw hnxw

end leafTail

section steer2

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- **One Fan step with two even vertices** (manuscript Lemma 6.2). Let the vertices of positive
even degree of `G` lie in `{z, o}`, with `z` even, and let `u ∈ N(z)`, `u ∉ X ∪ {o}`, be
non-adjacent to `o` in `G − uz`. If `G − uz` has a decomposition with `ends = deg mod 2` meeting `X`
at most once per path, so has `G`. In `G − uz` only `u` and `o` can be even, so `u` has no blank
neighbour and Fan's lemma applies. -/
theorem fan_step_two (G : SimpleGraph W) [DecidableRel G.Adj] {X : Finset W} {z o u : W}
    (hev : ∀ v ∈ evenSet G, v = z ∨ v = o) (hz : z ∈ evenSet G) (huz : G.Adj u z) (huX : u ∉ X)
    (huo : u ≠ o) (hno : ¬ (delEdge G u z).Adj u o)
    (D' : PathDecomp (delEdge G u z)) (hD' : ∀ v, D'.ends v = (delEdge G u z).degree v % 2)
    (hsep' : MeetsOnce D' X) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ MeetsOnce D X := by
  have hzd := mem_evenSet_iff.mp hz
  have hne : u ≠ z := huz.ne
  have hdeg := delEdge_degree G huz
  have hdu := hdeg u
  have hdz := hdeg z
  simp only [hne, hne.symm, ite_true, ite_false, add_zero] at hdu hdz
  have huodd : G.degree u % 2 = 1 := by
    have hupos : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).mpr ⟨z, huz⟩
    have : u ∉ evenSet G := fun h => by
      rcases hev u h with h | h
      · exact hne h
      · exact huo h
    rw [mem_evenSet_iff] at this
    omega
  have hev' : ∀ v ∈ evenSet (delEdge G u z), v = u ∨ v = o := by
    intro v hv
    obtain ⟨hpos, heven⟩ := mem_evenSet_iff.mp hv
    by_cases hvu : v = u
    · exact Or.inl hvu
    · by_cases hvz : v = z
      · subst hvz
        omega
      · have h := hdeg v
        simp only [hvu, hvz, ite_false, add_zero] at h
        rcases hev v (mem_evenSet_iff.mpr ⟨h ▸ hpos, h ▸ heven⟩) with h' | h'
        · exact absurd h' hvz
        · exact Or.inr h'
  have hD'z : D'.ends z = 1 := by rw [hD' z]; omega
  obtain ⟨D, -, hDu, hDz, hDo, hcov⟩ := fan_single_supp huz (delEdge_edgeSet G u z) D' (by
    rw [hD'z]
    have : Finset.univ.filter (fun v => (delEdge G u z).Adj u v ∧ D'.ends v = 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro v - ⟨hadj, h0⟩
      have hvu : v ≠ u := hadj.ne.symm
      have hpos : 0 < (delEdge G u z).degree v :=
        ((delEdge G u z).degree_pos_iff_exists_adj v).mpr ⟨u, hadj.symm⟩
      rw [hD' v] at h0
      rcases hev' v (mem_evenSet_iff.mpr ⟨hpos, h0⟩) with h | h
      · exact hvu h
      · exact hno (h ▸ hadj)
    rw [this, Finset.card_empty]
    exact Nat.one_pos)
  refine ⟨D, fun v => ?_, meetsOnce_of_cover huX hsep' hcov⟩
  by_cases hvu : v = u
  · subst hvu
    rw [hDu, hD' v]
    omega
  · by_cases hvz : v = z
    · subst hvz
      omega
    · rw [hDo v hvu hvz, hD' v]
      have h := hdeg v
      simp only [hvu, hvz, ite_false, add_zero] at h
      rw [h]

/-- `Steer2 X K a b` (manuscript Definition 6.3): a schedule for two tokens at `a` and `b`. A token moves from `p` along an
edge `pu` to `u ∉ X`, where `u` is not the other token and, once `pu` is deleted, `u` is not
adjacent to the other token. The schedule ends when a token reaches a vertex that the deletions
leave isolated. `swap` lets either token move. -/
inductive Steer2 (X : Finset W) : SimpleGraph W → W → W → Prop
  | fin {K : SimpleGraph W} {a b u : W} : K.Adj a u → u ∉ X → u ≠ b →
      (∀ v, K.Adj u v → v = a) → Steer2 X K a b
  | step {K : SimpleGraph W} {a b u : W} : K.Adj a u → u ∉ X → u ≠ b →
      ¬ (delEdge K u a).Adj u b → Steer2 X (delEdge K u a) u b → Steer2 X K a b
  | swap {K : SimpleGraph W} {a b : W} : Steer2 X K b a → Steer2 X K a b

omit [DecidableEq W] in
/-- If the vertices of positive even degree of `K` lie in `{a, b}` and `a` is not one of them,
there is at most one. -/
theorem card_evenSet_le_one_of_not_mem {K : SimpleGraph W} [DecidableRel K.Adj] {a b : W}
    (hev : ∀ v ∈ evenSet K, v = a ∨ v = b) (ha : a ∉ evenSet K) : (evenSet K).card ≤ 1 := by
  refine (Finset.card_le_card (s := evenSet K) (t := {b}) ?_).trans (by simp)
  intro v hv
  rw [Finset.mem_singleton]
  rcases hev v hv with h | h
  · exact absurd (h ▸ hv) ha
  · exact h

/-- **The two-token schedule gives a decomposition** (manuscript Lemma 6.4). Let `P` be a property of
graphs kept by deleting edges with both ends outside `X`, and suppose every graph with `P` and at
most one vertex of positive even degree has a decomposition with `ends = deg mod 2` meeting `X`
at most once per path. If `a ≠ b` lie outside `X`, the even vertices of `K` lie in `{a, b}`, `K`
has `P`, and `Steer2 X K a b`, then `K` has such a decomposition too. -/
theorem steer2_meetsOnce {X : Finset W} (P : SimpleGraph W → Prop)
    (hP : ∀ K a b, P K → a ∉ X → b ∉ X → P (delEdge K a b))
    (hbase : ∀ (K : SimpleGraph W) [DecidableRel K.Adj], P K → (evenSet K).card ≤ 1 →
      ∃ D : PathDecomp K, (∀ v, D.ends v = K.degree v % 2) ∧ MeetsOnce D X) :
    ∀ {K : SimpleGraph W} {a b : W}, Steer2 X K a b → ∀ [DecidableRel K.Adj], P K → a ∉ X →
      b ∉ X → a ≠ b → (∀ v ∈ evenSet K, v = a ∨ v = b) →
      ∃ D : PathDecomp K, (∀ v, D.ends v = K.degree v % 2) ∧ MeetsOnce D X := by
  intro K a b hS
  induction hS with
  | @fin K a b u hau huX hub hiso =>
    intro _ hPK haX hbX hab hev
    by_cases haE : a ∈ evenSet K
    swap
    · exact hbase K hPK (card_evenSet_le_one_of_not_mem hev haE)
    have hua : K.Adj u a := hau.symm
    have hdeg := delEdge_degree K hua
    have hev' : (evenSet (delEdge K u a)).card ≤ 1 := by
      refine (Finset.card_le_card (s := evenSet (delEdge K u a)) (t := {b}) ?_).trans (by simp)
      intro v hv
      rw [Finset.mem_singleton]
      obtain ⟨hpos, heven⟩ := mem_evenSet_iff.mp hv
      have h := hdeg v
      by_cases hvu : v = u
      · exfalso
        subst hvu
        obtain ⟨z, hz⟩ := ((delEdge K v a).degree_pos_iff_exists_adj v).mp hpos
        have hza := hiso z hz.1
        subst hza
        exact hz.2 rfl
      · by_cases hva : v = a
        · subst hva
          simp only [hvu, ite_false, ite_true] at h
          have := (mem_evenSet_iff.mp haE).2
          omega
        · simp only [hvu, hva, ite_false, add_zero] at h
          rcases hev v (mem_evenSet_iff.mpr ⟨h ▸ hpos, h ▸ heven⟩) with h' | h'
          · exact absurd h' hva
          · exact h'
    obtain ⟨D', hD', hm'⟩ := hbase (delEdge K u a) (hP K u a hPK huX haX) hev'
    exact fan_step_two K hev haE hua huX hub (fun h => hab (hiso b h.1).symm) D' hD' hm'
  | @step K a b u hau huX hub hno hS' ih =>
    intro _ hPK haX hbX hab hev
    by_cases haE : a ∈ evenSet K
    swap
    · exact hbase K hPK (card_evenSet_le_one_of_not_mem hev haE)
    have hua : K.Adj u a := hau.symm
    have hdeg := delEdge_degree K hua
    have hev' : ∀ v ∈ evenSet (delEdge K u a), v = u ∨ v = b := by
      intro v hv
      obtain ⟨hpos, heven⟩ := mem_evenSet_iff.mp hv
      by_cases hvu : v = u
      · exact Or.inl hvu
      · have h := hdeg v
        by_cases hva : v = a
        · subst hva
          simp only [hvu, ite_false, ite_true] at h
          have := (mem_evenSet_iff.mp haE).2
          omega
        · simp only [hvu, hva, ite_false, add_zero] at h
          rcases hev v (mem_evenSet_iff.mpr ⟨h ▸ hpos, h ▸ heven⟩) with h' | h'
          · exact absurd h' hva
          · exact Or.inr h'
    obtain ⟨D', hD', hm'⟩ := ih (hP K u a hPK huX haX) huX hbX hub hev'
    exact fan_step_two K hev haE hua huX hub hno D' hD' hm'
  | @swap K a b hS' ih =>
    intro _ hPK haX hbX hab hev
    exact ih hPK hbX haX (Ne.symm hab) (fun v hv => (hev v hv).symm)

end steer2

section main

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The avoided set of the leaf graph: the leaf `none` and `x`. -/
abbrev leafX (x : V) : Finset (Option V) := insert none {some x}

/-- **Two-token steering** (manuscript Theorem 6.5). Let `g` be the only even vertex of `G`, and
let `x, y` be odd and non-adjacent. If the leaf graph `apex G {y}` admits a two-token schedule from
`(g, y)` avoiding `{ℓ, x}`, then some Lovász decomposition of `G` has the path ending at `y`
avoiding `x`. Nothing is assumed about `G − gu`. -/
theorem avoid_of_steer2 (G : SimpleGraph V) [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1)
    {g x y : V} (hg : g ∈ evenSet G) (hx : G.degree x % 2 = 1) (hy : G.degree y % 2 = 1)
    (hxy : x ≠ y) (hnxy : ¬ G.Adj x y)
    (hS : Steer2 (leafX x) (apex G {y}) (some g) (some y)) : AvoidDecomp G y {x} := by
  classical
  set K := apex G {y} with hK
  set X := leafX x with hX
  have huniq : ∀ w ∈ evenSet G, w = g := fun w hw => Finset.card_le_one.mp hev w hw g hg
  have hgdeg := mem_evenSet_iff.mp hg
  have hxg : x ≠ g := by rintro rfl; omega
  have hyg : y ≠ g := by rintro rfl; omega
  have hKsome : ∀ v, K.degree (some v) = G.degree v + if v = y then 1 else 0 := by
    intro v
    have h := apex_degree_some (G := G) (T := {y}) v
    simp only [Finset.mem_singleton] at h
    exact h
  have hKnone : K.degree none = 1 := by
    have h := apex_degree_none (G := G) (T := {y})
    simp only [Finset.card_singleton] at h
    exact h
  have hnoneX : (none : Option V) ∈ X := Finset.mem_insert_self _ _
  have hxX : some x ∈ X := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hsomeX : ∀ v : V, some v ∈ X ↔ v = x := by intro v; simp [hX]
  have hevK : ∀ v ∈ evenSet K, v = some g ∨ v = some y := by
    intro v hv
    rw [mem_evenSet_iff] at hv
    cases v with
    | none => rw [hKnone] at hv; omega
    | some v =>
      rw [hKsome] at hv
      by_cases hvy : v = y
      · exact Or.inr (by rw [hvy])
      · simp only [hvy, ite_false, add_zero] at hv
        exact Or.inl (by rw [huniq v (mem_evenSet_iff.mpr hv)])
  -- the invariant: a subgraph of `K` with every edge at `X` kept
  obtain ⟨DH, hDH, hm⟩ := steer2_meetsOnce (X := X)
    (fun K' => K' ≤ K ∧ ∀ v ∈ X, ∀ z, (K'.Adj v z ↔ K.Adj v z))
    (fun K' a b hP ha hb => ⟨fun p q h => hP.1 h.1, fun v hv z => by
      rw [← hP.2 v hv z]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        rw [Sym2.eq_iff]
        rintro (⟨h1, -⟩ | ⟨h1, -⟩)
        · exact ha (h1 ▸ hv)
        · exact hb (h1 ▸ hv)⟩)
    (fun K' _ hP hev' => by
      have hnK' : ∀ z, K'.Adj none z ↔ z = some y := by
        intro z
        rw [hP.2 none hnoneX z]
        cases z with
        | none => simp [hK]
        | some z => simp [hK, eq_comm]
      have hxdeg : K'.degree (some x) = K.degree (some x) := by
        rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
        congr 1
        ext z
        rw [mem_neighborFinset, mem_neighborFinset]
        exact hP.2 (some x) hxX z
      have hx' : K'.degree (some x) % 2 = 1 := by
        rw [hxdeg, hKsome]
        simp only [hxy, ite_false, add_zero]
        exact hx
      have hnxy' : ¬ K'.Adj (some x) (some y) := fun h => hnxy (by simpa [hK] using hP.1 h)
      obtain ⟨D, hD, hav⟩ := avoid_leafTail K' hev' hnK' hx' (by simp)
        (fun h => hxy (Option.some.inj h)) hnxy'
      refine ⟨D, hD, fun P hP a ha b hb haP hbP => ?_⟩
      have hpend : ∀ e ∈ K'.edgeSet, (none : Option V) ∈ e → e = s(none, some y) := by
        intro e he hne
        induction e using Sym2.inductionOn with
        | hf p q =>
          rw [mem_edgeSet] at he
          rcases Sym2.mem_iff.mp hne with rfl | rfl
          · rw [(hnK' q).mp he]
          · rw [(hnK' p).mp he.symm, Sym2.eq_swap]
      have key : some x ∈ P.walk.support → (none : Option V) ∉ P.walk.support := by
        intro hxP hnP
        exact hav P hP (P.end_of_pendant hpend hnP) (some x) (Finset.mem_singleton_self _) hxP
      have hab : ∀ c ∈ X, c = none ∨ c = some x := by
        intro c hc
        rw [hX, Finset.mem_insert, Finset.mem_singleton] at hc
        exact hc
      rcases hab a ha with rfl | rfl <;> rcases hab b hb with rfl | rfl
      · rfl
      · exact absurd haP (key hbP)
      · exact absurd hbP (key haP)
      · rfl)
    hS ⟨le_refl _, fun _ _ _ => Iff.rfl⟩
    (by rw [hsomeX]; exact Ne.symm hxg) (by rw [hsomeX]; exact Ne.symm hxy)
    (fun h => hyg (Option.some.inj h).symm) hevK
  refine avoid_of_apexSep G hy DH (fun v hv => ?_) ?_ (fun P hP hnP a ha haP => ?_)
  · rw [hDH, hKsome]; simp [hv]
  · rw [hDH, hKsome]; simp only [ite_true]; omega
  · rw [Finset.mem_singleton] at ha
    rw [ha] at haP
    have := hm P hP none hnoneX (some x) hxX hnP haP
    cases this

/-- **The core of TRN without a two-token schedule** (manuscript Definition 6.8):
`TightTransferNCore` restricted to the instances whose leaf graph admits no two-token schedule. -/
def TightTransferNCore2 (V : Type u) [Fintype V] [DecidableEq V] : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj], (evenSet G).card ≤ 1 → ∀ g ∈ evenSet G,
    ∀ x y u : V, G.degree x % 2 = 1 → G.degree y % 2 = 1 → x ≠ y → ¬ G.Adj x y →
    G.Adj g u → G.Adj y u → u ≠ x →
    (∃ w, G.Adj y w ∧ w ∉ evenSet G ∧ ¬ G.Adj x w) →
    ConjNBelow V (∑ w, G.degree w) →
    (∀ v, G.Adj g v → v ≠ x → v ≠ y → G.Adj y v) →
    (∃ w, G.Adj y w ∧ w ≠ u ∧ ¬ G.Adj x w) →
    (∃ c, G.Adj y c ∧ G.Adj c x) →
    ¬ (∃ a b, a ≠ b ∧ ¬ G.Adj a b ∧ ∀ v, G.Adj g v ↔ v = a ∨ v = b) →
    ¬ Steer2 (leafX x) (apex G {y}) (some g) (some y) →
    AvoidDecomp (delEdge G g u) y {x} → AvoidDecomp G y {x}

/-- The core of TRN implies its restriction to instances without a schedule. -/
theorem tightTransferNCore2_of (hT : TightTransferNCore V) : TightTransferNCore2 V :=
  fun G _ hev g hg x y u hx hy hxy hnxy hgu hyu hux h0 hb ht hw hc hi _ hchild =>
    hT G hev g hg x y u hx hy hxy hnxy hgu hyu hux h0 hb ht hw hc hi hchild

/-- Two-token steering settles every core instance that has a schedule. -/
theorem tightTransferNCore_of_core2 (hT : TightTransferNCore2 V) : TightTransferNCore V := by
  intro G _ hev g hg x y u hx hy hxy hnxy hgu hyu hux h0 hb ht hw hc hi hchild
  by_cases hS : Steer2 (leafX x) (apex G {y}) (some g) (some y)
  · exact avoid_of_steer2 G hev hg hx hy hxy hnxy hS
  · exact hT G hev g hg x y u hx hy hxy hnxy hgu hyu hux h0 hb ht hw hc hi hS hchild

/-- **Conjecture N from the unscheduled core** (manuscript Theorem 6.9). TRN restricted to core
instances that admit no two-token schedule implies Conjecture N. (The degree-two case is NA, now a
theorem: `conjNDegTwoOn`.) -/
theorem conjN_of_core2 (hT : TightTransferNCore2 V) : ConjNOn V :=
  conjN_of_core (tightTransferNCore_of_core2 hT) conjNDegTwoOn

end main

end Gallai
