import GallaiLean.ConjN

/-!
# Neighbour avoidance (NA): a proof

Manuscript `manuscripts/na`.

**Theorem** (`neighbourAvoid`, hence `NeighbourAvoidOn V` for every `V`: `neighbourAvoidOn`). Let `G`
have no vertex of positive even degree, let `x ~ y`, and let `y` have a neighbour `w ≠ x` with
`w ≁ x`. Then some Lovász decomposition of `G` has the path ending at `y` avoiding `x`.

It is the case `Y = {x}`, walk `y w`, of the set form **`avoid_packed_of_reach`**: if `Y` is packed,
`y ∉ Y` is odd, and a vertex `w` of positive degree with no neighbour in `Y` is joined to `y` by a walk
avoiding `Y`, then some Lovász decomposition has every path meeting `Y` at most once and the path
ending at `y` disjoint from `Y`. This extends `L₁` (`lovasz_avoid_set`), which needs `y ∉ N(Y)`.
`avoid_of_reach` is the single-vertex form, and it is sharp: **`avoid_iff_reach`** — `Q(y)` can avoid
`x` iff the component of `y` in `G − x` is not contained in `N(x)`; the converse direction is
`mem_pathEndingAt_of_component_sub` (a count of ends in the component against edges from `x`).

Consequences: `conjNDegTwoOn` (the degree-two case of Conjecture N, unconditionally),
`conjN_of_tightTransferN` (TRN ⇒ N), `conjN_of_TR` (TR ∧ `TightTransferAdj` ⇒ N).

Proof (manuscript Sections 3–5).
1. Hang a leaf `ℓ = none` at `y` (`apex G {y}`); now `y` is the only vertex of positive even
   degree, and it suffices that every path meets `X = {ℓ} ∪ Y` at most once (`apexSep_meetsOnce`).
2. **Steering** (`Steer`, `steer_meetsOnce`). Run Lovász's Case I from the even vertex `y`, always
   with a target outside `X`: delete `g u`, and the target `u` becomes the even vertex. Fan's lemma
   with vertex sets (`fan_single_supp`) restores each edge and only adds the target `u ∉ X` to one
   path, so "every path meets `X` at most once" goes back up the chain (`fan_step_meetsOnce`). The
   target may be `y` itself: since `ℓ` is a leaf, the condition is about vertex sets only. The chain
   stops when the target is left isolated; then there is no even vertex, `ℓ` is a leaf at `y ∉ Y`,
   and `L₁` (`lovasz_avoid_set`) starts the chain.
3. **The chain exists** (`steer_of_inv`, `exists_inv_subgraph`). Let `H = K − X`. It suffices to
   have `S ≤ H` whose odd vertices other than `y` are odd vertices of `H` (all of them have no
   neighbour in `X`) at which `S` contains every edge; walking along `S` keeps this invariant and
   can only stop at such a vertex, which is then isolated (`steer_of_inv`). `S` is `H` with shortest
   paths from `y` to the odd vertices of its component other than a farthest one, `t`, toggled
   (`exists_toggle_walk`, `exists_inv_subgraph`); the parity of the component
   (`even_card_odd_reachable`) makes `y` odd in `S`. The witness `w` makes the component contain an
   odd vertex.
-/

open SimpleGraph

namespace Gallai

universe u

/-! ### The steered Case-I chain -/

section steer

variable {W : Type u}

/-- `Steer X K g`: Lovász's Case I can be run from `g` with targets outside `X` until the target
is left isolated. At each step the edge `gu` is deleted and `u` becomes the current vertex. -/
inductive Steer (X : Finset W) : SimpleGraph W → W → Prop
  | last {K : SimpleGraph W} {g u : W} : K.Adj g u → u ∉ X → (∀ v, K.Adj u v → v = g) →
      Steer X K g
  | step {K : SimpleGraph W} {g u : W} : K.Adj g u → u ∉ X → Steer X (delEdge K u g) u →
      Steer X K g

theorem Steer.exists_adj {X : Finset W} {K : SimpleGraph W} {g : W} (h : Steer X K g) :
    ∃ u, K.Adj g u := by
  cases h with
  | last h _ _ => exact ⟨_, h⟩
  | step h _ _ => exact ⟨_, h⟩

variable [Fintype W] [DecidableEq W]

/-- **One Fan step** (Lovász's Case I, the body of `sep_case_even`). If `z` is the only vertex of
positive even degree, `u ∈ N(z)` lies outside `X`, and `G − uz` has a Lovász decomposition meeting
`X` at most once per path, so has `G`. -/
theorem fan_step_meetsOnce (G : SimpleGraph W) [DecidableRel G.Adj] {X : Finset W} {z u : W}
    (hev : (evenSet G).card ≤ 1) (hz : z ∈ evenSet G) (huz : G.Adj u z) (huX : u ∉ X)
    (D' : PathDecomp (delEdge G u z)) (hD' : ∀ v, D'.ends v = (delEdge G u z).degree v % 2)
    (hsep' : MeetsOnce D' X) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ MeetsOnce D X := by
  have hzd := mem_evenSet_iff.mp hz
  have hne : u ≠ z := huz.ne
  have huniq : ∀ w ∈ evenSet G, w = z := fun w hw => Finset.card_le_one.mp hev w hw z hz
  have hdeg := delEdge_degree G huz
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
  refine ⟨D, fun w => ?_, meetsOnce_of_cover huX hsep' hcov⟩
  by_cases hwu : w = u
  · subst hwu
    have hupos : 0 < G.degree w := (G.degree_pos_iff_exists_adj w).mpr ⟨z, huz⟩
    have huodd : G.degree w % 2 = 1 := by
      have : w ∉ evenSet G := fun h => hne (huniq w h)
      rw [mem_evenSet_iff] at this
      omega
    rw [hDu, hD' w]
    omega
  · by_cases hwz : w = z
    · subst hwz
      omega
    · rw [hDo w hwu hwz, hD' w]
      have h := hdeg w
      simp only [hwu, hwz, ite_false, add_zero] at h
      rw [h]

/-- **The steered chain gives a separating decomposition.** Let `P` be a property of graphs kept
by deleting edges with both ends outside `X`, and suppose every graph with `P` and no vertex of
positive even degree has a Lovász decomposition meeting `X` at most once per path. If `g ∉ X` is
the only vertex of positive even degree of `K`, `K` has `P`, and `Steer X K g`, then `K` has such a
decomposition too. -/
theorem steer_meetsOnce {X : Finset W} (P : SimpleGraph W → Prop)
    (hP : ∀ K a b, P K → a ∉ X → b ∉ X → P (delEdge K a b))
    (hbase : ∀ (K : SimpleGraph W) [DecidableRel K.Adj], P K → (evenSet K).card = 0 →
      ∃ D : PathDecomp K, (∀ v, D.ends v = K.degree v % 2) ∧ MeetsOnce D X) :
    ∀ {K : SimpleGraph W} {g : W}, Steer X K g → ∀ [DecidableRel K.Adj], P K → g ∉ X →
      g ∈ evenSet K → (evenSet K).card ≤ 1 →
      ∃ D : PathDecomp K, (∀ v, D.ends v = K.degree v % 2) ∧ MeetsOnce D X := by
  intro K g hS
  induction hS with
  | @last K g u hgu huX hiso =>
    intro _ hPK hgX hg hev
    have hug : K.Adj u g := hgu.symm
    have hne : u ≠ g := hug.ne
    have huniq : ∀ w ∈ evenSet K, w = g := fun w hw => Finset.card_le_one.mp hev w hw g hg
    have hdeg := delEdge_degree K hug
    have hdu1 : K.degree u = 1 := by
      have : K.neighborFinset u = {g} := by
        ext v
        rw [mem_neighborFinset, Finset.mem_singleton]
        exact ⟨hiso v, fun h => h ▸ hug⟩
      rw [← card_neighborFinset_eq_degree, this, Finset.card_singleton]
    have hgd := mem_evenSet_iff.mp hg
    have hev0 : (evenSet (delEdge K u g)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro w hw
      obtain ⟨hpos, heven⟩ := mem_evenSet_iff.mp hw
      have h := hdeg w
      by_cases hwu : w = u
      · subst hwu
        simp only [ite_true, hne, ite_false, add_zero] at h
        omega
      · by_cases hwg : w = g
        · subst hwg
          simp only [hwu, ite_false, ite_true] at h
          omega
        · simp only [hwu, hwg, ite_false, add_zero] at h
          exact hwg (huniq w (mem_evenSet_iff.mpr ⟨h ▸ hpos, h ▸ heven⟩))
    obtain ⟨D', hD', hm'⟩ := hbase (delEdge K u g) (hP K u g hPK huX hgX) hev0
    exact fan_step_meetsOnce K hev hg hug huX D' hD' hm'
  | @step K g u hgu huX hS' ih =>
    intro _ hPK hgX hg hev
    have hug : K.Adj u g := hgu.symm
    have hne : u ≠ g := hug.ne
    have huniq : ∀ w ∈ evenSet K, w = g := fun w hw => Finset.card_le_one.mp hev w hw g hg
    have hdeg := delEdge_degree K hug
    have hgd := mem_evenSet_iff.mp hg
    have hupos : 0 < K.degree u := (K.degree_pos_iff_exists_adj u).mpr ⟨g, hug⟩
    have huodd : K.degree u % 2 = 1 := by
      have : u ∉ evenSet K := fun h => hne (huniq u h)
      rw [mem_evenSet_iff] at this
      omega
    have hdu := hdeg u
    simp only [ite_true, hne, ite_false, add_zero] at hdu
    obtain ⟨u', hu'⟩ := hS'.exists_adj
    have hupos' : 0 < (delEdge K u g).degree u :=
      ((delEdge K u g).degree_pos_iff_exists_adj u).mpr ⟨u', hu'⟩
    have hu_ev : u ∈ evenSet (delEdge K u g) := mem_evenSet_iff.mpr ⟨hupos', by omega⟩
    have hev' : evenSet (delEdge K u g) ⊆ {u} := by
      intro w hw
      rw [Finset.mem_singleton]
      obtain ⟨hpos, heven⟩ := mem_evenSet_iff.mp hw
      by_contra hwu
      have h := hdeg w
      by_cases hwg : w = g
      · subst hwg
        simp only [hwu, ite_false, ite_true] at h
        omega
      · simp only [hwu, hwg, ite_false, add_zero] at h
        exact hwg (huniq w (mem_evenSet_iff.mpr ⟨h ▸ hpos, h ▸ heven⟩))
    have hcard' : (evenSet (delEdge K u g)).card ≤ 1 :=
      (Finset.card_le_card hev').trans (by simp)
    obtain ⟨D', hD', hm'⟩ := ih (hP K u g hPK huX hgX) huX hu_ev hcard'
    exact fan_step_meetsOnce K hev hg hug huX D' hD' hm'

/-- **A subgraph invariant gives the chain.** Let `A` be a set of vertices. Suppose
`S ≤ K` has no edge at `X`, contains every edge of `K` at every vertex of `A`, every vertex other
than `c` of odd degree in `S` lies in `A`, `c` lies in `A` or has odd degree in `S`, and `c` has an
edge in `S`. Then `Steer X K c`. (Walk along `S`: each step keeps the invariant, and the walk can
only stop at a vertex of `A` whose edges are all used, which is then isolated in `K`.) -/
theorem steer_of_inv {X : Finset W} (A : W → Prop) :
    ∀ (n : ℕ) (K S : SimpleGraph W) [DecidableRel S.Adj] (c : W),
      ∑ w, S.degree w = n → S ≤ K → (∀ a b, S.Adj a b → b ∉ X) →
      (∀ v, A v → ∀ w, K.Adj v w → S.Adj v w) →
      (∀ v, v ≠ c → S.degree v % 2 = 1 → A v) →
      (A c ∨ S.degree c % 2 = 1) → 0 < S.degree c → Steer X K c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K S _ c hn hSK hSX hAK hodd hc hcpos
  obtain ⟨u, hcu⟩ := (S.degree_pos_iff_exists_adj c).mp hcpos
  have huX : u ∉ X := hSX c u hcu
  have huc : S.Adj u c := hcu.symm
  have hne : u ≠ c := huc.ne
  have hdeg := delEdge_degree S huc
  have hsum := delEdge_sum_degree S huc
  by_cases hstop : A u ∧ (delEdge S u c).degree u = 0
  · refine Steer.last (hSK hcu) huX (fun v hv => ?_)
    by_contra hvc
    have hSuv : (delEdge S u c).Adj u v := by
      refine ⟨hAK u hstop.1 v hv, ?_⟩
      rw [Sym2.eq_iff]
      rintro (⟨-, h⟩ | ⟨h1, -⟩)
      · exact hvc h
      · exact hne h1
    have : 0 < (delEdge S u c).degree u :=
      ((delEdge S u c).degree_pos_iff_exists_adj u).mpr ⟨v, hSuv⟩
    omega
  · refine Steer.step (hSK hcu) huX (ih (∑ w, (delEdge S u c).degree w) (by omega)
      (delEdge K u c) (delEdge S u c) u rfl ?_ ?_ ?_ ?_ ?_ ?_)
    · intro a b hab
      exact ⟨hSK hab.1, hab.2⟩
    · intro a b hab
      exact hSX a b hab.1
    · intro v hv w hvw
      exact ⟨hAK v hv w hvw.1, hvw.2⟩
    · intro v hvu hv
      have h := hdeg v
      by_cases hvc : v = c
      · subst hvc
        simp only [hvu, ite_false, ite_true] at h
        rcases hc with hc | hc
        · exact hc
        · omega
      · simp only [hvu, hvc, ite_false, add_zero] at h
        exact hodd v hvc (h ▸ hv)
    · by_cases hAu : A u
      · exact Or.inl hAu
      · right
        have h := hdeg u
        simp only [ite_true, hne, ite_false, add_zero] at h
        have : S.degree u % 2 ≠ 1 := fun h' => hAu (hodd u hne h')
        have hupos : 0 < S.degree u := (S.degree_pos_iff_exists_adj u).mpr ⟨c, huc⟩
        omega
    · by_cases hAu : A u
      · have : (delEdge S u c).degree u ≠ 0 := fun h0 => hstop ⟨hAu, h0⟩
        omega
      · have h := hdeg u
        simp only [ite_true, hne, ite_false, add_zero] at h
        have : S.degree u % 2 ≠ 1 := fun h' => hAu (hodd u hne h')
        have hupos : 0 < S.degree u := (S.degree_pos_iff_exists_adj u).mpr ⟨c, huc⟩
        omega

end steer

/-! ### The invariant subgraph: a parity correction by shortest paths -/

section parity

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- **Toggling a walk.** Toggling, one after another, the edges of a walk `p : a → b` of `H` in a
subgraph `J ≤ H` gives a subgraph `J' ≤ H` whose degree parities differ from those of `J` exactly
at `a` and `b`, and which agrees with `J` at every vertex off the walk. -/
theorem exists_toggle_walk (H : SimpleGraph W) :
    ∀ {a b : W} (p : H.Walk a b) (J : SimpleGraph W) [DecidableRel J.Adj], J ≤ H →
      ∃ (J' : SimpleGraph W) (_ : DecidableRel J'.Adj), J' ≤ H ∧
        (∀ v, J'.degree v % 2 =
          (J.degree v + (if v = a then 1 else 0) + (if v = b then 1 else 0)) % 2) ∧
        (∀ v, v ∉ p.support → ∀ z, (J'.Adj v z ↔ J.Adj v z)) := by
  intro a b p
  induction p with
  | nil =>
    intro J _ hJ
    refine ⟨J, inferInstance, hJ, fun v => ?_, fun _ _ _ => Iff.rfl⟩
    split_ifs <;> omega
  | @cons a c b hac p ih =>
    intro J _ hJ
    obtain ⟨J1, _, hJ1, hpar1, hoff1⟩ := ih J hJ
    have hne : a ≠ c := hac.ne
    by_cases hin : J1.Adj a c
    · refine ⟨delEdge J1 a c, inferInstance, fun x y h => hJ1 h.1, fun v => ?_, ?_⟩
      · have h := delEdge_degree J1 hin v
        have h1 := hpar1 v
        by_cases hva : v = a
        · subst hva
          simp only [ite_true, hne, ite_false] at h h1 ⊢
          omega
        · by_cases hvc : v = c
          · subst hvc
            simp only [ite_true, hva, ite_false] at h h1 ⊢
            omega
          · simp only [hva, hvc, ite_false, add_zero] at h h1 ⊢
            omega
      · intro v hv z
        rw [Walk.support_cons, List.mem_cons, not_or] at hv
        have hvc : v ≠ c := fun h => hv.2 (h ▸ p.start_mem_support)
        rw [← hoff1 v hv.2 z]
        constructor
        · exact fun h => h.1
        · intro h
          refine ⟨h, ?_⟩
          rw [Sym2.eq_iff]
          rintro (⟨h1, -⟩ | ⟨h1, -⟩)
          · exact hv.1 h1
          · exact hvc h1
    · refine ⟨plusEdge J1 a c, inferInstance, ?_, fun v => ?_, ?_⟩
      · intro x y h
        rcases h with h | ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact hJ1 h
        · exact hac
        · exact hac.symm
      · have h := plusEdge_degree (G := J1) hne hin v
        have h1 := hpar1 v
        rw [h]
        by_cases hva : v = a
        · subst hva
          simp only [true_or, ite_true, hne, ite_false] at h1 ⊢
          omega
        · by_cases hvc : v = c
          · subst hvc
            simp only [or_true, ite_true, hva, ite_false] at h1 ⊢
            omega
          · have hn : ¬ (v = a ∨ v = c) := fun h => h.elim hva hvc
            simp only [hva, hvc, or_self, ite_false, add_zero] at h1 ⊢
            omega
      · intro v hv z
        rw [Walk.support_cons, List.mem_cons, not_or] at hv
        have hvc : v ≠ c := fun h => hv.2 (h ▸ p.start_mem_support)
        rw [← hoff1 v hv.2 z, plusEdge_adj]
        constructor
        · rintro (h | ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩⟩)
          · exact h
          · exact absurd h1 hv.1
          · exact absurd h1 hvc
        · exact Or.inl

/-- The odd vertices of one component are even in number. -/
theorem even_card_odd_reachable (H : SimpleGraph W) [DecidableRel H.Adj] (s : W) :
    Even (Finset.univ.filter (fun v => H.Reachable s v ∧ H.degree v % 2 = 1)).card := by
  classical
  let Hc : SimpleGraph W :=
    { Adj := fun a b => H.Adj a b ∧ H.Reachable s a
      symm := ⟨fun a b h => ⟨h.1.symm, h.2.trans h.1.reachable⟩⟩
      loopless := ⟨fun a h => H.loopless.irrefl a h.1⟩ }
  have hdeg : ∀ v, Hc.degree v = if H.Reachable s v then H.degree v else 0 := by
    intro v
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
    split_ifs with hv
    · congr 1
      ext z
      simp only [mem_neighborFinset]
      exact ⟨fun h => h.1, fun h => ⟨h, hv⟩⟩
    · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro z hz
      rw [mem_neighborFinset] at hz
      exact hv hz.2
  have h := even_card_odd_degree_vertices Hc
  convert h using 2
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hdeg, Nat.odd_iff]
  split_ifs with hv <;> simp [hv]

/-- **The invariant subgraph.** Let `s` have even degree in `H`, and let the component of `s`
contain a vertex of odd degree. Then there are a vertex `t` and a subgraph `S ≤ H` such that
`S` contains every edge of `H` at `t` and at every vertex outside the component of `s`, and the odd
vertices of `S` are `s`, `t` and the odd vertices of `H` outside the component of `s`.

`t` is an odd vertex of the component at the largest distance from `s`; then every other odd vertex
`o` of the component is joined to `s` by a shortest path avoiding `t`, and toggling all these paths
in `H` gives `S`. -/
theorem exists_inv_subgraph (H : SimpleGraph W) [DecidableRel H.Adj] {s : W}
    (hs : H.degree s % 2 = 0) {w : W} (hsw : H.Reachable s w) (hw : H.degree w % 2 = 1) :
    ∃ (t : W) (S : SimpleGraph W) (_ : DecidableRel S.Adj), S ≤ H ∧
      (∀ v, (v = t ∨ ¬ H.Reachable s v) → ∀ z, (S.Adj v z ↔ H.Adj v z)) ∧
      (∀ v, S.degree v % 2 = 1 ↔ (v = s ∨ ((v = t ∨ ¬ H.Reachable s v) ∧ H.degree v % 2 = 1))) := by
  classical
  set O := Finset.univ.filter (fun v => H.Reachable s v ∧ H.degree v % 2 = 1) with hO
  have hwO : w ∈ O := by simp [hO, hsw, hw]
  obtain ⟨t, htO, hmax⟩ := O.exists_max_image (fun v => H.dist s v) ⟨w, hwO⟩
  have htO' := htO
  simp only [hO, Finset.mem_filter, Finset.mem_univ, true_and] at htO'
  have hst : s ≠ t := fun h => by rw [h] at hs; omega
  have hsO : s ∉ O := by simp [hO, hs]
  -- every other odd vertex of the component has a walk from `s` avoiding `t`
  have havoid : ∀ o ∈ O, o ≠ t → ∃ p : H.Walk s o, t ∉ p.support := by
    intro o ho hot
    have ho' := ho
    simp only [hO, Finset.mem_filter, Finset.mem_univ, true_and] at ho'
    obtain ⟨p, hp⟩ := ho'.1.exists_walk_length_eq_dist
    refine ⟨p, fun htp => ?_⟩
    have hspec := p.take_spec htp
    have hlen : p.length = (p.takeUntil t htp).length + (p.dropUntil t htp).length := by
      conv_lhs => rw [← hspec]
      exact Walk.length_append _ _
    have h1 : H.dist s t ≤ (p.takeUntil t htp).length := dist_le _
    have h2 : 0 < (p.dropUntil t htp).length := by
      rcases Nat.eq_zero_or_pos (p.dropUntil t htp).length with h | h
      · exact absurd (Walk.eq_of_length_eq_zero h) (Ne.symm hot)
      · exact h
    have h3 := hmax o ho
    omega
  have hreach_supp : ∀ {o : W} (p : H.Walk s o), ∀ v ∈ p.support, H.Reachable s v := by
    intro o p v hv
    exact ⟨p.takeUntil v hv⟩
  -- toggle the walks one by one, starting from `H`
  have key : ∀ T : Finset W, T ⊆ O.erase t →
      ∃ (J : SimpleGraph W) (_ : DecidableRel J.Adj), J ≤ H ∧
        (∀ v, (v = t ∨ ¬ H.Reachable s v) → ∀ z, (J.Adj v z ↔ H.Adj v z)) ∧
        (∀ v, J.degree v % 2 =
          (H.degree v + T.card * (if v = s then 1 else 0) + (if v ∈ T then 1 else 0)) % 2) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨H, inferInstance, le_refl _, fun _ _ _ => Iff.rfl, fun v => ?_⟩
      simp
    | @insert o T hoT ih =>
      intro hsub
      obtain ⟨J, _, hJH, hJoff, hJpar⟩ := ih ((Finset.subset_insert o T).trans hsub)
      have hoO : o ∈ O.erase t := hsub (Finset.mem_insert_self o T)
      rw [Finset.mem_erase] at hoO
      obtain ⟨p, htp⟩ := havoid o hoO.2 hoO.1
      obtain ⟨J', _, hJ'H, hJ'par, hJ'off⟩ := exists_toggle_walk H p J hJH
      refine ⟨J', inferInstance, hJ'H, fun v hv z => ?_, fun v => ?_⟩
      · have hvp : v ∉ p.support := by
          rcases hv with rfl | hv
          · exact htp
          · exact fun h => hv (hreach_supp p v h)
        rw [hJ'off v hvp z]
        exact hJoff v hv z
      · rw [hJ'par v, Finset.card_insert_of_notMem hoT]
        have hJv := hJpar v
        have hso : s ≠ o := fun h => hsO (h ▸ hoO.2)
        by_cases hvs : v = s
        · subst hvs
          have hvT : v ∉ insert o T := by
            intro h
            exact hsO ((Finset.erase_subset t O) (hsub h))
          have hvT' : v ∉ T := fun h => hvT (Finset.mem_insert_of_mem h)
          simp only [hvT, hvT', hso, ite_true, ite_false, add_zero] at hJv ⊢
          omega
        · by_cases hvo : v = o
          · subst hvo
            simp only [hvs, hoT, Finset.mem_insert_self, ite_true, ite_false, mul_zero,
              add_zero] at hJv ⊢
            omega
          · have : (v ∈ insert o T) ↔ v ∈ T := by
              rw [Finset.mem_insert]; exact ⟨fun h => h.resolve_left hvo, Or.inr⟩
            simp only [hvs, hvo, this, ite_false, mul_zero, add_zero] at hJv ⊢
            omega
  obtain ⟨S, _, hSH, hSoff, hSpar⟩ := key (O.erase t) (le_refl _)
  have hOeven := even_card_odd_reachable H s
  rw [← hO] at hOeven
  have hcard : (O.erase t).card % 2 = 1 := by
    rw [Finset.card_erase_of_mem htO]
    obtain ⟨k, hk⟩ := hOeven
    have : 0 < O.card := Finset.card_pos.mpr ⟨t, htO⟩
    omega
  refine ⟨t, S, inferInstance, hSH, hSoff, fun v => ?_⟩
  rw [hSpar v]
  by_cases hvs : v = s
  · subst hvs
    have : v ∉ O.erase t := fun h => hsO (Finset.mem_of_mem_erase h)
    simp only [this, ite_true, ite_false, add_zero, mul_one, true_or, iff_true]
    omega
  · by_cases hvt : v = t
    · subst hvt
      simp only [hvs, Finset.notMem_erase, ite_false, mul_zero, add_zero, true_or, true_and,
        false_or, htO'.2]
    · by_cases hvO : v ∈ O
      · have hv' := hvO
        simp only [hO, Finset.mem_filter, Finset.mem_univ, true_and] at hv'
        have : v ∈ O.erase t := Finset.mem_erase.mpr ⟨hvt, hvO⟩
        simp only [hvs, hvt, this, hv'.1, hv'.2, ite_false, ite_true, mul_zero, add_zero,
          not_true_eq_false, or_self, false_and, iff_false]
        omega
      · have : v ∉ O.erase t := fun h => hvO (Finset.mem_of_mem_erase h)
        simp only [hvs, hvt, this, ite_false, mul_zero, add_zero, false_or]
        simp only [hO, Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hvO
        by_cases hr : H.Reachable s v
        · have := hvO hr
          simp only [hr, not_true_eq_false, false_and, iff_false]
          omega
        · simp [hr]

end parity

/-! ### Neighbour avoidance -/

section na

variable {W : Type u}

/-- `K` with every edge at a vertex of `X` deleted. -/
def offX (K : SimpleGraph W) (X : Finset W) : SimpleGraph W where
  Adj a b := K.Adj a b ∧ a ∉ X ∧ b ∉ X
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun a h => K.loopless.irrefl a h.1⟩

instance offX.decRel [DecidableEq W] (K : SimpleGraph W) [DecidableRel K.Adj] (X : Finset W) :
    DecidableRel (offX K X).Adj := fun a b =>
  inferInstanceAs (Decidable (K.Adj a b ∧ a ∉ X ∧ b ∉ X))

theorem offX_degree [Fintype W] [DecidableEq W] (K : SimpleGraph W) [DecidableRel K.Adj]
    (X : Finset W) {v : W} (hv : v ∉ X) :
    (offX K X).degree v + (Finset.univ.filter (fun z => K.Adj v z ∧ z ∈ X)).card = K.degree v := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree, neighborFinset_eq_filter,
    neighborFinset_eq_filter (G := K), Finset.card_filter, Finset.card_filter, Finset.card_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  change ((if K.Adj v z ∧ v ∉ X ∧ z ∉ X then 1 else 0) + if K.Adj v z ∧ z ∈ X then 1 else 0) =
    if K.Adj v z then 1 else 0
  by_cases h1 : K.Adj v z <;> by_cases h2 : z ∈ X <;> simp [h1, h2, hv]

end na

/-! ### The set form, under the weak hypothesis -/

section setForm

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Deleting the leaf, keeping a packed set.** A decomposition of the leaf graph `apex G {c}`
with the end counts of `G` away from `c`, no end at `c`, and every path meeting `{ℓ} ∪ Y` at most
once gives a Lovász decomposition of `G` in which every path meets `Y` at most once and the path
ending at `c` avoids `Y` (the tail of `lovasz_avoid_set`). -/
theorem apexSep_meetsOnce (G : SimpleGraph V) [DecidableRel G.Adj] {c : V}
    (hc : G.degree c % 2 = 1) (DH : PathDecomp (apex G {c}))
    (hDH : ∀ w, w ≠ c → DH.ends (some w) = G.degree w % 2) (hc0 : DH.ends (some c) = 0)
    {Y : Finset V} (hsep : MeetsOnce DH (insert none (Y.image some))) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ MeetsOnce D Y ∧
      ∀ P ∈ D.paths, (P.src = c ∨ P.tgt = c) → ∀ y ∈ Y, y ∉ P.walk.support := by
  classical
  obtain ⟨D, hD, hcov⟩ := (apexRetract G {c} c).delete_supp DH (by
    intro P _ y hy hky
    cases y with
    | some _ => simp [apexRetract] at hky
    | none => exact (P.end_of_pendant apex_none_pendant hy).imp Eq.symm Eq.symm)
  have hmemX : ∀ q ∈ Y, some q ∈ insert none (Y.image some) := fun q hq =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hq)
  refine ⟨D, fun w => ?_, ?_, ?_⟩
  · by_cases hwc : w = c
    · subst hwc
      have hle := (hD w).2 (fun e₁ he₁ e₂ he₂ hk₁ hk₂ hv₁ hv₂ => by
        rw [(apex_nonkept he₁ hk₁ hv₁).1, (apex_nonkept he₂ hk₂ hv₂).1])
      change D.ends w ≤ DH.ends (some w) + 1 at hle
      rw [hc0] at hle
      have hp := D.ends_mod_two w
      rw [hc] at hp ⊢
      omega
    · rw [(hD w).1 (fun e he hk hwe => hwc (Finset.mem_singleton.mp (apex_nonkept he hk hwe).2))]
      change DH.ends (some w) = _
      exact hDH w hwc
  · intro Q hQ p hp q hq hpQ hqQ
    obtain ⟨P, hP, hPs, -⟩ := hcov Q hQ
    exact Option.some.inj (hsep P hP (some p) (hmemX p hp) (some q) (hmemX q hq)
      (hPs p hpQ) (hPs q hqQ))
  · intro Q hQ hend y hy hyQ
    obtain ⟨P, hP, hPs, hperm⟩ := hcov Q hQ
    have hyP : some y ∈ P.walk.support := hPs y hyQ
    have hnoneP : none ∉ P.walk.support := fun h =>
      absurd (hsep P hP none (Finset.mem_insert_self _ _) (some y) (hmemX y hy) h hyP)
        (by simp)
    have hsome : ∀ e ∈ P.edges, ∃ x y : V, e = s(some x, some y) := by
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

/-- **Avoiding a packed set that contains a neighbour (the set form of NA).** Let `G` have no vertex
of positive even degree, let `Y` be packed, and let `y ∉ Y` have odd degree. Suppose some vertex
`w` of positive degree with no neighbour in `Y` is joined to `y` by a walk avoiding `Y` (that is, the
component of `y` in `G − Y` is not contained in `N(Y)`). Then some Lovász decomposition of `G` has
every path meeting `Y` at most once and the path ending at `y` disjoint from `Y`.

When `y` has no neighbour in `Y` this is `L₁` (`lovasz_avoid_set`); the new case is `y ∈ N(Y)`. -/
theorem avoid_packed_of_reach (G : SimpleGraph V) [DecidableRel G.Adj]
    (hev : (evenSet G).card = 0) {Y : Finset V} (hY : Packed G Y) {y : V}
    (hy : G.degree y % 2 = 1) (hyY : y ∉ Y) {w : V} (p : G.Walk y w)
    (hp : ∀ v ∈ p.support, v ∉ Y) (hw : ∀ z, G.Adj w z → z ∉ Y) (hwpos : 0 < G.degree w) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ MeetsOnce D Y ∧
      ∀ P ∈ D.paths, (P.src = y ∨ P.tgt = y) → ∀ a ∈ Y, a ∉ P.walk.support := by
  classical
  by_cases hyN : ∀ a ∈ Y, ¬ G.Adj y a
  · exact lovasz_avoid_set G hev hy hY (fun a ha => ⟨fun h => hyY (h ▸ ha), hyN a ha⟩)
  obtain ⟨x, hxY, hyx⟩ : ∃ x ∈ Y, G.Adj y x := by
    by_contra h
    exact hyN (fun a ha hya => h ⟨a, ha, hya⟩)
  have hnoev : ∀ v, v ∉ evenSet G := fun v hv => by
    rw [Finset.card_eq_zero] at hev; rw [hev] at hv; simp at hv
  have hpar : ∀ v, 0 < G.degree v → G.degree v % 2 = 1 := fun v hv => by
    have := hnoev v; rw [mem_evenSet_iff] at this; omega
  set K := apex G {y} with hK
  set X : Finset (Option V) := insert none (Y.image some) with hX
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
  have hsomeX : ∀ v : V, some v ∈ X ↔ v ∈ Y := by intro v; simp [hX]
  have hyX : some y ∉ X := fun h => hyY ((hsomeX y).mp h)
  have hyK : some y ∈ evenSet K := by
    rw [mem_evenSet_iff, hKsome]
    simp only [ite_true]
    omega
  have hevK : (evenSet K).card ≤ 1 := by
    have : evenSet K ⊆ {some y} := by
      intro v hv
      rw [Finset.mem_singleton]
      rw [mem_evenSet_iff] at hv
      cases v with
      | none => rw [hKnone] at hv; omega
      | some v =>
        rw [hKsome] at hv
        by_cases hvy : v = y
        · rw [hvy]
        · simp only [hvy, ite_false, add_zero] at hv
          have := hpar v hv.1
          omega
    exact (Finset.card_le_card this).trans (by simp)
  -- neighbours in `Y`: at most one, by packing
  set nY : V → ℕ := fun v => (Finset.univ.filter (fun z => G.Adj v z ∧ z ∈ Y)).card with hnY
  have hnY1 : ∀ v, nY v ≤ 1 := by
    intro v
    rw [hnY]
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    by_contra hab
    exact (hY a ha.2 b hb.2 hab).2 v ⟨ha.1.symm, hb.1⟩
  have hnY0 : ∀ v, nY v = 0 ↔ ∀ z, G.Adj v z → z ∉ Y := by
    intro v
    rw [hnY, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    simp only [Finset.mem_univ, true_imp_iff, not_and]
  have hnYy : nY y = 1 := by
    have : nY y ≠ 0 := fun h => (hnY0 y).mp h x hyx hxY
    have := hnY1 y
    omega
  have hfilt : ∀ v : V, v ∉ Y →
      (Finset.univ.filter (fun z => K.Adj (some v) z ∧ z ∈ X)).card =
        (if v = y then 1 else 0) + nY v := by
    intro v hvY
    rw [Finset.card_filter, Fintype.sum_option]
    simp only [hnY]
    rw [Finset.card_filter]
    congr 1
    · simp [hK, hnoneX]
    · simp only [hK, apex_adj_some_some, hsomeX]
  have hHdeg : ∀ v : V, v ∉ Y → (offX K X).degree (some v) + nY v = G.degree v := by
    intro v hvY
    have h1 := offX_degree K X (fun h => hvY ((hsomeX v).mp h))
    rw [hfilt v hvY, hKsome] at h1
    omega
  have hstop : ∀ v, (offX K X).degree v % 2 = 1 → v ∉ X ∧ ∀ z, K.Adj v z → z ∉ X := by
    intro v hv
    have hvX : v ∉ X := by
      intro hvX
      have : (offX K X).degree v = 0 := by
        rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero,
          Finset.eq_empty_iff_forall_notMem]
        intro z hz
        rw [mem_neighborFinset] at hz
        exact hz.2.1 hvX
      omega
    refine ⟨hvX, fun z hz hzX => ?_⟩
    cases v with
    | none => exact hvX hnoneX
    | some v =>
      have hvY : v ∉ Y := fun h => hvX ((hsomeX v).mpr h)
      have hd := hHdeg v hvY
      cases z with
      | none =>
        have hvy : v = y := by simpa [hK] using hz
        subst hvy
        rw [hnYy] at hd
        have := hpar v (by omega)
        omega
      | some z =>
        have hzY : z ∈ Y := (hsomeX z).mp hzX
        have hvz : G.Adj v z := by simpa [hK] using hz
        have h1 : nY v = 1 := by
          have : nY v ≠ 0 := fun h => (hnY0 v).mp h z hvz hzY
          have := hnY1 v
          omega
        rw [h1] at hd
        have := hpar v (by omega)
        omega
  have hHy : (offX K X).degree (some y) % 2 = 0 := by
    have hd := hHdeg y hyY
    rw [hnYy] at hd
    omega
  -- the walk lifts to `H`
  have hlift : ∀ {a b : V} (q : G.Walk a b), (∀ v ∈ q.support, v ∉ Y) →
      (offX K X).Reachable (some a) (some b) := by
    intro a b q
    induction q with
    | nil => intro _; exact Reachable.refl _
    | @cons a c b hac q ih =>
      intro hq
      have ha : a ∉ Y := hq a (by simp)
      have hc : c ∉ Y := hq c (by simp)
      have hadj : (offX K X).Adj (some a) (some c) :=
        ⟨by simpa [hK] using hac, fun h => ha ((hsomeX a).mp h), fun h => hc ((hsomeX c).mp h)⟩
      exact hadj.reachable.trans (ih (fun v hv => hq v (by simp [hv])))
  have hwY : w ∉ Y := hp w p.end_mem_support
  have hHw : (offX K X).degree (some w) % 2 = 1 := by
    have hd := hHdeg w hwY
    rw [(hnY0 w).mpr hw, add_zero] at hd
    rw [hd]
    exact hpar w hwpos
  obtain ⟨t, S, _, hSH, hSoff, hSpar⟩ :=
    exists_inv_subgraph (offX K X) hHy (hlift p hp) hHw
  have hSteer : Steer X K (some y) := by
    refine steer_of_inv (fun v => (v ∉ X ∧ ∀ z, K.Adj v z → z ∉ X) ∧
        (v = t ∨ ¬ (offX K X).Reachable (some y) v)) _ K S (some y) rfl
      (fun a b h => (hSH h).1) (fun a b h => (hSH h).2.2) ?_ ?_ ?_ ?_
    · intro v hv z hvz
      exact (hSoff v hv.2 z).mpr ⟨hvz, hv.1.1, hv.1.2 z hvz⟩
    · intro v hvy hv
      have h := (hSpar v).mp hv
      rcases h with h | h
      · exact absurd h hvy
      · exact ⟨hstop v h.2, h.1⟩
    · exact Or.inr ((hSpar _).mpr (Or.inl rfl))
    · have := (hSpar (some y)).mpr (Or.inl rfl)
      omega
  obtain ⟨DH, hDH, hm⟩ := steer_meetsOnce (X := X)
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
      have hdn : K'.degree none = 1 := by
        rw [← card_neighborFinset_eq_degree]
        have : K'.neighborFinset none = {some y} := by
          ext z; rw [mem_neighborFinset, Finset.mem_singleton, hnK']
        rw [this, Finset.card_singleton]
      have hYK : Packed K' (Y.image some) := by
        intro a ha b hb hab
        obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
        have hab' : a' ≠ b' := fun h => hab (h ▸ rfl)
        refine ⟨fun h => (hY a' ha' b' hb' hab').1 (by simpa [hK] using hP.1 h), fun z hz => ?_⟩
        have h1 := hP.1 hz.1
        have h2 := hP.1 hz.2
        cases z with
        | none =>
          have : a' = y := by simpa [hK] using h1
          exact hyY (this ▸ ha')
        | some z =>
          exact (hY a' ha' b' hb' hab').2 z ⟨by simpa [hK] using h1, by simpa [hK] using h2⟩
      obtain ⟨D, hD, hmY, hav⟩ := lovasz_avoid_set K' hev' (c := none) (by rw [hdn])
        hYK (fun q hq => by
          obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
          refine ⟨by simp, fun h => ?_⟩
          rw [hnK'] at h
          exact hyY (Option.some.inj h ▸ hq'))
      refine ⟨D, hD, fun P hP a ha b hb haP hbP => ?_⟩
      have hpend : ∀ e ∈ K'.edgeSet, (none : Option V) ∈ e → e = s(none, some y) := by
        intro e he hne
        induction e using Sym2.inductionOn with
        | hf p q =>
          rw [mem_edgeSet] at he
          rcases Sym2.mem_iff.mp hne with rfl | rfl
          · rw [(hnK' q).mp he]
          · rw [(hnK' p).mp he.symm, Sym2.eq_swap]
      have hXc : ∀ c ∈ X, c ≠ none → c ∈ Y.image some := by
        intro c hc hcn
        rw [hX, Finset.mem_insert] at hc
        exact hc.resolve_left hcn
      have key : ∀ c ∈ X, c ∈ P.walk.support → c ≠ none →
          (none : Option V) ∉ P.walk.support := by
        intro c hc hcP hcn hnP
        exact hav P hP (P.end_of_pendant hpend hnP) c (hXc c hc hcn) hcP
      by_cases han : a = none
      · by_cases hbn : b = none
        · rw [han, hbn]
        · exact absurd (han ▸ haP) (key b hb hbP hbn)
      · by_cases hbn : b = none
        · exact absurd (hbn ▸ hbP) (key a ha haP han)
        · exact hmY P hP a (hXc a ha han) b (hXc b hb hbn) haP hbP)
    hSteer ⟨le_refl _, fun _ _ _ => Iff.rfl⟩ hyX hyK hevK
  refine apexSep_meetsOnce G hy DH (fun v hv => ?_) ?_ hm
  · rw [hDH, hKsome]; simp [hv]
  · rw [hDH, hKsome]; simp only [ite_true]; omega

/-- **The sharp single-vertex form.** If the component of `y` in `G − x` contains a vertex of positive
degree not adjacent to `x` (for instance a neighbour `w ≠ x` of `y` with `w ≁ x`), then some Lovász
decomposition has the path ending at `y` avoiding `x`. -/
theorem avoid_of_reach (G : SimpleGraph V) [DecidableRel G.Adj] (hev : (evenSet G).card = 0)
    {x y w : V} (hy : G.degree y % 2 = 1) (hxy : x ≠ y) (p : G.Walk y w)
    (hp : x ∉ p.support) (hw : ¬ G.Adj w x) (hwpos : 0 < G.degree w) : AvoidDecomp G y {x} := by
  have hY : Packed G {x} := by
    intro a ha b hb hab
    rw [Finset.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  obtain ⟨D, hD, -, hav⟩ := avoid_packed_of_reach G hev hY hy (by simpa using Ne.symm hxy) p
    (fun v hv h => hp (by rw [Finset.mem_singleton] at h; exact h ▸ hv))
    (fun z hz h => hw (by rw [Finset.mem_singleton] at h; exact h ▸ hz)) hwpos
  exact ⟨D, hD, hav⟩

/-- **Neighbour avoidance (NA).** Let `G` have no vertex of positive even degree, let `x ~ y`, and
let `y` have a neighbour `w ≠ x` not adjacent to `x`. Then some Lovász decomposition of `G` has
its path ending at `y` avoiding `x`. -/
theorem neighbourAvoid (G : SimpleGraph V) [DecidableRel G.Adj] (hev : (evenSet G).card = 0)
    {x y w : V} (hy : G.degree y % 2 = 1) (hxy : G.Adj x y) (hyw : G.Adj y w) (hwx : w ≠ x)
    (hxw : ¬ G.Adj x w) : AvoidDecomp G y {x} :=
  avoid_of_reach G hev hy hxy.ne (Walk.cons hyw Walk.nil)
    (by simp [hxy.ne, Ne.symm hwx]) (fun h => hxw h.symm)
    ((G.degree_pos_iff_exists_adj w).mpr ⟨y, hyw.symm⟩)

/-- **NA** in the form of `ConjN.lean`. -/
theorem neighbourAvoidOn : NeighbourAvoidOn V := by
  intro G _ hev x y hy hxy ⟨w, hyw, hwx, hxw⟩
  exact neighbourAvoid G hev hy hxy hyw hwx hxw

end setForm

/-! ### The boundary is exact -/

section boundary

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Strict comparison of list sums. -/
theorem list_sum_lt_sum {α : Type*} (f g : α → ℕ) :
    ∀ (L : List α), (∀ a ∈ L, f a ≤ g a) → (∃ a ∈ L, f a < g a) →
      (L.map f).sum < (L.map g).sum := by
  intro L
  induction L with
  | nil => intro _ h; simp at h
  | cons a L ih =>
    intro hle hlt
    simp only [List.map_cons, List.sum_cons]
    have ha := hle a (List.mem_cons_self ..)
    have hrest : ∀ b ∈ L, f b ≤ g b := fun b hb => hle b (List.mem_cons_of_mem _ hb)
    have hsum : (L.map f).sum ≤ (L.map g).sum := by
      clear ih hlt hle ha
      induction L with
      | nil => simp
      | cons b L ih' =>
        simp only [List.map_cons, List.sum_cons]
        have := hrest b (List.mem_cons_self ..)
        have := ih' (fun c hc => hrest c (List.mem_cons_of_mem _ hc))
        omega
    obtain ⟨b, hb, hfb⟩ := hlt
    rcases List.mem_cons.mp hb with rfl | hb
    · omega
    · have := ih hrest ⟨b, hb, hfb⟩
      omega

omit [Fintype V] [DecidableEq V] in
/-- Exchanging a list sum and a finset sum. -/
theorem list_sum_finset_sum {α β : Type*} (C : Finset β) (f : α → β → ℕ) :
    ∀ L : List α, (L.map (fun a => ∑ b ∈ C, f a b)).sum = ∑ b ∈ C, (L.map (fun a => f a b)).sum := by
  intro L
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

/-- **The boundary (manuscript Theorem 1.4).** Let `G` have no vertex of positive even degree, let
`x ≠ y`, and suppose every vertex joined to `y` by a walk avoiding `x` is adjacent to `x` (the
component of `y` in `G − x` lies in `N(x)`). Then in every Lovász decomposition the path ending at `y`
contains `x`.

Proof: count, over the paths, the ends in that component `C` and the edges from `x` to `C`. Both
totals are `|C|`. A path through `x` has as many of each (its two halves leave `x` and stay in `C`
until they end), a path avoiding `x` has no such edge, and `Q(y)` would have ends but no such edge. -/
theorem mem_pathEndingAt_of_component_sub (G : SimpleGraph V) [DecidableRel G.Adj]
    (hev : (evenSet G).card = 0) {x y : V} (hxy : x ≠ y)
    (hC : ∀ v (p : G.Walk y v), x ∉ p.support → G.Adj v x)
    (D : PathDecomp G) (hD : ∀ v, D.ends v = G.degree v % 2) :
    ∀ P ∈ D.paths, (P.src = y ∨ P.tgt = y) → x ∈ P.walk.support := by
  classical
  have hnoev : ∀ v, v ∉ evenSet G := fun v hv => by
    rw [Finset.card_eq_zero] at hev; rw [hev] at hv; simp at hv
  have hpar : ∀ v, 0 < G.degree v → G.degree v % 2 = 1 := fun v hv => by
    have := hnoev v; rw [mem_evenSet_iff] at this; omega
  -- the component and the edges from `x` into it
  set C : Finset V := Finset.univ.filter (fun v => ∃ p : G.Walk y v, x ∉ p.support) with hCdef
  have hmemC : ∀ v, v ∈ C ↔ ∃ p : G.Walk y v, x ∉ p.support := by
    intro v; simp [hCdef]
  have hxC : x ∉ C := by
    rw [hmemC]; rintro ⟨p, hp⟩; exact hp p.end_mem_support
  have hyC : y ∈ C := (hmemC y).mpr ⟨Walk.nil, by simpa using hxy⟩
  have hCadj : ∀ v ∈ C, G.Adj v x := fun v hv => by
    obtain ⟨p, hp⟩ := (hmemC v).mp hv; exact hC v p hp
  -- walks avoiding `x` stay in or out of `C`
  have hstay : ∀ {a b : V} (q : G.Walk a b), x ∉ q.support → (a ∈ C ↔ b ∈ C) := by
    intro a b q hq
    constructor
    · intro ha
      obtain ⟨p, hp⟩ := (hmemC a).mp ha
      refine (hmemC b).mpr ⟨p.append q, fun h => ?_⟩
      rcases (Walk.mem_support_append_iff p q).mp h with h | h
      · exact hp h
      · exact hq h
    · intro hb
      obtain ⟨p, hp⟩ := (hmemC b).mp hb
      refine (hmemC a).mpr ⟨p.append q.reverse, fun h => ?_⟩
      rcases (Walk.mem_support_append_iff p q.reverse).mp h with h | h
      · exact hp h
      · rw [Walk.support_reverse, List.mem_reverse] at h; exact hq h
  set EX : Finset (Sym2 V) := C.image (fun v => s(x, v)) with hEX
  have hmemEX : ∀ v, s(x, v) ∈ EX ↔ v ∈ C := by
    intro v
    rw [hEX, Finset.mem_image]
    constructor
    · rintro ⟨u, hu, he⟩
      rw [Sym2.congr_right.mp he] at hu
      exact hu
    · intro hv; exact ⟨v, hv, rfl⟩
  have hEXx : ∀ e ∈ EX, x ∈ e := by
    intro e he
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp he
    exact Sym2.mem_mk_left _ _
  -- edges of `x`-free walks are not in `EX`
  have hfree : ∀ {a b : V} (q : G.Walk a b), x ∉ q.support →
      q.edges.countP (fun e => decide (e ∈ EX)) = 0 := by
    intro a b q hq
    rw [List.countP_eq_zero]
    intro e he hdec
    have hxe := hEXx e (of_decide_eq_true hdec)
    induction e using Sym2.inductionOn with
    | hf p r =>
      rcases Sym2.mem_iff.mp hxe with rfl | rfl
      · exact hq (Walk.fst_mem_support_of_mem_edges _ he)
      · exact hq (Walk.snd_mem_support_of_mem_edges _ he)
  -- a walk leaving `x` once: one edge of `EX` exactly when it ends in `C`
  have hfromx : ∀ {b : V} (r : G.Walk x b), x ∉ r.support.tail →
      r.edges.countP (fun e => decide (e ∈ EX)) = if b ∈ C then 1 else 0 := by
    intro b r hr
    cases r with
    | nil => simp [hxC]
    | @cons _ v _ h r' =>
      rw [Walk.support_cons, List.tail_cons] at hr
      rw [Walk.edges_cons, List.countP_cons, hfree r' hr, zero_add]
      have := hstay r' hr
      by_cases hv : v ∈ C
      · simp [(hmemEX v).mpr hv, this.mp hv]
      · have hb : b ∉ C := fun hb => hv (this.mpr hb)
        simp [hb, (hmemEX v).not.mpr hv]
  -- per path: edges of `EX` at most ends in `C`
  let e : GPath G → ℕ := fun P => P.edges.countP (fun e => decide (e ∈ EX))
  let n : GPath G → ℕ := fun P => ∑ v ∈ C, P.endsAt v
  have hn : ∀ P : GPath G, n P = (if P.src ∈ C then 1 else 0) + (if P.tgt ∈ C then 1 else 0) := by
    intro P
    simp only [n, GPath.endsAt, Finset.sum_add_distrib]
    congr 1 <;> simp [Finset.sum_ite_eq]
  have hle : ∀ P : GPath G, e P ≤ n P := by
    intro P
    rw [hn]
    by_cases hxP : x ∈ P.walk.support
    · have hsplit := P.walk.take_spec hxP
      have hpath := P.isPath
      have hta : (P.walk.takeUntil x hxP).IsPath := hpath.takeUntil hxP
      have hdr : (P.walk.dropUntil x hxP).IsPath := hpath.dropUntil hxP
      have hE : e P = (P.walk.takeUntil x hxP).reverse.edges.countP (fun e => decide (e ∈ EX)) +
          (P.walk.dropUntil x hxP).edges.countP (fun e => decide (e ∈ EX)) := by
        simp only [e, GPath.edges]
        conv_lhs => rw [← hsplit]
        rw [Walk.edges_append, List.countP_append, Walk.edges_reverse, List.countP_reverse]
      have h1 : x ∉ (P.walk.takeUntil x hxP).reverse.support.tail := by
        have hnd := hta.reverse.support_nodup
        rw [← Walk.cons_tail_support] at hnd
        exact (List.nodup_cons.mp hnd).1
      have h2 : x ∉ (P.walk.dropUntil x hxP).support.tail := by
        have hnd := hdr.support_nodup
        rw [← Walk.cons_tail_support] at hnd
        exact (List.nodup_cons.mp hnd).1
      rw [hE, hfromx _ h1, hfromx _ h2]
    · simp only [e, GPath.edges, hfree P.walk hxP]
      omega
  -- the sums
  have hsum_e : (D.paths.map e).sum = C.card := by
    have hcount : (D.paths.map e).sum =
        (D.paths.flatMap GPath.edges).countP (fun e => decide (e ∈ EX)) := by
      simp only [e]
      clear hle
      induction D.paths with
      | nil => simp
      | cons P L ih => simp [List.flatMap_cons, List.countP_append, ih]
    rw [hcount, List.countP_eq_length_filter]
    have hnd : ((D.paths.flatMap GPath.edges).filter (fun e => decide (e ∈ EX))).Nodup :=
      D.nodup_edges.filter _
    rw [← List.toFinset_card_of_nodup hnd]
    have : ((D.paths.flatMap GPath.edges).filter (fun e => decide (e ∈ EX))).toFinset = EX := by
      ext f
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · intro hf
        refine ⟨(D.covers f).mp ?_, hf⟩
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hf
        exact (hCadj v hv).symm
    rw [this, hEX, Finset.card_image_of_injective _ (fun a b h => Sym2.congr_right.mp h)]
  have hsum_n : (D.paths.map n).sum = C.card := by
    simp only [n]
    rw [list_sum_finset_sum C (fun P v => P.endsAt v) D.paths]
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro v hv
    have := hD v
    unfold PathDecomp.ends at this
    rw [this]
    exact hpar v ((G.degree_pos_iff_exists_adj v).mpr ⟨x, hCadj v hv⟩)
  intro P hP hend
  by_contra hxP
  have hlt : e P < n P := by
    rw [hn]
    simp only [e, GPath.edges, hfree P.walk hxP]
    have hsC : P.src ∈ C ↔ P.tgt ∈ C := hstay P.walk hxP
    rcases hend with h | h
    · rw [h] at hsC ⊢; simp [hyC]
    · rw [h] at hsC ⊢; simp [hyC]
  have := list_sum_lt_sum e n D.paths (fun P _ => hle P) ⟨P, hP, hlt⟩
  omega

/-- **The exact boundary, both directions.** In a graph with no vertex of positive even degree, for
distinct `x, y` with `y` odd: `Q(y)` can avoid `x` if and only if some vertex of positive degree joined
to `y` by a walk avoiding `x` is not adjacent to `x`. -/
theorem avoid_iff_reach (G : SimpleGraph V) [DecidableRel G.Adj] (hev : (evenSet G).card = 0)
    {x y : V} (hxy : x ≠ y) (hy : G.degree y % 2 = 1) :
    AvoidDecomp G y {x} ↔
      ∃ (w : V) (p : G.Walk y w), x ∉ p.support ∧ ¬ G.Adj w x ∧ 0 < G.degree w := by
  constructor
  · intro ⟨D, hD, hav⟩
    by_contra hno
    have hC : ∀ v (p : G.Walk y v), x ∉ p.support → G.Adj v x := by
      intro v p hp
      by_contra hvx
      have hpos : 0 < G.degree v := by
        by_cases hvy : v = y
        · subst hvy; omega
        · obtain ⟨u, h, -, -⟩ := Walk.exists_eq_cons_of_ne hvy p.reverse
          exact (G.degree_pos_iff_exists_adj v).mpr ⟨u, h⟩
      exact hno ⟨v, p, hp, hvx, hpos⟩
    obtain ⟨P, hP, hend⟩ : ∃ P ∈ D.paths, P.src = y ∨ P.tgt = y := by
      have h1 : D.ends y = 1 := by rw [hD y, hy]
      unfold PathDecomp.ends at h1
      by_contra hno'
      push Not at hno'
      have : (D.paths.map (fun P => P.endsAt y)).sum = 0 := by
        apply List.sum_eq_zero
        intro k hk
        obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hk
        simp [GPath.endsAt, hno' P hP]
      omega
    exact hav P hP hend x (Finset.mem_singleton_self x)
      (mem_pathEndingAt_of_component_sub G hev hxy hC D hD P hP hend)
  · rintro ⟨w, p, hp, hw, hwpos⟩
    exact avoid_of_reach G hev hy hxy p hp hw hwpos

/-- **The boundary of the set form.** Let `G` have no vertex of positive even degree, let `Y` be
packed, let `y ∉ Y`, and suppose every vertex joined to `y` by a walk avoiding `Y` has a neighbour in
`Y`. Then in every Lovász decomposition that meets `Y` at most once per path, the path ending at `y`
meets `Y`. (The same count as `mem_pathEndingAt_of_component_sub`, with the edges between `Y` and the
component; packing makes each vertex of the component send exactly one of them, and meeting `Y` at most
once makes both halves of a path through `Y` stay in the component.) -/
theorem meets_of_component_sub (G : SimpleGraph V) [DecidableRel G.Adj]
    (hev : (evenSet G).card = 0) {Y : Finset V} (hY : Packed G Y) {y : V} (hyY : y ∉ Y)
    (hC : ∀ v (p : G.Walk y v), (∀ u ∈ p.support, u ∉ Y) → ∃ a ∈ Y, G.Adj v a)
    (D : PathDecomp G) (hD : ∀ v, D.ends v = G.degree v % 2) (hm : MeetsOnce D Y) :
    ∀ P ∈ D.paths, (P.src = y ∨ P.tgt = y) → ∃ a ∈ Y, a ∈ P.walk.support := by
  classical
  have hnoev : ∀ v, v ∉ evenSet G := fun v hv => by
    rw [Finset.card_eq_zero] at hev; rw [hev] at hv; simp at hv
  have hpar : ∀ v, 0 < G.degree v → G.degree v % 2 = 1 := fun v hv => by
    have := hnoev v; rw [mem_evenSet_iff] at this; omega
  set C : Finset V := Finset.univ.filter
    (fun v => ∃ p : G.Walk y v, ∀ u ∈ p.support, u ∉ Y) with hCdef
  have hmemC : ∀ v, v ∈ C ↔ ∃ p : G.Walk y v, ∀ u ∈ p.support, u ∉ Y := by
    intro v; simp [hCdef]
  have hYC : ∀ v ∈ C, v ∉ Y := by
    intro v hv hvY
    obtain ⟨p, hp⟩ := (hmemC v).mp hv
    exact hp v p.end_mem_support hvY
  have hyC : y ∈ C := (hmemC y).mpr ⟨Walk.nil, by simpa using hyY⟩
  have hCadj : ∀ v ∈ C, ∃ a ∈ Y, G.Adj v a := fun v hv => by
    obtain ⟨p, hp⟩ := (hmemC v).mp hv; exact hC v p hp
  -- the neighbour in `Y` is unique
  have huniq : ∀ v a b, a ∈ Y → b ∈ Y → G.Adj v a → G.Adj v b → a = b := by
    intro v a b ha hb hva hvb
    by_contra hab
    exact (hY a ha b hb hab).2 v ⟨hva.symm, hvb⟩
  have hstay : ∀ {a b : V} (q : G.Walk a b), (∀ u ∈ q.support, u ∉ Y) → (a ∈ C ↔ b ∈ C) := by
    intro a b q hq
    constructor
    · intro ha
      obtain ⟨p, hp⟩ := (hmemC a).mp ha
      refine (hmemC b).mpr ⟨p.append q, fun u hu => ?_⟩
      rcases (Walk.mem_support_append_iff p q).mp hu with h | h
      · exact hp u h
      · exact hq u h
    · intro hb
      obtain ⟨p, hp⟩ := (hmemC b).mp hb
      refine (hmemC a).mpr ⟨p.append q.reverse, fun u hu => ?_⟩
      rcases (Walk.mem_support_append_iff p q.reverse).mp hu with h | h
      · exact hp u h
      · rw [Walk.support_reverse, List.mem_reverse] at h; exact hq u h
  -- the edges between `Y` and `C`
  let f : V → V := fun v => if h : ∃ a ∈ Y, G.Adj v a then h.choose else v
  have hf : ∀ v ∈ C, f v ∈ Y ∧ G.Adj v (f v) := by
    intro v hv
    have h := hCadj v hv
    simp only [f, h, dite_true]
    exact h.choose_spec
  set EX : Finset (Sym2 V) := C.image (fun v => s(f v, v)) with hEX
  have hmemEX : ∀ a v, a ∈ Y → (s(a, v) ∈ EX ↔ v ∈ C ∧ G.Adj v a) := by
    intro a v ha
    rw [hEX, Finset.mem_image]
    constructor
    · rintro ⟨u, hu, he⟩
      rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h2; rw [← h1]; exact ⟨hu, (hf u hu).2⟩
      · exact absurd (h2 ▸ ha) (hYC u hu)
    · rintro ⟨hv, hva⟩
      refine ⟨v, hv, ?_⟩
      rw [huniq v (f v) a (hf v hv).1 ha (hf v hv).2 hva]
  have hEXY : ∀ e ∈ EX, ∃ a ∈ Y, a ∈ e := by
    intro e he
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
    exact ⟨f v, (hf v hv).1, Sym2.mem_mk_left _ _⟩
  have hfree : ∀ {a b : V} (q : G.Walk a b), (∀ u ∈ q.support, u ∉ Y) →
      q.edges.countP (fun e => decide (e ∈ EX)) = 0 := by
    intro a b q hq
    rw [List.countP_eq_zero]
    intro e he hdec
    obtain ⟨c, hcY, hce⟩ := hEXY e (of_decide_eq_true hdec)
    induction e using Sym2.inductionOn with
    | hf p r =>
      rcases Sym2.mem_iff.mp hce with rfl | rfl
      · exact hq _ (Walk.fst_mem_support_of_mem_edges _ he) hcY
      · exact hq _ (Walk.snd_mem_support_of_mem_edges _ he) hcY
  have hfromY : ∀ {a b : V} (r : G.Walk a b), a ∈ Y → (∀ u ∈ r.support.tail, u ∉ Y) →
      r.edges.countP (fun e => decide (e ∈ EX)) = if b ∈ C then 1 else 0 := by
    intro a b r ha hr
    cases r with
    | nil => simp [hYC a |>.mt (not_not.mpr ha)]
    | @cons _ v _ h r' =>
      rw [Walk.support_cons, List.tail_cons] at hr
      rw [Walk.edges_cons, List.countP_cons, hfree r' hr, zero_add]
      have := hstay r' hr
      by_cases hv : v ∈ C
      · simp [(hmemEX a v ha).mpr ⟨hv, h.symm⟩, this.mp hv]
      · have hb : b ∉ C := fun hb => hv (this.mpr hb)
        have : s(a, v) ∉ EX := fun h' => hv ((hmemEX a v ha).mp h').1
        simp [hb, this]
  let e : GPath G → ℕ := fun P => P.edges.countP (fun e => decide (e ∈ EX))
  let n : GPath G → ℕ := fun P => ∑ v ∈ C, P.endsAt v
  have hn : ∀ P : GPath G, n P = (if P.src ∈ C then 1 else 0) + (if P.tgt ∈ C then 1 else 0) := by
    intro P
    simp only [n, GPath.endsAt, Finset.sum_add_distrib]
    congr 1 <;> simp [Finset.sum_ite_eq]
  have hle : ∀ P ∈ D.paths, e P ≤ n P := by
    intro P hP
    rw [hn]
    by_cases hmeet : ∃ a ∈ Y, a ∈ P.walk.support
    · obtain ⟨a, haY, haP⟩ := hmeet
      have honly : ∀ u ∈ P.walk.support, u ∈ Y → u = a := fun u hu huY =>
        hm P hP u huY a haY hu haP
      have hsplit := P.walk.take_spec haP
      have hpath := P.isPath
      have hta : (P.walk.takeUntil a haP).IsPath := hpath.takeUntil haP
      have hdr : (P.walk.dropUntil a haP).IsPath := hpath.dropUntil haP
      have hE : e P = (P.walk.takeUntil a haP).reverse.edges.countP (fun e => decide (e ∈ EX)) +
          (P.walk.dropUntil a haP).edges.countP (fun e => decide (e ∈ EX)) := by
        simp only [e, GPath.edges]
        conv_lhs => rw [← hsplit]
        rw [Walk.edges_append, List.countP_append, Walk.edges_reverse, List.countP_reverse]
      have hsub1 : ∀ u ∈ (P.walk.takeUntil a haP).reverse.support, u ∈ P.walk.support := by
        intro u hu
        rw [Walk.support_reverse, List.mem_reverse] at hu
        exact P.walk.support_takeUntil_subset_support haP hu
      have hsub2 : ∀ u ∈ (P.walk.dropUntil a haP).support, u ∈ P.walk.support := by
        intro u hu
        exact P.walk.support_dropUntil_subset_support haP hu
      have h1 : ∀ u ∈ (P.walk.takeUntil a haP).reverse.support.tail, u ∉ Y := by
        intro u hu huY
        have hnd := hta.reverse.support_nodup
        rw [← Walk.cons_tail_support] at hnd
        have hua := honly u (hsub1 u (List.mem_of_mem_tail hu)) huY
        subst hua
        exact (List.nodup_cons.mp hnd).1 hu
      have h2 : ∀ u ∈ (P.walk.dropUntil a haP).support.tail, u ∉ Y := by
        intro u hu huY
        have hnd := hdr.support_nodup
        rw [← Walk.cons_tail_support] at hnd
        have hua := honly u (hsub2 u (List.mem_of_mem_tail hu)) huY
        subst hua
        exact (List.nodup_cons.mp hnd).1 hu
      rw [hE, hfromY _ haY h1, hfromY _ haY h2]
    · push Not at hmeet
      simp only [e, GPath.edges, hfree P.walk (fun u hu huY => hmeet u huY hu)]
      omega
  have hsum_e : (D.paths.map e).sum = C.card := by
    have hcount : (D.paths.map e).sum =
        (D.paths.flatMap GPath.edges).countP (fun e => decide (e ∈ EX)) := by
      simp only [e]
      clear hle
      induction D.paths with
      | nil => simp
      | cons P L ih => simp [List.flatMap_cons, List.countP_append, ih]
    rw [hcount, List.countP_eq_length_filter]
    have hnd : ((D.paths.flatMap GPath.edges).filter (fun e => decide (e ∈ EX))).Nodup :=
      D.nodup_edges.filter _
    rw [← List.toFinset_card_of_nodup hnd]
    have : ((D.paths.flatMap GPath.edges).filter (fun e => decide (e ∈ EX))).toFinset = EX := by
      ext g
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · intro hg
        refine ⟨(D.covers g).mp ?_, hg⟩
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hg
        exact (hf v hv).2.symm
    rw [this, hEX, Finset.card_image_of_injOn]
    intro a ha b hb hab
    simp only at hab
    rcases Sym2.eq_iff.mp hab with ⟨-, h⟩ | ⟨h1, -⟩
    · exact h
    · exact absurd (h1 ▸ (hf a ha).1) (hYC b hb)
  have hsum_n : (D.paths.map n).sum = C.card := by
    simp only [n]
    rw [list_sum_finset_sum C (fun P v => P.endsAt v) D.paths]
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro v hv
    have := hD v
    unfold PathDecomp.ends at this
    rw [this]
    obtain ⟨a, -, hva⟩ := hCadj v hv
    exact hpar v ((G.degree_pos_iff_exists_adj v).mpr ⟨a, hva⟩)
  intro P hP hend
  by_contra hno
  push Not at hno
  have hfreeP : ∀ u ∈ P.walk.support, u ∉ Y := fun u hu huY => hno u huY hu
  have hlt : e P < n P := by
    rw [hn]
    simp only [e, GPath.edges, hfree P.walk hfreeP]
    have hsC : P.src ∈ C ↔ P.tgt ∈ C := hstay P.walk hfreeP
    rcases hend with h | h
    · rw [h] at hsC ⊢; simp [hyC]
    · rw [h] at hsC ⊢; simp [hyC]
  have := list_sum_lt_sum e n D.paths hle ⟨P, hP, hlt⟩
  omega

/-- **Theorem A is sharp.** For `Y` packed and `y ∉ Y` odd: some Lovász decomposition meets `Y` at most
once per path with `Q(y) ∩ Y = ∅` **iff** the component of `y` in `G − Y` contains a vertex of
positive degree with no neighbour in `Y`. -/
theorem avoid_packed_iff_reach (G : SimpleGraph V) [DecidableRel G.Adj]
    (hev : (evenSet G).card = 0) {Y : Finset V} (hY : Packed G Y) {y : V}
    (hy : G.degree y % 2 = 1) (hyY : y ∉ Y) :
    (∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ MeetsOnce D Y ∧
      ∀ P ∈ D.paths, (P.src = y ∨ P.tgt = y) → ∀ a ∈ Y, a ∉ P.walk.support) ↔
    ∃ (w : V) (p : G.Walk y w), (∀ u ∈ p.support, u ∉ Y) ∧ (∀ z, G.Adj w z → z ∉ Y) ∧
      0 < G.degree w := by
  constructor
  · rintro ⟨D, hD, hm, hav⟩
    by_contra hno
    have hC : ∀ v (p : G.Walk y v), (∀ u ∈ p.support, u ∉ Y) → ∃ a ∈ Y, G.Adj v a := by
      intro v p hp
      by_contra hva
      push Not at hva
      have hpos : 0 < G.degree v := by
        by_cases hvy : v = y
        · subst hvy; omega
        · obtain ⟨u, h, -, -⟩ := Walk.exists_eq_cons_of_ne hvy p.reverse
          exact (G.degree_pos_iff_exists_adj v).mpr ⟨u, h⟩
      exact hno ⟨v, p, hp, fun z hz hzY => hva z hzY hz, hpos⟩
    obtain ⟨P, hP, hend⟩ : ∃ P ∈ D.paths, P.src = y ∨ P.tgt = y := by
      have h1 : D.ends y = 1 := by rw [hD y, hy]
      unfold PathDecomp.ends at h1
      by_contra hno'
      push Not at hno'
      have : (D.paths.map (fun P => P.endsAt y)).sum = 0 := by
        apply List.sum_eq_zero
        intro k hk
        obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hk
        simp [GPath.endsAt, hno' P hP]
      omega
    obtain ⟨a, haY, haP⟩ := meets_of_component_sub G hev hY hyY hC D hD hm P hP hend
    exact hav P hP hend a haY haP
  · rintro ⟨w, p, hp, hw, hwpos⟩
    exact avoid_packed_of_reach G hev hY hy hyY p hp hw hwpos

end boundary

/-! ### Consequences for Conjecture N -/

section consequences

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **The degree-two case of Conjecture N** (`N(g) = {x, y}`) holds unconditionally. -/
theorem conjNDegTwoOn : ConjNDegTwoOn V :=
  conjNDegTwo_of_neighbourAvoid neighbourAvoidOn

/-- **Conjecture N follows from TRN alone.** -/
theorem conjN_of_tightTransferN (hT : TightTransferNOn V) : ConjNOn V :=
  conjN_of_tight_neighbourAvoid hT neighbourAvoidOn

/-- **Conjecture N follows from TR and its counterpart for tails adjacent to `g`.** -/
theorem conjN_of_TR (h1 : TightTransfer.{u}) (h2 : TightTransferAdj.{u}) : ConjNOn V :=
  conjN_of_TR_neighbourAvoid h1 h2 neighbourAvoidOn

end consequences

end Gallai
