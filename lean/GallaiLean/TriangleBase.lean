import GallaiLean.DirectTest1

/-!
# Triangle bases from the single-vertex tools (session `claude/triangle-base`)

Manuscript: `manuscripts/direct-test1/direct-test1.tex`, §7.

The triangle base conjecture (`TriangleBaseConj`, manuscript Conjecture 3.1) asks for a Lovász
decomposition of `M = J − zw − {zaᵢ, zbᵢ, aᵢbᵢ}` in which, for every pair, the path ending at `bᵢ`
avoids `aᵢ` or the path ending at `aᵢ` avoids `bᵢ`. In `M` the only even vertex is `w`, and each
pair is non-adjacent. This file proves the cases reached by the project's single-vertex tools.

* `TriangleData.triM_evenSet`: `M` has at most one vertex of positive even degree.
* **`triangleBase_of_packed`**: if the pair vertices are pairwise at distance `≥ 3` in `M`, a base
  exists (separation, `separation_set`), for every `m`.
* **`triangleBase_of_farApart`**: for one pair (`d(z) = 4`), if `a` and `b` have no common
  neighbour in `M`, a base exists (`separation`).
* **`triangleBase_of_L1Star`**: for one pair, if `a` or `b` is not adjacent to `w`, a base exists,
  provided the avoidance conjecture `L1Star` holds; hence (`l1starGen_of_blocked`) provided its
  blocked case `L1Blocked` holds.
* `test1At_of_packed`, `test1At_of_farApart`, `test1At_of_L1Star`: the corresponding cases of
  Test1 through the direct lift.
* `UnivTwins`, **`DisjL1`** (Conjecture DL, the disjunctive avoidance conjecture: no multi-pair
  compatibility beyond excluding universal twins), `TriangleData.not_univTwins`,
  **`triangleBase_of_disjL1`**, `triangleBase_of_disjL1_reach`, **`test1At_of_disjL1`**: DL gives a
  triangle base, hence Test1, at every root with data whose `M` is connected.
* **`triangleBase_of_E5_E7`**, `triangleBase_of_lovaszBase_E7` (audit A28): on the base graph of
  t6-dense, (E5) and (E7) are disjuncts of (2.1), so every (E7)-branch base of t6-dense Conjecture 5.1
  is a triangle base at `y₁`.
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {J : SimpleGraph V} [DecidableRel J.Adj]
  {z r w : V} {L : List (V × V)}

/-- `M` has at most one vertex of positive even degree (manuscript Lemma 1.2). -/
theorem TriangleData.triM_evenSet (hD : TriangleData J z r w L)
    (hz : ∀ v, Even (J.degree v) ↔ v = z) : (evenSet (triM J z w L)).card ≤ 1 := by
  have hpar := hD.triM_parity hz
  have hsub : evenSet (triM J z w L) ⊆ {w} := by
    intro v hv
    simp only [evenSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rw [Finset.mem_singleton]
    by_contra hvw
    have h1 := hpar v
    simp only [hvw, ite_false] at h1
    exact (Nat.not_even_iff_odd.mpr (Nat.odd_iff.mpr h1)) hv.2
  exact (Finset.card_le_card hsub).trans (Finset.card_singleton w).le

omit [Fintype V] [DecidableEq V] [DecidableRel J.Adj] in
/-- The two vertices of a pair are non-adjacent in `M`. -/
theorem TriangleData.triM_not_adj [DecidableEq V] (_hD : TriangleData J z r w L) {p : V × V}
    (hp : p ∈ L) :
    ¬ (triM J z w L).Adj p.1 p.2 := fun h =>
  h.2 (List.mem_append_right _ (List.mem_map_of_mem hp))

/-- **Packed pairs** (separation). If the vertices of all pairs are pairwise at distance at least
three in `M`, some Lovász decomposition of `M` has no path through both vertices of a pair, so
every disjunction holds. -/
theorem triangleBase_of_packed (hz : ∀ v, Even (J.degree v) ↔ v = z)
    (hD : TriangleData J z r w L) (hX : Packed (triM J z w L) (pairVerts L).toFinset) :
    TriangleBase J z r := by
  obtain ⟨-, -, -, -, -, -, hnd⟩ := hD.facts
  obtain ⟨D, hD₀, hmeet⟩ := separation_set (triM J z w L) (hD.triM_evenSet hz) hX
  refine ⟨w, L, hD, D, hD₀, fun p hp => Or.inl fun P hP hend h1 => ?_⟩
  have h2 : p.2 ∈ P.walk.support := by
    rcases hend with h | h
    · rw [← h]; exact P.walk.start_mem_support
    · rw [← h]; exact P.walk.end_mem_support
  exact fst_ne_snd hnd hp (hmeet P hP p.1 (List.mem_toFinset.2 (fst_mem_pairVerts hp)) p.2
    (List.mem_toFinset.2 (snd_mem_pairVerts hp)) h1 h2)

/-- **One pair, far apart** (separation; `d(z) = 4`). If `a` and `b` have no common neighbour in
`M`, a triangle base exists. -/
theorem triangleBase_of_farApart {a b : V} (hz : ∀ v, Even (J.degree v) ↔ v = z)
    (hD : TriangleData J z r w [(a, b)])
    (hcn : ∀ x, ¬ ((triM J z w [(a, b)]).Adj a x ∧ (triM J z w [(a, b)]).Adj x b)) :
    TriangleBase J z r := by
  have hp : (a, b) ∈ [(a, b)] := List.mem_singleton_self _
  obtain ⟨-, -, -, -, -, -, hnd⟩ := hD.facts
  have hab : a ≠ b := fst_ne_snd hnd hp
  obtain ⟨D, hD₀, hsep⟩ := separation (triM J z w [(a, b)]) (hD.triM_evenSet hz)
    (c := a) (a := b) ⟨hab, hD.triM_not_adj hp, hcn⟩
  refine ⟨w, [(a, b)], hD, D, hD₀, fun p hp' => ?_⟩
  rw [List.mem_singleton] at hp'
  subst hp'
  dsimp only
  refine Or.inl fun P hP hend h1 => hsep P hP ⟨h1, ?_⟩
  have hs : ∀ x, x = P.src → x ∈ P.walk.support := fun x hx => by
    subst hx; exact P.walk.start_mem_support
  have ht : ∀ x, x = P.tgt → x ∈ P.walk.support := fun x hx => by
    subst hx; exact P.walk.end_mem_support
  rcases hend with h | h
  · exact hs b h.symm
  · exact ht b h.symm

/-- **One pair, through `L₁*`.** If `a` is not adjacent to `w`, the avoidance conjecture `L₁*`
(with `c = b`, `A = {a}`) gives a Lovász decomposition of `M` whose path ending at `b` avoids `a`.
The hypothesis `a ≁ w` is exactly the admissibility of `{a}` (`A ∩ N(g) = ∅` with `g = w`). -/
theorem triangleBase_of_L1Star (hL : L1Star.{u}) {a b : V} (hz : ∀ v, Even (J.degree v) ↔ v = z)
    (hD : TriangleData J z r w [(a, b)]) (haw : ¬ J.Adj w a ∨ ¬ J.Adj w b) :
    TriangleBase J z r := by
  have hp : (a, b) ∈ [(a, b)] := List.mem_singleton_self _
  obtain ⟨-, -, -, -, -, hwL, hnd⟩ := hD.facts
  have hab : a ≠ b := fst_ne_snd hnd hp
  have hpar := hD.triM_parity hz
  have hwa : a ≠ w := fun h => hwL (h ▸ fst_mem_pairVerts hp)
  have hwb : b ≠ w := fun h => hwL (h ▸ snd_mem_pairVerts hp)
  have hoa : (triM J z w [(a, b)]).degree a % 2 = 1 := by
    have := hpar a; simpa [hwa] using this
  have hob : (triM J z w [(a, b)]).degree b % 2 = 1 := by
    have := hpar b; simpa [hwb] using this
  have hev := hD.triM_evenSet hz
  -- the only even vertex of `M` is `w`
  have heven : ∀ g ∈ evenSet (triM J z w [(a, b)]), g = w := by
    intro g hg
    simp only [evenSet, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    by_contra hgw
    have h1 := hpar g
    simp only [hgw, ite_false] at h1
    exact (Nat.not_even_iff_odd.mpr (Nat.odd_iff.mpr h1)) hg.2
  have hnadj := hD.triM_not_adj hp
  rcases haw with ha | hb
  · obtain ⟨D, hD₀, hav⟩ := hL V (triM J z w [(a, b)]) hev b hob {a} (by simp) (by
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      refine ⟨hab, fun h => hnadj h.symm, fun g hg h => ha ?_⟩
      rw [heven g hg] at h
      exact h.1)
    refine ⟨w, [(a, b)], hD, D, hD₀, fun p hp' => ?_⟩
    rw [List.mem_singleton] at hp'
    subst hp'
    dsimp only
    exact Or.inl fun P hP hend => hav P hP hend a (Finset.mem_singleton_self _)
  · obtain ⟨D, hD₀, hav⟩ := hL V (triM J z w [(a, b)]) hev a hoa {b} (by simp) (by
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      refine ⟨hab.symm, hnadj, fun g hg h => hb ?_⟩
      rw [heven g hg] at h
      exact h.1)
    refine ⟨w, [(a, b)], hD, D, hD₀, fun p hp' => ?_⟩
    rw [List.mem_singleton] at hp'
    subst hp'
    dsimp only
    exact Or.inr fun P hP hend => hav P hP hend b (Finset.mem_singleton_self _)

/-- **One pair, through the blocked case of `L₁*`** (`l1starGen_of_blocked`). -/
theorem triangleBase_of_L1Blocked (hB : L1Blocked.{u}) {a b : V}
    (hz : ∀ v, Even (J.degree v) ↔ v = z) (hD : TriangleData J z r w [(a, b)])
    (haw : ¬ J.Adj w a ∨ ¬ J.Adj w b) : TriangleBase J z r :=
  triangleBase_of_L1Star (l1star_of_gen (l1starGen_of_blocked hB)) hz hD haw

/-! ### The corresponding cases of Test1 -/

theorem test1At_of_packed (hz : ∀ v, Even (J.degree v) ↔ v = z) (hr3 : 3 ≤ J.degree r)
    (hD : TriangleData J z r w L) (hX : Packed (triM J z w L) (pairVerts L).toFinset) :
    Test1At J z r :=
  test1At_of_triangleBase J hz hr3 (triangleBase_of_packed hz hD hX)

theorem test1At_of_farApart {a b : V} (hz : ∀ v, Even (J.degree v) ↔ v = z)
    (hr3 : 3 ≤ J.degree r) (hD : TriangleData J z r w [(a, b)])
    (hcn : ∀ x, ¬ ((triM J z w [(a, b)]).Adj a x ∧ (triM J z w [(a, b)]).Adj x b)) :
    Test1At J z r :=
  test1At_of_triangleBase J hz hr3 (triangleBase_of_farApart hz hD hcn)

theorem test1At_of_L1Star (hL : L1Star.{u}) {a b : V} (hz : ∀ v, Even (J.degree v) ↔ v = z)
    (hr3 : 3 ≤ J.degree r) (hD : TriangleData J z r w [(a, b)])
    (haw : ¬ J.Adj w a ∨ ¬ J.Adj w b) : Test1At J z r :=
  test1At_of_triangleBase J hz hr3 (triangleBase_of_L1Star hL hz hD haw)

/-! ### The disjunctive avoidance conjecture DL -/

section DL

omit [Fintype V] [DecidableEq V] [DecidableRel J.Adj] in
/-- `a, b` are **universal twins** of their component: `b` is in the component of `a`, and every
other vertex of that component is adjacent to both. -/
def UnivTwins (G : SimpleGraph V) (a b : V) : Prop :=
  G.Reachable a b ∧ ∀ x, x ≠ a → x ≠ b → G.Reachable a x → G.Adj a x ∧ G.Adj b x

/-- **Conjecture DL (disjunctive avoidance)** (manuscript Conjecture 7.3). If `G` has at most one
vertex of positive even degree and `L` lists disjoint pairs of non-adjacent odd vertices, none of
them universal twins of its component, then some Lovász decomposition of `G` has, for every pair
`(a, b)`, the path ending at `b` avoiding `a` or the path ending at `a` avoiding `b`. -/
def DisjL1 : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    (evenSet G).card ≤ 1 → ∀ L : List (W × W), (pairVerts L).Nodup →
    (∀ p ∈ L, G.degree p.1 % 2 = 1 ∧ G.degree p.2 % 2 = 1 ∧ ¬ G.Adj p.1 p.2 ∧
      ¬ UnivTwins G p.1 p.2) →
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ TriangleDisj D L

omit [Fintype V] [DecidableEq V] [DecidableRel J.Adj] in
/-- In `M`, a pair whose first vertex is connected to `z` is never a pair of universal twins: `z` is
not adjacent to it. -/
theorem TriangleData.not_univTwins (hD : TriangleData J z r w L) {p : V × V} (hp : p ∈ L)
    (hreach : (triM J z w L).Reachable p.1 z) : ¬ UnivTwins (triM J z w L) p.1 p.2 := by
  obtain ⟨-, -, hzL, -, -, -, -⟩ := hD.facts
  intro h
  have h1 : z ≠ p.1 := fun e => hzL (e ▸ fst_mem_pairVerts hp)
  have h2 : z ≠ p.2 := fun e => hzL (e ▸ snd_mem_pairVerts hp)
  have hadj := (h.2 z h1 h2 hreach).1
  have := (hD.triM_adj_z (x := p.1)).1 hadj.symm
  obtain ⟨-, -, -, -, hrL, -, -⟩ := hD.facts
  exact hrL (this ▸ fst_mem_pairVerts hp)

/-- **DL gives triangle bases** wherever no pair is a pair of universal twins of its component of
`M`, in particular (`triangleBase_of_disjL1_reach`) whenever every pair is connected to `z` in
`M`. -/
theorem triangleBase_of_disjL1 (hDL : DisjL1.{u}) (hz : ∀ v, Even (J.degree v) ↔ v = z)
    (hD : TriangleData J z r w L) (htw : ∀ p ∈ L, ¬ UnivTwins (triM J z w L) p.1 p.2) :
    TriangleBase J z r := by
  obtain ⟨-, -, -, -, -, hwL, hnd⟩ := hD.facts
  have hpar := hD.triM_parity hz
  obtain ⟨D, hD₀, hdisj⟩ := hDL V (triM J z w L) (hD.triM_evenSet hz) L hnd (by
    intro p hp
    have hw1 : p.1 ≠ w := fun h => hwL (h ▸ fst_mem_pairVerts hp)
    have hw2 : p.2 ≠ w := fun h => hwL (h ▸ snd_mem_pairVerts hp)
    have h1 := hpar p.1
    have h2 := hpar p.2
    simp only [hw1, hw2, ite_false] at h1 h2
    exact ⟨h1, h2, hD.triM_not_adj hp, htw p hp⟩)
  exact ⟨w, L, hD, D, hD₀, hdisj⟩

theorem triangleBase_of_disjL1_reach (hDL : DisjL1.{u}) (hz : ∀ v, Even (J.degree v) ↔ v = z)
    (hD : TriangleData J z r w L) (hreach : ∀ p ∈ L, (triM J z w L).Reachable p.1 z) :
    TriangleBase J z r :=
  triangleBase_of_disjL1 hDL hz hD fun p hp => hD.not_univTwins hp (hreach p hp)

/-- **DL gives Test1** at every root with triangle data whose auxiliary graph `M` is connected. -/
theorem test1At_of_disjL1 (hDL : DisjL1.{u}) (hz : ∀ v, Even (J.degree v) ↔ v = z)
    (hr3 : 3 ≤ J.degree r) (hD : TriangleData J z r w L) (hM : (triM J z w L).Connected) :
    Test1At J z r :=
  test1At_of_triangleBase J hz hr3
    (triangleBase_of_disjL1_reach hDL hz hD fun _ _ => hM.preconnected _ _)

end DL

/-! ### Comparison with t6-dense (audit A28, F2)

For `r = y₁`, `w = x₃` and `M₀ = {x₁y₂, x₂y₃}`, the graph `M` is the base graph `baseM` of
t6-dense (Definition 2.1 there), and its conditions (E7) and (E5) are one disjunct each of (2.1).
So every base of the (E7) branch of t6-dense Conjecture 5.1 is a triangle base at `y₁`. The proof is
the auditor's (`research/audit/A28-scripts/A28Check.lean`), with renamed helper lemmas. -/

section t6

omit [Fintype V] [DecidableEq V] [DecidableRel J.Adj] in
/-- Equal graphs have the same decompositions, with the same ends and vertex sets. -/
theorem PathDecomp.transport_eq {K K' : SimpleGraph V} (h : K = K') (D : PathDecomp K) :
    ∃ D' : PathDecomp K', D'.paths.map (fun P => (P.src, P.tgt, P.walk.support)) =
      D.paths.map (fun P => (P.src, P.tgt, P.walk.support)) := by
  subst h; exact ⟨D, rfl⟩

omit [Fintype V] [DecidableRel J.Adj] in
theorem ends_eq_of_triples {K K' : SimpleGraph V} {D : PathDecomp K} {D' : PathDecomp K'}
    (h : D'.paths.map (fun P => (P.src, P.tgt, P.walk.support)) =
      D.paths.map (fun P => (P.src, P.tgt, P.walk.support))) (v : V) : D'.ends v = D.ends v := by
  have h2 := congrArg (fun l => (l.map (fun t : V × V × List V =>
    (if t.1 = v then 1 else 0) + (if t.2.1 = v then 1 else 0))).sum) h
  simpa [PathDecomp.ends, GPath.endsAt, List.map_map, Function.comp_def] using h2

omit [Fintype V] [DecidableEq V] [DecidableRel J.Adj] in
theorem avoid_of_triples {K K' : SimpleGraph V} {D : PathDecomp K} {D' : PathDecomp K'}
    (h : D'.paths.map (fun P => (P.src, P.tgt, P.walk.support)) =
      D.paths.map (fun P => (P.src, P.tgt, P.walk.support))) {x y : V}
    (hD : ∀ P ∈ D.paths, (P.src = x ∨ P.tgt = x) → y ∉ P.walk.support) :
    ∀ P ∈ D'.paths, (P.src = x ∨ P.tgt = x) → y ∉ P.walk.support := by
  intro P hP hx
  have hm : (P.src, P.tgt, P.walk.support) ∈
      D.paths.map (fun P => (P.src, P.tgt, P.walk.support)) := by
    rw [← h]; exact List.mem_map_of_mem hP
  obtain ⟨Q, hQ, hQe⟩ := List.mem_map.mp hm
  simp only [Prod.mk.injEq] at hQe
  obtain ⟨h1, h2, h3⟩ := hQe
  rw [← h3]
  exact hD Q hQ (by rw [h1, h2]; exact hx)

omit [DecidableRel J.Adj] in
/-- **(E5) + (E7) on the t6-dense base graph give a triangle base at `y₁`** (A28). -/
theorem triangleBase_of_E5_E7 (J : SimpleGraph V) [DecidableRel J.Adj]
    {z x₁ y₁ x₂ y₂ x₃ y₃ : V}
    (hne : [z, x₁, y₁, x₂, y₂, x₃, y₃].Nodup)
    (hN : ∀ v, J.Adj z v ↔ v = x₁ ∨ v = y₁ ∨ v = x₂ ∨ v = y₂ ∨ v = x₃ ∨ v = y₃)
    (h₁₂ : J.Adj x₁ y₂) (h₂₃ : J.Adj x₂ y₃)
    (D₀ : PathDecomp (baseM J z x₁ x₂ y₂ x₃ y₃))
    (hD₀ : ∀ v, D₀.ends v = (baseM J z x₁ x₂ y₂ x₃ y₃).degree v % 2)
    (E5 : ∀ P ∈ D₀.paths, (P.src = x₂ ∨ P.tgt = x₂) → y₃ ∉ P.walk.support)
    (E7 : ∀ P ∈ D₀.paths, (P.src = x₁ ∨ P.tgt = x₁) → y₂ ∉ P.walk.support) :
    TriangleBase J z y₁ := by
  obtain ⟨hzx₁, hzy₁, hzx₂, hzy₂, hzx₃, hzy₃, hx₁y₁, hx₁x₂, hx₁y₂, hx₁x₃, hx₁y₃, hy₁x₂, hy₁y₂,
    hy₁x₃, hy₁y₃, hx₂y₂, hx₂x₃, hx₂y₃, hy₂x₃, hy₂y₃, hx₃y₃⟩ := nodup7 hne
  -- the two auxiliary graphs are the same graph
  have hEq : baseM J z x₁ x₂ y₂ x₃ y₃ = triM J z x₃ [(x₁, y₂), (x₂, y₃)] := by
    ext a b
    simp only [delList_adj, triDel, zDel, pairEdge, List.flatMap_cons, List.flatMap_nil,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false]
    tauto
  refine ⟨x₃, [(x₁, y₂), (x₂, y₃)], ⟨?_, ?_, ?_⟩, ?_⟩
  · simp only [pairVerts, List.flatMap_cons, List.flatMap_nil, List.cons_append,
      List.nil_append, List.append_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or, List.nodup_nil, and_true]
    exact ⟨⟨hy₁x₃, hx₁y₁.symm, hy₁y₂, hy₁x₂, hy₁y₃⟩,
      ⟨hx₁x₃.symm, hy₂x₃.symm, hx₂x₃.symm, hx₃y₃⟩, ⟨hx₁y₂, hx₁x₂, hx₁y₃⟩, ⟨hx₂y₂.symm, hy₂y₃⟩,
      hx₂y₃, not_false⟩
  · intro v
    rw [hN v]
    simp only [pairVerts, List.flatMap_cons, List.flatMap_nil, List.cons_append,
      List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact h₁₂
    · exact h₂₃
  · obtain ⟨D, hD⟩ := PathDecomp.transport_eq hEq D₀
    refine ⟨D, fun v => ?_, ?_⟩
    · rw [ends_eq_of_triples hD v, hD₀ v]
      congr 1
      exact degree_congr (fun w => by rw [hEq])
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact Or.inr (avoid_of_triples hD E7)
      · exact Or.inr (avoid_of_triples hD E5)

omit [DecidableRel J.Adj] in
/-- The same, stated from `LovaszBase` whose last clause is the (E7) branch. -/
theorem triangleBase_of_lovaszBase_E7 (J : SimpleGraph V) [DecidableRel J.Adj]
    {z x₁ y₁ x₂ y₂ x₃ y₃ : V}
    (h : [z, x₁, y₁, x₂, y₂, x₃, y₃].Nodup ∧
      (∀ v, J.Adj z v ↔ v = x₁ ∨ v = y₁ ∨ v = x₂ ∨ v = y₂ ∨ v = x₃ ∨ v = y₃) ∧
      J.Adj x₁ y₂ ∧ J.Adj x₂ y₃ ∧
      ∃ D₀ : PathDecomp (baseM J z x₁ x₂ y₂ x₃ y₃),
        (∀ v, D₀.ends v = (baseM J z x₁ x₂ y₂ x₃ y₃).degree v % 2) ∧
        (∀ P ∈ D₀.paths, (P.src = x₂ ∨ P.tgt = x₂) → y₃ ∉ P.walk.support) ∧
        (∀ P ∈ D₀.paths, (P.src = x₁ ∨ P.tgt = x₁) → y₂ ∉ P.walk.support)) :
    TriangleBase J z y₁ := by
  obtain ⟨hne, hN, h₁₂, h₂₃, D₀, hD₀, E5, E7⟩ := h
  exact triangleBase_of_E5_E7 J hne hN h₁₂ h₂₃ D₀ hD₀ E5 E7

end t6

end Gallai
