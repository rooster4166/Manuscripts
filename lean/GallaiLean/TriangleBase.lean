import GallaiLean.DirectTest1

/-!
# Triangle bases from the single-vertex tools (session `claude/triangle-base`)

Manuscript: `manuscripts/direct-test1/direct-test1.tex`, §6.

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

end Gallai
