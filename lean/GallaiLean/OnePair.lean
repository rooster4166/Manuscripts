import GallaiLean.RouteDescent
import GallaiLean.Separation

/-!
# One step of route descent, end to end

Route-descent manuscript, Corollary "onepair". Let `G` have exactly two vertices of positive even
degree, `c` and `a`, and let them be adjacent. Then `{a}` is realisable, by a path partition in which
the edge `ca` is the terminal edge, at `a`, of some path.

This is route descent with one route `R = ca`.
* The base is `lovasz_avoid_nonadj` (Theorem "L₁") on `G − ca`, where all degrees are odd. It gives a
  Lovász decomposition whose path at `c` avoids `a`.
* The step is `PathDecomp.route_append` (Lemma "extension", (i) ⇒ (ii)). Appending `ca` to that path
  moves the end from `c` to `a`.
-/

open SimpleGraph

namespace Gallai

universe u

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- **Corollary "onepair"** (route-descent manuscript). If the only vertices of positive even degree
are `c` and `a`, and `c ~ a`, then `{a}` is realisable, with `ca` the terminal edge at `a` of some path. -/
theorem realisable_two_even_adj (G : SimpleGraph W) [DecidableRel G.Adj] {a c : W}
    (hev : evenSet G = {a, c}) (hca : G.Adj c a) :
    ∃ D : PathDecomp G, Realises G D {a} ∧
      ∃ P ∈ D.paths, ∃ hPt : P.tgt = a, ∃ p : G.Walk P.src c,
        P.walk.copy rfl hPt = p.append (Walk.cons hca Walk.nil) := by
  classical
  have hne : c ≠ a := hca.ne
  have hdeg := delEdge_degree G hca
  have hcE : c ∈ evenSet G := by rw [hev]; simp
  have haE : a ∈ evenSet G := by rw [hev]; simp
  have hcd := mem_evenSet_iff.mp hcE
  have had := mem_evenSet_iff.mp haE
  have hdc := hdeg c
  have hda := hdeg a
  simp only [hne, hne.symm, ite_true, ite_false, add_zero] at hdc hda
  -- in `G − ca` every vertex of positive degree is odd
  have hev' : (evenSet (delEdge G c a)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [mem_evenSet_iff] at hw
    by_cases hwc : w = c
    · subst hwc; omega
    by_cases hwa : w = a
    · subst hwa; omega
    have h := hdeg w
    simp only [hwc, hwa, ite_false, add_zero] at h
    have hwE : w ∉ evenSet G := by rw [hev]; simp [hwc, hwa]
    rw [mem_evenSet_iff] at hwE
    exact hwE ⟨h ▸ hw.1, h ▸ hw.2⟩
  have hc' : (delEdge G c a).degree c % 2 = 1 := by omega
  have hnadj : ¬ (delEdge G c a).Adj c a := fun h => h.2 rfl
  obtain ⟨D', hD', hav⟩ := lovasz_avoid_nonadj (delEdge G c a) hev' hc' hne hnadj
  -- the path of `D'` ending at `c`
  have hDc : D'.ends c = 1 := by rw [hD', hc']
  obtain ⟨Q, hQ, hQc⟩ : ∃ Q ∈ D'.paths, Q.src = c ∨ Q.tgt = c := by
    by_contra hno
    push_neg at hno
    have h0 : D'.ends c = 0 := by
      unfold PathDecomp.ends
      rw [List.sum_eq_zero]
      intro x hx
      obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hx
      obtain ⟨h1, h2⟩ := hno P hP
      simp [GPath.endsAt, h1, h2]
    omega
  have haQ := hav Q hQ hQc
  -- the route `ca`
  let R : GPath G := ⟨c, a, Walk.cons hca Walk.nil,
    (Walk.cons_isPath_iff _ _).mpr ⟨Walk.IsPath.nil, by simp [hne]⟩, by simp⟩
  have hK : ∀ e, e ∈ (delEdge G c a).edgeSet ↔ e ∈ G.edgeSet ∧ e ∉ R.edges := by
    intro e
    rw [delEdge_edgeSet]
    simp [R, GPath.edges]
  have hdisj : ∀ x ∈ Q.walk.support, x ∈ R.walk.support → x = c := by
    intro x hx hxR
    simp only [R, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hxR
    rcases hxR with rfl | rfl
    · rfl
    · exact absurd hx haQ
  obtain ⟨D, -, hends, P, hP, hPt, p, hPw⟩ := D'.route_append (R := R) rfl rfl hK hQ hQc hdisj
  refine ⟨D, fun v => ?_, P, hP, hPt, p, hPw⟩
  have h : D.ends v + (if c = v then 1 else 0) = D'.ends v + (if a = v then 1 else 0) := hends v
  rw [hD'] at h
  unfold profile
  by_cases hvc : v = c
  · rw [hvc] at h ⊢
    have hnodd : ¬ Odd (G.degree c) := Nat.not_odd_iff_even.mpr (Nat.even_iff.mpr hcd.2)
    have hcS : c ∉ ({a} : Finset W) := by simp [hne]
    rw [if_neg hnodd, if_neg hcS]
    rw [if_pos rfl, if_neg (Ne.symm hne)] at h
    omega
  by_cases hva : v = a
  · rw [hva] at h ⊢
    have hnodd : ¬ Odd (G.degree a) := Nat.not_odd_iff_even.mpr (Nat.even_iff.mpr had.2)
    rw [if_neg hnodd, if_pos (Finset.mem_singleton_self a)]
    rw [if_neg hne, if_pos rfl] at h
    omega
  · have hcv : ¬ c = v := fun h' => hvc h'.symm
    have hav : ¬ a = v := fun h' => hva h'.symm
    rw [if_neg hcv, if_neg hav] at h
    have hd := hdeg v
    simp only [hvc, hva, ite_false, add_zero] at hd
    have hvS : v ∉ ({a} : Finset W) := by simp [hva]
    have hvE : v ∉ evenSet G := by rw [hev]; simp [hvc, hva]
    rw [mem_evenSet_iff] at hvE
    by_cases hodd : Odd (G.degree v)
    · rw [if_pos hodd]; rw [Nat.odd_iff] at hodd; omega
    · rw [if_neg hodd, if_neg hvS]; rw [Nat.odd_iff] at hodd; omega

end Gallai
