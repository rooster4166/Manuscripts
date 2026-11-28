import GallaiLean.Conj31
import GallaiLean.CycleInsert

/-!
# Upward closure of realisable profiles, and PC with at most one zero

Manuscript `manuscripts/conj31`, Lemma 2.4 and Theorem 2.5.

* `PathDecomp.exists_interior`: a vertex with fewer ends than edges is an interior vertex of some
  path of the decomposition.
* `PathDecomp.split_at_interior`: splitting that path at the vertex adds two ends there.
* **`realisesProfile_up`** (upward closure): if `b` is realisable and `b(x) < d(x)`, then
  `b + 2·1_x` is realisable.
* `realisesProfile_of_le`: from a realisable `m ≤ b` with `m ≡ b (mod 2)` and `b ≤ d`, the profile
  `b` is realisable.
* **`realisesProfile_of_no_zero`**, **`realisesProfile_of_one_zero`** (PC with at most one zero):
  every profile `b ≡ d (mod 2)`, `b ≤ d`, with `b ≥ 1` at every vertex (resp. every vertex but one
  even vertex `z`) is realisable. The graph need not be 2-connected. The proofs use Lovász's
  theorem through `realisable_evenSet'` and `realisable_evenSet_erase'`; the latter, and hence the
  one-zero statement here, assumes even order (the manuscript proof does not need it).
-/

open SimpleGraph Finset

namespace Gallai

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A vertex with fewer ends than edges is an interior vertex of some path. -/
theorem PathDecomp.exists_interior {G : SimpleGraph V} [DecidableRel G.Adj] (D : PathDecomp G)
    {x : V} (h : D.ends x < G.degree x) :
    ∃ P ∈ D.paths, x ∈ P.walk.support ∧ P.src ≠ x ∧ P.tgt ≠ x := by
  by_contra hno
  have hle : ∀ P ∈ D.paths, P.incid x ≤ P.endsAt x := by
    intro P hP
    have h1 := P.incid_add_endsAt x
    by_cases hx : x ∈ P.walk.support
    · rw [if_pos hx] at h1
      have hend : 1 ≤ P.endsAt x := by
        unfold GPath.endsAt
        by_cases hs : P.src = x
        · rw [if_pos hs]
          omega
        · have ht : P.tgt = x := by
            by_contra ht
            exact hno ⟨P, hP, hx, hs, ht⟩
          rw [if_pos ht]
          omega
      omega
    · rw [if_neg hx] at h1
      omega
  have hsum := sum_map_le_sum_map D.paths (fun P => P.incid x) (fun P => P.endsAt x) hle
  rw [← D.degree_eq_sum x] at hsum
  unfold PathDecomp.ends at h
  omega

/-- **Split a path at an interior vertex**: two more ends at `x`, the same ends elsewhere. -/
theorem PathDecomp.split_at_interior {G : SimpleGraph V} [DecidableRel G.Adj] (D : PathDecomp G) {x : V}
    (h : D.ends x < G.degree x) :
    ∃ D' : PathDecomp G, ∀ w, D'.ends w = D.ends w + (if x = w then 2 else 0) := by
  obtain ⟨P, hP, hx, hs, ht⟩ := D.exists_interior h
  have hpos1 : 0 < (P.walk.takeUntil x hx).length := by
    by_contra h0
    have h0' : (P.walk.takeUntil x hx).length = 0 := by omega
    exact hs (Walk.eq_of_length_eq_zero h0')
  have hpos2 : 0 < (P.walk.dropUntil x hx).length := by
    by_contra h0
    have h0' : (P.walk.dropUntil x hx).length = 0 := by omega
    exact ht (Walk.eq_of_length_eq_zero h0').symm
  let P₁ : GPath G := ⟨P.src, x, P.walk.takeUntil x hx, P.isPath.takeUntil hx, hpos1⟩
  let P₂ : GPath G := ⟨x, P.tgt, P.walk.dropUntil x hx, P.isPath.dropUntil hx, hpos2⟩
  have hedges : [P₁, P₂].flatMap GPath.edges = P.edges := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, P₁, P₂, GPath.edges]
    rw [← Walk.edges_append, Walk.take_spec]
  obtain ⟨D', -, hD'⟩ := PathDecomp.replaceList D hP [P₁, P₂] [] (fun e he => he)
    (by rw [hedges, List.append_nil]) List.nodup_nil (by simp) (by simp)
  refine ⟨D', fun w => ?_⟩
  have h1 := hD' w
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h1
  have e1 : P₁.endsAt w = (if P.src = w then 1 else 0) + (if x = w then 1 else 0) := rfl
  have e2 : P₂.endsAt w = (if x = w then 1 else 0) + (if P.tgt = w then 1 else 0) := rfl
  have e0 : P.endsAt w = (if P.src = w then 1 else 0) + (if P.tgt = w then 1 else 0) := rfl
  rw [e1, e2, e0] at h1
  split_ifs at h1 ⊢ <;> omega

/-- **Upward closure** (manuscript Lemma 2.4). -/
theorem realisesProfile_up {G : SimpleGraph V} [DecidableRel G.Adj] {b : V → ℕ}
    (h : RealisesProfile G b) {x : V} (hx : b x < G.degree x) :
    RealisesProfile G (fun w => b w + if x = w then 2 else 0) := by
  obtain ⟨D, hD⟩ := h
  obtain ⟨D', hD'⟩ := D.split_at_interior (by rw [hD x]; exact hx)
  exact ⟨D', fun w => by rw [hD' w, hD w]⟩

/-- From a realisable profile below `b`, of the same parity, `b` is realisable (when `b ≤ d`). -/
theorem realisesProfile_of_le {G : SimpleGraph V} [DecidableRel G.Adj] {b : V → ℕ}
    (hbd : ∀ v, b v ≤ G.degree v) :
    ∀ (k : ℕ) (m : V → ℕ), ∑ v, (b v - m v) = k → RealisesProfile G m → (∀ v, m v ≤ b v) →
      (∀ v, m v % 2 = b v % 2) → RealisesProfile G b := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro m hk hm hle hpar
  by_cases hall : ∀ v, m v = b v
  · have hmb : m = b := funext hall
    rw [← hmb]
    exact hm
  · obtain ⟨x, hx⟩ := not_forall.mp hall
    have hlt : m x < b x := lt_of_le_of_ne (hle x) hx
    have h2 : m x + 2 ≤ b x := by
      have := hpar x
      omega
    have hup := realisesProfile_up hm (show m x < G.degree x by have := hbd x; omega)
    have hk' : ∑ v, (b v - (m v + if x = v then 2 else 0)) + 2 = k := by
      rw [← hk, ← Finset.add_sum_erase _ _ (Finset.mem_univ x),
        ← Finset.add_sum_erase _ (fun v => b v - m v) (Finset.mem_univ x)]
      have hrest : ∑ v ∈ univ.erase x, (b v - (m v + if x = v then 2 else 0)) =
          ∑ v ∈ univ.erase x, (b v - m v) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [if_neg (Finset.ne_of_mem_erase hv).symm, add_zero]
      rw [hrest, if_pos rfl]
      omega
    refine ih _ (by omega) _ rfl hup ?_ ?_
    · intro v
      by_cases hxv : x = v
      · rw [if_pos hxv, ← hxv]
        exact h2
      · rw [if_neg hxv, add_zero]
        exact hle v
    · intro v
      by_cases hxv : x = v
      · rw [if_pos hxv, ← hxv]
        have := hpar x
        omega
      · rw [if_neg hxv, add_zero]
        exact hpar v

/-- **PC with no zero** (manuscript Theorem 2.5, zero-free case). Any graph without isolated
vertices; no connectivity is needed. -/
theorem realisesProfile_of_no_zero {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : ∀ v, 0 < G.degree v) {b : V → ℕ} (hpar : ∀ v, b v % 2 = G.degree v % 2)
    (hbd : ∀ v, b v ≤ G.degree v) (hpos : ∀ v, 1 ≤ b v) : RealisesProfile G b := by
  obtain ⟨-, D, hD⟩ := realisable_evenSet' hG
  refine realisesProfile_of_le hbd _ _ rfl ⟨D, hD⟩ ?_ ?_
  · intro v
    have := hpar v
    have := hpos v
    unfold profile
    split_ifs with h1 h2
    · omega
    · have := Nat.even_iff.mp (Nat.not_odd_iff_even.mp h1)
      omega
    · omega
  · intro v
    have := hpar v
    unfold profile
    split_ifs with h1 h2
    · have := Nat.odd_iff.mp h1
      omega
    · have := Nat.even_iff.mp (Nat.not_odd_iff_even.mp h1)
      omega
    · have := Nat.even_iff.mp (Nat.not_odd_iff_even.mp h1)
      omega

/-- **PC with one zero** (manuscript Theorem 2.5; here at even order, as in
`realisable_evenSet_erase'`). Any graph without isolated vertices. -/
theorem realisesProfile_of_one_zero {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : ∀ v, 0 < G.degree v) (hn : Even (Fintype.card V)) {z : V} (hz : z ∈ evenSet G)
    {b : V → ℕ} (hpar : ∀ v, b v % 2 = G.degree v % 2) (hbd : ∀ v, b v ≤ G.degree v)
    (hpos : ∀ v, v ≠ z → 1 ≤ b v) : RealisesProfile G b := by
  obtain ⟨-, D, hD⟩ := realisable_evenSet_erase' hG hn hz
  refine realisesProfile_of_le hbd _ _ rfl ⟨D, hD⟩ ?_ ?_
  · intro v
    have := hpar v
    unfold profile
    split_ifs with h1 h2
    · have := hpos v (fun h => by rw [h] at h1; exact not_odd_of_mem_evenSet hz h1)
      omega
    · have := hpos v (Finset.ne_of_mem_erase h2)
      have := Nat.even_iff.mp (Nat.not_odd_iff_even.mp h1)
      omega
    · omega
  · intro v
    have := hpar v
    unfold profile
    split_ifs with h1 h2
    · have := Nat.odd_iff.mp h1
      omega
    · have := Nat.even_iff.mp (Nat.not_odd_iff_even.mp h1)
      omega
    · have := Nat.even_iff.mp (Nat.not_odd_iff_even.mp h1)
      omega

end Gallai
