import GallaiLean.Project

/-!
# A lower bound for path numbers from a low-degree vertex

`pathNumber_gt_of_low_degree`: if `G` has `n ≥ 2` vertices and at least `k (n - 1)` edges and some
vertex `w` has degree `< k`, then `p(G) ≥ k + 1`. (Here `k ≥ 1` is automatic.)

Each path has at most `n - 1` edges, so `k` paths covering at least `k (n - 1)` edges are all
Hamiltonian. Hence they all contain `w`, and distinct paths use distinct edges at `w`.
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem eq_of_sum_eq_length_mul {l : List ℕ} {c : ℕ} (hle : ∀ x ∈ l, x ≤ c)
    (hsum : l.sum = l.length * c) : ∀ x ∈ l, x = c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hle a List.mem_cons_self
    have hl : ∀ x ∈ l, x ≤ c := fun x hx => hle x (List.mem_cons_of_mem _ hx)
    have hsl : l.sum ≤ l.length * c := by
      have := List.sum_le_length_nsmul l c hl
      simpa using this
    simp only [List.sum_cons, List.length_cons] at hsum
    have h1 : a = c := by nlinarith
    have h2 : l.sum = l.length * c := by nlinarith
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h1
    · exact ih hl h2 x hx

/-- A path through `w` has at least one edge at `w`. -/
theorem GPath.one_le_incid [DecidableEq V] (P : GPath G) {w : V} (hw : w ∈ P.walk.support) :
    1 ≤ P.incid w := by
  have h1 := P.incid_add_endsAt w
  have h2 := P.endsAt_eq_ite w
  simp only [hw, ite_true] at h1
  split_ifs at h2 <;> omega

/-- The number of edges is the total length of the paths of any decomposition. -/
theorem PathDecomp.sum_length_eq_card [Fintype G.edgeSet] [DecidableEq V] (D : PathDecomp G) :
    (D.paths.map (fun P => P.edges.length)).sum = G.edgeFinset.card := by
  rw [← List.length_flatMap, ← List.toFinset_card_of_nodup D.nodup_edges]
  congr 1
  ext e
  rw [List.mem_toFinset, mem_edgeFinset, D.covers]

/-- **Low-degree lower bound.** If `n ≥ 2`, `|E(G)| ≥ k (n - 1)` and some vertex has degree `< k`
(so `k ≥ 1`), then `p(G) ≥ k + 1`. -/
theorem pathNumber_gt_of_low_degree [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {k : ℕ}
    (hn : 2 ≤ Fintype.card V) (hE : k * (Fintype.card V - 1) ≤ G.edgeFinset.card)
    {w : V} (hw : G.degree w < k) : k + 1 ≤ pathNumber G := by
  apply le_pathNumber
  intro D
  by_contra hlt
  push Not at hlt
  set n := Fintype.card V with hn_def
  have hsize : D.size ≤ k := by omega
  have htot := D.sum_length_eq_card
  have hlen : ∀ x ∈ D.paths.map (fun P => P.edges.length), x ≤ n - 1 := by
    intro x hx
    obtain ⟨P, -, rfl⟩ := List.mem_map.mp hx
    have := P.isPath.length_lt
    rw [P.length_edges]
    omega
  have hsum_le : (D.paths.map (fun P => P.edges.length)).sum ≤ D.size * (n - 1) := by
    have := List.sum_le_length_nsmul _ _ hlen
    simpa [PathDecomp.size] using this
  have hn1 : 1 ≤ n - 1 := by omega
  have hsz : D.size = k := by
    by_contra hne
    have : D.size * (n - 1) < k * (n - 1) := Nat.mul_lt_mul_of_pos_right (by omega) hn1
    omega
  have hsum_eq : (D.paths.map (fun P => P.edges.length)).sum =
      (D.paths.map (fun P => P.edges.length)).length * (n - 1) := by
    rw [List.length_map]
    have : D.paths.length = k := hsz
    rw [this]
    rw [hsz] at hsum_le
    omega
  have heach := eq_of_sum_eq_length_mul hlen hsum_eq
  have hwmem : ∀ P ∈ D.paths, w ∈ P.walk.support := by
    intro P hP
    by_contra hnot
    have hPl : P.edges.length = n - 1 := heach _ (List.mem_map_of_mem hP)
    have hsupp : P.walk.support.length = n := by
      rw [Walk.length_support, ← P.length_edges, hPl]
      omega
    have hsub : P.walk.support.toFinset ⊆ Finset.univ.erase w := by
      intro x hx
      rw [List.mem_toFinset] at hx
      exact Finset.mem_erase.mpr ⟨fun h => hnot (h ▸ hx), Finset.mem_univ _⟩
    have hcard := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup P.isPath.support_nodup, hsupp,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at hcard
    omega
  have hdeg := D.degree_eq_sum w
  have : D.size ≤ (D.paths.map (fun P => P.incid w)).sum := by
    have := List.length_le_sum_of_one_le (D.paths.map (fun P => P.incid w))
      (fun x hx => by
        obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hx
        exact P.one_le_incid (hwmem P hP))
    simpa [PathDecomp.size] using this
  omega

end Gallai
