import GallaiLean.MarkedSurgery
import Mathlib.Combinatorics.Hall.Basic

/-!
# Assigning marks to path ends (Hall's theorem)

Marked-reduction manuscript, §2.1: the private-leaf identity and the odd-mark rank inequality.
Both are consequences of one assignment lemma, proved here with Hall's marriage theorem.

**`markedNumber_add_card_le`.** Let `D` be a path decomposition of `F` and `T` a set of marks. Let
`O` be a set of exceptional marks. Suppose every mark has at least one end of `D` and every
mark outside `O` has at least two. Then `q(F, T) + |T| ≤ |D| + ⌊|O|/2⌋`.

Proof. Give each mark the paths ending at it, plus `⌊|O|/2⌋` dummy slots. A set `s` of marks
carries at least `2|s| − |s ∩ O|` path ends. Each path carries at most two of them, so `s` sees at
least `|s| − ⌊|O|/2⌋` paths, and Hall's condition holds. An injective choice of slots then assigns
all but at most `⌊|O|/2⌋` marks to distinct paths ending there.

In applications the exceptional marks are the odd-degree ones (parity gives them one end), and the
others are even-degree marks with at least one end (parity gives them two).
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u} [DecidableEq V] {F : SimpleGraph V}

/-- A sum over a finset of the indicator of one vertex is at most one. -/
theorem sum_ite_eq_le_one {s : Finset V} (x : V) :
    (∑ w ∈ s, if x = w then 1 else 0) ≤ 1 := by
  rw [Finset.sum_ite_eq]; split_ifs <;> omega

/-- A path has at most two ends in any set of vertices. -/
theorem GPath.sum_endsAt_le_two (P : GPath F) (s : Finset V) :
    (∑ w ∈ s, P.endsAt w) ≤ 2 := by
  unfold GPath.endsAt
  rw [Finset.sum_add_distrib]
  have h1 := sum_ite_eq_le_one (s := s) P.src
  have h2 := sum_ite_eq_le_one (s := s) P.tgt
  omega

theorem PathDecomp.ends_eq_sum_fin (D : PathDecomp F) (v : V) :
    D.ends v = ∑ i : Fin D.paths.length, (D.paths.get i).endsAt v := by
  unfold PathDecomp.ends
  conv_lhs => rw [← List.ofFn_get D.paths]
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

theorem countP_finRange_eq_card {n : ℕ} (p : Fin n → Bool) :
    (List.finRange n).countP p = (Finset.univ.filter (fun i => p i = true)).card := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup
    ((List.nodup_finRange n).filter _), List.toFinset_filter, List.toFinset_finRange]

/-- **The assignment lemma.** If every mark has an end of `D`, and every mark outside `O`
has two, then all but `⌊|O|/2⌋` marks can be assigned distinct paths of `D`:
`q(F, T) + |T| ≤ |D| + ⌊|O|/2⌋`. -/
theorem markedNumber_add_card_le (D : PathDecomp F) (T O : Finset V)
    (h1 : ∀ v ∈ T, 1 ≤ D.ends v) (h2 : ∀ v ∈ T, v ∉ O → 2 ≤ D.ends v) :
    markedNumber F T + T.card ≤ D.size + O.card / 2 := by
  classical
  set n := D.paths.length with hn
  set k := O.card / 2 with hk
  set P : Fin n → GPath F := D.paths.get with hP
  let t : T → Finset (Fin n ⊕ Fin k) := fun v =>
    (Finset.univ.filter (fun i => 0 < (P i).endsAt v.1)).disjSum Finset.univ
  -- Hall's condition
  have hall : ∀ s : Finset T, s.card ≤ (s.biUnion t).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
    · simp
    set N := Finset.univ.filter (fun i : Fin n => ∃ v ∈ s, 0 < (P i).endsAt v.1) with hN
    have hsub : N.disjSum (Finset.univ : Finset (Fin k)) ⊆ s.biUnion t := by
      intro x hx
      rw [Finset.mem_biUnion]
      rcases x with i | j
      · rw [Finset.inl_mem_disjSum, hN, Finset.mem_filter] at hx
        obtain ⟨v, hv, hpos⟩ := hx.2
        exact ⟨v, hv, by simp [t, hpos]⟩
      · exact ⟨v₀, hv₀, by simp [t]⟩
    have hcardN := Finset.card_le_card hsub
    rw [Finset.card_disjSum, Finset.card_univ, Fintype.card_fin] at hcardN
    -- count ends
    have hupper : (∑ v ∈ s, D.ends v.1) ≤ 2 * N.card := by
      simp only [PathDecomp.ends_eq_sum_fin]
      rw [Finset.sum_comm]
      calc (∑ i : Fin n, ∑ v ∈ s, (P i).endsAt v.1)
          ≤ ∑ i : Fin n, if i ∈ N then 2 else 0 := by
            apply Finset.sum_le_sum
            intro i _
            split_ifs with hi
            · have := (P i).sum_endsAt_le_two (s.map (Function.Embedding.subtype _))
              rwa [Finset.sum_map] at this
            · apply le_of_eq
              apply Finset.sum_eq_zero
              intro v hv
              by_contra hne
              exact hi (by rw [hN, Finset.mem_filter]; exact ⟨Finset.mem_univ _, v, hv,
                Nat.pos_of_ne_zero hne⟩)
        _ = 2 * N.card := by
            rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_comm]
    have hlower : 2 * s.card ≤ (∑ v ∈ s, D.ends v.1) + (s.filter (fun v => v.1 ∈ O)).card := by
      have : ∀ v ∈ s, 2 ≤ D.ends v.1 + (if v.1 ∈ O then 1 else 0) := by
        intro v _
        by_cases hvO : v.1 ∈ O
        · have := h1 v.1 v.2; simp [hvO]; omega
        · have := h2 v.1 v.2 hvO; simp [hvO]; omega
      have h := Finset.sum_le_sum this
      rw [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib, Finset.sum_boole] at h
      simpa [mul_comm] using h
    have hO : (s.filter (fun v => v.1 ∈ O)).card ≤ O.card := by
      exact Finset.card_le_card_of_injOn (s := s.filter (fun v => v.1 ∈ O)) (t := O)
        (fun v : T => v.1) (fun v hv => (Finset.mem_filter.mp hv).2)
        (fun a _ b _ h => Subtype.ext h)
    omega
  obtain ⟨f, hfinj, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
  -- the assignment
  let g : Fin n → Option V := fun i =>
    if h : ∃ v : T, f v = Sum.inl i then some (Classical.choose h).1 else none
  have hg : ∀ i w, g i = some w → ∃ v : T, f v = Sum.inl i ∧ v.1 = w := by
    intro i w h
    simp only [g] at h
    split_ifs at h with hex
    · exact ⟨_, Classical.choose_spec hex, Option.some.inj h⟩
  have hgsome : ∀ v : T, ∀ i, f v = Sum.inl i → g i = some v.1 := by
    intro v i hvi
    have hex : ∃ v : T, f v = Sum.inl i := ⟨v, hvi⟩
    simp only [g, hex, dite_true]
    congr 2
    exact hfinj ((Classical.choose_spec hex).trans hvi.symm)
  have hginj : ∀ i j w, w ∈ g i → w ∈ g j → i = j := by
    intro i j w hi hj
    obtain ⟨v, hv, rfl⟩ := hg i w hi
    obtain ⟨v', hv', hvv'⟩ := hg j v.1 hj
    have : v' = v := Subtype.ext hvv'
    subst this
    exact Sum.inl_injective (hv.symm.trans hv')
  let h : Fin n → GPath F × Option V := fun i => (P i, g i)
  have hfst : (List.ofFn h).map Prod.fst = D.paths := by
    rw [List.map_ofFn]; exact List.ofFn_get D.paths
  let M : MarkedPartition F T :=
    { paths := List.ofFn h
      nodup_edges := by rw [hfst]; exact D.nodup_edges
      covers := by rw [hfst]; exact D.covers
      site_ok := by
        intro x hx s hs
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
        obtain ⟨v, hv, rfl⟩ := hg i s hs
        have hmem := hft v
        rw [hv] at hmem
        simp only [t, Finset.inl_mem_disjSum, Finset.mem_filter, Finset.mem_univ,
          true_and] at hmem
        refine ⟨v.2, ?_⟩
        change (P i).src = v.1 ∨ (P i).tgt = v.1
        unfold GPath.endsAt at hmem
        by_contra hc
        rw [not_or] at hc
        simp [hc.1, hc.2] at hmem
      sites_nodup := by
        rw [List.ofFn_eq_map, List.filterMap_map]
        exact (List.nodup_finRange n).filterMap hginj }
  have hcost : markedCost M = (Finset.univ.filter (fun i => (g i).isNone = true)).card := by
    show (List.ofFn h).countP _ = _
    rw [List.ofFn_eq_map, List.countP_map]
    exact countP_finRange_eq_card _
  -- counting
  set L := Finset.univ.filter (fun v : T => (f v).isLeft = true) with hL
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset T))
    (fun v : T => (f v).isLeft = true)
  rw [Finset.card_univ, Fintype.card_coe, ← hL] at hsplit
  have hR : (Finset.univ.filter (fun v : T => ¬ (f v).isLeft = true)).card ≤ k := by
    have := Finset.card_le_card_of_injOn
      (s := Finset.univ.filter (fun v : T => ¬ (f v).isLeft = true))
      (t := (Finset.univ : Finset (Fin k)).map ⟨Sum.inr, Sum.inr_injective⟩) f (by
        intro v hv
        rw [Finset.coe_filter] at hv
        simp only [Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hv
        rcases hfv : f v with i | j
        · rw [hfv] at hv; simp at hv
        · simp) hfinj.injOn
    simpa using this
  have hLsome : L.card ≤ (Finset.univ.filter (fun i => (g i).isSome = true)).card := by
    have := Finset.card_le_card_of_injOn (s := L)
      (t := (Finset.univ.filter (fun i => (g i).isSome = true)).map ⟨Sum.inl, Sum.inl_injective⟩)
      f (by
        intro v hv
        rw [hL, Finset.coe_filter] at hv
        simp only [Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hv
        rcases hfv : f v with i | j
        · simp [hgsome v i hfv]
        · rw [hfv] at hv; simp at hv) hfinj.injOn
    simpa using this
  have hsplit2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => (g i).isSome = true)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit2
  have hnone : Finset.univ.filter (fun i => ¬ (g i).isSome = true) =
      Finset.univ.filter (fun i => (g i).isNone = true) := by
    ext i; simp [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none]
  rw [hnone] at hsplit2
  have := markedNumber_le M
  unfold PathDecomp.size
  omega

end Gallai
