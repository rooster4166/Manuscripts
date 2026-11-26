import GallaiLean.Bridge

/-!
# The branching base case as a single named hypothesis

`BranchBase k`: in every connected graph of even order with at least `2k` even vertices, every
even vertex `y` that has at least two even neighbours, and no bridge to a vertex of degree at least
two, lies in a realisable set `Ev ∖ R` with `|R| = k` and `y ∉ R`.

* **`rootedTest_of_branchBase`**: `(∀ k, BranchBase k) → RootedTest`, and
  **`gallai_of_branchBase`**: `(∀ k, BranchBase k) → GallaiConjecture` (via
  `gallai_iff_rootedTest`). `branchBase_one`, `branchBase_two` hold (Lemma 3, two-step descent),
  so only `k ≥ 3` is open (`gallai_of_branchBase_three`).
* `branchBase_of_bstmt`: `BStmt k → BranchBase k`, so `BranchBase` is weaker than `BStmt`: no
  prescribed removed vertex, and vertices with a non-pendant bridge are excluded.
* `dstmt0E_succ`: `D⁰_1, …, D⁰_k` and `BranchBase (k+1)` give `D⁰_{k+1}` (descent keeping `y`, no
  prescribed vertex). Four cases: a non-pendant bridge at `y` (`bridge_odd0`, `bridge_even0`);
  two even neighbours (`BranchBase`); exactly one even neighbour through a non-bridge
  (`desc_succ_of_transfer0`); otherwise a non-bridge edge to an odd neighbour
  (`desc_lift_of_no_even_nbr`).
-/

open SimpleGraph

namespace Gallai

universe u

/-- `D⁰_j`: `j`-step descent keeping `y`, in connected even-order graphs with `≥ 2j` even
vertices. -/
def DStmt0 (j : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
    H.Connected → Even (Fintype.card W) → 2 * j ≤ (evenSet H).card →
    ∀ y, y ∈ evenSet H → Desc H j y ∅

/-- `D⁰_j` for graphs with at most `N` edges. -/
def DStmt0E (j N : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
    H.edgeFinset.card ≤ N → H.Connected → Even (Fintype.card W) →
    2 * j ≤ (evenSet H).card → ∀ y, y ∈ evenSet H → Desc H j y ∅

/-- **The branching base case.** `k`-step descent keeping `y`, for even vertices `y` with at least
two even neighbours and no bridge to a vertex of degree at least two. -/
def BranchBase (k : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
    H.Connected → Even (Fintype.card W) → 2 * k ≤ (evenSet H).card →
    ∀ y, y ∈ evenSet H →
    (∃ v₁ ∈ evenSet H, ∃ v₂ ∈ evenSet H, v₁ ≠ v₂ ∧ H.Adj y v₁ ∧ H.Adj y v₂) →
    (∀ t, H.Adj y t → H.IsBridge s(y, t) → H.degree t ≤ 1) → Desc H k y ∅

section pieces

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem desc0_of_dstmt0E {j N : ℕ} (hD : DStmt0E.{u} j N) {H : SimpleGraph V}
    [DecidableRel H.Adj] (hE : H.edgeFinset.card ≤ N) (hconn : NIConn H)
    (hev : Even (nonIso H).card) (h2j : 2 * j ≤ (evenSet H).card) {y : V}
    (hy : y ∈ evenSet H) : Desc H j y ∅ := by
  have hs : ∀ a b, H.Adj a b → a ∈ {v | 0 < H.degree v} := fun a b h => by
    simp only [Set.mem_ofPred_eq]; rw [degree_pos_iff_exists_adj]; exact ⟨b, h⟩
  have hy' : y ∈ {v | 0 < H.degree v} := (mem_evenSet_iff_even.mp hy).1
  have hcard : Fintype.card {v | 0 < H.degree v} = (nonIso H).card := by
    rw [Fintype.card_subtype]; rfl
  have hEv : (evenSet (H.induce {v | 0 < H.degree v})).card = (evenSet H).card := by
    rw [← evenSet_induce_map hs, Finset.card_map]
  have h := hD _ (H.induce {v | 0 < H.degree v}) ((card_edgeFinset_induce_le hs).trans hE)
    (induce_nonIso_connected hconn hy') (hcard ▸ hev) (hEv ▸ h2j) ⟨y, hy'⟩
    ((mem_evenSet_induce hs _).2 hy)
  have := desc_of_induce hs h
  simpa using this

theorem desc0_of_dstmt0 {j : ℕ} (hD : DStmt0.{u} j) {H : SimpleGraph V} [DecidableRel H.Adj]
    (hconn : NIConn H) (hev : Even (nonIso H).card) (h2j : 2 * j ≤ (evenSet H).card) {y : V}
    (hy : y ∈ evenSet H) : Desc H j y ∅ :=
  desc0_of_dstmt0E (N := H.edgeFinset.card)
    (fun W _ _ H' _ _ hc hn h2 y' hy' => hD W H' hc hn h2 y' hy') le_rfl hconn hev h2j hy

/-- Descent in a piece, keeping `kept` when it is even. -/
theorem piece_desc0 {P : SimpleGraph V} [DecidableRel P.Adj] {k M r : ℕ}
    (hlow : ∀ j, 1 ≤ j → j ≤ k → DStmt0.{u} j) (hIH : DStmt0E.{u} (k + 1) M)
    (hEP : P.edgeFinset.card ≤ M) (hr : r ≤ k + 1) (hconn : NIConn P)
    (hev : Even (nonIso P).card) (h2r : 2 * r ≤ (evenSet P).card) (kept : V) :
    ∃ R ⊆ evenSet P, R.card = r ∧ kept ∉ R ∧ Realisable P (evenSet P \ R) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr1
  · exact ⟨∅, Finset.empty_subset _, rfl, by simp, by simpa using realisable_evenSet_ni P⟩
  have hdesc : ∀ y', y' ∈ evenSet P → Desc P r y' ∅ := by
    intro y' hy'
    by_cases hrk : r ≤ k
    · exact desc0_of_dstmt0 (hlow r hr1 hrk) hconn hev h2r hy'
    · have : r = k + 1 := by omega
      subst this
      exact desc0_of_dstmt0E hIH hEP hconn hev h2r hy'
  obtain ⟨y', hy', hky'⟩ : ∃ y' ∈ evenSet P, kept ∈ evenSet P → y' = kept := by
    by_cases hk : kept ∈ evenSet P
    · exact ⟨kept, hk, fun _ => rfl⟩
    · obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < (evenSet P).card by omega)
      exact ⟨a, ha, fun h => absurd h hk⟩
  obtain ⟨R, hRE, hRc, -, hyR, hreal⟩ := hdesc y' hy'
  exact ⟨R, hRE, hRc, fun hkR => hyR (hky' (hRE hkR) ▸ hkR), hreal⟩

end pieces

section bridge0

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem bridge_odd0 {k M : ℕ} (hlow : ∀ j, 1 ≤ j → j ≤ k → DStmt0.{u} j)
    (hIH : DStmt0E.{u} (k + 1) M) (hG : ∀ v, 0 < G.degree v) (hn : Even (Fintype.card V))
    (hEM : G.edgeFinset.card ≤ M + 1) (h2k : 2 * (k + 1) ≤ (evenSet G).card) {y t : V}
    (hy : y ∈ evenSet G) (hyt : G.Adj y t)
    (hdt : 2 ≤ G.degree t) {A : Finset V} (hyA : y ∈ A) (htA : t ∉ A)
    (hcross : ∀ a b, G.Adj a b → a ∈ A → b ∉ A → a = y ∧ b = t)
    (hreachA : ∀ v ∈ A, (restr G A).Reachable y v)
    (hreachB : ∀ v ∉ A, (restr G Aᶜ).Reachable t v) (hAodd : Odd A.card) :
    Desc G (k + 1) y ∅ := by
  have hyt' : y ≠ t := hyt.ne
  have nbrA : ∀ v ∈ A, v ≠ y → ∀ b, G.Adj v b → b ∈ A := fun v hv hvy b h => by
    by_contra hb; exact hvy (hcross v b h hv hb).1
  have nbrB : ∀ v, v ∉ A → v ≠ t → ∀ b, G.Adj v b → b ∉ A := fun v hv hvt b h hb =>
    hvt (hcross b v h.symm hb hv).2
  have nbrY : ∀ b, G.Adj y b → b ≠ t → b ∈ A := fun b h hbt => by
    by_contra hb; exact hbt (hcross y b h hyA hb).2
  have nbrT : ∀ b, G.Adj t b → b ≠ y → b ∉ A := fun b h hby hb =>
    hby (hcross b t h.symm hb htA).1
  -- degrees in the pieces
  have dA_A : ∀ v ∈ A, (restr G (insert t A)).degree v = G.degree v := by
    intro v hv
    refine degree_restr_full (Finset.mem_insert_of_mem hv) (fun b h => ?_)
    by_cases hvy : v = y
    · subst hvy
      by_cases hbt : b = t
      · exact hbt ▸ Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (nbrY b h hbt)
    · exact Finset.mem_insert_of_mem (nbrA v hv hvy b h)
  have dA_t : (restr G (insert t A)).degree t = 1 := degree_restr_one (Finset.mem_insert_self _ _) hyt.symm
    (Finset.mem_insert_of_mem hyA) (fun b h hb => by
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact absurd h (G.loopless.irrefl _)
      · by_contra hby; exact nbrT b h hby hb)
  have dA_out : ∀ v, v ∉ A → v ≠ t → (restr G (insert t A)).degree v = 0 := fun v hv hvt =>
    degree_restr_out (by simp [hv, hvt])
  have dB_B : ∀ v, v ∉ A → (restr G (insert y Aᶜ)).degree v = G.degree v := by
    intro v hv
    refine degree_restr_full (Finset.mem_insert_of_mem (Finset.mem_compl.mpr hv))
      (fun b h => ?_)
    by_cases hvt : v = t
    · subst hvt
      by_cases hby : b = y
      · exact hby ▸ Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_compl.mpr (nbrT b h hby))
    · exact Finset.mem_insert_of_mem (Finset.mem_compl.mpr (nbrB v hv hvt b h))
  have dB_y : (restr G (insert y Aᶜ)).degree y = 1 := degree_restr_one (Finset.mem_insert_self _ _) hyt
    (Finset.mem_insert_of_mem (Finset.mem_compl.mpr htA)) (fun b h hb => by
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact absurd h (G.loopless.irrefl _)
      · by_contra hbt; exact Finset.mem_compl.mp hb (nbrY b h hbt))
  have dB_out : ∀ v ∈ A, v ≠ y → (restr G (insert y Aᶜ)).degree v = 0 := fun v hv hvy =>
    degree_restr_out (by simp [hv, hvy])
  -- even vertices of the pieces
  have EvA : evenSet (restr G (insert t A)) = (evenSet G).filter (· ∈ A) := by
    ext v
    simp only [Finset.mem_filter]
    by_cases hv : v ∈ A
    · rw [mem_evenSet_iff_even, mem_evenSet_iff_even, dA_A v hv]; simp [hv]
    · simp only [hv, and_false, iff_false]
      by_cases hvt : v = t
      · subst hvt; rw [mem_evenSet_iff_even, dA_t]; decide
      · rw [mem_evenSet_iff_even, dA_out v hv hvt]; simp
  have EvB : evenSet (restr G (insert y Aᶜ)) = (evenSet G).filter (· ∉ A) := by
    ext v
    simp only [Finset.mem_filter]
    by_cases hv : v ∈ A
    · simp only [hv, not_true_eq_false, and_false, iff_false]
      by_cases hvy : v = y
      · subst hvy; rw [mem_evenSet_iff_even, dB_y]; decide
      · rw [mem_evenSet_iff_even, dB_out v hv hvy]; simp
    · rw [mem_evenSet_iff_even, mem_evenSet_iff_even, dB_B v hv]; simp [hv]
  have hEvsum : (evenSet (restr G (insert t A))).card + (evenSet (restr G (insert y Aᶜ))).card = (evenSet G).card := by
    rw [EvA, EvB]; exact Finset.card_filter_add_card_filter_not (fun v => v ∈ A)
  -- non-isolated vertices, connectivity, parity
  have nonA : nonIso (restr G (insert t A)) = insert t A := by
    ext v
    simp only [nonIso, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hv : v ∈ A
    · rw [dA_A v hv]; simp [hv, hG v]
    · by_cases hvt : v = t
      · subst hvt; rw [dA_t]; simp
      · rw [dA_out v hv hvt]; simp [hv, hvt]
  have nonB : nonIso (restr G (insert y Aᶜ)) = insert y Aᶜ := by
    ext v
    simp only [nonIso, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_compl]
    by_cases hv : v ∈ A
    · by_cases hvy : v = y
      · subst hvy; rw [dB_y]; simp
      · rw [dB_out v hv hvy]; simp [hv, hvy]
    · rw [dB_B v hv]; simp [hv, hG v]
  have hevA : Even (nonIso (restr G (insert t A))).card := by
    rw [nonA, Finset.card_insert_of_notMem htA]; exact hAodd.add_one
  have hevB : Even (nonIso (restr G (insert y Aᶜ))).card := by
    rw [nonB, Finset.card_insert_of_notMem (by simp [hyA]), Finset.card_compl]
    have := Finset.card_le_univ A
    obtain ⟨m, hm⟩ := hn
    obtain ⟨j, hj⟩ := hAodd
    exact ⟨m - j, by omega⟩
  have hconnA : NIConn (restr G (insert t A)) := by
    have key : ∀ v, 0 < (restr G (insert t A)).degree v → (restr G (insert t A)).Reachable y v := by
      intro v hv
      by_cases hvA : v ∈ A
      · exact (hreachA v hvA).mono (by
          intro a b h; exact ⟨h.1, Finset.mem_insert_of_mem h.2.1, Finset.mem_insert_of_mem h.2.2⟩)
      · by_cases hvt : v = t
        · rw [hvt]
          exact (show (restr G (insert t A)).Adj y t from ⟨hyt, Finset.mem_insert_of_mem hyA,
            Finset.mem_insert_self _ _⟩).reachable
        · rw [dA_out v hvA hvt] at hv; exact absurd hv (lt_irrefl 0)
    exact fun a b ha hb => (key a ha).symm.trans (key b hb)
  have hconnB : NIConn (restr G (insert y Aᶜ)) := by
    have key : ∀ v, 0 < (restr G (insert y Aᶜ)).degree v → (restr G (insert y Aᶜ)).Reachable t v := by
      intro v hv
      by_cases hvA : v ∈ A
      · by_cases hvy : v = y
        · rw [hvy]
          exact (show (restr G (insert y Aᶜ)).Adj t y from ⟨hyt.symm, Finset.mem_insert_of_mem
            (Finset.mem_compl.mpr htA), Finset.mem_insert_self _ _⟩).reachable
        · rw [dB_out v hvA hvy] at hv; exact absurd hv (lt_irrefl 0)
      · exact (hreachB v hvA).mono (by
          intro a b h; exact ⟨h.1, Finset.mem_insert_of_mem h.2.1, Finset.mem_insert_of_mem h.2.2⟩)
    exact fun a b ha hb => (key a ha).symm.trans (key b hb)
  -- fewer edges
  obtain ⟨c, hc, hcy⟩ : ∃ c, G.Adj t c ∧ c ≠ y := by
    have : 1 < (G.neighborFinset t).card := by rw [card_neighborFinset_eq_degree]; omega
    obtain ⟨c, hc, hcy⟩ := Finset.exists_mem_ne this y
    exact ⟨c, (mem_neighborFinset _ _ _).mp hc, hcy⟩
  obtain ⟨d, hd, hdt'⟩ : ∃ d, G.Adj y d ∧ d ≠ t := by
    have hdy : 2 ≤ G.degree y := by
      obtain ⟨hp, j, hj⟩ := mem_evenSet_iff_even.mp hy; omega
    have : 1 < (G.neighborFinset y).card := by rw [card_neighborFinset_eq_degree]; omega
    obtain ⟨d, hd, hdt'⟩ := Finset.exists_mem_ne this t
    exact ⟨d, (mem_neighborFinset _ _ _).mp hd, hdt'⟩
  have hEA : (restr G (insert t A)).edgeFinset.card ≤ M := by
    have := card_edgeFinset_restr_lt (C := insert t A) hc (fun h => by
      have := h.2; simp only [Finset.mem_insert] at this
      rcases this with rfl | h'
      · exact G.loopless.irrefl _ hc
      · exact nbrT c hc hcy h')
    omega
  have hEB : (restr G (insert y Aᶜ)).edgeFinset.card ≤ M := by
    have := card_edgeFinset_restr_lt (C := insert y Aᶜ) hd (fun h => by
      have := h.2; simp only [Finset.mem_insert, Finset.mem_compl] at this
      rcases this with rfl | h'
      · exact G.loopless.irrefl _ hd
      · exact h' (nbrY d hd hdt'))
    omega
  -- distribute the `k + 1` removals
  have hyEA : y ∈ evenSet (restr G (insert t A)) := by rw [EvA]; simp [hy, hyA]
  obtain ⟨a2, ha2⟩ := even_card_evenSet_of_nonIso hevA
  obtain ⟨b2, hb2⟩ := even_card_evenSet_of_nonIso hevB
  obtain ⟨rA, rB, hsum, hrA, hrB⟩ := split_any (k + 1) a2 b2 (by omega)
  -- descents in the pieces
  obtain ⟨RA, hRAE, hRAc, hyRA, -, DA, hDA⟩ :=
    piece_desc0 (r := rA) hlow hIH hEA (by omega) hconnA hevA (by omega) y
  obtain ⟨RB, hRBE, hRBc, -, -, DB, hDB⟩ :=
    piece_desc0 (r := rB) hlow hIH hEB (by omega) hconnB hevB (by omega) y
  -- glue
  obtain ⟨D, -, hD⟩ := glue_bridge DA DB (A := (A : Set V)) (B := ((Aᶜ : Finset V) : Set V))
    hyA (by simp [htA]) (fun x hx => by simpa using hx)
    ⟨hyt, Finset.mem_insert_of_mem hyA, Finset.mem_insert_self _ _⟩
    ⟨hyt, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_compl.mpr htA)⟩
    (fun a b h hne => by
      obtain ⟨hab, ha, hb⟩ := h
      simp only [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact absurd hab (G.loopless.irrefl _)
        · obtain ⟨rfl, -⟩ := hcross b a hab.symm hb htA
          exact absurd Sym2.eq_swap hne
      rcases hb with rfl | hb
      · obtain ⟨rfl, -⟩ := hcross a b hab ha htA
        exact absurd rfl hne
      exact ⟨ha, hb⟩)
    (fun a b h hne => by
      obtain ⟨hab, ha, hb⟩ := h
      simp only [Finset.mem_insert, Finset.mem_compl] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact absurd hab (G.loopless.irrefl _)
        · obtain ⟨-, rfl⟩ := hcross a b hab hyA hb
          exact absurd rfl hne
      rcases hb with rfl | hb
      · obtain ⟨-, rfl⟩ := hcross b a hab.symm hyA ha
        exact absurd Sym2.eq_swap hne
      exact ⟨by simpa using ha, by simpa using hb⟩)
    (fun e => by
      induction e using Sym2.inductionOn with
      | hf a b =>
        simp only [mem_edgeSet, restr_adj, Finset.mem_insert, Finset.mem_compl]
        constructor
        · intro h
          by_cases ha : a ∈ A
          · by_cases hb : b ∈ A
            · exact Or.inl ⟨h, Or.inr ha, Or.inr hb⟩
            · obtain ⟨rfl, rfl⟩ := hcross a b h ha hb
              exact Or.inl ⟨h, Or.inr ha, Or.inl rfl⟩
          · by_cases hb : b ∈ A
            · obtain ⟨rfl, rfl⟩ := hcross b a h.symm hb ha
              exact Or.inl ⟨h, Or.inl rfl, Or.inr hb⟩
            · exact Or.inr ⟨h, Or.inr ha, Or.inr hb⟩
        · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h)
  -- the result
  refine ⟨RA ∪ RB, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · have := hRAE h; rw [EvA] at this; exact (Finset.mem_filter.mp this).1
    · have := hRBE h; rw [EvB] at this; exact (Finset.mem_filter.mp this).1
  · rw [Finset.card_union_of_disjoint (by
      rw [Finset.disjoint_left]
      intro x h1 h2
      have := hRAE h1; rw [EvA] at this
      have := hRBE h2; rw [EvB] at this
      simp_all), hRAc, hRBc, hsum]
  · exact Finset.empty_subset _
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · exact hyRA h
    · have := hRBE h; rw [EvB] at this; exact (Finset.mem_filter.mp this).2 hyA
  · refine ⟨Finset.sdiff_subset, D, fun v => ?_⟩
    have h1 := hD v
    have hA' := hDA v
    have hB' := hDB v
    have hRAA : ∀ x ∈ RA, x ∈ A := fun x hx => by
      have := hRAE hx; rw [EvA] at this; exact (Finset.mem_filter.mp this).2
    have hRBB : ∀ x ∈ RB, x ∉ A := fun x hx => by
      have := hRBE hx; rw [EvB] at this; exact (Finset.mem_filter.mp this).2
    by_cases hvy : v = y
    · subst hvy
      rw [profile_even_mem (mem_evenSet_iff_even.mp hyEA).2 (Finset.mem_sdiff.mpr ⟨hyEA, hyRA⟩)]
        at hA'
      rw [profile_odd (by rw [dB_y]; decide)] at hB'
      rw [profile_even_mem (mem_evenSet_iff_even.mp hy).2 (Finset.mem_sdiff.mpr ⟨hy, by
        simp only [Finset.mem_union, not_or]; exact ⟨hyRA, fun h => hRBB v h hyA⟩⟩)]
      simp only [Ne.symm hyt', ite_false, ite_true] at h1
      omega
    by_cases hvt : v = t
    · subst hvt
      rw [profile_odd (by rw [dA_t]; decide)] at hA'
      have : D.ends v = DB.ends v := by
        simp only [hvy, Ne.symm hvy, ite_false, ite_true] at h1; omega
      rw [this, hB']
      apply profile_congr (dB_B v htA)
      rw [EvB]
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_union, not_or]
      constructor
      · rintro ⟨⟨h, -⟩, h'⟩; exact ⟨h, fun h'' => htA (hRAA v h''), h'⟩
      · rintro ⟨h, -, h'⟩; exact ⟨⟨h, htA⟩, h'⟩
    simp only [Ne.symm hvy, Ne.symm hvt, ite_false, add_zero] at h1
    by_cases hvA : v ∈ A
    · rw [profile_zero_of_degree Finset.sdiff_subset (dB_out v hvA hvy)] at hB'
      rw [h1, hA', hB', add_zero]
      apply profile_congr (dA_A v hvA)
      rw [EvA]
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_union, not_or]
      constructor
      · rintro ⟨⟨h, -⟩, h'⟩; exact ⟨h, h', fun h'' => hRBB v h'' hvA⟩
      · rintro ⟨h, h', -⟩; exact ⟨⟨h, hvA⟩, h'⟩
    · rw [profile_zero_of_degree Finset.sdiff_subset (dA_out v hvA hvt)] at hA'
      rw [h1, hA', hB', zero_add]
      apply profile_congr (dB_B v hvA)
      rw [EvB]
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_union, not_or]
      constructor
      · rintro ⟨⟨h, -⟩, h'⟩; exact ⟨h, fun h'' => hvA (hRAA v h''), h'⟩
      · rintro ⟨h, -, h'⟩; exact ⟨⟨h, hvA⟩, h'⟩

theorem bridge_even0 {k M : ℕ} (hlow : ∀ j, 1 ≤ j → j ≤ k → DStmt0.{u} j)
    (hIH : DStmt0E.{u} (k + 1) M) (hG : ∀ v, 0 < G.degree v) (hn : Even (Fintype.card V))
    (hEM : G.edgeFinset.card ≤ M + 1) (h2k : 2 * (k + 1) ≤ (evenSet G).card) {y t : V}
    (hy : y ∈ evenSet G) (hyt : G.Adj y t)
    (hdt : 2 ≤ G.degree t) {A : Finset V} (hyA : y ∈ A) (htA : t ∉ A)
    (hcross : ∀ a b, G.Adj a b → a ∈ A → b ∉ A → a = y ∧ b = t)
    (hreachA : ∀ v ∈ A, (restr G A).Reachable y v)
    (hreachB : ∀ v ∉ A, (restr G Aᶜ).Reachable t v) (hAeven : Even A.card) :
    Desc G (k + 1) y ∅ := by
  have hyt' : y ≠ t := hyt.ne
  have nbrA : ∀ v ∈ A, v ≠ y → ∀ b, G.Adj v b → b ∈ A := fun v hv hvy b h => by
    by_contra hb; exact hvy (hcross v b h hv hb).1
  have nbrB : ∀ v, v ∉ A → v ≠ t → ∀ b, G.Adj v b → b ∉ A := fun v hv hvt b h hb =>
    hvt (hcross b v h.symm hb hv).2
  have nbrY : ∀ b, G.Adj y b → b ≠ t → b ∈ A := fun b h hbt => by
    by_contra hb; exact hbt (hcross y b h hyA hb).2
  have nbrT : ∀ b, G.Adj t b → b ≠ y → b ∉ A := fun b h hby hb =>
    hby (hcross b t h.symm hb htA).1
  obtain ⟨hy0, jy, hjy⟩ := mem_evenSet_iff_even.mp hy
  -- degrees
  have dA_A : ∀ v ∈ A, v ≠ y → (restr G A).degree v = G.degree v := fun v hv hvy =>
    degree_restr_full hv (nbrA v hv hvy)
  have dA_y : (restr G A).degree y + 1 = G.degree y :=
    degree_restr_minus hyA hyt htA (fun b h hbt => nbrY b h hbt)
  have dA_out : ∀ v, v ∉ A → (restr G A).degree v = 0 := fun v hv => degree_restr_out hv
  have dB_B : ∀ v, v ∉ A → v ≠ t → (restr G Aᶜ).degree v = G.degree v := fun v hv hvt =>
    degree_restr_full (Finset.mem_compl.mpr hv)
      (fun b h => Finset.mem_compl.mpr (nbrB v hv hvt b h))
  have dB_t : (restr G Aᶜ).degree t + 1 = G.degree t :=
    degree_restr_minus (Finset.mem_compl.mpr htA) hyt.symm (by simp [hyA])
      (fun b h hby => Finset.mem_compl.mpr (nbrT b h hby))
  have dB_out : ∀ v ∈ A, (restr G Aᶜ).degree v = 0 := fun v hv =>
    degree_restr_out (by simp [hv])
  have hyodd : Odd ((restr G A).degree y) := ⟨jy - 1, by omega⟩
  -- even vertices
  have EvA : evenSet (restr G A) = ((evenSet G).filter (· ∈ A)).erase y := by
    ext v
    simp only [Finset.mem_erase, Finset.mem_filter]
    by_cases hv : v ∈ A
    · by_cases hvy : v = y
      · rw [hvy]
        simp only [ne_eq, not_true_eq_false, false_and, iff_false]
        exact fun h => (Nat.not_even_iff_odd.mpr hyodd) (mem_evenSet_iff_even.mp h).2
      · rw [mem_evenSet_iff_even, mem_evenSet_iff_even, dA_A v hv hvy]; simp [hv, hvy]
    · rw [mem_evenSet_iff_even, dA_out v hv]; simp [hv]
  have hEvA_card : (evenSet (restr G A)).card + 1 = ((evenSet G).filter (· ∈ A)).card := by
    rw [EvA, Finset.card_erase_of_mem (by simp [hy, hyA])]
    have : 0 < ((evenSet G).filter (· ∈ A)).card := Finset.card_pos.mpr ⟨y, by simp [hy, hyA]⟩
    omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := evenSet G) (fun v => v ∈ A)
  -- non-isolated vertices, connectivity, parity
  have nonA : nonIso (restr G A) = A := by
    ext v
    simp only [nonIso, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hv : v ∈ A
    · by_cases hvy : v = y
      · rw [hvy]; simp [hyA]; omega
      · rw [dA_A v hv hvy]; simp [hv, hG v]
    · rw [dA_out v hv]; simp [hv]
  have nonB : nonIso (restr G Aᶜ) = Aᶜ := by
    ext v
    simp only [nonIso, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
    by_cases hv : v ∈ A
    · rw [dB_out v hv]; simp [hv]
    · by_cases hvt : v = t
      · rw [hvt]; simp [htA]; omega
      · rw [dB_B v hv hvt]; simp [hv, hG v]
  have hevA : Even (nonIso (restr G A)).card := by rw [nonA]; exact hAeven
  have hevB : Even (nonIso (restr G Aᶜ)).card := by
    rw [nonB, Finset.card_compl]
    have := Finset.card_le_univ A
    obtain ⟨m, hm⟩ := hn
    obtain ⟨j, hj⟩ := hAeven
    exact ⟨m - j, by omega⟩
  have hconnA : NIConn (restr G A) := by
    have key : ∀ v, 0 < (restr G A).degree v → (restr G A).Reachable y v := by
      intro v hv
      by_cases hvA : v ∈ A
      · exact hreachA v hvA
      · rw [dA_out v hvA] at hv; exact absurd hv (lt_irrefl 0)
    exact fun a b ha hb => (key a ha).symm.trans (key b hb)
  have hconnB : NIConn (restr G Aᶜ) := by
    have key : ∀ v, 0 < (restr G Aᶜ).degree v → (restr G Aᶜ).Reachable t v := by
      intro v hv
      by_cases hvA : v ∈ A
      · rw [dB_out v hvA] at hv; exact absurd hv (lt_irrefl 0)
      · exact hreachB v hvA
    exact fun a b ha hb => (key a ha).symm.trans (key b hb)
  have hEA : (restr G A).edgeFinset.card ≤ M := by
    have := card_edgeFinset_restr_lt (C := A) hyt (fun h => htA h.2); omega
  have hEB : (restr G Aᶜ).edgeFinset.card ≤ M := by
    have := card_edgeFinset_restr_lt (C := Aᶜ) hyt (fun h => (Finset.mem_compl.mp h.1) hyA)
    omega
  -- gluing data
  have hdisj : ∀ e, e ∈ (restr G A).edgeSet → e ∉ (restr G Aᶜ).edgeSet := by
    intro e h1 h2
    induction e using Sym2.inductionOn with
    | hf a b => exact (Finset.mem_compl.mp h2.2.1) h1.2.1
  have hK : ∀ e, e ∈ (delE G {s(y, t)}).edgeSet ↔
      e ∈ (restr G A).edgeSet ∨ e ∈ (restr G Aᶜ).edgeSet := by
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      rw [delE_edgeSet, Finset.mem_singleton]
      simp only [mem_edgeSet, restr_adj, Finset.mem_compl]
      constructor
      · rintro ⟨h, hne⟩
        by_cases ha : a ∈ A
        · by_cases hb : b ∈ A
          · exact Or.inl ⟨h, ha, hb⟩
          · obtain ⟨rfl, rfl⟩ := hcross a b h ha hb; exact absurd rfl hne
        · by_cases hb : b ∈ A
          · obtain ⟨rfl, rfl⟩ := hcross b a h.symm hb ha; exact absurd Sym2.eq_swap hne
          · exact Or.inr ⟨h, ha, hb⟩
      · rintro (⟨h, ha, hb⟩ | ⟨h, ha, hb⟩)
        · refine ⟨h, fun he => ?_⟩
          rcases Sym2.eq_iff.mp he with ⟨-, rfl⟩ | ⟨rfl, -⟩
          · exact htA hb
          · exact htA ha
        · refine ⟨h, fun he => ?_⟩
          rcases Sym2.eq_iff.mp he with ⟨rfl, -⟩ | ⟨-, rfl⟩
          · exact ha hyA
          · exact hb hyA
  have hGK : ∀ e, e ∈ G.edgeSet ↔ e ∈ (delE G {s(y, t)}).edgeSet ∨ e = s(t, y) := by
    intro e
    rw [delE_edgeSet, Finset.mem_singleton, Sym2.eq_swap (a := t)]
    constructor
    · intro h; by_cases he : e = s(y, t)
      · exact Or.inr he
      · exact Or.inl ⟨h, he⟩
    · rintro (⟨h, -⟩ | rfl)
      · exact h
      · exact hyt
  have hKty : ¬ (delE G {s(y, t)}).Adj t y := fun h =>
    (delE_adj.mp h).2 (by simp [Sym2.eq_swap])
  -- the final check, shared by both parities of `t`
  have hfinal : ∀ (RA RB : Finset V) (DA : PathDecomp (restr G A))
      (DB : PathDecomp (restr G Aᶜ)) (D : PathDecomp G),
      RA ⊆ evenSet (restr G A) → RB ⊆ evenSet (restr G Aᶜ) →
      Realises (restr G A) DA (evenSet (restr G A) \ RA) →
      Realises (restr G Aᶜ) DB (evenSet (restr G Aᶜ) \ RB) →
      (∀ v, D.ends v + (if t = v then 1 else 0) =
        DA.ends v + DB.ends v + (if y = v then 1 else 0)) →
      ∀ R : Finset V, (∀ v ∈ A, v ∈ R ↔ v ∈ RA) → (∀ v, v ∉ A → v ≠ t → (v ∈ R ↔ v ∈ RB)) →
      y ∉ R → (t ∈ evenSet G → t ∈ R) → (t ∉ evenSet G → t ∈ evenSet (restr G Aᶜ) \ RB) →
      Realises G D (evenSet G \ R) := by
    intro RA RB DA DB D hRA hRB hDA hDB hD R hRA' hRB' hyR htR htR'
    intro v
    have h1 := hD v
    have hA' := hDA v
    have hB' := hDB v
    by_cases hvy : v = y
    · rw [hvy] at h1 hA' hB' ⊢
      rw [profile_odd hyodd] at hA'
      rw [profile_zero_of_degree Finset.sdiff_subset (dB_out y hyA)] at hB'
      rw [profile_even_mem (mem_evenSet_iff_even.mp hy).2 (Finset.mem_sdiff.mpr ⟨hy, hyR⟩)]
      simp only [hyt', Ne.symm hyt', ite_false, ite_true] at h1
      omega
    by_cases hvt : v = t
    · rw [hvt] at h1 hA' hB' ⊢
      rw [profile_zero_of_degree Finset.sdiff_subset (dA_out t htA)] at hA'
      simp only [hyt', Ne.symm hyt', ite_false, ite_true] at h1
      by_cases htE : t ∈ evenSet G
      · have htodd : Odd ((restr G Aᶜ).degree t) := by
          obtain ⟨-, i, hi⟩ := mem_evenSet_iff_even.mp htE; exact ⟨i - 1, by omega⟩
        rw [profile_odd htodd] at hB'
        rw [profile_even_not_mem (mem_evenSet_iff_even.mp htE).2
          (fun h => (Finset.mem_sdiff.mp h).2 (htR htE))]
        omega
      · have htev := htR' htE
        rw [profile_even_mem (mem_evenSet_iff_even.mp (Finset.mem_sdiff.mp htev).1).2 htev]
          at hB'
        rw [profile_odd (odd_of_not_mem_evenSet hG htE)]
        omega
    simp only [Ne.symm hvy, Ne.symm hvt, ite_false, add_zero] at h1
    by_cases hvA : v ∈ A
    · rw [profile_zero_of_degree Finset.sdiff_subset (dB_out v hvA)] at hB'
      rw [h1, hA', hB', add_zero]
      apply profile_congr (dA_A v hvA hvy)
      rw [EvA]
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_filter]
      rw [hRA' v hvA]
      constructor
      · rintro ⟨⟨-, h, -⟩, h'⟩; exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨⟨hvy, h, hvA⟩, h'⟩
    · rw [profile_zero_of_degree Finset.sdiff_subset (dA_out v hvA)] at hA'
      rw [h1, hA', hB', zero_add]
      apply profile_congr (dB_B v hvA hvt)
      simp only [Finset.mem_sdiff]
      rw [hRB' v hvA hvt]
      have : v ∈ evenSet (restr G Aᶜ) ↔ v ∈ evenSet G := by
        rw [mem_evenSet_iff_even, mem_evenSet_iff_even, dB_B v hvA hvt]
      rw [this]
  have hRAA : ∀ (RA : Finset V), RA ⊆ evenSet (restr G A) → ∀ x ∈ RA, x ∈ A ∧ x ≠ y := by
    intro RA hRA x hx
    have := hRA hx; rw [EvA] at this
    simp only [Finset.mem_erase, Finset.mem_filter] at this
    exact ⟨this.2.2, this.1⟩
  have hRBB : ∀ (RB : Finset V), RB ⊆ evenSet (restr G Aᶜ) → ∀ x ∈ RB, x ∉ A := by
    intro RB hRB x hx
    have := hRB hx
    by_contra hxA
    have := (mem_evenSet_iff_even.mp this).1
    rw [dB_out x hxA] at this
    exact lt_irrefl 0 this
  have hBpaths : ∀ DB : PathDecomp (restr G Aᶜ), ∀ P ∈ DB.paths, y ∉ P.walk.support :=
    fun DB P _ hyP => (Finset.mem_compl.mp (restr_path_support P y hyP)) hyA
  by_cases htE : t ∈ evenSet G
  · -- `t` even in `G`: remove `t`, and `k` further vertices
    obtain ⟨-, jt, hjt⟩ := mem_evenSet_iff_even.mp htE
    have htodd : Odd ((restr G Aᶜ).degree t) := ⟨jt - 1, by omega⟩
    have EvB : evenSet (restr G Aᶜ) = ((evenSet G).filter (· ∉ A)).erase t := by
      ext v
      simp only [Finset.mem_erase, Finset.mem_filter]
      by_cases hv : v ∈ A
      · rw [mem_evenSet_iff_even, dB_out v hv]; simp [hv]
      · by_cases hvt : v = t
        · rw [hvt]
          simp only [ne_eq, not_true_eq_false, false_and, iff_false]
          exact fun h => (Nat.not_even_iff_odd.mpr htodd) (mem_evenSet_iff_even.mp h).2
        · rw [mem_evenSet_iff_even, mem_evenSet_iff_even, dB_B v hv hvt]; simp [hv, hvt]
    have hEvB_card : (evenSet (restr G Aᶜ)).card + 1 =
        ((evenSet G).filter (· ∉ A)).card := by
      rw [EvB, Finset.card_erase_of_mem (by simp [htE, htA])]
      have : 0 < ((evenSet G).filter (· ∉ A)).card := Finset.card_pos.mpr ⟨t, by simp [htE, htA]⟩
      omega
    obtain ⟨a2, ha2⟩ := even_card_evenSet_of_nonIso hevA
    obtain ⟨b2, hb2⟩ := even_card_evenSet_of_nonIso hevB
    obtain ⟨rA, rB, hsum, hrA, hrB⟩ := split_any k a2 b2 (by omega)
    obtain ⟨RA, hRAE, hRAc, -, -, DA, hDA⟩ :=
      piece_desc0 (r := rA) hlow hIH hEA (by omega) hconnA hevA (by omega) y
    obtain ⟨RB, hRBE, hRBc, -, -, DB, hDB⟩ :=
      piece_desc0 (r := rB) hlow hIH hEB (by omega) hconnB hevB (by omega) y
    obtain ⟨D, -, hD⟩ := glue_append DA DB hdisj hK hGK hKty (hBpaths DB)
      (by rw [hDB t, profile_odd htodd]; exact Nat.one_pos)
    have htRA : t ∉ RA := fun h => htA (hRAA RA hRAE t h).1
    have htRB : t ∉ RB := fun h => by
      have := hRBE h; rw [EvB] at this; simp at this
    have hdisjAB : Disjoint RA RB := by
      rw [Finset.disjoint_left]
      exact fun x h1 h2 => hRBB RB hRBE x h2 (hRAA RA hRAE x h1).1
    refine ⟨insert t (RA ∪ RB), ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact htE
      rcases Finset.mem_union.mp hx with h | h
      · have := hRAE h; rw [EvA] at this; exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase this)).1
      · have := hRBE h; rw [EvB] at this; exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase this)).1
    · rw [Finset.card_insert_of_notMem (by simp [htRA, htRB]),
        Finset.card_union_of_disjoint hdisjAB, hRAc, hRBc]
      omega
    · exact Finset.empty_subset _
    · intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact hyt' h
      rcases Finset.mem_union.mp h with h | h
      · exact (hRAA RA hRAE y h).2 rfl
      · exact hRBB RB hRBE y h hyA
    · refine ⟨Finset.sdiff_subset, D, ?_⟩
      apply hfinal RA RB DA DB D hRAE hRBE hDA hDB hD
      · intro v hv
        simp only [Finset.mem_insert, Finset.mem_union]
        constructor
        · rintro (rfl | h | h)
          · exact absurd hv htA
          · exact h
          · exact absurd hv (hRBB RB hRBE v h)
        · intro h; exact Or.inr (Or.inl h)
      · intro v hv hvt
        simp only [Finset.mem_insert, Finset.mem_union, hvt, false_or]
        constructor
        · rintro (h | h)
          · exact absurd (hRAA RA hRAE v h).1 hv
          · exact h
        · intro h; exact Or.inr h
      · intro h
        rcases Finset.mem_insert.mp h with h | h
        · exact hyt' h
        rcases Finset.mem_union.mp h with h | h
        · exact (hRAA RA hRAE y h).2 rfl
        · exact hRBB RB hRBE y h hyA
      · intro _; exact Finset.mem_insert_self _ _
      · intro h; exact absurd htE h
  · -- `t` odd in `G`: keep `t` in `G[Aᶜ]`, remove `k + 1` vertices
    have htev : Even ((restr G Aᶜ).degree t) := by
      obtain ⟨i, hi⟩ := odd_of_not_mem_evenSet hG htE; exact ⟨i, by omega⟩
    have htEB : t ∈ evenSet (restr G Aᶜ) := mem_evenSet_iff_even.mpr ⟨by omega, htev⟩
    have EvB : evenSet (restr G Aᶜ) = insert t ((evenSet G).filter (· ∉ A)) := by
      ext v
      simp only [Finset.mem_insert, Finset.mem_filter]
      by_cases hvt : v = t
      · rw [hvt]; simp [htEB]
      · by_cases hv : v ∈ A
        · rw [mem_evenSet_iff_even, dB_out v hv]; simp [hv, hvt]
        · rw [mem_evenSet_iff_even, mem_evenSet_iff_even, dB_B v hv hvt]; simp [hv, hvt]
    have hEvB_card : (evenSet (restr G Aᶜ)).card = ((evenSet G).filter (· ∉ A)).card + 1 := by
      rw [EvB, Finset.card_insert_of_notMem (by simp [htE])]
    obtain ⟨a2, ha2⟩ := even_card_evenSet_of_nonIso hevA
    obtain ⟨b2, hb2⟩ := even_card_evenSet_of_nonIso hevB
    obtain ⟨rA, rB, hsum, hrA, hrB⟩ := split_any (k + 1) a2 b2 (by omega)
    obtain ⟨RA, hRAE, hRAc, -, -, DA, hDA⟩ :=
      piece_desc0 (r := rA) hlow hIH hEA (by omega) hconnA hevA (by omega) y
    obtain ⟨RB, hRBE, hRBc, htRB, -, DB, hDB⟩ :=
      piece_desc0 (r := rB) hlow hIH hEB (by omega) hconnB hevB (by omega) t
    have htS : t ∈ evenSet (restr G Aᶜ) \ RB := Finset.mem_sdiff.mpr ⟨htEB, htRB⟩
    obtain ⟨D, -, hD⟩ := glue_append DA DB hdisj hK hGK hKty (hBpaths DB)
      (by rw [hDB t, profile_even_mem htev htS]; exact Nat.two_pos)
    have hdisjAB : Disjoint RA RB := by
      rw [Finset.disjoint_left]
      exact fun x h1 h2 => hRBB RB hRBE x h2 (hRAA RA hRAE x h1).1
    refine ⟨RA ∪ RB, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · have := hRAE h; rw [EvA] at this
        exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase this)).1
      · have := hRBE h; rw [EvB] at this
        rcases Finset.mem_insert.mp this with rfl | h'
        · exact absurd h htRB
        · exact (Finset.mem_filter.mp h').1
    · rw [Finset.card_union_of_disjoint hdisjAB, hRAc, hRBc, hsum]
    · exact Finset.empty_subset _
    · intro h
      rcases Finset.mem_union.mp h with h | h
      · exact (hRAA RA hRAE y h).2 rfl
      · exact hRBB RB hRBE y h hyA
    · refine ⟨Finset.sdiff_subset, D, ?_⟩
      apply hfinal RA RB DA DB D hRAE hRBE hDA hDB hD
      · intro v hv
        simp only [Finset.mem_union]
        constructor
        · rintro (h | h)
          · exact h
          · exact absurd hv (hRBB RB hRBE v h)
        · intro h; exact Or.inl h
      · intro v hv hvt
        simp only [Finset.mem_union]
        constructor
        · rintro (h | h)
          · exact absurd (hRAA RA hRAE v h).1 hv
          · exact h
        · intro h; exact Or.inr h
      · intro h
        rcases Finset.mem_union.mp h with h | h
        · exact (hRAA RA hRAE y h).2 rfl
        · exact hRBB RB hRBE y h hyA
      · intro h; exact absurd h htE
      · intro _; exact htS

/-- Transfer from `k`-step descent in `G − yt`, `t` the only even neighbour of `y`. -/
theorem desc_succ_of_transfer0 {k : ℕ} {y t y' : V} (hy : y ∈ evenSet G)
    (ht : t ∈ evenSet G) (hyt : G.Adj y t) (huniq : ∀ v ∈ evenSet G, G.Adj y v → v = t)
    (hdesc : Desc (delE G {s(y, t)}) k y' ∅) : Desc G (k + 1) y ∅ := by
  have hyt' : y ≠ t := hyt.ne
  have hEvK := evenSet_delE_even hy ht hyt
  obtain ⟨W', hWK, hWc, -, -, hreal⟩ := hdesc
  have hWE : ∀ a ∈ W', a ∈ evenSet G ∧ a ≠ y ∧ a ≠ t := by
    intro a ha
    have := hWK ha
    rw [hEvK] at this
    simp only [Finset.mem_erase] at this
    exact ⟨this.2.2, this.2.1, this.1⟩
  have htrans := realisable_transfer hy ht hyt hreal (by
    intro u hu huS hadj
    have huW : u ∈ W' := by
      by_contra h; exact huS (Finset.mem_sdiff.mpr ⟨hu, h⟩)
    exact (hWE u huW).2.2 (huniq u (hWE u huW).1 hadj))
  have htW : t ∉ W' := fun h => (hWE t h).2.2 rfl
  have hyW : y ∉ W' := fun h => (hWE y h).2.1 rfl
  refine ⟨insert t W', ?_, ?_, Finset.empty_subset _, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ht
    · exact (hWE a ha).1
  · rw [Finset.card_insert_of_notMem htW, hWc]
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hyt' h
    · exact hyW h
  · convert htrans using 1
    ext a
    rw [hEvK]
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    by_cases h1 : a = y
    · rw [h1]; simp [hy, hyt', hyW]
    by_cases h2 : a = t
    · rw [h2]; simp [Ne.symm hyt']
    simp [h1, h2]

/-- **One level of the reduction.** `D⁰_1, …, D⁰_k` (`k ≥ 2`) and `BranchBase (k+1)` give
`D⁰_{k+1}`. -/
theorem dstmt0E_succ (k : ℕ) (hk : 2 ≤ k) (hlow : ∀ j, 1 ≤ j → j ≤ k → DStmt0.{u} j)
    (hB : BranchBase.{u} (k + 1)) : ∀ N, DStmt0E.{u} (k + 1) N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro W _ _ G _ hN hconn hn h2k y hy
  obtain ⟨w, hw, hwy⟩ := Finset.exists_mem_ne (show 1 < (evenSet G).card by omega) y
  have hyw : y ≠ w := Ne.symm hwy
  have hG := degree_pos_of_connected hconn hyw
  -- Case A: a bridge at `y` to a vertex of degree at least two
  by_cases h2 : ∃ t, G.Adj y t ∧ G.IsBridge s(y, t) ∧ 2 ≤ G.degree t
  · obtain ⟨t, hyt, hbr, hdt⟩ := h2
    have hN1 : 1 ≤ N := by
      have : 0 < G.edgeFinset.card := Finset.card_pos.mpr ⟨s(y, t), mem_edgeFinset.mpr hyt⟩
      omega
    have hIH : DStmt0E.{u} (k + 1) (N - 1) := ih (N - 1) (by omega)
    have hEM : G.edgeFinset.card ≤ (N - 1) + 1 := by omega
    classical
    have hnr : ¬ (delE G {s(y, t)}).Reachable y t := by
      rw [isBridge_iff] at hbr; simpa [delE] using hbr
    let A : Finset W := Finset.univ.filter (fun v => (delE G {s(y, t)}).Reachable y v)
    have hmemA : ∀ v, v ∈ A ↔ (delE G {s(y, t)}).Reachable y v := by simp [A]
    have hyA : y ∈ A := (hmemA y).2 (Reachable.refl _)
    have htA : t ∉ A := fun h => hnr ((hmemA t).1 h)
    have hcross : ∀ a b, G.Adj a b → a ∈ A → b ∉ A → a = y ∧ b = t := by
      intro a b hab ha hb
      by_cases he : s(a, b) = s(y, t)
      · rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1, h2⟩
        · exact absurd (h1 ▸ ha) htA
      · exact absurd ((hmemA b).2 (((hmemA a).1 ha).trans
          (delE_adj.mpr ⟨hab, by simpa using he⟩).reachable)) hb
    have hreachA : ∀ v ∈ A, (restr G A).Reachable y v := by
      intro v hv
      obtain ⟨p⟩ := (hmemA v).1 hv
      exact restr_reachable_of_walk p (fun x hx => (hmemA x).2 ⟨p.takeUntil x hx⟩)
    have hreachB : ∀ v ∉ A, (restr G Aᶜ).Reachable t v := by
      intro v hv
      have hvt : (delE G {s(y, t)}).Reachable t v :=
        ((delE_reach_or_reach hconn y t v).resolve_left (fun h => hv ((hmemA v).2 h.symm))).symm
      obtain ⟨p⟩ := hvt
      refine restr_reachable_of_walk p (fun x hx => Finset.mem_compl.mpr (fun hxA => ?_))
      exact hnr (((hmemA x).1 hxA).trans ⟨(p.takeUntil x hx).reverse⟩)
    rcases Nat.even_or_odd A.card with hAe | hAo
    · exact bridge_even0 hlow hIH hG hn hEM h2k hy hyt hdt hyA htA hcross hreachA hreachB hAe
    · exact bridge_odd0 hlow hIH hG hn hEM h2k hy hyt hdt hyA htA hcross hreachA hreachB hAo
  -- Case B: two even neighbours (the branching base case)
  by_cases h1 : ∃ v₁ ∈ evenSet G, ∃ v₂ ∈ evenSet G, v₁ ≠ v₂ ∧ G.Adj y v₁ ∧ G.Adj y v₂
  · exact hB W G hconn hn h2k y hy h1 (fun t hyt hbr => by
      by_contra h; exact h2 ⟨t, hyt, hbr, by omega⟩)
  have huniq : ∀ t ∈ evenSet G, G.Adj y t → ∀ v ∈ evenSet G, G.Adj y v → v = t := by
    intro t ht hyt v hv hyv
    by_contra hvt
    exact h1 ⟨t, ht, v, hv, Ne.symm hvt, hyt, hyv⟩
  -- Case C: exactly one even neighbour, through a non-bridge
  by_cases h3 : ∃ t ∈ evenSet G, G.Adj y t ∧ ¬ G.IsBridge s(y, t)
  · obtain ⟨t, ht, hyt, hnb⟩ := h3
    have hKconn := connected_delE_of_not_isBridge hconn hnb
    have hEvK := evenSet_delE_even hy ht hyt
    have hcardK : 2 * k ≤ (evenSet (delE G {s(y, t)})).card := by
      rw [hEvK, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hyt.ne.symm, ht⟩),
        Finset.card_erase_of_mem hy]
      omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < (evenSet (delE G {s(y, t)})).card by omega)
    exact desc_succ_of_transfer0 hy ht hyt (huniq t ht hyt)
      (hlow k (by omega) le_rfl W _ hKconn hn hcardK a ha)
  -- Case D: no even neighbour; delete a non-bridge edge to an odd neighbour
  have hnoev : ∀ v ∈ evenSet G, ¬ G.Adj y v := by
    intro t ht hyt
    have hbr : G.IsBridge s(y, t) := by
      by_contra h; exact h3 ⟨t, ht, hyt, h⟩
    obtain ⟨-, j, hj⟩ := mem_evenSet_iff_even.mp ht
    have := hG t
    exact h2 ⟨t, hyt, hbr, by omega⟩
  obtain ⟨t, hyt, hnb⟩ : ∃ t, G.Adj y t ∧ ¬ G.IsBridge s(y, t) := by
    by_contra hall
    push Not at hall
    have hleaf : ∀ c, G.Adj y c → ∀ d, G.Adj c d → d = y := by
      intro c hyc d hcd
      have hdeg : G.degree c ≤ 1 := by
        by_contra h; exact h2 ⟨c, hyc, hall c hyc, by omega⟩
      by_contra hdy
      have : 2 ≤ G.degree c := by
        rw [← card_neighborFinset_eq_degree]
        have hsub : ({y, d} : Finset W) ⊆ G.neighborFinset c := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact (mem_neighborFinset _ _ _).mpr hyc.symm
          · exact (mem_neighborFinset _ _ _).mpr hcd
        have := Finset.card_le_card hsub
        rwa [Finset.card_pair (Ne.symm hdy)] at this
      omega
    obtain ⟨p⟩ := hconn.preconnected y w
    have hpp := p.bypass_isPath
    cases hq : p.bypass with
    | nil => exact hyw rfl
    | @cons _ c _ hyc q =>
      rw [hq, Walk.cons_isPath_iff] at hpp
      cases q with
      | nil =>
        obtain ⟨-, j, hj⟩ := mem_evenSet_iff_even.mp hw
        have hdw : G.degree w ≤ 1 := by
          rw [← card_neighborFinset_eq_degree]
          apply Finset.card_le_one.mpr
          intro a ha b hb
          rw [hleaf w hyc a ((mem_neighborFinset _ _ _).mp ha),
            hleaf w hyc b ((mem_neighborFinset _ _ _).mp hb)]
        have := hG w
        omega
      | cons hcd q' =>
        have := hleaf c hyc _ hcd
        subst this
        exact hpp.2 (by simp)
  have htE : t ∉ evenSet G := fun h => hnoev t h hyt
  have hKconn := connected_delE_of_not_isBridge hconn hnb
  have hKpos := degree_pos_of_connected hKconn hyt.ne
  have hEvK := evenSet_delE_odd hG hy htE hyt (hKpos t)
  have hlt := card_edgeFinset_delE_lt hyt
  have htK : t ∈ evenSet (delE G {s(y, t)}) := by rw [hEvK]; exact Finset.mem_insert_self _ _
  have hcardK : 2 * (k + 1) ≤ (evenSet (delE G {s(y, t)})).card := by
    rw [hEvK, Finset.card_insert_of_notMem (fun h => htE (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem hy]
    have : 0 < (evenSet G).card := Finset.card_pos.mpr ⟨y, hy⟩
    omega
  have hdesc := ih _ (by omega) W _ le_rfl hKconn hn hcardK t htK
  exact desc_lift_of_no_even_nbr hG hy hnoev hyt (hKpos t) (Finset.empty_subset _)
    (Finset.notMem_empty _) hdesc

end bridge0

/-! ## Consequences -/

theorem dstmt0_one : DStmt0.{u} 1 := by
  intro W _ _ H _ hconn hn h2 y hy
  obtain ⟨w, hw, hwy⟩ := Finset.exists_mem_ne (show 1 < (evenSet H).card by omega) y
  obtain ⟨R, h1, h2', -, h4, h5⟩ := dstmt_one W H hconn hn h2 y w hy hw (Ne.symm hwy)
  exact ⟨R, h1, h2', Finset.empty_subset _, h4, h5⟩

theorem dstmt0_two : DStmt0.{u} 2 := by
  intro W _ _ H _ hconn hn h2 y hy
  obtain ⟨w, hw, hwy⟩ := Finset.exists_mem_ne (show 1 < (evenSet H).card by omega) y
  obtain ⟨R, h1, h2', -, h4, h5⟩ := dstmt_two W H hconn hn h2 y w hy hw (Ne.symm hwy)
  exact ⟨R, h1, h2', Finset.empty_subset _, h4, h5⟩

theorem branchBase_one : BranchBase.{u} 1 := fun W _ _ H _ hc hn h2 y hy _ _ =>
  dstmt0_one W H hc hn h2 y hy

theorem branchBase_two : BranchBase.{u} 2 := fun W _ _ H _ hc hn h2 y hy _ _ =>
  dstmt0_two W H hc hn h2 y hy

/-- `BranchBase` is weaker than `BStmt`. -/
theorem branchBase_of_bstmt {k : ℕ} (hB : BStmt.{u} k) : BranchBase.{u} k := by
  intro W _ _ H _ hc hn h2 y hy htwo _
  obtain ⟨v₁, hv₁, v₂, hv₂, h12, hy1, hy2⟩ := htwo
  obtain ⟨R, h1, h2', -, h4, h5⟩ := hB W H hc hn h2 y v₁ hy hv₁ hy1.ne
    ⟨v₁, hv₁, v₂, hv₂, h12, hy1, hy2⟩
  exact ⟨R, h1, h2', Finset.empty_subset _, h4, h5⟩

/-- `BranchBase 3, …, BranchBase K` give `D⁰_1, …, D⁰_K`. -/
theorem dstmt0_of_branchBase (K : ℕ) (hB : ∀ j, 3 ≤ j → j ≤ K → BranchBase.{u} j) :
    ∀ k, 1 ≤ k → k ≤ K → DStmt0.{u} k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk1 hkK
  rcases (show k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | hk3
  · exact dstmt0_one
  · exact dstmt0_two
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hD := dstmt0E_succ m (by omega) (fun j hj1 hjm => ih j (by omega) hj1 (by omega))
      (hB (m + 1) hk3 hkK)
    intro W _ _ H _ hconn hn h2 y hy
    exact hD _ W H le_rfl hconn hn h2 y hy

/-- The rooted test from `D⁰_{e/2}`. -/
theorem rooted_of_dstmt0 {W : Type u} [Fintype W] [DecidableEq W] {H : SimpleGraph W}
    [DecidableRel H.Adj] (hconn : H.Connected) (hn : Even (Fintype.card W)) (r : W)
    (hD : ∀ k, 1 ≤ k → 2 * k = (evenSet H).card → DStmt0.{u} k) :
    pathNumber (addLeaf H r) ≤ Fintype.card W / 2 := by
  have h2 : 1 < Fintype.card W := by
    have := Fintype.card_pos_iff.mpr ⟨r⟩
    obtain ⟨m, hm⟩ := hn
    omega
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card h2
  have hG := degree_pos_of_connected hconn hab
  have hc := card_oddSet_add_card_evenSet hG
  obtain ⟨m, hm⟩ := H.even_card_odd_degree_vertices
  have hm' : (oddSet H).card = m + m := hm
  obtain ⟨e2, he2⟩ : Even (evenSet H).card := by
    obtain ⟨c, hc'⟩ := hn; exact ⟨c - m, by omega⟩
  rcases Nat.eq_zero_or_pos e2 with he | he
  · obtain ⟨hSE, D, hDr⟩ := realisable_evenSet' hG
    have := pathNumber_addLeaf_le_of_realises hG hSE hDr (r := r) (fun h => h)
    omega
  · obtain ⟨y, hy, hry⟩ : ∃ y ∈ evenSet H, r ∈ evenSet H → y = r := by
      by_cases hr : r ∈ evenSet H
      · exact ⟨r, hr, fun _ => rfl⟩
      · obtain ⟨y, hy⟩ := Finset.card_pos.mp (show 0 < (evenSet H).card by omega)
        exact ⟨y, hy, fun h => absurd h hr⟩
    obtain ⟨R, hRE, hRc, -, hyR, hSE, D, hDr⟩ :=
      hD e2 he (by omega) W H hconn hn (by omega) y hy
    have := pathNumber_addLeaf_le_of_realises hG hSE hDr (r := r) (fun h => by
      rw [← hry h]; exact Finset.mem_sdiff.mpr ⟨hy, hyR⟩)
    rw [Finset.card_sdiff_of_subset hRE] at this
    omega

/-- **`(∀ k, BranchBase k) → RootedTest`.** -/
theorem rootedTest_of_branchBase (hB : ∀ k, BranchBase.{u} k) : RootedTest.{u} := by
  intro W _ _ H hconn hn r
  classical
  exact rooted_of_dstmt0 hconn hn r (fun k hk1 _ =>
    dstmt0_of_branchBase k (fun j _ _ => hB j) k hk1 le_rfl)

/-- **Gallai's conjecture from the branching base case.** -/
theorem gallai_of_branchBase (hB : ∀ k, BranchBase.{u} k) : GallaiConjecture.{u} :=
  gallai_iff_rootedTest.mpr (rootedTest_of_branchBase hB)

/-- Only `k ≥ 3` is open. -/
theorem gallai_of_branchBase_three (hB : ∀ k, 3 ≤ k → BranchBase.{u} k) :
    GallaiConjecture.{u} :=
  gallai_of_branchBase (fun k => by
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | rfl | hk
    · intro W _ _ H _ _ _ _ y hy _ _
      exact ⟨∅, Finset.empty_subset _, rfl, Finset.empty_subset _, by simp,
        by simpa using realisable_evenSet_ni H⟩
    · exact branchBase_one
    · exact branchBase_two
    · exact hB k hk)

end Gallai
