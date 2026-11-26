import GallaiLean.SeparatorSetup

/-!
# Theorem 113, odd component

`|C| = 2s + 1`, every vertex of `C` odd in `B`, so exactly one port is odd in `A`; here it is `x`
(the other orientation follows by symmetry, see `Separator.lean`). Lovász on `A` (on `C ∪ {x, y}`,
only `y` even) gives `s + 1` paths with one end at each odd vertex and none at `y`. Let `P` be the
path ending at `x`, read from `x` to its other end `c ∈ C`.

* If `P` omits `y`: `W = E + xc` (with `c` as a leaf), substitute `P` for `xc`.
* If `P` visits `y`: split `P = T · U` at `y`; `W = E + xy + yc`, substitute `T` for `xy` and `U`
  for `yc`.

In both cases `|W| = n − 2s`, the other `s` local paths are restored, and the ends outside `C` are
preserved; `rootedAt_of_lift` concludes.
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u}

/-- The vertex set `C ∪ {x, y}` of the local side. -/
def localSet [DecidableEq V] (C : Finset V) (x y : V) : Finset V := insert x (insert y C)

theorem mem_localSet [DecidableEq V] {C : Finset V} {x y v : V} :
    v ∈ localSet C x y ↔ v = x ∨ v = y ∨ v ∈ C := by
  simp [localSet]

/-- A decomposition with an end at `v` has a path with exactly one end at `v`. -/
theorem PathDecomp.exists_path_endsAt [DecidableEq V] {G : SimpleGraph V} (D : PathDecomp G)
    {v : V} (h : D.ends v ≠ 0) : ∃ P ∈ D.paths, P.endsAt v = 1 := by
  by_contra hc
  push Not at hc
  apply h
  unfold PathDecomp.ends
  refine List.sum_eq_zero_iff_forall_eq_nat.mpr (fun n hn => ?_)
  obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hn
  have := P.endsAt_le_one v
  have := hc P hP
  omega

/-- Orient a path so that it starts at one of its ends. -/
theorem GPath.exists_orientT [DecidableEq V] {G : SimpleGraph V} (P : GPath G) {v : V}
    (h : P.endsAt v = 1) : ∃ P' : TPath V, P'.src = v ∧
      (P'.edges : Multiset (Sym2 V)) = P.edges ∧
      (∀ w, w ∈ P'.walk.support ↔ w ∈ P.walk.support) ∧ ∀ w, P'.endsAt w = P.endsAt w := by
  by_cases hs : P.src = v
  · exact ⟨P.toTop, hs, by simp, fun w => by rw [GPath.toTop_support], fun w => rfl⟩
  · have ht : P.tgt = v := by
      unfold endsAt at h; by_contra ht; simp [hs, ht] at h
    refine ⟨P.toTop.reverse, ht, ?_,
      fun w => by rw [GPath.reverse_support, List.mem_reverse, GPath.toTop_support], fun w => ?_⟩
    · simp [Multiset.coe_reverse]
    · rw [GPath.reverse_endsAt']; rfl

section odd

variable [Fintype V] [DecidableEq V] {B : SimpleGraph V} [DecidableRel B.Adj] {C : Finset V}
  {x y : V}

omit [Fintype V] [DecidableRel B.Adj] in
theorem sideA_support_local (hC : IsSepComponent B x y C) :
    ∀ a b, (sideA B C x y).Adj a b → a ∈ localSet C x y := by
  intro a b h
  rw [mem_localSet]
  rcases sideA_support hC h with h | h | h <;> tauto

omit [Fintype V] [DecidableRel B.Adj] in
theorem card_localSet (hC : IsSepComponent B x y C) : (localSet C x y).card = C.card + 2 := by
  rw [localSet, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem hC.y_notMem]
  simp only [Finset.mem_insert, not_or]
  exact ⟨hC.ne, hC.x_notMem⟩

/-- A component of `B − {x, y}` all of whose vertices are odd has at least two vertices. -/
theorem two_le_card_of_odd (hB : KConnected 2 B) (hC : IsSepComponent B x y C)
    (hodd : ∀ c ∈ C, Odd (B.degree c)) : 2 ≤ C.card := by
  by_contra hlt
  push Not at hlt
  obtain ⟨c, hc⟩ := hC.nonempty
  have hC1 : C = {c} := by
    have := Finset.card_pos.mpr ⟨c, hc⟩
    obtain ⟨d, hd⟩ := Finset.card_eq_one.mp (by omega : C.card = 1)
    rw [hd] at hc ⊢; rw [Finset.mem_singleton.mp hc]
  have hsub : B.neighborFinset c ⊆ {x, y} := by
    intro w hw
    rw [mem_neighborFinset] at hw
    rcases hC.closed c hc w hw with h | h | h
    · rw [hC1, Finset.mem_singleton] at h; subst h; exact absurd hw (B.loopless.irrefl _)
    · simp [h]
    · simp [h]
  have h2 := hB.le_degree c
  have hle := Finset.card_le_card hsub
  rw [card_neighborFinset_eq_degree] at hle
  have : B.degree c = 2 := by
    have := Finset.card_le_two (a := x) (b := y); omega
  have := hodd c hc
  rw [Nat.odd_iff] at this
  omega

/-- **Theorem 113, odd component, with `x` the odd port of `A`.** -/
theorem rootedAt_oddComp (hL : LovaszStatement.{u})
    (hMB : MarkedBoundUpTo.{u} (Fintype.card V - 2)) (hB : KConnected 2 B)
    (hC : IsSepComponent B x y C) (hodd : ∀ c ∈ C, Odd (B.degree c)) {r : V} (hr : r ∉ C)
    (hCodd : Odd C.card) (hx : Odd ((sideA B C x y).degree x))
    (hy : Even ((sideA B C x y).degree y)) : RootedAt B r := by
  have hAU := sideA_support_local hC
  obtain ⟨s, hs⟩ := hCodd
  have hs1 : 1 ≤ s := by have := two_le_card_of_odd hB hC hodd; omega
  have hxC := hC.x_notMem
  have hyC := hC.y_notMem
  have hxy := hC.ne
  -- parity of `A`
  have hdegC : ∀ c ∈ C, (sideA B C x y).degree c = B.degree c := fun c hc => sideA_degree_of_mem hc
  have hoddA : ∀ v, v ∉ C → (Odd ((sideA B C x y).degree v) ↔ v = x) := by
    intro v hv
    by_cases hvx : v = x
    · subst hvx; exact ⟨fun _ => rfl, fun _ => hx⟩
    by_cases hvy : v = y
    · subst hvy
      exact ⟨fun h => absurd hy (Nat.not_even_iff_odd.mpr h), fun h => absurd h hvx⟩
    · rw [sideA_degree_of_ext hC hv hvx hvy]
      exact ⟨fun h => absurd h (by decide), fun h => absurd h hvx⟩
  -- Lovász on `A`
  have hevenA : (localSet C x y).filter (fun v => Even ((sideA B C x y).degree v)) = {y} := by
    ext v
    simp only [Finset.mem_filter, mem_localSet, Finset.mem_singleton]
    constructor
    · rintro ⟨hv, he⟩
      rcases hv with rfl | rfl | hv
      · exact absurd hx (Nat.not_odd_iff_even.mpr he)
      · rfl
      · rw [hdegC v hv] at he; exact absurd (hodd v hv) (Nat.not_odd_iff_even.mpr he)
    · rintro rfl; exact ⟨Or.inr (Or.inl rfl), hy⟩
  obtain ⟨DA, hDA1, hDA2⟩ := lovasz_tight hL hAU (by rw [hevenA]; simp)
  rw [hevenA, Finset.card_singleton, card_localSet hC] at hDA1
  have hDAsize : DA.size = s + 1 := by omega
  have hendsOut : ∀ v, v ∉ C → DA.ends v = if v = x then 1 else 0 := by
    intro v hv
    rw [hDA2 v]
    by_cases hvx : v = x
    · rw [hvx]; simp [hx]
    · have h' : ¬ Odd ((sideA B C x y).degree v) := fun h => hvx ((hoddA v hv).mp h)
      simp [hvx, h']
  -- the path ending at `x`
  obtain ⟨P, hP, hPx⟩ := DA.exists_path_endsAt (v := x) (by rw [hendsOut x hxC]; simp)
  obtain ⟨P', hP's, hP'e, hP'supp, hP'ends⟩ := P.exists_orientT hPx
  set c := P'.tgt with hcdef
  have hcx : c ≠ x := fun h => P'.src_ne_tgt (hP's.trans h.symm)
  have hcC : c ∈ C := by
    by_contra hc
    have h1 : 1 ≤ P'.endsAt c := by
      unfold GPath.endsAt; rw [hcdef]; simp only [ite_true]; omega
    rw [hP'ends] at h1
    have h2 : P.endsAt c ≤ DA.ends c := by
      unfold PathDecomp.ends; exact List.le_sum_of_mem (List.mem_map_of_mem hP)
    rw [hendsOut c hc] at h2
    simp [hcx] at h2
    omega
  have hPA : ∀ w ∈ P.walk.support, w ∈ localSet C x y := GPath.support_subset hAU P
  -- the other local paths
  obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hP
  set rest := (l₁ ++ l₂).map GPath.toTop with hrest
  have hrestE : edgesM rest + (P.edges : Multiset (Sym2 V)) = (sideA B C x y).edgeFinset.val := by
    rw [← DA.edgesM_toTop, hl]
    simp only [hrest, List.map_append, List.map_cons, edgesM_append, edgesM_cons,
      GPath.toTop_edges]
    abel
  have hrestlen : rest.length = s := by
    have : DA.paths.length = s + 1 := hDAsize
    rw [hl] at this; simp [hrest] at this ⊢; omega
  have hrestends : ∀ v, v ∉ C → endsL rest v = 0 := by
    intro v hv
    have h1 := hendsOut v hv
    have h2 : DA.ends v = endsL rest v + P.endsAt v := by
      rw [← DA.endsL_toTop, hl]
      simp only [hrest, List.map_append, List.map_cons, endsL_append, endsL_cons,
        GPath.toTop_endsAt]
      ring
    by_cases hvx : v = x
    · subst hvx; rw [hPx] at h2; simp at h1; omega
    · simp [hvx] at h1; omega
  -- finishing: any exterior list carrying `E` and `P` gives a decomposition of `B`
  have hBval := edgeFinset_sides (B := B) (C := C) (x := x) (y := y)
  have finish : ∀ (k : ℕ) (Lw : List (TPath V)), Lw.length = k →
      edgesM Lw = (sideE B C x y).edgeFinset.val + P.edges →
      ∃ D' : PathDecomp B, D'.size ≤ k + s ∧ D'.ends r = endsL Lw r := by
    intro k Lw hk hLw
    obtain ⟨D', h1, h2⟩ := exists_decomp_of_edgesM (G := B) (Lw ++ rest) (by
      rw [edgesM_append, hLw, hBval, ← hrestE]; abel)
    refine ⟨D', by rw [h1]; simp [hk, hrestlen], ?_⟩
    rw [h2, endsL_append, hrestends r hr, add_zero]
  -- common facts for the exterior graphs
  have hEconn := sideE_induce_connected hC hB
  have hEpos := sideE_port_pos hC hB
  have hcardU : (insert c (Cᶜ : Finset V)).card + 2 * s = Fintype.card V := by
    rw [Finset.card_insert_of_notMem (by simpa using hcC), Finset.card_compl]
    have := Finset.card_le_univ C
    omega
  have hrU : r ∈ insert c (Cᶜ : Finset V) := Finset.mem_insert_of_mem (by simpa using hr)
  have hrc : r ≠ c := fun h => hr (h ▸ hcC)
  have hdegB := degree_sides (B := B) (C := C) (x := x) (y := y) r
  have hB2 := hB.le_degree r
  have hnEc : ∀ a, ¬ (sideE B C x y).Adj a c := fun a h => sideE_notMem h.symm hcC
  by_cases hyP : y ∉ P.walk.support
  · ------------------------------------------------------------------
    -- `P` omits `y`: `W = E + xc`
    set W := plusEdge (sideE B C x y) x c
    have hWdeg : W.degree r = (sideE B C x y).degree r + if r = x ∨ r = c then 1 else 0 :=
      plusEdge_degree hcx.symm (hnEc x) r
    have hWU : ∀ a b, W.Adj a b → a ∈ insert c (Cᶜ : Finset V) := by
      intro a b h
      rcases h with h | ⟨-, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
      · exact Finset.mem_insert_of_mem (by simpa using sideE_notMem h)
      · exact Finset.mem_insert_of_mem (by simpa using hxC)
      · exact Finset.mem_insert_self _ _
    have hWc : (W.induce ((insert c (Cᶜ : Finset V) : Finset V) : Set V)).Connected :=
      induce_connected_insert (induce_connected_mono le_plusEdge hEconn)
        (by simpa using hxC) (Or.inr ⟨hcx.symm, Or.inl ⟨rfl, rfl⟩⟩)
    refine rootedAt_of_lift hMB hB r W _ s hs1 hWU hWc hcardU hrU ?_ ?_ ?_
    · rw [hWdeg, ← hdegB]
      by_cases hrx : r = x
      · rw [hrx]; simp only [true_or, ite_true]; rw [Nat.odd_iff] at hx; omega
      by_cases hry : r = y
      · rw [hry]; rw [hry] at hrx hrc; simp only [hrx, hrc, or_self, ite_false, add_zero]
        rw [Nat.even_iff] at hy; omega
      · simp only [hrx, hrc, or_self, ite_false, add_zero, sideA_degree_of_ext hC hr hrx hry,
          zero_add]
    · rw [hWdeg]
      by_cases hrx : r = x
      · simp only [hrx, true_or, ite_true]; omega
      by_cases hry : r = y
      · rw [hry]; rw [hry] at hrx hrc; simp only [hrx, hrc, or_self, ite_false, add_zero]
        exact hEpos.2
      · simp only [hrx, hrc, or_self, ite_false, add_zero]
        rw [sideA_degree_of_ext hC hr hrx hry] at hdegB; omega
    · intro DW
      set Lw := DW.paths.map GPath.toTop
      have hWval : W.edgeFinset.val = (sideE B C x y).edgeFinset.val + {s(x, c)} := by
        refine edgeFinset_val_eq_add _ (Multiset.nodup_singleton _) ?_ ?_
        · intro e he; rw [Multiset.mem_singleton] at he; subst he
          exact hnEc x
        · intro e; rw [plusEdge_edgeSet hcx.symm, Multiset.mem_singleton]
      have hLw : edgesM Lw = (sideE B C x y).edgeFinset.val + {s(x, c)} := by
        rw [DW.edgesM_toTop, hWval]
      have hxcL : s(x, c) ∈ edgesM Lw := by
        rw [hLw]; exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self _))
      obtain ⟨Lw', h1, h2, h3, -⟩ := exists_subst_list Lw hxcL P' hP's rfl (by
        intro R hR _ w hwT hwR
        obtain ⟨R₀, hR₀, rfl⟩ := List.mem_map.mp hR
        have hwU := GPath.support_subset hWU R₀ w (by rw [GPath.toTop_support] at hwR; exact hwR)
        have hwA := hPA w ((hP'supp w).mp hwT)
        have hwy : w ≠ y := fun h => hyP (h ▸ (hP'supp w).mp hwT)
        rw [Finset.mem_insert, Finset.mem_compl] at hwU
        rw [mem_localSet] at hwA
        tauto)
      have hLw' : edgesM Lw' = (sideE B C x y).edgeFinset.val + P.edges := by
        rw [hLw] at h2
        rw [← hP'e]
        have : edgesM Lw' + {s(x, c)} =
            ((sideE B C x y).edgeFinset.val + P'.edges) + {s(x, c)} := by
          rw [h2]; abel
        exact (add_left_inj _).mp this
      obtain ⟨D', hD'1, hD'2⟩ := finish _ Lw' h1 hLw'
      refine ⟨D', by simpa [Lw, PathDecomp.size] using hD'1, ?_⟩
      rw [hD'2, h3, DW.endsL_toTop]
  · ------------------------------------------------------------------
    -- `P` visits `y`: split it there, `W = E + xy + yc`
    push Not at hyP
    have hyP' : y ∈ P'.walk.support := (hP'supp y).mpr hyP
    obtain ⟨q₁, q₂, hq⟩ := P'.exists_split_support hyP'
    have hPn := P'.support_nodup
    rw [hq] at hPn
    have hq₁n := support_nodup_of_append_left hPn
    have hq₂n := support_nodup_of_append_right hPn
    have hq₁₂ := ((nodup_support_append q₁ q₂).mp hPn).2.2
    have hyc : y ≠ c := fun h => hyC (h ▸ hcC)
    have hq₁pos : 0 < q₁.length := by
      by_contra h0
      exact hxy (hP's.symm.trans (Walk.eq_of_length_eq_zero (p := q₁) (by omega)))
    have hq₂pos : 0 < q₂.length := by
      by_contra h0
      exact hyc (Walk.eq_of_length_eq_zero (p := q₂) (by omega))
    let T : TPath V := ⟨P'.src, y, q₁, (Walk.isPath_def _).mpr hq₁n, hq₁pos⟩
    let U' : TPath V := ⟨y, P'.tgt, q₂, (Walk.isPath_def _).mpr hq₂n, hq₂pos⟩
    have hTU : (P'.edges : Multiset (Sym2 V)) = T.edges + U'.edges := by
      show (P'.walk.edges : Multiset (Sym2 V)) = (q₁.edges : Multiset (Sym2 V)) + q₂.edges
      rw [hq, Walk.edges_append, Multiset.coe_add]
    have hcT : c ∉ T.walk.support := fun h =>
      hyc (hq₁₂ c h q₂.end_mem_support).symm
    have hxU : x ∉ U'.walk.support := fun h =>
      hxy (hq₁₂ x (by rw [← hP's]; exact q₁.start_mem_support) h)
    have hTP : ∀ w ∈ T.walk.support, w ∈ P.walk.support := fun w hw =>
      (hP'supp w).mp (by rw [hq]; exact (Walk.mem_support_append_iff q₁ q₂).mpr (Or.inl hw))
    have hUP : ∀ w ∈ U'.walk.support, w ∈ P.walk.support := fun w hw =>
      (hP'supp w).mp (by rw [hq]; exact (Walk.mem_support_append_iff q₁ q₂).mpr (Or.inr hw))
    set W₁ := plusEdge (sideE B C x y) x y
    set W := plusEdge W₁ y c
    have hnExy : ¬ (sideE B C x y).Adj x y := fun h => h.2.2.2 (Or.inl ⟨rfl, rfl⟩)
    have hnW₁ : ¬ W₁.Adj y c := by
      rintro (h | ⟨-, ⟨-, h⟩ | ⟨-, h⟩⟩)
      · exact hnEc y h
      · exact hyc h.symm
      · exact hcx h
    have hW₁deg : ∀ v, W₁.degree v = (sideE B C x y).degree v + if v = x ∨ v = y then 1 else 0 :=
      plusEdge_degree hxy hnExy
    have hWdeg : W.degree r = W₁.degree r + if r = y ∨ r = c then 1 else 0 :=
      plusEdge_degree hyc hnW₁ r
    have hWU : ∀ a b, W.Adj a b → a ∈ insert c (Cᶜ : Finset V) := by
      intro a b h
      rcases h with (h | ⟨-, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩) | ⟨-, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
      · exact Finset.mem_insert_of_mem (by simpa using sideE_notMem h)
      · exact Finset.mem_insert_of_mem (by simpa using hxC)
      · exact Finset.mem_insert_of_mem (by simpa using hyC)
      · exact Finset.mem_insert_of_mem (by simpa using hyC)
      · exact Finset.mem_insert_self _ _
    have hWc : (W.induce ((insert c (Cᶜ : Finset V) : Finset V) : Set V)).Connected :=
      induce_connected_insert
        (induce_connected_mono (le_plusEdge.trans le_plusEdge) hEconn)
        (by simpa using hyC) (Or.inr ⟨hyc, Or.inl ⟨rfl, rfl⟩⟩)
    refine rootedAt_of_lift hMB hB r W _ s hs1 hWU hWc hcardU hrU ?_ ?_ ?_
    · rw [hWdeg, hW₁deg, ← hdegB]
      by_cases hrx : r = x
      · rw [hrx]; rw [hrx] at hrc
        simp only [true_or, ite_true, hxy, hrc, or_self, ite_false, add_zero]
        rw [Nat.odd_iff] at hx; omega
      by_cases hry : r = y
      · rw [hry]; rw [hry] at hrx hrc
        simp only [hrx, true_or, or_true, ite_true]
        rw [Nat.even_iff] at hy; omega
      · simp only [hrx, hry, hrc, or_self, ite_false, add_zero,
          sideA_degree_of_ext hC hr hrx hry, zero_add]
    · rw [hWdeg, hW₁deg]
      by_cases hrx : r = x
      · simp only [hrx, true_or, ite_true]; omega
      by_cases hry : r = y
      · simp only [hry, or_true, true_or, ite_true]; omega
      · simp only [hrx, hry, hrc, or_self, ite_false, add_zero]
        rw [sideA_degree_of_ext hC hr hrx hry] at hdegB; omega
    · intro DW
      set Lw := DW.paths.map GPath.toTop
      have hW₁val : W₁.edgeFinset.val = (sideE B C x y).edgeFinset.val + {s(x, y)} := by
        refine edgeFinset_val_eq_add _ (Multiset.nodup_singleton _) ?_ ?_
        · intro e he; rw [Multiset.mem_singleton] at he; subst he; exact hnExy
        · intro e; rw [plusEdge_edgeSet hxy, Multiset.mem_singleton]
      have hWval : W.edgeFinset.val = W₁.edgeFinset.val + {s(y, c)} := by
        refine edgeFinset_val_eq_add _ (Multiset.nodup_singleton _) ?_ ?_
        · intro e he; rw [Multiset.mem_singleton] at he; subst he; exact hnW₁
        · intro e; rw [plusEdge_edgeSet hyc, Multiset.mem_singleton]
      have hLw : edgesM Lw = (sideE B C x y).edgeFinset.val + {s(x, y)} + {s(y, c)} := by
        rw [DW.edgesM_toTop, hWval, hW₁val]
      have hxyL : s(x, y) ∈ edgesM Lw := by
        rw [hLw]; simp
      -- first substitution: `T` for `xy`
      obtain ⟨Lw₁, h11, h12, h13, h14⟩ := exists_subst_list Lw hxyL T hP's rfl (by
        intro R hR _ w hwT hwR
        obtain ⟨R₀, hR₀, rfl⟩ := List.mem_map.mp hR
        have hwU := GPath.support_subset hWU R₀ w (by rw [GPath.toTop_support] at hwR; exact hwR)
        have hwA := hPA w (hTP w hwT)
        have hwc : w ≠ c := fun h => hcT (h ▸ hwT)
        rw [Finset.mem_insert, Finset.mem_compl] at hwU
        rw [mem_localSet] at hwA
        tauto)
      have hycL : s(y, c) ∈ edgesM Lw₁ := by
        have : s(y, c) ∈ edgesM Lw₁ + {s(x, y)} := by
          rw [h12, hLw]; simp
        rcases Multiset.mem_add.mp this with h | h
        · exact h
        · rw [Multiset.mem_singleton, Sym2.eq_iff] at h
          rcases h with ⟨h, -⟩ | ⟨-, h⟩
          · exact absurd h hxy.symm
          · exact absurd h hcx
      -- second substitution: `U'` for `yc`
      obtain ⟨Lw₂, h21, h22, h23, -⟩ := exists_subst_list Lw₁ hycL U' rfl rfl (by
        intro R hR _ w hwU' hwR
        rcases h14 R hR w hwR with ⟨R₀', hR₀', hwR₀'⟩ | hwT
        · obtain ⟨R₀, hR₀, rfl⟩ := List.mem_map.mp hR₀'
          have hwU := GPath.support_subset hWU R₀ w (by rw [GPath.toTop_support] at hwR₀'; exact hwR₀')
          have hwA := hPA w (hUP w hwU')
          have hwx : w ≠ x := fun h => hxU (h ▸ hwU')
          rw [Finset.mem_insert, Finset.mem_compl] at hwU
          rw [mem_localSet] at hwA
          tauto
        · exact Or.inl (hq₁₂ w hwT hwU'))
      have hLw₂ : edgesM Lw₂ = (sideE B C x y).edgeFinset.val + P.edges := by
        rw [← hP'e, hTU]
        have : edgesM Lw₂ + {s(y, c)} + {s(x, y)} =
            ((sideE B C x y).edgeFinset.val + (T.edges + U'.edges)) + {s(y, c)} + {s(x, y)} := by
          rw [h22, add_right_comm, h12, hLw]; abel
        exact (add_left_inj _).mp ((add_left_inj _).mp this)
      obtain ⟨D', hD'1, hD'2⟩ := finish _ Lw₂ (h21.trans h11) hLw₂
      refine ⟨D', by simpa [Lw, PathDecomp.size] using hD'1, ?_⟩
      rw [hD'2, h23, h13, DW.endsL_toTop]

end odd

end Gallai
