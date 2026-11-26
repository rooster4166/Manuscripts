import GallaiLean.SeparatorOdd

/-!
# Theorem 113, even component with both ports odd in `A`

`|C| = 2s` and every vertex of `C ∪ {x, y}` is odd in `A`. Lovász on `A` gives `s + 1` paths with
one end at every vertex of `C ∪ {x, y}`. Take `W = E + xy` (on `V ∖ C`, of order `n − 2s`).

* If one local path `Q` ends at both ports, substitute `Q` for `xy`.
* Otherwise the port-ended local paths `X` (from `x`) and `Y` (from `y`) are distinct: delete `xy`
  from its exterior row and attach `X` and `Y` to the two sides (`exists_cut_edge`).

In both cases `s` paths are added and the ends outside `C` are preserved.
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {B : SimpleGraph V} [DecidableRel B.Adj]
  {C : Finset V} {x y : V}

/-- **Theorem 113, even component, both ports odd in `A`.** -/
theorem rootedAt_evenComp_oddPorts (hL : LovaszStatement.{u})
    (hMB : MarkedBoundUpTo.{u} (Fintype.card V - 2)) (hB : KConnected 2 B)
    (hC : IsSepComponent B x y C) (hodd : ∀ c ∈ C, Odd (B.degree c)) {r : V} (hr : r ∉ C)
    (hCeven : Even C.card) (hx : Odd ((sideA B C x y).degree x))
    (hy : Odd ((sideA B C x y).degree y)) : RootedAt B r := by
  have hAU := sideA_support_local hC
  obtain ⟨s, hs⟩ := hCeven
  have hs1 : 1 ≤ s := by
    have := Finset.card_pos.mpr hC.nonempty; omega
  have hxC := hC.x_notMem
  have hyC := hC.y_notMem
  have hxy := hC.ne
  have hdegC : ∀ c ∈ C, (sideA B C x y).degree c = B.degree c :=
    fun c hc => sideA_degree_of_mem hc
  have hoddA : ∀ v, v ∉ C → (Odd ((sideA B C x y).degree v) ↔ v = x ∨ v = y) := by
    intro v hv
    by_cases hvx : v = x
    · rw [hvx]; exact ⟨fun _ => Or.inl rfl, fun _ => hx⟩
    by_cases hvy : v = y
    · rw [hvy]; exact ⟨fun _ => Or.inr rfl, fun _ => hy⟩
    · rw [sideA_degree_of_ext hC hv hvx hvy]
      exact ⟨fun h => absurd h (by decide), fun h => by tauto⟩
  -- Lovász on `A`: no even vertex in `C ∪ {x, y}`
  have hevenA : (localSet C x y).filter (fun v => Even ((sideA B C x y).degree v)) = ∅ := by
    ext v
    simp only [Finset.mem_filter, mem_localSet, Finset.notMem_empty, iff_false, not_and]
    rintro (rfl | rfl | hv) he
    · exact (Nat.not_even_iff_odd.mpr hx) he
    · exact (Nat.not_even_iff_odd.mpr hy) he
    · rw [hdegC v hv] at he; exact (Nat.not_even_iff_odd.mpr (hodd v hv)) he
  obtain ⟨DA, hDA1, hDA2⟩ := lovasz_tight hL hAU (by rw [hevenA]; simp)
  rw [hevenA, Finset.card_empty, add_zero, card_localSet hC] at hDA1
  have hDAsize : DA.size = s + 1 := by omega
  have hendsOut : ∀ v, v ∉ C → DA.ends v = if v = x ∨ v = y then 1 else 0 := by
    intro v hv
    rw [hDA2 v]
    by_cases h : v = x ∨ v = y
    · simp [h, (hoddA v hv).mpr h]
    · have h' : ¬ Odd ((sideA B C x y).degree v) := fun h' => h ((hoddA v hv).mp h')
      simp [h, h']
  have hendsC : ∀ c ∈ C, DA.ends c = 1 := by
    intro c hc; rw [hDA2 c, hdegC c hc]; simp [hodd c hc]
  -- the path ending at `x`
  obtain ⟨X, hX, hXx⟩ := DA.exists_path_endsAt (v := x) (by rw [hendsOut x hxC]; simp)
  obtain ⟨X', hX's, hX'e, hX'supp, hX'ends⟩ := X.exists_orientT hXx
  have hXA : ∀ w ∈ X.walk.support, w ∈ localSet C x y := GPath.support_subset hAU X
  have hX'A : ∀ w ∈ X'.walk.support, w ∈ localSet C x y := fun w hw => hXA w ((hX'supp w).mp hw)
  have hXle : ∀ v, X.endsAt v ≤ DA.ends v := fun v => by
    unfold PathDecomp.ends; exact List.le_sum_of_mem (List.mem_map_of_mem hX)
  -- common facts
  have hBval := edgeFinset_sides (B := B) (C := C) (x := x) (y := y)
  have hEconn := sideE_induce_connected hC hB
  have hEpos := sideE_port_pos hC hB
  have hcardU : (Cᶜ : Finset V).card + 2 * s = Fintype.card V := by
    rw [Finset.card_compl]; have := Finset.card_le_univ C; omega
  have hrU : r ∈ (Cᶜ : Finset V) := by simpa using hr
  have hdegB := degree_sides (B := B) (C := C) (x := x) (y := y) r
  have hB2 := hB.le_degree r
  set W := plusEdge (sideE B C x y) x y
  have hnExy : ¬ (sideE B C x y).Adj x y := fun h => h.2.2.2 (Or.inl ⟨rfl, rfl⟩)
  have hWdeg : W.degree r = (sideE B C x y).degree r + if r = x ∨ r = y then 1 else 0 :=
    plusEdge_degree hxy hnExy r
  have hWU : ∀ a b, W.Adj a b → a ∈ (Cᶜ : Finset V) := by
    intro a b h
    rcases h with h | ⟨-, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
    · simpa using sideE_notMem h
    · simpa using hxC
    · simpa using hyC
  have hWc : (W.induce ((Cᶜ : Finset V) : Set V)).Connected :=
    induce_connected_mono le_plusEdge hEconn
  have hWval : W.edgeFinset.val = (sideE B C x y).edgeFinset.val + {s(x, y)} := by
    refine edgeFinset_val_eq_add _ (Multiset.nodup_singleton _) ?_ ?_
    · intro e he; rw [Multiset.mem_singleton] at he; subst he; exact hnExy
    · intro e; rw [plusEdge_edgeSet hxy, Multiset.mem_singleton]
  refine rootedAt_of_lift hMB hB r W _ s hs1 hWU hWc hcardU hrU ?_ ?_ ?_
  · rw [hWdeg, ← hdegB]
    by_cases hrx : r = x
    · rw [hrx]; simp only [true_or, ite_true]; rw [Nat.odd_iff] at hx; omega
    by_cases hry : r = y
    · rw [hry]; simp only [or_true, ite_true]; rw [Nat.odd_iff] at hy; omega
    · simp only [hrx, hry, or_self, ite_false, add_zero, sideA_degree_of_ext hC hr hrx hry,
        zero_add]
  · rw [hWdeg]
    by_cases hrxy : r = x ∨ r = y
    · simp only [hrxy, ite_true]; omega
    · push Not at hrxy
      simp only [hrxy.1, hrxy.2, or_self, ite_false, add_zero]
      rw [sideA_degree_of_ext hC hr hrxy.1 hrxy.2] at hdegB; omega
  intro DW
  set Lw := DW.paths.map GPath.toTop with hLwdef
  have hLw : edgesM Lw = (sideE B C x y).edgeFinset.val + {s(x, y)} := by
    rw [DW.edgesM_toTop, hWval]
  have hxyL : s(x, y) ∈ edgesM Lw := by rw [hLw]; simp
  have hLwU : ∀ R ∈ Lw, ∀ w ∈ R.walk.support, w ∉ C := by
    intro R hR w hw
    obtain ⟨R₀, hR₀, rfl⟩ := List.mem_map.mp hR
    rw [GPath.toTop_support] at hw
    simpa using GPath.support_subset hWU R₀ w hw
  -- local pieces meet exterior rows only at the ports
  have hmeet : ∀ R ∈ Lw, ∀ (Q : TPath V), (∀ w ∈ Q.walk.support, w ∈ localSet C x y) →
      ∀ w ∈ Q.walk.support, w ∈ R.walk.support → w = x ∨ w = y := by
    intro R hR Q hQ w hwQ hwR
    have h1 := hQ w hwQ
    have h2 := hLwU R hR w hwR
    rw [mem_localSet] at h1
    tauto
  by_cases hXy : X'.tgt = y
  · ---------------------------------------------------------------- one path ends at both ports
    obtain ⟨Lw', h1, h2, h3, -⟩ := exists_subst_list Lw hxyL X' hX's hXy
      (fun R hR _ => hmeet R hR X' hX'A)
    obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hX
    set rest := (l₁ ++ l₂).map GPath.toTop with hrest
    have hrestE : edgesM rest + (X.edges : Multiset (Sym2 V)) =
        (sideA B C x y).edgeFinset.val := by
      rw [← DA.edgesM_toTop, hl]
      simp only [hrest, List.map_append, List.map_cons, edgesM_append, edgesM_cons,
        GPath.toTop_edges]
      abel
    have hrestlen : rest.length = s := by
      have : DA.paths.length = s + 1 := hDAsize
      rw [hl] at this; simp [hrest] at this ⊢; omega
    have hXy' : X.endsAt y = 1 := by
      rw [← hX'ends]; unfold GPath.endsAt; rw [hXy]; simp [hX's, hxy]
    have hrestends : endsL rest r = 0 := by
      have h1 := hendsOut r hr
      have h2 : DA.ends r = endsL rest r + X.endsAt r := by
        rw [← DA.endsL_toTop, hl]
        simp only [hrest, List.map_append, List.map_cons, endsL_append, endsL_cons,
          GPath.toTop_endsAt]
        ring
      by_cases hrx : r = x
      · rw [hrx] at h1 h2 ⊢; rw [hXx] at h2; simp at h1; omega
      by_cases hry : r = y
      · rw [hry] at h1 h2 ⊢; rw [hXy'] at h2; simp at h1; omega
      · simp [hrx, hry] at h1; omega
    have hLw' : edgesM Lw' = (sideE B C x y).edgeFinset.val + X.edges := by
      rw [hLw] at h2
      rw [← hX'e]
      have : edgesM Lw' + {s(x, y)} =
          ((sideE B C x y).edgeFinset.val + X'.edges) + {s(x, y)} := by
        rw [h2]; abel
      exact (add_left_inj _).mp this
    obtain ⟨D', hD'1, hD'2⟩ := exists_decomp_of_edgesM (G := B) (Lw' ++ rest) (by
      rw [edgesM_append, hLw', hBval, ← hrestE]; abel)
    refine ⟨D', ?_, ?_⟩
    · rw [hD'1]; simp [h1, hrestlen, Lw, PathDecomp.size]
    · rw [hD'2, endsL_append, hrestends, add_zero, h3, DW.endsL_toTop]
  · ---------------------------------------------------------------- `X ≠ Y`: cut `xy`
    have hXy0 : X.endsAt y = 0 := by
      rw [← hX'ends]; unfold GPath.endsAt; simp [hX's, hxy, hXy]
    obtain ⟨Y, hY, hYy⟩ := DA.exists_path_endsAt (v := y) (by rw [hendsOut y hyC]; simp)
    obtain ⟨Y', hY's, hY'e, hY'supp, hY'ends⟩ := Y.exists_orientT hYy
    have hYA : ∀ w ∈ Y.walk.support, w ∈ localSet C x y := GPath.support_subset hAU Y
    have hY'A : ∀ w ∈ Y'.walk.support, w ∈ localSet C x y :=
      fun w hw => hYA w ((hY'supp w).mp hw)
    have hXY : X ≠ Y := by rintro rfl; rw [hXy0] at hYy; exact absurd hYy (by decide)
    have hYx0 : Y.endsAt x = 0 := by
      by_contra h
      have h1 : Y.endsAt x = 1 := by have := Y.endsAt_le_one x; omega
      have := hendsOut x hxC
      have h2 : DA.ends x ≥ X.endsAt x + Y.endsAt x := by
        obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hX
        have hYl : Y ∈ l₁ ++ l₂ := by
          have := hY; rw [hl] at this
          rcases List.mem_append.mp this with h | h
          · exact List.mem_append_left _ h
          · rcases List.mem_cons.mp h with h | h
            · exact absurd h.symm hXY
            · exact List.mem_append_right _ h
        have : Y.endsAt x ≤ endsL ((l₁ ++ l₂).map GPath.toTop) x := by
          unfold endsL
          exact List.le_sum_of_mem (List.mem_map.mpr ⟨Y.toTop, List.mem_map_of_mem hYl, rfl⟩)
        rw [← DA.endsL_toTop, hl]
        simp only [List.map_append, List.map_cons, endsL_append, endsL_cons,
          GPath.toTop_endsAt] at this ⊢
        omega
      simp at this; omega
    -- the exterior row through `xy`
    obtain ⟨R, hR, hRxy⟩ := mem_edgesM.mp hxyL
    obtain ⟨N₁, N₂, hN1, hN2⟩ := exists_cut_edge R X' Y' hRxy hX's hY's
      (hmeet R hR X' hX'A) (hmeet R hR Y' hY'A)
    obtain ⟨k₁, k₂, hk⟩ := List.append_of_mem hR
    obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hX
    have hYl : Y ∈ l₁ ++ l₂ := by
      have := hY; rw [hl] at this
      rcases List.mem_append.mp this with h | h
      · exact List.mem_append_left _ h
      · rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hXY
        · exact List.mem_append_right _ h
    obtain ⟨m₁, m₂, hm⟩ := List.append_of_mem hYl
    set rest := (m₁ ++ m₂).map GPath.toTop with hrest
    have e1 : edgesM (DA.paths.map GPath.toTop) = edgesM (l₁.map GPath.toTop) + X.edges +
        edgesM (l₂.map GPath.toTop) := by
      rw [hl]; simp only [List.map_append, List.map_cons, edgesM_append, edgesM_cons,
        GPath.toTop_edges]; abel
    have e2 : edgesM (l₁.map GPath.toTop) + edgesM (l₂.map GPath.toTop) =
        edgesM rest + Y.edges := by
      have : edgesM ((l₁ ++ l₂).map GPath.toTop) = edgesM ((m₁ ++ Y :: m₂).map GPath.toTop) := by
        rw [hm]
      simp only [List.map_append, List.map_cons, edgesM_append, edgesM_cons,
        GPath.toTop_edges] at this
      rw [this]; simp only [hrest, List.map_append, edgesM_append]; abel
    have hrestE : edgesM rest + (X.edges : Multiset (Sym2 V)) + Y.edges =
        (sideA B C x y).edgeFinset.val := by
      calc edgesM rest + (X.edges : Multiset (Sym2 V)) + Y.edges
          = (edgesM rest + Y.edges) + X.edges := by abel
        _ = (edgesM (l₁.map GPath.toTop) + edgesM (l₂.map GPath.toTop)) + X.edges := by rw [e2]
        _ = edgesM (DA.paths.map GPath.toTop) := by rw [e1]; abel
        _ = _ := DA.edgesM_toTop
    have hrestlen : rest.length + 2 = s + 1 := by
      have h1 : DA.paths.length = s + 1 := hDAsize
      have h2 : DA.paths.length = l₁.length + l₂.length + 1 := by rw [hl]; simp; omega
      have h3 : l₁.length + l₂.length = m₁.length + m₂.length + 1 := by
        have := congrArg List.length hm; simp at this; omega
      have h4 : rest.length = m₁.length + m₂.length := by simp [hrest]
      omega
    have hrestends : ∀ v, endsL rest v + X.endsAt v + Y.endsAt v = DA.ends v := by
      intro v
      have f1 : DA.ends v = endsL (l₁.map GPath.toTop) v + X.endsAt v +
          endsL (l₂.map GPath.toTop) v := by
        rw [← DA.endsL_toTop, hl]; simp only [List.map_append, List.map_cons, endsL_append,
          endsL_cons, GPath.toTop_endsAt]; ring
      have f2 : endsL (l₁.map GPath.toTop) v + endsL (l₂.map GPath.toTop) v =
          endsL rest v + Y.endsAt v := by
        have : endsL ((l₁ ++ l₂).map GPath.toTop) v = endsL ((m₁ ++ Y :: m₂).map GPath.toTop) v := by
          rw [hm]
        simp only [List.map_append, List.map_cons, endsL_append, endsL_cons,
          GPath.toTop_endsAt] at this
        rw [this]; simp only [hrest, List.map_append, endsL_append]; ring
      omega
    set L := (k₁ ++ N₁ :: N₂ :: k₂) ++ rest
    have hLE : edgesM L = B.edgeFinset.val := by
      have hRw : edgesM Lw = edgesM k₁ + R.edges + edgesM k₂ := by
        rw [hk]; simp only [edgesM_append, edgesM_cons]; abel
      have : edgesM L + {s(x, y)} = edgesM Lw + X'.edges + Y'.edges + edgesM rest := by
        calc edgesM L + {s(x, y)}
            = edgesM k₁ + edgesM k₂ + (N₁.edges + N₂.edges + {s(x, y)}) + edgesM rest := by
              simp only [L, edgesM_append, edgesM_cons]; abel
          _ = edgesM k₁ + edgesM k₂ + (R.edges + X'.edges + Y'.edges) + edgesM rest := by
              rw [hN1]
          _ = _ := by rw [hRw]; abel
      rw [hLw, hX'e, hY'e] at this
      have h' : edgesM L + {s(x, y)} =
          ((sideE B C x y).edgeFinset.val + (sideA B C x y).edgeFinset.val) + {s(x, y)} := by
        rw [this, ← hrestE]; abel
      rw [(add_left_inj _).mp h', hBval]; abel
    obtain ⟨D', hD'1, hD'2⟩ := exists_decomp_of_edgesM (G := B) L hLE
    refine ⟨D', ?_, ?_⟩
    · rw [hD'1]
      have hlen : Lw.length = k₁.length + 1 + k₂.length := by rw [hk]; simp; omega
      have : Lw.length = DW.size := by simp [Lw, PathDecomp.size]
      simp only [L, List.length_append, List.length_cons]
      omega
    · rw [hD'2, show DW.ends r = endsL Lw r from (DW.endsL_toTop r).symm]
      have hRw : endsL Lw r = endsL k₁ r + R.endsAt r + endsL k₂ r := by
        rw [hk]; simp only [endsL_append, endsL_cons]; ring
      have h3 := hrestends r
      have hcomb : N₁.endsAt r + N₂.endsAt r + DA.ends r =
          R.endsAt r + X.endsAt r + Y.endsAt r := by
        have h2 := hN2 r
        rw [hX'ends r, hY'ends r] at h2
        rw [hendsOut r hr]
        by_cases hrx : r = x
        · rw [hrx] at h2 ⊢; simp only [hxy, Ne.symm hxy, true_or, ite_true, ite_false,
            add_zero] at h2 ⊢; omega
        · by_cases hry : r = y
          · rw [hry] at h2 ⊢; simp only [hxy, Ne.symm hxy, or_true, ite_true, ite_false] at h2 ⊢
            omega
          · simp only [hrx, hry, Ne.symm hrx, Ne.symm hry, or_self, ite_false,
              add_zero] at h2 ⊢; omega
      simp only [L, endsL_append, endsL_cons]
      omega

/-! ### Swapping the ports -/

omit [Fintype V] [DecidableEq V] [DecidableRel B.Adj] in
theorem sideA_swap : sideA B C y x = sideA B C x y := by
  ext a b; simp only [sideA_adj]; tauto

omit [Fintype V] [DecidableEq V] [DecidableRel B.Adj] in
theorem IsSepComponent.swap (hC : IsSepComponent B x y C) : IsSepComponent B y x C where
  ne := hC.ne.symm
  x_notMem := hC.y_notMem
  y_notMem := hC.x_notMem
  nonempty := hC.nonempty
  conn := hC.conn
  closed := fun a ha b hab => by rcases hC.closed a ha b hab with h | h | h <;> tauto
  sep := by obtain ⟨w, h1, h2, h3⟩ := hC.sep; exact ⟨w, h1, h3, h2⟩

theorem degree_sideA_swap (v : V) : (sideA B C y x).degree v = (sideA B C x y).degree v := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp only [mem_neighborFinset, sideA_adj]
  tauto

end Gallai
