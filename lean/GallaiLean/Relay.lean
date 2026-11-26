import GallaiLean.EvenInsert

/-!
# Relays, carries and hub transfers (d6-frontier manuscript, Lemma 2.3 and §3)

Everything here is stated for the edge-set form `Ach E b` of `Insertion.lean`: the graph
`fromEdgeSet E` has a path decomposition with exactly `b v` ends at every `v`. Every step is one
application of Fan's lemma (`Ach.transfer`, `Ach.grouped`), so the number of paths never changes.

**Lemma 2.3 (relay).** Let `v₀ v₁ ⋯ v_m` (`m ≥ 1`) be a duplicate-free list whose consecutive
edges are not in `E`.

* `Ach.forwardRelay` (part (a), *forward relay*): the single transfers `v₀ → v₁ → ⋯ → v_m` succeed
  if `b(v₀) > bl_E(v₁)`, the internal vertices `v₁, …, v_{m-1}` have at least one end, and every
  later receiver `v_i` (`i ≥ 2`) has at most one blank neighbour. The blank neighbours are counted
  for the end vector `mv b v₀ v₁` after the first transfer. For `i ≥ 2` this is exactly the
  partition current when `v_i` receives: the neighbours of `v_i` are those in `E`, and the only
  vertices whose blankness changed are `v₀` (possibly) and `v₁`, which has an end again. Net
  effect: one end moves from `v₀` to `v_m`.
* `Ach.carry` (part (b), *carry*): the transfers `v₁ → v₀, v₂ → v₁, …, v_m → v_{m-1}` succeed if
  `v₁, …, v_m` have at least one end and none of the receivers `v₀, …, v_{m-1}` is adjacent in
  `E` to a blank vertex other than `v₀`. This is weaker than the manuscript's hypothesis (no
  receiver is adjacent in `H_m` to a blank vertex of `D`). Net effect: one end moves from `v_m` to
  `v₀`. With `b(v_m) = 1` the vertex `v_m` is *parked* (blank).

**Hub transfers** (the counting of Remark 3.4), for a hub `h`:

* `Ach.receiveMany`: `m` grouped receipts at `h` from a set `S` of non-neighbours with one end
  each. The `j`-th receipt has supply `|S| − j` against at most `bl(h) + j` blank neighbours. The
  donor set `Z` (`|Z| = m`) is existential: Fan does not let us choose it.
* `Ach.giveAll`: single donations from `h` to every vertex of a set `R`, in any order. It suffices
  that `c + |R| ≤ b(h)`, where `c` bounds, for every receiver, its blank neighbours *outside* `R`.
  Blank receivers (paybacks to parked vertices) and receivers with ends (donations) are both
  covered.
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u} [DecidableEq V]

/-- First `c → z`, then `x → c`: the net effect is `x → z`. -/
theorem mv_mv_back {W : Type*} [DecidableEq W] (b : W → ℕ) {x c z : W} (hxc : x ≠ c)
    (hxz : x ≠ z) (hcz : c ≠ z) (hc : 1 ≤ b c) : mv (mv b c z) x c = mv b x z := by
  funext w
  unfold mv
  by_cases hwc : w = c
  · subst hwc
    simp only [ite_true, hcz, ite_false, Ne.symm hxc]
    omega
  · by_cases hwz : w = z
    · subst hwz
      simp [hwc, Ne.symm hxz]
    · by_cases hwx : w = x
      · subst hwx
        simp [hwc, hwz]
      · simp [hwc, hwz, hwx]

section relay

variable [Fintype V]

omit [DecidableEq V] in
theorem blankNbrs_eq_zero {E : Set (Sym2 V)} {b : V → ℕ} {u : V}
    (h : ∀ w, s(u, w) ∈ E → w ≠ u → b w ≠ 0) : blankNbrs E b u = 0 := by
  have := blankNbrs_le_of_subset (S := (∅ : Set V)) (E := E) (b := b) (u := u)
    (fun w h1 h2 h3 => absurd h3 (h w h1 h2))
  simpa using this

/-- **Carry** (Lemma 2.3(b)). Along the list `x :: l = v₀ v₁ ⋯ v_m`, the single transfers
`v₁ → v₀, v₂ → v₁, …, v_m → v_{m-1}` succeed: one end moves from `v_m` to `v₀`. -/
theorem Ach.carry : ∀ (l : List V) (x : V) (E : Set (Sym2 V)) (b : V → ℕ), Ach E b → l ≠ [] →
    (x :: l).Nodup → (∀ e ∈ lEdges x l, e ∉ E) → (∀ c ∈ l, 1 ≤ b c) →
    (∀ c ∈ x :: l.dropLast, ∀ w, s(c, w) ∈ E → w ≠ c → w ≠ x → b w ≠ 0) →
    Ach (E ∪ {e | e ∈ lEdges x l}) (mv b (lastOf x l) x)
  | [], _, _, _, _, hl, _, _, _, _ => absurd rfl hl
  | [y], x, E, b, h, _, hnd, hnew, hpos, hbl => by
    have hxy : x ≠ y := by simpa using hnd
    have h1 := h.transfer (Ne.symm hxy)
      (fun h' => hnew s(x, y) (by simp) (by rwa [Sym2.eq_swap]))
      (by
        rw [blankNbrs_eq_zero (fun w h1 h2 => hbl x List.mem_cons_self w h1 h2 h2)]
        have := hpos y (by simp)
        omega)
    refine h1.congr ?_ (fun _ => rfl)
    ext e
    simp only [Set.mem_insert_iff, Set.mem_union, lEdges_cons, lEdges_nil, List.mem_singleton,
      Set.mem_ofPred_eq]
    rw [Sym2.eq_swap (a := y)]
    tauto
  | y :: z :: l, x, E, b, h, _, hnd, hnew, hpos, hbl => by
    have hx : x ∉ y :: z :: l := (List.nodup_cons.mp hnd).1
    have hnd' : (y :: z :: l).Nodup := (List.nodup_cons.mp hnd).2
    have hy : y ∉ z :: l := (List.nodup_cons.mp hnd').1
    have hxy : x ≠ y := fun h => hx (h ▸ List.mem_cons_self)
    have hdl : (y :: z :: l).dropLast = y :: (z :: l).dropLast := rfl
    have h1 := h.transfer (Ne.symm hxy)
      (fun h' => hnew s(x, y) (by simp) (by rwa [Sym2.eq_swap]))
      (by
        rw [blankNbrs_eq_zero (fun w h1 h2 => hbl x List.mem_cons_self w h1 h2 h2)]
        have := hpos y (by simp)
        omega)
    have hlast : lastOf y (z :: l) ∈ z :: l := by
      rw [lastOf_cons]; exact lastOf_mem z l
    have h2 := Ach.carry (z :: l) y (insert s(y, x) E) (mv b y x) h1 (List.cons_ne_nil _ _)
      hnd'
      (by
        intro e he hmem
        rw [Set.mem_insert_iff] at hmem
        rcases hmem with rfl | hmem
        · exact hx (mem_of_mem_lEdges he (Sym2.mem_mk_right y x))
        · exact hnew e (by rw [lEdges_cons]; exact List.mem_cons_of_mem _ he) hmem)
      (by
        intro c hc
        have h1 : c ≠ x := fun h => hx (h ▸ List.mem_cons_of_mem _ hc)
        have h2 : c ≠ y := fun h => hy (h ▸ hc)
        rw [mv_apply_other _ h2 h1]
        exact hpos c (List.mem_cons_of_mem _ hc))
      (by
        intro c hc w hw hwc hwy
        by_cases hwx : w = x
        · subst hwx
          rw [mv_apply_recv]
          omega
        · rw [mv_apply_other _ hwy hwx]
          rw [Set.mem_insert_iff] at hw
          rcases hw with hw | hw
          · rcases Sym2.eq_iff.mp hw with ⟨-, h2⟩ | ⟨-, h2⟩
            · exact absurd h2 hwx
            · exact absurd h2 hwy
          · exact hbl c (by rw [hdl]; exact List.mem_cons_of_mem _ hc) w hw hwc hwx)
    refine h2.congr ?_ (fun w => ?_)
    · ext e
      simp only [Set.mem_insert_iff, Set.mem_union, lEdges_cons, List.mem_cons,
        Set.mem_ofPred_eq]
      rw [Sym2.eq_swap (a := y)]
      tauto
    · rw [lastOf_cons x y]
      have h3 : lastOf y (z :: l) ≠ y := fun h => hy (h ▸ hlast)
      have h4 : lastOf y (z :: l) ≠ x := fun h => hx (h ▸ List.mem_cons_of_mem _ hlast)
      exact congrFun (mv_mv_back b h3 h4 (Ne.symm hxy) (hpos y (by simp))) w

/-- **Forward relay** (Lemma 2.3(a)). Along the list `x :: y :: l = v₀ v₁ ⋯ v_m`, the single
transfers `v₀ → v₁ → ⋯ → v_m` succeed: one end moves from `v₀` to `v_m`. The hypothesis on the
later receivers `c ∈ l` counts blank neighbours for the vector after the first transfer, which is
the partition current at the moment `c` receives (see the module docstring). -/
theorem Ach.forwardRelay : ∀ (l : List V) (x y : V) (E : Set (Sym2 V)) (b : V → ℕ), Ach E b →
    (x :: y :: l).Nodup → (∀ e ∈ lEdges x (y :: l), e ∉ E) →
    blankNbrs E b y < b x → (∀ c ∈ (y :: l).dropLast, 1 ≤ b c) →
    (∀ c ∈ l, blankNbrs E (mv b x y) c ≤ 1) →
    Ach (E ∪ {e | e ∈ lEdges x (y :: l)}) (mv b x (lastOf y l))
  | [], x, y, E, b, h, hnd, hnew, hxy, _, _ => by
    have hne : x ≠ y := by simpa using hnd
    have h1 := h.transfer hne (hnew s(x, y) (by simp)) hxy
    refine h1.congr ?_ (fun _ => rfl)
    ext e
    simp only [Set.mem_insert_iff, Set.mem_union, lEdges_cons, lEdges_nil, List.mem_singleton,
      Set.mem_ofPred_eq]
    tauto
  | z :: l, x, y, E, b, h, hnd, hnew, hxy, hpos, hbl => by
    have hx : x ∉ y :: z :: l := (List.nodup_cons.mp hnd).1
    have hnd' : (y :: z :: l).Nodup := (List.nodup_cons.mp hnd).2
    have hy : y ∉ z :: l := (List.nodup_cons.mp hnd').1
    have hne : x ≠ y := fun h => hx (h ▸ List.mem_cons_self)
    have hxz : x ≠ z := fun h => hx (h ▸ by simp)
    have hyz : y ≠ z := fun h => hy (h ▸ List.mem_cons_self)
    have hbx : 1 ≤ b x := by omega
    have hby : 1 ≤ b y := hpos y (by simp)
    have h1 := h.transfer hne (hnew s(x, y) (by simp)) hxy
    -- neighbours of a later vertex are unchanged by the first insertion
    have hmono : ∀ c ∈ z :: l, ∀ b' b'' : V → ℕ, (∀ w, b'' w = 0 → b' w = 0) →
        blankNbrs (insert s(x, y) E) b'' c ≤ blankNbrs E b' c := by
      intro c hc b' b'' hbb
      apply blankNbrs_mono
      intro w hw _ hw0
      refine ⟨?_, hbb w hw0⟩
      rw [Set.mem_insert_iff] at hw
      rcases hw with hw | hw
      · rcases Sym2.eq_iff.mp hw with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact absurd (h1 ▸ List.mem_cons_of_mem _ hc) hx
        · exact absurd (h1 ▸ hc) hy
      · exact hw
    have hlast : lastOf z l ∈ z :: l := lastOf_mem z l
    have h2 := Ach.forwardRelay l y z (insert s(x, y) E) (mv b x y) h1 hnd'
      (by
        intro e he hmem
        rw [Set.mem_insert_iff] at hmem
        rcases hmem with rfl | hmem
        · exact hx (mem_of_mem_lEdges he (Sym2.mem_mk_left x y))
        · exact hnew e (by rw [lEdges_cons]; exact List.mem_cons_of_mem _ he) hmem)
      (by
        rw [mv_apply_recv]
        have := (hmono z List.mem_cons_self _ _ (fun _ h => h)).trans
          (hbl z List.mem_cons_self)
        omega)
      (by
        intro c hc
        have hc' : c ∈ z :: l := List.dropLast_subset _ hc
        have h1 : c ≠ x := fun h => hx (h ▸ List.mem_cons_of_mem _ hc')
        have h2 : c ≠ y := fun h => hy (h ▸ hc')
        rw [mv_apply_other _ h1 h2]
        have hdl : (y :: z :: l).dropLast = y :: (z :: l).dropLast := rfl
        exact hpos c (by rw [hdl]; exact List.mem_cons_of_mem _ hc))
      (by
        intro c hc
        rw [mv_mv b hne hxz hyz hbx]
        refine (hmono c (List.mem_cons_of_mem _ hc) _ _ ?_).trans
          (hbl c (List.mem_cons_of_mem _ hc))
        intro w hw0
        by_cases h1 : w = z
        · subst h1; rw [mv_apply_recv] at hw0; omega
        · by_cases h3 : w = x
          · subst h3
            rw [mv_apply_donor _ hxz] at hw0
            rw [mv_apply_donor _ hne]
            exact hw0
          · rw [mv_apply_other _ h3 h1] at hw0
            by_cases h2 : w = y
            · subst h2; omega
            · rw [mv_apply_other _ h3 h2]; exact hw0)
    refine h2.congr ?_ (fun w => ?_)
    · ext e
      simp only [Set.mem_insert_iff, Set.mem_union, lEdges_cons, List.mem_cons,
        Set.mem_ofPred_eq]
      tauto
    · rw [lastOf_cons]
      have h3 : x ≠ lastOf z l := fun h => hx (h ▸ List.mem_cons_of_mem _ hlast)
      have h4 : y ≠ lastOf z l := fun h => hy (h ▸ hlast)
      exact congrFun (mv_mv b hne h3 h4 hbx) w

end relay

/-! ### Hub transfers -/

/-- The spokes `s(h, z)` from the hub `h` to the vertices of `Z`. -/
def hubSpokes (h : V) (Z : Finset V) : Set (Sym2 V) := {e | ∃ z ∈ Z, e = s(h, z)}

/-- The end vector after `h` has received one end from every vertex of `Z`. -/
def recvEnds (b : V → ℕ) (h : V) (Z : Finset V) (v : V) : ℕ :=
  if v = h then b v + Z.card else if v ∈ Z then b v - 1 else b v

/-- The end vector after `h` has given one end to every vertex of `R`. -/
def giveEnds (b : V → ℕ) (h : V) (R : Finset V) (v : V) : ℕ :=
  if v = h then b v - R.card else if v ∈ R then b v + 1 else b v

omit [DecidableEq V] in
theorem hubSpokes_empty (h : V) : hubSpokes h (∅ : Finset V) = ∅ := by
  ext e; simp [hubSpokes]

theorem hubSpokes_insert (h t : V) (Z : Finset V) :
    hubSpokes h (insert t Z) = insert s(h, t) (hubSpokes h Z) := by
  ext e; simp [hubSpokes]

section hub

variable [Fintype V]

/-- **Grouped receipts at a hub.** The hub `h` receives `m` times from a set `S` of
non-neighbours with one end each. The `j`-th receipt offers `S` minus the spent donors (supply
`|S| − j`) against at most `bl(h) + j` blank neighbours (the spent donors). -/
theorem Ach.receiveMany {E : Set (Sym2 V)} {b : V → ℕ} (hA : Ach E b) (h : V) (S : Finset V)
    (hhS : h ∉ S) (hSE : ∀ t ∈ S, s(t, h) ∉ E) (hS1 : ∀ t ∈ S, b t = 1) (m : ℕ)
    (hm : ∀ j < m, blankNbrs E b h + j < S.card - j) :
    ∃ Z ⊆ S, Z.card = m ∧ Ach (E ∪ hubSpokes h Z) (recvEnds b h Z) := by
  induction m with
  | zero =>
    refine ⟨∅, Finset.empty_subset _, rfl, hA.congr (by rw [hubSpokes_empty, Set.union_empty])
      (fun v => ?_)⟩
    simp [recvEnds]
  | succ m ih =>
    obtain ⟨Z, hZS, hZc, hZ⟩ := ih (fun j hj => hm j (by omega))
    have hhZ : h ∉ Z := fun h' => hhS (hZS h')
    have hbl : blankNbrs (E ∪ hubSpokes h Z) (recvEnds b h Z) h ≤ blankNbrs E b h + Z.card := by
      calc blankNbrs (E ∪ hubSpokes h Z) (recvEnds b h Z) h
          ≤ ({w | s(h, w) ∈ E ∧ w ≠ h ∧ b w = 0} ∪ (Z : Set V)).ncard := by
            apply blankNbrs_le_of_subset
            intro w hw hwh hw0
            by_cases hwZ : w ∈ Z
            · exact Or.inr hwZ
            · left
              have hb : recvEnds b h Z w = b w := by simp [recvEnds, hwh, hwZ]
              refine ⟨?_, hwh, hb ▸ hw0⟩
              rcases hw with hw | ⟨z, hz, hzw⟩
              · exact hw
              · exact absurd ((Sym2.congr_right.mp hzw) ▸ hz) hwZ
        _ ≤ _ := by
            refine (Set.ncard_union_le _ _).trans ?_
            rw [Set.ncard_coe_finset]
            rfl
    have hsum : ∑ t ∈ S \ Z, recvEnds b h Z t = (S \ Z).card := by
      rw [Finset.card_eq_sum_ones]
      refine Finset.sum_congr rfl (fun t ht => ?_)
      rw [Finset.mem_sdiff] at ht
      have hth : t ≠ h := fun h' => hhS (h' ▸ ht.1)
      simp [recvEnds, hth, ht.2, hS1 t ht.1]
    have hcard : (S \ Z).card = S.card - m := by rw [Finset.card_sdiff_of_subset hZS, hZc]
    obtain ⟨t, ht, -, ht'⟩ := hZ.grouped h (S \ Z) (fun h' => hhS (Finset.mem_sdiff.mp h').1)
      (by
        intro t ht hmem
        rw [Finset.mem_sdiff] at ht
        rcases hmem with hmem | ⟨z, hz, hzt⟩
        · exact hSE t ht.1 hmem
        · rcases Sym2.eq_iff.mp hzt with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact hhS (h1 ▸ ht.1)
          · exact ht.2 (h1 ▸ hz))
      (by rw [hsum, hcard]; have := hm m (by omega); omega)
    rw [Finset.mem_sdiff] at ht
    have hth : t ≠ h := fun h' => hhS (h' ▸ ht.1)
    refine ⟨insert t Z, Finset.insert_subset ht.1 hZS,
      by rw [Finset.card_insert_of_notMem ht.2, hZc], ht'.congr ?_ (fun v => ?_)⟩
    · rw [hubSpokes_insert, ← Set.union_insert, Sym2.eq_swap]
    · unfold mv recvEnds
      rw [Finset.card_insert_of_notMem ht.2]
      by_cases hvh : v = h
      · subst hvh; simp; omega
      · by_cases hvt : v = t
        · subst hvt; simp [hvh, ht.2]
        · simp [hvh, hvt]

/-- **Donations from a hub.** The hub `h` gives one end to every vertex of `R`, in any order. It
suffices that `c + |R| ≤ b(h)`, where every receiver has at most `c` blank neighbours outside `R`
(blank receivers that have not yet been paid count against the receiver, and are absorbed by the
`|R|` term). -/
theorem Ach.giveAll {E : Set (Sym2 V)} {b : V → ℕ} (hA : Ach E b) (h : V) (R : Finset V)
    (hhR : h ∉ R) (hRE : ∀ a ∈ R, s(h, a) ∉ E) (c : ℕ)
    (hc : ∀ a ∈ R, {w | s(a, w) ∈ E ∧ w ≠ a ∧ b w = 0 ∧ w ∉ R}.ncard ≤ c)
    (hN : c + R.card ≤ b h) : Ach (E ∪ hubSpokes h R) (giveEnds b h R) := by
  induction R using Finset.induction_on generalizing E b with
  | empty =>
    refine hA.congr (by rw [hubSpokes_empty, Set.union_empty]) (fun v => ?_)
    simp [giveEnds]
  | @insert a R haR ih =>
    have hha : h ≠ a := fun h' => hhR (h' ▸ Finset.mem_insert_self a R)
    have hbl : blankNbrs E b a ≤ c + R.card := by
      calc blankNbrs E b a
          ≤ ({w | s(a, w) ∈ E ∧ w ≠ a ∧ b w = 0 ∧ w ∉ insert a R} ∪ (R : Set V)).ncard := by
            apply blankNbrs_le_of_subset
            intro w hw hwa hw0
            by_cases hwR : w ∈ R
            · exact Or.inr hwR
            · left
              refine ⟨hw, hwa, hw0, ?_⟩
              rw [Finset.mem_insert, not_or]
              exact ⟨hwa, hwR⟩
        _ ≤ _ := by
            refine (Set.ncard_union_le _ _).trans ?_
            rw [Set.ncard_coe_finset]
            have := hc a (Finset.mem_insert_self a R)
            omega
    rw [Finset.card_insert_of_notMem haR] at hN
    have h1 := hA.transfer hha (hRE a (Finset.mem_insert_self a R)) (by omega)
    have h2 := ih h1 (fun h' => hhR (Finset.mem_insert_of_mem h'))
      (by
        intro x hx hmem
        rw [Set.mem_insert_iff] at hmem
        rcases hmem with hmem | hmem
        · have hxa : x = a := Sym2.congr_right.mp hmem
          exact haR (hxa ▸ hx)
        · exact hRE x (Finset.mem_insert_of_mem hx) hmem)
      (by
        intro x hx
        refine (Set.ncard_le_ncard ?_ (Set.toFinite _)).trans (hc x (Finset.mem_insert_of_mem hx))
        rintro w ⟨hw, hwx, hw0, hwR⟩
        have hxh : x ≠ h := fun h' => hhR (h' ▸ Finset.mem_insert_of_mem hx)
        have hxa : x ≠ a := fun h' => haR (h' ▸ hx)
        have hw' : s(x, w) ∈ E := by
          rw [Set.mem_insert_iff] at hw
          rcases hw with hw | hw
          · rcases Sym2.eq_iff.mp hw with ⟨h1, -⟩ | ⟨h1, -⟩
            · exact absurd h1 hxh
            · exact absurd h1 hxa
          · exact hw
        have hwa : w ≠ a := by
          rintro rfl; rw [mv_apply_recv] at hw0; omega
        have hwh : w ≠ h := by
          rintro rfl
          exact hRE x (Finset.mem_insert_of_mem hx) (by rwa [Sym2.eq_swap])
        refine ⟨hw', hwx, by rwa [mv_apply_other _ hwh hwa] at hw0, ?_⟩
        rw [Finset.mem_insert, not_or]
        exact ⟨hwa, hwR⟩)
      (by rw [mv_apply_donor _ hha]; omega)
    refine h2.congr (by rw [hubSpokes_insert, Set.union_insert, Set.insert_union])
      (fun v => ?_)
    unfold giveEnds mv
    rw [Finset.card_insert_of_notMem haR]
    by_cases hvh : v = h
    · subst hvh; simp [hha]; omega
    · by_cases hva : v = a
      · subst hva; simp [hvh, haR]
      · simp [hvh, hva]

end hub

end Gallai
