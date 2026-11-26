import GallaiLean.Lovasz

/-!
# BP₃ and realisable pairs among four even vertices

Write `b = ends_D`, and use "even" for *positive* even degree.

## Two-even lemma (`two_even`)

Suppose `u` has even degree and every even vertex other than `u` is a single vertex `v`. Then
`G` has a decomposition with `b(w) = deg(w) mod 2` for `w ≠ u` (so `b(v) = 0`) and
`b(u) ∈ {0, 2}`.

*Proof.* Attach a leaf at `u` (`apex G {u}`). Then `v` is the only even vertex, so Lovász
applies. Delete the leaf: the end count at `u` changes by at most one and keeps the parity of
`deg u`.

## Four even vertices (`four_even_pair`)

Let `evenSet G = {r} ∪ T` with `|T| = 3`, and let some path join `r` to `T`. Then there is
`w ∈ T` with `{r, w}` realisable (`b = 2` on `r, w`, `0` on the other even vertices, `1` on odd
ones).

*Case A* (`r` is adjacent to some `p ∈ T` and not to some `v ∈ T`; let `u` be the third vertex).
In `G' = G − rp` the even vertices are `u, v`. The two-even lemma gives `b'(v) = 0`,
`b'(u) ∈ {0, 2}`, and `b'(r) = b'(p) = 1`.
* If `b'(u) = 0`, add `rp` as a new path, which realises `{r, p}`.
* If `b'(u) = 2`, every zero-end vertex of `G'` is `v` or isolated. Since `v ∉ N(r)`, Fan's
  lemma moves an end from `p` to `r`, which realises `{r, u}`.

*Case B* (`r` is adjacent to all of `T = {p, q, q'}`). Delete `rq`, `rq'` and `rp`. Every degree
becomes odd, so Lovász gives `b ≡ 1` on vertices of positive degree.
1. Restore `rp` by Fan (`p → r`). Now `r` has 2 ends and `p` has 0.
2. Grouped Fan with donors `{q, q'}` has `∑ = 2 > 1 = #{p}`, so some `t` moves its end to `r`.
   Now `r` has 3 ends and `t` has 0.
3. Restore the last edge `rt'` by Fan `r → t'`, where `#{p, t} ≤ 2 < 3`.
This realises `{r, t'}`.

*Case C* (`r` has no neighbour in `T`). Let `o` be the next vertex on a shortest path to `T`.
It is odd. In `G' = G − ro` the even vertices are `{o} ∪ T`, and `o` is one step closer to
`T`. Induction gives `{o, w}` realisable in `G'`. No zero-end vertex is adjacent to `r`: such
a vertex would lie in `T`. So Fan moves an end from `o` (which has 2 ends) to `r`, which
realises `{r, w}`.

## BP₃ (`bp3`)

`W` is connected, with a leaf `ℓ` at `s` and exactly three even vertices. Then `W` realises
some `S` with `|S| ≤ 1`, so `p(W) ≤ ⌊|W|/2⌋`.
* If `s` is even, then in `W − ℓs` the even vertices are the other two. Apply the two-even
  lemma, then re-append `ℓ` at an end at `s`.
* If `s` is odd, then in `W − ℓs` the even vertices are `{s} ∪ E`. Apply `four_even_pair` at
  `s` to get `{s, w}` realisable, then re-append `ℓ` at `s`.
-/

open SimpleGraph

namespace Gallai

universe u

section helpers

variable {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]

theorem delEdge_degree_of_ne {a b : W} (hab : G.Adj a b) {w : W} (hwa : w ≠ a) (hwb : w ≠ b) :
    (delEdge G a b).degree w = G.degree w := by
  have := delEdge_degree G hab w
  simp only [hwa, hwb, ite_false, add_zero] at this
  exact this

theorem delEdge_degree_left {a b : W} (hab : G.Adj a b) :
    (delEdge G a b).degree a + 1 = G.degree a := by
  have := delEdge_degree G hab a
  simp only [hab.ne, ite_true, ite_false, add_zero] at this
  exact this

theorem delEdge_degree_right {a b : W} (hab : G.Adj a b) :
    (delEdge G a b).degree b + 1 = G.degree b := by
  have := delEdge_degree G hab b
  simp only [hab.ne.symm, ite_true, ite_false, add_zero] at this
  exact this

variable {G}

theorem realises_of {S : Finset W} {D : PathDecomp G} (hS : S ⊆ evenSet G)
    (h : ∀ v, D.ends v = G.degree v % 2 + if v ∈ S then 2 else 0) : Realises G D S := by
  intro v
  rw [h v]
  unfold profile
  by_cases ho : Odd (G.degree v)
  · have hvS : v ∉ S := fun hv => not_odd_of_mem_evenSet (hS hv) ho
    have ho' := Nat.odd_iff.mp ho
    simp only [ho, ite_true, hvS, ite_false, ho', add_zero]
  · have he : G.degree v % 2 = 0 := by rw [Nat.odd_iff] at ho; omega
    simp only [ho, ite_false, he, zero_add]

theorem ends_of_realises {S : Finset W} {D : PathDecomp G} (hS : S ⊆ evenSet G)
    (h : Realises G D S) (v : W) : D.ends v = G.degree v % 2 + if v ∈ S then 2 else 0 := by
  rw [h v]
  unfold profile
  by_cases ho : Odd (G.degree v)
  · have hvS : v ∉ S := fun hv => not_odd_of_mem_evenSet (hS hv) ho
    have ho' := Nat.odd_iff.mp ho
    simp only [ho, ite_true, hvS, ite_false, ho', add_zero]
  · have he : G.degree v % 2 = 0 := by rw [Nat.odd_iff] at ho; omega
    simp only [ho, ite_false, he, zero_add]

omit [Fintype W] [DecidableRel G.Adj] in
theorem PathDecomp.exists_end_of_pos (D : PathDecomp G) {x : W} (h : 0 < D.ends x) :
    ∃ P ∈ D.paths, P.src = x ∨ P.tgt = x := by
  by_contra hc
  simp only [not_exists, not_and] at hc
  have : D.ends x = 0 := by
    unfold PathDecomp.ends
    refine List.sum_eq_zero_iff_forall_eq_nat.mpr ?_
    intro n hn
    obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hn
    unfold GPath.endsAt
    by_cases hs : P.src = x
    · exact absurd (Or.inl hs) (hc P hP)
    · by_cases ht : P.tgt = x
      · exact absurd (Or.inr ht) (hc P hP)
      · simp [hs, ht]
  omega

omit [DecidableRel G.Adj] in
theorem not_mem_support_of_degree_zero [DecidableRel G.Adj] (P : GPath G) {x : W}
    (hx : G.degree x = 0) : x ∉ P.walk.support := by
  intro hm
  obtain ⟨e, he, hxe⟩ := P.exists_edge_of_mem_support hm
  have heG := P.walk.edges_subset_edgeSet he
  induction e using Sym2.inductionOn with
  | hf a b =>
  rcases Sym2.mem_iff.mp hxe with rfl | rfl
  · have := (G.degree_pos_iff_exists_adj x).mpr ⟨b, heG⟩; omega
  · have := (G.degree_pos_iff_exists_adj x).mpr ⟨a, G.symm.symm _ _ heG⟩; omega

end helpers

/-! ### The two-even lemma -/

section twoEven

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- **Two-even lemma.** If `u` has even degree and at most one other vertex has positive even
degree, then some decomposition has `b(w) = deg(w) mod 2` for `w ≠ u` and `b(u) ∈ {0, 2}`. -/
theorem two_even (G : SimpleGraph W) [DecidableRel G.Adj] {u : W} (hu : G.degree u % 2 = 0)
    (hev : ((evenSet G).erase u).card ≤ 1) :
    ∃ D : PathDecomp G, (∀ w, w ≠ u → D.ends w = G.degree w % 2) ∧
      (D.ends u = 0 ∨ D.ends u = 2) := by
  have hHsome : ∀ w, (apex G {u}).degree (some w) = G.degree w + (if w = u then 1 else 0) := by
    intro w
    rw [apex_degree_some]
    simp [Finset.mem_singleton]
  have hHnone : (apex G {u}).degree none = 1 := by
    rw [apex_degree_none]; simp
  have hevH : evenSet (apex G {u}) ⊆
      ((evenSet G).erase u).map ⟨some, Option.some_injective _⟩ := by
    intro w hw
    rw [mem_evenSet_iff] at hw
    cases w with
    | none => rw [hHnone] at hw; omega
    | some y =>
      rw [hHsome] at hw
      rw [Finset.mem_map]
      refine ⟨y, ?_, rfl⟩
      by_cases hyu : y = u
      · subst hyu
        simp only [ite_true] at hw
        omega
      · simp only [hyu, ite_false, add_zero] at hw
        exact Finset.mem_erase.mpr ⟨hyu, mem_evenSet_iff.mpr hw⟩
  have hcardH : (evenSet (apex G {u})).card ≤ 1 :=
    (Finset.card_le_card hevH).trans (by rw [Finset.card_map]; exact hev)
  obtain ⟨DH, hDH⟩ := lovasz_ends (apex G {u}) hcardH
  obtain ⟨D, hD⟩ := (apexRetract G {u} u).delete DH (by
    intro P _ y hy hky
    cases y with
    | some _ => simp [apexRetract] at hky
    | none => exact (P.end_of_pendant apex_none_pendant hy).imp Eq.symm Eq.symm)
  refine ⟨D, fun w hwu => ?_, ?_⟩
  · rw [(hD w).1 (fun e he hk hwe => hwu (Finset.mem_singleton.mp (apex_nonkept he hk hwe).2))]
    change DH.ends (some w) = _
    rw [hDH, hHsome]
    simp [hwu]
  · have hle := (hD u).2 (fun e₁ he₁ e₂ he₂ hk₁ hk₂ hv₁ hv₂ => by
      rw [(apex_nonkept he₁ hk₁ hv₁).1, (apex_nonkept he₂ hk₂ hv₂).1])
    change D.ends u ≤ DH.ends (some u) + 1 at hle
    rw [hDH, hHsome] at hle
    simp only [ite_true] at hle
    have hp := D.ends_mod_two u
    omega

end twoEven

/-! ### Four even vertices -/

section four

variable {W : Type u} [Fintype W] [DecidableEq W]

theorem mem_evenSet_insert {G : SimpleGraph W} [DecidableRel G.Adj] {r : W} {T : Finset W}
    (hE : evenSet G = insert r T) (w : W) :
    (0 < G.degree w ∧ G.degree w % 2 = 0) ↔ (w = r ∨ w ∈ T) := by
  rw [← mem_evenSet_iff, hE, Finset.mem_insert]

theorem pair_subset_evenSet {G : SimpleGraph W} [DecidableRel G.Adj] {r w : W} {T : Finset W}
    (hE : evenSet G = insert r T) (hw : w ∈ T) : ({r, w} : Finset W) ⊆ evenSet G := by
  intro x hx
  rw [Finset.mem_insert, Finset.mem_singleton] at hx
  rw [hE, Finset.mem_insert]
  rcases hx with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr hw

/-- Case A: `r` sees some `p ∈ T` and misses some `v ∈ T`. -/
theorem four_even_caseA (G : SimpleGraph W) [DecidableRel G.Adj] (r : W) (T : Finset W)
    (hrT : r ∉ T) (hT : T.card = 3) (hE : evenSet G = insert r T)
    {p v : W} (hpT : p ∈ T) (hrp : G.Adj r p) (hvT : v ∈ T) (hrv : ¬ G.Adj r v) :
    ∃ w ∈ T, Realisable G {r, w} := by
  have hEv := mem_evenSet_insert hE
  have hpv : p ≠ v := fun h => hrv (h ▸ hrp)
  have hrp' : r ≠ p := hrp.ne
  obtain ⟨u, hu⟩ : ∃ u, (T.erase p).erase v = {u} := by
    apply Finset.card_eq_one.mp
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hpv, hvT⟩),
      Finset.card_erase_of_mem hpT, hT]
  have huT' : u ∈ (T.erase p).erase v := by rw [hu]; exact Finset.mem_singleton_self u
  have hup : u ≠ p := (Finset.mem_erase.mp (Finset.mem_erase.mp huT').2).1
  have huT : u ∈ T := (Finset.mem_erase.mp (Finset.mem_erase.mp huT').2).2
  have hru : r ≠ u := fun h => hrT (h ▸ huT)
  have hTmem : ∀ w, w ∈ T → w = p ∨ w = v ∨ w = u := by
    intro w hw
    by_cases hwp : w = p
    · exact Or.inl hwp
    · by_cases hwv : w = v
      · exact Or.inr (Or.inl hwv)
      · have : w ∈ (T.erase p).erase v :=
          Finset.mem_erase.mpr ⟨hwv, Finset.mem_erase.mpr ⟨hwp, hw⟩⟩
        rw [hu, Finset.mem_singleton] at this
        exact Or.inr (Or.inr this)
  have hr2 := ((hEv r).2 (Or.inl rfl)).2
  have hp2 := ((hEv p).2 (Or.inr hpT)).2
  have hu2 := ((hEv u).2 (Or.inr huT)).2
  have hdr := delEdge_degree_left G hrp
  have hdp := delEdge_degree_right G hrp
  have hdo : ∀ w, w ≠ r → w ≠ p → (delEdge G r p).degree w = G.degree w :=
    fun w h1 h2 => delEdge_degree_of_ne G hrp h1 h2
  have hev' : ∀ w ∈ evenSet (delEdge G r p), w = u ∨ w = v := by
    intro w hw
    rw [mem_evenSet_iff] at hw
    by_cases hwr : w = r
    · rw [hwr] at hw; omega
    · by_cases hwp : w = p
      · rw [hwp] at hw; omega
      · rw [hdo w hwr hwp] at hw
        rcases (hEv w).1 hw with h | h
        · exact absurd h hwr
        · rcases hTmem w h with h' | h' | h'
          · exact absurd h' hwp
          · exact Or.inr h'
          · exact Or.inl h'
  have hcard : ((evenSet (delEdge G r p)).erase u).card ≤ 1 := by
    apply (Finset.card_le_card (t := {v}) ?_).trans (by simp)
    intro w hw
    rw [Finset.mem_erase] at hw
    rcases hev' w hw.2 with h | h
    · exact absurd h hw.1
    · rw [h]; exact Finset.mem_singleton_self v
  obtain ⟨D', hD'w, hD'u⟩ := two_even (delEdge G r p) (u := u)
    (by rw [hdo u (Ne.symm hru) hup]; exact hu2) hcard
  rcases hD'u with h0 | h2
  · -- add `rp` as a new path: realise `{r, p}`
    obtain ⟨D, hD⟩ := PathDecomp.add_edge hrp (delEdge_edgeSet G r p) D'
    refine ⟨p, hpT, pair_subset_evenSet hE hpT, D,
      realises_of (pair_subset_evenSet hE hpT) (fun w => ?_)⟩
    rw [hD w]
    by_cases hwu : w = u
    · rw [hwu, h0]
      simp [hru, Ne.symm hru, hup, Ne.symm hup] <;> omega
    · rw [hD'w w hwu]
      by_cases hwr : w = r
      · rw [hwr]
        simp [hrp', Ne.symm hrp'] <;> omega
      · by_cases hwp : w = p
        · rw [hwp]
          simp [hrp', Ne.symm hrp'] <;> omega
        · rw [hdo w hwr hwp]
          simp [hwr, hwp, Ne.symm hwr, Ne.symm hwp]
  · -- Fan's transfer `p → r`: realise `{r, u}`
    obtain ⟨D, -, hDr, hDp, hDo⟩ := fan_single hrp (delEdge_edgeSet G r p) D' (by
      have hempty : Finset.univ.filter
          (fun w => (delEdge G r p).Adj r w ∧ D'.ends w = 0) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        rintro w - ⟨hadj, hw0⟩
        have hwu : w ≠ u := by rintro rfl; omega
        have hpos : 0 < (delEdge G r p).degree w :=
          ((delEdge G r p).degree_pos_iff_exists_adj w).mpr ⟨r, hadj.symm⟩
        rw [hD'w w hwu] at hw0
        rcases hev' w (mem_evenSet_iff.mpr ⟨hpos, hw0⟩) with h | h
        · exact hwu h
        · rw [h] at hadj; exact hrv hadj.1
      rw [hempty, Finset.card_empty, hD'w p (Ne.symm hup)]
      omega)
    refine ⟨u, huT, pair_subset_evenSet hE huT, D,
      realises_of (pair_subset_evenSet hE huT) (fun w => ?_)⟩
    by_cases hwr : w = r
    · rw [hwr, hDr, hD'w r hru]
      simp <;> omega
    · by_cases hwp : w = p
      · have h1 := hD'w p (Ne.symm hup)
        rw [hwp]
        simp [hrp', Ne.symm hrp', hup, Ne.symm hup] <;> omega
      · rw [hDo w hwr hwp]
        by_cases hwu : w = u
        · rw [hwu, h2]
          simp <;> omega
        · rw [hD'w w hwu, hdo w hwr hwp]
          simp [hwr, hwu, Ne.symm hwr, Ne.symm hwu]

/-- Case B: `r` sees all of `T`. -/
theorem four_even_caseB (G : SimpleGraph W) [DecidableRel G.Adj] (r : W) (T : Finset W)
    (hrT : r ∉ T) (hT : T.card = 3) (hE : evenSet G = insert r T)
    (hall : ∀ x ∈ T, G.Adj r x) :
    ∃ w ∈ T, Realisable G {r, w} := by
  have hEv := mem_evenSet_insert hE
  obtain ⟨p, q, q', hpq, hpq', hqq', rfl⟩ := Finset.card_eq_three.mp hT
  have hrp := hall p (by simp)
  have hrq := hall q (by simp)
  have hrq' := hall q' (by simp)
  have hr2 := ((hEv r).2 (Or.inl rfl)).2
  have hp2 := ((hEv p).2 (Or.inr (by simp))).2
  have hq2 := ((hEv q).2 (Or.inr (by simp))).2
  have hq'2 := ((hEv q').2 (Or.inr (by simp))).2
  have hrp' : r ≠ p := hrp.ne
  have hrq0 : r ≠ q := hrq.ne
  have hrq'0 : r ≠ q' := hrq'.ne
  have hne : ∀ {a b : W}, a ≠ b → s(r, a) ≠ s(r, b) := fun h h' => h (Sym2.congr_right.mp h')
  have h1 : (delEdge G r q).Adj r q' := ⟨hrq', hne (Ne.symm hqq')⟩
  have h2 : (delEdge (delEdge G r q) r q').Adj r p := ⟨⟨hrp, hne hpq⟩, hne hpq'⟩
  have d1 := delEdge_degree G hrq
  have d2 := delEdge_degree (delEdge G r q) h1
  have d3 := delEdge_degree (delEdge (delEdge G r q) r q') h2
  have deg3 : ∀ w, w ≠ r → w ≠ p → w ≠ q → w ≠ q' →
      (delEdge (delEdge (delEdge G r q) r q') r p).degree w = G.degree w := by
    intro w h1 h2 h3 h4
    have a := d1 w; have b := d2 w; have c := d3 w
    simp only [h1, h2, h3, h4, ite_false, add_zero] at a b c
    omega
  have hev3 : ∀ w, w ∉ evenSet (delEdge (delEdge (delEdge G r q) r q') r p) := by
    intro w hw
    rw [mem_evenSet_iff] at hw
    have a := d1 w; have b := d2 w; have c := d3 w
    by_cases hwr : w = r
    · rw [hwr] at a b c hw
      simp only [hrp', hrq0, hrq'0, ite_true, ite_false, add_zero] at a b c
      omega
    · by_cases hwp : w = p
      · rw [hwp] at a b c hw
        simp only [Ne.symm hrp', hpq, hpq', ite_true, ite_false, add_zero] at a b c
        omega
      · by_cases hwq : w = q
        · rw [hwq] at a b c hw
          simp only [Ne.symm hrq0, Ne.symm hpq, hqq', ite_true, ite_false, add_zero] at a b c
          omega
        · by_cases hwq' : w = q'
          · rw [hwq'] at a b c hw
            simp only [Ne.symm hrq'0, Ne.symm hpq', Ne.symm hqq', ite_true, ite_false,
              add_zero] at a b c
            omega
          · rw [deg3 w hwr hwp hwq hwq'] at hw
            rcases (hEv w).1 hw with h | h
            · exact hwr h
            · simp only [Finset.mem_insert, Finset.mem_singleton] at h
              rcases h with h | h | h
              · exact hwp h
              · exact hwq h
              · exact hwq' h
  obtain ⟨D₃, hD₃⟩ := lovasz_ends (delEdge (delEdge (delEdge G r q) r q') r p) (by
    rw [Finset.eq_empty_of_forall_notMem hev3]; simp)
  have hone3 : ∀ w, 0 < (delEdge (delEdge (delEdge G r q) r q') r p).degree w →
      D₃.ends w = 1 := by
    intro w hw
    rw [hD₃ w]
    have := hev3 w
    rw [mem_evenSet_iff] at this
    omega
  have hpos3 : ∀ {x w : W}, (delEdge (delEdge (delEdge G r q) r q') r p).Adj x w →
      0 < (delEdge (delEdge (delEdge G r q) r q') r p).degree w :=
    fun h => ((delEdge (delEdge (delEdge G r q) r q') r p).degree_pos_iff_exists_adj _).mpr
      ⟨_, h.symm⟩
  have e3 : ∀ w, (w = r ∨ w = p ∨ w = q ∨ w = q') → D₃.ends w = 1 := by
    intro w hw
    apply hone3
    have a := d1 w; have b := d2 w; have c := d3 w
    rcases hw with rfl | rfl | rfl | rfl
    · simp only [hrp', hrq0, hrq'0, ite_true, ite_false, add_zero] at a b c; omega
    · simp only [Ne.symm hrp', hpq, hpq', ite_true, ite_false, add_zero] at a b c; omega
    · simp only [Ne.symm hrq0, Ne.symm hpq, hqq', ite_true, ite_false, add_zero] at a b c
      omega
    · simp only [Ne.symm hrq'0, Ne.symm hpq', Ne.symm hqq', ite_true, ite_false,
        add_zero] at a b c
      omega
  have e3r := e3 r (Or.inl rfl)
  have e3p := e3 p (Or.inr (Or.inl rfl))
  have e3q := e3 q (Or.inr (Or.inr (Or.inl rfl)))
  have e3q' := e3 q' (Or.inr (Or.inr (Or.inr rfl)))
  -- step 1: restore `rp`
  obtain ⟨D₂, -, hD₂r, hD₂p, hD₂o⟩ := fan_single h2
    (delEdge_edgeSet (delEdge (delEdge G r q) r q') r p) D₃ (by
      have hempty : Finset.univ.filter (fun w =>
          (delEdge (delEdge (delEdge G r q) r q') r p).Adj r w ∧ D₃.ends w = 0) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        rintro w - ⟨hadj, hw0⟩
        rw [hone3 w (hpos3 hadj)] at hw0
        exact one_ne_zero hw0
      rw [hempty, Finset.card_empty, e3p]
      exact Nat.one_pos)
  -- step 2: grouped transfer from `{q, q'}` to `r`
  obtain ⟨t, ht, hK⟩ := fan_grouped D₂ r {q, q'}
    (by simp [hrq0, hrq'0])
    (by
      intro t ht hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hadj.1.2 Sym2.eq_swap
      · exact hadj.2 Sym2.eq_swap)
    (by
      rw [Finset.sum_pair hqq', hD₂o q (Ne.symm hrq0) (Ne.symm hpq),
        hD₂o q' (Ne.symm hrq'0) (Ne.symm hpq'), e3q, e3q']
      have hsub : Finset.univ.filter
          (fun w => (delEdge (delEdge G r q) r q').Adj r w ∧ D₂.ends w = 0) ⊆ {p} := by
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
        rw [Finset.mem_singleton]
        by_contra hwp
        have hwr : w ≠ r := hw.1.ne.symm
        rw [hD₂o w hwr hwp] at hw
        have hadj3 : (delEdge (delEdge (delEdge G r q) r q') r p).Adj r w :=
          ⟨hw.1, fun h => hwp (Sym2.congr_right.mp h)⟩
        rw [hone3 w (hpos3 hadj3)] at hw
        exact one_ne_zero hw.2
      have := Finset.card_le_card hsub
      rw [Finset.card_singleton] at this
      omega)
  -- step 3: restore the last edge `rt'`
  have step3 : ∀ t' : W, ((t = q ∧ t' = q') ∨ (t = q' ∧ t' = q)) →
      (∀ e, e ∈ (delEdge G r t').edgeSet ↔
        e ∈ (delEdge (delEdge G r q) r q').edgeSet ∨ e = s(t, r)) →
      ∃ w ∈ ({p, q, q'} : Finset W), Realisable G {r, w} := by
    intro t' htt hedges
    obtain ⟨D₁, -, hD₁⟩ := hK (delEdge G r t') hedges
    have htr : t ≠ r := by
      rcases htt with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]; exact Ne.symm hrq0
      · rw [h]; exact Ne.symm hrq'0
    have ht'r : t' ≠ r := by
      rcases htt with ⟨-, h⟩ | ⟨-, h⟩
      · rw [h]; exact Ne.symm hrq'0
      · rw [h]; exact Ne.symm hrq0
    have htp : t ≠ p := by
      rcases htt with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]; exact Ne.symm hpq
      · rw [h]; exact Ne.symm hpq'
    have ht'p : t' ≠ p := by
      rcases htt with ⟨-, h⟩ | ⟨-, h⟩
      · rw [h]; exact Ne.symm hpq'
      · rw [h]; exact Ne.symm hpq
    have htt' : t ≠ t' := by
      rcases htt with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hqq'
      · rw [h1, h2]; exact Ne.symm hqq'
    have e3t : D₃.ends t = 1 := by
      rcases htt with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]; exact e3q
      · rw [h]; exact e3q'
    have e3t' : D₃.ends t' = 1 := by
      rcases htt with ⟨-, h⟩ | ⟨-, h⟩
      · rw [h]; exact e3q'
      · rw [h]; exact e3q
    have hother : ∀ w, w ≠ t → w ≠ t' → w ≠ q ∧ w ≠ q' := by
      intro w h1 h2
      rcases htt with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [ha] at h1; rw [hb] at h2; exact ⟨h1, h2⟩
      · rw [ha] at h1; rw [hb] at h2; exact ⟨h2, h1⟩
    have hrt' : G.Adj t' r := by
      rcases htt with ⟨-, h⟩ | ⟨-, h⟩
      · rw [h]; exact hrq'.symm
      · rw [h]; exact hrq.symm
    have ht'2 : G.degree t' % 2 = 0 := by
      rcases htt with ⟨-, h⟩ | ⟨-, h⟩
      · rw [h]; exact hq'2
      · rw [h]; exact hq2
    have ht2 : G.degree t % 2 = 0 := by
      rcases htt with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]; exact hq2
      · rw [h]; exact hq'2
    have hD₁r : D₁.ends r = 3 := by
      have := hD₁ r
      rw [hD₂r, e3r] at this
      simp only [htr, ite_true, ite_false, add_zero] at this
      omega
    have hD₁t : D₁.ends t = 0 := by
      have := hD₁ t
      rw [hD₂o t htr htp, e3t] at this
      simp only [htr, Ne.symm htr, ite_true, ite_false, add_zero] at this
      omega
    have hD₁o : ∀ w, w ≠ r → w ≠ t → D₁.ends w = D₂.ends w := by
      intro w hwr hwt
      have := hD₁ w
      simp only [Ne.symm hwt, Ne.symm hwr, ite_false, add_zero] at this
      exact this
    have hG' : ∀ e, e ∈ (delEdge G r t').edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(t', r) := by
      intro e
      rw [delEdge_edgeSet, Sym2.eq_swap (a := r)]
    obtain ⟨D, -, hDt', hDr, hDo⟩ := fan_single hrt' hG' D₁ (by
      have hsub : Finset.univ.filter
          (fun w => (delEdge G r t').Adj t' w ∧ D₁.ends w = 0) ⊆ {p, t} := by
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
        rw [Finset.mem_insert, Finset.mem_singleton]
        by_contra hc
        rw [not_or] at hc
        obtain ⟨hwp, hwt⟩ := hc
        have hwr : w ≠ r := by
          intro h
          rw [h, hD₁r] at hw
          exact absurd hw.2 (by norm_num)
        rw [hD₁o w hwr hwt, hD₂o w hwr hwp] at hw
        have hnr : ∀ a, ¬ s(t', w) = s(r, a) := by
          intro a h
          rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
          · exact ht'r h1
          · exact hwr h2
        have hadj3 : (delEdge (delEdge (delEdge G r q) r q') r p).Adj t' w :=
          ⟨⟨⟨hw.1.1, hnr q⟩, hnr q'⟩, hnr p⟩
        rw [hone3 w (hpos3 hadj3)] at hw
        exact one_ne_zero hw.2
      have := Finset.card_le_card hsub
      have h2c : ({p, t} : Finset W).card ≤ 2 := Finset.card_le_two
      omega)
    have ht'mem : t' ∈ ({p, q, q'} : Finset W) := by
      rcases htt with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
    refine ⟨t', ht'mem, pair_subset_evenSet hE ht'mem, D,
      realises_of (pair_subset_evenSet hE ht'mem) (fun w => ?_)⟩
    by_cases hwr : w = r
    · rw [hwr]
      simp <;> omega
    · by_cases hwt' : w = t'
      · rw [hwt', hDt', hD₁o t' ht'r (Ne.symm htt'), hD₂o t' ht'r ht'p, e3t']
        simp <;> omega
      · rw [hDo w hwt' hwr]
        have hS : w ∉ ({r, t'} : Finset W) := by simp [hwr, hwt']
        simp only [hS, ite_false, add_zero]
        by_cases hwt : w = t
        · rw [hwt, hD₁t]; omega
        · rw [hD₁o w hwr hwt]
          by_cases hwp : w = p
          · rw [hwp]; omega
          · rw [hD₂o w hwr hwp]
            obtain ⟨hwq, hwq'⟩ := hother w hwt hwt'
            have hdeg := deg3 w hwr hwp hwq hwq'
            rcases Nat.eq_zero_or_pos
                ((delEdge (delEdge (delEdge G r q) r q') r p).degree w) with hz | hpw
            · rw [hD₃ w, hz, ← hdeg, hz]
            · rw [hone3 w hpw]
              have := hev3 w
              rw [mem_evenSet_iff, hdeg] at this
              rw [hdeg] at hpw
              omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with ht | ht
  · refine step3 q' (Or.inl ⟨ht, rfl⟩) ?_
    intro e
    rw [ht]
    simp only [delEdge_edgeSet]
    constructor
    · rintro ⟨he, hne'⟩
      by_cases h : e = s(r, q)
      · exact Or.inr (h.trans Sym2.eq_swap)
      · exact Or.inl ⟨⟨he, h⟩, hne'⟩
    · rintro (⟨⟨he, -⟩, hne'⟩ | rfl)
      · exact ⟨he, hne'⟩
      · refine ⟨hrq.symm, ?_⟩
        intro h
        rw [Sym2.eq_swap] at h
        exact hqq' (Sym2.congr_right.mp h)
  · refine step3 q (Or.inr ⟨ht, rfl⟩) ?_
    intro e
    rw [ht]
    simp only [delEdge_edgeSet]
    constructor
    · rintro ⟨he, hne'⟩
      by_cases h : e = s(r, q')
      · exact Or.inr (h.trans Sym2.eq_swap)
      · exact Or.inl ⟨⟨he, hne'⟩, h⟩
    · rintro (⟨⟨he, h1⟩, -⟩ | rfl)
      · exact ⟨he, h1⟩
      · refine ⟨hrq'.symm, ?_⟩
        intro h
        rw [Sym2.eq_swap] at h
        exact hqq' (Sym2.congr_right.mp h).symm

/-- Every realisable pair among four even vertices, by induction on the length of a path from
`r` to `T`. -/
theorem four_even_pair (d : ℕ) : ∀ (G : SimpleGraph W) [DecidableRel G.Adj] (r : W)
    (T : Finset W), r ∉ T → T.card = 3 → evenSet G = insert r T →
    (∃ t ∈ T, ∃ p : G.Walk r t, p.IsPath ∧ p.length ≤ d) →
    ∃ w ∈ T, Realisable G {r, w} := by
  induction d with
  | zero =>
    rintro G _ r T hrT - - ⟨t, ht, p, -, hp⟩
    have hrt := Walk.eq_of_length_eq_zero (p := p) (by omega)
    exact absurd (hrt ▸ ht) hrT
  | succ d ih =>
    intro G _ r T hrT hT hE ⟨t, ht, p, hpath, hp⟩
    by_cases hadj : ∃ x ∈ T, G.Adj r x
    · obtain ⟨x, hxT, hrx⟩ := hadj
      by_cases hall : ∀ y ∈ T, G.Adj r y
      · exact four_even_caseB G r T hrT hT hE hall
      · simp only [not_forall] at hall
        obtain ⟨v, hvT, hrv⟩ := hall
        exact four_even_caseA G r T hrT hT hE hxT hrx hvT hrv
    · -- Case C: step towards `T`
      simp only [not_exists, not_and] at hadj
      have hEv := mem_evenSet_insert hE
      have hrt : r ≠ t := fun h => hrT (h ▸ ht)
      obtain ⟨o, hro, p', rfl⟩ := Walk.exists_eq_cons_of_length_pos p (by
        by_contra h0
        exact hrt (Walk.eq_of_length_eq_zero (p := p) (by omega)))
      rw [Walk.cons_isPath_iff] at hpath
      have hoT : o ∉ T := fun h => hadj o h hro
      have hor : o ≠ r := hro.ne.symm
      have hot : o ≠ t := fun h => hoT (h ▸ ht)
      obtain ⟨y, hoy, p'', rfl⟩ := Walk.exists_eq_cons_of_length_pos p' (by
        by_contra h0
        exact hot (Walk.eq_of_length_eq_zero (p := p') (by omega)))
      have hyr : y ≠ r := by
        intro h
        apply hpath.2
        rw [Walk.support_cons]
        exact List.mem_cons_of_mem _ (h ▸ p''.start_mem_support)
      have hr2 := ((hEv r).2 (Or.inl rfl)).2
      have hopos : 0 < G.degree o := (G.degree_pos_iff_exists_adj o).mpr ⟨r, hro.symm⟩
      have hoodd : G.degree o % 2 = 1 := by
        have := (hEv o).not.mpr (by rintro (h | h); exact hor h; exact hoT h)
        omega
      have hdr := delEdge_degree_left G hro
      have hdo' := delEdge_degree_right G hro
      have hdo : ∀ w, w ≠ r → w ≠ o → (delEdge G r o).degree w = G.degree w :=
        fun w h1 h2 => delEdge_degree_of_ne G hro h1 h2
      have hadj' : (delEdge G r o).Adj o y := ⟨hoy, fun h => by
        rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact hor h1
        · exact hyr h2⟩
      have hopos' : 0 < (delEdge G r o).degree o :=
        ((delEdge G r o).degree_pos_iff_exists_adj o).mpr ⟨y, hadj'⟩
      have hE' : evenSet (delEdge G r o) = insert o T := by
        ext w
        rw [mem_evenSet_iff, Finset.mem_insert]
        by_cases hwr : w = r
        · rw [hwr]
          constructor
          · intro h; omega
          · rintro (h | h)
            · exact absurd h hor.symm
            · exact absurd h hrT
        · by_cases hwo : w = o
          · rw [hwo]
            constructor
            · intro _; exact Or.inl rfl
            · intro _; exact ⟨hopos', by omega⟩
          · rw [hdo w hwr hwo, hEv w]
            simp [hwr, hwo]
      have hnr : r ∉ (Walk.cons hoy p'').support := hpath.2
      have htr : ∀ e ∈ (Walk.cons hoy p'').edges, e ∈ (delEdge G r o).edgeSet := by
        intro e he
        rw [delEdge_edgeSet]
        refine ⟨(Walk.cons hoy p'').edges_subset_edgeSet he, ?_⟩
        rintro rfl
        exact hnr ((Walk.cons hoy p'').fst_mem_support_of_mem_edges he)
      obtain ⟨w, hwT, hw⟩ := ih (delEdge G r o) o T hoT hT hE'
        ⟨t, ht, (Walk.cons hoy p'').transfer _ htr, (Walk.isPath_transfer htr).mpr hpath.1,
          by rw [Walk.length_transfer]; simp only [Walk.length_cons] at hp ⊢; omega⟩
      obtain ⟨hS', D', hD'⟩ := hw
      have e' := ends_of_realises hS' hD'
      have hwo : w ≠ o := fun h => hoT (h ▸ hwT)
      have hwr : w ≠ r := fun h => hrT (h ▸ hwT)
      have hD'o : D'.ends o = 2 := by
        rw [e' o]; simp; omega
      obtain ⟨D, -, hDr, hDo, hDoth⟩ := fan_single hro (delEdge_edgeSet G r o) D' (by
        have hempty : Finset.univ.filter
            (fun x => (delEdge G r o).Adj r x ∧ D'.ends x = 0) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          rintro x - ⟨hadjx, hx0⟩
          have hxpos : 0 < (delEdge G r o).degree x :=
            ((delEdge G r o).degree_pos_iff_exists_adj x).mpr ⟨r, hadjx.symm⟩
          rw [e' x] at hx0
          have hxeven : (delEdge G r o).degree x % 2 = 0 := by omega
          have hxE : x ∈ evenSet (delEdge G r o) := mem_evenSet_iff.mpr ⟨hxpos, hxeven⟩
          rw [hE', Finset.mem_insert] at hxE
          rcases hxE with hxo | hxT
          · rw [hxo] at hadjx; exact hadjx.2 rfl
          · exact hadj x hxT hadjx.1
        rw [hempty, Finset.card_empty, hD'o]
        omega)
      refine ⟨w, hwT, pair_subset_evenSet hE hwT, D,
        realises_of (pair_subset_evenSet hE hwT) (fun x => ?_)⟩
      by_cases hxr : x = r
      · rw [hxr, hDr, e' r]
        simp [hor.symm, Ne.symm hwr, hor, hwr] <;> omega
      · by_cases hxo : x = o
        · rw [hxo]
          have := hDo
          rw [hD'o] at this
          simp [hor, Ne.symm hor, hwo, Ne.symm hwo] <;> omega
        · rw [hDoth x hxr hxo, e' x, hdo x hxr hxo]
          simp [hxr, hxo]

/-- **Realisable pairs, `e = 4`** (endpoint-structure, small even sets): in a connected graph
with exactly four even vertices, every even vertex lies in a realisable 2-set. -/
theorem realisable_pair_of_four (G : SimpleGraph W) [DecidableRel G.Adj] (hconn : G.Connected)
    {r : W} (hr : r ∈ evenSet G) (h4 : (evenSet G).card = 4) :
    ∃ w, w ≠ r ∧ w ∈ evenSet G ∧ Realisable G {r, w} := by
  have hT : ((evenSet G).erase r).card = 3 := by rw [Finset.card_erase_of_mem hr, h4]
  have hE : evenSet G = insert r ((evenSet G).erase r) := (Finset.insert_erase hr).symm
  obtain ⟨t, ht⟩ : ((evenSet G).erase r).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q⟩ := hconn.preconnected r t
  obtain ⟨w, hwT, hw⟩ := four_even_pair q.bypass.length G r ((evenSet G).erase r)
    (Finset.notMem_erase r _) hT hE ⟨t, ht, q.bypass, q.bypass_isPath, le_rfl⟩
  exact ⟨w, (Finset.mem_erase.mp hwT).1, (Finset.mem_erase.mp hwT).2, hw⟩

end four

/-! ### BP₃ -/

section bp3

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- **BP₃** (profile form): a connected graph with a leaf and exactly three even vertices
realises some set `S` of at most one even vertex. -/
theorem bp3 (G : SimpleGraph W) [DecidableRel G.Adj] (hconn : G.Connected) {ℓ s : W}
    (hℓ : G.degree ℓ = 1) (hℓs : G.Adj ℓ s) (h3 : (evenSet G).card = 3) :
    ∃ S : Finset W, S.card ≤ 1 ∧ Realisable G S := by
  have hsℓ : s ≠ ℓ := hℓs.ne.symm
  -- `ℓ` is pendant
  have hN : G.neighborFinset ℓ = {s} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨(G.mem_neighborFinset ℓ s).mpr hℓs, fun y hy => ?_⟩
    have hcard : (G.neighborFinset ℓ).card = 1 := by rw [card_neighborFinset_eq_degree, hℓ]
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
    have h1 : y ∈ ({z} : Finset W) := hz ▸ hy
    have h2 : s ∈ ({z} : Finset W) := hz ▸ (G.mem_neighborFinset ℓ s).mpr hℓs
    rw [Finset.mem_singleton] at h1 h2
    rw [h1, h2]
  have hpend : ∀ e ∈ G.edgeSet, ℓ ∈ e → e = s(ℓ, s) := by
    intro e he hle
    induction e using Sym2.inductionOn with
    | hf a b =>
    rw [mem_edgeSet] at he
    rcases Sym2.mem_iff.mp hle with rfl | rfl
    · have : b ∈ G.neighborFinset a := (G.mem_neighborFinset a b).mpr he
      rw [hN, Finset.mem_singleton] at this
      rw [this]
    · have : a ∈ G.neighborFinset b := (G.mem_neighborFinset b a).mpr he.symm
      rw [hN, Finset.mem_singleton] at this
      rw [this, Sym2.eq_swap]
  have hdℓ : (delEdge G ℓ s).degree ℓ = 0 := by
    have := delEdge_degree_left G hℓs; omega
  have hds := delEdge_degree_right G hℓs
  have hdo : ∀ w, w ≠ ℓ → w ≠ s → (delEdge G ℓ s).degree w = G.degree w :=
    fun w h1 h2 => delEdge_degree_of_ne G hℓs h1 h2
  have hℓE : ℓ ∉ evenSet G := by rw [mem_evenSet_iff]; omega
  -- re-append `ℓ` at an end at `s`
  have reappend : ∀ (D₀ : PathDecomp (delEdge G ℓ s)), 0 < D₀.ends s →
      ∃ D : PathDecomp G, ∀ w, D.ends w + (if s = w then 1 else 0) =
        D₀.ends w + (if ℓ = w then 1 else 0) := by
    intro D₀ hpos
    obtain ⟨P, hP, hend⟩ := D₀.exists_end_of_pos hpos
    obtain ⟨D, -, hD⟩ := D₀.append_move (K' := G) (t := s) (u := ℓ)
      (fun h => by
        have := ((delEdge G ℓ s).degree_pos_iff_exists_adj ℓ).mpr ⟨s, h.symm⟩
        omega)
      (fun e => by
        rw [delEdge_edgeSet, Sym2.eq_swap (a := s)]
        constructor
        · intro he
          by_cases h : e = s(ℓ, s)
          · exact Or.inr h
          · exact Or.inl ⟨he, h⟩
        · rintro (⟨he, -⟩ | rfl)
          · exact he
          · exact hℓs)
      hP hend (not_mem_support_of_degree_zero P hdℓ)
    exact ⟨D, hD⟩
  by_cases hsE : s ∈ evenSet G
  · -- the leaf hangs at an even vertex
    have hs := mem_evenSet_iff.mp hsE
    obtain ⟨u, hu⟩ : ((evenSet G).erase s).Nonempty :=
      Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hsE, h3]; omega)
    have huE := (Finset.mem_erase.mp hu).2
    have hus : u ≠ s := (Finset.mem_erase.mp hu).1
    have huℓ : u ≠ ℓ := fun h => hℓE (h ▸ huE)
    have hu2 := (mem_evenSet_iff.mp huE).2
    have hev0 : ∀ w ∈ evenSet (delEdge G ℓ s), w ∈ (evenSet G).erase s := by
      intro w hw
      rw [mem_evenSet_iff] at hw
      by_cases hwℓ : w = ℓ
      · rw [hwℓ] at hw; omega
      · by_cases hws : w = s
        · rw [hws] at hw; omega
        · rw [hdo w hwℓ hws] at hw
          exact Finset.mem_erase.mpr ⟨hws, mem_evenSet_iff.mpr hw⟩
    have hcard : ((evenSet (delEdge G ℓ s)).erase u).card ≤ 1 := by
      have hsub : (evenSet (delEdge G ℓ s)).erase u ⊆ ((evenSet G).erase s).erase u := by
        intro w hw
        rw [Finset.mem_erase] at hw ⊢
        exact ⟨hw.1, hev0 w hw.2⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hu, Finset.card_erase_of_mem hsE, h3] at this
      omega
    obtain ⟨D₀, hD₀w, hD₀u⟩ := two_even (delEdge G ℓ s) (u := u)
      (by rw [hdo u huℓ hus]; exact hu2) hcard
    obtain ⟨D, hD⟩ := reappend D₀ (by rw [hD₀w s hus.symm]; omega)
    rcases hD₀u with h0 | h2
    · refine ⟨∅, by simp, by simp, D, realises_of (by simp) (fun w => ?_)⟩
      have h := hD w
      simp only [Finset.notMem_empty, ite_false, add_zero]
      by_cases hws : w = s
      · rw [hws] at h ⊢
        rw [hD₀w s hus.symm] at h
        simp only [hsℓ, ite_true, ite_false, add_zero] at h
        omega
      · by_cases hwℓ : w = ℓ
        · rw [hwℓ] at h ⊢
          rw [hD₀w ℓ (Ne.symm huℓ)] at h
          simp only [Ne.symm hsℓ, ite_true, ite_false, add_zero] at h
          omega
        · simp only [Ne.symm hws, Ne.symm hwℓ, ite_false, add_zero] at h
          rw [h]
          by_cases hwu : w = u
          · rw [hwu, h0]; omega
          · rw [hD₀w w hwu, hdo w hwℓ hws]
    · refine ⟨{u}, by simp, by simpa using huE, D,
        realises_of (by simpa using huE) (fun w => ?_)⟩
      have h := hD w
      by_cases hws : w = s
      · rw [hws] at h ⊢
        rw [hD₀w s hus.symm] at h
        simp only [hsℓ, ite_true, ite_false, add_zero, Finset.mem_singleton,
          Ne.symm hus] at h ⊢
        omega
      · by_cases hwℓ : w = ℓ
        · rw [hwℓ] at h ⊢
          rw [hD₀w ℓ (Ne.symm huℓ)] at h
          simp only [Ne.symm hsℓ, ite_true, ite_false, add_zero, Finset.mem_singleton,
            Ne.symm huℓ] at h ⊢
          omega
        · simp only [Ne.symm hws, Ne.symm hwℓ, ite_false, add_zero] at h
          rw [h]
          by_cases hwu : w = u
          · rw [hwu, h2]; simp; omega
          · rw [hD₀w w hwu, hdo w hwℓ hws]
            simp [hwu]
  · -- the leaf hangs at an odd vertex
    have hspos : 0 < G.degree s := (G.degree_pos_iff_exists_adj s).mpr ⟨ℓ, hℓs.symm⟩
    have hsodd : G.degree s % 2 = 1 := by
      rw [mem_evenSet_iff] at hsE; omega
    obtain ⟨t, ht⟩ : (evenSet G).Nonempty := Finset.card_pos.mp (by omega)
    have hts : t ≠ s := fun h => hsE (h ▸ ht)
    have htℓ : t ≠ ℓ := fun h => hℓE (h ▸ ht)
    obtain ⟨q⟩ := hconn.preconnected s t
    have hp : q.bypass.IsPath := q.bypass_isPath
    have hlen : 0 < q.bypass.length := by
      by_contra h0
      exact hts (Walk.eq_of_length_eq_zero (p := q.bypass) (by omega)).symm
    have hℓp : ℓ ∉ q.bypass.support := by
      intro hm
      rcases GPath.end_of_pendant ⟨s, t, q.bypass, hp, hlen⟩ hpend hm with h | h
      · exact hsℓ h
      · exact htℓ h
    have htr : ∀ e ∈ q.bypass.edges, e ∈ (delEdge G ℓ s).edgeSet := by
      intro e he
      rw [delEdge_edgeSet]
      refine ⟨q.bypass.edges_subset_edgeSet he, ?_⟩
      rintro rfl
      exact hℓp (q.bypass.fst_mem_support_of_mem_edges he)
    obtain ⟨y, hsy, p', hpeq⟩ := Walk.exists_eq_cons_of_length_pos q.bypass hlen
    have hyℓ : y ≠ ℓ := by
      intro h
      apply hℓp
      rw [hpeq, Walk.support_cons]
      exact List.mem_cons_of_mem _ (h ▸ p'.start_mem_support)
    have hs0pos : 0 < (delEdge G ℓ s).degree s :=
      ((delEdge G ℓ s).degree_pos_iff_exists_adj s).mpr ⟨y, hsy, fun h => by
        rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact hsℓ h1
        · exact hyℓ h2⟩
    have hE0 : evenSet (delEdge G ℓ s) = insert s (evenSet G) := by
      ext w
      rw [mem_evenSet_iff, Finset.mem_insert]
      by_cases hwℓ : w = ℓ
      · rw [hwℓ, hdℓ]
        constructor
        · intro h; omega
        · rintro (h | h)
          · exact absurd h.symm hsℓ
          · exact absurd h hℓE
      · by_cases hws : w = s
        · rw [hws]
          constructor
          · intro _; exact Or.inl rfl
          · intro _; exact ⟨hs0pos, by omega⟩
        · rw [hdo w hwℓ hws, ← mem_evenSet_iff]
          simp [hws]
    obtain ⟨w, hwE, hw⟩ := four_even_pair q.bypass.length (delEdge G ℓ s) s (evenSet G) hsE
      h3 hE0 ⟨t, ht, q.bypass.transfer _ htr, (Walk.isPath_transfer htr).mpr hp,
        by rw [Walk.length_transfer]⟩
    obtain ⟨hS₀, D₀, hD₀⟩ := hw
    have e₀ := ends_of_realises hS₀ hD₀
    have hws : w ≠ s := fun h => hsE (h ▸ hwE)
    have hwℓ : w ≠ ℓ := fun h => hℓE (h ▸ hwE)
    obtain ⟨D, hD⟩ := reappend D₀ (by rw [e₀ s]; simp)
    refine ⟨{w}, by simp, by simpa using hwE, D, realises_of (by simpa using hwE) (fun x => ?_)⟩
    have h := hD x
    rw [e₀ x] at h
    by_cases hxs : x = s
    · rw [hxs] at h ⊢
      simp [hsℓ, Ne.symm hws] at h ⊢
      omega
    · by_cases hxℓ : x = ℓ
      · rw [hxℓ] at h ⊢
        simp [Ne.symm hsℓ, Ne.symm hwℓ, hℓ] at h ⊢
        omega
      · simp only [Finset.mem_insert, Finset.mem_singleton, hxs, false_or, Ne.symm hxs,
          Ne.symm hxℓ, ite_false, add_zero] at h ⊢
        rw [h, hdo x hxℓ hxs]

/-- **BP₃**: a connected graph of order `N` with a leaf and exactly three even vertices has a
path decomposition into at most `⌊N/2⌋` paths. -/
theorem bp3_pathNumber (G : SimpleGraph W) [DecidableRel G.Adj] (hconn : G.Connected) {ℓ s : W}
    (hℓ : G.degree ℓ = 1) (hℓs : G.Adj ℓ s) (h3 : (evenSet G).card = 3) :
    pathNumber G ≤ Fintype.card W / 2 := by
  obtain ⟨S, hS, hS', D, hD⟩ := bp3 G hconn hℓ hℓs h3
  have hsize := Realises.size_eq hS' hD
  have h1 := pathNumber_le D
  have hsℓ : s ≠ ℓ := hℓs.ne.symm
  have hposall : ∀ v, 0 < G.degree v := by
    intro v
    obtain ⟨x, hxv⟩ : ∃ x, x ≠ v := by
      by_cases h : ℓ = v
      · exact ⟨s, fun h' => hsℓ (h'.trans h.symm)⟩
      · exact ⟨ℓ, h⟩
    obtain ⟨q⟩ := hconn.preconnected v x
    obtain ⟨z, hvz, -, -⟩ := Walk.exists_eq_cons_of_length_pos q (by
      by_contra h0
      exact hxv (Walk.eq_of_length_eq_zero (p := q) (by omega)).symm)
    exact (G.degree_pos_iff_exists_adj v).mpr ⟨z, hvz⟩
  have hsum := card_oddSet_add_card_evenSet (G := G) hposall
  obtain ⟨k, hk⟩ := G.even_card_odd_degree_vertices
  unfold oddSet at hsize hsum
  omega

end bp3

end Gallai
