import GallaiLean.FanSupport
import GallaiLean.Flower
import GallaiLean.L1Star
import GallaiLean.EMCFour
import GallaiLean.ThreeConnected
import GallaiLean.Lovasz

/-!
# Fan's lemma at equality: protected blanks

Manuscript `manuscripts/tight-fan/tight-fan.tex`.

Four lines of work (L∞, the blocked case of L₁*, EE with two common neighbours, PTM's base step)
stop at a Lovász Case I step `t → w` in which a protected vertex `p` (the end `c`, the far end of
the leaf path, or the endless short end) is a *blank* neighbour of the Fan target `w`: in the leaf
graph `b(t) = 1 = |Z(w)|`, so Fan's inequality is an equality. This file proves the refined form of
Fan's counting that handles such blanks, and the negative facts about the flower move.

## Main results

* **`fan_exists_chain_protected`** (Fan's lemma with protected blanks). A blank that no chain
  vertex reaches as a predecessor does not count against the supply: if
  `#{w ∈ N(u) : ends w = 0, w ∉ B} < ∑_{t ∈ T} ends t` and no vertex of `T ∪ N(u)` has a vertex of
  `B` as its predecessor of `u`, a chain exists, and it avoids `B`.
* **`fan_grouped_protected_supp`**, **`fan_single_protected_supp`**: the corresponding transfers,
  with vertex sets (every new path lies in an old path together with `u`).
* **`fanPred_unique`**: in a decomposition with at most one end at `x`, the predecessor of `u`
  read from `x` is unique. So on Lovász decompositions Fan's chain is *forced*.
* **A flower cannot be the last move of a Lovász-type argument**: `hub_cycles_card_le_one`
  (with at most one end everywhere, the hypothesis of `hub_cycles` forces `|T| ≤ 1`),
  `flower_decomp_not_le_one`, `flower_decomp_rest_not_le_one` (the recombined decomposition has
  two ends on the transversal).
* `l1_tight_transfer` (the tight case of `L₁*`), `lInfty_of_l1Blocked` (L∞ from the blocked case),
  `test1_deg_four` (spine Test 1 at degree four, a Lean packaging via `emc_four` of the known case,
  terminal-matching Remark 7.3).
-/

open SimpleGraph

namespace Gallai

universe v

variable {U : Type v}

section protected_chain

variable [DecidableEq U] {K : SimpleGraph U}

omit [DecidableEq U] in
/-- Along a `FanPre` list whose head is in `T` or adjacent to `u`, every later vertex is adjacent to
`u` and, if no vertex of `T ∪ N(u)` has a vertex of `B` as predecessor, lies outside `B`. -/
theorem fanPre_protect {D : PathDecomp K} {u : U} {T B : Finset U}
    (hB : ∀ x z, (x ∈ T ∨ K.Adj x u) → FanPred D u x z → z ∉ B) :
    ∀ (x : U) (l : List U), (x ∈ T ∨ K.Adj x u) → FanPre D u (x :: l) →
      ∀ y ∈ l, K.Adj y u ∧ y ∉ B
  | _, [], _, _ => fun y hy => absurd hy List.not_mem_nil
  | x, y :: rest, hx, hpre => by
    obtain ⟨hp, hpre'⟩ := hpre
    have hyu : K.Adj y u := FanPred.adj hp
    have hyB : y ∉ B := hB x y hx hp
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact ⟨hyu, hyB⟩
    · exact fanPre_protect hB y rest (Or.inr hyu) hpre' w hw

variable [Fintype U] [DecidableRel K.Adj]

/-- **Fan's lemma with protected blanks.** Let `T` be a set of non-neighbours of `u` and `B` a set
of *protected* vertices, disjoint from `T`, such that no vertex of `T ∪ N(u)` has a vertex of `B`
as its predecessor of `u` (`FanPred`). If the blanks of `u` outside `B` are fewer than the ends on
`T`, some `t ∈ T` starts a chain, and the chain avoids `B`.

This is Fan's counting (`fan_exists_chain`) with the blanks in `B` discounted: the reachable set
never meets `B`. With `B = ∅` it is `fan_exists_chain`. -/
theorem fan_exists_chain_protected (D : PathDecomp K) (u : U) (T B : Finset U) (huT : u ∉ T)
    (hT : ∀ t ∈ T, ¬ K.Adj t u) (hBT : ∀ t ∈ T, t ∉ B)
    (hB : ∀ x z, (x ∈ T ∨ K.Adj x u) → FanPred D u x z → z ∉ B)
    (hsum : (Finset.univ.filter (fun w => K.Adj u w ∧ D.ends w = 0 ∧ w ∉ B)).card <
      ∑ t ∈ T, D.ends t) :
    ∃ t ∈ T, ∃ xs, (t :: xs).Nodup ∧ FanChain D u (t :: xs) ∧ ∀ y ∈ t :: xs, y ∉ B := by
  classical
  by_contra hno
  let Reach : U → Prop := fun x => ∃ t ∈ T, ∃ xs : List U, (t :: xs).Nodup ∧
    FanPre D u (t :: xs) ∧ (t :: xs).getLast? = some x
  -- every vertex of a `FanPre` list from `T` avoids `B`
  have hlistB : ∀ t ∈ T, ∀ xs : List U, FanPre D u (t :: xs) → ∀ y ∈ t :: xs, y ∉ B := by
    intro t ht xs hpre y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hBT y ht
    · exact (fanPre_protect hB t xs (Or.inl ht) hpre y hy).2
  have hnoav : ∀ x, Reach x → ¬ FanAvoid D u x := by
    rintro x ⟨t, ht, xs, hnd, hpre, hlast⟩ hav
    exact hno ⟨t, ht, xs, hnd, ⟨hpre, x, hlast, hav⟩, hlistB t ht xs hpre⟩
  let R : Finset U := Finset.univ.filter Reach
  have hTR : T ⊆ R := fun t ht =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ht, [], by simp, trivial, rfl⟩
  have hRB : ∀ x ∈ R, x ∉ B := by
    intro x hx
    obtain ⟨t, ht, xs, -, hpre, hlast⟩ := (Finset.mem_filter.mp hx).2
    exact hlistB t ht xs hpre x (List.mem_of_getLast? hlast)
  have hclos : ∀ x z, x ∈ R → FanPred D u x z → z ∈ R := by
    intro x z hx hp
    obtain ⟨t, ht, xs, hnd, hpre, hlast⟩ := (Finset.mem_filter.mp hx).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    by_cases hz : z ∈ t :: xs
    · obtain ⟨L₁, L₂, hL⟩ := List.append_of_mem hz
      cases L₁ with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hL
        obtain ⟨rfl, -⟩ := hL
        exact ⟨t, ht, [], by simp, trivial, rfl⟩
      | cons a L₁' =>
        simp only [List.cons_append, List.cons.injEq] at hL
        obtain ⟨-, hxs⟩ := hL
        refine ⟨t, ht, L₁' ++ [z], ?_, ?_, ?_⟩
        · have hsub : (t :: (L₁' ++ [z])).Sublist (t :: xs) := by
            rw [hxs]
            exact List.Sublist.cons_cons t
              (List.Sublist.append_left (List.singleton_sublist.mpr List.mem_cons_self) L₁')
          exact hnd.sublist hsub
        · have := FanPre.prefix (t :: L₁') z L₂ (by rw [List.cons_append, ← hxs]; exact hpre)
          simpa using this
        · rw [← List.cons_append, List.getLast?_concat]
    · refine ⟨t, ht, xs ++ [z], ?_, ?_, by rw [← List.cons_append, List.getLast?_concat]⟩
      · rw [← List.cons_append, List.nodup_append]
        refine ⟨hnd, List.nodup_singleton z, ?_⟩
        intro a ha b hb hab
        rw [List.mem_singleton] at hb
        subst hb hab
        exact hz ha
      · have := FanPre.snoc (t :: xs) x z hpre hlast hp
        simpa using this
  have hRadj : ∀ x ∈ R, x ∈ T ∨ K.Adj x u := by
    intro x hx
    obtain ⟨t, ht, xs, -, hpre, hlast⟩ := (Finset.mem_filter.mp hx).2
    rcases FanPre.last (t :: xs) x hpre hlast with h | ⟨w, hw⟩
    · simp only [List.head?_cons, Option.some.injEq] at h
      exact Or.inl (h ▸ ht)
    · exact Or.inr (FanPred.adj hw)
  have huR : u ∉ R := fun hu => by
    rcases hRadj u hu with h | h
    · exact huT h
    · exact K.loopless.irrefl u h
  have hthru : ∀ P ∈ D.paths, ∀ x ∈ R, (P.src = x ∨ P.tgt = x) → u ∈ P.walk.support := by
    intro P hP x hx hend
    by_contra hu
    exact hnoav x (Finset.mem_filter.mp hx).2 ⟨P, hP, hend, hu⟩
  let p : Sym2 U → Bool := fun e => decide (u ∈ e ∧ ∃ z ∈ R, z ∈ e)
  have hper : ∀ P ∈ D.paths,
      (if P.src ∈ R then 1 else 0) + (if P.tgt ∈ R then 1 else 0) ≤ P.edges.countP p := by
    intro P hP
    have hnd : P.edges.Nodup := P.isPath.isTrail.edges_nodup
    have hsrc : P.src ∈ R → ∃ d ∈ P.walk.darts, d.snd = u ∧ p d.edge = true := by
      intro hs
      have hu := hthru P hP _ hs (Or.inl rfl)
      have hne : u ≠ P.src := fun h => huR (h ▸ hs)
      obtain ⟨d, hd, hdu⟩ := Walk.exists_dart_snd_eq P.walk hu hne
      have hinf : [d.fst, u] <:+: P.walk.support := by
        rw [← hdu]; exact Walk.mem_darts_iff_fst_snd_infix_support.mp hd
      have hzR : d.fst ∈ R := hclos _ _ hs ⟨P, hP, Or.inl ⟨rfl, hinf⟩⟩
      refine ⟨d, hd, hdu, ?_⟩
      simp only [p, decide_eq_true_eq, Dart.edge, Sym2.mem_iff]
      exact ⟨Or.inr hdu.symm, d.fst, hzR, Or.inl rfl⟩
    have htgt : P.tgt ∈ R → ∃ d ∈ P.walk.darts, d.fst = u ∧ p d.edge = true := by
      intro hs
      have hu := hthru P hP _ hs (Or.inr rfl)
      have hne : u ≠ P.tgt := fun h => huR (h ▸ hs)
      obtain ⟨d, hd, hdu⟩ := Walk.exists_dart_fst_eq P.walk hu hne
      have hinf : [u, d.snd] <:+: P.walk.support := by
        rw [← hdu]; exact Walk.mem_darts_iff_fst_snd_infix_support.mp hd
      have hzR : d.snd ∈ R := hclos _ _ hs ⟨P, hP, Or.inr ⟨rfl, hinf⟩⟩
      refine ⟨d, hd, hdu, ?_⟩
      simp only [p, decide_eq_true_eq, Dart.edge, Sym2.mem_iff]
      exact ⟨Or.inl hdu.symm, d.snd, hzR, Or.inr rfl⟩
    have hmem : ∀ d ∈ P.walk.darts, d.edge ∈ P.edges := fun d hd =>
      List.mem_map_of_mem hd
    by_cases hs : P.src ∈ R <;> by_cases ht : P.tgt ∈ R
    · obtain ⟨d, hd, hdu, hpd⟩ := hsrc hs
      obtain ⟨d', hd', hdu', hpd'⟩ := htgt ht
      have hne : d.edge ≠ d'.edge := by
        intro h
        have := List.inj_on_of_nodup_map hnd hd hd' h
        subst this
        have hadj : K.Adj d.fst d.snd := d.adj
        rw [hdu, hdu'] at hadj
        exact K.loopless.irrefl u hadj
      have := two_le_countP hnd p (hmem d hd) (hmem d' hd') hne hpd hpd'
      simp only [hs, ht, ite_true]
      omega
    · obtain ⟨d, hd, -, hpd⟩ := hsrc hs
      have := List.countP_pos_iff.mpr ⟨d.edge, hmem d hd, hpd⟩
      simp only [hs, ht, ite_true, ite_false]
      omega
    · obtain ⟨d, hd, -, hpd⟩ := htgt ht
      have := List.countP_pos_iff.mpr ⟨d.edge, hmem d hd, hpd⟩
      simp only [hs, ht, ite_true, ite_false]
      omega
    · simp [hs, ht]
  let NR : Finset U := R.filter (fun z => K.Adj u z)
  have hcount : (D.paths.flatMap GPath.edges).countP p ≤ NR.card := by
    rw [List.countP_eq_length_filter,
      ← List.toFinset_card_of_nodup (D.nodup_edges.filter p)]
    refine (Finset.card_le_card ?_).trans (Finset.card_image_le (f := fun z => s(z, u)))
    intro e he
    rw [List.mem_toFinset, List.mem_filter] at he
    obtain ⟨heD, hpe⟩ := he
    simp only [p, decide_eq_true_eq] at hpe
    obtain ⟨hue, z, hzR, hze⟩ := hpe
    have hzu : z ≠ u := fun h => huR (h ▸ hzR)
    have he' : e = s(z, u) := (Sym2.mem_and_mem_iff hzu).mp ⟨hze, hue⟩
    have heK : e ∈ K.edgeSet := (D.covers e).2 heD
    rw [he'] at heK
    rw [Finset.mem_image]
    exact ⟨z, Finset.mem_filter.mpr ⟨hzR, (K.mem_edgeSet.mp heK).symm⟩, he'.symm⟩
  have hR : ∑ x ∈ R, D.ends x ≤ NR.card := by
    rw [sum_ends_eq]
    have hc : (D.paths.map (fun P => P.edges.countP p)).sum =
        (D.paths.flatMap GPath.edges).countP p := by
      rw [List.countP_flatMap]; rfl
    calc _ ≤ (D.paths.map (fun P => P.edges.countP p)).sum := sum_map_le_sum_map _ _ _ hper
      _ = _ := hc
      _ ≤ NR.card := hcount
  have hdisj : Disjoint T NR := by
    rw [Finset.disjoint_left]
    intro t ht htN
    exact hT t ht (Finset.mem_filter.mp htN).2.symm
  have h1 : ∑ t ∈ T, D.ends t + ∑ w ∈ NR, D.ends w ≤ ∑ x ∈ R, D.ends x := by
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset (Finset.union_subset hTR (Finset.filter_subset _ _))
  have hkey : ∀ S : Finset U,
      S.card ≤ ∑ w ∈ S, D.ends w + (S.filter (fun w => D.ends w = 0)).card := by
    intro S
    rw [Finset.card_filter, ← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro w _
    split_ifs <;> omega
  have h2 := hkey NR
  -- the only change from `fan_exists_chain`: the blanks met by `R` avoid `B`
  have h3 : (NR.filter (fun w => D.ends w = 0)).card ≤
      (Finset.univ.filter (fun w => K.Adj u w ∧ D.ends w = 0 ∧ w ∉ B)).card := by
    apply Finset.card_le_card
    intro w hw
    simp only [NR, Finset.mem_filter] at hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hw.1.2, hw.2, hRB w hw.1.1⟩
  omega

/-- **Fan's grouped transfer with protected blanks**, recording supports. As `fan_grouped_supp`,
with the blanks in `B` discounted under the reachability hypothesis `hB`. The ends change only at
`t` and `u`; in particular the vertices of `B ∖ {u}` keep their end counts. -/
theorem fan_grouped_protected_supp (D : PathDecomp K) (u : U) (T B : Finset U) (huT : u ∉ T)
    (hT : ∀ t ∈ T, ¬ K.Adj t u) (hBT : ∀ t ∈ T, t ∉ B)
    (hB : ∀ x z, (x ∈ T ∨ K.Adj x u) → FanPred D u x z → z ∉ B)
    (hsum : (Finset.univ.filter (fun w => K.Adj u w ∧ D.ends w = 0 ∧ w ∉ B)).card <
      ∑ t ∈ T, D.ends t) :
    ∃ t ∈ T, ∀ K' : SimpleGraph U, (∀ e, e ∈ K'.edgeSet ↔ e ∈ K.edgeSet ∨ e = s(t, u)) →
      ∃ D' : PathDecomp K', D'.size = D.size ∧
        (∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if u = w then 1 else 0)) ∧
        ∀ Q' ∈ D'.paths, ∃ Q ∈ D.paths, ∀ x ∈ Q'.walk.support, x ∈ Q.walk.support ∨ x = u := by
  obtain ⟨t, ht, xs, hnd, hch, -⟩ := fan_exists_chain_protected D u T B huT hT hBT hB hsum
  exact ⟨t, ht, fun K' hK' =>
    fan_exec_supp u xs D t hnd hch (fun h => huT (h ▸ ht)) (hT t ht) K' hK'⟩

/-- **Fan's single transfer at equality with a protected blank.** Let `uv ∈ E(G)`, `G' = G − uv`,
and `D'` a decomposition of `G'`. Let `B` be a set of protected vertices with `v ∉ B`, such that no
vertex of `{v} ∪ N_{G'}(u)` has a vertex of `B` as its predecessor of `u`. If
`ends v > #{w ∈ N_{G'}(u) : ends w = 0, w ∉ B}`, the conclusion of `fan_single_supp` holds.

The typical use: `ends v = 1`, and the only blank of `u` is the protected vertex `p`, so Fan's
inequality is an equality (`1 = |Z(u)|`). The transfer still goes through provided no vertex of
`{v} ∪ N(u)` has `p` as its predecessor of `u` (when every vertex has at most one end: the end of
the path through `pu` on `p`'s side is not in `{v} ∪ N(u)`). The sharper condition "the forced
chain does not reach `p`" is manuscript Corollary 2.3(2), not formalised. -/
theorem fan_single_protected_supp {G G' : SimpleGraph U} [DecidableRel G'.Adj] {u v : U}
    (huv : G.Adj u v) (hG' : ∀ e, e ∈ G'.edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(u, v))
    (D' : PathDecomp G') (B : Finset U) (hvB : v ∉ B)
    (hB : ∀ x z, (x = v ∨ G'.Adj x u) → FanPred D' u x z → z ∉ B)
    (h : (Finset.univ.filter (fun w => G'.Adj u w ∧ D'.ends w = 0 ∧ w ∉ B)).card < D'.ends v) :
    ∃ D : PathDecomp G, D.size = D'.size ∧ D.ends u = D'.ends u + 1 ∧
      D.ends v + 1 = D'.ends v ∧ (∀ w, w ≠ u → w ≠ v → D.ends w = D'.ends w) ∧
      ∀ Q ∈ D.paths, ∃ Q' ∈ D'.paths, ∀ x ∈ Q.walk.support, x ∈ Q'.walk.support ∨ x = u := by
  have huv' : u ≠ v := huv.ne
  obtain ⟨t, ht, hK⟩ := fan_grouped_protected_supp D' u {v} B (by simpa using huv')
    (by
      intro t ht
      rw [Finset.mem_singleton] at ht
      subst ht
      rw [← mem_edgeSet, hG']
      rintro ⟨-, h⟩
      exact h Sym2.eq_swap)
    (by intro t ht; rw [Finset.mem_singleton] at ht; subst ht; exact hvB)
    (by
      intro x z hx hp
      refine hB x z ?_ hp
      rcases hx with hx | hx
      · exact Or.inl (Finset.mem_singleton.mp hx)
      · exact Or.inr hx)
    (by simpa using h)
  obtain rfl : t = v := Finset.mem_singleton.mp ht
  obtain ⟨D, hs, he, hcovD⟩ := hK G (by
    intro e
    rw [hG' e]
    have hvu : s(t, u) = s(u, t) := Sym2.eq_swap
    have : s(u, t) ∈ G.edgeSet := huv
    constructor
    · intro he
      by_cases h' : e = s(u, t)
      · exact Or.inr (h'.trans hvu.symm)
      · exact Or.inl ⟨he, h'⟩
    · rintro (⟨he, -⟩ | rfl)
      · exact he
      · rw [hvu]; exact this)
  refine ⟨D, hs, ?_, ?_, ?_, hcovD⟩
  · have := he u
    simp only [Ne.symm huv', ite_false, ite_true, add_zero] at this
    omega
  · have := he t
    simp only [huv', ite_false, ite_true, add_zero] at this
    omega
  · intro w hwu hwt
    have := he w
    simp only [Ne.symm hwu, Ne.symm hwt, ite_false, add_zero] at this
    exact this

end protected_chain

section l1tight

variable {W : Type v} [Fintype W] [DecidableEq W]

/-- **The tight transfer for `L₁*`** (manuscript Theorem 3.3). Let `g` be the even vertex of `G`,
`c` odd, and `x ∈ N(g)` with `x ≠ c` and `x ∉ A` (no hypothesis `c ∉ N(g)` is needed); typically
`x ∈ N(c)`, which is the blocked residual of `L₁*` where Lemma 2.4 of the l1star manuscript
(protected transfer) does not apply. Let `D₃` be
a decomposition of the leaf graph `apex (G − gx) {c}` (a leaf `none` hung at `c`, so that `c` has
no end) with the Lovász end counts of `G − gx` elsewhere, in which the leaf path avoids `A`.

In the leaf graph, `c` is a blank neighbour of the Fan target `x`: Fan's inequality for restoring
`gx` is the equality `b(g) = 1 = |Z(x)|`. If no vertex of `{g} ∪ N(x)` has `c` as its
predecessor of `x` (`hB`: the path through `cx`, read from its end on `c`'s side, is never reached
by the chain), the transfer still goes through, and `(G, c, A)` is good. -/
theorem l1_tight_transfer (G : SimpleGraph W) [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1)
    {g c x : W} (hg : g ∈ evenSet G) (hgx : G.Adj g x) (hxc : x ≠ c)
    (hc : G.degree c % 2 = 1) {A : Finset W} (hxA : x ∉ A)
    (D₃ : PathDecomp (apex (delEdge G g x) {c}))
    (hD₃ : ∀ w, w ≠ c → D₃.ends (some w) = (delEdge G g x).degree w % 2)
    (hD₃c : D₃.ends (some c) = 0)
    (hsep : ∀ P ∈ D₃.paths, (none : Option W) ∈ P.walk.support →
      ∀ a ∈ A, some a ∉ P.walk.support)
    (hB : ∀ y z, (y = some g ∨ (apex (delEdge G g x) {c}).Adj y (some x)) →
      FanPred D₃ (some x) y z → z ≠ some c) :
    AvoidDecomp G c A := by
  classical
  have hgx' : g ≠ x := hgx.ne
  have huniq : ∀ v ∈ evenSet G, v = g := fun v hv => Finset.card_le_one.mp hev v hv g hg
  have hodd : ∀ v, v ≠ g → 0 < G.degree v → G.degree v % 2 = 1 := by
    intro v hvg hpos
    have : v ∉ evenSet G := fun h => hvg (huniq v h)
    rw [mem_evenSet_iff] at this
    omega
  have hgd := mem_evenSet_iff.mp hg
  have hcg : c ≠ g := fun h => by rw [h] at hc; omega
  have hdeg := delEdge_degree G hgx
  have hK : (apex G {c}).Adj (some x) (some g) := by
    rw [apex_adj_some_some]; exact hgx.symm
  have hD₃g : D₃.ends (some g) = 1 := by
    rw [hD₃ g hcg.symm]
    have := hdeg g
    simp only [hgx', ite_true, ite_false] at this
    omega
  have hcount : (Finset.univ.filter (fun v => (apex (delEdge G g x) {c}).Adj (some x) v ∧
      D₃.ends v = 0 ∧ v ∉ ({some c} : Finset (Option W)))).card < D₃.ends (some g) := by
    have hempty : Finset.univ.filter (fun v => (apex (delEdge G g x) {c}).Adj (some x) v ∧
        D₃.ends v = 0 ∧ v ∉ ({some c} : Finset (Option W))) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
      rw [Finset.mem_filter] at hv
      obtain ⟨-, hadj, h0, hvB⟩ := hv
      cases v with
      | none =>
        rw [apex_adj_some_none, Finset.mem_singleton] at hadj
        exact hxc hadj
      | some w =>
        rw [apex_adj_some_some] at hadj
        have hwc : w ≠ c := fun h => hvB (by simp [h])
        have hwg : w ≠ g := fun h => hadj.2 (by rw [h, Sym2.eq_swap])
        have hwx : w ≠ x := hadj.ne.symm
        rw [hD₃ w hwc] at h0
        have hdw := hdeg w
        simp only [hwg, hwx, ite_false, add_zero] at hdw
        have := hodd w hwg ((G.degree_pos_iff_exists_adj w).mpr ⟨x, hadj.1.symm⟩)
        omega
    rw [hempty, Finset.card_empty, hD₃g]
    omega
  obtain ⟨DH, -, hDHx, hDHg, hDHrest, hcovH⟩ :=
    fan_single_protected_supp (G := apex G {c}) hK (apex_delEdge_edge_iff G {c} g x) D₃
      {some c} (by simp [hcg.symm])
      (fun y z hy hp hz => hB y z hy hp (Finset.mem_singleton.mp hz)) hcount
  have hsepH : ∀ Q ∈ DH.paths, (none : Option W) ∈ Q.walk.support →
      ∀ a ∈ A, some a ∉ Q.walk.support := by
    intro Q hQ hn a ha hx
    obtain ⟨Q', hQ', hsub⟩ := hcovH Q hQ
    have hn' : (none : Option W) ∈ Q'.walk.support :=
      (hsub none hn).resolve_right (by simp)
    rcases hsub (some a) hx with h | h
    · exact hsep Q' hQ' hn' a ha h
    · rw [Option.some.injEq] at h
      exact hxA (h ▸ ha)
  refine avoid_of_apexSep G hc DH (fun w hwc => ?_) ?_ hsepH
  · by_cases hwx : w = x
    · subst hwx
      rw [hDHx, hD₃ w hwc]
      have := hdeg w
      simp only [hgx'.symm, ite_true, ite_false] at this
      have := hodd w hgx'.symm ((G.degree_pos_iff_exists_adj w).mpr ⟨g, hgx.symm⟩)
      omega
    · by_cases hwg : w = g
      · subst hwg
        rw [hD₃g] at hDHg
        have : DH.ends (some w) = 0 := by omega
        rw [this, hgd.2]
      · rw [hDHrest (some w) (by simp [hwx]) (by simp [hwg]), hD₃ w hwc]
        have := hdeg w
        simp only [hwg, hwx, ite_false, add_zero] at this
        rw [this]
  · rw [hDHrest (some c) (by simp [hxc.symm]) (by simp [hcg]), hD₃c]

end l1tight

/-! ### Flowers do not produce Lovász decompositions -/

section flowers

variable {V : Type v} [DecidableEq V]

/-- **The hub hypothesis is trivial for decompositions with at most one end everywhere.** If `D`
satisfies the hypothesis of `hub_cycles` (`|T|` ends at the hub `s`, one at each vertex of `T`,
none elsewhere) and has at most one end at every vertex, then `|T| ≤ 1`: the flower has at most
one petal. -/
theorem hub_cycles_card_le_one {H : SimpleGraph V} (D : PathDecomp H) (s : V) (T : Finset V)
    (hends : ∀ v, D.ends v = if v = s then T.card else if v ∈ T then 1 else 0)
    (hle : ∀ v, D.ends v ≤ 1) : T.card ≤ 1 := by
  have := hends s
  simp only [ite_true] at this
  rw [← this]
  exact hle s

/-- **The flower recombination has two ends on the transversal.** Any decomposition with the end
counts produced by `flower_decomp` (two ends at every vertex of the transversal `L`, none elsewhere)
has a vertex with two ends; so it is never a decomposition with at most one end at each vertex,
in particular never a Lovász decomposition. -/
theorem flower_decomp_not_le_one {G : SimpleGraph V} (L : TPath V) (D : PathDecomp G)
    (hD : ∀ v, D.ends v = if v ∈ L.walk.support then 2 else 0) : ¬ ∀ v, D.ends v ≤ 1 := by
  intro h
  have := h L.src
  rw [hD] at this
  simp only [L.walk.start_mem_support, ite_true] at this
  omega

/-- The same for `flower_decomp_rest` (receipt-or-flower, with untouched paths): the recombined
decomposition has at least two ends at every vertex of `L`. -/
theorem flower_decomp_rest_not_le_one {G : SimpleGraph V} (L : TPath V) (rest : List (TPath V))
    (D : PathDecomp G)
    (hD : ∀ v, D.ends v = (if v ∈ L.walk.support then 2 else 0) + endsL rest v) :
    ¬ ∀ v, D.ends v ≤ 1 := by
  intro h
  have := h L.src
  rw [hD] at this
  simp only [L.walk.start_mem_support, ite_true] at this
  omega

end flowers

/-! ### L∞ from the blocked case of `L₁*` -/

section linfty

universe w

/-- **Conjecture L∞** (route descent, §V.4c; l1star Proposition 3.1): in a graph with no vertex
of positive even degree, every odd `c` has a Lovász decomposition whose path ending at `c` lies in
the closed neighbourhood `N[c]`. -/
def LInfty : Prop :=
  ∀ (V : Type w) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (evenSet G).card = 0 → ∀ c : V, G.degree c % 2 = 1 →
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∀ P ∈ D.paths, (P.src = c ∨ P.tgt = c) → ∀ x ∈ P.walk.support, x = c ∨ G.Adj c x

/-- `L₁*` (general form) implies L∞: take `A = V ∖ N[c]`, which is admissible when there is no
even vertex. -/
theorem lInfty_of_l1StarGen (h : L1StarGen.{w}) : LInfty.{w} := by
  intro V _ _ G _ hev c hc
  classical
  let A : Finset V := Finset.univ.filter (fun a => a ≠ c ∧ ¬ G.Adj c a)
  have hA : Admissible G c A := by
    intro a ha
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    refine ⟨ha.1, ha.2, fun g hg => ?_⟩
    rw [Finset.card_eq_zero] at hev
    rw [hev] at hg
    exact absurd hg (Finset.notMem_empty g)
  obtain ⟨D, hD, hav⟩ := h V G (by rw [hev]; omega) c hc A hA
  refine ⟨D, hD, fun P hP hend x hx => ?_⟩
  by_contra hne
  rw [not_or] at hne
  exact hav P hP hend x (by simp [A, hne.1, hne.2]) hx

/-- **The three Lovász-side residuals are one statement.** The blocked case of `L₁*` implies
L∞ (here) and EE (`ee_of_l1Blocked`). -/
theorem lInfty_of_l1Blocked (hB : L1Blocked.{w}) : LInfty.{w} :=
  lInfty_of_l1StarGen (l1starGen_of_blocked hB)

end linfty

/-! ### Spine Test 1 at `d(z) = 4` without PTM -/

section test1four

variable {V : Type v} [Fintype V] [DecidableEq V]

/-- **Spine Test 1 at a vertex of degree four.** If `z` is the only even vertex of `J`, `d(z) = 4`,
and `J − z` is connected, then `Test1 J z` holds: for every `r ∈ N(z)`, `J − z` has a partition
into `(|J| − 1)/2` paths with two ends at `r`.

`J − z` has exactly four even vertices, the neighbours of `z`, and by `emc_four` (two-step
faithful descent, from Lovász and Fan alone) some pair `{r, x}` of them is realisable. This does
not use the terminal-matching property PTM₂, so PTM's base failures do not obstruct Test 1 at
`d(z) = 4`. -/
theorem test1_deg_four (J : SimpleGraph V) [DecidableRel J.Adj] (z : V) (h4 : J.degree z = 4)
    (hconn : (delVert J z).Connected) : Test1 J z := by
  classical
  intro hz r hr
  let H := delVert J z
  let r' : {v | v ≠ z} := ⟨r, hr.ne'⟩
  -- degrees in `J − z`
  have hdeg : ∀ v : {v | v ≠ z}, H.degree v + (if J.Adj v z then 1 else 0) = J.degree v :=
    fun v => delVert_degree z v
  have hoddJ : ∀ v : V, v ≠ z → Odd (J.degree v) := fun v hv =>
    Nat.not_even_iff_odd.mp (fun he => hv ((hz v).1 he))
  -- the even vertices of `J − z` are the neighbours of `z`
  have hevJ : ∀ v : {v | v ≠ z}, (Even (H.degree v) ↔ J.Adj v z) := by
    intro v
    have h := hdeg v
    have ho := hoddJ v.1 v.2
    by_cases hv : J.Adj v z
    · simp only [hv, ite_true] at h
      constructor
      · intro; exact hv
      · intro
        rw [← h] at ho
        exact (Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr ho |> fun h' => h') |> fun h' => by
          rcases Nat.even_or_odd (H.degree v) with he | he
          · exact he
          · exact absurd (Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr he)) (Nat.not_even_iff_odd.mpr ho))
    · simp only [hv, ite_false, add_zero] at h
      rw [h]
      exact ⟨fun he => absurd he (Nat.not_even_iff_odd.mpr ho), fun h' => absurd h' hv⟩
  -- the neighbours of `z` in `J − z`
  let N : Finset {v | v ≠ z} := Finset.univ.filter (fun v => J.Adj v z)
  have hNcard : N.card = 4 := by
    rw [← h4, ← card_neighborFinset_eq_degree]
    have : N.map (Function.Embedding.subtype _) = J.neighborFinset z := by
      ext w
      simp only [N, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.subtype_apply, mem_neighborFinset]
      constructor
      · rintro ⟨v, hv, rfl⟩; exact hv.symm
      · intro hw; exact ⟨⟨w, hw.ne'⟩, hw.symm, rfl⟩
    rw [← this, Finset.card_map]
  have hrN : r' ∈ N := by simp [N, r', hr.symm]
  -- a second vertex of `J − z`, so degrees are positive
  obtain ⟨x₀, hx₀, hx₀r⟩ : ∃ x ∈ N, x ≠ r' := by
    by_contra hcon
    push Not at hcon
    have : N ⊆ {r'} := fun x hx => Finset.mem_singleton.mpr (hcon x hx)
    have := Finset.card_le_card this
    rw [hNcard, Finset.card_singleton] at this
    omega
  have hpos : ∀ v, 0 < H.degree v := degree_pos_of_connected hconn hx₀r
  have hevSet : evenSet H = N := by
    ext v
    simp only [evenSet, N, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hevJ v]
    exact ⟨fun h => h.2, fun h => ⟨hpos v, h⟩⟩
  have hev4 : (evenSet H).card = 4 := by rw [hevSet, hNcard]
  -- three further even vertices
  have h3 : (N.erase r').card = 3 := by rw [Finset.card_erase_of_mem hrN, hNcard]
  obtain ⟨x, y, w, hxy, hxw, hyw, hEq⟩ := Finset.card_eq_three.mp h3
  have hx : x ∈ N.erase r' := by rw [hEq]; simp
  have hy : y ∈ N.erase r' := by rw [hEq]; simp
  have hxr : x ≠ r' := (Finset.mem_erase.mp hx).1
  have hyr : y ≠ r' := (Finset.mem_erase.mp hy).1
  -- even order of `J − z`
  have hcardS : Fintype.card {v | v ≠ z} + 1 = Fintype.card V := by
    have h1 := card_delVert (W := V) z
    have : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨z⟩
    omega
  have hoddSet : (oddSet H).card + 4 = Fintype.card {v | v ≠ z} := by
    rw [← hev4]; exact card_oddSet_add_card_evenSet hpos
  have hn : Even (Fintype.card {v | v ≠ z}) := by
    obtain ⟨k, hk⟩ := H.even_card_odd_degree_vertices
    have : (oddSet H).card = Finset.card (Finset.univ.filter (fun v => Odd (H.degree v))) := rfl
    refine ⟨k + 2, ?_⟩
    have h' : (oddSet H).card = k + k := hk ▸ this
    omega
  have hrE : r' ∈ evenSet H := hevSet ▸ hrN
  have hxE : x ∈ evenSet H := hevSet ▸ (Finset.mem_erase.mp hx).2
  have hyE : y ∈ evenSet H := hevSet ▸ (Finset.mem_erase.mp hy).2
  have key : ∀ S : Finset {v | v ≠ z}, S.card = 2 → r' ∈ S → Realisable H S →
      ∃ D : PathDecomp H, D.size ≤ (Fintype.card V - 1) / 2 ∧ 2 ≤ D.ends r' := by
    intro S hS2 hrS hreal
    obtain ⟨hSsub, D, hD⟩ := hreal
    refine ⟨D, ?_, ?_⟩
    · rw [hD.size_eq hSsub, hS2]
      omega
    · rw [hD r']
      unfold profile
      have : ¬ Odd (H.degree r') := not_odd_of_mem_evenSet hrE
      simp [this, hrS]
  rcases emc_four lovaszStatement hconn hn hev4 hrE hxE hyE hxr.symm hyr.symm hxy with h | h
  · exact key _ (Finset.card_pair hxr.symm) (by simp) h
  · exact key _ (Finset.card_pair hyr.symm) (by simp) h

end test1four

/-! ### On decompositions with at most one end per vertex, Fan's chain is forced -/

section forced

variable [DecidableEq U] {K : SimpleGraph U}

omit [DecidableEq U] in
theorem two_le_sum_of_mem_ne {α : Type*} (f : α → ℕ) :
    ∀ (l : List α) {a b : α}, a ∈ l → b ∈ l → a ≠ b → f a + f b ≤ (l.map f).sum
  | [], _, _, ha, _, _ => absurd ha List.not_mem_nil
  | c :: t, a, b, ha, hb, hab => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp ha with rfl | ha'
    · have hb' : b ∈ t := (List.mem_cons.mp hb).resolve_left (Ne.symm hab)
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := f) hb')
      omega
    · rcases List.mem_cons.mp hb with rfl | hb'
      · have := List.le_sum_of_mem (List.mem_map_of_mem (f := f) ha')
        omega
      · have := two_le_sum_of_mem_ne f t ha' hb' hab
        omega

omit [DecidableEq U] in
/-- In a path, the vertex before `u` is unique. -/
theorem pred_unique_of_isPath {a b z z' u : U} (p : K.Walk a b) (hp : p.IsPath)
    (h : [z, u] <:+: p.support) (h' : [z', u] <:+: p.support) : z = z' := by
  obtain ⟨d, hd, hdeq⟩ : ∃ d ∈ p.darts, d.fst = z ∧ d.snd = u := by
    have hadj : K.Adj z u := Walk.adj_of_infix_support p h
    exact ⟨⟨(z, u), hadj⟩, Walk.mem_darts_iff_fst_snd_infix_support.mpr h, rfl, rfl⟩
  obtain ⟨d', hd', hdeq'⟩ : ∃ d ∈ p.darts, d.fst = z' ∧ d.snd = u := by
    have hadj : K.Adj z' u := Walk.adj_of_infix_support p h'
    exact ⟨⟨(z', u), hadj⟩, Walk.mem_darts_iff_fst_snd_infix_support.mpr h', rfl, rfl⟩
  have hnd : (p.darts.map (·.snd)).Nodup := by
    rw [Walk.map_snd_darts]; exact hp.support_nodup.sublist (List.tail_sublist _)
  have := List.inj_on_of_nodup_map hnd hd hd' (hdeq.2.trans hdeq'.2.symm)
  rw [← hdeq.1, ← hdeq'.1, this]

omit [DecidableEq U] in
/-- In a path, the vertex after `u` is unique. -/
theorem succ_unique_of_isPath {a b z z' u : U} (p : K.Walk a b) (hp : p.IsPath)
    (h : [u, z] <:+: p.support) (h' : [u, z'] <:+: p.support) : z = z' := by
  obtain ⟨d, hd, hdeq⟩ : ∃ d ∈ p.darts, d.fst = u ∧ d.snd = z := by
    have hadj : K.Adj u z := Walk.adj_of_infix_support p h
    exact ⟨⟨(u, z), hadj⟩, Walk.mem_darts_iff_fst_snd_infix_support.mpr h, rfl, rfl⟩
  obtain ⟨d', hd', hdeq'⟩ : ∃ d ∈ p.darts, d.fst = u ∧ d.snd = z' := by
    have hadj : K.Adj u z' := Walk.adj_of_infix_support p h'
    exact ⟨⟨(u, z'), hadj⟩, Walk.mem_darts_iff_fst_snd_infix_support.mpr h', rfl, rfl⟩
  have hnd : (p.darts.map (·.fst)).Nodup := by
    rw [Walk.map_fst_darts]; exact hp.support_nodup.sublist (List.dropLast_sublist _)
  have := List.inj_on_of_nodup_map hnd hd hd' (hdeq.1.trans hdeq'.1.symm)
  rw [← hdeq.2, ← hdeq'.2, this]

/-- **Fan's chain is forced.** If `x` is the end of at most one path of `D`, the predecessor of `u`
read from `x` is unique. So on a decomposition with at most one end at every vertex (a Lovász
decomposition) the chain `x_{i+1} = pred(x_i)` of Fan's lemma is determined by `D`, `t` and `u`:
in the tight configuration the only freedom is the choice of `D` and of the target. -/
theorem fanPred_unique (D : PathDecomp K) {u x z z' : U} (hx : D.ends x ≤ 1)
    (h : FanPred D u x z) (h' : FanPred D u x z') : z = z' := by
  obtain ⟨P, hP, hPc⟩ := h
  obtain ⟨P', hP', hP'c⟩ := h'
  have hst : ∀ Q : GPath K, Q.src ≠ Q.tgt := fun Q => Q.src_ne_tgt
  have hend : ∀ Q : GPath K, (Q.src = x ∨ Q.tgt = x) → 1 ≤ Q.endsAt x := by
    intro Q hQ
    unfold GPath.endsAt
    rcases hQ with h | h <;> simp [h]
  by_cases hPP : P = P'
  · subst hPP
    rcases hPc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hP'c with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · exact pred_unique_of_isPath P.walk P.isPath h2 h2'
    · exact absurd (h1.trans h1'.symm) (hst P)
    · exact absurd (h1'.trans h1.symm) (hst P)
    · exact succ_unique_of_isPath P.walk P.isPath h2 h2'
  · exfalso
    have h1 := hend P (hPc.imp And.left And.left)
    have h2 := hend P' (hP'c.imp And.left And.left)
    have := two_le_sum_of_mem_ne (fun Q : GPath K => Q.endsAt x) D.paths hP hP' hPP
    unfold PathDecomp.ends at hx
    omega

end forced

end Gallai
