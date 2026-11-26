import GallaiLean.Insertion
import GallaiLean.Lovasz
import GallaiLean.PrivateLeaf

/-!
# The missing move: Lovász's spare path at a hub

Manuscript: `manuscripts/missing-move`.

Fan's transfers keep the number of paths fixed. A Lovász seed on a graph `K` with an isolated
vertex `s` has `⌊(n-1)/2⌋ = n/2 - 1` paths when `n` is even: one path of the budget is spare.
Re-inserting the four edges at a hub `s` of degree four spends it exactly: two edges are received
at `s` by Fan transfers, and the last two become one new path through `s`. This is the vertex
step of Lovász's own induction, and it is the move that the n = 8 losers of the profile game need.

* `Ach.decomp_of_edgeSet`, `Ach.of_decomp`: `Ach G.edgeSet b` is the same as a decomposition of
  `G` with end vector `b`.
* `isolate G s`: `G` with every edge at `s` removed; `isolate_degree`, `isolate_edgeSet`.
* **`Ach.hub_four`** (hub lemma): if `s` meets no edge of `E` and `a, c, d` have ends, then
  inserting the four edges `sa, sc, sd, sx` costs one extra path: for some labelling `{y, y'} =
  {c, d}` the end vector changes by `+2` at `s`, `-1` at `a` and `y`, `+1` at `y'` and `x`.
* **`hub_four_ends`**: let `G` have even order, let `s` have degree four with all four
  neighbours even, and let at most one even vertex lie outside `N[s]`. Then for every neighbour
  `x` of `s`, `G` has a decomposition into at most `n/2` paths with two ends at `s` and two at `x`.
* **`hub_four_rooted`**: consequently the rooted test holds at `s` and at every neighbour of `s`.

The profile-level Pósa moves tested alongside (rotation at equality, Fan's alternative; see the
manuscript) are single steps of the chain in `Fan.lean` (`PathDecomp.reroute_move`,
`PathDecomp.append_move`); they do not make the n = 8 losers winnable and are not needed here.
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u} [DecidableEq V]

/-! ### `Ach` on the full edge set -/

section conv

theorem Ach.decomp_of_edgeSet {G : SimpleGraph V} {b : V → ℕ} (h : Ach G.edgeSet b) :
    ∃ D : PathDecomp G, ∀ v, D.ends v = b v := by
  obtain ⟨D, hD⟩ := h
  revert D
  rw [fromEdgeSet_edgeSet]
  exact fun D hD => ⟨D, hD⟩

theorem Ach.of_decomp {G : SimpleGraph V} (D : PathDecomp G) : Ach G.edgeSet (fun v => D.ends v) := by
  unfold Ach
  rw [fromEdgeSet_edgeSet]
  exact ⟨D, fun v => rfl⟩

end conv

/-! ### Isolating a vertex -/

section isolate

/-- `G` with every edge at `s` removed. -/
def isolate (G : SimpleGraph V) (s : V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ≠ s ∧ y ≠ s
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩

instance isolate.decRel (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) :
    DecidableRel (isolate G s).Adj := fun x y =>
  inferInstanceAs (Decidable (G.Adj x y ∧ x ≠ s ∧ y ≠ s))

omit [DecidableEq V] in
theorem isolate_edgeSet (G : SimpleGraph V) (s : V) (e : Sym2 V) :
    e ∈ (isolate G s).edgeSet ↔ e ∈ G.edgeSet ∧ s ∉ e := by
  induction e using Sym2.ind with
  | _ x y =>
    simp only [mem_edgeSet, Sym2.mem_iff, not_or]
    show G.Adj x y ∧ x ≠ s ∧ y ≠ s ↔ _
    constructor
    · rintro ⟨h, hx, hy⟩; exact ⟨h, Ne.symm hx, Ne.symm hy⟩
    · rintro ⟨h, hx, hy⟩; exact ⟨h, Ne.symm hx, Ne.symm hy⟩

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem isolate_degree_self (s : V) : (isolate G s).degree s = 0 := by
  rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro y hy
  rw [mem_neighborFinset] at hy
  exact hy.2.1 rfl

theorem isolate_degree {s w : V} (hw : w ≠ s) :
    (isolate G s).degree w + (if G.Adj w s then 1 else 0) = G.degree w := by
  have hN : (isolate G s).neighborFinset w = (G.neighborFinset w).erase s := by
    ext y
    simp only [mem_neighborFinset, Finset.mem_erase]
    show G.Adj w y ∧ w ≠ s ∧ y ≠ s ↔ _
    tauto
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree, hN]
  split_ifs with h
  · exact Finset.card_erase_add_one ((mem_neighborFinset G w s).mpr h)
  · rw [Finset.erase_eq_of_notMem (by rwa [mem_neighborFinset]), add_zero]

end isolate

/-! ### The hub lemma -/

section hub

variable [Fintype V]

omit [DecidableEq V] [Fintype V] in
theorem blankNbrs_eq_zero_of_isolated {E : Set (Sym2 V)} {b : V → ℕ} {s : V}
    (hs : ∀ w, s(s, w) ∉ E) : blankNbrs E b s = 0 := by
  unfold blankNbrs
  have : {w | s(s, w) ∈ E ∧ w ≠ s ∧ b w = 0} = (∅ : Set V) := by
    ext w; exact ⟨fun h => absurd h.1 (hs w), fun h => h.elim⟩
  rw [this, Set.ncard_empty]

omit [Fintype V] in
/-- The last two steps of the hub: a grouped receipt has made `y` a donor, and the remaining
edges `sy'`, `sx` form one new path `y' s x`. -/
theorem Ach.hub_close {E : Set (Sym2 V)} {b : V → ℕ} {s a y y' x : V}
    (h : Ach (insert s(y, s) (insert s(a, s) E)) (mv (mv b a s) y s))
    (hs : ∀ w, s(s, w) ∉ E) (hsa : s ≠ a) (hsy : s ≠ y) (hsy' : s ≠ y') (hsx : s ≠ x)
    (hay : a ≠ y) (hay' : a ≠ y') (hax : a ≠ x) (hyy' : y ≠ y') (hyx : y ≠ x) (hy'x : y' ≠ x)
    (ha : 1 ≤ b a) (hy : 1 ≤ b y) :
    ∃ b' : V → ℕ, Ach (E ∪ {s(s, a), s(s, y), s(s, y'), s(s, x)}) b' ∧
      ∀ v, b' v + (if v = a then 1 else 0) + (if v = y then 1 else 0) =
        b v + 2 * (if v = s then 1 else 0) + (if v = y' then 1 else 0) +
          (if v = x then 1 else 0) := by
  have h1 := hsa.symm; have h2 := hsy.symm; have h3 := hsy'.symm; have h4 := hsx.symm
  have h5 := hay.symm; have h6 := hay'.symm; have h7 := hax.symm; have h8 := hyy'.symm
  have h9 := hyx.symm; have h10 := hy'x.symm
  have hnd : [y', s, x].Nodup := by simp [*]
  have hnew : ∀ e ∈ lEdges y' [s, x], e ∉ insert s(y, s) (insert s(a, s) E) := by
    intro e he
    simp only [lEdges_cons, lEdges_nil, List.mem_cons, List.not_mem_nil, or_false] at he
    have hy's := hs y'
    rw [Sym2.eq_swap] at hy's
    rcases he with rfl | rfl <;> simp [*]
  have h3' := h.addPath y' [s, x] (by simp) hnd hnew
  refine ⟨_, h3'.congr ?_ (fun v => rfl), fun v => ?_⟩
  · ext e
    have e1 : s(a, s) = s(s, a) := Sym2.eq_swap
    have e2 : s(y, s) = s(s, y) := Sym2.eq_swap
    have e3 : s(y', s) = s(s, y') := Sym2.eq_swap
    simp only [lEdges_cons, lEdges_nil, Set.mem_union, Set.mem_insert_iff, Set.mem_ofPred_eq,
      List.mem_cons, List.not_mem_nil, or_false, Set.mem_singleton_iff, e1, e2, e3]
    tauto
  · simp only [lastOf_cons, lastOf_nil]
    by_cases hvs : v = s
    · subst hvs
      rw [mv_apply_recv, mv_apply_recv]
      simp [*]
    have hm : mv (mv b a s) y s v = mv b a s v - (if v = y then 1 else 0) := by
      by_cases hvy : v = y
      · subst hvy; rw [mv_apply_donor _ hsy.symm]; simp
      · rw [mv_apply_other _ hvy hvs]; simp [hvy]
    have hm' : mv b a s v = b v - (if v = a then 1 else 0) := by
      by_cases hva : v = a
      · subst hva; rw [mv_apply_donor _ hsa.symm]; simp
      · rw [mv_apply_other _ hva hvs]; simp [hva]
    rw [hm, hm']
    by_cases hva : v = a
    · subst hva; simp [*]
    by_cases hvy : v = y
    · subst hvy; simp [*]
    by_cases hvy' : v = y'
    · subst hvy'; simp [*]
    by_cases hvx : v = x
    · subst hvx; simp [*]
    simp [*, Ne.symm hvy', Ne.symm hvx]

/-- **The hub lemma.** Let `s` meet no edge of `E`, and let `a, c, d, x` be distinct from each
other and from `s`, with at least one end at each of `a, c, d`. Then the graph with the four
edges `sa, sc, sd, sx` added has a decomposition with **one more path**, in which, for some
labelling `{y, y'} = {c, d}`, `s` has two more ends, `a` and `y` one fewer, `y'` and `x` one more,
and every other vertex is unchanged.

Proof: Fan's single transfer of `sa` towards `s` (no blank neighbour), a grouped transfer of
`{sc, sd}` towards `s` (supply `≥ 2`, at most the one blank neighbour `a`), and the new path
`y' s x`. -/
theorem Ach.hub_four {E : Set (Sym2 V)} {b : V → ℕ} (h : Ach E b) {s a c d x : V}
    (hs : ∀ w, s(s, w) ∉ E) (hsa : s ≠ a) (hsc : s ≠ c) (hsd : s ≠ d) (hsx : s ≠ x)
    (hac : a ≠ c) (had : a ≠ d) (hax : a ≠ x) (hcd : c ≠ d) (hcx : c ≠ x) (hdx : d ≠ x)
    (ha : 1 ≤ b a) (hc : 1 ≤ b c) (hd : 1 ≤ b d) :
    ∃ y y', ((y = c ∧ y' = d) ∨ (y = d ∧ y' = c)) ∧ ∃ b' : V → ℕ,
      Ach (E ∪ {s(s, a), s(s, c), s(s, d), s(s, x)}) b' ∧
      ∀ v, b' v + (if v = a then 1 else 0) + (if v = y then 1 else 0) =
        b v + 2 * (if v = s then 1 else 0) + (if v = y' then 1 else 0) +
          (if v = x then 1 else 0) := by
  have h1 := h.transfer (t := a) (u := s) (Ne.symm hsa) (by rw [Sym2.eq_swap]; exact hs a)
    (by rw [blankNbrs_eq_zero_of_isolated hs]; omega)
  have hsT : s ∉ ({c, d} : Finset V) := by simp [hsc, hsd]
  have hT : ∀ t ∈ ({c, d} : Finset V), s(t, s) ∉ insert s(a, s) E := by
    intro t ht
    have hta : t ≠ a := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact Ne.symm hac
      · exact Ne.symm had
    have hts : t ≠ s := fun h' => hsT (h' ▸ ht)
    simp only [Set.mem_insert_iff, not_or]
    refine ⟨?_, ?_⟩
    · rw [Sym2.eq_iff]; rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact hta h1
      · exact hts h1
    · rw [Sym2.eq_swap]; exact hs t
  have hbl : blankNbrs (insert s(a, s) E) (mv b a s) s ≤ 1 := by
    have := blankNbrs_le_of_subset (E := insert s(a, s) E) (b := mv b a s) (u := s)
      (S := {a}) (fun w hw _ _ => by
        rcases (Set.mem_insert_iff.mp hw) with h' | h'
        · rw [Sym2.eq_iff] at h'
          rcases h' with ⟨h1, -⟩ | ⟨-, h1⟩
          · exact absurd h1 hsa
          · exact h1
        · exact absurd h' (hs w))
    simpa using this
  have hsum : ∑ t ∈ ({c, d} : Finset V), mv b a s t = b c + b d := by
    rw [Finset.sum_pair hcd, mv_apply_other _ (Ne.symm hac) (Ne.symm hsc),
      mv_apply_other _ (Ne.symm had) (Ne.symm hsd)]
  obtain ⟨y, hy, hby, h2⟩ := h1.grouped s {c, d} hsT hT (by rw [hsum]; omega)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl
  · rw [mv_apply_other _ (Ne.symm hac) (Ne.symm hsc)] at hby
    obtain ⟨b', hb', hid⟩ := h2.hub_close hs hsa hsc hsd hsx hac had hax hcd hcx hdx ha hby
    exact ⟨y, d, Or.inl ⟨rfl, rfl⟩, b', hb', hid⟩
  · rw [mv_apply_other _ (Ne.symm had) (Ne.symm hsd)] at hby
    obtain ⟨b', hb', hid⟩ := h2.hub_close hs hsa hsd hsc hsx had hac hax (Ne.symm hcd) hdx hcx
      ha hby
    refine ⟨y, c, Or.inr ⟨rfl, rfl⟩, b', hb'.congr ?_ (fun v => rfl), hid⟩
    ext e
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

end hub

/-! ### A hub of degree four: the rooted test -/

section rooted

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Degree-four hubs.** Let `G` have even order `n`, let `s` have degree four with all four
neighbours of even degree, and suppose at most one even vertex of `G` lies outside `N[s]`. Then
for every neighbour `x` of `s`, `G` has a decomposition into at most `n/2` paths with exactly two
ends at `s` and exactly two at `x`.

Lovász's theorem on `G - s` (at most one even vertex, odd order after discarding `s`) gives
`⌊(n-1)/2⌋ = n/2 - 1` paths with one end at each neighbour of `s`; the hub lemma re-inserts the
four edges at `s` with one more path. -/
theorem hub_four_ends (hn : Even (Fintype.card V)) {s x : V} (hdeg : G.degree s = 4)
    (hx : G.Adj s x) (hNev : ∀ w, G.Adj s w → Even (G.degree w))
    (hEv : ((evenSet G).filter (fun v => v ≠ s ∧ ¬ G.Adj s v)).card ≤ 1) :
    ∃ D : PathDecomp G, 2 * D.size ≤ Fintype.card V ∧ D.ends s = 2 ∧ D.ends x = 2 := by
  classical
  -- the other three neighbours
  have hxN : x ∈ G.neighborFinset s := (mem_neighborFinset _ _ _).mpr hx
  have h3 : ((G.neighborFinset s).erase x).card = 3 := by
    rw [Finset.card_erase_of_mem hxN, card_neighborFinset_eq_degree, hdeg]
  obtain ⟨a, c, d, hac, had, hcd, hacd⟩ := Finset.card_eq_three.mp h3
  have hmem : ∀ w, w ∈ ({a, c, d} : Finset V) ↔ G.Adj s w ∧ w ≠ x := by
    intro w
    rw [← hacd, Finset.mem_erase, mem_neighborFinset]
    exact and_comm
  have ha := (hmem a).mp (by simp)
  have hc := (hmem c).mp (by simp)
  have hd := (hmem d).mp (by simp)
  have hN : ∀ w, G.Adj s w → w = a ∨ w = c ∨ w = d ∨ w = x := by
    intro w hw
    by_cases hwx : w = x
    · exact Or.inr (Or.inr (Or.inr hwx))
    · have := (hmem w).mpr ⟨hw, hwx⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      tauto
  have hsa : s ≠ a := ha.1.ne
  have hsc : s ≠ c := hc.1.ne
  have hsd : s ≠ d := hd.1.ne
  have hsx : s ≠ x := hx.ne
  -- the seed: Lovász on `G - s`
  have hKd : ∀ w, w ≠ s → (isolate G s).degree w + (if G.Adj w s then 1 else 0) = G.degree w :=
    fun w hw => isolate_degree G hw
  have hKs : (isolate G s).degree s = 0 := isolate_degree_self G s
  have hevK : (evenSet (isolate G s)).card ≤ 1 := by
    refine (Finset.card_le_card ?_).trans hEv
    intro v hv
    rw [mem_evenSet_iff] at hv
    have hvs : v ≠ s := by
      rintro rfl
      rw [hKs] at hv
      omega
    have hdv := hKd v hvs
    by_cases hadj : G.Adj v s
    · exfalso
      obtain ⟨k, hk⟩ := hNev v hadj.symm
      simp only [hadj, ite_true] at hdv
      have := hv.2
      omega
    · simp only [hadj, ite_false, add_zero] at hdv
      simp only [Finset.mem_filter, mem_evenSet_iff]
      exact ⟨⟨by omega, by omega⟩, hvs, fun h => hadj h.symm⟩
  obtain ⟨D0, hD0⟩ := lovasz_ends (isolate G s) hevK
  have hA : Ach (isolate G s).edgeSet (fun v => (isolate G s).degree v % 2) :=
    (Ach.of_decomp D0).congr rfl (fun v => hD0 v)
  have hs : ∀ w, s(s, w) ∉ (isolate G s).edgeSet := fun w h =>
    ((isolate_edgeSet G s _).mp h).2 (Sym2.mem_mk_left _ _)
  have hb1 : ∀ w, G.Adj s w → (isolate G s).degree w % 2 = 1 := by
    intro w hw
    have hdw := hKd w hw.ne.symm
    simp only [hw.symm, ite_true] at hdw
    obtain ⟨k, hk⟩ := hNev w hw
    omega
  obtain ⟨y, y', hyy, b', hb', hid⟩ := hA.hub_four hs hsa hsc hsd hsx hac had ha.2
    hcd hc.2 hd.2 (by rw [hb1 a ha.1]) (by rw [hb1 c hc.1])
    (by rw [hb1 d hd.1])
  -- the edge set is that of `G`
  have hE : (isolate G s).edgeSet ∪ {s(s, a), s(s, c), s(s, d), s(s, x)} = G.edgeSet := by
    ext e
    induction e using Sym2.ind with
    | _ p q =>
      rw [Set.mem_union, isolate_edgeSet]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, mem_edgeSet]
      constructor
      · rintro (⟨h, -⟩ | h | h | h | h)
        · exact h
        all_goals
          rw [Sym2.eq_iff] at h
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            first
              | exact ha.1 | exact hc.1 | exact hd.1 | exact hx
              | exact ha.1.symm | exact hc.1.symm | exact hd.1.symm | exact hx.symm
      · intro h
        by_cases hsm : s ∈ s(p, q)
        · right
          rcases Sym2.mem_iff.mp hsm with rfl | rfl
          · rcases hN q h with rfl | rfl | rfl | rfl <;> simp
          · rcases hN p h.symm with rfl | rfl | rfl | rfl <;> simp [Sym2.eq_swap]
        · exact Or.inl ⟨h, hsm⟩
  obtain ⟨D, hD⟩ := (hb'.congr hE (fun _ => rfl)).decomp_of_edgeSet
  -- counting
  have hsum0 : ∑ v, (isolate G s).degree v % 2 = 2 * D0.size := by
    rw [← D0.sum_ends]; exact Finset.sum_congr rfl (fun v _ => (hD0 v).symm)
  have hle : ∑ v, (isolate G s).degree v % 2 ≤ Fintype.card V - 1 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s), hKs, Nat.zero_mod,
      zero_add]
    calc ∑ v ∈ Finset.univ.erase s, (isolate G s).degree v % 2 ≤ (Finset.univ.erase s).card • 1 :=
          Finset.sum_le_card_nsmul _ _ _ (fun v _ => Nat.le_of_lt_succ (Nat.mod_lt _ two_pos))
      _ = Fintype.card V - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ s), Finset.card_univ, smul_eq_mul,
            mul_one]
  have hsum : ∑ v, b' v + 2 = ∑ v, (isolate G s).degree v % 2 + 4 := by
    have := Finset.sum_congr rfl (fun v (_ : v ∈ Finset.univ) => hid v)
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      ← Finset.mul_sum] at this
    omega
  have hsz : 2 * D.size = ∑ v, b' v := by
    rw [← D.sum_ends]; exact Finset.sum_congr rfl (fun v _ => hD v)
  obtain ⟨m, hm⟩ := hn
  have hfin : 2 * D.size ≤ Fintype.card V := by
    have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
    omega
  refine ⟨D, hfin, ?_, ?_⟩
  · have h := hid s
    rw [hD s]
    rcases hyy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [hsa, hsc, hsd, hsx, hKs] at h <;> omega
  · have h := hid x
    rw [hD x]
    have := hb1 x hx
    rcases hyy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [Ne.symm hsx, Ne.symm ha.2, Ne.symm hc.2, Ne.symm hd.2] at h <;> omega

/-- **The rooted test at a degree-four hub and at its neighbours.** Under the hypotheses of
`hub_four_ends`, `p(G + leaf at r) ≤ n/2` for `r = s` and for every neighbour `r` of `s`. -/
theorem hub_four_rooted (hn : Even (Fintype.card V)) {s : V} (hdeg : G.degree s = 4)
    (hNev : ∀ w, G.Adj s w → Even (G.degree w))
    (hEv : ((evenSet G).filter (fun v => v ≠ s ∧ ¬ G.Adj s v)).card ≤ 1) {r : V}
    (hr : r = s ∨ G.Adj s r) :
    pathNumber (addLeaf G r) ≤ Fintype.card V / 2 := by
  classical
  have hx : ∃ x, G.Adj s x ∧ (r = s ∨ r = x) := by
    rcases hr with rfl | hr
    · obtain ⟨x, hx⟩ := (G.degree_pos_iff_exists_adj r).mp (by omega)
      exact ⟨x, hx, Or.inl rfl⟩
    · exact ⟨r, hr, Or.inr rfl⟩
  obtain ⟨x, hx, hrx⟩ := hx
  obtain ⟨D, hsz, hs2, hx2⟩ := hub_four_ends G hn hdeg hx hNev hEv
  have hend : D.ends r ≠ 0 := by
    rcases hrx with rfl | rfl <;> omega
  calc pathNumber (addLeaf G r) ≤ leafCost D r := pathNumber_addLeaf_le D r
    _ = D.size := by simp [leafCost, hend]
    _ ≤ Fintype.card V / 2 := by omega

end rooted

end Gallai
