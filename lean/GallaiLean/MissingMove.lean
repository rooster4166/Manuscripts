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
* **`Ach.hub_four_tail`, `hub_four_odd_ends`, `hub_four_odd_rooted`**: the same with one odd
  neighbour `x` of `s`; the held edge `xz` extends the new path to `y' s x z`.
* **`gqz_rooted_three`**: the critical order-8 graph `Gqz~vw` (`K₈` minus `03, 12, 23, 34, 56, 67`;
  `p = n/2`), which the original game loses at the root `3`, satisfies the rooted test there.
  The hypotheses of `hub_four_odd_rooted` are checked by `decide`.

* **Arbitrary degree.** `Ach.hub_receipts`: if `s` meets no edge of a set `T` of receivers with
  one or two ends each, `r ≤ |T|`, and `blank(s) + 2r ≤ ∑_T b + 1`, then `r` of the edges `ts`
  are received at `s` by grouped transfers, each moving one end from its `t` to `s`.
  **`Ach.hub_general`** (general hub lemma): an isolated `s` with `d ≥ 2` such neighbours and
  `∑_N b ≥ 2d - 5` is re-inserted at the cost of one path (`d - 2` receipts and the new path
  `y s y'`). **`Ach.two_hub`** (two hubs): two isolated hubs `s₁, s₂` with private neighbour
  sets `N₁, N₂` (supply `∑_{N_i} b ≥ 2|N_i| - 3`) and a common neighbour `m` are re-inserted at
  the cost of one path in all: `|N_i| - 1` receipts at each hub, and the path `y₁ s₁ m s₂ y₂`.
  **`Ach.relays`** (forward relays `z x → x`, in any order, when no relayed `x` sees a blank
  vertex or a `z x'`) and **`Ach.relay_hub`** (relays into `X ⊆ N(s)` raise the supply to
  `|N| + |X|`, so `|N| ≤ |X| + 5` suffices for `Ach.hub_general`).

* **`fan_alternative`** (Fan's alternative, manuscript Lemma 4.2): either some `t ∈ T` gives an
  end to `u` (Fan's conclusion), or at least `∑_T ends` blank neighbours `z` of `u` can each be
  activated: `K + tu - zu` has a decomposition of the same size with an end moved from `t` to `z`.
  Its parts are `fan_reroute_exec` (the reroute steps of `fan_exec` without the final append) and
  `fan_alt_count` (the counting of `fan_exists_chain`, stopped before the contradiction).
  As a move of the profile game it repairs none of the n = 8 losers (manuscript Prop 4.3).
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

/-! ### A hub with one odd neighbour: the through-path continues -/

section tail

variable [Fintype V]

omit [Fintype V] in
/-- The last two steps of the hub when the new path continues along one more held edge `xz`:
the new path is `y' s x z`, so `x` stays interior and the extra end goes to `z`. -/
theorem Ach.hub_close_tail {E : Set (Sym2 V)} {b : V → ℕ} {s a y y' x z : V}
    (h : Ach (insert s(y, s) (insert s(a, s) E)) (mv (mv b a s) y s))
    (hs : ∀ w, s(s, w) ∉ E) (hxz : s(x, z) ∉ E) (hnd6 : [s, a, y, y', x, z].Nodup)
    (ha : 1 ≤ b a) (hy : 1 ≤ b y) :
    ∃ b' : V → ℕ, Ach (E ∪ {s(s, a), s(s, y), s(s, y'), s(s, x), s(x, z)}) b' ∧
      ∀ v, b' v + (if v = a then 1 else 0) + (if v = y then 1 else 0) =
        b v + 2 * (if v = s then 1 else 0) + (if v = y' then 1 else 0) +
          (if v = z then 1 else 0) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd6
  obtain ⟨⟨hsa, hsy, hsy', hsx, hsz⟩, ⟨hay, hay', hax, haz⟩, ⟨hyy', hyx, hyz⟩, ⟨hy'x, hy'z⟩,
    hxz', -⟩ := hnd6
  have h1 := Ne.symm hsa; have h2 := Ne.symm hsy; have h3 := Ne.symm hsy'; have h4 := Ne.symm hsx
  have h5 := Ne.symm hay; have h6 := Ne.symm hay'; have h7 := Ne.symm hax; have h8 := Ne.symm hyy'
  have h9 := Ne.symm hyx; have h10 := Ne.symm hy'x; have h11 := Ne.symm hsz; have h12 := Ne.symm haz
  have h13 := Ne.symm hyz; have h14 := Ne.symm hy'z; have h15 := Ne.symm hxz'
  have hnd : [y', s, x, z].Nodup := by simp [*]
  have hnew : ∀ e ∈ lEdges y' [s, x, z], e ∉ insert s(y, s) (insert s(a, s) E) := by
    intro e he
    simp only [lEdges_cons, lEdges_nil, List.mem_cons, List.not_mem_nil, or_false] at he
    have hy's := hs y'
    rw [Sym2.eq_swap] at hy's
    rcases he with rfl | rfl | rfl <;> simp [*]
  have h3' := h.addPath y' [s, x, z] (by simp) hnd hnew
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
      · subst hvy; rw [mv_apply_donor _ (Ne.symm hsy)]; simp
      · rw [mv_apply_other _ hvy hvs]; simp [hvy]
    have hm' : mv b a s v = b v - (if v = a then 1 else 0) := by
      by_cases hva : v = a
      · subst hva; rw [mv_apply_donor _ (Ne.symm hsa)]; simp
      · rw [mv_apply_other _ hva hvs]; simp [hva]
    rw [hm, hm']
    by_cases hva : v = a
    · subst hva; simp [*]
    by_cases hvy : v = y
    · subst hvy; simp [*]
    by_cases hvy' : v = y'
    · subst hvy'; simp [*]
    by_cases hvz : v = z
    · subst hvz; simp [*]
    simp [*, Ne.symm hvy', Ne.symm hvz]

/-- **The hub lemma, odd-neighbour form.** As `Ach.hub_four`, with a further held edge `xz`: the
new path is `y' s x z`. The profile changes by `+2` at `s`, `-1` at `a` and `y`, `+1` at `y'` and
`z`; `x` is unchanged. -/
theorem Ach.hub_four_tail {E : Set (Sym2 V)} {b : V → ℕ} (h : Ach E b) {s a c d x z : V}
    (hs : ∀ w, s(s, w) ∉ E) (hxz : s(x, z) ∉ E) (hnd6 : [s, a, c, d, x, z].Nodup)
    (ha : 1 ≤ b a) (hc : 1 ≤ b c) (hd : 1 ≤ b d) :
    ∃ y y', ((y = c ∧ y' = d) ∨ (y = d ∧ y' = c)) ∧ ∃ b' : V → ℕ,
      Ach (E ∪ {s(s, a), s(s, c), s(s, d), s(s, x), s(x, z)}) b' ∧
      ∀ v, b' v + (if v = a then 1 else 0) + (if v = y then 1 else 0) =
        b v + 2 * (if v = s then 1 else 0) + (if v = y' then 1 else 0) +
          (if v = z then 1 else 0) := by
  have hnd6' := hnd6
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd6'
  obtain ⟨⟨hsa, hsc, hsd, hsx, hsz⟩, ⟨hac, had, hax, haz⟩, ⟨hcd, hcx, hcz⟩, ⟨hdx, hdz⟩,
    hxz', -⟩ := hnd6'
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
    obtain ⟨b', hb', hid⟩ := h2.hub_close_tail hs hxz hnd6 ha hby
    exact ⟨y, d, Or.inl ⟨rfl, rfl⟩, b', hb', hid⟩
  · rw [mv_apply_other _ (Ne.symm had) (Ne.symm hsd)] at hby
    have hnd6s : [s, a, y, c, x, z].Nodup :=
      (List.Perm.cons s (List.Perm.cons a (List.Perm.swap y c [x, z]))).nodup_iff.mp hnd6
    obtain ⟨b', hb', hid⟩ := h2.hub_close_tail hs hxz hnd6s ha hby
    refine ⟨y, c, Or.inr ⟨rfl, rfl⟩, b', hb'.congr ?_ (fun v => rfl), hid⟩
    ext e
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

end tail

section rootedTail

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Degree-four hubs with one odd neighbour.** Let `G` have even order `n`, let `s` have degree
four, let its neighbour `x` be odd and its other three neighbours even, and let `z ∉ N[s]` be an
even neighbour of `x`. If at most one even vertex lies outside `N[s] ∪ {z}`, then `G` has a
decomposition into at most `n/2` paths with exactly two ends at `s` and exactly two at `z`.

Lovász on `G - s - xz` (now `x` and `z` are odd), then `Ach.hub_four_tail`: two receipts at `s`
and the new path `y' s x z`. This closes the critical order-8 graph `Gqz~vw` at its losing root. -/
theorem hub_four_odd_ends (hn : Even (Fintype.card V)) {s x z : V} (hdeg : G.degree s = 4)
    (hx : G.Adj s x) (hxodd : Odd (G.degree x)) (hNev : ∀ w, G.Adj s w → w ≠ x → Even (G.degree w))
    (hxz : G.Adj x z) (hzs : z ≠ s) (hzN : ¬ G.Adj s z) (hzev : Even (G.degree z))
    (hEv : ((evenSet G).filter (fun v => v ≠ s ∧ ¬ G.Adj s v ∧ v ≠ z)).card ≤ 1) :
    ∃ D : PathDecomp G, 2 * D.size ≤ Fintype.card V ∧ D.ends s = 2 ∧ D.ends z = 2 := by
  classical
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
  have hxz' : x ≠ z := hxz.ne
  have hzs' : ¬ G.Adj z s := fun h => hzN h.symm
  have hza : z ≠ a := fun h => hzN (h ▸ ha.1)
  have hzc : z ≠ c := fun h => hzN (h ▸ hc.1)
  have hzd : z ≠ d := fun h => hzN (h ▸ hd.1)
  -- the seed graph: `s` isolated and `xz` deleted
  have hI : (isolate G s).Adj x z := ⟨hxz, hsx.symm, hzs⟩
  have hKd : ∀ w, w ≠ s → (delEdge (isolate G s) x z).degree w + (if w = x then 1 else 0) +
      (if w = z then 1 else 0) + (if G.Adj w s then 1 else 0) = G.degree w := by
    intro w hw
    have h1 := delEdge_degree (isolate G s) hI w
    have h2 := isolate_degree G hw
    omega
  have hKs : (delEdge (isolate G s) x z).degree s = 0 := by
    have h1 := delEdge_degree (isolate G s) hI s
    have h2 := isolate_degree_self G s
    omega
  have hevK : (evenSet (delEdge (isolate G s) x z)).card ≤ 1 := by
    refine (Finset.card_le_card ?_).trans hEv
    intro v hv
    rw [mem_evenSet_iff] at hv
    have hvs : v ≠ s := by
      rintro rfl
      rw [hKs] at hv
      omega
    have hdv := hKd v hvs
    have hvx : v ≠ x := by
      rintro rfl
      obtain ⟨k, hk⟩ := hxodd
      simp [hxz', hx.symm] at hdv
      omega
    have hvz : v ≠ z := by
      rintro rfl
      obtain ⟨k, hk⟩ := hzev
      simp [hxz'.symm, hzs'] at hdv
      omega
    by_cases hadj : G.Adj v s
    · exfalso
      obtain ⟨k, hk⟩ := hNev v hadj.symm hvx
      simp only [hvx, hvz, hadj, ite_true, ite_false, add_zero] at hdv
      omega
    · simp only [hvx, hvz, hadj, ite_false, add_zero] at hdv
      simp only [Finset.mem_filter, mem_evenSet_iff]
      exact ⟨⟨by omega, by omega⟩, hvs, fun h => hadj h.symm, hvz⟩
  obtain ⟨D0, hD0⟩ := lovasz_ends (delEdge (isolate G s) x z) hevK
  have hA : Ach (delEdge (isolate G s) x z).edgeSet
      (fun v => (delEdge (isolate G s) x z).degree v % 2) :=
    (Ach.of_decomp D0).congr rfl (fun v => hD0 v)
  have hKE : ∀ e, e ∈ (delEdge (isolate G s) x z).edgeSet ↔
      (e ∈ G.edgeSet ∧ s ∉ e) ∧ e ≠ s(x, z) := by
    intro e
    rw [delEdge_edgeSet, isolate_edgeSet]
  have hs : ∀ w, s(s, w) ∉ (delEdge (isolate G s) x z).edgeSet := fun w h =>
    ((hKE _).mp h).1.2 (Sym2.mem_mk_left _ _)
  have hxzK : s(x, z) ∉ (delEdge (isolate G s) x z).edgeSet := fun h => ((hKE _).mp h).2 rfl
  have hb1 : ∀ w, G.Adj s w → w ≠ x → (delEdge (isolate G s) x z).degree w % 2 = 1 := by
    intro w hw hwx
    have hdw := hKd w hw.ne.symm
    have hwz : w ≠ z := fun h => hzN (h ▸ hw)
    simp only [hwx, hwz, hw.symm, ite_true, ite_false, add_zero] at hdw
    obtain ⟨k, hk⟩ := hNev w hw hwx
    omega
  have hbz : (delEdge (isolate G s) x z).degree z % 2 = 1 := by
    have hdz := hKd z hzs
    simp [hxz'.symm, hzs'] at hdz
    obtain ⟨k, hk⟩ := hzev
    omega
  have hnd6 : [s, a, c, d, x, z].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    exact ⟨⟨hsa, hsc, hsd, hsx, hzs.symm⟩, ⟨hac, had, ha.2, Ne.symm hza⟩,
      ⟨hcd, hc.2, Ne.symm hzc⟩, ⟨hd.2, Ne.symm hzd⟩, hxz', not_false⟩
  obtain ⟨y, y', hyy, b', hb', hid⟩ := hA.hub_four_tail hs hxzK hnd6
    (by rw [hb1 a ha.1 ha.2]) (by rw [hb1 c hc.1 hc.2]) (by rw [hb1 d hd.1 hd.2])
  have hE : (delEdge (isolate G s) x z).edgeSet ∪ {s(s, a), s(s, c), s(s, d), s(s, x), s(x, z)}
      = G.edgeSet := by
    ext e
    induction e using Sym2.ind with
    | _ p q =>
      rw [Set.mem_union, hKE]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, mem_edgeSet]
      constructor
      · rintro (⟨⟨h, -⟩, -⟩ | h | h | h | h | h)
        · exact h
        all_goals
          rw [Sym2.eq_iff] at h
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            first
              | exact ha.1 | exact hc.1 | exact hd.1 | exact hx | exact hxz
              | exact ha.1.symm | exact hc.1.symm | exact hd.1.symm | exact hx.symm
              | exact hxz.symm
      · intro h
        by_cases hsm : s ∈ s(p, q)
        · right
          rcases Sym2.mem_iff.mp hsm with rfl | rfl
          · rcases hN q h with rfl | rfl | rfl | rfl <;> simp
          · rcases hN p h.symm with rfl | rfl | rfl | rfl <;> simp [Sym2.eq_swap]
        · by_cases hxzm : s(p, q) = s(x, z)
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hxzm))))
          · exact Or.inl ⟨⟨h, hsm⟩, hxzm⟩
  obtain ⟨D, hD⟩ := (hb'.congr hE (fun _ => rfl)).decomp_of_edgeSet
  have hsum0 : ∑ v, (delEdge (isolate G s) x z).degree v % 2 = 2 * D0.size := by
    rw [← D0.sum_ends]; exact Finset.sum_congr rfl (fun v _ => (hD0 v).symm)
  have hle : ∑ v, (delEdge (isolate G s) x z).degree v % 2 ≤ Fintype.card V - 1 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s), hKs, Nat.zero_mod, zero_add]
    calc ∑ v ∈ Finset.univ.erase s, (delEdge (isolate G s) x z).degree v % 2
          ≤ (Finset.univ.erase s).card • 1 :=
          Finset.sum_le_card_nsmul _ _ _ (fun v _ => Nat.le_of_lt_succ (Nat.mod_lt _ two_pos))
      _ = Fintype.card V - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ s), Finset.card_univ, smul_eq_mul,
            mul_one]
  have hsum : ∑ v, b' v + 2 = ∑ v, (delEdge (isolate G s) x z).degree v % 2 + 4 := by
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
      simp [hsa, hsc, hsd, hzs.symm, hKs] at h <;> omega
  · have h := hid z
    rw [hD z]
    rcases hyy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [hza, hzc, hzd, hzs] at h <;> omega

/-- **The rooted test at a degree-four hub with one odd neighbour**, at `s` and at `z`. -/
theorem hub_four_odd_rooted (hn : Even (Fintype.card V)) {s x z : V} (hdeg : G.degree s = 4)
    (hx : G.Adj s x) (hxodd : Odd (G.degree x)) (hNev : ∀ w, G.Adj s w → w ≠ x → Even (G.degree w))
    (hxz : G.Adj x z) (hzs : z ≠ s) (hzN : ¬ G.Adj s z) (hzev : Even (G.degree z))
    (hEv : ((evenSet G).filter (fun v => v ≠ s ∧ ¬ G.Adj s v ∧ v ≠ z)).card ≤ 1) {r : V}
    (hr : r = s ∨ r = z) :
    pathNumber (addLeaf G r) ≤ Fintype.card V / 2 := by
  classical
  obtain ⟨D, hsz, hs2, hz2⟩ := hub_four_odd_ends G hn hdeg hx hxodd hNev hxz hzs hzN hzev hEv
  have hend : D.ends r ≠ 0 := by
    rcases hr with rfl | rfl <;> omega
  calc pathNumber (addLeaf G r) ≤ leafCost D r := pathNumber_addLeaf_le D r
    _ = D.size := by simp [leafCost, hend]
    _ ≤ Fintype.card V / 2 := by omega


end rootedTail

/-! ### Hubs of arbitrary degree -/

section general

variable [Fintype V]

omit [Fintype V] in
/-- Inserting `ts` and moving an end from `t` to `s` creates at most one new blank neighbour of
`s`, namely `t`, and only when `t` had exactly one end. -/
theorem blankNbrs_insert_le [Finite V] {E : Set (Sym2 V)} {b : V → ℕ} {s t : V} (hts : t ≠ s)
    (hbt : 1 ≤ b t) :
    blankNbrs (insert s(t, s) E) (mv b t s) s ≤
      blankNbrs E b s + (if b t = 1 then 1 else 0) := by
  unfold blankNbrs
  have hsub : {w | s(s, w) ∈ insert s(t, s) E ∧ w ≠ s ∧ mv b t s w = 0} ⊆
      {w | s(s, w) ∈ E ∧ w ≠ s ∧ b w = 0} ∪ (if b t = 1 then {t} else ∅) := by
    rintro w ⟨hw, hws, hb0⟩
    by_cases hwt : w = t
    · subst hwt
      rw [mv_apply_donor _ hts] at hb0
      have h1 : b w = 1 := by omega
      right; simp [h1]
    · left
      rw [mv_apply_other _ hwt hws] at hb0
      refine ⟨?_, hws, hb0⟩
      rcases Set.mem_insert_iff.mp hw with h | h
      · rw [Sym2.eq_iff] at h
        rcases h with ⟨h1, -⟩ | ⟨-, h1⟩
        · exact absurd h1.symm hts
        · exact absurd h1 hwt
      · exact h
  calc _ ≤ ({w | s(s, w) ∈ E ∧ w ≠ s ∧ b w = 0} ∪ (if b t = 1 then {t} else ∅)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ _ := by
        refine (Set.ncard_union_le _ _).trans ?_
        split_ifs <;> simp

/-- **Receipts at a hub.** Let `T` be a set of non-neighbours of `s` with one or two ends each,
and suppose `∑_T b ≥ blank(s) + 2r - 1`. Then `r` grouped transfers towards `s` succeed: for some
`R ⊆ T` with `|R| = r`, the graph with the edges `sR` added has a decomposition with the same
number of paths, `r` more ends at `s` and one fewer at each vertex of `R`. Each receipt lowers
`∑_T b - blank(s)` by at most two (`blankNbrs_insert_le`). -/
theorem Ach.hub_receipts {s : V} : ∀ (r : ℕ) {E : Set (Sym2 V)} {b : V → ℕ} (T : Finset V),
    Ach E b → s ∉ T → (∀ t ∈ T, s(t, s) ∉ E) → (∀ t ∈ T, 1 ≤ b t ∧ b t ≤ 2) → r ≤ T.card →
    blankNbrs E b s + 2 * r ≤ ∑ t ∈ T, b t + 1 →
    ∃ R ⊆ T, R.card = r ∧ ∃ b' : V → ℕ, Ach (E ∪ {e | ∃ t ∈ R, e = s(t, s)}) b' ∧
      ∀ v, b' v + (if v ∈ R then 1 else 0) = b v + r * (if v = s then 1 else 0)
  | 0, E, b, T, h, _, _, _, _, _ => ⟨∅, Finset.empty_subset _, rfl, b, h.congr (by simp) (fun _ => rfl),
      fun v => by simp⟩
  | r + 1, E, b, T, h, hsT, hT, hb, hr, hsum => by
    classical
    have hpos : blankNbrs E b s < ∑ t ∈ T, b t := by omega
    obtain ⟨t, ht, hbt, h1⟩ := h.grouped s T hsT hT hpos
    have hts : t ≠ s := fun h' => hsT (h' ▸ ht)
    have hbl := blankNbrs_insert_le (E := E) (b := b) hts hbt
    have hsum' : ∑ u ∈ T.erase t, mv b t s u + b t = ∑ u ∈ T, b u := by
      rw [← Finset.sum_erase_add _ _ ht]
      congr 1
      refine Finset.sum_congr rfl (fun u hu => ?_)
      exact mv_apply_other _ (Finset.ne_of_mem_erase hu)
        (fun h' => hsT (by rw [← h']; exact Finset.mem_of_mem_erase hu))
    have hbt2 := (hb t ht).2
    obtain ⟨R, hRT, hRc, b', hb', hid⟩ := Ach.hub_receipts r (T.erase t) h1
      (fun h' => hsT (Finset.mem_of_mem_erase h'))
      (fun u hu h' => by
        rcases Set.mem_insert_iff.mp h' with h'' | h''
        · rw [Sym2.eq_iff] at h''
          rcases h'' with ⟨h3, -⟩ | ⟨h3, -⟩
          · exact Finset.ne_of_mem_erase hu h3
          · exact hsT (by rw [← h3]; exact Finset.mem_of_mem_erase hu)
        · exact hT u (Finset.mem_of_mem_erase hu) h'')
      (fun u hu => by
        have hus : u ≠ s := fun h' => hsT (by rw [← h']; exact Finset.mem_of_mem_erase hu)
        rw [mv_apply_other _ (Finset.ne_of_mem_erase hu) hus]
        exact hb u (Finset.mem_of_mem_erase hu))
      (by rw [Finset.card_erase_of_mem ht]; omega)
      (by split_ifs at hbl <;> omega)
    have htR : t ∉ R := fun h' => (Finset.mem_erase.mp (hRT h')).1 rfl
    refine ⟨insert t R, Finset.insert_subset ht (hRT.trans (Finset.erase_subset _ _)),
      by rw [Finset.card_insert_of_notMem htR, hRc], b', hb'.congr ?_ (fun _ => rfl), fun v => ?_⟩
    · ext e
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_ofPred_eq, Finset.mem_insert]
      constructor
      · rintro ((h' | h') | ⟨u, hu, rfl⟩)
        · exact Or.inr ⟨t, Or.inl rfl, h'⟩
        · exact Or.inl h'
        · exact Or.inr ⟨u, Or.inr hu, rfl⟩
      · rintro (h' | ⟨u, hu | hu, rfl⟩)
        · exact Or.inl (Or.inr h')
        · exact Or.inl (Or.inl (by rw [hu]))
        · exact Or.inr ⟨u, hu, rfl⟩
    · have := hid v
      unfold mv at this
      by_cases hvs : v = s
      · subst hvs
        simp only [ite_true, Finset.mem_insert, hts.symm, false_or] at this ⊢
        have hvR : v ∉ R := fun h' => hsT (Finset.mem_of_mem_erase (hRT h'))
        simp only [hvR, ite_false] at this ⊢
        nlinarith
      · by_cases hvt : v = t
        · subst hvt
          simp only [hvs, ite_false, ite_true, Finset.mem_insert, true_or, htR] at this ⊢
          omega
        · simp only [hvs, hvt, ite_false, Finset.mem_insert, false_or, mul_zero, add_zero]
            at this ⊢
          omega

/-- **The hub lemma, arbitrary degree.** Let `s` meet no edge of `E`, and let `N` be a set of
`d ≥ 2` vertices, `s ∉ N`, with one or two ends each and `∑_N b ≥ 2d - 5`. Then inserting the
`d` edges `sN` costs **one** extra path: `d - 2` grouped receipts at `s` (from a set `R`), and the
last two edges `sy, sy'` form the new path `y s y'`. So `s` gets `d - 2` ends. For `d ≤ 5` the
supply condition holds as soon as `b ≥ 1` on `N`; at degree six one neighbour needs two ends. -/
theorem Ach.hub_general {E : Set (Sym2 V)} {b : V → ℕ} (h : Ach E b) {s : V} (N : Finset V)
    (hs : ∀ w, s(s, w) ∉ E) (hsN : s ∉ N) (hb : ∀ t ∈ N, 1 ≤ b t ∧ b t ≤ 2) (hd : 2 ≤ N.card)
    (hσ : 2 * N.card ≤ ∑ t ∈ N, b t + 5) :
    ∃ R ⊆ N, R.card = N.card - 2 ∧ ∃ y y', y ∈ N ∧ y' ∈ N ∧ y ≠ y' ∧ y ∉ R ∧ y' ∉ R ∧
      ∃ b' : V → ℕ, Ach (E ∪ {e | ∃ t ∈ N, e = s(s, t)}) b' ∧
        ∀ v, b' v + (if v ∈ R then 1 else 0) =
          b v + (N.card - 2) * (if v = s then 1 else 0) + (if v = y then 1 else 0) +
            (if v = y' then 1 else 0) := by
  classical
  have hT : ∀ t ∈ N, s(t, s) ∉ E := fun t _ h' => hs t (by rw [Sym2.eq_swap]; exact h')
  obtain ⟨R, hRN, hRc, b1, hb1, hid1⟩ := h.hub_receipts (N.card - 2) N hsN hT hb (by omega)
    (by rw [blankNbrs_eq_zero_of_isolated hs]; omega)
  have hrest : (N \ R).card = 2 := by rw [Finset.card_sdiff_of_subset hRN, hRc]; omega
  obtain ⟨y, y', hyy', hNR⟩ := Finset.card_eq_two.mp hrest
  have hy : y ∈ N \ R := by rw [hNR]; simp
  have hy' : y' ∈ N \ R := by rw [hNR]; simp
  rw [Finset.mem_sdiff] at hy hy'
  have hsy : s ≠ y := fun h' => hsN (h' ▸ hy.1)
  have hsy' : s ≠ y' := fun h' => hsN (h' ▸ hy'.1)
  have hnd : [y, s, y'].Nodup := by simp [hyy', Ne.symm hsy, hsy']
  have hnew : ∀ e ∈ lEdges y [s, y'], e ∉ E ∪ {e | ∃ t ∈ R, e = s(t, s)} := by
    intro e he
    simp only [lEdges_cons, lEdges_nil, List.mem_cons, List.not_mem_nil, or_false] at he
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and]
    rcases he with rfl | rfl
    · refine ⟨fun h' => hs y (by rw [Sym2.eq_swap]; exact h'), fun t ht h' => ?_⟩
      rw [Sym2.eq_iff] at h'
      rcases h' with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hy.2 (h1 ▸ ht)
      · exact hsy h1.symm
    · refine ⟨hs y', fun t ht h' => ?_⟩
      rw [Sym2.eq_iff] at h'
      rcases h' with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact hsN (h1 ▸ hRN ht)
      · exact hy'.2 (h2 ▸ ht)
  have h2 := hb1.addPath y [s, y'] (by simp) hnd hnew
  refine ⟨R, hRN, hRc, y, y', hy.1, hy'.1, hyy', hy.2, hy'.2, _, h2.congr ?_ (fun _ => rfl),
    fun v => ?_⟩
  · ext e
    simp only [lEdges_cons, lEdges_nil, Set.mem_union, Set.mem_ofPred_eq, List.mem_cons,
      List.not_mem_nil, or_false]
    constructor
    · rintro ((h' | ⟨t, ht, rfl⟩) | h' | h')
      · exact Or.inl h'
      · exact Or.inr ⟨t, hRN ht, Sym2.eq_swap⟩
      · exact Or.inr ⟨y, hy.1, by rw [h', Sym2.eq_swap]⟩
      · exact Or.inr ⟨y', hy'.1, h'⟩
    · rintro (h' | ⟨t, ht, rfl⟩)
      · exact Or.inl (Or.inl h')
      · by_cases htR : t ∈ R
        · exact Or.inl (Or.inr ⟨t, htR, Sym2.eq_swap⟩)
        · have : t ∈ N \ R := Finset.mem_sdiff.mpr ⟨ht, htR⟩
          rw [hNR] at this
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with rfl | rfl
          · exact Or.inr (Or.inl Sym2.eq_swap)
          · exact Or.inr (Or.inr rfl)
  · have := hid1 v
    simp only [lastOf_cons, lastOf_nil]
    have e1 := Ne.symm hsy; have e2 := Ne.symm hsy'; have e3 := Ne.symm hyy'
    have hsR : s ∉ R := fun h' => hsN (hRN h')
    by_cases hvs : v = s
    · subst hvs
      simp [hsy, hsy', e1, e2, hsR] at this ⊢
      omega
    by_cases hvy : v = y
    · subst hvy
      simp [hy.2, hvs, hyy', e3] at this ⊢
      omega
    by_cases hvy' : v = y'
    · subst hvy'
      simp [hy'.2, hvs, hvy, hyy'] at this ⊢
      omega
    · simp [hvs, hvy, hvy', Ne.symm hvy, Ne.symm hvy'] at this ⊢
      omega

/-- **Two hubs share one spare path.** Let `s₁ ≠ s₂` meet no edge of `E`, with neighbour sets
`N₁ ∪ {m}` and `N₂ ∪ {m}` (`N₁, N₂` disjoint, `m ∉ N₁ ∪ N₂`, `s₁, s₂, m` outside them). If each
`N_i` carries one or two ends per vertex and `∑_{N_i} b ≥ 2|N_i| - 3`, then inserting both stars
costs one extra path: `|N_i| - 1` receipts at each hub, and the new path `y₁ s₁ m s₂ y₂`. -/
theorem Ach.two_hub {E : Set (Sym2 V)} {b : V → ℕ} (h : Ach E b) {s₁ s₂ m : V}
    (N₁ N₂ : Finset V) (hs₁ : ∀ w, s(s₁, w) ∉ E) (hs₂ : ∀ w, s(s₂, w) ∉ E) (h12 : s₁ ≠ s₂)
    (hm₁ : m ≠ s₁) (hm₂ : m ≠ s₂) (hmN₁ : m ∉ N₁) (hmN₂ : m ∉ N₂) (hdisj : Disjoint N₁ N₂)
    (hs₁N : s₁ ∉ N₁ ∪ N₂) (hs₂N : s₂ ∉ N₁ ∪ N₂)
    (hb₁ : ∀ t ∈ N₁, 1 ≤ b t ∧ b t ≤ 2) (hb₂ : ∀ t ∈ N₂, 1 ≤ b t ∧ b t ≤ 2)
    (hd₁ : 1 ≤ N₁.card) (hd₂ : 1 ≤ N₂.card)
    (hσ₁ : 2 * N₁.card ≤ ∑ t ∈ N₁, b t + 3) (hσ₂ : 2 * N₂.card ≤ ∑ t ∈ N₂, b t + 3) :
    ∃ R₁ ⊆ N₁, R₁.card = N₁.card - 1 ∧ ∃ R₂ ⊆ N₂, R₂.card = N₂.card - 1 ∧
      ∃ y₁ ∈ N₁, y₁ ∉ R₁ ∧ ∃ y₂ ∈ N₂, y₂ ∉ R₂ ∧
      ∃ b' : V → ℕ, Ach (E ∪ {e | ∃ t ∈ N₁, e = s(s₁, t)} ∪ {e | ∃ t ∈ N₂, e = s(s₂, t)} ∪
          {s(s₁, m), s(s₂, m)}) b' ∧
        ∀ v, b' v + (if v ∈ R₁ then 1 else 0) + (if v ∈ R₂ then 1 else 0) =
          b v + (N₁.card - 1) * (if v = s₁ then 1 else 0) +
            (N₂.card - 1) * (if v = s₂ then 1 else 0) + (if v = y₁ then 1 else 0) +
              (if v = y₂ then 1 else 0) := by
  classical
  have hs₁N₁ : s₁ ∉ N₁ := fun h' => hs₁N (Finset.mem_union_left _ h')
  have hs₁N₂ : s₁ ∉ N₂ := fun h' => hs₁N (Finset.mem_union_right _ h')
  have hs₂N₁ : s₂ ∉ N₁ := fun h' => hs₂N (Finset.mem_union_left _ h')
  have hs₂N₂ : s₂ ∉ N₂ := fun h' => hs₂N (Finset.mem_union_right _ h')
  have hT₁ : ∀ t ∈ N₁, s(t, s₁) ∉ E := fun t _ h' => hs₁ t (by rw [Sym2.eq_swap]; exact h')
  obtain ⟨R₁, hR₁, hR₁c, b1, hb1, hid1⟩ := h.hub_receipts (N₁.card - 1) N₁ hs₁N₁ hT₁ hb₁
    (by omega) (by rw [blankNbrs_eq_zero_of_isolated hs₁]; omega)
  have hb1N₂ : ∀ t ∈ N₂, b1 t = b t := by
    intro t ht
    have h1 := hid1 t
    have htR : t ∉ R₁ := fun h' => Finset.disjoint_left.mp hdisj (hR₁ h') ht
    have hts : t ≠ s₁ := fun h' => hs₁N₂ (h' ▸ ht)
    simp [htR, hts] at h1
    omega
  -- `s₂` is still isolated after the first receipts.
  have hs₂' : ∀ w, s(s₂, w) ∉ E ∪ {e | ∃ t ∈ R₁, e = s(t, s₁)} := by
    intro w h'
    simp only [Set.mem_union, Set.mem_ofPred_eq] at h'
    rcases h' with h' | ⟨t, ht, h'⟩
    · exact hs₂ w h'
    · rw [Sym2.eq_iff] at h'
      rcases h' with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hs₂N₁ (h1 ▸ hR₁ ht)
      · exact h12 h1.symm
  have hT₂ : ∀ t ∈ N₂, s(t, s₂) ∉ E ∪ {e | ∃ t ∈ R₁, e = s(t, s₁)} :=
    fun t _ h' => hs₂' t (by rw [Sym2.eq_swap]; exact h')
  have hsum : ∑ t ∈ N₂, b1 t = ∑ t ∈ N₂, b t := Finset.sum_congr rfl hb1N₂
  obtain ⟨R₂, hR₂, hR₂c, b2, hb2, hid2⟩ := hb1.hub_receipts (N₂.card - 1) N₂ hs₂N₂ hT₂
    (fun t ht => hb1N₂ t ht ▸ hb₂ t ht) (by omega)
    (by rw [blankNbrs_eq_zero_of_isolated hs₂', hsum]; omega)
  have hr₁ : (N₁ \ R₁).card = 1 := by rw [Finset.card_sdiff_of_subset hR₁, hR₁c]; omega
  have hr₂ : (N₂ \ R₂).card = 1 := by rw [Finset.card_sdiff_of_subset hR₂, hR₂c]; omega
  obtain ⟨y₁, hy₁e⟩ := Finset.card_eq_one.mp hr₁
  obtain ⟨y₂, hy₂e⟩ := Finset.card_eq_one.mp hr₂
  have hy₁ : y₁ ∈ N₁ \ R₁ := by rw [hy₁e]; simp
  have hy₂ : y₂ ∈ N₂ \ R₂ := by rw [hy₂e]; simp
  rw [Finset.mem_sdiff] at hy₁ hy₂
  have hy12 : y₁ ≠ y₂ := fun h' => Finset.disjoint_left.mp hdisj hy₁.1 (h' ▸ hy₂.1)
  have hy₁s₁ : y₁ ≠ s₁ := fun h' => hs₁N₁ (h' ▸ hy₁.1)
  have hy₁s₂ : y₁ ≠ s₂ := fun h' => hs₂N₁ (h' ▸ hy₁.1)
  have hy₁m : y₁ ≠ m := fun h' => hmN₁ (h' ▸ hy₁.1)
  have hy₂s₁ : y₂ ≠ s₁ := fun h' => hs₁N₂ (h' ▸ hy₂.1)
  have hy₂s₂ : y₂ ≠ s₂ := fun h' => hs₂N₂ (h' ▸ hy₂.1)
  have hy₂m : y₂ ≠ m := fun h' => hmN₂ (h' ▸ hy₂.1)
  have hnd : [y₁, s₁, m, s₂, y₂].Nodup := by
    simp [hy12, hy₁s₁, hy₁s₂, hy₁m, Ne.symm hm₁, h12, Ne.symm hy₂s₁, hm₂, Ne.symm hy₂m,
      Ne.symm hy₂s₂]
  have hnew : ∀ e ∈ lEdges y₁ [s₁, m, s₂, y₂],
      e ∉ E ∪ {e | ∃ t ∈ R₁, e = s(t, s₁)} ∪ {e | ∃ t ∈ R₂, e = s(t, s₂)} := by
    intro e he h'
    simp only [lEdges_cons, lEdges_nil, List.mem_cons, List.not_mem_nil, or_false] at he
    simp only [Set.mem_union, Set.mem_ofPred_eq] at h'
    rcases h' with (h' | ⟨t, ht, h'⟩) | ⟨t, ht, h'⟩
    · rcases he with rfl | rfl | rfl | rfl
      · exact hs₁ y₁ (by rw [Sym2.eq_swap]; exact h')
      · exact hs₁ m h'
      · exact hs₂ m (by rw [Sym2.eq_swap]; exact h')
      · exact hs₂ y₂ h'
    · rcases he with rfl | rfl | rfl | rfl <;> rw [Sym2.eq_iff] at h' <;>
        rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hy₁.2 (h1 ▸ ht)
      · exact hs₁N₁ (h2 ▸ hR₁ ht)
      · exact hs₁N₁ (h1 ▸ hR₁ ht)
      · exact hmN₁ (h2 ▸ hR₁ ht)
      · exact hmN₁ (h1 ▸ hR₁ ht)
      · exact hm₁ h1
      · exact hs₂N₁ (h1 ▸ hR₁ ht)
      · exact h12 h1.symm
    · rcases he with rfl | rfl | rfl | rfl <;> rw [Sym2.eq_iff] at h' <;>
        rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h12 h2
      · exact hy₁s₂ h1
      · exact hs₁N₂ (h1 ▸ hR₂ ht)
      · exact h12 h1
      · exact hmN₂ (h1 ▸ hR₂ ht)
      · exact hm₂ h1
      · exact hs₂N₂ (h1 ▸ hR₂ ht)
      · exact hy₂.2 (h2 ▸ ht)
  have h3 := hb2.addPath y₁ [s₁, m, s₂, y₂] (by simp) hnd hnew
  refine ⟨R₁, hR₁, hR₁c, R₂, hR₂, hR₂c, y₁, hy₁.1, hy₁.2, y₂, hy₂.1, hy₂.2, _,
    h3.congr ?_ (fun _ => rfl), fun v => ?_⟩
  · ext e
    simp only [lEdges_cons, lEdges_nil, Set.mem_union, Set.mem_ofPred_eq, List.mem_cons,
      List.not_mem_nil, or_false, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (((h' | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩) | rfl | rfl | rfl | rfl)
      · exact Or.inl (Or.inl (Or.inl h'))
      · exact Or.inl (Or.inl (Or.inr ⟨t, hR₁ ht, Sym2.eq_swap⟩))
      · exact Or.inl (Or.inr ⟨t, hR₂ ht, Sym2.eq_swap⟩)
      · exact Or.inl (Or.inl (Or.inr ⟨y₁, hy₁.1, Sym2.eq_swap⟩))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr Sym2.eq_swap)
      · exact Or.inl (Or.inr ⟨y₂, hy₂.1, rfl⟩)
    · rintro (((h' | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩) | rfl | rfl)
      · exact Or.inl (Or.inl (Or.inl h'))
      · by_cases htR : t ∈ R₁
        · exact Or.inl (Or.inl (Or.inr ⟨t, htR, Sym2.eq_swap⟩))
        · have : t ∈ N₁ \ R₁ := Finset.mem_sdiff.mpr ⟨ht, htR⟩
          rw [hy₁e, Finset.mem_singleton] at this
          subst this
          exact Or.inr (Or.inl Sym2.eq_swap)
      · by_cases htR : t ∈ R₂
        · exact Or.inl (Or.inr ⟨t, htR, Sym2.eq_swap⟩)
        · have : t ∈ N₂ \ R₂ := Finset.mem_sdiff.mpr ⟨ht, htR⟩
          rw [hy₂e, Finset.mem_singleton] at this
          subst this
          exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl Sym2.eq_swap)))
  · have k1 := hid1 v
    have k2 := hid2 v
    simp only [lastOf_cons, lastOf_nil, @eq_comm _ y₁ v, @eq_comm _ y₂ v]
    omega

/-- **Forward relays.** Let `X` be a set of vertices and `z` a map, injective on `X`, sending each
`x ∈ X` to a vertex `z x ∉ X` with one end, with `z x x` not an edge of `E`. Suppose that no
`x ∈ X` has, in `E`, a blank neighbour or a neighbour of the form `z x'`. Then the single
transfers `z x → x` succeed in any order: the edges `z x x` are added, each `x` gains one end and
each `z x` loses its end. (Each transfer has supply `1` against no blank neighbour.) -/
theorem Ach.relays {E : Set (Sym2 V)} {b : V → ℕ} (h : Ach E b) (X : Finset V) (z : V → V)
    (hzX : ∀ x ∈ X, z x ∉ X) (hinj : ∀ x ∈ X, ∀ x' ∈ X, z x = z x' → x = x')
    (hzE : ∀ x ∈ X, s(z x, x) ∉ E) (hbz : ∀ x ∈ X, b (z x) = 1)
    (hnb : ∀ x ∈ X, ∀ w, s(x, w) ∈ E → w ≠ x → b w ≠ 0 ∧ ∀ x' ∈ X, w ≠ z x') :
    ∃ b' : V → ℕ, Ach (E ∪ {e | ∃ x ∈ X, e = s(z x, x)}) b' ∧
      ∀ v, b' v + (if v ∈ X.image z then 1 else 0) = b v + (if v ∈ X then 1 else 0) := by
  classical
  revert hzX hinj hzE hbz hnb
  induction X using Finset.induction_on with
  | empty =>
    intro _ _ _ _ _
    exact ⟨b, h.congr (by ext e; simp) (fun _ => rfl), fun v => by simp⟩
  | @insert a X haX ih =>
    intro hzX hinj hzE hbz hnb
    have ha : a ∈ insert a X := Finset.mem_insert_self a X
    have sub : ∀ {x}, x ∈ X → x ∈ insert a X := fun hx => Finset.mem_insert_of_mem hx
    obtain ⟨b1, hb1, hid1⟩ := ih (fun x hx h' => hzX x (sub hx) (sub h'))
      (fun x hx x' hx' => hinj x (sub hx) x' (sub hx')) (fun x hx => hzE x (sub hx))
      (fun x hx => hbz x (sub hx))
      (fun x hx w hw hwx => ⟨(hnb x (sub hx) w hw hwx).1,
        fun x' hx' => (hnb x (sub hx) w hw hwx).2 x' (sub hx')⟩)
    have hza : z a ∉ insert a X := hzX a ha
    have hzaX : z a ∉ X := fun h' => hza (sub h')
    have hza' : z a ≠ a := fun h' => hza (by rw [h']; exact ha)
    have hzim : z a ∉ X.image z := by
      simp only [Finset.mem_image, not_exists, not_and]
      intro x hx h'
      exact haX (hinj x (sub hx) a ha h' ▸ hx)
    have haim : a ∉ X.image z := by
      simp only [Finset.mem_image, not_exists, not_and]
      intro x hx h'
      exact hzX x (sub hx) (by rw [h']; exact ha)
    have hb1z : b1 (z a) = 1 := by
      have := hid1 (z a)
      simp [hzim, hzaX, hbz a ha] at this
      omega
    have hb1a : b1 a = b a := by
      have := hid1 a
      simp [haim, haX] at this
      omega
    have hnotE : s(z a, a) ∉ E ∪ {e | ∃ x ∈ X, e = s(z x, x)} := by
      intro h'
      simp only [Set.mem_union, Set.mem_ofPred_eq] at h'
      rcases h' with h' | ⟨x, hx, h'⟩
      · exact hzE a ha h'
      · rw [Sym2.eq_iff] at h'
        rcases h' with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact haX (h2 ▸ hx)
        · exact hzaX (h1 ▸ hx)
    have key : ∀ w, s(a, w) ∈ E ∪ {e | ∃ x ∈ X, e = s(z x, x)} → w ≠ a → b1 w ≠ 0 := by
      intro w hw hwa
      simp only [Set.mem_union, Set.mem_ofPred_eq] at hw
      rcases hw with hw | ⟨x, hx, hw⟩
      · obtain ⟨h1, h2⟩ := hnb a ha w hw hwa
        have hwim : w ∉ X.image z := by
          simp only [Finset.mem_image, not_exists, not_and]
          intro x hx h'
          exact h2 x (sub hx) h'.symm
        have := hid1 w
        simp only [hwim, ite_false] at this
        omega
      · rw [Sym2.eq_iff] at hw
        rcases hw with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact absurd (h1 ▸ ha) (hzX x (sub hx))
        · exact absurd (h1 ▸ hx) haX
    have hbl : blankNbrs (E ∪ {e | ∃ x ∈ X, e = s(z x, x)}) b1 a = 0 := by
      have := blankNbrs_le_of_subset (S := (∅ : Set V)) (E := E ∪ {e | ∃ x ∈ X, e = s(z x, x)})
        (b := b1) (u := a) (fun w h1 h2 h3 => absurd h3 (key w h1 h2))
      simpa using this
    have h2 := hb1.transfer hza' hnotE (by rw [hbl, hb1z]; omega)
    refine ⟨_, h2.congr ?_ (fun _ => rfl), fun v => ?_⟩
    · ext e
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_ofPred_eq, Finset.mem_insert]
      constructor
      · rintro (rfl | h' | ⟨x, hx, rfl⟩)
        · exact Or.inr ⟨a, Or.inl rfl, rfl⟩
        · exact Or.inl h'
        · exact Or.inr ⟨x, Or.inr hx, rfl⟩
      · rintro (h' | ⟨x, rfl | hx, rfl⟩)
        · exact Or.inr (Or.inl h')
        · exact Or.inl rfl
        · exact Or.inr (Or.inr ⟨x, hx, rfl⟩)
    · rw [Finset.image_insert]
      have k := hid1 v
      by_cases hva : v = a
      · subst hva
        rw [mv_apply_recv]
        simp [haim, Ne.symm hza', haX] at k ⊢
        omega
      by_cases hvz : v = z a
      · subst hvz
        rw [mv_apply_donor _ hza']
        simp [hza', hzaX, hzim, hbz a ha] at k ⊢
        omega
      · rw [mv_apply_other _ hvz hva]
        simp [hva, hvz] at k ⊢
        omega

/-- **Relays, then a hub.** Let `s` meet no edge of `E` and have neighbour set `N` (`s ∉ N`) with
one end at each vertex of `N`. Relay into a subset `X ⊆ N` as in `Ach.relays`, from vertices
`z x` outside `N ∪ {s}`. If `|N| ≤ |X| + 5`, then inserting the star `sN` costs one path: each
`x ∈ X` has two ends after its relay, so the supply condition of `Ach.hub_general` holds. -/
theorem Ach.relay_hub {E : Set (Sym2 V)} {b : V → ℕ} (h : Ach E b) {s : V} (N X : Finset V)
    (z : V → V) (hs : ∀ w, s(s, w) ∉ E) (hsN : s ∉ N) (hXN : X ⊆ N)
    (hzN : ∀ x ∈ X, z x ∉ N) (hzs : ∀ x ∈ X, z x ≠ s)
    (hinj : ∀ x ∈ X, ∀ x' ∈ X, z x = z x' → x = x')
    (hzE : ∀ x ∈ X, s(z x, x) ∉ E) (hbz : ∀ x ∈ X, b (z x) = 1)
    (hnb : ∀ x ∈ X, ∀ w, s(x, w) ∈ E → w ≠ x → b w ≠ 0 ∧ ∀ x' ∈ X, w ≠ z x')
    (hbN : ∀ t ∈ N, b t = 1) (hd : 2 ≤ N.card) (hX : N.card ≤ X.card + 5) :
    ∃ R ⊆ N, R.card = N.card - 2 ∧ ∃ y y', y ∈ N ∧ y' ∈ N ∧ y ≠ y' ∧ y ∉ R ∧ y' ∉ R ∧
      ∃ b' : V → ℕ, Ach (E ∪ {e | ∃ x ∈ X, e = s(z x, x)} ∪ {e | ∃ t ∈ N, e = s(s, t)}) b' ∧
        ∀ v, b' v + (if v ∈ R then 1 else 0) + (if v ∈ X.image z then 1 else 0) =
          b v + (if v ∈ X then 1 else 0) + (N.card - 2) * (if v = s then 1 else 0) +
            (if v = y then 1 else 0) + (if v = y' then 1 else 0) := by
  classical
  have hzX : ∀ x ∈ X, z x ∉ X := fun x hx h' => hzN x hx (hXN h')
  obtain ⟨b1, hb1, hid1⟩ := h.relays X z hzX hinj hzE hbz hnb
  have hs1 : ∀ w, s(s, w) ∉ E ∪ {e | ∃ x ∈ X, e = s(z x, x)} := by
    intro w h'
    simp only [Set.mem_union, Set.mem_ofPred_eq] at h'
    rcases h' with h' | ⟨x, hx, h'⟩
    · exact hs w h'
    · rw [Sym2.eq_iff] at h'
      rcases h' with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hzs x hx h1.symm
      · exact hsN (h1 ▸ hXN hx)
  have hb1N : ∀ t ∈ N, b1 t = 1 + (if t ∈ X then 1 else 0) := by
    intro t ht
    have k := hid1 t
    have : t ∉ X.image z := by
      simp only [Finset.mem_image, not_exists, not_and]
      intro x hx h'
      exact hzN x hx (h' ▸ ht)
    simp only [this, ite_false, hbN t ht] at k
    omega
  have hsum : ∑ t ∈ N, b1 t = N.card + X.card := by
    rw [Finset.sum_congr rfl hb1N, Finset.sum_add_distrib, Finset.sum_boole]
    simp [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hXN]
  obtain ⟨R, hRN, hRc, y, y', hy, hy', hyy', hyR, hy'R, b2, hb2, hid2⟩ :=
    hb1.hub_general N hs1 hsN
      (fun t ht => by rw [hb1N t ht]; split_ifs <;> omega) hd (by rw [hsum]; omega)
  refine ⟨R, hRN, hRc, y, y', hy, hy', hyy', hyR, hy'R, b2, hb2, fun v => ?_⟩
  have k1 := hid1 v
  have k2 := hid2 v
  omega

end general

/-! ### Fan's alternative -/

section alternative

omit [DecidableEq V] in
/-- `FanPre` survives a reroute away from its vertices (the `FanPre` half of
`fanChain_transport`). -/
theorem fanPre_transport {K K₁ : SimpleGraph V} {D : PathDecomp K} {D₁ : PathDecomp K₁}
    {u t : V} {P : GPath K}
    (htrans : ∀ Q ∈ D.paths, Q ≠ P → ∃ Q' ∈ D₁.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
      Q'.walk.support = Q.walk.support)
    (hP' : ∃ P' ∈ D₁.paths, ∀ x z, x ≠ t →
      ((P.src = x ∧ [z, u] <:+: P.walk.support) ∨ (P.tgt = x ∧ [u, z] <:+: P.walk.support)) →
      (P'.tgt = x ∧ [u, z] <:+: P'.walk.support)) :
    ∀ l, t ∉ l → FanPre D u l → FanPre D₁ u l := by
  apply FanPre.transport
  rintro x z hx ⟨Q, hQ, hocc⟩
  by_cases hQP : Q = P
  · subst hQP
    obtain ⟨P', hP'mem, hP'⟩ := hP'
    exact ⟨P', hP'mem, Or.inr (hP' x z hx hocc)⟩
  · obtain ⟨Q', hQ', hs, ht, hsupp⟩ := htrans Q hQ hQP
    refine ⟨Q', hQ', ?_⟩
    rcases hocc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hs.trans h1, by rw [hsupp]; exact h2⟩
    · exact Or.inr ⟨ht.trans h1, by rw [hsupp]; exact h2⟩

/-- **Executing a partial chain.** Along a duplicate-free predecessor sequence
`t = x₀, x₁, …, x_k = z` (`k ≥ 1`) from a non-neighbour `t` of `u`, the graph `K + tu - zu` has a
decomposition of the same size with one end moved from `t` to `z`. These are the reroute steps of
`fan_exec` without its final append. -/
theorem fan_reroute_exec (u : V) : ∀ (xs : List V) {K : SimpleGraph V} (D : PathDecomp K)
    (t z : V), xs ≠ [] → (t :: xs).Nodup → FanPre D u (t :: xs) → (t :: xs).getLast? = some z →
    t ≠ u → ¬ K.Adj t u → ∀ K' : SimpleGraph V,
    (∀ e, e ∈ K'.edgeSet ↔ (e ∈ K.edgeSet ∧ e ≠ s(z, u)) ∨ e = s(t, u)) →
    ∃ D' : PathDecomp K', D'.size = D.size ∧
      ∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if z = w then 1 else 0)
  | [], _, _, _, _, h, _, _, _, _, _, _, _ => absurd rfl h
  | y :: rest, K, D, t, z, _, hnd, hpre, hlast, htu, hadj, K', hK' => by
    obtain ⟨hpred, hpre'⟩ := hpre
    have hyu : K.Adj y u := FanPred.adj hpred
    obtain ⟨P, hP, hocc⟩ := hpred
    have hty : t ≠ y := by
      rintro rfl; exact (List.nodup_cons.mp hnd).1 List.mem_cons_self
    have hyu' : y ≠ u := hyu.ne
    cases rest with
    | nil =>
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      obtain ⟨D', hs', he', -, -⟩ := D.reroute_move hadj hK' hP hocc
      exact ⟨D', hs', he'⟩
    | cons y' rest' =>
      let K₁ : SimpleGraph V := SimpleGraph.fromEdgeSet ((K.edgeSet \ {s(y, u)}) ∪ {s(t, u)})
      have hK₁ : ∀ e, e ∈ K₁.edgeSet ↔ (e ∈ K.edgeSet ∧ e ≠ s(y, u)) ∨ e = s(t, u) := by
        intro e
        simp only [K₁, edgeSet_fromEdgeSet, Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff,
          Sym2.mem_diagSet]
        constructor
        · rintro ⟨h, -⟩; exact h
        · intro h
          refine ⟨h, ?_⟩
          rcases h with ⟨he, -⟩ | rfl
          · exact K.not_isDiag_of_mem_edgeSet he
          · simpa using htu
      obtain ⟨D₁, hs₁, he₁, htrans, hP'⟩ := D.reroute_move hadj hK₁ hP hocc
      have hpre₁ : FanPre D₁ u (y :: y' :: rest') :=
        fanPre_transport htrans hP' _ (List.nodup_cons.mp hnd).1 hpre'
      have hadj₁ : ¬ K₁.Adj y u := by
        rw [← mem_edgeSet, hK₁]
        rintro (⟨-, h⟩ | h)
        · exact h rfl
        · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact hty h1.symm
          · exact hyu' h1
      have hz : z ∈ y' :: rest' := by
        have := List.mem_of_getLast? (by simpa using hlast)
        simpa using this
      have hzt : z ≠ t := by
        rintro rfl
        exact (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem _ hz)
      have hzy : z ≠ y := by
        rintro rfl
        exact (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 hz
      have hK'₁ : ∀ e, e ∈ K'.edgeSet ↔ (e ∈ K₁.edgeSet ∧ e ≠ s(z, u)) ∨ e = s(y, u) := by
        intro e
        rw [hK' e, hK₁ e]
        have hyuK : s(y, u) ∈ K.edgeSet := hyu
        have hzu_tu : s(z, u) ≠ s(t, u) := by
          intro h; rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, h2⟩
          · exact hzt h1
          · exact htu h2.symm
        have hyu_zu : s(y, u) ≠ s(z, u) := by
          intro h; rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, h2⟩
          · exact hzy h1.symm
          · exact hyu' h1
        constructor
        · rintro (⟨h, hz'⟩ | h)
          · by_cases hey : e = s(y, u)
            · exact Or.inr hey
            · exact Or.inl ⟨Or.inl ⟨h, hey⟩, hz'⟩
          · exact Or.inl ⟨Or.inr h, by rw [h]; exact hzu_tu.symm⟩
        · rintro (⟨⟨h, -⟩ | h, hz'⟩ | h)
          · exact Or.inl ⟨h, hz'⟩
          · exact Or.inr h
          · exact Or.inl ⟨h ▸ hyuK, h ▸ hyu_zu⟩
      obtain ⟨D', hs', he'⟩ := fan_reroute_exec u (y' :: rest') D₁ y z (by simp)
        (List.nodup_cons.mp hnd).2 hpre₁ (by simpa using hlast) hyu' hadj₁ K' hK'₁
      refine ⟨D', hs'.trans hs₁, fun w => ?_⟩
      have a := he' w
      have b := he₁ w
      omega

section count

variable [Fintype V] {K : SimpleGraph V} [DecidableRel K.Adj]

open Classical in
/-- **The counting half of Fan's alternative.** Either some chain from `T` terminates, or the
supply at `T` is at most the number of blank neighbours of `u` reachable by predecessor
sequences from `T`. -/
theorem fan_alt_count (D : PathDecomp K) (u : V) (T : Finset V) (huT : u ∉ T)
    (hT : ∀ t ∈ T, ¬ K.Adj t u) :
    (∃ t ∈ T, ∃ xs, (t :: xs).Nodup ∧ FanChain D u (t :: xs)) ∨
      ∑ t ∈ T, D.ends t ≤ (Finset.univ.filter (fun w => K.Adj u w ∧ D.ends w = 0 ∧
        ∃ t ∈ T, ∃ xs : List V, (t :: xs).Nodup ∧ FanPre D u (t :: xs) ∧
          (t :: xs).getLast? = some w)).card := by
  classical
  by_cases hno : ∃ t ∈ T, ∃ xs, (t :: xs).Nodup ∧ FanChain D u (t :: xs)
  · exact Or.inl hno
  right
  let Reach : V → Prop := fun x => ∃ t ∈ T, ∃ xs : List V, (t :: xs).Nodup ∧
    FanPre D u (t :: xs) ∧ (t :: xs).getLast? = some x
  have hnoav : ∀ x, Reach x → ¬ FanAvoid D u x := by
    rintro x ⟨t, ht, xs, hnd, hpre, hlast⟩ hav
    exact hno ⟨t, ht, xs, hnd, hpre, x, hlast, hav⟩
  let R : Finset V := Finset.univ.filter Reach
  have hTR : T ⊆ R := fun t ht =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ht, [], by simp, trivial, rfl⟩
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
  -- every end at `R` lies on a path through `u`
  have hthru : ∀ P ∈ D.paths, ∀ x ∈ R, (P.src = x ∨ P.tgt = x) → u ∈ P.walk.support := by
    intro P hP x hx hend
    by_contra hu
    exact hnoav x (Finset.mem_filter.mp hx).2 ⟨P, hP, hend, hu⟩
  let p : Sym2 V → Bool := fun e => decide (u ∈ e ∧ ∃ z ∈ R, z ∈ e)
  -- per path: ends at `R` ≤ edges from `u` into `R`
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
  -- edges from `u` into `R`
  let NR : Finset V := R.filter (fun z => K.Adj u z)
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
  have hkey : ∀ S : Finset V,
      S.card ≤ ∑ w ∈ S, D.ends w + (S.filter (fun w => D.ends w = 0)).card := by
    intro S
    rw [Finset.card_filter, ← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro w _
    split_ifs <;> omega
  have h2 := hkey NR
  have h3 : (NR.filter (fun w => D.ends w = 0)).card ≤
      (Finset.univ.filter (fun w => K.Adj u w ∧ D.ends w = 0 ∧
        ∃ t ∈ T, ∃ xs : List V, (t :: xs).Nodup ∧ FanPre D u (t :: xs) ∧
          (t :: xs).getLast? = some w)).card := by
    apply Finset.card_le_card
    intro w hw
    simp only [NR, R, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hw.1.2, hw.2, hw.1.1⟩
  omega


omit [Fintype V] [DecidableRel K.Adj] in
theorem one_le_ends_of_end (D : PathDecomp K) {P : GPath K} (hP : P ∈ D.paths) {t : V}
    (h : P.src = t ∨ P.tgt = t) : 1 ≤ D.ends t := by
  have h1 : 1 ≤ P.endsAt t := by
    unfold GPath.endsAt
    rcases h with h | h <;> simp [h]
  exact h1.trans (List.le_sum_of_mem (List.mem_map_of_mem hP))

omit [Fintype V] [DecidableRel K.Adj] in
theorem one_le_ends_of_fanPred {D : PathDecomp K} {u t y : V} (h : FanPred D u t y) :
    1 ≤ D.ends t := by
  obtain ⟨P, hP, ⟨h1, -⟩ | ⟨h1, -⟩⟩ := h
  · exact one_le_ends_of_end D hP (Or.inl h1)
  · exact one_le_ends_of_end D hP (Or.inr h1)

/-- **Fan's alternative** (missing-move manuscript, Lemma 4.2). Let `T` be a set of
non-neighbours of `u` with `u ∉ T`. Then either some `t ∈ T` with an end gives an end to `u`
(Fan's conclusion), or there is a set `W` of **blank** neighbours of `u` with
`|W| ≥ ∑_{t ∈ T} ends t` such that every `z ∈ W` can be *activated*: for some `t ∈ T` with an
end, `K + tu - zu` has a decomposition of the same size with one end moved from `t` to `z`.
If `∑_T ends > #blank neighbours`, the second case is impossible; this is `fan_grouped`. -/
theorem fan_alternative (D : PathDecomp K) (u : V) (T : Finset V) (huT : u ∉ T)
    (hT : ∀ t ∈ T, ¬ K.Adj t u) :
    (∃ t ∈ T, 1 ≤ D.ends t ∧ ∀ K' : SimpleGraph V,
        (∀ e, e ∈ K'.edgeSet ↔ e ∈ K.edgeSet ∨ e = s(t, u)) →
        ∃ D' : PathDecomp K', D'.size = D.size ∧
          ∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if u = w then 1 else 0)) ∨
    ∃ W : Finset V, ∑ t ∈ T, D.ends t ≤ W.card ∧ (∀ z ∈ W, K.Adj u z ∧ D.ends z = 0) ∧
      ∀ z ∈ W, ∃ t ∈ T, 1 ≤ D.ends t ∧ ∀ K' : SimpleGraph V,
        (∀ e, e ∈ K'.edgeSet ↔ (e ∈ K.edgeSet ∧ e ≠ s(z, u)) ∨ e = s(t, u)) →
        ∃ D' : PathDecomp K', D'.size = D.size ∧
          ∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if z = w then 1 else 0) := by
  classical
  rcases fan_alt_count D u T huT hT with ⟨t, ht, xs, hnd, hch⟩ | hcount
  · left
    refine ⟨t, ht, ?_, fun K' hK' =>
      fan_exec u xs D t hnd hch (fun h => huT (h ▸ ht)) (hT t ht) K' hK'⟩
    obtain ⟨hpre, x, hx, Q, hQ, hend, -⟩ := hch
    cases xs with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hx
      subst hx
      exact one_le_ends_of_end D hQ hend
    | cons y rest => exact one_le_ends_of_fanPred hpre.1
  · right
    refine ⟨_, hcount, fun z hz => ?_, fun z hz => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      exact ⟨hz.1, hz.2.1⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      obtain ⟨hadj, -, t, ht, xs, hnd, hpre, hlast⟩ := hz
      cases xs with
      | nil =>
        simp only [List.getLast?_singleton, Option.some.injEq] at hlast
        subst hlast
        exact absurd hadj.symm (hT t ht)
      | cons y rest =>
        exact ⟨t, ht, one_le_ends_of_fanPred hpre.1, fun K' hK' =>
          fan_reroute_exec u (y :: rest) D t z (by simp) hnd hpre hlast
            (fun h => huT (h ▸ ht)) (hT t ht) K' hK'⟩

end count

end alternative

/-! ### The critical order-8 loser `Gqz~vw` -/

section gqz

/-- Adjacency of `Gqz~vw`: `K₈` minus `{03, 12, 23, 34, 56, 67}`. -/
def gqzAdj (a b : Fin 8) : Bool :=
  a != b && !([(0, 3), (1, 2), (2, 3), (3, 4), (5, 6), (6, 7)].any
    (fun p : ℕ × ℕ => (p.1 == a.val && p.2 == b.val) || (p.1 == b.val && p.2 == a.val)))

theorem gqzAdj_symm : ∀ a b : Fin 8, gqzAdj a b = true → gqzAdj b a = true := by decide
theorem gqzAdj_irrefl : ∀ a : Fin 8, gqzAdj a a = false := by decide

/-- The critical order-8 graph `Gqz~vw` (graph6). -/
def gqzGraph : SimpleGraph (Fin 8) where
  Adj a b := gqzAdj a b = true
  symm := ⟨fun a b h => gqzAdj_symm a b h⟩
  loopless := ⟨fun a h => by rw [gqzAdj_irrefl] at h; exact Bool.false_ne_true h⟩

instance : DecidableRel gqzGraph.Adj := fun a b => inferInstanceAs (Decidable (gqzAdj a b = true))

/-- **The critical order-8 loser of the original Fan game is closed by the odd-neighbour hub.**
`Gqz~vw` is 4-connected with `p = 4 = n/2`, and the original game loses it at the root `3`. Hub
`s = 3` (degree 4), odd neighbour `x = 6`, and `z = 0`. -/
theorem gqz_rooted_three : pathNumber (addLeaf gqzGraph 3) ≤ Fintype.card (Fin 8) / 2 :=
  hub_four_odd_rooted gqzGraph (by decide) (s := 3) (x := 6) (z := 0) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Or.inl rfl)

end gqz

end Gallai
