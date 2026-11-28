import GallaiLean.Test2Converse

/-!
# The all-odd twin of the forest lift, for Test1 (session `claude/test2`)

Manuscript: `manuscripts/test2/test2.tex`, §`sec:allodd` (`thm:oddlift`, `cor:oddmatch`).

Let `z` be the only even vertex of `J` and `r ∈ N(z)`. In `B = J − z` the even vertices are exactly
`T = N(z)`, `r` included. Let `Φ` be a forest `T`-join of `B` (a list `L` of (child, parent) pairs
in parent-first order), rooted so that **`r` is never a child**. Then `H = B − Φ` has **no** even
vertex, so a Lovász decomposition of `H` has one end at every vertex and exactly `|B|/2` paths. If it
satisfies
* (i) the path ending at each child `v` avoids `p(v)`, and
* (ii) no path has two siblings as its two ends,
the forest can be appended (`append_forest_ends`), and `r` then ends `1 + c(r) ≥ 2` paths, since its
`Φ`-degree `c(r)` is odd. That is Test1 at `(z, r)`, with no leaf and no trimming
(**`test1At_of_oddBase`**).

The base graph is the same all-odd graph `B − Φ` as for the Test2 forest lift (there `z` hangs as an
extra leaf at `r`), with the odd set `T = N(z)` in both cases. So both spine tests reduce to the
same constrained Lovász problem in a graph without even vertices.

The matching case (**`test1At_of_matchingOdd`**): `Φ` a perfect matching of `J[N(z)]` with `r`
matched to `a₀`. The conditions are `r ∉ Q(a₀)` and, for every other pair `ab`, `a ∉ Q(b)` or
`b ∉ Q(a)` (the orientation of each pair is then chosen by the disjunction, `orientPairs`).

## Main results

* `OddData`, `OddBase`, **`twoEnds_of_oddBase`** (any graph `B` whose even vertices are `T`).
* `even_delVert_iff_adj`: in a Test1 instance the even vertices of `J − z` are `N(z)`.
* **`test1At_of_oddBase`**.
* `orientPairs` and its facts; **`oddBase_of_matching`**, **`test1At_of_matchingOdd`**.
-/

open SimpleGraph

namespace Gallai

universe u

section allOdd

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **All-odd forest data** on a graph `B` whose even vertices are the list `T`: a forest `Φ` of
`B` whose odd-degree vertices are exactly `T`, given by (child, parent) pairs in parent-first
order, with `r ∈ T` never a child. -/
structure OddData (B : SimpleGraph W) (r : W) (T : List W) (L : List (W × W)) : Prop where
  edge : ∀ p ∈ L, B.Adj p.1 p.2
  r_mem : r ∈ T
  child_ne_r : ∀ p ∈ L, p.1 ≠ r
  children : (L.map Prod.fst).Nodup
  edges : (L.map pairEdge).Nodup
  parent_first : L.Pairwise (fun p q => p.2 ≠ q.1)
  tjoin : ∀ v, (L.map pairEdge).countP (fun e => decide (v ∈ e)) % 2 = if v ∈ T then 1 else 0

/-- **An all-odd base**: all-odd data and a Lovász decomposition of `B − Φ` with (i) and (ii). -/
def OddBase (B : SimpleGraph W) [DecidableRel B.Adj] (r : W) (T : List W) : Prop :=
  ∃ L, OddData B r T L ∧ ∃ D₀ : PathDecomp (delList B (L.map pairEdge)),
    (∀ v, D₀.ends v = (delList B (L.map pairEdge)).degree v % 2) ∧
    (∀ p ∈ L, ∀ P ∈ D₀.paths, (P.src = p.1 ∨ P.tgt = p.1) → p.2 ∉ P.walk.support) ∧
    (∀ p ∈ L, ∀ q ∈ L, p.1 ≠ q.1 → p.2 = q.2 → ∀ P ∈ D₀.paths,
      ¬ ((P.src = p.1 ∨ P.tgt = p.1) ∧ (P.src = q.1 ∨ P.tgt = q.1)))

/-- **The all-odd lift** (manuscript `thm:oddlift`). If the even vertices of `B` are exactly the
vertices of `T`, an all-odd base rooted at `r` gives a decomposition of `B` into at most `|B|/2`
paths with at least two ends at `r`. -/
theorem twoEnds_of_oddBase (B : SimpleGraph W) [DecidableRel B.Adj] {r : W} {T : List W}
    (hev : ∀ v, Even (B.degree v) ↔ v ∈ T) (h : OddBase B r T) :
    ∃ D : PathDecomp B, D.size ≤ Fintype.card W / 2 ∧ 2 ≤ D.ends r := by
  obtain ⟨L, hF, D₀, hD₀, hi, hii⟩ := h
  have hnd : (L.map pairEdge).Nodup := hF.edges
  have hin : ∀ e ∈ L.map pairEdge, e ∈ B.edgeSet := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    exact hF.edge p hp
  have hdeg := delList_degree_count B (L.map pairEdge) hnd hin
  -- every vertex is odd in `B − Φ`
  have hodd : ∀ v, (delList B (L.map pairEdge)).degree v % 2 = 1 := by
    intro v
    have h1 := hdeg v
    have ht := hF.tjoin v
    by_cases hT : v ∈ T
    · have he : Even (B.degree v) := (hev v).2 hT
      rw [Nat.even_iff] at he
      simp only [hT, ite_true] at ht
      omega
    · have ho : ¬ Even (B.degree v) := fun he => hT ((hev v).1 he)
      rw [Nat.not_even_iff] at ho
      simp only [hT, ite_false] at ht
      omega
  have hone : ∀ v, D₀.ends v = 1 := fun v => by rw [hD₀, hodd]
  have hnotK : ∀ p ∈ L, ¬ (delList B (L.map pairEdge)).Adj p.1 p.2 := fun p hp h =>
    h.2 (List.mem_map_of_mem hp)
  have hG : ∀ e, e ∈ B.edgeSet ↔ e ∈ (delList B (L.map pairEdge)).edgeSet ∨ e ∈ L.map pairEdge := by
    intro e
    rw [delList_edgeSet]
    constructor
    · intro he
      by_cases hm : e ∈ L.map pairEdge
      · exact Or.inr hm
      · exact Or.inl ⟨he, hm⟩
    · rintro (⟨he, -⟩ | hm)
      · exact he
      · exact hin e hm
  obtain ⟨D, hDs, hDe⟩ := append_forest_ends (G := B) L (delList B (L.map pairEdge)) hG hnotK
    hF.children hF.edges hF.parent_first D₀ (fun p _ => by rw [hone]) hi hii
  refine ⟨D, ?_, ?_⟩
  · -- one end per vertex in `D₀`
    have h2 : 2 * D₀.size ≤ Fintype.card W := by
      rw [← D₀.sum_ends]
      have h1 : ∑ v, D₀.ends v ≤ ∑ _v : W, 1 :=
        Finset.sum_le_sum fun v _ => by rw [hone v]
      refine h1.trans (le_of_eq ?_)
      simp
    omega
  · -- `r` is never a child, and it has at least one child (its `Φ`-degree is odd)
    have h0 : L.countP (fun p => decide (p.1 = r)) = 0 :=
      List.countP_eq_zero.mpr (fun p hp => by simpa using hF.child_ne_r p hp)
    have hc : 1 ≤ L.countP (fun p => decide (p.2 = r)) := by
      have ht := hF.tjoin r
      simp only [hF.r_mem, ite_true] at ht
      have hpos : 0 < (L.map pairEdge).countP (fun e => decide (r ∈ e)) := by omega
      obtain ⟨e, he, hre⟩ := List.countP_pos_iff.mp hpos
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
      have hr : r ∈ s(p.1, p.2) := by simpa [pairEdge] using hre
      rcases Sym2.mem_iff.mp hr with h | h
      · exact absurd h.symm (hF.child_ne_r p hp)
      · exact List.countP_pos_iff.mpr ⟨p, hp, by simp [h]⟩
    have := hDe r
    rw [h0, hone r] at this
    omega

end allOdd

section allOddT1

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- In a Test1 instance (`z` the only even vertex of `J`), the even vertices of `J − z` are exactly
the neighbours of `z`. -/
theorem even_delVert_iff_adj (J : SimpleGraph V) [DecidableRel J.Adj] {z : V}
    (hz : ∀ v, Even (J.degree v) ↔ v = z) (v : {v | v ≠ z}) :
    Even ((delVert J z).degree v) ↔ J.Adj z v := by
  have hd := delVert_degree (J := J) z v
  have hvz : (v : V) ≠ z := v.2
  have hodd : J.degree v % 2 = 1 :=
    Nat.odd_iff.mp (Nat.not_even_iff_odd.mp (fun he => hvz ((hz v).1 he)))
  rw [Nat.even_iff, ← J.adj_comm]
  by_cases ha : J.Adj (v : V) z
  · simp only [ha, ite_true] at hd
    simp only [ha, iff_true]
    omega
  · simp only [ha, ite_false, add_zero] at hd
    simp only [ha, iff_false]
    omega

/-- **The all-odd lift gives Test1** (manuscript `thm:oddlift`). Let `z` be the only even vertex of
`J`, let `r ∈ N(z)`, and let `T` list `N(z)` (as vertices of `J − z`). An all-odd base of `J − z`
rooted at `r` gives Test1 at `(z, r)`. -/
theorem test1At_of_oddBase (J : SimpleGraph V) [DecidableRel J.Adj] {z r : V}
    (hz : ∀ v, Even (J.degree v) ↔ v = z) (hrz : r ≠ z) {T : List {v | v ≠ z}}
    (hT : ∀ v : {v | v ≠ z}, J.Adj z v ↔ v ∈ T)
    (h : OddBase (delVert J z) ⟨r, hrz⟩ T) : Test1At J z r := by
  intro hr
  have hev : ∀ v, Even ((delVert J z).degree v) ↔ v ∈ T := fun v =>
    (even_delVert_iff_adj J hz v).trans (hT v)
  obtain ⟨D, hD, hDr⟩ := twoEnds_of_oddBase (delVert J z) hev h
  have hcard := card_delVert (W := V) z
  exact ⟨D, by rw [hcard] at hD; exact hD, hDr⟩

end allOddT1

/-! ### The matching case -/

section orient

variable {W : Type*} [Fintype W] [DecidableEq W]

open Classical in
/-- Orient every pair `(a, b)` of `L` so that the path ending at the first vertex avoids the
second, where possible: keep `(a, b)` if every path of `D` ending at `a` avoids `b`, else swap. -/
noncomputable def orientPairs {K : SimpleGraph W} (D : PathDecomp K) (L : List (W × W)) :
    List (W × W) :=
  L.map fun p => if (∀ P ∈ D.paths, (P.src = p.1 ∨ P.tgt = p.1) → p.2 ∉ P.walk.support) then p
    else p.swap

omit [Fintype W] in
theorem mem_orientPairs {K : SimpleGraph W} {D : PathDecomp K} {L : List (W × W)} {q : W × W}
    (hq : q ∈ orientPairs D L) : ∃ p ∈ L, q = p ∨ q = p.swap := by
  classical
  unfold orientPairs at hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  refine ⟨p, hp, ?_⟩
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

omit [Fintype W] in
theorem orientPairs_pairEdge {K : SimpleGraph W} (D : PathDecomp K) (L : List (W × W)) :
    (orientPairs D L).map pairEdge = L.map pairEdge := by
  classical
  unfold orientPairs
  rw [List.map_map]
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply]
  split_ifs
  · rfl
  · simp [pairEdge, Sym2.eq_swap]

omit [Fintype W] in
theorem orientPairs_perm {K : SimpleGraph W} (D : PathDecomp K) :
    ∀ L : List (W × W), (pairVerts (orientPairs D L)).Perm (pairVerts L)
  | [] => by simp [orientPairs, pairVerts]
  | p :: L => by
    classical
    have ih := orientPairs_perm D L
    have hcons : orientPairs D (p :: L) =
        (if (∀ P ∈ D.paths, (P.src = p.1 ∨ P.tgt = p.1) → p.2 ∉ P.walk.support) then p
          else p.swap) :: orientPairs D L := by
      simp [orientPairs]
    rw [hcons, pairVerts_cons, pairVerts_cons]
    split_ifs
    · exact (ih.cons _).cons _
    · simp only [Prod.fst_swap, Prod.snd_swap]
      exact (List.Perm.swap _ _ _).trans ((ih.cons _).cons _)

omit [Fintype W] in
/-- Each oriented pair satisfies its condition, given the disjunction for every pair. -/
theorem orientPairs_avoid {K : SimpleGraph W} {D : PathDecomp K} {L : List (W × W)}
    (hdisj : TriangleDisj D L) :
    ∀ q ∈ orientPairs D L, ∀ P ∈ D.paths, (P.src = q.1 ∨ P.tgt = q.1) → q.2 ∉ P.walk.support := by
  classical
  intro q hq
  unfold orientPairs at hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  split_ifs with hc
  · exact hc
  · rcases hdisj p hp with h | h
    · simpa using h
    · exact absurd h hc

/-- **The all-odd base from a matching** (manuscript `cor:oddmatch`). Let the even vertices of `B`
be exactly the vertices of the disjoint pairs `(a₀, r) :: L`, edges of `B`. A Lovász decomposition
of `B` minus these edges in which the path ending at `a₀` avoids `r`, and in which every other pair
satisfies its disjunction, is an all-odd base rooted at `r`. -/
theorem oddBase_of_matching (B : SimpleGraph W) [DecidableRel B.Adj] {a₀ r : W}
    {L : List (W × W)} (hnd : (pairVerts ((a₀, r) :: L)).Nodup)
    (hedge : ∀ p ∈ (a₀, r) :: L, B.Adj p.1 p.2)
    (D₀ : PathDecomp (delList B (((a₀, r) :: L).map pairEdge)))
    (hD₀ : ∀ v, D₀.ends v = (delList B (((a₀, r) :: L).map pairEdge)).degree v % 2)
    (hfix : ∀ P ∈ D₀.paths, (P.src = a₀ ∨ P.tgt = a₀) → r ∉ P.walk.support)
    (hdisj : TriangleDisj D₀ L) :
    OddBase B r (pairVerts ((a₀, r) :: L)) := by
  set L' := (a₀, r) :: orientPairs D₀ L with hL'
  have hmap : L'.map pairEdge = ((a₀, r) :: L).map pairEdge := by
    show pairEdge (a₀, r) :: List.map pairEdge (orientPairs D₀ L) =
      pairEdge (a₀, r) :: List.map pairEdge L
    exact congrArg _ (orientPairs_pairEdge D₀ L)
  have hperm : (pairVerts L').Perm (pairVerts ((a₀, r) :: L)) := by
    rw [hL', pairVerts_cons, pairVerts_cons]
    exact ((orientPairs_perm D₀ L).cons _).cons _
  have hnd' : (pairVerts L').Nodup := hperm.nodup_iff.mpr hnd
  obtain ⟨hfst, hsnd, hpf, -, -⟩ := pairVerts_facts L' hnd'
  have hnd0 := hnd
  rw [pairVerts_cons, List.nodup_cons, List.nodup_cons, List.mem_cons, not_or] at hnd0
  obtain ⟨⟨ha0r, -⟩, hrL, -⟩ := hnd0
  have hmemL : ∀ q ∈ orientPairs D₀ L, q.1 ∈ pairVerts L := by
    intro q hq
    obtain ⟨p, hp, rfl | rfl⟩ := mem_orientPairs hq
    · exact fst_mem_pairVerts hp
    · exact snd_mem_pairVerts hp
  have hdata : OddData B r (pairVerts ((a₀, r) :: L)) L' := by
    refine ⟨?_, ?_, ?_, hfst, ?_, ?_, ?_⟩
    · intro q hq
      have hq' : q ∈ (a₀, r) :: orientPairs D₀ L := hq
      rcases List.mem_cons.mp hq' with rfl | hq
      · exact hedge _ List.mem_cons_self
      · obtain ⟨p, hp, h | h⟩ := mem_orientPairs hq
        · rw [h]; exact hedge p (List.mem_cons_of_mem _ hp)
        · rw [h]; exact (hedge p (List.mem_cons_of_mem _ hp)).symm
    · rw [pairVerts_cons]; simp
    · intro q hq
      have hq' : q ∈ (a₀, r) :: orientPairs D₀ L := hq
      rcases List.mem_cons.mp hq' with rfl | hq
      · exact ha0r
      · intro h
        exact hrL (h ▸ hmemL q hq)
    · exact nodup_map_pairEdge L' hnd'
    · refine List.Pairwise.imp_of_mem (R := fun _ _ => True)
        (@fun p q hp hq _ h => hpf p hp ?_) (List.pairwise_of_forall (fun _ _ => trivial))
      rw [h]
      exact List.mem_map_of_mem hq
    · intro v
      rw [countP_pairEdge_of_nodup L' hnd' v]
      simp only [hperm.mem_iff]
      split_ifs <;> rfl
  refine ⟨L', hdata, ?_⟩
  rw [hmap]
  refine ⟨D₀, hD₀, ?_, ?_⟩
  · intro q hq
    have hq' : q ∈ (a₀, r) :: orientPairs D₀ L := hq
    rcases List.mem_cons.mp hq' with rfl | hq
    · exact hfix
    · exact orientPairs_avoid hdisj q hq
  · intro p hp q hq h1 h2
    exact absurd (List.inj_on_of_nodup_map hsnd hp hq h2) (fun h => h1 (h ▸ rfl))

end orient

section matchingT1

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **The matching case of the all-odd lift gives Test1** (manuscript `cor:oddmatch`). Let `z` be
the only even vertex of `J` and `r ∈ N(z)`. Let `(a₀, r) :: L` be disjoint pairs, edges of `J − z`,
covering exactly `N(z)`, and let `H = (J − z)` minus these edges (no even vertex). If some Lovász
decomposition of `H` has `r ∉ Q(a₀)` and, for every other pair `ab`, `a ∉ Q(b)` or `b ∉ Q(a)`, then
Test1 holds at `(z, r)`. -/
theorem test1At_of_matchingOdd (J : SimpleGraph V) [DecidableRel J.Adj] {z r : V}
    (hz : ∀ v, Even (J.degree v) ↔ v = z) (hrz : r ≠ z) {a₀ : {v | v ≠ z}}
    {L : List ({v | v ≠ z} × {v | v ≠ z})}
    (hnd : (pairVerts ((a₀, ⟨r, hrz⟩) :: L)).Nodup)
    (hcover : ∀ v : {v | v ≠ z}, J.Adj z v ↔ v ∈ pairVerts ((a₀, ⟨r, hrz⟩) :: L))
    (hedge : ∀ p ∈ (a₀, ⟨r, hrz⟩) :: L, (delVert J z).Adj p.1 p.2)
    (D₀ : PathDecomp (delList (delVert J z) (((a₀, ⟨r, hrz⟩) :: L).map pairEdge)))
    (hD₀ : ∀ v, D₀.ends v =
      (delList (delVert J z) (((a₀, ⟨r, hrz⟩) :: L).map pairEdge)).degree v % 2)
    (hfix : ∀ P ∈ D₀.paths, (P.src = a₀ ∨ P.tgt = a₀) → ⟨r, hrz⟩ ∉ P.walk.support)
    (hdisj : TriangleDisj D₀ L) : Test1At J z r :=
  test1At_of_oddBase J hz hrz hcover (oddBase_of_matching (delVert J z) hnd hedge D₀ hD₀ hfix hdisj)

end matchingT1

end Gallai
