import GallaiLean.Test1AllOdd

/-!
# Roots without matching data: twin pairs and the fat theta (session `claude/nodata`)

Manuscript: `manuscripts/nodata/nodata.tex`.

A *twin pair* is two vertices `x, y` of degree two in a graph `G` with the same two neighbours
`a, b`. Deleting the four edges `ax, xb, ay, yb` and re-inserting them costs exactly one path, and
the ends change only at `x`, which gains two (`PathDecomp.twin_insert`). This is the 4-cycle
`a y b x a` inserted by `PathDecomp.cycle_insert` (eulerian-cone, Lemma 5.2): both new vertices
have no other edge, and only `b` may.

Consequences.
* **The fat theta** `K_{3,t} + h₂h₃` (`fatTheta`): Test1 holds at its unique even vertex for every
  even `t ≥ 2` (`test1_fatTheta`). This is the family on which the all-odd forest lift has no base
  (manuscript `test2`, example `ex:t1theta`, `t = 6`). The proof is by induction on `t` using
  `theta_decomp` (the theta graph with `2n` leaves has `n + 1` paths), and the root `r` itself is
  taken as one of the twins.
* **Twin reductions** for arbitrary `J` (`test1At_of_twins`, `test2At_of_twins`): if two vertices
  of `N(z)` have the same neighbourhood `{z, a, b}`, then Test1 (Test2) at `(J, z, r)` follows
  from a decomposition of `J − z` with the four twin edges removed using one path fewer, with the
  same end condition at `r` (and none at all if `r` is one of the twins, for Test1).

## Main results

* `PathDecomp.twin_insert`.
* `theta`, `theta_decomp`, `theta_rooted`.
* `fatTheta`, **`test1_fatTheta`**.
* `twinDel`, **`test1At_of_twins`**, **`test2At_of_twins`**.
-/

open SimpleGraph

namespace Gallai

universe u

section twin

variable {U : Type u} [DecidableEq U]

/-- **Twin insertion.** Let `x, y` have no `K`-edge, and let `G` be `K` plus the four edges
`ax, xb, ay, yb`, where `a ≠ b` and `a` has a `K`-edge. A decomposition of `K` gives one of `G`
with one more path, the same ends everywhere except at `x`, and two more ends at `x`. -/
theorem PathDecomp.twin_insert {K G : SimpleGraph U} (D' : PathDecomp K) {a b x y : U}
    (hab : a ≠ b) (hxy : x ≠ y) (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (h1 : G.Adj a x) (h2 : G.Adj x b) (h3 : G.Adj a y) (h4 : G.Adj y b)
    (hG : ∀ e, e ∈ G.edgeSet ↔
      e ∈ K.edgeSet ∨ e = s(a, x) ∨ e = s(x, b) ∨ e = s(a, y) ∨ e = s(y, b))
    (hx : ∀ w, ¬ K.Adj x w) (hy : ∀ w, ¬ K.Adj y w) (ha : ∃ w, K.Adj a w) :
    ∃ D : PathDecomp G, D.size = D'.size + 1 ∧
      ∀ w, D.ends w = D'.ends w + (if w = x then 2 else 0) := by
  -- the path `R = a y b x` and the closing edge `x a`
  have hp : (Walk.cons h3 (Walk.cons h4 (Walk.cons h2.symm Walk.nil)) : G.Walk a x).IsPath := by
    rw [Walk.isPath_def]
    simp [hab, hxy.symm, hxa.symm, hxb.symm, hya.symm, hyb]
  let R : GPath G := ⟨a, x, _, hp, by simp⟩
  have hRe : R.edges = [s(a, y), s(y, b), s(b, x)] := rfl
  have hRs : R.walk.support = [a, y, b, x] := rfl
  have hKx : ∀ w, s(x, w) ∉ K.edgeSet := fun w h => hx w h
  have hKy : ∀ w, s(y, w) ∉ K.edgeSet := fun w h => hy w h
  refine D'.cycle_insert (a := a) (c := x) (b := b) R rfl rfl h1.symm (fun e => ?_) ?_ ?_ ?_
    hx ?_ ha
  · rw [hG e, hRe]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    have e1 : s(a, x) = s(x, a) := Sym2.eq_swap
    have e2 : s(x, b) = s(b, x) := Sym2.eq_swap
    rw [e1, e2]
    tauto
  · intro e he
    rw [hRe] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · rw [Sym2.eq_swap]; exact hKy a
    · exact hKy b
    · rw [Sym2.eq_swap]; exact hKx b
  · exact hKx a
  · rw [hRe]
    intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h
    · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hxa h1
      · exact hxy h1
    · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hxy h1
      · exact hxb h1
    · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h1⟩
      · exact hxb h1
      · exact hab h1
  · intro v hv hva hvb w
    rw [hRs] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact absurd rfl hva
    · exact hy w
    · exact absurd rfl hvb
    · exact hx w

end twin

/-! ### The theta graph and the fat theta -/

section theta

variable {U : Type u} [DecidableEq U]

/-- The **theta graph** with hubs `a, b` and leaf set `L`: the edge `ab` and the edges `ℓa, ℓb`
for `ℓ ∈ L`. -/
def theta (a b : U) (L : Finset U) : SimpleGraph U :=
  SimpleGraph.fromEdgeSet {e | e = s(a, b) ∨ ∃ ℓ ∈ L, e = s(ℓ, a) ∨ e = s(ℓ, b)}

omit [DecidableEq U] in
theorem theta_adj {a b : U} {L : Finset U} {v w : U} :
    (theta a b L).Adj v w ↔
      (s(v, w) = s(a, b) ∨ ∃ ℓ ∈ L, s(v, w) = s(ℓ, a) ∨ s(v, w) = s(ℓ, b)) ∧ v ≠ w := by
  simp [theta, SimpleGraph.fromEdgeSet_adj]

omit [DecidableEq U] in
theorem mem_theta_edgeSet {a b : U} {L : Finset U} (hab : a ≠ b) (haL : a ∉ L) (hbL : b ∉ L)
    (e : Sym2 U) :
    e ∈ (theta a b L).edgeSet ↔ e = s(a, b) ∨ ∃ ℓ ∈ L, e = s(ℓ, a) ∨ e = s(ℓ, b) := by
  simp only [theta, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, Set.mem_ofPred_eq]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    rcases h with rfl | ⟨ℓ, hℓ, rfl | rfl⟩
    · simpa using hab
    · have : ℓ ≠ a := fun h => haL (h ▸ hℓ)
      simpa using this
    · have : ℓ ≠ b := fun h => hbL (h ▸ hℓ)
      simpa using this

omit [DecidableEq U] in
/-- A leaf outside `L` (and not a hub) has no edge in the theta graph. -/
theorem theta_isolated {a b : U} {L : Finset U} {x : U} (hxa : x ≠ a) (hxb : x ≠ b)
    (hxL : x ∉ L) (w : U) : ¬ (theta a b L).Adj x w := by
  rw [theta_adj]
  rintro ⟨h | ⟨ℓ, hℓ, h | h⟩, -⟩
  · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hxa h1
    · exact hxb h1
  · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hxL (h1 ▸ hℓ)
    · exact hxa h1
  · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hxL (h1 ▸ hℓ)
    · exact hxb h1

omit [DecidableEq U] in
/-- The single edge `ab` as a decomposition of `theta a b ∅`. -/
theorem theta_empty_decomp {a b : U} (hab : a ≠ b) :
    ∃ D : PathDecomp (theta a b ∅), D.size = 1 := by
  have hadj : (theta a b ∅).Adj a b := by
    rw [theta_adj]; exact ⟨Or.inl rfl, hab⟩
  refine ⟨⟨[GPath.ofAdj hadj], by simp [GPath.ofAdj_edges], fun e => ?_⟩, rfl⟩
  rw [mem_theta_edgeSet hab (Finset.notMem_empty a) (Finset.notMem_empty b)]
  simp [GPath.ofAdj_edges]

/-- Removing two leaves `x, y` from the leaf set removes exactly the four twin edges. -/
theorem theta_insert_twins {a b x y : U} {L : Finset U} (hab : a ≠ b) (haL : a ∉ L)
    (hbL : b ∉ L) (hxL : x ∈ L) (hyL : y ∈ L) (hxy : x ≠ y) (e : Sym2 U) :
    e ∈ (theta a b L).edgeSet ↔ e ∈ (theta a b ((L.erase x).erase y)).edgeSet ∨
      e = s(a, x) ∨ e = s(x, b) ∨ e = s(a, y) ∨ e = s(y, b) := by
  have haL' : a ∉ (L.erase x).erase y := fun h => haL (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  have hbL' : b ∉ (L.erase x).erase y := fun h => hbL (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  rw [mem_theta_edgeSet hab haL hbL, mem_theta_edgeSet hab haL' hbL']
  have ex1 : s(a, x) = s(x, a) := Sym2.eq_swap
  have ex2 : s(a, y) = s(y, a) := Sym2.eq_swap
  rw [ex1, ex2]
  constructor
  · rintro (h | ⟨ℓ, hℓ, h⟩)
    · exact Or.inl (Or.inl h)
    · by_cases hlx : ℓ = x
      · subst hlx; rcases h with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
      · by_cases hly : ℓ = y
        · subst hly; rcases h with h | h
          · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
        · exact Or.inl (Or.inr ⟨ℓ, Finset.mem_erase.mpr ⟨hly, Finset.mem_erase.mpr ⟨hlx, hℓ⟩⟩, h⟩)
  · rintro ((h | ⟨ℓ, hℓ, h⟩) | h | h | h | h)
    · exact Or.inl h
    · exact Or.inr ⟨ℓ, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hℓ), h⟩
    · exact Or.inr ⟨x, hxL, Or.inl h⟩
    · exact Or.inr ⟨x, hxL, Or.inr h⟩
    · exact Or.inr ⟨y, hyL, Or.inl h⟩
    · exact Or.inr ⟨y, hyL, Or.inr h⟩

/-- **The theta graph with `2n` leaves has a decomposition into `n + 1` paths.** -/
theorem theta_decomp {a b : U} (hab : a ≠ b) :
    ∀ (n : ℕ) (L : Finset U), L.card = 2 * n → a ∉ L → b ∉ L →
      ∃ D : PathDecomp (theta a b L), D.size = n + 1 := by
  intro n
  induction n with
  | zero =>
    intro L hL _ _
    have : L = ∅ := Finset.card_eq_zero.mp (by simpa using hL)
    subst this
    exact theta_empty_decomp hab
  | succ n ih =>
    intro L hL haL hbL
    obtain ⟨x, hxL⟩ : L.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨y, hyL'⟩ : (L.erase x).Nonempty := Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem hxL]; omega)
    have hyx : y ≠ x := (Finset.mem_erase.mp hyL').1
    have hyL : y ∈ L := (Finset.mem_erase.mp hyL').2
    set L' := (L.erase x).erase y with hL'def
    have hcard : L'.card = 2 * n := by
      rw [hL'def, Finset.card_erase_of_mem hyL', Finset.card_erase_of_mem hxL]; omega
    have haL' : a ∉ L' := fun h => haL (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
    have hbL' : b ∉ L' := fun h => hbL (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
    obtain ⟨D', hD'⟩ := ih L' hcard haL' hbL'
    have hxa : x ≠ a := fun h => haL (h ▸ hxL)
    have hxb : x ≠ b := fun h => hbL (h ▸ hxL)
    have hya : y ≠ a := fun h => haL (h ▸ hyL)
    have hyb : y ≠ b := fun h => hbL (h ▸ hyL)
    have hxL' : x ∉ L' := fun h => by
      rw [hL'def] at h
      exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase h)).1 rfl
    have hyL'' : y ∉ L' := fun h => by
      rw [hL'def] at h
      exact (Finset.mem_erase.mp h).1 rfl
    have adj : ∀ ℓ ∈ L, (theta a b L).Adj a ℓ ∧ (theta a b L).Adj ℓ b := by
      intro ℓ hℓ
      have hla : ℓ ≠ a := fun h => haL (h ▸ hℓ)
      have hlb : ℓ ≠ b := fun h => hbL (h ▸ hℓ)
      refine ⟨?_, ?_⟩
      · rw [theta_adj]; exact ⟨Or.inr ⟨ℓ, hℓ, Or.inl Sym2.eq_swap⟩, fun h => hla h.symm⟩
      · rw [theta_adj]; exact ⟨Or.inr ⟨ℓ, hℓ, Or.inr rfl⟩, hlb⟩
    obtain ⟨D, hD, -⟩ := D'.twin_insert (K := theta a b L') (G := theta a b L) hab hyx.symm
      hxa hxb hya hyb (adj x hxL).1 (adj x hxL).2 (adj y hyL).1 (adj y hyL).2
      (theta_insert_twins hab haL hbL hxL hyL hyx.symm)
      (theta_isolated hxa hxb hxL') (theta_isolated hya hyb hyL'')
      ⟨b, by rw [theta_adj]; exact ⟨Or.inl rfl, hab⟩⟩
    exact ⟨D, by rw [hD, hD']⟩

/-- **The theta graph rooted at a leaf.** If `r ∈ L` and `|L| = 2n + 2`, the theta graph has a
decomposition into `n + 2` paths with at least two ends at `r`: remove `r` and one more leaf, and
insert them back as a twin pair with `r` taking the two new ends. -/
theorem theta_rooted {a b r : U} (hab : a ≠ b) (n : ℕ) (L : Finset U) (hL : L.card = 2 * n + 2)
    (haL : a ∉ L) (hbL : b ∉ L) (hrL : r ∈ L) :
    ∃ D : PathDecomp (theta a b L), D.size = n + 2 ∧ 2 ≤ D.ends r := by
  obtain ⟨y, hyL'⟩ : (L.erase r).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hrL]; omega)
  have hyr : y ≠ r := (Finset.mem_erase.mp hyL').1
  have hyL : y ∈ L := (Finset.mem_erase.mp hyL').2
  set L' := (L.erase r).erase y with hL'def
  have hcard : L'.card = 2 * n := by
    rw [hL'def, Finset.card_erase_of_mem hyL', Finset.card_erase_of_mem hrL]; omega
  have haL' : a ∉ L' := fun h => haL (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  have hbL' : b ∉ L' := fun h => hbL (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  obtain ⟨D', hD'⟩ := theta_decomp hab n L' hcard haL' hbL'
  have hra : r ≠ a := fun h => haL (h ▸ hrL)
  have hrb : r ≠ b := fun h => hbL (h ▸ hrL)
  have hya : y ≠ a := fun h => haL (h ▸ hyL)
  have hyb : y ≠ b := fun h => hbL (h ▸ hyL)
  have hrL' : r ∉ L' := fun h => by
    rw [hL'def] at h
    exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase h)).1 rfl
  have hyL'' : y ∉ L' := fun h => by
    rw [hL'def] at h
    exact (Finset.mem_erase.mp h).1 rfl
  have adj : ∀ ℓ ∈ L, (theta a b L).Adj a ℓ ∧ (theta a b L).Adj ℓ b := by
    intro ℓ hℓ
    have hla : ℓ ≠ a := fun h => haL (h ▸ hℓ)
    have hlb : ℓ ≠ b := fun h => hbL (h ▸ hℓ)
    refine ⟨?_, ?_⟩
    · rw [theta_adj]; exact ⟨Or.inr ⟨ℓ, hℓ, Or.inl Sym2.eq_swap⟩, fun h => hla h.symm⟩
    · rw [theta_adj]; exact ⟨Or.inr ⟨ℓ, hℓ, Or.inr rfl⟩, hlb⟩
  obtain ⟨D, hD, hDe⟩ := D'.twin_insert (K := theta a b L') (G := theta a b L) hab hyr.symm
    hra hrb hya hyb (adj r hrL).1 (adj r hrL).2 (adj y hyL).1 (adj y hyL).2
    (theta_insert_twins hab haL hbL hrL hyL hyr.symm)
    (theta_isolated hra hrb hrL') (theta_isolated hya hyb hyL'')
    ⟨b, by rw [theta_adj]; exact ⟨Or.inl rfl, hab⟩⟩
  refine ⟨D, by rw [hD, hD'], ?_⟩
  rw [hDe r]
  simp

end theta

/-! ### The fat theta `K_{3,t} + h₂h₃` -/

section fat

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The **fat theta** with hubs `z, a, b` and leaf set `L`: the edge `ab` and the edges
`ℓz, ℓa, ℓb` for `ℓ ∈ L` (that is, `K_{3,|L|} + ab`). -/
def fatTheta (z a b : V) (L : Finset V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | e = s(a, b) ∨ ∃ ℓ ∈ L, e = s(ℓ, a) ∨ e = s(ℓ, b) ∨ e = s(ℓ, z)}

omit [Fintype V] [DecidableEq V] in
theorem fatTheta_adj {z a b : V} {L : Finset V} {v w : V} :
    (fatTheta z a b L).Adj v w ↔ (s(v, w) = s(a, b) ∨
      ∃ ℓ ∈ L, s(v, w) = s(ℓ, a) ∨ s(v, w) = s(ℓ, b) ∨ s(v, w) = s(ℓ, z)) ∧ v ≠ w := by
  simp [fatTheta, SimpleGraph.fromEdgeSet_adj]

omit [Fintype V] in
/-- `J − z` is the theta graph on the other vertices. -/
theorem delVert_fatTheta {z a b : V} {L : Finset V} (haz : a ≠ z) (hbz : b ≠ z) (hzL : z ∉ L) :
    delVert (fatTheta z a b L) z =
      theta (⟨a, haz⟩ : {v | v ≠ z}) ⟨b, hbz⟩ (L.subtype (fun v => v ∈ {v | v ≠ z})) := by
  ext u v
  simp only [delVert, SimpleGraph.induce_adj, fatTheta_adj, theta_adj, ne_eq]
  have hne : (¬ u.1 = v.1) ↔ (¬ u = v) := by rw [Subtype.ext_iff]
  rw [hne]
  refine and_congr_left fun _ => ?_
  have key : ∀ p q : {v | v ≠ z}, s(u.1, v.1) = s(p.1, q.1) ↔ s(u, v) = s(p, q) := by
    intro p q
    simp only [Sym2.eq_iff, Subtype.ext_iff]
  constructor
  · rintro (h | ⟨ℓ, hℓ, h | h | h⟩)
    · exact Or.inl ((key ⟨a, haz⟩ ⟨b, hbz⟩).mp h)
    · have hℓz : ℓ ≠ z := fun h' => hzL (h' ▸ hℓ)
      exact Or.inr ⟨⟨ℓ, hℓz⟩, by simpa using hℓ, Or.inl ((key ⟨ℓ, hℓz⟩ ⟨a, haz⟩).mp h)⟩
    · have hℓz : ℓ ≠ z := fun h' => hzL (h' ▸ hℓ)
      exact Or.inr ⟨⟨ℓ, hℓz⟩, by simpa using hℓ, Or.inr ((key ⟨ℓ, hℓz⟩ ⟨b, hbz⟩).mp h)⟩
    · exfalso
      rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact v.2 h2
      · exact u.2 h1
  · rintro (h | ⟨ℓ, hℓ, h | h⟩)
    · exact Or.inl ((key ⟨a, haz⟩ ⟨b, hbz⟩).mpr h)
    · exact Or.inr ⟨ℓ.1, by simpa using hℓ, Or.inl ((key ℓ ⟨a, haz⟩).mpr h)⟩
    · exact Or.inr ⟨ℓ.1, by simpa using hℓ, Or.inr (Or.inl ((key ℓ ⟨b, hbz⟩).mpr h))⟩

/-- **Test1 on the fat theta.** Let every vertex be one of the hubs `z, a, b` or a leaf in `L`,
with `|L|` even and at least `2`. Then Test1 holds at `z`: for every leaf `r`, `J − z` has a
decomposition into `(|J| − 1)/2` paths with two ends at `r`. (For `|L| ≥ 4`, `J` is 3-connected
and `z` is its only even vertex; these hypotheses of Test1 are not needed.) -/
theorem test1_fatTheta {z a b : V} {L : Finset V} [DecidableRel (fatTheta z a b L).Adj]
    (hab : a ≠ b) (haz : a ≠ z) (hbz : b ≠ z) (hzL : z ∉ L) (haL : a ∉ L) (hbL : b ∉ L)
    (hV : ∀ v, v = z ∨ v = a ∨ v = b ∨ v ∈ L) (hev : Even L.card) (h2 : 2 ≤ L.card) :
    Test1 (fatTheta z a b L) z := by
  intro _ r hr
  -- the root is a leaf
  have hrL : r ∈ L := by
    rw [fatTheta_adj] at hr
    obtain ⟨h | ⟨ℓ, hℓ, h | h | h⟩, hzr⟩ := hr
    · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1.symm haz
      · exact absurd h1.symm hbz
    · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd (h1 ▸ hℓ) hzL
      · exact absurd h1.symm haz
    · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd (h1 ▸ hℓ) hzL
      · exact absurd h1.symm hbz
    · rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨-, h2⟩
      · exact absurd (h1 ▸ hℓ) hzL
      · exact h2 ▸ hℓ
  obtain ⟨n, hn⟩ : ∃ n, L.card = 2 * n + 2 := by
    obtain ⟨k, hk⟩ := hev; exact ⟨k - 1, by omega⟩
  -- the order of `J`
  have hcard : Fintype.card V = L.card + 3 := by
    have huniv : (Finset.univ : Finset V) = insert z (insert a (insert b L)) := by
      ext v; simp only [Finset.mem_univ, Finset.mem_insert, true_iff]; exact hV v
    rw [← Finset.card_univ, huniv, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem hbL]
    · simp only [Finset.mem_insert, not_or]; exact ⟨hab, haL⟩
    · simp only [Finset.mem_insert, not_or]; exact ⟨haz.symm, hbz.symm, hzL⟩
  set L' := L.subtype (fun v => v ∈ {v | v ≠ z}) with hL'
  have hcard' : L'.card = 2 * n + 2 := by
    rw [hL', Finset.card_subtype, ← hn]
    congr 1
    ext v; simp only [Finset.mem_filter, Set.mem_ofPred_eq, ne_eq, and_iff_left_iff_imp]
    exact fun hv h => hzL (h ▸ hv)
  have hab' : (⟨a, haz⟩ : {v | v ≠ z}) ≠ ⟨b, hbz⟩ := fun h => hab (congrArg Subtype.val h)
  have haL' : (⟨a, haz⟩ : {v | v ≠ z}) ∉ L' := by simpa [hL'] using haL
  have hbL' : (⟨b, hbz⟩ : {v | v ≠ z}) ∉ L' := by simpa [hL'] using hbL
  have hrL' : (⟨r, hr.ne'⟩ : {v | v ≠ z}) ∈ L' := by simpa [hL'] using hrL
  obtain ⟨D, hD, hDr⟩ := theta_rooted hab' n L' hcard' haL' hbL' hrL'
  rw [delVert_fatTheta haz hbz hzL]
  exact ⟨D, by rw [hD, hcard]; omega, hDr⟩

end fat

/-! ### Twin reductions for Test1 and Test2 -/

section reductions

variable {W : Type u} [DecidableEq W]

/-- `B` with every edge at `x` or `y` removed. -/
def twinDel (B : SimpleGraph W) (x y : W) : SimpleGraph W :=
  SimpleGraph.fromEdgeSet {e | e ∈ B.edgeSet ∧ x ∉ e ∧ y ∉ e}

omit [DecidableEq W] in
theorem twinDel_adj {B : SimpleGraph W} {x y v w : W} :
    (twinDel B x y).Adj v w ↔ B.Adj v w ∧ v ≠ x ∧ w ≠ x ∧ v ≠ y ∧ w ≠ y := by
  simp only [twinDel, SimpleGraph.fromEdgeSet_adj, Set.mem_ofPred_eq, SimpleGraph.mem_edgeSet,
    Sym2.mem_iff, not_or]
  constructor
  · rintro ⟨⟨h, ⟨h1, h2⟩, ⟨h3, h4⟩⟩, -⟩
    exact ⟨h, fun h' => h1 h'.symm, fun h' => h2 h'.symm, fun h' => h3 h'.symm,
      fun h' => h4 h'.symm⟩
  · rintro ⟨h, h1, h2, h3, h4⟩
    exact ⟨⟨h, ⟨fun h' => h1 h'.symm, fun h' => h2 h'.symm⟩,
      ⟨fun h' => h3 h'.symm, fun h' => h4 h'.symm⟩⟩, h.ne⟩

/-- The twin insertion in the form used below: `x, y` have exactly the neighbours `a, b` in `B`. -/
theorem twin_insert_twinDel {B K : SimpleGraph W} {a b x y : W}
    (hab : a ≠ b) (hxy : x ≠ y) (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (hx : ∀ w, B.Adj x w ↔ w = a ∨ w = b) (hy : ∀ w, B.Adj y w ↔ w = a ∨ w = b)
    (ha : ∃ w, w ≠ x ∧ w ≠ y ∧ B.Adj a w)
    (hK : ∀ v w, K.Adj v w ↔ B.Adj v w ∧ v ≠ x ∧ w ≠ x ∧ v ≠ y ∧ w ≠ y) (D' : PathDecomp K) :
    ∃ D : PathDecomp B, D.size = D'.size + 1 ∧
      ∀ w, D.ends w = D'.ends w + (if w = x then 2 else 0) := by
  have h1 : B.Adj a x := ((hx a).2 (Or.inl rfl)).symm
  have h2 : B.Adj x b := (hx b).2 (Or.inr rfl)
  have h3 : B.Adj a y := ((hy a).2 (Or.inl rfl)).symm
  have h4 : B.Adj y b := (hy b).2 (Or.inr rfl)
  refine D'.twin_insert hab hxy hxa hxb hya hyb h1 h2 h3 h4 (fun e => ?_) ?_ ?_ ?_
  · induction e using Sym2.inductionOn with
    | hf v w =>
      simp only [SimpleGraph.mem_edgeSet, hK]
      constructor
      · intro h
        by_cases hvx : v = x
        · subst hvx
          rcases (hx w).1 h with rfl | rfl
          · exact Or.inr (Or.inl Sym2.eq_swap)
          · exact Or.inr (Or.inr (Or.inl rfl))
        by_cases hwx : w = x
        · subst hwx
          rcases (hx v).1 h.symm with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl Sym2.eq_swap))
        by_cases hvy : v = y
        · subst hvy
          rcases (hy w).1 h with rfl | rfl
          · exact Or.inr (Or.inr (Or.inr (Or.inl Sym2.eq_swap)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
        by_cases hwy : w = y
        · subst hwy
          rcases (hy v).1 h.symm with rfl | rfl
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr Sym2.eq_swap)))
        exact Or.inl ⟨h, hvx, hwx, hvy, hwy⟩
      · rintro (⟨h, -⟩ | h | h | h | h)
        · exact h
        · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h1
          · exact h1.symm
        · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h2
          · exact h2.symm
        · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h3
          · exact h3.symm
        · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h4
          · exact h4.symm
  · intro w h; exact ((hK _ _).mp h).2.1 rfl
  · intro w h; exact ((hK _ _).mp h).2.2.2.1 rfl
  · obtain ⟨w, hwx, hwy, haw⟩ := ha
    exact ⟨w, (hK _ _).mpr ⟨haw, hxa.symm, hwx, hya.symm, hwy⟩⟩

end reductions

section reductionsJ

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Twin reduction for Test1.** Let `x, y ∈ N(z)` have the same neighbourhood `{z, a, b}` in `J`,
and let `a` have a neighbour outside `{z, x, y}`. If `J − z` with the four edges at `x, y` removed
has a decomposition into at most `(|J| − 1)/2 − 1` paths, with two ends at `r` unless `r` is one
of the twins, then Test1 holds at `(J, z, r)`. -/
theorem test1At_of_twins (J : SimpleGraph V) [DecidableRel J.Adj] {z r x y a b : V}
    (hrz : r ≠ z) (hxz : x ≠ z) (hyz : y ≠ z) (haz : a ≠ z) (hbz : b ≠ z)
    (hab : a ≠ b) (hxy : x ≠ y) (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (hx : ∀ w, J.Adj x w ↔ w = z ∨ w = a ∨ w = b) (hy : ∀ w, J.Adj y w ↔ w = z ∨ w = a ∨ w = b)
    (ha : ∃ w, w ≠ z ∧ w ≠ x ∧ w ≠ y ∧ J.Adj a w)
    (D' : PathDecomp (twinDel (delVert J z) ⟨x, hxz⟩ ⟨y, hyz⟩))
    (hs : D'.size + 1 ≤ (Fintype.card V - 1) / 2)
    (he : r = x ∨ r = y ∨ 2 ≤ D'.ends ⟨r, hrz⟩) : Test1At J z r := by
  intro hr
  let x' : {v | v ≠ z} := ⟨x, hxz⟩
  let y' : {v | v ≠ z} := ⟨y, hyz⟩
  let a' : {v | v ≠ z} := ⟨a, haz⟩
  let b' : {v | v ≠ z} := ⟨b, hbz⟩
  have nb : ∀ (t : V) (ht : t ≠ z), (∀ w, J.Adj t w ↔ w = z ∨ w = a ∨ w = b) →
      ∀ w : {v | v ≠ z}, (delVert J z).Adj ⟨t, ht⟩ w ↔ w = a' ∨ w = b' := by
    intro t ht h w
    simp only [delVert, SimpleGraph.induce_adj, h w.1, a', b', Subtype.ext_iff]
    have := w.2
    constructor
    · rintro (h' | h' | h')
      · exact absurd h' this
      · exact Or.inl h'
      · exact Or.inr h'
    · rintro (h' | h')
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
  have ne : ∀ {p q : V} (hp : p ≠ z) (hq : q ≠ z), p ≠ q →
      (⟨p, hp⟩ : {v | v ≠ z}) ≠ ⟨q, hq⟩ := fun _ _ h h' => h (congrArg Subtype.val h')
  have ha' : ∃ w, w ≠ x' ∧ w ≠ y' ∧ (delVert J z).Adj a' w := by
    obtain ⟨w, hwz, hwx, hwy, haw⟩ := ha
    exact ⟨⟨w, hwz⟩, ne hwz hxz hwx, ne hwz hyz hwy, haw⟩
  have hK : ∀ v w, (twinDel (delVert J z) x' y').Adj v w ↔ (delVert J z).Adj v w ∧ v ≠ x' ∧ w ≠ x' ∧ v ≠ y' ∧ w ≠ y' :=
    fun _ _ => twinDel_adj
  have hK' : ∀ v w, (twinDel (delVert J z) x' y').Adj v w ↔ (delVert J z).Adj v w ∧ v ≠ y' ∧ w ≠ y' ∧ v ≠ x' ∧ w ≠ x' :=
    fun v w => by rw [hK]; tauto
  rcases he with hrx | hry | he
  · obtain ⟨D, hD, hDe⟩ := twin_insert_twinDel (B := delVert J z) (ne haz hbz hab) (ne hxz hyz hxy)
      (ne hxz haz hxa) (ne hxz hbz hxb) (ne hyz haz hya) (ne hyz hbz hyb)
      (nb x hxz hx) (nb y hyz hy) ha' hK D'
    have hr' : (⟨r, hr.ne'⟩ : {v | v ≠ z}) = x' := Subtype.ext hrx
    refine ⟨D, by rw [hD]; exact hs, ?_⟩
    rw [hDe, hr']; simp [x']
  · obtain ⟨D, hD, hDe⟩ := twin_insert_twinDel (B := delVert J z) (ne haz hbz hab) (ne hyz hxz hxy.symm)
      (ne hyz haz hya) (ne hyz hbz hyb) (ne hxz haz hxa) (ne hxz hbz hxb)
      (nb y hyz hy) (nb x hxz hx)
      (by obtain ⟨w, h1, h2, h3⟩ := ha'; exact ⟨w, h2, h1, h3⟩) hK' D'
    have hr' : (⟨r, hr.ne'⟩ : {v | v ≠ z}) = y' := Subtype.ext hry
    refine ⟨D, by rw [hD]; exact hs, ?_⟩
    rw [hDe, hr']; simp [y']
  · obtain ⟨D, hD, hDe⟩ := twin_insert_twinDel (B := delVert J z) (ne haz hbz hab) (ne hxz hyz hxy)
      (ne hxz haz hxa) (ne hxz hbz hxb) (ne hyz haz hya) (ne hyz hbz hyb)
      (nb x hxz hx) (nb y hyz hy) ha' hK D'
    refine ⟨D, by rw [hD]; exact hs, ?_⟩
    rw [hDe]; exact le_trans he (Nat.le_add_right _ _)

/-- **Twin reduction for Test2.** As `test1At_of_twins`, with the Test2 budget `|J|/2` and three
ends at `r`. -/
theorem test2At_of_twins (J : SimpleGraph V) [DecidableRel J.Adj] {z r x y a b : V}
    (hrz : r ≠ z) (hxz : x ≠ z) (hyz : y ≠ z) (haz : a ≠ z) (hbz : b ≠ z)
    (hab : a ≠ b) (hxy : x ≠ y) (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (hx : ∀ w, J.Adj x w ↔ w = z ∨ w = a ∨ w = b) (hy : ∀ w, J.Adj y w ↔ w = z ∨ w = a ∨ w = b)
    (ha : ∃ w, w ≠ z ∧ w ≠ x ∧ w ≠ y ∧ J.Adj a w)
    (D' : PathDecomp (twinDel (delVert J z) ⟨x, hxz⟩ ⟨y, hyz⟩))
    (hs : D'.size + 1 ≤ Fintype.card V / 2) (he : 3 ≤ D'.ends ⟨r, hrz⟩) : Test2At J z r := by
  intro hr
  let a' : {v | v ≠ z} := ⟨a, haz⟩
  let b' : {v | v ≠ z} := ⟨b, hbz⟩
  have nb : ∀ (t : V) (ht : t ≠ z), (∀ w, J.Adj t w ↔ w = z ∨ w = a ∨ w = b) →
      ∀ w : {v | v ≠ z}, (delVert J z).Adj ⟨t, ht⟩ w ↔ w = a' ∨ w = b' := by
    intro t ht h w
    simp only [delVert, SimpleGraph.induce_adj, h w.1, a', b', Subtype.ext_iff]
    have := w.2
    constructor
    · rintro (h' | h' | h')
      · exact absurd h' this
      · exact Or.inl h'
      · exact Or.inr h'
    · rintro (h' | h')
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
  have ne : ∀ {p q : V} (hp : p ≠ z) (hq : q ≠ z), p ≠ q →
      (⟨p, hp⟩ : {v | v ≠ z}) ≠ ⟨q, hq⟩ := fun _ _ h h' => h (congrArg Subtype.val h')
  have ha' : ∃ w, w ≠ (⟨x, hxz⟩ : {v | v ≠ z}) ∧ w ≠ ⟨y, hyz⟩ ∧ (delVert J z).Adj a' w := by
    obtain ⟨w, hwz, hwx, hwy, haw⟩ := ha
    exact ⟨⟨w, hwz⟩, ne hwz hxz hwx, ne hwz hyz hwy, haw⟩
  obtain ⟨D, hD, hDe⟩ := twin_insert_twinDel (B := delVert J z) (ne haz hbz hab) (ne hxz hyz hxy)
    (ne hxz haz hxa) (ne hxz hbz hxb) (ne hyz haz hya) (ne hyz hbz hyb)
    (nb x hxz hx) (nb y hyz hy) ha' (fun _ _ => twinDel_adj) D'
  refine ⟨D, by rw [hD]; exact hs, ?_⟩
  rw [hDe]; exact le_trans he (Nat.le_add_right _ _)

end reductionsJ

end Gallai
