import GallaiLean.Test1AllOdd
import GallaiLean.ConstrainedLovasz

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

/-! ### The cherry form of `L_N` and Test1 at roots with cherry data -/

section cherry

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- **A forest base in an arbitrary graph**: a Lovász decomposition of `H` in which, for every
(child, parent) pair `p` of `L`, (i) the path ending at the child avoids the parent, and
(ii) no path has two siblings as its ends. -/
def ForestLN (H : SimpleGraph W) [DecidableRel H.Adj] (L : List (W × W)) : Prop :=
  ∃ D₀ : PathDecomp H, (∀ v, D₀.ends v = H.degree v % 2) ∧
    (∀ p ∈ L, ∀ P ∈ D₀.paths, (P.src = p.1 ∨ P.tgt = p.1) → p.2 ∉ P.walk.support) ∧
    (∀ p ∈ L, ∀ q ∈ L, p.1 ≠ q.1 → p.2 = q.2 → ∀ P ∈ D₀.paths,
      ¬ ((P.src = p.1 ∨ P.tgt = p.1) ∧ (P.src = q.1 ∨ P.tgt = q.1)))

/-- **Cherry constraints**: (child, parent) pairs on non-edges of `H` forming a rooted linear
forest whose components have at most two edges and are rooted at an end: children distinct,
parents distinct (no siblings), no chain of three pairs. The components are single pairs
`c ← a` (`a ∉ Q(c)`) and 2-chains `a ← x ← b` (`a ∉ Q(x)`, `x ∉ Q(b)`). -/
structure CherryList (H : SimpleGraph W) (L : List (W × W)) : Prop where
  children : (L.map Prod.fst).Nodup
  parents : (L.map Prod.snd).Nodup
  nonadj : ∀ p ∈ L, ¬ H.Adj p.1 p.2
  irrefl : ∀ p ∈ L, p.1 ≠ p.2
  depth : ∀ p ∈ L, ∀ q ∈ L, p.2 = q.1 → ∀ s ∈ L, q.2 ≠ s.1

end cherry

/-- **Conjecture CL (cherry `L_N`)** (manuscript `conj:CL`): in a graph with no vertex of positive
even degree (the convention of `LN`), every system of cherry constraints is satisfied by some
Lovász decomposition. With only single pairs this is `LN` (`lN_of_cherryLN`). -/
def CherryLN : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (L : List (W × W)), (evenSet H).card = 0 → CherryList H L → ForestLN H L

section cherryT1

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Conjecture CL gives Test1 at every root with cherry data**: all-odd forest data
(`OddData`) whose forest is a linear forest of components with at most two edges, rooted at
ends (`r` is then a root). -/
theorem test1At_of_cherryLN (hC : CherryLN.{u}) (J : SimpleGraph V) [DecidableRel J.Adj] {z r : V}
    (hz : ∀ v, Even (J.degree v) ↔ v = z) (hrz : r ≠ z) {T : List {v | v ≠ z}}
    (hT : ∀ v : {v | v ≠ z}, J.Adj z v ↔ v ∈ T) {L : List ({v | v ≠ z} × {v | v ≠ z})}
    (hF : OddData (delVert J z) ⟨r, hrz⟩ T L) (hpar : (L.map Prod.snd).Nodup)
    (hdepth : ∀ p ∈ L, ∀ q ∈ L, p.2 = q.1 → ∀ s ∈ L, q.2 ≠ s.1) : Test1At J z r := by
  classical
  set B := delVert J z with hB
  have hev : ∀ v, Even (B.degree v) ↔ v ∈ T := fun v =>
    (even_delVert_iff_adj J hz v).trans (hT v)
  have hnd : (L.map pairEdge).Nodup := hF.edges
  have hin : ∀ e ∈ L.map pairEdge, e ∈ B.edgeSet := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    exact hF.edge p hp
  have hdeg := delList_degree_count B (L.map pairEdge) hnd hin
  have hodd : ∀ v, (delList B (L.map pairEdge)).degree v % 2 = 1 := by
    intro v
    have h1 := hdeg v
    have ht := hF.tjoin v
    by_cases hTv : v ∈ T
    · have he : Even (B.degree v) := (hev v).2 hTv
      rw [Nat.even_iff] at he
      simp only [hTv, ite_true] at ht
      omega
    · have ho : ¬ Even (B.degree v) := fun he => hTv ((hev v).1 he)
      rw [Nat.not_even_iff] at ho
      simp only [hTv, ite_false] at ht
      omega
  have hCL : CherryList (delList B (L.map pairEdge)) L :=
    { children := hF.children
      parents := hpar
      nonadj := fun p hp h => h.2 (List.mem_map_of_mem hp)
      irrefl := fun p hp => (hF.edge p hp).ne
      depth := hdepth }
  have hev0 : (evenSet (delList B (L.map pairEdge))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro v hv
    simp only [evenSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have := hodd v
    rw [Nat.even_iff] at hv
    omega
  obtain ⟨D₀, hD₀, hi, hii⟩ := hC _ (delList B (L.map pairEdge)) L hev0 hCL
  exact test1At_of_oddBase J hz hrz hT ⟨L, hF, D₀, hD₀, hi, hii⟩

end cherryT1

/-! ### Root moves (MR Thm 145's one-edge steps) -/

section rootmove

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- **The Fan step of a root move.** Let `uv` be an edge of `G` with `u` of even degree, and let
`u` have at most one neighbour `t ≠ v` of even degree. A decomposition of `G − uv` with at least
two ends at `v` gives one of `G` with the same number of paths and at least two ends at `u`
(Fan's single-edge lemma, `fan_single`: only even vertices can have no end). -/
theorem fan_root_move {G : SimpleGraph W} [DecidableRel G.Adj] {u v : W} (huv : G.Adj u v)
    (D' : PathDecomp (delList G [s(u, v)])) (hv : 2 ≤ D'.ends v) (hu : Even (G.degree u))
    (hnb : ∀ t₁ t₂, G.Adj u t₁ → t₁ ≠ v → Even (G.degree t₁) →
      G.Adj u t₂ → t₂ ≠ v → Even (G.degree t₂) → t₁ = t₂) :
    ∃ D : PathDecomp G, D.size = D'.size ∧ 2 ≤ D.ends u := by
  classical
  have hnd : [s(u, v)].Nodup := List.nodup_singleton _
  have hin : ∀ e ∈ [s(u, v)], e ∈ G.edgeSet := by
    intro e he; rw [List.mem_singleton] at he; subst he; exact huv
  have hdeg := delList_degree_count G [s(u, v)] hnd hin
  have hdeg' : ∀ t, t ≠ u → t ≠ v → (delList G [s(u, v)]).degree t = G.degree t := by
    intro t htu htv
    have := hdeg t
    simp only [List.countP_singleton, Sym2.mem_iff, htu, htv, or_self, decide_false,
      Bool.false_eq_true, ite_false, add_zero] at this
    exact this
  have hdegu : (delList G [s(u, v)]).degree u + 1 = G.degree u := by
    have := hdeg u
    simpa using this
  have hzero : (Finset.univ.filter (fun w => (delList G [s(u, v)]).Adj u w ∧ D'.ends w = 0)).card < D'.ends v := by
    have hle : (Finset.univ.filter (fun w => (delList G [s(u, v)]).Adj u w ∧ D'.ends w = 0)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have key : ∀ t, (delList G [s(u, v)]).Adj u t → D'.ends t = 0 → G.Adj u t ∧ t ≠ v ∧ Even (G.degree t) := by
        intro t hadj hends
        have htv : t ≠ v := by
          rintro rfl
          exact hadj.2 (List.mem_singleton.mpr rfl)
        have htu : t ≠ u := (hadj.1.ne).symm
        refine ⟨hadj.1, htv, ?_⟩
        have hm := PathDecomp.ends_mod_two D' t
        rw [hends, hdeg' t htu htv] at hm
        exact Nat.even_iff.mpr hm.symm
      obtain ⟨a1, a2, a3⟩ := key a ha.1 ha.2
      obtain ⟨b1, b2, b3⟩ := key b hb.1 hb.2
      exact hnb a b a1 a2 a3 b1 b2 b3
    omega
  have hG' : ∀ e, e ∈ (delList G [s(u, v)]).edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(u, v) := by
    intro e
    rw [delList_edgeSet, List.mem_singleton]
  obtain ⟨D, hD, hDu, -, -⟩ := fan_single huv hG' D' hzero
  refine ⟨D, hD, ?_⟩
  have hm := PathDecomp.ends_mod_two D' u
  have hodd : (delList G [s(u, v)]).degree u % 2 = 1 := by
    rw [Nat.even_iff] at hu; omega
  omega

end rootmove

section rootmoveJ

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Root move M1** (MR Thm 145, the one-edge step). Let `z` be the only even vertex of `J`,
`r ∈ N(z)` with at most one neighbour in `N(z)`, and `w ∉ N(z)` a neighbour of `r`. If
`(J − z) − rw` has a decomposition into at most `(|J| − 1)/2` paths with two ends at `w`, then
Test1 holds at `(J, z, r)`. (That hypothesis is Test1 at `(J − rw − zr + zw, z, w)`, whose
deletion graph is `(J − z) − rw`; normally `w ∉ N(z)`, but this is not needed.) -/
theorem test1At_of_move1 (J : SimpleGraph V) [DecidableRel J.Adj] {z r w : V}
    (hz : ∀ v, Even (J.degree v) ↔ v = z) (hrz : r ≠ z) (hwz : w ≠ z) (hrw : J.Adj r w)
    (hone : ∀ t₁ t₂, t₁ ≠ z → t₂ ≠ z → J.Adj r t₁ → J.Adj z t₁ → J.Adj r t₂ → J.Adj z t₂ →
      t₁ = t₂)
    (h' : ∃ D' : PathDecomp (delList (delVert J z) [s((⟨r, hrz⟩ : {v | v ≠ z}), ⟨w, hwz⟩)]),
      D'.size ≤ (Fintype.card V - 1) / 2 ∧ 2 ≤ D'.ends ⟨w, hwz⟩) : Test1At J z r := by
  intro hr
  obtain ⟨D', hs, hw⟩ := h'
  have hev := even_delVert_iff_adj J hz
  obtain ⟨D, hD, hDr⟩ := fan_root_move (G := delVert J z) (u := ⟨r, hrz⟩) (v := ⟨w, hwz⟩)
    hrw D' hw ((hev _).2 hr) (by
      intro t₁ t₂ h1 _ e1 h2 _ e2
      exact Subtype.ext (hone t₁.1 t₂.1 t₁.2 t₂.2 h1 ((hev _).1 e1) h2 ((hev _).1 e2)))
  exact ⟨D, by rw [hD]; exact hs, hDr⟩

/-- **Root move M2** (MR Thm 145, "a second even neighbour"). Let `z` be the only even vertex of
`J` and let `r ∈ N(z)` have exactly the two neighbours `u ≠ v` in `N(z)`. If `(J − z) − ru` has a
decomposition into at most `(|J| − 1)/2` paths with two ends at `v`, then Test1 holds at
`(J, z, r)`. (That hypothesis is Test1 at `(J − ru − zr − zu, z, v)`, whose deletion graph is
`(J − z) − ru`.) -/
theorem test1At_of_move2 (J : SimpleGraph V) [DecidableRel J.Adj] {z r u v : V}
    (hz : ∀ v, Even (J.degree v) ↔ v = z) (hrz : r ≠ z) (huz : u ≠ z) (hvz : v ≠ z)
    (hru : J.Adj r u) (hzu : J.Adj z u)
    (htwo : ∀ t, t ≠ z → J.Adj r t → J.Adj z t → t = u ∨ t = v)
    (h' : ∃ D' : PathDecomp (delList (delVert J z) [s((⟨r, hrz⟩ : {v | v ≠ z}), ⟨u, huz⟩)]),
      D'.size ≤ (Fintype.card V - 1) / 2 ∧ 2 ≤ D'.ends ⟨v, hvz⟩) : Test1At J z r := by
  classical
  intro hr
  have hev := even_delVert_iff_adj J hz
  set G := delVert J z
  set r' : {v | v ≠ z} := ⟨r, hrz⟩
  set u' : {v | v ≠ z} := ⟨u, huz⟩
  set v' : {v | v ≠ z} := ⟨v, hvz⟩
  obtain ⟨D', hs, hv⟩ := h'
  have hru' : G.Adj r' u' := hru
  have hnd : [s(r', u')].Nodup := List.nodup_singleton _
  have hin : ∀ e ∈ [s(r', u')], e ∈ G.edgeSet := by
    intro e he; rw [List.mem_singleton] at he; subst he; exact hru'
  have hdeg := delList_degree_count G [s(r', u')] hnd hin
  have hdeg' : ∀ t, t ≠ r' → t ≠ u' → (delList G [s(r', u')]).degree t = G.degree t := by
    intro t htr htu
    have := hdeg t
    simp only [List.countP_singleton, Sym2.mem_iff, htr, htu, or_self, decide_false,
      Bool.false_eq_true, ite_false, add_zero] at this
    exact this
  have hzero : (Finset.univ.filter (fun w => (delList G [s(r', u')]).Adj r' w ∧ D'.ends w = 0)).card < D'.ends u' := by
    have h0 : (Finset.univ.filter (fun w => (delList G [s(r', u')]).Adj r' w ∧ D'.ends w = 0)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro t - ⟨hadj, hends⟩
      have htu : t ≠ u' := by
        rintro rfl; exact hadj.2 (List.mem_singleton.mpr rfl)
      have htr : t ≠ r' := (hadj.1.ne).symm
      have hm := PathDecomp.ends_mod_two D' t
      rw [hends, hdeg' t htr htu] at hm
      have hzt : J.Adj z t.1 := (hev t).1 (Nat.even_iff.mpr hm.symm)
      rcases htwo t.1 t.2 hadj.1 hzt with h | h
      · exact htu (Subtype.ext h)
      · have htv : t = v' := Subtype.ext h
        rw [htv] at hends; omega
    rw [h0, Finset.card_empty]
    have hm := PathDecomp.ends_mod_two D' u'
    have hdu : (delList G [s(r', u')]).degree u' + 1 = G.degree u' := by
      have := hdeg u'; simpa using this
    have heu : Even (G.degree u') := (hev u').2 hzu
    rw [Nat.even_iff] at heu
    omega
  have hG' : ∀ e, e ∈ (delList G [s(r', u')]).edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(r', u') := by
    intro e
    rw [delList_edgeSet, List.mem_singleton]
  obtain ⟨D, hD, hDr, -, -⟩ := fan_single hru' hG' D' hzero
  refine ⟨D, by rw [hD]; exact hs, ?_⟩
  have hm := PathDecomp.ends_mod_two D' r'
  have hdr : (delList G [s(r', u')]).degree r' + 1 = G.degree r' := by
    have := hdeg r'; simpa using this
  have her : Even (G.degree r') := (hev r').2 hr
  rw [Nat.even_iff] at her
  show 2 ≤ D.ends r'
  omega

omit [Fintype V] [DecidableEq V] in
/-- The deletion graph of a graph that agrees with `J` off `z` except for one edge `ab`. -/
theorem delVert_eq_delList (J J' : SimpleGraph V) {z a b : V} (haz : a ≠ z) (hbz : b ≠ z)
    (hJ' : ∀ x y, x ≠ z → y ≠ z → (J'.Adj x y ↔ J.Adj x y ∧ s(x, y) ≠ s(a, b))) :
    delVert J' z = delList (delVert J z) [s((⟨a, haz⟩ : {v | v ≠ z}), ⟨b, hbz⟩)] := by
  ext x y
  simp only [delVert, SimpleGraph.induce_adj, delList_adj, List.mem_singleton]
  rw [hJ' x.1 y.1 x.2 y.2]
  refine and_congr_right fun _ => not_congr ?_
  simp only [Sym2.eq_iff, Subtype.ext_iff]

/-- **Root move M1, in terms of the moved instance**: Test1 at `(J', z, w)`, where `J'` agrees
with `J` off `z` except that `rw` is missing (for instance `J' = J − rw − zr + zw`), gives Test1
at `(J, z, r)` when `r` has at most one neighbour in `N(z)`. -/
theorem test1At_of_move1' (J J' : SimpleGraph V) [DecidableRel J.Adj] [DecidableRel J'.Adj]
    {z r w : V} (hz : ∀ v, Even (J.degree v) ↔ v = z) (hrz : r ≠ z) (hwz : w ≠ z)
    (hrw : J.Adj r w)
    (hone : ∀ t₁ t₂, t₁ ≠ z → t₂ ≠ z → J.Adj r t₁ → J.Adj z t₁ → J.Adj r t₂ → J.Adj z t₂ →
      t₁ = t₂)
    (hJ' : ∀ x y, x ≠ z → y ≠ z → (J'.Adj x y ↔ J.Adj x y ∧ s(x, y) ≠ s(r, w)))
    (hzw' : J'.Adj z w) (h' : Test1At J' z w) : Test1At J z r := by
  refine test1At_of_move1 J hz hrz hwz hrw hone ?_
  obtain ⟨D', hs, hw⟩ := h' hzw'
  have he := delVert_eq_delList J J' hrz hwz hJ'
  revert D'
  rw [he]
  intro D' hs hw
  exact ⟨D', hs, hw⟩

/-- **Root move M2, in terms of the moved instance**: Test1 at `(J', z, v)`, where `J'` agrees
with `J` off `z` except that `ru` is missing (for instance `J' = J − ru − zr − zu`), gives Test1
at `(J, z, r)` when the neighbours of `r` in `N(z)` are exactly `u` and `v`. -/
theorem test1At_of_move2' (J J' : SimpleGraph V) [DecidableRel J.Adj] [DecidableRel J'.Adj]
    {z r u v : V} (hz : ∀ v, Even (J.degree v) ↔ v = z) (hrz : r ≠ z) (huz : u ≠ z)
    (hvz : v ≠ z) (hru : J.Adj r u) (hzu : J.Adj z u)
    (htwo : ∀ t, t ≠ z → J.Adj r t → J.Adj z t → t = u ∨ t = v)
    (hJ' : ∀ x y, x ≠ z → y ≠ z → (J'.Adj x y ↔ J.Adj x y ∧ s(x, y) ≠ s(r, u)))
    (hzv' : J'.Adj z v) (h' : Test1At J' z v) : Test1At J z r := by
  refine test1At_of_move2 J hz hrz huz hvz hru hzu htwo ?_
  obtain ⟨D', hs, hv⟩ := h' hzv'
  have he := delVert_eq_delList J J' hrz huz hJ'
  revert D'
  rw [he]
  intro D' hs hv
  exact ⟨D', hs, hv⟩

end rootmoveJ

/-! ### `L_N` and CL -/

/-- **CL contains `L_N`**: a list of disjoint non-adjacent pairs is a list of cherry constraints
(no parent is a child, so there are no chains and no siblings). -/
theorem lN_of_cherryLN (h : CherryLN.{u}) : LN.{u} := by
  intro V _ _ G _ hev L hnd hL
  have hdis := List.nodup_append.mp hnd
  have hCL : CherryList G L :=
    { children := hdis.1
      parents := hdis.2.1
      nonadj := fun p hp => (hL p hp).2
      irrefl := fun p hp h => hdis.2.2 p.1 (List.mem_map_of_mem hp) p.2
        (List.mem_map_of_mem hp) h
      depth := fun p hp q hq hpq _ _ => absurd hpq
        (hdis.2.2 q.1 (List.mem_map_of_mem hq) p.2 (List.mem_map_of_mem hp) |>.symm |> fun h' => h') }
  obtain ⟨D, hD, hi, -⟩ := h V G L hev hCL
  exact ⟨D, hD, hi⟩

section LNmatching

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **`L_N` gives Test1 at every root with matching data** (synthesis §32): a perfect matching
`(a₀, r) :: L` of `J[N(z)]` by edges of `J`, with the pairs oriented as listed. -/
theorem test1At_of_LN_matching (hLN : LN.{u}) (J : SimpleGraph V) [DecidableRel J.Adj] {z r : V}
    (hz : ∀ v, Even (J.degree v) ↔ v = z) (hrz : r ≠ z) {a₀ : {v | v ≠ z}}
    {L : List ({v | v ≠ z} × {v | v ≠ z})}
    (hnd : (pairVerts ((a₀, ⟨r, hrz⟩) :: L)).Nodup)
    (hcover : ∀ v : {v | v ≠ z}, J.Adj z v ↔ v ∈ pairVerts ((a₀, ⟨r, hrz⟩) :: L))
    (hedge : ∀ p ∈ (a₀, ⟨r, hrz⟩) :: L, (delVert J z).Adj p.1 p.2) : Test1At J z r := by
  classical
  set M := (a₀, (⟨r, hrz⟩ : {v | v ≠ z})) :: L with hM
  set B := delVert J z with hB
  have hev : ∀ v, Even (B.degree v) ↔ v ∈ pairVerts M := fun v =>
    (even_delVert_iff_adj J hz v).trans (hcover v)
  have hndE : (M.map pairEdge).Nodup := nodup_map_pairEdge M hnd
  have hin : ∀ e ∈ M.map pairEdge, e ∈ B.edgeSet := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    exact hedge p hp
  have hdeg := delList_degree_count B (M.map pairEdge) hndE hin
  have hcnt := countP_pairEdge_of_nodup M hnd
  have hodd : ∀ v, (delList B (M.map pairEdge)).degree v % 2 = 1 := by
    intro v
    have h1 := hdeg v
    have h2 := hcnt v
    by_cases hv : v ∈ pairVerts M
    · have he : Even (B.degree v) := (hev v).2 hv
      rw [Nat.even_iff] at he
      simp only [hv, ite_true] at h2
      omega
    · have ho : ¬ Even (B.degree v) := fun he => hv ((hev v).1 he)
      rw [Nat.not_even_iff] at ho
      simp only [hv, ite_false] at h2
      omega
  have hev0 : (evenSet (delList B (M.map pairEdge))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro v hv
    simp only [evenSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have := hodd v
    rw [Nat.even_iff] at hv
    omega
  obtain ⟨hfst, hsnd, hsf, -, -⟩ := pairVerts_facts M hnd
  have hnd2 : (M.map Prod.fst ++ M.map Prod.snd).Nodup := by
    rw [List.nodup_append]
    refine ⟨hfst, hsnd, fun a ha b hb hab => ?_⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
    exact hsf p hp (hab ▸ ha)
  obtain ⟨D₀, hD₀, hi⟩ := hLN _ (delList B (M.map pairEdge)) hev0 M hnd2
    (fun p hp => ⟨hodd p.1, fun h => h.2 (List.mem_map_of_mem hp)⟩)
  refine test1At_of_matchingOdd J hz hrz hnd hcover hedge D₀ hD₀ ?_ ?_
  · exact hi _ List.mem_cons_self
  · intro p hp
    exact Or.inr (hi p (List.mem_cons_of_mem _ hp))

end LNmatching

end Gallai
