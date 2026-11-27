import GallaiLean.Marked
import GallaiLean.Realisable

/-!
# Three-connected graphs and the deletion tests (marked-reduction, Theorem 114)

This file sets up the statement of Theorem 114 of the marked-reduction manuscript and proves
its easy direction.

* `KConnected k G`: `G` has at least `k + 1` vertices and deleting any set of fewer than `k`
  vertices leaves a connected graph. `KConnected.walk`, `KConnected.le_degree`
  (minimum degree `≥ k`).
* `delVert J z`: the graph `J − z`, induced on `{v | v ≠ z}`. `delVert_degree`.
* `HasMatchingCut G`: a bipartition into two nonempty sides whose crossing edges form a
  matching.
* `Test1 J z`, `Test2 J z`: the two deletion assertions of Theorem 114. `SpineTests` asks both
  for every three-connected `J` and every `z`; `SpineTestsNMC` only when `J − z` has no
  matching cut.
* `PathDecomp.exists_internal_of_ends_lt`, `exists_two_ends`, `exists_three_ends`: getting
  two ends at a positive even root (`F₂`), or three at an odd root of degree `≥ 3` (`F₃`).
* `PathDecomp.trim_ends`: deleting the private leaf of `addLeaf G x` from a decomposition, with
  the exact effect on the ends at `x`.
* **`spineTests_of_gallai`**: Gallai's conjecture implies both tests (the forward direction of
  Theorem 114), with no matching-cut restriction.
-/

open SimpleGraph

namespace Gallai

universe u

/-! ### Induced subgraphs and vertex connectivity -/

section induce

variable {V : Type u} {G : SimpleGraph V}

/-- A walk of `G` inside `s` gives reachability in the induced graph. -/
theorem induce_reachable_of_walk {s : Set V} : ∀ {a b : V} (p : G.Walk a b)
    (hp : ∀ v ∈ p.support, v ∈ s),
    (G.induce s).Reachable ⟨a, hp a p.start_mem_support⟩ ⟨b, hp b p.end_mem_support⟩
  | _, _, .nil, _ => Reachable.refl _
  | _, _, .cons h p, hp => by
    refine Reachable.trans ?_ (induce_reachable_of_walk p (fun v hv => hp v (by simp [hv])))
    exact Adj.reachable (show (G.induce s).Adj _ _ from h)

/-- Reachability in the induced graph gives a walk of `G` inside `s`. -/
theorem walk_of_induce_reachable {s : Set V} {a b : s} (h : (G.induce s).Reachable a b) :
    ∃ p : G.Walk a b, ∀ v ∈ p.support, v ∈ s := by
  obtain ⟨q⟩ := h
  induction q with
  | nil => exact ⟨Walk.nil, by simp⟩
  | cons h q ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨Walk.cons (SimpleGraph.induce_adj.1 h) p, ?_⟩
    intro v hv
    rw [Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact Subtype.property _
    · exact hp v hv

theorem induce_connected_iff {s : Set V} :
    (G.induce s).Connected ↔
      s.Nonempty ∧ ∀ a ∈ s, ∀ b ∈ s, ∃ p : G.Walk a b, ∀ v ∈ p.support, v ∈ s := by
  constructor
  · intro h
    obtain ⟨⟨v, hv⟩⟩ := h.nonempty
    exact ⟨⟨v, hv⟩, fun a ha b hb => walk_of_induce_reachable (h.preconnected ⟨a, ha⟩ ⟨b, hb⟩)⟩
  · rintro ⟨⟨v, hv⟩, h⟩
    have : Nonempty s := ⟨⟨v, hv⟩⟩
    refine ⟨fun a b => ?_⟩
    obtain ⟨p, hp⟩ := h a a.2 b b.2
    exact induce_reachable_of_walk p hp

variable [Fintype V]

/-- **`k`-connectivity**: at least `k + 1` vertices, and deleting any set of fewer than `k`
vertices leaves a connected graph. -/
def KConnected (k : ℕ) (G : SimpleGraph V) : Prop :=
  k + 1 ≤ Fintype.card V ∧ ∀ X : Finset V, X.card < k → (G.induce ((X : Set V)ᶜ)).Connected

theorem KConnected.walk {k : ℕ} (hG : KConnected k G) {X : Finset V} (hX : X.card < k)
    {a b : V} (ha : a ∉ X) (hb : b ∉ X) : ∃ p : G.Walk a b, ∀ v ∈ p.support, v ∉ X :=
  (induce_connected_iff.mp (hG.2 X hX)).2 a ha b hb

theorem kConnected_of_walks {k : ℕ} (hcard : k + 1 ≤ Fintype.card V)
    (h : ∀ X : Finset V, X.card < k → ∀ a b, a ∉ X → b ∉ X →
      ∃ p : G.Walk a b, ∀ v ∈ p.support, v ∉ X) : KConnected k G := by
  refine ⟨hcard, fun X hX => induce_connected_iff.mpr ⟨?_, fun a ha b hb => h X hX a b ha hb⟩⟩
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := X) (t := Finset.univ)
    (by rw [Finset.card_univ]; omega)
  exact ⟨a, ha⟩

theorem KConnected.mono {j k : ℕ} (hG : KConnected k G) (hjk : j ≤ k) : KConnected j G :=
  ⟨by have := hG.1; omega, fun X hX => hG.2 X (by omega)⟩

theorem KConnected.connected {k : ℕ} (hG : KConnected k G) (hk : 1 ≤ k) : G.Connected := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by have := hG.1; omega)
  refine ⟨fun a b => ?_⟩
  obtain ⟨p, -⟩ := hG.walk (X := ∅) (by simp; omega) (Finset.notMem_empty a)
    (Finset.notMem_empty b)
  exact ⟨p⟩

/-- A `k`-connected graph has minimum degree at least `k`. -/
theorem KConnected.le_degree [DecidableEq V] [DecidableRel G.Adj] {k : ℕ} (hG : KConnected k G)
    (v : V) : k ≤ G.degree v := by
  by_contra hlt
  push Not at hlt
  have hX : (G.neighborFinset v).card < k := by rw [card_neighborFinset_eq_degree]; exact hlt
  obtain ⟨w, -, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := insert v (G.neighborFinset v)) (t := Finset.univ)
    (by rw [Finset.card_univ]; have := Finset.card_insert_le v (G.neighborFinset v)
        have := hG.1; omega)
  have hwv : w ≠ v := fun h => hw (h ▸ Finset.mem_insert_self _ _)
  have hwX : w ∉ G.neighborFinset v := fun h => hw (Finset.mem_insert_of_mem h)
  have hvX : v ∉ G.neighborFinset v := by simp
  obtain ⟨p, hp⟩ := hG.walk hX hvX hwX
  cases p with
  | nil => exact hwv rfl
  | cons h q =>
    exact hp _ (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ q.start_mem_support)
      (by simpa using h)

end induce

/-! ### Deleting a vertex -/

section delVert

variable {V : Type u} {J : SimpleGraph V}

/-- `J − z`: the subgraph induced on `{v | v ≠ z}`. -/
abbrev delVert (J : SimpleGraph V) (z : V) : SimpleGraph {v | v ≠ z} := J.induce {v | v ≠ z}

theorem delVert_degree [Fintype V] [DecidableEq V] [DecidableRel J.Adj] (z : V)
    (v : {v | v ≠ z}) :
    (delVert J z).degree v + (if J.Adj v z then 1 else 0) = J.degree v := by
  have h1 : (delVert J z).degree v = (J.neighborFinset v ∩ {w | w ≠ z}.toFinset).card := by
    rw [← card_neighborFinset_eq_degree, ← Finset.card_map, map_neighborFinset_induce]
  have h2 : J.neighborFinset v ∩ {w | w ≠ z}.toFinset = (J.neighborFinset v).erase z := by
    ext w; simp [and_comm]
  rw [h1, h2, ← card_neighborFinset_eq_degree]
  split_ifs with h
  · exact Finset.card_erase_add_one (by simpa using h)
  · rw [Finset.erase_eq_of_notMem (by simpa using h)]; rfl

/-- `J − z` is connected when `J` is `k`-connected with `k ≥ 2`. -/
theorem KConnected.delVert_connected [Fintype V] [DecidableEq V] {k : ℕ} (hJ : KConnected k J)
    (hk : 2 ≤ k) (z : V) : (delVert J z).Connected := by
  refine induce_connected_iff.mpr ⟨?_, fun a ha b hb => ?_⟩
  · obtain ⟨w, -, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {z})
      (t := Finset.univ) (by rw [Finset.card_univ, Finset.card_singleton]; have := hJ.1; omega)
    exact ⟨w, by simpa using hw⟩
  · obtain ⟨p, hp⟩ := hJ.walk (X := {z}) (by simp; omega) (by simpa using ha) (by simpa using hb)
    exact ⟨p, fun v hv => by simpa using hp v hv⟩

end delVert

/-! ### Matching cuts and the class `C` -/

section matching

variable {V : Type u}

/-- `G` has a **matching cut**: a bipartition `(X, Xᶜ)` with both sides nonempty such that every
vertex has at most one neighbour on the other side. -/
def HasMatchingCut (G : SimpleGraph V) : Prop :=
  ∃ X : Set V, X.Nonempty ∧ Xᶜ.Nonempty ∧
    ∀ a b c, G.Adj a b → G.Adj a c → (a ∈ X ↔ b ∉ X) → (a ∈ X ↔ c ∉ X) → b = c

/-- The class `C` of Theorem 59: two-connected graphs without a matching cut. -/
def InClassC [Fintype V] (B : SimpleGraph V) : Prop := KConnected 2 B ∧ ¬ HasMatchingCut B

end matching

/-! ### The two deletion tests of Theorem 114 -/

section tests

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Assertion 1 of Theorem 114** for `(J, z)`: if `z` is the only even-degree vertex of `J`,
then for each `r ∈ N_J(z)`, `J − z` has a partition into at most `(|V(J)| − 1)/2` paths, at least
two of them ending at `r`. -/
def Test1 (J : SimpleGraph V) [DecidableRel J.Adj] (z : V) : Prop :=
  (∀ v, Even (J.degree v) ↔ v = z) → ∀ r (hr : J.Adj z r),
    ∃ D : PathDecomp (delVert J z),
      D.size ≤ (Fintype.card V - 1) / 2 ∧ 2 ≤ D.ends ⟨r, hr.ne'⟩

/-- **Assertion 2 of Theorem 114** for `(J, z)`: if `z, r` are the only even-degree vertices of
`J` and are adjacent, then `J − z` has a partition into at most `|V(J)|/2` paths, at least three
of them ending at `r`. -/
def Test2 (J : SimpleGraph V) [DecidableRel J.Adj] (z : V) : Prop :=
  ∀ r (hr : J.Adj z r), (∀ v, Even (J.degree v) ↔ v = z ∨ v = r) →
    ∃ D : PathDecomp (delVert J z), D.size ≤ Fintype.card V / 2 ∧ 3 ≤ D.ends ⟨r, hr.ne'⟩

end tests

/-- Both tests of Theorem 114, for every three-connected `J` and every vertex `z`. -/
def SpineTests : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj] (z : V),
    KConnected 3 J → Test1 J z ∧ Test2 J z

/-- Both tests of Theorem 114, restricted to `J − z` without a matching cut. -/
def SpineTestsNMC : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj] (z : V),
    KConnected 3 J → ¬ HasMatchingCut (delVert J z) → Test1 J z ∧ Test2 J z

theorem SpineTests.nmc (h : SpineTests.{u}) : SpineTestsNMC.{u} :=
  fun V _ _ J _ z hJ _ => h V J z hJ

/-! ### Two ends at an even root, three at an odd root -/

section ends

variable {W : Type u} [DecidableEq W] {G : SimpleGraph W} {x : W}

/-- If a decomposition has fewer ends at `x` than `deg x`, some path passes through `x`. -/
theorem PathDecomp.exists_internal_of_ends_lt [Fintype (G.neighborSet x)] (D : PathDecomp G)
    (h : D.ends x < G.degree x) :
    ∃ Q ∈ D.paths, x ∈ Q.walk.support ∧ Q.src ≠ x ∧ Q.tgt ≠ x := by
  by_contra hc
  push Not at hc
  have hle : G.degree x ≤ D.ends x := by
    rw [D.degree_eq_sum x, PathDecomp.ends]
    refine sum_map_le_sum_map _ _ _ (fun P hP => ?_)
    have h1 := P.incid_add_endsAt x
    by_cases hx : x ∈ P.walk.support
    · have h2 : P.src = x ∨ P.tgt = x := by
        by_cases hs : P.src = x
        · exact Or.inl hs
        · exact Or.inr (hc P hP hx hs)
      have := P.incid_of_end h2
      have : 1 ≤ P.endsAt x := by
        unfold GPath.endsAt; rcases h2 with h2 | h2 <;> simp [h2]
      omega
    · rw [P.incid_of_not_mem hx]; exact Nat.zero_le _
  omega

/-- Split at an internal visit, which exists when `ends x < deg x`. -/
theorem PathDecomp.exists_split_of_ends_lt [Fintype (G.neighborSet x)] (D : PathDecomp G)
    (h : D.ends x < G.degree x) :
    ∃ D' : PathDecomp G, D'.size = D.size + 1 ∧ D'.ends x = D.ends x + 2 := by
  obtain ⟨Q, hQ, hx, hs, ht⟩ := D.exists_internal_of_ends_lt h
  obtain ⟨D', h1, h2⟩ := D.exists_split hQ hx hs ht
  exact ⟨D', h1, by rw [h2]; simp⟩

/-- **Two ends at a positive even root**: from a decomposition of leaf cost `≤ k` (that is,
`|D| + [x is not an end] ≤ k`) one gets `F₂(G, x) ≤ k`. -/
theorem exists_two_ends [Fintype (G.neighborSet x)] (D : PathDecomp G) {k : ℕ}
    (hD : leafCost D x ≤ k) (hev : Even (G.degree x)) (hpos : 0 < G.degree x) :
    ∃ D' : PathDecomp G, D'.size ≤ k ∧ 2 ≤ D'.ends x := by
  unfold leafCost at hD
  by_cases h0 : D.ends x = 0
  · obtain ⟨D', h1, h2⟩ := D.exists_split_of_ends_eq_zero hpos h0
    refine ⟨D', ?_, ?_⟩
    · rw [h1]; simp only [h0, ite_true] at hD; omega
    · rw [h2 x, h0]; simp
  · refine ⟨D, ?_, ?_⟩
    · simpa [h0] using hD
    · have := D.ends_mod_two x
      rw [Nat.even_iff] at hev
      omega

/-- **Three ends at an odd root of degree `≥ 3`**: from any decomposition of size `≤ k` one gets
`F₃(G, x) ≤ k + 1` (split once at an internal visit if needed). -/
theorem exists_three_ends [Fintype (G.neighborSet x)] (D : PathDecomp G) {k : ℕ}
    (hD : D.size ≤ k) (hodd : Odd (G.degree x)) (h3 : 3 ≤ G.degree x) :
    ∃ D' : PathDecomp G, D'.size ≤ k + 1 ∧ 3 ≤ D'.ends x := by
  have hpar := D.ends_mod_two x
  rw [Nat.odd_iff] at hodd
  by_cases he : 3 ≤ D.ends x
  · exact ⟨D, by omega, he⟩
  · obtain ⟨D', h1, h2⟩ := D.exists_split_of_ends_lt (by omega : D.ends x < G.degree x)
    exact ⟨D', by omega, by omega⟩

/-- On a path of `addLeaf G x`, the kept edges at `x` plus the leaf edge are all its edges
at `some x`. -/
theorem kept_count_add (P : GPath (addLeaf G x)) :
    ((P.edges.filter bothSome).map (Sym2.map (unSome x))).countP (fun e => decide (x ∈ e)) +
      P.edges.count s(none, some x) = P.incid (some x) := by
  unfold GPath.incid
  rw [List.countP_eq_countP_filter_add P.edges (fun e => decide (some x ∈ e)) bothSome,
    List.countP_map]
  congr 1
  · apply List.countP_congr
    intro e he
    rw [List.mem_filter] at he
    induction e using Sym2.inductionOn with
    | hf a b =>
    simp only [bothSome_mk, Bool.and_eq_true] at he
    obtain ⟨-, ha, hb⟩ := he
    cases a with
    | none => simp at ha
    | some a =>
      cases b with
      | none => simp at hb
      | some b => simp [unSome]
  · rw [List.countP_filter, List.count]
    apply List.countP_congr
    intro e he
    have heG := P.walk.edges_subset_edgeSet he
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq,
      beq_iff_eq]
    constructor
    · rintro rfl
      exact ⟨Sym2.mem_mk_right _ _, rfl⟩
    · rintro ⟨-, hS⟩
      apply addLeaf_eq_of_none_mem heG
      induction e using Sym2.inductionOn with
      | hf a b =>
      simp only [bothSome_mk, Bool.and_eq_false_iff] at hS
      rcases hS with h | h
      · cases a with
        | none => exact Sym2.mem_mk_left _ _
        | some a => simp at h
      · cases b with
        | none => exact Sym2.mem_mk_right _ _
        | some b => simp at h

/-- **Trimming the private leaf, with ends.** A decomposition of `addLeaf G x` gives one of `G`
that either keeps the size and gains an end at `x` (the leaf path continued past `x`), or loses a
path and an end at `x` (the leaf path was the leaf edge alone). -/
theorem PathDecomp.trim_ends (D' : PathDecomp (addLeaf G x)) :
    ∃ D : PathDecomp G, (D.size ≤ D'.size ∧ D.ends x = D'.ends (some x) + 1) ∨
      (D.size + 1 ≤ D'.size ∧ D.ends x + 1 = D'.ends (some x)) := by
  have hleaf : s(none, some x) ∈ (addLeaf G x).edgeSet := by rw [mem_edgeSet]; rfl
  obtain ⟨Q₀, hQ₀, hlQ₀⟩ := List.mem_flatMap.mp ((D'.covers _).1 hleaf)
  obtain ⟨D, hsize, -, hends⟩ := D'.project_full (unSome x) bothSome _ trim_injOn trim_hT
    trim_hcov (fun P _ => trim_hasPiece P)
  refine ⟨D, ?_⟩
  obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hQ₀
  have hc0 : 1 ≤ Q₀.edges.count s(none, some x) := List.count_pos_iff.mpr hlQ₀
  have hc1 : Q₀.edges.count s(none, some x) ≤ 1 :=
    List.nodup_iff_count_le_one.mp Q₀.isPath.isTrail.edges_nodup _
  have hcount : ∀ P ∈ l₁ ++ l₂, P.edges.count s(none, some x) = 0 := by
    have h := D'.sum_count_le_one s(none, some x)
    rw [hl] at h
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at h
    have h1 : (l₁.map (fun P => P.edges.count s(none, some x))).sum = 0 := by omega
    have h2 : (l₂.map (fun P => P.edges.count s(none, some x))).sum = 0 := by omega
    intro P hP
    rcases List.mem_append.mp hP with hP | hP
    · exact List.sum_eq_zero_iff_forall_eq_nat.mp h1 _ (List.mem_map_of_mem hP)
    · exact List.sum_eq_zero_iff_forall_eq_nat.mp h2 _ (List.mem_map_of_mem hP)
  set g : GPath (addLeaf G x) → ℕ := fun P =>
    if ((P.edges.filter bothSome).map (Sym2.map (unSome x))).countP
      (fun e => decide (x ∈ e)) = 1 then 1 else 0 with hg
  have hgP : ∀ P ∈ l₁ ++ l₂, g P = P.endsAt (some x) := by
    intro P hP
    have := kept_count_add P
    rw [hcount P hP, add_zero] at this
    simp only [hg, P.endsAt_eq_ite, this]
  have hsum : ∀ l : List (GPath (addLeaf G x)), (∀ P ∈ l, P ∈ l₁ ++ l₂) →
      (l.map g).sum = (l.map (fun P => P.endsAt (some x))).sum := fun l hl' =>
    congrArg List.sum (List.map_congr_left (fun P hP => hgP P (hl' P hP)))
  have hE : D.ends x = (l₁.map g).sum + g Q₀ + (l₂.map g).sum := by
    rw [hends x, hl, hg]
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    ring
  have hE' : D'.ends (some x) = (l₁.map (fun P => P.endsAt (some x))).sum +
      Q₀.endsAt (some x) + (l₂.map (fun P => P.endsAt (some x))).sum := by
    unfold PathDecomp.ends; rw [hl]
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    ring
  rw [hsum l₁ (fun P hP => List.mem_append_left _ hP),
    hsum l₂ (fun P hP => List.mem_append_right _ hP)] at hE
  have hκ := kept_count_add Q₀
  have hinc := Q₀.incid_add_endsAt (some x)
  have hendQ := Q₀.endsAt_eq_ite (some x)
  by_cases hS : Q₀.edges.any bothSome = true
  · have h1 : ((Q₀.edges.filter bothSome).map (Sym2.map (unSome x))).countP
        (fun e => decide (x ∈ e)) = 1 := by
      rw [List.countP_map]
      simpa only [Function.comp_def] using leaf_path_count Q₀ hlQ₀ hS
    have hgQ : g Q₀ = 1 := by rw [hg]; simp only [h1, ite_true]
    have hi : Q₀.incid (some x) = 2 := by omega
    rw [hi] at hendQ
    simp only [OfNat.ofNat_ne_one, ite_false] at hendQ
    left
    refine ⟨hsize.trans List.countP_le_length, ?_⟩
    rw [hE, hE', hgQ, hendQ]; ring
  · have hfil : Q₀.edges.filter bothSome = [] := by
      rw [List.filter_eq_nil_iff]
      intro e he hSe
      exact hS (List.any_eq_true.mpr ⟨e, he, hSe⟩)
    have hgQ : g Q₀ = 0 := by rw [hg]; simp [hfil]
    rw [hfil] at hκ
    simp only [List.map_nil, List.countP_nil, zero_add] at hκ
    have hi : Q₀.incid (some x) = 1 := by omega
    rw [hi] at hendQ
    simp only [ite_true] at hendQ
    right
    refine ⟨?_, ?_⟩
    · have hlt : D'.paths.countP (fun P => P.edges.any bothSome) < D'.paths.length := by
        rw [List.countP_eq_length_filter]
        exact List.length_filter_lt_length_iff_exists.mpr ⟨Q₀, hQ₀, by simpa using hS⟩
      unfold PathDecomp.size at hsize ⊢
      omega
    · rw [hE, hE', hgQ, hendQ]; ring

end ends

/-! ### Degrees after adding a leaf or deleting a vertex -/

section degrees

variable {W : Type u}

instance addLeaf.decRel [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj] (r : W) :
    DecidableRel (addLeaf G r).Adj := fun x y =>
  match x, y with
  | some a, some b => inferInstanceAs (Decidable (G.Adj a b))
  | none, some b => inferInstanceAs (Decidable (b = r))
  | some a, none => inferInstanceAs (Decidable (a = r))
  | none, none => inferInstanceAs (Decidable False)

theorem addLeaf_degree_some (G : SimpleGraph W) (x v : W) [Fintype (G.neighborSet v)]
    [Fintype ((addLeaf G x).neighborSet (some v))] [Decidable (v = x)] :
    (addLeaf G x).degree (some v) = G.degree v + if v = x then 1 else 0 := by
  classical
  have h : (addLeaf G x).neighborFinset (some v) =
      (if v = x then insert none else id) ((G.neighborFinset v).map Function.Embedding.some) := by
    ext w
    cases w with
    | none => split_ifs with h <;> simp [mem_neighborFinset, h]
    | some a => split_ifs with h <;> simp [mem_neighborFinset]
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree, h]
  split_ifs with hv
  · rw [Finset.card_insert_of_notMem (by simp), Finset.card_map]
  · simp

theorem addLeaf_degree_none [Fintype W] [DecidableEq W] (G : SimpleGraph W) (x : W)
    [Fintype ((addLeaf G x).neighborSet none)] : (addLeaf G x).degree none = 1 := by
  classical
  have h : (addLeaf G x).neighborFinset none = {some x} := by
    ext w
    cases w with
    | none => simp [mem_neighborFinset]
    | some a => simp [mem_neighborFinset]
  rw [← card_neighborFinset_eq_degree, h, Finset.card_singleton]

theorem card_delVert [Fintype W] [DecidableEq W] (z : W) :
    Fintype.card {v | v ≠ z} = Fintype.card W - 1 := by
  rw [Fintype.card_ofFinset]
  simp [Finset.filter_ne', Finset.card_erase_of_mem]

end degrees

/-! ### Gallai implies both tests (the forward direction of Theorem 114) -/

section forward

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Gallai ⇒ assertion 1.** `J − z` is connected of even order and `r` has positive even
degree in it; the rooted private-leaf test (equivalent to Gallai) and the private-leaf formula give
a decomposition of leaf cost `≤ (|J| − 1)/2`, hence `F₂(J − z, r) ≤ (|J| − 1)/2`. -/
theorem test1_of_gallai (hG : GallaiConjecture.{u}) (J : SimpleGraph V) [DecidableRel J.Adj]
    (z : V) (hJ : KConnected 3 J) : Test1 J z := by
  intro heven r hr
  set r' : {v | v ≠ z} := ⟨r, hr.ne'⟩
  have hHc : (delVert J z).Connected := hJ.delVert_connected (by norm_num) z
  -- parity of the order
  have hodd : (Finset.univ.filter (fun v => Odd (J.degree v))) = Finset.univ.erase z := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    rw [← Nat.not_even_iff_odd, heven v]
  have hev : Even (Fintype.card V - 1) := by
    have := J.even_card_odd_degree_vertices
    rwa [hodd, Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ] at this
  have hcard := card_delVert z
  -- the root degree
  have hrJ : J.Adj r z := hr.symm
  have hdeg : (delVert J z).degree r' + (if J.Adj r z then 1 else 0) = J.degree r :=
    delVert_degree z r'
  simp only [hrJ, ite_true] at hdeg
  have h3 := hJ.le_degree r
  have hrodd : ¬ Even (J.degree r) := by rw [heven r]; exact hr.ne'
  rw [Nat.not_even_iff_odd, Nat.odd_iff] at hrodd
  have hevr : Even ((delVert J z).degree r') := by
    rw [Nat.even_iff]; omega
  have hposr : 0 < (delVert J z).degree r' := by omega
  -- the rooted test
  have hR := rootedTest_of_gallai hG _ (delVert J z) hHc (by rw [hcard]; exact hev) r'
  obtain ⟨D, hD⟩ := exists_leafCost_le (delVert J z) r'
  obtain ⟨D', h1, h2⟩ := exists_two_ends D (hD.trans hR) hevr hposr
  exact ⟨D', by rw [hcard] at h1; exact h1, h2⟩

/-- **Gallai ⇒ assertion 2.** `J − z` has odd order `2k + 1` and `r` has odd degree `≥ 3` in it.
Add a leaf at `r` (order `2k + 2`); the rooted test at `r` gives a decomposition of the leafed graph
into `≤ k + 1` paths with two ends at `r`. Trimming the leaf gives three ends at `r`, or loses a
path, which pays for a split at an internal visit of `r`. -/
theorem test2_of_gallai (hG : GallaiConjecture.{u}) (J : SimpleGraph V) [DecidableRel J.Adj]
    (z : V) (hJ : KConnected 3 J) : Test2 J z := by
  intro r hr heven
  set r' : {v | v ≠ z} := ⟨r, hr.ne'⟩
  have hrz : r ≠ z := hr.ne'
  have hHc : (delVert J z).Connected := hJ.delVert_connected (by norm_num) z
  have hodd : (Finset.univ.filter (fun v => Odd (J.degree v))) =
      (Finset.univ.erase z).erase r := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    rw [← Nat.not_even_iff_odd, heven v]
    tauto
  have hev : Even (Fintype.card V) := by
    have := J.even_card_odd_degree_vertices
    rw [hodd, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hrz, Finset.mem_univ r⟩),
      Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ] at this
    have h4 := hJ.1
    obtain ⟨m, hm⟩ := this
    exact ⟨m + 1, by omega⟩
  have hcard := card_delVert z
  have hrJ : J.Adj r z := hr.symm
  have hdeg : (delVert J z).degree r' + (if J.Adj r z then 1 else 0) = J.degree r :=
    delVert_degree z r'
  simp only [hrJ, ite_true] at hdeg
  have h3 := hJ.le_degree r
  have hreven : Even (J.degree r) := (heven r).mpr (Or.inr rfl)
  rw [Nat.even_iff] at hreven
  have hoddr : Odd ((delVert J z).degree r') := by rw [Nat.odd_iff]; omega
  have h3r : 3 ≤ (delVert J z).degree r' := by omega
  -- one private leaf at `r`, then the rooted test at `r` on the leafed graph
  set H' := addLeaf (delVert J z) r'
  have hH'c : H'.Connected := addLeaf_connected hHc r'
  have hcard' : Fintype.card (Option {v | v ≠ z}) = Fintype.card V := by
    rw [Fintype.card_option, hcard]; have := hJ.1; omega
  have hR := rootedTest_of_gallai hG _ H' hH'c (by rw [hcard']; exact hev) (some r')
  rw [hcard'] at hR
  obtain ⟨D₁, hD₁⟩ := exists_leafCost_le H' (some r')
  have hdeg' : H'.degree (some r') = (delVert J z).degree r' + 1 := by
    rw [addLeaf_degree_some]; simp
  obtain ⟨D₂, h21, h22⟩ := exists_two_ends D₁ (hD₁.trans hR)
    (by rw [hdeg', Nat.even_add_one, Nat.not_even_iff_odd]; exact hoddr) (by omega)
  obtain ⟨D, hD | hD⟩ := PathDecomp.trim_ends D₂
  · exact ⟨D, hD.1.trans h21, by omega⟩
  · obtain ⟨D', h1, h2⟩ := exists_three_ends D (k := Fintype.card V / 2 - 1) (by omega) hoddr h3r
    exact ⟨D', by omega, h2⟩

/-- **Theorem 114, forward direction**: Gallai's conjecture implies both deletion tests, for
every three-connected `J` (no matching-cut restriction is needed). -/
theorem spineTests_of_gallai (hG : GallaiConjecture.{u}) : SpineTests.{u} :=
  fun _ _ _ J _ z hJ => ⟨test1_of_gallai hG J z hJ, test2_of_gallai hG J z hJ⟩

end forward

/-! ### The parity apex is three-connected -/

section apexConn

variable {V : Type u} [Fintype V] [DecidableEq V] {B : SimpleGraph V} {S : Finset V}

omit [Fintype V] [DecidableEq V] in
/-- A walk of `B` lifts to the apex graph `apex B S`, through the same vertices. -/
theorem apex_walk_of_walk : ∀ {a b : V} (p : B.Walk a b),
    ∃ q : (apex B S).Walk (some a) (some b), q.support = p.support.map some
  | _, _, .nil => ⟨.nil, rfl⟩
  | _, _, .cons h p => by
    obtain ⟨q, hq⟩ := apex_walk_of_walk p
    exact ⟨.cons (show (apex B S).Adj (some _) (some _) from h) q, by simp [hq]⟩

/-- **The apex lemma** (A2 audit, §4.2). Let `B` be two-connected and `|S| ≥ 3`. If, for every
pair `x ≠ y`, every vertex `v ∉ {x, y}` is joined inside `B − {x, y}` to a vertex of `S` (that is,
every component of `B − {x, y}` meets `S`), then `B` plus an apex adjacent to `S` is
three-connected. -/
theorem apex_kConnected_three (hB : KConnected 2 B) (hS : 3 ≤ S.card)
    (hcomp : ∀ x y, x ≠ y → ∀ v, v ≠ x → v ≠ y →
      ∃ s ∈ S, s ≠ x ∧ s ≠ y ∧ ∃ p : B.Walk v s, ∀ w ∈ p.support, w ≠ x ∧ w ≠ y) :
    KConnected 3 (apex B S) := by
  refine kConnected_of_walks ?_ ?_
  · rw [Fintype.card_option]; have := hB.1; omega
  intro X hX a b ha hb
  by_cases hn : none ∈ X
  · -- the apex is deleted: at most one old vertex is deleted, and `B` is two-connected
    have hX' : X.eraseNone.card < 2 := by rw [Finset.card_eraseNone_of_mem hn]; omega
    cases a with
    | none => exact absurd hn ha
    | some a =>
    cases b with
    | none => exact absurd hn hb
    | some b =>
    obtain ⟨p, hp⟩ := hB.walk hX' (by simpa [Finset.mem_eraseNone] using ha)
      (by simpa [Finset.mem_eraseNone] using hb)
    obtain ⟨q, hq⟩ := apex_walk_of_walk (S := S) p
    refine ⟨q, fun w hw => ?_⟩
    rw [hq, List.mem_map] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    simpa [Finset.mem_eraseNone] using hp w' hw'
  · -- the apex survives: join every surviving vertex to it
    have key : ∀ v, v ∉ X → ∃ q : (apex B S).Walk v none, ∀ w ∈ q.support, w ∉ X := by
      intro v hv
      cases v with
      | none => exact ⟨.nil, by simpa using hn⟩
      | some v =>
      have hv' : v ∉ X.eraseNone := by simpa [Finset.mem_eraseNone] using hv
      have hcard : X.eraseNone.card ≤ 2 := by
        rw [Finset.card_eraseNone_of_notMem hn]; omega
      obtain ⟨t, htS, p, hp⟩ : ∃ t ∈ S, ∃ p : B.Walk v t, ∀ w ∈ p.support, w ∉ X.eraseNone := by
        rcases Nat.lt_or_ge X.eraseNone.card 2 with hlt | hge
        · obtain ⟨t, htS, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card
            (s := X.eraseNone) (t := S) (by omega)
          obtain ⟨p, hp⟩ := hB.walk hlt hv' ht
          exact ⟨t, htS, p, hp⟩
        · obtain ⟨x, y, hxy, hXe⟩ := Finset.card_eq_two.mp (by omega : X.eraseNone.card = 2)
          rw [hXe] at hv' ⊢
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv' ⊢
          obtain ⟨t, htS, -, -, p, hp⟩ := hcomp x y hxy v hv'.1 hv'.2
          exact ⟨t, htS, p, hp⟩
      obtain ⟨q, hq⟩ := apex_walk_of_walk (S := S) p
      refine ⟨q.concat (show (apex B S).Adj (some t) none from htS), fun w hw => ?_⟩
      rw [Walk.support_concat, List.mem_append, List.mem_singleton, hq, List.mem_map] at hw
      rcases hw with ⟨w', hw', rfl⟩ | rfl
      · simpa [Finset.mem_eraseNone] using hp w' hw'
      · exact hn
    obtain ⟨qa, hqa⟩ := key a ha
    obtain ⟨qb, hqb⟩ := key b hb
    refine ⟨qa.append qb.reverse, fun w hw => ?_⟩
    rw [Walk.support_append, List.mem_append] at hw
    rcases hw with hw | hw
    · exact hqa w hw
    · exact hqb w (by rw [← List.mem_reverse, ← Walk.support_reverse]; exact List.mem_of_mem_tail hw)

end apexConn

/-! ### Statements of Theorems 59 and 113 -/

section statements

variable {V : Type u} [Fintype V]

/-- Every two-connected induced subgraph of `F` has at most `m` vertices, i.e. the two-connected
blocks of `F` have order at most `m`. -/
def SmallBlocks (F : SimpleGraph V) (m : ℕ) : Prop :=
  ∀ S : Finset V, KConnected 2 (F.induce (S : Set V)) → S.card ≤ m

theorem smallBlocks_card (F : SimpleGraph V) : SmallBlocks F (Fintype.card V) :=
  fun S _ => Finset.card_le_univ S

/-- The two rooted assertions of Theorem 59 at the root `x`:
`F₂(B, x) ≤ k` if `|B| = 2k` and `d(x)` is even, and `F₃(B, x) ≤ k + 1` if `|B| = 2k + 1` and
`d(x)` is odd. -/
def RootedAt [DecidableEq V] (B : SimpleGraph V) [DecidableRel B.Adj] (x : V) : Prop :=
  (Even (Fintype.card V) → Even (B.degree x) →
    ∃ D : PathDecomp B, D.size ≤ Fintype.card V / 2 ∧ 2 ≤ D.ends x) ∧
  (Odd (Fintype.card V) → Odd (B.degree x) →
    ∃ D : PathDecomp B, D.size ≤ Fintype.card V / 2 + 1 ∧ 3 ≤ D.ends x)

end statements

/-- The marked bound (1) on every connected graph whose two-connected blocks have order `≤ m`. -/
def MarkedBoundUpTo (m : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (F : SimpleGraph V), F.Connected → SmallBlocks F m →
    ∀ S : Finset V, S.Nonempty → markedNumber F S ≤ (Fintype.card V - S.card) / 2

/-- **Theorem 59** (marked-reduction, p. 84), in the finite-order form recommended by the A2 audit
(finding F1): if both rooted assertions hold on every member of the class `C` (two-connected, no
matching cut) with at most `m + 1` vertices, then the marked bound holds on every connected graph
whose two-connected blocks have order at most `m`. It is proved as `thm59` in
`GallaiLean/Thm59.lean`. -/
def Thm59Statement : Prop :=
  ∀ m : ℕ, (∀ (W : Type u) [Fintype W] [DecidableEq W] (B : SimpleGraph W) [DecidableRel B.Adj],
    InClassC B → Fintype.card W ≤ m + 1 → ∀ x, RootedAt B x) → MarkedBoundUpTo.{u} m

/-- `C` is the vertex set of a component of `B − {x, y}`, and `{x, y}` is a separating pair. -/
structure IsSepComponent {V : Type u} (B : SimpleGraph V) (x y : V) (C : Finset V) : Prop where
  ne : x ≠ y
  x_notMem : x ∉ C
  y_notMem : y ∉ C
  nonempty : C.Nonempty
  conn : ∀ a ∈ C, ∀ b ∈ C, ∃ p : B.Walk a b, ∀ v ∈ p.support, v ∈ C
  closed : ∀ a ∈ C, ∀ b, B.Adj a b → b ∈ C ∨ b = x ∨ b = y
  sep : ∃ w, w ∉ C ∧ w ≠ x ∧ w ≠ y

/-- **Theorem 113** (separator theorem, marked-reduction p. 127), in the form of the A2 audit's
remark F7: let `B` be two-connected of order `n` and assume the marked bound on connected graphs
whose blocks have order `≤ n − 2` (which Theorem 59 provides at a least-order failure). If `C` is a
component of `B − {x, y}` for a separating pair `{x, y}`, `r ∉ C` (`r` may be a port), and every
vertex of `C` has odd degree in `B`, then `B` passes the rooted test at `r`. -/
def SeparatorStatement : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (B : SimpleGraph V) [DecidableRel B.Adj],
    MarkedBoundUpTo.{u} (Fintype.card V - 2) → KConnected 2 B →
    ∀ (x y : V) (C : Finset V), IsSepComponent B x y C → ∀ r, r ∉ C →
      (∀ c ∈ C, Odd (B.degree c)) → RootedAt B r

/-! ### Transport along an injective vertex map, with ends -/

section transport

variable {V V' : Type u} [DecidableEq V] [DecidableEq V'] {G : SimpleGraph V}
  {G' : SimpleGraph V'}

/-- A decomposition maps along an injective vertex map whose image of `G.edgeSet` is
`G'.edgeSet`, with the same end counts. -/
theorem PathDecomp.map_injective_ends (D : PathDecomp G) (f : V → V')
    (hinj : Function.Injective f)
    (hcov : ∀ e', e' ∈ G'.edgeSet ↔ ∃ e ∈ G.edgeSet, e.map f = e') :
    ∃ D' : PathDecomp G', D'.size ≤ D.size ∧ ∀ v, D'.ends (f v) = D.ends v := by
  have hpiece : ∀ P ∈ D.paths, HasPiece G' f (fun _ => true) P := by
    intro P _
    refine hasPiece_of_walk P.walk P.isPath ?_ (fun x _ y _ h => hinj h) (by simp [GPath.edges])
    intro e he
    exact (hcov _).2 ⟨e, P.walk.edges_subset_edgeSet he, rfl⟩
  obtain ⟨D', h1, -, h3⟩ := D.project_full f (fun _ => true) Set.univ hinj.injOn (by simp)
    (by simpa using hcov) hpiece
  refine ⟨D', h1.trans List.countP_le_length, fun v => ?_⟩
  rw [h3, PathDecomp.ends]
  congr 1
  refine List.map_congr_left (fun P _ => ?_)
  rw [P.endsAt_eq_ite, GPath.incid, List.filter_true, List.countP_map]
  congr 2
  apply List.countP_congr
  intro e _
  simp only [Function.comp_apply, decide_eq_true_eq, Sym2.mem_map]
  constructor
  · rintro ⟨a, ha, hfa⟩; rwa [← hinj hfa]
  · intro h; exact ⟨v, h, rfl⟩

end transport

/-! ### Few even vertices: Lovász's theorem passes the rooted test -/

section fewEven

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem card_filter_option (P : Option V → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      (if P none then 1 else 0) + (Finset.univ.filter (fun a => P (some a))).card := by
  rw [Finset.card_filter, Finset.card_filter, Fintype.sum_option]

/-- If at most two vertices lie in `{v : d(v) even} ∪ {r}`, the rooted test passes at `r` by
Lovász's theorem (at even order with a private leaf at `r`). This is the `|S| ≤ 2` step of the
proof of Theorem 114. -/
theorem rootedAt_of_few_even (hL : LovaszStatement.{u}) (B : SimpleGraph V) [DecidableRel B.Adj]
    (hB : KConnected 2 B) (r : V)
    (hfew : (Finset.univ.filter (fun v => Even (B.degree v) ∨ v = r)).card ≤ 2) :
    RootedAt B r := by
  have hrS : r ∈ Finset.univ.filter (fun v => Even (B.degree v) ∨ v = r) := by simp
  have hsub : ∀ P : V → Prop, [DecidablePred P] → (∀ v, P v → (Even (B.degree v) ∨ v = r) ∧ v ≠ r) →
      (Finset.univ.filter P).card ≤ 1 := by
    intro P _ hP
    have : Finset.univ.filter P ⊆
        (Finset.univ.filter (fun v => Even (B.degree v) ∨ v = r)).erase r := by
      intro v hv
      rw [Finset.mem_filter] at hv
      exact Finset.mem_erase.mpr ⟨(hP v hv.2).2, by simpa using (hP v hv.2).1⟩
    have := Finset.card_le_card this
    rw [Finset.card_erase_of_mem hrS] at this
    omega
  have h2 := hB.le_degree r
  constructor
  · intro _ hr
    have hcnt : (Finset.univ.filter (fun w => Even ((addLeaf B r).degree w))).card ≤ 1 := by
      rw [card_filter_option, addLeaf_degree_none]
      simp only [Nat.not_even_one, ite_false, zero_add]
      apply hsub
      intro v hv
      rw [addLeaf_degree_some] at hv
      by_cases hvr : v = r
      · subst hvr
        simp only [ite_true, Nat.even_add_one] at hv
        exact absurd hr hv
      · simp only [hvr, ite_false, add_zero] at hv
        exact ⟨Or.inl hv, hvr⟩
    have hp := hL _ (addLeaf B r) hcnt
    rw [Fintype.card_option] at hp
    obtain ⟨D, hD⟩ := exists_leafCost_le B r
    obtain ⟨D', h1, h2⟩ := exists_two_ends D (k := Fintype.card V / 2) (by
      have : (Fintype.card V + 1) / 2 = Fintype.card V / 2 := by
        obtain ⟨m, hm⟩ := ‹Even (Fintype.card V)›; omega
      omega) hr (by omega)
    exact ⟨D', h1, h2⟩
  · intro _ hr
    have hcnt : (Finset.univ.filter (fun w => Even (B.degree w))).card ≤ 1 := by
      apply hsub
      intro v hv
      refine ⟨Or.inl hv, ?_⟩
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hr) hv
    have hp := hL _ B hcnt
    obtain ⟨D, hD⟩ := pathNumber_spec B
    have h3 : 3 ≤ B.degree r := by
      rcases Nat.lt_or_ge (B.degree r) 3 with h | h
      · have : B.degree r = 2 := by omega
        rw [this] at hr; exact absurd hr (by decide)
      · exact h
    exact exists_three_ends D (hD ▸ hp) hr h3

end fewEven

/-! ### The converse of Theorem 114 -/

section converse

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Either some vertex of `S` is reachable from `v` in `B − {x, y}`, or the vertices reachable
from `v` form a component of `B − {x, y}` that misses `S` and is separated from the rest. -/
theorem exists_sepComponent_or {B : SimpleGraph V} {S : Finset V} (hS : 3 ≤ S.card) {x y : V}
    (hxy : x ≠ y) {v : V} (hvx : v ≠ x) (hvy : v ≠ y) :
    (∃ s ∈ S, s ≠ x ∧ s ≠ y ∧ ∃ p : B.Walk v s, ∀ w ∈ p.support, w ≠ x ∧ w ≠ y) ∨
      ∃ C : Finset V, IsSepComponent B x y C ∧ ∀ s ∈ S, s ∉ C := by
  classical
  set C := Finset.univ.filter
    (fun w => w ≠ x ∧ w ≠ y ∧ ∃ p : B.Walk v w, ∀ u ∈ p.support, u ≠ x ∧ u ≠ y) with hC
  have memC : ∀ w, w ∈ C ↔ w ≠ x ∧ w ≠ y ∧ ∃ p : B.Walk v w, ∀ u ∈ p.support, u ≠ x ∧ u ≠ y := by
    intro w; simp [hC]
  -- every vertex of a walk from `v` avoiding `x, y` lies in `C`
  have hpre : ∀ w (p : B.Walk v w), (∀ u ∈ p.support, u ≠ x ∧ u ≠ y) → ∀ u ∈ p.support, u ∈ C := by
    intro w p hp u hu
    refine (memC u).mpr ⟨(hp u hu).1, (hp u hu).2, p.takeUntil u hu, fun t ht => hp t ?_⟩
    exact p.support_takeUntil_subset_support hu ht
  by_cases hno : ∃ s ∈ S, s ∈ C
  · obtain ⟨s, hs, hsC⟩ := hno
    obtain ⟨h1, h2, p, hp⟩ := (memC s).mp hsC
    exact Or.inl ⟨s, hs, h1, h2, p, hp⟩
  push Not at hno
  right
  refine ⟨C, ⟨hxy, fun h => ((memC x).mp h).1 rfl, fun h => ((memC y).mp h).2.1 rfl,
    ⟨v, (memC v).mpr ⟨hvx, hvy, .nil, by simpa using ⟨hvx, hvy⟩⟩⟩, ?_, ?_, ?_⟩, hno⟩
  · intro a ha b hb
    obtain ⟨-, -, pa, hpa⟩ := (memC a).mp ha
    obtain ⟨-, -, pb, hpb⟩ := (memC b).mp hb
    refine ⟨pa.reverse.append pb, fun u hu => ?_⟩
    rw [Walk.support_append, List.mem_append] at hu
    rcases hu with hu | hu
    · rw [Walk.support_reverse, List.mem_reverse] at hu
      exact hpre a pa hpa u hu
    · exact hpre b pb hpb u (List.mem_of_mem_tail hu)
  · intro a ha b hab
    by_cases hbx : b = x
    · exact Or.inr (Or.inl hbx)
    by_cases hby : b = y
    · exact Or.inr (Or.inr hby)
    left
    obtain ⟨-, -, pa, hpa⟩ := (memC a).mp ha
    refine (memC b).mpr ⟨hbx, hby, pa.concat hab, fun u hu => ?_⟩
    rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hu
    rcases hu with hu | rfl
    · exact hpa u hu
    · exact ⟨hbx, hby⟩
  · obtain ⟨s, hs, hsxy⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {x, y}) (t := S)
      (by have := Finset.card_le_two (a := x) (b := y); omega)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hsxy
    exact ⟨s, hno s hs, hsxy.1, hsxy.2⟩

omit [Fintype V] [DecidableEq V] in
/-- `J − none` for the apex graph has a matching cut only if `B` does. -/
theorem not_hasMatchingCut_delVert_apex {B : SimpleGraph V} {S : Finset V}
    (hB : ¬ HasMatchingCut B) : ¬ HasMatchingCut (delVert (apex B S) none) := by
  rintro ⟨X, ⟨⟨w, hw⟩, hwX⟩, ⟨⟨w', hw'⟩, hw'X⟩, hm⟩
  let ι : V → {v : Option V | v ≠ none} := fun v => ⟨some v, Option.some_ne_none v⟩
  have hι : ∀ (w : Option V) (hw : w ∈ {v : Option V | v ≠ none}),
      ∃ v, (⟨w, hw⟩ : {v : Option V | v ≠ none}) = ι v := by
    intro w hw
    cases w with
    | none => exact absurd rfl hw
    | some v => exact ⟨v, rfl⟩
  apply hB
  refine ⟨{v | ι v ∈ X}, ?_, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hι w hw
    exact ⟨v, by rw [Set.mem_ofPred_eq, ← hv]; exact hwX⟩
  · obtain ⟨v, hv⟩ := hι w' hw'
    exact ⟨v, by rw [Set.mem_compl_iff, Set.mem_ofPred_eq, ← hv]; exact hw'X⟩
  · intro a b c hab hac hb hc
    have := hm (ι a) (ι b) (ι c) hab hac hb hc
    exact Option.some_injective _ (congrArg Subtype.val this)

/-- The vertex map `J − none → B` for the apex graph. -/
def unApex : {v : Option V | v ≠ none} → V := fun w => w.1.get (Option.ne_none_iff_isSome.mp w.2)

omit [Fintype V] [DecidableEq V] in
theorem unApex_injective : Function.Injective (unApex : {v : Option V | v ≠ none} → V) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ h
  cases a with
  | none => exact absurd rfl ha
  | some a =>
  cases b with
  | none => exact absurd rfl hb
  | some b =>
  simp only [unApex, Option.get_some] at h
  subst h; rfl

omit [Fintype V] in
/-- A decomposition of `(apex B S) − none` is a decomposition of `B`, with the same ends. -/
theorem decomp_of_delVert_apex {B : SimpleGraph V} {S : Finset V}
    (D : PathDecomp (delVert (apex B S) none)) :
    ∃ D' : PathDecomp B, D'.size ≤ D.size ∧
      ∀ v : V, D'.ends v = D.ends ⟨some v, Option.some_ne_none v⟩ := by
  obtain ⟨D', h1, h2⟩ := D.map_injective_ends unApex unApex_injective (by
    intro e'
    induction e' using Sym2.inductionOn with
    | hf a b =>
    constructor
    · intro hab
      exact ⟨s(⟨some a, Option.some_ne_none a⟩, ⟨some b, Option.some_ne_none b⟩), hab, rfl⟩
    · rintro ⟨e, he, hmap⟩
      induction e using Sym2.inductionOn with
      | hf c d =>
      obtain ⟨c, hc⟩ := c
      obtain ⟨d, hd⟩ := d
      cases c with
      | none => exact absurd rfl hc
      | some c =>
      cases d with
      | none => exact absurd rfl hd
      | some d =>
      simp only [Sym2.map_mk, unApex, Option.get_some] at hmap
      rw [← hmap]
      exact he)
  exact ⟨D', h1, fun v => h2 ⟨some v, Option.some_ne_none v⟩⟩

/-- **The core of Theorem 114's converse.** Let `B ∈ C`, and assume the marked bound for blocks of
order `≤ |B| − 2`, Lovász, the separator theorem, and the two deletion tests (restricted to `J − z`
without a matching cut). Then `B` passes the rooted test at every `r`.

Proof: with `S = {even vertices} ∪ {r}`: if `|S| ≤ 2`, Lovász. If some component behind a
separating pair avoids `r` and has only odd vertices, Theorem 113. Otherwise every such component
meets `S`, so `J = B + z(S)` is three-connected; its only even vertices are `z` (even order) or
`z, r` (odd order), and the deletion test on `J − z = B` is the rooted test. -/
theorem rootedAt_of_tests (hL : LovaszStatement.{u}) (hsep : SeparatorStatement.{u})
    (hT : SpineTestsNMC.{u}) (B : SimpleGraph V) [DecidableRel B.Adj] (hC : InClassC B)
    (hMB : MarkedBoundUpTo.{u} (Fintype.card V - 2)) (r : V) : RootedAt B r := by
  set S := Finset.univ.filter (fun v => Even (B.degree v) ∨ v = r) with hSdef
  have memS : ∀ v, v ∈ S ↔ Even (B.degree v) ∨ v = r := by intro v; simp [hSdef]
  by_cases hfew : S.card ≤ 2
  · exact rootedAt_of_few_even hL B hC.1 r hfew
  push Not at hfew
  by_cases hsc : ∃ x y C, IsSepComponent B x y C ∧ r ∉ C ∧ ∀ c ∈ C, Odd (B.degree c)
  · obtain ⟨x, y, C, h1, h2, h3⟩ := hsc
    exact hsep V B hMB hC.1 x y C h1 r h2 h3
  push Not at hsc
  -- every component of `B − {x, y}` meets `S`
  have hcomp : ∀ x y, x ≠ y → ∀ v, v ≠ x → v ≠ y →
      ∃ s ∈ S, s ≠ x ∧ s ≠ y ∧ ∃ p : B.Walk v s, ∀ w ∈ p.support, w ≠ x ∧ w ≠ y := by
    intro x y hxy v hvx hvy
    rcases exists_sepComponent_or (B := B) (by omega : 3 ≤ S.card) hxy hvx hvy with h | ⟨C, hC', hSC⟩
    · exact h
    · exfalso
      obtain ⟨c, hcC, hc⟩ := hsc x y C hC' (hSC r ((memS r).mpr (Or.inr rfl)))
      exact hSC c ((memS c).mpr (Or.inl hc)) hcC
  have hJ : KConnected 3 (apex B S) := apex_kConnected_three hC.1 (by omega) hcomp
  have hnmc := not_hasMatchingCut_delVert_apex (S := S) hC.2
  obtain ⟨t1, t2⟩ := hT (Option V) (apex B S) none hJ hnmc
  have hzr : (apex B S).Adj none (some r) := (memS r).mpr (Or.inr rfl)
  -- the parity of `|S|`
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun v => Even (B.degree v) ∨ v = r)
  have hhand := B.even_card_odd_degree_vertices
  rw [Finset.card_univ, ← hSdef] at hsplit
  have hdeg_some := fun v => apex_degree_some (G := B) (T := S) v
  have h3 := hC.1.le_degree r
  constructor
  · intro hn hr
    have hneg : Finset.univ.filter (fun v => ¬ (Even (B.degree v) ∨ v = r)) =
        Finset.univ.filter (fun v => Odd (B.degree v)) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or, ← Nat.not_even_iff_odd]
      constructor
      · exact fun h => h.1
      · rintro h; exact ⟨h, by rintro rfl; exact h hr⟩
    rw [hneg] at hsplit
    have hSev : Even S.card := by
      obtain ⟨a, ha⟩ := hn; obtain ⟨b, hb⟩ := hhand
      exact ⟨a - b, by omega⟩
    have hev : ∀ w, Even ((apex B S).degree w) ↔ w = none := by
      intro w
      cases w with
      | none => simpa [apex_degree_none] using hSev
      | some v =>
        rw [hdeg_some v]
        simp only [reduceCtorEq, iff_false]
        by_cases hv : Even (B.degree v)
        · simp only [(memS v).mpr (Or.inl hv), ite_true, Nat.even_add_one]
          exact not_not.mpr hv
        · have hvr : v ≠ r := by rintro rfl; exact hv hr
          have hvS : v ∉ S := by rw [memS]; tauto
          simp only [hvS, ite_false, add_zero]; exact hv
    obtain ⟨D, hD1, hD2⟩ := t1 hev (some r) hzr
    obtain ⟨D', h1, h2⟩ := decomp_of_delVert_apex D
    refine ⟨D', ?_, by rw [h2 r]; exact hD2⟩
    rw [Fintype.card_option] at hD1
    simpa using h1.trans hD1
  · intro hn hr
    have hneg : Finset.univ.filter (fun v => ¬ (Even (B.degree v) ∨ v = r)) =
        (Finset.univ.filter (fun v => Odd (B.degree v))).erase r := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or, ← Nat.not_even_iff_odd,
        Finset.mem_erase]
      tauto
    have hrodd : r ∈ Finset.univ.filter (fun v => Odd (B.degree v)) := by simpa using hr
    rw [hneg, Finset.card_erase_of_mem hrodd] at hsplit
    have hpos : 1 ≤ (Finset.univ.filter (fun v => Odd (B.degree v))).card :=
      Finset.card_pos.mpr ⟨r, hrodd⟩
    have hSev : Even S.card := by
      obtain ⟨a, ha⟩ := hn; obtain ⟨b, hb⟩ := hhand
      exact ⟨a - b + 1, by omega⟩
    have hev : ∀ w, Even ((apex B S).degree w) ↔ w = none ∨ w = some r := by
      intro w
      cases w with
      | none => simpa [apex_degree_none] using hSev
      | some v =>
        rw [hdeg_some v]
        simp only [reduceCtorEq, false_or, Option.some.injEq]
        by_cases hvr : v = r
        · subst hvr
          simp only [(memS v).mpr (Or.inr rfl), ite_true, Nat.even_add_one, Nat.not_even_iff_odd]
          simpa using hr
        · by_cases hv : Even (B.degree v)
          · simp only [(memS v).mpr (Or.inl hv), ite_true, Nat.even_add_one]
            simpa [hvr] using hv
          · have hvS : v ∉ S := by rw [memS]; tauto
            simp only [hvS, ite_false, add_zero]
            simpa [hvr] using hv
    obtain ⟨D, hD1, hD2⟩ := t2 (some r) hzr hev
    obtain ⟨D', h1, h2⟩ := decomp_of_delVert_apex D
    refine ⟨D', ?_, by rw [h2 r]; exact hD2⟩
    rw [Fintype.card_option] at hD1
    have : (Fintype.card V + 1) / 2 = Fintype.card V / 2 + 1 := by
      obtain ⟨a, ha⟩ := hn; omega
    omega

/-- **Theorem 114, converse direction** (modulo Lovász, Theorem 59 and Theorem 113, all explicit
hypotheses): the two deletion tests on three-connected graphs, even restricted to `J − z` without a
matching cut, imply Gallai's conjecture. Every member of `C` passes both rooted tests, by strong
induction on the order (Theorem 59 turns the tests below order `n` into the marked bound for
blocks of order `≤ n − 2`); Theorem 59 then gives the marked bound everywhere, and a single mark
gives Gallai. -/
theorem gallai_of_spineTestsNMC (hL : LovaszStatement.{u}) (h59 : Thm59Statement.{u})
    (hsep : SeparatorStatement.{u}) (hT : SpineTestsNMC.{u}) : GallaiConjecture.{u} := by
  have key : ∀ n, ∀ (V : Type u) [Fintype V] [DecidableEq V] (B : SimpleGraph V)
      [DecidableRel B.Adj], Fintype.card V = n → InClassC B → ∀ r, RootedAt B r := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro V _ _ B _ hn hC r
    have h3 := hC.1.1
    have hMB : MarkedBoundUpTo.{u} (Fintype.card V - 2) :=
      h59 _ (fun W _ _ B' _ hC' hcard x => ih _ (by omega) W B' rfl hC' x)
    exact rootedAt_of_tests hL hsep hT B hC hMB r
  intro W _ G hG
  classical
  have hMB := h59 (Fintype.card W) (fun W' _ _ B _ hC _ x => key _ W' B rfl hC x)
  obtain ⟨r⟩ := hG.nonempty
  have h1 := hMB W G hG (smallBlocks_card G) {r} (Finset.singleton_nonempty r)
  have h2 := pathNumber_le_markedNumber_add G {r}
  have h3 : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨r⟩
  rw [Finset.card_singleton] at h1 h2
  omega

end converse

end Gallai
