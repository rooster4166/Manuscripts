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

end Gallai
