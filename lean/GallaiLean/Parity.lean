import GallaiLean.Basic

/-!
# Parity of path ends, and existence of path decompositions

* `GPath.countP_add_endsAt`: for a path `P` and a vertex `v`,
  `#(edges of P at v) + endsAt P v = 2 * [v ∈ P]`; hence the number of edges of `P` at `v` is
  `2` at an internal vertex, `1` at an end and `0` off the path
  (`GPath.countP_of_internal`, `GPath.countP_of_end`, `GPath.countP_of_not_mem`).
* `PathDecomp.degree_eq_sum`: `deg v = ∑_{P ∈ D} #(edges of P at v)`.
* `PathDecomp.ends_mod_two`: `ends D v ≡ deg v (mod 2)`.
* `PathDecomp.sum_ends`: `∑_v ends D v = 2 |D|`.
* `PathDecomp.card_odd_le`: `#{v | deg v odd} ≤ 2 |D|`.
* `PathDecomp.singleEdges`, `PathDecomp.nonempty`: every finite graph has a path decomposition.
* `pathNumber_spec`, `pathNumber_le`: `pathNumber` is attained and is a lower bound.
* `card_odd_le_two_mul_pathNumber`: `#{v | deg v odd} ≤ 2 p(G)`.
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u} {G : SimpleGraph V}

/-! ### Incidence counts along a single path -/

/-- On a path, `#(edges at v) + #(ends at v) = 2 * [v on the path]`. -/
theorem Walk.countP_add_ends [DecidableEq V] {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (v : V) :
    p.edges.countP (fun e => v ∈ e) + ((if a = v then 1 else 0) + (if b = v then 1 else 0)) =
      2 * (if v ∈ p.support then 1 else 0) := by
  induction p with
  | @nil x =>
    by_cases h : x = v
    · subst h; simp
    · simp [h, Ne.symm h]
  | @cons a c b h p ih =>
    rw [Walk.cons_isPath_iff] at hp
    have ih := ih hp.1
    have hac : a ≠ c := h.ne
    have hap : a ∉ p.support := hp.2
    simp only [Walk.edges_cons, List.countP_cons, Walk.support_cons, List.mem_cons,
      Sym2.mem_iff] at ih ⊢
    by_cases hva : v = a
    · subst hva
      have hcv : c ≠ v := fun h => hac h.symm
      simp only [hcv, hap, ite_false] at ih
      simp only [hap, true_or, decide_true, ite_true, or_false]
      split_ifs at ih ⊢; omega
    · by_cases hvc : v = c
      · subst hvc
        have : v ∈ p.support := p.start_mem_support
        simp only [this, ite_true] at ih
        simp only [Ne.symm hva, hva, this, or_true, decide_true, ite_true, ite_false]
        split_ifs at ih ⊢ <;> omega
      · simp only [Ne.symm hvc, ite_false] at ih
        simp only [Ne.symm hva, hva, hvc, or_self, decide_false, Bool.false_eq_true, ite_false, false_or]
        split_ifs at ih ⊢ <;> omega

/-- On any walk, `#(edges at v) + #(ends at v)` is even (no simplicity needed). -/
theorem Walk.even_countP_add_ends [DecidableEq V] {a b : V} (p : G.Walk a b) (v : V) :
    Even (p.edges.countP (fun e => v ∈ e) +
      ((if a = v then 1 else 0) + (if b = v then 1 else 0))) := by
  induction p with
  | @nil x => by_cases h : x = v <;> simp [h]
  | @cons a c b h p ih =>
    have hac : a ≠ c := h.ne
    simp only [Walk.edges_cons, List.countP_cons, Sym2.mem_iff] at ih ⊢
    obtain ⟨k, hk⟩ := ih
    by_cases hva : v = a
    · subst hva
      have hcv : c ≠ v := fun h => hac h.symm
      simp only [hcv, ite_false] at hk
      refine ⟨k + 1, ?_⟩
      simp only [true_or, decide_true, ite_true]
      split_ifs at hk ⊢ <;> omega
    · by_cases hvc : v = c
      · subst hvc
        refine ⟨k, ?_⟩
        simp only [hva, or_true, decide_true, Ne.symm hva, ite_true, ite_false] at hk ⊢
        split_ifs at hk ⊢ <;> omega
      · refine ⟨k, ?_⟩
        simp only [hva, hvc, or_self, decide_false, Bool.false_eq_true, Ne.symm hva, Ne.symm hvc, ite_false] at hk ⊢
        split_ifs at hk ⊢ <;> omega

namespace GPath

/-- Number of edges of `P` incident to `v`. -/
def incid [DecidableEq V] (P : GPath G) (v : V) : ℕ := P.edges.countP (fun e => v ∈ e)

theorem src_ne_tgt (P : GPath G) : P.src ≠ P.tgt := by
  obtain ⟨s, t, w, hw, hpos⟩ := P
  rintro (rfl : s = t)
  have := Walk.length_eq_zero_iff.mpr (Walk.isPath_iff_nil.mp hw)
  omega

theorem incid_add_endsAt [DecidableEq V] (P : GPath G) (v : V) :
    P.incid v + P.endsAt v = 2 * (if v ∈ P.walk.support then 1 else 0) :=
  Walk.countP_add_ends P.walk P.isPath v

theorem even_incid_add_endsAt [DecidableEq V] (P : GPath G) (v : V) :
    Even (P.incid v + P.endsAt v) :=
  Walk.even_countP_add_ends P.walk v

/-- At an internal vertex a path has exactly two edges. -/
theorem incid_of_internal [DecidableEq V] (P : GPath G) {v : V} (hv : v ∈ P.walk.support)
    (hs : P.src ≠ v) (ht : P.tgt ≠ v) : P.incid v = 2 := by
  have := P.incid_add_endsAt v
  simp only [endsAt, hs, ht, ite_false, hv, ite_true] at this
  omega

/-- At an end a path has exactly one edge. -/
theorem incid_of_end [DecidableEq V] (P : GPath G) {v : V} (hv : P.src = v ∨ P.tgt = v) :
    P.incid v = 1 := by
  have h1 := P.incid_add_endsAt v
  have hne := P.src_ne_tgt
  have hmem : v ∈ P.walk.support := by
    rcases hv with rfl | rfl
    · exact P.walk.start_mem_support
    · exact P.walk.end_mem_support
  simp only [endsAt, hmem, ite_true] at h1
  rcases hv with rfl | rfl
  · simp only [ite_true, hne.symm, ite_false] at h1
    omega
  · simp only [ite_true, hne, ite_false] at h1
    omega

/-- Off the path there are no edges of the path. -/
theorem incid_of_not_mem [DecidableEq V] (P : GPath G) {v : V} (hv : v ∉ P.walk.support) :
    P.incid v = 0 := by
  have := P.incid_add_endsAt v
  simp only [hv, ite_false] at this
  omega

theorem sum_endsAt [Fintype V] [DecidableEq V] (P : GPath G) : ∑ v, P.endsAt v = 2 := by
  simp [endsAt, Finset.sum_add_distrib]

theorem length_edges (P : GPath G) : P.edges.length = P.walk.length := P.walk.length_edges

theorem edges_ne_nil (P : GPath G) : P.edges ≠ [] := by
  intro h
  have := P.length_edges
  rw [h] at this
  exact P.pos.ne' this.symm

end GPath

/-! ### Degrees and ends of a decomposition -/

namespace PathDecomp

theorem mem_flatMap_iff (D : PathDecomp G) (e : Sym2 V) :
    e ∈ D.paths.flatMap GPath.edges ↔ e ∈ G.edgeSet := (D.covers e).symm

/-- `deg v = ∑_{P ∈ D} #(edges of P at v)`, for any locally finite vertex. -/
theorem degree_eq_sum [DecidableEq V] (D : PathDecomp G) (v : V) [Fintype (G.neighborSet v)] :
    G.degree v = (D.paths.map (fun P => P.incid v)).sum := by
  set L := D.paths.flatMap GPath.edges with hL
  have hset : G.incidenceSet v = ((L.filter (fun e => v ∈ e)).toFinset : Set (Sym2 V)) := by
    ext e
    simp only [incidenceSet, Set.mem_ofPred_eq, List.coe_toFinset, List.mem_filter,
      decide_eq_true_eq, D.covers e, hL]
  rw [← G.ncard_incidenceSet v, hset, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (D.nodup_edges.filter _), ← List.countP_eq_length_filter,
    List.countP_flatMap]
  rfl

theorem ends_add_degree_even [DecidableEq V] (D : PathDecomp G) (v : V)
    [Fintype (G.neighborSet v)] : Even (D.ends v + G.degree v) := by
  rw [D.degree_eq_sum v, ends]
  generalize D.paths = l
  induction l with
  | nil => simp
  | cons P l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := P.even_incid_add_endsAt v
    have h : P.endsAt v + (l.map fun P => P.endsAt v).sum +
        (P.incid v + (l.map fun P => P.incid v).sum) =
        (P.incid v + P.endsAt v) +
          ((l.map fun P => P.endsAt v).sum + (l.map fun P => P.incid v).sum) := by ring
    rw [h]
    exact this.add ih

/-- **Parity lemma**: the number of path ends at `v` has the parity of `deg v`. -/
theorem ends_mod_two [DecidableEq V] (D : PathDecomp G) (v : V) [Fintype (G.neighborSet v)] :
    D.ends v % 2 = G.degree v % 2 := by
  obtain ⟨k, hk⟩ := D.ends_add_degree_even v
  omega

/-- Each path has two ends: `∑_v ends D v = 2 |D|`. -/
theorem sum_ends [Fintype V] [DecidableEq V] (D : PathDecomp G) :
    ∑ v, D.ends v = 2 * D.size := by
  rw [size]
  unfold ends
  generalize D.paths = l
  induction l with
  | nil => simp
  | cons P l ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih, P.sum_endsAt,
      List.length_cons]
    ring

/-- The number of odd-degree vertices is at most twice the size of any path decomposition. -/
theorem card_odd_le [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (D : PathDecomp G) :
    (Finset.univ.filter (fun v => Odd (G.degree v))).card ≤ 2 * D.size := by
  rw [← D.sum_ends]
  calc (Finset.univ.filter (fun v => Odd (G.degree v))).card
      = (Finset.univ.filter (fun v => Odd (G.degree v))).card • 1 := by simp
    _ ≤ ∑ v ∈ Finset.univ.filter (fun v => Odd (G.degree v)), D.ends v := by
        apply Finset.card_nsmul_le_sum
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        have h1 := D.ends_mod_two v
        rw [Nat.odd_iff] at hv
        omega
    _ ≤ ∑ v, D.ends v := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end PathDecomp

/-! ### Existence of decompositions; `pathNumber` is attained -/

namespace GPath

/-- The one-edge path `a — b`. -/
def ofAdj {a b : V} (h : G.Adj a b) : GPath G where
  src := a
  tgt := b
  walk := Walk.cons h Walk.nil
  isPath := by simp [h.ne]
  pos := by simp

@[simp] theorem ofAdj_edges {a b : V} (h : G.Adj a b) : (ofAdj h).edges = [s(a, b)] := rfl

/-- The one-edge path along an edge `e` (endpoints chosen by `Quot.out`). -/
noncomputable def ofEdge (e : Sym2 V) (he : e ∈ G.edgeSet) : GPath G :=
  ofAdj (G := G) (a := (Quot.out e).1) (b := (Quot.out e).2) (by
    have : s((Quot.out e).1, (Quot.out e).2) = e := Quot.out_eq e
    rw [← this] at he
    exact he)

@[simp] theorem ofEdge_edges (e : Sym2 V) (he : e ∈ G.edgeSet) : (ofEdge e he).edges = [e] := by
  show [s((Quot.out e).1, (Quot.out e).2)] = [e]
  rw [show s((Quot.out e).1, (Quot.out e).2) = e from Quot.out_eq e]

end GPath

namespace PathDecomp

/-- The decomposition into single edges, from a duplicate-free list of all edges. -/
noncomputable def ofEdgeList (l : List (Sym2 V)) (hnd : l.Nodup)
    (hl : ∀ e, e ∈ G.edgeSet ↔ e ∈ l) : PathDecomp G where
  paths := l.attach.map (fun e => GPath.ofEdge e.1 ((hl e.1).2 e.2))
  nodup_edges := by
    have : (l.attach.map (fun e => GPath.ofEdge e.1 ((hl e.1).2 e.2))).flatMap GPath.edges = l := by
      simp [List.flatMap_map]
    rw [this]; exact hnd
  covers := by
    have : (l.attach.map (fun e => GPath.ofEdge e.1 ((hl e.1).2 e.2))).flatMap GPath.edges = l := by
      simp [List.flatMap_map]
    rw [this]; exact hl

theorem ofEdgeList_size (l : List (Sym2 V)) (hnd : l.Nodup)
    (hl : ∀ e, e ∈ G.edgeSet ↔ e ∈ l) : (ofEdgeList l hnd hl).size = l.length := by
  simp [ofEdgeList, size]

/-- The decomposition of a graph with finitely many edges into its single edges. -/
noncomputable def singleEdges [Fintype G.edgeSet] : PathDecomp G :=
  ofEdgeList G.edgeFinset.toList (Finset.nodup_toList _) (by simp)

theorem singleEdges_size [Fintype G.edgeSet] : (singleEdges (G := G)).size = G.edgeFinset.card := by
  simp [singleEdges, ofEdgeList_size]

/-- Every graph on a finite vertex type has a path decomposition. -/
theorem nonempty [Finite V] (G : SimpleGraph V) : Nonempty (PathDecomp G) := by
  classical
  have : Fintype V := Fintype.ofFinite V
  exact ⟨singleEdges⟩

end PathDecomp

/-- `pathNumber G` is a lower bound for the size of every path decomposition. -/
theorem pathNumber_le (D : PathDecomp G) : pathNumber G ≤ D.size :=
  Nat.sInf_le ⟨D, rfl⟩

/-- On a finite vertex type, `pathNumber G` is attained by some decomposition. -/
theorem pathNumber_spec [Finite V] (G : SimpleGraph V) :
    ∃ D : PathDecomp G, D.size = pathNumber G := by
  obtain ⟨D⟩ := PathDecomp.nonempty G
  exact Nat.sInf_mem (s := {k | ∃ D : PathDecomp G, D.size = k}) ⟨D.size, D, rfl⟩

/-- To bound `pathNumber G` from below it suffices to bound every decomposition. -/
theorem le_pathNumber [Finite V] {k : ℕ} (h : ∀ D : PathDecomp G, k ≤ D.size) :
    k ≤ pathNumber G := by
  obtain ⟨D, hD⟩ := pathNumber_spec G
  exact hD ▸ h D

/-- **Corollary of the parity lemma**: `#{v | deg v odd} ≤ 2 p(G)`. -/
theorem card_odd_le_two_mul_pathNumber [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    (Finset.univ.filter (fun v => Odd (G.degree v))).card ≤ 2 * pathNumber G := by
  obtain ⟨D, hD⟩ := pathNumber_spec G
  rw [← hD]
  exact D.card_odd_le

end Gallai
