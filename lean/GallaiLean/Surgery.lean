import GallaiLean.Project

/-!
# Surgery on path decompositions

* `PathDecomp.split_at`: split a path at an internal vertex `x`.
* `PathDecomp.exists_split`: the result has one more path and two more ends at `x`, and is
  otherwise unchanged (`ends v` is unchanged for `v ≠ x`).
* `PathDecomp.exists_split_of_ends_eq_zero`: a vertex of positive degree with no ends is interior
  to some path, so it can be split.
* `PathDecomp.exists_split_set`: split at every vertex of a finite set of such vertices.
* `PathDecomp.exists_split_all`: split until `z` is an end of every path through it.
* `PathDecomp.ends_eq_of_tight`: if `2|D| ≤ #odd`, then `D` has exactly one end at each odd
  vertex and none at each even vertex.
* `PathDecomp.sum_count_le_one`: each edge lies on exactly one path.
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem sum_map_le_sum_map {α : Type*} (l : List α) (f g : α → ℕ) (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a List.mem_cons_self) (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem sum_map_add' {α : Type*} (l : List α) (f g : α → ℕ) :
    (l.map (fun a => f a + g a)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

namespace PathDecomp

theorem ends_append_cons [DecidableEq V] (l₁ l₂ : List (GPath G)) (Q : GPath G) (v : V) :
    ((l₁ ++ Q :: l₂).map (fun P => P.endsAt v)).sum =
      (l₁.map (fun P => P.endsAt v)).sum + Q.endsAt v + (l₂.map (fun P => P.endsAt v)).sum := by
  simp [List.sum_append, add_assoc]

/-- Each edge lies on at most one path of a decomposition. -/
theorem sum_count_le_one [DecidableEq V] (D : PathDecomp G) (e : Sym2 V) :
    (D.paths.map (fun P => P.edges.count e)).sum ≤ 1 := by
  have : (D.paths.map (fun P => P.edges.count e)).sum = (D.paths.flatMap GPath.edges).count e := by
    rw [List.count_flatMap]; rfl
  rw [this]
  exact List.nodup_iff_count_le_one.mp D.nodup_edges e

/-- Split a path of `D` at an internal vertex `x`. -/
theorem split_at (D : PathDecomp G) {Q : GPath G} (hQ : Q ∈ D.paths) {x : V}
    (hx : x ∈ Q.walk.support) (hs : Q.src ≠ x) (ht : Q.tgt ≠ x) :
    ∃ (D' : PathDecomp G) (l₁ l₂ : List (GPath G)) (Q₁ Q₂ : GPath G),
      D.paths = l₁ ++ Q :: l₂ ∧ D'.paths = l₁ ++ Q₁ :: Q₂ :: l₂ ∧
      Q₁.src = Q.src ∧ Q₁.tgt = x ∧ Q₂.src = x ∧ Q₂.tgt = Q.tgt := by
  obtain ⟨q₁, q₂, hq⟩ := Walk.mem_support_iff_exists_append.mp hx
  have hpath : (q₁.append q₂).IsPath := hq ▸ Q.isPath
  have h₁ : 0 < q₁.length := by
    by_contra hc
    exact hs (Walk.eq_of_length_eq_zero (p := q₁) (by omega))
  have h₂ : 0 < q₂.length := by
    by_contra hc
    exact ht (Walk.eq_of_length_eq_zero (p := q₂) (by omega)).symm
  let Q₁ : GPath G := ⟨_, _, q₁, Walk.isPath_of_append_left hpath, h₁⟩
  let Q₂ : GPath G := ⟨_, _, q₂, Walk.isPath_of_append_right hpath, h₂⟩
  obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hQ
  have hperm : ((l₁ ++ Q₁ :: Q₂ :: l₂).flatMap GPath.edges).Perm (D.paths.flatMap GPath.edges) := by
    have : Q.edges = Q₁.edges ++ Q₂.edges := by
      show Q.walk.edges = q₁.edges ++ q₂.edges
      rw [hq, Walk.edges_append]
    simp only [hl, List.flatMap_append, List.flatMap_cons, this, List.append_assoc]
    exact List.Perm.refl _
  exact ⟨PathDecomp.ofPerm _ _ hperm D.nodup_edges D.covers, l₁, l₂, Q₁, Q₂, hl, rfl,
    rfl, rfl, rfl, rfl⟩

/-- Splitting at an internal vertex `x`: one more path, two more ends at `x`, nothing else
changes. -/
theorem exists_split [DecidableEq V] (D : PathDecomp G) {Q : GPath G} (hQ : Q ∈ D.paths) {x : V}
    (hx : x ∈ Q.walk.support) (hs : Q.src ≠ x) (ht : Q.tgt ≠ x) :
    ∃ D' : PathDecomp G, D'.size = D.size + 1 ∧
      ∀ v, D'.ends v = D.ends v + if x = v then 2 else 0 := by
  obtain ⟨D', l₁, l₂, Q₁, Q₂, hl, hl', h1s, h1t, h2s, h2t⟩ := D.split_at hQ hx hs ht
  refine ⟨D', ?_, ?_⟩
  · simp only [size, hl, hl', List.length_append, List.length_cons]
    omega
  · intro v
    unfold ends
    rw [hl, hl']
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, GPath.endsAt,
      h1s, h1t, h2s, h2t]
    split_ifs <;> omega

/-- A vertex of positive degree without ends is interior to some path. -/
theorem exists_internal [DecidableEq V] (D : PathDecomp G) {x : V} [Fintype (G.neighborSet x)]
    (hx : 0 < G.degree x) (h0 : D.ends x = 0) :
    ∃ Q ∈ D.paths, x ∈ Q.walk.support ∧ Q.src ≠ x ∧ Q.tgt ≠ x := by
  obtain ⟨y, hy⟩ := (G.degree_pos_iff_exists_adj x).mp hx
  obtain ⟨Q, hQ, hxyQ⟩ := List.mem_flatMap.mp ((D.covers _).1 (G.mem_edgeSet.mpr hy))
  have hQ0 : Q.endsAt x = 0 := by
    unfold ends at h0
    exact List.sum_eq_zero_iff_forall_eq_nat.mp h0 _ (List.mem_map_of_mem hQ)
  unfold GPath.endsAt at hQ0
  refine ⟨Q, hQ, Q.walk.fst_mem_support_of_mem_edges hxyQ, ?_, ?_⟩
  · intro hs; simp [hs] at hQ0
  · intro ht; simp [ht] at hQ0

theorem exists_split_of_ends_eq_zero [DecidableEq V] (D : PathDecomp G) {x : V}
    [Fintype (G.neighborSet x)] (hx : 0 < G.degree x) (h0 : D.ends x = 0) :
    ∃ D' : PathDecomp G, D'.size = D.size + 1 ∧
      ∀ v, D'.ends v = D.ends v + if x = v then 2 else 0 := by
  obtain ⟨Q, hQ, hxQ, hs, ht⟩ := D.exists_internal hx h0
  exact D.exists_split hQ hxQ hs ht

/-- Split at every vertex of a finite set of positive-degree vertices without ends. -/
theorem exists_split_set [DecidableEq V] [∀ v, Fintype (G.neighborSet v)] (D : PathDecomp G)
    (Z : Finset V) (hZ : ∀ z ∈ Z, 0 < G.degree z ∧ D.ends z = 0) :
    ∃ D' : PathDecomp G, D'.size = D.size + Z.card ∧
      ∀ v, D'.ends v = D.ends v + if v ∈ Z then 2 else 0 := by
  induction Z using Finset.induction_on with
  | empty => exact ⟨D, by simp, by simp⟩
  | @insert a Z ha ih =>
    obtain ⟨D₁, hs₁, he₁⟩ := ih (fun z hz => hZ z (Finset.mem_insert_of_mem hz))
    have ha0 : D₁.ends a = 0 := by
      rw [he₁]
      simp only [ha, ite_false, add_zero]
      exact (hZ a (Finset.mem_insert_self a Z)).2
    obtain ⟨D₂, hs₂, he₂⟩ :=
      D₁.exists_split_of_ends_eq_zero (hZ a (Finset.mem_insert_self a Z)).1 ha0
    refine ⟨D₂, by rw [hs₂, hs₁, Finset.card_insert_of_notMem ha]; ring, fun v => ?_⟩
    rw [he₂, he₁]
    by_cases hv : v = a
    · subst hv; simp [ha]
    · simp [hv, Ne.symm hv, Finset.mem_insert]

/-- Split until `z` is an end of every path through it; end counts away from `z` are
unchanged. -/
theorem exists_split_all [DecidableEq V] (D : PathDecomp G) (z : V) :
    ∃ D' : PathDecomp G, (∀ v, v ≠ z → D'.ends v = D.ends v) ∧
      ∀ P ∈ D'.paths, z ∈ P.walk.support → P.src = z ∨ P.tgt = z := by
  let p : GPath G → Bool := fun P => decide (z ∈ P.walk.support ∧ P.src ≠ z ∧ P.tgt ≠ z)
  suffices h : ∀ n, ∀ D : PathDecomp G, D.paths.countP p = n →
      ∃ D' : PathDecomp G, (∀ v, v ≠ z → D'.ends v = D.ends v) ∧
        ∀ P ∈ D'.paths, z ∈ P.walk.support → P.src = z ∨ P.tgt = z from h _ D rfl
  intro n
  induction n with
  | zero =>
    intro D hD
    refine ⟨D, fun _ _ => rfl, fun P hP hz => ?_⟩
    have := List.countP_eq_zero.mp hD P hP
    simp only [p, decide_eq_true_eq, not_and, ne_eq, not_not] at this
    by_contra hc
    rw [not_or] at hc
    exact hc.2 (this hz hc.1)
  | succ n ih =>
    intro D hD
    obtain ⟨Q, hQ, hpQ⟩ := List.countP_pos_iff.mp (by omega : 0 < D.paths.countP p)
    simp only [p, decide_eq_true_eq] at hpQ
    obtain ⟨D₁, l₁, l₂, Q₁, Q₂, hl, hl', h1s, h1t, h2s, h2t⟩ :=
      D.split_at hQ hpQ.1 hpQ.2.1 hpQ.2.2
    have hc : D₁.paths.countP p = n := by
      have hQp : p Q = true := by simp [p, hpQ]
      have h1 : p Q₁ = false := by simp [p, h1t]
      have h2 : p Q₂ = false := by simp [p, h2s]
      rw [hl] at hD
      rw [hl']
      simp only [List.countP_append, List.countP_cons, hQp, h1, h2] at hD ⊢
      simp only [ite_true, Bool.false_eq_true, ite_false] at hD ⊢
      omega
    obtain ⟨D₂, he₂, hz₂⟩ := ih D₁ hc
    refine ⟨D₂, fun v hv => ?_, hz₂⟩
    rw [he₂ v hv]
    unfold ends
    rw [hl, hl']
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, GPath.endsAt,
      h1s, h1t, h2s, h2t, Ne.symm hv, ite_false]
    omega

/-- **Tightness**: a decomposition with at most `#odd / 2` paths has exactly one end at every
odd vertex and none at every even vertex. -/
theorem ends_eq_of_tight [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (D : PathDecomp G)
    (h : 2 * D.size ≤ (Finset.univ.filter (fun v => Odd (G.degree v))).card) :
    ∀ v, D.ends v = if Odd (G.degree v) then 1 else 0 := by
  have hle : ∀ v ∈ (Finset.univ : Finset V), (if Odd (G.degree v) then 1 else 0) ≤ D.ends v := by
    intro v _
    have := D.ends_mod_two v
    split_ifs with ho
    · rw [Nat.odd_iff] at ho; omega
    · exact Nat.zero_le _
  have hsum : ∑ v, D.ends v = ∑ v, (if Odd (G.degree v) then 1 else 0) := by
    apply le_antisymm
    · rw [D.sum_ends, ← Finset.card_filter]; exact h
    · exact Finset.sum_le_sum hle
  have := (Finset.sum_eq_sum_iff_of_le hle).mp hsum.symm
  intro v
  exact (this v (Finset.mem_univ v)).symm

end PathDecomp

end Gallai
