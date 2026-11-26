import GallaiLean.Fan

/-!
# Insertion bookkeeping: decompositions as (edge set, end vector) pairs

The six-clique construction never looks inside a decomposition: it only tracks which edges are
present and how many path ends sit at each vertex. This file packages exactly that information.

* `Ach E b`: the graph `fromEdgeSet E` has a path decomposition with `b v` ends at every `v`.
* `blankNbrs E b u`: the number of *blank* neighbours of `u` (neighbours with no end).
* `mv b t u`: the end vector after moving one end from `t` to `u`.
* **`Ach.grouped`** (Fan's grouped transfer, `fan_grouped`): if the receiver `u` has fewer blank
  neighbours than the total number of ends at a set `T` of non-neighbours, then some `t ∈ T` with
  `b t ≥ 1` gives `Ach (E ∪ {tu}) (mv b t u)`.
* `Ach.transfer`: the single-donor case.
* `lEdges a l`, `lastOf a l`: the consecutive edges and the last vertex of the list `a :: l`;
  `mem_lEdges_iff`: an edge lies on the list iff it joins two consecutive entries.
* **`Ach.addPath`**: a new path, given by a duplicate-free vertex list whose edges are all new,
  can be added as an extra row; it adds one end at each of its two ends.
* `Ach.empty`: the empty graph has the empty decomposition.

Only the end vector is tracked; the number of paths is recovered at the end from
`PathDecomp.sum_ends` (`∑ ends = 2 · size`).
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u} [DecidableEq V]

/-- `Ach E b`: the graph with edge set `E` (diagonal entries ignored) has a path decomposition
with exactly `b v` path ends at every vertex `v`. -/
def Ach (E : Set (Sym2 V)) (b : V → ℕ) : Prop :=
  ∃ D : PathDecomp (fromEdgeSet E), ∀ v, D.ends v = b v

/-- The number of blank neighbours of `u`: vertices `w ≠ u` with `s(u, w) ∈ E` and `b w = 0`. -/
noncomputable def blankNbrs (E : Set (Sym2 V)) (b : V → ℕ) (u : V) : ℕ :=
  {w | s(u, w) ∈ E ∧ w ≠ u ∧ b w = 0}.ncard

/-- Move one end from `t` to `u`. -/
def mv {W : Type*} [DecidableEq W] (b : W → ℕ) (t u : W) (w : W) : ℕ :=
  if w = u then b w + 1 else if w = t then b w - 1 else b w

theorem mv_apply_recv {W : Type*} [DecidableEq W] (b : W → ℕ) (t u : W) :
    mv b t u u = b u + 1 := by simp [mv]

theorem mv_apply_donor {W : Type*} [DecidableEq W] (b : W → ℕ) {t u : W} (h : t ≠ u) :
    mv b t u t = b t - 1 := by simp [mv, h]

theorem mv_apply_other {W : Type*} [DecidableEq W] (b : W → ℕ) {t u w : W} (ht : w ≠ t)
    (hu : w ≠ u) : mv b t u w = b w := by simp [mv, ht, hu]

theorem Ach.congr {E E' : Set (Sym2 V)} {b b' : V → ℕ} (h : Ach E b) (hE : E = E')
    (hb : ∀ v, b v = b' v) : Ach E' b' := by
  subst hE
  obtain ⟨D, hD⟩ := h
  exact ⟨D, fun v => (hD v).trans (hb v)⟩

/-- The empty graph has the empty decomposition. -/
theorem Ach.empty : Ach (∅ : Set (Sym2 V)) (fun _ => 0) := by
  refine ⟨⟨[], List.nodup_nil, fun e => ?_⟩, fun v => rfl⟩
  simp

omit [DecidableEq V] in
theorem blankNbrs_le_of_subset [Finite V] {E : Set (Sym2 V)} {b : V → ℕ} {u : V} {S : Set V}
    (h : ∀ w, s(u, w) ∈ E → w ≠ u → b w = 0 → w ∈ S) : blankNbrs E b u ≤ S.ncard :=
  Set.ncard_le_ncard (fun w hw => h w hw.1 hw.2.1 hw.2.2) (Set.toFinite S)

omit [DecidableEq V] in
theorem blankNbrs_mono [Finite V] {E E' : Set (Sym2 V)} {b b' : V → ℕ} {u : V}
    (h : ∀ w, s(u, w) ∈ E' → w ≠ u → b' w = 0 → s(u, w) ∈ E ∧ b w = 0) :
    blankNbrs E' b' u ≤ blankNbrs E b u :=
  blankNbrs_le_of_subset fun w h1 h2 h3 => ⟨(h w h1 h2 h3).1, h2, (h w h1 h2 h3).2⟩

/-! ### Transfers -/

section transfer

variable [Fintype V]

/-- **Grouped transfer** (Fan's Lemma 3.3 as used; `fan_grouped`), in edge-set form. -/
theorem Ach.grouped {E : Set (Sym2 V)} {b : V → ℕ} (h : Ach E b) (u : V) (T : Finset V)
    (huT : u ∉ T) (hT : ∀ t ∈ T, s(t, u) ∉ E) (hsum : blankNbrs E b u < ∑ t ∈ T, b t) :
    ∃ t ∈ T, 1 ≤ b t ∧ Ach (insert s(t, u) E) (mv b t u) := by
  classical
  obtain ⟨D, hD⟩ := h
  have hT' : ∀ t ∈ T, ¬ (fromEdgeSet E).Adj t u := fun t ht hadj =>
    hT t ht ((fromEdgeSet_adj E).mp hadj).1
  have hcard : (Finset.univ.filter (fun w => (fromEdgeSet E).Adj u w ∧ D.ends w = 0)).card =
      blankNbrs E b u := by
    unfold blankNbrs
    rw [← Set.ncard_coe_finset]
    congr 1
    ext w
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, fromEdgeSet_adj,
      hD]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, Ne.symm h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, Ne.symm h2⟩, h3⟩
  have hsum' : (Finset.univ.filter (fun w => (fromEdgeSet E).Adj u w ∧ D.ends w = 0)).card <
      ∑ t ∈ T, D.ends t := by
    rw [hcard]; simpa only [hD] using hsum
  obtain ⟨t, ht, hK⟩ := fan_grouped D u T huT hT' hsum'
  have htu : t ≠ u := fun h => huT (h ▸ ht)
  obtain ⟨D', -, hD'⟩ := hK (fromEdgeSet (insert s(t, u) E)) (by
    intro e
    simp only [edgeSet_fromEdgeSet, Set.mem_sdiff, Set.mem_insert_iff]
    constructor
    · rintro ⟨h | h, hd⟩
      · exact Or.inr h
      · exact Or.inl ⟨h, hd⟩
    · rintro (⟨h, hd⟩ | h)
      · exact ⟨Or.inr h, hd⟩
      · refine ⟨Or.inl h, ?_⟩
        subst h
        simpa using htu)
  refine ⟨t, ht, ?_, D', fun w => ?_⟩
  · have := hD' t
    rw [hD t] at this
    simp only [ite_true, Ne.symm htu, ite_false] at this
    omega
  · have := hD' w
    rw [hD w] at this
    unfold mv
    by_cases hwu : w = u
    · subst hwu
      simp only [htu, ite_false, ite_true] at this ⊢
      omega
    · by_cases hwt : w = t
      · subst hwt
        simp only [hwu, ite_false, ite_true, Ne.symm hwu] at this ⊢
        omega
      · simp only [hwu, hwt, ite_false, Ne.symm hwu, Ne.symm hwt] at this ⊢
        omega

/-- **Single transfer** (Fan's Lemma 3.4). -/
theorem Ach.transfer {E : Set (Sym2 V)} {b : V → ℕ} (h : Ach E b) {t u : V} (htu : t ≠ u)
    (hE : s(t, u) ∉ E) (hc : blankNbrs E b u < b t) : Ach (insert s(t, u) E) (mv b t u) := by
  obtain ⟨t', ht', -, h'⟩ := h.grouped u {t} (by simpa using htu.symm) (by simpa using hE)
    (by simpa using hc)
  rw [Finset.mem_singleton] at ht'
  subst ht'
  exact h'

end transfer

/-! ### Vertex lists -/

section lists

/-- The last vertex of the list `a :: l`. -/
def lastOf {W : Type*} : W → List W → W
  | a, [] => a
  | _, b :: l => lastOf b l

/-- The consecutive edges of the list `a :: l`. -/
def lEdges {W : Type*} : W → List W → List (Sym2 W)
  | _, [] => []
  | a, b :: l => s(a, b) :: lEdges b l

variable {W : Type*}

@[simp] theorem lastOf_nil (a : W) : lastOf a [] = a := rfl
@[simp] theorem lastOf_cons (a b : W) (l : List W) : lastOf a (b :: l) = lastOf b l := rfl
@[simp] theorem lEdges_nil (a : W) : lEdges a [] = [] := rfl
@[simp] theorem lEdges_cons (a b : W) (l : List W) : lEdges a (b :: l) = s(a, b) :: lEdges b l :=
  rfl

theorem lastOf_append (a : W) (l₁ l₂ : List W) :
    lastOf a (l₁ ++ l₂) = lastOf (lastOf a l₁) l₂ := by
  induction l₁ generalizing a with
  | nil => rfl
  | cons b l ih => exact ih b

@[simp] theorem lastOf_concat (a : W) (l : List W) (z : W) : lastOf a (l ++ [z]) = z := by
  rw [lastOf_append]; rfl

theorem lEdges_append (a : W) (l₁ l₂ : List W) :
    lEdges a (l₁ ++ l₂) = lEdges a l₁ ++ lEdges (lastOf a l₁) l₂ := by
  induction l₁ generalizing a with
  | nil => rfl
  | cons b l ih => simp [ih]

theorem lastOf_mem (a : W) (l : List W) : lastOf a l ∈ a :: l := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => exact List.mem_cons_of_mem _ (ih b)

theorem lastOf_mem_of_ne_nil (a : W) {l : List W} (hl : l ≠ []) : lastOf a l ∈ l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons b l => exact lastOf_mem b l

/-- An edge lies on the list `a :: l` iff it joins two consecutive entries. -/
theorem mem_lEdges_iff {a : W} {l : List W} {e : Sym2 W} :
    e ∈ lEdges a l ↔ ∃ x y, [x, y] <:+: a :: l ∧ e = s(x, y) := by
  induction l generalizing a with
  | nil =>
    simp only [lEdges_nil, List.not_mem_nil, false_iff, not_exists, not_and]
    intro x y h
    have := h.length_le
    simp at this
  | cons b l ih =>
    rw [lEdges_cons, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨x, y, hxy, rfl⟩)
      · exact ⟨a, b, List.infix_cons_iff.mpr (Or.inl (by simp)), rfl⟩
      · exact ⟨x, y, hxy.trans (List.suffix_cons a _).isInfix, rfl⟩
    · rintro ⟨x, y, hxy, rfl⟩
      rcases List.infix_cons_iff.mp hxy with h | h
      · rw [List.cons_prefix_cons] at h
        obtain ⟨rfl, h⟩ := h
        rw [List.cons_prefix_cons] at h
        obtain ⟨rfl, -⟩ := h
        exact Or.inl rfl
      · exact Or.inr ⟨x, y, h, rfl⟩

theorem mem_of_mem_lEdges {a : W} {l : List W} {e : Sym2 W} (he : e ∈ lEdges a l) {v : W}
    (hv : v ∈ e) : v ∈ a :: l := by
  obtain ⟨x, y, hxy, rfl⟩ := mem_lEdges_iff.mp he
  rcases Sym2.mem_iff.mp hv with rfl | rfl
  · exact hxy.subset (by simp)
  · exact hxy.subset (by simp)

theorem lEdges_not_diag {a : W} {l : List W} (hnd : (a :: l).Nodup) {e : Sym2 W}
    (he : e ∈ lEdges a l) : ¬ e.IsDiag := by
  obtain ⟨x, y, hxy, rfl⟩ := mem_lEdges_iff.mp he
  have := hnd.sublist hxy.sublist
  simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_self, and_true] at this
  simpa using this

theorem lEdges_nodup {a : W} {l : List W} (hnd : (a :: l).Nodup) : (lEdges a l).Nodup := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    rw [lEdges_cons, List.nodup_cons]
    refine ⟨fun h => ?_, ih (List.nodup_cons.mp hnd).2⟩
    have := mem_of_mem_lEdges h (Sym2.mem_mk_left a b)
    exact (List.nodup_cons.mp hnd).1 this

end lists

/-! ### Adding a path -/

section addPath

omit [DecidableEq V]

/-- The walk along the list `a :: l`. -/
def walkOf (K : SimpleGraph V) : (a : V) → (l : List V) → (∀ e ∈ lEdges a l, e ∈ K.edgeSet) →
    K.Walk a (lastOf a l)
  | _, [], _ => Walk.nil
  | a, b :: l, h => Walk.cons ((mem_edgeSet K).mp (h s(a, b) (by simp)))
      (walkOf K b l (fun e he => h e (by simp [he])))

theorem walkOf_support (K : SimpleGraph V) (a : V) (l : List V) (h) :
    (walkOf K a l h).support = a :: l := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    simp only [walkOf]
    exact (Walk.support_cons _ _).trans (congrArg _ (ih b _))

theorem walkOf_edges (K : SimpleGraph V) (a : V) (l : List V) (h) :
    (walkOf K a l h).edges = lEdges a l := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    simp only [walkOf]
    exact (Walk.edges_cons _ _).trans (congrArg _ (ih b _))

theorem walkOf_length (K : SimpleGraph V) (a : V) (l : List V) (h) :
    (walkOf K a l h).length = l.length := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    simp only [walkOf]
    exact (Walk.length_cons _ _).trans (congrArg (· + 1) (ih b _))

/-- The path along a duplicate-free list `a :: l` with `l ≠ []`. -/
def GPath.ofList (K : SimpleGraph V) (a : V) (l : List V) (hl : l ≠ []) (hnd : (a :: l).Nodup)
    (h : ∀ e ∈ lEdges a l, e ∈ K.edgeSet) : GPath K :=
  ⟨a, lastOf a l, walkOf K a l h, by rw [Walk.isPath_def, walkOf_support]; exact hnd,
    by rw [walkOf_length]; exact List.length_pos_of_ne_nil hl⟩

variable [DecidableEq V]

/-- **Adding a path.** A duplicate-free list `a :: l` (`l ≠ []`) whose consecutive edges are all
new becomes an extra row, with one more end at `a` and one more at `lastOf a l`. -/
theorem Ach.addPath {E : Set (Sym2 V)} {b : V → ℕ} (h : Ach E b) (a : V) (l : List V)
    (hl : l ≠ []) (hnd : (a :: l).Nodup) (hnew : ∀ e ∈ lEdges a l, e ∉ E) :
    Ach (E ∪ {e | e ∈ lEdges a l})
      (fun v => b v + ((if a = v then 1 else 0) + (if lastOf a l = v then 1 else 0))) := by
  obtain ⟨D, hD⟩ := h
  set K' : SimpleGraph V := fromEdgeSet (E ∪ {e | e ∈ lEdges a l})
  have hK'P : ∀ e ∈ lEdges a l, e ∈ K'.edgeSet := fun e he => by
    simp only [K', edgeSet_fromEdgeSet, Set.mem_sdiff, Set.mem_union, Set.mem_ofPred_eq]
    exact ⟨Or.inr he, lEdges_not_diag hnd he⟩
  have hDE : ∀ e ∈ D.paths.flatMap GPath.edges, e ∈ E ∧ ¬ e.IsDiag := fun e he => by
    have := (D.covers e).2 he
    simp only [edgeSet_fromEdgeSet, Set.mem_sdiff] at this
    exact ⟨this.1, this.2⟩
  have H : ∀ Q ∈ D.paths, ∀ e ∈ Q.edges, e ∈ K'.edgeSet := fun Q hQ e he => by
    have := hDE e (List.mem_flatMap.mpr ⟨Q, hQ, he⟩)
    simp only [K', edgeSet_fromEdgeSet, Set.mem_sdiff, Set.mem_union]
    exact ⟨Or.inl this.1, this.2⟩
  let P := GPath.ofList K' a l hl hnd hK'P
  have hPe : P.edges = lEdges a l := walkOf_edges _ _ _ _
  let L := D.paths.pmap (fun Q hQ => Q.transfer hQ) H ++ [P]
  have hLe : L.flatMap GPath.edges = D.paths.flatMap GPath.edges ++ lEdges a l := by
    simp only [L, List.flatMap_append, flatMap_pmap_transfer, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, hPe]
  have hnd' : (L.flatMap GPath.edges).Nodup := by
    rw [hLe, List.nodup_append]
    refine ⟨D.nodup_edges, lEdges_nodup hnd, ?_⟩
    rintro x hx y hy rfl
    exact hnew x hy (hDE x hx).1
  have hcov : ∀ e, e ∈ K'.edgeSet ↔ e ∈ L.flatMap GPath.edges := by
    intro e
    rw [hLe, List.mem_append]
    simp only [K', edgeSet_fromEdgeSet, Set.mem_sdiff, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h | h, hd⟩
      · refine Or.inl ((D.covers e).1 ?_)
        simp only [edgeSet_fromEdgeSet, Set.mem_sdiff]
        exact ⟨h, hd⟩
      · exact Or.inr h
    · rintro (h | h)
      · exact ⟨Or.inl (hDE e h).1, (hDE e h).2⟩
      · exact ⟨Or.inr h, lEdges_not_diag hnd h⟩
  refine ⟨⟨L, hnd', hcov⟩, fun v => ?_⟩
  have h1 := sum_endsAt_pmap_transfer D.paths H v
  have h2 : (D.paths.map (fun P => P.endsAt v)).sum = b v := hD v
  show (L.map (fun P => P.endsAt v)).sum = _
  simp only [L, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, h1, h2]
  rfl

end addPath

end Gallai
