import GallaiLean.SixCliqueModel
import GallaiLean.EvenInsert

/-!
# The six-clique construction on a labelled graph

`SixData V` packages a graph `G` together with the labelling used in Section 4 of the paper:

* `ι : Fin 12 → V` (injective): `ι 0, …, ι 5` are the clique `U`, and `ι (6 + h)` is the
  representative of omission type `h`;
* `ty v`: the clique label omitted by an exterior vertex `v`;
* `prs`: a partition of the non-representative exterior vertices into pairs of equal type;
* the adjacency facts of Theorem 1 and the evenness of the exterior graph `F = G[X]`.

`SixData.main` produces a path decomposition of `G` with end vector `B cfin`: two ends at
`ι 0, ι 2, ι 3`, none at `ι 1, ι 4, ι 5`, one at every exterior vertex.

**Graph states.** `St L A` is the edge set at a point of the construction: the core edges
`ι(L)` (`L` a list of model edges), the seed rows `x — ι (ptc (ty x))` of every non-representative
`x`, the whole exterior graph `F`, and all true spokes of the non-representatives in `A` (those
whose pair has been completed). `B c` is the end vector `c` on the core and `1` elsewhere.

**Steps.**
1. `seed`: the five seed paths and one two-edge row `x, p, y` per pair give
   `Ach (ι(seedE) ∪ seedP) (B c1)` (`Ach.addMapPaths`, `Ach.addPath`).
2. `after_F`: Lemma 3 (`Ach.insert_even`) inserts `F`.
3. For each of the three stages: `stage` completes every pair of the two types processed there
   (one checked Lemma-4 program per pair, `pair_step`), then `segment` performs the core transfers.
4. `main`: the final path `(0, 5, 1, 2, 4, 3)` is added, and the edge set is exactly `E(G)`.

The model checks are those of `SixCliqueModel`; the transfer from model to graph is
`Prog.sound₀`. Every blank vertex lies in the model because non-core vertices keep one end.
-/

open SimpleGraph

namespace Gallai

open SixModel

universe u

/-! ### Generic helpers -/

section helpers

variable {V : Type u} [DecidableEq V]

theorem lEdges_map {W : Type*} (f : W → V) (a : W) (l : List W) :
    lEdges (f a) (l.map f) = (lEdges a l).map (Sym2.map f) := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => simp [ih]

theorem lastOf_map {W : Type*} (f : W → V) (a : W) (l : List W) :
    lastOf (f a) (l.map f) = f (lastOf a l) := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => simp [ih]

theorem img_ofSym_eq {n : ℕ} (ι : Fin n → V) (L : List (Sym2 (Fin n))) :
    img ι (ofSym L) = {e | ∃ x ∈ L, e = x.map ι} := by
  ext e
  simp only [img, ofSym, decide_eq_true_eq, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, b, h, rfl⟩
    exact ⟨s(a, b), h, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    induction x using Sym2.ind with
    | _ a b => exact ⟨a, b, hx, rfl⟩

theorem img_ofSym_append {n : ℕ} (ι : Fin n → V) (L₁ L₂ : List (Sym2 (Fin n))) :
    img ι (ofSym (L₁ ++ L₂)) = img ι (ofSym L₁) ∪ img ι (ofSym L₂) := by
  simp only [img_ofSym_eq, List.mem_append]
  ext e
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨x, hx | hx, rfl⟩
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨x, Or.inl hx, rfl⟩
    · exact ⟨x, Or.inr hx, rfl⟩

/-- Adding a path given on a model. -/
theorem Ach.addMapPath {n : ℕ} (ι : Fin n → V) (hι : Function.Injective ι) {E : Set (Sym2 V)}
    {b : V → ℕ} (h : Ach E b) (a : Fin n) (l : List (Fin n)) (hl : l ≠ [])
    (hnd : (a :: l).Nodup) (hnew : ∀ x ∈ lEdges a l, x.map ι ∉ E) :
    Ach (E ∪ {e | ∃ x ∈ lEdges a l, e = x.map ι})
      (fun v => b v + ((if ι a = v then 1 else 0) + (if ι (lastOf a l) = v then 1 else 0))) := by
  have h' := h.addPath (ι a) (l.map ι) (by simpa using hl)
    (by rw [← List.map_cons]; exact hnd.map hι)
    (by
      rw [lEdges_map]
      intro e he
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
      exact hnew x hx)
  refine h'.congr ?_ (fun v => by rw [lastOf_map])
  ext e
  simp only [Set.mem_union, Set.mem_ofPred_eq, lEdges_map, List.mem_map]
  constructor
  · rintro (h | ⟨x, hx, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨x, hx, rfl⟩
  · rintro (h | ⟨x, hx, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨x, hx, rfl⟩

/-- Adding a list of model paths. -/
theorem Ach.addMapPaths [Fintype V] {n : ℕ} (ι : Fin n → V) (hι : Function.Injective ι) :
    ∀ (P : List (Fin n × List (Fin n))) {E : Set (Sym2 V)} {b : V → ℕ}, Ach E b →
      (∀ p ∈ P, p.2 ≠ [] ∧ (p.1 :: p.2).Nodup) →
      (P.flatMap (fun p => lEdges p.1 p.2)).Nodup →
      (∀ x ∈ P.flatMap (fun p => lEdges p.1 p.2), x.map ι ∉ E) →
      Ach (E ∪ {e | ∃ x ∈ P.flatMap (fun p => lEdges p.1 p.2), e = x.map ι})
        (fun v => b v + (P.map (fun p => (if ι p.1 = v then 1 else 0) +
          (if ι (lastOf p.1 p.2) = v then 1 else 0))).sum)
  | [], E, b, h, _, _, _ => h.congr (by ext e; simp) (fun v => by simp)
  | p :: P, E, b, h, hP, hnd, hnew => by
    rw [List.flatMap_cons, List.nodup_append] at hnd
    have h1 := h.addMapPath ι hι p.1 p.2 (hP p (by simp)).1 (hP p (by simp)).2
      (fun x hx => hnew x (by simp [hx]))
    have h2 := Ach.addMapPaths ι hι P h1 (fun q hq => hP q (by simp [hq])) hnd.2.1
      (by
        intro x hx hmem
        rcases hmem with hmem | ⟨y, hy, hxy⟩
        · exact hnew x (by simp only [List.flatMap_cons, List.mem_append]; exact Or.inr hx) hmem
        · exact hnd.2.2 y hy x hx (Sym2.map.injective hι hxy).symm)
    refine h2.congr ?_ (fun v => by simp only [List.map_cons, List.sum_cons]; ring)
    ext e
    simp only [Set.mem_union, Set.mem_ofPred_eq, List.flatMap_cons, List.mem_append]
    constructor
    · rintro ((h | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, Or.inl hx, rfl⟩
      · exact Or.inr ⟨x, Or.inr hx, rfl⟩
    · rintro (h | ⟨x, hx | hx, rfl⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨x, hx, rfl⟩)
      · exact Or.inr ⟨x, hx, rfl⟩

end helpers

/-! ### The labelled data -/

/-- The data of Theorem 1 after labelling the clique and choosing representatives and pairs. -/
structure SixData (V : Type u) [DecidableEq V] [Fintype V] where
  G : SimpleGraph V
  ι : Fin 12 → V
  inj : Function.Injective ι
  ty : V → Fin 6
  prs : List (V × V)
  adj_cc : ∀ i j : Fin 12, i.val < 6 → j.val < 6 → i ≠ j → G.Adj (ι i) (ι j)
  adj_ext : ∀ v, (¬ ∃ i : Fin 12, i.val < 6 ∧ ι i = v) → ∀ k : Fin 12, k.val < 6 →
    (G.Adj v (ι k) ↔ k.val ≠ (ty v).val)
  ty_rep : ∀ i : Fin 12, 6 ≤ i.val → (ty (ι i)).val = i.val - 6
  ext_even : ∀ v, (¬ ∃ i : Fin 12, i.val < 6 ∧ ι i = v) →
    Even {w | G.Adj v w ∧ ¬ ∃ i : Fin 12, i.val < 6 ∧ ι i = w}.ncard
  prs_nc : ∀ p ∈ prs, p.1 ∉ Set.range ι ∧ p.2 ∉ Set.range ι ∧ ty p.1 = ty p.2
  prs_nodup : (prs.flatMap (fun p => [p.1, p.2])).Nodup
  prs_cover : ∀ v, v ∉ Set.range ι → ∃ p ∈ prs, v = p.1 ∨ v = p.2

namespace SixData

variable {V : Type u} [DecidableEq V] [Fintype V] (S : SixData V)

/-- Clique vertices. -/
def cl (v : V) : Prop := ∃ i : Fin 12, i.val < 6 ∧ S.ι i = v

/-- Non-core vertices: exterior and not a representative. -/
def nc (v : V) : Prop := v ∉ Set.range S.ι

/-- The exterior graph `F = G[X]`. -/
noncomputable def Fset : Finset (Sym2 V) := by
  classical exact Finset.univ.filter (fun e => e ∈ S.G.edgeSet ∧ ∀ v ∈ e, ¬ S.cl v)

/-- The seed rows: each non-representative `x` has its spoke to `ι (ptc (ty x))`. -/
def seedP : Set (Sym2 V) := {e | ∃ v, S.nc v ∧ e = s(v, S.ι (ptc (S.ty v)))}

/-- All true spokes of the vertices in `A`. -/
def PS (A : Set V) : Set (Sym2 V) :=
  {e | ∃ v ∈ A, ∃ k : Fin 12, k.val < 6 ∧ S.G.Adj v (S.ι k) ∧ e = s(v, S.ι k)}

/-- The edge set with core edges `L` and the pairs of `A` completed. -/
noncomputable def St (L : List (Sym2 (Fin 12))) (A : Set V) : Set (Sym2 V) :=
  img S.ι (ofSym L) ∪ S.seedP ∪ ↑S.Fset ∪ S.PS A

/-- Non-representatives whose type is processed before stage `s`. -/
def Ast (s : ℕ) : Set V := {v | S.nc v ∧ (S.ty v).val / 2 < s}

/-- The end vector `c` on the core and `1` elsewhere. -/
noncomputable def B (c : Fin 12 → ℕ) : V → ℕ := Function.extend S.ι c (fun _ => 1)

variable {S}

theorem cl_iota {i : Fin 12} : S.cl (S.ι i) ↔ i.val < 6 := by
  constructor
  · rintro ⟨j, hj, h⟩
    rw [S.inj h] at hj
    exact hj
  · intro h
    exact ⟨i, h, rfl⟩

theorem nc_not_cl {v : V} (h : S.nc v) : ¬ S.cl v := by
  rintro ⟨i, -, rfl⟩
  exact h ⟨i, rfl⟩

theorem nc_ne_iota {v : V} (h : S.nc v) (i : Fin 12) : v ≠ S.ι i := by
  rintro rfl; exact h ⟨i, rfl⟩

theorem mem_Fset {e : Sym2 V} : e ∈ S.Fset ↔ e ∈ S.G.edgeSet ∧ ∀ v ∈ e, ¬ S.cl v := by
  classical
  unfold Fset
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem B_iota (c : Fin 12 → ℕ) (a : Fin 12) : S.B c (S.ι a) = c a :=
  S.inj.extend_apply c _ a

theorem B_nc (c : Fin 12 → ℕ) {v : V} (h : S.nc v) : S.B c v = 1 := by
  unfold B
  rw [Function.extend_apply']
  rintro ⟨a, rfl⟩
  exact h ⟨a, rfl⟩

theorem B_pos (c : Fin 12 → ℕ) : ∀ v, v ∉ Set.range S.ι → 0 < S.B c v := by
  intro v hv
  rw [B_nc c hv]
  exact Nat.one_pos

theorem ty_prs_nc {p : V × V} (hp : p ∈ S.prs) : S.nc p.1 ∧ S.nc p.2 := by
  exact ⟨(S.prs_nc p hp).1, (S.prs_nc p hp).2.1⟩

/-- Core edges of a state are allowed by `cupS`. -/
theorem core_mem {L : List (Sym2 (Fin 12))} {A : Set V} (hA : ∀ v ∈ A, S.nc v) {a a' : Fin 12}
    (h : a ≠ a') (hm : s(S.ι a, S.ι a') ∈ S.St L A) : cupS L a a' = true := by
  unfold St at hm
  simp only [cupS, Bool.or_eq_true]
  rcases hm with ((hm | ⟨v, hv, he⟩) | hm) | ⟨v, hvA, k, -, -, he⟩
  · obtain ⟨c, d, hcd, he⟩ := hm
    left
    simp only [ofSym, decide_eq_true_eq] at hcd ⊢
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [S.inj h1, S.inj h2]; exact hcd
    · rw [S.inj h1, S.inj h2, Sym2.eq_swap]; exact hcd
  · exfalso
    rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact hv ⟨a, h1⟩
    · exact hv ⟨a', h1⟩
  · right
    rw [Finset.mem_coe, mem_Fset] at hm
    have h1 := hm.2 _ (Sym2.mem_mk_left _ _)
    have h2 := hm.2 _ (Sym2.mem_mk_right _ _)
    rw [cl_iota] at h1 h2
    simp only [rr, Bool.and_eq_true, decide_eq_true_eq]
    omega
  · exfalso
    rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact hA v hvA ⟨a, h1⟩
    · exact hA v hvA ⟨a', h1⟩

/-- A non-core vertex outside `A` meets the core only at its seed vertex and at representatives. -/
theorem nc_mem {L : List (Sym2 (Fin 12))} {A : Set V} (hA : ∀ v ∈ A, S.nc v) {v : V}
    (hv : S.nc v) (hvA : v ∉ A) {i : Fin 12} (hm : s(v, S.ι i) ∈ S.St L A) :
    i = ptc (S.ty v) ∨ 6 ≤ i.val := by
  unfold St at hm
  rcases hm with ((⟨c, d, -, he⟩ | ⟨x, hx, he⟩) | hm) | ⟨x, hxA, k, -, -, he⟩
  · exfalso
    rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hv ⟨c, h1.symm⟩
    · exact hv ⟨d, h1.symm⟩
  · rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, -⟩
    · subst h1; exact Or.inl (S.inj h2)
    · exact absurd h1 (nc_ne_iota hv _)
  · right
    rw [Finset.mem_coe, mem_Fset] at hm
    have := hm.2 _ (Sym2.mem_mk_right _ _)
    rw [cl_iota] at this
    omega
  · exfalso
    rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hvA (h1 ▸ hxA)
    · exact nc_ne_iota hv _ h1

/-! ### Core segments -/

/-- A checked list of core transfers. -/
theorem segment {L : List (Sym2 (Fin 12))} {A : Set V} (hA : ∀ v ∈ A, S.nc v)
    (seg : List (Fin 12 × Fin 12)) {c c' : Fin 12 → ℕ}
    (hok : (Prog.ofList seg).ok (ofSym (segE seg)) c' (cupS L) (fun _ _ => false) c = true)
    (h : Ach (S.St L A) (S.B c)) : Ach (S.St (L ++ segE seg) A) (S.B c') := by
  obtain ⟨b', hach, hb'ι, hb'o⟩ := Prog.sound₀ S.ι S.inj _ (cupS L) _ c c' hok h (B_iota c)
    (B_pos c) (fun a a' haa' hm => core_mem hA haa' hm)
  refine hach.congr ?_ ?_
  · unfold St
    rw [img_ofSym_append]
    ext e
    simp only [Set.mem_union]
    tauto
  · intro v
    by_cases hv : v ∈ Set.range S.ι
    · obtain ⟨a, rfl⟩ := hv
      rw [hb'ι, B_iota]
    · rw [hb'o v hv, B_nc c hv, B_nc c' hv]

/-! ### Pairs (Lemma 4) -/

/-- The pair model map. -/
def iota14 (S : SixData V) (x y : V) (a : Fin 14) : V :=
  if h : a.val < 12 then S.ι ⟨a.val, h⟩ else if a.val = 12 then x else y

theorem iota14_lt {x y : V} {a : Fin 14} (h : a.val < 12) : iota14 S x y a = S.ι ⟨a.val, h⟩ := by
  simp [iota14, h]

theorem iota14_core {x y : V} (k : Fin 12) {h : k.val < 14} :
    iota14 S x y ⟨k.val, h⟩ = S.ι k := by
  simp [iota14]

theorem iota14_inj {x y : V} (hx : S.nc x) (hy : S.nc y) (hxy : x ≠ y) :
    Function.Injective (iota14 S x y) := by
  intro a b hab
  unfold iota14 at hab
  by_cases ha : a.val < 12 <;> by_cases hb : b.val < 12
  · simp only [ha, hb, dite_true] at hab
    exact Fin.ext (by simpa using S.inj hab)
  · simp only [ha, hb, dite_true, dite_false] at hab
    split_ifs at hab
    · exact absurd hab.symm (nc_ne_iota hx _)
    · exact absurd hab.symm (nc_ne_iota hy _)
  · simp only [ha, hb, dite_true, dite_false] at hab
    split_ifs at hab
    · exact absurd hab (nc_ne_iota hx _)
    · exact absurd hab (nc_ne_iota hy _)
  · simp only [ha, hb, dite_false] at hab
    have ha' : a.val < 14 := a.isLt
    have hb' : b.val < 14 := b.isLt
    split_ifs at hab with h1 h2 h2
    · exact Fin.ext (by omega)
    · exact absurd hab hxy
    · exact absurd hab.symm hxy
    · exact Fin.ext (by omega)

theorem range_iota14 {x y v : V} (hv : v ∉ Set.range (iota14 S x y)) : v ∉ Set.range S.ι := by
  rintro ⟨a, rfl⟩
  exact hv ⟨⟨a.val, by omega⟩, by rw [iota14_lt (by simp)]⟩

/-- **Lemma 4 for one pair**: all remaining spokes of `x, y` are inserted, end vector restored. -/
theorem pair_step {L : List (Sym2 (Fin 12))} {A : Set V} (hA : ∀ v ∈ A, S.nc v)
    {c : Fin 12 → ℕ} {x y : V} (hx : S.nc x) (hy : S.nc y) (hxy : x ≠ y)
    (hty : S.ty x = S.ty y) (hxA : x ∉ A) (hyA : y ∉ A)
    (hok : (pairProg (S.ty x)).ok (ofSym (pairE (S.ty x))) (ext14 c) (cup14 L (S.ty x))
      (fun _ _ => false) (ext14 c) = true)
    (h : Ach (S.St L A) (S.B c)) : Ach (S.St L (A ∪ {x, y})) (S.B c) := by
  have hinj := iota14_inj hx hy hxy
  have h12 : (iota14 S x y) 12 = x := by simp [iota14]
  have h13 : (iota14 S x y) 13 = y := by simp [iota14]
  have hιxy : ∀ a : Fin 14, 12 ≤ a.val → (iota14 S x y) a = x ∨ (iota14 S x y) a = y := by
    intro a ha
    have : a.val < 14 := a.isLt
    simp only [iota14, show ¬ a.val < 12 by omega, dite_false]
    split_ifs <;> simp
  have hbc : ∀ a, S.B c ((iota14 S x y) a) = ext14 c a := by
    intro a
    unfold ext14
    by_cases ha : a.val < 12
    · rw [iota14_lt ha, B_iota, dif_pos ha]
    · rw [dite_eq_right ha]
      rcases hιxy a (by omega) with h | h <;> rw [h]
      · exact B_nc c hx
      · exact B_nc c hy
  have hadj : ∀ a a', a ≠ a' → s((iota14 S x y) a, (iota14 S x y) a') ∈ S.St L A → cup14 L (S.ty x) a a' = true := by
    -- a non-core end of an edge
    have key : ∀ (a a' : Fin 14), 12 ≤ a.val → a'.val < 12 →
        s((iota14 S x y) a, (iota14 S x y) a') ∈ S.St L A → (a'.val == (ptc (S.ty x)).val || 6 ≤ a'.val) = true := by
      intro a a' ha ha' hm
      rw [iota14_lt ha'] at hm
      have hv : S.nc ((iota14 S x y) a) ∧ (iota14 S x y) a ∉ A ∧ S.ty ((iota14 S x y) a) = S.ty x := by
        rcases hιxy a ha with h | h <;> rw [h]
        · exact ⟨hx, hxA, rfl⟩
        · exact ⟨hy, hyA, hty.symm⟩
      rcases nc_mem hA hv.1 hv.2.1 hm with h | h
      · simp only [Bool.or_eq_true, beq_iff_eq]
        left
        rw [← hv.2.2, ← h]
      · simp only [Bool.or_eq_true, decide_eq_true_eq]
        right; exact h
    intro a a' haa' hm
    unfold cup14
    by_cases ha : a.val < 12 <;> by_cases ha' : a'.val < 12
    · rw [dif_pos ⟨ha, ha'⟩]
      rw [iota14_lt ha, iota14_lt ha'] at hm
      exact core_mem hA (fun h => haa' (Fin.ext (by simpa using congrArg Fin.val h))) hm
    · rw [dite_eq_right (by omega), if_pos ha]
      have := key a' a (by omega) ha (by rwa [Sym2.eq_swap])
      simp only [Bool.or_eq_true] at this ⊢
      exact Or.inr this
    · rw [dite_eq_right (by omega), if_neg ha]
      have := key a a' (by omega) ha' hm
      simp only [Bool.or_eq_true] at this ⊢
      exact Or.inr this
    · rw [dite_eq_right (by omega)]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      left; omega
  obtain ⟨b', hach, hb'ι, hb'o⟩ := Prog.sound₀ (iota14 S x y) hinj _ _ _ _ _ hok h hbc
    (fun v hv => B_pos c v (range_iota14 hv)) hadj
  refine hach.congr ?_ ?_
  · -- the inserted spokes complete `x` and `y`
    ext e
    simp only [St, Set.mem_union]
    constructor
    · rintro ((((h | h) | h) | h) | ⟨a, b, hab, rfl⟩)
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · obtain ⟨v, hv, k, hk, hadj, rfl⟩ := h
        exact Or.inr ⟨v, Or.inl hv, k, hk, hadj, rfl⟩
      · simp only [ofSym, decide_eq_true_eq] at hab
        right
        rcases (pairE_iff _ a b).mp hab with ⟨ha, hb, hbh, -⟩ | ⟨hb, ha, hah, -⟩
        · have hv : (iota14 S x y) a = x ∨ (iota14 S x y) a = y := hιxy a (by omega)
          refine ⟨(iota14 S x y) a, by rcases hv with h | h <;> simp [h], ⟨b.val, by omega⟩, hb, ?_, ?_⟩
          · rcases hv with h | h <;> rw [h]
            · rw [S.adj_ext x (nc_not_cl hx) _ hb]; exact hbh
            · rw [S.adj_ext y (nc_not_cl hy) _ hb, ← hty]; exact hbh
          · rw [iota14_lt (a := b) (by omega)]
        · have hv : (iota14 S x y) b = x ∨ (iota14 S x y) b = y := hιxy b (by omega)
          refine ⟨(iota14 S x y) b, by rcases hv with h | h <;> simp [h], ⟨a.val, by omega⟩, ha, ?_, ?_⟩
          · rcases hv with h | h <;> rw [h]
            · rw [S.adj_ext x (nc_not_cl hx) _ ha]; exact hah
            · rw [S.adj_ext y (nc_not_cl hy) _ ha, ← hty]; exact hah
          · rw [iota14_lt (a := a) (by omega), Sym2.eq_swap]
    · rintro (((h | h) | h) | ⟨v, hv, k, hk, hadj, rfl⟩)
      · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
      · exact Or.inl (Or.inl (Or.inr h))
      · rcases hv with hv | hv
        · exact Or.inl (Or.inr ⟨v, hv, k, hk, hadj, rfl⟩)
        · -- `v ∈ {x, y}`
          have hv' : v = x ∨ v = y := by simpa using hv
          have hvnc : S.nc v := by rcases hv' with rfl | rfl <;> assumption
          have hvty : S.ty v = S.ty x := by rcases hv' with rfl | rfl <;> simp [hty]
          have hkh : k.val ≠ (S.ty x).val := by
            rw [← hvty, ← S.adj_ext v (nc_not_cl hvnc) k hk]; exact hadj
          by_cases hkp : k = ptc (S.ty x)
          · left; left; left; right
            exact ⟨v, hvnc, by rw [hvty, hkp]⟩
          · right
            refine ⟨if v = x then 12 else 13, ⟨k.val, by omega⟩, ?_, ?_⟩
            · simp only [ofSym, decide_eq_true_eq]
              rw [pairE_iff]
              left
              refine ⟨by split_ifs <;> decide, hk, hkh, fun h => hkp (Fin.ext h)⟩
            · rw [iota14_core]
              congr 1
              rcases hv' with rfl | rfl
              · simp [h12]
              · simp [Ne.symm hxy, h13]
  · intro v
    by_cases hv : v ∈ Set.range (iota14 S x y)
    · obtain ⟨a, rfl⟩ := hv
      rw [hb'ι, hbc]
    · exact (hb'o v hv)

/-- **One stage**: complete every pair of the two types processed at stage `s`. -/
theorem stage_aux {L : List (Sym2 (Fin 12))} {c : Fin 12 → ℕ} :
    ∀ (P : List (V × V)) (A : Set V), (∀ v ∈ A, S.nc v) → (∀ p ∈ P, p ∈ S.prs) →
      (∀ p ∈ P, (pairProg (S.ty p.1)).ok (ofSym (pairE (S.ty p.1))) (ext14 c)
        (cup14 L (S.ty p.1)) (fun _ _ => false) (ext14 c) = true) →
      (P.flatMap (fun p => [p.1, p.2])).Nodup → (∀ p ∈ P, p.1 ∉ A ∧ p.2 ∉ A) →
      Ach (S.St L A) (S.B c) →
      Ach (S.St L (A ∪ {v | ∃ p ∈ P, v = p.1 ∨ v = p.2})) (S.B c)
  | [], A, _, _, _, _, _, h => h.congr (by simp) (fun _ => rfl)
  | p :: P, A, hA, hP, hok, hnd, hPA, h => by
    have hp := S.prs_nc p (hP p (by simp))
    rw [List.flatMap_cons, List.nodup_append] at hnd
    have hxy : p.1 ≠ p.2 := by
      have := hnd.1
      simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
        List.nodup_nil, and_self, and_true] at this
      exact this
    have h1 := pair_step hA hp.1 hp.2.1 hxy hp.2.2 (hPA p (by simp)).1 (hPA p (by simp)).2
      (hok p (by simp)) h
    have h2 := stage_aux P (A ∪ {p.1, p.2})
      (by
        rintro v (hv | hv)
        · exact hA v hv
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
          rcases hv with rfl | rfl
          · exact hp.1
          · exact hp.2.1)
      (fun q hq => hP q (by simp [hq])) (fun q hq => hok q (by simp [hq])) hnd.2.1
      (by
        intro q hq
        have hq1 : q.1 ∈ P.flatMap (fun p => [p.1, p.2]) := List.mem_flatMap.mpr ⟨q, hq, by simp⟩
        have hq2 : q.2 ∈ P.flatMap (fun p => [p.1, p.2]) := List.mem_flatMap.mpr ⟨q, hq, by simp⟩
        have hd := hnd.2.2
        refine ⟨?_, ?_⟩
        · rintro (h | h)
          · exact (hPA q (by simp [hq])).1 h
          · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
            rcases h with h | h
            · exact hd p.1 (by simp) q.1 hq1 h.symm
            · exact hd p.2 (by simp) q.1 hq1 h.symm
        · rintro (h | h)
          · exact (hPA q (by simp [hq])).2 h
          · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
            rcases h with h | h
            · exact hd p.1 (by simp) q.2 hq2 h.symm
            · exact hd p.2 (by simp) q.2 hq2 h.symm)
      h1
    refine h2.congr ?_ (fun _ => rfl)
    unfold St
    congr 2
    ext v
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq,
      List.mem_cons]
    constructor
    · rintro ((h | h | h) | ⟨q, hq, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨p, Or.inl rfl, Or.inl h⟩
      · exact Or.inr ⟨p, Or.inl rfl, Or.inr h⟩
      · exact Or.inr ⟨q, Or.inr hq, h⟩
    · rintro (h | ⟨q, rfl | hq, h⟩)
      · exact Or.inl (Or.inl h)
      · rcases h with h | h
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inl (Or.inr (Or.inr h))
      · exact Or.inr ⟨q, hq, h⟩

theorem stage {L : List (Sym2 (Fin 12))} {c : Fin 12 → ℕ} (s : ℕ)
    (hok : ∀ h : Fin 6, h.val / 2 = s → (pairProg h).ok (ofSym (pairE h)) (ext14 c)
      (cup14 L h) (fun _ _ => false) (ext14 c) = true)
    (h : Ach (S.St L (S.Ast s)) (S.B c)) : Ach (S.St L (S.Ast (s + 1))) (S.B c) := by
  set P := S.prs.filter (fun p => (S.ty p.1).val / 2 = s) with hPdef
  have hPs : ∀ p ∈ P, p ∈ S.prs ∧ (S.ty p.1).val / 2 = s := by
    intro p hp
    simpa [hPdef] using hp
  have h' := stage_aux (S := S) (L := L) (c := c) P (S.Ast s) (fun v hv => hv.1)
    (fun p hp => (hPs p hp).1) (fun p hp => hok _ (hPs p hp).2)
    (((List.filter_sublist (l := S.prs)).flatMap _).nodup S.prs_nodup)
    (by
      intro p hp
      have hs := (hPs p hp).2
      have hty := (S.prs_nc p (hPs p hp).1).2.2
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have := h.2; omega
      · have := h.2; rw [← hty] at this; omega)
    h
  refine h'.congr ?_ (fun _ => rfl)
  unfold St
  congr 2
  ext v
  simp only [Ast, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨hv, hlt⟩ | ⟨p, hp, hv⟩)
    · exact ⟨hv, by omega⟩
    · have hp' := hPs p hp
      have hnc := S.prs_nc p hp'.1
      rcases hv with rfl | rfl
      · exact ⟨hnc.1, by omega⟩
      · exact ⟨hnc.2.1, by rw [← hnc.2.2]; omega⟩
  · rintro ⟨hv, hlt⟩
    by_cases hs : (S.ty v).val / 2 < s
    · exact Or.inl ⟨hv, hs⟩
    · right
      obtain ⟨p, hp, hvp⟩ := S.prs_cover v hv
      have hty := (S.prs_nc p hp).2.2
      refine ⟨p, ?_, hvp⟩
      simp only [hPdef, List.mem_filter, decide_eq_true_eq]
      refine ⟨hp, ?_⟩
      rcases hvp with rfl | rfl
      · omega
      · rw [hty]; omega

/-! ### The seed -/

/-- The five seed paths. -/
theorem seed_core : Ach (img S.ι (ofSym seedE)) (Function.extend S.ι c1 (fun _ => 0)) := by
  have h := Ach.addMapPaths S.ι S.inj mpaths (Ach.empty (V := V)) mpaths_ok seedE_nodup
    (by simp)
  refine h.congr ?_ ?_
  · rw [img_ofSym_eq, Set.empty_union]
    rfl
  · intro v
    by_cases hv : v ∈ Set.range S.ι
    · obtain ⟨a, rfl⟩ := hv
      rw [S.inj.extend_apply, ← seed_ends a, zero_add]
      simp only [S.inj.eq_iff]
    · rw [Function.extend_apply' _ _ _ hv, zero_add]
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
      have h1 : S.ι p.1 ≠ v := fun h => hv ⟨_, h⟩
      have h2 : S.ι (lastOf p.1 p.2) ≠ v := fun h => hv ⟨_, h⟩
      simp [h1, h2]

/-- The seed rows `x, ι p, y` of the pairs. -/
theorem seed_pairs : ∀ P : List (V × V), (∀ p ∈ P, p ∈ S.prs) →
    (P.flatMap (fun p => [p.1, p.2])).Nodup →
    Ach (img S.ι (ofSym seedE) ∪
        {e | ∃ v ∈ P.flatMap (fun p => [p.1, p.2]), e = s(v, S.ι (ptc (S.ty v)))})
      (fun v => Function.extend S.ι c1 (fun _ => 0) v + (P.flatMap (fun p => [p.1, p.2])).count v)
  | [], _, _ => S.seed_core.congr (by ext; simp) (fun v => by simp)
  | p :: P, hP, hnd => by
    have hp := S.prs_nc p (hP p (by simp))
    have hnd' := hnd
    rw [List.flatMap_cons, List.nodup_append] at hnd'
    have hxy : p.1 ≠ p.2 := by
      have := hnd'.1
      simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
        List.nodup_nil, and_self, and_true] at this
      exact this
    have hfree : ∀ u ∈ [p.1, p.2], u ∉ P.flatMap (fun p => [p.1, p.2]) :=
      fun u hu hu' => hnd'.2.2 u hu u hu' rfl
    have ih := seed_pairs P (fun q hq => hP q (by simp [hq])) hnd'.2.1
    have hpx : p.1 ≠ S.ι (ptc (S.ty p.1)) := nc_ne_iota hp.1 _
    have hpy : S.ι (ptc (S.ty p.1)) ≠ p.2 := (nc_ne_iota hp.2.1 _).symm
    have h := ih.addPath p.1 [S.ι (ptc (S.ty p.1)), p.2] (by simp)
      (by simp [hpx, hpy, hxy])
      (by
        intro e he hmem
        simp only [lEdges_cons, lEdges_nil, List.mem_cons, List.mem_singleton,
          List.not_mem_nil, or_false] at he
        rcases hmem with ⟨a, b, -, hab⟩ | ⟨u, hu, hue⟩
        · rcases he with rfl | rfl
          · rcases Sym2.eq_iff.mp hab with ⟨h1, -⟩ | ⟨h1, -⟩
            · exact hp.1 ⟨a, h1.symm⟩
            · exact hp.1 ⟨b, h1.symm⟩
          · rcases Sym2.eq_iff.mp hab with ⟨-, h1⟩ | ⟨-, h1⟩
            · exact hp.2.1 ⟨b, h1.symm⟩
            · exact hp.2.1 ⟨a, h1.symm⟩
        · have hunc : S.nc u := by
            obtain ⟨q, hq, hq'⟩ := List.mem_flatMap.mp hu
            have := S.prs_nc q (hP q (by simp [hq]))
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hq'
            rcases hq' with rfl | rfl
            · exact this.1
            · exact this.2.1
          rcases he with rfl | rfl
          · rcases Sym2.eq_iff.mp hue with ⟨h1, -⟩ | ⟨h1, -⟩
            · exact hfree p.1 (by simp) (h1 ▸ hu)
            · exact hp.1 ⟨_, h1.symm⟩
          · rcases Sym2.eq_iff.mp hue with ⟨h1, -⟩ | ⟨-, h1⟩
            · exact hunc ⟨_, h1⟩
            · exact hfree p.2 (by simp) (h1 ▸ hu))
    refine h.congr ?_ ?_
    · ext e
      simp only [Set.mem_union, Set.mem_ofPred_eq, lEdges_cons, lEdges_nil, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false, List.flatMap_cons, List.mem_append]
      constructor
      · rintro ((h | ⟨u, hu, rfl⟩) | (rfl | rfl))
        · exact Or.inl h
        · exact Or.inr ⟨u, Or.inr hu, rfl⟩
        · exact Or.inr ⟨p.1, Or.inl (Or.inl rfl), rfl⟩
        · exact Or.inr ⟨p.2, Or.inl (Or.inr rfl), by rw [Sym2.eq_swap, hp.2.2]⟩
      · rintro (h | ⟨u, (rfl | rfl) | hu, rfl⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (by rw [Sym2.eq_swap, hp.2.2]))
        · exact Or.inl (Or.inr ⟨u, hu, rfl⟩)
    · intro v
      have hc : (List.flatMap (fun p => [p.1, p.2]) (p :: P)).count v =
          (List.flatMap (fun p => [p.1, p.2]) P).count v +
            ((if p.1 = v then 1 else 0) + (if p.2 = v then 1 else 0)) := by
        rw [List.flatMap_cons, List.count_append]
        simp only [List.count_cons, List.count_nil, beq_iff_eq]
        omega
      simp only [lastOf_cons, lastOf_nil]
      rw [hc]
      by_cases h1 : p.1 = v <;> by_cases h2 : p.2 = v <;> simp [h1, h2] <;> omega

/-- The initial partition: five seed paths and one row per pair. -/
theorem seed : Ach (img S.ι (ofSym seedE) ∪ S.seedP) (S.B c1) := by
  have hmem : ∀ u ∈ S.prs.flatMap (fun p => [p.1, p.2]), S.nc u := by
    intro u hu
    obtain ⟨q, hq, hq'⟩ := List.mem_flatMap.mp hu
    have := S.prs_nc q hq
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl
    · exact this.1
    · exact this.2.1
  have hcov : ∀ u, S.nc u → u ∈ S.prs.flatMap (fun p => [p.1, p.2]) := by
    intro u hu
    obtain ⟨p, hp, hup⟩ := S.prs_cover u hu
    exact List.mem_flatMap.mpr ⟨p, hp, by rcases hup with rfl | rfl <;> simp⟩
  have h := S.seed_pairs S.prs (fun p hp => hp) S.prs_nodup
  refine h.congr ?_ ?_
  · ext e
    simp only [Set.mem_union, Set.mem_ofPred_eq, seedP]
    constructor
    · rintro (h | ⟨u, hu, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨u, hmem u hu, rfl⟩
    · rintro (h | ⟨u, hu, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨u, hcov u hu, rfl⟩
  · intro v
    by_cases hv : v ∈ Set.range S.ι
    · obtain ⟨a, rfl⟩ := hv
      rw [S.inj.extend_apply, B_iota, List.count_eq_zero.mpr (fun h => hmem _ h ⟨a, rfl⟩),
        Nat.add_zero]
    · rw [Function.extend_apply' _ _ _ hv, B_nc c1 hv,
        List.count_eq_one_of_mem S.prs_nodup (hcov v hv)]

/-! ### Inserting the exterior graph (Lemma 3) -/

theorem fdeg_Fset (v : V) (hv : ¬ S.cl v) :
    fdeg S.Fset v = {w | S.G.Adj v w ∧ ¬ S.cl w}.ncard := by
  classical
  unfold fdeg
  have : S.Fset.filter (fun e => v ∈ e) =
      (Finset.univ.filter (fun w => S.G.Adj v w ∧ ¬ S.cl w)).image (fun w => s(v, w)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, mem_Fset]
    constructor
    · rintro ⟨⟨he, hcl⟩, hve⟩
      obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hve
      exact ⟨w, ⟨he, hcl w (Sym2.mem_mk_right _ _)⟩, rfl⟩
    · rintro ⟨w, ⟨hadj, hw⟩, rfl⟩
      refine ⟨⟨hadj, ?_⟩, Sym2.mem_mk_left _ _⟩
      intro u hu
      rcases Sym2.mem_iff.mp hu with rfl | rfl
      · exact hv
      · exact hw
  rw [this, Finset.card_image_of_injective]
  · rw [← Set.ncard_coe_finset, Finset.coe_filter]
    simp
  · intro w w' h
    rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1

theorem Fset_even (v : V) : Even (fdeg S.Fset v) := by
  classical
  by_cases hv : S.cl v
  · have : S.Fset.filter (fun e => v ∈ e) = ∅ := by
      ext e
      simp only [Finset.mem_filter, mem_Fset, Finset.notMem_empty, iff_false, not_and]
      intro ⟨_, hcl⟩ hve
      exact hcl v hve hv
    unfold fdeg
    rw [this]
    exact ⟨0, rfl⟩
  · rw [S.fdeg_Fset v hv]
    exact S.ext_even v hv

/-- After Lemma 3: the seed plus the whole exterior graph. -/
theorem after_F : Ach (S.St seedE (S.Ast 0)) (S.B c1) := by
  have hcl : ∀ i : Fin 12, i.val < 6 → S.cl (S.ι i) := fun i hi => cl_iota.mpr hi
  have h := S.seed.insert_even {v | ¬ S.cl v}
    (by
      intro v hv w hw hmem
      rcases hmem with ⟨a, b, hab, he⟩ | ⟨x, -, he⟩
      · simp only [ofSym, decide_eq_true_eq] at hab
        rcases seedE_clique a b hab with h | h
        · rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨-, h1⟩
          · exact hv (h1 ▸ hcl a h)
          · exact hw (h1 ▸ hcl a h)
        · rcases Sym2.eq_iff.mp he with ⟨-, h1⟩ | ⟨h1, -⟩
          · exact hw (h1 ▸ hcl b h)
          · exact hv (h1 ▸ hcl b h)
      · rcases Sym2.eq_iff.mp he with ⟨-, h1⟩ | ⟨h1, -⟩
        · exact hw (h1 ▸ hcl _ (ptc_lt _))
        · exact hv (h1 ▸ hcl _ (ptc_lt _)))
    (by
      intro v hv
      by_cases hvr : v ∈ Set.range S.ι
      · obtain ⟨a, rfl⟩ := hvr
        have ha : ¬ a.val < 6 := fun h => hv (hcl a h)
        rw [B_iota, c1_rep a (by omega)]
      · rw [B_nc c1 hvr])
    (by
      intro v hv
      by_cases hvr : v ∈ Set.range S.ι
      · obtain ⟨r, rfl⟩ := hvr
        have hr : ¬ r.val < 6 := fun h => hv (hcl r h)
        refine (blankNbrs_le_mblank S.ι S.inj (cupS seedE) c1 r (B_iota c1) (B_pos c1) ?_).trans
          (seed_rep_blank r (by omega))
        intro a har hmem
        rcases hmem with ⟨c, d, hcd, he⟩ | ⟨x, hx, he⟩
        · simp only [cupS, Bool.or_eq_true]
          left
          simp only [ofSym, decide_eq_true_eq] at hcd ⊢
          rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [S.inj h1, S.inj h2]; exact hcd
          · rw [S.inj h1, S.inj h2, Sym2.eq_swap]; exact hcd
        · exfalso
          rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨-, h1⟩
          · exact hx ⟨r, h1⟩
          · exact hx ⟨a, h1⟩
      · -- a non-representative sees only its seed vertex
        refine (blankNbrs_le_of_subset (S := {S.ι (ptc (S.ty v))}) ?_).trans
          (by rw [Set.ncard_singleton])
        intro w hw _ _
        rcases hw with ⟨c, d, -, he⟩ | ⟨x, hx, he⟩
        · rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact absurd ⟨c, h1.symm⟩ hvr
          · exact absurd ⟨d, h1.symm⟩ hvr
        · rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, -⟩
          · subst h1; exact h2
          · exact absurd ⟨_, h1.symm⟩ hvr)
    S.Fset (fun e he => S.G.not_isDiag_of_mem_edgeSet (mem_Fset.mp he).1) S.Fset_even
    (fun e he v hve => (mem_Fset.mp he).2 v hve)
  refine h.congr ?_ (fun _ => rfl)
  have hA0 : S.PS (S.Ast 0) = ∅ := by
    ext e
    simp only [PS, Ast, Set.mem_ofPred_eq, Nat.not_lt_zero, and_false, false_and,
      exists_false, Set.mem_empty_iff_false]
  unfold St
  rw [hA0, Set.union_empty]

/-! ### The whole construction -/

/-- The edge set of the end result is `E(G)`. -/
theorem final_edges :
    fromEdgeSet (S.St E4 (S.Ast 3) ∪ {e | ∃ x ∈ lEdges (0 : Fin 12) [5, 1, 2, 4, 3], e = x.map S.ι})
      = S.G := by
  have hcl : ∀ i : Fin 12, i.val < 6 → S.cl (S.ι i) := fun i hi => cl_iota.mpr hi
  -- core edges of the result are edges of `G`
  have hcore : ∀ a b : Fin 12, s(a, b) ∈ E4 ++ finalE → S.G.Adj (S.ι a) (S.ι b) := by
    intro a b hab
    rcases core_sound a b hab with ⟨ha, hb, hne⟩ | ⟨ha, hb, hne⟩ | ⟨hb, ha, hne⟩
    · exact S.adj_cc a b ha hb hne
    · have hnc : ¬ S.cl (S.ι b) := fun h => by rw [cl_iota] at h; omega
      refine (S.adj_ext _ hnc a ha |>.mpr ?_).symm
      rw [S.ty_rep b hb]; omega
    · have hnc : ¬ S.cl (S.ι a) := fun h => by rw [cl_iota] at h; omega
      refine S.adj_ext _ hnc b hb |>.mpr ?_
      rw [S.ty_rep a ha]; omega
  ext v w
  rw [fromEdgeSet_adj]
  constructor
  · rintro ⟨hm, hvw⟩
    rw [← mem_edgeSet]
    rcases hm with (((⟨a, b, hab, he⟩ | ⟨x, hx, he⟩) | hm) | ⟨x, -, k, -, hadj, he⟩) | ⟨y, hy, he⟩
    · rw [he]
      simp only [ofSym, decide_eq_true_eq] at hab
      exact hcore a b (List.mem_append_left _ hab)
    · rw [he]
      exact (S.adj_ext x (nc_not_cl hx) _ (ptc_lt _)).mpr (ptc_ne _)
    · exact (mem_Fset.mp hm).1
    · rw [he]; exact hadj
    · rw [he]
      induction y using Sym2.ind with
      | _ a b => exact hcore a b (List.mem_append_right _ hy)
  · intro hadj
    refine ⟨?_, hadj.ne⟩
    -- the clique–exterior case, in one orientation
    have hspoke : ∀ u k, ¬ S.cl u → k.val < 6 → S.G.Adj u (S.ι k) →
        s(u, S.ι k) ∈ S.St E4 (S.Ast 3) ∪
          {e | ∃ x ∈ lEdges (0 : Fin 12) [5, 1, 2, 4, 3], e = x.map S.ι} := by
      intro u k hu hk hadj
      by_cases hur : u ∈ Set.range S.ι
      · obtain ⟨r, rfl⟩ := hur
        have hr : ¬ r.val < 6 := fun h => hu (hcl r h)
        have hkr : k.val ≠ (S.ty (S.ι r)).val := (S.adj_ext _ hu k hk).mp hadj
        rw [S.ty_rep r (by omega)] at hkr
        have hm := core_complete k r (Or.inr ⟨hk, by omega, by omega⟩)
        rw [List.mem_append] at hm
        rcases hm with hm | hm
        · left; left; left; left
          exact ⟨r, k, by simp only [ofSym, decide_eq_true_eq]; rwa [Sym2.eq_swap], rfl⟩
        · right
          exact ⟨s(k, r), hm, by simp [Sym2.eq_swap]⟩
      · left; right
        exact ⟨u, ⟨hur, by have := (S.ty u).isLt; omega⟩, k, hk, hadj, rfl⟩
    by_cases hv : S.cl v <;> by_cases hw : S.cl w
    · obtain ⟨a, ha, rfl⟩ := hv
      obtain ⟨b, hb, rfl⟩ := hw
      have hm := core_complete a b (Or.inl ⟨ha, hb, fun h => hadj.ne (h ▸ rfl)⟩)
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · left; left; left; left
        exact ⟨a, b, by simpa only [ofSym, decide_eq_true_eq] using hm, rfl⟩
      · right
        exact ⟨s(a, b), hm, rfl⟩
    · obtain ⟨a, ha, rfl⟩ := hv
      rw [Sym2.eq_swap]
      exact hspoke w a hw ha hadj.symm
    · obtain ⟨b, hb, rfl⟩ := hw
      exact hspoke v b hv hb hadj
    · left; left; right
      exact mem_Fset.mpr ⟨hadj, fun u hu => by rcases Sym2.mem_iff.mp hu with rfl | rfl <;> assumption⟩

/-- **The construction**: a decomposition of `G` with end vector `B cfin`. -/
theorem main : ∃ D : PathDecomp S.G, ∀ v, D.ends v = S.B cfin v := by
  have hA : ∀ s, ∀ v ∈ S.Ast s, S.nc v := fun _ _ hv => hv.1
  have h0 := S.after_F
  have h1 := S.stage 0 (fun h hs => by have := pair_ok h; rw [hs] at this; exact this) h0
  have h2 := S.segment (hA 1) seg1 seg1_ok h1
  have h3 := S.stage 1 (fun h hs => by have := pair_ok h; rw [hs] at this; exact this) h2
  have h4 := S.segment (hA 2) seg2 seg2_ok h3
  have h5 := S.stage 2 (fun h hs => by have := pair_ok h; rw [hs] at this; exact this) h4
  have h6 := S.segment (hA 3) seg3 seg3_ok h5
  have h7 := h6.addMapPath S.ι S.inj 0 [5, 1, 2, 4, 3] (by simp) finalE_ok
    (by
      intro x hx hmem
      induction x using Sym2.ind with
      | _ a b =>
        have hab : a ≠ b := fun h => lEdges_not_diag finalE_ok hx (by simp [h])
        have := core_mem (hA 3) hab hmem
        exact Bool.false_ne_true ((finalE_new a b hx).symm.trans this))
  rw [show E3 ++ segE seg3 = E4 from rfl] at h7
  unfold Ach at h7
  rw [final_edges] at h7
  obtain ⟨D, hD⟩ := h7
  refine ⟨D, fun v => ?_⟩
  rw [hD v]
  dsimp only
  by_cases hv : v ∈ Set.range S.ι
  · obtain ⟨a, rfl⟩ := hv
    rw [B_iota, B_iota, ← final_ends a]
    simp only [S.inj.eq_iff]
    rfl
  · rw [B_nc _ hv, B_nc _ hv]
    have h1 : S.ι 0 ≠ v := fun h => hv ⟨0, h⟩
    have h2 : S.ι 3 ≠ v := fun h => hv ⟨_, h⟩
    simp [h1, h2]

end SixData

end Gallai
