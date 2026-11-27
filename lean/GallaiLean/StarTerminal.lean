import GallaiLean.Separator

/-!
# Star-terminal decompositions and the deletion tests (session `claude/stl`)

Manuscript: `manuscripts/stl/stl.tex`.

Let `z` be a vertex of `J` and `D` a path decomposition of `J` in which `z` is an end of no path.
`D` is **star-terminal at `z`** (`StarAt D z`) if every path through `z` has `z` as its second
(or second-to-last) vertex, i.e. one of its two edges at `z` joins `z` to an end of the path.
Deleting `z` then cuts each path through `z` into at most one non-trivial piece, so the library's
projection lemma applies (`star_delete`). A path `x z y ⋯` loses its *short side* `xz` and keeps
its *long side* `y ⋯`; the neighbour `y` gains an end and `x` loses one.

* `delVertRetract`: `J − z` as a retract of `J`.
* **`star_delete`**: the decomposition of `J − z` with the exact end count
  `ends' v + Σ_P c_P [incid_P v = 1] = ends v + Σ_P c_P [incid_P v = 2]`, where `c_P` counts the
  edge `vz` on `P`, and with one path fewer for each path of `D` all of whose edges contain `z`.
* **`test1_of_stl`**: if `z` is the only even vertex and, for every `r ∈ N(z)`, some
  star-terminal Lovász decomposition of `J` has `r` on a long side or has a path `x z y` of
  length two, then `Test1 J z` holds (neighbours of degree `≥ 3`).
* **`test2_of_stl2`**: the analogue for two adjacent even vertices `z, r`: a star-terminal
  decomposition with `b(z) = 0`, `b(r) ∈ {0, 2}` and one end elsewhere, with `b(r) = 0`, or `r` long,
  or a path of length two through `z`, gives `Test2` at `(z, r)`.
* **`gallai_of_stl`**: STL and STL2 on every three-connected `J` imply Gallai's conjecture.
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u} [DecidableEq V] {J : SimpleGraph V}

/-! ### `J − z` as a retract -/

/-- `J − z` is the subgraph of `J` induced by the kept vertices `≠ z`; `o` is any vertex of
`J − z`, the image of `z` under the retraction. -/
def delVertRetract (J : SimpleGraph V) (z : V) (o : {v | v ≠ z}) : Retract J (delVert J z) where
  ι := Subtype.val
  f := fun x => if h : x = z then o else ⟨x, h⟩
  kept := fun x => decide (x ≠ z)
  f_ι a := by
    have h : (a : V) ≠ z := a.2
    simp [h]
  kept_iff x := by
    constructor
    · intro h; exact ⟨⟨x, by simpa using h⟩, rfl⟩
    · rintro ⟨a, rfl⟩; exact decide_eq_true a.2
  adj_iff _ _ := Iff.rfl

/-! ### Star-terminal decompositions -/

/-- `D` is **star-terminal at `z`**: every path through `z` contains the edge from `z` to one of
its ends. (When `z` is an end of no path, this says that `z` is the second vertex of the path,
read from a suitable end.) -/
def StarAt (D : PathDecomp J) (z : V) : Prop :=
  ∀ P ∈ D.paths, z ∈ P.walk.support → s(P.src, z) ∈ P.edges ∨ s(P.tgt, z) ∈ P.edges

/-- The neighbour `r` of `z` is on a **long side**: the path through the edge `zr` does not end at
`r`. -/
def LongAt (D : PathDecomp J) (z r : V) : Prop :=
  ∃ P ∈ D.paths, s(z, r) ∈ P.edges ∧ P.src ≠ r ∧ P.tgt ≠ r

/-- Some path of `D` consists of edges at `z` only (a path `x z y` of length two). -/
def HasShortShort (D : PathDecomp J) (z : V) : Prop :=
  ∃ P ∈ D.paths, ∀ e ∈ P.edges, z ∈ e

section piece

/-- A path that starts `x z ⋯` (with `z` not an end) has a piece in `J − z`: the rest after `z`. -/
theorem hasPiece_of_second (z : V) (o : {v | v ≠ z}) (P : GPath J)
    (hsrc : P.src ≠ z) (htgt : P.tgt ≠ z) (he : s(P.src, z) ∈ P.edges) :
    HasPiece (delVert J z) (delVertRetract J z o).f (bothKept (delVertRetract J z o).kept) P := by
  set R := delVertRetract J z o with hR
  obtain ⟨s, t, w, hw, hpos⟩ := P
  simp only at hsrc htgt he ⊢
  cases w with
  | nil => simp at hpos
  | @cons _ c _ h q =>
    rw [Walk.cons_isPath_iff] at hw
    have hcz : c = z := by
      simp only [GPath.edges, Walk.edges_cons, List.mem_cons] at he
      rcases he with he | he
      · rcases Sym2.eq_iff.mp he with ⟨-, h2⟩ | ⟨-, h2⟩
        · exact h2.symm
        · exact absurd h2.symm hsrc
      · exact absurd (q.fst_mem_support_of_mem_edges he) hw.2
    subst hcz
    cases q with
    | nil => exact absurd rfl htgt
    | @cons _ d _ h2 q' =>
      have hq := hw.1
      rw [Walk.cons_isPath_iff] at hq
      have hsupp : ∀ x ∈ q'.support, R.kept x = true := by
        intro x hx
        simp only [hR, delVertRetract, decide_eq_true_eq]
        rintro rfl
        exact hq.2 hx
      refine R.hasPiece_of_core q' hq.1 hsupp ?_
      simp only [GPath.edges, Walk.edges_cons, List.filter_cons]
      have h1 : bothKept R.kept s(s, c) = false := by simp [hR, delVertRetract]
      have h2' : bothKept R.kept s(c, d) = false := by simp [hR, delVertRetract]
      rw [h1, h2']
      simp only [Bool.false_eq_true, ite_false]
      rw [filter_bothKept_of_kept R.kept q' hsupp]

end piece

/-! ### Deleting `z` from a star-terminal decomposition -/

variable [Fintype V] [DecidableRel J.Adj]

/-- Number of copies of the edge `vz` on `P` (`0` or `1`). -/
def zc (z v : V) (P : GPath J) : ℕ := P.edges.count s(v, z)

omit [Fintype V] [DecidableRel J.Adj] in
theorem zc_le_one (D : PathDecomp J) (z v : V) {P : GPath J} (hP : P ∈ D.paths) : zc z v P ≤ 1 := by
  have h := D.sum_count_le_one s(v, z)
  exact (List.le_sum_of_mem (List.mem_map_of_mem (f := fun P => P.edges.count s(v, z)) hP)).trans h

omit [Fintype V] [DecidableRel J.Adj] in
theorem sum_zc (D : PathDecomp J) {z v : V} (hadj : J.Adj v z) :
    (D.paths.map (zc z v)).sum = 1 := by
  have h1 : (D.paths.map (zc z v)).sum = (D.paths.flatMap GPath.edges).count s(v, z) := by
    rw [List.count_flatMap]; rfl
  rw [h1]
  have hmem : s(v, z) ∈ D.paths.flatMap GPath.edges := (D.covers _).1 hadj
  have hle := List.nodup_iff_count_le_one.mp D.nodup_edges s(v, z)
  have hpos := List.count_pos_iff.mpr hmem
  omega

omit [Fintype V] [DecidableRel J.Adj] in
/-- **Deleting `z`.** If `z` is an end of no path and `D` is star-terminal at `z`, then `J − z`
has a decomposition `D'` with at most one path for each path of `D` that has an edge avoiding
`z`, and with, at every `v ≠ z`,
`ends' v + Σ_P zc_P [incid_P v = 1] = ends v + Σ_P zc_P [incid_P v = 2]`. -/
theorem star_delete (D : PathDecomp J) (z : V) (o : {v | v ≠ z})
    (hend : ∀ P ∈ D.paths, P.src ≠ z ∧ P.tgt ≠ z) (hstar : StarAt D z) :
    ∃ D' : PathDecomp (delVert J z),
      D'.size + D.paths.countP (fun P => P.edges.all (fun e => decide (z ∈ e))) ≤ D.size ∧
      ∀ v : {v | v ≠ z},
        D'.ends v + (D.paths.map (fun P => zc z v.1 P * (if P.incid v.1 = 1 then 1 else 0))).sum =
          D.ends v.1 + (D.paths.map (fun P => zc z v.1 P * (if P.incid v.1 = 2 then 1 else 0))).sum := by
  set R := delVertRetract J z o with hR
  have hpiece : ∀ P ∈ D.paths, HasPiece (delVert J z) R.f (bothKept R.kept) P := by
    intro P hP
    obtain ⟨hs, ht⟩ := hend P hP
    by_cases hz : z ∈ P.walk.support
    · rcases hstar P hP hz with he | he
      · exact hasPiece_of_second z o P hs ht he
      · apply HasPiece.of_reverse
        refine hasPiece_of_second z o P.reverse ht hs ?_
        simpa [GPath.reverse, GPath.edges, Walk.edges_reverse] using he
    · refine R.hasPiece P (fun x hx hk => ?_)
      simp only [hR, delVertRetract, decide_eq_false_iff_not, not_not] at hk
      subst hk; exact absurd hx hz
  obtain ⟨D', hsize, -, hends⟩ := D.project_full R.f (bothKept R.kept) _ R.injOn R.hT R.hcov hpiece
  refine ⟨D', ?_, fun v => ?_⟩
  · -- size: a path with no kept edge has all its edges at `z`
    have hc : ∀ l : List (GPath J), l.countP (fun P => P.edges.any (bothKept R.kept)) +
        l.countP (fun P => P.edges.all (fun e => decide (z ∈ e))) ≤ l.length := by
      intro l
      induction l with
      | nil => simp
      | cons P l ih =>
        simp only [List.countP_cons, List.length_cons]
        have hex : ¬ (P.edges.any (bothKept R.kept) = true ∧
            P.edges.all (fun e => decide (z ∈ e)) = true) := by
          rintro ⟨h1, h2⟩
          obtain ⟨e, he, hk⟩ := List.any_eq_true.mp h1
          have hz := List.all_eq_true.mp h2 e he
          simp only [decide_eq_true_eq] at hz
          have := (bothKept_iff _ e).1 hk z hz
          simp [hR, delVertRetract] at this
        split_ifs with h1 h2 h2
        · exact absurd ⟨h1, h2⟩ hex
        · omega
        · omega
        · omega
    have := hc D.paths
    simp only [PathDecomp.size] at hsize ⊢
    omega
  · -- ends
    have hkc : ∀ P : GPath J, ((P.edges.filter (bothKept R.kept)).map (Sym2.map R.f)).countP
        (fun e => decide (v ∈ e)) + zc z v.1 P = P.incid v.1 := by
      intro P
      have h := R.count_split v P.edges
      have h2 : (P.edges.filter (fun e => !bothKept R.kept e)).countP (fun e => decide (R.ι v ∈ e)) =
          zc z v.1 P := by
        unfold zc
        rw [List.countP_filter, List.count]
        apply List.countP_congr
        intro e he
        have heJ := P.walk.edges_subset_edgeSet he
        induction e using Sym2.inductionOn with
        | hf a b =>
        have hab : a ≠ b := J.ne_of_adj heJ
        have hv : (v : V) ≠ z := v.2
        have hk : ∀ x, R.kept x = decide (x ≠ z) := fun _ => rfl
        have hι : R.ι v = (v : V) := rfl
        simp only [bothKept_mk, hk, hι, beq_iff_eq]
        have hL : ∀ x y : V, (v : V) ∉ s(x, y) → s(x, y) ≠ s((v : V), z) →
            ((decide ((v : V) ∈ s(x, y)) && !(decide (x ≠ z) && decide (y ≠ z))) = true ↔
              s(x, y) = s((v : V), z)) := by
          intro x y h1 h2; simp [h1, h2]
        by_cases ha : a = z
        · rw [ha]
          by_cases hb : b = v
          · rw [hb]; simp [Sym2.eq_swap, hv]
          · apply hL
            · rw [Sym2.mem_iff]; rintro (h | h)
              · exact hv h
              · exact hb h.symm
            · intro h
              rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
              · exact hv h1.symm
              · exact hb h2
        · by_cases hb : b = z
          · rw [hb]
            by_cases ha' : a = v
            · rw [ha']; simp [hv]
            · apply hL
              · rw [Sym2.mem_iff]; rintro (h | h)
                · exact ha' h.symm
                · exact hv h
              · intro h
                rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
                · exact ha' h1
                · exact hv h2.symm
          · have hne : ¬ (s(a, b) = s((v : V), z)) := by
              intro h
              rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
              · exact hb h2
              · exact ha h1
            simp [ha, hb, hne]
      rw [h2] at h
      rw [List.countP_map]
      exact h
    have hpt : ∀ P ∈ D.paths,
        (if ((P.edges.filter (bothKept R.kept)).map (Sym2.map R.f)).countP
            (fun e => decide (v ∈ e)) = 1 then 1 else 0) +
          zc z v.1 P * (if P.incid v.1 = 1 then 1 else 0) =
        P.endsAt v.1 + zc z v.1 P * (if P.incid v.1 = 2 then 1 else 0) := by
      intro P hP
      have h1 := hkc P
      have h2 := zc_le_one D z v.1 hP
      have h3 := P.incid_add_endsAt v.1
      have h4 := P.endsAt_eq_ite v.1
      have h5 : zc z v.1 P ≤ P.incid v.1 := by
        unfold zc GPath.incid
        rw [List.count]
        apply List.countP_mono_left
        intro e _ he
        simp only [beq_iff_eq] at he
        subst he
        simp
      generalize ((P.edges.filter (bothKept R.kept)).map (Sym2.map R.f)).countP
        (fun e => decide (v ∈ e)) = k at h1 ⊢
      generalize zc z v.1 P = c at h1 h2 h5 ⊢
      generalize P.incid v.1 = i at h1 h3 h4 h5 ⊢
      generalize P.endsAt v.1 = e at h3 h4 ⊢
      split_ifs at h3 h4 ⊢ <;> omega
    rw [hends v]
    unfold PathDecomp.ends
    rw [← sum_map_add', ← sum_map_add']
    exact congrArg List.sum (List.map_congr_left hpt)

/-! ### Counting at a neighbour of `z` -/

omit [Fintype V] [DecidableRel J.Adj] in
theorem not_end_of_ends_zero (D : PathDecomp J) {z : V} (h : D.ends z = 0) :
    ∀ P ∈ D.paths, P.src ≠ z ∧ P.tgt ≠ z := by
  intro P hP
  have h1 := List.le_sum_of_mem (List.mem_map_of_mem (f := fun P => P.endsAt z) hP)
  unfold PathDecomp.ends at h
  rw [h] at h1
  unfold GPath.endsAt at h1
  constructor <;> intro hc <;> simp [hc] at h1

omit [Fintype V] [DecidableRel J.Adj] in
/-- The three facts used at a neighbour `r` of `z`: with `c_P = zc z r P` and `i_P = incid_P r`,
`Σ c[i=1] + Σ c[i=2] = 1` and `Σ c[i=1] ≤ ends r`. -/
theorem zc_sums (D : PathDecomp J) {z r : V} (hadj : J.Adj r z) :
    (D.paths.map (fun P => zc z r P * (if P.incid r = 1 then 1 else 0))).sum +
      (D.paths.map (fun P => zc z r P * (if P.incid r = 2 then 1 else 0))).sum = 1 ∧
    (D.paths.map (fun P => zc z r P * (if P.incid r = 1 then 1 else 0))).sum ≤ D.ends r := by
  have hpos : ∀ P : GPath J, zc z r P ≤ P.incid r := by
    intro P
    unfold zc GPath.incid
    rw [List.count]
    apply List.countP_mono_left
    intro e _ he
    simp only [beq_iff_eq] at he
    subst he
    simp
  constructor
  · rw [← sum_map_add']
    have hm : D.paths.map (fun P => zc z r P * (if P.incid r = 1 then 1 else 0) +
        zc z r P * (if P.incid r = 2 then 1 else 0)) = D.paths.map (zc z r) := by
      apply List.map_congr_left
      intro P hP
      have h1 := zc_le_one D z r hP
      have h2 := hpos P
      have h3 := P.incid_add_endsAt r
      simp only [zc] at h1 h2 ⊢
      generalize P.edges.count s(r, z) = c at h1 h2 ⊢
      generalize P.incid r = i at h2 h3 ⊢
      split_ifs at h3 ⊢ <;> omega
    rw [hm]
    exact sum_zc D hadj
  · unfold PathDecomp.ends
    apply sum_map_le_sum_map
    intro P hP
    have h1 := zc_le_one D z r hP
    have h4 := P.endsAt_eq_ite r
    simp only [zc] at h1 ⊢
    generalize P.edges.count s(r, z) = c at h1 ⊢
    split_ifs at h4 ⊢ <;> omega

omit [Fintype V] [DecidableRel J.Adj] in
/-- If `r` is on a long side, the path through `zr` contributes to `Σ c[i=2]`. -/
theorem one_le_of_longAt (D : PathDecomp J) {z r : V} (hL : LongAt D z r) :
    1 ≤ (D.paths.map (fun P => zc z r P * (if P.incid r = 2 then 1 else 0))).sum := by
  obtain ⟨P, hP, he, hs, ht⟩ := hL
  have hi : P.incid r = 2 :=
    P.incid_of_internal (Walk.mem_support_of_mem_edge P.walk he (Sym2.mem_mk_right _ _)) hs ht
  have hc : 1 ≤ zc z r P := by
    unfold zc
    rw [Sym2.eq_swap] at he
    exact List.count_pos_iff.mpr he
  refine le_trans ?_ (List.le_sum_of_mem (List.mem_map_of_mem
    (f := fun P => zc z r P * (if P.incid r = 2 then 1 else 0)) hP))
  simp only [hi, ite_true, mul_one]
  exact hc

/-! ### The two tests -/

/-- **STL(r)**: a star-terminal Lovász decomposition of `J` in which `r` is on a long side or some
path through `z` has length two. -/
def STL (J : SimpleGraph V) [DecidableRel J.Adj] (z r : V) : Prop :=
  ∃ D : PathDecomp J, (∀ v, D.ends v = J.degree v % 2) ∧ StarAt D z ∧
    (LongAt D z r ∨ HasShortShort D z)

/-- **STL2(z, r)**: a star-terminal decomposition with `b(z) = 0`, one end at every other vertex
except `r`, `b(r) ∈ {0, 2}`, and `b(r) = 0`, or `r` on a long side, or a path of length two. -/
def STL2 (J : SimpleGraph V) [DecidableRel J.Adj] (z r : V) : Prop :=
  ∃ D : PathDecomp J, (∀ v, v ≠ r → D.ends v = J.degree v % 2) ∧ (D.ends r = 0 ∨ D.ends r = 2) ∧
    StarAt D z ∧ (D.ends r = 0 ∨ LongAt D z r ∨ HasShortShort D z)

omit [Fintype V] [DecidableRel J.Adj] in
theorem countP_all_pos (D : PathDecomp J) {z : V} (h : HasShortShort D z) :
    1 ≤ D.paths.countP (fun P => P.edges.all (fun e => decide (z ∈ e))) := by
  obtain ⟨P, hP, hall⟩ := h
  exact List.countP_pos_iff.mpr ⟨P, hP, List.all_eq_true.mpr (fun e he => by simpa using hall e he)⟩

/-- **STL ⇒ Test1.** If every neighbour of `z` has degree `≥ 3` and STL holds at every neighbour
whenever `z` is the only even vertex, then `Test1 J z`. -/
theorem test1_of_stl (z : V) (hdeg : ∀ r, J.Adj z r → 3 ≤ J.degree r)
    (h : (∀ v, Even (J.degree v) ↔ v = z) → ∀ r, J.Adj z r → STL J z r) : Test1 J z := by
  intro hz r hr
  obtain ⟨D, hD, hst, hc⟩ := h hz r hr
  have hrz : r ≠ z := hr.ne'
  let r' : {v | v ≠ z} := ⟨r, hrz⟩
  have hpar : ∀ v, J.degree v % 2 = if v = z then 0 else 1 := by
    intro v
    split_ifs with hv
    · exact Nat.even_iff.mp ((hz v).2 hv)
    · have : ¬ Even (J.degree v) := fun he => hv ((hz v).1 he)
      rw [Nat.not_even_iff] at this; exact this
  have hDz : D.ends z = 0 := by rw [hD z, hpar z]; simp
  obtain ⟨D', hsz, hends⟩ := star_delete D z r' (not_end_of_ends_zero D hDz) hst
  -- the size of `D`
  have hc1 : (Finset.univ.filter (fun v : V => v ≠ z)).card = Fintype.card V - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have h2size : 2 * D.size = Fintype.card V - 1 := by
    rw [← D.sum_ends, ← hc1, Finset.card_filter]
    exact Finset.sum_congr rfl (fun v _ => by
      rw [hD v, hpar v]; by_cases hv : v = z <;> simp [hv])
  -- the ends at `r`
  have hDr : D.ends r = 1 := by rw [hD r, hpar r]; simp [hrz]
  obtain ⟨hS, -⟩ := zc_sums D hr.symm
  have hE : D'.ends r' + (D.paths.map (fun P => zc z r P * (if P.incid r = 1 then 1 else 0))).sum =
      D.ends r + (D.paths.map (fun P => zc z r P * (if P.incid r = 2 then 1 else 0))).sum :=
    hends r'
  -- the degree of `r` in `J − z`
  have hdr : (delVert J z).degree r' + 1 = J.degree r := by
    have := delVert_degree (J := J) z r'
    simp only [show J.Adj (r' : V) z from hr.symm, ite_true] at this
    exact this
  have hodd : J.degree r % 2 = 1 := by rw [hpar r]; simp [hrz]
  have h3 := hdeg r hr
  rcases hc with hL | hSS
  · have h1 := one_le_of_longAt D hL
    refine ⟨D', by omega, ?_⟩
    show 2 ≤ D'.ends r'
    omega
  · have h1 := countP_all_pos D hSS
    obtain ⟨D'', h1'', h2''⟩ := exists_two_ends (x := r') D' (k := (Fintype.card V - 1) / 2)
      (by unfold leafCost; split_ifs <;> omega)
      (by rw [Nat.even_iff]; omega) (by omega)
    exact ⟨D'', h1'', h2''⟩

/-- **STL2 ⇒ Test2.** -/
theorem test2_of_stl2 (z : V) (hdeg : ∀ r, J.Adj z r → 3 ≤ J.degree r)
    (h : ∀ r, J.Adj z r → (∀ v, Even (J.degree v) ↔ v = z ∨ v = r) → STL2 J z r) : Test2 J z := by
  intro r hr hzr
  obtain ⟨D, hD, hβ, hst, hc⟩ := h r hr hzr
  have hrz : r ≠ z := hr.ne'
  let r' : {v | v ≠ z} := ⟨r, hrz⟩
  have hpar : ∀ v, J.degree v % 2 = if v = z ∨ v = r then 0 else 1 := by
    intro v
    split_ifs with hv
    · exact Nat.even_iff.mp ((hzr v).2 hv)
    · have : ¬ Even (J.degree v) := fun he => hv ((hzr v).1 he)
      rw [Nat.not_even_iff] at this; exact this
  have hDz : D.ends z = 0 := by rw [hD z (Ne.symm hrz), hpar z]; simp
  obtain ⟨D', hsz, hends⟩ := star_delete D z r' (not_end_of_ends_zero D hDz) hst
  -- the size of `D`
  have hc2 : (Finset.univ.filter (fun v : V => v ≠ z ∧ v ≠ r)).card = Fintype.card V - 2 := by
    rw [show Finset.univ.filter (fun v : V => v ≠ z ∧ v ≠ r) = (Finset.univ.erase z).erase r by
        ext v; simp [and_comm],
      Finset.card_erase_of_mem (by simp [hrz]), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
    omega
  have hpt : ∀ v, D.ends v = (if v = r then D.ends r else 0) + (if v ≠ z ∧ v ≠ r then 1 else 0) := by
    intro v
    by_cases hv : v = r
    · subst hv; simp [hrz]
    · rw [hD v hv, hpar v]
      by_cases hvz : v = z
      · subst hvz; simp [hv]
      · simp [hv, hvz]
  have h2size : 2 * D.size = D.ends r + (Fintype.card V - 2) := by
    rw [← D.sum_ends, Finset.sum_congr rfl (fun v _ => hpt v), Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ r (fun _ => D.ends r), ← Finset.card_filter, hc2]
    simp
  obtain ⟨hS, hS1⟩ := zc_sums D hr.symm
  have hE : D'.ends r' + (D.paths.map (fun P => zc z r P * (if P.incid r = 1 then 1 else 0))).sum =
      D.ends r + (D.paths.map (fun P => zc z r P * (if P.incid r = 2 then 1 else 0))).sum :=
    hends r'
  have hdr : (delVert J z).degree r' + 1 = J.degree r := by
    have := delVert_degree (J := J) z r'
    simp only [show J.Adj (r' : V) z from hr.symm, ite_true] at this
    exact this
  have hev : J.degree r % 2 = 0 := by rw [hpar r]; simp
  have h3 := hdeg r hr
  have hcard : 2 ≤ Fintype.card V := by
    have := Finset.card_le_univ ({z, r} : Finset V)
    rw [Finset.card_pair (Ne.symm hrz)] at this; exact this
  have hodd : Odd ((delVert J z).degree r') := by rw [Nat.odd_iff]; omega
  have h3' : 3 ≤ (delVert J z).degree r' := by omega
  rcases hc with h0 | hL | hSS
  · -- `b(r) = 0`: one end at `r`, split once
    obtain ⟨D'', h1'', h2''⟩ := exists_three_ends (x := r') D' (k := (Fintype.card V - 2) / 2)
      (by omega) hodd h3'
    exact ⟨D'', by omega, h2''⟩
  · have h1 := one_le_of_longAt D hL
    rcases hβ with hβ | hβ
    · obtain ⟨D'', h1'', h2''⟩ := exists_three_ends (x := r') D' (k := (Fintype.card V - 2) / 2)
        (by omega) hodd h3'
      exact ⟨D'', by omega, h2''⟩
    · refine ⟨D', by omega, ?_⟩
      show 3 ≤ D'.ends r'
      omega
  · have h1 := countP_all_pos D hSS
    obtain ⟨D'', h1'', h2''⟩ := exists_three_ends (x := r') D' (k := (Fintype.card V - 2) / 2)
      (by rcases hβ with hβ | hβ <;> omega) hodd h3'
    exact ⟨D'', by rcases hβ with hβ | hβ <;> omega, h2''⟩

/-! ### Gallai from STL and STL2 -/

/-- **STL and STL2 on three-connected graphs imply Gallai.** Hypotheses: for every
three-connected `J` and every `z` with `J − z` free of matching cuts, (STL) if `z` is the only even
vertex, STL holds at every neighbour `r`; (STL2) if `z` and a neighbour `r` are the only even
vertices, STL2 holds at `(z, r)`. -/
theorem gallai_of_stl
    (h1 : ∀ (W : Type u) [Fintype W] [DecidableEq W] (J : SimpleGraph W) [DecidableRel J.Adj] (z : W),
      KConnected 3 J → ¬ HasMatchingCut (delVert J z) →
      (∀ v, Even (J.degree v) ↔ v = z) → ∀ r, J.Adj z r → STL J z r)
    (h2 : ∀ (W : Type u) [Fintype W] [DecidableEq W] (J : SimpleGraph W) [DecidableRel J.Adj] (z : W),
      KConnected 3 J → ¬ HasMatchingCut (delVert J z) →
      ∀ r, J.Adj z r → (∀ v, Even (J.degree v) ↔ v = z ∨ v = r) → STL2 J z r) :
    GallaiConjecture.{u} := by
  refine (gallai_iff_spineTests'.{u}).2.2 ?_
  intro W _ _ J _ z hJ hmc
  have hdeg : ∀ r, J.Adj z r → 3 ≤ J.degree r := fun r _ => hJ.le_degree r
  exact ⟨test1_of_stl z hdeg (h1 W J z hJ hmc), test2_of_stl2 z hdeg (h2 W J z hJ hmc)⟩

end Gallai
