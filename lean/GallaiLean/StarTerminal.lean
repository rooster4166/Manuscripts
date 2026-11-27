import GallaiLean.Separator
import GallaiLean.Separation
import GallaiLean.PrescribedEnd

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
* **`stl_of_deg_two`**: STL when `d(z) = 2` and the two neighbours of `z` are not adjacent
  (separation in `J − uz`, where `z` is a leaf, then append `zu`); `append_move_new` is
  `append_move` with the new path made explicit.
* **`stl_of_deg_two_tri`**: STL when `d(z) = 2`, the neighbours `u, w` are adjacent and `z` is
  their only common neighbour (separation in `J − uz − uw`, then two appends). By
  `d(z) = 2 ⇒ (STL ⇔ EE)` this is a case of conjecture EE with `uz` in a triangle.
* **`stl_deg_two`**: STL at *every* vertex of degree two, from `ee_deg_two` (session `claude/ee`,
  `PrescribedEnd.lean`); it supersedes the two previous theorems.
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

/-! ### `d(z) = 2`: STL from the separation theorem -/

section degTwo

omit [Fintype V] [DecidableRel J.Adj] in
/-- `append_move` with the new path made explicit: appending the edge `tu` at the end `t` of `P`
(when `u ∉ P`) gives a path `P'` starting at `u` whose edges are `tu` and those of `P`. -/
theorem append_move_new {K K' : SimpleGraph V} (D : PathDecomp K) {t u : V} (hadj : ¬ K.Adj t u)
    (hK' : ∀ e, e ∈ K'.edgeSet ↔ e ∈ K.edgeSet ∨ e = s(t, u))
    {P : GPath K} (hP : P ∈ D.paths) (hend : P.src = t ∨ P.tgt = t)
    (hu : u ∉ P.walk.support) :
    ∃ D' : PathDecomp K',
      (∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if u = w then 1 else 0)) ∧
      ∃ P' ∈ D'.paths, P'.src = u ∧ (P'.tgt = P.src ∨ P'.tgt = P.tgt) ∧ P'.tgt ≠ t ∧
        s(t, u) ∈ P'.edges ∧
        (∀ e ∈ P.edges, e ∈ P'.edges) ∧ (∀ e ∈ P'.edges, e = s(t, u) ∨ e ∈ P.edges) ∧
        (∀ Q' ∈ D'.paths, Q' = P' ∨ ∃ Q ∈ D.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
          Q'.walk.support = Q.walk.support) := by
  obtain ⟨Q, hQs, hQe, hQends, hQsupp⟩ := P.exists_orient hend
  have hQK : ∀ e ∈ Q.walk.edges, e ∈ K'.edgeSet := fun e he =>
    (hK' e).2 (Or.inl (Q.walk.edges_subset_edgeSet he))
  have hs : s(u, Q.src) = s(t, u) := by rw [hQs, Sym2.eq_swap]
  have hut : K'.Adj u Q.src := by
    rw [← mem_edgeSet, hK', hs]; exact Or.inr rfl
  have huQ : u ∉ Q.walk.support := fun h => hu ((hQsupp u).1 h)
  let P' : GPath K' :=
    ⟨u, Q.tgt, Walk.cons hut (Q.walk.transfer K' hQK),
      by
        rw [Walk.cons_isPath_iff]
        exact ⟨by simpa using Q.isPath, by simpa using huQ⟩,
      by simp⟩
  have hP'e : P'.edges = s(t, u) :: Q.edges := by
    show (Walk.cons hut (Q.walk.transfer K' hQK)).edges = _
    rw [Walk.edges_cons, Walk.edges_transfer, hs]
    rfl
  have hPK : ∀ e ∈ P.edges, e ∈ K.edgeSet := fun e he => P.walk.edges_subset_edgeSet he
  have htuK : s(t, u) ∉ K.edgeSet := hadj
  obtain ⟨D', -, hmem, hends, -, hcovr⟩ := D.replace_supp hP P' (by
      intro e
      rw [hK' e, hP'e, List.mem_cons, hQe.mem_iff]
      constructor
      · rintro (h | h)
        · by_cases heP : e ∈ P.edges
          · exact Or.inr (Or.inr heP)
          · exact Or.inl ⟨h, heP⟩
        · exact Or.inr (Or.inl h)
      · rintro (⟨h, -⟩ | h | h)
        · exact Or.inl h
        · exact Or.inr h
        · exact Or.inl (hPK e h))
    (by
      intro e he
      rw [hP'e, List.mem_cons, hQe.mem_iff] at he
      rcases he with rfl | he
      · exact Or.inr htuK
      · exact Or.inl he)
  have htgt : Q.tgt = P.src ∨ Q.tgt = P.tgt := by
    have h1 : Q.endsAt Q.tgt = 1 := by
      unfold GPath.endsAt; have := Q.src_ne_tgt; simp [this]
    rw [hQends] at h1
    unfold GPath.endsAt at h1
    by_cases h : P.src = Q.tgt
    · exact Or.inl h.symm
    · simp only [h, ite_false, zero_add] at h1
      split_ifs at h1 with h'
      · exact Or.inr h'.symm
  refine ⟨D', fun w => ?_, P', hmem, rfl, htgt, ?_, ?_, ?_, ?_, hcovr⟩
  · have h1 := hends w
    have h2 : P'.endsAt w = (if u = w then 1 else 0) + (if Q.tgt = w then 1 else 0) := rfl
    have h3 : P.endsAt w = (if t = w then 1 else 0) + (if Q.tgt = w then 1 else 0) := by
      rw [← hQends]; simp only [GPath.endsAt, hQs]
    omega
  · show Q.tgt ≠ t
    rw [← hQs]; exact Q.src_ne_tgt.symm
  · rw [hP'e]; exact List.mem_cons_self
  · intro e he; rw [hP'e]; exact List.mem_cons_of_mem _ (hQe.mem_iff.2 he)
  · intro e he
    rw [hP'e, List.mem_cons] at he
    rcases he with rfl | he
    · exact Or.inl rfl
    · exact Or.inr (hQe.mem_iff.1 he)

omit [Fintype V] [DecidableRel J.Adj] in
/-- A vertex of a path lies on one of its edges. -/
theorem GPath.exists_edge_of_mem (P : GPath J) {v : V} (hv : v ∈ P.walk.support) :
    ∃ e ∈ P.edges, v ∈ e := by
  have h := P.incid_add_endsAt v
  have h2 : P.endsAt v ≤ 1 := by
    unfold GPath.endsAt
    have := P.src_ne_tgt
    by_cases hs : P.src = v
    · have : P.tgt ≠ v := fun ht => this (hs.trans ht.symm)
      simp [hs, this]
    · simp only [hs, ite_false, zero_add]; split_ifs <;> omega
  simp only [hv, ite_true] at h
  have h3 : 0 < P.incid v := by omega
  unfold GPath.incid at h3
  obtain ⟨e, he, hve⟩ := List.countP_pos_iff.mp h3
  exact ⟨e, he, by simpa using hve⟩

omit [Fintype V] [DecidableRel J.Adj] in
/-- A path through a leaf `z` (whose only neighbour is `w`) uses the edge `zw`. -/
theorem GPath.leaf_edge_mem {K : SimpleGraph V} (P : GPath K) {z w : V}
    (hleaf : ∀ y, K.Adj z y → y = w) (hz : z ∈ P.walk.support) : s(z, w) ∈ P.edges := by
  obtain ⟨e, he, hze⟩ := P.exists_edge_of_mem hz
  have heK : e ∈ K.edgeSet := P.walk.edges_subset_edgeSet he
  obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hze
  rw [← hleaf y heK]; exact he

omit [Fintype V] [DecidableRel J.Adj] in
/-- A path with ends `z` and `w`, where `z` is a leaf at `w`, is the single edge `zw`. -/
theorem GPath.single_edge_of_leaf {K : SimpleGraph V} (P : GPath K) {z w : V} (hwz : w ≠ z)
    (hleaf : ∀ y, K.Adj z y → y = w)
    (hPends : (P.src = z ∧ P.tgt = w) ∨ (P.src = w ∧ P.tgt = z)) :
    ∀ e ∈ P.edges, e = s(z, w) := by
  have hend : P.src = z ∨ P.tgt = z := by
    rcases hPends with ⟨h, -⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨Q, hQs, hQe, hQends, -⟩ := P.exists_orient hend
  have hQt : Q.tgt = w := by
    have h1 : Q.endsAt w = 1 := by
      rw [hQends]
      rcases hPends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp [GPath.endsAt, h1, h2, Ne.symm hwz]
      · simp [GPath.endsAt, h1, h2, Ne.symm hwz]
    unfold GPath.endsAt at h1
    rw [hQs] at h1
    simp only [Ne.symm hwz, ite_false, zero_add] at h1
    split_ifs at h1 with h
    exact h
  intro e he
  rw [← hQe.mem_iff] at he
  obtain ⟨qs, qt, qw, hqw, hqpos⟩ := Q
  simp only at hQs hQt he
  subst qs
  subst qt
  cases qw with
  | nil => simp at hqpos
  | @cons _ c _ h q =>
    have hc : c = w := hleaf c h
    subst c
    rw [Walk.cons_isPath_iff] at hqw
    have hqn : q = Walk.nil := (Walk.isPath_iff_nil.mp hqw.1).eq_nil
    subst hqn
    simpa [GPath.edges] using he

/-- **STL when `d(z) = 2` and the neighbours `u, w` of `z` are adjacent with no common neighbour
other than `z`.** (A new case of EE: `uz` lies in a triangle and `d(u)` is arbitrary.) Proof:
separation of `u` and `w` in `J − uz − uw` (where `w` is the even vertex and `z` a leaf at `w`),
then append `uw` to the path ending at `u`, and `zu` to the path ending at `z`. -/
theorem stl_of_deg_two_tri (z u w : V) (hev : ∀ v, Even (J.degree v) ↔ v = z)
    (hzu : J.Adj z u) (hzw : J.Adj z w) (hne : u ≠ w) (hN : ∀ v, J.Adj z v → v = u ∨ v = w)
    (huw : J.Adj u w) (hcom : ∀ t, J.Adj u t → J.Adj w t → t = z) : STL J z w := by
  classical
  let K1 := delEdge J u z
  let K := delEdge K1 u w
  have hdeg1 : ∀ v, K1.degree v + (if v = u then 1 else 0) + (if v = z then 1 else 0) = J.degree v :=
    delEdge_degree J hzu.symm
  have hK1adj : ∀ x y, K1.Adj x y ↔ J.Adj x y ∧ ¬ s(x, y) = s(u, z) := fun _ _ => Iff.rfl
  have hKadj : ∀ x y, K.Adj x y ↔ K1.Adj x y ∧ ¬ s(x, y) = s(u, w) := fun _ _ => Iff.rfl
  have huz : u ≠ z := hzu.ne'
  have hwz : w ≠ z := hzw.ne'
  have huw1 : K1.Adj u w := (hK1adj u w).2 ⟨huw, fun h => by
    rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hwz h2
    · exact huz h1⟩
  have hdeg : ∀ v, K.degree v + (if v = u then 1 else 0) + (if v = w then 1 else 0) = K1.degree v :=
    delEdge_degree K1 huw1
  have hpar : ∀ v, J.degree v % 2 = if v = z then 0 else 1 := by
    intro v
    split_ifs with hv
    · exact Nat.even_iff.mp ((hev v).2 hv)
    · have : ¬ Even (J.degree v) := fun he => hv ((hev v).1 he)
      rw [Nat.not_even_iff] at this; exact this
  have hdz : J.degree z = 2 := by
    rw [← card_neighborFinset_eq_degree]
    have : J.neighborFinset z = {u, w} := by
      ext v
      simp only [mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨hN v, by rintro (rfl | rfl) <;> assumption⟩
    rw [this, Finset.card_pair hne]
  -- `z` is a leaf of `K1` (and of `K`) at `w`
  have hK1z : ∀ y, K1.Adj z y → y = w := by
    intro y hy
    rw [hK1adj] at hy
    rcases hN y hy.1 with rfl | rfl
    · exact absurd (Sym2.eq_swap) hy.2
    · rfl
  have hKz : ∀ y, K.Adj z y → y = w := fun y hy => hK1z y ((hKadj z y).1 hy).1
  have hw3 : 3 ≤ J.degree w := by
    have h1 : J.degree w % 2 = 1 := by rw [hpar w]; simp [hwz]
    have h2 : 2 ≤ J.degree w := by
      rw [← card_neighborFinset_eq_degree]
      have : ({z, u} : Finset V) ⊆ J.neighborFinset w := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · simpa using hzw.symm
        · simpa using huw.symm
      have := Finset.card_le_card this
      rwa [Finset.card_pair huz.symm] at this
    omega
  have hevK : (evenSet K).card ≤ 1 := by
    have hsub : evenSet K ⊆ {w} := by
      intro v hv
      rw [mem_evenSet_iff] at hv
      rw [Finset.mem_singleton]
      by_contra hvw
      have h1 := hdeg v
      have h2 := hdeg1 v
      have h3 := hpar v
      by_cases hvz : v = z
      · subst v; have h5 := hdz
        simp only [huz.symm, hwz.symm, ite_false, ite_true] at h1 h2 h3; omega
      · by_cases hvu : v = u
        · subst v; simp only [hne, hvz, ite_false, ite_true] at h1 h2 h3; omega
        · simp only [hvu, hvw, hvz, ite_false] at h1 h2 h3; omega
    exact (Finset.card_le_card hsub).trans (by simp)
  have hfar : FarApart K u w := by
    refine ⟨hne, fun h => ((hKadj u w).1 h).2 rfl, fun t ⟨h1, h2⟩ => ?_⟩
    have ht1 := ((hK1adj u t).1 ((hKadj u t).1 h1).1)
    have ht2 := ((hK1adj t w).1 ((hKadj t w).1 h2).1)
    have := hcom t ht1.1 ht2.1.symm
    subst this
    exact ht1.2 rfl
  obtain ⟨D, hD, hsep⟩ := separation K hevK hfar
  -- the path ending at `u`
  have hDu : D.ends u = 1 := by
    rw [hD u]; have h1 := hdeg u; have h2 := hdeg1 u; have h3 := hpar u
    simp only [hne, huz, ite_false, ite_true] at h1 h2 h3; omega
  have hexists : ∀ v, D.ends v = 1 → ∃ P ∈ D.paths, P.src = v ∨ P.tgt = v := by
    intro v hv
    by_contra hc
    push Not at hc
    have : D.ends v = 0 := by
      unfold PathDecomp.ends
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hx
      obtain ⟨h1, h2⟩ := hc Q hQ
      simp [GPath.endsAt, h1, h2]
    omega
  obtain ⟨Pu, hPu, hendu⟩ := hexists u hDu
  have huPu : u ∈ Pu.walk.support := by
    rcases hendu with h | h
    · rw [← h]; exact Pu.walk.start_mem_support
    · rw [← h]; exact Pu.walk.end_mem_support
  have hwPu : w ∉ Pu.walk.support := fun h => hsep Pu hPu ⟨huPu, h⟩
  -- step 1: append `uw`
  have hK1' : ∀ e, e ∈ K1.edgeSet ↔ e ∈ K.edgeSet ∨ e = s(u, w) := by
    intro e
    rw [delEdge_edgeSet K1 u w]
    constructor
    · intro he
      by_cases h : e = s(u, w)
      · exact Or.inr h
      · exact Or.inl ⟨he, h⟩
    · rintro (⟨he, -⟩ | rfl)
      · exact he
      · exact huw1
  obtain ⟨D1, hends1, P1, hP1, hsrc1, htgt1, -, -, -, -, hcov1⟩ :=
    append_move_new D (fun h => ((hKadj u w).1 h).2 rfl) hK1' hPu hendu hwPu
  -- the path of `D1` ending at `z` is an old path through `w`, so it avoids `u`
  have hD1z : D1.ends z = 1 := by
    have h1 := hends1 z
    rw [hD z] at h1
    have h2 := hdeg z; have h3 := hdeg1 z; have h5 := hdz
    simp only [huz, hwz, huz.symm, hwz.symm, ite_false, ite_true, add_zero] at h1 h2 h3
    omega
  have hexists1 : ∃ R ∈ D1.paths, R.src = z ∨ R.tgt = z := by
    by_contra hc
    push Not at hc
    have : D1.ends z = 0 := by
      unfold PathDecomp.ends
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hx
      obtain ⟨h1, h2⟩ := hc Q hQ
      simp [GPath.endsAt, h1, h2]
    omega
  obtain ⟨R, hR, hendR⟩ := hexists1
  have huR : u ∉ R.walk.support := by
    rcases hcov1 R hR with rfl | ⟨Q, hQ, hs, ht, hsupp⟩
    · -- `P1` cannot end at `z`: then `Pu` would end at `z`, hence contain `w`
      exfalso
      have hzPu : z ∈ Pu.walk.support := by
        rcases hendR with h | h
        · rw [hsrc1] at h; exact absurd h hwz
        · rcases htgt1 with h' | h'
          · rw [← h, h']; exact Pu.walk.start_mem_support
          · rw [← h, h']; exact Pu.walk.end_mem_support
      exact hwPu (Walk.mem_support_of_mem_edge Pu.walk
        (Pu.leaf_edge_mem hKz hzPu) (Sym2.mem_mk_right _ _))
    · rw [hsupp]
      have hzQ : z ∈ Q.walk.support := by
        rcases hendR with h | h
        · rw [hs] at h; rw [← h]; exact Q.walk.start_mem_support
        · rw [ht] at h; rw [← h]; exact Q.walk.end_mem_support
      have hwQ : w ∈ Q.walk.support :=
        Walk.mem_support_of_mem_edge Q.walk (Q.leaf_edge_mem hKz hzQ) (Sym2.mem_mk_right _ _)
      exact fun h => hsep Q hQ ⟨h, hwQ⟩
  -- step 2: append `zu`
  have hJ' : ∀ e, e ∈ J.edgeSet ↔ e ∈ K1.edgeSet ∨ e = s(z, u) := by
    intro e
    rw [delEdge_edgeSet]
    constructor
    · intro he
      by_cases h : e = s(z, u)
      · exact Or.inr h
      · exact Or.inl ⟨he, by rw [Sym2.eq_swap]; exact h⟩
    · rintro (⟨he, -⟩ | rfl)
      · exact he
      · exact hzu
  obtain ⟨D2, hends2, P2, hP2, hsrc2, htgt2, -, hzuP2, hsub2, hsub2', -⟩ :=
    append_move_new D1 (fun h => ((hK1adj z u).1 h).2 Sym2.eq_swap) hJ' hR hendR huR
  have hzR : z ∈ R.walk.support := by
    rcases hendR with h | h
    · rw [← h]; exact R.walk.start_mem_support
    · rw [← h]; exact R.walk.end_mem_support
  have hzwP2 : s(z, w) ∈ P2.edges := hsub2 _ (R.leaf_edge_mem hK1z hzR)
  refine ⟨D2, fun v => ?_, ?_, ?_⟩
  · -- ends
    have h1 := hends2 v
    have h1' := hends1 v
    have h2 := hD v
    have h3 := hdeg v
    have h3' := hdeg1 v
    have h4 := hpar v
    by_cases hvz : v = z
    · subst v
      simp only [huz, huz.symm, hwz, hwz.symm, ite_true, ite_false, hdz] at h1 h1' h3 h3' h4 ⊢
      omega
    · by_cases hvu : v = u
      · subst v
        simp only [hvz, hne, Ne.symm hne, ite_true, ite_false, Ne.symm hvz] at h1 h1' h3 h3' h4 ⊢
        omega
      · by_cases hvw : v = w
        · subst v
          simp only [hvz, hvu, Ne.symm hvu, Ne.symm hvz, ite_true, ite_false] at h1 h1' h3 h3' h4 ⊢
          omega
        · simp only [hvz, hvu, hvw, Ne.symm hvz, Ne.symm hvu, Ne.symm hvw, ite_false] at h1 h1' h3 h3' h4 ⊢
          omega
  · -- star-terminal
    intro Q hQ hz
    obtain ⟨e, he, hze⟩ := Q.exists_edge_of_mem hz
    have heJ : e ∈ J.edgeSet := Q.walk.edges_subset_edgeSet he
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hze
    have heP2 : s(z, y) ∈ P2.edges := by
      rcases hN y heJ with rfl | rfl
      · exact hzuP2
      · exact hzwP2
    have := PathDecomp.eq_of_mem_edges D2 hQ hP2 he heP2
    subst this
    left
    rw [hsrc2, Sym2.eq_swap]
    exact hzuP2
  · by_cases hw : P2.tgt = w
    · right
      refine ⟨P2, hP2, fun e he => ?_⟩
      have hRends : (R.src = z ∧ R.tgt = w) ∨ (R.src = w ∧ R.tgt = z) := by
        rcases hendR with h | h <;> rcases htgt2 with h' | h'
        · exact absurd (h.symm.trans (h'.symm.trans hw)) hwz.symm
        · exact Or.inl ⟨h, h'.symm.trans hw⟩
        · exact Or.inr ⟨h'.symm.trans hw, h⟩
        · exact absurd (h.symm.trans (h'.symm.trans hw)) hwz.symm
      rcases hsub2' e he with rfl | he'
      · exact Sym2.mem_mk_left _ _
      · rw [R.single_edge_of_leaf hwz hK1z hRends e he']; exact Sym2.mem_mk_left _ _
    · left
      exact ⟨P2, hP2, hzwP2, by rw [hsrc2]; exact hne, hw⟩

/-- **STL when `d(z) = 2` and the two neighbours of `z` are not adjacent.** If `z` is the only
even vertex, `N(z) = {u, w}` and `u ≁ w`, then some star-terminal Lovász decomposition has `u`
short (`uz` is the terminal edge at `u`); in particular `STL J z w`. Proof: separation in
`J − uz`, where `z` is a leaf at `w` at distance `≥ 3` from `u`, then append `zu`. -/
theorem stl_of_deg_two (z u w : V) (hev : ∀ v, Even (J.degree v) ↔ v = z)
    (hzu : J.Adj z u) (hzw : J.Adj z w) (hne : u ≠ w) (hN : ∀ v, J.Adj z v → v = u ∨ v = w)
    (huw : ¬ J.Adj u w) : STL J z w := by
  classical
  let K := delEdge J u z
  have hdeg : ∀ v, K.degree v + (if v = u then 1 else 0) + (if v = z then 1 else 0) = J.degree v :=
    delEdge_degree J hzu.symm
  have huz : u ≠ z := hzu.ne'
  have hwz : w ≠ z := hzw.ne'
  have hpar : ∀ v, J.degree v % 2 = if v = z then 0 else 1 := by
    intro v
    split_ifs with hv
    · exact Nat.even_iff.mp ((hev v).2 hv)
    · have : ¬ Even (J.degree v) := fun he => hv ((hev v).1 he)
      rw [Nat.not_even_iff] at this; exact this
  have hdz : J.degree z = 2 := by
    rw [← card_neighborFinset_eq_degree]
    have : J.neighborFinset z = {u, w} := by
      ext v
      simp only [mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨hN v, by rintro (rfl | rfl) <;> assumption⟩
    rw [this, Finset.card_pair hne]
  have hKadj : ∀ x y, K.Adj x y ↔ J.Adj x y ∧ ¬ s(x, y) = s(u, z) := fun _ _ => Iff.rfl
  -- `z` is a leaf of `K` at `w`
  have hKz : ∀ y, K.Adj z y → y = w := by
    intro y hy
    rw [hKadj] at hy
    rcases hN y hy.1 with rfl | rfl
    · exact absurd (Sym2.eq_swap) hy.2
    · rfl
  have hevK : (evenSet K).card ≤ 1 := by
    have hsub : evenSet K ⊆ {u} := by
      intro v hv
      rw [mem_evenSet_iff] at hv
      rw [Finset.mem_singleton]
      by_contra hvu
      have h1 := hdeg v
      have h2 := hpar v
      by_cases hvz : v = z
      · subst hvz; have h5 := hdz; simp only [hvu, ite_false, ite_true] at h1 h2; omega
      · simp only [hvu, hvz, ite_false] at h1 h2; omega
    exact (Finset.card_le_card hsub).trans (by simp)
  have hfar : FarApart K z u := by
    refine ⟨huz.symm, fun h => (hKadj z u).1 h |>.2 Sym2.eq_swap, fun x ⟨h1, h2⟩ => ?_⟩
    have := hKz x h1
    subst this
    exact huw ((hKadj _ _).1 h2).1.symm
  obtain ⟨D, hD, hsep⟩ := separation K hevK hfar
  -- the path ending at `z`
  have hDz : D.ends z = 1 := by
    rw [hD z]; have := hdeg z; simp only [huz.symm, ite_false, ite_true] at this; omega
  obtain ⟨P, hP, hend⟩ : ∃ P ∈ D.paths, P.src = z ∨ P.tgt = z := by
    by_contra hc
    push Not at hc
    have : D.ends z = 0 := by
      unfold PathDecomp.ends
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hx
      obtain ⟨h1, h2⟩ := hc Q hQ
      simp [GPath.endsAt, h1, h2]
    omega
  have hzP : z ∈ P.walk.support := by
    rcases hend with h | h
    · rw [← h]; exact P.walk.start_mem_support
    · rw [← h]; exact P.walk.end_mem_support
  have huP : u ∉ P.walk.support := fun h => hsep P hP ⟨hzP, h⟩
  have hK' : ∀ e, e ∈ J.edgeSet ↔ e ∈ K.edgeSet ∨ e = s(z, u) := by
    intro e
    rw [delEdge_edgeSet]
    constructor
    · intro he
      by_cases h : e = s(z, u)
      · exact Or.inr h
      · exact Or.inl ⟨he, by rw [Sym2.eq_swap]; exact h⟩
    · rintro (⟨he, -⟩ | rfl)
      · exact he
      · exact hzu
  obtain ⟨D', hends', P', hP', hsrc, htgt, -, hzuP', hsub, hsub', -⟩ :=
    append_move_new D (fun h => ((hKadj z u).1 h).2 Sym2.eq_swap) hK' hP hend huP
  -- `zw` lies on `P`, hence on `P'`
  have hzwP : s(z, w) ∈ P.edges := by
    obtain ⟨e, he, hze⟩ := P.exists_edge_of_mem hzP
    have heK : e ∈ K.edgeSet := P.walk.edges_subset_edgeSet he
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hze
    rw [← hKz y heK]; exact he
  have hzwP' : s(z, w) ∈ P'.edges := hsub _ hzwP
  refine ⟨D', fun v => ?_, ?_, ?_⟩
  · -- ends
    have h1 := hends' v
    have h2 := hD v
    have h3 := hdeg v
    have h4 := hpar v
    by_cases hvz : v = z
    · subst v
      simp only [huz, huz.symm, ite_true, ite_false, hdz] at h1 h3 h4 ⊢
      omega
    · by_cases hvu : v = u
      · subst v
        simp only [hvz, ite_true, ite_false, Ne.symm hvz] at h1 h3 h4 ⊢
        omega
      · simp only [hvz, hvu, Ne.symm hvz, Ne.symm hvu, ite_false] at h1 h3 h4 ⊢
        omega
  · -- star-terminal
    intro Q hQ hz
    obtain ⟨e, he, hze⟩ := Q.exists_edge_of_mem hz
    have heJ : e ∈ J.edgeSet := Q.walk.edges_subset_edgeSet he
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hze
    have heP' : s(z, y) ∈ P'.edges := by
      rcases hN y heJ with rfl | rfl
      · exact hzuP'
      · exact hzwP'
    have := PathDecomp.eq_of_mem_edges D' hQ hP' he heP'
    subst this
    left
    rw [hsrc, Sym2.eq_swap]
    exact hzuP'
  · -- `w` long, or the path is `u z w`
    by_cases hw : P'.tgt = w
    · right
      refine ⟨P', hP', fun e he => ?_⟩
      -- `P` runs from `z` to `w`, so it is the single edge `zw`
      have hPends : (P.src = z ∧ P.tgt = w) ∨ (P.src = w ∧ P.tgt = z) := by
        rcases hend with h | h <;> rcases htgt with h' | h'
        · exact absurd (h.symm.trans (h'.symm.trans hw)) hwz.symm
        · exact Or.inl ⟨h, h'.symm.trans hw⟩
        · exact Or.inr ⟨h'.symm.trans hw, h⟩
        · exact absurd (h.symm.trans (h'.symm.trans hw)) hwz.symm
      have hsingle : ∀ e ∈ P.edges, e = s(z, w) := by
        obtain ⟨Q, hQs, hQe, hQends, -⟩ := P.exists_orient hend
        have hQt : Q.tgt = w := by
          have h1 : Q.endsAt w = 1 := by
            rw [hQends]
            rcases hPends with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · simp [GPath.endsAt, h1, h2, Ne.symm hwz]
            · simp [GPath.endsAt, h1, h2, Ne.symm hwz]
          unfold GPath.endsAt at h1
          rw [hQs] at h1
          simp only [Ne.symm hwz, ite_false, zero_add] at h1
          split_ifs at h1 with h
          exact h
        intro e he
        rw [← hQe.mem_iff] at he
        obtain ⟨qs, qt, qw, hqw, hqpos⟩ := Q
        simp only at hQs hQt he
        subst qs
        subst qt
        cases qw with
        | nil => simp at hqpos
        | @cons _ c _ h q =>
          have hc : c = w := hKz c h
          subst c
          rw [Walk.cons_isPath_iff] at hqw
          have hqn : q = Walk.nil := (Walk.isPath_iff_nil.mp hqw.1).eq_nil
          subst hqn
          simpa [GPath.edges] using he
      rcases hsub' e he with rfl | he'
      · exact Sym2.mem_mk_left _ _
      · rw [hsingle e he']; exact Sym2.mem_mk_left _ _
    · left
      exact ⟨P', hP', hzwP', by rw [hsrc]; exact hne, hw⟩

/-- **STL at every vertex of degree two** (from `ee_deg_two`, session `claude/ee`). If `z` is the
only even vertex and `N(z) = {u, w}`, then `STL J z w` (and, symmetrically, `STL J z u`). By the
equivalence `d(z) = 2 ⇒ (STL(w) ⇔ EE(u))`, the path ending at `u` through `uz` is `u z w ⋯`;
it is star-terminal, and `w` is long unless the path is `u z w`. -/
theorem stl_deg_two (z u w : V) (hev : ∀ v, Even (J.degree v) ↔ v = z)
    (hzu : J.Adj z u) (hzw : J.Adj z w) (hne : u ≠ w) (hN : ∀ v, J.Adj z v → v = u ∨ v = w) :
    STL J z w := by
  classical
  have hdz : J.degree z = 2 := by
    rw [← card_neighborFinset_eq_degree]
    have : J.neighborFinset z = {u, w} := by
      ext v
      simp only [mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨hN v, by rintro (rfl | rfl) <;> assumption⟩
    rw [this, Finset.card_pair hne]
  have hz : z ∈ evenSet J := by
    rw [mem_evenSet_iff]; exact ⟨by omega, by omega⟩
  have hevc : (evenSet J).card ≤ 1 := by
    have hsub : evenSet J ⊆ {z} := by
      intro v hv
      rw [mem_evenSet_iff] at hv
      rw [Finset.mem_singleton]
      exact (hev v).1 (Nat.even_iff.mpr hv.2)
    exact (Finset.card_le_card hsub).trans (by simp)
  obtain ⟨D, hD, P, hP, hendu, huzP⟩ := ee_deg_two J hevc hz hzu hdz
  have hDz : D.ends z = 0 := by rw [hD z, hdz]
  have hnotend := not_end_of_ends_zero D hDz
  -- orient `P` from `u` and read off its first two vertices
  obtain ⟨Q, hQs, hQe, hQends, hQsupp⟩ := P.exists_orient hendu
  have hQz : Q.src ≠ z ∧ Q.tgt ≠ z := by
    have h1 := hnotend P hP
    have : Q.endsAt z = 0 := by
      rw [hQends]; unfold GPath.endsAt; simp [h1.1, h1.2]
    unfold GPath.endsAt at this
    constructor <;> intro h <;> simp [h] at this
  have huzQ : s(u, z) ∈ Q.edges := hQe.mem_iff.2 huzP
  have key : s(z, w) ∈ Q.edges ∧ (Q.tgt = w → ∀ e ∈ Q.edges, z ∈ e) := by
    obtain ⟨qs, qt, qw, hqw, hqpos⟩ := Q
    simp only at hQs hQz huzQ ⊢
    subst qs
    cases qw with
    | nil => simp at hqpos
    | @cons _ c _ h q =>
      rw [Walk.cons_isPath_iff] at hqw
      have hc : c = z := by
        simp only [GPath.edges, Walk.edges_cons, List.mem_cons] at huzQ
        rcases huzQ with he | he
        · rcases Sym2.eq_iff.mp he with ⟨-, h2⟩ | ⟨-, h2⟩
          · exact h2.symm
          · exact absurd h2 hzu.ne
        · exact absurd (q.fst_mem_support_of_mem_edges he) hqw.2
      subst c
      cases q with
      | nil => exact absurd rfl hQz.2
      | @cons _ c' _ h' q' =>
        rw [Walk.cons_isPath_iff] at hqw
        have hc' : c' = w := by
          rcases hN c' h' with rfl | rfl
          · exact absurd (by simp) hqw.2
          · rfl
        subst c'
        constructor
        · simp [GPath.edges]
        · intro ht e he
          subst ht
          have hqn : q' = Walk.nil := (Walk.isPath_iff_nil.mp hqw.1.1).eq_nil
          subst hqn
          simp only [GPath.edges, Walk.edges_cons, Walk.edges_nil, List.mem_cons,
            List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl <;> simp
  have hzwP : s(z, w) ∈ P.edges := hQe.mem_iff.1 key.1
  refine ⟨D, hD, ?_, ?_⟩
  · intro R hR hzR
    obtain ⟨e, he, hze⟩ := R.exists_edge_of_mem hzR
    have heJ : e ∈ J.edgeSet := R.walk.edges_subset_edgeSet he
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hze
    have heP : s(z, y) ∈ P.edges := by
      rcases hN y heJ with rfl | rfl
      · rw [Sym2.eq_swap]; exact huzP
      · exact hzwP
    have := PathDecomp.eq_of_mem_edges D hR hP he heP
    subst this
    rcases hendu with h | h
    · left; rw [h]; exact huzP
    · right; rw [h]; exact huzP
  · by_cases hw : Q.tgt = w
    · right
      exact ⟨P, hP, fun e he => key.2 hw e (hQe.mem_iff.2 he)⟩
    · left
      have hPends : ∀ v, (P.src = v ∨ P.tgt = v) → v = u ∨ v = Q.tgt := by
        intro v hv
        have h1 : P.endsAt v ≥ 1 := by
          unfold GPath.endsAt; rcases hv with h | h <;> simp [h]
        rw [← hQends] at h1
        unfold GPath.endsAt at h1
        rw [hQs] at h1
        by_cases h : u = v
        · exact Or.inl h.symm
        · simp only [h, ite_false, zero_add] at h1
          split_ifs at h1 with h'
          · exact Or.inr h'.symm
          · omega
      refine ⟨P, hP, hzwP, ?_, ?_⟩
      · intro h
        rcases hPends w (Or.inl h) with h' | h'
        · exact hne h'.symm
        · exact hw h'.symm
      · intro h
        rcases hPends w (Or.inr h) with h' | h'
        · exact hne h'.symm
        · exact hw h'.symm

end degTwo

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
