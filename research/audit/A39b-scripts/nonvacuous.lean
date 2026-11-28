import GallaiLean.DenseRootB

/-! Audit A39b: the hypotheses of Theorem B (both cases) and of its spine forms are satisfiable.
All side conditions are discharged by `decide` (kernel evaluation; no `native_decide`). -/

open Gallai SimpleGraph Finset

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A graph on `Fin n` from an edge list. -/
def gr (n : ℕ) (L : List (ℕ × ℕ)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun a b : Fin n => (a.val, b.val) ∈ L)

instance (n : ℕ) (L : List (ℕ × ℕ)) : DecidableRel (gr n L).Adj := fun a b => by
  unfold gr; infer_instance

/-! ### 1. `δ = 0`, `k = 2`: `B = K₄ − rs`, `r = 0`, `s = 3`, `Q = 1 2`. (t-range empty.) -/

def B4 : SimpleGraph (Fin 4) := gr 4 [(0,1),(0,2),(1,2),(1,3),(2,3)]
instance : DecidableRel B4.Adj := by unfold B4; infer_instance

def Q4 : GPath (starDel B4 0) :=
  ⟨1, 2, Walk.cons (by decide) Walk.nil, (Walk.isPath_def _).mpr (by decide), by decide⟩

theorem nv_d0_k2 : ∃ D : PathDecomp B4, D.size = 2 ∧ D.ends 0 = 2 :=
  exists_decomp_of_connector B4 (k := 2) le_rfl (by decide) 0 (by decide) Q4 (by decide)
    (by decide) (by decide) (by decide) 2 (by decide) (by intro t h1 h2; omega)

/-! ### 2. `δ = 0`, `k = 4` (t = 3 is in range, and the condition is tight).
`r = 0`, `N = {1,…,6}`, `s = 7`, `Q = 1 2`; in `B`: `d(3) = d(4) = d(5) = 6`, so `h̃₃ = 3`,
`λ = ⌈3/2⌉ + ⌈3/2⌉ = 4 ≥ 3`, and `⌊3/2⌋ + 1 + 3 = 5 ≤ k + 1`. -/

def B8 : SimpleGraph (Fin 8) := gr 8
  [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),
   (1,2),
   (3,4),(3,5),(4,5),(3,1),(3,2),(3,6),(4,1),(4,2),(4,7),(5,6),(5,7),(5,1),(2,6)]
instance : DecidableRel B8.Adj := by unfold B8; infer_instance

def Q8 : GPath (starDel B8 0) :=
  ⟨1, 2, Walk.cons (by decide) Walk.nil, (Walk.isPath_def _).mpr (by decide), by decide⟩

-- the numbers in the comment
theorem nv_h3 : #((heavyNbrs B8 0 3).filter (fun x => x ∉ Q8.walk.support)) = 3 := by decide
theorem nv_lam : ∑ v ∈ Q8.walk.support.toFinset,
    ((delList (starDel B8 0) Q8.edges).degree v + 1) / 2 = 4 := by decide

theorem nv_d0_k4 : ∃ D : PathDecomp B8, D.size = 4 ∧ D.ends 0 = 2 :=
  exists_decomp_of_connector B8 (k := 4) (by decide) (by decide) 0 (by decide) Q8 (by decide)
    (by decide) (by decide) (by decide) 4 (by decide) (by
      intro t h1 h2
      obtain rfl : t = 3 := by omega
      left; decide)

/-! ### 3. `δ = 1`, `k = 3`: `r = 0`, `N = {1,2,3,4}`, `s = 5`, `Q = 1 3 2` (`y = 3`). -/

def B6 : SimpleGraph (Fin 6) := gr 6
  [(0,1),(0,2),(0,3),(0,4),(1,3),(3,2),(1,5),(2,5),(3,4)]
instance : DecidableRel B6.Adj := by unfold B6; infer_instance

def Q6 : GPath (starDel B6 0) :=
  ⟨1, 2, Walk.cons (v := 3) (by decide) (Walk.cons (by decide) Walk.nil),
    (Walk.isPath_def _).mpr (by decide), by decide⟩

theorem nv_d1_k3 : ∃ D : PathDecomp B6, D.size = 3 ∧ D.ends 0 = 2 :=
  exists_decomp_of_connector_mid B6 (k := 3) (by decide) (by decide) 0 (by decide) Q6
    (by decide) (by decide) 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) 10 (by decide) (by intro t h1 h2; omega)

/-! ### 4. `δ = 1` with a connector of length 3 (`q₁ y s q₂`), outside Theorem 4.1 as stated.
`r = 0`, `N = {1,2,3,4}`, `s = 5`, `Q = 1 3 5 2`. -/

def B6' : SimpleGraph (Fin 6) := gr 6
  [(0,1),(0,2),(0,3),(0,4),(1,3),(3,5),(5,2),(3,4),(1,4),(2,4)]
instance : DecidableRel B6'.Adj := by unfold B6'; infer_instance

def Q6' : GPath (starDel B6' 0) :=
  ⟨1, 2, Walk.cons (v := 3) (by decide) (Walk.cons (v := 5) (by decide)
    (Walk.cons (by decide) Walk.nil)), (Walk.isPath_def _).mpr (by decide), by decide⟩

theorem nv_d1_len3 : ∃ D : PathDecomp B6', D.size = 3 ∧ D.ends 0 = 2 :=
  exists_decomp_of_connector_mid B6' (k := 3) (by decide) (by decide) 0 (by decide) Q6'
    (by decide) (by decide) 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) 10 (by decide) (by intro t h1 h2; omega)

/-! ### 5. Spine form, `δ = 0`, `k = 2`: `J = B4 + z` on `Fin 5`, `z = 4` adjacent to `0, 1, 2`
(so `d_J(r) = 3 = n − 2`). -/

def J5 : SimpleGraph (Fin 5) := gr 5 [(0,1),(0,2),(1,2),(1,3),(2,3),(4,0),(4,1),(4,2)]
instance : DecidableRel J5.Adj := by unfold J5; infer_instance

theorem hz40 : J5.Adj 4 0 := by decide

abbrev r5 : {v : Fin 5 | v ≠ 4} := ⟨0, hz40.ne'⟩
abbrev v1 : {v : Fin 5 | v ≠ 4} := ⟨1, by decide⟩
abbrev v2 : {v : Fin 5 | v ≠ 4} := ⟨2, by decide⟩

def Q5 : GPath (starDel (delVert J5 4) r5) :=
  ⟨v1, v2, Walk.cons (by decide) Walk.nil, (Walk.isPath_def _).mpr (by decide), by decide⟩

theorem nv_spine_d0 : Test1At J5 4 0 :=
  test1At_of_connector J5 (k := 2) le_rfl (by decide) hz40 (by decide) Q5 (by decide)
    (by decide) (by decide) (by decide) 2 (by decide) (by intro t h1 h2; omega)

/-! ### Checks: no `sorryAx`; a false count is rejected (sanity check of `decide`). -/

#print axioms nv_d0_k2
#print axioms nv_d0_k4
#print axioms nv_d1_k3
#print axioms nv_d1_len3
#print axioms nv_spine_d0

/-! ### 6. Spine form at order 9 (`k = 4`, t = 3 in range, tight), from the multi-token data.
`J` = line 419 of `multi-token/data/J9_d6.g6` (`Hsbfn\~`), `z = 5` (its only even vertex),
`r = 0` (`d_J(r) = 7 = n − 2`), `s = 8 ∈ Z`, `T = {3, 4}`, `Q = 3 8 4` (`q₁ s q₂`, `δ = 0`).
`λ = 1 + 2 + 1 = 4`, `h̃₃ = #{6, 7} = 2`: `⌊2/2⌋ + 1 + 3 = 5 ≤ k + 1`. -/

def J9 : SimpleGraph (Fin 9) := gr 9
  [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,5),(1,6),(1,7),(1,8),(2,5),(2,6),(2,7),(2,8),
   (3,6),(3,8),(4,7),(4,8),(5,6),(5,7),(5,8),(6,7),(6,8),(7,8)]
instance : DecidableRel J9.Adj := by unfold J9; infer_instance

theorem hz9 : J9.Adj 5 0 := by decide
theorem J9_onlyEven : ∀ v, Even (J9.degree v) ↔ v = 5 := by decide

abbrev r9 : {v : Fin 9 | v ≠ 5} := ⟨0, hz9.ne'⟩
abbrev u3 : {v : Fin 9 | v ≠ 5} := ⟨3, by decide⟩
abbrev u4 : {v : Fin 9 | v ≠ 5} := ⟨4, by decide⟩
abbrev u8 : {v : Fin 9 | v ≠ 5} := ⟨8, by decide⟩

def Q9 : GPath (starDel (delVert J9 5) r9) :=
  ⟨u3, u4, Walk.cons (v := u8) (by decide) (Walk.cons (by decide) Walk.nil),
    (Walk.isPath_def _).mpr (by decide), by decide⟩

theorem nv9_h3 : #((heavyNbrs (delVert J9 5) r9 3).filter (fun x => x ∉ Q9.walk.support)) = 2 := by
  decide
theorem nv9_lam : ∑ v ∈ Q9.walk.support.toFinset,
    ((delList (starDel (delVert J9 5) r9) Q9.edges).degree v + 1) / 2 = 4 := by decide

theorem nv_spine9 : Test1At J9 5 0 :=
  test1At_of_connector J9 (k := 4) (by decide) (by decide) hz9 (by decide) Q9 (by decide)
    (by decide) (by decide) (by decide) 4 (by decide) (by
      intro t h1 h2
      obtain rfl : t = 3 := by omega
      left; decide)

#print axioms nv_spine9

/-! ### 7. Spine form, `δ = 1`, order 9: line 27 of `J9_d6.g6` (`HsaBe]~`), `z = 7`, `r = 8`,
`s = 1`, `Q = 2 0 3` (`y = 0`), `λ = 4`, `h̃₃ = 0`: `⌊1/2⌋ + 1 + 3 ≤ 5`. -/

def J9b : SimpleGraph (Fin 9) := gr 9
  [(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,8),(1,6),(1,7),(2,6),(2,8),(3,6),(3,8),(4,7),(4,8),
   (5,7),(5,8),(6,7),(6,8),(7,8)]
instance : DecidableRel J9b.Adj := by unfold J9b; infer_instance

theorem hz9b : J9b.Adj 7 8 := by decide
theorem J9b_onlyEven : ∀ v, Even (J9b.degree v) ↔ v = 7 := by decide

abbrev w8 : {v : Fin 9 | v ≠ 7} := ⟨8, hz9b.ne'⟩
abbrev w0 : {v : Fin 9 | v ≠ 7} := ⟨0, by decide⟩
abbrev w2 : {v : Fin 9 | v ≠ 7} := ⟨2, by decide⟩
abbrev w3 : {v : Fin 9 | v ≠ 7} := ⟨3, by decide⟩

def Q9b : GPath (starDel (delVert J9b 7) w8) :=
  ⟨w2, w3, Walk.cons (v := w0) (by decide) (Walk.cons (by decide) Walk.nil),
    (Walk.isPath_def _).mpr (by decide), by decide⟩

theorem nv_spine9_mid : Test1At J9b 7 8 :=
  test1At_of_connector_mid J9b (k := 4) (by decide) (by decide) hz9b (by decide) Q9b (by decide)
    (by decide) w0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 4
    (by decide) (by
      intro t h1 h2
      obtain rfl : t = 3 := by omega
      left; decide)

/-! ### 8. A root certified by the Lean `δ = 1` theorem only through a connector of length 3
(`q₁ y s q₂`), hence outside Theorem 4.1 as stated and outside the paper's count of 1,143:
line 55 of `J9_d6.g6` (``Hs`@dZ^``), `z = 0`, `r = 8`, `s = 2`, `Q = 5 7 2 6` (`y = 7`), `λ = 3`,
`h̃₃ = 0`. -/

def J9c : SimpleGraph (Fin 9) := gr 9
  [(0,1),(0,2),(0,3),(0,4),(0,7),(0,8),(1,5),(1,8),(2,6),(2,7),(3,6),(3,8),(4,7),(4,8),(5,7),
   (5,8),(6,8),(7,8)]
instance : DecidableRel J9c.Adj := by unfold J9c; infer_instance

theorem hz9c : J9c.Adj 0 8 := by decide
theorem J9c_onlyEven : ∀ v, Even (J9c.degree v) ↔ v = 0 := by decide

abbrev x8 : {v : Fin 9 | v ≠ 0} := ⟨8, hz9c.ne'⟩
abbrev x5 : {v : Fin 9 | v ≠ 0} := ⟨5, by decide⟩
abbrev x7 : {v : Fin 9 | v ≠ 0} := ⟨7, by decide⟩
abbrev x2 : {v : Fin 9 | v ≠ 0} := ⟨2, by decide⟩
abbrev x6 : {v : Fin 9 | v ≠ 0} := ⟨6, by decide⟩

def Q9c : GPath (starDel (delVert J9c 0) x8) :=
  ⟨x5, x6, Walk.cons (v := x7) (by decide) (Walk.cons (v := x2) (by decide)
    (Walk.cons (by decide) Walk.nil)), (Walk.isPath_def _).mpr (by decide), by decide⟩

theorem nv_spine9_len3 : Test1At J9c 0 8 :=
  test1At_of_connector_mid J9c (k := 4) (by decide) (by decide) hz9c (by decide) Q9c (by decide)
    (by decide) x7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 3
    (by decide) (by
      intro t h1 h2
      obtain rfl : t = 3 := by omega
      left; decide)

#print axioms nv_spine9_mid
#print axioms nv_spine9_len3
