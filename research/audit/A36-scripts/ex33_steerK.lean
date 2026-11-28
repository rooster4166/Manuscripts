import GallaiLean.MultiToken

/-!
A36 auditor: Example 3.3 of multi-token.tex as a concrete `SteerK` derivation.

J = HsaBEy~ (order 9), z = 7, r = 3, w = 1, oriented pairs (x, y) = (0, 4), (5, 8)
(in Lean the second coordinate carries the leaf).  Schedule: S 1:0-6, 8 → 3, 3 → z, 4 → 8,
D (ℓ₁, 4, 0).  Every side condition is closed by `decide` (kernel evaluation, no `native_decide`).
The derivation is then fed to `triangleBase_of_steerK` and `test1At_of_steerK`.
-/

open SimpleGraph Gallai

/-! Instances needed only to let `decide` see through the graph operations (instance search fails
on `DecidablePred ((delEdge G a b).Adj x)` for nested operations, although
`Decidable ((delEdge G a b).Adj x y)` is found), and through the three `def`s of `MultiToken`. -/
instance (priority := high) decPredDelEdge {W : Type*} [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (a b x : W) : DecidablePred ((delEdge G a b).Adj x) :=
  fun y => delEdge.decRel G a b x y
instance (priority := high) decPredPlusEdge {W : Type*} [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (a b x : W) : DecidablePred ((plusEdge G a b).Adj x) :=
  fun y => plusEdge.decRel G a b x y
instance decOffTails {U : Type*} [DecidableEq U] (T : Finset (U × U × U)) (K : SimpleGraph U)
    [DecidableRel K.Adj] (u : U) : Decidable (OffTails T K u) := by
  unfold OffTails; infer_instance
instance decSuppOK {U : Type*} [DecidableEq U] (T : Finset (U × U × U)) (K : SimpleGraph U)
    [DecidableRel K.Adj] (a b : U) : Decidable (SuppOK T K a b) := by
  unfold SuppOK; infer_instance
instance decOneLive {U : Type*} [DecidableEq U] (T : Finset (U × U × U)) (K : SimpleGraph U)
    [DecidableRel K.Adj] : Decidable (OneLive T K) := by
  unfold OneLive; infer_instance

def E33 : List (Fin 9 × Fin 9) :=
  [(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,8),(1,6),(1,7),(2,6),(2,8),(3,7),(3,8),(4,7),(4,8),
   (5,7),(5,8),(6,8),(7,8)]

def J33 : SimpleGraph (Fin 9) where
  Adj a b := a ≠ b ∧ ((a, b) ∈ E33 ∨ (b, a) ∈ E33)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel J33.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a, b) ∈ E33 ∨ (b, a) ∈ E33)))

def L33 : List (Fin 9 × Fin 9) := [(0, 4), (5, 8)]

abbrev K0 := triLeaf J33 7 1 L33
abbrev T33 := triTails L33
abbrev K1 := plusEdge (delEdge (delEdge K0 (.inl 1) (.inl 0)) (.inl 1) (.inl 6)) (.inl 0) (.inl 6)
abbrev K2 := delEdge K1 (.inl 3) (.inl 8)
abbrev K3 := delEdge K2 (.inl 7) (.inl 3)
abbrev K4 := delEdge K3 (.inl 8) (.inl 4)
abbrev K5 := delEdge K4 (.inr 4) (.inl 4)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
theorem ex33_steerK : SteerK T33 K0 (evenSet K0) := by
  refine SteerK.supp (p := .inl 1) (a := .inl 0) (b := .inl 6) (by decide) (by decide) (by decide)
    (by decide) (by decide) ?_
  -- 8 → 3: new tokens {3, 4}
  refine SteerK.move (p := .inl 8) (u := .inl 3) (τ' := {.inl 3, .inl 4}) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  -- 3 → z = 7, which is left isolated: the token retires
  refine SteerK.move (p := .inl 3) (u := .inl 7) (τ' := {.inl 4}) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  -- 4 → 8: new token {8}
  refine SteerK.move (p := .inl 4) (u := .inl 8) (τ' := {.inl 8}) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  -- drop the tail (ℓ₁, 4, 0) = (inr 4, inl 4, inl 0); the stem 4 is left isolated
  refine SteerK.drop (t := (.inr 4, .inl 4, .inl 0)) (τ' := {.inl 8}) (by decide) (by decide)
    (by decide) (by decide) ?_
  exact SteerK.fin (by decide) (by decide)

theorem hz33 : ∀ v, Even (J33.degree v) ↔ v = 7 := by decide
theorem hD33 : TriangleData J33 7 3 1 L33 := ⟨by decide, by decide, by decide⟩

theorem ex33_triangleBase : TriangleBase J33 7 3 := triangleBase_of_steerK hz33 hD33 ex33_steerK
theorem ex33_test1 : Test1At J33 7 3 := test1At_of_steerK hz33 (by decide) hD33 ex33_steerK

/-- Sanity: the token set of `M⁺` is `{w, y₁, y₂} = {1, 4, 8}`. -/
theorem ex33_tokens : evenSet K0 = {.inl 1, .inl 4, .inl 8} := by decide

/-- The forbidden step: `y₁ = 4` cannot move onto 8 at the start (8 is a token). -/
theorem ex33_not_first : Sum.inl 8 ∈ evenSet K0 := by decide

#print axioms ex33_test1
