-- steer2_examples.lean (audit A35): smoke test of the Lean definition `Steer2` against the paper.
-- The schedules of Example 6.6 (FsRDG) and Example 9.2 (FqJPo) are built as `Steer2` derivations,
-- move by move, and `avoid_of_steer2` is applied to them.  Example 9.2 has the g-token move onto
-- y after the y-token has left, and return to g, where it retires.
-- Run from lean/:  lake env lean ../research/audit/A35-scripts/steer2_examples.lean
import GallaiLean.TRNSteer

open SimpleGraph Gallai

namespace A35

/-- A graph on `Fin n` from an edge list. -/
abbrev ofList (n : ℕ) (L : List (ℕ × ℕ)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun a b : Fin n => (a.val, b.val) ∈ L)

instance (n : ℕ) (L : List (ℕ × ℕ)) : DecidableRel (ofList n L).Adj := by
  intro a b; unfold ofList; infer_instance

/-- Example 6.6: FsRDG, g = 2, y = 0, x = 4. -/
abbrev G66 : SimpleGraph (Fin 7) :=
  ofList 7 [(0,1),(0,2),(0,3),(0,5),(0,6),(1,4),(1,5),(2,6),(5,6)]

-- the schedule: y-token 0 -> 1; g-token 2 -> 0; g-token 0 -> 3 (retires)
theorem steer_G66 :
    Steer2 (leafX (4 : Fin 7)) (apex G66 {0}) (some 2) (some 0) := by
  refine Steer2.swap (Steer2.step (u := some 1) (by decide) (by decide) (by decide) (by decide) ?_)
  refine Steer2.swap (Steer2.step (u := some 0) (by decide) (by decide) (by decide) (by decide) ?_)
  exact Steer2.fin (u := some 3) (by decide) (by decide) (by decide) (by decide)

theorem good_G66 : AvoidDecomp G66 0 {4} :=
  avoid_of_steer2 G66 (by decide) (g := 2) (by decide) (by decide) (by decide) (by decide)
    (by decide) steer_G66

/-- Example 9.2: FqJPo, g = 4, y = 2, x = 3. -/
abbrev G92 : SimpleGraph (Fin 7) :=
  ofList 7 [(0,1),(0,2),(0,5),(1,3),(1,5),(2,4),(2,6),(3,5),(3,6),(4,6)]

-- the schedule: y-token 2 -> 0; g-token 4 -> 2 -> 6 -> 4 (retires at 4)
theorem steer_G92 :
    Steer2 (leafX (3 : Fin 7)) (apex G92 {2}) (some 4) (some 2) := by
  refine Steer2.swap (Steer2.step (u := some 0) (by decide) (by decide) (by decide) (by decide) ?_)
  refine Steer2.swap (Steer2.step (u := some 2) (by decide) (by decide) (by decide) (by decide) ?_)
  refine Steer2.step (u := some 6) (by decide) (by decide) (by decide) (by decide) ?_
  exact Steer2.fin (u := some 4) (by decide) (by decide) (by decide) (by decide)

theorem good_G92 : AvoidDecomp G92 2 {3} :=
  avoid_of_steer2 G92 (by decide) (g := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) steer_G92

-- TRN's own step g -> u (u = 6 in Example 6.6) fails the side condition of `Steer2.step` and
-- `Steer2.fin`: after deleting gu, u is still adjacent to the y-token (Remark 6.7).
example : (delEdge (apex G66 {0}) (some 6) (some 2)).Adj (some 6) (some 0) := by decide
example : ¬ ∀ v, (apex G66 {0}).Adj (some 6) v → v = some 2 := by decide

end A35

#print axioms A35.good_G66
#print axioms A35.good_G92
