import GallaiLean.Lovasz
import GallaiLean.EMCFour

/-!
# Hypothesis-free forms of the four-even-vertex results

`GallaiLean/EMCFour.lean` proves its results under the hypothesis `LovaszStatement`. Since
`lovaszStatement : LovaszStatement` is now proved (`GallaiLean/Lovasz.lean`), the hypothesis is
discharged here; the results are restated with primed names.
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Two-step descent**, unconditionally. -/
theorem two_step_descent' (hconn : G.Connected)
    (hn : Even (Fintype.card V)) (h4 : 4 ≤ (evenSet G).card) {y w : V} (hy : y ∈ evenSet G)
    (hw : w ∈ evenSet G) (hyw : y ≠ w) :
    ∃ v ∈ evenSet G, v ≠ y ∧ v ≠ w ∧ Realisable G (((evenSet G).erase w).erase v) :=
  two_step_descent lovaszStatement hconn hn h4 hy hw hyw

/-- **The endpoint matroid for four even vertices (pair form)**, unconditionally. -/
theorem emc_four' (hconn : G.Connected) (hn : Even (Fintype.card V))
    (h4 : (evenSet G).card = 4) {y x z : V} (hy : y ∈ evenSet G) (hx : x ∈ evenSet G)
    (hz : z ∈ evenSet G) (hyx : y ≠ x) (hyz : y ≠ z) (hxz : x ≠ z) :
    Realisable G {y, x} ∨ Realisable G {y, z} :=
  emc_four lovaszStatement hconn hn h4 hy hx hz hyx hyz hxz

/-- Every realisable set of size at least three contains a realisable pair (four even
vertices), unconditionally. -/
theorem exists_pair_subset' (hconn : G.Connected)
    (hn : Even (Fintype.card V)) (h4 : (evenSet G).card = 4) {S : Finset V}
    (hS : Realisable G S) (h3 : 3 ≤ S.card) :
    ∃ T ⊆ S, T.card = 2 ∧ Realisable G T :=
  exists_pair_subset lovaszStatement hconn hn h4 hS h3

/-- Minimal realisable sets of a critical graph with four even vertices are the realisable
pairs, unconditionally. -/
theorem minimal_realisable_iff' (hconn : G.Connected)
    (hn : Even (Fintype.card V)) (h4 : (evenSet G).card = 4)
    (hcrit : pathNumber G = Fintype.card V / 2) (S : Finset V) :
    Minimal (Realisable G) S ↔ S.card = 2 ∧ Realisable G S :=
  minimal_realisable_iff lovaszStatement hconn hn h4 hcrit S

/-- Basis exchange for realisable pairs, unconditionally. -/
theorem pair_exchange' (hconn : G.Connected)
    (hn : Even (Fintype.card V)) (h4 : (evenSet G).card = 4) :
    Matroid.ExchangeProperty
      (fun B : Set V => ∃ T : Finset V, (T : Set V) = B ∧ T.card = 2 ∧ Realisable G T) :=
  pair_exchange lovaszStatement hconn hn h4

/-- **The endpoint matroid for four even vertices**, unconditionally. -/
theorem endpoint_matroid_four' (hconn : G.Connected)
    (hn : Even (Fintype.card V)) (h4 : (evenSet G).card = 4)
    (hcrit : pathNumber G = Fintype.card V / 2) :
    ∃ M : Matroid V, M.E = ↑(evenSet G) ∧ M.Loopless ∧
      (∀ B, M.IsBase B ↔ ∃ T : Finset V, (T : Set V) = B ∧ T.card = 2 ∧ Realisable G T) ∧
      ∀ S : Finset V, Minimal (Realisable G) S ↔ M.IsBase ↑S :=
  endpoint_matroid_four lovaszStatement hconn hn h4 hcrit

/-- **The rooted test for four even vertices**, unconditionally. -/
theorem rooted_four' (hconn : G.Connected) (hn : Even (Fintype.card V))
    (h4 : (evenSet G).card = 4) (r : V) :
    pathNumber (addLeaf G r) ≤ Fintype.card V / 2 :=
  rooted_four lovaszStatement hconn hn h4 r

end Gallai
