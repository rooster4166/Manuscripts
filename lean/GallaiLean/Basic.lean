import Mathlib

/-!
# Path decompositions: core definitions

Conventions shared by every file in this project.

* A *path* is a nonempty simple walk (`Walk.IsPath`, length ≥ 1).
* A *path decomposition* of `G` is a list of paths whose edge lists, concatenated, contain
  every edge of `G` exactly once.
* `pathNumber G` is the least length of a path decomposition (`p(G)` in the manuscripts).
* `ends D v` counts the path ends at `v`, with multiplicity.
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u}

/-- A path of `G`, packaged with its endpoints. -/
structure GPath (G : SimpleGraph V) where
  src : V
  tgt : V
  walk : G.Walk src tgt
  isPath : walk.IsPath
  pos : 0 < walk.length

namespace GPath

variable {G : SimpleGraph V}

/-- Edge list of a path. -/
def edges (P : GPath G) : List (Sym2 V) := P.walk.edges

/-- Number of ends of `P` at `v` (0, 1 or 2; it is 2 only if `src = tgt`, which a path forbids). -/
def endsAt [DecidableEq V] (P : GPath G) (v : V) : ℕ :=
  (if P.src = v then 1 else 0) + (if P.tgt = v then 1 else 0)

end GPath

/-- A path decomposition of `G`. -/
structure PathDecomp (G : SimpleGraph V) where
  paths : List (GPath G)
  nodup_edges : (paths.flatMap GPath.edges).Nodup
  covers : ∀ e, e ∈ G.edgeSet ↔ e ∈ paths.flatMap GPath.edges

namespace PathDecomp

variable {G : SimpleGraph V}

/-- Number of paths. -/
def size (D : PathDecomp G) : ℕ := D.paths.length

/-- Number of path ends at `v`, with multiplicity. -/
def ends [DecidableEq V] (D : PathDecomp G) (v : V) : ℕ :=
  (D.paths.map (fun P => P.endsAt v)).sum

end PathDecomp

/-- The path number `p(G)`: the least size of a path decomposition. Every finite graph has one,
since every single edge is a path. -/
noncomputable def pathNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ D : PathDecomp G, D.size = k}

/-- Gallai's conjecture, as a proposition about one universe of vertex types. -/
def GallaiConjecture : Prop :=
  ∀ (W : Type u) [Fintype W] (G : SimpleGraph W), G.Connected →
    pathNumber G ≤ (Fintype.card W + 1) / 2

end Gallai
