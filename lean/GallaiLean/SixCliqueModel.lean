import GallaiLean.Schedule

/-!
# The finite core of the six-clique construction

Model data for Theorem 1 of *Prescribed path ends at a clique of six even vertices*, Section 4.
Every finite fact used by the proof is checked here by `decide +kernel` (kernel evaluation; no
extra axioms).

**The core model `Fin 12`.** Vertices `0, …, 5` are the clique `U` and `6 + i` is the
representative `i'` of omission type `i`. `rr a b` (both `≥ 6`) marks the representative pairs,
whose exterior edges are unknown and are always allowed when blank neighbours are counted.

* `mpaths`: the five seed paths of the paper; `seedE`: their 24 edges (`D₀ = {23, 45}` plus the
  installed spokes).
* `seg1`, `seg2`, `seg3`: the 2 + 8 + 6 single transfers between the stages; `E1 … E4` the core
  edges present at each stage; `c1 … c4` the core end vectors.
* `finalE`: the final path `(0, 5, 1, 2, 4, 3)`.

**The pair model `Fin 14`.** `12, 13` are a pair `x, y` of non-representative exterior vertices of
type `h`; `0, …, 11` are the core. `pairProg h` is Lemma 4: the two rectangles
`{x, y} → v; u → x; v → y; y → u` and `{x, y} → j; w → x; j → y; y → w` (after relabelling the
returned donor as `x`), with `(j, u, v, w)` read from `jtab, utab, vtab, wtab`. `cup14 L h` allows
`x`, `y` to be adjacent to each other, to every representative and to the clique vertex
`ptc h` of its seed row.
-/

namespace Gallai

namespace SixModel

open Prog

/-- The Boolean relation "`s(a, b)` belongs to the list `L`". -/
def ofSym {n : ℕ} (L : List (Sym2 (Fin n))) : Fin n → Fin n → Bool :=
  fun a b => decide (s(a, b) ∈ L)

/-- Representative pairs (`a, b ≥ 6`). -/
def rr (a b : Fin 12) : Bool := 6 ≤ a.val && 6 ≤ b.val

/-- The allowed core adjacency at a stage with core edge list `L`. -/
def cupS (L : List (Sym2 (Fin 12))) (a b : Fin 12) : Bool := ofSym L a b || rr a b

/-- The five seed paths of the paper (`6 + i` is `i'`). -/
def mpaths : List (Fin 12 × List (Fin 12)) :=
  [(2, [11, 1, 9, 4, 8, 5, 6, 3, 10, 0, 7]), (8, [1, 6, 4, 5, 7, 3, 2, 10]), (4, [7, 2, 6]),
    (3, [11]), (5, [9])]

/-- The 24 seed edges. -/
def seedE : List (Sym2 (Fin 12)) := mpaths.flatMap (fun p => lEdges p.1 p.2)

/-- The edges of a list of single transfers. -/
def segE (L : List (Fin 12 × Fin 12)) : List (Sym2 (Fin 12)) := L.map (fun p => s(p.1, p.2))

def seg1 : List (Fin 12 × Fin 12) := [(2, 0), (3, 1)]
def seg2 : List (Fin 12 × Fin 12) :=
  [(0, 8), (8, 3), (4, 1), (1, 0), (9, 2), (3, 0), (0, 9), (5, 3)]
def seg3 : List (Fin 12 × Fin 12) := [(11, 0), (0, 4), (4, 11), (1, 10), (10, 5), (5, 2)]

def E1 : List (Sym2 (Fin 12)) := seedE
def E2 : List (Sym2 (Fin 12)) := E1 ++ segE seg1
def E3 : List (Sym2 (Fin 12)) := E2 ++ segE seg2
def E4 : List (Sym2 (Fin 12)) := E3 ++ segE seg3

def c1 : Fin 12 → ℕ := ![0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def c2 : Fin 12 → ℕ := ![1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1]
def c3 : Fin 12 → ℕ := ![1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1]
def c4 : Fin 12 → ℕ := ![1, 0, 2, 1, 0, 0, 1, 1, 1, 1, 1, 1]

/-- The final path `(0, 5, 1, 2, 4, 3)`. -/
def finalE : List (Sym2 (Fin 12)) := lEdges 0 [5, 1, 2, 4, 3]

/-- The final end vector: two ends at `0, 2, 3`, none at `1, 4, 5`, one at each representative. -/
def cfin : Fin 12 → ℕ := ![2, 0, 2, 2, 0, 0, 1, 1, 1, 1, 1, 1]

/-- The clique vertex carrying the seed row of a non-representative pair of type `h`. -/
def ptc (h : Fin 6) : Fin 12 := if h.val < 2 then 2 else 0

/-- The core edge list and end vector at stage `s` (`s = h / 2` for type `h`). -/
def ES : ℕ → List (Sym2 (Fin 12))
  | 0 => E1
  | 1 => E2
  | _ => E3

def cS : ℕ → Fin 12 → ℕ
  | 0 => c1
  | 1 => c2
  | _ => c3

/-! ### The pair model -/

/-- The core vector extended by one end at `12` and `13`. -/
def ext14 (c : Fin 12 → ℕ) (a : Fin 14) : ℕ := if h : a.val < 12 then c ⟨a.val, h⟩ else 1

/-- Allowed adjacency in the pair model. -/
def cup14 (L : List (Sym2 (Fin 12))) (h : Fin 6) (a b : Fin 14) : Bool :=
  if hab : a.val < 12 ∧ b.val < 12 then cupS L ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩
  else (12 ≤ a.val && 12 ≤ b.val) ||
    (if a.val < 12 then (a.val == (ptc h).val || 6 ≤ a.val)
      else (b.val == (ptc h).val || 6 ≤ b.val))

def jtab : Fin 6 → Fin 14 := ![1, 0, 3, 2, 5, 4]
def utab : Fin 6 → Fin 14 := ![3, 3, 1, 1, 1, 1]
def vtab : Fin 6 → Fin 14 := ![4, 4, 4, 4, 2, 2]
def wtab : Fin 6 → Fin 14 := ![5, 5, 5, 5, 3, 3]

/-- One rectangle of Lemma 4: offer `{x, y}` to `recv`; relabel the returned donor as `x`; then
`a → x`, `recv → y`, `y → a`. -/
def rect (x y recv a : Fin 14) (k : Prog 14) : Prog 14 :=
  offer [x, y] recv (fun t => let o := if t = x then y else x; tr a t (tr recv o (tr o a k)))

/-- Lemma 4 for a pair of type `h`. -/
def pairProg (h : Fin 6) : Prog 14 :=
  rect 12 13 (vtab h) (utab h) (rect 12 13 (jtab h) (wtab h) done)

/-- The eight spokes inserted by Lemma 4. -/
def pairE (h : Fin 6) : List (Sym2 (Fin 14)) :=
  [s(12, jtab h), s(12, utab h), s(12, vtab h), s(12, wtab h),
    s(13, jtab h), s(13, utab h), s(13, vtab h), s(13, wtab h)]

/-! ### The finite checks -/

theorem mpaths_ok : ∀ p ∈ mpaths, p.2 ≠ [] ∧ (p.1 :: p.2).Nodup := by decide +kernel

theorem seedE_nodup : seedE.Nodup := by decide +kernel

/-- The seed end vector is `c1`. -/
theorem seed_ends : ∀ a : Fin 12,
    (mpaths.map (fun p => (if p.1 = a then 1 else 0) + (if lastOf p.1 p.2 = a then 1 else 0))).sum
      = c1 a := by decide +kernel

/-- Every seed edge has an endpoint in the clique. -/
theorem seedE_clique : ∀ a b : Fin 12, s(a, b) ∈ seedE → a.val < 6 ∨ b.val < 6 := by
  decide +kernel

/-- Every representative sees at most one blank in the seed. -/
theorem seed_rep_blank : ∀ r : Fin 12, 6 ≤ r.val → mblank (cupS seedE) c1 r ≤ 1 := by
  decide +kernel

theorem c1_rep : ∀ a : Fin 12, 6 ≤ a.val → c1 a = 1 := by decide +kernel

theorem seg1_ok : (ofList seg1).ok (ofSym (segE seg1)) c2 (cupS E1) (fun _ _ => false) c1 = true := by
  decide +kernel

theorem seg2_ok : (ofList seg2).ok (ofSym (segE seg2)) c3 (cupS E2) (fun _ _ => false) c2 = true := by
  decide +kernel

theorem seg3_ok : (ofList seg3).ok (ofSym (segE seg3)) c4 (cupS E3) (fun _ _ => false) c3 = true := by
  decide +kernel

/-- Lemma 4 at every type, in the stage `h / 2` where the type is processed. -/
theorem pair_ok : ∀ h : Fin 6, (pairProg h).ok (ofSym (pairE h)) (ext14 (cS (h.val / 2)))
    (cup14 (ES (h.val / 2)) h) (fun _ _ => false) (ext14 (cS (h.val / 2))) = true := by
  decide +kernel

/-- The spokes inserted for a pair are exactly those to clique vertices other than the omitted
`h` and the seed vertex `ptc h`. -/
theorem pairE_iff : ∀ (h : Fin 6) (a b : Fin 14), s(a, b) ∈ pairE h ↔
    ((a.val = 12 ∨ a.val = 13) ∧ b.val < 6 ∧ b.val ≠ h.val ∧ b.val ≠ (ptc h).val) ∨
    ((b.val = 12 ∨ b.val = 13) ∧ a.val < 6 ∧ a.val ≠ h.val ∧ a.val ≠ (ptc h).val) := by
  decide +kernel

theorem ptc_lt (h : Fin 6) : (ptc h).val < 6 := by unfold ptc; split <;> simp

theorem ptc_ne : ∀ h : Fin 6, (ptc h).val ≠ h.val := by decide +kernel

/-- The final path is new. -/
theorem finalE_new : ∀ a b : Fin 12, s(a, b) ∈ finalE → cupS E4 a b = false := by decide +kernel

theorem finalE_ok : ((0 : Fin 12) :: [5, 1, 2, 4, 3]).Nodup := by decide +kernel

/-- The final end vector. -/
theorem final_ends : ∀ a : Fin 12,
    c4 a + ((if (0 : Fin 12) = a then 1 else 0) + (if (3 : Fin 12) = a then 1 else 0)) = cfin a := by
  decide +kernel

/-- Every core edge of the end result is a clique edge or a true spoke of a representative. -/
theorem core_sound : ∀ a b : Fin 12, s(a, b) ∈ E4 ++ finalE →
    (a.val < 6 ∧ b.val < 6 ∧ a ≠ b) ∨ (a.val < 6 ∧ 6 ≤ b.val ∧ b.val - 6 ≠ a.val) ∨
    (b.val < 6 ∧ 6 ≤ a.val ∧ a.val - 6 ≠ b.val) := by decide +kernel

/-- Every clique edge and every true spoke of a representative is used. -/
theorem core_complete : ∀ a b : Fin 12,
    ((a.val < 6 ∧ b.val < 6 ∧ a ≠ b) ∨ (a.val < 6 ∧ 6 ≤ b.val ∧ b.val - 6 ≠ a.val)) →
    s(a, b) ∈ E4 ++ finalE := by decide +kernel

theorem cfin_spec : ∀ a : Fin 12, cfin a =
    if a.val = 0 ∨ a.val = 2 ∨ a.val = 3 then 2 else if a.val < 6 then 0 else 1 := by
  decide +kernel

end SixModel

end Gallai
