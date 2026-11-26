import GallaiLean.Insertion

/-!
# Insertion schedules: finite transfer programs replayed on arbitrary graphs

This is the reusable "insertion schedule" lemma. A schedule of grouped endpoint transfers is
written on a finite *model* `Fin n` and checked there by evaluation (`decide`). The soundness
theorem `Prog.sound` replays it on any graph whose blank vertices all lie in the image of the
model, under an injective map `ι : Fin n → V`.

**Programs.** `Prog n` is a tree:

* `done`;
* `offer ds r k`: offer the donors `ds` to the receiver `r` (Fan's grouped transfer); if the
  donor `t` is returned, continue with `k t`.

A single transfer `t → r` is `tr t r k = offer [t] r (fun _ => k)`; `ofList` turns a list of
single transfers into a program.

**Model state.** `adj : Fin n → Fin n → Bool` is an *upper bound* for the present edges between
model vertices (unknown edges may be included: this only increases blank counts); `ins` records
the edges inserted so far; `c : Fin n → ℕ` is the end vector on the model.

**Checks** (`Prog.ok T tgt`). At an offer: `r ∉ ds`, `ds` has no duplicates, no donor is
`adj`-adjacent to `r`, and the model blank count of `r` is smaller than the total supply
`∑_{t ∈ ds} c t`. Each branch with `c t > 0` is checked after inserting `tr` and moving one end
from `t` to `r` (a branch with `c t = 0` cannot occur, since Fan only returns donors with an end).
At a leaf: the inserted edges are exactly `T` and the end vector is `tgt`.

**Soundness** (`Prog.sound`). Suppose `E₀ ∪ img ι ins` has a decomposition with end vector `b`,
`b ∘ ι = c`, every vertex outside the image of `ι` has a positive end count, and every edge of the
current graph between distinct model vertices is allowed by `adj`. If the program checks, then
`E₀ ∪ img ι T` has a decomposition whose end vector is `tgt` on the model and unchanged outside.

The proof is an induction on the program: each offer is one application of `Ach.grouped`. The
real blank neighbours of the receiver inject into the model blank neighbours, because every
blank vertex lies in the model.
-/

open SimpleGraph

namespace Gallai

universe u

/-- An insertion program on the model vertex set `Fin n`. -/
inductive Prog (n : ℕ) where
  | done : Prog n
  | offer (donors : List (Fin n)) (recv : Fin n) (cont : Fin n → Prog n) : Prog n

namespace Prog

variable {n : ℕ}

/-- A single transfer `t → r` followed by `k`. -/
def tr (t r : Fin n) (k : Prog n) : Prog n := offer [t] r (fun _ => k)

/-- A list of single transfers, in order. -/
def ofList : List (Fin n × Fin n) → Prog n
  | [] => done
  | (t, r) :: l => tr t r (ofList l)

/-- Add the pair `{t, r}` to a symmetric Boolean relation. -/
def bupd (f : Fin n → Fin n → Bool) (t r : Fin n) : Fin n → Fin n → Bool :=
  fun a b => f a b || (a == t && b == r) || (a == r && b == t)

/-- The model blank count of `r`: model vertices `a ≠ r` allowed adjacent to `r` with `c a = 0`. -/
def mblank (adj : Fin n → Fin n → Bool) (c : Fin n → ℕ) (r : Fin n) : ℕ :=
  (Finset.univ.filter (fun a => adj r a = true ∧ a ≠ r ∧ c a = 0)).card

/-- The checker. -/
def ok (T : Fin n → Fin n → Bool) (tgt : Fin n → ℕ) :
    Prog n → (Fin n → Fin n → Bool) → (Fin n → Fin n → Bool) → (Fin n → ℕ) → Bool
  | done, _, ins, c =>
      decide (∀ a b, ins a b = T a b) && decide (∀ a, c a = tgt a)
  | offer ds r k, adj, ins, c =>
      decide (r ∉ ds) && decide ds.Nodup && decide (∀ t ∈ ds, adj t r = false) &&
      decide (mblank adj c r < (ds.map c).sum) &&
      ds.attach.all (fun t => decide (c t.1 = 0) ||
        ok T tgt (k t.1) (bupd adj t.1 r) (bupd ins t.1 r) (mv c t.1 r))

end Prog

/-- The image in `V` of a Boolean relation on the model. -/
def img {V : Type u} {n : ℕ} (ι : Fin n → V) (f : Fin n → Fin n → Bool) : Set (Sym2 V) :=
  {e | ∃ a b, f a b = true ∧ e = s(ι a, ι b)}

theorem img_bupd {V : Type u} {n : ℕ} (ι : Fin n → V) (f : Fin n → Fin n → Bool) (t r : Fin n) :
    img ι (Prog.bupd f t r) = insert s(ι t, ι r) (img ι f) := by
  ext e
  simp only [img, Prog.bupd, Set.mem_insert_iff, Set.mem_ofPred_eq, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨a, b, (h | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩, rfl⟩
    · exact Or.inr ⟨a, b, h, rfl⟩
    · exact Or.inl rfl
    · exact Or.inl Sym2.eq_swap
  · rintro (rfl | ⟨a, b, h, rfl⟩)
    · exact ⟨t, r, Or.inl (Or.inr ⟨rfl, rfl⟩), rfl⟩
    · exact ⟨a, b, Or.inl (Or.inl h), rfl⟩

theorem img_congr {V : Type u} {n : ℕ} (ι : Fin n → V) {f g : Fin n → Fin n → Bool}
    (h : ∀ a b, f a b = g a b) : img ι f = img ι g := by
  ext e
  simp only [img, Set.mem_ofPred_eq, h]

/-- **Soundness of insertion programs** (the insertion-schedule lemma). -/
theorem Prog.sound {V : Type u} [DecidableEq V] [Fintype V] {n : ℕ} (ι : Fin n → V)
    (hι : Function.Injective ι) (T : Fin n → Fin n → Bool) (tgt : Fin n → ℕ)
    (E₀ : Set (Sym2 V)) (b₀ : V → ℕ) (hb₀ : ∀ v, v ∉ Set.range ι → 0 < b₀ v) :
    ∀ (P : Prog n) (adj ins : Fin n → Fin n → Bool) (c : Fin n → ℕ) (b : V → ℕ),
      P.ok T tgt adj ins c = true →
      Ach (E₀ ∪ img ι ins) b →
      (∀ a, b (ι a) = c a) →
      (∀ v, v ∉ Set.range ι → b v = b₀ v) →
      (∀ a a', a ≠ a' → s(ι a, ι a') ∈ E₀ ∪ img ι ins → adj a a' = true) →
      ∃ b', Ach (E₀ ∪ img ι T) b' ∧ (∀ a, b' (ι a) = tgt a) ∧
        (∀ v, v ∉ Set.range ι → b' v = b₀ v) := by
  intro P
  induction P with
  | done =>
    intro adj ins c b hok hach hbc hbo _
    simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hins, hc⟩ := hok
    refine ⟨b, ?_, fun a => (hbc a).trans (hc a), hbo⟩
    rwa [img_congr ι hins] at hach
  | offer ds r k ih =>
    intro adj ins c b hok hach hbc hbo hadj
    simp only [ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
      List.mem_attach, true_implies, Subtype.forall] at hok
    obtain ⟨⟨⟨⟨hr, hnd⟩, hna⟩, hlt⟩, hk⟩ := hok
    set E := E₀ ∪ img ι ins with hE
    -- the real offer
    have huT : ι r ∉ ds.toFinset.image ι := by
      simp only [Finset.mem_image, List.mem_toFinset, not_exists, not_and]
      intro t ht h
      exact hr (hι h ▸ ht)
    have hT : ∀ t ∈ ds.toFinset.image ι, s(t, ι r) ∉ E := by
      simp only [Finset.mem_image, List.mem_toFinset]
      rintro _ ⟨t, ht, rfl⟩ hmem
      have htr : t ≠ r := fun h => hr (h ▸ ht)
      have := hadj t r htr hmem
      rw [hna t ht] at this
      exact Bool.false_ne_true this
    have hblank : blankNbrs E b (ι r) ≤ mblank adj c r := by
      unfold mblank
      rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _ hι]
      apply blankNbrs_le_of_subset
      intro w hw hwr hb0
      by_cases hwι : w ∈ Set.range ι
      · obtain ⟨a, rfl⟩ := hwι
        refine ⟨a, ?_, rfl⟩
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
        have har : a ≠ r := fun h => hwr (h ▸ rfl)
        refine ⟨hadj r a (Ne.symm har) hw, har, ?_⟩
        rw [← hbc a]; exact hb0
      · have := hb₀ w hwι
        rw [hbo w hwι] at hb0
        omega
    have hsum : ∑ t ∈ ds.toFinset.image ι, b t = (ds.map c).sum := by
      rw [Finset.sum_image (fun x _ y _ h => hι h), List.sum_toFinset _ hnd]
      congr 1
      exact List.map_congr_left (fun a _ => hbc a)
    obtain ⟨t', ht', ht1, hach'⟩ :=
      hach.grouped (ι r) (ds.toFinset.image ι) huT hT (by omega)
    obtain ⟨t, htds, rfl⟩ : ∃ t ∈ ds, ι t = t' := by
      simpa only [Finset.mem_image, List.mem_toFinset] using ht'
    have htr : t ≠ r := fun h => hr (h ▸ htds)
    have hct : c t ≠ 0 := by rw [← hbc t]; omega
    have hkt : (k t).ok T tgt (Prog.bupd adj t r) (Prog.bupd ins t r) (mv c t r) = true := by
      rcases hk t htds with h | h
      · exact absurd h hct
      · exact h
    refine ih t _ _ _ (mv b (ι t) (ι r)) hkt ?_ ?_ ?_ ?_
    · refine hach'.congr ?_ (fun _ => rfl)
      rw [img_bupd, Set.union_insert]
    · intro a
      unfold mv
      simp only [hι.eq_iff, hbc]
    · intro v hv
      have h1 : v ≠ ι t := fun h => hv ⟨t, h.symm⟩
      have h2 : v ≠ ι r := fun h => hv ⟨r, h.symm⟩
      rw [mv_apply_other _ h1 h2]
      exact hbo v hv
    · intro a a' haa' hmem
      rw [img_bupd, Set.union_insert, Set.mem_insert_iff] at hmem
      simp only [Prog.bupd, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
      rcases hmem with h | h
      · rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl (Or.inr ⟨hι h1, hι h2⟩)
        · exact Or.inr ⟨hι h1, hι h2⟩
      · exact Or.inl (Or.inl (hadj a a' haa' h))

/-- `Prog.sound` started from `ins = ∅` (nothing inserted yet). -/
theorem Prog.sound₀ {V : Type u} [DecidableEq V] [Fintype V] {n : ℕ} (ι : Fin n → V)
    (hι : Function.Injective ι) (P : Prog n) (adj T : Fin n → Fin n → Bool) (c tgt : Fin n → ℕ)
    (hok : P.ok T tgt adj (fun _ _ => false) c = true)
    {E : Set (Sym2 V)} {b : V → ℕ} (hach : Ach E b) (hbc : ∀ a, b (ι a) = c a)
    (hpos : ∀ v, v ∉ Set.range ι → 0 < b v)
    (hadj : ∀ a a', a ≠ a' → s(ι a, ι a') ∈ E → adj a a' = true) :
    ∃ b', Ach (E ∪ img ι T) b' ∧ (∀ a, b' (ι a) = tgt a) ∧
      (∀ v, v ∉ Set.range ι → b' v = b v) := by
  have he : img ι (fun _ _ => false) = (∅ : Set (Sym2 V)) := by
    ext e; simp [img]
  refine P.sound ι hι T tgt E b hpos adj _ c b hok (by rwa [he, Set.union_empty]) hbc
    (fun _ _ => rfl) ?_
  intro a a' h hm
  rw [he, Set.union_empty] at hm
  exact hadj a a' h hm

/-- Real blank neighbours of a model vertex are bounded by the model blank count, when every blank
vertex lies in the model. -/
theorem blankNbrs_le_mblank {V : Type u} [DecidableEq V] [Fintype V] {n : ℕ} (ι : Fin n → V)
    (hι : Function.Injective ι) {E : Set (Sym2 V)} {b : V → ℕ} (adj : Fin n → Fin n → Bool)
    (c : Fin n → ℕ) (r : Fin n) (hbc : ∀ a, b (ι a) = c a)
    (hpos : ∀ v, v ∉ Set.range ι → 0 < b v)
    (hadj : ∀ a, a ≠ r → s(ι r, ι a) ∈ E → adj r a = true) :
    blankNbrs E b (ι r) ≤ Prog.mblank adj c r := by
  unfold Prog.mblank
  rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _ hι]
  apply blankNbrs_le_of_subset
  intro w hw hwr hb0
  by_cases hwι : w ∈ Set.range ι
  · obtain ⟨a, rfl⟩ := hwι
    refine ⟨a, ?_, rfl⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    have har : a ≠ r := fun h => hwr (h ▸ rfl)
    exact ⟨hadj a har hw, har, (hbc a) ▸ hb0⟩
  · have := hpos w hwι
    omega


end Gallai
