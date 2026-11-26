import GallaiLean.Realisable
import GallaiLean.Fan
import GallaiLean.LeafDictionary

/-!
# The second descent step and the two-even-vertex problem

(endpoint-structure manuscript, Section 5; theorem numbers as in the current PDF)

`rmEdge G a b` is `G` without the edge `ab`.

* `realisable_erase_of_fan` (**Fan descent, even partner**): if `u, w ∈ S`, `uw ∈ E(G)`, no
  neighbour of `w` is an even vertex outside `S`, and `S \ {u, w}` is realisable in `G − uw`,
  then `S \ {u}` is realisable in `G`.
* `realisable_of_fan_transfer` (**Fan transfer, odd partner**): if `u ∉ S` is even, `w` is odd,
  `uw ∈ E(G)`, every even neighbour `x ≠ u` of `w` lies in `S`, and `S` is realisable in `G − uw`,
  then `S` is realisable in `G`.
* `realisable_evenSet_erase_pair` (**second descent step**): at even order and without isolated
  vertices, if `a, b, w` are distinct even vertices with `aw ∈ E(G)` and `bw ∉ E(G)`, then
  `Ev \ {a, b}` is realisable (Lovász enters only as `LovaszStatement`).
* `etwin_of_not_realisable`: if `Ev \ {a, b}` is not realisable, then `a` and `b` have the same
  neighbours among the other even vertices.
* `fd_second_step`: the second step of faithful descent from `Ev \ {u}` keeping a root `r`.
* `FanSchedule`, `realisable_of_fanSchedule`: iterated Fan descent (even steps only).
* `FanCert`, `realisable_of_fanCert` (**soundness of the Fan calculus**): a list of even steps and
  odd transfers that ends with at most one vertex certifies that `Ev \ X` is realisable.
* `Tight`, `tight_of_transfer`, `tight_of_fanCert`: the two-even-vertex problem (parity bound
  `#odd / 2`).
* `realisable_pair` (**pair step**, Theorem 26): Fan's grouped lemma at a common neighbour `w` of
  two twins `a, a'` gives `Ev \ {u, a}` or `Ev \ {u, a'}`.
* `OddPath`, `realisable_of_oddPath` (**path transfer**, the step in Theorem 28).
* `degree_le_of_tight` (obstruction (O1)); `realisable_leaves_singleton`,
  `tight_leaves_of_lovasz` (move (L) and the leaf case of the two-even problem).
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u}

/-! ### Deleting one edge -/

/-- `G` without the edge `ab`. -/
def rmEdge (G : SimpleGraph V) (a b : V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ s(x, y) ≠ s(a, b)
  symm := ⟨fun x y h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩

instance [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    DecidableRel (rmEdge G a b).Adj :=
  fun x y => inferInstanceAs (Decidable (G.Adj x y ∧ s(x, y) ≠ s(a, b)))

variable {G : SimpleGraph V}

@[simp] theorem rmEdge_adj {a b x y : V} :
    (rmEdge G a b).Adj x y ↔ G.Adj x y ∧ s(x, y) ≠ s(a, b) := Iff.rfl

theorem rmEdge_edgeSet (a b : V) (e : Sym2 V) :
    e ∈ (rmEdge G a b).edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(a, b) := by
  induction e using Sym2.ind with
  | h x y => simp [rmEdge]

theorem rmEdge_le (a b : V) {x y : V} (h : (rmEdge G a b).Adj x y) : G.Adj x y := h.1

theorem rmEdge_adj_of_ne {a b x y : V} (hx : x ≠ a) (hx' : x ≠ b) :
    (rmEdge G a b).Adj x y ↔ G.Adj x y := by
  simp only [rmEdge_adj, and_iff_left_iff_imp]
  intro _ h
  rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hx h1
  · exact hx' h1

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem rmEdge_neighborFinset_of_ne {a b x : V} (hx : x ≠ a) (hx' : x ≠ b) :
    (rmEdge G a b).neighborFinset x = G.neighborFinset x := by
  ext y
  simp only [mem_neighborFinset]
  exact rmEdge_adj_of_ne hx hx'

theorem rmEdge_degree_of_ne {a b x : V} (hx : x ≠ a) (hx' : x ≠ b) :
    (rmEdge G a b).degree x = G.degree x := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
    rmEdge_neighborFinset_of_ne hx hx']

theorem rmEdge_neighborFinset_left {a b : V} :
    (rmEdge G a b).neighborFinset a = (G.neighborFinset a).erase b := by
  ext y
  simp only [mem_neighborFinset, Finset.mem_erase, rmEdge_adj]
  constructor
  · rintro ⟨h, hne⟩
    exact ⟨fun hy => hne (by rw [hy]), h⟩
  · rintro ⟨hy, h⟩
    refine ⟨h, fun he => hy ?_⟩
    rcases Sym2.eq_iff.mp he with ⟨-, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · exact absurd (h2 ▸ h) (G.loopless.irrefl a)

theorem rmEdge_degree_left {a b : V} (h : G.Adj a b) :
    (rmEdge G a b).degree a + 1 = G.degree a := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
    rmEdge_neighborFinset_left, Finset.card_erase_of_mem ((mem_neighborFinset _ _ _).mpr h)]
  have : 0 < (G.neighborFinset a).card :=
    Finset.card_pos.mpr ⟨b, (mem_neighborFinset _ _ _).mpr h⟩
  omega

theorem rmEdge_neighborFinset_right {a b : V} :
    (rmEdge G a b).neighborFinset b = (G.neighborFinset b).erase a := by
  ext y
  simp only [mem_neighborFinset, Finset.mem_erase, rmEdge_adj]
  constructor
  · rintro ⟨h, hne⟩
    exact ⟨fun hy => hne (by rw [hy, Sym2.eq_swap]), h⟩
  · rintro ⟨hy, h⟩
    refine ⟨h, fun he => hy ?_⟩
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨-, h2⟩
    · exact h2.trans h1
    · exact h2

theorem rmEdge_degree_right {a b : V} (h : G.Adj a b) :
    (rmEdge G a b).degree b + 1 = G.degree b := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
    rmEdge_neighborFinset_right,
    Finset.card_erase_of_mem ((mem_neighborFinset _ _ _).mpr h.symm)]
  have : 0 < (G.neighborFinset b).card :=
    Finset.card_pos.mpr ⟨a, (mem_neighborFinset _ _ _).mpr h.symm⟩
  omega

theorem rmEdge_profile_of_ne {a b x : V} (hx : x ≠ a) (hx' : x ≠ b) (S : Finset V) :
    profile (rmEdge G a b) S x = profile G S x := by
  unfold profile
  rw [rmEdge_degree_of_ne hx hx']

/-- After deleting `ab`, an even endpoint becomes odd. -/
theorem odd_delEdge_left {a b : V} (h : G.Adj a b) (ha : Even (G.degree a)) :
    Odd ((rmEdge G a b).degree a) := by
  have := rmEdge_degree_left h
  rcases ha with ⟨k, hk⟩
  have : 0 < G.degree a := G.degree_pos_iff_exists_adj a |>.mpr ⟨b, h⟩
  exact ⟨k - 1, by omega⟩

theorem odd_delEdge_right {a b : V} (h : G.Adj a b) (hb : Even (G.degree b)) :
    Odd ((rmEdge G a b).degree b) := by
  have := rmEdge_degree_right h
  rcases hb with ⟨k, hk⟩
  have : 0 < G.degree b := G.degree_pos_iff_exists_adj b |>.mpr ⟨a, h.symm⟩
  exact ⟨k - 1, by omega⟩

theorem even_delEdge_right {a b : V} (h : G.Adj a b) (hb : Odd (G.degree b)) :
    Even ((rmEdge G a b).degree b) := by
  have := rmEdge_degree_right h
  rcases hb with ⟨k, hk⟩
  exact ⟨k, by omega⟩

/-! ### Fan descent and Fan transfer -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A neighbour `x` of `w` in `G − uw` is neither `u` nor `w`. -/
theorem ne_of_delEdge_adj {u w x : V} (h : (rmEdge G u w).Adj w x) : x ≠ u ∧ x ≠ w := by
  refine ⟨fun hx => h.2 ?_, fun hx => G.loopless.irrefl w (hx ▸ h.1)⟩
  rw [hx, Sym2.eq_swap]

/-- **Fan descent** (even partner). Let `u, w ∈ S ⊆ Ev` with `uw ∈ E(G)`, and suppose no
neighbour of `w` is an even vertex outside `S`. If `S \ {u, w}` is realisable in `G − uw`, then
`S \ {u}` is realisable in `G`. The merge that lowers the number of paths happens in `G − uw`,
where `u` and `w` are odd; Fan's lemma then restores `uw`, moving the end of `u` to `w`. -/
theorem realisable_erase_of_fan {S : Finset V} {u w : V} (huw : G.Adj u w)
    (hu : u ∈ S) (hw : w ∈ S) (hS : S ⊆ evenSet G)
    (hN : ∀ x, G.Adj w x → x ∈ evenSet G → x ∈ S)
    (h' : Realisable (rmEdge G u w) ((S.erase u).erase w)) :
    Realisable G (S.erase u) := by
  obtain ⟨-, D', hD'⟩ := h'
  have hne : u ≠ w := G.ne_of_adj huw
  have heu := (Finset.mem_filter.mp (hS hu)).2
  have hew := (Finset.mem_filter.mp (hS hw)).2
  have hDu : D'.ends u = 1 := by
    rw [hD' u]; unfold profile
    simp [odd_delEdge_left huw heu.2]
  have hDw : D'.ends w = 1 := by
    rw [hD' w]; unfold profile
    simp [odd_delEdge_right huw hew.2]
  have hcond : (Finset.univ.filter
      (fun x => (rmEdge G u w).Adj w x ∧ D'.ends x = 0)).card < D'.ends u := by
    rw [hDu]
    suffices h0 : Finset.univ.filter
        (fun x => (rmEdge G u w).Adj w x ∧ D'.ends x = 0) = ∅ by
      rw [h0]; simp
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨-, hadj, h0⟩ := hx
    obtain ⟨hxu, hxw⟩ := ne_of_delEdge_adj hadj
    rw [hD' x, rmEdge_profile_of_ne hxu hxw] at h0
    unfold profile at h0
    by_cases ho : Odd (G.degree x)
    · simp [ho] at h0
    · have hxE : x ∈ evenSet G := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        G.degree_pos_iff_exists_adj x |>.mpr ⟨w, hadj.1.symm⟩, Nat.not_odd_iff_even.mp ho⟩
      have : x ∈ (S.erase u).erase w :=
        Finset.mem_erase.mpr ⟨hxw, Finset.mem_erase.mpr ⟨hxu, hN x hadj.1 hxE⟩⟩
      simp [ho, this] at h0
  obtain ⟨D, -, hDw', hDu', hrest⟩ := fan_single (G := G) (G' := rmEdge G u w) (u := w) (v := u)
    huw.symm (fun e => by rw [rmEdge_edgeSet, Sym2.eq_swap (a := w)]) D' hcond
  refine ⟨(Finset.erase_subset _ _).trans hS, D, fun x => ?_⟩
  unfold profile
  by_cases hxw : x = w
  · subst hxw
    have : x ∈ S.erase u := Finset.mem_erase.mpr ⟨Ne.symm hne, hw⟩
    simp [Nat.not_odd_iff_even.mpr hew.2, this, hDw', hDw]
  · by_cases hxu : x = u
    · subst hxu
      simp [Nat.not_odd_iff_even.mpr heu.2]
      omega
    · rw [hrest x hxw hxu, hD' x, rmEdge_profile_of_ne hxu hxw]
      unfold profile
      have : x ∈ (S.erase u).erase w ↔ x ∈ S.erase u := by
        simp [Finset.mem_erase, hxw]
      simp only [this]

/-- **Fan transfer** (odd partner). Let `u ∉ S` be even, `w` odd and `uw ∈ E(G)`, and suppose
every even neighbour `x ≠ u` of `w` lies in `S`. If `S` is realisable in `G − uw` (where `u` is
odd and `w` even), then `S` is realisable in `G`. The role of the excluded even vertex moves from
`u` to `w`. -/
theorem realisable_of_fan_transfer {S : Finset V} {u w : V} (huw : G.Adj u w)
    (hu : u ∈ evenSet G) (huS : u ∉ S) (hw : Odd (G.degree w)) (hS : S ⊆ evenSet G)
    (hN : ∀ x, x ≠ u → G.Adj w x → x ∈ evenSet G → x ∈ S)
    (h' : Realisable (rmEdge G u w) S) : Realisable G S := by
  obtain ⟨-, D', hD'⟩ := h'
  have hne : u ≠ w := G.ne_of_adj huw
  have heu := (Finset.mem_filter.mp hu).2
  have hwS : w ∉ S := fun h => not_odd_of_mem_evenSet (hS h) hw
  have hDu : D'.ends u = 1 := by
    rw [hD' u]; unfold profile
    simp [odd_delEdge_left huw heu.2]
  have hDw : D'.ends w = 0 := by
    rw [hD' w]; unfold profile
    simp [Nat.not_odd_iff_even.mpr (even_delEdge_right huw hw), hwS]
  have hcond : (Finset.univ.filter
      (fun x => (rmEdge G u w).Adj w x ∧ D'.ends x = 0)).card < D'.ends u := by
    rw [hDu]
    suffices h0 : Finset.univ.filter
        (fun x => (rmEdge G u w).Adj w x ∧ D'.ends x = 0) = ∅ by
      rw [h0]; simp
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨-, hadj, h0⟩ := hx
    obtain ⟨hxu, hxw⟩ := ne_of_delEdge_adj hadj
    rw [hD' x, rmEdge_profile_of_ne hxu hxw] at h0
    unfold profile at h0
    by_cases ho : Odd (G.degree x)
    · simp [ho] at h0
    · have hxE : x ∈ evenSet G := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        G.degree_pos_iff_exists_adj x |>.mpr ⟨w, hadj.1.symm⟩, Nat.not_odd_iff_even.mp ho⟩
      simp [ho, hN x hxu hadj.1 hxE] at h0
  obtain ⟨D, -, hDw', hDu', hrest⟩ := fan_single (G := G) (G' := rmEdge G u w) (u := w) (v := u)
    huw.symm (fun e => by rw [rmEdge_edgeSet, Sym2.eq_swap (a := w)]) D' hcond
  refine ⟨hS, D, fun x => ?_⟩
  unfold profile
  by_cases hxw : x = w
  · subst hxw
    simp [hw, hDw', hDw]
  · by_cases hxu : x = u
    · subst hxu
      simp [Nat.not_odd_iff_even.mpr heu.2, huS]
      omega
    · rw [hrest x hxw hxu, hD' x, rmEdge_profile_of_ne hxu hxw]
      rfl

/-! ### The second descent step -/

/-- Deleting an edge between two even vertices: the degrees stay positive. -/
theorem rmEdge_degree_pos {a w : V} (haw : G.Adj a w) (ha : a ∈ evenSet G)
    (hw : w ∈ evenSet G) (hG : ∀ v, 0 < G.degree v) : ∀ v, 0 < (rmEdge G a w).degree v := by
  intro v
  have hne : a ≠ w := G.ne_of_adj haw
  by_cases hva : v = a
  · subst hva
    have h1 := rmEdge_degree_left haw
    have h2 := (Finset.mem_filter.mp ha).2
    rcases h2.2 with ⟨k, hk⟩
    omega
  · by_cases hvw : v = w
    · subst hvw
      have h1 := rmEdge_degree_right haw
      have h2 := (Finset.mem_filter.mp hw).2
      rcases h2.2 with ⟨k, hk⟩
      omega
    · rw [rmEdge_degree_of_ne hva hvw]; exact hG v

/-- The even vertices of `G − aw`, for an edge `aw` between even vertices. -/
theorem evenSet_delEdge {a w : V} (haw : G.Adj a w) (ha : a ∈ evenSet G) (hw : w ∈ evenSet G) :
    evenSet (rmEdge G a w) = ((evenSet G).erase a).erase w := by
  have hne : a ≠ w := G.ne_of_adj haw
  ext x
  simp only [Finset.mem_erase]
  by_cases hxa : x = a
  · subst hxa
    simp only [hne, ne_eq, not_true_eq_false, and_false, false_and, iff_false, not_false_eq_true]
    intro hx
    exact Nat.not_odd_iff_even.mpr (Finset.mem_filter.mp hx).2.2
      (odd_delEdge_left haw (Finset.mem_filter.mp ha).2.2)
  · by_cases hxw : x = w
    · subst hxw
      simp only [ne_eq, not_true_eq_false, false_and, iff_false]
      intro hx
      exact Nat.not_odd_iff_even.mpr (Finset.mem_filter.mp hx).2.2
        (odd_delEdge_right haw (Finset.mem_filter.mp hw).2.2)
    · simp only [evenSet, Finset.mem_filter, Finset.mem_univ, true_and, rmEdge_degree_of_ne hxa hxw]
      tauto

/-- **Second descent step.** Let `G` have even order and no isolated vertex, and let `a, b, w` be
distinct even vertices with `aw ∈ E(G)` and `bw ∉ E(G)`. Then `Ev \ {a, b}` is realisable.

Proof: Lemma 3 in `G − aw` (where `a, w` are odd) realises `Ev \ {a, b, w}`; Fan descent puts
`aw` back. -/
theorem realisable_evenSet_erase_pair (hL : LovaszStatement.{u}) (hG : ∀ v, 0 < G.degree v)
    (hn : Even (Fintype.card V)) {a b w : V} (ha : a ∈ evenSet G) (hb : b ∈ evenSet G)
    (hw : w ∈ evenSet G) (hab : a ≠ b) (hwb : w ≠ b) (haw : G.Adj a w) (hbw : ¬ G.Adj b w) :
    Realisable G (((evenSet G).erase b).erase a) := by
  have hne : a ≠ w := G.ne_of_adj haw
  have hG' := rmEdge_degree_pos haw ha hw hG
  have hEv := evenSet_delEdge haw ha hw
  have hb' : b ∈ evenSet (rmEdge G a w) := by
    rw [hEv]
    exact Finset.mem_erase.mpr ⟨Ne.symm hwb, Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩⟩
  have h3 := realisable_evenSet_erase hL hG' hn hb'
  rw [hEv] at h3
  apply realisable_erase_of_fan haw (Finset.mem_erase.mpr ⟨hab, ha⟩)
    (Finset.mem_erase.mpr ⟨hwb, hw⟩) (Finset.erase_subset _ _)
  · intro x hwx hx
    refine Finset.mem_erase.mpr ⟨?_, hx⟩
    rintro rfl
    exact hbw hwx.symm
  · have : (((evenSet G).erase b).erase a).erase w = (((evenSet G).erase a).erase w).erase b := by
      ext x; simp only [Finset.mem_erase]; tauto
    rw [this]
    exact h3

/-- **Non-realisable pairs are E-twins.** If `Ev \ {a, b}` is not realisable, then `a` and `b`
are adjacent to the same even vertices other than `a, b`. -/
theorem etwin_of_not_realisable (hL : LovaszStatement.{u}) (hG : ∀ v, 0 < G.degree v)
    (hn : Even (Fintype.card V)) {a b : V} (ha : a ∈ evenSet G) (hb : b ∈ evenSet G)
    (hab : a ≠ b) (h : ¬ Realisable G (((evenSet G).erase b).erase a)) :
    ∀ w ∈ evenSet G, w ≠ a → w ≠ b → (G.Adj a w ↔ G.Adj b w) := by
  intro w hw hwa hwb
  constructor
  · intro haw
    by_contra hbw
    exact h (realisable_evenSet_erase_pair hL hG hn ha hb hw hab hwb haw hbw)
  · intro hbw
    by_contra haw
    have := realisable_evenSet_erase_pair hL hG hn hb ha hw (Ne.symm hab) hwa hbw haw
    rw [Finset.erase_right_comm] at this
    exact h this

/-- **The second step of faithful descent.** Start from the realisable set `Ev \ {u}`
(Lemma 3) and keep a root `r ≠ u`. If some even `v ∉ {u, r}` is not an E-twin of `u`, then
`Ev \ {u, v}` is realisable and still contains `r`. -/
theorem fd_second_step (hL : LovaszStatement.{u}) (hG : ∀ v, 0 < G.degree v)
    (hn : Even (Fintype.card V)) {u v r : V} (hu : u ∈ evenSet G) (hv : v ∈ evenSet G)
    (hr : r ∈ evenSet G) (hvu : v ≠ u) (hru : r ≠ u) (hrv : r ≠ v)
    (hw : ∃ w ∈ evenSet G, w ≠ u ∧ w ≠ v ∧ ¬ (G.Adj u w ↔ G.Adj v w)) :
    Realisable G (((evenSet G).erase u).erase v) ∧ r ∈ ((evenSet G).erase u).erase v := by
  refine ⟨?_, Finset.mem_erase.mpr ⟨hrv, Finset.mem_erase.mpr ⟨hru, hr⟩⟩⟩
  by_contra hnot
  obtain ⟨w, hwE, hwu, hwv, hiff⟩ := hw
  exact hiff (etwin_of_not_realisable hL hG hn hv hu hvu hnot w hwE hwv hwu).symm

/-! ### Fan schedules: iterating the descent -/

/-- A **Fan schedule** for `x₁`: pairs `(x, w)` in the order in which they are processed. Each
`w` is an even neighbour of its `x`, is adjacent neither to `x₁` nor to the `x` of any later
pair, and all the vertices involved are distinct. -/
def FanSchedule (G : SimpleGraph V) [DecidableRel G.Adj] (x₁ : V) : List (V × V) → Prop
  | [] => True
  | (x, w) :: P => x ∈ evenSet G ∧ w ∈ evenSet G ∧ G.Adj x w ∧ x ≠ x₁ ∧ w ≠ x₁ ∧
      ¬ G.Adj w x₁ ∧ (∀ q ∈ P, ¬ G.Adj w q.1 ∧ q.1 ≠ x ∧ q.1 ≠ w ∧ q.2 ≠ x ∧ q.2 ≠ w) ∧
      FanSchedule G x₁ P

theorem FanSchedule.rmEdge {x₁ a b : V} :
    ∀ {P : List (V × V)}, FanSchedule G x₁ P →
      (∀ q ∈ P, q.1 ≠ a ∧ q.1 ≠ b ∧ q.2 ≠ a ∧ q.2 ≠ b) → G.Adj a b → a ∈ evenSet G →
      b ∈ evenSet G → FanSchedule (rmEdge G a b) x₁ P
  | [], _, _, _, _, _ => trivial
  | (x, w) :: P, ⟨hx, hw, hxw, hxx₁, hwx₁, hnwx₁, hwP, hP⟩, hq, hab, ha, hb => by
    have h0 := hq (x, w) List.mem_cons_self
    have hEv := evenSet_delEdge hab ha hb
    refine ⟨?_, ?_, ?_, hxx₁, hwx₁, fun h => hnwx₁ h.1,
      fun q hq' => ⟨fun h => (hwP q hq').1 h.1, (hwP q hq').2⟩,
      FanSchedule.rmEdge hP (fun q hq' => hq q (List.mem_cons_of_mem _ hq')) hab ha hb⟩
    · rw [hEv]; exact Finset.mem_erase.mpr ⟨h0.2.1, Finset.mem_erase.mpr ⟨h0.1, hx⟩⟩
    · rw [hEv]; exact Finset.mem_erase.mpr ⟨h0.2.2.2, Finset.mem_erase.mpr ⟨h0.2.2.1, hw⟩⟩
    · exact (rmEdge_adj_of_ne h0.1 h0.2.1).mpr hxw

/-- **Iterated Fan descent.** Let `G` have even order and no isolated vertex, let `x₁` be even
and let `P` be a Fan schedule for `x₁`. Then `Ev` minus `x₁` and the first coordinates of `P` is
realisable. -/
theorem realisable_of_fanSchedule (hL : LovaszStatement.{u}) (hn : Even (Fintype.card V))
    {x₁ : V} : ∀ (P : List (V × V)) (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, 0 < G.degree v) → x₁ ∈ evenSet G → FanSchedule G x₁ P →
    Realisable G (evenSet G \ insert x₁ (P.map Prod.fst).toFinset)
  | [], G, _, hG, hx₁, _ => by
    have h := realisable_evenSet_erase hL hG hn hx₁
    have : evenSet G \ insert x₁ (([] : List (V × V)).map Prod.fst).toFinset =
        (evenSet G).erase x₁ := by
      ext y; simp [and_comm]
    rw [this]; exact h
  | (x, w) :: P, G, _, hG, hx₁, ⟨hx, hw, hxw, hxx₁, hwx₁, hnwx₁, hwP, hP⟩ => by
    have hEv := evenSet_delEdge hxw hx hw
    have hx₁' : x₁ ∈ evenSet (rmEdge G x w) := by
      rw [hEv]
      exact Finset.mem_erase.mpr ⟨Ne.symm hwx₁, Finset.mem_erase.mpr ⟨Ne.symm hxx₁, hx₁⟩⟩
    have hP' : FanSchedule (rmEdge G x w) x₁ P :=
      hP.rmEdge (fun q hq => ⟨(hwP q hq).2.1, (hwP q hq).2.2.1, (hwP q hq).2.2.2.1,
        (hwP q hq).2.2.2.2⟩) hxw hx hw
    have ih := realisable_of_fanSchedule hL hn P (rmEdge G x w)
      (rmEdge_degree_pos hxw hx hw hG) hx₁' hP'
    rw [hEv] at ih
    set X := insert x₁ (P.map Prod.fst).toFinset with hX
    have hxX : x ∉ X := by
      rw [hX, Finset.mem_insert, List.mem_toFinset, List.mem_map]
      rintro (h | ⟨q, hq, rfl⟩)
      · exact hxx₁ h
      · exact (hwP q hq).2.1 rfl
    have hwX : w ∉ X := by
      rw [hX, Finset.mem_insert, List.mem_toFinset, List.mem_map]
      rintro (h | ⟨q, hq, rfl⟩)
      · exact hwx₁ h
      · exact (hwP q hq).2.2.1 rfl
    have key := realisable_erase_of_fan (S := evenSet G \ X) hxw
      (Finset.mem_sdiff.mpr ⟨hx, hxX⟩) (Finset.mem_sdiff.mpr ⟨hw, hwX⟩) Finset.sdiff_subset
      (by
        intro y hwy hy
        refine Finset.mem_sdiff.mpr ⟨hy, ?_⟩
        rw [hX, Finset.mem_insert, List.mem_toFinset, List.mem_map]
        rintro (rfl | ⟨q, hq, rfl⟩)
        · exact hnwx₁ hwy
        · exact (hwP q hq).1 hwy)
      (by
        have : ((evenSet G \ X).erase x).erase w = ((evenSet G).erase x).erase w \ X := by
          ext y; simp only [Finset.mem_erase, Finset.mem_sdiff]; tauto
        rw [this]; exact ih)
    have : evenSet G \ insert x₁ (((x, w) :: P).map Prod.fst).toFinset = (evenSet G \ X).erase x := by
      ext y
      simp only [hX, List.map_cons, List.toFinset_cons, Finset.mem_sdiff, Finset.mem_insert,
        Finset.mem_erase]
      tauto
    rw [this]; exact key

/-! ### The Fan calculus: even steps and odd transfers -/

/-- The even vertices of `G − aw` for `a` even and `w` odd of degree at least `3`. -/
theorem evenSet_delEdge_odd {a w : V} (haw : G.Adj a w) (ha : a ∈ evenSet G)
    (hw : Odd (G.degree w)) (hw3 : 1 < G.degree w) :
    evenSet (rmEdge G a w) = insert w ((evenSet G).erase a) := by
  have hne : a ≠ w := G.ne_of_adj haw
  ext x
  simp only [Finset.mem_insert, Finset.mem_erase]
  by_cases hxa : x = a
  · subst hxa
    simp only [hne, false_or, ne_eq, not_true_eq_false, false_and, iff_false]
    intro hx
    exact Nat.not_odd_iff_even.mpr (Finset.mem_filter.mp hx).2.2
      (odd_delEdge_left haw (Finset.mem_filter.mp ha).2.2)
  · by_cases hxw : x = w
    · subst hxw
      simp only [true_or, iff_true]
      have h1 := rmEdge_degree_right haw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, even_delEdge_right haw hw⟩
    · simp only [hxw, false_or, evenSet, Finset.mem_filter, Finset.mem_univ, true_and,
        rmEdge_degree_of_ne hxa hxw]
      tauto

/-- A **Fan certificate** for removing the set `X` of even vertices: a list of moves `(x, w)`,
processed from the head. Each move deletes an edge `xw` with `x ∈ X` such that `w` is adjacent to
no other vertex of `X`. If `w` is even (and outside `X`) the move removes `x` from `X`
(*even step*); if `w` is odd of degree at least `3` the move replaces `x` by `w` (*odd transfer*).
The list ends when at most one vertex is left. -/
def FanCert : (G : SimpleGraph V) → [DecidableRel G.Adj] → Finset V → List (V × V) → Prop
  | _, _, X, [] => X.card ≤ 1
  | G, _, X, (x, w) :: M => x ∈ X ∧ G.Adj x w ∧ (∀ y ∈ X, y ≠ x → ¬ G.Adj w y) ∧
      ((w ∈ evenSet G ∧ w ∉ X ∧ FanCert (rmEdge G x w) (X.erase x) M) ∨
       (Odd (G.degree w) ∧ 1 < G.degree w ∧
         FanCert (rmEdge G x w) (insert w (X.erase x)) M))

/-- **Soundness of the Fan calculus.** At even order and without isolated vertices, if `X ⊆ Ev`
has a Fan certificate, then `Ev \ X` is realisable. -/
theorem realisable_of_fanCert (hL : LovaszStatement.{u}) (hn : Even (Fintype.card V)) :
    ∀ (M : List (V × V)) (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V),
    (∀ v, 0 < G.degree v) → X ⊆ evenSet G → FanCert G X M → Realisable G (evenSet G \ X)
  | [], G, _, X, hG, hX, hM => by
    rcases Finset.eq_empty_or_nonempty X with rfl | ⟨x, hx⟩
    · rw [Finset.sdiff_empty]; exact realisable_evenSet hL hG
    · have hX1 : X = {x} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hx, fun y hy => Finset.card_le_one.mp hM y hy x hx⟩
      subst hX1
      rw [Finset.sdiff_singleton_eq_erase]
      exact realisable_evenSet_erase hL hG hn (hX (Finset.mem_singleton_self x))
  | (x, w) :: M, G, _, X, hG, hX, ⟨hxX, hxw, hwX, hM⟩ => by
    have hx := hX hxX
    have hne : x ≠ w := G.ne_of_adj hxw
    rcases hM with ⟨hw, hwX', hM⟩ | ⟨hw, hw3, hM⟩
    · -- even step
      have hEv := evenSet_delEdge hxw hx hw
      have ih := realisable_of_fanCert hL hn M (rmEdge G x w) (X.erase x)
        (rmEdge_degree_pos hxw hx hw hG)
        (by
          intro y hy
          rw [hEv]
          obtain ⟨hyx, hyX⟩ := Finset.mem_erase.mp hy
          exact Finset.mem_erase.mpr ⟨fun h => hwX' (h ▸ hyX), Finset.mem_erase.mpr ⟨hyx, hX hyX⟩⟩)
        hM
      rw [hEv] at ih
      have key := realisable_erase_of_fan (S := evenSet G \ X.erase x) hxw
        (Finset.mem_sdiff.mpr ⟨hx, fun h => (Finset.mem_erase.mp h).1 rfl⟩)
        (Finset.mem_sdiff.mpr ⟨hw, fun h => hwX' (Finset.mem_of_mem_erase h)⟩) Finset.sdiff_subset
        (by
          intro y hwy hy
          refine Finset.mem_sdiff.mpr ⟨hy, fun h => ?_⟩
          obtain ⟨hyx, hyX⟩ := Finset.mem_erase.mp h
          exact hwX y hyX hyx hwy)
        (by
          have : ((evenSet G \ X.erase x).erase x).erase w =
              ((evenSet G).erase x).erase w \ X.erase x := by
            ext y; simp only [Finset.mem_erase, Finset.mem_sdiff]; tauto
          rw [this]; exact ih)
      have : (evenSet G \ X.erase x).erase x = evenSet G \ X := by
        ext y
        simp only [Finset.mem_erase, Finset.mem_sdiff]
        constructor
        · rintro ⟨hyx, hy, hyX⟩; exact ⟨hy, fun h => hyX ⟨hyx, h⟩⟩
        · rintro ⟨hy, hyX⟩
          exact ⟨fun h => hyX (h ▸ hxX), hy, fun h => hyX h.2⟩
      rw [← this]; exact key
    · -- odd transfer
      have hEv := evenSet_delEdge_odd hxw hx hw hw3
      have hdeg : ∀ v, 0 < (rmEdge G x w).degree v := by
        intro v
        by_cases hvx : v = x
        · subst hvx
          have h1 := rmEdge_degree_left hxw
          have h2 := (Finset.mem_filter.mp hx).2
          rcases h2.2 with ⟨k, hk⟩
          omega
        · by_cases hvw : v = w
          · subst hvw
            have h1 := rmEdge_degree_right hxw
            omega
          · rw [rmEdge_degree_of_ne hvx hvw]; exact hG v
      have ih := realisable_of_fanCert hL hn M (rmEdge G x w) (insert w (X.erase x)) hdeg
        (by
          rw [hEv]
          exact Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hX))
        hM
      rw [hEv] at ih
      have hwE : w ∉ evenSet G := fun h => not_odd_of_mem_evenSet h hw
      have : insert w ((evenSet G).erase x) \ insert w (X.erase x) = evenSet G \ X := by
        ext y
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨h1 | ⟨hyx, hy⟩, h2⟩
          · exact absurd (Or.inl h1) h2
          · exact ⟨hy, fun hyX => h2 (Or.inr ⟨hyx, hyX⟩)⟩
        · rintro ⟨hy, hyX⟩
          refine ⟨Or.inr ⟨fun h => hyX (h ▸ hxX), hy⟩, ?_⟩
          rintro (rfl | ⟨-, h⟩)
          · exact hwE hy
          · exact hyX h
      rw [this] at ih
      exact realisable_of_fan_transfer hxw hx (fun h => (Finset.mem_sdiff.mp h).2 hxX) hw
        Finset.sdiff_subset
        (by
          intro y hyx hwy hy
          exact Finset.mem_sdiff.mpr ⟨hy, fun hyX => hwX y hyX hyx hwy⟩)
        ih

/-! ### The two-even-vertex problem -/

/-- `H` is **tight** if it has a decomposition with one end at every odd vertex and none at the
even vertices, i.e. into `#odd / 2` paths (the parity bound). This is `Realisable H ∅`. -/
abbrev Tight (H : SimpleGraph V) [DecidableRel H.Adj] : Prop := Realisable H ∅

/-- **Transfer lemma** for graphs with exactly two even vertices `u, v`: if `w` is an odd
neighbour of `u` not adjacent to `v`, and `H − uw` (whose even vertices are `w, v`) is tight, then
`H` is tight. -/
theorem tight_of_transfer {H : SimpleGraph V} [DecidableRel H.Adj] {u v w : V}
    (hEv : evenSet H = {u, v}) (huw : H.Adj u w) (hw : Odd (H.degree w)) (hwv : ¬ H.Adj w v)
    (h : Tight (rmEdge H u w)) : Tight H := by
  have hu : u ∈ evenSet H := by rw [hEv]; simp
  refine realisable_of_fan_transfer huw hu (Finset.notMem_empty u) hw (Finset.empty_subset _)
    ?_ h
  intro x hxu hwx hx
  rw [hEv, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact absurd rfl hxu
  · exact absurd hwx hwv

/-- A graph (even order, no isolated vertex) whose even set has a Fan certificate is tight. For a
graph with exactly two even vertices this is a sufficient condition for the parity bound. -/
theorem tight_of_fanCert (hL : LovaszStatement.{u}) (hn : Even (Fintype.card V))
    {H : SimpleGraph V} [DecidableRel H.Adj] (hG : ∀ v, 0 < H.degree v) {M : List (V × V)}
    (hM : FanCert H (evenSet H) M) : Tight H := by
  have := realisable_of_fanCert hL hn M H (evenSet H) hG (subset_refl _) hM
  rwa [Finset.sdiff_self] at this

/-! ### The pair step (Fan's grouped lemma) -/

/-- Second half of the pair step: one application of `fan_single` at the edge `t'w`. -/
theorem pair_finish {u t t' w : V} (ht'w : G.Adj t' w) (ht : t ∈ evenSet G)
    (ht' : t' ∈ evenSet G) (hut : u ≠ t) (hut' : u ≠ t') (htt' : t ≠ t')
    (D' : PathDecomp (rmEdge G t' w)) (hDt : D'.ends t = 0) (hDt' : D'.ends t' = 1)
    (hDx : ∀ x, x ≠ t → x ≠ t' → x ≠ w → D'.ends x = profile G ((evenSet G).erase u) x)
    (hDw : D'.ends w = profile G (((evenSet G).erase u).erase t) w + 1)
    (hcond : (Finset.univ.filter
      (fun x => (rmEdge G t' w).Adj t' x ∧ D'.ends x = 0)).card < D'.ends w) :
    Realisable G (((evenSet G).erase u).erase t) := by
  have hne : t' ≠ w := G.ne_of_adj ht'w
  obtain ⟨D, -, hDt'', hDw'', hrest⟩ := fan_single (G := G) (G' := rmEdge G t' w) (u := t')
    (v := w) ht'w (fun e => rmEdge_edgeSet t' w e) D' hcond
  refine ⟨(Finset.erase_subset _ _).trans (Finset.erase_subset _ _), D, fun x => ?_⟩
  by_cases hxt' : x = t'
  · subst hxt'
    rw [hDt'', hDt']
    have : x ∈ ((evenSet G).erase u).erase t :=
      Finset.mem_erase.mpr ⟨Ne.symm htt', Finset.mem_erase.mpr ⟨Ne.symm hut', ht'⟩⟩
    simp [profile, not_odd_of_mem_evenSet ht', this]
  · by_cases hxw : x = w
    · subst hxw; omega
    · rw [hrest x hxt' hxw]
      by_cases hxt : x = t
      · subst hxt
        rw [hDt]
        simp [profile, not_odd_of_mem_evenSet ht]
      · rw [hDx x hxt hxt' hxw]
        unfold profile
        have : x ∈ ((evenSet G).erase u).erase t ↔ x ∈ (evenSet G).erase u := by
          simp [Finset.mem_erase, hxt]
        simp only [this]

/-- Degree bookkeeping for `G − aw − a'w`. -/
theorem degree_delEdge₂ {a a' w : V} (haa' : a ≠ a') (haw : G.Adj a w) (ha'w : G.Adj a' w) :
    (rmEdge (rmEdge G a w) a' w).degree a + 1 = G.degree a ∧
    (rmEdge (rmEdge G a w) a' w).degree a' + 1 = G.degree a' ∧
    (rmEdge (rmEdge G a w) a' w).degree w + 2 = G.degree w ∧
    ∀ x, x ≠ a → x ≠ a' → x ≠ w → (rmEdge (rmEdge G a w) a' w).degree x = G.degree x := by
  have hne : a ≠ w := G.ne_of_adj haw
  have hne' : a' ≠ w := G.ne_of_adj ha'w
  have h1 : (rmEdge G a w).Adj a' w := (rmEdge_adj_of_ne (Ne.symm haa') hne').mpr ha'w
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [rmEdge_degree_of_ne haa' hne]; exact rmEdge_degree_left haw
  · rw [← rmEdge_degree_of_ne (G := G) (Ne.symm haa') hne']; exact rmEdge_degree_left h1
  · have := rmEdge_degree_right h1
    have := rmEdge_degree_right (G := G) haw
    omega
  · intro x hxa hxa' hxw
    rw [rmEdge_degree_of_ne hxa' hxw, rmEdge_degree_of_ne hxa hxw]

omit [Fintype V] [DecidableRel G.Adj] in
theorem edgeSet_readd {G2 : SimpleGraph V} {a a' w t t' : V}
    (hE2 : ∀ e, e ∈ G2.edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(a, w) ∧ e ≠ s(a', w))
    (h : (t = a ∧ t' = a') ∨ (t = a' ∧ t' = a))
    (haa' : a ≠ a') (haw : G.Adj a w) (ha'w : G.Adj a' w) (e : Sym2 V) :
    e ∈ (rmEdge G t' w).edgeSet ↔ e ∈ G2.edgeSet ∨ e = s(t, w) := by
  rw [rmEdge_edgeSet, hE2]
  have hst : s(a, w) ≠ s(a', w) := by
    intro he
    rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact haa' h1
    · exact haa' (h1.trans h2)
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · constructor
    · rintro ⟨he, hne⟩
      by_cases h : e = s(t, w)
      · exact Or.inr h
      · exact Or.inl ⟨he, h, hne⟩
    · rintro (⟨he, -, hne⟩ | rfl)
      · exact ⟨he, hne⟩
      · exact ⟨haw, hst⟩
  · constructor
    · rintro ⟨he, hne⟩
      by_cases h : e = s(t, w)
      · exact Or.inr h
      · exact Or.inl ⟨he, hne, h⟩
    · rintro (⟨he, hne, -⟩ | rfl)
      · exact ⟨he, hne⟩
      · exact ⟨ha'w, Ne.symm hst⟩

/-- The pair step, for an abstract `G2 = G − aw − a'w`. -/
theorem pair_core (hL : LovaszStatement.{u}) (hn : Even (Fintype.card V)) {u a a' w : V}
    (G2 : SimpleGraph V) [DecidableRel G2.Adj]
    (hE2 : ∀ e, e ∈ G2.edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(a, w) ∧ e ≠ s(a', w))
    (d2a : G2.degree a + 1 = G.degree a) (d2a' : G2.degree a' + 1 = G.degree a')
    (d2w : G2.degree w + 2 = G.degree w)
    (d2x : ∀ x, x ≠ a → x ≠ a' → x ≠ w → G2.degree x = G.degree x)
    (hG : ∀ v, 0 < G.degree v) (hu : u ∈ evenSet G) (ha : a ∈ evenSet G)
    (ha' : a' ∈ evenSet G) (hua : u ≠ a) (hua' : u ≠ a') (haa' : a ≠ a') (huw : u ≠ w)
    (haw : G.Adj a w) (ha'w : G.Adj a' w)
    (hw : (w ∈ evenSet G ∧ 4 ≤ G.degree w) ∨
      (Odd (G.degree w) ∧ (¬ G.Adj a a' ∨ (¬ G.Adj a u ∧ ¬ G.Adj a' u)))) :
    Realisable G (((evenSet G).erase u).erase a) ∨
      Realisable G (((evenSet G).erase u).erase a') := by
  have hne : a ≠ w := G.ne_of_adj haw
  have hne' : a' ≠ w := G.ne_of_adj ha'w
  have hadj2 : ∀ x y, G2.Adj x y → G.Adj x y := fun x y h => ((hE2 s(x, y)).mp h).1
  have hae := (Finset.mem_filter.mp ha).2
  have hae' := (Finset.mem_filter.mp ha').2
  have hap := hae.1
  have hap' := hae'.1
  have hwpos : 3 ≤ G.degree w := by
    rcases hw with ⟨-, h4⟩ | ⟨hodd, -⟩
    · omega
    · have h2 : a ∈ G.neighborFinset w := (mem_neighborFinset _ _ _).mpr haw.symm
      have h3 : a' ∈ G.neighborFinset w := (mem_neighborFinset _ _ _).mpr ha'w.symm
      have : 2 ≤ (G.neighborFinset w).card := by
        have := Finset.card_le_card (s := {a, a'}) (t := G.neighborFinset w)
          (Finset.insert_subset h2 (Finset.singleton_subset_iff.mpr h3))
        rwa [Finset.card_pair haa'] at this
      rw [card_neighborFinset_eq_degree] at this
      rcases hodd with ⟨k, hk⟩
      omega
  have hG2pos : ∀ x, 0 < G2.degree x := by
    intro x
    by_cases hxa : x = a
    · rw [hxa]; rcases hae.2 with ⟨k, hk⟩; omega
    · by_cases hxa' : x = a'
      · rw [hxa']; rcases hae'.2 with ⟨k, hk⟩; omega
      · by_cases hxw : x = w
        · rw [hxw]
          rcases hw with ⟨hwE, h4⟩ | ⟨⟨k, hk⟩, -⟩
          · omega
          · omega
        · rw [d2x x hxa hxa' hxw]; exact hG x
  have hodd2a : Odd (G2.degree a) := by rcases hae.2 with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
  have hodd2a' : Odd (G2.degree a') := by rcases hae'.2 with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
  have hu2 : u ∈ evenSet G2 := by
    have := d2x u hua hua' huw
    have hu' := (Finset.mem_filter.mp hu).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, this ▸ hu'.1, this ▸ hu'.2⟩
  obtain ⟨-, D2, hD2⟩ := realisable_evenSet_erase hL hG2pos hn hu2
  have hD2a : D2.ends a = 1 := by rw [hD2 a]; simp [profile, hodd2a]
  have hD2a' : D2.ends a' = 1 := by rw [hD2 a']; simp [profile, hodd2a']
  have hmem2 : ∀ x, x ≠ a → x ≠ a' → x ≠ w → (x ∈ evenSet G2 ↔ x ∈ evenSet G) := by
    intro x hxa hxa' hxw
    simp only [evenSet, Finset.mem_filter, Finset.mem_univ, true_and, d2x x hxa hxa' hxw]
  have hD2x : ∀ x, x ≠ a → x ≠ a' → x ≠ w → D2.ends x = profile G ((evenSet G).erase u) x := by
    intro x hxa hxa' hxw
    rw [hD2 x]
    unfold profile
    rw [d2x x hxa hxa' hxw]
    simp only [Finset.mem_erase, hmem2 x hxa hxa' hxw]
  have hD2w : D2.ends w = profile G ((evenSet G).erase u) w := by
    rcases hw with ⟨hwE, h4⟩ | ⟨hodd, -⟩
    · have hwe := (Finset.mem_filter.mp hwE).2.2
      have h2e : Even (G2.degree w) := by rcases hwe with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
      have hw2 : w ∈ (evenSet G2).erase u := Finset.mem_erase.mpr ⟨Ne.symm huw,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG2pos w, h2e⟩⟩
      have hwu : w ∈ (evenSet G).erase u := Finset.mem_erase.mpr ⟨Ne.symm huw, hwE⟩
      rw [hD2 w]
      simp [profile, Nat.not_odd_iff_even.mpr h2e, hw2, Nat.not_odd_iff_even.mpr hwe, hwu]
    · have h2o : Odd (G2.degree w) := by rcases hodd with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
      rw [hD2 w]
      simp [profile, h2o, hodd]
  have hzero : ∀ x, G2.Adj w x → D2.ends x = 0 → x = u := by
    intro x hwx h0
    have hxw : x ≠ w := fun h => G2.loopless.irrefl w (h ▸ hwx)
    have hxa : x ≠ a := fun h => ((hE2 s(w, x)).mp hwx).2.1 (by rw [h, Sym2.eq_swap])
    have hxa' : x ≠ a' := fun h => ((hE2 s(w, x)).mp hwx).2.2 (by rw [h, Sym2.eq_swap])
    rw [hD2x x hxa hxa' hxw] at h0
    by_contra hxu
    unfold profile at h0
    by_cases ho : Odd (G.degree x)
    · simp [ho] at h0
    · have hxE : x ∈ evenSet G := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        G.degree_pos_iff_exists_adj x |>.mpr ⟨w, (hadj2 _ _ hwx).symm⟩,
        Nat.not_odd_iff_even.mp ho⟩
      simp [ho, Finset.mem_erase, hxu, hxE] at h0
  -- Fan's grouped lemma at `w` for the two deleted edges
  have hsum : (Finset.univ.filter (fun x => G2.Adj w x ∧ D2.ends x = 0)).card <
      ∑ t ∈ ({a, a'} : Finset V), D2.ends t := by
    rw [Finset.sum_pair haa', hD2a, hD2a']
    have hsub : Finset.univ.filter (fun x => G2.Adj w x ∧ D2.ends x = 0) ⊆ {u} := by
      intro x hx
      rw [Finset.mem_filter] at hx
      exact Finset.mem_singleton.mpr (hzero x hx.2.1 hx.2.2)
    have := Finset.card_le_card hsub
    rw [Finset.card_singleton] at this
    omega
  have hwT : w ∉ ({a, a'} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hne, Ne.symm hne'⟩
  have hT : ∀ t ∈ ({a, a'} : Finset V), ¬ G2.Adj t w := by
    intro t ht h
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact ((hE2 _).mp h).2.1 rfl
    · rw [Finset.mem_singleton] at ht
      subst ht
      exact ((hE2 _).mp h).2.2 rfl
  obtain ⟨t, ht, hK⟩ := fan_grouped D2 w {a, a'} hwT hT hsum
  -- finish with `fan_single` at the other edge
  have finish : ∀ t t', ((t = a ∧ t' = a') ∨ (t = a' ∧ t' = a)) →
      (∀ K' : SimpleGraph V, (∀ e, e ∈ K'.edgeSet ↔ e ∈ G2.edgeSet ∨ e = s(t, w)) →
        ∃ D' : PathDecomp K', D'.size = D2.size ∧
          ∀ x, D'.ends x + (if t = x then 1 else 0) = D2.ends x + (if w = x then 1 else 0)) →
      Realisable G (((evenSet G).erase u).erase t) := by
    intro t t' htt hK
    have htt' : t ≠ t' := by
      rcases htt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact haa'
      · exact Ne.symm haa'
    have ht'w : G.Adj t' w := by
      rcases htt with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact ha'w
      · exact haw
    have htE : t ∈ evenSet G := by
      rcases htt with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ha
      · exact ha'
    have ht'E : t' ∈ evenSet G := by
      rcases htt with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact ha'
      · exact ha
    have hut : u ≠ t := by
      rcases htt with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hua
      · exact hua'
    have hut' : u ≠ t' := by
      rcases htt with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact hua'
      · exact hua
    have htw : t ≠ w := by
      rcases htt with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hne
      · exact hne'
    have ht'w' : t' ≠ w := G.ne_of_adj ht'w
    have hD2t : D2.ends t = 1 := by
      rcases htt with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hD2a
      · exact hD2a'
    have hD2t' : D2.ends t' = 1 := by
      rcases htt with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact hD2a'
      · exact hD2a
    have hnot : ∀ x, x ≠ t → x ≠ t' → x ≠ a ∧ x ≠ a' := by
      intro x h1 h2
      rcases htt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨h1, h2⟩
      · exact ⟨h2, h1⟩
    obtain ⟨D', -, hD'⟩ := hK (rmEdge G t' w)
      (edgeSet_readd hE2 htt haa' haw ha'w)
    have hDt : D'.ends t = 0 := by
      have := hD' t
      simp only [ite_true, Ne.symm htw, ite_false, add_zero, hD2t] at this
      omega
    have hDt' : D'.ends t' = 1 := by
      have := hD' t'
      simp only [htt', Ne.symm ht'w', ite_false, add_zero, hD2t'] at this
      exact this
    have hDw : D'.ends w = D2.ends w + 1 := by
      have := hD' w
      simp only [htw, ite_false, ite_true, add_zero] at this
      exact this
    have hDx : ∀ x, x ≠ t → x ≠ t' → x ≠ w →
        D'.ends x = profile G ((evenSet G).erase u) x := by
      intro x h1 h2 h3
      have := hD' x
      simp only [Ne.symm h1, Ne.symm h3, ite_false, add_zero] at this
      rw [this]
      exact hD2x x (hnot x h1 h2).1 (hnot x h1 h2).2 h3
    -- zeros of `D'` next to `t'` are among `t, u`
    have hz : ∀ x, (rmEdge G t' w).Adj t' x → D'.ends x = 0 → x = t ∨ x = u := by
      intro x hx h0
      by_cases hxt : x = t
      · exact Or.inl hxt
      · right
        have hxt' : x ≠ t' := fun h => G.loopless.irrefl t' (h ▸ hx.1)
        have hxw : x ≠ w := fun h => hx.2 (by rw [h])
        rw [hDx x hxt hxt' hxw] at h0
        by_contra hxu
        unfold profile at h0
        by_cases ho : Odd (G.degree x)
        · simp [ho] at h0
        · have hxE : x ∈ evenSet G := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            G.degree_pos_iff_exists_adj x |>.mpr ⟨t', hx.1.symm⟩, Nat.not_odd_iff_even.mp ho⟩
          simp [ho, Finset.mem_erase, hxu, hxE] at h0
    have hprof : profile G (((evenSet G).erase u).erase t) w = profile G ((evenSet G).erase u) w := by
      unfold profile
      have : w ∈ ((evenSet G).erase u).erase t ↔ w ∈ (evenSet G).erase u := by
        simp [Finset.mem_erase, Ne.symm htw]
      simp only [this]
    refine pair_finish ht'w htE ht'E hut hut' htt' D' hDt hDt' hDx (by rw [hDw, hD2w, hprof]) ?_
    rw [hDw, hD2w]
    rcases hw with ⟨hwE, -⟩ | ⟨hodd, hcase⟩
    · -- even `w`: at most two zeros, and `D'` has three ends at `w`
      have hsub : Finset.univ.filter (fun x => (rmEdge G t' w).Adj t' x ∧ D'.ends x = 0) ⊆
          {t, u} := by
        intro x hx
        rw [Finset.mem_filter] at hx
        rcases hz x hx.2.1 hx.2.2 with rfl | rfl <;> simp
      have h1 := (Finset.card_le_card hsub).trans (Finset.card_le_two)
      have hwu : w ∈ (evenSet G).erase u := Finset.mem_erase.mpr ⟨Ne.symm huw, hwE⟩
      simp only [profile, not_odd_of_mem_evenSet hwE, hwu, ite_true, ite_false]
      omega
    · -- odd `w`: at most one zero
      have hpw : profile G ((evenSet G).erase u) w = 1 := by simp [profile, hodd]
      rw [hpw]
      have hsub : ∃ y, Finset.univ.filter
          (fun x => (rmEdge G t' w).Adj t' x ∧ D'.ends x = 0) ⊆ {y} := by
        rcases hcase with hna | ⟨hnu, hnu'⟩
        · refine ⟨u, fun x hx => ?_⟩
          rw [Finset.mem_filter] at hx
          rcases hz x hx.2.1 hx.2.2 with rfl | rfl
          · exfalso
            have := hx.2.1.1
            rcases htt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hna this.symm
            · exact hna this
          · exact Finset.mem_singleton_self _
        · refine ⟨t, fun x hx => ?_⟩
          rw [Finset.mem_filter] at hx
          rcases hz x hx.2.1 hx.2.2 with rfl | rfl
          · exact Finset.mem_singleton_self _
          · exfalso
            have := hx.2.1.1
            rcases htt with ⟨-, rfl⟩ | ⟨-, rfl⟩
            · exact hnu' this
            · exact hnu this
      obtain ⟨y, hy⟩ := hsub
      have := Finset.card_le_card hy
      rw [Finset.card_singleton] at this
      omega
  rcases Finset.mem_insert.mp ht with rfl | ht
  · exact Or.inl (finish t a' (Or.inl ⟨rfl, rfl⟩) hK)
  · rw [Finset.mem_singleton] at ht
    subst ht
    exact Or.inr (finish t a (Or.inr ⟨rfl, rfl⟩) hK)

/-- **Pair step.** Let `u, a, a'` be distinct even vertices and `w ≠ u` a common neighbour of `a`
and `a'`. Suppose that `w` is even of degree at least `4`, or that `w` is odd and `aa' ∉ E` or
neither `a` nor `a'` is adjacent to `u`. Then `Ev \ {u, a}` or `Ev \ {u, a'}` is realisable.

Proof: Lemma 3 in `G − aw − a'w` (exceptional vertex `u`), Fan's grouped lemma for the two
edges into `w` (it puts back one of them, say `tw`), then Fan's single lemma for the other. -/
theorem realisable_pair (hL : LovaszStatement.{u}) (hG : ∀ v, 0 < G.degree v)
    (hn : Even (Fintype.card V)) {u a a' w : V} (hu : u ∈ evenSet G) (ha : a ∈ evenSet G)
    (ha' : a' ∈ evenSet G) (hua : u ≠ a) (hua' : u ≠ a') (haa' : a ≠ a') (huw : u ≠ w)
    (haw : G.Adj a w) (ha'w : G.Adj a' w)
    (hw : (w ∈ evenSet G ∧ 4 ≤ G.degree w) ∨
      (Odd (G.degree w) ∧ (¬ G.Adj a a' ∨ (¬ G.Adj a u ∧ ¬ G.Adj a' u)))) :
    Realisable G (((evenSet G).erase u).erase a) ∨
      Realisable G (((evenSet G).erase u).erase a') := by
  obtain ⟨d2a, d2a', d2w, d2x⟩ := degree_delEdge₂ haa' haw ha'w
  exact pair_core hL hn (rmEdge (rmEdge G a w) a' w)
    (fun e => by rw [rmEdge_edgeSet, rmEdge_edgeSet, and_assoc]) d2a d2a' d2w d2x hG hu ha ha'
    hua hua' haa' huw haw ha'w hw

/-! ### Certificates along paths -/

/-- The moves along a path `x, y₁, …, y_k`. -/
def pathMoves : V → List V → List (V × V)
  | _, [] => []
  | x, y :: l => (x, y) :: pathMoves y l

/-- `OddPath G u x l`: `x, l` is a walk ending at an even vertex `t ≠ u` with `t ≁ u`, whose
interior vertices are odd of degree at least `3`, different from `u` and not adjacent to `u`. -/
def OddPath (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : V → List V → Prop
  | _, [] => False
  | x, [t] => G.Adj x t ∧ t ∈ evenSet G ∧ t ≠ u ∧ ¬ G.Adj t u
  | x, y :: z :: l => G.Adj x y ∧ Odd (G.degree y) ∧ 1 < G.degree y ∧ y ≠ u ∧ ¬ G.Adj y u ∧
      OddPath G u y (z :: l)

/-- Deleting an edge `ab` with `a` off the path and `b` off its tail keeps an `OddPath`. -/
theorem OddPath.rmEdge {u a b : V} : ∀ {y : V} {l : List V}, OddPath G u y l → a ∉ y :: l →
    b ∉ l → OddPath (rmEdge G a b) u y l
  | _, [], h, _, _ => h.elim
  | y, [t], ⟨hyt, ht, htu, htu'⟩, ha, hb => by
    have hat : t ≠ a := fun h => ha (by simp [h])
    have hbt : t ≠ b := fun h => hb (by simp [h])
    refine ⟨⟨hyt, fun he => ?_⟩, ?_, htu, fun h => htu' h.1⟩
    · rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact ha (by simp [h1])
      · exact hat h2
    · have := rmEdge_degree_of_ne (G := G) hat hbt
      simp only [evenSet, Finset.mem_filter, Finset.mem_univ, true_and, this] at ht ⊢
      exact ht
  | y, z :: w :: l, ⟨hyz, hzo, hz3, hzu, hzu', hP⟩, ha, hb => by
    have haz : z ≠ a := fun h => ha (by simp [h])
    have hbz : z ≠ b := fun h => hb (by simp [h])
    have hdz := rmEdge_degree_of_ne (G := G) haz hbz
    refine ⟨?_, hdz ▸ hzo, hdz ▸ hz3, hzu, fun h => hzu' h.1,
      OddPath.rmEdge hP (fun h => ha (List.mem_cons_of_mem _ h))
        (fun h => hb (List.mem_cons_of_mem _ h))⟩
    refine ⟨hyz, fun he => ?_⟩
    rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact ha (by simp [h1])
    · exact haz h2

/-- The moves along an `OddPath` from `x` form a Fan certificate for `{x, u}`: odd transfers along
the interior, then an even step into the last vertex. -/
theorem fanCert_of_oddPath {u : V} : ∀ {x : V} {l : List V} (G : SimpleGraph V)
    [DecidableRel G.Adj], OddPath G u x l → (x :: l).Nodup → x ≠ u →
    FanCert G {x, u} (pathMoves x l)
  | _, [], _, _, h, _, _ => h.elim
  | x, [t], G, _, ⟨hxt, ht, htu, htu'⟩, hnd, hxu => by
    have hxt' : x ≠ t := G.ne_of_adj hxt
    have hXe : ({x, u} : Finset V).erase x = {u} :=
      Finset.erase_insert (by simp [hxu])
    refine ⟨Finset.mem_insert_self _ _, hxt, ?_, Or.inl ⟨ht, ?_, ?_⟩⟩
    · intro y hy hyx
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact absurd rfl hyx
      · exact htu'
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hxt', htu⟩
    · show (({x, u} : Finset V).erase x).card ≤ 1
      rw [hXe, Finset.card_singleton]
  | x, y :: z :: l, G, _, ⟨hxy, hyo, hy3, hyu, hyu', hP⟩, hnd, hxu => by
    have hXe : ({x, u} : Finset V).erase x = {u} :=
      Finset.erase_insert (by simp [hxu])
    refine ⟨Finset.mem_insert_self _ _, hxy, ?_, Or.inr ⟨hyo, hy3, ?_⟩⟩
    · intro w hw hwx
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact absurd rfl hwx
      · exact hyu'
    · have hins : insert y (({x, u} : Finset V).erase x) = {y, u} := by rw [hXe]
      rw [hins]
      have hnd' := List.nodup_cons.mp hnd
      exact fanCert_of_oddPath (rmEdge G x y) (hP.rmEdge hnd'.1
        (List.nodup_cons.mp hnd'.2).1) hnd'.2 hyu

/-- **Path transfer.** Let `a ≠ u` be even and let `a, l` be an `OddPath` for `u` (odd interior
vertices of degree `≥ 3` not adjacent to `u`, ending at an even vertex `t ∉ {u}` with `t ≁ u`), with
distinct vertices. Then `Ev \ {a, u}` is realisable. -/
theorem realisable_of_oddPath (hL : LovaszStatement.{u}) (hG : ∀ v, 0 < G.degree v)
    (hn : Even (Fintype.card V)) {u a : V} {l : List V} (ha : a ∈ evenSet G)
    (hu : u ∈ evenSet G) (hau : a ≠ u) (hP : OddPath G u a l) (hnd : (a :: l).Nodup) :
    Realisable G (((evenSet G).erase a).erase u) := by
  have h := realisable_of_fanCert hL hn (pathMoves a l) G {a, u} hG
    (Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hu)) (fanCert_of_oddPath G hP hnd hau)
  have : evenSet G \ {a, u} = ((evenSet G).erase a).erase u := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
    tauto
  rwa [this] at h

/-! ### An obstruction -/

omit [Fintype V] [DecidableRel G.Adj] in
/-- In any decomposition, `deg v + ends v ≤ 2 |D|`: a path has at most two edges at `v`, and one
fewer for each of its ends at `v`. -/
theorem PathDecomp.degree_add_ends_le (D : PathDecomp G) (v : V) [Fintype (G.neighborSet v)] :
    G.degree v + D.ends v ≤ 2 * D.size := by
  rw [D.degree_eq_sum v]
  unfold PathDecomp.ends PathDecomp.size
  rw [← sum_map_add']
  calc (D.paths.map (fun P => P.incid v + P.endsAt v)).sum
      ≤ (D.paths.map (fun _ => 2)).sum := sum_map_le_sum_map _ _ _ (fun P _ => by
        have := P.incid_add_endsAt v
        split_ifs at this <;> omega)
    _ = 2 * D.paths.length := by
        rw [List.map_const', List.sum_replicate, smul_eq_mul, mul_comm]

/-- **Obstruction (O1).** In a tight graph every odd vertex has degree at most `#odd − 1`. For a
graph of order `n` with exactly two even vertices this excludes an odd vertex of degree `n − 1`. -/
theorem degree_le_of_tight {H : SimpleGraph V} [DecidableRel H.Adj] (h : Tight H) {w : V}
    (hw : Odd (H.degree w)) : H.degree w + 1 ≤ (oddSet H).card := by
  obtain ⟨-, D, hD⟩ := h
  have hsz := Realises.size_eq (Finset.empty_subset _) hD
  have h1 := D.degree_add_ends_le w
  have hw1 : D.ends w = 1 := by rw [hD w]; simp [profile, hw]
  obtain ⟨k, hk⟩ := H.even_card_odd_degree_vertices
  unfold oddSet at hsz ⊢
  rw [Finset.card_empty, add_zero] at hsz
  omega

/-! ### The leaf move (L) and the leaf case of the two-even problem -/

omit [Fintype V] [DecidableRel G.Adj] in
/-- A path decomposition has no more ends at a vertex than the vertex has edges. -/
theorem PathDecomp.ends_le_degree (D : PathDecomp G) (v : V) [Fintype (G.neighborSet v)] :
    D.ends v ≤ G.degree v := by
  rw [D.degree_eq_sum v]
  unfold PathDecomp.ends
  apply sum_map_le_sum_map
  intro P _
  have h := P.incid_add_endsAt v
  have hne := P.src_ne_tgt
  unfold GPath.endsAt at h ⊢
  split_ifs at h ⊢ with h1 h2 h2 <;> simp_all

/-- **Move (L)**, in the language of `leaves`: attach a pendant vertex at an odd vertex `x`.
A realisation of `S` in `G` gives a realisation of the same set in `G` plus the pendant edge, in
which `x` (now even) has no end. -/
theorem realisable_leaves_singleton {S : Finset V} {x : V} (hx : Odd (G.degree x))
    (h : Realisable G S) :
    Realisable (leaves G (insert x ∅)) (S.map Function.Embedding.inl) := by
  obtain ⟨hS, D, hD⟩ := h
  obtain ⟨D₁, -, he₁⟩ := leaves_empty_decomp (G := G) D
  have hpos : 0 < D₁.ends (.inl x) := by rw [he₁ x, hD x]; simp [profile, hx]
  obtain ⟨D₂, -, he₂⟩ := D₁.extend_pendant (leaves_insert_edgeSet (G := G))
    (leaves_inr_isolated (G := G) (Finset.notMem_empty x)) ⟨rfl, Finset.mem_insert_self _ _⟩ hpos
  have hxS : x ∉ S := fun h => not_odd_of_mem_evenSet (hS h) hx
  have hiso : ∀ v, D₁.ends (.inr v) = 0 := by
    intro v
    have := D₁.ends_le_degree (.inr v)
    rw [leaves_degree_inr] at this
    simpa using this
  have hdl : ∀ v, (leaves G (insert x ∅)).degree (.inl v) = G.degree v + if v = x then 1 else 0 := by
    intro v
    rw [leaves_degree_inl]
    congr 1
    simp only [Finset.mem_insert, Finset.notMem_empty, or_false]
  have hdr : ∀ v, (leaves G (insert x ∅)).degree (.inr v) = if v = x then 1 else 0 := by
    intro v
    rw [leaves_degree_inr]
    simp only [Finset.mem_insert, Finset.notMem_empty, or_false]
  have hml : ∀ v, (Sum.inl v : V ⊕ V) ∈ S.map Function.Embedding.inl ↔ v ∈ S := by
    intro v; simp
  have hmr : ∀ v, (Sum.inr v : V ⊕ V) ∉ S.map Function.Embedding.inl := by
    intro v; simp
  refine ⟨?_, D₂, fun w => ?_⟩
  · intro y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hy
    have hsx : s ≠ x := fun h => hxS (h ▸ hs)
    have := (Finset.mem_filter.mp (hS hs)).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [Function.Embedding.inl_apply, hdl s]
    simp only [hsx, ite_false, add_zero]
    exact this
  · have hw := he₂ w
    unfold profile
    rcases w with v | v
    · simp only [hdl v, hml v]
      by_cases hvx : v = x
      · subst hvx
        have hDv : D.ends v = 1 := by have := hD v; simpa [profile, hx] using this
        have h0 : D₂.ends (.inl v) = 0 := by
          have := hw; simp only [ite_true, reduceCtorEq, ite_false, add_zero, he₁, hDv] at this
          omega
        have : ¬ Odd (G.degree v + 1) := by rw [Nat.odd_add_one]; exact not_not.mpr hx
        simp only [ite_true, this, hxS, ite_false, h0]
      · simp only [Sum.inl.injEq, Ne.symm hvx, ite_false, reduceCtorEq, add_zero, he₁] at hw
        simp only [hw, hvx, ite_false, add_zero]
        exact hD v
    · simp only [hdr v, hmr v, ite_false]
      by_cases hvx : v = x
      · subst hvx
        have h1 : D₂.ends (.inr v) = 1 := by
          have := hw
          simp only [reduceCtorEq, ite_false, add_zero, ite_true, hiso] at this
          omega
        rw [h1]
        simp only [ite_true]
        decide
      · have h0 : D₂.ends (.inr v) = 0 := by
          have := hw
          simp only [reduceCtorEq, ite_false, Sum.inr.injEq, Ne.symm hvx, add_zero, hiso] at this
          exact this
        convert h0 using 1
        simp [hvx]

/-- **The leaf case of the two-even problem**: if `G` has at most one even vertex and `x` is odd,
then `G` plus a pendant vertex at `x` is tight. -/
theorem tight_leaves_of_lovasz (hL : LovaszStatement.{u}) {x : V}
    (h1 : (Finset.univ.filter (fun v => Even (G.degree v))).card ≤ 1) (hx : Odd (G.degree x)) :
    Tight (leaves G (insert x ∅)) := by
  have hR : Realisable G ∅ := by
    obtain ⟨D, hD⟩ := pathNumber_spec G
    have hle := hL V G h1
    have hcard : 2 * D.size ≤ (Finset.univ.filter (fun v => Odd (G.degree v))).card := by
      have hc := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset V)) (fun v => Odd (G.degree v))
      have he : Finset.univ.filter (fun v => ¬ Odd (G.degree v)) =
          Finset.univ.filter (fun v => Even (G.degree v)) := by
        ext v; simp [Nat.not_odd_iff_even]
      rw [he, Finset.card_univ] at hc
      obtain ⟨k, hk⟩ := G.even_card_odd_degree_vertices
      omega
    refine ⟨Finset.empty_subset _, D, fun v => ?_⟩
    rw [PathDecomp.ends_eq_of_tight D hcard v]
    simp [profile]
  have := realisable_leaves_singleton hx hR
  simpa using this

end Gallai
