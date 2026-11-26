import GallaiLean.Realisable
import GallaiLean.Fan

/-!
# The second descent step and the two-even-vertex problem

(endpoint-structure manuscript, Section "Fan descent")

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

end Gallai
