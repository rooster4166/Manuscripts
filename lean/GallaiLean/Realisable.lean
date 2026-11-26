import GallaiLean.Retract

/-!
# Realisable sets (endpoint-structure manuscript, Section 2)

For a finite graph `G`, `oddSet G` is the set of odd-degree vertices and `evenSet G` the set of
even vertices of positive degree. A set `S ⊆ evenSet G` is *realisable* if some path
decomposition has exactly one end at every odd vertex, two at every vertex of `S` and none at the
other vertices (`profile G S`).

* `Realises.size_eq`: such a decomposition has `#odd / 2 + |S|` paths.
* `Realisable.insert`, `Realisable.mono` (Lemma 1, up-closure).
* `LovaszStatement`: Lovász's theorem, as an explicit hypothesis.
* `apex G T`: `G` plus a vertex `none` adjacent to the vertices of `T`.
* `realisable_of_apex`: if the apex graph has at most one even vertex, then (under Lovász) `T` is
  realisable. This is the device in the proofs of Lemmas 2 and 3.
* `realisable_evenSet` (Lemma 2, faithful partitions): `evenSet G` is realisable when `G` has no
  isolated vertex.
* `realisable_evenSet_erase` (Lemma 3): at even order, `evenSet G \ {u}` is realisable for every
  `u ∈ evenSet G`.
-/

open SimpleGraph

namespace Gallai

universe u

/-- **Lovász's theorem** (as a hypothesis): a graph on `N` vertices with at most one vertex of
even degree (isolated vertices count as even) has a path decomposition into `⌊N/2⌋` paths. -/
def LovaszStatement : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    (Finset.univ.filter (fun v => Even (G.degree v))).card ≤ 1 →
      pathNumber G ≤ Fintype.card W / 2

variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Odd-degree vertices. -/
def oddSet : Finset V := Finset.univ.filter (fun v => Odd (G.degree v))

/-- Even vertices of positive degree. -/
def evenSet : Finset V := Finset.univ.filter (fun v => 0 < G.degree v ∧ Even (G.degree v))

/-- The end profile of a realisation of `S`. -/
def profile (S : Finset V) (v : V) : ℕ :=
  if Odd (G.degree v) then 1 else if v ∈ S then 2 else 0

/-- `D` realises `S`. -/
def Realises (D : PathDecomp G) (S : Finset V) : Prop := ∀ v, D.ends v = profile G S v

/-- `S` is realisable. -/
def Realisable (S : Finset V) : Prop := S ⊆ evenSet G ∧ ∃ D : PathDecomp G, Realises G D S

variable {G}

omit [DecidableEq V] in
theorem not_odd_of_mem_evenSet {v : V} (hv : v ∈ evenSet G) : ¬ Odd (G.degree v) :=
  Nat.not_odd_iff_even.mpr (Finset.mem_filter.mp hv).2.2

/-- **Size identity**: a realisation of `S` has `#odd / 2 + |S|` paths. -/
theorem Realises.size_eq {S : Finset V} {D : PathDecomp G} (hS : S ⊆ evenSet G)
    (hD : Realises G D S) : D.size = (oddSet G).card / 2 + S.card := by
  have h1 := D.sum_ends
  have hp : ∀ v, profile G S v =
      (if Odd (G.degree v) then 1 else 0) + (if v ∈ S then 2 else 0) := by
    intro v
    unfold profile
    by_cases ho : Odd (G.degree v)
    · have : v ∉ S := fun hv => not_odd_of_mem_evenSet (hS hv) ho
      simp [ho, this]
    · simp [ho]
  have h2 : ∑ v, D.ends v = (oddSet G).card + 2 * S.card := by
    rw [Finset.sum_congr rfl (fun v _ => (hD v).trans (hp v)), Finset.sum_add_distrib,
      ← Finset.card_filter, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul]
    unfold oddSet
    ring
  obtain ⟨k, hk⟩ := G.even_card_odd_degree_vertices
  unfold oddSet at h2 ⊢
  omega

/-- **Up-closure**, one vertex at a time: split a path at an interior visit of `v`. -/
theorem Realisable.insert {S : Finset V} {v : V} (h : Realisable G S) (hv : v ∈ evenSet G)
    (hvS : v ∉ S) : Realisable G (insert v S) := by
  obtain ⟨hS, D, hD⟩ := h
  have hv' := (Finset.mem_filter.mp hv).2
  have h0 : D.ends v = 0 := by
    rw [hD v]; unfold profile; simp [not_odd_of_mem_evenSet hv, hvS]
  obtain ⟨D', -, hD'⟩ := D.exists_split_of_ends_eq_zero hv'.1 h0
  refine ⟨Finset.insert_subset hv hS, D', fun w => ?_⟩
  rw [hD', hD w]
  unfold profile
  by_cases hw : v = w
  · subst hw; simp [not_odd_of_mem_evenSet hv, hvS]
  · simp [hw, Ne.symm hw]

/-- **Up-closure** (Lemma 1). -/
theorem Realisable.mono {S T : Finset V} (h : Realisable G S) (hST : S ⊆ T)
    (hT : T ⊆ evenSet G) : Realisable G T := by
  have key : ∀ U : Finset V, U ⊆ evenSet G → Disjoint U S → Realisable G (U ∪ S) := by
    intro U
    induction U using Finset.induction_on with
    | empty => intro _ _; simpa using h
    | @insert a U ha ih =>
      intro hU hdisj
      have ih := ih ((Finset.subset_insert a U).trans hU)
        (Finset.disjoint_of_subset_left (Finset.subset_insert a U) hdisj)
      rw [Finset.insert_union]
      refine ih.insert (hU (Finset.mem_insert_self a U)) ?_
      rw [Finset.mem_union, not_or]
      exact ⟨ha, Finset.disjoint_left.mp hdisj (Finset.mem_insert_self a U)⟩
  have := key (T \ S) (Finset.sdiff_subset.trans hT) Finset.sdiff_disjoint
  rwa [Finset.sdiff_union_of_subset hST] at this

/-! ### The apex extension -/

variable (G) in
/-- `G` plus a vertex `none` adjacent exactly to the vertices of `T`. -/
def apex (T : Finset V) : SimpleGraph (Option V) where
  Adj x y := match x, y with
    | some a, some b => G.Adj a b
    | none, some b => b ∈ T
    | some a, none => a ∈ T
    | none, none => False
  symm := ⟨fun x y h => by
    cases x <;> cases y <;> simp only at h ⊢
    · exact h
    · exact h
    · exact h.symm⟩
  loopless := ⟨fun x h => by
    cases x <;> simp only at h
    exact G.loopless.irrefl _ h⟩

variable {T : Finset V}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem apex_adj_some_some {a b : V} : (apex G T).Adj (some a) (some b) ↔ G.Adj a b :=
  Iff.rfl
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem apex_adj_none_some {b : V} : (apex G T).Adj none (some b) ↔ b ∈ T := Iff.rfl
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem apex_adj_some_none {a : V} : (apex G T).Adj (some a) none ↔ a ∈ T := Iff.rfl
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem apex_not_adj_none_none : ¬ (apex G T).Adj none none := id

instance apex.decRel (T : Finset V) : DecidableRel (apex G T).Adj := fun x y =>
  match x, y with
  | some a, some b => inferInstanceAs (Decidable (G.Adj a b))
  | none, some b => inferInstanceAs (Decidable (b ∈ T))
  | some a, none => inferInstanceAs (Decidable (a ∈ T))
  | none, none => inferInstanceAs (Decidable False)

theorem apex_degree_some (v : V) :
    (apex G T).degree (some v) = G.degree v + if v ∈ T then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
    neighborFinset_eq_filter, neighborFinset_eq_filter (G := G), Finset.card_filter,
    Finset.card_filter, Fintype.sum_option]
  simp only [apex_adj_some_none, apex_adj_some_some]
  ring

theorem apex_degree_none : (apex G T).degree none = T.card := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter,
    Fintype.sum_option]
  simp

variable (G T) in
/-- The apex graph retracts onto `G`. -/
def apexRetract (r : V) : Retract (apex G T) G where
  ι := some
  f := fun x => x.getD r
  kept := Option.isSome
  f_ι _ := rfl
  kept_iff x := by cases x <;> simp
  adj_iff _ _ := Iff.rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The only edge at `some v` leaving `G` is `some v — none`, present iff `v ∈ T`. -/
theorem apex_nonkept {e : Sym2 (Option V)} (he : e ∈ (apex G T).edgeSet)
    (hk : bothKept Option.isSome e = false) {v : V} (hv : some v ∈ e) :
    e = s(some v, none) ∧ v ∈ T := by
  induction e using Sym2.inductionOn with
  | hf x y =>
  rw [mem_edgeSet] at he
  rcases Sym2.mem_iff.mp hv with rfl | rfl
  · cases y with
    | none => exact ⟨rfl, he⟩
    | some b => simp at hk
  · cases x with
    | none => exact ⟨Sym2.eq_swap, he⟩
    | some b => simp at hk

/-- **The apex device.** If `G` plus an apex on `T` has at most one even vertex then, assuming
Lovász's theorem, `T` is realisable. -/
theorem realisable_of_apex (hL : LovaszStatement.{u}) (hT : T ⊆ evenSet G)
    (hcond : (Finset.univ.filter (fun w => Even ((apex G T).degree w))).card ≤ 1) :
    Realisable G T := by
  refine ⟨hT, ?_⟩
  rcases isEmpty_or_nonempty V with hV | ⟨⟨r⟩⟩
  · obtain ⟨D⟩ := PathDecomp.nonempty G
    exact ⟨D, fun v => isEmptyElim v⟩
  -- Lovász on the apex graph, and tightness
  have hp := hL (Option V) (apex G T) hcond
  rw [Fintype.card_option] at hp
  obtain ⟨D₀, hD₀⟩ := pathNumber_spec (apex G T)
  obtain ⟨m, hm⟩ := (apex G T).even_card_odd_degree_vertices
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Option V))) (fun w => Odd ((apex G T).degree w))
  have hev : Finset.univ.filter (fun w => ¬ Odd ((apex G T).degree w)) =
      Finset.univ.filter (fun w => Even ((apex G T).degree w)) := by
    ext w; simp [Nat.not_odd_iff_even]
  rw [hev, Finset.card_univ, Fintype.card_option] at hcard
  have htight := D₀.ends_eq_of_tight (by omega)
  -- make the apex an end of every path through it, then delete it
  obtain ⟨D₁, he₁, hz₁⟩ := D₀.exists_split_all none
  obtain ⟨D₂, hD₂⟩ := (apexRetract G T r).delete D₁ (by
    intro P hP x hx hkx
    cases x with
    | some _ => simp [apexRetract] at hkx
    | none => exact (hz₁ P hP hx).imp Eq.symm Eq.symm)
  have hsome : ∀ v, D₁.ends (some v) = if Odd ((apex G T).degree (some v)) then 1 else 0 :=
    fun v => (he₁ (some v) (Option.some_ne_none v)).trans (htight _)
  have h₂T : ∀ v ∈ T, D₂.ends v = 0 ∨ D₂.ends v = 2 := by
    intro v hv
    have hvE := (Finset.mem_filter.mp (hT hv)).2
    have hle := (hD₂ v).2 (fun e₁ he₁ e₂ he₂ hk₁ hk₂ hv₁ hv₂ => by
      rw [(apex_nonkept he₁ hk₁ hv₁).1, (apex_nonkept he₂ hk₂ hv₂).1])
    have h1 : D₁.ends (some v) = 1 := by
      rw [hsome, apex_degree_some]
      simp [hv, Nat.odd_add_one, Nat.not_odd_iff_even.mpr hvE.2]
    have hpar := D₂.ends_mod_two v
    have : G.degree v % 2 = 0 := Nat.even_iff.mp hvE.2
    change D₂.ends v ≤ D₁.ends (some v) + 1 at hle
    omega
  have h₂nT : ∀ v ∉ T, D₂.ends v = if Odd (G.degree v) then 1 else 0 := by
    intro v hv
    rw [(hD₂ v).1 (fun e he hk hve => hv (apex_nonkept he hk hve).2)]
    change D₁.ends (some v) = _
    rw [hsome, apex_degree_some]
    simp [hv]
  -- repair the vertices of `T` left without ends
  obtain ⟨D₃, -, he₃⟩ := D₂.exists_split_set (T.filter (fun v => D₂.ends v = 0)) (by
    intro z hz
    have hzT := Finset.mem_filter.mp hz
    exact ⟨(Finset.mem_filter.mp (hT hzT.1)).2.1, hzT.2⟩)
  refine ⟨D₃, fun v => ?_⟩
  rw [he₃]
  unfold profile
  by_cases hvT : v ∈ T
  · simp only [not_odd_of_mem_evenSet (hT hvT), ite_false, hvT, ite_true, Finset.mem_filter,
      true_and]
    rcases h₂T v hvT with h | h <;> simp [h]
  · have : v ∉ T.filter (fun v => D₂.ends v = 0) := fun hz => hvT (Finset.mem_filter.mp hz).1
    simp only [this, ite_false, add_zero, h₂nT v hvT, hvT]

/-- **Faithful partitions** (Lemma 2; Cai's theorem from Lovász's): without isolated vertices,
the set of all even vertices is realisable. -/
theorem realisable_evenSet (hL : LovaszStatement.{u}) (hG : ∀ v, 0 < G.degree v) :
    Realisable G (evenSet G) := by
  apply realisable_of_apex hL (subset_refl _)
  calc (Finset.univ.filter (fun w => Even ((apex G (evenSet G)).degree w))).card
      ≤ ({none} : Finset (Option V)).card := by
        apply Finset.card_le_card
        intro w hw
        rw [Finset.mem_filter] at hw
        cases w with
        | none => simp
        | some v =>
          exfalso
          rw [apex_degree_some] at hw
          by_cases hv : v ∈ evenSet G
          · simp only [hv, ite_true] at hw
            exact (Nat.even_add_one.mp hw.2) (Finset.mem_filter.mp hv).2.2
          · simp only [hv, ite_false, add_zero] at hw
            exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG v, hw.2⟩)
    _ = 1 := Finset.card_singleton _

omit [DecidableEq V] in
theorem card_oddSet_add_card_evenSet (hG : ∀ v, 0 < G.degree v) :
    (oddSet G).card + (evenSet G).card = Fintype.card V := by
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset V)) (fun v => Odd (G.degree v))
  have he : Finset.univ.filter (fun v => ¬ Odd (G.degree v)) = evenSet G := by
    ext v; simp [evenSet, hG v, Nat.not_odd_iff_even]
  rw [he, Finset.card_univ] at hc
  exact hc

/-- **Removing one vertex** (Lemma 3): at even order and without isolated vertices,
`evenSet G \ {u}` is realisable for every even `u`. -/
theorem realisable_evenSet_erase (hL : LovaszStatement.{u}) (hG : ∀ v, 0 < G.degree v)
    (hn : Even (Fintype.card V)) {u : V} (hu : u ∈ evenSet G) :
    Realisable G ((evenSet G).erase u) := by
  have hEv : Even (evenSet G).card := by
    have hc := card_oddSet_add_card_evenSet hG
    obtain ⟨a, ha⟩ := G.even_card_odd_degree_vertices
    obtain ⟨b, hb⟩ := hn
    unfold oddSet at hc
    exact ⟨b - a, by omega⟩
  apply realisable_of_apex hL (Finset.erase_subset u _)
  calc (Finset.univ.filter (fun w => Even ((apex G ((evenSet G).erase u)).degree w))).card
      ≤ ({some u} : Finset (Option V)).card := by
        apply Finset.card_le_card
        intro w hw
        rw [Finset.mem_filter] at hw
        cases w with
        | none =>
          exfalso
          rw [apex_degree_none, Finset.card_erase_of_mem hu] at hw
          obtain ⟨b, hb⟩ := hEv
          obtain ⟨c, hc⟩ := hw.2
          have : 0 < (evenSet G).card := Finset.card_pos.mpr ⟨u, hu⟩
          omega
        | some v =>
          by_cases hvu : v = u
          · simp [hvu]
          · exfalso
            rw [apex_degree_some] at hw
            by_cases hv : v ∈ evenSet G
            · have hv' : v ∈ (evenSet G).erase u := Finset.mem_erase.mpr ⟨hvu, hv⟩
              simp only [hv', ite_true] at hw
              exact (Nat.even_add_one.mp hw.2) (Finset.mem_filter.mp hv).2.2
            · have hv' : v ∉ (evenSet G).erase u := fun h => hv (Finset.mem_of_mem_erase h)
              simp only [hv', ite_false, add_zero] at hw
              exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG v, hw.2⟩)
    _ = 1 := Finset.card_singleton _

end Gallai
