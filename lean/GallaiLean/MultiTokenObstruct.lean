import GallaiLean.MultiToken

/-!
# An obstruction to multi-token schedules (session `claude/multi-token`)

Manuscript `manuscripts/multi-token`, Proposition 6.1.

Fix a vertex `r` that is odd, and is neither a leaf nor a stem of a tail. Let `A(K)` be the set of
vertices `v ≠ r` of positive degree, not adjacent to `r` and not a leaf of a tail (`nonNbr`), and
`Φ(K)` the number of tokens plus the number of live tails. If
`|A| + 2 ≤ #tokens` and `|A| + 3 ≤ Φ`, then there is no schedule (`not_steerK`):
* no token can enter `r`, since all other tokens would lie in `A`;
* every other move keeps both inequalities: a retirement, a suppression or a drop that isolates its
  stem lowers the left side by at least one and the right side by one, any other move does not
  raise the left side or lower the right side;
* at the end `Φ ≤ 2`.

In the triangle base at a root `r` with `t` non-neighbours in `J − r`, the start has `k + 1` tokens,
`k` live tails and `|A| = t`, so `t < k` excludes every schedule.
-/

open SimpleGraph

namespace Gallai

universe u

section obstruct

variable {U : Type u} [Fintype U] [DecidableEq U]

open Classical in
/-- The non-neighbours of `r` that can host a removal: `v ≠ r`, positive degree, not adjacent to
`r`, not the leaf of a tail. -/
noncomputable def nonNbr (T : Finset (U × U × U)) (K : SimpleGraph U) [DecidableRel K.Adj]
    (r : U) : Finset U :=
  Finset.univ.filter (fun v => v ≠ r ∧ ¬ K.Adj r v ∧ 0 < K.degree v ∧ ∀ t ∈ T, v ≠ t.1)

open Classical in
/-- The live tails. -/
noncomputable def liveSet (T : Finset (U × U × U)) (K : SimpleGraph U) : Finset (U × U × U) :=
  T.filter (fun t => K.Adj t.1 t.2.1)

theorem mem_nonNbr {T : Finset (U × U × U)} {K : SimpleGraph U} [DecidableRel K.Adj] {r v : U} :
    v ∈ nonNbr T K r ↔ v ≠ r ∧ ¬ K.Adj r v ∧ 0 < K.degree v ∧ ∀ t ∈ T, v ≠ t.1 := by
  classical
  unfold nonNbr
  rw [Finset.mem_filter]
  simp

omit [Fintype U] [DecidableEq U] in
theorem mem_liveSet {T : Finset (U × U × U)} {K : SimpleGraph U} {t : U × U × U} :
    t ∈ liveSet T K ↔ t ∈ T ∧ K.Adj t.1 t.2.1 := by
  classical
  unfold liveSet
  rw [Finset.mem_filter]

/-- The invariant of the obstruction. -/
structure ObstrInv (T : Finset (U × U × U)) (K : SimpleGraph U) [DecidableRel K.Adj] (r : U)
    (τ : Finset U) : Prop where
  even : evenSet K = τ
  inv : TailInv T K
  leaf : ∀ t ∈ T, ∀ v, K.Adj t.1 v → v = t.2.1
  rodd : K.degree r % 2 = 1
  tok : (nonNbr T K r).card + 2 ≤ τ.card
  pot : (nonNbr T K r).card + 3 ≤ τ.card + (liveSet T K).card

omit [DecidableEq U] in
/-- A leaf of a tail has degree at most one, so it is not a token. -/
theorem leaf_not_even {T : Finset (U × U × U)} {K : SimpleGraph U} [DecidableRel K.Adj]
    (hleaf : ∀ t ∈ T, ∀ v, K.Adj t.1 v → v = t.2.1) {t : U × U × U} (ht : t ∈ T) :
    t.1 ∉ evenSet K := by
  intro h
  have hpos := (mem_evenSet_iff.mp h)
  have hle : K.degree t.1 ≤ 1 := by
    rw [← card_neighborFinset_eq_degree]
    refine (Finset.card_le_card (t := {t.2.1}) ?_).trans (by simp)
    intro v hv
    rw [mem_neighborFinset] at hv
    rw [Finset.mem_singleton]
    exact hleaf t ht v hv
  omega

omit [Fintype U] [DecidableEq U] in
/-- A dead leaf is isolated. -/
theorem dead_leaf_isolated {T : Finset (U × U × U)} {K : SimpleGraph U}
    (hleaf : ∀ t ∈ T, ∀ v, K.Adj t.1 v → v = t.2.1) {t : U × U × U} (ht : t ∈ T)
    (hd : ¬ K.Adj t.1 t.2.1) (v : U) : ¬ K.Adj t.1 v := fun h => hd ((hleaf t ht v h) ▸ h)

omit [Fintype U] in
/-- The token count after a move. -/
theorem card_tau_move {τ τ' : Finset U} {K' : SimpleGraph U} {p u : U} (hp : p ∈ τ) (hu : u ∉ τ)
    (hτ' : ∀ v, v ∈ τ' ↔ (v ∈ τ ∧ v ≠ p) ∨ (v = u ∧ ∃ q, K'.Adj u q)) :
    ((∃ q, K'.Adj u q) → τ'.card = τ.card) ∧ (¬ (∃ q, K'.Adj u q) → τ'.card + 1 = τ.card) := by
  have hc := Finset.card_erase_of_mem hp
  have hpos : 0 < τ.card := Finset.card_pos.mpr ⟨p, hp⟩
  constructor
  · intro h
    have : τ' = insert u (τ.erase p) := by
      ext v
      rw [hτ', Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, -⟩)
        · exact Or.inr ⟨h2, h1⟩
        · exact Or.inl h1
      · rintro (h1 | ⟨h2, h1⟩)
        · exact Or.inr ⟨h1, h⟩
        · exact Or.inl ⟨h1, h2⟩
    rw [this, Finset.card_insert_of_notMem (fun h' => hu (Finset.mem_of_mem_erase h')), hc]
    omega
  · intro h
    have : τ' = τ.erase p := by
      ext v
      rw [hτ', Finset.mem_erase]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨-, h1⟩)
        · exact ⟨h2, h1⟩
        · exact absurd h1 h
      · rintro ⟨h2, h1⟩
        exact Or.inl ⟨h1, h2⟩
    rw [this, hc]
    omega

omit [Fintype U] in
/-- The token count after a drop. -/
theorem card_tau_drop {τ τ' : Finset U} {K' : SimpleGraph U} {s : U} (hs : s ∉ τ)
    (hτ' : ∀ v, v ∈ τ' ↔ v ∈ τ ∨ (v = s ∧ ∃ q, K'.Adj s q)) :
    ((∃ q, K'.Adj s q) → τ'.card = τ.card + 1) ∧ (¬ (∃ q, K'.Adj s q) → τ'.card = τ.card) := by
  constructor
  · intro h
    have : τ' = insert s τ := by
      ext v
      rw [hτ', Finset.mem_insert]
      constructor
      · rintro (h1 | ⟨h1, -⟩)
        · exact Or.inr h1
        · exact Or.inl h1
      · rintro (h1 | h1)
        · exact Or.inr ⟨h1, h⟩
        · exact Or.inl h1
    rw [this, Finset.card_insert_of_notMem hs]
  · intro h
    have : τ' = τ := by
      ext v
      rw [hτ']
      constructor
      · rintro (h1 | ⟨-, h1⟩)
        · exact h1
        · exact absurd h1 h
      · exact Or.inl
    rw [this]

/-- No token can enter `r`. -/
theorem obstr_no_entry {T : Finset (U × U × U)} {K : SimpleGraph U} [DecidableRel K.Adj] {r : U}
    {τ : Finset U} (hI : ObstrInv T K r τ) {p : U} (hp : p ∈ τ)
    (hno : ∀ v ∈ τ, v ≠ p → ¬ (delEdge K r p).Adj r v) : False := by
  have hsub : τ.erase p ⊆ nonNbr T K r := by
    intro v hv
    obtain ⟨hvp, hvτ⟩ := Finset.mem_erase.mp hv
    have hvE : v ∈ evenSet K := hI.even ▸ hvτ
    rw [mem_nonNbr]
    refine ⟨fun h => ?_, fun h => hno v hvτ hvp ⟨h, ?_⟩, (mem_evenSet_iff.mp hvE).1,
      fun t ht h => leaf_not_even hI.leaf ht (h ▸ hvE)⟩
    · subst h
      have := (mem_evenSet_iff.mp hvE).2
      have := hI.rodd
      omega
    · rw [Sym2.eq_iff]
      rintro (⟨-, h⟩ | ⟨h1, h2⟩)
      · exact hvp h
      · exact hvp (h2.trans h1)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hp] at h1
  have := hI.tok
  have hpos : 0 < τ.card := Finset.card_pos.mpr ⟨p, hp⟩
  omega

/-- A move that does not enter `r` keeps the invariant. -/
theorem obstr_move {T : Finset (U × U × U)} {K : SimpleGraph U} [DecidableRel K.Adj] {r : U}
    {τ τ' : Finset U} (hI : ObstrInv T K r τ) {p u : U} (hp : p ∈ τ) (hpu : K.Adj p u)
    (hu : u ∉ τ) (hoff : OffTails T K u) (hur : u ≠ r)
    (hτ' : ∀ v, v ∈ τ' ↔ (v ∈ τ ∧ v ≠ p) ∨ (v = u ∧ ∃ q, (delEdge K u p).Adj u q)) :
    ObstrInv T (delEdge K u p) r τ' := by
  have hpE : p ∈ evenSet K := hI.even ▸ hp
  have huE : u ∉ evenSet K := hI.even ▸ hu
  have hpr : p ≠ r := by
    rintro rfl
    have := (mem_evenSet_iff.mp hpE).2
    have := hI.rodd
    omega
  have hdeg := delEdge_degree K hpu.symm
  -- the invariant pieces
  have hE' : evenSet (delEdge K u p) = τ' := evenSet_move K hpE hpu huE (hI.even ▸ hτ')
  have hinv' := tailInv_move K hI.inv hpE hpu hoff
  have hleaf' : ∀ t ∈ T, ∀ v, (delEdge K u p).Adj t.1 v → v = t.2.1 :=
    fun t ht v h => hI.leaf t ht v h.1
  have hr' : (delEdge K u p).degree r = K.degree r := by
    have h := hdeg r
    simp only [Ne.symm hur, Ne.symm hpr, ite_false, add_zero] at h
    exact h
  -- the non-neighbour set does not grow
  have hrv : ∀ v, K.Adj r v → (delEdge K u p).Adj r v := by
    intro v h
    refine ⟨h, ?_⟩
    rw [Sym2.eq_iff]
    rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · exact hur h1.symm
    · exact hpr h1.symm
  have hsub : nonNbr T (delEdge K u p) r ⊆ nonNbr T K r := by
    intro v hv
    rw [mem_nonNbr] at hv ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hv
    refine ⟨h1, fun h => h2 (hrv v h), ?_, h4⟩
    have h := hdeg v
    omega
  -- live tails are unchanged
  have hlive : liveSet T (delEdge K u p) = liveSet T K := by
    ext t
    rw [mem_liveSet, mem_liveSet]
    constructor
    · rintro ⟨ht, h⟩
      exact ⟨ht, h.1⟩
    · rintro ⟨ht, h⟩
      exact ⟨ht, live_move K hI.inv hpE hoff ht h⟩
  obtain ⟨hcA, hcB⟩ := card_tau_move hp hu hτ'
  have htok := hI.tok
  have hpot := hI.pot
  by_cases hq : ∃ q, (delEdge K u p).Adj u q
  · have hc := hcA hq
    have hle := Finset.card_le_card hsub
    exact ⟨hE', hinv', hleaf', by rw [hr']; exact hI.rodd, by omega, by rw [hlive]; omega⟩
  · have hc := hcB hq
    -- `u` retires: it lay in the non-neighbour set and has left it
    have huA : u ∈ nonNbr T K r := by
      rw [mem_nonNbr]
      refine ⟨hur, fun h => hq ⟨r, (hrv u h).symm⟩,
        (K.degree_pos_iff_exists_adj u).mpr ⟨p, hpu.symm⟩, fun t ht h => ?_⟩
      by_cases hl : K.Adj t.1 t.2.1
      · exact (hoff t ht hl).1 h
      · exact dead_leaf_isolated hI.leaf ht hl p (h ▸ hpu.symm)
    have huA' : u ∉ nonNbr T (delEdge K u p) r := by
      rw [mem_nonNbr]
      rintro ⟨-, -, h, -⟩
      exact hq (((delEdge K u p).degree_pos_iff_exists_adj u).mp h)
    have hsub' : nonNbr T (delEdge K u p) r ⊆ (nonNbr T K r).erase u := fun v hv =>
      Finset.mem_erase.mpr ⟨fun h => huA' (h ▸ hv), hsub hv⟩
    have hle := Finset.card_le_card hsub'
    rw [Finset.card_erase_of_mem huA] at hle
    have hApos : 0 < (nonNbr T K r).card := Finset.card_pos.mpr ⟨u, huA⟩
    exact ⟨hE', hinv', hleaf', by rw [hr']; exact hI.rodd, by omega, by rw [hlive]; omega⟩

/-- A drop keeps the invariant. -/
theorem obstr_drop {T : Finset (U × U × U)} (hT : TailSys T) {K : SimpleGraph U}
    [DecidableRel K.Adj] {r : U} (hrT : ∀ t ∈ T, r ≠ t.1 ∧ r ≠ t.2.1) {τ τ' : Finset U}
    (hI : ObstrInv T K r τ) {t : U × U × U} (ht : t ∈ T) (hl : K.Adj t.1 t.2.1) (hw : t.2.1 ∉ τ)
    (hτ' : ∀ v, v ∈ τ' ↔ v ∈ τ ∨ (v = t.2.1 ∧ ∃ q, (delEdge K t.1 t.2.1).Adj t.2.1 q)) :
    ObstrInv T (delEdge K t.1 t.2.1) r τ' := by
  obtain ⟨hc, -, -⟩ := hI.inv t ht hl
  have hwE : t.2.1 ∉ evenSet K := hI.even ▸ hw
  have hne : t.1 ≠ t.2.1 := hl.ne
  obtain ⟨hrc, hrs⟩ := hrT t ht
  have hdeg := delEdge_degree K hl
  have hE' : evenSet (delEdge K t.1 t.2.1) = τ' := evenSet_drop K hl hc hwE (hI.even ▸ hτ')
  have hinv' := tailInv_drop K hT hI.inv ht hl
  have hleaf' : ∀ t' ∈ T, ∀ v, (delEdge K t.1 t.2.1).Adj t'.1 v → v = t'.2.1 :=
    fun t' ht' v h => hI.leaf t' ht' v h.1
  have hr' : (delEdge K t.1 t.2.1).degree r = K.degree r := by
    have h := hdeg r
    simp only [hrc, hrs, ite_false, add_zero] at h
    exact h
  have hrv : ∀ v, K.Adj r v → (delEdge K t.1 t.2.1).Adj r v := by
    intro v h
    refine ⟨h, ?_⟩
    rw [Sym2.eq_iff]
    rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · exact hrc h1
    · exact hrs h1
  have hsub : nonNbr T (delEdge K t.1 t.2.1) r ⊆ nonNbr T K r := by
    intro v hv
    rw [mem_nonNbr] at hv ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hv
    refine ⟨h1, fun h => h2 (hrv v h), ?_, h4⟩
    have h := hdeg v
    omega
  -- the dropped tail dies, the others stay as they are
  have htl : t ∈ liveSet T K := mem_liveSet.mpr ⟨ht, hl⟩
  have hlive : liveSet T (delEdge K t.1 t.2.1) = (liveSet T K).erase t := by
    ext t'
    rw [Finset.mem_erase, mem_liveSet, mem_liveSet]
    constructor
    · rintro ⟨ht', h⟩
      refine ⟨fun h' => ?_, ht', h.1⟩
      subst h'
      exact h.2 rfl
    · rintro ⟨htt, ht', h⟩
      exact ⟨ht', live_drop hT K ht ht' htt h⟩
  have hlc : (liveSet T (delEdge K t.1 t.2.1)).card + 1 = (liveSet T K).card := by
    rw [hlive, Finset.card_erase_of_mem htl]
    have : 0 < (liveSet T K).card := Finset.card_pos.mpr ⟨t, htl⟩
    omega
  obtain ⟨hcA, hcB⟩ := card_tau_drop hw hτ'
  have htok := hI.tok
  have hpot := hI.pot
  by_cases hq : ∃ q, (delEdge K t.1 t.2.1).Adj t.2.1 q
  · have hcard := hcA hq
    have hle := Finset.card_le_card hsub
    exact ⟨hE', hinv', hleaf', by rw [hr']; exact hI.rodd, by omega, by omega⟩
  · have hcard := hcB hq
    -- the stem is isolated: it lay in the non-neighbour set and has left it
    have hsA : t.2.1 ∈ nonNbr T K r := by
      rw [mem_nonNbr]
      refine ⟨Ne.symm hrs, fun h => hq ⟨r, (hrv _ h).symm⟩,
        (K.degree_pos_iff_exists_adj _).mpr ⟨t.1, hl.symm⟩, fun t' ht' h => ?_⟩
      by_cases htt : t' = t
      · subst htt
        exact hne h.symm
      · exact (hT.cross t ht t' ht' (Ne.symm htt)).2.1 h.symm
    have hsA' : t.2.1 ∉ nonNbr T (delEdge K t.1 t.2.1) r := by
      rw [mem_nonNbr]
      rintro ⟨-, -, h, -⟩
      exact hq (((delEdge K t.1 t.2.1).degree_pos_iff_exists_adj _).mp h)
    have hsub' : nonNbr T (delEdge K t.1 t.2.1) r ⊆ (nonNbr T K r).erase t.2.1 := fun v hv =>
      Finset.mem_erase.mpr ⟨fun h => hsA' (h ▸ hv), hsub hv⟩
    have hle := Finset.card_le_card hsub'
    rw [Finset.card_erase_of_mem hsA] at hle
    have hApos : 0 < (nonNbr T K r).card := Finset.card_pos.mpr ⟨_, hsA⟩
    exact ⟨hE', hinv', hleaf', by rw [hr']; exact hI.rodd, by omega, by omega⟩

/-- A suppression keeps the invariant. -/
theorem obstr_supp {T : Finset (U × U × U)} {K : SimpleGraph U} [DecidableRel K.Adj] {r : U}
    {τ : Finset U} (hI : ObstrInv T K r τ) {p a b : U} (hp : p ∈ τ)
    (hNg : ∀ v, K.Adj p v ↔ v = a ∨ v = b) (hab : a ≠ b) (hnadj : ¬ K.Adj a b)
    (hok : SuppOK T K a b) :
    ObstrInv T (plusEdge (delEdge (delEdge K p a) p b) a b) r (τ.erase p) := by
  obtain ⟨hHw, hHg, hHab, hHadj, -⟩ := splitOff_facts hNg hab hnadj
  have hpE : p ∈ evenSet K := hI.even ▸ hp
  have hpr : p ≠ r := by
    rintro rfl
    have := (mem_evenSet_iff.mp hpE).2
    have := hI.rodd
    omega
  have hE' : evenSet (plusEdge (delEdge (delEdge K p a) p b) a b) = τ.erase p := by
    rw [evenSet_supp K hNg hab hnadj, hI.even]
  have hinv' := tailInv_supp K hI.inv hpE hNg hab hnadj hok
  have hleaf' : ∀ t ∈ T, ∀ v, (plusEdge (delEdge (delEdge K p a) p b) a b).Adj t.1 v →
      v = t.2.1 := by
    intro t ht v h
    obtain ⟨hac, hbc, -⟩ := hok t ht
    rcases hHadj _ _ h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h', -, -⟩
    · exact absurd h1.symm hac
    · exact absurd h1.symm hbc
    · exact hI.leaf t ht v h'
  have hr' := hHw r (Ne.symm hpr)
  have hlive : liveSet T (plusEdge (delEdge (delEdge K p a) p b) a b) = liveSet T K := by
    ext t
    rw [mem_liveSet, mem_liveSet]
    constructor
    · rintro ⟨ht, h⟩
      obtain ⟨hac, hbc, -⟩ := hok t ht
      refine ⟨ht, ?_⟩
      rcases hHadj _ _ h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h', -, -⟩
      · exact absurd h1.symm hac
      · exact absurd h1.symm hbc
      · exact h'
    · rintro ⟨ht, h⟩
      exact ⟨ht, live_supp K hI.inv hpE hok ht h⟩
  -- the edges of `r` other than `rp` survive
  have hrv : ∀ v, v ≠ p → K.Adj r v → (plusEdge (delEdge (delEdge K p a) p b) a b).Adj r v := by
    intro v hvp h
    refine Or.inl ⟨⟨h, ?_⟩, ?_⟩
    · rw [Sym2.eq_iff]
      rintro (⟨h1, -⟩ | ⟨-, h1⟩)
      · exact hpr h1.symm
      · exact hvp h1
    · rw [Sym2.eq_iff]
      rintro (⟨h1, -⟩ | ⟨-, h1⟩)
      · exact hpr h1.symm
      · exact hvp h1
  have hsub : ∀ c, c ∈ nonNbr T K r →
      (plusEdge (delEdge (delEdge K p a) p b) a b).Adj r c ∨ c = p →
      nonNbr T (plusEdge (delEdge (delEdge K p a) p b) a b) r ⊆ (nonNbr T K r).erase c := by
    intro c _ hcgone v hv
    rw [mem_nonNbr] at hv
    obtain ⟨h1, h2, h3, h4⟩ := hv
    have hvp : v ≠ p := by
      rintro rfl
      rw [hHg] at h3
      omega
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · rintro rfl
      rcases hcgone with h | h
      · exact h2 h
      · exact hvp h
    · rw [mem_nonNbr]
      refine ⟨h1, fun h => h2 (hrv v hvp h), ?_, h4⟩
      rw [hHw v hvp] at h3
      exact h3
  -- the vertex used up by the suppression
  obtain ⟨c, hcA, hcgone⟩ : ∃ c, c ∈ nonNbr T K r ∧
      ((plusEdge (delEdge (delEdge K p a) p b) a b).Adj r c ∨ c = p) := by
    by_cases hra : r = a ∨ r = b
    · -- `p ∼ r`: the other neighbour of `p` becomes adjacent to `r`
      obtain ⟨c, hrc, hcab, hcr, hadj⟩ : ∃ c, ¬ K.Adj r c ∧ (c = a ∨ c = b) ∧ c ≠ r ∧
          (plusEdge (delEdge (delEdge K p a) p b) a b).Adj r c := by
        rcases hra with rfl | rfl
        · exact ⟨b, hnadj, Or.inr rfl, Ne.symm hab, hHab⟩
        · exact ⟨a, fun h => hnadj h.symm, Or.inl rfl, hab, hHab.symm⟩
      refine ⟨c, ?_, Or.inl hadj⟩
      rw [mem_nonNbr]
      refine ⟨hcr, hrc, (K.degree_pos_iff_exists_adj c).mpr ⟨p, ((hNg c).mpr hcab).symm⟩,
        fun t ht h => ?_⟩
      obtain ⟨hac, hbc, -⟩ := hok t ht
      rcases hcab with rfl | rfl
      · exact hac h
      · exact hbc h
    · -- `p ≁ r`: `p` itself is used up
      refine ⟨p, ?_, Or.inr rfl⟩
      rw [mem_nonNbr]
      exact ⟨hpr, fun h => hra ((hNg r).mp h.symm), (mem_evenSet_iff.mp hpE).1,
        fun t ht h => leaf_not_even hI.leaf ht (h ▸ hpE)⟩
  have hle := Finset.card_le_card (hsub c hcA hcgone)
  rw [Finset.card_erase_of_mem hcA] at hle
  have hApos : 0 < (nonNbr T K r).card := Finset.card_pos.mpr ⟨c, hcA⟩
  have hτc := Finset.card_erase_of_mem hp
  have hτpos : 0 < τ.card := Finset.card_pos.mpr ⟨p, hp⟩
  have htok := hI.tok
  have hpot := hI.pot
  exact ⟨hE', hinv', hleaf', by rw [hr']; exact hI.rodd, by omega, by rw [hlive]; omega⟩

/-- **The obstruction** (manuscript Proposition 6.1, abstract form). If the invariant holds, there
is no schedule. -/
theorem not_steerK {T : Finset (U × U × U)} (hT : TailSys T) {r : U}
    (hrT : ∀ t ∈ T, r ≠ t.1 ∧ r ≠ t.2.1) :
    ∀ {K : SimpleGraph U} {τ : Finset U}, SteerK T K τ → ∀ [DecidableRel K.Adj],
      ObstrInv T K r τ → False := by
  intro K τ hS
  induction hS with
  | @fin K τ hτ h1 =>
    intro _ hI
    have hl : (liveSet T K).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro t ht t' ht'
      rw [mem_liveSet] at ht ht'
      exact h1 t ht.1 t' ht'.1 ht.2 ht'.2
    have := hI.pot
    omega
  | @move K τ τ' p u hp hpu hu hoff hno hτ' _ ih =>
    intro _ hI
    by_cases hur : u = r
    · subst hur
      exact obstr_no_entry hI hp hno
    · exact ih (obstr_move hI hp hpu hu hoff hur hτ')
  | @drop K τ τ' t ht hl hw hτ' _ ih =>
    intro _ hI
    exact ih (obstr_drop hT hrT hI ht hl hw hτ')
  | @supp K τ p a b hp hNg hab hnadj hok _ ih =>
    intro _ hI
    exact ih (obstr_supp hI hp hNg hab hnadj hok)

end obstruct

/-! ### Roots with few non-neighbours -/

section triangle

variable {V : Type u} [Fintype V] [DecidableEq V] {J : SimpleGraph V} [DecidableRel J.Adj]
  {z r w : V} {L : List (V × V)}

omit [Fintype V] [DecidableEq V] in
theorem nodup_of_pairVerts (hnd : (pairVerts L).Nodup) : L.Nodup := by
  rw [pairVerts, List.nodup_flatMap] at hnd
  refine hnd.2.imp (fun {p q} h hpq => ?_)
  subst hpq
  exact h (List.mem_cons_self) (List.mem_cons_self)

omit [Fintype V] in
theorem leafSet_card (hnd : (pairVerts L).Nodup) : (leafSet L).card = L.length := by
  unfold leafSet
  rw [List.toFinset_card_of_nodup, List.length_map]
  refine List.Nodup.map_on (fun p hp q hq h => ?_) (nodup_of_pairVerts hnd)
  exact pair_eq_of_share hnd hp hq (Or.inr rfl) (Or.inr h)

/-- **No schedule at a root with fewer than `k` non-neighbours** (manuscript Proposition 6.1).
For triangle data with `k = |L|` pairs, if `r` has fewer than `k` non-neighbours in `J − r` (and
`d(w) ≥ 2`), then for every orientation the leaf graph `M⁺` has no `k`-token schedule. At
`d(z) = 6` (`k = 2`) this is every root of degree `|J| − 2`. -/
theorem not_steerK_triangle (hz : ∀ v, Even (J.degree v) ↔ v = z) (hD : TriangleData J z r w L)
    (hw2 : 2 ≤ J.degree w)
    (ht : (Finset.univ.filter (fun x => x ≠ r ∧ ¬ J.Adj r x)).card < L.length) :
    ¬ SteerK (triTails L) (triLeaf J z w L) (evenSet (triLeaf J z w L)) := by
  intro hS
  obtain ⟨hzr, -, -, hrw, hrL, hwL, hnd⟩ := hD.facts
  have hpar := hD.triM_parity hz
  have hrY : r ∉ leafSet L := fun h => by
    obtain ⟨p, hp, rfl⟩ := mem_leafSet.mp h
    exact hrL (snd_mem_pairVerts hp)
  have hwY : w ∉ leafSet L := fun h => by
    obtain ⟨p, hp, rfl⟩ := mem_leafSet.mp h
    exact hwL (snd_mem_pairVerts hp)
  -- the adjacency of `r` is that of `J`
  have hradj : ∀ x, (triM J z w L).Adj r x ↔ J.Adj r x := fun x =>
    ⟨fun h => h.1, fun h => ⟨h, not_mem_triDel_other (Ne.symm hzr) hrw hrL x⟩⟩
  -- the tokens of `M⁺` include `w` and every `yᵢ`
  have htok : insert (Sum.inl w) ((leafSet L).image Sum.inl) ⊆ evenSet (triLeaf J z w L) := by
    intro v hv
    rw [mem_evenSet_iff]
    rcases Finset.mem_insert.mp hv with rfl | hv
    · rw [leaves_degree_inl, ite_eq_right hwY, add_zero]
      have h1 := hD.triM_degree_w
      have h2 := hpar w
      rw [ite_eq_left rfl] at h2
      omega
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨p, hp, rfl⟩ := mem_leafSet.mp hy
      have hw2' : p.2 ≠ w := fun h => hwL (h ▸ snd_mem_pairVerts hp)
      rw [leaves_degree_inl, ite_eq_left hy]
      have h2 := hpar p.2
      rw [ite_eq_right hw2'] at h2
      omega
  have htokc : L.length + 1 ≤ (evenSet (triLeaf J z w L)).card := by
    have h := Finset.card_le_card htok
    rw [Finset.card_insert_of_notMem (by
      intro h'
      obtain ⟨y, hy, hyw⟩ := Finset.mem_image.mp h'
      exact hwY (Sum.inl_injective hyw ▸ hy)),
      Finset.card_image_of_injective _ Sum.inl_injective, leafSet_card hnd] at h
    exact h
  -- the non-neighbour set is the copy of the non-neighbours of `r` in `J`
  have hA : nonNbr (triTails L) (triLeaf J z w L) (Sum.inl r) ⊆
      (Finset.univ.filter (fun x => x ≠ r ∧ ¬ J.Adj r x)).image Sum.inl := by
    intro v hv
    rw [mem_nonNbr] at hv
    obtain ⟨h1, h2, h3, h4⟩ := hv
    cases v with
    | inl x =>
      refine Finset.mem_image.mpr ⟨x, ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun h => h1 (h ▸ rfl), fun h => h2 ?_⟩
      show (triM J z w L).Adj r x
      exact (hradj x).mpr h
    | inr x =>
      exfalso
      by_cases hx : x ∈ leafSet L
      · obtain ⟨p, hp, rfl⟩ := mem_leafSet.mp hx
        exact h4 _ (mem_triTails.mpr ⟨p, hp, rfl⟩) rfl
      · have : (triLeaf J z w L).degree (Sum.inr x) = 0 := by
          rw [leaves_degree_inr, ite_eq_right hx]
        omega
  have hAc := (Finset.card_le_card hA).trans Finset.card_image_le
  -- all tails are live
  have hL : 0 < L.length := by omega
  obtain ⟨p, hp⟩ : ∃ p, p ∈ L := List.exists_mem_of_length_pos hL
  have hlive : 1 ≤ (liveSet (triTails L) (triLeaf J z w L)).card := by
    refine Finset.card_pos.mpr ⟨_, mem_liveSet.mpr ⟨mem_triTails.mpr ⟨p, hp, rfl⟩, ?_⟩⟩
    exact ⟨rfl, mem_leafSet.mpr ⟨p, hp, rfl⟩⟩
  refine not_steerK (triTails_sys hnd) (r := Sum.inl r) (fun t htT => ?_) hS
    ⟨rfl, triTails_inv hz hD, fun t htT v hv => ?_, ?_, by omega, by omega⟩
  · obtain ⟨q, hq, rfl⟩ := mem_triTails.mp htT
    refine ⟨Sum.inl_ne_inr, fun h => hrL ?_⟩
    rw [Sum.inl.injEq] at h
    exact h ▸ snd_mem_pairVerts hq
  · obtain ⟨q, hq, rfl⟩ := mem_triTails.mp htT
    cases v with
    | inl b =>
      obtain ⟨h, -⟩ := leaves_adj_inr_inl.mp hv
      rw [h]
    | inr b => exact absurd hv leaves_not_adj_inr_inr
  · rw [leaves_degree_inl, ite_eq_right hrY, add_zero, hpar r, ite_eq_right hrw]

end triangle

end Gallai
