import GallaiLean.Realisable
import GallaiLean.Fan

/-!
# Two-step faithful descent, and the endpoint matroid for four even vertices

Endpoint-structure manuscript, section "Four even vertices".

## Edge deletion

`delE G F` is `G` with the edges of the finset `F` removed (`G.deleteEdges ↑F`), with a
decidable adjacency relation. `degree_delE`: deleting edges of `G` lowers the degree of `v` by
the number of deleted edges at `v`.
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

section delete

/-- `G` with the edges of `F` removed. -/
def delE (G : SimpleGraph V) (F : Finset (Sym2 V)) : SimpleGraph V := G.deleteEdges (↑F)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem delE_adj {G : SimpleGraph V} {F : Finset (Sym2 V)} {a b : V} :
    (delE G F).Adj a b ↔ G.Adj a b ∧ s(a, b) ∉ F := by
  simp [delE]

instance delE.decRel (G : SimpleGraph V) [DecidableRel G.Adj] (F : Finset (Sym2 V)) :
    DecidableRel (delE G F).Adj := fun a b =>
  decidable_of_iff (G.Adj a b ∧ s(a, b) ∉ F) delE_adj.symm

omit [Fintype V] [DecidableEq V] in
theorem delE_edgeSet {G : SimpleGraph V} {F : Finset (Sym2 V)} (e : Sym2 V) :
    e ∈ (delE G F).edgeSet ↔ e ∈ G.edgeSet ∧ e ∉ F := by
  simp [delE, edgeSet_deleteEdges]

omit [Fintype V] [DecidableEq V] in
theorem delE_le {G : SimpleGraph V} {F : Finset (Sym2 V)} {a b : V} (h : (delE G F).Adj a b) :
    G.Adj a b := (delE_adj.mp h).1

/-- Deleting edges of `G` lowers the degree of `v` by the number of deleted edges at `v`. -/
theorem degree_delE (G : SimpleGraph V) [DecidableRel G.Adj] (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, e ∈ G.edgeSet) (v : V) :
    (delE G F).degree v + (F.filter (fun e => v ∈ e)).card = G.degree v := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  have h1 : (delE G F).neighborFinset v =
      (G.neighborFinset v).filter (fun w => s(v, w) ∉ F) := by
    ext w; simp
  have h2 : ((G.neighborFinset v).filter (fun w => ¬ (s(v, w) ∉ F))).card =
      (F.filter (fun e => v ∈ e)).card := by
    apply Finset.card_bij (fun w _ => s(v, w))
    · intro w hw
      simp only [Finset.mem_filter, not_not] at hw ⊢
      exact ⟨hw.2, Sym2.mem_mk_left v w⟩
    · intro a _ b _ hab
      exact Sym2.congr_right.mp hab
    · intro e he
      simp only [Finset.mem_filter] at he
      obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp he.2 |>.imp fun w h => h
      refine ⟨w, ?_, rfl⟩
      simp only [Finset.mem_filter, mem_neighborFinset, not_not]
      exact ⟨hF _ he.1, he.1⟩
  rw [h1, ← h2, Finset.card_filter_add_card_filter_not]

/-- Degrees after deleting one edge. -/
theorem degree_delE_single (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V} (h : G.Adj a b)
    (v : V) :
    (delE G {s(a, b)}).degree v + (if v = a ∨ v = b then 1 else 0) = G.degree v := by
  have := degree_delE G {s(a, b)} (by simpa using h) v
  rw [Finset.filter_singleton] at this
  by_cases hv : v = a ∨ v = b
  · simp only [Sym2.mem_iff, hv, ite_true, Finset.card_singleton] at this ⊢
    exact this
  · simp only [Sym2.mem_iff, hv, ite_false, Finset.card_empty] at this ⊢
    exact this

end delete

section steps

variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem mem_evenSet_iff {v : V} : v ∈ evenSet G ↔ 0 < G.degree v ∧ Even (G.degree v) := by
  simp [evenSet]

omit [DecidableEq V] in
theorem odd_of_not_mem_evenSet (hG : ∀ v, 0 < G.degree v) {v : V} (hv : v ∉ evenSet G) :
    Odd (G.degree v) := by
  rw [mem_evenSet_iff, not_and] at hv
  exact Nat.not_even_iff_odd.mp (hv (hG v))

theorem profile_congr {K : SimpleGraph V} [DecidableRel K.Adj] {S T : Finset V} {v : V}
    (hd : K.degree v = G.degree v) (hm : v ∈ S ↔ v ∈ T) : profile K S v = profile G T v := by
  unfold profile
  rw [hd]
  simp only [hm]

theorem profile_odd {S : Finset V} {v : V} (h : Odd (G.degree v)) : profile G S v = 1 := by
  simp [profile, h]

theorem profile_even_mem {S : Finset V} {v : V} (h : Even (G.degree v)) (hv : v ∈ S) :
    profile G S v = 2 := by
  simp [profile, Nat.not_odd_iff_even.mpr h, hv]

theorem profile_even_not_mem {S : Finset V} {v : V} (h : Even (G.degree v)) (hv : v ∉ S) :
    profile G S v = 0 := by
  simp [profile, Nat.not_odd_iff_even.mpr h, hv]

/-- A vertex with no ends in a realisation, of positive degree, is an even vertex outside the
realised set. -/
theorem mem_of_ends_eq_zero {S : Finset V} {D : PathDecomp G} (hD : Realises G D S) {v : V}
    (hpos : 0 < G.degree v) (h0 : D.ends v = 0) : v ∈ evenSet G ∧ v ∉ S := by
  rw [hD v] at h0
  unfold profile at h0
  split_ifs at h0 with ho hS
  refine ⟨mem_evenSet_iff.mpr ⟨hpos, Nat.not_odd_iff_even.mp ho⟩, hS⟩

/-- Deleting one edge `ab` between two vertices of positive degree: the parities at `a`, `b`
flip, the others are unchanged. -/
theorem delE_single_facts {a b : V} (hab : G.Adj a b) :
    (delE G {s(a, b)}).degree a + 1 = G.degree a ∧ (delE G {s(a, b)}).degree b + 1 = G.degree b ∧
      ∀ v, v ≠ a → v ≠ b → (delE G {s(a, b)}).degree v = G.degree v := by
  have hdeg := degree_delE_single G hab
  refine ⟨by simpa using hdeg a, by simpa using hdeg b, fun v h1 h2 => by simpa [h1, h2] using hdeg v⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem fan_edgeSet {a b : V} (e : Sym2 V) :
    e ∈ (delE G {s(a, b)}).edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(a, b) := by
  rw [delE_edgeSet]; simp

/-- **Transfer across an even edge.** Let `s, t, u'` be distinct even vertices with `st` an edge
and `su'` a non-edge. Then `Ev ∖ {t, u'}` is realisable. (Lemma 3 on `G − st`, then Fan's single
transfer of `st` towards `s`.) -/
theorem realisable_of_edge (hL : LovaszStatement.{u}) (hG : ∀ v, 0 < G.degree v)
    (hn : Even (Fintype.card V)) {s t u' : V} (hs : s ∈ evenSet G) (ht : t ∈ evenSet G)
    (hu' : u' ∈ evenSet G) (hst : G.Adj s t) (hsu : ¬ G.Adj s u') (hsu' : s ≠ u')
    (htu' : t ≠ u') :
    Realisable G (((evenSet G).erase t).erase u') := by
  have hne : s ≠ t := hst.ne
  obtain ⟨hKs, hKt, hKo⟩ := delE_single_facts hst
  obtain ⟨hs0, ks, hks⟩ := mem_evenSet_iff.mp hs
  obtain ⟨ht0, kt, hkt⟩ := mem_evenSet_iff.mp ht
  have hsodd : Odd ((delE G {s(s, t)}).degree s) := ⟨ks - 1, by omega⟩
  have htodd : Odd ((delE G {s(s, t)}).degree t) := ⟨kt - 1, by omega⟩
  have hKpos : ∀ v, 0 < (delE G {s(s, t)}).degree v := by
    intro v
    by_cases h1 : v = s
    · subst h1; omega
    by_cases h2 : v = t
    · subst h2; omega
    rw [hKo v h1 h2]; exact hG v
  have hEvK : evenSet (delE G {s(s, t)}) = ((evenSet G).erase s).erase t := by
    ext v
    simp only [Finset.mem_erase, mem_evenSet_iff]
    by_cases h1 : v = s
    · subst h1
      simp only [ne_eq, not_true_eq_false, false_and, and_false, iff_false, not_and]
      exact fun _ he => (Nat.not_even_iff_odd.mpr hsodd) he
    by_cases h2 : v = t
    · subst h2
      simp only [ne_eq, not_true_eq_false, false_and, iff_false, not_and]
      exact fun _ he => (Nat.not_even_iff_odd.mpr htodd) he
    rw [hKo v h1 h2]
    simp [h1, h2]
  have hu'K : u' ∈ evenSet (delE G {s(s, t)}) := by
    rw [hEvK]; exact Finset.mem_erase.mpr ⟨htu'.symm, Finset.mem_erase.mpr ⟨hsu'.symm, hu'⟩⟩
  obtain ⟨-, D', hD'⟩ := realisable_evenSet_erase hL hKpos hn hu'K
  have hcond : (Finset.univ.filter
      (fun w => (delE G {s(s, t)}).Adj s w ∧ D'.ends w = 0)).card < D'.ends t := by
    rw [hD' t, profile_odd htodd, Finset.card_eq_zero.mpr]
    · exact Nat.one_pos
    rw [Finset.filter_eq_empty_iff]
    rintro w - ⟨hadj, h0⟩
    obtain ⟨hwE, hwS⟩ := mem_of_ends_eq_zero hD' (hKpos w) h0
    rw [hEvK] at hwE
    have : w = u' := by
      by_contra hwu
      exact hwS (Finset.mem_erase.mpr ⟨hwu, by rw [hEvK]; exact hwE⟩)
    subst this
    exact hsu (delE_le hadj)
  obtain ⟨D, -, hDs, hDt, hDo⟩ := fan_single hst fan_edgeSet D' hcond
  refine ⟨(Finset.erase_subset _ _).trans (Finset.erase_subset _ _), D, fun v => ?_⟩
  by_cases h1 : v = s
  · subst h1
    rw [hDs, hD' v, profile_odd hsodd, profile_even_mem (mem_evenSet_iff.mp hs).2 ?_]
    simp [hne, hsu', hs]
  by_cases h2 : v = t
  · subst h2
    rw [hD' v, profile_odd htodd] at hDt
    rw [profile_even_not_mem (mem_evenSet_iff.mp ht).2 (by simp)]
    omega
  rw [hDo v h1 h2, hD' v]
  apply profile_congr (hKo v h1 h2)
  rw [hEvK]
  simp [h1, h2]

/-- The last transfer of the star lemma: from `D₂` on `G − y t''` with three ends at `y`, no
ends at `w, t'` and the profile of `S = Ev ∖ {w, t'}` elsewhere, transfer `y t''` towards `t''`. -/
theorem star_finish {y w t' t'' : V} (hG : ∀ v, 0 < G.degree v) (hy : y ∈ evenSet G)
    (hw : w ∈ evenSet G) (ht' : t' ∈ evenSet G) (ht'' : t'' ∈ evenSet G) (hyw : y ≠ w)
    (hyt' : y ≠ t') (hyt'' : y ≠ t'') (hwt'' : w ≠ t'') (ht't'' : t' ≠ t'')
    (hadj : G.Adj y t'') (D₂ : PathDecomp (delE G {s(y, t'')}))
    (h₂y : D₂.ends y = 3) (h₂w : D₂.ends w = 0) (h₂t' : D₂.ends t' = 0) (h₂t'' : D₂.ends t'' = 1)
    (h₂o : ∀ v, v ≠ y → v ≠ w → v ≠ t' → v ≠ t'' →
      D₂.ends v = profile G (((evenSet G).erase w).erase t') v) :
    Realisable G (((evenSet G).erase w).erase t') := by
  have hG' : ∀ e, e ∈ (delE G {s(y, t'')}).edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(t'', y) := by
    intro e; rw [fan_edgeSet, Sym2.eq_swap]
  have hcond : (Finset.univ.filter
      (fun v => (delE G {s(y, t'')}).Adj t'' v ∧ D₂.ends v = 0)).card < D₂.ends y := by
    rw [h₂y]
    calc _ ≤ ({w, t'} : Finset V).card := by
          apply Finset.card_le_card
          intro v hv
          rw [Finset.mem_filter] at hv
          have h0 := hv.2.2
          by_cases h1 : v = y
          · subst h1; omega
          by_cases h2 : v = w
          · simp [h2]
          by_cases h3 : v = t'
          · simp [h3]
          by_cases h4 : v = t''
          · subst h4; omega
          rw [h₂o v h1 h2 h3 h4] at h0
          unfold profile at h0
          split_ifs at h0 with ho hS
          exact absurd (Finset.mem_erase.mpr ⟨h3, Finset.mem_erase.mpr ⟨h2,
            mem_evenSet_iff.mpr ⟨hG v, Nat.not_odd_iff_even.mp ho⟩⟩⟩) hS
      _ ≤ 2 := Finset.card_le_two
      _ < 3 := by norm_num
  obtain ⟨D, -, hDt'', hDy, hDo⟩ := fan_single hadj.symm hG' D₂ hcond
  have hyS : y ∈ ((evenSet G).erase w).erase t' := by simp [hyw, hyt', hy]
  have ht''S : t'' ∈ ((evenSet G).erase w).erase t' := by simp [hwt''.symm, ht't''.symm, ht'']
  refine ⟨(Finset.erase_subset _ _).trans (Finset.erase_subset _ _), D, fun v => ?_⟩
  by_cases h1 : v = y
  · subst h1
    rw [profile_even_mem (mem_evenSet_iff.mp hy).2 hyS]
    omega
  by_cases h4 : v = t''
  · subst h4
    rw [profile_even_mem (mem_evenSet_iff.mp ht'').2 ht''S]
    omega
  rw [hDo v h4 h1]
  by_cases h2 : v = w
  · subst h2
    rw [h₂w, profile_even_not_mem (mem_evenSet_iff.mp hw).2 (by simp)]
  by_cases h3 : v = t'
  · subst h3
    rw [h₂t', profile_even_not_mem (mem_evenSet_iff.mp ht').2 (by simp)]
  exact h₂o v h1 h2 h3 h4

/-- **Star lemma.** If an even vertex `y` is adjacent to three further even vertices `w, x, z`,
then `Ev ∖ {w, x}` or `Ev ∖ {w, z}` is realisable. Lemma 2 on `K = G − yw − yx − yz`, then a
single transfer of `yw` towards `y`, a grouped transfer of `{yx, yz}` towards `y`, and a single
transfer of the last edge away from `y`. -/
theorem realisable_of_star (hL : LovaszStatement.{u}) (hG : ∀ v, 0 < G.degree v) {y w x z : V}
    (hy : y ∈ evenSet G) (hw : w ∈ evenSet G) (hx : x ∈ evenSet G) (hz : z ∈ evenSet G)
    (hyw : y ≠ w) (hyx : y ≠ x) (hyz : y ≠ z) (hwx : w ≠ x) (hwz : w ≠ z) (hxz : x ≠ z)
    (ayw : G.Adj y w) (ayx : G.Adj y x) (ayz : G.Adj y z) :
    Realisable G (((evenSet G).erase w).erase x) ∨
      Realisable G (((evenSet G).erase w).erase z) := by
  -- the three intermediate graphs
  have e1 : s(y, x) ≠ s(y, z) := fun h => hxz (Sym2.congr_right.mp h)
  have e2 : s(y, w) ≠ s(y, z) := fun h => hwz (Sym2.congr_right.mp h)
  have e3 : s(y, w) ≠ s(y, x) := fun h => hwx (Sym2.congr_right.mp h)
  have a0 : (delE G {s(y, z)}).Adj y x := delE_adj.mpr ⟨ayx, by simpa using e1⟩
  have a0w : (delE G {s(y, z)}).Adj y w := delE_adj.mpr ⟨ayw, by simpa using e2⟩
  have a1 : (delE (delE G {s(y, z)}) {s(y, x)}).Adj y w := delE_adj.mpr ⟨a0w, by simpa using e3⟩
  obtain ⟨d0y, d0z, d0o⟩ := delE_single_facts ayz
  obtain ⟨d1y, d1x, d1o⟩ := delE_single_facts a0
  obtain ⟨d2y, d2w, d2o⟩ := delE_single_facts a1
  have hKy : (delE (delE (delE G {s(y, z)}) {s(y, x)}) {s(y, w)}).degree y + 3 = G.degree y := by omega
  have hKw : (delE (delE (delE G {s(y, z)}) {s(y, x)}) {s(y, w)}).degree w + 1 = G.degree w := by
    have := d1o w hyw.symm hwx; have := d0o w hyw.symm hwz; omega
  have hKx : (delE (delE (delE G {s(y, z)}) {s(y, x)}) {s(y, w)}).degree x + 1 = G.degree x := by
    have := d2o x hyx.symm hwx.symm; have := d0o x hyx.symm hxz; omega
  have hKz : (delE (delE (delE G {s(y, z)}) {s(y, x)}) {s(y, w)}).degree z + 1 = G.degree z := by
    have := d2o z hyz.symm hwz.symm; have := d1o z hyz.symm hxz.symm; omega
  have hKo : ∀ v, v ≠ y → v ≠ w → v ≠ x → v ≠ z → (delE (delE (delE G {s(y, z)}) {s(y, x)}) {s(y, w)}).degree v = G.degree v := by
    intro v h1 h2 h3 h4
    rw [d2o v h1 h2, d1o v h1 h3, d0o v h1 h4]
  have oddK : ∀ v ∈ evenSet G, ∀ c, (delE (delE (delE G {s(y, z)}) {s(y, x)}) {s(y, w)}).degree v + c = G.degree v → Odd c → Odd ((delE (delE (delE G {s(y, z)}) {s(y, x)}) {s(y, w)}).degree v) := by
    intro v hv c hc hco
    obtain ⟨-, k, hk⟩ := mem_evenSet_iff.mp hv
    obtain ⟨j, hj⟩ := hco
    exact ⟨k - j - 1, by omega⟩
  have oy := oddK y hy 3 hKy (by decide)
  have ow := oddK w hw 1 hKw odd_one
  have ox := oddK x hx 1 hKx odd_one
  have oz := oddK z hz 1 hKz odd_one
  have hKpos : ∀ v, 0 < (delE (delE (delE G {s(y, z)}) {s(y, x)}) {s(y, w)}).degree v := by
    intro v
    by_cases h1 : v = y; · subst h1; exact oy.pos
    by_cases h2 : v = w; · subst h2; exact ow.pos
    by_cases h3 : v = x; · subst h3; exact ox.pos
    by_cases h4 : v = z; · subst h4; exact oz.pos
    rw [hKo v h1 h2 h3 h4]; exact hG v
  obtain ⟨-, D₀, hD₀⟩ := realisable_evenSet hL hKpos
  have h0y : D₀.ends y = 1 := (hD₀ y).trans (profile_odd oy)
  have h0w : D₀.ends w = 1 := (hD₀ w).trans (profile_odd ow)
  have h0x : D₀.ends x = 1 := (hD₀ x).trans (profile_odd ox)
  have h0z : D₀.ends z = 1 := (hD₀ z).trans (profile_odd oz)
  have h0ne : ∀ v, D₀.ends v ≠ 0 := by
    intro v h0
    obtain ⟨h1, h2⟩ := mem_of_ends_eq_zero hD₀ (hKpos v) h0
    exact h2 h1
  -- step 1: transfer `yw` towards `y`
  have hc1 : (Finset.univ.filter (fun v => (delE (delE (delE G {s(y, z)}) {s(y, x)}) {s(y, w)}).Adj y v ∧ D₀.ends v = 0)).card < D₀.ends w := by
    rw [h0w, Finset.card_eq_zero.mpr]
    · exact Nat.one_pos
    rw [Finset.filter_eq_empty_iff]
    exact fun v _ h => h0ne v h.2
  obtain ⟨D₁, hs₁, h1y, h1w, h1o⟩ := fan_single a1 fan_edgeSet D₀ hc1
  -- step 2: grouped transfer of `{yx, yz}` towards `y`
  have hT : ∀ t ∈ ({x, z} : Finset V), ¬ (delE (delE G {s(y, z)}) {s(y, x)}).Adj t y := by
    intro t ht hadj
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact (delE_adj.mp hadj).2 (by simp [Sym2.eq_swap])
    · rw [Finset.mem_singleton] at ht
      subst ht
      exact (delE_adj.mp (delE_le hadj)).2 (by simp [Sym2.eq_swap])
  have hsum : (Finset.univ.filter (fun v => (delE (delE G {s(y, z)}) {s(y, x)}).Adj y v ∧ D₁.ends v = 0)).card <
      ∑ t ∈ ({x, z} : Finset V), D₁.ends t := by
    rw [Finset.sum_pair hxz, h1o x hyx.symm hwx.symm, h1o z hyz.symm hwz.symm, h0x, h0z]
    calc _ ≤ ({w} : Finset V).card := by
          apply Finset.card_le_card
          intro v hv
          rw [Finset.mem_filter] at hv
          by_cases h1 : v = y
          · subst h1; omega
          by_cases h2 : v = w
          · simp [h2]
          exact absurd hv.2.2 (by rw [h1o v h1 h2]; exact h0ne v)
      _ < 2 := by simp
  obtain ⟨t', ht', hK'⟩ := fan_grouped D₁ y {x, z} (by simp [hyx, hyz]) hT hsum
  have hothers : ∀ v, v ≠ y → v ≠ w → v ≠ x → v ≠ z → ∀ S : Finset V,
      (v ∈ S ↔ v ∈ evenSet G) → D₁.ends v = profile G S v := by
    intro v h1 h2 h3 h4 S hS
    rw [h1o v h1 h2, hD₀ v]
    apply profile_congr (hKo v h1 h2 h3 h4)
    rw [hS]
    simp only [evenSet, Finset.mem_filter, Finset.mem_univ, true_and, hKo v h1 h2 h3 h4]
  rcases Finset.mem_insert.mp ht' with h | h
  · -- `t' = x`: the last edge is `yz`, and `G − yz` is `G₁ + xy`
    subst t'
    left
    obtain ⟨D₂, -, hD₂⟩ := hK' (delE G {s(y, z)}) (by
      intro e
      rw [delE_edgeSet (G := delE G {s(y, z)}) (F := {s(y, x)})]
      constructor
      · intro he
        by_cases hex : e = s(y, x)
        · exact Or.inr (hex.trans Sym2.eq_swap)
        · exact Or.inl ⟨he, by simpa using hex⟩
      · rintro (⟨he, -⟩ | rfl)
        · exact he
        · exact a0.symm)
    refine star_finish hG hy hw hx hz hyw hyx hyz hwz hxz ayz D₂ ?_ ?_ ?_ ?_ ?_
    · have := hD₂ y; rw [ite_eq_right hyx.symm, ite_eq_left rfl] at this; omega
    · have := hD₂ w; rw [ite_eq_right hwx.symm, ite_eq_right hyw] at this; omega
    · have := hD₂ x; rw [ite_eq_left rfl, ite_eq_right hyx, h1o x hyx.symm hwx.symm] at this; omega
    · have := hD₂ z
      rw [ite_eq_right hxz, ite_eq_right hyz, h1o z hyz.symm hwz.symm] at this; omega
    · intro v h1 h2 h3 h4
      have := hD₂ v
      rw [ite_eq_right (Ne.symm h3), ite_eq_right (Ne.symm h1), add_zero, add_zero] at this
      rw [this]
      exact hothers v h1 h2 h3 h4 _ (by simp [h2, h3])
  · -- `t' = z`: the last edge is `yx`, and `G − yx` is `G₁ + zy`
    rw [Finset.mem_singleton] at h
    subst t'
    right
    obtain ⟨D₂, -, hD₂⟩ := hK' (delE G {s(y, x)}) (by
      intro e
      rw [delE_edgeSet (G := G) (F := {s(y, x)}),
        delE_edgeSet (G := delE G {s(y, z)}) (F := {s(y, x)}),
        delE_edgeSet (G := G) (F := {s(y, z)})]
      simp only [Finset.mem_singleton]
      constructor
      · rintro ⟨he, hex⟩
        by_cases hez : e = s(y, z)
        · exact Or.inr (hez.trans Sym2.eq_swap)
        · exact Or.inl ⟨⟨he, hez⟩, hex⟩
      · rintro (⟨⟨he, -⟩, hex⟩ | rfl)
        · exact ⟨he, hex⟩
        · refine ⟨ayz.symm, ?_⟩
          rw [Sym2.eq_swap]; exact e1.symm)
    refine star_finish hG hy hw hz hx hyw hyz hyx hwx hxz.symm ayx D₂ ?_ ?_ ?_ ?_ ?_
    · have := hD₂ y; rw [ite_eq_right hyz.symm, ite_eq_left rfl] at this; omega
    · have := hD₂ w; rw [ite_eq_right hwz.symm, ite_eq_right hyw] at this; omega
    · have := hD₂ z; rw [ite_eq_left rfl, ite_eq_right hyz, h1o z hyz.symm hwz.symm] at this; omega
    · have := hD₂ x
      rw [ite_eq_right hxz.symm, ite_eq_right hyx, h1o x hyx.symm hwx.symm] at this; omega
    · intro v h1 h2 h3 h4
      have := hD₂ v
      rw [ite_eq_right (Ne.symm h3), ite_eq_right (Ne.symm h1), add_zero, add_zero] at this
      rw [this]
      exact hothers v h1 h2 h4 h3 _ (by simp [h2, h3])

/-- **Lifting along an odd neighbour.** Let `y` be even and `t` an odd neighbour of `y`, and let
`K = G − yt`. If `S ∋ t` is realisable in `K` and `y` has no neighbour among the even vertices
of `K` outside `S`, then `S − t + y` is realisable in `G` (single transfer of `yt` towards `y`). -/
theorem realisable_lift (hG : ∀ v, 0 < G.degree v) {y t : V} (hy : y ∈ evenSet G)
    (ht : t ∉ evenSet G) (hyt : G.Adj y t) {S : Finset V} (hS : Realisable (delE G {s(y, t)}) S)
    (htS : t ∈ S) (hnb : ∀ v ∈ evenSet (delE G {s(y, t)}), v ∉ S → ¬ G.Adj y v) :
    Realisable G (insert y (S.erase t)) := by
  obtain ⟨hSE, D', hD'⟩ := hS
  obtain ⟨hKy, hKt, hKo⟩ := delE_single_facts hyt
  obtain ⟨-, k, hk⟩ := mem_evenSet_iff.mp hy
  have hyodd : Odd ((delE G {s(y, t)}).degree y) := ⟨k - 1, by have := hG y; omega⟩
  have htodd : Odd (G.degree t) := odd_of_not_mem_evenSet hG ht
  have hteven : Even ((delE G {s(y, t)}).degree t) := by
    obtain ⟨j, hj⟩ := htodd; exact ⟨j, by omega⟩
  have hcond : (Finset.univ.filter
      (fun v => (delE G {s(y, t)}).Adj y v ∧ D'.ends v = 0)).card < D'.ends t := by
    rw [hD' t, profile_even_mem hteven htS, Finset.card_eq_zero.mpr]
    · exact Nat.two_pos
    rw [Finset.filter_eq_empty_iff]
    rintro v - ⟨hadj, h0⟩
    obtain ⟨hvE, hvS⟩ := mem_of_ends_eq_zero hD'
      (by rw [degree_pos_iff_exists_adj]; exact ⟨y, hadj.symm⟩) h0
    exact hnb v hvE hvS (delE_le hadj)
  obtain ⟨D, -, hDy, hDt, hDo⟩ := fan_single hyt fan_edgeSet D' hcond
  have hne : y ≠ t := hyt.ne
  refine ⟨?_, D, fun v => ?_⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hy
    obtain ⟨hvt, hvS⟩ := Finset.mem_erase.mp hv
    have hvK := hSE hvS
    have hvy : v ≠ y := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hyodd) (mem_evenSet_iff.mp hvK).2
    rw [mem_evenSet_iff, ← hKo v hvy hvt]
    exact mem_evenSet_iff.mp hvK
  by_cases h1 : v = y
  · subst h1
    rw [hDy, hD' v, profile_odd hyodd, profile_even_mem (mem_evenSet_iff.mp hy).2
      (Finset.mem_insert_self _ _)]
  by_cases h2 : v = t
  · subst h2
    rw [hD' v, profile_even_mem hteven htS] at hDt
    rw [profile_odd htodd]
    omega
  rw [hDo v h1 h2, hD' v]
  apply profile_congr (hKo v h1 h2)
  simp [h1, h2]

omit [Fintype V] [DecidableEq V] in
theorem exists_adj_of_walk {K : SimpleGraph V} {a b : V} (p : K.Walk a b) (hab : a ≠ b) :
    ∃ c, K.Adj a c := by
  cases p with
  | nil => exact absurd rfl hab
  | cons h _ => exact ⟨_, h⟩

/-- **Base of the descent**: `y` has an even neighbour. -/
theorem two_step_base (hL : LovaszStatement.{u}) (hG : ∀ v, 0 < G.degree v)
    (hn : Even (Fintype.card V)) {y w : V} (hy : y ∈ evenSet G) (hw : w ∈ evenSet G) (hyw : y ≠ w)
    (h4 : 4 ≤ (evenSet G).card) (hnb : ∃ v ∈ evenSet G, G.Adj y v) :
    ∃ v ∈ evenSet G, v ≠ y ∧ v ≠ w ∧ Realisable G (((evenSet G).erase w).erase v) := by
  by_cases ayw : G.Adj y w
  · by_cases hall : ∀ v ∈ evenSet G, v ≠ y → v ≠ w → G.Adj y v
    · -- the star case
      have hc : 1 < (((evenSet G).erase y).erase w).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hyw.symm, hw⟩),
          Finset.card_erase_of_mem hy]
        omega
      obtain ⟨x, hx, z, hz, hxz⟩ := Finset.one_lt_card.mp hc
      simp only [Finset.mem_erase] at hx hz
      rcases realisable_of_star hL hG hy hw hx.2.2 hz.2.2 hyw (Ne.symm hx.2.1) (Ne.symm hz.2.1)
          (Ne.symm hx.1) (Ne.symm hz.1) hxz ayw (hall x hx.2.2 hx.2.1 hx.1)
          (hall z hz.2.2 hz.2.1 hz.1) with h | h
      · exact ⟨x, hx.2.2, hx.2.1, hx.1, h⟩
      · exact ⟨z, hz.2.2, hz.2.1, hz.1, h⟩
    · push Not at hall
      obtain ⟨v, hv, hvy, hvw, hnadj⟩ := hall
      exact ⟨v, hv, hvy, hvw, realisable_of_edge hL hG hn hy hw hv ayw hnadj (Ne.symm hvy)
        (Ne.symm hvw)⟩
  · obtain ⟨t, ht, ayt⟩ := hnb
    have hty : t ≠ y := ayt.ne.symm
    have htw : t ≠ w := by rintro rfl; exact ayw ayt
    refine ⟨t, ht, hty, htw, ?_⟩
    rw [Finset.erase_right_comm]
    exact realisable_of_edge hL hG hn hy ht hw ayt ayw hyw htw

/-- **Two-step descent along a path.** Induction on the length of a path from `y` to another
even vertex. If `y` has an even neighbour, `two_step_base` applies. Otherwise the second vertex
`t` of the path is odd; in `G − yt` the vertex `t` takes the place of `y`, and the path is
shorter. `realisable_lift` brings the result back. -/
theorem two_step_aux (hL : LovaszStatement.{u}) (hn : Even (Fintype.card V)) (k : ℕ) :
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (y w s : V) (p : G.Walk y s), p.IsPath →
      p.length = k → (∀ v, 0 < G.degree v) → y ∈ evenSet G → w ∈ evenSet G → y ≠ w →
      4 ≤ (evenSet G).card → s ∈ evenSet G → s ≠ y →
      ∃ v ∈ evenSet G, v ≠ y ∧ v ≠ w ∧ Realisable G (((evenSet G).erase w).erase v) := by
  induction k with
  | zero =>
    intro G _ y w s p _ hk _ _ _ _ _ _ hsy
    exact absurd (Walk.eq_of_length_eq_zero hk).symm hsy
  | succ k ih =>
    intro G _ y w s p hp hk hG hy hw hyw h4 hs hsy
    by_cases hnb : ∃ v ∈ evenSet G, G.Adj y v
    · exact two_step_base hL hG hn hy hw hyw h4 hnb
    push Not at hnb
    cases p with
    | nil => exact absurd rfl hsy
    | @cons _ t _ hyt q =>
      rw [Walk.cons_isPath_iff] at hp
      obtain ⟨hq, hyq⟩ := hp
      have hk' : q.length = k := by simpa using hk
      have htE : t ∉ evenSet G := fun h => hnb t h hyt
      have hts : t ≠ s := by rintro rfl; exact htE hs
      have hyt' : y ≠ t := hyt.ne
      have htw : t ≠ w := by rintro rfl; exact htE hw
      have hqe : ∀ e ∈ q.edges, e ∈ (delE G {s(y, t)}).edgeSet := by
        intro e he
        rw [delE_edgeSet]
        refine ⟨q.edges_subset_edgeSet he, ?_⟩
        intro hmem
        rw [Finset.mem_singleton] at hmem
        subst hmem
        exact hyq (q.fst_mem_support_of_mem_edges he)
      obtain ⟨hKy, hKt, hKo⟩ := delE_single_facts hyt
      obtain ⟨-, j, hj⟩ := mem_evenSet_iff.mp hy
      have hyodd : Odd ((delE G {s(y, t)}).degree y) := ⟨j - 1, by have := hG y; omega⟩
      have hteven : Even ((delE G {s(y, t)}).degree t) := by
        obtain ⟨i, hi⟩ := odd_of_not_mem_evenSet hG htE; exact ⟨i, by omega⟩
      have hKpos : ∀ v, 0 < (delE G {s(y, t)}).degree v := by
        intro v
        by_cases h1 : v = y
        · subst h1; exact hyodd.pos
        by_cases h2 : v = t
        · subst h2
          rw [degree_pos_iff_exists_adj]
          exact exists_adj_of_walk (q.transfer _ hqe) hts
        rw [hKo v h1 h2]; exact hG v
      have hEvK : evenSet (delE G {s(y, t)}) = insert t ((evenSet G).erase y) := by
        ext v
        simp only [Finset.mem_insert, Finset.mem_erase]
        by_cases h1 : v = y
        · subst h1
          simp only [hyt', false_or, ne_eq, not_true_eq_false, false_and, iff_false]
          exact fun h => (Nat.not_even_iff_odd.mpr hyodd) (mem_evenSet_iff.mp h).2
        by_cases h2 : v = t
        · subst h2
          simp only [true_or, iff_true]
          exact mem_evenSet_iff.mpr ⟨hKpos v, hteven⟩
        simp only [h1, h2, false_or, ne_eq, not_false_eq_true, true_and]
        rw [mem_evenSet_iff, mem_evenSet_iff, hKo v h1 h2]
      have h4K : 4 ≤ (evenSet (delE G {s(y, t)})).card := by
        rw [hEvK, Finset.card_insert_of_notMem (fun h => htE (Finset.mem_of_mem_erase h)),
          Finset.card_erase_of_mem hy]
        omega
      have hwK : w ∈ evenSet (delE G {s(y, t)}) := by
        rw [hEvK]; exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hyw.symm, hw⟩)
      have hsK : s ∈ evenSet (delE G {s(y, t)}) := by
        rw [hEvK]; exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hsy, hs⟩)
      have htK : t ∈ evenSet (delE G {s(y, t)}) := by rw [hEvK]; exact Finset.mem_insert_self _ _
      obtain ⟨v, hvK, hvt, hvw, hreal⟩ := ih (delE G {s(y, t)}) t w s (q.transfer _ hqe)
        (hq.transfer hqe) (by rw [Walk.length_transfer, hk']) hKpos htK hwK htw h4K hsK hts.symm
      have hvE : v ∈ (evenSet G).erase y := by
        rw [hEvK] at hvK
        exact (Finset.mem_insert.mp hvK).resolve_left hvt
      obtain ⟨hvy, hvG⟩ := Finset.mem_erase.mp hvE
      have htS : t ∈ ((evenSet (delE G {s(y, t)})).erase w).erase v :=
        Finset.mem_erase.mpr ⟨Ne.symm hvt, Finset.mem_erase.mpr ⟨htw, htK⟩⟩
      have hlift := realisable_lift hG hy htE hyt hreal htS (by
        intro v' hv' hv'S
        have hv't : v' ≠ t := by rintro rfl; exact hv'S htS
        rw [hEvK] at hv'
        exact hnb v' (Finset.mem_of_mem_erase ((Finset.mem_insert.mp hv').resolve_left hv't)))
      refine ⟨v, hvG, hvy, hvw, ?_⟩
      convert hlift using 1
      ext a
      rw [hEvK]
      simp only [Finset.mem_insert, Finset.mem_erase]
      by_cases h1 : a = y
      · subst h1; simp [hvy.symm, hyw, hy]
      by_cases h2 : a = t
      · subst h2; simp [htE, h1]
      simp [h1, h2]

omit [DecidableEq V] in
theorem degree_pos_of_connected (hconn : G.Connected) {a b : V} (hab : a ≠ b) (v : V) :
    0 < G.degree v := by
  rw [degree_pos_iff_exists_adj]
  by_cases hva : v = a
  · subst hva
    obtain ⟨p⟩ := hconn.preconnected v b
    exact exists_adj_of_walk p hab
  · obtain ⟨p⟩ := hconn.preconnected v a
    exact exists_adj_of_walk p hva

/-- **Two-step faithful descent.** Let `G` be connected of even order with at least four even
vertices. For all distinct even `y, w` there is an even `v ∉ {y, w}` such that `Ev ∖ {w, v}` is
realisable: from the realisable set `Ev ∖ {w}` (Lemma 3) one can remove a second vertex while
keeping `y`. -/
theorem two_step_descent (hL : LovaszStatement.{u}) (hconn : G.Connected)
    (hn : Even (Fintype.card V)) (h4 : 4 ≤ (evenSet G).card) {y w : V} (hy : y ∈ evenSet G)
    (hw : w ∈ evenSet G) (hyw : y ≠ w) :
    ∃ v ∈ evenSet G, v ≠ y ∧ v ≠ w ∧ Realisable G (((evenSet G).erase w).erase v) := by
  obtain ⟨p⟩ := hconn.preconnected y w
  exact two_step_aux hL hn _ G y w w p.bypass p.bypass_isPath rfl
    (degree_pos_of_connected hconn hyw) hy hw hyw h4 hw (Ne.symm hyw)

end steps

end Gallai
