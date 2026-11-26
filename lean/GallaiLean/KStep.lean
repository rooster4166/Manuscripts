import GallaiLean.EMCFour
import GallaiLean.Lovasz

/-!
# k-step descent: general transfer, reduction to base cases, one even neighbour

Endpoint-structure manuscript, section "Two descent steps, and four even vertices",
subsection "k-step descent".

`Desc G k y W₀`: some set `R` of `k` even vertices with `W₀ ⊆ R` and `y ∉ R` has
`Ev ∖ R` realisable. Lemma 3 is `Desc G 1 y {w}`, and `two_step_descent` is `Desc G 2 y {w}`.

* `realisable_transfer` (general transfer across an even edge): if `s, t` are adjacent even
  vertices and `S` is realisable in `G − st` with no neighbour of `s` among the even vertices
  of `G − st` outside `S`, then `S ∪ {s}` is realisable in `G`.
* `delE_reach_or_reach`, `connected_delE_of_not_isBridge`: after deleting an edge `ab` of a
  connected graph, every vertex reaches `a` or `b`; if `ab` is not a bridge the graph stays
  connected.
* **`desc_reduction`** (connected reduction): for every `k`, `W₀` and `m`, if `Desc` holds in
  connected graphs with `≥ m` even vertices whenever `y` has an even neighbour or every edge
  at `y` is a bridge, then it holds in all connected graphs with `≥ m` even vertices.
  Induction on the number of edges, removing a non-bridge edge `yt` to an odd neighbour.
  Neither parity nor criticality is used.
* **`desc_succ_of_unique`** (one even neighbour): if `y` has exactly one even neighbour `t`,
  then `Desc G (k+1) y {w}` follows from `k`-step descent (for vertices joined to another even
  vertex) in `G − yt`, for `k ≥ 2` and connected `G` with `≥ 2k + 2` even vertices.
* `desc_two_of_reachable`: two-step descent in this form (from `two_step_aux`).
* **`desc_three_of_unique`**: three-step descent at every even vertex with exactly one even
  neighbour (connected, even order, `e ≥ 6`).
* **`desc_three_reduction`**: three-step descent holds in all connected even-order graphs with
  `e ≥ 6` once it holds when `y` has at least two even neighbours, and when `y` has no even
  neighbour and every edge at `y` is a bridge.
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

section kstep

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `k`-step descent at `y` with required set `W₀`: some `k`-set `R` of even vertices with
`W₀ ⊆ R` and `y ∉ R` has `Ev ∖ R` realisable. -/
def Desc (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (y : V) (W₀ : Finset V) : Prop :=
  ∃ R : Finset V, R ⊆ evenSet G ∧ R.card = k ∧ W₀ ⊆ R ∧ y ∉ R ∧
    Realisable G (evenSet G \ R)

/-- **General transfer across an even edge.** If `s, t` are adjacent even vertices and `S` is
realisable in `K = G − st`, and `s` has no neighbour among the even vertices of `K` outside `S`,
then `S ∪ {s}` is realisable in `G`. -/
theorem realisable_transfer {s t : V} (hs : s ∈ evenSet G)
    (ht : t ∈ evenSet G) (hst : G.Adj s t) {S : Finset V}
    (hS : Realisable (delE G {s(s, t)}) S)
    (hnb : ∀ u ∈ evenSet (delE G {s(s, t)}), u ∉ S → ¬ G.Adj s u) :
    Realisable G (insert s S) := by
  obtain ⟨hSE, D, hD⟩ := hS
  have hne : s ≠ t := hst.ne
  obtain ⟨hKs, hKt, hKo⟩ := delE_single_facts hst
  obtain ⟨hs0, ks, hks⟩ := mem_evenSet_iff_even.mp hs
  obtain ⟨ht0, kt, hkt⟩ := mem_evenSet_iff_even.mp ht
  have hsodd : Odd ((delE G {s(s, t)}).degree s) := ⟨ks - 1, by omega⟩
  have htodd : Odd ((delE G {s(s, t)}).degree t) := ⟨kt - 1, by omega⟩
  have hcond : (Finset.univ.filter
      (fun v => (delE G {s(s, t)}).Adj s v ∧ D.ends v = 0)).card < D.ends t := by
    rw [hD t, profile_odd htodd, Finset.card_eq_zero.mpr]
    · exact Nat.one_pos
    rw [Finset.filter_eq_empty_iff]
    rintro u - ⟨hadj, h0⟩
    obtain ⟨huE, huS⟩ := mem_of_ends_eq_zero hD
      (by rw [degree_pos_iff_exists_adj]; exact ⟨s, hadj.symm⟩) h0
    exact hnb u huE huS (delE_le hadj)
  obtain ⟨D', -, hDs, hDt, hDo⟩ := fan_single hst fan_edgeSet D hcond
  have hsS : s ∉ S := fun h =>
    (Nat.not_even_iff_odd.mpr hsodd) (mem_evenSet_iff_even.mp (hSE h)).2
  have htS : t ∉ S := fun h =>
    (Nat.not_even_iff_odd.mpr htodd) (mem_evenSet_iff_even.mp (hSE h)).2
  refine ⟨?_, D', fun v => ?_⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hs
    have hvs : v ≠ s := fun h => hsS (h ▸ hv)
    have hvt : v ≠ t := fun h => htS (h ▸ hv)
    rw [mem_evenSet_iff_even, ← hKo v hvs hvt]
    exact mem_evenSet_iff_even.mp (hSE hv)
  by_cases h1 : v = s
  · subst h1
    rw [hDs, hD v, profile_odd hsodd,
      profile_even_mem (mem_evenSet_iff_even.mp hs).2 (Finset.mem_insert_self _ _)]
  by_cases h2 : v = t
  · subst h2
    rw [hD v, profile_odd htodd] at hDt
    rw [profile_even_not_mem (mem_evenSet_iff_even.mp ht).2 (by simp [Ne.symm hne, htS])]
    omega
  rw [hDo v h1 h2, hD v]
  apply profile_congr (hKo v h1 h2)
  simp [h1]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- After deleting an edge `ab`, every vertex joined to `a` or `b` by a walk ending in that set
still reaches `a` or `b`. -/
theorem delE_reach_or_reach_walk {a b : V} {x z : V} (p : G.Walk x z)
    (hz : (delE G {s(a, b)}).Reachable z a ∨ (delE G {s(a, b)}).Reachable z b) :
    (delE G {s(a, b)}).Reachable x a ∨ (delE G {s(a, b)}).Reachable x b := by
  induction p with
  | nil => exact hz
  | @cons x c z h q ih =>
    have hc := ih hz
    by_cases he : s(x, c) = s(a, b)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Or.inl (Reachable.refl _)
      · exact Or.inr (Reachable.refl _)
    · have hK : (delE G {s(a, b)}).Adj x c := delE_adj.mpr ⟨h, by simpa using he⟩
      exact hc.imp (fun h' => hK.reachable.trans h') (fun h' => hK.reachable.trans h')

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- In a connected graph minus one edge `ab`, every vertex reaches `a` or `b`. -/
theorem delE_reach_or_reach (hconn : G.Connected) (a b x : V) :
    (delE G {s(a, b)}).Reachable x a ∨ (delE G {s(a, b)}).Reachable x b := by
  obtain ⟨p⟩ := hconn.preconnected x a
  exact delE_reach_or_reach_walk p (Or.inl (Reachable.refl _))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Deleting a non-bridge edge keeps a connected graph connected. -/
theorem connected_delE_of_not_isBridge (hconn : G.Connected) {a b : V}
    (hnb : ¬ G.IsBridge s(a, b)) : (delE G {s(a, b)}).Connected := by
  have hr : (delE G {s(a, b)}).Reachable a b := by
    rw [isBridge_iff, not_not] at hnb
    simpa [delE] using hnb
  have := hconn.nonempty
  have key : ∀ x, (delE G {s(a, b)}).Reachable x a := fun x =>
    (delE_reach_or_reach hconn a b x).elim id (fun h => h.trans hr.symm)
  exact ⟨fun x y => (key x).trans (key y).symm⟩

/-- Deleting an edge from `y` (even) to `t` (odd): the even vertices of `G − yt`. -/
theorem evenSet_delE_odd (hG : ∀ v, 0 < G.degree v) {y t : V} (hy : y ∈ evenSet G)
    (ht : t ∉ evenSet G) (hyt : G.Adj y t) (hKt : 0 < (delE G {s(y, t)}).degree t) :
    evenSet (delE G {s(y, t)}) = insert t ((evenSet G).erase y) := by
  obtain ⟨hKy, hKt', hKo⟩ := delE_single_facts hyt
  have hyt' : y ≠ t := hyt.ne
  obtain ⟨-, j, hj⟩ := mem_evenSet_iff_even.mp hy
  have hyodd : Odd ((delE G {s(y, t)}).degree y) := ⟨j - 1, by have := hG y; omega⟩
  have hteven : Even ((delE G {s(y, t)}).degree t) := by
    obtain ⟨i, hi⟩ := odd_of_not_mem_evenSet hG ht; exact ⟨i, by omega⟩
  ext v
  simp only [Finset.mem_insert, Finset.mem_erase]
  by_cases h1 : v = y
  · subst h1
    simp only [hyt', false_or, ne_eq, not_true_eq_false, false_and, iff_false]
    exact fun h => (Nat.not_even_iff_odd.mpr hyodd) (mem_evenSet_iff_even.mp h).2
  by_cases h2 : v = t
  · subst h2
    simp only [true_or, iff_true]
    exact mem_evenSet_iff_even.mpr ⟨hKt, hteven⟩
  simp only [h1, h2, false_or, ne_eq, not_false_eq_true, true_and]
  rw [mem_evenSet_iff_even, mem_evenSet_iff_even, hKo v h1 h2]

/-- Deleting an edge between two even vertices: the even vertices of `G − st`. -/
theorem evenSet_delE_even {s t : V} (hs : s ∈ evenSet G) (ht : t ∈ evenSet G)
    (hst : G.Adj s t) :
    evenSet (delE G {s(s, t)}) = ((evenSet G).erase s).erase t := by
  obtain ⟨hKs, hKt, hKo⟩ := delE_single_facts hst
  obtain ⟨hs0, ks, hks⟩ := mem_evenSet_iff_even.mp hs
  obtain ⟨ht0, kt, hkt⟩ := mem_evenSet_iff_even.mp ht
  have hsodd : Odd ((delE G {s(s, t)}).degree s) := ⟨ks - 1, by omega⟩
  have htodd : Odd ((delE G {s(s, t)}).degree t) := ⟨kt - 1, by omega⟩
  ext v
  simp only [Finset.mem_erase, mem_evenSet_iff_even]
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

theorem card_edgeFinset_delE_lt {a b : V} (hab : G.Adj a b) :
    (delE G {s(a, b)}).edgeFinset.card < G.edgeFinset.card := by
  have hsub : (delE G {s(a, b)}).edgeFinset ⊆ G.edgeFinset.erase s(a, b) := by
    intro e he
    rw [mem_edgeFinset, delE_edgeSet] at he
    exact Finset.mem_erase.mpr ⟨by simpa using he.2, mem_edgeFinset.mpr he.1⟩
  have hmem : s(a, b) ∈ G.edgeFinset := mem_edgeFinset.mpr hab
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hmem] at this
  have : 0 < G.edgeFinset.card := Finset.card_pos.mpr ⟨_, hmem⟩
  omega

/-- **Connected reduction of `k`-step descent.** Suppose `Desc · k y W₀` holds in every connected
graph with at least `m` even vertices, for every even `y ∉ W₀` that has an even neighbour or all
of whose edges are bridges. Then it holds for every even `y ∉ W₀` in every connected graph with
at least `m` even vertices. (Induction on the number of edges: delete a non-bridge edge from `y`
to an odd neighbour and lift.) -/
theorem desc_reduction (k : ℕ) (W₀ : Finset V) (m : ℕ)
    (hbase : ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (y : V), G.Connected →
      y ∈ evenSet G → W₀ ⊆ evenSet G → y ∉ W₀ → m ≤ (evenSet G).card →
      ((∃ v ∈ evenSet G, G.Adj y v) ∨ ∀ t, G.Adj y t → G.IsBridge s(y, t)) →
      Desc G k y W₀) :
    ∀ (N : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] (y : V), G.edgeFinset.card ≤ N →
      G.Connected → y ∈ evenSet G → W₀ ⊆ evenSet G → y ∉ W₀ → m ≤ (evenSet G).card →
      Desc G k y W₀ := by
  intro N
  induction N with
  | zero =>
    intro G _ y hN hconn hy hW hyW hm
    apply hbase G y hconn hy hW hyW hm
    right
    intro t hyt
    have : 0 < G.edgeFinset.card :=
      Finset.card_pos.mpr ⟨s(y, t), mem_edgeFinset.mpr hyt⟩
    omega
  | succ N ih =>
    intro G _ y hN hconn hy hW hyW hm
    by_cases hb : (∃ v ∈ evenSet G, G.Adj y v) ∨ ∀ t, G.Adj y t → G.IsBridge s(y, t)
    · exact hbase G y hconn hy hW hyW hm hb
    push Not at hb
    obtain ⟨hnoev, t, hyt, hnb⟩ := hb
    have hyt' : y ≠ t := hyt.ne
    have hG := degree_pos_of_connected hconn hyt'
    have htE : t ∉ evenSet G := fun h => hnoev t h hyt
    have hKconn := connected_delE_of_not_isBridge hconn hnb
    have hKpos := degree_pos_of_connected hKconn hyt'
    have hEvK := evenSet_delE_odd hG hy htE hyt (hKpos t)
    have hWK : W₀ ⊆ evenSet (delE G {s(y, t)}) := by
      intro a ha
      rw [hEvK]
      exact Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨fun h => hyW (h ▸ ha), hW ha⟩)
    have htW : t ∉ W₀ := fun h => htE (hW h)
    have htK : t ∈ evenSet (delE G {s(y, t)}) := by rw [hEvK]; exact Finset.mem_insert_self _ _
    have hmK : m ≤ (evenSet (delE G {s(y, t)})).card := by
      rw [hEvK, Finset.card_insert_of_notMem (fun h => htE (Finset.mem_of_mem_erase h)),
        Finset.card_erase_of_mem hy]
      have : 0 < (evenSet G).card := Finset.card_pos.mpr ⟨y, hy⟩
      omega
    have hNK : (delE G {s(y, t)}).edgeFinset.card ≤ N := by
      have := card_edgeFinset_delE_lt hyt; omega
    obtain ⟨R, hRK, hRc, hWR, htR, hreal⟩ :=
      ih (delE G {s(y, t)}) t hNK hKconn htK hWK htW hmK
    have htS : t ∈ evenSet (delE G {s(y, t)}) \ R := Finset.mem_sdiff.mpr ⟨htK, htR⟩
    have hRE : ∀ a ∈ R, a ∈ evenSet G ∧ a ≠ y := by
      intro a ha
      have := hRK ha
      rw [hEvK] at this
      rcases Finset.mem_insert.mp this with rfl | h
      · exact absurd ha htR
      · exact ⟨Finset.mem_of_mem_erase h, Finset.ne_of_mem_erase h⟩
    have hlift := realisable_lift hG hy htE hyt hreal htS (by
      intro a ha haS
      have haR : a ∈ R := by
        by_contra h; exact haS (Finset.mem_sdiff.mpr ⟨ha, h⟩)
      exact hnoev a (hRE a haR).1)
    have hyR : y ∉ R := fun h => (hRE y h).2 rfl
    refine ⟨R, fun a ha => (hRE a ha).1, hRc, hWR, hyR, ?_⟩
    convert hlift using 1
    ext a
    rw [hEvK]
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    by_cases h1 : a = y
    · subst h1; simp [hy, hyR]
    by_cases h2 : a = t
    · subst h2; simp [htE, h1]
    simp [h1, h2]

/-- **One even neighbour.** Let `G` be connected with at least `2k + 2` even vertices (`k ≥ 2`),
and let the even vertex `y` have exactly one even neighbour `t`. If `k`-step descent holds (in
graphs on the same vertex type without isolated vertices and with at least `2k` even vertices) at
every even vertex joined to another even vertex, then `Desc G (k+1) y {w}` for every even
`w ≠ y`. (Transfer across `yt` from `k`-step descent in `G − yt`.) -/
theorem desc_succ_of_unique (k : ℕ) (hk : 2 ≤ k)
    (hdesc : ∀ (K : SimpleGraph V) [DecidableRel K.Adj] (y' w' : V), (∀ v, 0 < K.degree v) →
      y' ∈ evenSet K → w' ∈ evenSet K → y' ≠ w' → 2 * k ≤ (evenSet K).card →
      (∃ s ∈ evenSet K, s ≠ y' ∧ K.Reachable y' s) → Desc K k y' {w'})
    (hconn : G.Connected) (hcard : 2 * (k + 1) ≤ (evenSet G).card) {y w t : V}
    (hy : y ∈ evenSet G) (hw : w ∈ evenSet G) (hyw : y ≠ w) (ht : t ∈ evenSet G)
    (hyt : G.Adj y t) (huniq : ∀ v ∈ evenSet G, G.Adj y v → v = t) :
    Desc G (k + 1) y {w} := by
  have hyt' : y ≠ t := hyt.ne
  have hG := degree_pos_of_connected hconn hyt'
  obtain ⟨hKy, hKt, hKo⟩ := delE_single_facts hyt
  obtain ⟨-, j, hj⟩ := mem_evenSet_iff_even.mp hy
  obtain ⟨-, i, hi⟩ := mem_evenSet_iff_even.mp ht
  have hKpos : ∀ v, 0 < (delE G {s(y, t)}).degree v := by
    intro v
    by_cases h1 : v = y
    · subst h1; have := hG v; omega
    by_cases h2 : v = t
    · subst h2; have := hG v; omega
    rw [hKo v h1 h2]; exact hG v
  have hEvK := evenSet_delE_even hy ht hyt
  have hcardK : 2 * k ≤ (evenSet (delE G {s(y, t)})).card := by
    rw [hEvK, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hyt'.symm, ht⟩),
      Finset.card_erase_of_mem hy]
    omega
  -- two even vertices of `G − yt` on the same side of the deleted edge
  have hside : ∃ a ∈ evenSet (delE G {s(y, t)}), ∃ b ∈ evenSet (delE G {s(y, t)}),
      a ≠ b ∧ (delE G {s(y, t)}).Reachable a b := by
    have hAB := Finset.card_filter_add_card_filter_not (s := evenSet (delE G {s(y, t)}))
      (fun v => (delE G {s(y, t)}).Reachable v y)
    by_cases hA : 1 < ((evenSet (delE G {s(y, t)})).filter
        (fun v => (delE G {s(y, t)}).Reachable v y)).card
    · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hA
      simp only [Finset.mem_filter] at ha hb
      exact ⟨a, ha.1, b, hb.1, hab, ha.2.trans hb.2.symm⟩
    · have hB : 1 < ((evenSet (delE G {s(y, t)})).filter
          (fun v => ¬ (delE G {s(y, t)}).Reachable v y)).card := by omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hB
      simp only [Finset.mem_filter] at ha hb
      have hat := (delE_reach_or_reach hconn y t a).resolve_left ha.2
      have hbt := (delE_reach_or_reach hconn y t b).resolve_left hb.2
      exact ⟨a, ha.1, b, hb.1, hab, hat.trans hbt.symm⟩
  obtain ⟨a, ha, b, hb, hab, hrab⟩ := hside
  -- the kept vertex `y'` of the smaller descent, and its prescribed vertex `w'`
  obtain ⟨y', hy', s', hs', hy's', hr', hy'w⟩ : ∃ y' ∈ evenSet (delE G {s(y, t)}),
      ∃ s' ∈ evenSet (delE G {s(y, t)}), s' ≠ y' ∧ (delE G {s(y, t)}).Reachable y' s' ∧
        y' ≠ w := by
    by_cases haw : a = w
    · exact ⟨b, hb, a, ha, hab, hrab.symm, fun h => hab (haw.trans h.symm)⟩
    · exact ⟨a, ha, b, hb, Ne.symm hab, hrab, haw⟩
  have hwK : w ≠ t → w ∈ evenSet (delE G {s(y, t)}) := fun hwt => by
    rw [hEvK]; exact Finset.mem_erase.mpr ⟨hwt, Finset.mem_erase.mpr ⟨Ne.symm hyw, hw⟩⟩
  obtain ⟨w', hw', hy'w', hww'⟩ : ∃ w' ∈ evenSet (delE G {s(y, t)}), y' ≠ w' ∧
      (w = t ∨ w = w') := by
    by_cases hwt : w = t
    · exact ⟨s', hs', Ne.symm hy's', Or.inl hwt⟩
    · exact ⟨w, hwK hwt, hy'w, Or.inr rfl⟩
  obtain ⟨W, hWK, hWc, hw'W, -, hreal⟩ :=
    hdesc (delE G {s(y, t)}) y' w' hKpos hy' hw' hy'w' hcardK ⟨s', hs', hy's', hr'⟩
  have hWE : ∀ a ∈ W, a ∈ evenSet G ∧ a ≠ y ∧ a ≠ t := by
    intro a ha
    have := hWK ha
    rw [hEvK] at this
    simp only [Finset.mem_erase] at this
    exact ⟨this.2.2, this.2.1, this.1⟩
  have htrans := realisable_transfer hy ht hyt hreal (by
    intro u hu huS hadj
    have huW : u ∈ W := by
      by_contra h; exact huS (Finset.mem_sdiff.mpr ⟨hu, h⟩)
    exact (hWE u huW).2.2 (huniq u (hWE u huW).1 hadj))
  have htW : t ∉ W := fun h => (hWE t h).2.2 rfl
  refine ⟨insert t W, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ht
    · exact (hWE a ha).1
  · rw [Finset.card_insert_of_notMem htW, hWc]
  · intro a ha
    rw [Finset.mem_singleton] at ha
    subst ha
    rcases hww' with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · rw [h]; exact Finset.mem_insert_of_mem (hw'W (Finset.mem_singleton_self _))
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hyt' h
    · exact (hWE y h).2.1 rfl
  · have hyW : y ∉ W := fun h => (hWE y h).2.1 rfl
    convert htrans using 1
    ext a
    rw [hEvK]
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    by_cases h1 : a = y
    · subst h1; simp [hy, hyt', hyW]
    by_cases h2 : a = t
    · subst h2; simp [h1]
    simp [h1, h2]

/-- Two-step descent in the form of `Desc`, for a vertex joined to another even vertex. -/
theorem desc_two_of_reachable (hL : LovaszStatement.{u}) (hn : Even (Fintype.card V))
    (K : SimpleGraph V) [DecidableRel K.Adj] (y' w' : V) (hpos : ∀ v, 0 < K.degree v)
    (hy' : y' ∈ evenSet K) (hw' : w' ∈ evenSet K) (hyw : y' ≠ w')
    (h4 : 2 * 2 ≤ (evenSet K).card) (hr : ∃ s ∈ evenSet K, s ≠ y' ∧ K.Reachable y' s) :
    Desc K 2 y' {w'} := by
  obtain ⟨s, hs, hsy, ⟨p⟩⟩ := hr
  obtain ⟨v, hv, hvy, hvw, hreal⟩ := two_step_aux hL hn _ K y' w' s p.bypass p.bypass_isPath rfl
    hpos hy' hw' hyw (by omega) hs hsy
  refine ⟨{w', v}, ?_, Finset.card_pair (Ne.symm hvw), by simp, ?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> assumption
  · simp [hyw, Ne.symm hvy]
  · convert hreal using 1
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
    tauto

/-- **Three-step descent at a vertex with exactly one even neighbour.** -/
theorem desc_three_of_unique (hL : LovaszStatement.{u}) (hn : Even (Fintype.card V))
    (hconn : G.Connected) (h6 : 6 ≤ (evenSet G).card) {y w t : V} (hy : y ∈ evenSet G)
    (hw : w ∈ evenSet G) (hyw : y ≠ w) (ht : t ∈ evenSet G) (hyt : G.Adj y t)
    (huniq : ∀ v ∈ evenSet G, G.Adj y v → v = t) :
    Desc G 3 y {w} :=
  desc_succ_of_unique 2 le_rfl (fun K _ y' w' => desc_two_of_reachable hL hn K y' w')
    hconn h6 hy hw hyw ht hyt huniq

/-- **Reduction of three-step descent to two residual cases.** Three-step descent at `y` (with
`w` prescribed) holds in every connected graph of even order with at least six even vertices,
provided it holds when `y` has at least two even neighbours, and when `y` has no even neighbour
and every edge at `y` is a bridge. -/
theorem desc_three_reduction (hL : LovaszStatement.{u}) (hn : Even (Fintype.card V)) (w : V)
    (hres : ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (y : V), G.Connected →
      y ∈ evenSet G → w ∈ evenSet G → y ≠ w → 6 ≤ (evenSet G).card →
      ((∃ v₁ ∈ evenSet G, ∃ v₂ ∈ evenSet G, v₁ ≠ v₂ ∧ G.Adj y v₁ ∧ G.Adj y v₂) ∨
        ((∀ v ∈ evenSet G, ¬ G.Adj y v) ∧ ∀ t, G.Adj y t → G.IsBridge s(y, t))) →
      Desc G 3 y {w})
    (hconn : G.Connected) (h6 : 6 ≤ (evenSet G).card) {y : V} (hy : y ∈ evenSet G)
    (hw : w ∈ evenSet G) (hyw : y ≠ w) :
    Desc G 3 y {w} := by
  refine desc_reduction 3 {w} 6 ?_ _ G y le_rfl hconn hy (by simpa using hw) (by simpa using hyw)
    h6
  intro G _ y hconn hy hW hyW hm hcase
  have hw : w ∈ evenSet G := hW (Finset.mem_singleton_self w)
  have hyw : y ≠ w := fun h => hyW (by simp [h])
  by_cases hnb : ∃ v ∈ evenSet G, G.Adj y v
  · obtain ⟨t, ht, hyt⟩ := hnb
    by_cases htwo : ∃ v₂ ∈ evenSet G, v₂ ≠ t ∧ G.Adj y v₂
    · obtain ⟨v₂, hv₂, hv₂t, hyv₂⟩ := htwo
      exact hres G y hconn hy hw hyw hm (Or.inl ⟨t, ht, v₂, hv₂, Ne.symm hv₂t, hyt, hyv₂⟩)
    · push Not at htwo
      exact desc_three_of_unique hL hn hconn hm hy hw hyw ht hyt
        (fun v hv hadj => by by_contra h; exact htwo v hv h hadj)
  · push Not at hnb
    exact hres G y hconn hy hw hyw hm
      (Or.inr ⟨hnb, hcase.resolve_left (by push Not; exact hnb)⟩)

/-- `desc_three_of_unique` without the Lovász hypothesis (`lovaszStatement`). -/
theorem desc_three_of_unique' (hn : Even (Fintype.card V)) (hconn : G.Connected)
    (h6 : 6 ≤ (evenSet G).card) {y w t : V} (hy : y ∈ evenSet G) (hw : w ∈ evenSet G)
    (hyw : y ≠ w) (ht : t ∈ evenSet G) (hyt : G.Adj y t)
    (huniq : ∀ v ∈ evenSet G, G.Adj y v → v = t) : Desc G 3 y {w} :=
  desc_three_of_unique lovaszStatement hn hconn h6 hy hw hyw ht hyt huniq

/-- `desc_three_reduction` without the Lovász hypothesis (`lovaszStatement`). -/
theorem desc_three_reduction' (hn : Even (Fintype.card V)) (w : V)
    (hres : ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (y : V), G.Connected →
      y ∈ evenSet G → w ∈ evenSet G → y ≠ w → 6 ≤ (evenSet G).card →
      ((∃ v₁ ∈ evenSet G, ∃ v₂ ∈ evenSet G, v₁ ≠ v₂ ∧ G.Adj y v₁ ∧ G.Adj y v₂) ∨
        ((∀ v ∈ evenSet G, ¬ G.Adj y v) ∧ ∀ t, G.Adj y t → G.IsBridge s(y, t))) →
      Desc G 3 y {w})
    (hconn : G.Connected) (h6 : 6 ≤ (evenSet G).card) {y : V} (hy : y ∈ evenSet G)
    (hw : w ∈ evenSet G) (hyw : y ≠ w) : Desc G 3 y {w} :=
  desc_three_reduction lovaszStatement hn w hres hconn h6 hy hw hyw

end kstep

end Gallai
