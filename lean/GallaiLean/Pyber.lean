import GallaiLean.BP3

/-!
# Pyber's theorem

**Theorem** (Pyber 1996). If every cycle of `G` passes through a vertex of odd degree (that is,
the vertices of positive even degree induce a forest), then `p(G) ≤ ⌊|V|/2⌋`. Connectivity is
not needed.

Write `E` for the set of vertices of positive even degree, `e = |E|`, and `b = ends_D`. We prove
the stronger **realisable form** (`pyber_claim`): some `S ⊆ E` with `|S| ≤ ⌊e/2⌋` is realisable.
By the size identity, this gives `p(G) ≤ |O|/2 + ⌊e/2⌋ ≤ ⌊|V|/2⌋`.

The proof is by strong induction on `4e + ∑ deg`. It uses only Lovász's theorem and Fan's
lemmas.

*Leaf case* (`G[E]` has an edge). Since `G[E]` is a forest, some `r ∈ E` has exactly one even
neighbour `p` (`exists_even_leaf`). In `G − rp` both `r` and `p` are odd, `e` drops by two, and
the forest condition is kept. Induction gives `S'`. Every neighbour of `r` in `G − rp` is odd,
so it has an end. Hence Fan's lemma moves an end from `p` to `r`, which realises `S' ∪ {r}`.

*Independent case* (`E` is independent). If `E = ∅`, use Lovász. Otherwise take an odd vertex
`o` adjacent to `E`, and let `Y = N(o) ∩ E`, with `k = |Y| ≥ 1`. Delete all edges from `o` to
`Y` (`cut G o Y`). Then the vertices of `Y` become odd, and `o` is the only possible new even
vertex. The even set of the result is independent. Induction gives a realisation with
`b(o) = a ∈ {0, 1, 2}` and `b ≡ 1` on `Y`. Put the `k` edges back:
* First, `q = (k + 1 − a)/2` times use Fan's grouped lemma with donors the remaining `Y`-vertices
  and receiver `o` (`cut_phase1`). The donors carry more ends than the zero-end neighbours of
  `o`, which are the earlier donors.
* Then, `k − q` times use Fan's lemma from `o` to a `Y`-vertex (`cut_phase2`). Each
  `Y`-vertex has only odd neighbours, so none has zero ends.
At the end `b(o) = 1`, and the vertices of `Y` that received carry two ends. The count gives
`|S| ≤ ⌊e/2⌋` in every parity case.
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ### The hypothesis and the claim -/

/-- Every cycle of `G` passes through a vertex of odd degree. Equivalently, the vertices of even
degree induce a forest. -/
def OddOnCycles (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ (v : V) (c : G.Walk v v), c.IsCycle → ∃ w ∈ c.support, Odd (G.degree w)

/-- The realisable form of Pyber's bound: some `S` with `|S| ≤ ⌊e/2⌋` is realisable. -/
def PyberClaim (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ S : Finset V, S.card ≤ (evenSet G).card / 2 ∧ Realisable G S

/-- The induction measure `4e + ∑ deg`. -/
def pyberMeasure (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  4 * (evenSet G).card + ∑ w, G.degree w

omit [DecidableEq V] in
/-- If no two even vertices are adjacent, every cycle meets an odd vertex. -/
theorem oddOnCycles_of_indep (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ∀ a b, G.Adj a b → a ∈ evenSet G → b ∉ evenSet G) : OddOnCycles G := by
  intro v c hc
  obtain ⟨x, hadj, p, rfl⟩ := Walk.exists_eq_cons_of_length_pos c (by
    have := hc.three_le_length; omega)
  have hpos : ∀ {a b : V}, G.Adj a b → 0 < G.degree a :=
    fun h => (G.degree_pos_iff_exists_adj _).mpr ⟨_, h⟩
  by_cases hv : Odd (G.degree v)
  · exact ⟨v, by simp, hv⟩
  · have hvE : v ∈ evenSet G := mem_evenSet_iff.mpr ⟨hpos hadj, by rw [Nat.odd_iff] at hv; omega⟩
    have hxE := h v x hadj hvE
    refine ⟨x, by simp, ?_⟩
    rw [mem_evenSet_iff] at hxE
    rw [Nat.odd_iff]
    have h1 := hpos hadj.symm
    have : G.degree x % 2 ≠ 0 := fun h0 => hxE ⟨h1, h0⟩
    omega

/-- Deleting an edge between two even vertices keeps the forest condition. -/
theorem oddOnCycles_delEdge (G : SimpleGraph V) [DecidableRel G.Adj] (hF : OddOnCycles G)
    {r p : V} (hrp : G.Adj r p) (hr : r ∈ evenSet G) (hp : p ∈ evenSet G) :
    OddOnCycles (delEdge G r p) := by
  intro v c hc
  have hsub : ∀ e ∈ c.edges, e ∈ G.edgeSet :=
    fun e he => ((delEdge_edgeSet G r p e).mp (c.edges_subset_edgeSet he)).1
  obtain ⟨w, hw, hodd⟩ := hF v (c.transfer G hsub) (hc.transfer hsub)
  rw [Walk.support_transfer] at hw
  refine ⟨w, hw, ?_⟩
  have hwr : w ≠ r := fun h => not_odd_of_mem_evenSet hr (h ▸ hodd)
  have hwp : w ≠ p := fun h => not_odd_of_mem_evenSet hp (h ▸ hodd)
  rwa [delEdge_degree_of_ne G hrp hwr hwp]

omit [DecidableEq V] in
/-- **Leaves of the even forest.** If the even vertices induce a forest with an edge, then some
even vertex has exactly one even neighbour. -/
theorem exists_even_leaf (G : SimpleGraph V) [DecidableRel G.Adj] (hF : OddOnCycles G)
    {a b : V} (ha : a ∈ evenSet G) (hb : b ∈ evenSet G) (hab : G.Adj a b) :
    ∃ r p, r ∈ evenSet G ∧ p ∈ evenSet G ∧ G.Adj r p ∧ ∀ q ∈ evenSet G, G.Adj r q → q = p := by
  classical
  by_contra hno
  push Not at hno
  have key : ∀ n : ℕ, ∃ (u v : V) (P : G.Walk u v), P.IsPath ∧ P.length = n + 1 ∧
      ∀ w ∈ P.support, w ∈ evenSet G := by
    intro n
    induction n with
    | zero =>
      refine ⟨a, b, Walk.cons hab Walk.nil, by simp [hab.ne], rfl, ?_⟩
      intro w hw
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hw
      rcases hw with rfl | rfl
      · exact ha
      · exact hb
    | succ n ih =>
      obtain ⟨u, v, P, hP, hlen, hsupp⟩ := ih
      obtain ⟨u₁, h, P', rfl⟩ := Walk.exists_eq_cons_of_length_pos P (by omega)
      have hu : u ∈ evenSet G := hsupp u (by simp)
      have hu₁ : u₁ ∈ evenSet G := hsupp u₁ (by simp)
      obtain ⟨q, hq, huq, hqu₁⟩ := hno u u₁ hu hu₁ h
      have hqu : q ≠ u := huq.ne.symm
      rw [Walk.cons_isPath_iff] at hP
      obtain ⟨hP', huP'⟩ := hP
      by_cases hqs : q ∈ P'.support
      · exfalso
        have hT : (P'.takeUntil q hqs).IsPath := hP'.takeUntil hqs
        have huT : u ∉ (P'.takeUntil q hqs).support :=
          fun hm => huP' (Walk.support_takeUntil_subset_support P' hqs hm)
        have hc : (Walk.cons huq.symm (Walk.cons h (P'.takeUntil q hqs))).IsCycle := by
          rw [Walk.cons_isCycle_iff]
          refine ⟨(Walk.cons_isPath_iff _ _).mpr ⟨hT, huT⟩, ?_⟩
          rw [Walk.edges_cons, List.mem_cons]
          rintro (he | he)
          · rw [Sym2.eq_iff] at he
            rcases he with ⟨h1, -⟩ | ⟨h1, -⟩
            · exact hqu h1
            · exact hqu₁ h1
          · exact huT (Walk.snd_mem_support_of_mem_edges _ he)
        obtain ⟨w, hw, hodd⟩ := hF q _ hc
        have hwE : w ∈ evenSet G := by
          simp only [Walk.support_cons, List.mem_cons] at hw
          rcases hw with rfl | rfl | hw
          · exact hq
          · exact hu
          · exact hsupp w (by
              rw [Walk.support_cons, List.mem_cons]
              exact Or.inr (Walk.support_takeUntil_subset_support P' hqs hw))
        exact not_odd_of_mem_evenSet hwE hodd
      · refine ⟨q, v, Walk.cons huq.symm (Walk.cons h P'), ?_, ?_, ?_⟩
        · rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff]
          refine ⟨⟨hP', huP'⟩, ?_⟩
          rw [Walk.support_cons, List.mem_cons]
          rintro (h' | h')
          · exact hqu h'
          · exact hqs h'
        · simp only [Walk.length_cons] at hlen ⊢
          omega
        · intro w hw
          rw [Walk.support_cons, List.mem_cons] at hw
          rcases hw with rfl | hw
          · exact hq
          · exact hsupp w hw
  obtain ⟨u, v, P, hP, hlen, -⟩ := key (Fintype.card V)
  have := hP.length_lt
  omega

/-! ### Cutting the edges from one vertex to a set -/

section cut

variable (G : SimpleGraph V) (o : V)

/-- `G` with the edges joining `o` to `R` removed. -/
def cut (R : Finset V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ ¬ (a = o ∧ b ∈ R) ∧ ¬ (b = o ∧ a ∈ R)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩

instance cut.decRel [DecidableRel G.Adj] (R : Finset V) : DecidableRel (cut G o R).Adj :=
  fun a b => inferInstanceAs (Decidable (G.Adj a b ∧ ¬ (a = o ∧ b ∈ R) ∧ ¬ (b = o ∧ a ∈ R)))

omit [Fintype V] [DecidableEq V] in
theorem cut_adj {R : Finset V} {a b : V} :
    (cut G o R).Adj a b ↔ G.Adj a b ∧ ¬ (a = o ∧ b ∈ R) ∧ ¬ (b = o ∧ a ∈ R) := Iff.rfl

omit [Fintype V] [DecidableEq V] in
theorem cut_empty : cut G o ∅ = G := by
  ext a b
  exact ⟨fun h => h.1, fun h => ⟨h, fun h' => Finset.notMem_empty _ h'.2,
    fun h' => Finset.notMem_empty _ h'.2⟩⟩

omit [Fintype V] in
theorem cut_edgeSet_erase {R : Finset V} {t : V} (_ht : t ∈ R) (hto : G.Adj t o) :
    ∀ e, e ∈ (cut G o (R.erase t)).edgeSet ↔ e ∈ (cut G o R).edgeSet ∨ e = s(t, o) := by
  intro e
  induction e using Sym2.inductionOn with
  | hf a b =>
  simp only [mem_edgeSet, cut_adj, Finset.mem_erase, Sym2.eq_iff]
  have hto' : t ≠ o := hto.ne
  constructor
  · rintro ⟨hab, h1, h2⟩
    by_cases hc : (a = t ∧ b = o) ∨ (a = o ∧ b = t)
    · exact Or.inr hc
    · left
      refine ⟨hab, ?_, ?_⟩
      · rintro ⟨hao, hb⟩
        exact h1 ⟨hao, fun hbt => hc (Or.inr ⟨hao, hbt⟩), hb⟩
      · rintro ⟨hbo, ha⟩
        exact h2 ⟨hbo, fun hat => hc (Or.inl ⟨hat, hbo⟩), ha⟩
  · rintro (⟨hab, h1, h2⟩ | ⟨hat, hbo⟩ | ⟨hao, hbt⟩)
    · exact ⟨hab, fun h => h1 ⟨h.1, h.2.2⟩, fun h => h2 ⟨h.1, h.2.2⟩⟩
    · rw [hat, hbo]
      refine ⟨hto, ?_, ?_⟩
      · rintro ⟨h, -⟩; exact hto' h
      · rintro ⟨-, h, -⟩; exact h rfl
    · rw [hao, hbt]
      refine ⟨hto.symm, ?_, ?_⟩
      · rintro ⟨-, h, -⟩; exact h rfl
      · rintro ⟨h, -⟩; exact hto' h

variable [DecidableRel G.Adj]

theorem cut_degree {R : Finset V} (hR : ∀ y ∈ R, G.Adj o y) (w : V) :
    (cut G o R).degree w + (if w = o then R.card else 0) + (if w ∈ R then 1 else 0) =
      G.degree w := by
  have hoR : o ∉ R := fun h => G.loopless.irrefl o (hR o h)
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree, neighborFinset_eq_filter,
    neighborFinset_eq_filter (G := G), Finset.card_filter, Finset.card_filter]
  have hy : ∀ y, (if G.Adj w y then 1 else 0) =
      (if (cut G o R).Adj w y then 1 else 0) + (if w = o ∧ y ∈ R then 1 else 0) +
        (if y = o ∧ w ∈ R then 1 else 0) := by
    intro y
    by_cases h1 : w = o ∧ y ∈ R
    · have hadj : G.Adj w y := h1.1 ▸ hR y h1.2
      have h2 : ¬ (y = o ∧ w ∈ R) := fun h => hoR (h1.1 ▸ h.2)
      have h3 : ¬ (cut G o R).Adj w y := fun h => h.2.1 h1
      rw [ite_eq_left hadj, ite_eq_left h1, ite_eq_right h2, ite_eq_right h3]
    · by_cases h2 : y = o ∧ w ∈ R
      · have hadj : G.Adj w y := h2.1 ▸ (hR w h2.2).symm
        have h3 : ¬ (cut G o R).Adj w y := fun h => h.2.2 h2
        rw [ite_eq_left hadj, ite_eq_right h1, ite_eq_left h2, ite_eq_right h3]
      · rw [ite_eq_right h1, ite_eq_right h2]
        by_cases hadj : G.Adj w y
        · have h3 : (cut G o R).Adj w y := ⟨hadj, h1, h2⟩
          rw [ite_eq_left hadj, ite_eq_left h3]
        · have h3 : ¬ (cut G o R).Adj w y := fun h => hadj h.1
          rw [ite_eq_right hadj, ite_eq_right h3]
  rw [Finset.sum_congr rfl (fun y _ => hy y), Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  · congr 1
    by_cases hw : w = o
    · simp [hw]
    · simp [hw]
  · by_cases hw : w ∈ R
    · simp [hw]
    · simp [hw]

theorem cut_sum_degree {R : Finset V} (hR : ∀ y ∈ R, G.Adj o y) :
    (∑ w, (cut G o R).degree w) + 2 * R.card = ∑ w, G.degree w := by
  rw [← Finset.sum_congr rfl (fun w _ => cut_degree G o hR w), Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  simp
  ring

/-- **Phase 1**: `q` grouped transfers into `o`, from the remaining vertices of `Y`. -/
theorem cut_phase1 {Y : Finset V} (hY : ∀ y ∈ Y, G.Adj o y) (f : V → ℕ)
    (hf : ∀ w, w ∉ Y → w ≠ o → G.Adj o w → 0 < f w) (q : ℕ) :
    ∀ R ⊆ Y, ∀ D : PathDecomp (cut G o R), (∀ y ∈ R, D.ends y = 1) →
      (∀ y ∈ Y, y ∉ R → D.ends y = 0) → (∀ w, w ∉ Y → w ≠ o → D.ends w = f w) →
      2 * (Y.card - R.card + q) ≤ Y.card + 1 →
      ∃ R' ⊆ R, R'.card + q = R.card ∧ ∃ D' : PathDecomp (cut G o R'),
        (∀ y ∈ R', D'.ends y = 1) ∧ (∀ y ∈ Y, y ∉ R' → D'.ends y = 0) ∧
        (∀ w, w ∉ Y → w ≠ o → D'.ends w = f w) ∧ D'.ends o = D.ends o + q := by
  have hoY : o ∉ Y := fun h => G.loopless.irrefl o (hY o h)
  induction q with
  | zero =>
    intro R _ D h1 h2 h3 _
    exact ⟨R, subset_refl R, by simp, D, h1, h2, h3, by simp⟩
  | succ q ih =>
    intro R hR D h1 h2 h3 hc
    have hRY := Finset.card_le_card hR
    have hz : Finset.univ.filter (fun w => (cut G o R).Adj o w ∧ D.ends w = 0) ⊆ Y \ R := by
      intro w hw
      rw [Finset.mem_filter] at hw
      obtain ⟨-, ⟨hadj, hnR, -⟩, h0⟩ := hw
      have hwR : w ∉ R := fun h => hnR ⟨rfl, h⟩
      rw [Finset.mem_sdiff]
      by_contra hwY
      have hwY' : w ∉ Y := fun h => hwY ⟨h, hwR⟩
      have := hf w hwY' hadj.ne.symm hadj
      rw [h3 w hwY' hadj.ne.symm] at h0
      omega
    have hsd := Finset.card_sdiff_of_subset hR
    have hsum : ∑ t ∈ R, D.ends t = R.card := by
      rw [Finset.sum_congr rfl h1]; simp
    obtain ⟨t, htR, hK⟩ := fan_grouped D o R (fun h => hoY (hR h))
      (fun t ht h => h.2.2 ⟨rfl, ht⟩)
      (by
        rw [hsum]
        have := Finset.card_le_card hz
        omega)
    have htY := hR htR
    have hto : t ≠ o := fun h => hoY (h ▸ htY)
    obtain ⟨D₁, -, hD₁⟩ := hK (cut G o (R.erase t)) (cut_edgeSet_erase G o htR (hY t htY).symm)
    have e_t : D₁.ends t = 0 := by
      have := hD₁ t
      simp only [Ne.symm hto, ite_true, ite_false, add_zero] at this
      rw [h1 t htR] at this
      omega
    have e_o : D₁.ends o = D.ends o + 1 := by
      have := hD₁ o
      simp only [hto, ite_true, ite_false, add_zero] at this
      exact this
    have e_w : ∀ w, w ≠ t → w ≠ o → D₁.ends w = D.ends w := by
      intro w hwt hwo
      have := hD₁ w
      simp only [Ne.symm hwt, Ne.symm hwo, ite_false, add_zero] at this
      exact this
    have hRt := Finset.card_erase_of_mem htR
    have hRpos : 0 < R.card := Finset.card_pos.mpr ⟨t, htR⟩
    obtain ⟨R', hR', hcard, D', a1, a2, a3, a4⟩ := ih (R.erase t)
      ((Finset.erase_subset t R).trans hR) D₁
      (by
        intro y hy
        rw [Finset.mem_erase] at hy
        rw [e_w y hy.1 (fun h => hoY (h ▸ hR hy.2)), h1 y hy.2])
      (by
        intro y hy hny
        by_cases hyt : y = t
        · rw [hyt, e_t]
        · have hyR : y ∉ R := fun h => hny (Finset.mem_erase.mpr ⟨hyt, h⟩)
          rw [e_w y hyt (fun h => hoY (h ▸ hy)), h2 y hy hyR])
      (by
        intro w hwY hwo
        rw [e_w w (fun h => hwY (h ▸ htY)) hwo, h3 w hwY hwo])
      (by rw [hRt]; omega)
    refine ⟨R', hR'.trans (Finset.erase_subset t R), by omega, D', a1, a2, a3, ?_⟩
    rw [a4, e_o]
    ring

/-- **Phase 2**: single transfers from `o` to each remaining vertex of `Y`. -/
theorem cut_phase2 {Y : Finset V} (hY : ∀ y ∈ Y, G.Adj o y)
    (hYi : ∀ y ∈ Y, ∀ w ∈ Y, ¬ G.Adj y w) (f : V → ℕ)
    (hf : ∀ w, w ∉ Y → w ≠ o → (∃ y ∈ Y, G.Adj y w) → 0 < f w) (n : ℕ) :
    ∀ R ⊆ Y, R.card = n → ∀ D : PathDecomp (cut G o R), (∀ y ∈ R, D.ends y = 1) →
      D.ends o = 1 + R.card → (∀ w, w ∉ Y → w ≠ o → D.ends w = f w) →
      ∃ D' : PathDecomp (cut G o ∅), D'.ends o = 1 ∧ (∀ y ∈ R, D'.ends y = 2) ∧
        ∀ w, w ∉ R → w ≠ o → D'.ends w = D.ends w := by
  have hoY : o ∉ Y := fun h => G.loopless.irrefl o (hY o h)
  induction n with
  | zero =>
    intro R _ hn D _ h2 _
    obtain rfl := Finset.card_eq_zero.mp hn
    exact ⟨D, by simpa using h2, by simp, fun w _ _ => rfl⟩
  | succ n ih =>
    intro R hR hn D h1 h2 h3
    obtain ⟨t, htR⟩ : R.Nonempty := Finset.card_pos.mp (by omega)
    have htY := hR htR
    have hto : t ≠ o := fun h => hoY (h ▸ htY)
    obtain ⟨x, hx, hK⟩ := fan_grouped D t {o} (by simpa using hto)
      (by
        intro x hx h
        rw [Finset.mem_singleton] at hx
        rw [hx] at h
        exact h.2.1 ⟨rfl, htR⟩)
      (by
        have hempty : Finset.univ.filter (fun w => (cut G o R).Adj t w ∧ D.ends w = 0) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          rintro w - ⟨hadj, h0⟩
          have hwo : w ≠ o := fun h => hadj.2.2 ⟨h, htR⟩
          have hwY : w ∉ Y := fun h => hYi t htY w h hadj.1
          rw [h3 w hwY hwo] at h0
          have := hf w hwY hwo ⟨t, htY, hadj.1⟩
          omega
        rw [hempty, Finset.card_empty, Finset.sum_singleton, h2]
        omega)
    rw [Finset.mem_singleton] at hx
    rw [hx] at hK
    have hs : s(o, t) = s(t, o) := Sym2.eq_swap
    obtain ⟨D₁, -, hD₁⟩ := hK (cut G o (R.erase t)) (fun e => by
      rw [hs]; exact cut_edgeSet_erase G o htR (hY t htY).symm e)
    have e_t : D₁.ends t = 2 := by
      have := hD₁ t
      simp only [Ne.symm hto, ite_true, ite_false, add_zero] at this
      rw [h1 t htR] at this
      omega
    have e_o : D₁.ends o = R.card := by
      have := hD₁ o
      simp only [hto, ite_true, ite_false, add_zero] at this
      omega
    have e_w : ∀ w, w ≠ t → w ≠ o → D₁.ends w = D.ends w := by
      intro w hwt hwo
      have := hD₁ w
      simp only [Ne.symm hwt, Ne.symm hwo, ite_false, add_zero] at this
      exact this
    have hRt := Finset.card_erase_of_mem htR
    obtain ⟨D', c1, c2, c3⟩ := ih (R.erase t) ((Finset.erase_subset t R).trans hR)
      (by omega) D₁
      (by
        intro y hy
        rw [Finset.mem_erase] at hy
        rw [e_w y hy.1 (fun h => hoY (h ▸ hR hy.2)), h1 y hy.2])
      (by rw [e_o, hRt]; omega)
      (by
        intro w hwY hwo
        rw [e_w w (fun h => hwY (h ▸ htY)) hwo, h3 w hwY hwo])
    refine ⟨D', c1, ?_, ?_⟩
    · intro y hy
      by_cases hyt : y = t
      · rw [hyt, c3 t (Finset.notMem_erase t R) hto, e_t]
      · exact c2 y (Finset.mem_erase.mpr ⟨hyt, hy⟩)
    · intro w hwR hwo
      have hwt : w ≠ t := fun h => hwR (h ▸ htR)
      rw [c3 w (fun h => hwR (Finset.mem_of_mem_erase h)) hwo, e_w w hwt hwo]

end cut

omit [Fintype V] in
theorem PathDecomp.ends_cast {K K' : SimpleGraph V} (h : K = K') (D : PathDecomp K) (w : V) :
    (h ▸ D).ends w = D.ends w := by
  subst h
  rfl

/-! ### The two cases -/

/-- The leaf case: `G[E]` has an edge. -/
theorem pyber_case_leaf (G : SimpleGraph V) [DecidableRel G.Adj]
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj], pyberMeasure G' < pyberMeasure G →
      OddOnCycles G' → PyberClaim G')
    (hF : OddOnCycles G) {a b : V} (ha : a ∈ evenSet G) (hb : b ∈ evenSet G) (hab : G.Adj a b) :
    PyberClaim G := by
  obtain ⟨r, p, hr, hp, hrp, hleaf⟩ := exists_even_leaf G hF ha hb hab
  have hrp' : r ≠ p := hrp.ne
  have dr := delEdge_degree_left G hrp
  have dp := delEdge_degree_right G hrp
  have dw : ∀ w, w ≠ r → w ≠ p → (delEdge G r p).degree w = G.degree w :=
    fun w h1 h2 => delEdge_degree_of_ne G hrp h1 h2
  have hr' := mem_evenSet_iff.mp hr
  have hp' := mem_evenSet_iff.mp hp
  -- the even set of `G − rp`
  have hE' : ∀ w ∈ evenSet (delEdge G r p), w ≠ r ∧ w ≠ p ∧ w ∈ evenSet G := by
    intro w hw
    rw [mem_evenSet_iff] at hw
    have hwr : w ≠ r := by rintro rfl; omega
    have hwp : w ≠ p := by rintro rfl; omega
    refine ⟨hwr, hwp, ?_⟩
    rw [mem_evenSet_iff, ← dw w hwr hwp]
    exact hw
  have hsub : evenSet (delEdge G r p) ⊆ ((evenSet G).erase r).erase p := by
    intro w hw
    obtain ⟨h1, h2, h3⟩ := hE' w hw
    exact Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, h3⟩⟩
  have hc1 := Finset.card_le_card hsub
  have hc2 : (((evenSet G).erase r).erase p).card + 2 = (evenSet G).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hrp', hp⟩),
      Finset.card_erase_of_mem hr]
    have : 2 ≤ (evenSet G).card := by
      have : ({r, p} : Finset V) ⊆ evenSet G := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hr
        · exact hp
      have h2 := Finset.card_le_card this
      rw [Finset.card_pair hrp'] at h2
      exact h2
    omega
  have hsum := delEdge_sum_degree G hrp
  obtain ⟨S', hS'c, hS'sub, D', hD'⟩ := ih (delEdge G r p)
    (by unfold pyberMeasure; omega) (oddOnCycles_delEdge G hF hrp hr hp)
  have ends' := ends_of_realises hS'sub hD'
  have hrS' : r ∉ S' := fun h => (hE' r (hS'sub h)).1 rfl
  have hpS' : p ∉ S' := fun h => (hE' p (hS'sub h)).2.1 rfl
  have er : D'.ends r = 1 := by rw [ends' r]; simp only [hrS', ite_false]; omega
  have ep : D'.ends p = 1 := by rw [ends' p]; simp only [hpS', ite_false]; omega
  obtain ⟨D, -, hDr, hDp, hDo⟩ := fan_single hrp (delEdge_edgeSet G r p) D' (by
    have hempty : Finset.univ.filter (fun w => (delEdge G r p).Adj r w ∧ D'.ends w = 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro w - ⟨hadj, h0⟩
      have hGa : G.Adj r w := hadj.1
      have hwp : w ≠ p := by
        rintro rfl
        exact hadj.2 rfl
      have hwr : w ≠ r := hGa.ne.symm
      have hwE : w ∉ evenSet G := fun h => hwp (hleaf w h hGa)
      have hpos : 0 < G.degree w := (G.degree_pos_iff_exists_adj w).mpr ⟨r, hGa.symm⟩
      rw [mem_evenSet_iff] at hwE
      have hodd : G.degree w % 2 = 1 := by
        have : G.degree w % 2 ≠ 0 := fun h => hwE ⟨hpos, h⟩
        omega
      rw [ends' w, dw w hwr hwp] at h0
      omega
    rw [hempty, Finset.card_empty, ep]
    exact Nat.one_pos)
  have hSsub : insert r S' ⊆ evenSet G := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hr
    · exact (hE' x (hS'sub hx)).2.2
  refine ⟨insert r S', ?_, hSsub, D, realises_of hSsub (fun v => ?_)⟩
  · have := Finset.card_insert_le r S'
    omega
  · by_cases hvr : v = r
    · rw [hvr, hDr, er]
      simp only [Finset.mem_insert_self, ite_true]
      omega
    · by_cases hvp : v = p
      · rw [hvp]
        have : p ∉ insert r S' := by
          rw [Finset.mem_insert]
          rintro (h | h)
          · exact hrp' h.symm
          · exact hpS' h
        simp only [this, ite_false]
        omega
      · rw [hDo v hvr hvp, ends' v, dw v hvr hvp]
        have : v ∈ insert r S' ↔ v ∈ S' := by
          rw [Finset.mem_insert]
          exact ⟨fun h => h.resolve_left hvr, Or.inr⟩
        simp only [this]

/-- The independent case: no two even vertices are adjacent. -/
theorem pyber_case_indep (G : SimpleGraph V) [DecidableRel G.Adj]
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj], pyberMeasure G' < pyberMeasure G →
      OddOnCycles G' → PyberClaim G')
    (hind : ∀ a b, a ∈ evenSet G → b ∈ evenSet G → ¬ G.Adj a b) : PyberClaim G := by
  by_cases hE : evenSet G = ∅
  · obtain ⟨D, hD⟩ := lovasz_ends G (by rw [hE]; simp)
    exact ⟨∅, by simp, Finset.empty_subset _, D,
      realises_of (Finset.empty_subset _) (fun v => by simp [hD v])⟩
  obtain ⟨y₀, hy₀⟩ := Finset.nonempty_iff_ne_empty.mpr hE
  have hy₀' := mem_evenSet_iff.mp hy₀
  obtain ⟨o, hy₀o⟩ := (G.degree_pos_iff_exists_adj y₀).mp hy₀'.1
  have hoE : o ∉ evenSet G := fun h => hind y₀ o hy₀ h hy₀o
  have hpos : ∀ {x w : V}, G.Adj x w → 0 < G.degree w :=
    fun h => (G.degree_pos_iff_exists_adj _).mpr ⟨_, h.symm⟩
  have hodd : ∀ w, w ∉ evenSet G → 0 < G.degree w → G.degree w % 2 = 1 := by
    intro w hw hw0
    rw [mem_evenSet_iff] at hw
    have : G.degree w % 2 ≠ 0 := fun h => hw ⟨hw0, h⟩
    omega
  have hdo : G.degree o % 2 = 1 := hodd o hoE (hpos hy₀o)
  obtain ⟨Y, hYdef⟩ : ∃ Y : Finset V, Y = (evenSet G).filter (fun y => G.Adj o y) := ⟨_, rfl⟩
  have hYmem : ∀ y, y ∈ Y ↔ y ∈ evenSet G ∧ G.Adj o y := by
    intro y; rw [hYdef, Finset.mem_filter]
  have hY : ∀ y ∈ Y, G.Adj o y := fun y hy => ((hYmem y).mp hy).2
  have hYE : Y ⊆ evenSet G := fun y hy => ((hYmem y).mp hy).1
  have hoY : o ∉ Y := fun h => hoE (hYE h)
  have hy₀Y : y₀ ∈ Y := (hYmem y₀).mpr ⟨hy₀, hy₀o.symm⟩
  have hk : 1 ≤ Y.card := Finset.card_pos.mpr ⟨y₀, hy₀Y⟩
  have hkE := Finset.card_le_card hYE
  have hYi : ∀ y ∈ Y, ∀ w ∈ Y, ¬ G.Adj y w := fun y hy w hw => hind y w (hYE hy) (hYE hw)
  -- degrees in `cut G o Y`
  have hdeg := cut_degree G o hY
  have d_o : (cut G o Y).degree o + Y.card = G.degree o := by
    have := hdeg o
    simp only [hoY, ite_true, ite_false, add_zero] at this
    exact this
  have d_y : ∀ y ∈ Y, (cut G o Y).degree y + 1 = G.degree y := by
    intro y hy
    have := hdeg y
    have hyo : y ≠ o := fun h => hoY (h ▸ hy)
    simp only [hyo, hy, ite_true, ite_false, add_zero] at this
    exact this
  have d_w : ∀ w, w ≠ o → w ∉ Y → (cut G o Y).degree w = G.degree w := by
    intro w hwo hwY
    have := hdeg w
    simp only [hwo, hwY, ite_false, add_zero] at this
    exact this
  have hYodd : ∀ y ∈ Y, (cut G o Y).degree y % 2 = 1 := by
    intro y hy
    have h1 := d_y y hy
    have h2 := mem_evenSet_iff.mp (hYE hy)
    omega
  have hE'' : ∀ w ∈ evenSet (cut G o Y), w ≠ o → w ∈ evenSet G ∧ w ∉ Y := by
    intro w hw hwo
    rw [mem_evenSet_iff] at hw
    have hwY : w ∉ Y := fun h => by have := hYodd w h; omega
    refine ⟨?_, hwY⟩
    rw [mem_evenSet_iff, ← d_w w hwo hwY]
    exact hw
  have hEcard : (evenSet (cut G o Y)).card ≤ (evenSet G).card - Y.card +
      (if o ∈ evenSet (cut G o Y) then 1 else 0) := by
    have hsub : (evenSet (cut G o Y)).erase o ⊆ evenSet G \ Y := by
      intro w hw
      rw [Finset.mem_erase] at hw
      obtain ⟨h1, h2⟩ := hE'' w hw.2 hw.1
      exact Finset.mem_sdiff.mpr ⟨h1, h2⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset hYE] at h1
    by_cases ho : o ∈ evenSet (cut G o Y)
    · rw [Finset.card_erase_of_mem ho] at h1
      simp only [ho, ite_true]
      have := Finset.card_pos.mpr ⟨o, ho⟩
      omega
    · rw [Finset.erase_eq_of_notMem ho] at h1
      simp only [ho, ite_false, add_zero]
      exact h1
  have hEcard' : (evenSet (cut G o Y)).card ≤ (evenSet G).card - Y.card + 1 := by
    split_ifs at hEcard <;> omega
  have hsum := cut_sum_degree G o hY
  have hmeas : pyberMeasure (cut G o Y) < pyberMeasure G := by
    unfold pyberMeasure
    omega
  have hF'' : OddOnCycles (cut G o Y) := by
    apply oddOnCycles_of_indep
    intro a b hab ha hb
    have hGab : G.Adj a b := hab.1
    by_cases hao : a = o
    · have hbo : b ≠ o := fun h => hGab.ne (hao.trans h.symm)
      obtain ⟨hbE, hbY⟩ := hE'' b hb hbo
      rw [hao] at hGab
      exact hbY ((hYmem b).mpr ⟨hbE, hGab⟩)
    · by_cases hbo : b = o
      · obtain ⟨haE, haY⟩ := hE'' a ha hao
        rw [hbo] at hGab
        exact haY ((hYmem a).mpr ⟨haE, hGab.symm⟩)
      · exact hind a b (hE'' a ha hao).1 (hE'' b hb hbo).1 hGab
  obtain ⟨S'', hS''c, hS''sub, D'', hD''⟩ := ih (cut G o Y) hmeas hF''
  have ends'' := ends_of_realises hS''sub hD''
  have hYS : ∀ y ∈ Y, y ∉ S'' := fun y hy h =>
    (hE'' y (hS''sub h) (fun h' => hoY (h' ▸ hy))).2 hy
  have hYend : ∀ y ∈ Y, D''.ends y = 1 := by
    intro y hy
    rw [ends'' y, hYodd y hy]
    simp only [hYS y hy, ite_false, add_zero]
  have hposw : ∀ w, w ∉ Y → w ≠ o → w ∉ evenSet G → 0 < G.degree w → 0 < D''.ends w := by
    intro w hwY hwo hwE hw0
    rw [ends'' w, d_w w hwo hwY, hodd w hwE hw0]
    omega
  have hf1 : ∀ w, w ∉ Y → w ≠ o → G.Adj o w → 0 < D''.ends w := by
    intro w hwY hwo hadj
    refine hposw w hwY hwo (fun h => hwY ((hYmem w).mpr ⟨h, hadj⟩)) (hpos hadj)
  have hf2 : ∀ w, w ∉ Y → w ≠ o → (∃ y ∈ Y, G.Adj y w) → 0 < D''.ends w := by
    rintro w hwY hwo ⟨y, hy, hadj⟩
    exact hposw w hwY hwo (fun h => hind y w (hYE hy) h hadj) (hpos hadj)
  -- the number `a` of ends at `o`, and the number `q` of grouped transfers
  obtain ⟨a, ha⟩ : ∃ a, a = D''.ends o := ⟨_, rfl⟩
  have hoS : o ∈ S'' → o ∈ evenSet (cut G o Y) := fun h => hS''sub h
  have hpar : (a + Y.card) % 2 = 1 ∧ a ≤ 2 := by
    rw [ha, ends'' o]
    by_cases h : o ∈ S''
    · have := mem_evenSet_iff.mp (hoS h)
      simp only [h, ite_true]
      omega
    · simp only [h, ite_false, add_zero]
      omega
  obtain ⟨q, hq⟩ : ∃ q, q = (Y.card + 1 - a) / 2 := ⟨_, rfl⟩
  obtain ⟨R', hR'Y, hR'card, D₁, b1, b2, b3, b4⟩ := cut_phase1 G o hY D''.ends hf1 q Y
    (subset_refl Y) D'' hYend (fun y hy hny => absurd hy hny) (fun w _ _ => rfl)
    (by rw [Nat.sub_self]; omega)
  obtain ⟨D₂, c1, c2, c3⟩ := cut_phase2 G o hY hYi D''.ends hf2 R'.card R' hR'Y rfl D₁ b1
    (by rw [b4, ← ha]; omega) b3
  let D : PathDecomp G := (cut_empty G o) ▸ D₂
  have hD : ∀ w, D.ends w = D₂.ends w := PathDecomp.ends_cast (cut_empty G o) D₂
  have hSsub : S''.erase o ∪ R' ⊆ evenSet G := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rw [Finset.mem_erase] at hx
      exact (hE'' x (hS''sub hx.2) hx.1).1
    · exact hYE (hR'Y hx)
  refine ⟨S''.erase o ∪ R', ?_, hSsub, D, realises_of hSsub (fun v => ?_)⟩
  · -- the count
    have h1 := Finset.card_union_le (S''.erase o) R'
    have h2 : (S''.erase o).card + (if o ∈ S'' then 1 else 0) = S''.card := by
      by_cases h : o ∈ S''
      · rw [Finset.card_erase_of_mem h]
        have := Finset.card_pos.mpr ⟨o, h⟩
        simp only [h, ite_true]
        omega
      · rw [Finset.erase_eq_of_notMem h]
        simp only [h, ite_false, add_zero]
    have ha' := ends'' o
    rw [← ha] at ha'
    by_cases h : o ∈ S''
    · have := mem_evenSet_iff.mp (hoS h)
      simp only [h, ite_true] at h2 ha' hEcard
      omega
    · simp only [h, ite_false, add_zero] at h2 ha'
      by_cases h' : o ∈ evenSet (cut G o Y)
      · have := mem_evenSet_iff.mp h'
        simp only [h', ite_true] at hEcard
        omega
      · have h'' : ¬ (0 < (cut G o Y).degree o ∧ (cut G o Y).degree o % 2 = 0) :=
          fun hh => h' (mem_evenSet_iff.mpr hh)
        simp only [h', ite_false, add_zero] at hEcard
        by_cases hz : (cut G o Y).degree o = 0
        · rw [hz] at ha' d_o
          omega
        · have : (cut G o Y).degree o % 2 = 1 := by
            have : (cut G o Y).degree o % 2 ≠ 0 := fun hh => h'' ⟨Nat.pos_of_ne_zero hz, hh⟩
            omega
          omega
  · -- the profile
    rw [hD v]
    have hoS' : o ∉ S''.erase o ∪ R' := by
      rw [Finset.mem_union, Finset.mem_erase]
      rintro (h | h)
      · exact h.1 rfl
      · exact hoY (hR'Y h)
    by_cases hvo : v = o
    · rw [hvo, c1, hdo]
      simp only [hoS', ite_false]
    · by_cases hvR : v ∈ R'
      · rw [c2 v hvR]
        have := mem_evenSet_iff.mp (hYE (hR'Y hvR))
        simp only [Finset.mem_union, hvR, or_true, ite_true]
        omega
      · rw [c3 v hvR hvo]
        by_cases hvY : v ∈ Y
        · rw [b2 v hvY hvR]
          have := mem_evenSet_iff.mp (hYE hvY)
          have : v ∉ S''.erase o ∪ R' := by
            rw [Finset.mem_union, Finset.mem_erase]
            rintro (h | h)
            · exact hYS v hvY h.2
            · exact hvR h
          simp only [this, ite_false]
          omega
        · rw [b3 v hvY hvo, ends'' v, d_w v hvo hvY]
          have : v ∈ S''.erase o ∪ R' ↔ v ∈ S'' := by
            rw [Finset.mem_union, Finset.mem_erase]
            exact ⟨fun h => h.elim (fun h => h.2) (fun h => absurd h hvR),
              fun h => Or.inl ⟨hvo, h⟩⟩
          simp only [this]

/-! ### Pyber's theorem -/

/-- **Pyber's theorem, realisable form**: if every cycle meets an odd vertex, then some set of at
most `⌊e/2⌋` even vertices is realisable. -/
theorem pyber_claim (G : SimpleGraph V) [DecidableRel G.Adj] (hF : OddOnCycles G) :
    PyberClaim G := by
  suffices h : ∀ n, ∀ (G : SimpleGraph V) [DecidableRel G.Adj], pyberMeasure G = n →
      OddOnCycles G → PyberClaim G from h _ G rfl hF
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ hn hF
  have ih' : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj], pyberMeasure G' < pyberMeasure G →
      OddOnCycles G' → PyberClaim G' := fun G' _ hlt hF' => ih _ (hn ▸ hlt) G' rfl hF'
  by_cases hedge : ∃ a b, a ∈ evenSet G ∧ b ∈ evenSet G ∧ G.Adj a b
  · obtain ⟨a, b, ha, hb, hab⟩ := hedge
    exact pyber_case_leaf G ih' hF ha hb hab
  · push Not at hedge
    exact pyber_case_indep G ih' hedge

/-- **Pyber's theorem** (1996): if every cycle of `G` passes through a vertex of odd degree
(equivalently, the even-degree vertices induce a forest), then `p(G) ≤ ⌊|V|/2⌋`. -/
theorem pyber (G : SimpleGraph V) [DecidableRel G.Adj]
    (hF : ∀ (v : V) (c : G.Walk v v), c.IsCycle → ∃ w ∈ c.support, Odd (G.degree w)) :
    pathNumber G ≤ Fintype.card V / 2 := by
  obtain ⟨S, hS, hS', D, hD⟩ := pyber_claim G hF
  have hsize := Realises.size_eq hS' hD
  have h1 := pathNumber_le D
  have hdisj : Disjoint (oddSet G) (evenSet G) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact not_odd_of_mem_evenSet hv' (Finset.mem_filter.mp hv).2
  have hcard : (oddSet G).card + (evenSet G).card ≤ Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_univ _
  obtain ⟨k, hk⟩ := G.even_card_odd_degree_vertices
  unfold oddSet at hsize hcard
  omega

/-- **Pyber's theorem for independent even vertices**: if no two vertices of positive even
degree are adjacent, then `p(G) ≤ ⌊|V|/2⌋`. -/
theorem pyber_of_indep (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ∀ a b, G.Adj a b → a ∈ evenSet G → b ∉ evenSet G) :
    pathNumber G ≤ Fintype.card V / 2 :=
  pyber G (oddOnCycles_of_indep G h)

end Gallai
