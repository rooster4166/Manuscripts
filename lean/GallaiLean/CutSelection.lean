import GallaiLean.PairingLemma
import GallaiLean.EmmTemplate
import GallaiLean.Realisable

/-!
# Cut selection (endpoint-min-max, Theorem 21)

**`cs_all`**: every connected graph `G` of even order has a pairing `P` of its even vertices such that
every half-set containing exactly one vertex of each pair satisfies the cut conditions `CutOK` of
even-degrees §12.4.

The proof follows the second proof in the manuscript.
1. Take a `T`-join `X` for `T = Ev` (`exists_tjoin`, by paths and symmetric differences), and put
   `F = G − X`, whose degrees are all odd.
2. Build the auxiliary graph `B` on `V × V`. Copy `v` carries `F^v`, which is `F` with the edges at
   `v` replaced by the non-edges at `v`. Each `X`-edge `vx` gives the edge `(v,x)–(x,v)`. Its odd
   vertices are exactly `(v,v)`, `v ∈ Ev`.
3. Apply the pairing lemma (`pairing_lemma`) to `B`. For each `v` and `Y ∌ v`, a suitable vertex
   set `S` of `B` has as many crossing edges as `G^v` has at `Y`. So the induced pairing of `Ev`
   satisfies the pairing criterion, and hence `CutOK` for every transversal.
-/

open SimpleGraph Finset

namespace Gallai

universe u

section tjoin

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The number of edges of the edge set `X` at `v`. -/
def edgeDeg (X : Finset (Sym2 V)) (v : V) : ℕ := #(X.filter (fun e => v ∈ e))

omit [Fintype V] in
theorem card_symmDiff_add (A B : Finset V) : #(symmDiff A B) + 2 * #(A ∩ B) = #A + #B := by
  have hU : ∀ C : Finset V, C ⊆ A ∪ B → #C = ∑ x ∈ A ∪ B, (if x ∈ C then 1 else 0) := by
    intro C hC
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hC, Finset.card_eq_sum_ones]
  have h1 : symmDiff A B ⊆ A ∪ B := by
    intro x hx; rw [Finset.mem_symmDiff] at hx; rw [Finset.mem_union]; tauto
  rw [hU _ h1, hU (A ∩ B) Finset.inter_subset_union, hU A Finset.subset_union_left,
    hU B Finset.subset_union_right, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [Finset.mem_symmDiff, ha, hb]

omit [Fintype V] in
theorem odd_card_symmDiff (A B : Finset V) :
    Odd #(symmDiff A B) ↔ ¬(Odd #A ↔ Odd #B) := by
  have h := card_symmDiff_add A B
  constructor
  · intro ho hiff
    rcases Nat.even_or_odd #A with hA | hA
    · have hB : Even #B := by
        rcases Nat.even_or_odd #B with hB | hB
        · exact hB
        · exact absurd (hiff.mpr hB) (Nat.not_odd_iff_even.mpr hA)
      have : Even (#(symmDiff A B) + 2 * #(A ∩ B)) := h ▸ hA.add hB
      have h2 : Even (2 * #(A ∩ B)) := even_two_mul _
      exact (Nat.not_even_iff_odd.mpr ho) ((Nat.even_add.mp this).mpr h2)
    · have hB := hiff.mp hA
      have : Even (#(symmDiff A B) + 2 * #(A ∩ B)) := h ▸ hA.add_odd hB
      have h2 : Even (2 * #(A ∩ B)) := even_two_mul _
      exact (Nat.not_even_iff_odd.mpr ho) ((Nat.even_add.mp this).mpr h2)
  · intro hn
    by_contra hc
    have he : Even #(symmDiff A B) := Nat.not_odd_iff_even.mp hc
    have hsum : Even (#A + #B) := h ▸ he.add (even_two_mul _)
    apply hn
    rcases Nat.even_or_odd #A with hA | hA
    · have hB : Even #B := (Nat.even_add.mp hsum).mp hA
      exact ⟨fun h' => absurd h' (Nat.not_odd_iff_even.mpr hA),
        fun h' => absurd h' (Nat.not_odd_iff_even.mpr hB)⟩
    · have hB : Odd #B := by
        rcases Nat.even_or_odd #B with hB | hB
        · exact absurd ((Nat.even_add.mp hsum).mpr hB) (Nat.not_even_iff_odd.mpr hA)
        · exact hB
      exact ⟨fun _ => hB, fun _ => hA⟩

omit [Fintype V] in
theorem filter_symmDiff' (A B : Finset (Sym2 V)) (p : Sym2 V → Prop) [DecidablePred p] :
    (symmDiff A B).filter p = symmDiff (A.filter p) (B.filter p) := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_symmDiff]
  tauto

omit [Fintype V] in
theorem odd_edgeDeg_symmDiff (A B : Finset (Sym2 V)) (v : V) :
    Odd (edgeDeg (symmDiff A B) v) ↔ ¬(Odd (edgeDeg A v) ↔ Odd (edgeDeg B v)) := by
  unfold edgeDeg
  rw [filter_symmDiff']
  exact odd_card_symmDiff _ _

variable {G : SimpleGraph V}

omit [Fintype V] in
/-- The edges of a path from `a` to `c ≠ a` have odd degree exactly at `a` and `c`. -/
theorem odd_edgeDeg_path {a c : V} (p : G.Walk a c) (hp : p.IsPath) (hac : a ≠ c) (v : V) :
    Odd (edgeDeg p.edges.toFinset v) ↔ v = a ∨ v = c := by
  have hnd : p.edges.Nodup := hp.isTrail.edges_nodup
  have hcount : edgeDeg p.edges.toFinset v = p.edges.countP (fun e => v ∈ e) := by
    unfold edgeDeg
    have hf : p.edges.toFinset.filter (fun e => v ∈ e) =
        (p.edges.filter (fun e => decide (v ∈ e))).toFinset := by
      ext e; simp [List.mem_filter]
    rw [hf, List.toFinset_card_of_nodup (hnd.filter _), List.countP_eq_length_filter]
  rw [hcount, ← Nat.not_even_iff_odd, hp.isTrail.even_countP_edges_iff v]
  constructor
  · intro h
    by_contra hne
    exact h (fun _ => ⟨fun h1 => hne (Or.inl h1), fun h2 => hne (Or.inr h2)⟩)
  · intro h h'
    rcases h with rfl | rfl
    · exact (h' hac).1 rfl
    · exact (h' hac).2 rfl

/-- **`T`-joins.** In a connected graph, every vertex set of even size is the set of odd-degree
vertices of some set of edges. -/
theorem exists_tjoin (hG : G.Connected) :
    ∀ (k : ℕ) (T : Finset V), #T = 2 * k →
      ∃ X : Finset (Sym2 V), (∀ e ∈ X, e ∈ G.edgeSet) ∧ ∀ v, Odd (edgeDeg X v) ↔ v ∈ T := by
  intro k
  induction k with
  | zero =>
    intro T hT
    refine ⟨∅, by simp, fun v => ?_⟩
    have : T = ∅ := Finset.card_eq_zero.mp (by simpa using hT)
    simp [edgeDeg, this]
  | succ k ih =>
    intro T hT
    have hpos : 0 < #T := by omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    have hpos' : 0 < #(T.erase a) := by rw [Finset.card_erase_of_mem ha]; omega
    obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos'
    have hca : c ≠ a := Finset.ne_of_mem_erase hc
    have hcT : c ∈ T := Finset.mem_of_mem_erase hc
    obtain ⟨X', hX'G, hX'⟩ := ih ((T.erase a).erase c)
      (by rw [Finset.card_erase_of_mem hc, Finset.card_erase_of_mem ha]; omega)
    let p := (hG.preconnected a c).some.toPath
    have hp : (p : G.Walk a c).IsPath := p.2
    refine ⟨symmDiff X' (p : G.Walk a c).edges.toFinset, ?_, fun v => ?_⟩
    · intro e he
      rw [Finset.mem_symmDiff] at he
      rcases he with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hX'G e h1
      · exact (p : G.Walk a c).edges_subset_edgeSet (List.mem_toFinset.mp h1)
    · rw [odd_edgeDeg_symmDiff, hX' v, odd_edgeDeg_path _ hp hca.symm v]
      simp only [Finset.mem_erase]
      by_cases hva : v = a
      · subst hva; simp [ha, hca.symm]
      · by_cases hvc : v = c
        · subst hvc; simp [hcT, hva]
        · simp [hva, hvc]

end tjoin

section aux

variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (X : Finset (Sym2 V))

/-- `F^v`: the edges of `G − X` not at `v`, together with `v` joined to its non-neighbours. -/
def freeStar (v : V) : SimpleGraph V where
  Adj w w' := (w ≠ v ∧ w' ≠ v ∧ G.Adj w w' ∧ s(w, w') ∉ X) ∨
    (w = v ∧ w' ≠ v ∧ ¬ G.Adj v w') ∨ (w' = v ∧ w ≠ v ∧ ¬ G.Adj v w)
  symm := ⟨fun w w' h => by
    rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h2, h1, h3.symm, by rwa [Sym2.eq_swap]⟩
    · exact Or.inr (Or.inr ⟨h1, h2, h3⟩)
    · exact Or.inr (Or.inl ⟨h1, h2, h3⟩)⟩
  loopless := ⟨fun w h => by
    rcases h with ⟨_, _, h3, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
    · exact G.loopless.irrefl w h3
    · exact h2 h1
    · exact h2 h1⟩

instance freeStar.decRel (v : V) : DecidableRel (freeStar G X v).Adj := fun w w' =>
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The auxiliary graph `B` on `V × V`: copy `v` carries `F^v`, and each `X`-edge `vx` gives the
edge `(v, x)–(x, v)`. -/
def auxB : SimpleGraph (V × V) where
  Adj p q := (p.1 = q.1 ∧ (freeStar G X p.1).Adj p.2 q.2) ∨
    (p.1 ≠ q.1 ∧ s(p.1, q.1) ∈ X ∧ p.2 = q.1 ∧ q.2 = p.1)
  symm := ⟨fun p q h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
    · refine Or.inl ⟨h1.symm, ?_⟩
      rw [← h1]; exact h2.symm
    · exact Or.inr ⟨h1.symm, by rwa [Sym2.eq_swap], h4, h3⟩⟩
  loopless := ⟨fun p h => by
    rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact (freeStar G X p.1).loopless.irrefl _ h2
    · exact h1 rfl⟩

instance auxB.decRel : DecidableRel (auxB G X).Adj := fun p q =>
  inferInstanceAs (Decidable (_ ∨ _))

omit [Fintype V] in
theorem degree_eq_sum {W : Type*} [Fintype W] (Γ : SimpleGraph W) [DecidableRel Γ.Adj] (x : W) :
    Γ.degree x = ∑ y, (if Γ.Adj x y then 1 else 0) := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter]

/-- The degree of `(v, w)` in `B` is the degree of `w` in `F^v`, plus one for the `X`-edge `vw`. -/
theorem degree_auxB (v w : V) :
    (auxB G X).degree (v, w) = (freeStar G X v).degree w + (if v ≠ w ∧ s(v, w) ∈ X then 1 else 0) := by
  rw [degree_eq_sum, degree_eq_sum, Fintype.sum_prod_type]
  have hsplit : ∀ a b : V, (if (auxB G X).Adj (v, w) (a, b) then 1 else 0 : ℕ) =
      (if a = v ∧ (freeStar G X v).Adj w b then 1 else 0) +
        (if a = w ∧ b = v ∧ v ≠ w ∧ s(v, w) ∈ X then 1 else 0) := by
    intro a b
    show (if (v = a ∧ (freeStar G X v).Adj w b) ∨ (v ≠ a ∧ s(v, a) ∈ X ∧ w = a ∧ b = v)
      then 1 else 0 : ℕ) = _
    by_cases hva : a = v
    · subst hva
      have h2 : ¬ (a = w ∧ b = a ∧ a ≠ w ∧ s(a, w) ∈ X) := fun h' => h'.2.2.1 h'.1
      by_cases h : (freeStar G X a).Adj w b
      · simp [h, h2]
      · simp [h, h2]
    · have hva' : v ≠ a := fun h => hva h.symm
      by_cases haw : a = w
      · subst haw; by_cases hb : b = v <;> by_cases hX : s(v, a) ∈ X <;> simp [hva, hva', hb, hX]
      · have hwa : w ≠ a := fun h => haw h.symm
        simp [hva, hva', haw, hwa]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hsplit a b))]
  simp only [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single v]
    · simp
    · intro a _ hav; simp [hav]
    · simp
  · rw [Finset.sum_eq_single w]
    · rw [Finset.sum_eq_single v]
      · simp
      · intro b _ hbv; simp [hbv]
      · simp
    · intro a _ haw; simp [haw]
    · simp

end aux

section parity

variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (X : Finset (Sym2 V))

omit [Fintype V] in
theorem edgeDeg_eq_card [Fintype V] (w : V) :
    edgeDeg X w = #(univ.filter (fun w' => s(w, w') ∈ X)) := by
  unfold edgeDeg
  have h : X.filter (fun e => w ∈ e) =
      (univ.filter (fun w' => s(w, w') ∈ X)).image (fun w' => s(w, w')) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hX, hw⟩
      obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hw
      exact ⟨y, hX, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, Sym2.mem_mk_left w y⟩
  rw [h, Finset.card_image_of_injective _ (fun a b hab => Sym2.congr_right.mp hab)]

/-- Degrees split into `X`-edges and the rest. -/
theorem degree_split (hXG : ∀ e ∈ X, e ∈ G.edgeSet) (w : V) :
    (∑ w', (if G.Adj w w' ∧ s(w, w') ∉ X then 1 else 0)) + edgeDeg X w = G.degree w := by
  rw [edgeDeg_eq_card, Finset.card_filter, degree_eq_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w' _
  by_cases hX : s(w, w') ∈ X
  · have hadj : G.Adj w w' := (mem_edgeSet G).mp (hXG _ hX)
    simp [hX, hadj]
  · by_cases hadj : G.Adj w w' <;> simp [hX, hadj]

omit [DecidableRel G.Adj] in
theorem sum_ite_eq_and (v : V) (P : Prop) [Decidable P] :
    ∑ w' : V, (if w' = v ∧ P then 1 else 0 : ℕ) = if P then 1 else 0 := by
  by_cases hP : P
  · simp only [hP, and_true]
    rw [Finset.sum_ite_eq']
    simp
  · simp [hP]

/-- The degree of `w ≠ v` in `F^v`. -/
theorem degree_freeStar_ne {v w : V} (hwv : w ≠ v) :
    (freeStar G X v).degree w + (if G.Adj v w ∧ s(v, w) ∉ X then 1 else 0) =
      (∑ w', (if G.Adj w w' ∧ s(w, w') ∉ X then 1 else 0)) + (if ¬ G.Adj v w then 1 else 0) := by
  rw [degree_eq_sum]
  have key : ∀ w', (if (freeStar G X v).Adj w w' then 1 else 0 : ℕ) +
      (if w' = v ∧ G.Adj v w ∧ s(v, w) ∉ X then 1 else 0) =
      (if G.Adj w w' ∧ s(w, w') ∉ X then 1 else 0) + (if w' = v ∧ ¬ G.Adj v w then 1 else 0) := by
    intro w'
    show (if (w ≠ v ∧ w' ≠ v ∧ G.Adj w w' ∧ s(w, w') ∉ X) ∨ (w = v ∧ w' ≠ v ∧ ¬ G.Adj v w') ∨
      (w' = v ∧ w ≠ v ∧ ¬ G.Adj v w) then 1 else 0 : ℕ) + _ = _
    by_cases hw' : w' = v
    · subst hw'
      have hs : s(w, w') = s(w', w) := Sym2.eq_swap
      by_cases hadj : G.Adj w' w
      · have hadj' : G.Adj w w' := hadj.symm
        by_cases hX : s(w', w) ∈ X <;> simp [hwv, hadj, hadj', hX, hs]
      · have hadj' : ¬ G.Adj w w' := fun h => hadj h.symm
        simp [hwv, hadj, hadj']
    · simp [hwv, hw']
  have hsum := Finset.sum_congr rfl (fun w' (_ : w' ∈ (univ : Finset V)) => key w')
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_ite_eq_and, sum_ite_eq_and] at hsum
  exact hsum

/-- The degree of `v` in `F^v`: its non-neighbours. -/
theorem degree_freeStar_self (v : V) :
    (freeStar G X v).degree v + G.degree v + 1 = Fintype.card V := by
  rw [degree_eq_sum, degree_eq_sum, ← Finset.card_univ, Finset.card_eq_sum_ones,
    ← Finset.sum_add_distrib]
  have key : ∀ w', (if (freeStar G X v).Adj v w' then 1 else 0 : ℕ) +
      (if G.Adj v w' then 1 else 0) = 1 - (if w' = v then 1 else 0) := by
    intro w'
    show (if (v ≠ v ∧ w' ≠ v ∧ G.Adj v w' ∧ s(v, w') ∉ X) ∨ (v = v ∧ w' ≠ v ∧ ¬ G.Adj v w') ∨
      (w' = v ∧ v ≠ v ∧ ¬ G.Adj v v) then 1 else 0 : ℕ) + _ = _
    by_cases hw' : w' = v
    · subst hw'; simp
    · by_cases hadj : G.Adj v w' <;> simp [hw', hadj]
  rw [Finset.sum_congr rfl (fun w' _ => key w')]
  have : ∑ w' : V, (1 - (if w' = v then 1 else 0) : ℕ) + 1 = ∑ w' : V, (1 : ℕ) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v), ← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
    simp only [if_true, Nat.sub_self, zero_add]
    rw [Finset.sum_congr rfl (fun w' hw' => by rw [if_neg (Finset.ne_of_mem_erase hw')])]
    simp
    have hc : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
    omega
  exact this

/-- **Parity of `B`.** If `X` is a `T`-join for the even vertices and `|V|` is even, the odd
vertices of `B` are exactly the diagonal `(v, v)` over even `v`. -/
theorem odd_degree_auxB (hXG : ∀ e ∈ X, e ∈ G.edgeSet)
    (hX : ∀ v, Odd (edgeDeg X v) ↔ Even (G.degree v)) (hn : Even (Fintype.card V)) (v w : V) :
    Odd ((auxB G X).degree (v, w)) ↔ (w = v ∧ Even (G.degree v)) := by
  rw [degree_auxB]
  by_cases hwv : w = v
  · subst hwv
    have h := degree_freeStar_self G X w
    simp only [ne_eq, not_true_eq_false, false_and, if_false, add_zero, true_and]
    rw [Nat.odd_iff, Nat.even_iff]
    rw [Nat.even_iff] at hn
    omega
  · have h1 := degree_freeStar_ne G X hwv
    have h2 := degree_split G X hXG w
    have h3 := hX w
    have hvw : v ≠ w := fun h => hwv h.symm
    simp only [hwv, false_and, iff_false]
    rw [Nat.odd_iff, Nat.even_iff] at h3
    rw [Nat.odd_iff]
    by_cases hadj : G.Adj v w
    · by_cases hXe : s(v, w) ∈ X
      · simp only [hadj, hXe, not_true_eq_false, and_false, if_false, add_zero, not_false_eq_true,
          ne_eq, hvw, and_self, if_true] at h1 ⊢
        omega
      · simp only [hadj, hXe, not_false_eq_true, and_self, if_true, not_true_eq_false, if_false,
          add_zero, ne_eq, hvw, and_false] at h1 ⊢
        omega
    · have hXe : s(v, w) ∉ X := fun h => hadj ((mem_edgeSet G).mp (hXG _ h))
      simp only [hadj, false_and, if_false, add_zero, not_false_eq_true, if_true, ne_eq, hvw,
        hXe, and_false] at h1 ⊢
      omega

end parity

section cut

variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (X : Finset (Sym2 V))

/-- `G^v`: the edges of `G` not at `v`, together with `v` joined to its non-neighbours. -/
def starComp (v : V) : SimpleGraph V where
  Adj w w' := (w ≠ v ∧ w' ≠ v ∧ G.Adj w w') ∨ (w = v ∧ w' ≠ v ∧ ¬ G.Adj v w') ∨
    (w' = v ∧ w ≠ v ∧ ¬ G.Adj v w)
  symm := ⟨fun w w' h => by
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h2, h1, h3.symm⟩
    · exact Or.inr (Or.inr ⟨h1, h2, h3⟩)
    · exact Or.inr (Or.inl ⟨h1, h2, h3⟩)⟩
  loopless := ⟨fun w h => by
    rcases h with ⟨_, _, h3⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
    · exact G.loopless.irrefl w h3
    · exact h2 h1
    · exact h2 h1⟩

instance starComp.decRel (v : V) : DecidableRel (starComp G v).Adj := fun w w' =>
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The vertex set of `B` attached to `v` and `Y`: whole copies `u ≠ v` with `u ∈ Y`, and the part
of copy `v` over `Y`. -/
def liftSet (v : V) (Y : Finset V) : Finset (V × V) :=
  univ.filter (fun p => (p.1 ≠ v ∧ p.1 ∈ Y) ∨ (p.1 = v ∧ p.2 ∈ Y))

theorem crossCount_eq_card {W : Type*} [Fintype W] [DecidableEq W] (Γ : SimpleGraph W)
    [DecidableRel Γ.Adj] (S : Finset W) :
    crossCount Γ S = #((S ×ˢ univ).filter (fun pq => Γ.Adj pq.1 pq.2 ∧ pq.2 ∉ S)) := by
  unfold crossCount
  rw [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.card_filter]

/-- An edge of `B` leaving the lifted set either lies in copy `v`, or is an `X`-edge away from `v`. -/
theorem auxB_cross_cases {v : V} {Y : Finset V} {p q : V × V}
    (hp : p ∈ liftSet v Y) (hq : q ∉ liftSet v Y) (h : (auxB G X).Adj p q) :
    (p.1 = v ∧ q.1 = v ∧ p.2 ∈ Y ∧ q.2 ∉ Y ∧ (freeStar G X v).Adj p.2 q.2) ∨
    (p.1 ≠ v ∧ q.1 ≠ v ∧ s(p.1, q.1) ∈ X ∧ p.1 ∈ Y ∧ q.1 ∉ Y ∧ p.2 = q.1 ∧ q.2 = p.1 ∧
      p.1 ≠ q.1) := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  simp only [liftSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
  · simp only at h1 h2
    subst h1
    by_cases hpv : p1 = v
    · subst hpv
      left
      refine ⟨rfl, rfl, ?_, ?_, h2⟩
      · rcases hp with ⟨h, _⟩ | ⟨_, h⟩
        · exact absurd rfl h
        · exact h
      · intro hq2; exact hq (Or.inr ⟨rfl, hq2⟩)
    · exfalso
      rcases hp with ⟨_, h⟩ | ⟨h, _⟩
      · exact hq (Or.inl ⟨hpv, h⟩)
      · exact hpv h
  · simp only at h1 h2 h3 h4
    rw [h3] at hp
    rw [h4] at hq
    right
    by_cases hpv : p1 = v
    · exfalso
      rcases hp with ⟨h, _⟩ | ⟨_, h⟩
      · exact h hpv
      · exact hq (Or.inl ⟨fun h' => h1 (hpv.trans h'.symm), h⟩)
    · by_cases hqv : q1 = v
      · exfalso
        rcases hp with ⟨_, h⟩ | ⟨h, _⟩
        · exact hq (Or.inr ⟨hqv, h⟩)
        · exact hpv h
      · have hpY : p1 ∈ Y := by
          rcases hp with ⟨_, h⟩ | ⟨h, _⟩
          · exact h
          · exact absurd h hpv
        exact ⟨hpv, hqv, h2, hpY, fun h => hq (Or.inl ⟨hqv, h⟩), h3, h4, h1⟩

/-- **Cut comparison.** The edges of `B` leaving the lifted set inject into the edges of `G^v`
leaving `Y`. -/
theorem crossCount_auxB_le (hXG : ∀ e ∈ X, e ∈ G.edgeSet) {v : V} {Y : Finset V} (hv : v ∉ Y) :
    crossCount (auxB G X) (liftSet v Y) ≤ crossCount (starComp G v) Y := by
  rw [crossCount_eq_card, crossCount_eq_card]
  let f : (V × V) × (V × V) → V × V := fun pq =>
    if pq.1.1 = pq.2.1 then (pq.1.2, pq.2.2) else (pq.1.1, pq.2.1)
  apply Finset.card_le_card_of_injOn f
  · intro pq hpq
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_univ, and_true,
      Set.mem_setOf_eq] at hpq ⊢
    obtain ⟨hp, hadj, hq⟩ := hpq
    rcases auxB_cross_cases G X hp hq hadj with ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5, _, _, hne⟩
    · have hf : f pq = (pq.1.2, pq.2.2) := by simp [f, h1, h2]
      rw [hf]
      refine ⟨h3, ?_, h4⟩
      rcases h5 with ⟨a1, a2, a3, _⟩ | ⟨a1, _, _⟩ | ⟨a1, a2, a3⟩
      · exact Or.inl ⟨a1, a2, a3⟩
      · exact absurd (a1 ▸ h3) hv
      · exact Or.inr (Or.inr ⟨a1, a2, a3⟩)
    · have hf : f pq = (pq.1.1, pq.2.1) := by simp [f, hne]
      rw [hf]
      exact ⟨h4, Or.inl ⟨h1, h2, (mem_edgeSet G).mp (hXG _ h3)⟩, h5⟩
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_univ, and_true,
      Set.mem_setOf_eq] at ha hb
    obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := a
    obtain ⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩ := b
    have ca := auxB_cross_cases G X ha.1 ha.2.2 ha.2.1
    have cb := auxB_cross_cases G X hb.1 hb.2.2 hb.2.1
    simp only at ca cb
    rcases ca with ⟨ha1, ha2, _, _, ha5⟩ | ⟨ha1, ha2, ha3, _, _, ha6, ha7, ha8⟩
    · have hfa : f ((a1, a2), (a3, a4)) = (a2, a4) := by simp [f, ha1, ha2]
      rcases cb with ⟨hb1, hb2, _, _, _⟩ | ⟨hb1, hb2, hb3, _, _, _, _, hb8⟩
      · have hfb : f ((b1, b2), (b3, b4)) = (b2, b4) := by simp [f, hb1, hb2]
        rw [hfa, hfb, Prod.mk.injEq] at hab
        rw [ha1, ha2, hb1, hb2, hab.1, hab.2]
      · have hfb : f ((b1, b2), (b3, b4)) = (b1, b3) := by simp [f, hb8]
        rw [hfa, hfb, Prod.mk.injEq] at hab
        exfalso
        rcases ha5 with ⟨_, _, _, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
        · rw [hab.1, hab.2] at h; exact h hb3
        · exact hb1 (by rw [← hab.1]; exact h)
        · exact hb2 (by rw [← hab.2]; exact h)
    · have hfa : f ((a1, a2), (a3, a4)) = (a1, a3) := by simp [f, ha8]
      rcases cb with ⟨hb1, hb2, _, _, hb5⟩ | ⟨hb1, hb2, hb3, _, _, hb6, hb7, hb8⟩
      · have hfb : f ((b1, b2), (b3, b4)) = (b2, b4) := by simp [f, hb1, hb2]
        rw [hfa, hfb, Prod.mk.injEq] at hab
        exfalso
        rcases hb5 with ⟨_, _, _, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
        · rw [← hab.1, ← hab.2] at h; exact h ha3
        · exact ha1 (by rw [hab.1]; exact h)
        · exact ha2 (by rw [hab.2]; exact h)
      · have hfb : f ((b1, b2), (b3, b4)) = (b1, b3) := by simp [f, hb8]
        rw [hfa, hfb, Prod.mk.injEq] at hab
        rw [ha6, ha7, hb6, hb7, hab.1, hab.2]

/-- Membership in the odd set of `B`. -/
theorem mem_oddV_auxB (hXG : ∀ e ∈ X, e ∈ G.edgeSet)
    (hX : ∀ v, Odd (edgeDeg X v) ↔ Even (G.degree v)) (hn : Even (Fintype.card V)) (p : V × V) :
    p ∈ oddV (auxB G X) ↔ p.2 = p.1 ∧ Even (G.degree p.1) := by
  simp only [oddV, Finset.mem_filter, Finset.mem_univ, true_and]
  exact odd_degree_auxB G X hXG hX hn p.1 p.2

/-- **Transfer.** A pairing of the odd vertices of `B` induces a pairing of the even vertices of `G`
whose split counts are bounded by those of `B` at the lifted sets. -/
theorem pairing_transfer (hXG : ∀ e ∈ X, e ∈ G.edgeSet)
    (hX : ∀ v, Odd (edgeDeg X v) ↔ Even (G.degree v)) (hn : Even (Fintype.card V))
    {π : V × V → V × V} (hπ : IsPairing (oddV (auxB G X)) π) :
    IsPairing (univ.filter (fun a => Even (G.degree a))) (fun a => (π (a, a)).1) ∧
      ∀ v Y, v ∉ Y → splitCount (univ.filter (fun a => Even (G.degree a))) (fun a => (π (a, a)).1) Y ≤
        splitCount (oddV (auxB G X)) π (liftSet v Y) := by
  have hmem := mem_oddV_auxB G X hXG hX hn
  have hdiag : ∀ a, Even (G.degree a) → π (a, a) = ((π (a, a)).1, (π (a, a)).1) ∧
      Even (G.degree (π (a, a)).1) ∧ (π (a, a)).1 ≠ a ∧ π ((π (a, a)).1, (π (a, a)).1) = (a, a) := by
    intro a ha
    have h0 : (a, a) ∈ oddV (auxB G X) := (hmem _).mpr ⟨rfl, ha⟩
    obtain ⟨h1, h2, h3⟩ := hπ _ h0
    obtain ⟨h4, h5⟩ := (hmem _).mp h1
    have heq : π (a, a) = ((π (a, a)).1, (π (a, a)).1) := Prod.ext rfl h4
    refine ⟨heq, h5, fun h => h2 ?_, ?_⟩
    · rw [heq, h]
    · rw [← heq, h3]
  refine ⟨?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    obtain ⟨_, h5, hne, hback⟩ := hdiag a ha
    exact ⟨h5, hne, by rw [hback]⟩
  · intro v Y hv
    unfold splitCount
    apply Finset.card_le_card_of_injOn (fun a => (a, a))
    · intro a ha
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
      obtain ⟨ha1, ha2, ha3⟩ := ha
      have ha1 : Even (G.degree a) := by simpa using ha1
      obtain ⟨heq, _, _, _⟩ := hdiag a ha1
      have hav : a ≠ v := fun h => hv (h ▸ ha2)
      refine ⟨(hmem _).mpr ⟨rfl, ha1⟩, ?_, ?_⟩
      · simp only [liftSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inl ⟨hav, ha2⟩
      · rw [heq]
        simp only [liftSet, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_and]
        exact ⟨fun _ => ha3, fun _ => ha3⟩
    · intro a _ b _ hab
      exact (Prod.mk.injEq _ _ _ _ ▸ hab).1

end cut

section algebra

variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Ordered adjacent pairs from `A` to `B`. -/
def adjCount (A B : Finset V) : ℕ := ∑ u, ∑ y, (if u ∈ A ∧ y ∈ B ∧ G.Adj u y then 1 else 0)

theorem adjCount_comm (A B : Finset V) : adjCount G A B = adjCount G B A := by
  unfold adjCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro u _
  apply Finset.sum_congr rfl; intro y _
  by_cases h1 : y ∈ A <;> by_cases h2 : u ∈ B <;> by_cases h3 : G.Adj u y <;>
    simp [h1, h2, h3, G.adj_comm y u]

theorem sum_card_filter (W : Finset V) (Q : V → V → Prop) [∀ u y, Decidable (Q u y)] :
    ∑ u ∈ W, #(univ.filter (fun y => Q u y)) =
      ∑ u, ∑ y, (if u ∈ W ∧ Q u y then 1 else 0 : ℕ) := by
  rw [← Finset.sum_subset (Finset.subset_univ W) (fun u _ hu => ?_)]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.card_filter]
    simp [hu]
  · simp [hu]

theorem adjCount_singleton (v : V) (B : Finset V) :
    adjCount G {v} B = ∑ y, (if y ∈ B ∧ G.Adj v y then 1 else 0) := by
  unfold adjCount
  rw [Finset.sum_eq_single v]
  · simp
  · intro u _ hu; simp [hu]
  · simp

theorem card_filter_eq_sum (Y : Finset V) (p : V → Prop) [DecidablePred p] :
    #(Y.filter p) = ∑ y, (if y ∈ Y ∧ p y then 1 else 0) := by
  rw [Finset.card_filter, ← Finset.univ_inter Y, ← Finset.sum_ite_mem]
  apply Finset.sum_congr rfl; intro y _
  by_cases hy : y ∈ Y <;> by_cases hp : p y <;> simp [hy, hp]

/-- The basic identity: `|δ(W)| + |Y| = |δ_{G^v}(Y)| + d(v)` for the partition `W, {v}, Y`. -/
theorem key_identity (v : V) (W : Finset V) (hv : v ∉ W) :
    cutCount G W + #(univ \ insert v W) =
      crossCount (starComp G v) (univ \ insert v W) + G.degree v := by
  set Y := univ \ insert v W with hY
  have hmemY : ∀ y, y ∈ Y ↔ y ≠ v ∧ y ∉ W := by
    intro y; simp [hY]
  -- cutCount G W = E(W, Y) + E(W, {v})
  have h1 : cutCount G W = adjCount G W Y + adjCount G W {v} := by
    unfold cutCount adjCount
    rw [sum_card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro u _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro y _
    by_cases hyv : y = v
    · subst hyv; by_cases hu : u ∈ W <;> by_cases ha : G.Adj u y <;> simp [hu, ha, hv, hmemY]
    · by_cases hu : u ∈ W <;> by_cases hyW : y ∈ W <;> by_cases ha : G.Adj u y <;>
        simp [hu, hyW, ha, hyv, hmemY]
  -- crossCount G^v Y = E(Y, W) + #(Y non-neighbours of v)
  have h2 : crossCount (starComp G v) Y =
      adjCount G Y W + #(Y.filter (fun u => ¬ G.Adj v u)) := by
    unfold crossCount adjCount
    rw [sum_card_filter, card_filter_eq_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro u _
    by_cases hu : u ∈ Y
    · have huv : u ≠ v := ((hmemY u).mp hu).1
      have key : ∀ y, (if u ∈ Y ∧ ((starComp G v).Adj u y ∧ y ∉ Y) then 1 else 0 : ℕ) =
          (if u ∈ Y ∧ y ∈ W ∧ G.Adj u y then 1 else 0) +
            (if y = v ∧ ¬ G.Adj v u then 1 else 0) := by
        intro y
        show (if u ∈ Y ∧ (((u ≠ v ∧ y ≠ v ∧ G.Adj u y) ∨ (u = v ∧ y ≠ v ∧ ¬ G.Adj v y) ∨
          (y = v ∧ u ≠ v ∧ ¬ G.Adj v u)) ∧ y ∉ Y) then 1 else 0 : ℕ) = _
        by_cases hyv : y = v
        · subst hyv
          have : y ∉ Y := fun h => ((hmemY y).mp h).1 rfl
          by_cases ha : G.Adj y u
          · have ha' : G.Adj u y := ha.symm
            simp [hu, huv, ha, ha', this, hv]
          · have ha' : ¬ G.Adj u y := fun h => ha h.symm
            simp [hu, huv, ha, ha', this, hv]
        · by_cases hyW : y ∈ W
          · have : y ∉ Y := fun h => ((hmemY y).mp h).2 hyW
            simp [hu, huv, hyv, hyW, this]
          · have : y ∈ Y := (hmemY y).mpr ⟨hyv, hyW⟩
            simp [hu, huv, hyv, hyW, this]
      rw [Finset.sum_congr rfl (fun y _ => key y), Finset.sum_add_distrib, sum_ite_eq_and]
      simp [hu]
    · simp [hu]
  -- degree and |Y| split at v
  have h3 : G.degree v = adjCount G {v} W + adjCount G {v} Y := by
    rw [degree_eq_sum, adjCount_singleton, adjCount_singleton, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro y _
    by_cases ha : G.Adj v y
    · have hyv : y ≠ v := fun h => G.loopless.irrefl v (h ▸ ha)
      by_cases hyW : y ∈ W
      · have : y ∉ Y := fun h => ((hmemY y).mp h).2 hyW
        simp [ha, hyW, this]
      · have : y ∈ Y := (hmemY y).mpr ⟨hyv, hyW⟩
        simp [ha, hyW, this]
    · simp [ha]
  have h4 : #Y = adjCount G {v} Y + #(Y.filter (fun u => ¬ G.Adj v u)) := by
    rw [adjCount_singleton, card_filter_eq_sum, ← Finset.filter_true_of_mem (s := Y) (p := fun _ => True)
      (fun _ _ => trivial), card_filter_eq_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro y _
    by_cases hy : y ∈ Y <;> by_cases ha : G.Adj v y <;> simp [hy, ha]
  have c1 := adjCount_comm G W Y
  have c2 := adjCount_comm G W {v}
  omega

end algebra

section assembly

variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The even vertices (degree parity only). -/
def evenV : Finset V := univ.filter (fun a => Even (G.degree a))

/-- **From good pairings to the cut conditions.** If a pairing `P` of the even vertices satisfies
the criterion `σ_P(Y) ≤ |δ_{G^v}(Y)|` for all `v ∉ Y`, then every transversal satisfies `CutOK`. -/
theorem cutOK_of_pairing (hn : Even (Fintype.card V)) (hpos : ∀ v, 0 < G.degree v)
    {P : V → V} (hP : IsPairing (evenV G) P)
    (hcut : ∀ v Y, v ∉ Y → splitCount (evenV G) P Y ≤ crossCount (starComp G v) Y)
    {M : Finset V} (hM : M ⊆ evenV G) (htr : ∀ a ∈ evenV G, (a ∈ M ↔ P a ∉ M)) :
    CutOK G (profile G M) (Fintype.card V / 2) := by
  have hev : ∀ a, a ∈ evenV G ↔ Even (G.degree a) := by intro a; simp [evenV]
  have hprof : ∀ u, profile G M u = (if Odd (G.degree u) then 1 else 0) + 2 * (if u ∈ M then 1 else 0) := by
    intro u
    unfold profile
    by_cases ho : Odd (G.degree u)
    · have : u ∉ M := fun h => (Nat.not_even_iff_odd.mpr ho) ((hev u).mp (hM h))
      simp [ho, this]
    · by_cases hu : u ∈ M <;> simp [ho, hu]
  -- sums of the profile over a set
  have hsumY : ∀ Y : Finset V, ∑ u ∈ Y, profile G M u =
      #(Y.filter (fun u => Odd (G.degree u))) + 2 * #(Y.filter (fun u => u ∈ M)) := by
    intro Y
    rw [Finset.sum_congr rfl (fun u _ => hprof u), Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.card_filter, Finset.card_filter]
  have hcardY : ∀ Y : Finset V, #Y = #(Y.filter (fun u => Odd (G.degree u))) +
      #(Y.filter (fun u => u ∈ M)) + #(Y.filter (fun u => Even (G.degree u) ∧ u ∉ M)) := by
    intro Y
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_eq_sum_ones,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro u _
    by_cases ho : Odd (G.degree u)
    · have hne : ¬ Even (G.degree u) := Nat.not_even_iff_odd.mpr ho
      have : u ∉ M := fun h => hne ((hev u).mp (hM h))
      simp [ho, hne, this]
    · have he : Even (G.degree u) := Nat.not_odd_iff_even.mp ho
      by_cases hu : u ∈ M <;> simp [ho, he, hu]
  -- the unmarked even vertices of Y are bounded by its marks and the split pairs
  have hI4 : ∀ Y : Finset V, #(Y.filter (fun u => Even (G.degree u) ∧ u ∉ M)) ≤
      #(Y.filter (fun u => u ∈ M)) + splitCount (evenV G) P Y := by
    intro Y
    set N := Y.filter (fun u => Even (G.degree u) ∧ u ∉ M)
    rw [← Finset.card_filter_add_card_filter_not (s := N) (p := fun a => P a ∈ Y)]
    apply Nat.add_le_add
    · apply Finset.card_le_card_of_injOn P
      · intro a ha
        simp only [N, Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq] at ha ⊢
        obtain ⟨⟨_, haE, haM⟩, hPa⟩ := ha
        exact ⟨hPa, by
          by_contra h
          exact haM ((htr a ((hev a).mpr haE)).mpr h)⟩
      · intro a ha b hb hab
        simp only [N, Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq] at ha hb
        have h1 := (hP a ((hev a).mpr ha.1.2.1)).2.2
        have h2 := (hP b ((hev b).mpr hb.1.2.1)).2.2
        rw [← h1, ← h2, hab]
    · unfold splitCount
      apply Finset.card_le_card
      intro a ha
      simp only [N, Finset.mem_filter] at ha ⊢
      exact ⟨(hev a).mpr ha.1.2.1, ha.1.1, ha.2⟩
  -- the profile sums to n
  have hMcard : #M = #((evenV G).filter (fun u => u ∉ M)) := by
    apply le_antisymm
    · apply Finset.card_le_card_of_injOn P
      · intro a ha
        have haE := hM ha
        simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq]
        exact ⟨(hP a haE).1, (htr a haE).mp ha⟩
      · intro a ha b hb hab
        rw [← (hP a (hM ha)).2.2, ← (hP b (hM hb)).2.2, hab]
    · apply Finset.card_le_card_of_injOn P
      · intro a ha
        simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq] at ha
        by_contra h
        exact ha.2 ((htr a ha.1).mpr h)
      · intro a ha b hb hab
        simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq] at ha hb
        rw [← (hP a ha.1).2.2, ← (hP b hb.1).2.2, hab]
  have htotal : ∑ u, profile G M u = Fintype.card V := by
    rw [hsumY univ, ← Finset.card_univ, hcardY univ]
    have : #((univ : Finset V).filter (fun u => u ∈ M)) = #M := by
      congr 1; ext u; simp
    have h2 : #((univ : Finset V).filter (fun u => Even (G.degree u) ∧ u ∉ M)) =
        #((evenV G).filter (fun u => u ∉ M)) := by
      congr 1; ext u; simp [evenV]
    omega
  have hn2 : 2 * (Fintype.card V / 2) = Fintype.card V := Nat.two_mul_div_two_of_even hn
  refine ⟨fun v => ?_, fun v W hvW => ?_⟩
  · -- local conditions
    have hlt := G.degree_lt_card_verts v
    rw [hn2, hprof]
    by_cases ho : Odd (G.degree v)
    · have : v ∉ M := fun h => (Nat.not_even_iff_odd.mpr ho) ((hev v).mp (hM h))
      simp only [ho, this, if_true, if_false]
      have : 1 ≤ G.degree v := ho.pos
      omega
    · have he : Even (G.degree v) := Nat.not_odd_iff_even.mp ho
      by_cases hu : v ∈ M
      · simp only [ho, hu, if_true, if_false]
        have hp := hpos v
        rw [Nat.even_iff] at he hn
        omega
      · simp only [ho, hu, if_false]; omega
  · -- the cut condition at v and W
    set Y := univ \ insert v W with hY
    have hkey := key_identity G v W hvW
    rw [← hY] at hkey
    have hsplit := hcut v Y (by simp [hY])
    have h3 := hsumY Y
    have h4 := hcardY Y
    have h5 := hI4 Y
    -- the profile over W, v and Y sums to n
    have hpart : ∑ u ∈ W, profile G M u + profile G M v + ∑ u ∈ Y, profile G M u =
        Fintype.card V := by
      rw [← htotal, ← Finset.sum_add_sum_compl W]
      have hc : Wᶜ = insert v Y := by
        ext u; simp [hY]; by_cases h : u = v <;> simp [h, hvW]
      rw [hc, Finset.sum_insert (by simp [hY])]
      ring
    rw [hn2]
    omega

/-- In a connected graph with at least two vertices, every vertex has a neighbour. -/
theorem cs_degree_pos (hG : G.Connected) (hn : 2 ≤ Fintype.card V) (v : V) :
    0 < G.degree v := by
  obtain ⟨w, hw⟩ : ∃ w, w ≠ v := by
    by_contra h
    push_neg at h
    have : Fintype.card V ≤ 1 := Fintype.card_le_one_iff.mpr (fun a b => (h a).trans (h b).symm)
    omega
  obtain ⟨p⟩ := hG.preconnected v w
  cases p with
  | nil => exact absurd rfl hw
  | cons h _ =>
    rw [← card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨_, (mem_neighborFinset _ _ _).mpr h⟩

/-- **Cut selection (endpoint-min-max, Theorem 21).** Every connected graph of even order has a
pairing `P` of its even vertices such that every half-set containing exactly one vertex of each
pair satisfies the cut conditions of even-degrees §12.4 for `n/2` paths. -/
theorem cs_all (hG : G.Connected) (hn : Even (Fintype.card V)) :
    ∃ P : V → V, IsPairing (evenSet G) P ∧
      ∀ M : Finset V, M ⊆ evenSet G → (∀ a ∈ evenSet G, (a ∈ M ↔ P a ∉ M)) →
        CutOK G (profile G M) (Fintype.card V / 2) := by
  have hcard : 2 ≤ Fintype.card V := by
    have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hG.nonempty
    rw [Nat.even_iff] at hn
    omega
  have hpos := cs_degree_pos G hG hcard
  have hEv : evenSet G = evenV G := by
    ext a; simp [evenSet, evenV, hpos a]
  rw [hEv]
  -- a T-join for the even vertices
  have hcardE : Even #(evenV G) := by
    have hodd := G.even_card_odd_degree_vertices
    have hsplit : #(evenV G) + #(univ.filter (fun a => Odd (G.degree a))) = Fintype.card V := by
      rw [evenV, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
        ← Finset.card_univ, Finset.card_eq_sum_ones]
      apply Finset.sum_congr rfl; intro a _
      rcases Nat.even_or_odd (G.degree a) with h | h
      · simp [h, Nat.not_odd_iff_even.mpr h]
      · simp [h, Nat.not_even_iff_odd.mpr h]
    rw [Nat.even_iff] at hn hodd ⊢
    have : #(univ.filter (fun a => Odd (G.degree a))) = #{v | Odd (G.degree v)} := rfl
    omega
  obtain ⟨k, hk⟩ := hcardE
  obtain ⟨X, hXG, hX⟩ := exists_tjoin hG k (evenV G) (by omega)
  have hX' : ∀ v, Odd (edgeDeg X v) ↔ Even (G.degree v) := by
    intro v; rw [hX v]; simp [evenV]
  -- the pairing lemma on B, and the transfer
  obtain ⟨π, hπ, hπcut⟩ := pairing_lemma (auxB G X)
  obtain ⟨hP, hPsplit⟩ := pairing_transfer G X hXG hX' hn hπ
  refine ⟨_, hP, fun M hM htr => cutOK_of_pairing G hn hpos hP (fun v Y hv => ?_) hM htr⟩
  exact (hPsplit v Y hv).trans ((hπcut _).trans (crossCount_auxB_le G X hXG hv))

end assembly

end Gallai
