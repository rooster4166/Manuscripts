import GallaiLean.PairingLemma
import GallaiLean.EmmTemplate

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

end Gallai
