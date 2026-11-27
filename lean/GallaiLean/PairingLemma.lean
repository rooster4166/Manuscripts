import GallaiLean.Lovasz

/-!
# The pairing lemma in cut form

Manuscript: `manuscripts/endpoint-min-max`, the second proof of Theorem 21 (cut selection).

**`pairing_lemma`**: in every finite simple graph `Γ`, the odd-degree vertices can be paired by an
involution `π` such that, for every vertex set `S`, the number of pairs split by `S` is at most the
number of edges of `Γ` leaving `S`.

The proof deletes an edge `xy` and re-pairs: drop the pair `{x, y}`, replace `{x, a}, {y, b}` by
`{a, b}`, replace `{x, a}` by `{y, a}`, or add `{x, y}`. The bound survives by the triangle
inequality of the separation indicator `sep S`. No paths, components or handshake lemma are
needed.
-/

open SimpleGraph Finset

namespace Gallai

universe u

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- `π` pairs the elements of `O`: it maps `O` to itself without fixed points, and it is an
involution there. -/
def IsPairing (O : Finset W) (π : W → W) : Prop :=
  ∀ z ∈ O, π z ∈ O ∧ π z ≠ z ∧ π (π z) = z

/-- The number of pairs of `π` split by `S`, each counted at its element in `S`. -/
def splitCount (O : Finset W) (π : W → W) (S : Finset W) : ℕ :=
  (O.filter (fun z => z ∈ S ∧ π z ∉ S)).card

/-- The number of edges of `Γ` leaving `S`, counted at their ends in `S`. -/
def crossCount (Γ : SimpleGraph W) [DecidableRel Γ.Adj] (S : Finset W) : ℕ :=
  ∑ u ∈ S, (univ.filter (fun y => Γ.Adj u y ∧ y ∉ S)).card

/-- The odd-degree vertices of `Γ`. -/
def oddV (Γ : SimpleGraph W) [DecidableRel Γ.Adj] : Finset W :=
  univ.filter (fun v => Odd (Γ.degree v))

/-- `1` if `S` separates `a` and `b`, else `0`. -/
def sep (S : Finset W) (a b : W) : ℕ := if (a ∈ S ↔ b ∈ S) then 0 else 1

theorem sep_comm (S : Finset W) (a b : W) : sep S a b = sep S b a := by
  unfold sep
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb]

theorem sep_triangle (S : Finset W) (a b c : W) : sep S a c ≤ sep S a b + sep S b c := by
  unfold sep
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> by_cases hc : c ∈ S <;> simp [ha, hb, hc]

theorem splitCount_eq_sum (O : Finset W) (π : W → W) (S : Finset W) :
    splitCount O π S = ∑ z ∈ O, (if z ∈ S ∧ π z ∉ S then 1 else 0) :=
  Finset.card_filter _ _

theorem sep_eq (S : Finset W) (a b : W) :
    sep S a b = (if a ∈ S ∧ b ∉ S then 1 else 0) + (if b ∈ S ∧ a ∉ S then 1 else 0) := by
  unfold sep
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb]

/-- Removing a pair `{a, π a}`. -/
theorem IsPairing.erase_pair {O : Finset W} {π : W → W} (hπ : IsPairing O π) {a : W} (ha : a ∈ O) :
    IsPairing ((O.erase a).erase (π a)) π ∧
      ∀ S, splitCount ((O.erase a).erase (π a)) π S + sep S a (π a) = splitCount O π S := by
  obtain ⟨hpa, hpa_ne, hppa⟩ := hπ a ha
  refine ⟨?_, ?_⟩
  · intro z hz
    simp only [Finset.mem_erase] at hz
    obtain ⟨hzpa, hza, hzO⟩ := hz
    obtain ⟨h1, h2, h3⟩ := hπ z hzO
    refine ⟨?_, h2, h3⟩
    simp only [Finset.mem_erase]
    refine ⟨?_, ?_, h1⟩
    · intro h
      apply hza
      rw [← h3, h, hppa]
    · intro h
      apply hzpa
      rw [← h3, h]
  · intro S
    have hpa_mem : π a ∈ O.erase a := Finset.mem_erase.mpr ⟨hpa_ne, hpa⟩
    rw [splitCount_eq_sum, splitCount_eq_sum, ← Finset.add_sum_erase O _ ha,
      ← Finset.add_sum_erase (O.erase a) _ hpa_mem, hppa, sep_eq]
    omega

/-- Adding a pair `{a, b}` of new elements. -/
theorem IsPairing.insert_pair {O : Finset W} {π : W → W} (hπ : IsPairing O π) {a b : W}
    (ha : a ∉ O) (hb : b ∉ O) (hab : a ≠ b) :
    IsPairing (insert a (insert b O)) (Function.update (Function.update π a b) b a) ∧
      ∀ S, splitCount (insert a (insert b O)) (Function.update (Function.update π a b) b a) S =
        splitCount O π S + sep S a b := by
  set π' := Function.update (Function.update π a b) b a with hπ'
  have hπ'a : π' a = b := by simp [hπ', hab]
  have hπ'b : π' b = a := by simp [hπ']
  have hπ'z : ∀ z, z ≠ a → z ≠ b → π' z = π z := by
    intro z hza hzb
    simp [hπ', hza, hzb]
  have hO : ∀ z ∈ O, z ≠ a ∧ z ≠ b := fun z hz =>
    ⟨fun h => ha (h ▸ hz), fun h => hb (h ▸ hz)⟩
  refine ⟨?_, ?_⟩
  · intro z hz
    simp only [Finset.mem_insert] at hz
    rcases hz with rfl | rfl | hz
    · refine ⟨by simp [hπ'a], by rw [hπ'a]; exact hab.symm, by rw [hπ'a, hπ'b]⟩
    · refine ⟨by simp [hπ'b], by rw [hπ'b]; exact hab, by rw [hπ'b, hπ'a]⟩
    · obtain ⟨hza, hzb⟩ := hO z hz
      obtain ⟨h1, h2, h3⟩ := hπ z hz
      obtain ⟨h1a, h1b⟩ := hO _ h1
      rw [hπ'z z hza hzb]
      refine ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h1), h2, ?_⟩
      rw [hπ'z _ h1a h1b, h3]
  · intro S
    have hbO : b ∉ O := hb
    have haO : a ∉ insert b O := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨hab, ha⟩
    rw [splitCount_eq_sum, splitCount_eq_sum, Finset.sum_insert haO, Finset.sum_insert hbO,
      hπ'a, hπ'b, sep_eq]
    have hsum : ∑ z ∈ O, (if z ∈ S ∧ π' z ∉ S then 1 else 0) =
        ∑ z ∈ O, (if z ∈ S ∧ π z ∉ S then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro z hz
      obtain ⟨hza, hzb⟩ := hO z hz
      rw [hπ'z z hza hzb]
    rw [hsum]
    omega

section delete

variable (Γ : SimpleGraph W) [DecidableRel Γ.Adj]

/-- Deleting the edge `xy` removes exactly the crossing `sep S x y`. -/
theorem crossCount_delEdge {x y : W} (hxy : Γ.Adj x y) (S : Finset W) :
    crossCount Γ S = crossCount (delEdge Γ x y) S + sep S x y := by
  have hne : x ≠ y := hxy.ne
  have key : ∀ u w, (if Γ.Adj u w ∧ w ∉ S then 1 else 0) =
      (if (delEdge Γ x y).Adj u w ∧ w ∉ S then 1 else 0) +
        ((if u = x ∧ w = y ∧ w ∉ S then 1 else 0) + (if u = y ∧ w = x ∧ w ∉ S then 1 else 0)) := by
    intro u w
    have hiff : (delEdge Γ x y).Adj u w ↔
        Γ.Adj u w ∧ ¬ ((u = x ∧ w = y) ∨ (u = y ∧ w = x)) := by
      show Γ.Adj u w ∧ ¬ s(u, w) = s(x, y) ↔ _
      rw [Sym2.eq_iff]
    by_cases h1 : (u = x ∧ w = y) ∨ (u = y ∧ w = x)
    · have hadj : Γ.Adj u w := by
        rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hxy
        · exact hxy.symm
      have h3 : ¬ (delEdge Γ x y).Adj u w := fun h => (hiff.mp h).2 h1
      rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · by_cases hw : w ∈ S <;> simp [hadj, h3, hw, hne, hne.symm]
      · by_cases hw : w ∈ S <;> simp [hadj, h3, hw, hne, hne.symm]
    · have h1' : ¬ (u = x ∧ w = y) ∧ ¬ (u = y ∧ w = x) := not_or.mp h1
      by_cases hadj : Γ.Adj u w
      · have h3 := hiff.mpr ⟨hadj, h1⟩
        by_cases hw : w ∈ S <;> simp [hadj, h3, hw] <;> tauto
      · have h3 : ¬ (delEdge Γ x y).Adj u w := fun h => hadj (hiff.mp h).1
        simp only [hadj, h3, false_and, if_false, zero_add]
        by_cases hux : u = x
        · subst hux
          have : w ≠ y := fun h => h1'.1 ⟨rfl, h⟩
          by_cases hw : w = u <;> simp [this, hne]
        · by_cases huy : u = y
          · subst huy
            have : w ≠ x := fun h => h1'.2 ⟨rfl, h⟩
            simp [this, hux]
          · simp [hux, huy]
  unfold crossCount
  simp only [Finset.card_filter]
  rw [Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun w _ => key u w))]
  simp only [Finset.sum_add_distrib]
  congr 1
  have inner : ∀ u, (∑ w, (if u = x ∧ w = y ∧ w ∉ S then 1 else 0) +
      ∑ w, (if u = y ∧ w = x ∧ w ∉ S then 1 else 0) : ℕ) =
      (if u = x ∧ y ∉ S then 1 else 0) + (if u = y ∧ x ∉ S then 1 else 0) := by
    intro u
    have e1 : ∀ (a b : W), (∑ w, (if u = a ∧ w = b ∧ w ∉ S then 1 else 0) : ℕ) =
        if u = a ∧ b ∉ S then 1 else 0 := by
      intro a b
      by_cases hua : u = a
      · have : ∀ w, (if u = a ∧ w = b ∧ w ∉ S then 1 else 0 : ℕ) =
            if w = b then (if b ∉ S then 1 else 0) else 0 := by
          intro w
          by_cases h : w = b
          · subst h; simp [hua]
          · simp [hua, h]
        rw [Finset.sum_congr rfl (fun w _ => this w), Finset.sum_ite_eq']
        simp [hua]
      · simp [hua]
    rw [e1 x y, e1 y x]
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun u _ => inner u), Finset.sum_add_distrib, sep_eq]
  congr 1
  · rw [← Finset.sum_filter]
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;>
      simp [hx, hy, Finset.filter_and, Finset.filter_eq']
  · rw [← Finset.sum_filter]
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;>
      simp [hx, hy, Finset.filter_and, Finset.filter_eq']

omit [Fintype W] [DecidableEq W] in
theorem not_even_iff_odd_self (n : ℕ) : ¬(Even n ↔ Odd n) := by
  intro h
  rcases Nat.even_or_odd n with he | ho
  · exact (Nat.not_even_iff_odd.mpr (h.mp he)) he
  · exact (Nat.not_even_iff_odd.mpr ho) (h.mpr ho)

/-- Parity bookkeeping for deleting the edge `xy`. -/
theorem mem_oddV_delEdge {x y : W} (hxy : Γ.Adj x y) (z : W) :
    (z ∈ oddV Γ ↔ z ∈ oddV (delEdge Γ x y)) ↔ z ≠ x ∧ z ≠ y := by
  have hne : x ≠ y := hxy.ne
  have h := delEdge_degree Γ hxy z
  simp only [oddV, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hzx : z = x
  · subst hzx
    simp only [hne, if_true, if_false, add_zero] at h
    rw [← h, Nat.odd_add_one]
    simpa using not_even_iff_odd_self _
  · by_cases hzy : z = y
    · subst hzy
      simp only [hzx, if_true, if_false, add_zero] at h
      rw [← h, Nat.odd_add_one]
      simpa [hzx] using not_even_iff_odd_self _
    · simp only [hzx, hzy, if_false, add_zero] at h
      rw [← h]
      simp [hzx, hzy]

end delete

/-- Strong form, by induction on the degree sum. -/
theorem pairing_lemma_aux : ∀ (n : ℕ) (Γ : SimpleGraph W) [DecidableRel Γ.Adj],
    ∑ w, Γ.degree w = n →
      ∃ π, IsPairing (oddV Γ) π ∧ ∀ S, splitCount (oddV Γ) π S ≤ crossCount Γ S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Γ _ hn
  by_cases hE : ∃ x y, Γ.Adj x y
  · obtain ⟨x, y, hxy⟩ := hE
    have hne : x ≠ y := hxy.ne
    have hsum := delEdge_sum_degree Γ hxy
    obtain ⟨π', hπ', hb'⟩ := ih (∑ w, (delEdge Γ x y).degree w) (by omega) (delEdge Γ x y) rfl
    have hcross := crossCount_delEdge Γ hxy
    have hodd := mem_oddV_delEdge Γ hxy
    set O' := oddV (delEdge Γ x y) with hO'
    have hxO : x ∈ oddV Γ ↔ x ∉ O' := by
      have := hodd x; simp only [ne_eq, not_true_eq_false, false_and, iff_false] at this; tauto
    have hyO : y ∈ oddV Γ ↔ y ∉ O' := by
      have := hodd y; simp only [ne_eq, not_true_eq_false, and_false, iff_false] at this; tauto
    have hzO : ∀ z, z ≠ x → z ≠ y → (z ∈ oddV Γ ↔ z ∈ O') := fun z h1 h2 => (hodd z).mpr ⟨h1, h2⟩
    by_cases hx : x ∈ O'
    · obtain ⟨hpa, hpa_ne, hppa⟩ := hπ' x hx
      by_cases hy : y ∈ O'
      · by_cases hpx : π' x = y
        · -- drop the pair {x, y}
          obtain ⟨hp1, hc1⟩ := hπ'.erase_pair hx
          rw [hpx] at hp1 hc1
          have hO : oddV Γ = (O'.erase x).erase y := by
            ext z
            simp only [Finset.mem_erase]
            by_cases hzx : z = x
            · subst hzx; simp [hxO, hx]
            · by_cases hzy : z = y
              · subst hzy; simp [hyO, hy]
              · simp [hzO z hzx hzy, hzx, hzy]
          refine ⟨π', hO ▸ hp1, fun S => ?_⟩
          rw [hO]
          have := hc1 S; have := hb' S; have := hcross S
          omega
        · -- replace {x, a}, {y, b} by {a, b}
          set a := π' x with ha
          obtain ⟨hpb, hpb_ne, hppb⟩ := hπ' y hy
          set b := π' y with hb
          have hay : a ≠ y := hpx
          have hbx : b ≠ x := fun h => hpx (by rw [ha, ← h, hppb])
          have hab : a ≠ b := fun h => hne (by rw [← hppa, ← hppb]; exact congrArg π' h)
          obtain ⟨hp1, hc1⟩ := hπ'.erase_pair hx
          rw [← ha] at hp1 hc1
          have hy1 : y ∈ (O'.erase x).erase a := by
            simp only [Finset.mem_erase]; exact ⟨hay.symm, hne.symm, hy⟩
          obtain ⟨hp2, hc2⟩ := hp1.erase_pair hy1
          rw [← hb] at hp2 hc2
          have ha2 : a ∉ (((O'.erase x).erase a).erase y).erase b := by simp
          have hb2 : b ∉ (((O'.erase x).erase a).erase y).erase b := by simp
          obtain ⟨hp3, hc3⟩ := hp2.insert_pair ha2 hb2 hab
          have hO : oddV Γ = insert a (insert b ((((O'.erase x).erase a).erase y).erase b)) := by
            ext z
            simp only [Finset.mem_insert, Finset.mem_erase]
            by_cases hzx : z = x
            · subst hzx; simp [hxO, hx, hpa_ne.symm, hbx.symm]
            · by_cases hzy : z = y
              · subst hzy; simp [hyO, hy, hay.symm, hpb_ne.symm]
              · rw [hzO z hzx hzy]
                by_cases hza : z = a
                · subst hza; simp [hpa]
                · by_cases hzb : z = b
                  · subst hzb; simp [hpb]
                  · simp [hza, hzb, hzx, hzy]
          refine ⟨_, hO ▸ hp3, fun S => ?_⟩
          rw [hO, hc3 S]
          have h1 := hc1 S; have h2 := hc2 S; have h3 := hb' S; have h4 := hcross S
          have t1 := sep_triangle S a x b
          have t2 := sep_triangle S x y b
          have c1 := sep_comm S a x
          omega
      · -- replace {x, a} by {y, a}
        set a := π' x with ha
        have hay : a ≠ y := fun h => hy (h ▸ hpa)
        obtain ⟨hp1, hc1⟩ := hπ'.erase_pair hx
        rw [← ha] at hp1 hc1
        have hy1 : y ∉ (O'.erase x).erase a := by simp [hy]
        have ha1 : a ∉ (O'.erase x).erase a := by simp
        obtain ⟨hp2, hc2⟩ := hp1.insert_pair hy1 ha1 hay.symm
        have hO : oddV Γ = insert y (insert a ((O'.erase x).erase a)) := by
          ext z
          simp only [Finset.mem_insert, Finset.mem_erase]
          by_cases hzx : z = x
          · subst hzx; simp [hxO, hx, hpa_ne.symm, hne]
          · by_cases hzy : z = y
            · subst hzy; simp [hyO, hy]
            · rw [hzO z hzx hzy]
              by_cases hza : z = a
              · subst hza; simp [hpa]
              · simp [hza, hzx, hzy]
        refine ⟨_, hO ▸ hp2, fun S => ?_⟩
        rw [hO, hc2 S]
        have h1 := hc1 S; have h3 := hb' S; have h4 := hcross S
        have t1 := sep_triangle S y x a
        have c1 := sep_comm S y x
        omega
    · by_cases hy : y ∈ O'
      · -- replace {y, b} by {x, b}
        obtain ⟨hpb, hpb_ne, hppb⟩ := hπ' y hy
        set b := π' y with hb
        have hbx : b ≠ x := fun h => hx (h ▸ hpb)
        obtain ⟨hp1, hc1⟩ := hπ'.erase_pair hy
        rw [← hb] at hp1 hc1
        have hx1 : x ∉ (O'.erase y).erase b := by simp [hx]
        have hb1 : b ∉ (O'.erase y).erase b := by simp
        obtain ⟨hp2, hc2⟩ := hp1.insert_pair hx1 hb1 hbx.symm
        have hO : oddV Γ = insert x (insert b ((O'.erase y).erase b)) := by
          ext z
          simp only [Finset.mem_insert, Finset.mem_erase]
          by_cases hzy : z = y
          · subst hzy; simp [hyO, hy, hpb_ne.symm, hne.symm]
          · by_cases hzx : z = x
            · subst hzx; simp [hxO, hx]
            · rw [hzO z hzx hzy]
              by_cases hzb : z = b
              · subst hzb; simp [hpb]
              · simp [hzb, hzx, hzy]
        refine ⟨_, hO ▸ hp2, fun S => ?_⟩
        rw [hO, hc2 S]
        have h1 := hc1 S; have h3 := hb' S; have h4 := hcross S
        have t1 := sep_triangle S x y b
        omega
      · -- add {x, y}
        obtain ⟨hp1, hc1⟩ := hπ'.insert_pair hx hy hne
        have hO : oddV Γ = insert x (insert y O') := by
          ext z
          simp only [Finset.mem_insert]
          by_cases hzx : z = x
          · subst hzx; simp [hxO, hx]
          · by_cases hzy : z = y
            · subst hzy; simp [hyO, hy]
            · simp [hzO z hzx hzy, hzx, hzy]
        refine ⟨_, hO ▸ hp1, fun S => ?_⟩
        rw [hO, hc1 S]
        have h3 := hb' S; have h4 := hcross S
        omega
  · have hdeg0 : ∀ z, Γ.degree z = 0 := by
      intro z
      rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro w hw
      exact hE ⟨z, w, (mem_neighborFinset _ _ _).mp hw⟩
    have hO : oddV Γ = ∅ := by
      ext z
      simp [oddV, hdeg0]
    refine ⟨id, ?_, ?_⟩
    · rw [hO]; intro z hz; simp at hz
    · intro S; rw [hO]; simp [splitCount]

/-- **The pairing lemma, cut form.** The odd vertices of every finite graph `Γ` can be paired so
that every vertex set `S` separates at most as many pairs as `Γ` has edges leaving `S`. -/
theorem pairing_lemma (Γ : SimpleGraph W) [DecidableRel Γ.Adj] :
    ∃ π, IsPairing (oddV Γ) π ∧ ∀ S, splitCount (oddV Γ) π S ≤ crossCount Γ S :=
  pairing_lemma_aux _ Γ rfl

end Gallai
