import GallaiLean.HubPhases

/-!
# Hub closures at every deletion degree (d6-frontier manuscript, Theorems 4.1, 5.2, 6.1)

**Setting.** `G` has even order, `U` is the set of even-degree vertices (`hU`), `d = |U|`. A
vertex `r` *passes* (`PassesAt G r`) if some path decomposition has at most `|V|/2` paths and at
least two ends at `r`. All results are proved in the stronger form "some `S ⊆ U` with `r ∈ S`
and `2|S| = |U|` is realisable": a decomposition with one end at every odd vertex, two on `S`,
and none on `U \ S` (`Realisable`). `passesAt_of_realisable` turns this into `PassesAt`.

**Batteries.** A battery at a hub `h` is a triangle `h a b` of odd vertices; `a` is the parked
vertex. Batteries are given as a list `L` of pairs `(a, b)`, in the order in which they are
carried. "`a_i b_j ∉ E` for `i < j`" is `L.Pairwise (fun p q => ¬ G.Adj p.1 q.2)`, and "all
vertices distinct" is a `Nodup` hypothesis on `L.map Prod.fst ++ L.map Prod.snd`.

**The run** (`hub_run`). From the seed, the hub
1. carries every battery (`hub_batteries`; `Ach.carry` along `h b a`), gaining `|L|` ends;
2. receives `m` times from `T` (`hub_receive`; the spent donors `Z` are not under our control);
3. gives one end to every vertex of `Q ∪ (T \ Z)` (`hub_give`; blank neighbours only in `Z`);
4. pays back the pendant `B₀` and the parked vertices (`hub_payback`; they are quiet).

**Theorems.**
* `root_hub_uniform` (Thm 6.1(a)): root hub at every deletion degree `d`.
* `full_hub_uniform`, `full_hub_pendant_uniform` (Thm 6.1(b)): full hub at every `d`.
* `full_hub_six`, `full_hub_six_pendant` (Thm 5.2): the case `d = 6`.
* `root_hub_six` (Thm 4.1(i)): `d = 6`, a pendant with up to two neighbours in `T`, using a
  controlled first receipt.
* `root_hub_six_Q1`, `root_hub_six_Q2` (Thm 4.1(ii), (iii)): `d = 6`, one or two core
  non-neighbours of `r` (assumed non-isolated) and a triangle `r a b` with a small-contact `a`.
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u} [DecidableEq V]

omit [DecidableEq V] in
theorem batChords_cons (p : V × V) (L : List (V × V)) :
    batChords (p :: L) = insert s(p.2, p.1) (batChords L) := by
  ext e; simp [batChords]

omit [DecidableEq V] in
theorem batChords_nil : batChords ([] : List (V × V)) = ∅ := by
  ext e; simp [batChords]

theorem hubSpokes_erase_iff {h x : V} {X : Finset V} (hx : x ∈ X) (e : Sym2 V) :
    e ∈ hubSpokes h X ↔ e ∈ hubSpokes h (X.erase x) ∨ e = s(h, x) := by
  simp only [hubSpokes, Set.mem_ofPred_eq, Finset.mem_erase]
  constructor
  · rintro ⟨z, hz, rfl⟩
    by_cases hzx : z = x
    · exact Or.inr (hzx ▸ rfl)
    · exact Or.inl ⟨z, ⟨hzx, hz⟩, rfl⟩
  · rintro (⟨z, ⟨-, hz⟩, rfl⟩ | rfl)
    · exact ⟨z, hz, rfl⟩
    · exact ⟨x, hx, rfl⟩

theorem mv_hst_take {h t : V} {N : ℕ} {B D : Finset V} (hth : t ≠ h) (htB : t ∉ B)
    (htD : t ∉ D) : mv (hst h N B D) t h = hst h (N + 1) (insert t B) D := by
  funext v
  unfold mv hst
  by_cases hvh : v = h
  · subst hvh; simp
  · by_cases hvt : v = t
    · subst hvt; simp [hvh, htB, htD]
    · simp [hvh, hvt]

section run

variable [Fintype V] {G : SimpleGraph V} {h : V} {D : Finset V}

/-- **Batteries**: carry every battery `(a, b)` of `L` in order (`b → h`, then `a → b`). The hub
gains `|L|` ends and the parked vertices become blank. -/
theorem hub_batteries : ∀ (L : List (V × V)) (X : Finset V) (N : ℕ) (B : Finset V),
    Ach (G.edgeSet \ hubHeld h X (batChords L)) (hst h N B D) →
    (h :: (L.map Prod.fst ++ L.map Prod.snd)).Nodup →
    (∀ p ∈ L, p.1 ∈ X ∧ p.2 ∈ X) →
    (∀ p ∈ L, G.Adj h p.2 ∧ G.Adj p.2 p.1) →
    (∀ p ∈ L, p.1 ∉ B ∧ p.1 ∉ D ∧ p.2 ∉ B ∧ p.2 ∉ D) →
    (∀ w ∈ B, G.Adj h w → w ∈ X) →
    (∀ p ∈ L, ∀ w ∈ B, ¬ G.Adj p.2 w) →
    L.Pairwise (fun p q => ¬ G.Adj q.2 p.1) →
    Ach (G.edgeSet \ hubHeld h (X \ (L.map Prod.snd).toFinset) ∅)
      (hst h (N + L.length) (B ∪ (L.map Prod.fst).toFinset) D)
  | [], X, N, B, hA, _, _, _, _, _, _, _ => by
    refine hA.congr (by rw [batChords_nil]; simp) (fun v => ?_)
    simp
  | p :: L, X, N, B, hA, hnd, hX, hadj, hBD, hhB, hcB, hpw => by
    -- distinctness
    have hh : h ∉ (p.1 :: L.map Prod.fst) ++ (p.2 :: L.map Prod.snd) := (List.nodup_cons.mp hnd).1
    have hnd2 := List.nodup_append.mp (List.nodup_cons.mp hnd).2
    have hA1 : (p.1 :: L.map Prod.fst).Nodup := hnd2.1
    have hA2 : (p.2 :: L.map Prod.snd).Nodup := hnd2.2.1
    have hdisj : ∀ a ∈ p.1 :: L.map Prod.fst, ∀ b ∈ p.2 :: L.map Prod.snd, a ≠ b := hnd2.2.2
    have hp1h : p.1 ≠ h := fun h' => hh (h' ▸ List.mem_append_left _ List.mem_cons_self)
    have hp2h : p.2 ≠ h := fun h' => hh (h' ▸ List.mem_append_right _ List.mem_cons_self)
    have hp12 : p.1 ≠ p.2 := hdisj p.1 List.mem_cons_self p.2 List.mem_cons_self
    have hp1L : p.1 ∉ L.map Prod.fst := (List.nodup_cons.mp hA1).1
    have hp2L : p.2 ∉ L.map Prod.snd := (List.nodup_cons.mp hA2).1
    have hp2L' : p.2 ∉ L.map Prod.fst := fun hm =>
      hdisj p.2 (List.mem_cons_of_mem _ hm) p.2 List.mem_cons_self rfl
    have hp1L' : p.1 ∉ L.map Prod.snd := fun hm =>
      hdisj p.1 List.mem_cons_self p.1 (List.mem_cons_of_mem _ hm) rfl
    have hhq : ∀ q ∈ L, h ≠ q.1 ∧ h ≠ q.2 := fun q hq =>
      ⟨fun h' => hh (h' ▸ List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hq))),
        fun h' => hh (h' ▸ List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hq)))⟩
    have hndL : (h :: (L.map Prod.fst ++ L.map Prod.snd)).Nodup := by
      rw [List.nodup_cons, List.nodup_append]
      refine ⟨fun hm => hh ?_, (List.nodup_cons.mp hA1).2, (List.nodup_cons.mp hA2).2,
        fun a ha b hb => hdisj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)⟩
      rw [List.mem_append] at hm ⊢
      rcases hm with hm | hm
      · exact Or.inl (List.mem_cons_of_mem _ hm)
      · exact Or.inr (List.mem_cons_of_mem _ hm)
    have hpX := hX p List.mem_cons_self
    have hpadj := hadj p List.mem_cons_self
    have hpBD := hBD p List.mem_cons_self
    -- the carry along `h, b, a`
    have h1 := Ach.carry [p.2, p.1] h (G.edgeSet \ hubHeld h X (batChords (p :: L)))
      (hst h N B D) hA (by simp)
      (by simp [Ne.symm hp2h, Ne.symm hp1h, Ne.symm hp12])
      (by
        intro e he hmem
        have he' : e = s(h, p.2) ∨ e = s(p.2, p.1) := by simpa using he
        rcases he' with rfl | rfl
        · exact spoke_notMem_hubE' hpX.2 hmem
        · exact hmem.2 (Or.inr (by rw [batChords_cons]; exact Set.mem_insert _ _)))
      (by
        intro c hc
        have hc' : c = p.2 ∨ c = p.1 := by simpa using hc
        rcases hc' with rfl | rfl
        · rw [hst_one hp2h hpBD.2.2.1 hpBD.2.2.2]
        · rw [hst_one hp1h hpBD.1 hpBD.2.1])
      (by
        intro c hc w hw hwc hwh hw0
        rw [hst_eq_zero_iff hwh] at hw0
        have hc' : c = h ∨ c = p.2 := by simpa using hc
        rcases hc' with hc' | hc'
        · rw [hc', mem_hubE] at hw
          exact hw.2.1 (Or.inl ⟨rfl, hhB w hw0 hw.1⟩)
        · rw [hc', mem_hubE] at hw
          exact hcB p List.mem_cons_self w hw0 hw.1)
    rw [show lastOf h [p.2, p.1] = p.1 from rfl, mv_hst_take hp1h hpBD.1 hpBD.2.1] at h1
    -- the new edge set
    have g1 : s(h, p.2) ∈ G.edgeSet ∧ s(h, p.2) ∉ hubSpokes h (X.erase p.2) ∧
        s(h, p.2) ∉ batChords L := by
      refine ⟨hpadj.1, ?_, ?_⟩
      · rw [mem_hubSpokes]
        rintro (⟨-, hm⟩ | ⟨h', -⟩)
        · exact (Finset.notMem_erase _ _) hm
        · exact hp2h h'
      · rintro ⟨q, hq, hqe⟩
        rcases Sym2.eq_iff.mp hqe with ⟨h', -⟩ | ⟨h', -⟩
        · exact (hhq q hq).2 h'
        · exact (hhq q hq).1 h'
    have g2 : s(p.2, p.1) ∈ G.edgeSet ∧ s(p.2, p.1) ∉ hubSpokes h (X.erase p.2) ∧
        s(p.2, p.1) ∉ batChords L := by
      refine ⟨hpadj.2, ?_, ?_⟩
      · rw [mem_hubSpokes]
        rintro (⟨h', -⟩ | ⟨h', -⟩)
        · exact hp2h h'
        · exact hp1h h'
      · rintro ⟨q, hq, hqe⟩
        rcases Sym2.eq_iff.mp hqe with ⟨h', -⟩ | ⟨h', -⟩
        · exact hp2L (h' ▸ List.mem_map_of_mem hq)
        · exact hp2L' (h' ▸ List.mem_map_of_mem hq)
    have hE' : (G.edgeSet \ hubHeld h X (batChords (p :: L))) ∪ {e | e ∈ lEdges h [p.2, p.1]} =
        G.edgeSet \ hubHeld h (X.erase p.2) (batChords L) := by
      ext e
      have hF : e ∈ {e : Sym2 V | e ∈ lEdges h [p.2, p.1]} ↔ e = s(h, p.2) ∨ e = s(p.2, p.1) := by
        simp
      rw [Set.mem_union, hF, Set.mem_sdiff, Set.mem_sdiff, hubHeld, hubHeld, Set.mem_union,
        Set.mem_union, batChords_cons, Set.mem_insert_iff, hubSpokes_erase_iff hpX.2 e]
      have k1 : e = s(h, p.2) → e ∈ G.edgeSet ∧ e ∉ hubSpokes h (X.erase p.2) ∧
          e ∉ batChords L := fun he => he ▸ g1
      have k2 : e = s(p.2, p.1) → e ∈ G.edgeSet ∧ e ∉ hubSpokes h (X.erase p.2) ∧
          e ∉ batChords L := fun he => he ▸ g2
      constructor
      · rintro (⟨he, hn⟩ | he | he)
        · exact ⟨he, fun h' => hn (h'.elim (fun h'' => Or.inl (Or.inl h''))
            (fun h'' => Or.inr (Or.inr h'')))⟩
        · obtain ⟨a1, a2, a3⟩ := k1 he; exact ⟨a1, fun h' => h'.elim a2 a3⟩
        · obtain ⟨a1, a2, a3⟩ := k2 he; exact ⟨a1, fun h' => h'.elim a2 a3⟩
      · rintro ⟨he, hn⟩
        by_cases e1 : e = s(h, p.2)
        · exact Or.inr (Or.inl e1)
        · by_cases e2 : e = s(p.2, p.1)
          · exact Or.inr (Or.inr e2)
          · refine Or.inl ⟨he, ?_⟩
            rintro ((h' | h') | (h' | h'))
            · exact hn (Or.inl h')
            · exact e1 h'
            · exact e2 h'
            · exact hn (Or.inr h')
    have h2 := hub_batteries L (X.erase p.2) (N + 1) (insert p.1 B) (h1.congr hE' (fun _ => rfl))
      hndL
      (fun q hq => ⟨Finset.mem_erase.mpr ⟨fun h' => hp2L' (h' ▸ List.mem_map_of_mem hq),
          (hX q (List.mem_cons_of_mem _ hq)).1⟩,
        Finset.mem_erase.mpr ⟨fun h' => hp2L (h' ▸ List.mem_map_of_mem hq),
          (hX q (List.mem_cons_of_mem _ hq)).2⟩⟩)
      (fun q hq => hadj q (List.mem_cons_of_mem _ hq))
      (by
        intro q hq
        have hq' := hBD q (List.mem_cons_of_mem _ hq)
        refine ⟨?_, hq'.2.1, ?_, hq'.2.2.2⟩
        · rw [Finset.mem_insert, not_or]
          exact ⟨fun h' => hp1L (h' ▸ List.mem_map_of_mem hq), hq'.1⟩
        · rw [Finset.mem_insert, not_or]
          exact ⟨fun h' => hp1L' (h' ▸ List.mem_map_of_mem hq), hq'.2.2.1⟩)
      (by
        intro w hw hhw
        rw [Finset.mem_insert] at hw
        rw [Finset.mem_erase]
        rcases hw with rfl | hw
        · exact ⟨hp12, hpX.1⟩
        · exact ⟨fun h' => hpBD.2.2.1 (h' ▸ hw), hhB w hw hhw⟩)
      (by
        intro q hq w hw
        rw [Finset.mem_insert] at hw
        rcases hw with rfl | hw
        · exact (List.pairwise_cons.mp hpw).1 q hq
        · exact hcB q (List.mem_cons_of_mem _ hq) w hw)
      (List.pairwise_cons.mp hpw).2
    have e1 : X.erase p.2 \ (L.map Prod.snd).toFinset = X \ ((p :: L).map Prod.snd).toFinset := by
      ext v
      simp only [Finset.mem_sdiff, Finset.mem_erase, List.mem_toFinset, List.map_cons,
        List.mem_cons]
      tauto
    have e2 : N + 1 + L.length = N + (p :: L).length := by
      rw [List.length_cons]; omega
    have e3 : insert p.1 B ∪ (L.map Prod.fst).toFinset = B ∪ ((p :: L).map Prod.fst).toFinset := by
      ext v
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.map_cons,
        List.mem_cons]
      tauto
    rw [e1, e2, e3] at h2
    exact h2

/-- **The hub run.** From a seed with `N₀` ends at the hub and blank set `B₀` (held: all spokes
to `T ∪ Q ∪ B₀` and to the battery vertices, and the battery chords), the hub carries the
batteries, receives `m` times from `T`, gives to `Q ∪ (T \ Z)`, and pays back `B₀` and the parked
vertices. The final state has all edges present, `Z` blank and `Q ∪ (T \ Z)` doubled. -/
theorem hub_run (T Q B₀ : Finset V) (L : List (V × V)) (N₀ m : ℕ)
    (hseed : Ach (G.edgeSet \ hubHeld h (T ∪ Q ∪ B₀ ∪ (L.map Prod.fst).toFinset ∪
      (L.map Prod.snd).toFinset) (batChords L)) (hst h N₀ B₀ ∅))
    (hnd : (h :: (L.map Prod.fst ++ L.map Prod.snd)).Nodup)
    (hTQ : Disjoint T Q) (hTB : Disjoint T B₀) (hQB : Disjoint Q B₀)
    (hLT : ∀ p ∈ L, p.1 ∉ T ∪ Q ∪ B₀ ∧ p.2 ∉ T ∪ Q ∪ B₀)
    (hhT : ∀ t ∈ T ∪ Q ∪ B₀, G.Adj h t)
    (hbat : ∀ p ∈ L, G.Adj h p.1 ∧ G.Adj h p.2 ∧ G.Adj p.2 p.1)
    (hcB : ∀ p ∈ L, ∀ w ∈ B₀, ¬ G.Adj p.2 w)
    (hpw : L.Pairwise (fun p q => ¬ G.Adj q.2 p.1))
    (hquiet : ∀ w ∈ B₀ ∪ (L.map Prod.fst).toFinset, ∀ t ∈ T ∪ Q, ¬ G.Adj w t)
    (hrecv : 2 * m ≤ T.card + 1)
    (hgive : Q.card + T.card ≤ N₀ + L.length + m)
    (hpay : B₀.card + L.length + Q.card + T.card ≤ N₀ + L.length + 2 * m) :
    ∃ Z ⊆ T, Z.card = m ∧
      Ach G.edgeSet (hst h (N₀ + 2 * m - Q.card - T.card - B₀.card) Z (Q ∪ (T \ Z))) := by
  set Af := (L.map Prod.fst).toFinset with hAf
  set Cf := (L.map Prod.snd).toFinset with hCf
  set X₀ := T ∪ Q ∪ B₀ ∪ Af ∪ Cf with hX₀
  have hnd2 := List.nodup_append.mp (List.nodup_cons.mp hnd).2
  have hhL : h ∉ L.map Prod.fst ++ L.map Prod.snd := (List.nodup_cons.mp hnd).1
  have mAf : ∀ {v}, v ∈ Af ↔ ∃ p ∈ L, p.1 = v := by
    intro v; rw [hAf, List.mem_toFinset, List.mem_map]
  have mCf : ∀ {v}, v ∈ Cf ↔ ∃ p ∈ L, p.2 = v := by
    intro v; rw [hCf, List.mem_toFinset, List.mem_map]
  have hAC : ∀ v ∈ Af, v ∉ Cf := by
    intro v hv hv'
    obtain ⟨p, hp, rfl⟩ := mAf.mp hv
    obtain ⟨q, hq, hq'⟩ := mCf.mp hv'
    exact hnd2.2.2 p.1 (List.mem_map_of_mem hp) q.2 (List.mem_map_of_mem hq) hq'.symm
  have hAT : ∀ v ∈ Af, v ∉ T ∪ Q ∪ B₀ := by
    intro v hv; obtain ⟨p, hp, rfl⟩ := mAf.mp hv; exact (hLT p hp).1
  have hCT : ∀ v ∈ Cf, v ∉ T ∪ Q ∪ B₀ := by
    intro v hv; obtain ⟨p, hp, rfl⟩ := mCf.mp hv; exact (hLT p hp).2
  have hcardA : Af.card = L.length := by
    rw [hAf, List.toFinset_card_of_nodup hnd2.1, List.length_map]
  have mem3 : ∀ {v}, v ∈ T ∪ Q ∪ B₀ ↔ v ∈ T ∨ v ∈ Q ∨ v ∈ B₀ := by
    intro v; simp only [Finset.mem_union, or_assoc]
  -- 1. batteries
  have h1 := hub_batteries (D := ∅) L X₀ N₀ B₀ hseed hnd
    (fun p hp => ⟨by rw [hX₀]; simp only [Finset.mem_union]; exact Or.inl (Or.inr
        (mAf.mpr ⟨p, hp, rfl⟩)),
      by rw [hX₀]; simp only [Finset.mem_union]; exact Or.inr (mCf.mpr ⟨p, hp, rfl⟩)⟩)
    (fun p hp => ⟨(hbat p hp).2.1, (hbat p hp).2.2⟩)
    (fun p hp => ⟨fun h' => (hLT p hp).1 (mem3.mpr (Or.inr (Or.inr h'))), Finset.notMem_empty _,
      fun h' => (hLT p hp).2 (mem3.mpr (Or.inr (Or.inr h'))), Finset.notMem_empty _⟩)
    (fun w hw _ => by rw [hX₀]; simp only [Finset.mem_union]; tauto)
    hcB hpw
  rw [← hCf, ← hAf, Nat.add_comm N₀] at h1
  set X₁ := X₀ \ Cf with hX₁
  have mX₁ : ∀ {v}, v ∈ T ∪ Q ∪ B₀ ∨ v ∈ Af → v ∈ X₁ := by
    intro v hv
    rw [hX₁, Finset.mem_sdiff, hX₀]
    rcases hv with hv | hv
    · exact ⟨by simp only [Finset.mem_union] at hv ⊢; tauto, fun h' => hCT v h' hv⟩
    · exact ⟨by simp only [Finset.mem_union]; tauto, hAC v hv⟩
  -- 2. receipts
  obtain ⟨Z, hZT, hZc, h2⟩ := hub_receive h1 T
    (fun t ht => mX₁ (Or.inl (mem3.mpr (Or.inl ht))))
    (fun t ht => hhT t (mem3.mpr (Or.inl ht))) (fun _ _ => Set.notMem_empty _)
    (by
      rw [Finset.disjoint_union_right]
      exact ⟨hTB, Finset.disjoint_left.mpr fun t ht ht' => hAT t ht' (mem3.mpr (Or.inl ht))⟩)
    (Finset.disjoint_empty_right _) m
    (by
      have h0 : blankNbrs (G.edgeSet \ hubHeld h X₁ ∅) (hst h (L.length + N₀) (B₀ ∪ Af) ∅) h ≤
          (∅ : Finset V).card := by
        apply blankNbrs_hub_le
        intro w hhw hw hwh hw0
        rw [hst_eq_zero_iff hwh, Finset.mem_union] at hw0
        exfalso
        apply hw
        refine Or.inl (mem_hubSpokes.mpr (Or.inl ⟨rfl, mX₁ ?_⟩))
        rcases hw0 with hw0 | hw0
        · exact Or.inl (mem3.mpr (Or.inr (Or.inr hw0)))
        · exact Or.inr hw0
      intro j hj
      rw [Finset.card_empty] at h0
      omega)
  -- 3. donations to `Q ∪ (T \ Z)`
  set R := Q ∪ (T \ Z) with hR
  have mR : ∀ {v}, v ∈ R ↔ v ∈ Q ∨ (v ∈ T ∧ v ∉ Z) := by
    intro v; rw [hR, Finset.mem_union, Finset.mem_sdiff]
  have hRcard : R.card = Q.card + T.card - m := by
    rw [hR, Finset.card_union_of_disjoint
      (Finset.disjoint_left.mpr fun v hv hv' =>
        Finset.disjoint_left.mp hTQ (Finset.mem_sdiff.mp hv').1 hv),
      Finset.card_sdiff_of_subset hZT, hZc]
    have := Finset.card_le_card hZT
    omega
  have h3 := hub_give h2 R
    (by
      intro v hv
      rw [Finset.mem_sdiff]
      rcases mR.mp hv with hv | ⟨hv, hvZ⟩
      · exact ⟨mX₁ (Or.inl (mem3.mpr (Or.inr (Or.inl hv)))),
          fun h' => Finset.disjoint_left.mp hTQ (hZT h') hv⟩
      · exact ⟨mX₁ (Or.inl (mem3.mpr (Or.inl hv))), hvZ⟩)
    (fun v hv => by
      rcases mR.mp hv with hv | ⟨hv, -⟩
      · exact hhT v (mem3.mpr (Or.inr (Or.inl hv)))
      · exact hhT v (mem3.mpr (Or.inl hv)))
    (fun _ _ => Set.notMem_empty _)
    (by
      rw [Finset.disjoint_left]
      intro v hv hv'
      simp only [Finset.mem_union] at hv'
      rcases mR.mp hv with hvQ | ⟨hvT, hvZ⟩
      · rcases hv' with (hv' | hv') | hv'
        · exact Finset.disjoint_left.mp hQB hvQ hv'
        · exact hAT v hv' (mem3.mpr (Or.inr (Or.inl hvQ)))
        · exact Finset.disjoint_left.mp hTQ (hZT hv') hvQ
      · rcases hv' with (hv' | hv') | hv'
        · exact Finset.disjoint_left.mp hTB hvT hv'
        · exact hAT v hv' (mem3.mpr (Or.inl hvT))
        · exact hvZ hv')
    (Finset.disjoint_empty_right _) m
    (by
      intro a ha
      refine le_of_le_of_eq (blankNbrs_hub_le Z ?_) hZc
      intro w haw hw hwa hw0
      have hwh : w ≠ h := by
        rintro rfl
        apply hw
        refine Or.inl (mem_hubSpokes.mpr (Or.inr ⟨rfl, ?_⟩))
        rw [Finset.mem_sdiff]
        rcases mR.mp ha with ha' | ⟨ha', haZ⟩
        · exact ⟨mX₁ (Or.inl (mem3.mpr (Or.inr (Or.inl ha')))),
            fun h' => Finset.disjoint_left.mp hTQ (hZT h') ha'⟩
        · exact ⟨mX₁ (Or.inl (mem3.mpr (Or.inl ha'))), haZ⟩
      rw [hst_eq_zero_iff hwh] at hw0
      simp only [Finset.mem_union] at hw0
      have haTQ : a ∈ T ∪ Q := by
        rw [Finset.mem_union]
        rcases mR.mp ha with ha' | ⟨ha', -⟩
        · exact Or.inr ha'
        · exact Or.inl ha'
      rcases hw0 with (hw0 | hw0) | hw0
      · exact absurd haw.symm (hquiet w (Finset.mem_union_left _ hw0) a haTQ)
      · exact absurd haw.symm (hquiet w (Finset.mem_union_right _ hw0) a haTQ)
      · exact hw0)
    (by rw [hRcard]; omega)
  -- 4. paybacks to `B₀ ∪ Af`
  set P := B₀ ∪ Af with hP
  have hPcard : P.card = B₀.card + L.length := by
    rw [hP, Finset.card_union_of_disjoint (Finset.disjoint_left.mpr fun v hv hv' =>
      hAT v hv' (mem3.mpr (Or.inr (Or.inr hv)))), hcardA]
  have mPX : ∀ v ∈ P, v ∈ (X₁ \ Z) \ R := by
    intro v hv
    rw [hP, Finset.mem_union] at hv
    have hvT : v ∉ T ∪ Q := by
      intro h'
      rcases hv with hv | hv
      · rcases Finset.mem_union.mp h' with h' | h'
        · exact Finset.disjoint_left.mp hTB h' hv
        · exact Finset.disjoint_left.mp hQB h' hv
      · exact hAT v hv (Finset.mem_union_left _ h')
    rw [Finset.mem_sdiff, Finset.mem_sdiff]
    refine ⟨⟨mX₁ ?_, fun h' => hvT (Finset.mem_union_left _ (hZT h'))⟩, fun h' => hvT ?_⟩
    · rcases hv with hv | hv
      · exact Or.inl (mem3.mpr (Or.inr (Or.inr hv)))
      · exact Or.inr hv
    · rcases mR.mp h' with h' | ⟨h', -⟩
      · exact Finset.mem_union_right _ h'
      · exact Finset.mem_union_left _ h'
  have h4 := hub_payback h3 P mPX
    (by
      intro v hv
      rw [hP, Finset.mem_union] at hv
      rcases hv with hv | hv
      · exact hhT v (mem3.mpr (Or.inr (Or.inr hv)))
      · obtain ⟨p, hp, rfl⟩ := mAf.mp hv
        exact (hbat p hp).1)
    (fun _ _ => Set.notMem_empty _)
    Finset.subset_union_left
    (by
      rw [Finset.empty_union, Finset.disjoint_left]
      intro v hv hvR
      exact (Finset.mem_sdiff.mp (mPX v hv)).2 hvR)
    (by
      intro a ha w hw haw
      rw [Finset.mem_union] at hw
      rcases hw with hw | hw
      · exact hw
      · exact absurd haw (hquiet a ha w (Finset.mem_union_left _ (hZT hw))))
    (by rw [hPcard, hRcard]; omega)
  -- the end state
  have hXe : ((X₁ \ Z) \ R) \ P = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro v hv
    simp only [Finset.mem_sdiff] at hv
    obtain ⟨⟨⟨hv1, hvZ⟩, hvR⟩, hvP⟩ := hv
    apply hvP
    rw [hX₁, Finset.mem_sdiff, hX₀] at hv1
    simp only [Finset.mem_union] at hv1
    rw [hP, Finset.mem_union]
    rcases hv1 with ⟨(((hv | hv) | hv) | hv) | hv, hvC⟩
    · exact absurd (mR.mpr (Or.inr ⟨hv, hvZ⟩)) hvR
    · exact absurd (mR.mpr (Or.inl hv)) hvR
    · exact Or.inl hv
    · exact Or.inr hv
    · exact absurd hv hvC
  have hBe : (P ∪ Z) \ P = Z := by
    ext v
    rw [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hv | hv, hn⟩
      · exact absurd hv hn
      · exact hv
    · intro hv
      refine ⟨Or.inr hv, ?_⟩
      rw [hP, Finset.mem_union]
      rintro (h' | h')
      · exact Finset.disjoint_left.mp hTB (hZT hv) h'
      · exact hAT v h' (mem3.mpr (Or.inl (hZT hv)))
  rw [hXe, hubHeld_empty, Set.sdiff_empty, hBe, Finset.empty_union, hRcard, hPcard] at h4
  refine ⟨Z, hZT, hZc, h4.congr rfl (fun v => ?_)⟩
  congr 1
  omega

omit [Fintype V] in
/-- The number of held spokes in a hub run. -/
theorem card_hubX (T Q B₀ : Finset V) (L : List (V × V))
    (hnd : (L.map Prod.fst ++ L.map Prod.snd).Nodup)
    (hTQ : Disjoint T Q) (hTB : Disjoint T B₀) (hQB : Disjoint Q B₀)
    (hLT : ∀ p ∈ L, p.1 ∉ T ∪ Q ∪ B₀ ∧ p.2 ∉ T ∪ Q ∪ B₀) :
    (T ∪ Q ∪ B₀ ∪ (L.map Prod.fst).toFinset ∪ (L.map Prod.snd).toFinset).card =
      T.card + Q.card + B₀.card + 2 * L.length := by
  have hnd2 := List.nodup_append.mp hnd
  have h1 : (L.map Prod.fst).toFinset.card = L.length := by
    rw [List.toFinset_card_of_nodup hnd2.1, List.length_map]
  have h2 : (L.map Prod.snd).toFinset.card = L.length := by
    rw [List.toFinset_card_of_nodup hnd2.2.1, List.length_map]
  have dA : Disjoint (T ∪ Q ∪ B₀) (L.map Prod.fst).toFinset := by
    rw [Finset.disjoint_right]
    intro v hv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    exact (hLT p hp).1
  have dC : Disjoint (T ∪ Q ∪ B₀ ∪ (L.map Prod.fst).toFinset) (L.map Prod.snd).toFinset := by
    rw [Finset.disjoint_right]
    intro v hv hv'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    rcases Finset.mem_union.mp hv' with hv' | hv'
    · exact (hLT p hp).2 hv'
    · obtain ⟨q, hq, hq'⟩ := List.mem_map.mp (List.mem_toFinset.mp hv')
      exact hnd2.2.2 q.1 (List.mem_map_of_mem hq) p.2 (List.mem_map_of_mem hp) hq'
  rw [Finset.card_union_of_disjoint dC, Finset.card_union_of_disjoint dA,
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hTB, hQB⟩),
    Finset.card_union_of_disjoint hTQ, h1, h2]
  ring

/-- **Degrees of the seed graph** of a hub run: the hub loses its held spokes, every other
held vertex loses one edge (two for battery vertices), so the vertices of `T ∪ Q` and the
battery vertices are odd, and those of `B₀` are even. -/
theorem hub_seed_deg [DecidableRel G.Adj] (U : Finset V) (hU : ∀ v, v ∈ U ↔ Even (G.degree v))
    (T Q B₀ : Finset V) (L : List (V × V)) (X₀ : Finset V)
    (mX : ∀ v, v ∈ X₀ ↔ v ∈ T ∪ Q ∨ v ∈ B₀ ∨ v ∈ L.map Prod.fst ∨ v ∈ L.map Prod.snd)
    [DecidableRel (G.deleteEdges (hubHeld h X₀ (batChords L))).Adj]
    (hnd : (h :: (L.map Prod.fst ++ L.map Prod.snd)).Nodup)
    (hTQU : ∀ v, v ≠ h → (v ∈ T ∪ Q ↔ v ∈ U))
    (hLU : ∀ p ∈ L, p.1 ∉ U ∧ p.2 ∉ U) (hLB : ∀ p ∈ L, p.1 ∉ B₀ ∧ p.2 ∉ B₀)
    (hhT : ∀ t ∈ T ∪ Q ∪ B₀, G.Adj h t)
    (hbat : ∀ p ∈ L, G.Adj h p.1 ∧ G.Adj h p.2 ∧ G.Adj p.2 p.1) :
    (G.deleteEdges (hubHeld h X₀ (batChords L))).degree h + X₀.card = G.degree h ∧
    ∀ v, v ≠ h →
      (v ∉ B₀ → Odd ((G.deleteEdges (hubHeld h X₀ (batChords L))).degree v)) ∧
      (v ∈ B₀ → (G.deleteEdges (hubHeld h X₀ (batChords L))).degree v + 1 = G.degree v) := by
  have hX : ∀ x ∈ X₀, G.Adj h x := by
    intro x hx
    rcases (mX x).mp hx with hx | hx | hx | hx
    · exact hhT x (Finset.mem_union_left _ hx)
    · exact hhT x (Finset.mem_union_right _ hx)
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact (hbat p hp).1
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact (hbat p hp).2.1
  have hch : ∀ p ∈ L, G.Adj p.2 p.1 := fun p hp => (hbat p hp).2.2
  have hdeg := degree_hubDel G h X₀ L hX hnd hch
  have hhX : h ∉ X₀ := fun hh => (hX h hh).ne rfl
  have hhL : h ∉ L.map Prod.fst ∧ h ∉ L.map Prod.snd := by
    have := (List.nodup_cons.mp hnd).1
    rw [List.mem_append, not_or] at this
    exact this
  have hvU : ∀ v, v ∈ L.map Prod.fst ∨ v ∈ L.map Prod.snd → v ∉ U := by
    rintro v (hv | hv)
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv; exact (hLU p hp).1
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv; exact (hLU p hp).2
  refine ⟨?_, fun v hvh => ⟨fun hvB => ?_, fun hvB => ?_⟩⟩
  · have := hdeg h
    rw [ite_eq_left rfl, ite_eq_right hhX, ite_eq_right (by tauto)] at this
    omega
  · have hd := hdeg v
    rw [ite_eq_right hvh] at hd
    by_cases hvTQ : v ∈ T ∪ Q
    · have hvU' : v ∈ U := (hTQU v hvh).mp hvTQ
      rw [ite_eq_left ((mX v).mpr (Or.inl hvTQ)),
        ite_eq_right (fun h' => hvU v h' hvU')] at hd
      have hev := (hU v).mp hvU'
      have hpos : 0 < G.degree v := G.degree_pos_iff_exists_adj v |>.mpr
        ⟨h, (hhT v (Finset.mem_union_left _ hvTQ)).symm⟩
      obtain ⟨k, hk⟩ := hev
      exact ⟨k - 1, by omega⟩
    · have hvU' : v ∉ U := fun h' => hvTQ ((hTQU v hvh).mpr h')
      have hodd : Odd (G.degree v) := Nat.not_even_iff_odd.mp (fun h' => hvU' ((hU v).mpr h'))
      by_cases hvL : v ∈ L.map Prod.fst ∨ v ∈ L.map Prod.snd
      · rw [ite_eq_left ((mX v).mpr (Or.inr (Or.inr hvL))), ite_eq_left hvL] at hd
        obtain ⟨k, hk⟩ := hodd
        exact ⟨k - 1, by omega⟩
      · have hvX : v ∉ X₀ := fun h' => by
          rcases (mX v).mp h' with h' | h' | h' | h'
          · exact hvTQ h'
          · exact hvB h'
          · exact hvL (Or.inl h')
          · exact hvL (Or.inr h')
        rw [ite_eq_right hvX, ite_eq_right hvL] at hd
        rw [show (G.deleteEdges (hubHeld h X₀ (batChords L))).degree v = G.degree v by omega]
        exact hodd
  · have hd := hdeg v
    have hvL : ¬ (v ∈ L.map Prod.fst ∨ v ∈ L.map Prod.snd) := by
      rintro (hv | hv)
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv; exact (hLB p hp).1 hvB
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv; exact (hLB p hp).2 hvB
    rw [ite_eq_right hvh, ite_eq_left ((mX v).mpr (Or.inr (Or.inl hvB))), ite_eq_right hvL] at hd
    omega

omit [DecidableEq V] in
/-- At even order the number of even-degree vertices (isolated ones included) is even. -/
theorem even_card_evenDeg [DecidableRel G.Adj] (hn : Even (Fintype.card V)) :
    Even (Finset.univ.filter (fun v => Even (G.degree v))).card := by
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset V)) (fun v => Even (G.degree v))
  have h2 : Finset.univ.filter (fun v => ¬ Even (G.degree v)) =
      Finset.univ.filter (fun v => Odd (G.degree v)) := by
    ext v; simp [Nat.not_even_iff_odd]
  rw [h2, Finset.card_univ] at h1
  obtain ⟨a, ha⟩ := G.even_card_odd_degree_vertices
  obtain ⟨b, hb⟩ := hn
  exact ⟨b - a, by omega⟩

/-- **From a realisable set to the rooted test.** If `S ∋ r` is realisable and `2|S|` is at most
the number of even-degree vertices, then `r` passes. -/
theorem passesAt_of_realisable [DecidableRel G.Adj] {S : Finset V} (hS : Realisable G S)
    {r : V} (hr : r ∈ S)
    (hcard : 2 * S.card ≤ (Finset.univ.filter (fun v => Even (G.degree v))).card) :
    PassesAt G r := by
  obtain ⟨hSE, D, hD⟩ := hS
  refine ⟨D, ?_, ?_⟩
  · have hsize := Realises.size_eq hSE hD
    have h1 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset V)) (fun v => Odd (G.degree v))
    have h2 : Finset.univ.filter (fun v => ¬ Odd (G.degree v)) =
        Finset.univ.filter (fun v => Even (G.degree v)) := by
      ext v; simp [Nat.not_odd_iff_even]
    rw [h2, Finset.card_univ] at h1
    obtain ⟨a, ha⟩ := G.even_card_odd_degree_vertices
    unfold oddSet at hsize
    omega
  · rw [hD r]
    unfold profile
    rw [ite_eq_right (not_odd_of_mem_evenSet (hSE hr)), ite_eq_left hr]

/-- The final state of a root-hub run is a realisation of `insert h R`. -/
theorem realisable_of_hst_root [DecidableRel G.Adj] (U : Finset V)
    (hU : ∀ v, v ∈ U ↔ Even (G.degree v)) (hpos : ∀ v ∈ U, 0 < G.degree v) {Z R : Finset V}
    (hA : Ach G.edgeSet (hst h 2 Z R)) (hh : h ∈ U)
    (hcov : ∀ v, v ≠ h → (v ∈ U ↔ v ∈ Z ∨ v ∈ R)) (hZR : Disjoint Z R) :
    Realisable G (insert h R) := by
  obtain ⟨D, hD⟩ := pathDecomp_of_ach hA
  have hev : ∀ v ∈ U, v ∈ evenSet G := fun v hv =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos v hv, (hU v).mp hv⟩
  refine ⟨fun v hv => ?_, D, fun v => ?_⟩
  · rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hev v hh
    · by_cases hvh : v = h
      · exact hvh ▸ hev h hh
      · exact hev v ((hcov v hvh).mpr (Or.inr hv))
  · rw [hD v]
    unfold profile hst
    by_cases hvh : v = h
    · subst hvh
      rw [ite_eq_left rfl, ite_eq_right (Nat.not_odd_iff_even.mpr ((hU v).mp hh)),
        ite_eq_left (Finset.mem_insert_self _ _)]
    · rw [ite_eq_right hvh]
      by_cases hvU : v ∈ U
      · rw [ite_eq_right (Nat.not_odd_iff_even.mpr ((hU v).mp hvU))]
        rcases (hcov v hvh).mp hvU with hvZ | hvR
        · have : v ∉ insert h R := by
            rw [Finset.mem_insert, not_or]
            exact ⟨hvh, Finset.disjoint_left.mp hZR hvZ⟩
          rw [ite_eq_left hvZ, ite_eq_right this]
        · rw [ite_eq_right (Finset.disjoint_right.mp hZR hvR), ite_eq_left hvR,
            ite_eq_left (Finset.mem_insert_of_mem hvR)]
      · have hodd : Odd (G.degree v) := Nat.not_even_iff_odd.mp (fun h' => hvU ((hU v).mpr h'))
        have hvZ : v ∉ Z := fun h' => hvU ((hcov v hvh).mpr (Or.inl h'))
        have hvR : v ∉ R := fun h' => hvU ((hcov v hvh).mpr (Or.inr h'))
        rw [ite_eq_left hodd, ite_eq_right hvZ, ite_eq_right hvR]

/-- The final state of a full-hub run is a realisation of `R`. -/
theorem realisable_of_hst_odd [DecidableRel G.Adj] (U : Finset V)
    (hU : ∀ v, v ∈ U ↔ Even (G.degree v)) (hpos : ∀ v ∈ U, 0 < G.degree v) {Z R : Finset V}
    (hA : Ach G.edgeSet (hst h 1 Z R)) (hh : h ∉ U)
    (hcov : ∀ v, v ∈ U ↔ v ∈ Z ∨ v ∈ R) (hZR : Disjoint Z R) : Realisable G R := by
  obtain ⟨D, hD⟩ := pathDecomp_of_ach hA
  refine ⟨fun v hv => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    hpos v ((hcov v).mpr (Or.inr hv)), (hU v).mp ((hcov v).mpr (Or.inr hv))⟩, D, fun v => ?_⟩
  rw [hD v]
  unfold profile hst
  by_cases hvh : v = h
  · subst hvh
    rw [ite_eq_left rfl, ite_eq_left (Nat.not_even_iff_odd.mp (fun h' => hh ((hU v).mpr h')))]
  · rw [ite_eq_right hvh]
    by_cases hvU : v ∈ U
    · rw [ite_eq_right (Nat.not_odd_iff_even.mpr ((hU v).mp hvU))]
      rcases (hcov v).mp hvU with hvZ | hvR
      · rw [ite_eq_left hvZ, ite_eq_right (Finset.disjoint_left.mp hZR hvZ)]
      · rw [ite_eq_right (Finset.disjoint_right.mp hZR hvR), ite_eq_left hvR, ite_eq_left hvR]
    · have hodd : Odd (G.degree v) := Nat.not_even_iff_odd.mp (fun h' => hvU ((hU v).mpr h'))
      have hvZ : v ∉ Z := fun h' => hvU ((hcov v).mpr (Or.inl h'))
      have hvR : v ∉ R := fun h' => hvU ((hcov v).mpr (Or.inr h'))
      rw [ite_eq_left hodd, ite_eq_right hvZ, ite_eq_right hvR]

end run

/-! ### Theorem 6.1: hubs at every deletion degree -/

section uniform

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem filter_even_eq {U : Finset V} (hU : ∀ v, v ∈ U ↔ Even (G.degree v)) :
    Finset.univ.filter (fun v => Even (G.degree v)) = U := by
  ext v; simp [hU v]

omit [DecidableEq V] in
theorem even_card_of_hU (hn : Even (Fintype.card V)) {U : Finset V}
    (hU : ∀ v, v ∈ U ↔ Even (G.degree v)) : Even U.card := by
  have := even_card_evenDeg (G := G) hn
  rwa [filter_even_eq G hU] at this

/-- The seed of the root hub (Lemma 3.2(b)): after holding the spokes from `r` to `T ∪ {y}` and
to the battery vertices, and the battery chords, the even vertices are exactly `r` and `y`. -/
theorem root_hub_seed (hn : Even (Fintype.card V)) (U : Finset V)
    (hU : ∀ v, v ∈ U ↔ Even (G.degree v)) {r : V} (hr : r ∈ U)
    (hrT : ∀ t ∈ U, t ≠ r → G.Adj r t)
    {y : V} (hry : G.Adj r y) (hyU : y ∉ U) (hy3 : 3 ≤ G.degree y)
    (L : List (V × V)) (hnd : (y :: (L.map Prod.fst ++ L.map Prod.snd)).Nodup)
    (hodd : ∀ p ∈ L, p.1 ∉ U ∧ p.2 ∉ U)
    (htri : ∀ p ∈ L, G.Adj r p.1 ∧ G.Adj r p.2 ∧ G.Adj p.1 p.2)
    (hdeg : U.card + 2 + 2 * L.length ≤ G.degree r) (T : Finset V) (hT : T = U.erase r) :
    Ach (G.edgeSet \ hubHeld r (T ∪ ∅ ∪ {y} ∪ (L.map Prod.fst).toFinset ∪
      (L.map Prod.snd).toFinset) (batChords L)) (hst r 2 {y} ∅) := by
  classical
  obtain ⟨b, hb⟩ := even_card_of_hU G hn hU
  have hTc : T.card = U.card - 1 := by rw [hT, Finset.card_erase_of_mem hr]
  have hU1 : 1 ≤ U.card := Finset.card_pos.mpr ⟨r, hr⟩
  have mT : ∀ {v}, v ∈ T ↔ v ≠ r ∧ v ∈ U := by intro v; rw [hT, Finset.mem_erase]
  have hyL : y ∉ L.map Prod.fst ++ L.map Prod.snd := (List.nodup_cons.mp hnd).1
  have hndr : (r :: (L.map Prod.fst ++ L.map Prod.snd)).Nodup := by
    refine List.nodup_cons.mpr ⟨fun hm => ?_, (List.nodup_cons.mp hnd).2⟩
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨p, hp, hpr⟩ := List.mem_map.mp hm; exact (hodd p hp).1 (hpr ▸ hr)
    · obtain ⟨p, hp, hpr⟩ := List.mem_map.mp hm; exact (hodd p hp).2 (hpr ▸ hr)
  have hTB : Disjoint T {y} := by
    rw [Finset.disjoint_singleton_right]; exact fun h' => hyU (mT.mp h').2
  have hLT : ∀ p ∈ L, p.1 ∉ T ∪ ∅ ∪ {y} ∧ p.2 ∉ T ∪ ∅ ∪ {y} := by
    intro p hp
    simp only [Finset.union_empty, Finset.mem_union, Finset.mem_singleton, not_or]
    refine ⟨⟨fun h' => (hodd p hp).1 (mT.mp h').2, fun h' => hyL (h' ▸ ?_)⟩,
      ⟨fun h' => (hodd p hp).2 (mT.mp h').2, fun h' => hyL (h' ▸ ?_)⟩⟩
    · exact List.mem_append_left _ (List.mem_map_of_mem hp)
    · exact List.mem_append_right _ (List.mem_map_of_mem hp)
  have hhT : ∀ t ∈ T ∪ ∅ ∪ {y}, G.Adj r t := by
    intro t ht
    simp only [Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact hrT t (mT.mp ht).2 (mT.mp ht).1
    · exact hry
  have hbat : ∀ p ∈ L, G.Adj r p.1 ∧ G.Adj r p.2 ∧ G.Adj p.2 p.1 :=
    fun p hp => ⟨(htri p hp).1, (htri p hp).2.1, (htri p hp).2.2.symm⟩
  -- the seed (Lemma 3.2(b)): `r` and `y` are the even vertices of `G − H`
  have mX : ∀ v, v ∈ T ∪ ∅ ∪ {y} ∪ (L.map Prod.fst).toFinset ∪ (L.map Prod.snd).toFinset ↔
      v ∈ T ∪ ∅ ∨ v ∈ ({y} : Finset V) ∨ v ∈ L.map Prod.fst ∨ v ∈ L.map Prod.snd := by
    intro v; simp only [Finset.mem_union, List.mem_toFinset]; tauto
  have hcard := card_hubX T ∅ {y} L (List.nodup_cons.mp hndr).2
    (Finset.disjoint_empty_right _) hTB (Finset.disjoint_empty_left _) hLT
  have hseed : Ach (G.edgeSet \ hubHeld r (T ∪ ∅ ∪ {y} ∪ (L.map Prod.fst).toFinset ∪
      (L.map Prod.snd).toFinset) (batChords L)) (hst r 2 {y} ∅) := by
    apply ach_of_deleteEdges
    obtain ⟨hdr, hdv⟩ := hub_seed_deg U hU T ∅ {y} L _ mX hndr
      (fun v hv => by rw [Finset.union_empty, mT]; exact and_iff_right hv)
      hodd (fun p hp => ⟨fun h' => (hLT p hp).1 (Finset.mem_union_right _ h'),
        fun h' => (hLT p hp).2 (Finset.mem_union_right _ h')⟩) hhT hbat
    rw [hcard] at hdr
    simp only [Finset.card_empty, Finset.card_singleton] at hdr
    refine seed_pair _ hn ?_ hry.ne ?_
    · intro v
      by_cases hvr : v = r
      · rw [hvr]; omega
      · by_cases hvy : v = y
        · have := (hdv v hvr).2 (Finset.mem_singleton.mpr hvy); rw [hvy] at this ⊢; omega
        · exact ((hdv v hvr).1 (fun h' => hvy (Finset.mem_singleton.mp h'))).pos
    · intro v
      by_cases hvr : v = r
      · rw [hvr]
        obtain ⟨a, ha⟩ := (hU r).mp hr
        exact ⟨fun _ => Or.inl rfl, fun _ => ⟨a - b - L.length, by omega⟩⟩
      · by_cases hvy : v = y
        · have h1 := (hdv v hvr).2 (Finset.mem_singleton.mpr hvy)
          rw [hvy] at h1 ⊢
          obtain ⟨a, ha⟩ := Nat.not_even_iff_odd.mp (fun h' => hyU ((hU y).mpr h'))
          exact ⟨fun _ => Or.inr rfl, fun _ => ⟨a, by omega⟩⟩
        · have h1 := (hdv v hvr).1 (fun h' => hvy (Finset.mem_singleton.mp h'))
          exact ⟨fun he => absurd he (Nat.not_even_iff_odd.mpr h1),
            fun h' => by rcases h' with h' | h' <;> contradiction⟩
  exact hseed

/-- **Theorem 6.1(a) (root hub, every deletion degree `d`).** Let `G` have even order and even
vertices `U`, `|U| = d`, and let `r ∈ U` be adjacent to every vertex of `T = U − r`. Suppose `r`
has a quiet odd neighbour `y` (`N(y) ∩ T = ∅`, `d(y) ≥ 3`) and carries `β ≥ d/2 − 3` quiet
batteries `r a_i b_i` (`a_i, b_i` odd, `N(a_i) ∩ T = ∅`, all vertices distinct,
`b_i ∉ N(y)`, `a_i b_j ∉ E` for `i < j`), and that `d(r) ≥ d + 2 + 2β`. Then some `S ⊆ U` with
`r ∈ S` and `|S| = d/2` is realisable; in particular `r` passes. -/
theorem root_hub_uniform (hn : Even (Fintype.card V)) (U : Finset V)
    (hU : ∀ v, v ∈ U ↔ Even (G.degree v)) {r : V} (hr : r ∈ U)
    (hrT : ∀ t ∈ U, t ≠ r → G.Adj r t)
    {y : V} (hry : G.Adj r y) (hyU : y ∉ U) (hyT : ∀ t ∈ U, t ≠ r → ¬ G.Adj y t)
    (hy3 : 3 ≤ G.degree y)
    (L : List (V × V)) (hnd : (y :: (L.map Prod.fst ++ L.map Prod.snd)).Nodup)
    (hodd : ∀ p ∈ L, p.1 ∉ U ∧ p.2 ∉ U)
    (htri : ∀ p ∈ L, G.Adj r p.1 ∧ G.Adj r p.2 ∧ G.Adj p.1 p.2)
    (haT : ∀ p ∈ L, ∀ t ∈ U, t ≠ r → ¬ G.Adj p.1 t)
    (hyb : ∀ p ∈ L, ¬ G.Adj y p.2)
    (hpw : L.Pairwise (fun p q => ¬ G.Adj p.1 q.2))
    (hβ : U.card ≤ 2 * L.length + 6)
    (hdeg : U.card + 2 + 2 * L.length ≤ G.degree r) :
    ∃ S ⊆ U, r ∈ S ∧ 2 * S.card = U.card ∧ Realisable G S := by
  classical
  obtain ⟨b, hb⟩ := even_card_of_hU G hn hU
  obtain ⟨T, hT⟩ : ∃ T, T = U.erase r := ⟨_, rfl⟩
  have hTc : T.card = U.card - 1 := by rw [hT, Finset.card_erase_of_mem hr]
  have hU1 : 1 ≤ U.card := Finset.card_pos.mpr ⟨r, hr⟩
  have mT : ∀ {v}, v ∈ T ↔ v ≠ r ∧ v ∈ U := by intro v; rw [hT, Finset.mem_erase]
  have hyL : y ∉ L.map Prod.fst ++ L.map Prod.snd := (List.nodup_cons.mp hnd).1
  have hndr : (r :: (L.map Prod.fst ++ L.map Prod.snd)).Nodup := by
    refine List.nodup_cons.mpr ⟨fun hm => ?_, (List.nodup_cons.mp hnd).2⟩
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨p, hp, hpr⟩ := List.mem_map.mp hm; exact (hodd p hp).1 (hpr ▸ hr)
    · obtain ⟨p, hp, hpr⟩ := List.mem_map.mp hm; exact (hodd p hp).2 (hpr ▸ hr)
  have hTB : Disjoint T {y} := by
    rw [Finset.disjoint_singleton_right]; exact fun h' => hyU (mT.mp h').2
  have hLT : ∀ p ∈ L, p.1 ∉ T ∪ ∅ ∪ {y} ∧ p.2 ∉ T ∪ ∅ ∪ {y} := by
    intro p hp
    simp only [Finset.union_empty, Finset.mem_union, Finset.mem_singleton, not_or]
    refine ⟨⟨fun h' => (hodd p hp).1 (mT.mp h').2, fun h' => hyL (h' ▸ ?_)⟩,
      ⟨fun h' => (hodd p hp).2 (mT.mp h').2, fun h' => hyL (h' ▸ ?_)⟩⟩
    · exact List.mem_append_left _ (List.mem_map_of_mem hp)
    · exact List.mem_append_right _ (List.mem_map_of_mem hp)
  have hhT : ∀ t ∈ T ∪ ∅ ∪ {y}, G.Adj r t := by
    intro t ht
    simp only [Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact hrT t (mT.mp ht).2 (mT.mp ht).1
    · exact hry
  have hbat : ∀ p ∈ L, G.Adj r p.1 ∧ G.Adj r p.2 ∧ G.Adj p.2 p.1 :=
    fun p hp => ⟨(htri p hp).1, (htri p hp).2.1, (htri p hp).2.2.symm⟩
  -- the seed (Lemma 3.2(b))
  have hseed := root_hub_seed G hn U hU hr hrT hry hyU hy3 L hnd hodd htri hdeg T hT
  -- the run
  obtain ⟨Z, hZT, hZc, hfin⟩ := hub_run (G := G) (h := r) T ∅ {y} L 2 (U.card / 2) hseed hndr
    (Finset.disjoint_empty_right _) hTB (Finset.disjoint_empty_left _) hLT hhT hbat
    (fun p hp w hw => by
      rw [Finset.mem_singleton] at hw; rw [hw]; exact fun h' => hyb p hp h'.symm)
    (hpw.imp (fun h' h'' => h' h''.symm))
    (by
      intro w hw t ht
      rw [Finset.union_empty] at ht
      rcases Finset.mem_union.mp hw with hw | hw
      · rw [Finset.mem_singleton.mp hw]; exact hyT t (mT.mp ht).2 (mT.mp ht).1
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
        exact haT p hp t (mT.mp ht).2 (mT.mp ht).1)
    (by omega) (by simp only [Finset.card_empty]; omega)
    (by simp only [Finset.card_empty, Finset.card_singleton]; omega)
  have hN : 2 + 2 * (U.card / 2) - (∅ : Finset V).card - T.card - ({y} : Finset V).card = 2 := by
    simp only [Finset.card_empty, Finset.card_singleton]; omega
  rw [hN, Finset.empty_union] at hfin
  have hpos : ∀ v ∈ U, 0 < G.degree v := by
    intro v hv
    by_cases hvr : v = r
    · rw [hvr]; omega
    · exact G.degree_pos_iff_exists_adj v |>.mpr ⟨r, (hrT v hv hvr).symm⟩
  have hreal := realisable_of_hst_root (G := G) U hU hpos hfin hr
    (by
      intro v hvr
      rw [Finset.mem_sdiff]
      constructor
      · intro hv
        by_cases hvZ : v ∈ Z
        · exact Or.inl hvZ
        · exact Or.inr ⟨mT.mpr ⟨hvr, hv⟩, hvZ⟩
      · rintro (hv | hv)
        · exact (mT.mp (hZT hv)).2
        · exact (mT.mp hv.1).2)
    (Finset.disjoint_left.mpr fun v hv hv' => (Finset.mem_sdiff.mp hv').2 hv)
  refine ⟨insert r (T \ Z), ?_, Finset.mem_insert_self _ _, ?_, hreal⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hr
    · exact (mT.mp (Finset.mem_sdiff.mp hv).1).2
  · rw [Finset.card_insert_of_notMem (fun h' => (mT.mp (Finset.mem_sdiff.mp h').1).1 rfl),
      Finset.card_sdiff_of_subset hZT, hZc, hTc]
    omega

/-- **Theorem 6.1(a)**, rooted-test form: `r` passes. -/
theorem root_hub_uniform_passes (hn : Even (Fintype.card V)) (U : Finset V)
    (hU : ∀ v, v ∈ U ↔ Even (G.degree v)) {r : V} (hr : r ∈ U)
    (hrT : ∀ t ∈ U, t ≠ r → G.Adj r t)
    {y : V} (hry : G.Adj r y) (hyU : y ∉ U) (hyT : ∀ t ∈ U, t ≠ r → ¬ G.Adj y t)
    (hy3 : 3 ≤ G.degree y)
    (L : List (V × V)) (hnd : (y :: (L.map Prod.fst ++ L.map Prod.snd)).Nodup)
    (hodd : ∀ p ∈ L, p.1 ∉ U ∧ p.2 ∉ U)
    (htri : ∀ p ∈ L, G.Adj r p.1 ∧ G.Adj r p.2 ∧ G.Adj p.1 p.2)
    (haT : ∀ p ∈ L, ∀ t ∈ U, t ≠ r → ¬ G.Adj p.1 t)
    (hyb : ∀ p ∈ L, ¬ G.Adj y p.2)
    (hpw : L.Pairwise (fun p q => ¬ G.Adj p.1 q.2))
    (hβ : U.card ≤ 2 * L.length + 6)
    (hdeg : U.card + 2 + 2 * L.length ≤ G.degree r) : PassesAt G r := by
  obtain ⟨S, -, hrS, hS, hreal⟩ := root_hub_uniform G hn U hU hr hrT hry hyU hyT hy3 L hnd hodd
    htri haT hyb hpw hβ hdeg
  exact passesAt_of_realisable hreal hrS (by rw [filter_even_eq G hU]; omega)

/-- **Theorem 6.1(b) (full hub, every deletion degree `d`).** Let `x` be adjacent to every even
vertex (so `x` is odd) and carry `β ≥ d/2 − 1` quiet batteries `x a_i b_i` (`a_i, b_i` odd,
`N(a_i) ∩ U = ∅`, all vertices distinct, `a_i b_j ∉ E` for `i < j`). Then for every `r ∈ U`
some `S ⊆ U` with `r ∈ S` and `|S| = d/2` is realisable; in particular every `r ∈ U` passes. -/
theorem full_hub_uniform (hn : Even (Fintype.card V)) (U : Finset V)
    (hU : ∀ v, v ∈ U ↔ Even (G.degree v)) {x : V} (hxU : ∀ u ∈ U, G.Adj x u)
    (L : List (V × V)) (hnd : (x :: (L.map Prod.fst ++ L.map Prod.snd)).Nodup)
    (hodd : ∀ p ∈ L, p.1 ∉ U ∧ p.2 ∉ U)
    (htri : ∀ p ∈ L, G.Adj x p.1 ∧ G.Adj x p.2 ∧ G.Adj p.1 p.2)
    (haU : ∀ p ∈ L, ∀ u ∈ U, ¬ G.Adj p.1 u)
    (hpw : L.Pairwise (fun p q => ¬ G.Adj p.1 q.2))
    (hβ : U.card ≤ 2 * L.length + 2) {r : V} (hr : r ∈ U) :
    ∃ S ⊆ U, r ∈ S ∧ 2 * S.card = U.card ∧ Realisable G S := by
  classical
  obtain ⟨b, hb⟩ := even_card_of_hU G hn hU
  obtain ⟨T, hT⟩ : ∃ T, T = U.erase r := ⟨_, rfl⟩
  have hTc : T.card = U.card - 1 := by rw [hT, Finset.card_erase_of_mem hr]
  have hU1 : 1 ≤ U.card := Finset.card_pos.mpr ⟨r, hr⟩
  have mT : ∀ {v}, v ∈ T ↔ v ≠ r ∧ v ∈ U := by intro v; rw [hT, Finset.mem_erase]
  have hxU' : x ∉ U := fun h' => (hxU x h').ne rfl
  have hTQ : Disjoint T {r} := by
    rw [Finset.disjoint_singleton_right]; exact fun h' => (mT.mp h').1 rfl
  have mTQ : ∀ {v}, v ∈ T ∪ {r} ↔ v ∈ U := by
    intro v
    rw [Finset.mem_union, Finset.mem_singleton, mT]
    constructor
    · rintro (h' | rfl)
      · exact h'.2
      · exact hr
    · intro hv
      by_cases hvr : v = r
      · exact Or.inr hvr
      · exact Or.inl ⟨hvr, hv⟩
  have hLT : ∀ p ∈ L, p.1 ∉ T ∪ {r} ∪ ∅ ∧ p.2 ∉ T ∪ {r} ∪ ∅ := by
    intro p hp
    rw [Finset.union_empty, mTQ, mTQ]
    exact hodd p hp
  have hhT : ∀ t ∈ T ∪ {r} ∪ ∅, G.Adj x t := by
    intro t ht
    rw [Finset.union_empty, mTQ] at ht
    exact hxU t ht
  have hbat : ∀ p ∈ L, G.Adj x p.1 ∧ G.Adj x p.2 ∧ G.Adj p.2 p.1 :=
    fun p hp => ⟨(htri p hp).1, (htri p hp).2.1, (htri p hp).2.2.symm⟩
  -- the seed (Lemma 3.2(a)): every vertex of `G − H` is odd
  have mX : ∀ v, v ∈ T ∪ {r} ∪ ∅ ∪ (L.map Prod.fst).toFinset ∪ (L.map Prod.snd).toFinset ↔
      v ∈ T ∪ {r} ∨ v ∈ (∅ : Finset V) ∨ v ∈ L.map Prod.fst ∨ v ∈ L.map Prod.snd := by
    intro v; simp only [Finset.mem_union, List.mem_toFinset]; tauto
  have hcard := card_hubX T {r} ∅ L (List.nodup_cons.mp hnd).2 hTQ
    (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _) hLT
  simp only [Finset.card_empty, Finset.card_singleton] at hcard
  have hseed : Ach (G.edgeSet \ hubHeld x (T ∪ {r} ∪ ∅ ∪ (L.map Prod.fst).toFinset ∪
      (L.map Prod.snd).toFinset) (batChords L)) (hst x 1 ∅ ∅) := by
    apply ach_of_deleteEdges
    obtain ⟨hdx, hdv⟩ := hub_seed_deg U hU T {r} ∅ L _ mX hnd (fun v _ => mTQ) hodd
      (fun _ _ => ⟨Finset.notMem_empty _, Finset.notMem_empty _⟩) hhT hbat
    rw [hcard] at hdx
    refine seed_odd _ (fun v => ?_) x
    by_cases hvx : v = x
    · rw [hvx]
      obtain ⟨a, ha⟩ := Nat.not_even_iff_odd.mp (fun h' => hxU' ((hU x).mpr h'))
      exact ⟨a - b - L.length, by omega⟩
    · exact (hdv v hvx).1 (Finset.notMem_empty _)
  -- the run
  obtain ⟨Z, hZT, hZc, hfin⟩ := hub_run (G := G) (h := x) T {r} ∅ L 1 (U.card / 2) hseed hnd
    hTQ (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _) hLT hhT hbat
    (fun _ _ w hw => absurd hw (Finset.notMem_empty _))
    (hpw.imp (fun h' h'' => h' h''.symm))
    (by
      intro w hw t ht
      rw [Finset.empty_union] at hw
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
      exact haU p hp t (mTQ.mp ht))
    (by omega) (by simp only [Finset.card_singleton]; omega)
    (by simp only [Finset.card_empty, Finset.card_singleton]; omega)
  have hN : 1 + 2 * (U.card / 2) - ({r} : Finset V).card - T.card - (∅ : Finset V).card = 1 := by
    simp only [Finset.card_empty, Finset.card_singleton]; omega
  rw [hN] at hfin
  have hreal := realisable_of_hst_odd (G := G) U hU
    (fun v hv => G.degree_pos_iff_exists_adj v |>.mpr ⟨x, (hxU v hv).symm⟩) hfin hxU'
    (by
      intro v
      rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_sdiff]
      constructor
      · intro hv
        by_cases hvZ : v ∈ Z
        · exact Or.inl hvZ
        · by_cases hvr : v = r
          · exact Or.inr (Or.inl hvr)
          · exact Or.inr (Or.inr ⟨mT.mpr ⟨hvr, hv⟩, hvZ⟩)
      · rintro (hv | hv | hv)
        · exact (mT.mp (hZT hv)).2
        · exact hv ▸ hr
        · exact (mT.mp hv.1).2)
    (by
      rw [Finset.disjoint_left]
      intro v hv hv'
      rcases Finset.mem_union.mp hv' with hv' | hv'
      · exact (mT.mp (hZT hv)).1 (Finset.mem_singleton.mp hv')
      · exact (Finset.mem_sdiff.mp hv').2 hv)
  refine ⟨{r} ∪ (T \ Z), ?_, Finset.mem_union_left _ (Finset.mem_singleton_self r), ?_, hreal⟩
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_singleton.mp hv ▸ hr
    · exact (mT.mp (Finset.mem_sdiff.mp hv).1).2
  · rw [Finset.card_union_of_disjoint (Finset.disjoint_left.mpr fun v hv hv' =>
      (mT.mp (Finset.mem_sdiff.mp hv').1).1 (Finset.mem_singleton.mp hv)),
      Finset.card_singleton, Finset.card_sdiff_of_subset hZT, hZc, hTc]
    omega

/-- **Theorem 6.1(b) with a pendant.** As `full_hub_uniform`, with `β ≥ d/2 − 2` batteries and
a quiet pendant `y` of `x` (`y` odd, `N(y) ∩ U = ∅`, `d(y) ≥ 3`, `b_i ∉ N(y)`), provided `x`
has a further neighbour `w` outside `U`, `y` and the batteries. -/
theorem full_hub_pendant_uniform (hn : Even (Fintype.card V)) (U : Finset V)
    (hU : ∀ v, v ∈ U ↔ Even (G.degree v)) {x : V} (hxU : ∀ u ∈ U, G.Adj x u)
    {y : V} (hxy : G.Adj x y) (hyU : y ∉ U) (hyq : ∀ u ∈ U, ¬ G.Adj y u)
    (hy3 : 3 ≤ G.degree y)
    (L : List (V × V)) (hnd : (x :: y :: (L.map Prod.fst ++ L.map Prod.snd)).Nodup)
    (hodd : ∀ p ∈ L, p.1 ∉ U ∧ p.2 ∉ U)
    (htri : ∀ p ∈ L, G.Adj x p.1 ∧ G.Adj x p.2 ∧ G.Adj p.1 p.2)
    (haU : ∀ p ∈ L, ∀ u ∈ U, ¬ G.Adj p.1 u)
    (hyb : ∀ p ∈ L, ¬ G.Adj y p.2)
    (hpw : L.Pairwise (fun p q => ¬ G.Adj p.1 q.2))
    (hβ : U.card ≤ 2 * L.length + 4)
    {w : V} (hxw : G.Adj x w) (hwU : w ∉ U) (hwy : w ≠ y)
    (hwL : w ∉ L.map Prod.fst ++ L.map Prod.snd) {r : V} (hr : r ∈ U) :
    ∃ S ⊆ U, r ∈ S ∧ 2 * S.card = U.card ∧ Realisable G S := by
  classical
  obtain ⟨b, hb⟩ := even_card_of_hU G hn hU
  obtain ⟨T, hT⟩ : ∃ T, T = U.erase r := ⟨_, rfl⟩
  have hTc : T.card = U.card - 1 := by rw [hT, Finset.card_erase_of_mem hr]
  have hU1 : 1 ≤ U.card := Finset.card_pos.mpr ⟨r, hr⟩
  have mT : ∀ {v}, v ∈ T ↔ v ≠ r ∧ v ∈ U := by intro v; rw [hT, Finset.mem_erase]
  have hxU' : x ∉ U := fun h' => (hxU x h').ne rfl
  have hyL : y ∉ L.map Prod.fst ++ L.map Prod.snd :=
    (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
  have hndx : (x :: (L.map Prod.fst ++ L.map Prod.snd)).Nodup :=
    List.nodup_cons.mpr ⟨fun h' => (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem _ h'),
      (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2⟩
  have hTQ : Disjoint T {r} := by
    rw [Finset.disjoint_singleton_right]; exact fun h' => (mT.mp h').1 rfl
  have mTQ : ∀ {v}, v ∈ T ∪ {r} ↔ v ∈ U := by
    intro v
    rw [Finset.mem_union, Finset.mem_singleton, mT]
    constructor
    · rintro (h' | rfl)
      · exact h'.2
      · exact hr
    · intro hv
      by_cases hvr : v = r
      · exact Or.inr hvr
      · exact Or.inl ⟨hvr, hv⟩
  have hTB : Disjoint T {y} := by
    rw [Finset.disjoint_singleton_right]; exact fun h' => hyU (mT.mp h').2
  have hQB : Disjoint ({r} : Finset V) {y} := by
    rw [Finset.disjoint_singleton]; exact fun h' => hyU (h' ▸ hr)
  have hLT : ∀ p ∈ L, p.1 ∉ T ∪ {r} ∪ {y} ∧ p.2 ∉ T ∪ {r} ∪ {y} := by
    intro p hp
    have m3 : ∀ {v}, v ∈ T ∪ {r} ∪ {y} ↔ v ∈ U ∨ v = y := by
      intro v; rw [Finset.mem_union, mTQ, Finset.mem_singleton]
    rw [m3, m3]
    refine ⟨not_or.mpr ⟨(hodd p hp).1, fun h' => hyL (h' ▸ ?_)⟩,
      not_or.mpr ⟨(hodd p hp).2, fun h' => hyL (h' ▸ ?_)⟩⟩
    · exact List.mem_append_left _ (List.mem_map_of_mem hp)
    · exact List.mem_append_right _ (List.mem_map_of_mem hp)
  have hhT : ∀ t ∈ T ∪ {r} ∪ {y}, G.Adj x t := by
    intro t ht
    rw [Finset.mem_union, mTQ, Finset.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact hxU t ht
    · exact hxy
  have hbat : ∀ p ∈ L, G.Adj x p.1 ∧ G.Adj x p.2 ∧ G.Adj p.2 p.1 :=
    fun p hp => ⟨(htri p hp).1, (htri p hp).2.1, (htri p hp).2.2.symm⟩
  -- the seed (Lemma 3.2(b)): `x` and `y` are the even vertices of `G − H`
  have mX : ∀ v, v ∈ T ∪ {r} ∪ {y} ∪ (L.map Prod.fst).toFinset ∪ (L.map Prod.snd).toFinset ↔
      v ∈ T ∪ {r} ∨ v ∈ ({y} : Finset V) ∨ v ∈ L.map Prod.fst ∨ v ∈ L.map Prod.snd := by
    intro v; simp only [Finset.mem_union, List.mem_toFinset]; tauto
  have hcard := card_hubX T {r} {y} L (List.nodup_cons.mp hndx).2 hTQ hTB hQB hLT
  simp only [Finset.card_singleton] at hcard
  -- `x` has a neighbour outside the held set
  have hxdeg : (T ∪ {r} ∪ {y} ∪ (L.map Prod.fst).toFinset ∪ (L.map Prod.snd).toFinset).card + 1 ≤
      G.degree x := by
    have hwX : w ∉ T ∪ {r} ∪ {y} ∪ (L.map Prod.fst).toFinset ∪ (L.map Prod.snd).toFinset := by
      rw [mX, mTQ, Finset.mem_singleton]
      rintro (h' | h' | h' | h')
      · exact hwU h'
      · exact hwy h'
      · exact hwL (List.mem_append_left _ h')
      · exact hwL (List.mem_append_right _ h')
    rw [← Finset.card_insert_of_notMem hwX, ← card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro v hv
    rw [mem_neighborFinset]
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hxw
    · rcases (mX v).mp hv with hv | hv | hv | hv
      · exact hhT v (Finset.mem_union_left _ hv)
      · exact hhT v (Finset.mem_union_right _ hv)
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv; exact (hbat p hp).1
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv; exact (hbat p hp).2.1
  rw [hcard] at hxdeg
  have hseed : Ach (G.edgeSet \ hubHeld x (T ∪ {r} ∪ {y} ∪ (L.map Prod.fst).toFinset ∪
      (L.map Prod.snd).toFinset) (batChords L)) (hst x 2 {y} ∅) := by
    apply ach_of_deleteEdges
    obtain ⟨hdx, hdv⟩ := hub_seed_deg U hU T {r} {y} L _ mX hndx (fun v _ => mTQ) hodd
      (fun p hp => ⟨fun h' => (hLT p hp).1 (Finset.mem_union_right _ h'),
        fun h' => (hLT p hp).2 (Finset.mem_union_right _ h')⟩) hhT hbat
    rw [hcard] at hdx
    obtain ⟨a, ha⟩ := Nat.not_even_iff_odd.mp (fun h' => hxU' ((hU x).mpr h'))
    refine seed_pair _ hn ?_ hxy.ne ?_
    · intro v
      by_cases hvx : v = x
      · rw [hvx]; omega
      · by_cases hvy : v = y
        · have := (hdv v hvx).2 (Finset.mem_singleton.mpr hvy); rw [hvy] at this ⊢; omega
        · exact ((hdv v hvx).1 (fun h' => hvy (Finset.mem_singleton.mp h'))).pos
    · intro v
      by_cases hvx : v = x
      · rw [hvx]
        exact ⟨fun _ => Or.inl rfl, fun _ => ⟨a - b - L.length, by omega⟩⟩
      · by_cases hvy : v = y
        · have h1 := (hdv v hvx).2 (Finset.mem_singleton.mpr hvy)
          rw [hvy] at h1 ⊢
          obtain ⟨c, hc⟩ := Nat.not_even_iff_odd.mp (fun h' => hyU ((hU y).mpr h'))
          exact ⟨fun _ => Or.inr rfl, fun _ => ⟨c, by omega⟩⟩
        · have h1 := (hdv v hvx).1 (fun h' => hvy (Finset.mem_singleton.mp h'))
          exact ⟨fun he => absurd he (Nat.not_even_iff_odd.mpr h1),
            fun h' => by rcases h' with h' | h' <;> contradiction⟩
  -- the run
  obtain ⟨Z, hZT, hZc, hfin⟩ := hub_run (G := G) (h := x) T {r} {y} L 2 (U.card / 2) hseed
    hndx hTQ hTB hQB hLT hhT hbat
    (fun p hp w hw => by
      rw [Finset.mem_singleton] at hw; rw [hw]; exact fun h' => hyb p hp h'.symm)
    (hpw.imp (fun h' h'' => h' h''.symm))
    (by
      intro w hw t ht
      rcases Finset.mem_union.mp hw with hw | hw
      · rw [Finset.mem_singleton.mp hw]; exact hyq t (mTQ.mp ht)
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
        exact haU p hp t (mTQ.mp ht))
    (by omega) (by simp only [Finset.card_singleton]; omega)
    (by simp only [Finset.card_singleton]; omega)
  have hN : 2 + 2 * (U.card / 2) - ({r} : Finset V).card - T.card - ({y} : Finset V).card = 1 := by
    simp only [Finset.card_singleton]; omega
  rw [hN] at hfin
  have hreal := realisable_of_hst_odd (G := G) U hU
    (fun v hv => G.degree_pos_iff_exists_adj v |>.mpr ⟨x, (hxU v hv).symm⟩) hfin hxU'
    (by
      intro v
      rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_sdiff]
      constructor
      · intro hv
        by_cases hvZ : v ∈ Z
        · exact Or.inl hvZ
        · by_cases hvr : v = r
          · exact Or.inr (Or.inl hvr)
          · exact Or.inr (Or.inr ⟨mT.mpr ⟨hvr, hv⟩, hvZ⟩)
      · rintro (hv | hv | hv)
        · exact (mT.mp (hZT hv)).2
        · exact hv ▸ hr
        · exact (mT.mp hv.1).2)
    (by
      rw [Finset.disjoint_left]
      intro v hv hv'
      rcases Finset.mem_union.mp hv' with hv' | hv'
      · exact (mT.mp (hZT hv)).1 (Finset.mem_singleton.mp hv')
      · exact (Finset.mem_sdiff.mp hv').2 hv)
  refine ⟨{r} ∪ (T \ Z), ?_, Finset.mem_union_left _ (Finset.mem_singleton_self r), ?_, hreal⟩
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_singleton.mp hv ▸ hr
    · exact (mT.mp (Finset.mem_sdiff.mp hv).1).2
  · rw [Finset.card_union_of_disjoint (Finset.disjoint_left.mpr fun v hv hv' =>
      (mT.mp (Finset.mem_sdiff.mp hv').1).1 (Finset.mem_singleton.mp hv)),
      Finset.card_singleton, Finset.card_sdiff_of_subset hZT, hZc, hTc]
    omega

/-- **Theorem 6.1(b)**, rooted-test form: every `r ∈ U` passes. -/
theorem full_hub_uniform_passes (hn : Even (Fintype.card V)) (U : Finset V)
    (hU : ∀ v, v ∈ U ↔ Even (G.degree v)) {x : V} (hxU : ∀ u ∈ U, G.Adj x u)
    (L : List (V × V)) (hnd : (x :: (L.map Prod.fst ++ L.map Prod.snd)).Nodup)
    (hodd : ∀ p ∈ L, p.1 ∉ U ∧ p.2 ∉ U)
    (htri : ∀ p ∈ L, G.Adj x p.1 ∧ G.Adj x p.2 ∧ G.Adj p.1 p.2)
    (haU : ∀ p ∈ L, ∀ u ∈ U, ¬ G.Adj p.1 u)
    (hpw : L.Pairwise (fun p q => ¬ G.Adj p.1 q.2))
    (hβ : U.card ≤ 2 * L.length + 2) : ∀ r ∈ U, PassesAt G r := by
  intro r hr
  obtain ⟨S, -, hrS, hS, hreal⟩ := full_hub_uniform G hn U hU hxU L hnd hodd htri haU hpw hβ hr
  exact passesAt_of_realisable hreal hrS (by rw [filter_even_eq G hU]; omega)

/-- **Theorem 6.1(b) with a pendant**, rooted-test form: every `r ∈ U` passes. -/
theorem full_hub_pendant_uniform_passes (hn : Even (Fintype.card V)) (U : Finset V)
    (hU : ∀ v, v ∈ U ↔ Even (G.degree v)) {x : V} (hxU : ∀ u ∈ U, G.Adj x u)
    {y : V} (hxy : G.Adj x y) (hyU : y ∉ U) (hyq : ∀ u ∈ U, ¬ G.Adj y u)
    (hy3 : 3 ≤ G.degree y)
    (L : List (V × V)) (hnd : (x :: y :: (L.map Prod.fst ++ L.map Prod.snd)).Nodup)
    (hodd : ∀ p ∈ L, p.1 ∉ U ∧ p.2 ∉ U)
    (htri : ∀ p ∈ L, G.Adj x p.1 ∧ G.Adj x p.2 ∧ G.Adj p.1 p.2)
    (haU : ∀ p ∈ L, ∀ u ∈ U, ¬ G.Adj p.1 u)
    (hyb : ∀ p ∈ L, ¬ G.Adj y p.2)
    (hpw : L.Pairwise (fun p q => ¬ G.Adj p.1 q.2))
    (hβ : U.card ≤ 2 * L.length + 4)
    {w : V} (hxw : G.Adj x w) (hwU : w ∉ U) (hwy : w ≠ y)
    (hwL : w ∉ L.map Prod.fst ++ L.map Prod.snd) : ∀ r ∈ U, PassesAt G r := by
  intro r hr
  obtain ⟨S, -, hrS, hS, hreal⟩ := full_hub_pendant_uniform G hn U hU hxU hxy hyU hyq hy3 L hnd
    hodd htri haU hyb hpw hβ hxw hwU hwy hwL hr
  exact passesAt_of_realisable hreal hrS (by rw [filter_even_eq G hU]; omega)

/-! ### Theorem 5.2: the full hub at deletion degree six -/

/-- **Theorem 5.2 (two quiet batteries).** `|U| = 6`, any core `G[U]`, `x` adjacent to all of
`U`, quiet batteries `x a₁ b₁`, `x a₂ b₂` on five distinct vertices with `a₁ b₂ ∉ E`: every
`r ∈ U` passes. -/
theorem full_hub_six (hn : Even (Fintype.card V)) (U : Finset V)
    (hU : ∀ v, v ∈ U ↔ Even (G.degree v)) (hU6 : U.card = 6) {x : V}
    (hxU : ∀ u ∈ U, G.Adj x u) {a₁ b₁ a₂ b₂ : V} (hdist : [x, a₁, b₁, a₂, b₂].Nodup)
    (hodd : a₁ ∉ U ∧ b₁ ∉ U ∧ a₂ ∉ U ∧ b₂ ∉ U)
    (htri₁ : G.Adj x a₁ ∧ G.Adj x b₁ ∧ G.Adj a₁ b₁)
    (htri₂ : G.Adj x a₂ ∧ G.Adj x b₂ ∧ G.Adj a₂ b₂)
    (hq₁ : ∀ u ∈ U, ¬ G.Adj a₁ u) (hq₂ : ∀ u ∈ U, ¬ G.Adj a₂ u) (h12 : ¬ G.Adj a₁ b₂) :
    ∀ r ∈ U, PassesAt G r := by
  refine full_hub_uniform_passes G hn U hU hxU [(a₁, b₁), (a₂, b₂)]
    ((((List.Perm.swap a₂ b₁ [b₂]).cons a₁).cons x).nodup_iff.mp hdist) ?_ ?_ ?_
    (List.pairwise_pair.mpr h12) (by simp [hU6])
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨hodd.1, hodd.2.1⟩
    · exact ⟨hodd.2.2.1, hodd.2.2.2⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact htri₁
    · exact htri₂
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hq₁
    · exact hq₂

/-- **Theorem 5.2 (a quiet battery and a quiet pendant).** `|U| = 6`, `x` adjacent to all of `U`,
a quiet battery `x a₁ b₁`, a quiet pendant `y ∉ {a₁, b₁}` with `y b₁ ∉ E`, and a neighbour `w` of
`x` outside `U ∪ {a₁, b₁, y}`: every `r ∈ U` passes. -/
theorem full_hub_six_pendant (hn : Even (Fintype.card V)) (U : Finset V)
    (hU : ∀ v, v ∈ U ↔ Even (G.degree v)) (hU6 : U.card = 6) {x : V}
    (hxU : ∀ u ∈ U, G.Adj x u) {a₁ b₁ : V} (hodd : a₁ ∉ U ∧ b₁ ∉ U)
    (htri : G.Adj x a₁ ∧ G.Adj x b₁ ∧ G.Adj a₁ b₁) (hq : ∀ u ∈ U, ¬ G.Adj a₁ u)
    {y : V} (hxy : G.Adj x y) (hyU : y ∉ U) (hyq : ∀ u ∈ U, ¬ G.Adj y u)
    (hy3 : 3 ≤ G.degree y) (hya : y ≠ a₁) (hyb : y ≠ b₁) (hyb' : ¬ G.Adj y b₁)
    {w : V} (hxw : G.Adj x w) (hwU : w ∉ U) (hwa : w ≠ a₁) (hwb : w ≠ b₁) (hwy : w ≠ y) :
    ∀ r ∈ U, PassesAt G r := by
  refine full_hub_pendant_uniform_passes G hn U hU hxU hxy hyU hyq hy3 [(a₁, b₁)] ?_ ?_ ?_ ?_ ?_
    (List.pairwise_singleton _ _) (by simp [hU6]) hxw hwU hwy (by simp [hwa, hwb])
  · simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.nodup_cons,
      List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, not_false_eq_true,
      and_true]
    exact ⟨⟨hxy.ne, htri.1.ne, htri.2.1.ne⟩, ⟨hya, hyb⟩, htri.2.2.ne⟩
  · intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact hodd
  · intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact htri
  · intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact hq
  · intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact hyb'

/-! ### Theorem 4.1(i): the root hub at deletion degree six -/

/-- **Theorem 4.1(i).** Let `G` have even order, `|U| = 6`, and let `r ∈ U` be adjacent to all of
`T = U − r`, with `d(r) ≥ 8`. Suppose `r` has an odd neighbour `y` with `d(y) ≥ 3` and
`|N(y) ∩ T| ≤ 2`. Then some `S ⊆ U` with `r ∈ S` and `|S| = 3` is realisable (one end at every odd
vertex, three doubled vertices of `U`, one of which is `r`); in particular `r` passes.

The certificate: hold `r–T` and `ry`; seed `b(r) = 2`, `b(y) = 0`; choose `p, p' ∈ T` with
`N(y) ∩ T ⊆ {p, p'}`; then `p → r` (single), two grouped receipts from `T − p`, `r → s₁`,
`r → s₂` with `s₂ ∉ N(y)`, and `r → y`. -/
theorem root_hub_six (hn : Even (Fintype.card V)) (U : Finset V)
    (hU : ∀ v, v ∈ U ↔ Even (G.degree v)) (hU6 : U.card = 6) {r : V} (hr : r ∈ U)
    (hrT : ∀ t ∈ U, t ≠ r → G.Adj r t) (hdeg : 8 ≤ G.degree r)
    {y : V} (hry : G.Adj r y) (hyU : y ∉ U) (hy3 : 3 ≤ G.degree y)
    (hyT : ((U.erase r).filter (G.Adj y)).card ≤ 2) :
    ∃ S ⊆ U, r ∈ S ∧ S.card = 3 ∧ Realisable G S := by
  classical
  obtain ⟨T, hT⟩ : ∃ T, T = U.erase r := ⟨_, rfl⟩
  have hTc : T.card = 5 := by rw [hT, Finset.card_erase_of_mem hr, hU6]
  have mT : ∀ {v}, v ∈ T ↔ v ≠ r ∧ v ∈ U := by intro v; rw [hT, Finset.mem_erase]
  have hyT' : y ∉ T := fun h' => hyU (mT.mp h').2
  have hyr : y ≠ r := hry.ne.symm
  -- the seed, with no battery
  have hseed0 := root_hub_seed G hn U hU hr hrT hry hyU hy3 [] (by simp) (by simp) (by simp)
    (by simp only [hU6, List.length_nil]; omega) T hT
  have hX0 : T ∪ ∅ ∪ {y} ∪ (([] : List (V × V)).map Prod.fst).toFinset ∪
      (([] : List (V × V)).map Prod.snd).toFinset = insert y T := by
    ext v; simp
  rw [hX0, batChords_nil] at hseed0
  -- `p, p'` with `N(y) ∩ T ⊆ {p, p'}`
  rw [← hT] at hyT
  obtain ⟨P, hYP, hPT, hPc⟩ := Finset.exists_subsuperset_card_eq (Finset.filter_subset (G.Adj y) T)
    hyT (by rw [hTc]; norm_num)
  obtain ⟨p, p', hpp', rfl⟩ := Finset.card_eq_two.mp hPc
  have hpT : p ∈ T := hPT (by simp)
  have hNy : ∀ t ∈ T, G.Adj y t → t = p ∨ t = p' := fun t ht hyt => by
    have := hYP (Finset.mem_filter.mpr ⟨ht, hyt⟩); simpa using this
  have hpr : p ≠ r := (mT.mp hpT).1
  have hpy : p ≠ y := fun h' => hyT' (h' ▸ hpT)
  have hadjT : ∀ t ∈ T, G.Adj r t := fun t ht => hrT t (mT.mp ht).2 (mT.mp ht).1
  -- step 1: `p → r`
  have h1 := hub_take hseed0 (t := p) (Finset.mem_insert_of_mem hpT) (hadjT p hpT)
    (Set.notMem_empty _) (fun h' => hpy (Finset.mem_singleton.mp h')) (Finset.notMem_empty _)
    (by
      apply Nat.le_zero.mp
      refine le_of_le_of_eq (blankNbrs_hub_le (∅ : Finset V) ?_) Finset.card_empty
      intro w _ hw hwr hw0
      rw [hst_eq_zero_iff hwr, Finset.mem_singleton] at hw0
      exact absurd (Or.inl (mem_hubSpokes.mpr (Or.inl ⟨rfl, hw0 ▸ Finset.mem_insert_self y T⟩)))
        hw)
  -- steps 2–3: two grouped receipts from `T − p`
  obtain ⟨Z', hZ'S, hZ'c, h2⟩ := hub_receive h1 (T.erase p)
    (fun t ht => Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp ht).1,
      Finset.mem_insert_of_mem (Finset.mem_erase.mp ht).2⟩)
    (fun t ht => hadjT t (Finset.mem_erase.mp ht).2) (fun _ _ => Set.notMem_empty _)
    (by
      rw [Finset.disjoint_left]
      intro t ht ht'
      rcases Finset.mem_insert.mp ht' with h' | h'
      · exact (Finset.mem_erase.mp ht).1 h'
      · exact hyT' (Finset.mem_singleton.mp h' ▸ (Finset.mem_erase.mp ht).2))
    (Finset.disjoint_empty_right _) 2
    (by
      have hb := blankNbrs_hub_le (G := G) (h := r) (X := (insert y T).erase p)
        (C := ∅) (N := 2 + 1) (B := insert p {y}) (D := ∅) (v := r) {p} (by
          intro w _ hw hwr hw0
          rw [hst_eq_zero_iff hwr, Finset.mem_insert, Finset.mem_singleton] at hw0
          rcases hw0 with rfl | rfl
          · exact Finset.mem_singleton_self _
          · exact absurd (Or.inl (mem_hubSpokes.mpr (Or.inl ⟨rfl, Finset.mem_erase.mpr
              ⟨Ne.symm hpy, Finset.mem_insert_self _ _⟩⟩))) hw)
      rw [Finset.card_singleton] at hb
      intro j hj
      rw [Finset.card_erase_of_mem hpT, hTc]
      omega)
  have hpZ' : p ∉ Z' := fun h => (Finset.mem_erase.mp (hZ'S h)).1 rfl
  have hZ'T : Z' ⊆ T := fun t ht => (Finset.mem_erase.mp (hZ'S ht)).2
  have hyZ' : y ∉ Z' := fun h => hyT' (hZ'T h)
  have hTZ : (T \ insert p Z').card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.insert_subset hpT hZ'T),
      Finset.card_insert_of_notMem hpZ', hZ'c, hTc]
  obtain ⟨u₁, u₂, hu, hTZeq⟩ := Finset.card_eq_two.mp hTZ
  -- order the two receivers so that `s₂ ≠ p'`
  obtain ⟨s₁, s₂, hs, hTZ', hs₂⟩ : ∃ s₁ s₂, s₁ ≠ s₂ ∧ T \ insert p Z' = {s₁, s₂} ∧ s₂ ≠ p' := by
    by_cases h : u₂ = p'
    · exact ⟨u₂, u₁, hu.symm, by rw [hTZeq, Finset.pair_comm], h ▸ hu⟩
    · exact ⟨u₁, u₂, hu, hTZeq, h⟩
  have hs₁ : s₁ ∈ T ∧ s₁ ∉ insert p Z' := by
    rw [← Finset.mem_sdiff, hTZ']; exact Finset.mem_insert_self _ _
  have hs₂' : s₂ ∈ T ∧ s₂ ∉ insert p Z' := by
    rw [← Finset.mem_sdiff, hTZ']; simp
  have hs₁p : s₁ ≠ p := fun h' => hs₁.2 (h' ▸ Finset.mem_insert_self _ _)
  have hs₂p : s₂ ≠ p := fun h' => hs₂'.2 (h' ▸ Finset.mem_insert_self _ _)
  have hs₁Z : s₁ ∉ Z' := fun h' => hs₁.2 (Finset.mem_insert_of_mem h')
  have hs₂Z : s₂ ∉ Z' := fun h' => hs₂'.2 (Finset.mem_insert_of_mem h')
  have hs₁y : s₁ ≠ y := fun h' => hyT' (h' ▸ hs₁.1)
  have hs₂y : s₂ ≠ y := fun h' => hyT' (h' ▸ hs₂'.1)
  have mB : ∀ {w}, w ∈ insert p {y} ∪ Z' ↔ w = y ∨ w ∈ insert p Z' := by
    intro w
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  -- step 4: `r → s₁`, at most four blank neighbours (`Z` and `y`)
  have h3 := hub_give h2 {s₁}
    (by
      rw [Finset.singleton_subset_iff, Finset.mem_sdiff, Finset.mem_erase]
      exact ⟨⟨hs₁p, Finset.mem_insert_of_mem hs₁.1⟩, hs₁Z⟩)
    (fun a ha => (Finset.mem_singleton.mp ha) ▸ hadjT s₁ hs₁.1)
    (fun _ _ => Set.notMem_empty _)
    (by
      rw [Finset.disjoint_singleton_left, mB, not_or]
      exact ⟨hs₁y, hs₁.2⟩)
    (Finset.disjoint_empty_right _) 4
    (by
      intro a ha
      rw [Finset.mem_singleton.mp ha]
      refine (blankNbrs_hub_le (insert y (insert p Z')) ?_).trans ?_
      · intro w _ _ _ hw0
        by_cases hwr : w = r
        · rw [hwr, hst_self] at hw0; omega
        · rw [hst_eq_zero_iff hwr, mB] at hw0
          rcases hw0 with rfl | hw0
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem hw0
      · refine (Finset.card_insert_le _ _).trans ?_
        rw [Finset.card_insert_of_notMem hpZ', hZ'c])
    (by rw [Finset.card_singleton])
  -- step 5: `r → s₂`, at most three blank neighbours (`Z`; `s₂ ∉ N(y)`)
  have h4 := hub_give h3 {s₂}
    (by
      rw [Finset.singleton_subset_iff, Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_erase]
      exact ⟨⟨⟨hs₂p, Finset.mem_insert_of_mem hs₂'.1⟩, hs₂Z⟩,
        fun h' => hs (Finset.mem_singleton.mp h').symm⟩)
    (fun a ha => (Finset.mem_singleton.mp ha) ▸ hadjT s₂ hs₂'.1)
    (fun _ _ => Set.notMem_empty _)
    (by
      rw [Finset.disjoint_singleton_left, mB, not_or]
      exact ⟨hs₂y, hs₂'.2⟩)
    (by
      rw [Finset.disjoint_singleton_left, Finset.empty_union, Finset.mem_singleton]
      exact fun h' => hs h'.symm)
    3
    (by
      intro a ha
      rw [Finset.mem_singleton.mp ha]
      refine (blankNbrs_hub_le (insert p Z') ?_).trans ?_
      · intro w hsw _ _ hw0
        by_cases hwr : w = r
        · rw [hwr, hst_self, Finset.card_singleton] at hw0; omega
        · rw [hst_eq_zero_iff hwr, mB] at hw0
          rcases hw0 with rfl | hw0
          · rcases hNy s₂ hs₂'.1 hsw.symm with h' | h'
            · exact absurd h' hs₂p
            · exact absurd h' hs₂
          · exact hw0
      · rw [Finset.card_insert_of_notMem hpZ', hZ'c])
    (by rw [Finset.card_singleton, Finset.card_singleton])
  -- step 6: `r → y`, at most two blank neighbours (`N(y) ∩ Z ⊆ {p, p'}`)
  have h5 := hub_pay_one h4 (a := y)
    (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr
      ⟨Finset.mem_erase.mpr ⟨Ne.symm hpy, Finset.mem_insert_self y T⟩, hyZ'⟩,
      fun h' => hs₁y (Finset.mem_singleton.mp h').symm⟩,
      fun h' => hs₂y (Finset.mem_singleton.mp h').symm⟩)
    hry (Set.notMem_empty _) (mB.mpr (Or.inl rfl))
    (by
      simp only [Finset.empty_union, Finset.mem_union, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hs₁y, Ne.symm hs₂y⟩)
    (by
      refine lt_of_le_of_lt (blankNbrs_hub_le {p, p'} ?_) ?_
      · intro w hyw _ hwy hw0
        by_cases hwr : w = r
        · rw [hwr, hst_self, Finset.card_singleton, Finset.card_singleton] at hw0; omega
        · rw [hst_eq_zero_iff hwr, mB] at hw0
          rcases hw0 with hw0 | hw0
          · exact absurd hw0 hwy
          · have hwT : w ∈ T := (Finset.insert_subset hpT hZ'T) hw0
            rcases hNy w hwT hyw with h' | h' <;> simp [h']
      · rw [Finset.card_pair hpp', Finset.card_singleton, Finset.card_singleton]; omega)
  -- the end state
  have hXe : ((((insert y T).erase p \ Z') \ {s₁}) \ {s₂}).erase y = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro v hv
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hv
    obtain ⟨hvy, ⟨⟨⟨hvp, hvT⟩, hvZ⟩, hv1⟩, hv2⟩ := hv
    have hvT' : v ∈ T := hvT.resolve_left hvy
    have : v ∈ T \ insert p Z' := by
      rw [Finset.mem_sdiff, Finset.mem_insert, not_or]; exact ⟨hvT', hvp, hvZ⟩
    rw [hTZ', Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h' | h'
    · exact hv1 h'
    · exact hv2 h'
  have hBe : (insert p {y} ∪ Z').erase y = insert p Z' := by
    ext w
    rw [Finset.mem_erase, mB]
    constructor
    · rintro ⟨hwy, hw | hw⟩
      · exact absurd hw hwy
      · exact hw
    · intro hw
      exact ⟨fun h' => hyT' (h' ▸ (Finset.insert_subset hpT hZ'T) hw), Or.inr hw⟩
  have hDe : ∅ ∪ {s₁} ∪ {s₂} = ({s₁, s₂} : Finset V) := by
    ext w; simp only [Finset.empty_union, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  rw [hXe, hubHeld_empty, Set.sdiff_empty, hBe, hDe] at h5
  simp only [Finset.card_singleton] at h5
  have hfin : Ach G.edgeSet (hst r 2 (insert p Z') {s₁, s₂}) := h5.congr rfl (fun v => rfl)
  have hpos : ∀ v ∈ U, 0 < G.degree v := by
    intro v hv
    by_cases hvr : v = r
    · rw [hvr]; omega
    · exact G.degree_pos_iff_exists_adj v |>.mpr ⟨r, (hrT v hv hvr).symm⟩
  have hreal := realisable_of_hst_root (G := G) U hU hpos hfin hr
    (by
      intro v hvr
      constructor
      · intro hv
        by_cases hvZ : v ∈ insert p Z'
        · exact Or.inl hvZ
        · right
          rw [← hTZ', Finset.mem_sdiff]
          exact ⟨mT.mpr ⟨hvr, hv⟩, hvZ⟩
      · rintro (hv | hv)
        · exact (mT.mp ((Finset.insert_subset hpT hZ'T) hv)).2
        · rw [← hTZ'] at hv
          exact (mT.mp (Finset.mem_sdiff.mp hv).1).2)
    (by
      rw [Finset.disjoint_right]
      intro v hv
      rw [← hTZ'] at hv
      exact (Finset.mem_sdiff.mp hv).2)
  refine ⟨insert r {s₁, s₂}, ?_, Finset.mem_insert_self _ _, ?_, hreal⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact hr
    · exact (mT.mp hs₁.1).2
    · exact (mT.mp hs₂'.1).2
  · rw [Finset.card_insert_of_notMem, Finset.card_pair hs]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h' => (mT.mp hs₁.1).1 h'.symm, fun h' => (mT.mp hs₂'.1).1 h'.symm⟩

/-- **Theorem 4.1(i)**, rooted-test form: `r` passes. -/
theorem root_hub_six_passes (hn : Even (Fintype.card V)) (U : Finset V)
    (hU : ∀ v, v ∈ U ↔ Even (G.degree v)) (hU6 : U.card = 6) {r : V} (hr : r ∈ U)
    (hrT : ∀ t ∈ U, t ≠ r → G.Adj r t) (hdeg : 8 ≤ G.degree r)
    {y : V} (hry : G.Adj r y) (hyU : y ∉ U) (hy3 : 3 ≤ G.degree y)
    (hyT : ((U.erase r).filter (G.Adj y)).card ≤ 2) : PassesAt G r := by
  obtain ⟨S, -, hrS, hS, hreal⟩ := root_hub_six G hn U hU hU6 hr hrT hdeg hry hyU hy3 hyT
  exact passesAt_of_realisable hreal hrS (by rw [filter_even_eq G hU]; omega)

/-- **Theorem 4.1(ii)** (`|Q| = 1`, the roots on the edge of `D = K₂`). `|U| = 6`; `r ∈ U` is
adjacent to every vertex of `T = U − r` except `q`, and `q` is not isolated; `d(r) ≥ 8`; `r` has
two adjacent odd neighbours `a, b` with `|N(a) ∩ T| ≤ 2` and `bq ∉ E`. Then some `S ⊆ U` with
`r ∈ S` and `|S| = 3` is realisable.

The certificate: hold `r–(T − q)`, `ra`, `rb`, `ab`; seed `b(r) = 2`, `b(q) = 0`; carry the
battery (`b → r`, `a → b`); `z₁ → r` with `N(a) ∩ (T − q) ⊆ {z₁, w}`; one grouped receipt;
`r → s₁`, `r → s₂` with `s₂ ≠ w`; `r → a`. -/
theorem root_hub_six_Q1 (hn : Even (Fintype.card V)) (U : Finset V)
    (hU : ∀ v, v ∈ U ↔ Even (G.degree v)) (hU6 : U.card = 6) {r q : V} (hr : r ∈ U)
    (hq : q ∈ U) (hqr : q ≠ r) (hrT : ∀ t ∈ U, t ≠ r → t ≠ q → G.Adj r t)
    (hrq : ¬ G.Adj r q) (hq0 : 0 < G.degree q) (hdeg : 8 ≤ G.degree r)
    {a b : V} (hra : G.Adj r a) (hrb : G.Adj r b) (hab : G.Adj a b) (haU : a ∉ U) (hbU : b ∉ U)
    (haT : ((U.erase r).filter (G.Adj a)).card ≤ 2) (hbq : ¬ G.Adj b q) :
    ∃ S ⊆ U, r ∈ S ∧ S.card = 3 ∧ Realisable G S := by
  classical
  obtain ⟨T, hT⟩ : ∃ T, T = (U.erase r).erase q := ⟨_, rfl⟩
  have hTc : T.card = 4 := by
    rw [hT, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hqr, hq⟩),
      Finset.card_erase_of_mem hr, hU6]
  have mT : ∀ {v}, v ∈ T ↔ v ≠ q ∧ v ≠ r ∧ v ∈ U := by
    intro v; rw [hT, Finset.mem_erase, Finset.mem_erase]
  have hadjT : ∀ t ∈ T, G.Adj r t := fun t ht =>
    hrT t (mT.mp ht).2.2 (mT.mp ht).2.1 (mT.mp ht).1
  have haT' : a ∉ T := fun h' => haU (mT.mp h').2.2
  have hbT' : b ∉ T := fun h' => hbU (mT.mp h').2.2
  have hqT : q ∉ T := fun h' => (mT.mp h').1 rfl
  have hab' : a ≠ b := hab.ne
  have har : a ≠ r := hra.ne.symm
  have hbr : b ≠ r := hrb.ne.symm
  have haq : a ≠ q := fun h' => haU (h' ▸ hq)
  have hbq' : b ≠ q := fun h' => hbU (h' ▸ hq)
  -- the seed: hold `r–(T ∪ {a, b})` and the chord `ab`
  obtain ⟨X₀, hX₀⟩ : ∃ X : Finset V, X = insert a (insert b T) := ⟨_, rfl⟩
  have mX : ∀ {v}, v ∈ X₀ ↔ v = a ∨ v = b ∨ v ∈ T := by
    intro v; rw [hX₀, Finset.mem_insert, Finset.mem_insert]
  have hverts : ∀ v, (v ∈ [(a, b)].map Prod.fst ∨ v ∈ [(a, b)].map Prod.snd) ↔ v = a ∨ v = b := by
    intro v; simp
  have hndr : (r :: ([(a, b)].map Prod.fst ++ [(a, b)].map Prod.snd)).Nodup := by
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.nodup_cons,
      List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, not_false_eq_true,
      and_true]
    exact ⟨⟨Ne.symm har, Ne.symm hbr⟩, hab'⟩
  have hX : ∀ x ∈ X₀, G.Adj r x := by
    intro x hx
    rcases mX.mp hx with rfl | rfl | hx
    · exact hra
    · exact hrb
    · exact hadjT x hx
  have hX₀c : X₀.card = 6 := by
    rw [hX₀, Finset.card_insert_of_notMem (by rw [Finset.mem_insert, not_or]; exact ⟨hab', haT'⟩),
      Finset.card_insert_of_notMem hbT', hTc]
  have hseed : Ach (G.edgeSet \ hubHeld r X₀ (batChords [(a, b)])) (hst r 2 {q} ∅) := by
    apply ach_of_deleteEdges
    have hd := degree_hubDel G r X₀ [(a, b)] hX hndr
      (fun p hp => by rw [List.mem_singleton] at hp; subst hp; exact hab.symm)
    have hcase : ∀ v, v ≠ r → v ≠ q →
        Odd ((G.deleteEdges (hubHeld r X₀ (batChords [(a, b)]))).degree v) := by
      intro v hvr hvq
      have h1 := hd v
      rw [ite_eq_right hvr] at h1
      by_cases hvab : v = a ∨ v = b
      · rw [ite_eq_left (mX.mpr (by tauto)), ite_eq_left ((hverts v).mpr hvab)] at h1
        have hvU : v ∉ U := by rcases hvab with rfl | rfl <;> assumption
        obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp (fun h' => hvU ((hU v).mpr h'))
        exact ⟨k - 1, by omega⟩
      · rw [ite_eq_right (fun h' => hvab ((hverts v).mp h'))] at h1
        by_cases hvT : v ∈ T
        · rw [ite_eq_left (mX.mpr (Or.inr (Or.inr hvT)))] at h1
          obtain ⟨k, hk⟩ := (hU v).mp (mT.mp hvT).2.2
          have hpos : 0 < G.degree v :=
            G.degree_pos_iff_exists_adj v |>.mpr ⟨r, (hadjT v hvT).symm⟩
          exact ⟨k - 1, by omega⟩
        · rw [ite_eq_right (fun h' => by
            rcases mX.mp h' with h' | h' | h'
            · exact hvab (Or.inl h')
            · exact hvab (Or.inr h')
            · exact hvT h')] at h1
          have hvU : v ∉ U := fun h' => hvT (mT.mpr ⟨hvq, hvr, h'⟩)
          rw [show (G.deleteEdges (hubHeld r X₀ (batChords [(a, b)]))).degree v = G.degree v by
            omega]
          exact Nat.not_even_iff_odd.mp (fun h' => hvU ((hU v).mpr h'))
    have hdr := hd r
    rw [ite_eq_left rfl, ite_eq_right (fun h' => by
      rcases mX.mp h' with h' | h' | h'
      · exact har h'.symm
      · exact hbr h'.symm
      · exact (mT.mp h').2.1 rfl),
      ite_eq_right (fun h' => by rcases (hverts r).mp h' with h' | h' <;> simp_all), hX₀c] at hdr
    have hdq := hd q
    rw [ite_eq_right hqr, ite_eq_right (fun h' => by
      rcases mX.mp h' with h' | h' | h'
      · exact haq h'.symm
      · exact hbq' h'.symm
      · exact hqT h'),
      ite_eq_right (fun h' => by rcases (hverts q).mp h' with h' | h' <;> simp_all)] at hdq
    refine seed_pair _ hn ?_ (Ne.symm hqr) ?_
    · intro v
      by_cases hvr : v = r
      · rw [hvr]; omega
      · by_cases hvq : v = q
        · rw [hvq]; omega
        · exact (hcase v hvr hvq).pos
    · intro v
      by_cases hvr : v = r
      · rw [hvr]
        obtain ⟨k, hk⟩ := (hU r).mp hr
        exact ⟨fun _ => Or.inl rfl, fun _ => ⟨k - 3, by omega⟩⟩
      · by_cases hvq : v = q
        · rw [hvq]
          obtain ⟨k, hk⟩ := (hU q).mp hq
          exact ⟨fun _ => Or.inr rfl, fun _ => ⟨k, by omega⟩⟩
        · exact ⟨fun he => absurd he (Nat.not_even_iff_odd.mpr (hcase v hvr hvq)),
            fun h' => by rcases h' with h' | h' <;> contradiction⟩
  -- steps 1–2: carry the battery (`b → r`, `a → b`)
  have h1 := hub_batteries (D := ∅) [(a, b)] X₀ 2 {q} hseed hndr
    (fun p hp => by
      rw [List.mem_singleton] at hp; subst hp
      exact ⟨mX.mpr (Or.inl rfl), mX.mpr (Or.inr (Or.inl rfl))⟩)
    (fun p hp => by rw [List.mem_singleton] at hp; subst hp; exact ⟨hrb, hab.symm⟩)
    (fun p hp => by
      rw [List.mem_singleton] at hp; subst hp
      exact ⟨fun h' => haq (Finset.mem_singleton.mp h'), Finset.notMem_empty _,
        fun h' => hbq' (Finset.mem_singleton.mp h'), Finset.notMem_empty _⟩)
    (fun w hw hrw => absurd (Finset.mem_singleton.mp hw ▸ hrw) hrq)
    (fun p hp w hw => by
      rw [List.mem_singleton] at hp; subst hp
      rw [Finset.mem_singleton.mp hw]; exact hbq)
    (List.pairwise_singleton _ _)
  have e1 : ([(a, b)].map Prod.snd).toFinset = {b} := by simp
  have e2 : ([(a, b)].map Prod.fst).toFinset = {a} := by simp
  rw [e1, e2, List.length_singleton] at h1
  -- `z₁, w` with `N(a) ∩ (T − q) ⊆ {z₁, w}`
  have hYc : (T.filter (G.Adj a)).card ≤ 2 := by
    refine le_trans (Finset.card_le_card ?_) haT
    intro t ht
    rw [Finset.mem_filter] at ht ⊢
    exact ⟨Finset.mem_erase.mpr ⟨(mT.mp ht.1).2.1, (mT.mp ht.1).2.2⟩, ht.2⟩
  obtain ⟨P, hYP, hPT, hPc⟩ := Finset.exists_subsuperset_card_eq (Finset.filter_subset (G.Adj a) T)
    hYc (by rw [hTc]; norm_num)
  obtain ⟨z₁, w, hzw, rfl⟩ := Finset.card_eq_two.mp hPc
  have hz₁T : z₁ ∈ T := hPT (by simp)
  have hNa : ∀ t ∈ T, G.Adj a t → t = z₁ ∨ t = w := fun t ht hat => by
    have := hYP (Finset.mem_filter.mpr ⟨ht, hat⟩); simpa using this
  have mX₁ : ∀ {v}, v ∈ X₀ \ {b} ↔ v = a ∨ v ∈ T := by
    intro v
    rw [Finset.mem_sdiff, mX, Finset.mem_singleton]
    constructor
    · rintro ⟨h' | h' | h', hvb⟩
      · exact Or.inl h'
      · exact absurd h' hvb
      · exact Or.inr h'
    · rintro (rfl | h')
      · exact ⟨Or.inl rfl, hab'⟩
      · exact ⟨Or.inr (Or.inr h'), fun h'' => hbT' (h'' ▸ h')⟩
  -- step 3: `z₁ → r`
  have h2 := hub_take h1 (t := z₁) (mX₁.mpr (Or.inr hz₁T)) (hadjT z₁ hz₁T) (Set.notMem_empty _)
    (by
      rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton, not_or]
      exact ⟨(mT.mp hz₁T).1, fun h' => haT' (h' ▸ hz₁T)⟩)
    (Finset.notMem_empty _)
    (by
      apply Nat.le_zero.mp
      refine le_of_le_of_eq (blankNbrs_hub_le (∅ : Finset V) ?_) Finset.card_empty
      intro w' hrw hw hwr hw0
      rw [hst_eq_zero_iff hwr, Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton] at hw0
      rcases hw0 with rfl | rfl
      · exact absurd hrw hrq
      · exact absurd (Or.inl (mem_hubSpokes.mpr (Or.inl ⟨rfl, mX₁.mpr (Or.inl rfl)⟩))) hw)
  -- step 4: one grouped receipt from `T − q − z₁`
  obtain ⟨Z'', hZS, hZc, h3⟩ := hub_receive h2 (T.erase z₁)
    (fun t ht => Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp ht).1,
      mX₁.mpr (Or.inr (Finset.mem_erase.mp ht).2)⟩)
    (fun t ht => hadjT t (Finset.mem_erase.mp ht).2) (fun _ _ => Set.notMem_empty _)
    (by
      rw [Finset.disjoint_left]
      intro t ht ht'
      have htT := (Finset.mem_erase.mp ht).2
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at ht'
      rcases ht' with h' | h' | h'
      · exact (Finset.mem_erase.mp ht).1 h'
      · exact hqT (h' ▸ htT)
      · exact haT' (h' ▸ htT))
    (Finset.disjoint_empty_right _) 1
    (by
      have hb := blankNbrs_hub_le (G := G) (h := r) (X := (X₀ \ {b}).erase z₁) (C := ∅)
        (N := 2 + 1 + 1) (B := insert z₁ ({q} ∪ {a})) (D := ∅) (v := r) {z₁} (by
          intro w' hrw hw hwr hw0
          rw [hst_eq_zero_iff hwr] at hw0
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hw0
          rcases hw0 with h' | h' | h'
          · rw [h']; exact Finset.mem_singleton_self _
          · rw [h'] at hrw; exact absurd hrw hrq
          · rw [h'] at hw
            exact absurd (Or.inl (mem_hubSpokes.mpr (Or.inl ⟨rfl, Finset.mem_erase.mpr
              ⟨fun (h'' : a = z₁) => haT' (h'' ▸ hz₁T), mX₁.mpr (Or.inl rfl)⟩⟩))) hw)
      rw [Finset.card_singleton] at hb
      intro j hj
      rw [Finset.card_erase_of_mem hz₁T, hTc]
      omega)
  obtain ⟨z₂, rfl⟩ := Finset.card_eq_one.mp hZc
  have hz₂T : z₂ ∈ T := (Finset.mem_erase.mp (hZS (Finset.mem_singleton_self _))).2
  have hz₂₁ : z₂ ≠ z₁ := (Finset.mem_erase.mp (hZS (Finset.mem_singleton_self _))).1
  -- the two receivers, ordered so that `s₂ ≠ w`
  have hTZ : (T \ {z₁, z₂}).card = 2 := by
    rw [Finset.card_sdiff_of_subset (by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hz₁T
      · exact hz₂T), Finset.card_pair (Ne.symm hz₂₁), hTc]
  obtain ⟨u₁, u₂, hu, hTZeq⟩ := Finset.card_eq_two.mp hTZ
  obtain ⟨s₁, s₂, hs, hTZ', hs₂⟩ : ∃ s₁ s₂, s₁ ≠ s₂ ∧ T \ {z₁, z₂} = {s₁, s₂} ∧ s₂ ≠ w := by
    by_cases h : u₂ = w
    · exact ⟨u₂, u₁, hu.symm, by rw [hTZeq, Finset.pair_comm], h ▸ hu⟩
    · exact ⟨u₁, u₂, hu, hTZeq, h⟩
  have hs₁ : s₁ ∈ T ∧ s₁ ∉ ({z₁, z₂} : Finset V) := by
    rw [← Finset.mem_sdiff, hTZ']; exact Finset.mem_insert_self _ _
  have hs₂' : s₂ ∈ T ∧ s₂ ∉ ({z₁, z₂} : Finset V) := by
    rw [← Finset.mem_sdiff, hTZ']; simp
  have hs₁z : s₁ ≠ z₁ ∧ s₁ ≠ z₂ := by
    have := hs₁.2; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at this; exact this
  have hs₂z : s₂ ≠ z₁ ∧ s₂ ≠ z₂ := by
    have := hs₂'.2; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at this
    exact this
  have mB : ∀ {v}, v ∈ insert z₁ (({q} : Finset V) ∪ {a}) ∪ ({z₂} : Finset V) ↔ v = a ∨ v = q ∨ v = z₁ ∨ v = z₂ := by
    intro v; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
  have hsB : ∀ s, s ∈ T → s ≠ z₁ → s ≠ z₂ →
      s ∉ insert z₁ (({q} : Finset V) ∪ {a}) ∪ ({z₂} : Finset V) := by
    intro s hsT h1 h2 h'
    rcases mB.mp h' with rfl | rfl | rfl | rfl
    · exact haT' hsT
    · exact hqT hsT
    · exact h1 rfl
    · exact h2 rfl
  have mX₃ : ∀ {v}, v ∈ ((X₀ \ {b}).erase z₁) \ {z₂} ↔ (v = a ∨ v ∈ T) ∧ v ≠ z₁ ∧ v ≠ z₂ := by
    intro v
    rw [Finset.mem_sdiff, Finset.mem_erase, mX₁, Finset.mem_singleton]
    tauto
  -- step 5: `r → s₁`, at most four blank neighbours
  have h4 := hub_give h3 {s₁}
    (by rw [Finset.singleton_subset_iff, mX₃]; exact ⟨Or.inr hs₁.1, hs₁z⟩)
    (fun x hx => (Finset.mem_singleton.mp hx) ▸ hadjT s₁ hs₁.1)
    (fun _ _ => Set.notMem_empty _)
    (Finset.disjoint_singleton_left.mpr (hsB s₁ hs₁.1 hs₁z.1 hs₁z.2))
    (Finset.disjoint_empty_right _) 4
    (by
      intro x hx
      rw [Finset.mem_singleton.mp hx]
      refine (blankNbrs_hub_le (insert a (insert q (insert z₁ {z₂}))) ?_).trans
        ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
          (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp))))))
      intro w' _ _ _ hw0
      by_cases hwr : w' = r
      · rw [hwr, hst_self] at hw0; omega
      · rw [hst_eq_zero_iff hwr, mB] at hw0
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact hw0)
    (by rw [Finset.card_singleton])
  -- step 6: `r → s₂`, at most three blank neighbours (`s₂ ∉ N(a)`)
  have h5 := hub_give h4 {s₂}
    (by
      rw [Finset.singleton_subset_iff, Finset.mem_sdiff, mX₃, Finset.mem_singleton]
      exact ⟨⟨Or.inr hs₂'.1, hs₂z⟩, fun h' => hs h'.symm⟩)
    (fun x hx => (Finset.mem_singleton.mp hx) ▸ hadjT s₂ hs₂'.1)
    (fun _ _ => Set.notMem_empty _)
    (Finset.disjoint_singleton_left.mpr (hsB s₂ hs₂'.1 hs₂z.1 hs₂z.2))
    (by
      rw [Finset.disjoint_singleton_left, Finset.empty_union, Finset.mem_singleton]
      exact fun h' => hs h'.symm)
    3
    (by
      intro x hx
      rw [Finset.mem_singleton.mp hx]
      refine (blankNbrs_hub_le (insert q (insert z₁ {z₂})) ?_).trans
        ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
          (by simp))))
      intro w' hsw _ _ hw0
      by_cases hwr : w' = r
      · rw [hwr, hst_self, Finset.card_singleton] at hw0; omega
      · rw [hst_eq_zero_iff hwr, mB] at hw0
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hw0 with rfl | hw0
        · rcases hNa s₂ hs₂'.1 hsw.symm with h' | h'
          · exact absurd h' hs₂z.1
          · exact absurd h' hs₂
        · exact hw0)
    (by rw [Finset.card_singleton, Finset.card_singleton])
  -- step 7: `r → a`, at most `|N(a) ∩ T| ≤ 2` blank neighbours
  have h6 := hub_pay_one h5 (a := a)
    (by
      rw [Finset.mem_sdiff, Finset.mem_sdiff, mX₃, Finset.mem_singleton, Finset.mem_singleton]
      exact ⟨⟨⟨Or.inl rfl, fun h' => haT' (h' ▸ hz₁T), fun h' => haT' (h' ▸ hz₂T)⟩,
        fun h' => haT' (h' ▸ hs₁.1)⟩, fun h' => haT' (h' ▸ hs₂'.1)⟩)
    hra (Set.notMem_empty _) (mB.mpr (Or.inl rfl))
    (by
      simp only [Finset.empty_union, Finset.mem_union, Finset.mem_singleton, not_or]
      exact ⟨fun h' => haT' (h' ▸ hs₁.1), fun h' => haT' (h' ▸ hs₂'.1)⟩)
    (by
      refine lt_of_le_of_lt (blankNbrs_hub_le ((U.erase r).filter (G.Adj a)) ?_) ?_
      · intro w' haw _ hwa hw0
        by_cases hwr : w' = r
        · rw [hwr, hst_self, Finset.card_singleton, Finset.card_singleton] at hw0; omega
        · rw [hst_eq_zero_iff hwr, mB] at hw0
          rw [Finset.mem_filter, Finset.mem_erase]
          refine ⟨⟨hwr, ?_⟩, haw⟩
          rcases hw0 with h' | rfl | rfl | rfl
          · exact absurd h' hwa
          · exact hq
          · exact (mT.mp hz₁T).2.2
          · exact (mT.mp hz₂T).2.2
      · simp only [Finset.card_singleton]; omega)
  -- the end state
  have hXe : ((((X₀ \ {b}).erase z₁ \ {z₂}) \ {s₁}) \ {s₂}).erase a = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro v hv
    rw [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_sdiff, mX₃, Finset.mem_singleton,
      Finset.mem_singleton] at hv
    obtain ⟨hva, ⟨⟨hvaT, hv1, hv2⟩, hvs1⟩, hvs2⟩ := hv
    have hvT : v ∈ T := hvaT.resolve_left hva
    have : v ∈ T \ {z₁, z₂} := by
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hvT, hv1, hv2⟩
    rw [hTZ', Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h' | h'
    · exact hvs1 h'
    · exact hvs2 h'
  have hBe : (insert z₁ (({q} : Finset V) ∪ {a}) ∪ ({z₂} : Finset V)).erase a = {q, z₁, z₂} := by
    ext v
    rw [Finset.mem_erase, mB]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hva, h' | h'⟩
      · exact absurd h' hva
      · exact h'
    · intro h'
      refine ⟨?_, Or.inr h'⟩
      rintro rfl
      rcases h' with h' | h' | h'
      · exact haq h'
      · exact haT' (h' ▸ hz₁T)
      · exact haT' (h' ▸ hz₂T)
  have hDe : ∅ ∪ {s₁} ∪ {s₂} = ({s₁, s₂} : Finset V) := by
    ext v; simp only [Finset.empty_union, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  rw [hXe, hubHeld_empty, Set.sdiff_empty, hBe, hDe] at h6
  simp only [Finset.card_singleton] at h6
  have hfin : Ach G.edgeSet (hst r 2 {q, z₁, z₂} {s₁, s₂}) := h6.congr rfl (fun v => rfl)
  have hpos : ∀ v ∈ U, 0 < G.degree v := by
    intro v hv
    by_cases hvr : v = r
    · rw [hvr]; omega
    · by_cases hvq : v = q
      · rw [hvq]; exact hq0
      · exact G.degree_pos_iff_exists_adj v |>.mpr ⟨r, (hrT v hv hvr hvq).symm⟩
  have hreal := realisable_of_hst_root (G := G) U hU hpos hfin hr
    (by
      intro v hvr
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hv
        by_cases hvq : v = q
        · exact Or.inl (Or.inl hvq)
        · have hvT : v ∈ T := mT.mpr ⟨hvq, hvr, hv⟩
          by_cases hvz : v = z₁ ∨ v = z₂
          · exact Or.inl (Or.inr hvz)
          · right
            have : v ∈ T \ {z₁, z₂} := by
              rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; exact ⟨hvT, hvz⟩
            rw [hTZ', Finset.mem_insert, Finset.mem_singleton] at this
            exact this
      · rintro ((rfl | rfl | rfl) | (rfl | rfl))
        · exact hq
        · exact (mT.mp hz₁T).2.2
        · exact (mT.mp hz₂T).2.2
        · exact (mT.mp hs₁.1).2.2
        · exact (mT.mp hs₂'.1).2.2)
    (by
      rw [Finset.disjoint_left]
      intro v hv hv'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv hv'
      rcases hv' with rfl | rfl
      · rcases hv with h' | h' | h'
        · exact hqT (h' ▸ hs₁.1)
        · exact hs₁z.1 h'
        · exact hs₁z.2 h'
      · rcases hv with h' | h' | h'
        · exact hqT (h' ▸ hs₂'.1)
        · exact hs₂z.1 h'
        · exact hs₂z.2 h')
  refine ⟨insert r {s₁, s₂}, ?_, Finset.mem_insert_self _ _, ?_, hreal⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact hr
    · exact (mT.mp hs₁.1).2.2
    · exact (mT.mp hs₂'.1).2.2
  · rw [Finset.card_insert_of_notMem, Finset.card_pair hs]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h' => (mT.mp hs₁.1).2.1 h'.symm, fun h' => (mT.mp hs₂'.1).2.1 h'.symm⟩

/-- **Theorem 4.1(iii)** (`|Q| = 2`: the middle of `P₃`, a vertex of `K₃`, a vertex of `C₄`).
`|U| = 6`; `r ∈ U` is adjacent to every vertex of `T = U − r` except `q₁, q₂`, which are not
isolated; `r` has two adjacent odd neighbours `a, b` with `|N(a) ∩ N_T(r)| ≤ 1` and `bq₂ ∉ E`.
Then some `S ⊆ U` with `r ∈ S` and `|S| = 3` is realisable.

The certificate: hold `r–N_T(r)`, `ra`, `rb`, `ab`; seed `b(q₁) = 2`, `b(q₂) = 0`, `b(r) = 1`;
carry the battery; `z₁ → r` with `N(a) ∩ N_T(r) ⊆ {z₁}`; one grouped receipt; `r → s`;
`r → a`. -/
theorem root_hub_six_Q2 (hn : Even (Fintype.card V)) (U : Finset V)
    (hU : ∀ v, v ∈ U ↔ Even (G.degree v)) (hU6 : U.card = 6) {r q₁ q₂ : V} (hr : r ∈ U)
    (hq₁ : q₁ ∈ U) (hq₂ : q₂ ∈ U) (hq₁r : q₁ ≠ r) (hq₂r : q₂ ≠ r) (hq₁₂ : q₁ ≠ q₂)
    (hrT : ∀ t ∈ U, t ≠ r → t ≠ q₁ → t ≠ q₂ → G.Adj r t)
    (hrq₁ : ¬ G.Adj r q₁) (hrq₂ : ¬ G.Adj r q₂) (hq₁0 : 0 < G.degree q₁)
    (hq₂0 : 0 < G.degree q₂)
    {a b : V} (hra : G.Adj r a) (hrb : G.Adj r b) (hab : G.Adj a b) (haU : a ∉ U) (hbU : b ∉ U)
    (haT : ((((U.erase r).erase q₁).erase q₂).filter (G.Adj a)).card ≤ 1)
    (hbq : ¬ G.Adj b q₂) :
    ∃ S ⊆ U, r ∈ S ∧ S.card = 3 ∧ Realisable G S := by
  classical
  obtain ⟨T, hT⟩ : ∃ T, T = ((U.erase r).erase q₁).erase q₂ := ⟨_, rfl⟩
  have hTc : T.card = 3 := by
    rw [hT, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hq₁₂.symm,
        Finset.mem_erase.mpr ⟨hq₂r, hq₂⟩⟩),
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hq₁r, hq₁⟩),
      Finset.card_erase_of_mem hr, hU6]
  have mT : ∀ {v}, v ∈ T ↔ v ≠ q₂ ∧ v ≠ q₁ ∧ v ≠ r ∧ v ∈ U := by
    intro v; rw [hT, Finset.mem_erase, Finset.mem_erase, Finset.mem_erase]
  rw [← hT] at haT
  have hadjT : ∀ t ∈ T, G.Adj r t := fun t ht =>
    hrT t (mT.mp ht).2.2.2 (mT.mp ht).2.2.1 (mT.mp ht).2.1 (mT.mp ht).1
  have haT' : a ∉ T := fun h' => haU (mT.mp h').2.2.2
  have hbT' : b ∉ T := fun h' => hbU (mT.mp h').2.2.2
  have hq₁T : q₁ ∉ T := fun h' => (mT.mp h').2.1 rfl
  have hq₂T : q₂ ∉ T := fun h' => (mT.mp h').1 rfl
  have hab' : a ≠ b := hab.ne
  have har : a ≠ r := hra.ne.symm
  have hbr : b ≠ r := hrb.ne.symm
  have haq₁ : a ≠ q₁ := fun h' => haU (h' ▸ hq₁)
  have haq₂ : a ≠ q₂ := fun h' => haU (h' ▸ hq₂)
  have hbq₁ : b ≠ q₁ := fun h' => hbU (h' ▸ hq₁)
  have hbq₂ : b ≠ q₂ := fun h' => hbU (h' ▸ hq₂)
  -- the seed: hold `r–(N_T(r) ∪ {a, b})` and the chord `ab`
  obtain ⟨X₀, hX₀⟩ : ∃ X : Finset V, X = insert a (insert b T) := ⟨_, rfl⟩
  have mX : ∀ {v}, v ∈ X₀ ↔ v = a ∨ v = b ∨ v ∈ T := by
    intro v; rw [hX₀, Finset.mem_insert, Finset.mem_insert]
  have hverts : ∀ v, (v ∈ [(a, b)].map Prod.fst ∨ v ∈ [(a, b)].map Prod.snd) ↔ v = a ∨ v = b := by
    intro v; simp
  have hndr : (r :: ([(a, b)].map Prod.fst ++ [(a, b)].map Prod.snd)).Nodup := by
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.nodup_cons,
      List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, not_false_eq_true,
      and_true]
    exact ⟨⟨Ne.symm har, Ne.symm hbr⟩, hab'⟩
  have hX : ∀ x ∈ X₀, G.Adj r x := by
    intro x hx
    rcases mX.mp hx with rfl | rfl | hx
    · exact hra
    · exact hrb
    · exact hadjT x hx
  have hX₀c : X₀.card = 5 := by
    rw [hX₀, Finset.card_insert_of_notMem (by rw [Finset.mem_insert, not_or]; exact ⟨hab', haT'⟩),
      Finset.card_insert_of_notMem hbT', hTc]
  have hseed0 : Ach (G.edgeSet \ hubHeld r X₀ (batChords [(a, b)])) (hst q₁ 2 {q₂} ∅) := by
    apply ach_of_deleteEdges
    have hd := degree_hubDel G r X₀ [(a, b)] hX hndr
      (fun p hp => by rw [List.mem_singleton] at hp; subst hp; exact hab.symm)
    have hcase : ∀ v, v ≠ q₁ → v ≠ q₂ →
        Odd ((G.deleteEdges (hubHeld r X₀ (batChords [(a, b)]))).degree v) := by
      intro v hv1 hv2
      have h1 := hd v
      by_cases hvr : v = r
      · rw [hvr, ite_eq_left rfl, ite_eq_right (fun h' => by
          rcases mX.mp h' with h' | h' | h'
          · exact har h'.symm
          · exact hbr h'.symm
          · exact (mT.mp h').2.2.1 rfl),
          ite_eq_right (fun h' => by rcases (hverts r).mp h' with h' | h' <;> simp_all), hX₀c] at h1
        obtain ⟨k, hk⟩ := (hU r).mp hr
        have h5 : 5 ≤ G.degree r := by
          rw [← hX₀c, ← card_neighborFinset_eq_degree]
          exact Finset.card_le_card (fun x hx => (mem_neighborFinset _ _ _).mpr (hX x hx))
        rw [hvr]
        exact ⟨k - 3, by omega⟩
      rw [ite_eq_right hvr] at h1
      by_cases hvab : v = a ∨ v = b
      · rw [ite_eq_left (mX.mpr (by tauto)), ite_eq_left ((hverts v).mpr hvab)] at h1
        have hvU : v ∉ U := by rcases hvab with rfl | rfl <;> assumption
        obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp (fun h' => hvU ((hU v).mpr h'))
        exact ⟨k - 1, by omega⟩
      · rw [ite_eq_right (fun h' => hvab ((hverts v).mp h'))] at h1
        by_cases hvT : v ∈ T
        · rw [ite_eq_left (mX.mpr (Or.inr (Or.inr hvT)))] at h1
          obtain ⟨k, hk⟩ := (hU v).mp (mT.mp hvT).2.2.2
          have hpos : 0 < G.degree v :=
            G.degree_pos_iff_exists_adj v |>.mpr ⟨r, (hadjT v hvT).symm⟩
          exact ⟨k - 1, by omega⟩
        · rw [ite_eq_right (fun h' => by
            rcases mX.mp h' with h' | h' | h'
            · exact hvab (Or.inl h')
            · exact hvab (Or.inr h')
            · exact hvT h')] at h1
          have hvU : v ∉ U := fun h' => hvT (mT.mpr ⟨hv2, hv1, hvr, h'⟩)
          rw [show (G.deleteEdges (hubHeld r X₀ (batChords [(a, b)]))).degree v = G.degree v by
            omega]
          exact Nat.not_even_iff_odd.mp (fun h' => hvU ((hU v).mpr h'))
    have hdq : ∀ q, q ∈ U → q ≠ r → q ∉ T →
        (G.deleteEdges (hubHeld r X₀ (batChords [(a, b)]))).degree q = G.degree q := by
      intro q hqU hqr hqT
      have h1 := hd q
      have hqa : q ≠ a := fun h' => haU (h' ▸ hqU)
      have hqb : q ≠ b := fun h' => hbU (h' ▸ hqU)
      rw [ite_eq_right hqr, ite_eq_right (fun h' => by
        rcases mX.mp h' with h' | h' | h'
        · exact hqa h'
        · exact hqb h'
        · exact hqT h'),
        ite_eq_right (fun h' => by rcases (hverts q).mp h' with h' | h' <;> simp_all)] at h1
      omega
    have hd1 := hdq q₁ hq₁ hq₁r hq₁T
    have hd2 := hdq q₂ hq₂ hq₂r hq₂T
    refine seed_pair _ hn ?_ hq₁₂ ?_
    · intro v
      by_cases hv1 : v = q₁
      · rw [hv1, hd1]; exact hq₁0
      · by_cases hv2 : v = q₂
        · rw [hv2, hd2]; exact hq₂0
        · exact (hcase v hv1 hv2).pos
    · intro v
      by_cases hv1 : v = q₁
      · rw [hv1, hd1]; exact ⟨fun _ => Or.inl rfl, fun _ => (hU q₁).mp hq₁⟩
      · by_cases hv2 : v = q₂
        · rw [hv2, hd2]; exact ⟨fun _ => Or.inr rfl, fun _ => (hU q₂).mp hq₂⟩
        · exact ⟨fun he => absurd he (Nat.not_even_iff_odd.mpr (hcase v hv1 hv2)),
            fun h' => by rcases h' with h' | h' <;> contradiction⟩
  have hseed : Ach (G.edgeSet \ hubHeld r X₀ (batChords [(a, b)])) (hst r 1 {q₂} {q₁}) := by
    refine hseed0.congr rfl (fun v => ?_)
    unfold hst
    by_cases hv1 : v = q₁
    · subst hv1
      simp [hq₁r, hq₁₂]
    · by_cases hvr : v = r
      · subst hvr
        simp [hv1, hq₂r.symm]
      · simp [hv1, hvr]
  -- steps 1–2: carry the battery
  have h1 := hub_batteries (D := {q₁}) [(a, b)] X₀ 1 {q₂} hseed hndr
    (fun p hp => by
      rw [List.mem_singleton] at hp; subst hp
      exact ⟨mX.mpr (Or.inl rfl), mX.mpr (Or.inr (Or.inl rfl))⟩)
    (fun p hp => by rw [List.mem_singleton] at hp; subst hp; exact ⟨hrb, hab.symm⟩)
    (fun p hp => by
      rw [List.mem_singleton] at hp; subst hp
      exact ⟨fun h' => haq₂ (Finset.mem_singleton.mp h'), fun h' => haq₁ (Finset.mem_singleton.mp h'),
        fun h' => hbq₂ (Finset.mem_singleton.mp h'), fun h' => hbq₁ (Finset.mem_singleton.mp h')⟩)
    (fun w hw hrw => absurd (Finset.mem_singleton.mp hw ▸ hrw) hrq₂)
    (fun p hp w hw => by
      rw [List.mem_singleton] at hp; subst hp
      rw [Finset.mem_singleton.mp hw]; exact hbq)
    (List.pairwise_singleton _ _)
  have e1 : ([(a, b)].map Prod.snd).toFinset = {b} := by simp
  have e2 : ([(a, b)].map Prod.fst).toFinset = {a} := by simp
  rw [e1, e2, List.length_singleton] at h1
  -- `z₁` with `N(a) ∩ N_T(r) ⊆ {z₁}`
  obtain ⟨P, hYP, hPT, hPc⟩ := Finset.exists_subsuperset_card_eq (Finset.filter_subset (G.Adj a) T)
    haT (by rw [hTc]; norm_num)
  obtain ⟨z₁, rfl⟩ := Finset.card_eq_one.mp hPc
  have hz₁T : z₁ ∈ T := hPT (Finset.mem_singleton_self _)
  have hNa : ∀ t ∈ T, G.Adj a t → t = z₁ := fun t ht hat => by
    have := hYP (Finset.mem_filter.mpr ⟨ht, hat⟩); simpa using this
  have mX₁ : ∀ {v}, v ∈ X₀ \ {b} ↔ v = a ∨ v ∈ T := by
    intro v
    rw [Finset.mem_sdiff, mX, Finset.mem_singleton]
    constructor
    · rintro ⟨h' | h' | h', hvb⟩
      · exact Or.inl h'
      · exact absurd h' hvb
      · exact Or.inr h'
    · rintro (rfl | h')
      · exact ⟨Or.inl rfl, hab'⟩
      · exact ⟨Or.inr (Or.inr h'), fun h'' => hbT' (h'' ▸ h')⟩
  -- step 3: `z₁ → r`
  have h2 := hub_take h1 (t := z₁) (mX₁.mpr (Or.inr hz₁T)) (hadjT z₁ hz₁T) (Set.notMem_empty _)
    (by
      rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton, not_or]
      exact ⟨(mT.mp hz₁T).1, fun h' => haT' (h' ▸ hz₁T)⟩)
    (fun h' => (mT.mp hz₁T).2.1 (Finset.mem_singleton.mp h'))
    (by
      apply Nat.le_zero.mp
      refine le_of_le_of_eq (blankNbrs_hub_le (∅ : Finset V) ?_) Finset.card_empty
      intro w' hrw hw hwr hw0
      rw [hst_eq_zero_iff hwr, Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton] at hw0
      rcases hw0 with h' | h'
      · rw [h'] at hrw; exact absurd hrw hrq₂
      · rw [h'] at hw
        exact absurd (Or.inl (mem_hubSpokes.mpr (Or.inl ⟨rfl, mX₁.mpr (Or.inl rfl)⟩))) hw)
  -- step 4: one grouped receipt from `N_T(r) − z₁`
  obtain ⟨Z'', hZS, hZc, h3⟩ := hub_receive h2 (T.erase z₁)
    (fun t ht => Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp ht).1,
      mX₁.mpr (Or.inr (Finset.mem_erase.mp ht).2)⟩)
    (fun t ht => hadjT t (Finset.mem_erase.mp ht).2) (fun _ _ => Set.notMem_empty _)
    (by
      rw [Finset.disjoint_left]
      intro t ht ht'
      have htT := (Finset.mem_erase.mp ht).2
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at ht'
      rcases ht' with h' | h' | h'
      · exact (Finset.mem_erase.mp ht).1 h'
      · exact hq₂T (h' ▸ htT)
      · exact haT' (h' ▸ htT))
    (by
      rw [Finset.disjoint_singleton_right]
      exact fun h' => hq₁T (Finset.mem_erase.mp h').2) 1
    (by
      have hb := blankNbrs_hub_le (G := G) (h := r) (X := (X₀ \ {b}).erase z₁) (C := ∅)
        (N := 1 + 1 + 1) (B := insert z₁ ({q₂} ∪ {a})) (D := {q₁}) (v := r) {z₁} (by
          intro w' hrw hw hwr hw0
          rw [hst_eq_zero_iff hwr] at hw0
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hw0
          rcases hw0 with h' | h' | h'
          · rw [h']; exact Finset.mem_singleton_self _
          · rw [h'] at hrw; exact absurd hrw hrq₂
          · rw [h'] at hw
            exact absurd (Or.inl (mem_hubSpokes.mpr (Or.inl ⟨rfl, Finset.mem_erase.mpr
              ⟨fun (h'' : a = z₁) => haT' (h'' ▸ hz₁T), mX₁.mpr (Or.inl rfl)⟩⟩))) hw)
      rw [Finset.card_singleton] at hb
      intro j hj
      rw [Finset.card_erase_of_mem hz₁T, hTc]
      omega)
  obtain ⟨z₂, rfl⟩ := Finset.card_eq_one.mp hZc
  have hz₂T : z₂ ∈ T := (Finset.mem_erase.mp (hZS (Finset.mem_singleton_self _))).2
  have hz₂₁ : z₂ ≠ z₁ := (Finset.mem_erase.mp (hZS (Finset.mem_singleton_self _))).1
  -- the third vertex `s` of `N_T(r)`
  have hTZ : (T \ {z₁, z₂}).card = 1 := by
    rw [Finset.card_sdiff_of_subset (by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hz₁T
      · exact hz₂T), Finset.card_pair (Ne.symm hz₂₁), hTc]
  obtain ⟨s, hTZ'⟩ := Finset.card_eq_one.mp hTZ
  have hs : s ∈ T ∧ s ∉ ({z₁, z₂} : Finset V) := by
    rw [← Finset.mem_sdiff, hTZ']; exact Finset.mem_singleton_self _
  have hsz : s ≠ z₁ ∧ s ≠ z₂ := by
    have := hs.2; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at this; exact this
  have mB : ∀ {v}, v ∈ insert z₁ (({q₂} : Finset V) ∪ {a}) ∪ ({z₂} : Finset V) ↔
      v = a ∨ v = q₂ ∨ v = z₁ ∨ v = z₂ := by
    intro v; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
  have mX₃ : ∀ {v}, v ∈ ((X₀ \ {b}).erase z₁) \ {z₂} ↔ (v = a ∨ v ∈ T) ∧ v ≠ z₁ ∧ v ≠ z₂ := by
    intro v
    rw [Finset.mem_sdiff, Finset.mem_erase, mX₁, Finset.mem_singleton]
    tauto
  -- step 5: `r → s`, at most three blank neighbours (`s ∉ N(a)`)
  have h4 := hub_give h3 {s}
    (by rw [Finset.singleton_subset_iff, mX₃]; exact ⟨Or.inr hs.1, hsz⟩)
    (fun x hx => (Finset.mem_singleton.mp hx) ▸ hadjT s hs.1)
    (fun _ _ => Set.notMem_empty _)
    (by
      rw [Finset.disjoint_singleton_left, mB]
      rintro (h' | h' | h' | h')
      · exact haT' (h' ▸ hs.1)
      · exact hq₂T (h' ▸ hs.1)
      · exact hsz.1 h'
      · exact hsz.2 h')
    (by
      rw [Finset.disjoint_singleton]
      exact fun h' => hq₁T (h' ▸ hs.1))
    3
    (by
      intro x hx
      rw [Finset.mem_singleton.mp hx]
      refine (blankNbrs_hub_le (insert q₂ (insert z₁ {z₂})) ?_).trans
        ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
          (by simp))))
      intro w' hsw _ _ hw0
      by_cases hwr : w' = r
      · rw [hwr, hst_self] at hw0; omega
      · rw [hst_eq_zero_iff hwr, mB] at hw0
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hw0 with h' | hw0
        · rw [h'] at hsw
          exact absurd (hNa s hs.1 hsw.symm) hsz.1
        · exact hw0)
    (by rw [Finset.card_singleton])
  -- step 6: `r → a`, at most two blank neighbours (`N(a) ∩ Z ⊆ {q₂, z₁}`)
  have h5 := hub_pay_one h4 (a := a)
    (by
      rw [Finset.mem_sdiff, mX₃, Finset.mem_singleton]
      exact ⟨⟨Or.inl rfl, fun h' => haT' (h' ▸ hz₁T), fun h' => haT' (h' ▸ hz₂T)⟩,
        fun h' => haT' (h' ▸ hs.1)⟩)
    hra (Set.notMem_empty _) (mB.mpr (Or.inl rfl))
    (by
      rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton, not_or]
      exact ⟨haq₁, fun h' => haT' (h' ▸ hs.1)⟩)
    (by
      refine lt_of_le_of_lt (blankNbrs_hub_le {q₂, z₁} ?_) ?_
      · intro w' haw _ hwa hw0
        by_cases hwr : w' = r
        · rw [hwr, hst_self, Finset.card_singleton] at hw0; omega
        · rw [hst_eq_zero_iff hwr, mB] at hw0
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases hw0 with h' | h' | h' | h'
          · exact absurd h' hwa
          · exact Or.inl h'
          · exact Or.inr h'
          · rw [h'] at haw
            exact absurd (hNa z₂ hz₂T haw) hz₂₁
      · exact lt_of_le_of_lt (Finset.card_insert_le _ _) (by simp))
  -- the end state
  have hXe : (((X₀ \ {b}).erase z₁ \ {z₂}) \ {s}).erase a = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro v hv
    rw [Finset.mem_erase, Finset.mem_sdiff, mX₃, Finset.mem_singleton] at hv
    obtain ⟨hva, ⟨hvaT, hv1, hv2⟩, hvs⟩ := hv
    have hvT : v ∈ T := hvaT.resolve_left hva
    have : v ∈ T \ {z₁, z₂} := by
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hvT, hv1, hv2⟩
    rw [hTZ', Finset.mem_singleton] at this
    exact hvs this
  have hBe : (insert z₁ (({q₂} : Finset V) ∪ {a}) ∪ ({z₂} : Finset V)).erase a = {q₂, z₁, z₂} := by
    ext v
    rw [Finset.mem_erase, mB]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hva, h' | h'⟩
      · exact absurd h' hva
      · exact h'
    · intro h'
      refine ⟨?_, Or.inr h'⟩
      rintro rfl
      rcases h' with h' | h' | h'
      · exact haq₂ h'
      · exact haT' (h' ▸ hz₁T)
      · exact haT' (h' ▸ hz₂T)
  have hDe : ({q₁} : Finset V) ∪ {s} = {q₁, s} := by
    ext v; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  rw [hXe, hubHeld_empty, Set.sdiff_empty, hBe, hDe] at h5
  simp only [Finset.card_singleton] at h5
  have hfin : Ach G.edgeSet (hst r 2 {q₂, z₁, z₂} {q₁, s}) := h5.congr rfl (fun v => rfl)
  have hpos : ∀ v ∈ U, 0 < G.degree v := by
    intro v hv
    by_cases hvr : v = r
    · rw [hvr]; exact G.degree_pos_iff_exists_adj r |>.mpr ⟨a, hra⟩
    · by_cases hv1 : v = q₁
      · rw [hv1]; exact hq₁0
      · by_cases hv2 : v = q₂
        · rw [hv2]; exact hq₂0
        · exact G.degree_pos_iff_exists_adj v |>.mpr ⟨r, (hrT v hv hvr hv1 hv2).symm⟩
  have hsq₁ : s ≠ q₁ := fun h' => hq₁T (h' ▸ hs.1)
  have hreal := realisable_of_hst_root (G := G) U hU hpos hfin hr
    (by
      intro v hvr
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hv
        by_cases hv1 : v = q₁
        · exact Or.inr (Or.inl hv1)
        · by_cases hv2 : v = q₂
          · exact Or.inl (Or.inl hv2)
          · have hvT : v ∈ T := mT.mpr ⟨hv2, hv1, hvr, hv⟩
            by_cases hvz : v = z₁ ∨ v = z₂
            · exact Or.inl (Or.inr hvz)
            · right; right
              have : v ∈ T \ {z₁, z₂} := by
                rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; exact ⟨hvT, hvz⟩
              rw [hTZ', Finset.mem_singleton] at this
              exact this
      · rintro ((rfl | rfl | rfl) | (rfl | rfl))
        · exact hq₂
        · exact (mT.mp hz₁T).2.2.2
        · exact (mT.mp hz₂T).2.2.2
        · exact hq₁
        · exact (mT.mp hs.1).2.2.2)
    (by
      rw [Finset.disjoint_left]
      intro v hv hv'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv hv'
      rcases hv' with rfl | rfl
      · rcases hv with h' | h' | h'
        · exact hq₁₂ h'
        · exact hq₁T (h' ▸ hz₁T)
        · exact hq₁T (h' ▸ hz₂T)
      · rcases hv with h' | h' | h'
        · exact hq₂T (h' ▸ hs.1)
        · exact hsz.1 h'
        · exact hsz.2 h')
  refine ⟨insert r {q₁, s}, ?_, Finset.mem_insert_self _ _, ?_, hreal⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact hr
    · exact hq₁
    · exact (mT.mp hs.1).2.2.2
  · rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hsq₁)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h' => hq₁r h'.symm, fun h' => (mT.mp hs.1).2.2.1 h'.symm⟩

/-- **Theorem 4.1(ii)**, rooted-test form. -/
theorem root_hub_six_Q1_passes (hn : Even (Fintype.card V)) (U : Finset V)
    (hU : ∀ v, v ∈ U ↔ Even (G.degree v)) (hU6 : U.card = 6) {r q : V} (hr : r ∈ U)
    (hq : q ∈ U) (hqr : q ≠ r) (hrT : ∀ t ∈ U, t ≠ r → t ≠ q → G.Adj r t)
    (hrq : ¬ G.Adj r q) (hq0 : 0 < G.degree q) (hdeg : 8 ≤ G.degree r)
    {a b : V} (hra : G.Adj r a) (hrb : G.Adj r b) (hab : G.Adj a b) (haU : a ∉ U) (hbU : b ∉ U)
    (haT : ((U.erase r).filter (G.Adj a)).card ≤ 2) (hbq : ¬ G.Adj b q) : PassesAt G r := by
  obtain ⟨S, -, hrS, hS, hreal⟩ := root_hub_six_Q1 G hn U hU hU6 hr hq hqr hrT hrq hq0 hdeg hra
    hrb hab haU hbU haT hbq
  exact passesAt_of_realisable hreal hrS (by rw [filter_even_eq G hU]; omega)

/-- **Theorem 4.1(iii)**, rooted-test form. -/
theorem root_hub_six_Q2_passes (hn : Even (Fintype.card V)) (U : Finset V)
    (hU : ∀ v, v ∈ U ↔ Even (G.degree v)) (hU6 : U.card = 6) {r q₁ q₂ : V} (hr : r ∈ U)
    (hq₁ : q₁ ∈ U) (hq₂ : q₂ ∈ U) (hq₁r : q₁ ≠ r) (hq₂r : q₂ ≠ r) (hq₁₂ : q₁ ≠ q₂)
    (hrT : ∀ t ∈ U, t ≠ r → t ≠ q₁ → t ≠ q₂ → G.Adj r t)
    (hrq₁ : ¬ G.Adj r q₁) (hrq₂ : ¬ G.Adj r q₂) (hq₁0 : 0 < G.degree q₁)
    (hq₂0 : 0 < G.degree q₂)
    {a b : V} (hra : G.Adj r a) (hrb : G.Adj r b) (hab : G.Adj a b) (haU : a ∉ U) (hbU : b ∉ U)
    (haT : ((((U.erase r).erase q₁).erase q₂).filter (G.Adj a)).card ≤ 1)
    (hbq : ¬ G.Adj b q₂) : PassesAt G r := by
  obtain ⟨S, -, hrS, hS, hreal⟩ := root_hub_six_Q2 G hn U hU hU6 hr hq₁ hq₂ hq₁r hq₂r hq₁₂ hrT
    hrq₁ hrq₂ hq₁0 hq₂0 hra hrb hab haU hbU haT hbq
  exact passesAt_of_realisable hreal hrS (by rw [filter_even_eq G hU]; omega)

end uniform

end Gallai
