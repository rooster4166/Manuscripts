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

end uniform

end Gallai
