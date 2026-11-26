import GallaiLean.Relay
import GallaiLean.Lovasz

/-!
# Hub certificates: held edges, seeds and the five phases (d6-frontier manuscript, §§4–6)

Every certificate of the manuscript has the same shape. Hold a set of edges at a hub `h`, take a
Lovász seed of the rest (Lemma 3.2), and put the held edges back by Fan transfers. This file
provides that machinery for an arbitrary graph `G`, in the edge-set form `Ach` of
`Insertion.lean`.

**Held edges.** `hubHeld h X C` is the set of spokes `s(h, x)` (`x ∈ X`) together with a set `C`
of further edges. The battery chords of a list `L` of pairs `(a, b)` (parked vertex `a`, partner
`b`) are `batChords L = {s(b, a)}`. The current graph is always `G.edgeSet \ hubHeld h X C`.

**End vectors.** `hst h N B D` has `N` ends at the hub, none on `B` (the blank vertices), two on
`D` (the doubled vertices) and one everywhere else.

**Seeds** (Lemma 3.2). `seed_pair` (two even vertices: double one, leave the other blank; from
`realisable_evenSet_erase'`) and `seed_odd` (no even vertex: one end everywhere; from
`lovasz_ends`). `degree_hubDel` computes the degrees after deleting `hubHeld h X (batChords L)`.

**Phases** (each keeps the form `Ach (G.edgeSet \ hubHeld h X C) (hst h N B D)`):

* `hub_take`: a single receipt `t → h` from an unblank `t`;
* `hub_receive`: `m` grouped receipts at `h` from a set `S` (`Ach.receiveMany`);
* `hub_give`: donations from `h` to a set `R` of vertices with one end (`Ach.giveAll`);
* `hub_payback`: donations from `h` to a set `P` of blank vertices whose blank neighbours lie in
  `P` (`Ach.giveAll`); `hub_pay_one`: a single payback with an explicit blank count;
* `hub_batteries`: the carries `b → h`, `a → b` of a list of batteries (`Ach.carry`).
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u} [DecidableEq V]

/-- The held edges: spokes from `h` to `X`, and the further edges `C`. -/
def hubHeld (h : V) (X : Finset V) (C : Set (Sym2 V)) : Set (Sym2 V) := hubSpokes h X ∪ C

/-- The hub end vector: `N` at the hub `h`, `0` on `B`, `2` on `D`, `1` elsewhere. -/
def hst (h : V) (N : ℕ) (B D : Finset V) (v : V) : ℕ :=
  if v = h then N else if v ∈ B then 0 else if v ∈ D then 2 else 1

/-- The chords `s(b, a)` of a list of batteries `(a, b)`. -/
def batChords (L : List (V × V)) : Set (Sym2 V) := {e | ∃ p ∈ L, e = s(p.2, p.1)}

/-- `r` **passes** the rooted two-end test in `G`: some path decomposition has at most `|V|/2`
paths and at least two ends at `r`. -/
def PassesAt [Fintype V] (G : SimpleGraph V) (r : V) : Prop :=
  ∃ D : PathDecomp G, D.size ≤ Fintype.card V / 2 ∧ 2 ≤ D.ends r

theorem hst_self (h : V) (N : ℕ) (B D : Finset V) : hst h N B D h = N := by simp [hst]

theorem hst_of_ne {h v : V} (N : ℕ) (B D : Finset V) (hv : v ≠ h) :
    hst h N B D v = if v ∈ B then 0 else if v ∈ D then 2 else 1 := by simp [hst, hv]

theorem hst_eq_zero_iff {h v : V} {N : ℕ} {B D : Finset V} (hv : v ≠ h) :
    hst h N B D v = 0 ↔ v ∈ B := by
  rw [hst_of_ne N B D hv]; split_ifs <;> simp_all

theorem hst_one {h v : V} {N : ℕ} {B D : Finset V} (hv : v ≠ h) (hB : v ∉ B) (hD : v ∉ D) :
    hst h N B D v = 1 := by
  rw [hst_of_ne N B D hv]; simp [hB, hD]

omit [DecidableEq V] in
theorem mem_hubSpokes {h v w : V} {X : Finset V} :
    s(v, w) ∈ hubSpokes h X ↔ (v = h ∧ w ∈ X) ∨ (w = h ∧ v ∈ X) := by
  simp only [hubSpokes, Set.mem_ofPred_eq, Sym2.eq_iff]
  constructor
  · rintro ⟨z, hz, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact Or.inl ⟨rfl, hz⟩
    · exact Or.inr ⟨rfl, hz⟩
  · rintro (⟨rfl, hw⟩ | ⟨rfl, hv⟩)
    · exact ⟨w, hw, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨v, hv, Or.inr ⟨rfl, rfl⟩⟩

omit [DecidableEq V] in
theorem mem_hubE {G : SimpleGraph V} {h v w : V} {X : Finset V} {C : Set (Sym2 V)} :
    s(v, w) ∈ G.edgeSet \ hubHeld h X C ↔
      G.Adj v w ∧ ¬ ((v = h ∧ w ∈ X) ∨ (w = h ∧ v ∈ X)) ∧ s(v, w) ∉ C := by
  simp only [hubHeld, Set.mem_sdiff, Set.mem_union, mem_edgeSet, mem_hubSpokes, not_or]

omit [DecidableEq V] in
theorem spoke_notMem_hubE {G : SimpleGraph V} {h x : V} {X : Finset V} {C : Set (Sym2 V)}
    (hx : x ∈ X) : s(x, h) ∉ G.edgeSet \ hubHeld h X C := by
  rw [mem_hubE]; tauto

omit [DecidableEq V] in
theorem spoke_notMem_hubE' {G : SimpleGraph V} {h x : V} {X : Finset V} {C : Set (Sym2 V)}
    (hx : x ∈ X) : s(h, x) ∉ G.edgeSet \ hubHeld h X C := by
  rw [mem_hubE]; tauto

/-- Inserting spokes: the held set loses them. -/
theorem hubE_union_spokes {G : SimpleGraph V} {h : V} {X Z : Finset V} {C : Set (Sym2 V)}
    (_hZX : Z ⊆ X) (hZ : ∀ z ∈ Z, G.Adj h z) (hZC : ∀ z ∈ Z, s(h, z) ∉ C) :
    (G.edgeSet \ hubHeld h X C) ∪ hubSpokes h Z = G.edgeSet \ hubHeld h (X \ Z) C := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
  rw [Set.mem_union, mem_hubE, mem_hubE, mem_hubSpokes]
  simp only [Finset.mem_sdiff]
  constructor
  · rintro (⟨hab, h1, h2⟩ | ⟨rfl, hb⟩ | ⟨rfl, ha⟩)
    · exact ⟨hab, fun h' => h1 (by tauto), h2⟩
    · refine ⟨hZ b hb, ?_, hZC b hb⟩
      rintro (⟨-, -, hb'⟩ | ⟨rfl, -⟩)
      · exact hb' hb
      · exact (hZ _ hb).ne rfl
    · refine ⟨(hZ a ha).symm, ?_, by rw [Sym2.eq_swap]; exact hZC a ha⟩
      rintro (⟨rfl, -⟩ | ⟨-, -, ha'⟩)
      · exact (hZ _ ha).ne rfl
      · exact ha' ha
  · rintro ⟨hab, h1, h2⟩
    by_cases hz : (a = h ∧ b ∈ Z) ∨ (b = h ∧ a ∈ Z)
    · exact Or.inr hz
    · left
      refine ⟨hab, ?_, h2⟩
      rintro (⟨rfl, hb⟩ | ⟨rfl, ha⟩)
      · exact h1 (Or.inl ⟨rfl, hb, fun hbZ => hz (Or.inl ⟨rfl, hbZ⟩)⟩)
      · exact h1 (Or.inr ⟨rfl, ha, fun haZ => hz (Or.inr ⟨rfl, haZ⟩)⟩)

omit [DecidableEq V] in
theorem hubHeld_empty (h : V) : hubHeld h (∅ : Finset V) (∅ : Set (Sym2 V)) = ∅ := by
  simp [hubHeld, hubSpokes_empty]

/-! ### Seeds -/

/-- A decomposition of `G − K` is an `Ach` for the edge set `E(G) \ K`. -/
theorem ach_of_deleteEdges {G : SimpleGraph V} {K : Set (Sym2 V)} {b : V → ℕ}
    (h : ∃ D : PathDecomp (G.deleteEdges K), ∀ v, D.ends v = b v) : Ach (G.edgeSet \ K) b := by
  have hG : fromEdgeSet (G.edgeSet \ K) = G.deleteEdges K := by
    ext v w
    simp only [fromEdgeSet_adj, Set.mem_sdiff, mem_edgeSet, deleteEdges_adj]
    exact ⟨fun h => h.1, fun h => ⟨h, h.1.ne⟩⟩
  unfold Ach
  rw [hG]
  exact h

/-- An `Ach` for the whole edge set is a decomposition of `G`. -/
theorem pathDecomp_of_ach {G : SimpleGraph V} {b : V → ℕ} (h : Ach G.edgeSet b) :
    ∃ D : PathDecomp G, ∀ v, D.ends v = b v := by
  unfold Ach at h
  rwa [fromEdgeSet_edgeSet] at h

section seeds

variable [Fintype V]

/-- **Seed (b)** (Lemma 3.2(b)): at even order, with no isolated vertex and exactly two even
vertices `h, y`, there is a decomposition with two ends at `h`, none at `y`, one elsewhere. -/
theorem seed_pair (K : SimpleGraph V) [DecidableRel K.Adj] (hn : Even (Fintype.card V))
    (hpos : ∀ v, 0 < K.degree v) {h y : V} (hhy : h ≠ y)
    (hev : ∀ v, Even (K.degree v) ↔ v = h ∨ v = y) :
    ∃ D : PathDecomp K, ∀ v, D.ends v = hst h 2 {y} ∅ v := by
  have hEv : evenSet K = {h, y} := by
    ext v
    simp only [evenSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    rw [← hev v]
    exact ⟨fun h => h.2, fun h' => ⟨hpos v, h'⟩⟩
  have hy : y ∈ evenSet K := by rw [hEv]; simp
  obtain ⟨-, D, hD⟩ := realisable_evenSet_erase' hpos hn hy
  refine ⟨D, fun v => ?_⟩
  rw [hD v, hEv]
  unfold profile hst
  have hyy : ({h, y} : Finset V).erase y = {h} := by
    ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact h2
      · exact absurd h2 h1
    · rintro rfl; exact ⟨hhy, Or.inl rfl⟩
  rw [hyy]
  by_cases hvh : v = h
  · subst hvh
    have : ¬ Odd (K.degree v) := Nat.not_odd_iff_even.mpr ((hev v).mpr (Or.inl rfl))
    simp [this]
  · by_cases hvy : v = y
    · subst hvy
      have : ¬ Odd (K.degree v) := Nat.not_odd_iff_even.mpr ((hev v).mpr (Or.inr rfl))
      simp [this, hvh]
    · have : Odd (K.degree v) := Nat.not_even_iff_odd.mp (fun h' => by
        rcases (hev v).mp h' with h1 | h1 <;> contradiction)
      simp [this, hvh, hvy]

/-- **Seed (a)** (Lemma 3.2(a)): if every vertex is odd there is a decomposition with one end
everywhere. -/
theorem seed_odd (K : SimpleGraph V) [DecidableRel K.Adj] (hodd : ∀ v, Odd (K.degree v))
    (h : V) : ∃ D : PathDecomp K, ∀ v, D.ends v = hst h 1 ∅ ∅ v := by
  have hEv : evenSet K = ∅ := by
    ext v
    simp only [evenSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false, not_and]
    exact fun _ h' => (Nat.not_even_iff_odd.mpr (hodd v)) h'
  obtain ⟨D, hD⟩ := lovasz_ends K (by rw [hEv]; simp)
  refine ⟨D, fun v => ?_⟩
  rw [hD v, Nat.odd_iff.mp (hodd v)]
  unfold hst
  split_ifs <;> simp_all

/-- Degrees after deleting the held spokes `h–X` and the chords of a battery list `L`. -/
theorem degree_hubDel (G : SimpleGraph V) [DecidableRel G.Adj] (h : V) (X : Finset V)
    (L : List (V × V)) [DecidableRel (G.deleteEdges (hubHeld h X (batChords L))).Adj]
    (hX : ∀ x ∈ X, G.Adj h x) (hnd : (h :: (L.map Prod.fst ++ L.map Prod.snd)).Nodup)
    (hch : ∀ p ∈ L, G.Adj p.2 p.1) (v : V) :
    (G.deleteEdges (hubHeld h X (batChords L))).degree v + (if v = h then X.card else 0) +
      (if v ∈ X then 1 else 0) +
      (if v ∈ L.map Prod.fst ∨ v ∈ L.map Prod.snd then 1 else 0) = G.degree v := by
  classical
  have hhX : h ∉ X := fun hh => (hX h hh).ne rfl
  have hh : h ∉ L.map Prod.fst ++ L.map Prod.snd := (List.nodup_cons.mp hnd).1
  have hnd2 := List.nodup_append.mp (List.nodup_cons.mp hnd).2
  have hfst := List.inj_on_of_nodup_map hnd2.1
  have hsnd := List.inj_on_of_nodup_map hnd2.2.1
  have hdisj : ∀ p ∈ L, ∀ q ∈ L, p.1 ≠ q.2 := fun p hp q hq =>
    hnd2.2.2 p.1 (List.mem_map_of_mem hp) q.2 (List.mem_map_of_mem hq)
  -- the chord neighbours of `v`
  have hchord : ∀ w, s(v, w) ∈ batChords L ↔
      ∃ p ∈ L, (v = p.2 ∧ w = p.1) ∨ (v = p.1 ∧ w = p.2) := by
    intro w
    simp only [batChords, Set.mem_ofPred_eq, Sym2.eq_iff]
  have hchG : ∀ w, s(v, w) ∈ batChords L → G.Adj v w := by
    intro w hw
    obtain ⟨p, hp, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (hchord w).mp hw
    · exact hch p hp
    · exact (hch p hp).symm
  have hchh : ∀ w, s(v, w) ∈ batChords L → v ≠ h ∧ w ≠ h := by
    intro w hw
    have hm1 : ∀ p ∈ L, p.1 ∈ L.map Prod.fst ++ L.map Prod.snd := fun p hp =>
      List.mem_append_left _ (List.mem_map_of_mem hp)
    have hm2 : ∀ p ∈ L, p.2 ∈ L.map Prod.fst ++ L.map Prod.snd := fun p hp =>
      List.mem_append_right _ (List.mem_map_of_mem hp)
    obtain ⟨p, hp, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (hchord w).mp hw
    · exact ⟨fun h' => hh (h' ▸ hm2 p hp), fun h' => hh (h' ▸ hm1 p hp)⟩
    · exact ⟨fun h' => hh (h' ▸ hm1 p hp), fun h' => hh (h' ▸ hm2 p hp)⟩
  have key : ∀ w, (if G.Adj v w then 1 else 0) = (if (G.deleteEdges (hubHeld h X (batChords L))).Adj v w then 1 else 0) +
      ((if v = h ∧ w ∈ X then 1 else 0) + (if w = h ∧ v ∈ X then 1 else 0) +
        (if s(v, w) ∈ batChords L then 1 else 0)) := by
    intro w
    have hG₀ : (G.deleteEdges (hubHeld h X (batChords L))).Adj v w ↔ G.Adj v w ∧ ¬ ((v = h ∧ w ∈ X) ∨ (w = h ∧ v ∈ X)) ∧
        s(v, w) ∉ batChords L := by
      simp only [deleteEdges_adj, hubHeld, Set.mem_union, mem_hubSpokes, not_or]
    by_cases h1 : v = h ∧ w ∈ X
    · have hadj : G.Adj v w := h1.1 ▸ hX w h1.2
      have h2 : ¬ (w = h ∧ v ∈ X) := fun h2 => hhX (h1.1 ▸ h2.2)
      have h3 : s(v, w) ∉ batChords L := fun h3 => (hchh w h3).1 h1.1
      have h4 : ¬ (G.deleteEdges (hubHeld h X (batChords L))).Adj v w := fun h4 => (hG₀.mp h4).2.1 (Or.inl h1)
      rw [ite_eq_left hadj, ite_eq_right h4, ite_eq_left h1, ite_eq_right h2, ite_eq_right h3]
    · by_cases h2 : w = h ∧ v ∈ X
      · have hadj : G.Adj v w := h2.1 ▸ (hX v h2.2).symm
        have h3 : s(v, w) ∉ batChords L := fun h3 => (hchh w h3).2 h2.1
        have h4 : ¬ (G.deleteEdges (hubHeld h X (batChords L))).Adj v w := fun h4 => (hG₀.mp h4).2.1 (Or.inr h2)
        rw [ite_eq_left hadj, ite_eq_right h4, ite_eq_right h1, ite_eq_left h2, ite_eq_right h3]
      · by_cases h3 : s(v, w) ∈ batChords L
        · have hadj := hchG w h3
          have h4 : ¬ (G.deleteEdges (hubHeld h X (batChords L))).Adj v w := fun h4 => (hG₀.mp h4).2.2 h3
          rw [ite_eq_left hadj, ite_eq_right h4, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
        · have h4 : (G.deleteEdges (hubHeld h X (batChords L))).Adj v w ↔ G.Adj v w := by rw [hG₀]; tauto
          rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
          by_cases hadj : G.Adj v w
          · rw [ite_eq_left hadj, ite_eq_left (h4.mpr hadj)]
          · rw [ite_eq_right hadj, ite_eq_right (fun h' => hadj (h4.mp h'))]
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree, neighborFinset_eq_filter,
    neighborFinset_eq_filter (G := G), Finset.card_filter, Finset.card_filter,
    Finset.sum_congr rfl (fun w _ => key w), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have s1 : ∑ w, (if v = h ∧ w ∈ X then 1 else 0) = if v = h then X.card else 0 := by
    by_cases hv : v = h
    · simp only [hv, true_and, ite_true]
      rw [← Finset.card_filter]
      congr 1; ext w; simp
    · simp [hv]
  have s2 : ∑ w, (if w = h ∧ v ∈ X then 1 else 0) = if v ∈ X then 1 else 0 := by
    by_cases hv : v ∈ X
    · simp [hv]
    · simp [hv]
  have s3 : ∑ w, (if s(v, w) ∈ batChords L then 1 else 0) =
      if v ∈ L.map Prod.fst ∨ v ∈ L.map Prod.snd then 1 else 0 := by
    rw [← Finset.card_filter]
    by_cases hv1 : v ∈ L.map Prod.fst
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv1
      have : Finset.univ.filter (fun w => s(p.1, w) ∈ batChords L) = {p.2} := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          hchord]
        constructor
        · rintro ⟨q, hq, ⟨h1, -⟩ | ⟨h1, rfl⟩⟩
          · exact absurd h1 (hdisj p hp q hq)
          · rw [hfst hp hq h1]
        · rintro rfl; exact ⟨p, hp, Or.inr ⟨rfl, rfl⟩⟩
      rw [this, ite_eq_left (Or.inl hv1)]; rfl
    · by_cases hv2 : v ∈ L.map Prod.snd
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv2
        have : Finset.univ.filter (fun w => s(p.2, w) ∈ batChords L) = {p.1} := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
            hchord]
          constructor
          · rintro ⟨q, hq, ⟨h1, rfl⟩ | ⟨h1, -⟩⟩
            · rw [hsnd hp hq h1]
            · exact absurd h1.symm (hdisj q hq p hp)
          · rintro rfl; exact ⟨p, hp, Or.inl ⟨rfl, rfl⟩⟩
        rw [this, ite_eq_left (Or.inr hv2)]; rfl
      · rw [ite_eq_right (by tauto), Finset.card_eq_zero]
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, hchord]
        rintro ⟨p, hp, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
        · exact hv2 (List.mem_map_of_mem hp)
        · exact hv1 (List.mem_map_of_mem hp)
  rw [s1, s2, s3]
  omega

end seeds

/-! ### The phases -/

section phases

variable [Fintype V] {G : SimpleGraph V} {h : V} {X : Finset V} {C : Set (Sym2 V)}
  {N : ℕ} {B D : Finset V}

/-- A blank count for the current graph, from a set containing the blank neighbours. -/
theorem blankNbrs_hub_le {v : V} (Y : Finset V)
    (hY : ∀ w, G.Adj v w → s(v, w) ∉ hubHeld h X C → w ≠ v → hst h N B D w = 0 → w ∈ Y) :
    blankNbrs (G.edgeSet \ hubHeld h X C) (hst h N B D) v ≤ Y.card := by
  rw [← Set.ncard_coe_finset]
  apply blankNbrs_le_of_subset
  intro w hw hwv hw0
  rw [Set.mem_sdiff] at hw
  exact hY w hw.1 hw.2 hwv hw0

/-- **Single receipt** `t → h`, when `h` has no blank neighbour. -/
theorem hub_take (hA : Ach (G.edgeSet \ hubHeld h X C) (hst h N B D)) {t : V} (htX : t ∈ X)
    (hht : G.Adj h t) (htC : s(h, t) ∉ C) (htB : t ∉ B) (htD : t ∉ D)
    (hbl : blankNbrs (G.edgeSet \ hubHeld h X C) (hst h N B D) h = 0) :
    Ach (G.edgeSet \ hubHeld h (X.erase t) C) (hst h (N + 1) (insert t B) D) := by
  have hth : t ≠ h := hht.ne.symm
  have h1 := hA.transfer hth (spoke_notMem_hubE htX)
    (by rw [hbl, hst_one hth htB htD]; omega)
  refine h1.congr ?_ (fun v => ?_)
  · rw [← Finset.sdiff_singleton_eq_erase, ← hubE_union_spokes (by simpa using htX)
      (by simpa using hht) (by simpa using htC)]
    ext e
    simp [hubSpokes, Sym2.eq_swap]
  · unfold mv hst
    by_cases hvh : v = h
    · subst hvh; simp
    · by_cases hvt : v = t
      · subst hvt; simp [hvh, htB, htD]
      · simp [hvh, hvt]

/-- **Grouped receipts** at `h` from `S` (Remark 3.4): `m` receipts, the `j`-th with supply
`|S| − j` against at most `bl(h) + j` blank neighbours. -/
theorem hub_receive (hA : Ach (G.edgeSet \ hubHeld h X C) (hst h N B D)) (S : Finset V)
    (hSX : S ⊆ X) (hS : ∀ t ∈ S, G.Adj h t) (hSC : ∀ t ∈ S, s(h, t) ∉ C) (hSB : Disjoint S B)
    (hSD : Disjoint S D) (m : ℕ)
    (hm : ∀ j < m, blankNbrs (G.edgeSet \ hubHeld h X C) (hst h N B D) h + j < S.card - j) :
    ∃ Z ⊆ S, Z.card = m ∧ Ach (G.edgeSet \ hubHeld h (X \ Z) C) (hst h (N + m) (B ∪ Z) D) := by
  have hhS : h ∉ S := fun hh => (hS h hh).ne rfl
  obtain ⟨Z, hZS, hZc, hZ⟩ := hA.receiveMany h S hhS (fun t ht => spoke_notMem_hubE (hSX ht))
    (fun t ht => hst_one (fun h' => hhS (h' ▸ ht)) (Finset.disjoint_left.mp hSB ht)
      (Finset.disjoint_left.mp hSD ht)) m hm
  refine ⟨Z, hZS, hZc, hZ.congr (hubE_union_spokes (hZS.trans hSX) (fun z hz => hS z (hZS hz))
    (fun z hz => hSC z (hZS hz))) (fun v => ?_)⟩
  unfold recvEnds hst
  rw [hZc]
  by_cases hvh : v = h
  · simp [hvh]
  · by_cases hvZ : v ∈ Z
    · have h1 : v ∉ B := Finset.disjoint_left.mp hSB (hZS hvZ)
      have h2 : v ∉ D := Finset.disjoint_left.mp hSD (hZS hvZ)
      simp [hvh, hvZ, h1, h2]
    · simp [hvh, hvZ]

/-- **Donations** from `h` to every vertex of `R` (each with one end), in any order: every
receiver has at most `c` blank neighbours, and `c + |R| ≤ N`. -/
theorem hub_give (hA : Ach (G.edgeSet \ hubHeld h X C) (hst h N B D)) (R : Finset V)
    (hRX : R ⊆ X) (hR : ∀ a ∈ R, G.Adj h a) (hRC : ∀ a ∈ R, s(h, a) ∉ C) (hRB : Disjoint R B)
    (hRD : Disjoint R D) (c : ℕ)
    (hc : ∀ a ∈ R, blankNbrs (G.edgeSet \ hubHeld h X C) (hst h N B D) a ≤ c)
    (hN : c + R.card ≤ N) :
    Ach (G.edgeSet \ hubHeld h (X \ R) C) (hst h (N - R.card) B (D ∪ R)) := by
  have hhR : h ∉ R := fun hh => (hR h hh).ne rfl
  have h1 := hA.giveAll h R hhR (fun a ha => spoke_notMem_hubE' (hRX ha)) c
    (fun a ha => by
      refine le_trans ?_ (hc a ha)
      unfold blankNbrs
      exact Set.ncard_le_ncard (fun w hw => ⟨hw.1, hw.2.1, hw.2.2.1⟩) (Set.toFinite _))
    (by rwa [hst_self])
  refine h1.congr (hubE_union_spokes hRX hR hRC) (fun v => ?_)
  unfold giveEnds hst
  by_cases hvh : v = h
  · simp [hvh]
  · by_cases hvR : v ∈ R
    · have h1 : v ∉ B := Finset.disjoint_left.mp hRB hvR
      have h2 : v ∉ D := Finset.disjoint_left.mp hRD hvR
      simp [hvh, hvR, h1, h2]
    · simp [hvh, hvR]

/-- **Paybacks** from `h` to a set `P` of blank vertices whose blank neighbours all lie in `P`:
`|P| ≤ N` suffices. -/
theorem hub_payback (hA : Ach (G.edgeSet \ hubHeld h X C) (hst h N B D)) (P : Finset V)
    (hPX : P ⊆ X) (hP : ∀ a ∈ P, G.Adj h a) (hPC : ∀ a ∈ P, s(h, a) ∉ C) (hPB : P ⊆ B)
    (hPD : Disjoint P D) (hq : ∀ a ∈ P, ∀ w ∈ B, G.Adj a w → w ∈ P) (hN : P.card ≤ N) :
    Ach (G.edgeSet \ hubHeld h (X \ P) C) (hst h (N - P.card) (B \ P) D) := by
  have hhP : h ∉ P := fun hh => (hP h hh).ne rfl
  have h1 := hA.giveAll h P hhP (fun a ha => spoke_notMem_hubE' (hPX ha)) 0
    (by
      intro a ha
      rw [Nat.le_zero, Set.ncard_eq_zero]
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hw hwa hw0 hwP
      have hah : a ≠ h := fun h' => hhP (h' ▸ ha)
      by_cases hwh : w = h
      · subst hwh
        exact spoke_notMem_hubE (hPX ha) hw
      · rw [hst_eq_zero_iff hwh] at hw0
        rw [mem_hubE] at hw
        exact hwP (hq a ha w hw0 hw.1))
    (by rwa [hst_self, zero_add])
  refine h1.congr (hubE_union_spokes hPX hP hPC) (fun v => ?_)
  unfold giveEnds hst
  by_cases hvh : v = h
  · simp [hvh]
  · by_cases hvP : v ∈ P
    · have h2 : v ∉ D := Finset.disjoint_left.mp hPD hvP
      simp [hvh, hvP, hPB hvP, h2]
    · simp [hvh, hvP]

/-- **A single payback** `h → a` to a blank vertex `a`, with an explicit blank count. -/
theorem hub_pay_one (hA : Ach (G.edgeSet \ hubHeld h X C) (hst h N B D)) {a : V} (haX : a ∈ X)
    (ha : G.Adj h a) (haC : s(h, a) ∉ C) (haB : a ∈ B) (haD : a ∉ D)
    (hbl : blankNbrs (G.edgeSet \ hubHeld h X C) (hst h N B D) a < N) :
    Ach (G.edgeSet \ hubHeld h (X.erase a) C) (hst h (N - 1) (B.erase a) D) := by
  have hha : h ≠ a := ha.ne
  have h1 := hA.transfer hha (spoke_notMem_hubE' haX) (by rwa [hst_self])
  refine h1.congr ?_ (fun v => ?_)
  · rw [← Finset.sdiff_singleton_eq_erase, ← hubE_union_spokes (by simpa using haX)
      (by simpa using ha) (by simpa using haC)]
    ext e
    simp [hubSpokes]
  · unfold mv hst
    by_cases hvh : v = h
    · subst hvh; simp [hha]
    · by_cases hva : v = a
      · subst hva; simp [hvh, haB, haD]
      · simp [hvh, hva]

end phases

end Gallai
