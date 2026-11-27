import GallaiLean.ConjN

/-!
# Fan's lemma with a protected path, and the target-in-A move

Manuscript `manuscripts/conj-n`, Lemma 3.2 (in the form with ends outside `{t, u} ∪ N(u)`) and
Theorem 3.3, move (x).

* **`fan_single_protected_path`** (Fan's lemma keeping a path). Let `G' = G − ut`, let `D'`
  decompose `G'` with Fan's inequality `#{w ∈ N_{G'}(u) : ends w = 0} < ends t`, and let `P ∈ D'`
  have no end in `{t, u} ∪ N_{G'}(u)`. Then `G` has a decomposition that moves one end from `t` to
  `u` and contains `P` itself (same ends, same support). Proof: remove `P`
  (`PathDecomp.erase_path`), apply `fan_single` to the rest, add `P` back
  (`PathDecomp.add_path`).
* **`avoidFar_target`** (move (x)): for `u ∈ N(g) ∖ N[c]`, with `u` allowed in the forbidden set,
  a Lovász decomposition of `G − gu` whose path ending at `c` avoids `A` and whose far end is not
  in `B ∪ N_G(u)` gives one of `G` whose path ending at `c` avoids `A` and has far end not in `B`.
-/

open SimpleGraph

namespace Gallai

universe u

section rebuild2

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `exists_decomp_of_edgesM'`, with both directions of the correspondence of paths. -/
theorem exists_decomp_of_edgesM_both (L : List (TPath V)) (h : edgesM L = G.edgeFinset.val) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = endsL L v) ∧
      ∀ P ∈ L, ∃ Q ∈ D.paths, Q.src = P.src ∧ Q.tgt = P.tgt ∧
        Q.walk.support = P.walk.support := by
  have hmem : ∀ P ∈ L, ∀ e ∈ P.walk.edges, e ∈ G.edgeSet := by
    intro P hP e he
    have : e ∈ edgesM L := mem_edgesM.mpr ⟨P, hP, he⟩
    rw [h, Finset.mem_val, mem_edgeFinset] at this
    exact this
  let L' := L.pmap (fun P hP => P.ofTop G hP) hmem
  have hfl : ∀ (l : List (TPath V)) (hl : ∀ P ∈ l, ∀ e ∈ P.walk.edges, e ∈ G.edgeSet),
      (l.pmap (fun P hP => P.ofTop G hP) hl).flatMap GPath.edges = l.flatMap GPath.edges ∧
      ∀ v, ((l.pmap (fun P hP => P.ofTop G hP) hl).map (fun P => P.endsAt v)).sum = endsL l v := by
    intro l hl
    induction l with
    | nil => simp
    | cons P l ih =>
      obtain ⟨ih1, ih2⟩ := ih (fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ))
      refine ⟨?_, fun v => ?_⟩
      · simp [List.pmap, ih1]
      · simp [List.pmap, ih2 v]
  obtain ⟨h1, h2⟩ := hfl L hmem
  have hnd : (L.flatMap GPath.edges).Nodup := by
    have := G.edgeFinset.nodup
    rw [← h] at this
    exact Multiset.coe_nodup.mp this
  refine ⟨⟨L', by rw [h1]; exact hnd, fun e => ?_⟩, h2, fun P hP => ?_⟩
  · rw [h1, ← mem_edgeFinset, ← Finset.mem_val, ← h, edgesM, Multiset.mem_coe]
  · exact ⟨P.ofTop G (hmem P hP), List.mem_pmap.mpr ⟨P, hP, rfl⟩, rfl, rfl,
      Walk.support_transfer _ _⟩

end rebuild2

section delEdgeList

variable {V : Type u} [DecidableEq V]

/-- `K` with the edges of a list removed. -/
def delEdgeList (K : SimpleGraph V) (S : List (Sym2 V)) : SimpleGraph V where
  Adj x y := K.Adj x y ∧ s(x, y) ∉ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun x h => K.loopless.irrefl x h.1⟩

instance delEdgeList.decRel (K : SimpleGraph V) [DecidableRel K.Adj] (S : List (Sym2 V)) :
    DecidableRel (delEdgeList K S).Adj := fun x y =>
  inferInstanceAs (Decidable (K.Adj x y ∧ s(x, y) ∉ S))

omit [DecidableEq V] in
theorem delEdgeList_edgeSet (K : SimpleGraph V) (S : List (Sym2 V)) (e : Sym2 V) :
    e ∈ (delEdgeList K S).edgeSet ↔ e ∈ K.edgeSet ∧ e ∉ S := by
  induction e using Sym2.inductionOn with
  | hf x y => exact Iff.rfl

end delEdgeList

section erase

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Removing a path** from a decomposition leaves a decomposition of the graph without its
edges, with the ends of the path removed. -/
theorem PathDecomp.erase_path {K : SimpleGraph V} [DecidableRel K.Adj] (D : PathDecomp K)
    {P : GPath K} (hP : P ∈ D.paths) :
    ∃ D' : PathDecomp (delEdgeList K P.edges), ∀ v, D'.ends v + P.endsAt v = D.ends v := by
  classical
  set L := (D.paths.erase P).map GPath.toTop with hL
  have hperm : (D.paths.map GPath.toTop).Perm (P.toTop :: L) := by
    have := (List.perm_cons_erase hP).map GPath.toTop
    simpa [hL] using this
  have hsplit : (P.edges : Multiset (Sym2 V)) + edgesM L = K.edgeFinset.val := by
    rw [← D.edgesM_toTop, edgesM_perm hperm, edgesM_cons, GPath.toTop_edges]
  have hndall : ((P.edges : Multiset (Sym2 V)) + edgesM L).Nodup := by
    rw [hsplit]; exact K.edgeFinset.nodup
  have hnd : (edgesM L).Nodup :=
    Multiset.nodup_of_le (Multiset.le_add_left _ _) hndall
  have hdisj : ∀ e ∈ edgesM L, e ∉ P.edges := by
    intro e he hPe
    rw [Multiset.nodup_add] at hndall
    exact Multiset.disjoint_left.mp hndall.2.2 (Multiset.mem_coe.mpr hPe) he
  have hEL : edgesM L = (delEdgeList K P.edges).edgeFinset.val := by
    refine (Multiset.Nodup.ext hnd (Finset.nodup _)).mpr fun e => ?_
    rw [Finset.mem_val, mem_edgeFinset, delEdgeList_edgeSet]
    constructor
    · intro he
      refine ⟨?_, hdisj e he⟩
      have : e ∈ K.edgeFinset.val := by
        rw [← hsplit]; exact Multiset.mem_add.mpr (Or.inr he)
      rwa [Finset.mem_val, mem_edgeFinset] at this
    · rintro ⟨heK, heP⟩
      have : e ∈ K.edgeFinset.val := by rwa [Finset.mem_val, mem_edgeFinset]
      rw [← hsplit, Multiset.mem_add] at this
      rcases this with h | h
      · exact absurd (Multiset.mem_coe.mp h) heP
      · exact h
  obtain ⟨D', hD', -⟩ := exists_decomp_of_edgesM' (G := delEdgeList K P.edges) L hEL
  refine ⟨D', fun v => ?_⟩
  rw [hD' v, ← D.endsL_toTop v, endsL_perm hperm, endsL_cons, GPath.toTop_endsAt]
  omega

/-- **Adding a path** to a decomposition of the graph without its edges. -/
theorem PathDecomp.add_path {G K : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel K.Adj]
    (P : TPath V) (hPG : ∀ e ∈ P.edges, e ∈ G.edgeSet)
    (hK : ∀ e, e ∈ K.edgeSet ↔ e ∈ G.edgeSet ∧ e ∉ P.edges) (D : PathDecomp K) :
    ∃ D' : PathDecomp G, (∀ v, D'.ends v = P.endsAt v + D.ends v) ∧
      ∃ Q ∈ D'.paths, Q.src = P.src ∧ Q.tgt = P.tgt ∧ Q.walk.support = P.walk.support := by
  classical
  set L := P :: D.paths.map GPath.toTop with hL
  have hPnd : P.edges.Nodup := P.isPath.edges_nodup
  have hEL : edgesM L = G.edgeFinset.val := by
    rw [hL, edgesM_cons, D.edgesM_toTop]
    refine (Multiset.Nodup.ext ?_ (Finset.nodup _)).mpr fun e => ?_
    · rw [Multiset.nodup_add]
      refine ⟨Multiset.coe_nodup.mpr hPnd, Finset.nodup _, Multiset.disjoint_left.mpr ?_⟩
      intro e h1 h2
      rw [Finset.mem_val, mem_edgeFinset, hK] at h2
      exact h2.2 (Multiset.mem_coe.mp h1)
    · rw [Multiset.mem_add, Finset.mem_val, Finset.mem_val, mem_edgeFinset, mem_edgeFinset, hK,
        Multiset.mem_coe]
      constructor
      · rintro (h | h)
        · exact hPG e h
        · exact h.1
      · intro h
        by_cases hp : e ∈ P.edges
        · exact Or.inl hp
        · exact Or.inr ⟨h, hp⟩
  obtain ⟨D', hD', hall⟩ := exists_decomp_of_edgesM_both L hEL
  refine ⟨D', fun v => ?_, hall P (List.mem_cons_self ..)⟩
  rw [hD' v, hL, endsL_cons, D.endsL_toTop]

end erase

section protectedFan

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Fan's lemma with a protected path** (manuscript Lemma 3.2, ends outside `{t, u} ∪ N(u)`).
Let `G' = G − ut` and `D'` a decomposition of `G'` with Fan's inequality at `(t, u)`. If no end of
`P ∈ D'` lies in `{t, u} ∪ N_{G'}(u)`, then `G` has a decomposition moving one end from `t` to `u`
and containing `P` (same ends, same support). -/
theorem fan_single_protected_path {G G' : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel G'.Adj] {u t : V} (hut : G.Adj u t)
    (hG' : ∀ e, e ∈ G'.edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(u, t)) (D' : PathDecomp G')
    (h : (Finset.univ.filter (fun w => G'.Adj u w ∧ D'.ends w = 0)).card < D'.ends t)
    {P : GPath G'} (hP : P ∈ D'.paths)
    (hends : ∀ e, (P.src = e ∨ P.tgt = e) → e ≠ t ∧ e ≠ u ∧ ¬ G'.Adj u e) :
    ∃ D : PathDecomp G, (D.ends u = D'.ends u + 1 ∧ D.ends t + 1 = D'.ends t ∧
      ∀ w, w ≠ u → w ≠ t → D.ends w = D'.ends w) ∧
      ∃ Q ∈ D.paths, Q.src = P.src ∧ Q.tgt = P.tgt ∧ Q.walk.support = P.walk.support := by
  classical
  have hendsAt : ∀ w, (w = t ∨ w = u ∨ G'.Adj u w) → P.endsAt w = 0 := by
    intro w hw
    unfold GPath.endsAt
    have h1 : P.src ≠ w := fun h => by
      obtain ⟨a, b, c⟩ := hends w (Or.inl h)
      rcases hw with hw | hw | hw
      · exact a hw
      · exact b hw
      · exact c hw
    have h2 : P.tgt ≠ w := fun h => by
      obtain ⟨a, b, c⟩ := hends w (Or.inr h)
      rcases hw with hw | hw | hw
      · exact a hw
      · exact b hw
      · exact c hw
    simp [h1, h2]
  obtain ⟨Dc, hDc⟩ := D'.erase_path hP
  -- the graphs without the edges of `P`
  have hPG' : ∀ e ∈ P.edges, e ∈ G'.edgeSet := fun e he => P.walk.edges_subset_edgeSet he
  have hPG : ∀ e ∈ P.edges, e ∈ G.edgeSet := fun e he => ((hG' e).mp (hPG' e he)).1
  have hutP : s(u, t) ∉ P.edges := fun he => ((hG' _).mp (hPG' _ he)).2 rfl
  have hutc : (delEdgeList G P.edges).Adj u t := ⟨hut, hutP⟩
  have hGc : ∀ e, e ∈ (delEdgeList G' P.edges).edgeSet ↔
      e ∈ (delEdgeList G P.edges).edgeSet ∧ e ≠ s(u, t) := by
    intro e
    rw [delEdgeList_edgeSet, delEdgeList_edgeSet, hG' e]
    tauto
  have hfan : (Finset.univ.filter
      (fun w => (delEdgeList G' P.edges).Adj u w ∧ Dc.ends w = 0)).card < Dc.ends t := by
    have ht := hDc t
    rw [hendsAt t (Or.inl rfl), add_zero] at ht
    rw [ht]
    refine lt_of_le_of_lt (Finset.card_le_card fun w hw => ?_) h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    have hadj : G'.Adj u w := hw.1.1
    refine ⟨hadj, ?_⟩
    have := hDc w
    rw [hendsAt w (Or.inr (Or.inr hadj)), hw.2] at this
    omega
  obtain ⟨Dp, -, hDpu, hDpt, hDpw⟩ := fan_single hutc hGc Dc hfan
  obtain ⟨D, hD, Q, hQ, hQs, hQt, hQsupp⟩ := PathDecomp.add_path (G := G) P.toTop
    (by simpa using hPG) (fun e => by rw [delEdgeList_edgeSet, GPath.toTop_edges]) Dp
  refine ⟨D, ⟨?_, ?_, fun w hwu hwt => ?_⟩, Q, hQ, hQs, hQt, by rw [hQsupp, GPath.toTop_support]⟩
  · rw [hD u, hDpu, GPath.toTop_endsAt, ← hDc u]
    omega
  · have h1 := hD t
    have h2 := hDc t
    rw [GPath.toTop_endsAt] at h1
    omega
  · rw [hD w, hDpw w hwu hwt, GPath.toTop_endsAt, ← hDc w]
    omega

end protectedFan

section farMove

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Far-end avoidance.** Some Lovász decomposition has the path ending at `c` avoiding `A`, with
its far end outside `B`. -/
def AvoidFarDecomp (G : SimpleGraph V) [DecidableRel G.Adj] (c : V) (A B : Finset V) : Prop :=
  ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
    ∀ P ∈ D.paths, (P.src = c ∨ P.tgt = c) →
      (∀ a ∈ A, a ∉ P.walk.support) ∧ (P.src = c → P.tgt ∉ B) ∧ (P.tgt = c → P.src ∉ B)

omit [Fintype V] in
theorem PathDecomp.exists_end_of_ends_pos {K : SimpleGraph V} (D : PathDecomp K) {c : V}
    (h : 0 < D.ends c) : ∃ P ∈ D.paths, P.src = c ∨ P.tgt = c := by
  by_contra hno
  simp only [not_exists, not_and, not_or] at hno
  have : D.ends c = 0 := by
    unfold PathDecomp.ends
    rw [List.sum_eq_zero]
    intro x hx
    obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hx
    obtain ⟨h1, h2⟩ := hno P hP
    simp [GPath.endsAt, h1, h2]
  omega

omit [Fintype V] in
theorem PathDecomp.eq_of_ends_one {K : SimpleGraph V} (D : PathDecomp K) {c : V}
    (h : D.ends c ≤ 1) {P Q : GPath K} (hP : P ∈ D.paths) (hQ : Q ∈ D.paths)
    (hPc : P.src = c ∨ P.tgt = c) (hQc : Q.src = c ∨ Q.tgt = c) : P = Q := by
  classical
  by_contra hne
  have h1 := sum_map_le_of_ne D.paths (fun R => R.endsAt c) hP hQ hne
  have hPpos : 1 ≤ P.endsAt c := by unfold GPath.endsAt; rcases hPc with h | h <;> simp [h]
  have hQpos : 1 ≤ Q.endsAt c := by unfold GPath.endsAt; rcases hQc with h | h <;> simp [h]
  have : D.ends c = (D.paths.map (fun R => R.endsAt c)).sum := rfl
  omega

/-- **The target-in-`A` move (x)** (manuscript Theorem 3.3). Let `g` be the even vertex,
`u ∈ N(g)` with `u ∉ N[c]`; `u` may lie in `A`. If `G − gu` has a Lovász decomposition whose path
ending at `c` avoids `A` and has far end outside `B ∪ N_G(u)`, then `G` has one whose path ending at
`c` avoids `A` and has far end outside `B`. -/
theorem avoidFar_target {G : SimpleGraph V} [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1)
    {g u c : V} (hg : g ∈ evenSet G) (hgu : G.Adj g u) (hcu : c ≠ u) (hncu : ¬ G.Adj c u)
    (hc : G.degree c % 2 = 1) {A B : Finset V}
    (hchild : AvoidFarDecomp (delEdge G g u) c A (B ∪ G.neighborFinset u)) :
    AvoidFarDecomp G c A B := by
  classical
  obtain ⟨D', hD', hav⟩ := hchild
  have huniq : ∀ w ∈ evenSet G, w = g := fun w hw => Finset.card_le_one.mp hev w hw g hg
  have hgdeg := mem_evenSet_iff.mp hg
  have hgu' : g ≠ u := hgu.ne
  have hcg : c ≠ g := by rintro rfl; omega
  have hodd : ∀ w, w ≠ g → 0 < G.degree w → G.degree w % 2 = 1 := by
    intro w hwg hpos
    have : w ∉ evenSet G := fun h => hwg (huniq w h)
    rw [mem_evenSet_iff] at this
    omega
  have hdeg := delEdge_degree G hgu
  have hudeg : G.degree u % 2 = 1 :=
    hodd u (Ne.symm hgu') ((G.degree_pos_iff_exists_adj u).mpr ⟨g, hgu.symm⟩)
  have hD'u : D'.ends u = 0 := by
    have := hdeg u
    simp only [Ne.symm hgu', ite_false, ite_true] at this
    rw [hD' u]; omega
  have hD'g : D'.ends g = 1 := by
    have := hdeg g
    simp only [ite_true, hgu', ite_false, add_zero] at this
    rw [hD' g]; omega
  have hD'c : D'.ends c = 1 := by
    have := hdeg c
    simp only [hcg, hcu, ite_false, add_zero] at this
    rw [hD' c, this, hc]
  -- the path ending at `c`
  obtain ⟨P, hP, hPc⟩ := D'.exists_end_of_ends_pos (by omega : 0 < D'.ends c)
  obtain ⟨hPA, hPs, hPt⟩ := hav P hP hPc
  have hG' : ∀ e, e ∈ (delEdge G g u).edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(u, g) := by
    intro e
    rw [delEdge_edgeSet, Sym2.eq_swap (a := u)]
  -- the ends of `P` avoid `{g, u} ∪ N(u)`
  have hfar : ∀ q, (P.src = c ∧ P.tgt = q) ∨ (P.tgt = c ∧ P.src = q) → q ∉ G.neighborFinset u := by
    rintro q (⟨h1, rfl⟩ | ⟨h1, rfl⟩)
    · exact fun h => hPs h1 (Finset.mem_union_right _ h)
    · exact fun h => hPt h1 (Finset.mem_union_right _ h)
  have hends : ∀ e, (P.src = e ∨ P.tgt = e) → e ≠ g ∧ e ≠ u ∧ ¬ (delEdge G g u).Adj u e := by
    intro e he
    by_cases hec : e = c
    · subst hec
      exact ⟨hcg, hcu, fun h => hncu h.1.symm⟩
    · have hq : e ∉ G.neighborFinset u := by
        rcases he with he | he
        · refine hfar e (Or.inr ⟨?_, he⟩)
          rcases hPc with h | h
          · exact absurd (h.symm.trans he) (Ne.symm hec)
          · exact h
        · refine hfar e (Or.inl ⟨?_, he⟩)
          rcases hPc with h | h
          · exact h
          · exact absurd (h.symm.trans he) (Ne.symm hec)
      rw [mem_neighborFinset] at hq
      refine ⟨fun h => hq (h ▸ hgu.symm), fun h => ?_, fun h => hq h.1⟩
      -- `u` has no end in `D'`
      subst h
      have : 1 ≤ P.endsAt e := by unfold GPath.endsAt; rcases he with h | h <;> simp [h]
      have h2 : P.endsAt e ≤ D'.ends e := List.le_sum_of_mem (List.mem_map_of_mem hP)
      omega
  -- Fan's inequality: `u` has no blank neighbour
  have hfan : (Finset.univ.filter (fun w => (delEdge G g u).Adj u w ∧ D'.ends w = 0)).card <
      D'.ends g := by
    rw [hD'g, Nat.lt_one_iff, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro w - ⟨hadj, hw0⟩
    have hwu : w ≠ u := fun h => (delEdge G g u).loopless.irrefl u (h ▸ hadj)
    have hwg : w ≠ g := by
      rintro rfl
      exact hadj.2 Sym2.eq_swap
    have hw := hdeg w
    simp only [hwg, hwu, ite_false, add_zero] at hw
    have hpos : 0 < G.degree w := (G.degree_pos_iff_exists_adj w).mpr ⟨u, hadj.1.symm⟩
    rw [hD' w, hw, hodd w hwg hpos] at hw0
    exact absurd hw0 one_ne_zero
  obtain ⟨D, ⟨hDu, hDg, hDw⟩, Q, hQ, hQs, hQt, hQsupp⟩ :=
    fan_single_protected_path hgu.symm hG' D' hfan hP hends
  refine ⟨D, fun v => ?_, fun R hR hRc => ?_⟩
  · by_cases hvu : v = u
    · subst hvu; rw [hDu, hD'u, hudeg]
    · by_cases hvg : v = g
      · subst hvg
        have := hgdeg.2
        omega
      · rw [hDw v hvu hvg, hD' v]
        have := hdeg v
        simp only [hvg, hvu, ite_false, add_zero] at this
        rw [this]
  · have hQc : Q.src = c ∨ Q.tgt = c := by rw [hQs, hQt]; exact hPc
    have hDc : D.ends c ≤ 1 := by rw [hDw c hcu hcg, hD'c]
    obtain rfl := D.eq_of_ends_one hDc hR hQ hRc hQc
    refine ⟨fun a ha haR => hPA a ha (hQsupp ▸ haR), fun h => ?_, fun h => ?_⟩
    · rw [hQt]
      intro hB
      exact hPs (by rw [← hQs]; exact h) (Finset.mem_union_left _ hB)
    · rw [hQs]
      intro hB
      exact hPt (by rw [← hQt]; exact h) (Finset.mem_union_left _ hB)

end farMove

end Gallai
