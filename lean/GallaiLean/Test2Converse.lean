import GallaiLean.Test2Lift
import GallaiLean.CycleInsert

/-!
# The converse of the floor lift, matching case (session `claude/test2`)

Manuscript: `manuscripts/test2/test2.tex`, Proposition 5.2 (the matching case).

Let the even vertices of `B` be `w` and the vertices of disjoint pairs `L = [(t₁, s₁), …]`, edges of
`B`. If `B` has a decomposition into at most `(|B| − 1)/2` paths in which every pair edge `tᵢsᵢ` is
the end edge, at `tᵢ`, of its path, then `B − L` has a Lovász decomposition in which the path
ending at each `sᵢ` avoids `tᵢ` (**`matchingFloorBase_of_terminal`**). With
`floor_of_matchingBase` this makes the matching floor base equivalent, for fixed data, to the floor
with a terminal matching.

## Main results

* `GPath.dropFirst`: drop the first edge of a path of length at least two.
* `exists_decomp_of_list`: a list of paths of `⊤` with the edge multiset of `G` is a decomposition of
  `G`, path by path.
* **`PathDecomp.drop_terminal`**: removing a terminal edge from one path keeps every other path.
* **`matchingFloorBase_of_terminal`**.
-/

open SimpleGraph

namespace Gallai

universe u

section drop

variable {V : Type u} [DecidableEq V]

/-- Drop the first edge of a path of length at least two. -/
def GPath.dropFirst {G : SimpleGraph V} (P : GPath G) (h : 2 ≤ P.walk.length) : GPath G :=
  ⟨P.walk.snd, P.tgt, P.walk.tail, P.isPath.tail, by rw [Walk.length_tail]; omega⟩

theorem GPath.not_nil_of_pos {G : SimpleGraph V} (P : GPath G) : ¬ P.walk.Nil := by
  intro h
  have := P.pos
  rw [h.length_eq_zero] at this
  exact absurd this (lt_irrefl 0)

theorem GPath.dropFirst_edges {G : SimpleGraph V} (P : GPath G) (h : 2 ≤ P.walk.length) :
    (P.dropFirst h).edges = P.edges.tail := Walk.edges_tail

theorem GPath.dropFirst_support {G : SimpleGraph V} (P : GPath G) (h : 2 ≤ P.walk.length) :
    (P.dropFirst h).walk.support = P.walk.support.tail :=
  Walk.support_tail_of_not_nil _ P.not_nil_of_pos

theorem GPath.edges_eq_cons_tail {G : SimpleGraph V} (P : GPath G) :
    P.edges = s(P.src, P.walk.snd) :: P.edges.tail := by
  have h := Walk.cons_tail_eq P.walk P.not_nil_of_pos
  unfold GPath.edges
  conv_lhs => rw [← h]
  rw [Walk.edges_cons, Walk.edges_tail]


theorem GPath.snd_of_support {G : SimpleGraph V} (P : GPath G) {t s : V} {l : List V}
    (h : P.walk.support = t :: s :: l) : P.walk.snd = s := by
  have h1 := Walk.cons_tail_eq P.walk P.not_nil_of_pos
  have h2 : P.walk.tail.support = P.walk.snd :: P.walk.tail.support.tail :=
    walk_support_eq_cons _
  have h3 : P.walk.support.tail = P.walk.tail.support :=
    (Walk.support_tail_of_not_nil _ P.not_nil_of_pos).symm
  rw [h, List.tail_cons, h2] at h3
  exact (List.cons.inj h3).1.symm

end drop

section builder

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **A list of paths with the right edges is a decomposition, path by path.** -/
theorem exists_decomp_of_list (L : List (TPath V)) (h : edgesM L = G.edgeFinset.val) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = endsL L v) ∧
      (∀ Q ∈ D.paths, ∃ P ∈ L, Q.src = P.src ∧ Q.tgt = P.tgt ∧
        Q.walk.support = P.walk.support) ∧
      (∀ P ∈ L, ∃ Q ∈ D.paths, Q.src = P.src ∧ Q.tgt = P.tgt ∧
        Q.walk.support = P.walk.support) := by
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
  refine ⟨⟨L', by rw [h1]; exact hnd, fun e => ?_⟩, h2, ?_, ?_⟩
  · rw [h1, ← mem_edgeFinset, ← Finset.mem_val, ← h, edgesM, Multiset.mem_coe]
  · intro Q hQ
    obtain ⟨P, hP, rfl⟩ := List.mem_pmap.mp hQ
    exact ⟨P, hP, rfl, rfl, Walk.support_transfer _ _⟩
  · intro P hP
    exact ⟨P.ofTop G (hmem P hP), List.mem_pmap.mpr ⟨P, hP, rfl⟩, rfl, rfl,
      Walk.support_transfer _ _⟩

end builder

section dropTerminal

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Removing a terminal edge.** Let `P ∈ D` and let `R` be `P` or its reverse, starting
`t, s, …` with length at least two. Removing the edge `ts` from `R` gives a decomposition of
`K − ts`: the new path starts at `s` with support `R.support.tail`, and every other path of `D` is
kept with its ends and support. -/
theorem PathDecomp.drop_terminal {K K' : SimpleGraph V} [DecidableRel K.Adj] [DecidableRel K'.Adj]
    (D : PathDecomp K) {P : GPath K} (hP : P ∈ D.paths) (R : GPath K)
    (hRe : (R.edges : Multiset (Sym2 V)) = P.edges)
    (hRends : ∀ v, R.endsAt v = P.endsAt v)
    {t s : V} {l : List V} (hRsrc : R.src = t) (hRs : R.walk.support = t :: s :: l)
    (hlen : 2 ≤ R.walk.length)
    (hK' : ∀ e, e ∈ K'.edgeSet ↔ e ∈ K.edgeSet ∧ e ≠ s(t, s)) :
    ∃ D' : PathDecomp K',
      (∀ v, D'.ends v + (if t = v then 1 else 0) = D.ends v + (if s = v then 1 else 0)) ∧
      (∀ Q' ∈ D'.paths, (Q'.src = s ∧ Q'.tgt = R.tgt ∧ Q'.walk.support = s :: l) ∨
        ∃ Q ∈ D.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
          Q'.walk.support = Q.walk.support) ∧
      (∀ Q ∈ D.paths, Q ≠ P → ∃ Q' ∈ D'.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
        Q'.walk.support = Q.walk.support) ∧
      (∃ Q' ∈ D'.paths, Q'.src = s ∧ Q'.tgt = R.tgt ∧ Q'.walk.support = s :: l) := by
  classical
  set R' := R.dropFirst hlen with hR'
  have hsnd : R.walk.snd = s := R.snd_of_support hRs
  have hR'src : R'.src = s := by rw [hR']; exact hsnd
  have hR'supp : R'.walk.support = s :: l := by
    rw [hR', GPath.dropFirst_support, hRs, List.tail_cons]
  have hRedges : R.edges = s(t, s) :: R'.edges := by
    have h := R.edges_eq_cons_tail
    rw [hsnd] at h
    rw [hRsrc] at h
    rw [hR', GPath.dropFirst_edges]
    exact h
  let L := R'.toTop :: (D.paths.erase P).map GPath.toTop
  -- the edge multiset of the new list
  have hperm : (D.paths.map GPath.toTop).Perm (P.toTop :: (D.paths.erase P).map GPath.toTop) := by
    have := (List.perm_cons_erase hP).map GPath.toTop
    simpa using this
  have hK : edgesM (D.paths.map GPath.toTop) = K.edgeFinset.val := D.edgesM_toTop
  have hsplit : (P.edges : Multiset (Sym2 V)) + edgesM ((D.paths.erase P).map GPath.toTop) =
      K.edgeFinset.val := by
    rw [← hK, edgesM_perm hperm, edgesM_cons, GPath.toTop_edges]
  have hPe : (P.edges : Multiset (Sym2 V)) = s(t, s) ::ₘ (R'.edges : Multiset (Sym2 V)) := by
    rw [← hRe, hRedges]; rfl
  have hLe : edgesM L = K'.edgeFinset.val := by
    have hnd : (K.edgeFinset.val).Nodup := K.edgeFinset.nodup
    rw [← hsplit, hPe] at hnd
    rw [edgesM_cons, GPath.toTop_edges]
    refine (Multiset.Nodup.ext ?_ (Finset.nodup _)).mpr fun e => ?_
    · rw [Multiset.cons_add] at hnd
      exact (Multiset.nodup_cons.mp hnd).2
    · rw [Finset.mem_val, mem_edgeFinset, hK', ← mem_edgeFinset, ← Finset.mem_val, ← hsplit, hPe,
        Multiset.cons_add, Multiset.mem_cons]
      constructor
      · intro he
        refine ⟨Or.inr he, ?_⟩
        rintro rfl
        rw [Multiset.cons_add] at hnd
        exact (Multiset.nodup_cons.mp hnd).1 he
      · rintro ⟨h | h, hne⟩
        · exact absurd h hne
        · exact h
  obtain ⟨D', hD'e, hD'1, hD'2⟩ := exists_decomp_of_list (G := K') L hLe
  refine ⟨D', fun v => ?_, fun Q' hQ' => ?_, fun Q hQ => ?_, ?_⟩
  · -- ends
    have hPends : endsL (D.paths.map GPath.toTop) v = D.ends v := D.endsL_toTop v
    rw [endsL_perm hperm, endsL_cons, GPath.toTop_endsAt] at hPends
    rw [hD'e v, endsL_cons, GPath.toTop_endsAt]
    have hR'ends : R'.endsAt v + (if t = v then 1 else 0) = R.endsAt v + (if s = v then 1 else 0) := by
      unfold GPath.endsAt
      rw [hR'src, hRsrc, show R'.tgt = R.tgt from rfl]
      omega
    rw [← hRends v] at hPends
    omega
  · obtain ⟨Q, hQ, hs, ht, hsupp⟩ := hD'1 Q' hQ'
    rcases List.mem_cons.mp hQ with rfl | hQ
    · exact Or.inl ⟨hs.trans hR'src, ht, hsupp.trans (by rw [GPath.toTop_support, hR'supp])⟩
    · obtain ⟨Q₀, hQ₀, rfl⟩ := List.mem_map.mp hQ
      exact Or.inr ⟨Q₀, List.mem_of_mem_erase hQ₀, hs, ht, hsupp.trans (GPath.toTop_support _)⟩
  · intro hne
    obtain ⟨Q', hQ', hs, ht, hsupp⟩ := hD'2 Q.toTop
      (List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_erase_of_ne hne |>.mpr hQ)))
    exact ⟨Q', hQ', hs, ht, hsupp.trans (GPath.toTop_support _)⟩
  · obtain ⟨Q', hQ', hs, ht, hsupp⟩ := hD'2 R'.toTop List.mem_cons_self
    exact ⟨Q', hQ', hs.trans hR'src, ht, hsupp.trans (by rw [GPath.toTop_support, hR'supp])⟩

end dropTerminal

section pairsInduction

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The pair edge `ts` is the end edge, at `t`, of some path of `D` (either orientation). -/
def TermAt {K : SimpleGraph V} (D : PathDecomp K) (t s : V) : Prop :=
  ∃ P ∈ D.paths, (∃ l, P.walk.support = t :: s :: l) ∨ (∃ l, P.walk.support = l ++ [s, t])

/-- Every path of `D` ending at `s` avoids `t`. -/
def AvoidAt {K : SimpleGraph V} (D : PathDecomp K) (s t : V) : Prop :=
  ∀ P ∈ D.paths, (P.src = s ∨ P.tgt = s) → t ∉ P.walk.support

omit [Fintype V] [DecidableEq V] in
theorem GPath.src_of_support {G : SimpleGraph V} (P : GPath G) {t : V} {l : List V}
    (h : P.walk.support = t :: l) : P.src = t := by
  have := walk_support_eq_cons P.walk
  rw [h] at this
  exact (List.cons.inj this).1.symm

omit [Fintype V] [DecidableEq V] in
theorem GPath.tgt_of_support {G : SimpleGraph V} (P : GPath G) {t : V} {l : List V}
    (h : P.walk.support = l ++ [t]) : P.tgt = t := by
  have h1 := P.walk.getLast_support
  simp only [h, List.getLast_append_singleton] at h1
  exact h1.symm

omit [Fintype V] in
theorem PathDecomp.endsAt_le_ends' {K : SimpleGraph V} (D : PathDecomp K) {P : GPath K}
    (hP : P ∈ D.paths) (v : V) : P.endsAt v ≤ D.ends v :=
  List.le_sum_of_mem (List.mem_map_of_mem hP)

omit [Fintype V] in
/-- Orient a terminal path so that it starts at `t`. -/
theorem orient_terminal {K : SimpleGraph V} {P : GPath K} {t s : V}
    (h : (∃ l, P.walk.support = t :: s :: l) ∨ (∃ l, P.walk.support = l ++ [s, t])) :
    ∃ R : GPath K, (R.edges : Multiset (Sym2 V)) = P.edges ∧ (∀ v, R.endsAt v = P.endsAt v) ∧
      R.src = t ∧ (∃ l, R.walk.support = t :: s :: l) ∧
      (∀ x, x ∈ R.walk.support ↔ x ∈ P.walk.support) ∧
      (R.tgt = P.src ∨ R.tgt = P.tgt) ∧
      (R.walk.support = P.walk.support ∨ R.walk.support = P.walk.support.reverse) := by
  rcases h with ⟨l, hl⟩ | ⟨l, hl⟩
  · exact ⟨P, rfl, fun _ => rfl, P.src_of_support hl, ⟨l, hl⟩, fun _ => Iff.rfl, Or.inr rfl,
      Or.inl rfl⟩
  · refine ⟨P.reverse, ?_, fun v => GPath.reverse_endsAt' P v, ?_, ⟨l.reverse, ?_⟩, ?_, Or.inl rfl,
      Or.inr (GPath.reverse_support P)⟩
    · rw [GPath.reverse_edges, Multiset.coe_reverse]
    · rw [GPath.reverse_src]; exact P.tgt_of_support (l := l ++ [s]) (by rw [hl]; simp)
    · rw [GPath.reverse_support, hl]; simp
    · intro x; rw [GPath.reverse_support, List.mem_reverse]

omit [Fintype V] [DecidableEq V] in
theorem tail_of_append_pair {t s a b : V} {l m : List V} (h : t :: s :: l = m ++ [a, b])
    (hta : t ≠ a) : ∃ m', s :: l = m' ++ [a, b] := by
  cases m with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at h
    exact absurd h.1 hta
  | cons x m' =>
    simp only [List.cons_append, List.cons.injEq] at h
    exact ⟨m', h.2⟩

/-- **Removing the pair edges one by one.** The invariants: pair vertices distinct, the
partners `s` have no end, every unprocessed pair edge is terminal at `t`, and every processed pair
has its `s`-paths avoiding `t`. -/
theorem drop_pairs :
    ∀ (L Prev : List (V × V)) (K G : SimpleGraph V) [DecidableRel K.Adj] [DecidableRel G.Adj]
      (D : PathDecomp K),
      (pairVerts (Prev ++ L)).Nodup →
      (∀ e, e ∈ G.edgeSet ↔ e ∈ K.edgeSet ∧ e ∉ L.map pairEdge) →
      (∀ p ∈ L, D.ends p.2 = 0) →
      (∀ p ∈ L, TermAt D p.1 p.2) →
      (∀ q ∈ Prev, AvoidAt D q.2 q.1) →
      ∃ D' : PathDecomp G,
        (∀ v, D'.ends v + L.countP (fun p => decide (p.1 = v)) =
          D.ends v + L.countP (fun p => decide (p.2 = v))) ∧
        (∀ q ∈ Prev ++ L, AvoidAt D' q.2 q.1)
  | [], Prev, K, G, _, _, D, _, hG, _, _, hav => by
      have hE : edgesM (D.paths.map GPath.toTop) = G.edgeFinset.val := by
        rw [D.edgesM_toTop]
        congr 1
        ext e
        rw [mem_edgeFinset, mem_edgeFinset, hG]
        simp
      obtain ⟨D', hD'e, hD'1, -⟩ := exists_decomp_of_list (G := G) _ hE
      refine ⟨D', fun v => by rw [hD'e, D.endsL_toTop]; simp, fun q hq P hP hend => ?_⟩
      rw [List.append_nil] at hq
      obtain ⟨Q, hQ, hs, ht, hsupp⟩ := hD'1 P hP
      obtain ⟨Q₀, hQ₀, rfl⟩ := List.mem_map.mp hQ
      rw [hsupp, GPath.toTop_support]
      rw [hs, ht, GPath.toTop_src, GPath.toTop_tgt] at hend
      exact hav q hq Q₀ hQ₀ hend
  | p :: L', Prev, K, G, _, _, D, hnd, hG, hzero, hterm, hav => by
      classical
      -- distinctness
      have hnd' := hnd
      rw [pairVerts, List.flatMap_append, ← pairVerts, ← pairVerts, pairVerts_cons,
        List.nodup_append] at hnd'
      obtain ⟨hndP, hndL, hdisj⟩ := hnd'
      rw [List.nodup_cons, List.nodup_cons, List.mem_cons, not_or] at hndL
      obtain ⟨⟨hp12, hp1L⟩, hp2L, hndL'⟩ := hndL
      have hp1P : p.1 ∉ pairVerts Prev := fun h =>
        hdisj p.1 h p.1 List.mem_cons_self rfl
      have hp2P : p.2 ∉ pairVerts Prev := fun h =>
        hdisj p.2 h p.2 (List.mem_cons_of_mem _ List.mem_cons_self) rfl
      -- the path of `p`
      obtain ⟨P, hP, hform⟩ := hterm p List.mem_cons_self
      obtain ⟨R, hRe, hRends, hRsrc, ⟨l, hRs⟩, hRmem, hRtgt, hRsupp⟩ := orient_terminal hform
      have hRnd : (p.1 :: p.2 :: l).Nodup := hRs ▸ R.isPath.support_nodup
      have hlen : 2 ≤ R.walk.length := by
        have h1 := R.walk.length_support
        rw [hRs] at h1
        cases l with
        | nil =>
          -- `R` is the single edge `ts`, so `s` would be an end
          exfalso
          have htgt : R.tgt = p.2 := R.tgt_of_support (l := [p.1]) (by rw [hRs]; rfl)
          have h2 : 1 ≤ R.endsAt p.2 := by unfold GPath.endsAt; rw [htgt]; simp
          rw [hRends] at h2
          have h3 := D.endsAt_le_ends' hP p.2
          have h4 := hzero p List.mem_cons_self
          omega
        | cons x l' => simp at h1; omega
      set K₁ := delList K [pairEdge p] with hK₁
      have hK₁e : ∀ e, e ∈ K₁.edgeSet ↔ e ∈ K.edgeSet ∧ e ≠ s(p.1, p.2) := by
        intro e
        rw [hK₁, delList_edgeSet]
        simp [pairEdge]
      obtain ⟨D₁, hends₁, hnew, hcopy, hnewIn⟩ :=
        D.drop_terminal hP R hRe hRends hRsrc hRs hlen hK₁e
      -- the invariants for `D₁`
      have hG' : ∀ e, e ∈ G.edgeSet ↔ e ∈ K₁.edgeSet ∧ e ∉ L'.map pairEdge := by
        intro e
        rw [hG e, hK₁e e, List.map_cons, List.mem_cons]
        simp only [pairEdge]
        tauto
      have hnd₁ : (pairVerts ((Prev ++ [p]) ++ L')).Nodup := by
        rw [List.append_assoc, List.singleton_append]; exact hnd
      have hzero₁ : ∀ q ∈ L', D₁.ends q.2 = 0 := by
        intro q hq
        have h1 := hends₁ q.2
        have hq2 : q.2 ∈ pairVerts L' := snd_mem_pairVerts hq
        have ht : p.1 ≠ q.2 := fun h => hp1L (h ▸ hq2)
        have hs : p.2 ≠ q.2 := fun h => hp2L (h ▸ hq2)
        rw [if_neg ht, if_neg hs, hzero q (List.mem_cons_of_mem _ hq)] at h1
        omega
      have hterm₁ : ∀ q ∈ L', TermAt D₁ q.1 q.2 := by
        intro q hq
        obtain ⟨Pq, hPq, hqform⟩ := hterm q (List.mem_cons_of_mem _ hq)
        have hq1 : q.1 ∈ pairVerts L' := fst_mem_pairVerts hq
        have hq2 : q.2 ∈ pairVerts L' := snd_mem_pairVerts hq
        have h11 : p.1 ≠ q.1 := fun h => hp1L (h ▸ hq1)
        have h12 : p.1 ≠ q.2 := fun h => hp1L (h ▸ hq2)
        by_cases hPP : Pq = P
        · -- the same path: the new path is still terminal at `q.1`
          subst hPP
          obtain ⟨Q', hQ', -, -, hQsupp⟩ := hnewIn
          refine ⟨Q', hQ', Or.inr ?_⟩
          rw [hQsupp]
          have hR2 : ∃ m, R.walk.support = m ++ [q.2, q.1] := by
            rcases hRsupp with hsame | hrev <;> rcases hqform with ⟨lq, hlq⟩ | ⟨mq, hmq⟩
            · exact absurd ((List.cons.inj (hRs.symm.trans (hsame.trans hlq))).1) h11
            · exact ⟨mq, hsame.trans hmq⟩
            · exact ⟨lq.reverse, by rw [hrev, hlq]; simp⟩
            · exfalso
              have : R.walk.support = q.1 :: q.2 :: mq.reverse := by rw [hrev, hmq]; simp
              exact h11 (List.cons.inj (hRs.symm.trans this)).1
          obtain ⟨m, hm⟩ := hR2
          exact tail_of_append_pair (hRs.symm.trans hm) h12
        · obtain ⟨Q', hQ', -, -, hsupp⟩ := hcopy Pq hPq hPP
          exact ⟨Q', hQ', by rw [hsupp]; exact hqform⟩
      have hav₁ : ∀ q ∈ Prev ++ [p], AvoidAt D₁ q.2 q.1 := by
        intro q hq Q' hQ' hend
        rcases hnew Q' hQ' with ⟨hs, ht, hsupp⟩ | ⟨Q, hQ, hs, ht, hsupp⟩
        · rw [hsupp]
          rcases List.mem_append.mp hq with hqP | hqp
          · -- an earlier pair
            have hq2 : q.2 ∈ pairVerts Prev := snd_mem_pairVerts hqP
            have hne : q.2 ≠ p.2 := fun h => hp2P (h ▸ hq2)
            have hendR : R.tgt = q.2 := by
              rcases hend with h | h
              · exact absurd (h.symm.trans hs) hne
              · exact (h.symm.trans ht).symm
            have hPend : P.src = q.2 ∨ P.tgt = q.2 := by
              rcases hRtgt with h | h
              · exact Or.inl (h.symm.trans hendR)
              · exact Or.inr (h.symm.trans hendR)
            have hnotP := hav q hqP P hP hPend
            intro hmem
            apply hnotP
            rw [← hRmem, hRs]
            exact List.mem_cons_of_mem _ hmem
          · -- the pair just processed
            rw [List.mem_singleton] at hqp
            subst hqp
            exact (List.nodup_cons.mp hRnd).1
        · rw [hsupp]
          rw [hs, ht] at hend
          rcases List.mem_append.mp hq with hqP | hqp
          · exact hav q hqP Q hQ hend
          · rw [List.mem_singleton] at hqp
            subst hqp
            exfalso
            have h1 : 1 ≤ Q.endsAt q.2 := by
              unfold GPath.endsAt
              rcases hend with h | h <;> simp [h]
            have h2 := D.endsAt_le_ends' hQ q.2
            have h3 := hzero q List.mem_cons_self
            omega
      obtain ⟨D', hD'e, hD'av⟩ :=
        drop_pairs L' (Prev ++ [p]) K₁ G D₁ hnd₁ hG' hzero₁ hterm₁ hav₁
      refine ⟨D', fun v => ?_, fun q hq => hD'av q (by
        rw [List.append_assoc, List.singleton_append]; exact hq)⟩
      have h1 := hD'e v
      have h2 := hends₁ v
      rw [List.countP_cons, List.countP_cons]
      by_cases h₁ : p.1 = v <;> by_cases h₂ : p.2 = v <;> simp [h₁, h₂] at h1 h2 ⊢ <;> omega

end pairsInduction

section converseMain

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem pairVerts_facts : ∀ (L : List (V × V)), (pairVerts L).Nodup →
    (L.map Prod.fst).Nodup ∧ (L.map Prod.snd).Nodup ∧ (∀ p ∈ L, p.2 ∉ L.map Prod.fst) ∧
      (∀ p ∈ L, p.1 ∉ L.map Prod.snd) ∧ (pairVerts L).length = 2 * L.length
  | [], _ => by simp [pairVerts]
  | p :: L, hnd => by
    have hnd' := hnd
    rw [pairVerts_cons, List.nodup_cons, List.nodup_cons, List.mem_cons, not_or] at hnd'
    obtain ⟨⟨h12, h1L⟩, h2L, hndL⟩ := hnd'
    obtain ⟨ih1, ih1', ih2, ih2', ih3⟩ := pairVerts_facts L hndL
    have hsub : ∀ x ∈ L.map Prod.fst, x ∈ pairVerts L := by
      intro x hx; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx; exact fst_mem_pairVerts hq
    have hsub' : ∀ x ∈ L.map Prod.snd, x ∈ pairVerts L := by
      intro x hx; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx; exact snd_mem_pairVerts hq
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [List.map_cons, List.nodup_cons]; exact ⟨fun h => h1L (hsub _ h), ih1⟩
    · rw [List.map_cons, List.nodup_cons]; exact ⟨fun h => h2L (hsub' _ h), ih1'⟩
    · intro q hq
      rw [List.map_cons, List.mem_cons, not_or]
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨fun h => h12 h.symm, fun h => h2L (hsub _ h)⟩
      · exact ⟨fun h => h1L (h ▸ snd_mem_pairVerts hq), ih2 q hq⟩
    · intro q hq
      rw [List.map_cons, List.mem_cons, not_or]
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨h12, fun h => h1L (hsub' _ h)⟩
      · exact ⟨fun h => h2L (h ▸ fst_mem_pairVerts hq), ih2' q hq⟩
    · rw [pairVerts_cons, List.length_cons, List.length_cons, ih3, List.length_cons]; ring

omit [Fintype V] in
theorem countP_comp_of_nodup (L : List (V × V)) (f : V × V → V) (hnd : (L.map f).Nodup) (v : V) :
    L.countP (fun p => decide (f p = v)) = if v ∈ L.map f then 1 else 0 := by
  have h : L.countP (fun p => decide (f p = v)) = (L.map f).count v := by
    rw [List.count, List.countP_map]
    apply List.countP_congr
    intro p _
    simp [Function.comp_def]
  rw [h]
  split_ifs with hv
  · exact List.count_eq_one_of_mem hnd hv
  · exact List.count_eq_zero_of_not_mem hv

/-- **The converse of the floor lift, matching case** (manuscript Proposition 5.2). Let the even
vertices of `B` be `w` and the vertices of the disjoint pairs `L`, edges of `B`. If `B` has a
decomposition into at most `(|B| − 1)/2` paths in which every pair edge `p.1 p.2` is the end edge,
at `p.1`, of its path, then `B − L` has a Lovász decomposition in which, for every pair, the paths
ending at `p.2` avoid `p.1` (a matching floor base, oriented by `L`). -/
theorem matchingFloorBase_of_terminal (B : SimpleGraph V) [DecidableRel B.Adj] {w : V}
    {L : List (V × V)} (hev : ∀ v, Even (B.degree v) ↔ v = w ∨ v ∈ pairVerts L)
    (hnd : (pairVerts L).Nodup) (hw : w ∉ pairVerts L) (hedge : ∀ p ∈ L, B.Adj p.1 p.2)
    (D : PathDecomp B) (hsize : D.size ≤ (Fintype.card V - 1) / 2)
    (hterm : ∀ p ∈ L, TermAt D p.1 p.2) :
    ∃ D₀ : PathDecomp (delList B (L.map pairEdge)),
      (∀ v, D₀.ends v = (delList B (L.map pairEdge)).degree v % 2) ∧ TriangleDisj D₀ L := by
  classical
  obtain ⟨hfst, hsnd, hsf, hfs, hlen⟩ := pairVerts_facts L hnd
  -- the lower bound `f` and the tight end count
  let f : V → ℕ := fun v => 2 * (if v ∈ L.map Prod.fst then 1 else 0) +
    (if v ∉ pairVerts L ∧ v ≠ w then 1 else 0)
  have hpar : ∀ v, D.ends v % 2 = B.degree v % 2 := fun v => D.ends_mod_two v
  have hmemPV : ∀ v, v ∈ L.map Prod.fst → v ∈ pairVerts L := by
    intro v hv; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv; exact fst_mem_pairVerts hq
  have hle : ∀ v ∈ (Finset.univ : Finset V), f v ≤ D.ends v := by
    intro v _
    by_cases hv : v ∈ L.map Prod.fst
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
      obtain ⟨P, hP, hform⟩ := hterm p hp
      have h1 : 1 ≤ P.endsAt p.1 := by
        unfold GPath.endsAt
        rcases hform with ⟨l, hl⟩ | ⟨l, hl⟩
        · rw [P.src_of_support hl]; simp
        · rw [P.tgt_of_support (l := l ++ [p.2]) (by rw [hl, List.append_assoc]; rfl)]; simp
      have h2 := D.endsAt_le_ends' hP p.1
      have he := (hev p.1).2 (Or.inr (fst_mem_pairVerts hp))
      rw [Nat.even_iff] at he
      have h3 := hpar p.1
      simp only [f, hv, ite_true, fst_mem_pairVerts hp, not_true_eq_false, false_and, ite_false]
      omega
    · simp only [f, hv, ite_false, mul_zero, zero_add]
      split_ifs with h
      · have ho : ¬ Even (B.degree v) := fun he => by
          rcases (hev v).1 he with h' | h'
          · exact h.2 h'
          · exact h.1 h'
        rw [Nat.not_even_iff] at ho
        have := hpar v
        omega
      · exact Nat.zero_le _
  have hcardW : 2 * L.length + 1 ≤ Fintype.card V := by
    have h1 : (insert w (pairVerts L).toFinset).card = 2 * L.length + 1 := by
      rw [Finset.card_insert_of_notMem (by simpa using hw), List.toFinset_card_of_nodup hnd, hlen]
    rw [← h1]; exact Finset.card_le_univ _
  have hsumf : ∑ v, f v = Fintype.card V - 1 := by
    have h1 : ∑ v : V, (if v ∈ L.map Prod.fst then 1 else 0) = L.length := by
      rw [Finset.sum_boole, Nat.cast_id]
      have : (Finset.univ.filter (fun v => v ∈ L.map Prod.fst)) = (L.map Prod.fst).toFinset := by
        ext v; simp
      rw [this, List.toFinset_card_of_nodup hfst, List.length_map]
    have h2 : ∑ v : V, (if v ∉ pairVerts L ∧ v ≠ w then 1 else 0) =
        Fintype.card V - (2 * L.length + 1) := by
      rw [Finset.sum_boole, Nat.cast_id]
      have : (Finset.univ.filter (fun v => v ∉ pairVerts L ∧ v ≠ w)) =
          (insert w (pairVerts L).toFinset)ᶜ := by
        ext v; simp [and_comm]
      rw [this, Finset.card_compl, Finset.card_insert_of_notMem (by simpa using hw),
        List.toFinset_card_of_nodup hnd, hlen]
    simp only [f, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2]
    omega
  have hsumD : ∑ v, D.ends v ≤ Fintype.card V - 1 := by
    rw [D.sum_ends]; omega
  have heq : ∀ v, f v = D.ends v := by
    have hs : ∑ v, f v = ∑ v, D.ends v :=
      le_antisymm (Finset.sum_le_sum hle) (by rw [hsumf]; exact hsumD)
    intro v
    exact (Finset.sum_eq_sum_iff_of_le hle).mp hs v (Finset.mem_univ v)
  -- apply the induction
  have hzero : ∀ p ∈ L, D.ends p.2 = 0 := by
    intro p hp
    rw [← heq]
    simp only [f, hsf p hp, ite_false, snd_mem_pairVerts hp, not_true_eq_false, false_and]
  have hG : ∀ e, e ∈ (delList B (L.map pairEdge)).edgeSet ↔ e ∈ B.edgeSet ∧ e ∉ L.map pairEdge :=
    delList_edgeSet B _
  obtain ⟨D', hD'e, hD'av⟩ := drop_pairs L [] B (delList B (L.map pairEdge)) D
    (by simpa using hnd) hG hzero hterm (fun q hq => absurd hq (List.not_mem_nil))
  refine ⟨D', fun v => ?_, fun p hp => Or.inl fun P hP hend => hD'av p (by simpa using hp) P hP hend⟩
  -- the ends of `D'`
  have hdeg := delPairs_degree_mod B hev hnd hw hedge v
  rw [hdeg]
  have h1 := hD'e v
  have h2 := heq v
  rw [countP_comp_of_nodup L Prod.fst hfst v, countP_comp_of_nodup L Prod.snd hsnd v] at h1
  have hpv : v ∈ pairVerts L ↔ v ∈ L.map Prod.fst ∨ v ∈ L.map Prod.snd := by
    rw [mem_pairVerts]; simp only [List.mem_map]
    constructor
    · rintro ⟨q, hq, rfl | rfl⟩
      · exact Or.inl ⟨q, hq, rfl⟩
      · exact Or.inr ⟨q, hq, rfl⟩
    · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
      · exact ⟨q, hq, Or.inl rfl⟩
      · exact ⟨q, hq, Or.inr rfl⟩
  by_cases hvw : v = w
  · subst hvw
    have hf : v ∉ L.map Prod.fst := fun h => hw (hmemPV v h)
    have hs : v ∉ L.map Prod.snd := fun h => hw (hpv.2 (Or.inr h))
    simp only [f, hf, hs, ite_false, ite_true, mul_zero, zero_add, ne_eq, not_true_eq_false,
      and_false] at h1 h2 ⊢
    omega
  · simp only [hvw, ite_false]
    by_cases hf : v ∈ L.map Prod.fst
    · have hs : v ∉ L.map Prod.snd := by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hf; exact hfs q hq
      simp only [f, hf, hs, ite_true, ite_false, hmemPV v hf, not_true_eq_false, false_and,
        add_zero] at h1 h2
      omega
    · by_cases hs : v ∈ L.map Prod.snd
      · have hv : v ∈ pairVerts L := hpv.2 (Or.inr hs)
        simp only [f, hf, hs, hv, ite_true, ite_false, not_true_eq_false, false_and, mul_zero,
          zero_add] at h1 h2
        omega
      · have hv : v ∉ pairVerts L := fun h => (hpv.1 h).elim hf hs
        simp only [f, hf, hs, hv, hvw, ite_false, mul_zero, zero_add, not_false_eq_true,
          ne_eq, and_self, ite_true] at h1 h2
        omega

end converseMain

section rootedConverse

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- The number of edges `zv` (`v ∈ U`) at a vertex. -/
theorem countP_zDel2 {z : V} {U : List V} (hU : U.Nodup) (hz : z ∉ U) (v : V) :
    (zDel2 z U).countP (fun e => decide (v ∈ e)) =
      (if v = z then U.length else 0) + (if v ∈ U then 1 else 0) := by
  rw [zDel2, List.countP_map]
  by_cases hvz : v = z
  · subst hvz
    rw [List.countP_eq_length.mpr (fun x _ => by simp)]
    simp [hz]
  · have hcnt : U.countP ((fun e => decide (v ∈ e)) ∘ fun x => s(z, x)) = U.count v := by
      rw [List.count]
      apply List.countP_congr
      intro x _
      simp only [Function.comp_apply, decide_eq_true_eq, beq_iff_eq, Sym2.mem_iff, hvz, false_or]
      exact eq_comm
    rw [hcnt]
    by_cases hvU : v ∈ U
    · rw [List.count_eq_one_of_mem hU hvU]; simp [hvz, hvU]
    · rw [List.count_eq_zero_of_not_mem hvU]; simp [hvz, hvU]

omit [Fintype V] in
theorem mem_pairEdge_swap {L : List (V × V)} {e : Sym2 V} :
    e ∈ (L.map Prod.swap).map pairEdge ↔ e ∈ L.map pairEdge := by
  simp only [List.map_map, List.mem_map, Function.comp_apply, pairEdge, Prod.fst_swap,
    Prod.snd_swap]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, Sym2.eq_swap⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, Sym2.eq_swap⟩

/-- **The converse of the forest lift, matching case** (manuscript Proposition 4.5(a)). Let `z, r`
be the only even vertices of `J`, adjacent, and let `L` be disjoint pairs `(t, s)` (parent `t`,
child `s`) covering `N(z) = r :: T`, with `r` a parent, forming Test2 forest data. Let `D` decompose
`J` minus all edges at `z` (that is, `J − z` with `z` isolated) into at most `|J|/2` paths with at
least three ends at `r`, every pair edge being the end edge, at `t`, of its path. Then the forest
lift has a base: a Lovász decomposition of `M` with (i) and (ii). -/
theorem forestBase2_matching_of_terminal (J : SimpleGraph V) [DecidableRel J.Adj] {z r : V}
    (hzr : ∀ v, Even (J.degree v) ↔ v = z ∨ v = r) {T : List V} {L : List (V × V)}
    (hF : ForestData2 J z r T (L.map Prod.swap)) (hnd : (pairVerts L).Nodup)
    (hcover : ∀ v, v ∈ pairVerts L ↔ v = r ∨ v ∈ T) (hrpar : r ∈ L.map Prod.fst)
    (D : PathDecomp (delList J (zDel2 z (r :: T)))) (hsize : D.size ≤ Fintype.card V / 2)
    (hr3 : 3 ≤ D.ends r) (hterm : ∀ p ∈ L, TermAt D p.1 p.2) :
    ∃ D₀ : PathDecomp (forM2 J z T (L.map Prod.swap)),
      (∀ v, D₀.ends v = (forM2 J z T (L.map Prod.swap)).degree v % 2) ∧
      (∀ p ∈ L.map Prod.swap, ∀ P ∈ D₀.paths, (P.src = p.1 ∨ P.tgt = p.1) → p.2 ∉ P.walk.support) ∧
      (∀ p ∈ L.map Prod.swap, ∀ q ∈ L.map Prod.swap, p.1 ≠ q.1 → p.2 = q.2 → ∀ P ∈ D₀.paths,
        ¬ ((P.src = p.1 ∨ P.tgt = p.1) ∧ (P.src = q.1 ∨ P.tgt = q.1))) := by
  classical
  obtain ⟨hzr', hzT, hrT, hTnd⟩ := hF.facts
  obtain ⟨hfst, hsnd, hsf, hfs, hlen⟩ := pairVerts_facts L hnd
  have hrT' : (r :: T).Nodup := hF.nodup
  have hzU : z ∉ r :: T := by rw [List.mem_cons, not_or]; exact ⟨hzr', hzT⟩
  have hzpv : z ∉ pairVerts L := fun h => hzU (by rw [List.mem_cons]; exact (hcover z).1 h)
  -- degrees in `J` minus all edges at `z`
  have hzK_in : ∀ e ∈ zDel2 z (r :: T), e ∈ J.edgeSet := by
    intro e he
    rw [zDel2, List.mem_map] at he
    obtain ⟨v, hv, rfl⟩ := he
    exact (hF.nbr v).2 (List.mem_cons.mp hv)
  have hzK_nd : (zDel2 z (r :: T)).Nodup := by
    refine hrT'.map_on ?_
    intro a _ b _ h
    rcases Sym2.eq_iff.1 h with ⟨-, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1
  have hdegK : ∀ v, (delList J (zDel2 z (r :: T))).degree v +
      ((if v = z then (r :: T).length else 0) + (if v ∈ r :: T then 1 else 0)) = J.degree v := by
    intro v
    rw [← countP_zDel2 hrT' hzU v]
    exact delList_degree_count J _ hzK_nd hzK_in v
  have hoddJ : ∀ v, v ≠ z → v ≠ r → J.degree v % 2 = 1 := fun v hvz hvr =>
    Nat.odd_iff.mp (Nat.not_even_iff_odd.mp (fun he => by
      rcases (hzr v).1 he with h' | h'
      · exact hvz h'
      · exact hvr h'))
  have hevr : J.degree r % 2 = 0 := Nat.even_iff.mp ((hzr r).2 (Or.inr rfl))
  have hparK : ∀ v, v ≠ z → (delList J (zDel2 z (r :: T))).degree v % 2 =
      if v ∈ T then 0 else 1 := by
    intro v hvz
    have h := hdegK v
    rw [if_neg hvz, zero_add] at h
    by_cases hvr : v = r
    · subst hvr
      rw [if_pos List.mem_cons_self] at h
      rw [if_neg hrT]
      omega
    · have ho := hoddJ v hvz hvr
      by_cases hvT : v ∈ T
      · rw [if_pos (List.mem_cons_of_mem _ hvT)] at h
        rw [if_pos hvT]
        omega
      · have hvU : v ∉ r :: T := by rw [List.mem_cons, not_or]; exact ⟨hvr, hvT⟩
        rw [if_neg hvU] at h
        rw [if_neg hvT]
        omega
  -- the lower bound and the tight count
  have hmemPV : ∀ v, v ∈ L.map Prod.fst → v ∈ pairVerts L := by
    intro v hv; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv; exact fst_mem_pairVerts hq
  let f : V → ℕ := fun v => 2 * (if v ∈ L.map Prod.fst then 1 else 0) + (if v = r then 1 else 0) +
    (if v ∉ pairVerts L ∧ v ≠ z then 1 else 0)
  have hrpv : r ∈ pairVerts L := hmemPV r hrpar
  have hrsnd : r ∉ L.map Prod.snd := by
    obtain ⟨p, hp, hpr⟩ := List.mem_map.mp hrpar
    rw [← hpr]; exact hfs p hp
  have hle : ∀ v ∈ (Finset.univ : Finset V), f v ≤ D.ends v := by
    intro v _
    by_cases hvr : v = r
    · subst hvr
      simp only [f, hrpar, ite_true, hrpv, not_true_eq_false, false_and, ite_false, add_zero]
      omega
    by_cases hv : v ∈ L.map Prod.fst
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
      obtain ⟨P, hP, hform⟩ := hterm p hp
      have h1 : 1 ≤ P.endsAt p.1 := by
        unfold GPath.endsAt
        rcases hform with ⟨l, hl⟩ | ⟨l, hl⟩
        · rw [P.src_of_support hl]; simp
        · rw [P.tgt_of_support (l := l ++ [p.2]) (by rw [hl, List.append_assoc]; rfl)]; simp
      have h2 := D.endsAt_le_ends' hP p.1
      have hp1z : p.1 ≠ z := fun h => hzpv (h ▸ fst_mem_pairVerts hp)
      have hpT : p.1 ∈ T := by
        rcases (hcover p.1).1 (fst_mem_pairVerts hp) with h | h
        · exact absurd h hvr
        · exact h
      have he := hparK p.1 hp1z
      rw [if_pos hpT] at he
      have h3 := D.ends_mod_two p.1
      simp only [f, hv, hvr, ite_true, ite_false, fst_mem_pairVerts hp, not_true_eq_false,
        false_and, add_zero]
      omega
    · simp only [f, hv, hvr, ite_false, mul_zero, zero_add]
      split_ifs with h
      · have := hparK v h.2
        have hvT : v ∉ T := fun hT => h.1 ((hcover v).2 (Or.inr hT))
        rw [if_neg hvT] at this
        have h3 := D.ends_mod_two v
        omega
      · exact Nat.zero_le _
  have hcard1 : (insert z (pairVerts L).toFinset).card = 2 * L.length + 1 := by
    rw [Finset.card_insert_of_notMem (by simpa using hzpv), List.toFinset_card_of_nodup hnd, hlen]
  have hcardW : 2 * L.length + 1 ≤ Fintype.card V := by
    rw [← hcard1]; exact Finset.card_le_univ _
  have hsumf : ∑ v, f v = Fintype.card V := by
    have h1 : ∑ v : V, (if v ∈ L.map Prod.fst then 1 else 0) = L.length := by
      rw [Finset.sum_boole, Nat.cast_id]
      have : (Finset.univ.filter (fun v => v ∈ L.map Prod.fst)) = (L.map Prod.fst).toFinset := by
        ext v; simp
      rw [this, List.toFinset_card_of_nodup hfst, List.length_map]
    have h2 : ∑ v : V, (if v ∉ pairVerts L ∧ v ≠ z then 1 else 0) =
        Fintype.card V - (2 * L.length + 1) := by
      rw [Finset.sum_boole, Nat.cast_id]
      have : (Finset.univ.filter (fun v => v ∉ pairVerts L ∧ v ≠ z)) =
          (insert z (pairVerts L).toFinset)ᶜ := by
        ext v; simp [and_comm]
      rw [this, Finset.card_compl, hcard1]
    have h3 : ∑ v : V, (if v = r then 1 else 0) = 1 := by simp
    simp only [f, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2, h3]
    omega
  have hsumD : ∑ v, D.ends v ≤ Fintype.card V := by rw [D.sum_ends]; omega
  have heq : ∀ v, f v = D.ends v := by
    have hs : ∑ v, f v = ∑ v, D.ends v :=
      le_antisymm (Finset.sum_le_sum hle) (by rw [hsumf]; exact hsumD)
    intro v
    exact (Finset.sum_eq_sum_iff_of_le hle).mp hs v (Finset.mem_univ v)
  have hzero : ∀ p ∈ L, D.ends p.2 = 0 := by
    intro p hp
    rw [← heq]
    have hp2r : p.2 ≠ r := fun h => hsf p hp (h ▸ hrpar)
    simp only [f, hsf p hp, hp2r, ite_false, snd_mem_pairVerts hp, not_true_eq_false, false_and]
  -- drop the pair edges
  have hG : ∀ e, e ∈ (delList J (zDel2 z (r :: T) ++ L.map pairEdge)).edgeSet ↔
      e ∈ (delList J (zDel2 z (r :: T))).edgeSet ∧ e ∉ L.map pairEdge := by
    intro e
    rw [delList_edgeSet, delList_edgeSet, List.mem_append]
    tauto
  obtain ⟨D₁, hD₁e, hD₁av⟩ := drop_pairs L [] (delList J (zDel2 z (r :: T)))
    (delList J (zDel2 z (r :: T) ++ L.map pairEdge)) D (by simpa using hnd) hG hzero hterm
    (fun q hq => absurd hq (List.not_mem_nil))
  have hD₁ends : ∀ v, D₁.ends v + (if v ∈ L.map Prod.fst then 1 else 0) =
      f v + (if v ∈ L.map Prod.snd then 1 else 0) := by
    intro v
    have h := hD₁e v
    rw [countP_comp_of_nodup L Prod.fst hfst v, countP_comp_of_nodup L Prod.snd hsnd v,
      ← heq v] at h
    exact h
  have hr1 : D₁.ends r = 2 := by
    have h := hD₁ends r
    simp only [f, hrpar, hrsnd, ite_true, ite_false, hrpv, not_true_eq_false, false_and,
      add_zero] at h
    omega
  -- re-attach the leaf `zr`
  obtain ⟨P, hP, hPr⟩ := D₁.exists_path_of_ends_pos (show 1 ≤ D₁.ends r by omega)
  have hzG : ∀ x, ¬ (delList J (zDel2 z (r :: T) ++ L.map pairEdge)).Adj z x := by
    intro x hx
    have hxU : x ∈ r :: T := List.mem_cons.mpr ((hF.nbr x).1 hx.1)
    exact hx.2 (List.mem_append_left _ (List.mem_map.mpr ⟨x, hxU, rfl⟩))
  have hzP : z ∉ P.walk.support := fun h => by
    obtain ⟨y, hy⟩ := GPath.adj_of_mem_support P h
    exact hzG y hy
  have hnadj : ¬ (delList J (zDel2 z (r :: T) ++ L.map pairEdge)).Adj r z := fun h => hzG r h.symm
  have hzrJ : J.Adj z r := (hF.nbr r).2 (Or.inl rfl)
  have hM : ∀ e, e ∈ (forM2 J z T (L.map Prod.swap)).edgeSet ↔
      e ∈ (delList J (zDel2 z (r :: T) ++ L.map pairEdge)).edgeSet ∨ e = s(r, z) := by
    intro e
    rw [delList_edgeSet, delList_edgeSet, List.mem_append, List.mem_append, mem_pairEdge_swap]
    have hzc : zDel2 z (r :: T) = s(z, r) :: zDel2 z T := rfl
    rw [hzc, List.mem_cons]
    constructor
    · rintro ⟨he, hn⟩
      by_cases her : e = s(z, r)
      · exact Or.inr (her.trans Sym2.eq_swap)
      · exact Or.inl ⟨he, by tauto⟩
    · rintro (⟨he, hn⟩ | rfl)
      · exact ⟨he, by tauto⟩
      · refine ⟨hzrJ.symm, ?_⟩
        rintro (h | h)
        · rw [hF.mem_zDel2] at h
          rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
          · exact hzr' h1.symm
          · exact hrT h2
        · obtain ⟨q, hq, hqe⟩ := List.mem_map.mp h
          have hz : z ∈ pairEdge q := by rw [hqe]; simp
          simp only [pairEdge, Sym2.mem_iff] at hz
          rcases hz with h | h
          · exact hzpv (h ▸ fst_mem_pairVerts hq)
          · exact hzpv (h ▸ snd_mem_pairVerts hq)
  obtain ⟨D₀, hD₀e, P', hP', hP'src, hP'case, hcls, -⟩ := append_full D₁ hnadj hM hP hPr hzP
  -- every vertex of `M` has odd degree
  have hzM : (forM2 J z T (L.map Prod.swap)).degree z = 1 := by
    rw [← card_neighborFinset_eq_degree, Finset.card_eq_one]
    refine ⟨r, ?_⟩
    ext x
    rw [mem_neighborFinset, Finset.mem_singleton]
    constructor
    · intro h; exact hF.leafT2_adj_z.1 ⟨h.1, fun h' => h.2 (List.mem_append_left _ h')⟩
    · rintro rfl
      exact ((hM _).2 (Or.inr Sym2.eq_swap))
  have hoddM : ∀ v, (forM2 J z T (L.map Prod.swap)).degree v % 2 = 1 := by
    intro v
    by_cases hvz : v = z
    · subst hvz; rw [hzM]
    have h := hF.forM2_degree v
    have ht := hF.tjoin v
    rw [if_neg hvz, zero_add] at h
    by_cases hvr : v = r
    · subst hvr
      rw [if_neg hrT] at h
      simp only [true_or, ite_true] at ht
      omega
    · have ho := hoddJ v hvz hvr
      by_cases hvT : v ∈ T
      · rw [if_pos hvT] at h
        simp only [hvT, or_true, ite_true] at ht
        omega
      · rw [if_neg hvT] at h
        simp only [hvr, hvT, or_false, ite_false] at ht
        omega
  refine ⟨D₀, fun v => ?_, ?_, ?_⟩
  · -- one end at every vertex
    rw [hoddM v]
    have h0 := hD₀e v
    have h1 := hD₁ends v
    by_cases hvz : v = z
    · subst hvz
      have hf : v ∉ L.map Prod.fst := fun h => hzpv (hmemPV v h)
      have hs : v ∉ L.map Prod.snd := fun h => hzpv (by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h; exact snd_mem_pairVerts hq)
      have hvr : r ≠ v := Ne.symm hzr'
      have hfv : f v = 0 := by
        simp only [f]
        rw [if_neg hf, if_neg (Ne.symm hvr), if_neg (fun h => h.2 rfl)]
      rw [if_neg hf, if_neg hs, hfv] at h1
      rw [if_neg hvr, if_pos rfl] at h0
      omega
    · by_cases hvr : v = r
      · subst hvr
        simp [Ne.symm hvz] at h0
        omega
      · simp only [Ne.symm hvr, Ne.symm hvz, ite_false, add_zero] at h0
        by_cases hf : v ∈ L.map Prod.fst
        · have hs : v ∉ L.map Prod.snd := by
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hf; exact hfs q hq
          simp only [f, hf, hs, hvr, ite_true, ite_false, hmemPV v hf, not_true_eq_false,
            false_and, add_zero] at h1
          omega
        · by_cases hs : v ∈ L.map Prod.snd
          · have hv : v ∈ pairVerts L := by
              obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs; exact snd_mem_pairVerts hq
            simp only [f, hf, hs, hvr, hv, ite_true, ite_false, not_true_eq_false, false_and,
              mul_zero, zero_add] at h1
            omega
          · have hv : v ∉ pairVerts L := fun h => by
              rcases mem_pairVerts.mp h with ⟨q, hq, rfl | rfl⟩
              · exact hf (List.mem_map_of_mem hq)
              · exact hs (List.mem_map_of_mem hq)
            simp only [f, hf, hs, hvr, hv, hvz, ite_false, mul_zero, zero_add, not_false_eq_true,
              ne_eq, and_self, ite_true] at h1
            omega
  · -- (i): the path ending at a child avoids its parent
    intro p hp Q hQ hend
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    simp only [Prod.fst_swap, Prod.snd_swap] at hend ⊢
    have hav := hD₁av q (by simpa using hq)
    have hq1z : q.1 ≠ z := fun h => hzpv (h ▸ fst_mem_pairVerts hq)
    have hq2z : q.2 ≠ z := fun h => hzpv (h ▸ snd_mem_pairVerts hq)
    rcases hcls Q hQ with rfl | ⟨Q₀, hQ₀, hs, ht, hsupp⟩
    · -- the path through the new leaf edge
      have hend' : Q.tgt = q.2 := by
        rcases hend with h | h
        · exact absurd (hP'src.symm.trans h) (Ne.symm hq2z)
        · exact h
      rcases hP'case with ⟨hPs, hPt, hPsupp⟩ | ⟨hPt, hPs, hPsupp⟩
      · rw [hPsupp, List.mem_cons, not_or]
        exact ⟨hq1z, hav P hP (Or.inr (hPt.symm.trans hend'))⟩
      · rw [hPsupp, List.mem_cons, not_or, List.mem_reverse]
        exact ⟨hq1z, hav P hP (Or.inl (hPs.symm.trans hend'))⟩
    · rw [hsupp]
      rw [hs, ht] at hend
      exact hav Q₀ hQ₀ hend
  · -- (ii): in a matching no two children share a parent
    intro p hp q hq hne hpar
    exfalso
    obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp
    obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq
    simp only [Prod.fst_swap, Prod.snd_swap] at hne hpar
    have := pair_eq_of_share hnd hp₀ hq₀ (x := p₀.1) (Or.inl rfl) (Or.inl hpar)
    exact hne (by rw [this])

end rootedConverse

section transport

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **From `J − z` to `J` with `z` isolated.** A decomposition of `delVert J z` gives one of `J`
minus all edges at `z`, with the same size, the same ends (and none at `z`), and the same
supports. -/
theorem exists_isolated_of_delVert (J : SimpleGraph V) [DecidableRel J.Adj] {z : V} {U : List V}
    (hU : ∀ v, J.Adj z v ↔ v ∈ U) (D : PathDecomp (delVert J z)) :
    ∃ D' : PathDecomp (delList J (zDel2 z U)), D'.size = D.size ∧
      (∀ v : {v | v ≠ z}, D'.ends v = D.ends v) ∧
      (∀ P ∈ D.paths, ∃ P' ∈ D'.paths, P'.walk.support = P.walk.support.map Subtype.val) := by
  have hmemz : ∀ {x y : V}, s(x, y) ∈ zDel2 z U → x = z ∨ y = z := by
    intro x y h
    rw [zDel2, List.mem_map] at h
    obtain ⟨u, -, hu⟩ := h
    rcases Sym2.eq_iff.1 hu with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1.symm
    · exact Or.inr h1.symm
  have hE : ∀ e ∈ (delVert J z).edgeSet, e.map Subtype.val ∈ (delList J (zDel2 z U)).edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf a b =>
    rw [Sym2.map_mk, delList_edgeSet]
    refine ⟨he, fun h => ?_⟩
    rcases hmemz h with h | h
    · exact a.2 h
    · exact b.2 h
  have hcov : ∀ e' ∈ (delList J (zDel2 z U)).edgeSet,
      ∃ e ∈ (delVert J z).edgeSet, e.map Subtype.val = e' := by
    intro e' he'
    induction e' using Sym2.inductionOn with
    | hf x y =>
    rw [delList_edgeSet] at he'
    obtain ⟨hxy, hn⟩ := he'
    have hx : x ≠ z := by
      rintro rfl
      exact hn (List.mem_map.mpr ⟨y, (hU y).1 hxy, rfl⟩)
    have hy : y ≠ z := by
      rintro rfl
      exact hn (List.mem_map.mpr ⟨x, (hU x).1 hxy.symm, Sym2.eq_swap⟩)
    exact ⟨s(⟨x, hx⟩, ⟨y, hy⟩), hxy, rfl⟩
  refine ⟨D.mapInj Subtype.val Subtype.val_injective hE hcov,
    PathDecomp.mapInj_size _ _ _ _ _, fun v => PathDecomp.mapInj_ends _ _ _ _ _ v,
    fun P hP => ⟨P.mapInj Subtype.val Subtype.val_injective hE, List.mem_map_of_mem hP, ?_⟩⟩
  simp [GPath.mapInj]

/-- **The converse of the forest lift, matching case, for the test itself.** As
`forestBase2_matching_of_terminal`, with `D` a decomposition of `J − z` (the conclusion of Test2):
every pair edge `tᵢsᵢ` is the end edge, at `tᵢ`, of its path. -/
theorem forestBase2_matching_of_test2 (J : SimpleGraph V) [DecidableRel J.Adj] {z r : V}
    (hzr : ∀ v, Even (J.degree v) ↔ v = z ∨ v = r) (hr : J.Adj z r) {T : List V}
    {L : List (V × V)} (hF : ForestData2 J z r T (L.map Prod.swap)) (hnd : (pairVerts L).Nodup)
    (hcover : ∀ v, v ∈ pairVerts L ↔ v = r ∨ v ∈ T) (hrpar : r ∈ L.map Prod.fst)
    (D : PathDecomp (delVert J z)) (hsize : D.size ≤ Fintype.card V / 2)
    (hr3 : 3 ≤ D.ends ⟨r, hr.ne'⟩)
    (hterm : ∀ p ∈ L, ∃ P ∈ D.paths, (∃ l, P.walk.support.map Subtype.val = p.1 :: p.2 :: l) ∨
      (∃ l, P.walk.support.map Subtype.val = l ++ [p.2, p.1])) :
    ForestBase2 J z r := by
  have hU : ∀ v, J.Adj z v ↔ v ∈ r :: T := fun v => (hF.nbr v).trans (by simp)
  obtain ⟨D', hD's, hD'e, hD'supp⟩ := exists_isolated_of_delVert J hU D
  have hr3' : 3 ≤ D'.ends r := by
    have h := hD'e ⟨r, hr.ne'⟩
    simp only at h
    rw [h]; exact hr3
  have hterm' : ∀ p ∈ L, TermAt D' p.1 p.2 := by
    intro p hp
    obtain ⟨P, hP, hform⟩ := hterm p hp
    obtain ⟨P', hP', hsupp⟩ := hD'supp P hP
    exact ⟨P', hP', by rw [hsupp]; exact hform⟩
  obtain ⟨D₀, h1, h2, h3⟩ := forestBase2_matching_of_terminal J hzr hF hnd hcover hrpar D'
    (by rw [hD's]; exact hsize) hr3' hterm'
  exact ⟨T, L.map Prod.swap, hF, D₀, h1, h2, h3⟩

end transport

end Gallai
