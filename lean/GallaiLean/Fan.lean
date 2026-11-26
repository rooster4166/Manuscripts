import GallaiLean.FanMoves

/-!
# Fan's addible-edge lemmas (Fan 2005, Lemmas 3.3–3.4)

For a decomposition `D` of `K`, a vertex `u` and a vertex `x ≠ u`, read a path of `D` from its
end `x`. If it reaches `u`, the vertex just before `u` is a *predecessor* (`FanPred D u x z`).
A *chain* from `t` is a duplicate-free sequence `t = x₀, x₁, …, x_k`. Each `x_{i+1}` is a
predecessor reached from `x_i`, and some path with an end at `x_k` avoids `u` (`FanChain`).

* `fan_exec`: along a chain from a non-neighbour `t` of `u`, the edge `tu` can be added. Each
  step is a single `reroute_move` and the last step is an `append_move`. Size is unchanged, `t`
  loses an end and `u` gains one.
* `fan_exists_chain`: if `∑_{t ∈ T} ends t > #{w ∈ N(u) : ends w = 0}`, some `t ∈ T` starts a
  chain. This is the counting/injection argument: endpoint occurrences at the reachable set map
  injectively to edges from `u` into it.
* **`fan_grouped`** (Fan's grouped transfer, Lemma 3.3 as used): some `t ∈ T` admits the
  transfer `t → u`.
* **`fan_single`** (Fan's Lemma 3.4): for `uv ∈ E(G)` and a decomposition `D'` of `G − uv` with
  `ends v > #{w ∈ N_{G−uv}(u) : ends w = 0}`, `G` has a decomposition of the same size with one
  more end at `u`, one fewer at `v`, and the same ends elsewhere.
-/

open SimpleGraph

namespace Gallai

universe v

variable {U : Type v} [DecidableEq U]

/-! ### Chains -/

section chain

variable {K : SimpleGraph U}

/-- Reading some path of `D` from its end `x`, the vertex just before `u` is `z`. -/
def FanPred (D : PathDecomp K) (u x z : U) : Prop :=
  ∃ P ∈ D.paths, (P.src = x ∧ [z, u] <:+: P.walk.support) ∨
    (P.tgt = x ∧ [u, z] <:+: P.walk.support)

/-- Some path of `D` with an end at `x` avoids `u`. -/
def FanAvoid (D : PathDecomp K) (u x : U) : Prop :=
  ∃ P ∈ D.paths, (P.src = x ∨ P.tgt = x) ∧ u ∉ P.walk.support

/-- Consecutive vertices are related by `FanPred`. -/
def FanPre (D : PathDecomp K) (u : U) : List U → Prop
  | [] => False
  | [_] => True
  | x :: y :: rest => FanPred D u x y ∧ FanPre D u (y :: rest)

/-- A chain: a `FanPre` sequence whose last vertex has a path end avoiding `u`. -/
def FanChain (D : PathDecomp K) (u : U) (l : List U) : Prop :=
  FanPre D u l ∧ ∃ x, l.getLast? = some x ∧ FanAvoid D u x

omit [DecidableEq U] in
theorem FanPred.adj {D : PathDecomp K} {u x z : U} (h : FanPred D u x z) : K.Adj z u := by
  obtain ⟨P, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := h
  · exact Walk.adj_of_infix_support P.walk h
  · exact (Walk.adj_of_infix_support P.walk h).symm

omit [DecidableEq U] in
theorem FanPre.transport {K₁ : SimpleGraph U} {D : PathDecomp K} {D₁ : PathDecomp K₁} {u t : U}
    (h : ∀ x z, x ≠ t → FanPred D u x z → FanPred D₁ u x z) :
    ∀ l : List U, t ∉ l → FanPre D u l → FanPre D₁ u l
  | [], _, h' => h'
  | [_], _, _ => trivial
  | x :: y :: rest, ht, h' => by
    obtain ⟨h1, h2⟩ := h'
    exact ⟨h x y (by rintro rfl; exact ht List.mem_cons_self) h1,
      FanPre.transport h (y :: rest) (fun hm => ht (List.mem_cons_of_mem _ hm)) h2⟩

omit [DecidableEq U] in
theorem FanPre.snoc {D : PathDecomp K} {u : U} :
    ∀ (L : List U) (x z : U), FanPre D u L → L.getLast? = some x → FanPred D u x z →
      FanPre D u (L ++ [z])
  | [], _, _, h, _, _ => h.elim
  | [a], x, z, _, hl, hp => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hl
    subst hl
    exact ⟨hp, trivial⟩
  | a :: b :: rest, x, z, h, hl, hp => by
    obtain ⟨h1, h2⟩ := h
    exact ⟨h1, FanPre.snoc (b :: rest) x z h2 (by simpa using hl) hp⟩

omit [DecidableEq U] in
theorem FanPre.prefix {D : PathDecomp K} {u : U} :
    ∀ (L₁ : List U) (z : U) (L₂ : List U), FanPre D u (L₁ ++ z :: L₂) → FanPre D u (L₁ ++ [z])
  | [], _, _, _ => trivial
  | [_], _, _, h => by
    obtain ⟨h1, -⟩ := h
    exact ⟨h1, trivial⟩
  | _ :: b :: rest, z, L₂, h => by
    obtain ⟨h1, h2⟩ := h
    exact ⟨h1, FanPre.prefix (b :: rest) z L₂ h2⟩

omit [DecidableEq U] in
theorem FanPre.last {D : PathDecomp K} {u : U} :
    ∀ (L : List U) (x : U), FanPre D u L → L.getLast? = some x →
      L.head? = some x ∨ ∃ w, FanPred D u w x
  | [], _, h, _ => h.elim
  | [_], _, _, hl => Or.inl (by simpa using hl)
  | a :: b :: rest, x, h, hl => by
    obtain ⟨h1, h2⟩ := h
    rcases FanPre.last (b :: rest) x h2 (by simpa using hl) with h' | h'
    · simp only [List.head?_cons, Option.some.injEq] at h'
      subst h'
      exact Or.inr ⟨a, h1⟩
    · exact Or.inr h'

omit [DecidableEq U] in
/-- Chains survive a reroute away from their vertices. -/
theorem fanChain_transport {K₁ : SimpleGraph U} {D : PathDecomp K} {D₁ : PathDecomp K₁}
    {u t : U} {P : GPath K} (huP : u ∈ P.walk.support)
    (htrans : ∀ Q ∈ D.paths, Q ≠ P → ∃ Q' ∈ D₁.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
      Q'.walk.support = Q.walk.support)
    (hP' : ∃ P' ∈ D₁.paths, ∀ x z, x ≠ t →
      ((P.src = x ∧ [z, u] <:+: P.walk.support) ∨ (P.tgt = x ∧ [u, z] <:+: P.walk.support)) →
      (P'.tgt = x ∧ [u, z] <:+: P'.walk.support)) :
    ∀ l, t ∉ l → FanChain D u l → FanChain D₁ u l := by
  have hpred : ∀ x z, x ≠ t → FanPred D u x z → FanPred D₁ u x z := by
    rintro x z hx ⟨Q, hQ, hocc⟩
    by_cases hQP : Q = P
    · subst hQP
      obtain ⟨P', hP'mem, hP'⟩ := hP'
      exact ⟨P', hP'mem, Or.inr (hP' x z hx hocc)⟩
    · obtain ⟨Q', hQ', hs, ht, hsupp⟩ := htrans Q hQ hQP
      refine ⟨Q', hQ', ?_⟩
      rcases hocc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨hs.trans h1, by rw [hsupp]; exact h2⟩
      · exact Or.inr ⟨ht.trans h1, by rw [hsupp]; exact h2⟩
  intro l hl ⟨hpre, x, hx, Q, hQ, hend, hu⟩
  refine ⟨FanPre.transport hpred l hl hpre, x, hx, ?_⟩
  have hQP : Q ≠ P := by rintro rfl; exact hu huP
  obtain ⟨Q', hQ', hs, ht, hsupp⟩ := htrans Q hQ hQP
  exact ⟨Q', hQ', hend.imp (fun h => hs.trans h) (fun h => ht.trans h),
    by rw [hsupp]; exact hu⟩

/-- **Executing a chain**: along a chain from a non-neighbour `t` of `u`, add the edge `tu`. -/
theorem fan_exec (u : U) (xs : List U) : ∀ {K : SimpleGraph U} (D : PathDecomp K) (t : U),
    (t :: xs).Nodup → FanChain D u (t :: xs) → t ≠ u → ¬ K.Adj t u →
    ∀ K' : SimpleGraph U, (∀ e, e ∈ K'.edgeSet ↔ e ∈ K.edgeSet ∨ e = s(t, u)) →
    ∃ D' : PathDecomp K', D'.size = D.size ∧
      ∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if u = w then 1 else 0) := by
  induction xs with
  | nil =>
    intro K D t _ hch _ hadj K' hK'
    obtain ⟨-, x, hx, P, hP, hend, hu⟩ := hch
    simp only [List.getLast?_singleton, Option.some.injEq] at hx
    subst hx
    exact D.append_move hadj hK' hP hend hu
  | cons y rest ih =>
    intro K D t hnd hch htu hadj K' hK'
    obtain ⟨hpre, x, hx, hav⟩ := hch
    obtain ⟨hpred, hpre'⟩ := hpre
    have hch' : FanChain D u (y :: rest) := ⟨hpre', x, by simpa using hx, hav⟩
    have hyu : K.Adj y u := FanPred.adj hpred
    obtain ⟨P, hP, hocc⟩ := hpred
    have hty : t ≠ y := by
      rintro rfl; exact (List.nodup_cons.mp hnd).1 List.mem_cons_self
    have hyu' : y ≠ u := hyu.ne
    let K₁ : SimpleGraph U := SimpleGraph.fromEdgeSet ((K.edgeSet \ {s(y, u)}) ∪ {s(t, u)})
    have hK₁ : ∀ e, e ∈ K₁.edgeSet ↔ (e ∈ K.edgeSet ∧ e ≠ s(y, u)) ∨ e = s(t, u) := by
      intro e
      simp only [K₁, edgeSet_fromEdgeSet, Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff,
        Sym2.mem_diagSet]
      constructor
      · rintro ⟨h, -⟩; exact h
      · intro h
        refine ⟨h, ?_⟩
        rcases h with ⟨he, -⟩ | rfl
        · exact K.not_isDiag_of_mem_edgeSet he
        · simpa using htu
    obtain ⟨D₁, hs₁, he₁, htrans, hP'⟩ := D.reroute_move hadj hK₁ hP hocc
    have huP : u ∈ P.walk.support := by
      rcases hocc with ⟨-, h⟩ | ⟨-, h⟩ <;> exact h.subset (by simp)
    have hch₁ : FanChain D₁ u (y :: rest) :=
      fanChain_transport huP htrans hP' (y :: rest) (List.nodup_cons.mp hnd).1 hch'
    have hadj₁ : ¬ K₁.Adj y u := by
      rw [← mem_edgeSet, hK₁]
      rintro (⟨-, h⟩ | h)
      · exact h rfl
      · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hty h1.symm
        · exact hyu' h1
    have hK'₁ : ∀ e, e ∈ K'.edgeSet ↔ e ∈ K₁.edgeSet ∨ e = s(y, u) := by
      intro e
      rw [hK' e, hK₁ e]
      have hyuK : s(y, u) ∈ K.edgeSet := hyu
      constructor
      · rintro (h | h)
        · by_cases hey : e = s(y, u)
          · exact Or.inr hey
          · exact Or.inl (Or.inl ⟨h, hey⟩)
        · exact Or.inl (Or.inr h)
      · rintro ((⟨h, -⟩ | h) | h)
        · exact Or.inl h
        · exact Or.inr h
        · exact Or.inl (h ▸ hyuK)
    obtain ⟨D', hs', he'⟩ := ih D₁ y (List.nodup_cons.mp hnd).2 hch₁ hyu' hadj₁ K' hK'₁
    refine ⟨D', hs'.trans hs₁, fun w => ?_⟩
    have a := he' w
    have b := he₁ w
    omega

end chain

/-! ### Existence of a chain: the counting argument -/

section counting

variable [Fintype U] {K : SimpleGraph U} [DecidableRel K.Adj]

theorem two_le_countP {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup) (p : α → Bool)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) (hpa : p a = true) (hpb : p b = true) :
    2 ≤ l.countP p := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hl.filter p),
    ← Finset.card_pair hab]
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_insert, Finset.mem_singleton] at hx
  rw [List.mem_toFinset, List.mem_filter]
  rcases hx with rfl | rfl
  · exact ⟨ha, hpa⟩
  · exact ⟨hb, hpb⟩

omit [Fintype U] [DecidableRel K.Adj] in
theorem sum_ends_eq (D : PathDecomp K) (R : Finset U) :
    ∑ x ∈ R, D.ends x = (D.paths.map (fun P =>
      (if P.src ∈ R then 1 else 0) + (if P.tgt ∈ R then 1 else 0))).sum := by
  unfold PathDecomp.ends
  generalize D.paths = l
  induction l with
  | nil => simp
  | cons P l ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
    congr 1
    simp only [GPath.endsAt, Finset.sum_add_distrib, Finset.sum_ite_eq]

/-- **Existence of a chain** (the counting argument behind Fan's grouped lemma). -/
theorem fan_exists_chain (D : PathDecomp K) (u : U) (T : Finset U) (huT : u ∉ T)
    (hT : ∀ t ∈ T, ¬ K.Adj t u)
    (hsum : (Finset.univ.filter (fun w => K.Adj u w ∧ D.ends w = 0)).card <
      ∑ t ∈ T, D.ends t) :
    ∃ t ∈ T, ∃ xs, (t :: xs).Nodup ∧ FanChain D u (t :: xs) := by
  classical
  by_contra hno
  let Reach : U → Prop := fun x => ∃ t ∈ T, ∃ xs : List U, (t :: xs).Nodup ∧
    FanPre D u (t :: xs) ∧ (t :: xs).getLast? = some x
  have hnoav : ∀ x, Reach x → ¬ FanAvoid D u x := by
    rintro x ⟨t, ht, xs, hnd, hpre, hlast⟩ hav
    exact hno ⟨t, ht, xs, hnd, hpre, x, hlast, hav⟩
  let R : Finset U := Finset.univ.filter Reach
  have hTR : T ⊆ R := fun t ht =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ht, [], by simp, trivial, rfl⟩
  have hclos : ∀ x z, x ∈ R → FanPred D u x z → z ∈ R := by
    intro x z hx hp
    obtain ⟨t, ht, xs, hnd, hpre, hlast⟩ := (Finset.mem_filter.mp hx).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    by_cases hz : z ∈ t :: xs
    · obtain ⟨L₁, L₂, hL⟩ := List.append_of_mem hz
      cases L₁ with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hL
        obtain ⟨rfl, -⟩ := hL
        exact ⟨t, ht, [], by simp, trivial, rfl⟩
      | cons a L₁' =>
        simp only [List.cons_append, List.cons.injEq] at hL
        obtain ⟨-, hxs⟩ := hL
        refine ⟨t, ht, L₁' ++ [z], ?_, ?_, ?_⟩
        · have hsub : (t :: (L₁' ++ [z])).Sublist (t :: xs) := by
            rw [hxs]
            exact List.Sublist.cons_cons t
              (List.Sublist.append_left (List.singleton_sublist.mpr List.mem_cons_self) L₁')
          exact hnd.sublist hsub
        · have := FanPre.prefix (t :: L₁') z L₂ (by rw [List.cons_append, ← hxs]; exact hpre)
          simpa using this
        · rw [← List.cons_append, List.getLast?_concat]
    · refine ⟨t, ht, xs ++ [z], ?_, ?_, by rw [← List.cons_append, List.getLast?_concat]⟩
      · rw [← List.cons_append, List.nodup_append]
        refine ⟨hnd, List.nodup_singleton z, ?_⟩
        intro a ha b hb hab
        rw [List.mem_singleton] at hb
        subst hb hab
        exact hz ha
      · have := FanPre.snoc (t :: xs) x z hpre hlast hp
        simpa using this
  have hRadj : ∀ x ∈ R, x ∈ T ∨ K.Adj x u := by
    intro x hx
    obtain ⟨t, ht, xs, -, hpre, hlast⟩ := (Finset.mem_filter.mp hx).2
    rcases FanPre.last (t :: xs) x hpre hlast with h | ⟨w, hw⟩
    · simp only [List.head?_cons, Option.some.injEq] at h
      exact Or.inl (h ▸ ht)
    · exact Or.inr (FanPred.adj hw)
  have huR : u ∉ R := fun hu => by
    rcases hRadj u hu with h | h
    · exact huT h
    · exact K.loopless.irrefl u h
  -- every end at `R` lies on a path through `u`
  have hthru : ∀ P ∈ D.paths, ∀ x ∈ R, (P.src = x ∨ P.tgt = x) → u ∈ P.walk.support := by
    intro P hP x hx hend
    by_contra hu
    exact hnoav x (Finset.mem_filter.mp hx).2 ⟨P, hP, hend, hu⟩
  let p : Sym2 U → Bool := fun e => decide (u ∈ e ∧ ∃ z ∈ R, z ∈ e)
  -- per path: ends at `R` ≤ edges from `u` into `R`
  have hper : ∀ P ∈ D.paths,
      (if P.src ∈ R then 1 else 0) + (if P.tgt ∈ R then 1 else 0) ≤ P.edges.countP p := by
    intro P hP
    have hnd : P.edges.Nodup := P.isPath.isTrail.edges_nodup
    have hsrc : P.src ∈ R → ∃ d ∈ P.walk.darts, d.snd = u ∧ p d.edge = true := by
      intro hs
      have hu := hthru P hP _ hs (Or.inl rfl)
      have hne : u ≠ P.src := fun h => huR (h ▸ hs)
      obtain ⟨d, hd, hdu⟩ := Walk.exists_dart_snd_eq P.walk hu hne
      have hinf : [d.fst, u] <:+: P.walk.support := by
        rw [← hdu]; exact Walk.mem_darts_iff_fst_snd_infix_support.mp hd
      have hzR : d.fst ∈ R := hclos _ _ hs ⟨P, hP, Or.inl ⟨rfl, hinf⟩⟩
      refine ⟨d, hd, hdu, ?_⟩
      simp only [p, decide_eq_true_eq, Dart.edge, Sym2.mem_iff]
      exact ⟨Or.inr hdu.symm, d.fst, hzR, Or.inl rfl⟩
    have htgt : P.tgt ∈ R → ∃ d ∈ P.walk.darts, d.fst = u ∧ p d.edge = true := by
      intro hs
      have hu := hthru P hP _ hs (Or.inr rfl)
      have hne : u ≠ P.tgt := fun h => huR (h ▸ hs)
      obtain ⟨d, hd, hdu⟩ := Walk.exists_dart_fst_eq P.walk hu hne
      have hinf : [u, d.snd] <:+: P.walk.support := by
        rw [← hdu]; exact Walk.mem_darts_iff_fst_snd_infix_support.mp hd
      have hzR : d.snd ∈ R := hclos _ _ hs ⟨P, hP, Or.inr ⟨rfl, hinf⟩⟩
      refine ⟨d, hd, hdu, ?_⟩
      simp only [p, decide_eq_true_eq, Dart.edge, Sym2.mem_iff]
      exact ⟨Or.inl hdu.symm, d.snd, hzR, Or.inr rfl⟩
    have hmem : ∀ d ∈ P.walk.darts, d.edge ∈ P.edges := fun d hd =>
      List.mem_map_of_mem hd
    by_cases hs : P.src ∈ R <;> by_cases ht : P.tgt ∈ R
    · obtain ⟨d, hd, hdu, hpd⟩ := hsrc hs
      obtain ⟨d', hd', hdu', hpd'⟩ := htgt ht
      have hne : d.edge ≠ d'.edge := by
        intro h
        have := List.inj_on_of_nodup_map hnd hd hd' h
        subst this
        have hadj : K.Adj d.fst d.snd := d.adj
        rw [hdu, hdu'] at hadj
        exact K.loopless.irrefl u hadj
      have := two_le_countP hnd p (hmem d hd) (hmem d' hd') hne hpd hpd'
      simp only [hs, ht, ite_true]
      omega
    · obtain ⟨d, hd, -, hpd⟩ := hsrc hs
      have := List.countP_pos_iff.mpr ⟨d.edge, hmem d hd, hpd⟩
      simp only [hs, ht, ite_true, ite_false]
      omega
    · obtain ⟨d, hd, -, hpd⟩ := htgt ht
      have := List.countP_pos_iff.mpr ⟨d.edge, hmem d hd, hpd⟩
      simp only [hs, ht, ite_true, ite_false]
      omega
    · simp [hs, ht]
  -- edges from `u` into `R`
  let NR : Finset U := R.filter (fun z => K.Adj u z)
  have hcount : (D.paths.flatMap GPath.edges).countP p ≤ NR.card := by
    rw [List.countP_eq_length_filter,
      ← List.toFinset_card_of_nodup (D.nodup_edges.filter p)]
    refine (Finset.card_le_card ?_).trans (Finset.card_image_le (f := fun z => s(z, u)))
    intro e he
    rw [List.mem_toFinset, List.mem_filter] at he
    obtain ⟨heD, hpe⟩ := he
    simp only [p, decide_eq_true_eq] at hpe
    obtain ⟨hue, z, hzR, hze⟩ := hpe
    have hzu : z ≠ u := fun h => huR (h ▸ hzR)
    have he' : e = s(z, u) := (Sym2.mem_and_mem_iff hzu).mp ⟨hze, hue⟩
    have heK : e ∈ K.edgeSet := (D.covers e).2 heD
    rw [he'] at heK
    rw [Finset.mem_image]
    exact ⟨z, Finset.mem_filter.mpr ⟨hzR, (K.mem_edgeSet.mp heK).symm⟩, he'.symm⟩
  have hR : ∑ x ∈ R, D.ends x ≤ NR.card := by
    rw [sum_ends_eq]
    have hc : (D.paths.map (fun P => P.edges.countP p)).sum =
        (D.paths.flatMap GPath.edges).countP p := by
      rw [List.countP_flatMap]; rfl
    calc _ ≤ (D.paths.map (fun P => P.edges.countP p)).sum := sum_map_le_sum_map _ _ _ hper
      _ = _ := hc
      _ ≤ NR.card := hcount
  have hdisj : Disjoint T NR := by
    rw [Finset.disjoint_left]
    intro t ht htN
    exact hT t ht (Finset.mem_filter.mp htN).2.symm
  have h1 : ∑ t ∈ T, D.ends t + ∑ w ∈ NR, D.ends w ≤ ∑ x ∈ R, D.ends x := by
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset (Finset.union_subset hTR (Finset.filter_subset _ _))
  have hkey : ∀ S : Finset U,
      S.card ≤ ∑ w ∈ S, D.ends w + (S.filter (fun w => D.ends w = 0)).card := by
    intro S
    rw [Finset.card_filter, ← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro w _
    split_ifs <;> omega
  have h2 := hkey NR
  have h3 : (NR.filter (fun w => D.ends w = 0)).card ≤
      (Finset.univ.filter (fun w => K.Adj u w ∧ D.ends w = 0)).card := by
    apply Finset.card_le_card
    intro w hw
    simp only [NR, Finset.mem_filter] at hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hw.1.2, hw.2⟩
  omega

/-- **Fan's grouped transfer** (Lemma 3.3 as used; six-clique paper, Lemma 2). Let `T` be a set
of non-neighbours of `u` with `u ∉ T` and `∑_{t ∈ T} ends t > #{w ∈ N(u) : ends w = 0}`. Then
for some `t ∈ T`, every graph `K'` with edge set `E(K) ∪ {tu}` has a decomposition of the same
size with one more end at `u`, one fewer at `t`, and the same ends elsewhere. -/
theorem fan_grouped (D : PathDecomp K) (u : U) (T : Finset U) (huT : u ∉ T)
    (hT : ∀ t ∈ T, ¬ K.Adj t u)
    (hsum : (Finset.univ.filter (fun w => K.Adj u w ∧ D.ends w = 0)).card <
      ∑ t ∈ T, D.ends t) :
    ∃ t ∈ T, ∀ K' : SimpleGraph U, (∀ e, e ∈ K'.edgeSet ↔ e ∈ K.edgeSet ∨ e = s(t, u)) →
      ∃ D' : PathDecomp K', D'.size = D.size ∧
        ∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if u = w then 1 else 0) := by
  obtain ⟨t, ht, xs, hnd, hch⟩ := fan_exists_chain D u T huT hT hsum
  exact ⟨t, ht, fun K' hK' =>
    fan_exec u xs D t hnd hch (fun h => huT (h ▸ ht)) (hT t ht) K' hK'⟩

/-- **Fan's Lemma 3.4** (single edge). Let `uv ∈ E(G)`, let `G'` be `G − uv`, and let `D'`
decompose `G'`. If `ends v > #{w ∈ N_{G'}(u) : ends w = 0}`, then `G` has a decomposition of the
same size with one more end at `u`, one fewer at `v`, and the same ends elsewhere. -/
theorem fan_single {G G' : SimpleGraph U} [DecidableRel G'.Adj] {u v : U} (huv : G.Adj u v)
    (hG' : ∀ e, e ∈ G'.edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(u, v)) (D' : PathDecomp G')
    (h : (Finset.univ.filter (fun w => G'.Adj u w ∧ D'.ends w = 0)).card < D'.ends v) :
    ∃ D : PathDecomp G, D.size = D'.size ∧ D.ends u = D'.ends u + 1 ∧
      D.ends v + 1 = D'.ends v ∧ ∀ w, w ≠ u → w ≠ v → D.ends w = D'.ends w := by
  have huv' : u ≠ v := huv.ne
  obtain ⟨t, ht, hK⟩ := fan_grouped D' u {v} (by simpa using huv')
    (by
      intro t ht
      rw [Finset.mem_singleton] at ht
      subst ht
      rw [← mem_edgeSet, hG']
      rintro ⟨-, h⟩
      exact h Sym2.eq_swap)
    (by simpa using h)
  obtain rfl : t = v := Finset.mem_singleton.mp ht
  obtain ⟨D, hs, he⟩ := hK G (by
    intro e
    rw [hG' e]
    have hvu : s(t, u) = s(u, t) := Sym2.eq_swap
    have : s(u, t) ∈ G.edgeSet := huv
    constructor
    · intro he
      by_cases h' : e = s(u, t)
      · exact Or.inr (h'.trans hvu.symm)
      · exact Or.inl ⟨he, h'⟩
    · rintro (⟨he, -⟩ | rfl)
      · exact he
      · rw [hvu]; exact this)
  refine ⟨D, hs, ?_, ?_, ?_⟩
  · have := he u
    simp only [Ne.symm huv', ite_false, ite_true, add_zero] at this
    omega
  · have := he t
    simp only [huv', ite_false, ite_true, add_zero] at this
    omega
  · intro w hwu hwt
    have := he w
    simp only [Ne.symm hwu, Ne.symm hwt, ite_false, add_zero] at this
    exact this

/-- `fan_single` for `G' = G.deleteEdges {uv}`. -/
theorem fan_single_deleteEdges {G : SimpleGraph U} {u v : U}
    [DecidableRel (G.deleteEdges {s(u, v)}).Adj] (huv : G.Adj u v)
    (D' : PathDecomp (G.deleteEdges {s(u, v)}))
    (h : (Finset.univ.filter (fun w => (G.deleteEdges {s(u, v)}).Adj u w ∧ D'.ends w = 0)).card
      < D'.ends v) :
    ∃ D : PathDecomp G, D.size = D'.size ∧ D.ends u = D'.ends u + 1 ∧
      D.ends v + 1 = D'.ends v ∧ ∀ w, w ≠ u → w ≠ v → D.ends w = D'.ends w :=
  fan_single huv (fun e => by simp [edgeSet_deleteEdges]) D' h

end counting

end Gallai
