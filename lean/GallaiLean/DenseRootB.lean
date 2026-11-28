import GallaiLean.DenseRoot

/-!
# Theorem B: one connector (session `claude/dense-root`)

Manuscript: `manuscripts/dense-root`, Theorem 4.1 with `δ = 0`.

Let `d(r) = 2k − 2` and let `Q` be a path of `G = B − r` whose ends `q₁, q₂` are neighbours of `r`
and whose other vertices are not, such that every neighbour of `r` has odd degree in
`G' = G − E(Q)`. Take a Lovász decomposition of `G'`, keep `Q` as one member attached at one of its
ends, and match by Hall (`hallReassemble`).

* `GPath.liftLe`, `consPath`: `Q` together with a decomposition of `G − E(Q)` is a decomposition of
  `G`.
* `connector_core`: the Hall counting, for any attachment plan of the required shape.
* **`exists_decomp_of_connector`** (Theorem B, `δ = 0`), **`test1At_of_connector`**.
-/

open SimpleGraph Finset

namespace Gallai

universe u

section liftLe

variable {W : Type u}

/-- A path of `K` as a path of a supergraph `G`. -/
def GPath.liftLe {K G : SimpleGraph W} (h : K ≤ G) (P : GPath K) : GPath G :=
  ⟨P.src, P.tgt, P.walk.mapLe h, P.isPath.mapLe h, by rw [Walk.length_mapLe]; exact P.pos⟩

variable {K G : SimpleGraph W} (h : K ≤ G) (P : GPath K)

@[simp] theorem GPath.liftLe_src : (P.liftLe h).src = P.src := rfl
@[simp] theorem GPath.liftLe_tgt : (P.liftLe h).tgt = P.tgt := rfl
@[simp] theorem GPath.liftLe_edges : (P.liftLe h).edges = P.edges := Walk.edges_mapLe_eq_edges _ _
@[simp] theorem GPath.liftLe_support : (P.liftLe h).walk.support = P.walk.support :=
  Walk.support_mapLe_eq_support _ _
@[simp] theorem GPath.liftLe_endsAt [DecidableEq W] (v : W) :
    (P.liftLe h).endsAt v = P.endsAt v := rfl

end liftLe

section consPath

variable {W : Type u} [DecidableEq W]

theorem delList_le' (K : SimpleGraph W) (L : List (Sym2 W)) : delList K L ≤ K := fun _ _ h => h.1

/-- `Q` followed by the paths of a decomposition of `G − E(Q)`. -/
def consPath {G : SimpleGraph W} (Q : GPath G) (D : PathDecomp (delList G Q.edges)) :
    PathDecomp G where
  paths := Q :: D.paths.map (GPath.liftLe (delList_le' G Q.edges))
  nodup_edges := by
    rw [List.flatMap_cons, List.flatMap_map]
    simp only [GPath.liftLe_edges]
    rw [List.nodup_append]
    refine ⟨Q.isPath.edges_nodup, D.nodup_edges, ?_⟩
    intro a ha b hb hab
    subst hab
    have : a ∈ (delList G Q.edges).edgeSet := (D.covers a).mpr hb
    exact ((delList_edgeSet G Q.edges a).mp this).2 ha
  covers := by
    intro e
    rw [List.flatMap_cons, List.flatMap_map, List.mem_append]
    simp only [GPath.liftLe_edges]
    rw [← D.covers e, delList_edgeSet]
    constructor
    · intro he
      by_cases hq : e ∈ Q.edges
      · exact Or.inl hq
      · exact Or.inr ⟨he, hq⟩
    · rintro (h | h)
      · exact Q.walk.edges_subset_edgeSet h
      · exact h.1

variable {G : SimpleGraph W} (Q : GPath G) (D : PathDecomp (delList G Q.edges))

theorem consPath_length : (consPath Q D).paths.length = D.paths.length + 1 := by
  simp [consPath]

/-- The index of the `j`-th path of `D` in `consPath Q D`. -/
def consIdx (j : Fin D.paths.length) : Fin (consPath Q D).paths.length :=
  ⟨j.1 + 1, by rw [consPath_length]; omega⟩

/-- The index of `Q`. -/
def consZero : Fin (consPath Q D).paths.length := ⟨0, by rw [consPath_length]; omega⟩

theorem consPath_get_zero : (consPath Q D).paths.get (consZero Q D) = Q := rfl

theorem consPath_get_idx (j : Fin D.paths.length) :
    (consPath Q D).paths.get (consIdx Q D j) =
      (D.paths.get j).liftLe (delList_le' G Q.edges) := by
  simp [consPath, consIdx]

theorem consIdx_injective : Function.Injective (consIdx Q D) := by
  intro a b h
  simp only [consIdx, Fin.mk.injEq] at h
  exact Fin.ext (by omega)

theorem consIdx_ne_zero (j : Fin D.paths.length) : consIdx Q D j ≠ consZero Q D := by
  simp [consIdx, consZero, Fin.ext_iff]

theorem cons_cases (i : Fin (consPath Q D).paths.length) :
    i = consZero Q D ∨ ∃ j, i = consIdx Q D j := by
  rcases Nat.eq_zero_or_pos i.1 with h | h
  · left; exact Fin.ext h
  · right
    refine ⟨⟨i.1 - 1, ?_⟩, Fin.ext ?_⟩
    · have h1 := i.2
      have h2 := consPath_length Q D
      omega
    · simp only [consIdx]; omega

end consPath

section core

variable {W : Type u} [Fintype W] [DecidableEq W]

theorem delList_degree_of_notMem (K : SimpleGraph W) [DecidableRel K.Adj] (P : GPath K) {v : W}
    (hv : v ∉ P.walk.support) : (delList K P.edges).degree v = K.degree v := by
  have h := delList_degree_count K P.edges P.isPath.edges_nodup
    (fun e he => P.walk.edges_subset_edgeSet he) v
  have h0 : P.edges.countP (fun e => decide (v ∈ e)) = 0 := by
    rw [List.countP_eq_zero]
    intro e he hve
    exact hv (P.walk.mem_support_of_mem_edges he (of_decide_eq_true hve))
  omega

/-- **The counting of Theorem B.** `D` is a Lovász decomposition of `G − E(Q)` whose ends are the
neighbours of `r`; every path `j` is attached at `att j` and has far end `lo j`; `Q` is attached at
`q_Q = lo iQ`; the other vertices of `Q` that are neighbours of `r` are attachments; `π j` is a
designated partner of the far end `lo j` (`j ≠ iQ`), injective, heavier, and off `Q`. -/
theorem connector_core (B : SimpleGraph W) [DecidableRel B.Adj] {k : ℕ} (hk : 2 ≤ k) {r : W}
    (hr : B.degree r + 2 = 2 * k) (Q : GPath (starDel B r))
    (D : PathDecomp (delList (starDel B r) Q.edges))
    (hDends : ∀ v, D.ends v = if B.Adj r v then 1 else 0)
    (hm : D.paths.length + 1 = k)
    (att lo : Fin D.paths.length → W)
    (hor : ∀ j, (att j = (D.paths.get j).src ∧ lo j = (D.paths.get j).tgt) ∨
      (att j = (D.paths.get j).tgt ∧ lo j = (D.paths.get j).src))
    (qQ : W) (hqQ : qQ = Q.src ∨ qQ = Q.tgt) (iQ : Fin D.paths.length) (hiQ : lo iQ = qQ)
    (hQdes : ∀ v ∈ Q.walk.support, B.Adj r v → v ≠ qQ → ∃ j, att j = v)
    (π : Fin D.paths.length → W)
    (hπdes : ∀ j, j ≠ iQ → ∃ j', att j' = π j)
    (hπinj : ∀ j j', j ≠ iQ → j' ≠ iQ → π j = π j' → j = j')
    (hπdeg : ∀ j, j ≠ iQ → B.degree (lo j) ≤ B.degree (π j))
    (hπQ : ∀ j, j ≠ iQ → π j ∉ Q.walk.support)
    (lam : ℕ)
    (hlam : ∑ v ∈ Q.walk.support.toFinset,
      ((delList (starDel B r) Q.edges).degree v + 1) / 2 ≤ lam)
    (hstar : ∀ t, 3 ≤ t → t ≤ k - 1 →
      #((heavyNbrs B r t).filter (fun x => x ∉ Q.walk.support)) / 2 +
          (if t ≤ lam then 1 else 0) + t ≤ k + 1 ∨
      #((heavyNbrs B r (t + 1)).filter (fun x => x ∉ Q.walk.support)) / 2 +
          (if t ≤ lam then 1 else 0) + 2 * t ≤ k + 1) :
    ∃ D' : PathDecomp B, D'.size = k ∧ D'.ends r = 2 := by
  classical
  set P := D.paths.get with hP
  -- ends
  have hends1 : ∀ v, D.ends v ≤ 1 := fun v => by rw [hDends v]; split_ifs <;> omega
  have hend_pos : ∀ i v, 1 ≤ (P i).endsAt v → 1 ≤ D.ends v :=
    fun i v h => h.trans (D.endsAt_le_ends v i)
  have hend_adj : ∀ i v, 1 ≤ (P i).endsAt v → B.Adj r v := by
    intro i v h
    have := hend_pos i v h
    rw [hDends v] at this
    by_contra hn; rw [if_neg hn] at this; omega
  have hend_uniq : ∀ i j v, 1 ≤ (P i).endsAt v → 1 ≤ (P j).endsAt v → i = j := by
    intro i j v hi hj
    by_contra hij
    have := D.two_le_ends_of_ne hij hi hj
    have := hends1 v
    omega
  have hatt_end : ∀ j, 1 ≤ (P j).endsAt (att j) := by
    intro j; rcases hor j with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    exacts [(P j).endsAt_src, (P j).endsAt_tgt]
  have hlo_end : ∀ j, 1 ≤ (P j).endsAt (lo j) := by
    intro j; rcases hor j with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
    exacts [(P j).endsAt_tgt, (P j).endsAt_src]
  have hattr : ∀ j, B.Adj r (att j) := fun j => hend_adj j _ (hatt_end j)
  have hlor : ∀ j, B.Adj r (lo j) := fun j => hend_adj j _ (hlo_end j)
  have hatt_inj : Function.Injective att := fun i j h =>
    hend_uniq i j (att i) (hatt_end i) (h ▸ hatt_end j)
  have hlo_inj : Function.Injective lo := fun i j h =>
    hend_uniq i j (lo i) (hlo_end i) (h ▸ hlo_end j)
  have hlo_att : ∀ i j, lo i ≠ att j := by
    intro i j h
    have := hend_uniq i j _ (hlo_end i) (h ▸ hatt_end j)
    subst this
    rcases hor i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (P i).src_ne_tgt (h1.symm.trans (h.symm.trans h2))
    · exact (P i).src_ne_tgt (h2.symm.trans (h.trans h1))
  have hqQr : B.Adj r qQ := hiQ ▸ hlor iQ
  have hqQatt : ∀ j, att j ≠ qQ := fun j h => hlo_att iQ j (hiQ.trans h.symm)
  have hloQ : ∀ j, j ≠ iQ → lo j ∉ Q.walk.support := by
    intro j hj hm'
    have hne : lo j ≠ qQ := fun h => hj (hlo_inj (h.trans hiQ.symm))
    obtain ⟨j', hj'⟩ := hQdes _ hm' (hlor j) hne
    exact hlo_att j j' hj'.symm
  -- the decomposition of `G` with `Q` first
  set D2 := consPath Q D with hD2
  have hlen : D2.paths.length = D.paths.length + 1 := consPath_length Q D
  let attP : Fin D2.paths.length → W := fun i =>
    if h : i.1 = 0 then qQ else att ⟨i.1 - 1, by have := i.2; have := hlen; omega⟩
  have hattP0 : attP (consZero Q D) = qQ := by simp [attP, consZero]
  have hattPj : ∀ j, attP (consIdx Q D j) = att j := by
    intro j; simp [attP, consIdx]
  have hget0 := consPath_get_zero Q D
  have hgetj := consPath_get_idx Q D
  have hattP_end : ∀ i, attP i = (D2.paths.get i).src ∨ attP i = (D2.paths.get i).tgt := by
    intro i
    rcases cons_cases Q D i with rfl | ⟨j, rfl⟩
    · rw [hattP0, hget0]; exact hqQ
    · rw [hattPj, hgetj]
      rcases hor j with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
  have hattPr : ∀ i, B.Adj r (attP i) := by
    intro i
    rcases cons_cases Q D i with rfl | ⟨j, rfl⟩
    · rw [hattP0]; exact hqQr
    · rw [hattPj]; exact hattr j
  have hattP_inj : Function.Injective attP := by
    intro a b h
    rcases cons_cases Q D a with rfl | ⟨j, rfl⟩ <;> rcases cons_cases Q D b with rfl | ⟨j', rfl⟩
    · rfl
    · rw [hattP0, hattPj] at h; exact absurd h.symm (hqQatt j')
    · rw [hattP0, hattPj] at h; exact absurd h (hqQatt j)
    · rw [hattPj, hattPj] at h; rw [hatt_inj h]
  -- the A-paths are the paths of `D`
  set Aset := univ.image (consIdx Q D) with hAset
  have hAcard : #Aset + 1 = k := by
    rw [hAset, card_image_of_injective _ (consIdx_injective Q D), card_univ, Fintype.card_fin]
    exact hm
  have hAimg : Aset.image attP = univ.image att := by
    ext x
    simp only [hAset, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, ⟨j, rfl⟩, rfl⟩; exact ⟨j, (hattPj j).symm⟩
    · rintro ⟨j, rfl⟩; exact ⟨consIdx Q D j, ⟨j, rfl⟩, hattPj j⟩
  set Cset := B.neighborFinset r \ Aset.image attP with hCset
  have hCmem : ∀ c, c ∈ Cset ↔ B.Adj r c ∧ ∀ j, att j ≠ c := by
    intro c
    rw [hCset, hAimg, mem_sdiff, mem_neighborFinset, mem_image]
    simp only [mem_univ, true_and, not_exists]
  have hInQ : ∀ v, InMember D2 attP qQ v ↔ v ∈ Q.walk.support := by
    intro v
    rw [← hattP0, inMember_att D2 attP hattP_end hattP_inj, hget0]
  have hInT : ∀ c ∈ Cset, c ≠ qQ → ∀ v, InMember D2 attP c v ↔ v = c := by
    intro c hc hcq v
    apply inMember_triv
    intro i h
    rcases cons_cases Q D i with rfl | ⟨j, rfl⟩
    · rw [hattP0] at h; exact hcq h.symm
    · rw [hattPj] at h; exact ((hCmem c).mp hc).2 j h
  have htrivQ : ∀ c ∈ Cset, c ≠ qQ → c ∉ Q.walk.support := by
    intro c hc hcq hcQ
    obtain ⟨j, hj⟩ := hQdes c hcQ ((hCmem c).mp hc).1 hcq
    exact ((hCmem c).mp hc).2 j hj
  have htriv_lo : ∀ c ∈ Cset, c ≠ qQ → ∃ j, j ≠ iQ ∧ lo j = c := by
    intro c hc hcq
    have hadj := ((hCmem c).mp hc).1
    have h1 : D.ends c = 1 := by rw [hDends c, if_pos hadj]
    rw [D.ends_eq_sum_get] at h1
    obtain ⟨j, -, hj⟩ := exists_ne_zero_of_sum_ne_zero (h1.trans_ne one_ne_zero)
    have hpos : 1 ≤ (P j).endsAt c := Nat.one_le_iff_ne_zero.mpr hj
    have hc' : (P j).src = c ∨ (P j).tgt = c := by
      unfold GPath.endsAt at hpos
      by_contra hn
      push Not at hn
      simp [hn.1, hn.2] at hpos
    have hna : att j ≠ c := ((hCmem c).mp hc).2 j
    have hlo : lo j = c := by
      rcases hor j with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hc' with h | h
      · exact absurd (h1.trans h) hna
      · exact h2.trans h
      · exact h2.trans h
      · exact absurd (h1.trans h) hna
    refine ⟨j, fun hjQ => hcq ?_, hlo⟩
    rw [← hlo, hjQ, hiQ]
  -- degrees off `Q`
  have hdegNQ : ∀ x, B.Adj r x → x ∉ Q.walk.support →
      (delList (starDel B r) Q.edges).degree x + 1 = B.degree x := by
    intro x hx hxQ
    rw [delList_degree_of_notMem _ Q hxQ]
    exact starDel_degree_of_adj hx
  have hcount : ∀ x, ∀ S' : Finset (Fin D.paths.length),
      (∀ j ∈ S', x ∈ (P j).walk.support) →
      2 * #S' ≤ (delList (starDel B r) Q.edges).degree x + D.ends x := by
    intro x S' hS'
    have h := D.degree_add_ends_eq_card x
    have : #S' ≤ #(univ.filter (fun i => x ∈ (D.paths.get i).walk.support)) :=
      card_le_card (fun i hi => mem_filter.mpr ⟨mem_univ _, hS' i hi⟩)
    omega
  -- heavy pairs off `Q`
  have hpairs : ∀ u, 2 * #(univ.filter (fun j => j ≠ iQ ∧ 2 * u ≤ B.degree (lo j))) ≤
      #((heavyNbrs B r u).filter (fun x => x ∉ Q.walk.support)) := by
    intro u
    set X := univ.filter (fun j => j ≠ iQ ∧ 2 * u ≤ B.degree (lo j)) with hX
    have hsub : X.image lo ∪ X.image π ⊆ (heavyNbrs B r u).filter (fun x => x ∉ Q.walk.support) := by
      intro x hx
      rw [mem_union, mem_image, mem_image] at hx
      rw [mem_filter, heavyNbrs, mem_filter, mem_neighborFinset]
      rcases hx with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ <;> rw [hX, mem_filter] at hj
      · exact ⟨⟨hlor j, hj.2.2⟩, hloQ j hj.2.1⟩
      · obtain ⟨j', hj'⟩ := hπdes j hj.2.1
        exact ⟨⟨hj' ▸ hattr j', hj.2.2.trans (hπdeg j hj.2.1)⟩, hπQ j hj.2.1⟩
    have hd : Disjoint (X.image lo) (X.image π) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [mem_image] at hx hx'
      obtain ⟨j, -, rfl⟩ := hx
      obtain ⟨j', hj', h⟩ := hx'
      rw [hX, mem_filter] at hj'
      obtain ⟨j'', hj''⟩ := hπdes j' hj'.2.1
      exact hlo_att j j'' (hj''.trans h).symm
    have h1 := card_le_card hsub
    rw [card_union_of_disjoint hd, card_image_of_injective _ hlo_inj,
      card_image_of_injOn (fun a ha b hb h => hπinj a b (by
        have := mem_filter.mp ha; exact this.2.1) (by have := mem_filter.mp hb; exact this.2.1) h)]
      at h1
    omega
  refine hallReassemble D2 attP hattP_end hattPr hattP_inj hk hr Aset hAcard ?_ ?_
  · intro c hc c' hc' hcc' v h1 h2
    by_cases hcq : c = qQ
    · subst hcq
      have hc'q : c' ≠ c := fun h => hcc' h.symm
      rw [hInQ] at h1
      rw [hInT c' hc' hc'q] at h2
      subst h2
      exact htrivQ v hc' hc'q h1
    · rw [hInT c hc hcq] at h1
      subst h1
      by_cases hc'q : c' = qQ
      · subst hc'q
        rw [hInQ] at h2
        exact htrivQ v hc hcq h2
      · rw [hInT c' hc' hc'q] at h2
        exact hcc' h2
  · intro S hS hS3
    set S' := univ.filter (fun j => consIdx Q D j ∈ S) with hS'
    have hSS' : S = S'.image (consIdx Q D) := by
      ext i
      rw [mem_image]
      constructor
      · intro hi
        obtain ⟨j, -, rfl⟩ := mem_image.mp (hS hi)
        exact ⟨j, mem_filter.mpr ⟨mem_univ _, hi⟩, rfl⟩
      · rintro ⟨j, hj, rfl⟩; exact (mem_filter.mp hj).2
    have hcardS : #S = #S' := by
      rw [hSS', card_image_of_injective _ (consIdx_injective Q D)]
    set Jt := Cset.filter (fun c => ∀ i ∈ S, ∃ v ∈ (D2.paths.get i).walk.support,
      InMember D2 attP c v) with hJt
    have hon : ∀ c ∈ Jt, ∀ j ∈ S', ∃ v ∈ (P j).walk.support, InMember D2 attP c v := by
      intro c hc j hj
      have := (mem_filter.mp hc).2 (consIdx Q D j) (mem_filter.mp hj).2
      rw [hgetj, GPath.liftLe_support] at this
      exact this
    -- the connector meets at most `lam` paths
    have hQb : #(Jt.filter (fun c => c = qQ)) ≤ (if #S ≤ lam then 1 else 0) := by
      by_cases hq : qQ ∈ Jt
      · have hle : #S' ≤ lam := by
          have hsub : S' ⊆ Q.walk.support.toFinset.biUnion
              (fun v => univ.filter (fun j => v ∈ (P j).walk.support)) := by
            intro j hj
            obtain ⟨v, hv, hm'⟩ := hon qQ hq j hj
            rw [hInQ] at hm'
            rw [mem_biUnion]
            exact ⟨v, List.mem_toFinset.mpr hm', mem_filter.mpr ⟨mem_univ _, hv⟩⟩
          refine (card_le_card hsub).trans (card_biUnion_le.trans (le_trans ?_ hlam))
          refine sum_le_sum (fun v _ => ?_)
          have h : (delList (starDel B r) Q.edges).degree v + D.ends v =
              2 * #(univ.filter (fun j => v ∈ (P j).walk.support)) := D.degree_add_ends_eq_card v
          have := hends1 v
          rw [Nat.le_div_iff_mul_le two_pos]
          omega
        rw [if_pos (hcardS ▸ hle)]
        exact card_le_one.mpr (fun a ha b hb => (mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
      · have : Jt.filter (fun c => c = qQ) = ∅ := by
          rw [filter_eq_empty_iff]; intro c hc h; exact hq (h ▸ hc)
        rw [this, card_empty]; exact Nat.zero_le _
    -- trivial members on all paths of `S`
    have hTon : ∀ c ∈ Jt, c ≠ qQ → ∀ j ∈ S', c ∈ (P j).walk.support := by
      intro c hc hcq j hj
      obtain ⟨v, hv, hm'⟩ := hon c hc j hj
      rw [hInT c (mem_filter.mp hc).1 hcq] at hm'
      rw [← hm']; exact hv
    have hTdeg : ∀ c ∈ Jt, c ≠ qQ → ∀ S'' : Finset (Fin D.paths.length),
        (∀ j ∈ S'', c ∈ (P j).walk.support) → 2 * #S'' ≤ B.degree c := by
      intro c hc hcq S'' hS''
      have hC := (mem_filter.mp hc).1
      have hadj := ((hCmem c).mp hC).1
      have h1 := hcount c S'' hS''
      have h2 := hdegNQ c hadj (htrivQ c hC hcq)
      rw [hDends c, if_pos hadj] at h1
      omega
    have hJsplit : #Jt ≤ #(Jt.filter (fun c => c = qQ)) + #(Jt.filter (fun c => c ≠ qQ)) := by
      rw [card_filter_add_card_filter_not]
    have htk : #S' ≤ k - 1 := by
      have := card_le_univ S'
      rw [Fintype.card_fin] at this; omega
    rw [hcardS] at hS3 hQb ⊢
    rcases hstar #S' hS3 htk with hA1 | hA2
    · set X := univ.filter (fun j => j ≠ iQ ∧ 2 * #S' ≤ B.degree (lo j)) with hX
      have hT : Jt.filter (fun c => c ≠ qQ) ⊆ X.image lo := by
        intro c hc
        rw [mem_filter] at hc
        obtain ⟨j, hj, rfl⟩ := htriv_lo c (mem_filter.mp hc.1).1 hc.2
        exact mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, hj,
          hTdeg _ hc.1 hc.2 S' (hTon _ hc.1 hc.2)⟩)
      have h1 := (card_le_card hT).trans card_image_le
      have h2 : 2 * #X ≤ #((heavyNbrs B r #S').filter (fun x => x ∉ Q.walk.support)) := hpairs #S'
      have h3 : #X ≤ #((heavyNbrs B r #S').filter (fun x => x ∉ Q.walk.support)) / 2 := by
        rw [Nat.le_div_iff_mul_le two_pos]; omega
      omega
    · set X := univ.filter (fun j => j ≠ iQ ∧ 2 * (#S' + 1) ≤ B.degree (lo j)) with hX
      have hT : Jt.filter (fun c => c ≠ qQ) ⊆ S'.image lo ∪ X.image lo := by
        intro c hc
        rw [mem_filter] at hc
        obtain ⟨j, hj, rfl⟩ := htriv_lo c (mem_filter.mp hc.1).1 hc.2
        rw [mem_union]
        by_cases hjS : j ∈ S'
        · exact Or.inl (mem_image_of_mem _ hjS)
        · right
          refine mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, hj, ?_⟩)
          have := hTdeg _ hc.1 hc.2 (insert j S') (by
            intro i hi
            rw [mem_insert] at hi
            rcases hi with rfl | hi
            · rcases hor i with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
              · exact (P i).walk.end_mem_support
              · exact (P i).walk.start_mem_support
            · exact hTon _ hc.1 hc.2 i hi)
          rw [card_insert_of_notMem hjS] at this
          exact this
      have h1 := (card_le_card hT).trans ((card_union_le _ _).trans
        (add_le_add card_image_le card_image_le))
      have h2 : 2 * #X ≤ #((heavyNbrs B r (#S' + 1)).filter (fun x => x ∉ Q.walk.support)) :=
        hpairs (#S' + 1)
      have h3 : #X ≤ #((heavyNbrs B r (#S' + 1)).filter (fun x => x ∉ Q.walk.support)) / 2 := by
        rw [Nat.le_div_iff_mul_le two_pos]; omega
      omega

end core

/-! ### Theorem B -/

section thmB

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- **Theorem B (`δ = 0`).** Let `B` have order `2k`, `d(r) = 2k − 2`, and let `Q` be a path of
`G = B − r` whose ends are neighbours of `r` and whose other vertices are not, such that every
neighbour of `r` has odd degree in `G' = G − E(Q)`. Let `λ ≥ ∑_{v ∈ Q} ⌈d_{G'}(v)/2⌉` and
`h̃_t = #{x ∈ N(r) ∖ V(Q) : d(x) ≥ 2t}`. If for every `3 ≤ t ≤ k − 1`,
`⌊h̃_t/2⌋ + [t ≤ λ] + t ≤ k + 1` or `⌊h̃_{t+1}/2⌋ + [t ≤ λ] + 2t ≤ k + 1`, then `B` has a
decomposition into `k` paths with exactly two ends at `r`. -/
theorem exists_decomp_of_connector (B : SimpleGraph W) [DecidableRel B.Adj] {k : ℕ} (hk : 2 ≤ k)
    (hW : Fintype.card W = 2 * k) (r : W) (hr : B.degree r + 2 = 2 * k)
    (Q : GPath (starDel B r)) (hq1 : B.Adj r Q.src) (hq2 : B.Adj r Q.tgt)
    (hQint : ∀ v ∈ Q.walk.support, B.Adj r v → v = Q.src ∨ v = Q.tgt)
    (hodd : ∀ x, B.Adj r x → (delList (starDel B r) Q.edges).degree x % 2 = 1)
    (lam : ℕ)
    (hlam : ∑ v ∈ Q.walk.support.toFinset,
      ((delList (starDel B r) Q.edges).degree v + 1) / 2 ≤ lam)
    (hstar : ∀ t, 3 ≤ t → t ≤ k - 1 →
      #((heavyNbrs B r t).filter (fun x => x ∉ Q.walk.support)) / 2 +
          (if t ≤ lam then 1 else 0) + t ≤ k + 1 ∨
      #((heavyNbrs B r (t + 1)).filter (fun x => x ∉ Q.walk.support)) / 2 +
          (if t ≤ lam then 1 else 0) + 2 * t ≤ k + 1) :
    ∃ D : PathDecomp B, D.size = k ∧ D.ends r = 2 := by
  classical
  -- `r` and `s`
  have hcS : #(univ \ insert r (B.neighborFinset r)) = 1 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hW, card_insert_of_notMem
      (by rw [mem_neighborFinset]; exact B.loopless.irrefl r), card_neighborFinset_eq_degree]
    omega
  obtain ⟨s, hs⟩ := card_eq_one.mp hcS
  have hsmem : s ∈ univ \ insert r (B.neighborFinset r) := by rw [hs]; exact mem_singleton_self _
  have hsr : s ≠ r ∧ ¬ B.Adj r s := by
    rw [mem_sdiff, mem_insert, mem_neighborFinset] at hsmem; push Not at hsmem; exact hsmem.2
  have hsuniq : ∀ v, v ≠ r → ¬ B.Adj r v → v = s := by
    intro v hvr hv
    have : v ∈ univ \ insert r (B.neighborFinset r) := by
      rw [mem_sdiff, mem_insert, mem_neighborFinset]; push Not; exact ⟨mem_univ _, hvr, hv⟩
    rw [hs, mem_singleton] at this; exact this
  have hdr : (delList (starDel B r) Q.edges).degree r = 0 := by
    have := (delList_le' (starDel B r) Q.edges)
    have h := (delList (starDel B r) Q.edges).degree_le_of_le (v := r) this
    rw [starDel_degree_self] at h; omega
  -- at most one even vertex in `G'`
  have hev : (evenSet (delList (starDel B r) Q.edges)).card ≤ 1 := by
    have hsub : evenSet (delList (starDel B r) Q.edges) ⊆ {s} := by
      intro v hv
      rw [mem_evenSet_iff] at hv
      rw [mem_singleton]
      have hvr : v ≠ r := fun h => by rw [h, hdr] at hv; exact lt_irrefl _ hv.1
      by_contra hvs
      have hadj : B.Adj r v := by
        by_contra hn; exact hvs (hsuniq v hvr hn)
      have := hodd v hadj; omega
    exact (card_le_card hsub).trans (card_singleton s).le
  obtain ⟨D, hD⟩ := lovasz_ends (delList (starDel B r) Q.edges) hev
  set P := D.paths.get with hP
  -- the ends are the neighbours of `r`, and there are `k − 1` paths
  have hsize : D.paths.length + 1 = k ∧ D.ends s = 0 := by
    have h1 := D.sum_ends
    set N := B.neighborFinset r with hNdef
    have hsplit : ∑ v, D.ends v = ∑ v ∈ N, D.ends v + ∑ v ∈ univ \ N, D.ends v := by
      rw [← sum_sdiff (subset_univ N), add_comm]
    have hrest : univ \ N = {r, s} := by
      ext v
      rw [mem_sdiff, hNdef, mem_neighborFinset, mem_insert, mem_singleton]
      constructor
      · rintro ⟨-, hv⟩
        by_cases hvr : v = r
        · exact Or.inl hvr
        · exact Or.inr (hsuniq v hvr hv)
      · rintro (h | h)
        · rw [h]; exact ⟨mem_univ _, B.loopless.irrefl _⟩
        · rw [h]; exact ⟨mem_univ _, hsr.2⟩
    have hrest_sum : ∑ v ∈ univ \ N, D.ends v = D.ends s := by
      rw [hrest, sum_pair hsr.1.symm, hD r, hdr, Nat.zero_mod, zero_add]
    have hNsum : ∑ v ∈ N, D.ends v = #N := by
      rw [card_eq_sum_ones]
      refine sum_congr rfl (fun x hx => ?_)
      rw [hD x, hodd x ((B.mem_neighborFinset r x).mp hx)]
    have hNc : #N = 2 * k - 2 := by rw [hNdef, card_neighborFinset_eq_degree]; omega
    have hs1 : D.ends s ≤ 1 := by rw [hD s]; omega
    rw [hsplit, hrest_sum, hNsum, hNc] at h1
    unfold PathDecomp.size at h1
    omega
  have hDends : ∀ v, D.ends v = if B.Adj r v then 1 else 0 := by
    intro v
    split_ifs with h
    · rw [hD v, hodd v h]
    · by_cases hvr : v = r
      · rw [hvr, hD r, hdr]
      · rw [hsuniq v hvr h]; exact hsize.2
  have hends1 : ∀ v, D.ends v ≤ 1 := fun v => by rw [hDends v]; split_ifs <;> omega
  have hend_pos : ∀ i v, 1 ≤ (P i).endsAt v → 1 ≤ D.ends v :=
    fun i v h => h.trans (D.endsAt_le_ends v i)
  have hend_uniq : ∀ i j v, 1 ≤ (P i).endsAt v → 1 ≤ (P j).endsAt v → i = j := by
    intro i j v hi hj
    by_contra hij
    have := D.two_le_ends_of_ne hij hi hj
    have := hends1 v
    omega
  have hend_adj : ∀ i v, 1 ≤ (P i).endsAt v → B.Adj r v := by
    intro i v h
    have := hend_pos i v h
    rw [hDends v] at this
    by_contra hn; rw [if_neg hn] at this; omega
  have hpathOf : ∀ v, B.Adj r v → ∃ i, 1 ≤ (P i).endsAt v := by
    intro v hv
    have h1 : D.ends v = 1 := by rw [hDends v, if_pos hv]
    rw [D.ends_eq_sum_get] at h1
    obtain ⟨j, -, hj⟩ := exists_ne_zero_of_sum_ne_zero (h1.trans_ne one_ne_zero)
    exact ⟨j, Nat.one_le_iff_ne_zero.mpr hj⟩
  have hsrc : ∀ i, 1 ≤ (P i).endsAt (P i).src := fun i => (P i).endsAt_src
  have htgt : ∀ i, 1 ≤ (P i).endsAt (P i).tgt := fun i => (P i).endsAt_tgt
  have hend_cases : ∀ i v, 1 ≤ (P i).endsAt v → (P i).src = v ∨ (P i).tgt = v := by
    intro i v h
    unfold GPath.endsAt at h
    by_contra hn
    push Not at hn
    simp [hn.1, hn.2] at h
  -- the other end of a path
  let oth : Fin D.paths.length → W → W := fun j v =>
    if (P j).src = v then (P j).tgt else (P j).src
  have hoth : ∀ j v, 1 ≤ (P j).endsAt v →
      ((P j).src = v ∧ oth j v = (P j).tgt) ∨ ((P j).tgt = v ∧ oth j v = (P j).src) := by
    intro j v h
    rcases hend_cases j v h with h' | h'
    · exact Or.inl ⟨h', if_pos h'⟩
    · by_cases h'' : (P j).src = v
      · exact Or.inl ⟨h'', if_pos h''⟩
      · exact Or.inr ⟨h', if_neg h''⟩
  have hoth_ne : ∀ j v, 1 ≤ (P j).endsAt v → oth j v ≠ v := by
    intro j v h
    rcases hoth j v h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2, ← h1]; exact (P j).src_ne_tgt.symm
    · rw [h2, ← h1]; exact (P j).src_ne_tgt
  have hoth_end : ∀ j v, 1 ≤ (P j).endsAt v → 1 ≤ (P j).endsAt (oth j v) := by
    intro j v h
    rcases hoth j v h with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
    exacts [htgt j, hsrc j]
  -- the plan: `Q` at `q_Q`, the other connector end `q_O` attached on its own path
  obtain ⟨i1, hi1⟩ := hpathOf Q.src hq1
  obtain ⟨i2, hi2⟩ := hpathOf Q.tgt hq2
  have hq12 : Q.src ≠ Q.tgt := Q.src_ne_tgt
  obtain ⟨qQ, iQ, qO, iO, hqQ, hiQe, hiOe, hqQO, hdegc⟩ : ∃ qQ iQ qO iO,
      ((qQ = Q.src ∧ qO = Q.tgt) ∨ (qQ = Q.tgt ∧ qO = Q.src)) ∧
      1 ≤ (P iQ).endsAt qQ ∧ 1 ≤ (P iO).endsAt qO ∧ qQ ≠ qO ∧
      (iO ≠ iQ → B.degree (oth iO qO) ≤ B.degree (oth iQ qQ)) := by
    by_cases hd : B.degree (oth i2 Q.tgt) ≤ B.degree (oth i1 Q.src)
    · exact ⟨Q.src, i1, Q.tgt, i2, Or.inl ⟨rfl, rfl⟩, hi1, hi2, hq12, fun _ => hd⟩
    · exact ⟨Q.tgt, i2, Q.src, i1, Or.inr ⟨rfl, rfl⟩, hi2, hi1, hq12.symm, fun _ => by omega⟩
  have hqQr : B.Adj r qQ := hend_adj iQ qQ hiQe
  have hqOr : B.Adj r qO := hend_adj iO qO hiOe
  have hQvert : ∀ v ∈ Q.walk.support, B.Adj r v → v = qQ ∨ v = qO := by
    intro v hv hvr
    rcases hQint v hv hvr with h | h <;> rcases hqQ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (h.trans h1.symm)
    · exact Or.inr (h.trans h2.symm)
    · exact Or.inr (h.trans h2.symm)
    · exact Or.inl (h.trans h1.symm)
  -- orientation of the other paths: attachment at the end of larger degree
  let att0 : Fin D.paths.length → W := fun j =>
    if B.degree (P j).tgt ≤ B.degree (P j).src then (P j).src else (P j).tgt
  let lo0 : Fin D.paths.length → W := fun j =>
    if B.degree (P j).tgt ≤ B.degree (P j).src then (P j).tgt else (P j).src
  let att : Fin D.paths.length → W := fun j =>
    if j = iQ then oth iQ qQ else if j = iO then qO else att0 j
  let lo : Fin D.paths.length → W := fun j =>
    if j = iQ then qQ else if j = iO then oth iO qO else lo0 j
  let π : Fin D.paths.length → W := fun j =>
    if j = iO ∧ iO ≠ iQ then oth iQ qQ else att j
  have hor : ∀ j, (att j = (P j).src ∧ lo j = (P j).tgt) ∨
      (att j = (P j).tgt ∧ lo j = (P j).src) := by
    intro j
    by_cases hjQ : j = iQ
    · subst hjQ
      simp only [att, lo, if_pos rfl]
      rcases hoth j qQ hiQe with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1.symm⟩
      · exact Or.inl ⟨h2, h1.symm⟩
    · by_cases hjO : j = iO
      · subst hjO
        simp only [att, lo, if_neg hjQ, if_pos rfl]
        rcases hoth j qO hiOe with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1.symm, h2⟩
        · exact Or.inr ⟨h1.symm, h2⟩
      · simp only [att, lo, att0, lo0, if_neg hjQ, if_neg hjO]
        split_ifs
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
  have hatt_end : ∀ j, 1 ≤ (P j).endsAt (att j) := by
    intro j; rcases hor j with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]; exacts [hsrc j, htgt j]
  have hatt_inj : Function.Injective att := fun i j h =>
    hend_uniq i j (att i) (hatt_end i) (h ▸ hatt_end j)
  have hlo_iQ : lo iQ = qQ := by simp [lo]
  -- the vertices of `Q` at `r` other than `q_Q` are attachments
  have hattO : ∃ j, att j = qO := by
    by_cases hOQ : iO = iQ
    · refine ⟨iQ, ?_⟩
      simp only [att, if_pos rfl]
      -- both ends of `P iQ` are `qQ` and `qO`
      have h2 : 1 ≤ (P iQ).endsAt qO := hOQ ▸ hiOe
      rcases hoth iQ qQ hiQe with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
        rcases hend_cases iQ qO h2 with h3 | h3
      · exact absurd (h1.symm.trans h3) hqQO
      · exact h1'.trans h3
      · exact h1'.trans h3
      · exact absurd (h1.symm.trans h3) hqQO
    · exact ⟨iO, by simp [att, hOQ]⟩
  have hQdes : ∀ v ∈ Q.walk.support, B.Adj r v → v ≠ qQ → ∃ j, att j = v := by
    intro v hv hvr hvq
    rcases hQvert v hv hvr with h | h
    · exact absurd h hvq
    · rw [h]; exact hattO
  -- the partners
  have hπ_att : ∀ j, j ≠ iQ → ∃ j', att j' = π j ∧ (j' = iQ ↔ (j = iO ∧ iO ≠ iQ)) := by
    intro j hj
    by_cases hc : j = iO ∧ iO ≠ iQ
    · exact ⟨iQ, by simp [att, π, hc], by simp [hc]⟩
    · exact ⟨j, by simp [π, hc], by simp [hj, hc]⟩
  have hπdes : ∀ j, j ≠ iQ → ∃ j', att j' = π j := by
    intro j hj
    obtain ⟨j', h, -⟩ := hπ_att j hj
    exact ⟨j', h⟩
  have hπinj : ∀ j j', j ≠ iQ → j' ≠ iQ → π j = π j' → j = j' := by
    intro j j' hj hj' h
    obtain ⟨a, ha, ha'⟩ := hπ_att j hj
    obtain ⟨b, hb, hb'⟩ := hπ_att j' hj'
    have hab : a = b := hatt_inj (ha.trans (h.trans hb.symm))
    subst hab
    by_cases hc : a = iQ
    · have h1 := ha'.mp hc; have h2 := hb'.mp hc; exact h1.1.trans h2.1.symm
    · -- then `π j = att j`
      have hj1 : ¬ (j = iO ∧ iO ≠ iQ) := fun h' => hc (ha'.mpr h')
      have hj2 : ¬ (j' = iO ∧ iO ≠ iQ) := fun h' => hc (hb'.mpr h')
      have e1 : π j = att j := by simp [π, hj1]
      have e2 : π j' = att j' := by simp [π, hj2]
      exact hatt_inj (e1.symm.trans (h.trans e2))
  have hπdeg : ∀ j, j ≠ iQ → B.degree (lo j) ≤ B.degree (π j) := by
    intro j hj
    by_cases hc : j = iO ∧ iO ≠ iQ
    · have e1 : π j = oth iQ qQ := by simp [π, hc]
      have e2 : lo j = oth iO qO := by simp [lo, hj, hc.1, hc.2]
      rw [e1, e2]; exact hdegc hc.2
    · have hjO : j ≠ iO := fun h => hc ⟨h, h ▸ hj⟩
      have e1 : π j = att0 j := by simp [π, hc, att, hj, hjO]
      have e2 : lo j = lo0 j := by simp [lo, hj, hjO]
      rw [e1, e2]
      show B.degree (if B.degree (P j).tgt ≤ B.degree (P j).src then (P j).tgt else (P j).src) ≤
        B.degree (if B.degree (P j).tgt ≤ B.degree (P j).src then (P j).src else (P j).tgt)
      by_cases h : B.degree (P j).tgt ≤ B.degree (P j).src
      · rw [if_pos h, if_pos h]; exact h
      · rw [if_neg h, if_neg h]; omega
  have hπQ : ∀ j, j ≠ iQ → π j ∉ Q.walk.support := by
    intro j hj hm'
    obtain ⟨a, ha, ha'⟩ := hπ_att j hj
    have hadj : B.Adj r (π j) := ha ▸ hend_adj a _ (hatt_end a)
    rcases hQvert _ hm' hadj with h | h
    · -- `π j = qQ`, an end of `P iQ` only, and it is not the attachment there
      have := hend_uniq a iQ _ (ha ▸ hatt_end a) (h ▸ hiQe)
      subst this
      have : att a = oth a qQ := by simp [att]
      exact hoth_ne a qQ hiQe (this ▸ ha.trans h)
    · have := hend_uniq a iO _ (ha ▸ hatt_end a) (h ▸ hiOe)
      subst this
      by_cases hOQ : a = iQ
      · -- then `j = iO = iQ`, excluded
        exact hj ((ha'.mp hOQ).1.trans hOQ)
      · have h1 := (not_congr ha').mp hOQ
        have : π j = att j := by simp [π, h1]
        have hja : j = a := hatt_inj (this.symm.trans (ha.symm))
        subst hja
        exact h1 ⟨rfl, hOQ⟩
  have hqQ' : qQ = Q.src ∨ qQ = Q.tgt := by
    rcases hqQ with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  exact connector_core B hk hr Q D hDends hsize.1 att lo hor qQ hqQ' iQ hlo_iQ hQdes π hπdes
    hπinj hπdeg hπQ lam hlam hstar

end thmB

section test1B

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Theorem B, spine form**: the two-end test (T1) at a root `r` of degree `|J| − 2`, from a
connector `Q` in `(J − z) − r` as in `exists_decomp_of_connector`. -/
theorem test1At_of_connector (J : SimpleGraph V) [DecidableRel J.Adj] {z r : V} {k : ℕ}
    (hk : 2 ≤ k) (hV : Fintype.card V = 2 * k + 1) (hzr : J.Adj z r)
    (hr : J.degree r + 2 = 2 * k + 1)
    (Q : GPath (starDel (delVert J z) ⟨r, hzr.ne'⟩))
    (hq1 : (delVert J z).Adj ⟨r, hzr.ne'⟩ Q.src) (hq2 : (delVert J z).Adj ⟨r, hzr.ne'⟩ Q.tgt)
    (hQint : ∀ v ∈ Q.walk.support, (delVert J z).Adj ⟨r, hzr.ne'⟩ v → v = Q.src ∨ v = Q.tgt)
    (hodd : ∀ x, (delVert J z).Adj ⟨r, hzr.ne'⟩ x →
      (delList (starDel (delVert J z) ⟨r, hzr.ne'⟩) Q.edges).degree x % 2 = 1)
    (lam : ℕ)
    (hlam : ∑ v ∈ Q.walk.support.toFinset,
      ((delList (starDel (delVert J z) ⟨r, hzr.ne'⟩) Q.edges).degree v + 1) / 2 ≤ lam)
    (hstar : ∀ t, 3 ≤ t → t ≤ k - 1 →
      #((heavyNbrs (delVert J z) ⟨r, hzr.ne'⟩ t).filter (fun x => x ∉ Q.walk.support)) / 2 +
          (if t ≤ lam then 1 else 0) + t ≤ k + 1 ∨
      #((heavyNbrs (delVert J z) ⟨r, hzr.ne'⟩ (t + 1)).filter (fun x => x ∉ Q.walk.support)) / 2 +
          (if t ≤ lam then 1 else 0) + 2 * t ≤ k + 1) :
    Test1At J z r := by
  have hW : Fintype.card {v | v ≠ z} = 2 * k := by rw [card_delVert, hV]; omega
  have hdeg := delVert_degree (J := J) z ⟨r, hzr.ne'⟩
  rw [if_pos hzr.symm] at hdeg
  exact test1At_of_decomp J hV hzr
    (exists_decomp_of_connector (delVert J z) hk hW ⟨r, hzr.ne'⟩ (by simp only at hdeg; omega)
      Q hq1 hq2 hQint hodd lam hlam (by convert hstar))

end test1B

end Gallai
