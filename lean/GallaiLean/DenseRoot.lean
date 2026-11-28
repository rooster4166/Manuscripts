import GallaiLean.RETight
import GallaiLean.ForestLift
import GallaiLean.ConjNFar

/-!
# Test1 at roots of degree `n − 2` without parity assumptions (session `claude/dense-root`)

Manuscript: `manuscripts/dense-root`.

Let `B` have order `2k`, let `r` have degree `2k − 2`, and let `G = B − r` (`starDel B r`).
A *family* gives every neighbour `x` of `r` a member: a path of `G` with an end at `x` (its
attachment) or the trivial member `x`; the nontrivial members partition `E(G)`. A set of disjoint
pairs of vertex-disjoint members, together with the remaining singletons, gives the paths
`Q_x x r y Q_y` and `Q_x x r` of `B` (`famReassemble`, manuscript Lemma 2.2). Nothing here needs
`B` to be Eulerian.

* `InMember D att x v`: `v` lies on the member at `x`.
* **`famReassemble`** (Lemma 2.2): pairs + singletons ⇒ a decomposition of `B` with one path per
  pair and per singleton, and one end at `r` per singleton.
-/

open SimpleGraph Finset

namespace Gallai

universe u

section family

variable {W : Type u} [Fintype W] [DecidableEq W] {B : SimpleGraph W} [DecidableRel B.Adj]
  {r : W}

/-- `v` lies on the member at `x`: `v = x`, or `x` is the attachment of a path of `D` through
`v`. -/
def InMember (D : PathDecomp (starDel B r)) (att : Fin D.paths.length → W) (x v : W) : Prop :=
  v = x ∨ ∃ i, att i = x ∧ v ∈ (D.paths.get i).walk.support

instance InMember.decidable (D : PathDecomp (starDel B r)) (att : Fin D.paths.length → W)
    (x v : W) : Decidable (InMember D att x v) := by
  unfold InMember; infer_instance

omit [Fintype W] [DecidableEq W] [DecidableRel B.Adj] in
/-- Glue `p : a → x`, the two edges `x r`, `r y`, and the reversal of `q : b → y`. -/
theorem exists_pair_path {a x b y : W} (p : (⊤ : SimpleGraph W).Walk a x)
    (q : (⊤ : SimpleGraph W).Walk b y) (hp : p.support.Nodup) (hq : q.support.Nodup)
    (hpr : r ∉ p.support) (hqr : r ∉ q.support) (hpq : ∀ v ∈ p.support, v ∉ q.support) :
    ∃ R : TPath W, R.edges = p.edges ++ [s(x, r), s(r, y)] ++ q.reverse.edges ∧
      R.src = a ∧ R.tgt = b := by
  have hxr : x ≠ r := fun h => hpr (h ▸ p.end_mem_support)
  have hyr : y ≠ r := fun h => hqr (h ▸ q.end_mem_support)
  have hxy : x ≠ y := fun h => hpq x p.end_mem_support (h ▸ q.end_mem_support)
  let mid : (⊤ : SimpleGraph W).Walk x y :=
    Walk.cons (top_adj x r |>.mpr hxr) (Walk.cons (top_adj r y |>.mpr hyr.symm) Walk.nil)
  have hmn : mid.support.Nodup := by simp [mid, hxr, hxy, hyr.symm]
  have hd1 : ∀ v ∈ p.support, v ∈ mid.support → v = x := by
    intro v hv hvm
    simp only [mid, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hvm
    rcases hvm with h | h | h
    · exact h
    · exact absurd (h ▸ hv) hpr
    · exact absurd (h ▸ q.end_mem_support) (hpq v hv)
  let w1 := p.append mid
  have hw1n : w1.support.Nodup := (nodup_support_append p mid).mpr ⟨hp, hmn, hd1⟩
  have hR1s : ∀ v, v ∈ w1.support ↔ v ∈ p.support ∨ v = r ∨ v = y := by
    intro v
    rw [Walk.mem_support_append_iff]
    simp only [mid, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false]
    constructor
    · rintro (h | h | h | h)
      · exact Or.inl h
      · exact Or.inl (h ▸ p.end_mem_support)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  have hqrn : q.reverse.support.Nodup := by rw [Walk.support_reverse, List.nodup_reverse]; exact hq
  have hd2 : ∀ v ∈ w1.support, v ∈ q.reverse.support → v = y := by
    intro v hv hvq
    rw [Walk.support_reverse, List.mem_reverse] at hvq
    rcases (hR1s v).mp hv with h | h | h
    · exact absurd hvq (hpq v h)
    · exact absurd (h ▸ hvq) hqr
    · exact h
  refine ⟨joinT w1 q.reverse hw1n hqrn hd2 (by simp [w1, mid]), ?_, rfl, rfl⟩
  rw [joinT_edges, Walk.edges_append]
  simp [mid]

omit [Fintype W] [DecidableEq W] [DecidableRel B.Adj] in
/-- Glue `p : a → x` and the edge `x r`. -/
theorem exists_single_path {a x : W} (p : (⊤ : SimpleGraph W).Walk a x) (hp : p.support.Nodup)
    (hpr : r ∉ p.support) :
    ∃ R : TPath W, R.edges = p.edges ++ [s(x, r)] ∧ R.src = a ∧ R.tgt = r := by
  have hxr : x ≠ r := fun h => hpr (h ▸ p.end_mem_support)
  let q : (⊤ : SimpleGraph W).Walk x r := Walk.cons (top_adj x r |>.mpr hxr) Walk.nil
  have hqn : q.support.Nodup := by simp [q, hxr]
  have hd : ∀ v ∈ p.support, v ∈ q.support → v = x := by
    intro v hv hvq
    simp only [q, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hvq
    rcases hvq with h | h
    · exact h
    · exact absurd (h ▸ hv) hpr
  exact ⟨joinT p q hp hqn hd (by simp [q]), by rw [joinT_edges]; simp [q], rfl, rfl⟩

omit [Fintype W] [DecidableRel B.Adj] in
/-- The member at `x`, as a walk of `⊤` ending at `x`. -/
theorem exists_member_walk (D : PathDecomp (starDel B r)) (att : Fin D.paths.length → W)
    (hatt : ∀ i, att i = (D.paths.get i).src ∨ att i = (D.paths.get i).tgt)
    (hinj : Function.Injective att) (x : W) :
    ∃ a, ∃ w : (⊤ : SimpleGraph W).Walk a x, w.support.Nodup ∧
      (∀ v, v ∈ w.support ↔ InMember D att x v) ∧
      (∀ e, e ∈ w.edges ↔ ∃ i, att i = x ∧ e ∈ (D.paths.get i).edges) ∧ w.edges.Nodup := by
  by_cases hx : ∃ i, att i = x
  · obtain ⟨i, rfl⟩ := hx
    set P := D.paths.get i
    have hor : ((if att i = P.src then P.tgt else P.src) = P.src ∧ att i = P.tgt) ∨
        ((if att i = P.src then P.tgt else P.src) = P.tgt ∧ att i = P.src) := by
      rcases hatt i with h | h
      · right; exact ⟨by rw [ite_eq_left h], h⟩
      · by_cases h' : att i = P.src
        · right; exact ⟨by rw [ite_eq_left h'], h'⟩
        · left; exact ⟨by rw [ite_eq_right h'], h⟩
    obtain ⟨w, hwn, -, hwe, hws⟩ := P.exists_oriented hor
    refine ⟨_, w, hwn, fun v => ?_, fun e => ?_, ?_⟩
    · rw [hws]
      constructor
      · intro hv; exact Or.inr ⟨i, rfl, hv⟩
      · rintro (rfl | ⟨j, hj, hv⟩)
        · rcases hatt i with h | h
          · rw [h]; exact P.walk.start_mem_support
          · rw [h]; exact P.walk.end_mem_support
        · rw [hinj hj] at hv; exact hv
    · rw [hwe]
      constructor
      · intro he; exact ⟨i, rfl, he⟩
      · rintro ⟨j, hj, he⟩; rw [hinj hj] at he; exact he
    · have : w.edges.Nodup := by
        have hpath : w.IsPath := (Walk.isPath_def _).mpr hwn
        exact hpath.isTrail.edges_nodup
      exact this
  · push Not at hx
    refine ⟨x, Walk.nil, by simp, fun v => ?_, fun e => ?_, by simp⟩
    · simp only [Walk.support_nil, List.mem_singleton, InMember]
      constructor
      · exact Or.inl
      · rintro (h | ⟨j, hj, -⟩)
        · exact h
        · exact absurd hj (hx j)
    · simp only [Walk.edges_nil, List.not_mem_nil, false_iff, not_exists, not_and]
      intro j hj; exact absurd hj (hx j)

/-- **Lemma 2.2 (families).** Members are attached to the neighbours of `r`: the path `P_i` of
`D` at its end `att i`, and the trivial member at every other neighbour. A list `pr` of pairs of
vertex-disjoint members and a list `sg` of singletons, using every neighbour of `r` exactly once,
give a decomposition of `B` with `|pr| + |sg|` paths and exactly `|sg|` ends at `r`. -/
theorem famReassemble (D : PathDecomp (starDel B r)) (att : Fin D.paths.length → W)
    (hatt : ∀ i, att i = (D.paths.get i).src ∨ att i = (D.paths.get i).tgt)
    (hattr : ∀ i, B.Adj r (att i)) (hinj : Function.Injective att)
    (pr : List (W × W)) (sg : List W)
    (hnd : (pr.flatMap (fun p => [p.1, p.2]) ++ sg).Nodup)
    (hmem : ∀ x, x ∈ pr.flatMap (fun p => [p.1, p.2]) ++ sg ↔ B.Adj r x)
    (hcomp : ∀ p ∈ pr, ∀ v, InMember D att p.1 v → ¬ InMember D att p.2 v) :
    ∃ D' : PathDecomp B, D'.size = pr.length + sg.length ∧ D'.ends r = sg.length := by
  set P := D.paths.get with hP
  choose far w hwn hws hwe hwnd using exists_member_walk D att hatt hinj
  have hPr : ∀ i, r ∉ (P i).walk.support := fun i => GPath.root_notMem_starDel _
  have hrw : ∀ x, x ≠ r → r ∉ (w x).support := by
    intro x hx hr
    rcases (hws x r).mp hr with h | ⟨i, -, hi⟩
    · exact hx h.symm
    · exact hPr i hi
  have hadjne : ∀ x, B.Adj r x → x ≠ r := fun x h => h.ne'
  have hmemP : ∀ p ∈ pr, B.Adj r p.1 ∧ B.Adj r p.2 := by
    intro p hp
    exact ⟨(hmem _).mp (List.mem_append_left _ (List.mem_flatMap.mpr ⟨p, hp, by simp⟩)),
      (hmem _).mp (List.mem_append_left _ (List.mem_flatMap.mpr ⟨p, hp, by simp⟩))⟩
  have hmemS : ∀ x ∈ sg, B.Adj r x := fun x hx => (hmem x).mp (List.mem_append_right _ hx)
  -- the paths of `B`
  have hRp : ∀ p ∈ pr, ∃ R : TPath W,
      R.edges = (w p.1).edges ++ [s(p.1, r), s(r, p.2)] ++ (w p.2).reverse.edges ∧
      R.src = far p.1 ∧ R.tgt = far p.2 := by
    intro p hp
    obtain ⟨h1, h2⟩ := hmemP p hp
    exact exists_pair_path (w p.1) (w p.2) (hwn _) (hwn _) (hrw _ (hadjne _ h1))
      (hrw _ (hadjne _ h2)) (fun v hv hv' => hcomp p hp v ((hws _ v).mp hv) ((hws _ v).mp hv'))
  have hRs : ∀ x ∈ sg, ∃ R : TPath W, R.edges = (w x).edges ++ [s(x, r)] ∧
      R.src = far x ∧ R.tgt = r := by
    intro x hx
    exact exists_single_path (w x) (hwn _) (hrw _ (hadjne _ (hmemS x hx)))
  choose Rp hRpe hRps hRpt using hRp
  choose Rs hRse hRss hRst using hRs
  set L1 := pr.attach.map (fun p => Rp p.1 p.2) with hL1
  set L2 := sg.attach.map (fun x => Rs x.1 x.2) with hL2
  -- the edge list of a member, with its edge at `r`
  let El : W → List (Sym2 W) := fun x => (w x).edges ++ [s(x, r)]
  have hcoeRp : ∀ p (hp : p ∈ pr), ((Rp p hp).edges : Multiset (Sym2 W)) =
      (El p.1 : Multiset (Sym2 W)) + (El p.2 : Multiset (Sym2 W)) := by
    intro p hp
    have key : ((w p.1).edges ++ [s(p.1, r), s(p.2, r)] ++ (w p.2).edges.reverse).Perm
        (((w p.1).edges ++ [s(p.1, r)]) ++ ((w p.2).edges ++ [s(p.2, r)])) := by
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      refine List.Perm.append_left _ (List.Perm.cons _ ?_)
      exact (List.perm_append_comm (l₁ := [s(p.2, r)]) (l₂ := (w p.2).edges.reverse)).trans
        ((List.reverse_perm _).append_right _)
    rw [hRpe, Walk.edges_reverse, Sym2.eq_swap (a := r) (b := p.2), Multiset.coe_eq_coe.mpr key,
      ← Multiset.coe_add]
  have hcoeRs : ∀ x (hx : x ∈ sg), ((Rs x hx).edges : Multiset (Sym2 W)) = (El x : Multiset (Sym2 W)) := by
    intro x hx; rw [hRse]
  have hedgesM : ∀ L : List (TPath W), edgesM L = (L.map (fun R => (R.edges : Multiset (Sym2 W)))).sum := by
    intro L
    induction L with
    | nil => simp
    | cons R L ih => rw [edgesM_cons, ih, List.map_cons, List.sum_cons]
  have hL1m : L1.map (fun R => (R.edges : Multiset (Sym2 W))) =
      pr.map (fun p => (El p.1 : Multiset (Sym2 W)) + (El p.2 : Multiset (Sym2 W))) := by
    rw [hL1, List.map_map]
    rw [← List.attach_map_val (l := pr)]
    exact List.map_congr_left (fun p _ => hcoeRp p.1 p.2)
  have hL2m : L2.map (fun R => (R.edges : Multiset (Sym2 W))) =
      sg.map (fun x => (El x : Multiset (Sym2 W))) := by
    rw [hL2, List.map_map]
    rw [← List.attach_map_val (l := sg)]
    exact List.map_congr_left (fun x _ => hcoeRs x.1 x.2)
  have hpairsum : ∀ l : List (W × W),
      (l.map (fun p => (El p.1 : Multiset (Sym2 W)) + (El p.2 : Multiset (Sym2 W)))).sum =
      ((l.flatMap (fun p => [p.1, p.2])).map (fun x => (El x : Multiset (Sym2 W)))).sum := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
      rw [List.map_cons, List.sum_cons, ih, List.flatMap_cons, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]
  -- the members, listed, are the neighbours of `r`
  set Lm := pr.flatMap (fun p => [p.1, p.2]) ++ sg with hLm
  have hperm : Lm.Perm (B.neighborFinset r).toList := by
    rw [List.perm_ext_iff_of_nodup hnd (Finset.nodup_toList _)]
    intro x
    rw [Finset.mem_toList, mem_neighborFinset, hmem]
  have hsum : edgesM (L1 ++ L2) = (((B.neighborFinset r).toList.flatMap El : List (Sym2 W)) :
      Multiset (Sym2 W)) := by
    rw [hedgesM, List.map_append, List.sum_append, hL1m, hL2m, hpairsum, ← List.sum_append,
      ← List.map_append, ← hLm, (hperm.map _).sum_eq]
    clear hperm hnd hmem hLm
    induction (B.neighborFinset r).toList with
    | nil => simp
    | cons x l ih => simp [ih]
  -- the members' edges are exactly the edges of `B`
  have hDdisj : ∀ i j, i ≠ j → ∀ e, e ∈ (P i).edges → e ∉ (P j).edges := by
    have hpw := (List.nodup_flatMap.mp D.nodup_edges).2
    rw [List.pairwise_iff_get] at hpw
    intro i j hij e he he'
    rcases lt_or_gt_of_ne hij with h | h
    · exact hpw i j h he he'
    · exact hpw j i h he' he
  have hstarE : ∀ {e : Sym2 W} {i}, e ∈ (P i).edges → r ∉ e :=
    fun he => GPath.root_notMem_edge_starDel _ he
  have hElnd : ((B.neighborFinset r).toList.flatMap El).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hwnd x, List.nodup_singleton _, ?_⟩
      intro e he e' he' hee
      rw [List.mem_singleton] at he'
      subst he'; subst hee
      obtain ⟨i, -, hi⟩ := (hwe x _).mp he
      exact hstarE hi (Sym2.mem_mk_right _ _)
    · refine (Finset.nodup_toList _).pairwise_of_forall_ne ?_
      intro x hx y hy hxy e he he'
      simp only [El, List.mem_append, List.mem_singleton] at he he'
      rcases he with he | rfl <;> rcases he' with he' | he'
      · obtain ⟨i, hi, hie⟩ := (hwe x _).mp he
        obtain ⟨j, hj, hje⟩ := (hwe y _).mp he'
        exact hDdisj i j (fun h => hxy (hi ▸ hj ▸ h ▸ rfl)) e hie hje
      · obtain ⟨i, -, hie⟩ := (hwe x _).mp he
        exact hstarE hie (he' ▸ Sym2.mem_mk_right _ _)
      · obtain ⟨j, -, hje⟩ := (hwe y _).mp he'
        exact hstarE hje (Sym2.mem_mk_right _ _)
      · exact hxy (Sym2.congr_left.mp he')
  have hElmem : ∀ e, e ∈ (B.neighborFinset r).toList.flatMap El ↔ e ∈ B.edgeSet := by
    intro e
    rw [List.mem_flatMap]
    constructor
    · rintro ⟨x, hx, he⟩
      rw [Finset.mem_toList, mem_neighborFinset] at hx
      simp only [El, List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · obtain ⟨i, -, hie⟩ := (hwe x _).mp he
        exact (mem_starDel_edgeSet.mp ((P i).walk.edges_subset_edgeSet hie)).1
      · exact hx.symm
    · intro heB
      by_cases hre : r ∈ e
      · obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.mp hre
        refine ⟨x, by rw [Finset.mem_toList, mem_neighborFinset]; exact heB, ?_⟩
        simp only [El, List.mem_append, List.mem_singleton]
        exact Or.inr Sym2.eq_swap
      · have heG : e ∈ (starDel B r).edgeSet := mem_starDel_edgeSet.mpr ⟨heB, hre⟩
        rw [D.covers e, List.mem_flatMap] at heG
        obtain ⟨Q, hQ, heQ⟩ := heG
        obtain ⟨i, rfl⟩ := List.get_of_mem hQ
        refine ⟨att i, by rw [Finset.mem_toList, mem_neighborFinset]; exact hattr i, ?_⟩
        simp only [El, List.mem_append]
        exact Or.inl ((hwe _ e).mpr ⟨i, rfl, heQ⟩)
  have hLE : edgesM (L1 ++ L2) = B.edgeFinset.val := by
    rw [hsum]
    refine (Multiset.Nodup.ext (Multiset.coe_nodup.mpr hElnd) B.edgeFinset.nodup).mpr ?_
    intro e
    rw [Multiset.mem_coe, hElmem, Finset.mem_val, mem_edgeFinset]
  obtain ⟨D', hD'size, hD'ends⟩ := exists_decomp_of_edgesM (L1 ++ L2) hLE
  refine ⟨D', by rw [hD'size, List.length_append, hL1, hL2]; simp, ?_⟩
  rw [hD'ends r, endsL_append]
  have hfar : ∀ x, B.Adj r x → far x ≠ r := by
    intro x hx h
    exact hrw x (hadjne x hx) (h ▸ (w x).start_mem_support)
  have h1 : endsL L1 r = 0 := by
    rw [hL1, endsL]
    simp only [List.map_map]
    apply List.sum_eq_zero
    intro n hn
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hn
    simp only [Function.comp_apply, GPath.endsAt, hRps, hRpt]
    rw [if_neg (hfar _ (hmemP p.1 p.2).1), if_neg (hfar _ (hmemP p.1 p.2).2)]
    rfl
  have h2 : endsL L2 r = sg.length := by
    rw [hL2, endsL]
    simp only [List.map_map]
    have : ∀ x ∈ sg.attach, ((fun P => GPath.endsAt P r) ∘ (fun x => Rs x.1 x.2)) x = 1 := by
      intro x _
      simp only [Function.comp_apply, GPath.endsAt, hRss, hRst]
      simp [hfar _ (hmemS x.1 x.2)]
    rw [List.map_congr_left this]
    simp
  omega

end family

/-! ### Hall's theorem with two wildcards -/

section hall

/-- **Hall with defect two.** If every set `S ⊆ I` has at least `|S| − 2` neighbours, some partial
injection on `I` into the neighbourhoods leaves at most two elements of `I` unmatched. -/
theorem hall_defect_two {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (I : Finset ι)
    (C : ι → Finset κ) (h : ∀ S ⊆ I, #S ≤ #(S.biUnion C) + 2) :
    ∃ σ : ι → Option κ, (∀ i ∈ I, ∀ j, σ i = some j → j ∈ C i) ∧
      (∀ i ∈ I, ∀ i' ∈ I, ∀ j, σ i = some j → σ i' = some j → i = i') ∧
      #(I.filter (fun i => σ i = none)) ≤ 2 := by
  classical
  let T : I → Finset (κ ⊕ Fin 2) := fun i => (C i.1).map Function.Embedding.inl ∪
    univ.map Function.Embedding.inr
  have hall : ∀ S : Finset I, #S ≤ #(S.biUnion T) := by
    intro S
    rcases S.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩
    · simp
    have hS := h (S.map (Function.Embedding.subtype _)) (by
      intro x hx; rw [mem_map] at hx; obtain ⟨y, -, rfl⟩ := hx; exact y.2)
    rw [card_map] at hS
    have hsub : ((S.map (Function.Embedding.subtype _)).biUnion C).map Function.Embedding.inl ∪
        univ.map Function.Embedding.inr ⊆ S.biUnion T := by
      intro a ha
      rw [mem_union] at ha
      rw [mem_biUnion]
      rcases ha with ha | ha
      · rw [mem_map] at ha
        obtain ⟨j, hj, rfl⟩ := ha
        rw [mem_biUnion] at hj
        obtain ⟨x, hx, hjx⟩ := hj
        rw [mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact ⟨y, hy, mem_union.mpr (Or.inl (mem_map_of_mem _ hjx))⟩
      · exact ⟨i0, hi0, mem_union.mpr (Or.inr ha)⟩
    have hdisj : Disjoint (((S.map (Function.Embedding.subtype _)).biUnion C).map
        Function.Embedding.inl) (univ.map (Function.Embedding.inr : Fin 2 ↪ κ ⊕ Fin 2)) := by
      rw [Finset.disjoint_left]
      intro a ha ha'
      rw [mem_map] at ha ha'
      obtain ⟨j, -, rfl⟩ := ha
      obtain ⟨l, -, hl⟩ := ha'
      exact Sum.inr_ne_inl hl
    have := card_le_card hsub
    rw [card_union_of_disjoint hdisj, card_map, card_map, card_univ, Fintype.card_fin] at this
    omega
  obtain ⟨f, hfinj, hfT⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective T).mp hall
  let σ : ι → Option κ := fun i => if hi : i ∈ I then Sum.elim some (fun _ => none) (f ⟨i, hi⟩)
    else none
  have hσ : ∀ i (hi : i ∈ I) j, σ i = some j ↔ f ⟨i, hi⟩ = Sum.inl j := by
    intro i hi j
    simp only [σ, dif_pos hi]
    cases f ⟨i, hi⟩ <;> simp
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro i hi j hj
    rw [hσ i hi] at hj
    have := hfT ⟨i, hi⟩
    rw [hj, mem_union, mem_map, mem_map] at this
    rcases this with ⟨j', hj', hjj'⟩ | ⟨l, -, hl⟩
    · cases hjj'; exact hj'
    · exact absurd hl Sum.inr_ne_inl
  · intro i hi i' hi' j h h'
    rw [hσ i hi] at h
    rw [hσ i' hi'] at h'
    have := hfinj (h.trans h'.symm)
    exact congrArg Subtype.val this
  · have hnone : ∀ i (hi : i ∈ I), σ i = none → ∃ l, f ⟨i, hi⟩ = Sum.inr l := by
      intro i hi h
      simp only [σ, dif_pos hi] at h
      revert h
      cases f ⟨i, hi⟩ <;> simp
    choose g hg using hnone
    have hinj : Set.InjOn (fun i : {i // i ∈ I.filter (fun i => σ i = none)} =>
        g i.1 (mem_filter.mp i.2).1 (mem_filter.mp i.2).2) Set.univ := by
      intro a _ b _ hab
      have ha := hg a.1 (mem_filter.mp a.2).1 (mem_filter.mp a.2).2
      have hb := hg b.1 (mem_filter.mp b.2).1 (mem_filter.mp b.2).2
      simp only at hab
      rw [hab] at ha
      have := hfinj (ha.trans hb.symm)
      exact Subtype.ext (by simpa using congrArg Subtype.val this)
    have h1 := Fintype.card_le_of_injective _ (Set.injOn_univ.mp hinj)
    rw [Fintype.card_coe, Fintype.card_fin] at h1
    exact h1

end hall

/-! ### Hall reassembly -/

section hallReassemble

variable {W : Type u} [Fintype W] [DecidableEq W] {B : SimpleGraph W} [DecidableRel B.Adj]
  {r : W}

omit [Fintype W] [DecidableRel B.Adj] in
theorem inMember_att (D : PathDecomp (starDel B r)) (att : Fin D.paths.length → W)
    (hatt : ∀ i, att i = (D.paths.get i).src ∨ att i = (D.paths.get i).tgt)
    (hinj : Function.Injective att) (i : Fin D.paths.length) (v : W) :
    InMember D att (att i) v ↔ v ∈ (D.paths.get i).walk.support := by
  constructor
  · rintro (rfl | ⟨j, hj, hv⟩)
    · rcases hatt i with h | h <;> rw [h]
      · exact (D.paths.get i).walk.start_mem_support
      · exact (D.paths.get i).walk.end_mem_support
    · rw [hinj hj] at hv; exact hv
  · intro hv; exact Or.inr ⟨i, rfl, hv⟩

/-- **Theorem 2.3 (Hall reassembly).** Let `d(r) = 2k − 2`. Split the paths of a decomposition
`D` of `G = B − r`, each attached at an end `att i ∈ N(r)`, into `k − 1` *A-paths* and the rest.
The *C-members* are the members at the other `k − 1` neighbours of `r` (trivial members and the
members of the remaining paths); suppose they are pairwise vertex-disjoint. If for every set `S`
of at least three A-paths, `|S|` plus the number of C-members meeting every path of `S` is at most
`k + 1`, then `B` has a decomposition into `k` paths with exactly two ends at `r`. -/
theorem hallReassemble (D : PathDecomp (starDel B r)) (att : Fin D.paths.length → W)
    (hatt : ∀ i, att i = (D.paths.get i).src ∨ att i = (D.paths.get i).tgt)
    (hattr : ∀ i, B.Adj r (att i)) (hinj : Function.Injective att)
    {k : ℕ} (hk : 2 ≤ k) (hr : B.degree r + 2 = 2 * k) (Aset : Finset (Fin D.paths.length))
    (hA : #Aset + 1 = k)
    (hCdisj : ∀ c ∈ B.neighborFinset r \ Aset.image att, ∀ c' ∈ B.neighborFinset r \ Aset.image att,
      c ≠ c' → ∀ v, InMember D att c v → ¬ InMember D att c' v)
    (hhall : ∀ S ⊆ Aset, 3 ≤ #S → #S + #((B.neighborFinset r \ Aset.image att).filter
      (fun c => ∀ i ∈ S, ∃ v ∈ (D.paths.get i).walk.support, InMember D att c v)) ≤ k + 1) :
    ∃ D' : PathDecomp B, D'.size = k ∧ D'.ends r = 2 := by
  classical
  set P := D.paths.get with hP
  set Cset := B.neighborFinset r \ Aset.image att with hCset
  have himg : Aset.image att ⊆ B.neighborFinset r := by
    intro x hx
    rw [mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    rw [mem_neighborFinset]; exact hattr i
  have hCcard : #Cset + 1 = k := by
    rw [hCset, card_sdiff_of_subset himg, card_image_of_injective _ hinj,
      card_neighborFinset_eq_degree]
    omega
  have hmemC : ∀ c, c ∈ Cset ↔ B.Adj r c ∧ ∀ i ∈ Aset, att i ≠ c := by
    intro c
    rw [hCset, mem_sdiff, mem_neighborFinset, mem_image]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun i hi h => h2 ⟨i, hi, h⟩⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun ⟨i, hi, h⟩ => h2 i hi h⟩
  -- the compatibility neighbourhoods
  let C : Fin D.paths.length → Finset W := fun i =>
    Cset.filter (fun c => ∀ v ∈ (P i).walk.support, ¬ InMember D att c v)
  have hHall : ∀ S ⊆ Aset, #S ≤ #(S.biUnion C) + 2 := by
    intro S hS
    by_cases hS2 : #S ≤ 2
    · omega
    push Not at hS2
    set J := Cset.filter (fun c => ∀ i ∈ S, ∃ v ∈ (P i).walk.support, InMember D att c v)
    have h1 : #S + #J ≤ k + 1 := hhall S hS (by omega)
    have hsub : Cset \ J ⊆ S.biUnion C := by
      intro c hc
      rw [mem_sdiff, mem_filter] at hc
      obtain ⟨hcC, hcJ⟩ := hc
      have : ∃ i ∈ S, ∀ v ∈ (P i).walk.support, ¬ InMember D att c v := by
        by_contra hn
        push Not at hn
        exact hcJ ⟨hcC, hn⟩
      obtain ⟨i, hiS, hi⟩ := this
      rw [mem_biUnion]
      exact ⟨i, hiS, mem_filter.mpr ⟨hcC, hi⟩⟩
    have h2 := card_le_card hsub
    have h3 : #(Cset \ J) + #J = #Cset := card_sdiff_add_card_eq_card (filter_subset _ _)
    omega
  obtain ⟨σ0, hσ0C, hσ0inj, hσ0U⟩ := hall_defect_two Aset C hHall
  have hAne : Aset.Nonempty := by rw [← card_pos]; omega
  -- leave at least one A-path unmatched
  obtain ⟨σ, hσC, hσinj, hσU1, hσU2⟩ : ∃ σ : Fin D.paths.length → Option W,
      (∀ i ∈ Aset, ∀ c, σ i = some c → c ∈ C i) ∧
      (∀ i ∈ Aset, ∀ i' ∈ Aset, ∀ c, σ i = some c → σ i' = some c → i = i') ∧
      1 ≤ #(Aset.filter (fun i => σ i = none)) ∧ #(Aset.filter (fun i => σ i = none)) ≤ 2 := by
    by_cases h0 : 1 ≤ #(Aset.filter (fun i => σ0 i = none))
    · exact ⟨σ0, hσ0C, hσ0inj, h0, hσ0U⟩
    · push Not at h0
      obtain ⟨i0, hi0⟩ := hAne
      have hall0 : ∀ i ∈ Aset, σ0 i ≠ none := by
        intro i hi h
        have : i ∈ Aset.filter (fun i => σ0 i = none) := mem_filter.mpr ⟨hi, h⟩
        rw [Nat.lt_one_iff, card_eq_zero] at h0
        rw [h0] at this; exact notMem_empty _ this
      have hf : Aset.filter (fun i => Function.update σ0 i0 none i = none) = {i0} := by
        ext i; rw [mem_filter, mem_singleton]
        constructor
        · rintro ⟨hi, h⟩; by_contra hne; rw [Function.update_of_ne hne] at h; exact hall0 i hi h
        · rintro rfl; exact ⟨hi0, by simp⟩
      refine ⟨Function.update σ0 i0 none, ?_, ?_, by rw [hf, card_singleton], by
        rw [hf, card_singleton]; omega⟩
      · intro i hi c h
        by_cases hii : i = i0
        · subst hii; simp at h
        · rw [Function.update_of_ne hii] at h; exact hσ0C i hi c h
      · intro i hi i' hi' c h h'
        by_cases hii : i = i0
        · subst hii; simp at h
        by_cases hii' : i' = i0
        · subst hii'; simp at h'
        rw [Function.update_of_ne hii] at h
        rw [Function.update_of_ne hii'] at h'
        exact hσ0inj i hi i' hi' c h h'
  set U := Aset.filter (fun i => σ i = none) with hU
  set Mt := Aset.filter (fun i => σ i ≠ none) with hMt
  let partner : Fin D.paths.length → W := fun i => (σ i).getD (att i)
  have hpart : ∀ i ∈ Mt, σ i = some (partner i) := by
    intro i hi
    rw [hMt, mem_filter] at hi
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hi.2
    simp [partner, hc]
  have hMtA : ∀ i ∈ Mt, i ∈ Aset := fun i hi => (mem_filter.mp hi).1
  have hpartC : ∀ i ∈ Mt, partner i ∈ C i := fun i hi => hσC i (hMtA i hi) _ (hpart i hi)
  have hpartCset : ∀ i ∈ Mt, partner i ∈ Cset := fun i hi => (mem_filter.mp (hpartC i hi)).1
  have hpartinj : ∀ i ∈ Mt, ∀ j ∈ Mt, partner i = partner j → i = j := by
    intro i hi j hj h
    exact hσinj i (hMtA i hi) j (hMtA j hj) _ (hpart i hi) (h ▸ hpart j hj)
  set Img := Mt.image partner with hImg
  set Left := Cset \ Img with hLeft
  have hImgC : Img ⊆ Cset := by
    intro c hc; rw [hImg, mem_image] at hc; obtain ⟨i, hi, rfl⟩ := hc; exact hpartCset i hi
  have hImgcard : #Img = #Mt := card_image_of_injOn (fun i hi j hj h => hpartinj i hi j hj h)
  have hMtU : #Mt + #U = #Aset := by
    rw [hMt, hU, add_comm]
    have := card_filter_add_card_filter_not (s := Aset) (p := fun i => σ i = none)
    simpa using this
  have hLeftcard : #Left = #U := by
    rw [hLeft, card_sdiff_of_subset hImgC, hImgcard]; omega
  have hattC : ∀ i ∈ Aset, att i ∉ Cset := fun i hi h => ((hmemC _).mp h).2 i hi rfl
  have hUA : ∀ i ∈ U, i ∈ Aset := fun i hi => (mem_filter.mp hi).1
  have hUMt : ∀ i ∈ U, i ∉ Mt := by
    intro i hi hi'
    exact (mem_filter.mp hi').2 (mem_filter.mp hi).2
  -- the matched pairs
  set prM := Mt.toList.map (fun i => (att i, partner i)) with hprM
  set base := prM.flatMap (fun p => [p.1, p.2]) with hbase
  have hbase' : ∀ x, x ∈ base ↔ ∃ i ∈ Mt, att i = x ∨ partner i = x := by
    intro x
    rw [hbase, hprM, List.flatMap_map, List.mem_flatMap]
    constructor
    · rintro ⟨i, hi, hx⟩
      rw [mem_toList] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      exact ⟨i, hi, by rcases hx with h | h <;> [exact Or.inl h.symm; exact Or.inr h.symm]⟩
    · rintro ⟨i, hi, hx⟩
      refine ⟨i, by rw [mem_toList]; exact hi, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rcases hx with h | h <;> [exact Or.inl h.symm; exact Or.inr h.symm]
  have hbasend : base.Nodup := by
    rw [hbase, hprM, List.flatMap_map, List.nodup_flatMap]
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [mem_toList] at hi
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
        and_true, not_false_eq_true]
      intro h
      exact hattC i (hMtA i hi) (h ▸ hpartCset i hi)
    · refine (Finset.nodup_toList _).pairwise_of_forall_ne ?_
      intro i hi j hj hij a ha hb
      rw [mem_toList] at hi hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with h | h
      · exact hij (hinj h)
      · exact hattC i (hMtA i hi) (h ▸ hpartCset j hj)
      · exact hattC j (hMtA j hj) (h.symm ▸ hpartCset i hi)
      · exact hij (hpartinj i hi j hj h)
  have hfinal : ∀ ex : List W, ex.Nodup → (∀ y, y ∈ ex ↔ (∃ i ∈ U, att i = y) ∨ y ∈ Left) →
      (base ++ ex).Nodup ∧ ∀ x, x ∈ base ++ ex ↔ B.Adj r x := by
    intro ex hexnd hexmem
    refine ⟨List.nodup_append.mpr ⟨hbasend, hexnd, ?_⟩, ?_⟩
    · intro a ha b hb hab
      subst hab
      obtain ⟨i, hi, hia⟩ := (hbase' a).mp ha
      rcases (hexmem a).mp hb with ⟨j, hj, hja⟩ | hl
      · rcases hia with h | h
        · exact hUMt j hj (hinj (hja.trans h.symm) ▸ hi)
        · exact hattC j (hUA j hj) (hja ▸ h ▸ hpartCset i hi)
      · rw [hLeft, mem_sdiff] at hl
        rcases hia with h | h
        · exact hattC i (hMtA i hi) (h ▸ hl.1)
        · exact hl.2 (h ▸ mem_image_of_mem _ hi)
    · intro x
      rw [List.mem_append, hbase', hexmem]
      constructor
      · rintro ((⟨i, hi, rfl | rfl⟩) | ⟨i, hi, rfl⟩ | hl)
        · exact hattr i
        · exact ((hmemC _).mp (hpartCset i hi)).1
        · exact hattr i
        · rw [hLeft, mem_sdiff] at hl; exact ((hmemC _).mp hl.1).1
      · intro hx
        by_cases hxA : ∃ i ∈ Aset, att i = x
        · obtain ⟨i, hi, rfl⟩ := hxA
          by_cases hσi : σ i = none
          · exact Or.inr (Or.inl ⟨i, mem_filter.mpr ⟨hi, hσi⟩, rfl⟩)
          · exact Or.inl ⟨i, mem_filter.mpr ⟨hi, hσi⟩, Or.inl rfl⟩
        · push Not at hxA
          have hxC : x ∈ Cset := (hmemC x).mpr ⟨hx, hxA⟩
          by_cases hxI : x ∈ Img
          · rw [hImg, mem_image] at hxI
            obtain ⟨i, hi, rfl⟩ := hxI
            exact Or.inl ⟨i, hi, Or.inr rfl⟩
          · exact Or.inr (Or.inr (by rw [hLeft, mem_sdiff]; exact ⟨hxC, hxI⟩))
  have hcompM : ∀ p ∈ prM, ∀ v, InMember D att p.1 v → ¬ InMember D att p.2 v := by
    intro p hp v h1 h2
    rw [hprM, List.mem_map] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    rw [mem_toList] at hi
    rw [inMember_att D att hatt hinj] at h1
    exact (mem_filter.mp (hpartC i hi)).2 v h1 h2
  have hprMlen : prM.length = #Mt := by rw [hprM, List.length_map, length_toList]
  rcases (show #U = 1 ∨ #U = 2 by omega) with hU1 | hU2
  · obtain ⟨i1, hi1⟩ := card_eq_one.mp hU1
    obtain ⟨c1, hc1⟩ := card_eq_one.mp (hLeftcard.trans hU1)
    have hfin := hfinal [att i1, c1] (by
      have : att i1 ≠ c1 := by
        intro h
        have : c1 ∈ Left := by rw [hc1]; exact mem_singleton_self _
        rw [hLeft, mem_sdiff] at this
        exact hattC i1 (hUA i1 (by rw [hi1]; exact mem_singleton_self _)) (h ▸ this.1)
      simp [this]) (by
      intro y
      simp only [List.mem_cons, List.not_mem_nil, or_false, hi1, hc1, mem_singleton]
      constructor
      · rintro (rfl | rfl)
        · exact Or.inl ⟨i1, rfl, rfl⟩
        · exact Or.inr rfl
      · rintro (⟨i, rfl, rfl⟩ | rfl)
        · exact Or.inl rfl
        · exact Or.inr rfl)
    obtain ⟨D', hD's, hD'e⟩ := famReassemble D att hatt hattr hinj prM [att i1, c1]
      (by rw [← hbase]; exact hfin.1) (by rw [← hbase]; exact hfin.2) hcompM
    refine ⟨D', ?_, ?_⟩
    · rw [hD's, hprMlen]; simp only [List.length_cons, List.length_nil]; omega
    · rw [hD'e]; rfl
  · obtain ⟨i1, i2, hi12, hi⟩ := card_eq_two.mp hU2
    obtain ⟨c1, c2, hc12, hc⟩ := card_eq_two.mp (hLeftcard.trans hU2)
    have hiU : ∀ i, i ∈ U ↔ i = i1 ∨ i = i2 := by intro i; rw [hi, mem_insert, mem_singleton]
    have hcL : ∀ c, c ∈ Left ↔ c = c1 ∨ c = c2 := by intro c; rw [hc, mem_insert, mem_singleton]
    have hcLC : ∀ c, c ∈ Left → c ∈ Cset := fun c h => (mem_sdiff.mp h).1
    have hattL : ∀ i ∈ U, ∀ c ∈ Left, att i ≠ c :=
      fun i hi c hc h => hattC i (hUA i hi) (h ▸ hcLC c hc)
    have h1U : i1 ∈ U := (hiU i1).mpr (Or.inl rfl)
    have h2U : i2 ∈ U := (hiU i2).mpr (Or.inr rfl)
    have h1L : c1 ∈ Left := (hcL c1).mpr (Or.inl rfl)
    have h2L : c2 ∈ Left := (hcL c2).mpr (Or.inr rfl)
    have hfin := hfinal ([c1, c2] ++ [att i1, att i2]) (by
      simp only [List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, List.nodup_nil, and_true, not_or]
      refine ⟨⟨hc12, fun h => hattL i1 h1U c1 h1L h.symm, fun h => hattL i2 h2U c1 h1L h.symm⟩,
        ⟨fun h => hattL i1 h1U c2 h2L h.symm, fun h => hattL i2 h2U c2 h2L h.symm⟩,
        fun h => hi12 (hinj h), not_false⟩) (by
      intro y
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
        hiU, hcL]
      constructor
      · rintro (rfl | rfl | rfl | rfl)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl ⟨i1, Or.inl rfl, rfl⟩
        · exact Or.inl ⟨i2, Or.inr rfl, rfl⟩
      · rintro (⟨i, rfl | rfl, rfl⟩ | rfl | rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl))
    obtain ⟨D', hD's, hD'e⟩ := famReassemble D att hatt hattr hinj (prM ++ [(c1, c2)])
      [att i1, att i2] (by
        rw [List.flatMap_append, ← hbase, List.append_assoc]
        simpa using hfin.1) (by
        intro x
        rw [List.flatMap_append, ← hbase, List.append_assoc]
        simpa using hfin.2 x) (by
        intro p hp
        rw [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact hcompM p hp
        · exact hCdisj c1 (hcLC c1 h1L) c2 (hcLC c2 h2L) hc12)
    refine ⟨D', ?_, ?_⟩
    · rw [hD's, List.length_append, hprMlen]; simp only [List.length_cons, List.length_nil]
      omega
    · rw [hD'e]; rfl

omit [Fintype W] [DecidableRel B.Adj] in
theorem inMember_triv (D : PathDecomp (starDel B r)) (att : Fin D.paths.length → W) {c : W}
    (hc : ∀ i, att i ≠ c) (v : W) : InMember D att c v ↔ v = c := by
  constructor
  · rintro (h | ⟨i, hi, -⟩)
    · exact h
    · exact absurd hi (hc i)
  · exact Or.inl

end hallReassemble

/-! ### Theorem A: at most one even vertex in `B − r` -/

section oneEven

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- **Theorem A.** Let `B` have order `2k`, `d(r) = 2k − 2`, every neighbour of `r` of degree at
least `2`, and let `G = B − r` have at most one vertex of positive even degree (no parity condition
on `B`). Let `ε ≥ 1` if some neighbour of `r` has even degree in `G` (`ε = 0` is allowed
otherwise, e.g. when `B` is Eulerian). With `h_t = #{x ∈ N(r) : d(x) ≥ 2t}`, suppose that for every
`3 ≤ t ≤ k − 1`, `⌊(h_t + ε)/2⌋ + t ≤ k + 1` or `⌊h_{t+1}/2⌋ + ε + 2t ≤ k + 1`. Then `B` has a
decomposition into `k` paths with exactly two ends at `r`. -/
theorem exists_decomp_of_oneEven (B : SimpleGraph W) [DecidableRel B.Adj] {k : ℕ} (hk : 2 ≤ k)
    (hW : Fintype.card W = 2 * k) (r : W) (hr : B.degree r + 2 = 2 * k)
    (hN : ∀ x, B.Adj r x → 2 ≤ B.degree x)
    (hev : (evenSet (starDel B r)).card ≤ 1) (ε : ℕ)
    (hε : ∀ x, B.Adj r x → (starDel B r).degree x % 2 = 0 → 1 ≤ ε)
    (hstar : ∀ t, 3 ≤ t → t ≤ k - 1 →
      (#(heavyNbrs B r t) + ε) / 2 + t ≤ k + 1 ∨
        #(heavyNbrs B r (t + 1)) / 2 + ε + 2 * t ≤ k + 1) :
    ∃ D : PathDecomp B, D.size = k ∧ D.ends r = 2 := by
  classical
  obtain ⟨D, hD⟩ := lovasz_ends (starDel B r) hev
  set P := D.paths.get with hP
  have hdegN : ∀ x, B.Adj r x → (starDel B r).degree x + 1 = B.degree x :=
    fun x hx => starDel_degree_of_adj hx
  -- the non-neighbour `s`
  have hcS : #(univ \ insert r (B.neighborFinset r)) = 1 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hW, card_insert_of_notMem
      (by rw [mem_neighborFinset]; exact B.loopless.irrefl r), card_neighborFinset_eq_degree]
    omega
  obtain ⟨s, hs⟩ := card_eq_one.mp hcS
  have hsuniq : ∀ v, v ≠ r → ¬ B.Adj r v → v = s := by
    intro v hvr hv
    have : v ∈ univ \ insert r (B.neighborFinset r) := by
      rw [mem_sdiff, mem_insert, mem_neighborFinset]; push Not; exact ⟨mem_univ _, hvr, hv⟩
    rw [hs, mem_singleton] at this; exact this
  have hends1 : ∀ v, D.ends v ≤ 1 := fun v => by rw [hD v]; omega
  have hendr : D.ends r = 0 := by rw [hD r, starDel_degree_self]
  have hend_pos : ∀ i v, 1 ≤ (P i).endsAt v → 1 ≤ D.ends v :=
    fun i v h => h.trans (D.endsAt_le_ends v i)
  have hend_uniq : ∀ i j v, 1 ≤ (P i).endsAt v → 1 ≤ (P j).endsAt v → i = j := by
    intro i j v hi hj
    by_contra hij
    have := D.two_le_ends_of_ne hij hi hj
    have := hends1 v
    omega
  have hsrc : ∀ i, 1 ≤ (P i).endsAt (P i).src := fun i => (P i).endsAt_src
  have htgt : ∀ i, 1 ≤ (P i).endsAt (P i).tgt := fun i => (P i).endsAt_tgt
  have hne_r : ∀ i v, 1 ≤ (P i).endsAt v → v ≠ r := by
    intro i v h hv; subst hv; have := hend_pos i _ h; omega
  -- orientation: the attachment is an end adjacent to `r`, the larger-degree one if both are
  let att : Fin D.paths.length → W := fun i =>
    if B.Adj r (P i).src ∧ (B.Adj r (P i).tgt → B.degree (P i).tgt ≤ B.degree (P i).src) then
      (P i).src else (P i).tgt
  let lo : Fin D.paths.length → W := fun i =>
    if B.Adj r (P i).src ∧ (B.Adj r (P i).tgt → B.degree (P i).tgt ≤ B.degree (P i).src) then
      (P i).tgt else (P i).src
  have hatt : ∀ i, att i = (P i).src ∨ att i = (P i).tgt := by
    intro i; simp only [att]; split_ifs <;> simp
  have hlo : ∀ i, (lo i = (P i).src ∧ att i = (P i).tgt) ∨ (lo i = (P i).tgt ∧ att i = (P i).src) := by
    intro i; simp only [att, lo]; split_ifs <;> simp
  have hattr : ∀ i, B.Adj r (att i) := by
    intro i
    simp only [att]
    split_ifs with h
    · exact h.1
    · by_cases hsr : B.Adj r (P i).src
      · push Not at h; exact (h hsr).1
      · by_contra htr
        have h1 := hsuniq _ (hne_r i _ (hsrc i)) hsr
        have h2 := hsuniq _ (hne_r i _ (htgt i)) htr
        exact (P i).src_ne_tgt (h1.trans h2.symm)
  have hlodeg : ∀ i, B.Adj r (lo i) → B.degree (lo i) ≤ B.degree (att i) := by
    intro i hl
    by_cases h : B.Adj r (P i).src ∧ (B.Adj r (P i).tgt → B.degree (P i).tgt ≤ B.degree (P i).src)
    · have e1 : att i = (P i).src := if_pos h
      have e2 : lo i = (P i).tgt := if_pos h
      rw [e2] at hl; rw [e1, e2]; exact h.2 hl
    · have e1 : att i = (P i).tgt := if_neg h
      have e2 : lo i = (P i).src := if_neg h
      rw [e2] at hl; rw [e1, e2]
      push Not at h
      exact (h hl).2.le
  have hatt_end : ∀ i, 1 ≤ (P i).endsAt (att i) := by
    intro i; rcases hatt i with h | h <;> rw [h]; exacts [hsrc i, htgt i]
  have hlo_end : ∀ i, 1 ≤ (P i).endsAt (lo i) := by
    intro i; rcases hlo i with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]; exacts [hsrc i, htgt i]
  have hinj : Function.Injective att := fun i j h =>
    hend_uniq i j (att i) (hatt_end i) (h ▸ hatt_end j)
  have hlo_att : ∀ i j, lo i ≠ att j := by
    intro i j h
    have := hend_uniq i j _ (hlo_end i) (h ▸ hatt_end j)
    subst this
    rcases hlo i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (P i).src_ne_tgt (h1.symm.trans (h.trans h2))
    · exact (P i).src_ne_tgt (h2.symm.trans (h.symm.trans h1))
  -- the number of paths
  have hsize : D.paths.length + 1 = k := by
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
        · rw [h]
          have : s ∈ univ \ insert r (B.neighborFinset r) := by rw [hs]; exact mem_singleton_self _
          rw [mem_sdiff, mem_insert, mem_neighborFinset] at this
          push Not at this
          exact ⟨mem_univ _, this.2.2⟩
    have hsr : s ≠ r := by
      have : s ∈ univ \ insert r (B.neighborFinset r) := by rw [hs]; exact mem_singleton_self _
      rw [mem_sdiff, mem_insert] at this; push Not at this; exact this.2.1
    have hrest_sum : ∑ v ∈ univ \ N, D.ends v = D.ends s := by
      rw [hrest, sum_pair hsr.symm, hendr, zero_add]
    set E := N.filter (fun x => D.ends x = 0) with hE
    have hEsub : E ⊆ evenSet (starDel B r) := by
      intro x hx
      rw [hE, mem_filter, hNdef, mem_neighborFinset] at hx
      rw [mem_evenSet_iff]
      have := hdegN x hx.1
      have := hN x hx.1
      rw [hD x] at hx
      exact ⟨by omega, hx.2⟩
    have hEcard := (card_le_card hEsub).trans hev
    have hNsum : ∑ v ∈ N, D.ends v + #E = #N := by
      rw [hE, card_filter, ← sum_add_distrib, card_eq_sum_ones]
      refine sum_congr rfl (fun x _ => ?_)
      have := hends1 x
      split_ifs with h <;> omega
    rw [hsplit, hrest_sum] at h1
    have hNc : #N = 2 * k - 2 := by rw [hNdef, card_neighborFinset_eq_degree]; omega
    have := hends1 s
    unfold PathDecomp.size at h1
    omega
  have hmuniv : #(univ : Finset (Fin D.paths.length)) + 1 = k := by
    rw [card_univ, Fintype.card_fin]; exact hsize
  have hCtriv : ∀ c ∈ B.neighborFinset r \ univ.image att, ∀ i, att i ≠ c := by
    intro c hc i h; rw [mem_sdiff, mem_image] at hc; exact hc.2 ⟨i, mem_univ _, h⟩
  have hcount' : ∀ x, B.Adj r x → ∀ S' : Finset (Fin D.paths.length),
      (∀ i ∈ S', x ∈ (P i).walk.support) → 2 * #S' ≤ B.degree x := by
    intro x hx S' hS'
    have h := D.degree_add_ends_eq_card x
    have h2 := hdegN x hx
    rw [hD x] at h
    have : #S' ≤ #(univ.filter (fun i => x ∈ (D.paths.get i).walk.support)) :=
      card_le_card (fun i hi => mem_filter.mpr ⟨mem_univ _, hS' i hi⟩)
    have : (starDel B r).degree x % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ two_pos)
    omega
  have hlo_inj : Function.Injective lo := fun i j h =>
    hend_uniq i j (lo i) (hlo_end i) (h ▸ hlo_end j)
  -- trivial members with no end: even in `G`, at most `ε` of them
  have hzero : ∀ X : Finset W, (∀ x ∈ X, B.Adj r x ∧ D.ends x = 0) → #X ≤ ε ∧ #X ≤ 1 := by
    intro X hX
    have hsub : X ⊆ evenSet (starDel B r) := by
      intro x hx
      obtain ⟨h1, h2⟩ := hX x hx
      rw [mem_evenSet_iff]
      have := hdegN x h1
      have := hN x h1
      rw [hD x] at h2
      exact ⟨by omega, h2⟩
    have h1 := (card_le_card hsub).trans hev
    refine ⟨?_, h1⟩
    rcases Nat.eq_zero_or_pos #X with h0 | hpos
    · omega
    · obtain ⟨x, hx⟩ := card_pos.mp hpos
      obtain ⟨hx1, hx2⟩ := hX x hx
      rw [hD x] at hx2
      have := hε x hx1 hx2
      omega
  -- heavy pairs
  have hpairs : ∀ u, 2 * #(univ.filter (fun j => B.Adj r (lo j) ∧ 2 * u ≤ B.degree (lo j))) +
      #((B.neighborFinset r).filter (fun x => D.ends x = 0 ∧ 2 * u ≤ B.degree x)) ≤
      #(heavyNbrs B r u) := by
    intro u
    set X := univ.filter (fun j => B.Adj r (lo j) ∧ 2 * u ≤ B.degree (lo j)) with hX
    set Z0 := (B.neighborFinset r).filter (fun x => D.ends x = 0 ∧ 2 * u ≤ B.degree x) with hZ0
    have hsub : X.image lo ∪ X.image att ∪ Z0 ⊆ heavyNbrs B r u := by
      intro x hx
      rw [mem_union, mem_union, mem_image, mem_image] at hx
      rw [heavyNbrs, mem_filter, mem_neighborFinset]
      rcases hx with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) | hx
      · rw [hX, mem_filter] at hj; exact hj.2
      · rw [hX, mem_filter] at hj; exact ⟨hattr j, hj.2.2.trans (hlodeg j hj.2.1)⟩
      · rw [hZ0, mem_filter, mem_neighborFinset] at hx; exact ⟨hx.1, hx.2.2⟩
    have hd1 : Disjoint (X.image lo) (X.image att) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [mem_image] at hx hx'
      obtain ⟨j, -, rfl⟩ := hx
      obtain ⟨j', -, h⟩ := hx'
      exact hlo_att j j' h.symm
    have hd2 : Disjoint (X.image lo ∪ X.image att) Z0 := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [hZ0, mem_filter] at hx'
      rw [mem_union, mem_image, mem_image] at hx
      rcases hx with ⟨j, -, rfl⟩ | ⟨j, -, rfl⟩
      · have := hend_pos j _ (hlo_end j); omega
      · have := hend_pos j _ (hatt_end j); omega
    have := card_le_card hsub
    rw [card_union_of_disjoint hd2, card_union_of_disjoint hd1, card_image_of_injective _ hlo_inj,
      card_image_of_injective _ hinj] at this
    omega
  refine hallReassemble D att hatt hattr hinj hk hr univ hmuniv ?_ ?_
  · intro c hc c' hc' hcc' v h1 h2
    rw [inMember_triv D att (hCtriv c hc)] at h1
    rw [inMember_triv D att (hCtriv c' hc')] at h2
    exact hcc' (h1.symm.trans h2)
  · intro S _ hS3
    set J := (B.neighborFinset r \ univ.image att).filter
      (fun c => ∀ i ∈ S, ∃ v ∈ (D.paths.get i).walk.support, InMember D att c v) with hJ
    have hJC : ∀ c ∈ J, c ∈ B.neighborFinset r \ univ.image att := fun c hc => (mem_filter.mp hc).1
    have hJadj : ∀ c ∈ J, B.Adj r c := fun c hc =>
      (B.mem_neighborFinset r c).mp (mem_sdiff.mp (hJC c hc)).1
    have hJon : ∀ c ∈ J, ∀ i ∈ S, c ∈ (P i).walk.support := by
      intro c hc i hi
      obtain ⟨v, hv, hm⟩ := (mem_filter.mp hc).2 i hi
      rw [inMember_triv D att (hCtriv c (hJC c hc))] at hm
      rw [← hm]; exact hv
    have hJdeg : ∀ c ∈ J, 2 * #S ≤ B.degree c := fun c hc => hcount' c (hJadj c hc) S (hJon c hc)
    -- members of `J` with an end are the far ends `lo j` of their own paths
    have hown : ∀ c ∈ J, D.ends c ≠ 0 → ∃ j, lo j = c := by
      intro c hc hne
      rw [D.ends_eq_sum_get] at hne
      obtain ⟨j, -, hj⟩ := exists_ne_zero_of_sum_ne_zero hne
      have hpos : 1 ≤ (P j).endsAt c := Nat.one_le_iff_ne_zero.mpr hj
      have hc' : (P j).src = c ∨ (P j).tgt = c := by
        unfold GPath.endsAt at hpos
        by_contra hn
        push Not at hn
        simp [hn.1, hn.2] at hpos
      refine ⟨j, ?_⟩
      have hna : att j ≠ c := hCtriv c (hJC c hc) j
      rcases hlo j with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hc' with h | h
      · exact h1.trans h
      · exact absurd (h2.trans h) hna
      · exact absurd (h2.trans h) hna
      · exact h1.trans h
    set J0 := J.filter (fun c => D.ends c = 0) with hJ0
    set J1 := J.filter (fun c => D.ends c ≠ 0) with hJ1
    have hJsplit : #J = #J0 + #J1 := by
      rw [hJ0, hJ1, add_comm]
      exact (card_filter_add_card_filter_not (s := J) (p := fun c => D.ends c ≠ 0)).symm.trans
        (by simp [add_comm])
    have hJ0b := hzero J0 (fun x hx => ⟨hJadj x (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩)
    have htk : #S ≤ k - 1 := by
      have := card_le_univ S
      rw [Fintype.card_fin] at this; omega
    rcases hstar #S hS3 htk with hA1 | hA2
    · -- every member of `J` is heavy
      set X := univ.filter (fun j => B.Adj r (lo j) ∧ 2 * #S ≤ B.degree (lo j)) with hX
      have hJ1X : J1 ⊆ X.image lo := by
        intro c hc
        rw [hJ1, mem_filter] at hc
        obtain ⟨j, rfl⟩ := hown c hc.1 hc.2
        exact mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, hJadj _ hc.1, hJdeg _ hc.1⟩)
      have h1 := (card_le_card hJ1X).trans card_image_le
      have hJ0Z : J0 ⊆ (B.neighborFinset r).filter (fun x => D.ends x = 0 ∧ 2 * #S ≤ B.degree x) := by
        intro c hc
        rw [hJ0, mem_filter] at hc
        exact mem_filter.mpr ⟨(B.mem_neighborFinset r c).mpr (hJadj c hc.1), hc.2, hJdeg c hc.1⟩
      have h2 := card_le_card hJ0Z
      have h3 : 2 * #X + #((B.neighborFinset r).filter
          (fun x => D.ends x = 0 ∧ 2 * #S ≤ B.degree x)) ≤ #(heavyNbrs B r #S) := hpairs #S
      have h4 := (hzero ((B.neighborFinset r).filter (fun x => D.ends x = 0 ∧ 2 * #S ≤ B.degree x))
        (fun x hx => by
          rw [mem_filter, mem_neighborFinset] at hx; exact ⟨hx.1, hx.2.1⟩)).1
      have h5 : 2 * #J ≤ #(heavyNbrs B r #S) + ε := by
        have := card_le_card hJ0Z
        omega
      have h6 : #J ≤ (#(heavyNbrs B r #S) + ε) / 2 := by
        rw [Nat.le_div_iff_mul_le two_pos]; omega
      omega
    · -- members of `J` whose own path is outside `S` are heavier
      set X := univ.filter (fun j => B.Adj r (lo j) ∧ 2 * (#S + 1) ≤ B.degree (lo j)) with hX
      have hJ1X : J1 ⊆ S.image lo ∪ X.image lo := by
        intro c hc
        rw [hJ1, mem_filter] at hc
        obtain ⟨j, rfl⟩ := hown _ hc.1 hc.2
        rw [mem_union]
        by_cases hjS : j ∈ S
        · exact Or.inl (mem_image_of_mem _ hjS)
        · right
          refine mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, hJadj _ hc.1, ?_⟩)
          have := hcount' _ (hJadj _ hc.1) (insert j S) (by
            intro i hi
            rw [mem_insert] at hi
            rcases hi with rfl | hi
            · rcases hlo i with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
              · exact (P i).walk.start_mem_support
              · exact (P i).walk.end_mem_support
            · exact hJon _ hc.1 i hi)
          rw [card_insert_of_notMem hjS] at this
          exact this
      have h1 := (card_le_card hJ1X).trans ((card_union_le _ _).trans
        (add_le_add card_image_le card_image_le))
      have h3 : 2 * #X + #((B.neighborFinset r).filter
          (fun x => D.ends x = 0 ∧ 2 * (#S + 1) ≤ B.degree x)) ≤ #(heavyNbrs B r (#S + 1)) :=
        hpairs (#S + 1)
      have h6 : #X ≤ #(heavyNbrs B r (#S + 1)) / 2 := by
        rw [Nat.le_div_iff_mul_le two_pos]; omega
      omega

end oneEven

/-! ### The spine's test (T1) -/

section test1

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A decomposition of `J − z` into `k` paths with two ends at `r` is the two-end test at `r`. -/
theorem test1At_of_decomp (J : SimpleGraph V) [DecidableRel J.Adj] {z r : V} {k : ℕ}
    (hV : Fintype.card V = 2 * k + 1) (hzr : J.Adj z r)
    (h : ∃ D : PathDecomp (delVert J z), D.size = k ∧ D.ends ⟨r, hzr.ne'⟩ = 2) :
    Test1At J z r := by
  intro hr
  obtain ⟨D, hD, hDr⟩ := h
  exact ⟨D, by rw [hD, hV]; omega, hDr.ge⟩

/-- **Theorem A, spine form.** Let `z` be a vertex of `J` (order `2k + 1`), `r ∈ N(z)` of degree
`|J| − 2`, and `B = J − z`. If `B − r` has at most one vertex of positive even degree, every
neighbour of `r` has degree at least `2` in `B`, and the degree condition of
`exists_decomp_of_oneEven` holds in `B`, then the two-end test (T1) holds at `r`. -/
theorem test1At_of_oneEven (J : SimpleGraph V) [DecidableRel J.Adj] {z r : V} {k : ℕ}
    (hk : 2 ≤ k) (hV : Fintype.card V = 2 * k + 1) (hzr : J.Adj z r)
    (hr : J.degree r + 2 = 2 * k + 1)
    (hN : ∀ x, (delVert J z).Adj ⟨r, hzr.ne'⟩ x → 2 ≤ (delVert J z).degree x)
    (hev : (evenSet (starDel (delVert J z) ⟨r, hzr.ne'⟩)).card ≤ 1) (ε : ℕ)
    (hε : ∀ x, (delVert J z).Adj ⟨r, hzr.ne'⟩ x →
      (starDel (delVert J z) ⟨r, hzr.ne'⟩).degree x % 2 = 0 → 1 ≤ ε)
    (hstar : ∀ t, 3 ≤ t → t ≤ k - 1 →
      (#(heavyNbrs (delVert J z) ⟨r, hzr.ne'⟩ t) + ε) / 2 + t ≤ k + 1 ∨
        #(heavyNbrs (delVert J z) ⟨r, hzr.ne'⟩ (t + 1)) / 2 + ε + 2 * t ≤ k + 1) :
    Test1At J z r := by
  have hW : Fintype.card {v | v ≠ z} = 2 * k := by rw [card_delVert, hV]; omega
  have hdeg := delVert_degree (J := J) z ⟨r, hzr.ne'⟩
  rw [if_pos hzr.symm] at hdeg
  exact test1At_of_decomp J hV hzr
    (exists_decomp_of_oneEven (delVert J z) hk hW ⟨r, hzr.ne'⟩ (by simp only at hdeg; omega)
      hN hev ε hε hstar)

end test1

end Gallai
