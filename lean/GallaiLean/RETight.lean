import GallaiLean.CycleInsert
import GallaiLean.Lovasz
import GallaiLean.PathSurgery
import Mathlib.Combinatorics.Hall.Basic

/-!
# RE at roots of degree `n − 2`: the Lovász-plus-matching method

Manuscript: `manuscripts/re-tight`.

Let `B` have even order `n = 2k`, every degree even, and let `r` have degree `n − 2`. Then
`G = B − r` (here `starDel B r`: `B` with the edges at `r` deleted, `r` kept as an isolated
vertex) has exactly one even vertex of positive degree, so Lovász's theorem gives `k − 1` paths
whose ends are the neighbours of `r`, each once. Every neighbour `x` of `r` lies on exactly
`d(x)/2` of them. Make the end of smaller degree of each path *trivial*. A path `P` can be
closed through `r` at its other end and continued to a trivial end not on `P`; Hall's theorem
with defect `2` matches all but two paths in this way, under a degree condition on `N(r)`; the
two leftover trivial ends form one more path through `r`.

* `starDel`, `mem_starDel_edgeSet`, `starDel_degree_of_adj`, `starDel_degree_of_not_adj`,
  `starDel_degree_self`.
* **`reassemble`**: from a decomposition of `starDel B r` whose ends pair up `N(r)`, an
  orientation `lo/hi` of every path, and a partial injection `σ` from paths to trivial ends
  `lo j ∉ P_i` leaving one or two paths unmatched, a decomposition of `B` with one more path
  and exactly two ends at `r`.
* **`exists_decomp_of_degStar`** (manuscript Theorem 3.1): if for every `3 ≤ t ≤ k − 1`,
  writing `h_t = #{x ∈ N(r) : d(x) ≥ 2t}`, either `⌊h_t/2⌋ + t ≤ k + 1` or
  `⌊h_{t+1}/2⌋ + 2t ≤ k + 1`, then `B` has a decomposition into `k` paths with exactly two ends
  at `r`. **`rootedDecomp_of_degStar`**: hence `RootedDecomp B r`.
* **`rootedDecomp_of_few_heavy`** (Corollary 3.3(a)): at most five neighbours of `r` have degree
  at least `6`. **`rootedDecomp_of_deg_le_six`** (Corollary 3.3(b)): `n ≥ 10` and every neighbour
  of `r` has degree at most `6`.
-/

open SimpleGraph Finset

namespace Gallai

universe u

/-! ### Deleting the edges at a vertex -/

section starDel

variable {W : Type u}

/-- `B` with every edge at `r` deleted (`r` stays, isolated). -/
def starDel (B : SimpleGraph W) (r : W) : SimpleGraph W where
  Adj x y := B.Adj x y ∧ x ≠ r ∧ y ≠ r
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun x h => B.loopless.irrefl x h.1⟩

instance starDel.decAdj (B : SimpleGraph W) [DecidableRel B.Adj] (r : W) [DecidableEq W] :
    DecidableRel (starDel B r).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

variable {B : SimpleGraph W} {r : W}

theorem starDel_adj {x y : W} : (starDel B r).Adj x y ↔ B.Adj x y ∧ x ≠ r ∧ y ≠ r := Iff.rfl

theorem starDel_le : starDel B r ≤ B := fun _ _ h => h.1

theorem mem_starDel_edgeSet {e : Sym2 W} :
    e ∈ (starDel B r).edgeSet ↔ e ∈ B.edgeSet ∧ r ∉ e := by
  induction e using Sym2.inductionOn with
  | hf a b =>
    rw [mem_edgeSet, mem_edgeSet, starDel_adj, Sym2.mem_iff]
    constructor
    · rintro ⟨h, ha, hb⟩
      exact ⟨h, by rintro (h' | h') <;> [exact ha h'.symm; exact hb h'.symm]⟩
    · rintro ⟨h, hn⟩
      exact ⟨h, fun e => hn (Or.inl e.symm), fun e => hn (Or.inr e.symm)⟩

/-- A path of `starDel B r` does not visit `r`. -/
theorem GPath.root_notMem_starDel (P : GPath (starDel B r)) : r ∉ P.walk.support := by
  intro h
  obtain ⟨y, hy⟩ := P.adj_of_mem_support h
  exact hy.2.1 rfl

/-- No edge of a path of `starDel B r` contains `r`. -/
theorem GPath.root_notMem_edge_starDel (P : GPath (starDel B r)) {e : Sym2 W}
    (he : e ∈ P.edges) : r ∉ e :=
  (mem_starDel_edgeSet.mp (P.walk.edges_subset_edgeSet he)).2

variable [Fintype W] [DecidableEq W] [DecidableRel B.Adj]

theorem starDel_neighborFinset_of_ne {x : W} (hx : x ≠ r) :
    (starDel B r).neighborFinset x = (B.neighborFinset x).erase r := by
  ext y
  rw [mem_neighborFinset, mem_erase, mem_neighborFinset, starDel_adj]
  tauto

theorem starDel_degree_of_adj {x : W} (hx : B.Adj r x) :
    (starDel B r).degree x + 1 = B.degree x := by
  have hm : r ∈ B.neighborFinset x := by rw [mem_neighborFinset]; exact hx.symm
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
    starDel_neighborFinset_of_ne hx.ne', card_erase_of_mem hm]
  have : 0 < #(B.neighborFinset x) := card_pos.mpr ⟨r, hm⟩
  omega

theorem starDel_degree_of_not_adj {x : W} (hx : x ≠ r) (h : ¬ B.Adj r x) :
    (starDel B r).degree x = B.degree x := by
  have hm : r ∉ B.neighborFinset x := by rw [mem_neighborFinset]; exact fun h' => h h'.symm
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
    starDel_neighborFinset_of_ne hx, erase_eq_of_notMem hm]

theorem starDel_degree_self : (starDel B r).degree r = 0 := by
  rw [← card_neighborFinset_eq_degree, card_eq_zero, eq_empty_iff_forall_notMem]
  intro y hy
  rw [mem_neighborFinset, starDel_adj] at hy
  exact hy.2.1 rfl

end starDel

/-! ### Lists of paths indexed by `Fin` -/

section finIndex

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

theorem PathDecomp.ends_eq_sum_get (D : PathDecomp G) (v : V) :
    D.ends v = ∑ i, (D.paths.get i).endsAt v := by
  rw [PathDecomp.ends, ← List.sum_ofFn]
  congr 1
  conv_lhs => rw [← List.ofFn_get D.paths]
  rw [List.map_ofFn]
  rfl

theorem PathDecomp.degree_eq_sum_get (D : PathDecomp G) (v : V) [Fintype (G.neighborSet v)] :
    G.degree v = ∑ i, (D.paths.get i).incid v := by
  rw [D.degree_eq_sum v, ← List.sum_ofFn]
  congr 1
  conv_lhs => rw [← List.ofFn_get D.paths]
  rw [List.map_ofFn]
  rfl

/-- `deg v + ends v = 2 · #{paths through v}`. -/
theorem PathDecomp.degree_add_ends_eq_card (D : PathDecomp G) (v : V)
    [Fintype (G.neighborSet v)] :
    G.degree v + D.ends v =
      2 * #(univ.filter (fun i => v ∈ (D.paths.get i).walk.support)) := by
  rw [D.degree_eq_sum_get, D.ends_eq_sum_get, ← sum_add_distrib, card_filter, mul_sum]
  refine sum_congr rfl (fun i _ => ?_)
  rw [GPath.incid_add_endsAt]

/-- An end that two different paths share has at least two ends counted. -/
theorem PathDecomp.two_le_ends_of_ne (D : PathDecomp G) {v : V} {i j : Fin D.paths.length}
    (hij : i ≠ j) (hi : 1 ≤ (D.paths.get i).endsAt v) (hj : 1 ≤ (D.paths.get j).endsAt v) :
    2 ≤ D.ends v := by
  rw [D.ends_eq_sum_get]
  have := sum_le_sum_of_subset (f := fun l => (D.paths.get l).endsAt v)
    (subset_univ ({i, j} : Finset _))
  rw [sum_pair hij] at this
  omega

theorem PathDecomp.endsAt_le_ends (D : PathDecomp G) (v : V) (i : Fin D.paths.length) :
    (D.paths.get i).endsAt v ≤ D.ends v := by
  rw [D.ends_eq_sum_get]
  exact single_le_sum (f := fun l => (D.paths.get l).endsAt v) (fun _ _ => Nat.zero_le _)
    (mem_univ i)

theorem GPath.endsAt_src (P : GPath G) : 1 ≤ P.endsAt P.src := by
  unfold GPath.endsAt; simp

theorem GPath.endsAt_tgt (P : GPath G) : 1 ≤ P.endsAt P.tgt := by
  unfold GPath.endsAt; simp

end finIndex

/-! ### Oriented copies in the complete graph -/

section orient

variable {V : Type u} {K : SimpleGraph V}

/-- A path, oriented from either end, as a walk of `⊤`. -/
theorem GPath.exists_oriented (P : GPath K) {a b : V}
    (h : (a = P.src ∧ b = P.tgt) ∨ (a = P.tgt ∧ b = P.src)) :
    ∃ p : (⊤ : SimpleGraph V).Walk a b, p.support.Nodup ∧ 0 < p.length ∧
      (∀ e, e ∈ p.edges ↔ e ∈ P.edges) ∧ (∀ v, v ∈ p.support ↔ v ∈ P.walk.support) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨P.walk.mapLe le_top, ?_, ?_, fun e => ?_, fun v => ?_⟩
    · rw [Walk.support_mapLe_eq_support]; exact P.isPath.support_nodup
    · rw [Walk.length_mapLe]; exact P.pos
    · rw [Walk.edges_mapLe_eq_edges]; rfl
    · rw [Walk.support_mapLe_eq_support]
  · refine ⟨(P.walk.mapLe le_top).reverse, ?_, ?_, fun e => ?_, fun v => ?_⟩
    · rw [Walk.support_reverse, Walk.support_mapLe_eq_support, List.nodup_reverse]
      exact P.isPath.support_nodup
    · rw [Walk.length_reverse, Walk.length_mapLe]; exact P.pos
    · rw [Walk.edges_reverse, List.mem_reverse, Walk.edges_mapLe_eq_edges]; rfl
    · rw [Walk.support_reverse, List.mem_reverse, Walk.support_mapLe_eq_support]

end orient

/-! ### Reassembly through `r` -/

section reassemble

variable {W : Type u} [Fintype W] [DecidableEq W] {B : SimpleGraph W} [DecidableRel B.Adj]
  {r : W}

omit [Fintype W] [DecidableRel B.Adj] in
/-- One path of `starDel B r`, oriented from `lo` to `hi`, closed through `r` at `hi`, and
continued to `lo j` when `σ` matches it to `j`. -/
theorem exists_closed_path (P : GPath (starDel B r)) {lo hi : W}
    (hends : (lo = P.src ∧ hi = P.tgt) ∨ (lo = P.tgt ∧ hi = P.src))
    (hlo : B.Adj r lo) (hhi : B.Adj r hi) (c : Option W)
    (hc : ∀ y, c = some y → B.Adj r y ∧ y ∉ P.walk.support) :
    ∃ R : TPath W,
      (∀ e, e ∈ R.edges ↔ e ∈ P.edges ∨ e = s(r, hi) ∨ ∃ y, c = some y ∧ e = s(r, y)) ∧
      R.endsAt r = (if c = none then 1 else 0) := by
  obtain ⟨p, hpn, hpl, hpe, hps⟩ := P.exists_oriented hends
  have hr : r ∉ p.support := by rw [hps]; exact P.root_notMem_starDel
  have hhir : hi ≠ r := hhi.ne'
  have hlor : lo ≠ r := hlo.ne'
  cases c with
  | none =>
    let q : (⊤ : SimpleGraph W).Walk hi r := Walk.cons (top_adj hi r |>.mpr hhir) Walk.nil
    have hqn : q.support.Nodup := by simp [q, hhir]
    have hd : ∀ v ∈ p.support, v ∈ q.support → v = hi := by
      intro v hv hvq
      simp only [q, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hvq
      rcases hvq with h | h
      · exact h
      · exact absurd (h ▸ hv) hr
    refine ⟨joinT p q hpn hqn hd (by omega), fun e => ?_, ?_⟩
    · rw [joinT_edges, List.mem_append, hpe]
      simp only [q, Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.not_mem_nil, or_false,
        reduceCtorEq, false_and, exists_false]
      rw [Sym2.eq_swap (a := r)]
    · unfold GPath.endsAt
      simp [hlor]
  | some y =>
    obtain ⟨hy, hyP⟩ := hc y rfl
    have hyp : y ∉ p.support := by rw [hps]; exact hyP
    have hyr : r ≠ y := hy.ne
    have hiy : hi ≠ y := fun h => hyp (h ▸ p.end_mem_support)
    let q : (⊤ : SimpleGraph W).Walk hi y :=
      Walk.cons (top_adj hi r |>.mpr hhir) (Walk.cons (top_adj r y |>.mpr hyr) Walk.nil)
    have hqn : q.support.Nodup := by simp [q, hhir, hiy, hyr]
    have hd : ∀ v ∈ p.support, v ∈ q.support → v = hi := by
      intro v hv hvq
      simp only [q, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hvq
      rcases hvq with h | h | h
      · exact h
      · exact absurd (h ▸ hv) hr
      · exact absurd (h ▸ hv) hyp
    refine ⟨joinT p q hpn hqn hd (by omega), fun e => ?_, ?_⟩
    · rw [joinT_edges, List.mem_append, hpe]
      simp only [q, Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.not_mem_nil, or_false,
        Option.some.injEq, exists_eq_left']
      rw [Sym2.eq_swap (a := r) (b := hi)]
    · unfold GPath.endsAt
      simp [hlor, hyr.symm]

/-- **Reassembly.** A decomposition of `starDel B r` whose ends pair up `N(r)`, with each path
oriented from `lo i` to `hi i` and a partial injection `σ` from paths to trivial ends
(`lo (σ i) ∉ P_i`) leaving one or two paths unmatched, gives a decomposition of `B` with one
more path and exactly two ends at `r`: `lo i ⋯ hi i r lo (σ i)` for matched paths,
`lo i ⋯ hi i r` for unmatched ones, and the one or two unmatched trivial ends joined through `r`. -/
theorem reassemble (D : PathDecomp (starDel B r)) (lo hi : Fin D.paths.length → W)
    (hends : ∀ i, (lo i = (D.paths.get i).src ∧ hi i = (D.paths.get i).tgt) ∨
      (lo i = (D.paths.get i).tgt ∧ hi i = (D.paths.get i).src))
    (hadjlo : ∀ i, B.Adj r (lo i)) (hadjhi : ∀ i, B.Adj r (hi i))
    (hcov : ∀ x, B.Adj r x → (∃ i, lo i = x) ∨ ∃ i, hi i = x)
    (hlo : Function.Injective lo) (hhi : Function.Injective hi) (hlh : ∀ i j, lo i ≠ hi j)
    (σ : Fin D.paths.length → Option (Fin D.paths.length))
    (hσ : ∀ i i' j, σ i = some j → σ i' = some j → i = i')
    (hav : ∀ i j, σ i = some j → lo j ∉ (D.paths.get i).walk.support)
    (hU : 1 ≤ #(univ.filter (fun i => σ i = none)) ∧ #(univ.filter (fun i => σ i = none)) ≤ 2) :
    ∃ D' : PathDecomp B, D'.size = D.size + 1 ∧ D'.ends r = 2 := by
  set P := D.paths.get with hP
  -- the closed paths
  have hR : ∀ i, ∃ R : TPath W,
      (∀ e, e ∈ R.edges ↔ e ∈ (P i).edges ∨ e = s(r, hi i) ∨
        ∃ y, (σ i).map lo = some y ∧ e = s(r, y)) ∧
      R.endsAt r = (if (σ i).map lo = none then 1 else 0) := by
    intro i
    refine exists_closed_path (P i) (hends i) (hadjlo i) (hadjhi i) ((σ i).map lo) ?_
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hy
    exact ⟨hadjlo j, hav i j hj⟩
  choose R hRe hRr using hR
  have hRe' : ∀ i e, e ∈ (R i).edges ↔ e ∈ (P i).edges ∨ e = s(r, hi i) ∨
      ∃ j, σ i = some j ∧ e = s(r, lo j) := by
    intro i e
    rw [hRe i e]
    constructor
    · rintro (h | h | ⟨y, hy, rfl⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hy
        exact Or.inr (Or.inr ⟨j, hj, rfl⟩)
    · rintro (h | h | ⟨j, hj, rfl⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨lo j, by rw [hj]; rfl, rfl⟩)
  have hRr' : ∀ i, (R i).endsAt r = if σ i = none then 1 else 0 := by
    intro i
    rw [hRr i]
    cases σ i <;> simp
  -- the unmatched trivial ends
  set U := univ.filter (fun i => σ i = none) with hUdef
  set J0 := univ.filter (fun j => ∀ i, σ i ≠ some j) with hJ0def
  have hJ0card : #J0 = #U := by
    set Mt := univ.filter (fun i => ¬ σ i = none) with hMt
    set Img := univ.filter (fun j => ∃ i, σ i = some j) with hImg
    have h1 : #U + #Mt = D.paths.length := by
      rw [hUdef, hMt, card_filter_add_card_filter_not, card_univ, Fintype.card_fin]
    have h2 : #Img + #J0 = D.paths.length := by
      have : J0 = univ.filter (fun j => ¬ ∃ i, σ i = some j) := by
        rw [hJ0def]; congr 1; ext j; push Not; rfl
      rw [this, hImg, card_filter_add_card_filter_not, card_univ, Fintype.card_fin]
    have h3 : #Img = #Mt := by
      have : Img = Mt.image (fun i => (σ i).getD i) := by
        ext j
        simp only [hImg, hMt, mem_filter, mem_univ, true_and, mem_image]
        constructor
        · rintro ⟨i, hi⟩
          exact ⟨i, by rw [hi]; simp, by rw [hi]; rfl⟩
        · rintro ⟨i, hi, rfl⟩
          obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hi
          exact ⟨i, by rw [hj]; rfl⟩
      rw [this, card_image_of_injOn]
      intro i hi i' hi' h
      simp only [hMt, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hi hi'
      obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hi
      obtain ⟨j', hj'⟩ := Option.ne_none_iff_exists'.mp hi'
      simp only [hj, hj', Option.getD_some] at h
      subst h
      exact hσ i i' j hj hj'
    omega
  have hmemJ0 : ∀ j, j ∈ J0 ↔ ∀ i, σ i ≠ some j := by
    intro j; simp [hJ0def]
  -- the extra path through the unmatched trivial ends
  have hL0 : ∃ L0 : List (TPath W), L0.length = 1 ∧
      (∀ e, e ∈ L0.flatMap GPath.edges ↔ ∃ j ∈ J0, e = s(r, lo j)) ∧
      (L0.flatMap GPath.edges).Nodup ∧ endsL L0 r + #U = 2 := by
    have hlor : ∀ j, lo j ≠ r := fun j => (hadjlo j).ne'
    rcases hU with ⟨hU1, hU2⟩
    rcases (show #U = 1 ∨ #U = 2 by omega) with h1 | h2
    · obtain ⟨j, hj⟩ := card_eq_one.mp (hJ0card.trans h1)
      refine ⟨[GPath.ofAdj (G := ⊤) (top_adj r (lo j) |>.mpr (hlor j).symm)], rfl,
        fun e => ?_, ?_, ?_⟩
      · simp [hj]
      · simp
      · simp [endsL, GPath.endsAt, GPath.ofAdj, h1, hlor j]
    · obtain ⟨j₁, j₂, hj12, hj⟩ := card_eq_two.mp (hJ0card.trans h2)
      have hl12 : lo j₁ ≠ lo j₂ := fun h => hj12 (hlo h)
      let w : (⊤ : SimpleGraph W).Walk (lo j₁) (lo j₂) :=
        Walk.cons (top_adj (lo j₁) r |>.mpr (hlor j₁))
          (Walk.cons (top_adj r (lo j₂) |>.mpr (hlor j₂).symm) Walk.nil)
      have hwp : w.IsPath := by
        rw [Walk.isPath_def]
        simp [w, hl12, hlor j₁, (hlor j₂).symm]
      refine ⟨[⟨lo j₁, lo j₂, w, hwp, by simp [w]⟩], rfl, fun e => ?_, ?_, ?_⟩
      · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, GPath.edges, w,
          Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.not_mem_nil, or_false, hj,
          mem_insert, mem_singleton]
        constructor
        · rintro (rfl | rfl)
          · exact ⟨j₁, Or.inl rfl, Sym2.eq_swap⟩
          · exact ⟨j₂, Or.inr rfl, rfl⟩
        · rintro ⟨j, (rfl | rfl), rfl⟩
          · exact Or.inl Sym2.eq_swap
          · exact Or.inr rfl
      · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, GPath.edges, w,
          Walk.edges_cons, Walk.edges_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
          or_false, not_false_eq_true, List.nodup_nil, and_true]
        intro h
        rw [Sym2.eq_swap, Sym2.congr_right] at h
        exact hl12 h
      · simp [endsL, GPath.endsAt, h2, hlor j₁, hlor j₂]
  obtain ⟨L0, hL0len, hL0e, hL0nd, hL0r⟩ := hL0
  -- facts about the edges
  have hstarE : ∀ {e : Sym2 W} {i}, e ∈ (P i).edges → r ∉ e :=
    fun he => GPath.root_notMem_edge_starDel _ he
  have hsym : ∀ {x y : W}, s(r, x) = s(r, y) → x = y := fun h => Sym2.congr_right.mp h
  have hDdisj : ∀ i i', i ≠ i' → ∀ e, e ∈ (P i).edges → e ∉ (P i').edges := by
    have hpw := (List.nodup_flatMap.mp D.nodup_edges).2
    rw [List.pairwise_iff_get] at hpw
    intro i i' hii' e he he'
    rcases lt_or_gt_of_ne hii' with h | h
    · exact hpw i i' h he he'
    · exact hpw i' i h he' he
  set L := List.ofFn R ++ L0 with hL
  have hLnd : (L.flatMap GPath.edges).Nodup := by
    rw [hL, List.flatMap_append, List.nodup_append]
    refine ⟨?_, hL0nd, ?_⟩
    · rw [List.nodup_flatMap]
      refine ⟨fun Q _ => GPath.edges_nodup' Q, ?_⟩
      rw [List.pairwise_ofFn]
      intro i i' hii' e he he'
      have hne : i ≠ i' := ne_of_lt hii'
      rcases (hRe' i e).mp he with h | h | ⟨j, hj, h⟩ <;>
        rcases (hRe' i' e).mp he' with h' | h' | ⟨j', hj', h'⟩
      · exact hDdisj i i' hne e h h'
      · exact hstarE h (h' ▸ Sym2.mem_mk_left _ _)
      · exact hstarE h (h' ▸ Sym2.mem_mk_left _ _)
      · exact hstarE h' (h ▸ Sym2.mem_mk_left _ _)
      · exact hne (hhi (hsym (h.symm.trans h')))
      · exact hlh j' i (hsym (h.symm.trans h')).symm
      · exact hstarE h' (h ▸ Sym2.mem_mk_left _ _)
      · exact hlh j i' (hsym (h.symm.trans h'))
      · have := hlo (hsym (h.symm.trans h'))
        subst this
        exact hne (hσ i i' j hj hj')
    · intro e he e' he' hee'
      subst hee'
      rw [List.mem_flatMap] at he
      obtain ⟨Q, hQ, heQ⟩ := he
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hQ
      obtain ⟨j, hjJ, rfl⟩ := (hL0e _).mp he'
      rcases (hRe' i _).mp heQ with h | h | ⟨j', hj', h'⟩
      · exact hstarE h (Sym2.mem_mk_left _ _)
      · exact hlh j i (hsym h)
      · have := hlo (hsym h')
        subst this
        exact (hmemJ0 j).mp hjJ i hj'
  have hLmem : ∀ e, e ∈ B.edgeSet ↔ e ∈ L.flatMap GPath.edges := by
    intro e
    rw [hL, List.flatMap_append, List.mem_append, List.mem_flatMap]
    constructor
    · intro heB
      by_cases hre : r ∈ e
      · obtain ⟨x, rfl⟩ := (Sym2.mem_iff_exists.mp hre)
        have hx : B.Adj r x := heB
        rcases hcov x hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
        · by_cases hm' : ∃ i', σ i' = some i
          · obtain ⟨i', hi'⟩ := hm'
            exact Or.inl ⟨R i', List.mem_ofFn.mpr ⟨i', rfl⟩, (hRe' i' _).mpr (Or.inr (Or.inr ⟨i, hi', rfl⟩))⟩
          · push Not at hm'
            exact Or.inr ((hL0e _).mpr ⟨i, (hmemJ0 i).mpr hm', rfl⟩)
        · exact Or.inl ⟨R i, List.mem_ofFn.mpr ⟨i, rfl⟩, (hRe' i _).mpr (Or.inr (Or.inl rfl))⟩
      · have heG : e ∈ (starDel B r).edgeSet := mem_starDel_edgeSet.mpr ⟨heB, hre⟩
        rw [D.covers e, List.mem_flatMap] at heG
        obtain ⟨Q, hQ, heQ⟩ := heG
        obtain ⟨i, rfl⟩ := List.get_of_mem hQ
        exact Or.inl ⟨R i, List.mem_ofFn.mpr ⟨i, rfl⟩, (hRe' i e).mpr (Or.inl heQ)⟩
    · rintro (⟨Q, hQ, heQ⟩ | he)
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hQ
        rcases (hRe' i e).mp heQ with h | rfl | ⟨j, -, rfl⟩
        · exact (mem_starDel_edgeSet.mp ((P i).walk.edges_subset_edgeSet h)).1
        · exact hadjhi i
        · exact hadjlo j
      · obtain ⟨j, -, rfl⟩ := (hL0e e).mp he
        exact hadjlo j
  have hLE : edgesM L = B.edgeFinset.val := by
    refine (Multiset.Nodup.ext (Multiset.coe_nodup.mpr hLnd) B.edgeFinset.nodup).mpr ?_
    intro e
    rw [Multiset.mem_coe, ← hLmem e, Finset.mem_val, mem_edgeFinset]
  obtain ⟨D', hD'size, hD'ends⟩ := exists_decomp_of_edgesM L hLE
  refine ⟨D', ?_, ?_⟩
  · rw [hD'size, hL, List.length_append, List.length_ofFn, hL0len]
    rfl
  · rw [hD'ends r, hL, endsL_append]
    have : endsL (List.ofFn R) r = #U := by
      rw [endsL, List.map_ofFn, List.sum_ofFn, hUdef, card_filter]
      exact sum_congr rfl (fun i _ => hRr' i)
    omega

end reassemble

/-! ### The theorem -/

section main

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- The neighbours of `r` of degree at least `2t`. -/
def heavyNbrs (B : SimpleGraph W) [DecidableRel B.Adj] (r : W) (t : ℕ) : Finset W :=
  (B.neighborFinset r).filter (fun x => 2 * t ≤ B.degree x)

/-- **Theorem 3.1** (the Lovász-plus-matching method). Let `B` have order `2k`, every degree
even, and `d(r) = 2k − 2`. Suppose that for every `3 ≤ t ≤ k − 1`, with `h_t` the number of
neighbours of `r` of degree at least `2t`, `⌊h_t/2⌋ + t ≤ k + 1` or `⌊h_{t+1}/2⌋ + 2t ≤ k + 1`.
Then `B` has a decomposition into exactly `k` paths with exactly two ends at `r`. -/
theorem exists_decomp_of_degStar (B : SimpleGraph W) [DecidableRel B.Adj]
    (hB : ∀ a, Even (B.degree a)) {k : ℕ} (hk : 2 ≤ k) (hW : Fintype.card W = 2 * k) (r : W)
    (hr : B.degree r + 2 = 2 * k)
    (hstar : ∀ t, 3 ≤ t → t ≤ k - 1 →
      #(heavyNbrs B r t) / 2 + t ≤ k + 1 ∨ #(heavyNbrs B r (t + 1)) / 2 + 2 * t ≤ k + 1) :
    ∃ D : PathDecomp B, D.size = k ∧ D.ends r = 2 := by
  have hadj_ne : ∀ {x}, B.Adj r x → x ≠ r := fun h => h.ne'
  -- parity in `G`
  have hodd : ∀ x, B.Adj r x → (starDel B r).degree x % 2 = 1 := by
    intro x hx
    have h1 := starDel_degree_of_adj (B := B) hx
    obtain ⟨c, hc⟩ := hB x
    omega
  have heven : ∀ x, ¬ B.Adj r x → (starDel B r).degree x % 2 = 0 := by
    intro x hx
    by_cases hxr : x = r
    · rw [hxr, starDel_degree_self]
    · rw [starDel_degree_of_not_adj hxr hx]
      obtain ⟨c, hc⟩ := hB x
      omega
  -- at most one even vertex of positive degree
  have hev : (evenSet (starDel B r)).card ≤ 1 := by
    have hsub : evenSet (starDel B r) ⊆ univ \ insert r (B.neighborFinset r) := by
      intro v hv
      rw [evenSet, mem_filter] at hv
      rw [mem_sdiff, mem_insert, mem_neighborFinset]
      refine ⟨mem_univ _, ?_⟩
      rintro (rfl | h)
      · rw [starDel_degree_self] at hv; exact lt_irrefl _ hv.2.1
      · have := hodd v h
        obtain ⟨c, hc⟩ := hv.2.2
        omega
    have hc : #(univ \ insert r (B.neighborFinset r)) = 1 := by
      rw [card_sdiff_of_subset (subset_univ _), card_univ, hW, card_insert_of_notMem
        (by rw [mem_neighborFinset]; exact B.loopless.irrefl r), card_neighborFinset_eq_degree]
      omega
    exact (card_le_card hsub).trans hc.le
  obtain ⟨D, hD⟩ := lovasz_ends (starDel B r) hev
  have hDx : ∀ x, D.ends x = if B.Adj r x then 1 else 0 := by
    intro x
    rw [hD x]
    split_ifs with h
    · exact hodd x h
    · exact heven x h
  -- the number of paths
  have hsize : D.size + 1 = k := by
    have h1 := D.sum_ends
    have h2 : ∑ v, D.ends v = B.degree r := by
      simp_rw [hDx]
      rw [sum_boole, ← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
      simp
    rw [h2] at h1
    omega
  set m := D.paths.length with hm
  have hmk : m + 1 = k := hsize
  set P := D.paths.get with hP
  -- ends of the paths are neighbours of `r`, each the end of exactly one path
  have hend_adj : ∀ i x, 1 ≤ (P i).endsAt x → B.Adj r x := by
    intro i x hx
    have := (D.endsAt_le_ends x i).trans_eq' rfl
    have h := hx.trans (D.endsAt_le_ends x i)
    rw [hDx x] at h
    by_contra hn
    rw [ite_eq_right hn] at h
    omega
  have hend_uniq : ∀ i j x, 1 ≤ (P i).endsAt x → 1 ≤ (P j).endsAt x → i = j := by
    intro i j x hi hj
    by_contra hij
    have h := D.two_le_ends_of_ne hij hi hj
    rw [hDx x] at h
    split_ifs at h <;> omega
  -- the orientation: the trivial end `lo` is the end of smaller degree
  let lo : Fin m → W := fun i =>
    if B.degree (P i).src ≤ B.degree (P i).tgt then (P i).src else (P i).tgt
  let hi : Fin m → W := fun i =>
    if B.degree (P i).src ≤ B.degree (P i).tgt then (P i).tgt else (P i).src
  have hends : ∀ i, (lo i = (P i).src ∧ hi i = (P i).tgt) ∨
      (lo i = (P i).tgt ∧ hi i = (P i).src) := by
    intro i
    by_cases h : B.degree (P i).src ≤ B.degree (P i).tgt
    · exact Or.inl ⟨ite_eq_left h, ite_eq_left h⟩
    · exact Or.inr ⟨ite_eq_right h, ite_eq_right h⟩
  have hlohi : ∀ i, B.degree (lo i) ≤ B.degree (hi i) := by
    intro i
    by_cases h : B.degree (P i).src ≤ B.degree (P i).tgt
    · have e1 : lo i = (P i).src := ite_eq_left h
      have e2 : hi i = (P i).tgt := ite_eq_left h
      rw [e1, e2]; exact h
    · have e1 : lo i = (P i).tgt := ite_eq_right h
      have e2 : hi i = (P i).src := ite_eq_right h
      rw [e1, e2]; omega
  have hlo_end : ∀ i, 1 ≤ (P i).endsAt (lo i) := by
    intro i
    rcases hends i with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    · exact (P i).endsAt_src
    · exact (P i).endsAt_tgt
  have hhi_end : ∀ i, 1 ≤ (P i).endsAt (hi i) := by
    intro i
    rcases hends i with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
    · exact (P i).endsAt_tgt
    · exact (P i).endsAt_src
  have hlo_ne_hi : ∀ i, lo i ≠ hi i := by
    intro i
    have := (P i).src_ne_tgt
    rcases hends i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact this
    · exact this.symm
  have hlo_inj : Function.Injective lo := fun i j h =>
    hend_uniq i j (lo i) (hlo_end i) (h ▸ hlo_end j)
  have hhi_inj : Function.Injective hi := fun i j h =>
    hend_uniq i j (hi i) (hhi_end i) (h ▸ hhi_end j)
  have hlh : ∀ i j, lo i ≠ hi j := by
    intro i j h
    have := hend_uniq i j (lo i) (hlo_end i) (h ▸ hhi_end j)
    subst this
    exact hlo_ne_hi i h
  have hadjlo : ∀ i, B.Adj r (lo i) := fun i => hend_adj i _ (hlo_end i)
  have hadjhi : ∀ i, B.Adj r (hi i) := fun i => hend_adj i _ (hhi_end i)
  have hcov : ∀ x, B.Adj r x → (∃ i, lo i = x) ∨ ∃ i, hi i = x := by
    intro x hx
    have h1 : D.ends x = 1 := by rw [hDx x, ite_eq_left hx]
    rw [D.ends_eq_sum_get] at h1
    obtain ⟨i, -, hi'⟩ := exists_ne_zero_of_sum_ne_zero (h1.trans_ne one_ne_zero)
    have hpos : 1 ≤ (P i).endsAt x := Nat.one_le_iff_ne_zero.mpr hi'
    have hx' : (P i).src = x ∨ (P i).tgt = x := by
      unfold GPath.endsAt at hpos
      by_contra hn
      push Not at hn
      simp [hn.1, hn.2] at hpos
    rcases hends i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hx' with hx' | hx'
    · exact Or.inl ⟨i, h1.trans hx'⟩
    · exact Or.inr ⟨i, h2.trans hx'⟩
    · exact Or.inr ⟨i, h2.trans hx'⟩
    · exact Or.inl ⟨i, h1.trans hx'⟩
  -- every neighbour `x` of `r` lies on exactly `d(x)/2` paths
  have hcount : ∀ x, B.Adj r x →
      2 * #(univ.filter (fun i => x ∈ (P i).walk.support)) = B.degree x := by
    intro x hx
    have h := D.degree_add_ends_eq_card x
    rw [hDx x, ite_eq_left hx] at h
    have h2 := starDel_degree_of_adj (B := B) hx
    rw [← h]
    exact h2.symm ▸ rfl
  have hcount' : ∀ x, B.Adj r x → ∀ S' : Finset (Fin m),
      (∀ i ∈ S', x ∈ (P i).walk.support) → 2 * #S' ≤ B.degree x := by
    intro x hx S' hS'
    rw [← hcount x hx]
    exact Nat.mul_le_mul_left 2 (card_le_card (fun i hi => mem_filter.mpr ⟨mem_univ _, hS' i hi⟩))
  -- heavy trivial ends come in disjoint pairs inside `heavyNbrs`
  have hpairs : ∀ u, 2 * #(univ.filter (fun j => 2 * u ≤ B.degree (lo j))) ≤
      #(heavyNbrs B r u) := by
    intro u
    set X := univ.filter (fun j => 2 * u ≤ B.degree (lo j)) with hX
    have hsub : X.image lo ∪ X.image hi ⊆ heavyNbrs B r u := by
      intro x hx
      rw [mem_union, mem_image, mem_image] at hx
      rw [heavyNbrs, mem_filter, mem_neighborFinset]
      rcases hx with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ <;> rw [hX, mem_filter] at hj
      · exact ⟨hadjlo j, hj.2⟩
      · exact ⟨hadjhi j, hj.2.trans (hlohi j)⟩
    have hdisj : Disjoint (X.image lo) (X.image hi) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [mem_image] at hx hx'
      obtain ⟨j, -, rfl⟩ := hx
      obtain ⟨j', -, h⟩ := hx'
      exact hlh j j' h.symm
    have := card_le_card hsub
    rw [card_union_of_disjoint hdisj, card_image_of_injective _ hlo_inj,
      card_image_of_injective _ hhi_inj] at this
    omega
  -- Hall's condition with two wildcards
  let T : Fin m → Finset (Fin m ⊕ Fin 2) := fun i =>
    (univ.filter (fun j => lo j ∉ (P i).walk.support)).map Function.Embedding.inl ∪
      univ.map Function.Embedding.inr
  have hall : ∀ S : Finset (Fin m), #S ≤ #(S.biUnion T) := by
    intro S
    rcases S.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩
    · simp
    set J := univ.filter (fun j => ∀ i ∈ S, lo j ∈ (P i).walk.support) with hJ
    have hsub : (univ.filter (fun j => ¬ ∀ i ∈ S, lo j ∈ (P i).walk.support)).map
        Function.Embedding.inl ∪ univ.map Function.Embedding.inr ⊆ S.biUnion T := by
      intro a ha
      rw [mem_union] at ha
      rw [mem_biUnion]
      rcases ha with ha | ha
      · rw [mem_map] at ha
        obtain ⟨j, hj, rfl⟩ := ha
        rw [mem_filter] at hj
        push Not at hj
        obtain ⟨i, hiS, hij⟩ := hj.2
        refine ⟨i, hiS, ?_⟩
        rw [mem_union, mem_map]
        exact Or.inl ⟨j, by rw [mem_filter]; exact ⟨mem_univ _, hij⟩, rfl⟩
      · exact ⟨i0, hi0, mem_union.mpr (Or.inr ha)⟩
    have hdisj : Disjoint ((univ.filter (fun j => ¬ ∀ i ∈ S, lo j ∈ (P i).walk.support)).map
        Function.Embedding.inl) (univ.map (Function.Embedding.inr : Fin 2 ↪ Fin m ⊕ Fin 2)) := by
      rw [Finset.disjoint_left]
      intro a ha ha'
      rw [mem_map] at ha ha'
      obtain ⟨j, -, rfl⟩ := ha
      obtain ⟨l, -, h⟩ := ha'
      exact Sum.inr_ne_inl h
    have h1 := card_le_card hsub
    rw [card_union_of_disjoint hdisj, card_map, card_map, card_univ, Fintype.card_fin] at h1
    have h2 : #J + #(univ.filter (fun j => ¬ ∀ i ∈ S, lo j ∈ (P i).walk.support)) = m := by
      rw [hJ, card_filter_add_card_filter_not, card_univ, Fintype.card_fin]
    have hSm : #S ≤ m := by
      have := card_le_univ S
      rwa [Fintype.card_fin] at this
    -- the key bound `#S + #J ≤ m + 2`
    suffices hkey : #S + #J ≤ m + 2 by omega
    by_cases hS2 : #S ≤ 2
    · have : #J ≤ m := by
        have := card_le_univ J
        rwa [Fintype.card_fin] at this
      omega
    push Not at hS2
    set t := #S with ht
    -- a trivial end on all paths of `S` lies on `t` paths, and on `t + 1` if its own path is
    -- not in `S`
    have hdeg_S : ∀ j ∈ J, 2 * t ≤ B.degree (lo j) := by
      intro j hj
      rw [hJ, mem_filter] at hj
      exact hcount' _ (hadjlo j) S hj.2
    have hdeg_out : ∀ j ∈ J, j ∉ S → 2 * (t + 1) ≤ B.degree (lo j) := by
      intro j hj hjS
      rw [hJ, mem_filter] at hj
      have hown : lo j ∈ (P j).walk.support := by
        rcases hends j with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
        · exact (P j).walk.start_mem_support
        · exact (P j).walk.end_mem_support
      have := hcount' _ (hadjlo j) (insert j S) (by
        intro i hi
        rw [mem_insert] at hi
        rcases hi with rfl | hi
        · exact hown
        · exact hj.2 i hi)
      rw [card_insert_of_notMem hjS] at this
      omega
    have htk : t ≤ k - 1 := by omega
    rcases hstar t (by omega) htk with hA | hB'
    · have hJX : J ⊆ univ.filter (fun j => 2 * t ≤ B.degree (lo j)) := by
        intro j hj
        rw [mem_filter]
        exact ⟨mem_univ _, hdeg_S j hj⟩
      have := card_le_card hJX
      have := hpairs t
      have : #(univ.filter (fun j => 2 * t ≤ B.degree (lo j))) ≤ #(heavyNbrs B r t) / 2 := by
        rw [Nat.le_div_iff_mul_le two_pos]; omega
      omega
    · have hJX : J ⊆ S ∪ univ.filter (fun j => 2 * (t + 1) ≤ B.degree (lo j)) := by
        intro j hj
        rw [mem_union, mem_filter]
        by_cases hjS : j ∈ S
        · exact Or.inl hjS
        · exact Or.inr ⟨mem_univ _, hdeg_out j hj hjS⟩
      have h3 := (card_le_card hJX).trans (card_union_le _ _)
      have := hpairs (t + 1)
      have : #(univ.filter (fun j => 2 * (t + 1) ≤ B.degree (lo j))) ≤
          #(heavyNbrs B r (t + 1)) / 2 := by
        rw [Nat.le_div_iff_mul_le two_pos]; omega
      omega
  obtain ⟨f, hfinj, hfT⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective T).mp hall
  -- the partial matching
  let σ0 : Fin m → Option (Fin m) := fun i => Sum.elim some (fun _ => none) (f i)
  have hσ0 : ∀ i j, σ0 i = some j ↔ f i = Sum.inl j := by
    intro i j
    simp only [σ0]
    cases f i <;> simp
  have hσ0inj : ∀ i i' j, σ0 i = some j → σ0 i' = some j → i = i' := by
    intro i i' j h h'
    rw [hσ0] at h h'
    exact hfinj (h.trans h'.symm)
  have hσ0av : ∀ i j, σ0 i = some j → lo j ∉ (P i).walk.support := by
    intro i j h
    rw [hσ0] at h
    have := hfT i
    rw [h, mem_union, mem_map, mem_map] at this
    rcases this with ⟨j', hj', hjj'⟩ | ⟨l, -, hl⟩
    · cases hjj'
      rw [mem_filter] at hj'
      exact hj'.2
    · exact absurd hl Sum.inr_ne_inl
  have hσ0U : #(univ.filter (fun i => σ0 i = none)) ≤ 2 := by
    have hnone : ∀ i, σ0 i = none ↔ ∃ l, f i = Sum.inr l := by
      intro i
      simp only [σ0]
      cases f i <;> simp
    have hmaps : ∀ i ∈ univ.filter (fun i => σ0 i = none), f i ∈ univ.map
        (Function.Embedding.inr : Fin 2 ↪ Fin m ⊕ Fin 2) := by
      intro i hi
      rw [mem_filter, hnone] at hi
      obtain ⟨l, hl⟩ := hi.2
      rw [hl, mem_map]
      exact ⟨l, mem_univ _, rfl⟩
    have := card_le_card_of_injOn f hmaps (fun a _ b _ h => hfinj h)
    rwa [card_map, card_univ, Fintype.card_fin] at this
  -- leave at least one path unmatched
  have hm1 : 0 < m := by omega
  obtain ⟨σ, hσinj, hσav, hσU⟩ : ∃ σ : Fin m → Option (Fin m),
      (∀ i i' j, σ i = some j → σ i' = some j → i = i') ∧
      (∀ i j, σ i = some j → lo j ∉ (P i).walk.support) ∧
      1 ≤ #(univ.filter (fun i => σ i = none)) ∧ #(univ.filter (fun i => σ i = none)) ≤ 2 := by
    by_cases h0 : 1 ≤ #(univ.filter (fun i => σ0 i = none))
    · exact ⟨σ0, hσ0inj, hσ0av, h0, hσ0U⟩
    · push Not at h0
      have hall0 : ∀ i, σ0 i ≠ none := by
        intro i hi
        have : i ∈ univ.filter (fun i => σ0 i = none) := by rw [mem_filter]; exact ⟨mem_univ _, hi⟩
        rw [Nat.lt_one_iff, card_eq_zero] at h0
        rw [h0] at this
        exact notMem_empty _ this
      let i0 : Fin m := ⟨0, hm1⟩
      refine ⟨Function.update σ0 i0 none, ?_, ?_, ?_⟩
      · intro i i' j h h'
        by_cases hi : i = i0
        · subst hi; simp at h
        by_cases hi' : i' = i0
        · subst hi'; simp at h'
        rw [Function.update_of_ne hi] at h
        rw [Function.update_of_ne hi'] at h'
        exact hσ0inj i i' j h h'
      · intro i j h
        by_cases hi : i = i0
        · subst hi; simp at h
        rw [Function.update_of_ne hi] at h
        exact hσ0av i j h
      · have : univ.filter (fun i => Function.update σ0 i0 none i = none) = {i0} := by
          ext i
          rw [mem_filter, mem_singleton]
          constructor
          · rintro ⟨-, h⟩
            by_contra hi
            rw [Function.update_of_ne hi] at h
            exact hall0 i h
          · rintro rfl
            simp
        rw [this, card_singleton]
        omega
  obtain ⟨D', hD'size, hD'ends⟩ := reassemble D lo hi hends hadjlo hadjhi hcov hlo_inj hhi_inj hlh
    σ hσinj hσav hσU
  exact ⟨D', by rw [hD'size]; exact hsize, hD'ends⟩

/-- **Theorem 3.1**, rooted form: `RootedDecomp B r`. -/
theorem rootedDecomp_of_degStar (B : SimpleGraph W) [DecidableRel B.Adj]
    (hB : ∀ a, Even (B.degree a)) {k : ℕ} (hk : 2 ≤ k) (hW : Fintype.card W = 2 * k) (r : W)
    (hr : B.degree r + 2 = 2 * k)
    (hstar : ∀ t, 3 ≤ t → t ≤ k - 1 →
      #(heavyNbrs B r t) / 2 + t ≤ k + 1 ∨ #(heavyNbrs B r (t + 1)) / 2 + 2 * t ≤ k + 1) :
    RootedDecomp B r := by
  obtain ⟨D, hD, hDr⟩ := exists_decomp_of_degStar B hB hk hW r hr hstar
  exact ⟨D, by rw [hD, hW]; omega, hDr.ge⟩

omit [DecidableEq W] in
theorem heavyNbrs_antitone (B : SimpleGraph W) [DecidableRel B.Adj] (r : W) {t t' : ℕ}
    (h : t ≤ t') : heavyNbrs B r t' ⊆ heavyNbrs B r t := by
  intro x hx
  rw [heavyNbrs, mem_filter] at hx ⊢
  exact ⟨hx.1, le_trans (by omega) hx.2⟩

/-- **Corollary 3.3(a).** If at most five neighbours of `r` have degree at least `6`, RE holds
at `r`. -/
theorem rootedDecomp_of_few_heavy (B : SimpleGraph W) [DecidableRel B.Adj]
    (hB : ∀ a, Even (B.degree a)) {k : ℕ} (hk : 2 ≤ k) (hW : Fintype.card W = 2 * k) (r : W)
    (hr : B.degree r + 2 = 2 * k) (h5 : #(heavyNbrs B r 3) ≤ 5) :
    RootedDecomp B r := by
  refine rootedDecomp_of_degStar B hB hk hW r hr (fun t ht3 htk => Or.inl ?_)
  have := card_le_card (heavyNbrs_antitone B r ht3)
  have : #(heavyNbrs B r t) / 2 ≤ 2 := by omega
  omega

/-- **Corollary 3.3(b).** If `|B| ≥ 10` and every neighbour of `r` has degree at most `6`, RE
holds at `r`. -/
theorem rootedDecomp_of_deg_le_six (B : SimpleGraph W) [DecidableRel B.Adj]
    (hB : ∀ a, Even (B.degree a)) {k : ℕ} (hk : 5 ≤ k) (hW : Fintype.card W = 2 * k) (r : W)
    (hr : B.degree r + 2 = 2 * k) (h6 : ∀ x, B.Adj r x → B.degree x ≤ 6) :
    RootedDecomp B r := by
  have h4 : ∀ t, 4 ≤ t → heavyNbrs B r t = ∅ := by
    intro t ht
    rw [eq_empty_iff_forall_notMem]
    intro x hx
    rw [heavyNbrs, mem_filter, mem_neighborFinset] at hx
    have := h6 x hx.1
    omega
  refine rootedDecomp_of_degStar B hB (by omega) hW r hr (fun t ht3 htk => ?_)
  rcases (show t = 3 ∨ 4 ≤ t by omega) with rfl | ht4
  · right
    rw [h4 4 le_rfl, card_empty]
    omega
  · left
    rw [h4 t ht4, card_empty]
    omega

end main

end Gallai
