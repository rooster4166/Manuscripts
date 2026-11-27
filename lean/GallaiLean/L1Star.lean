import GallaiLean.PrescribedEndOutside

/-!
# The avoidance conjecture `L₁*`: reduction to blocked instances

Manuscript `manuscripts/l1star/l1star.tex`.

A *Lovász decomposition* of a graph `G` with at most one vertex of positive even degree has
`ends v = deg v mod 2` for every `v`; for an odd vertex `c`, `Q_c` is the path ending at `c`.
An *instance* is `(G, c, A)` with `c` odd and `A` a finite set of vertices that contains neither
`c`, nor a neighbour of `c`, nor a neighbour of the even vertex (`Admissible`). The instance is
*good* (`AvoidDecomp`) if some Lovász decomposition has `Q_c` disjoint from `A`.

* **`L1StarGen`**: every instance is good (no bound on `|A|`). It implies `L1Star`
  (`l1star_of_gen`), hence Conjecture EE (`ee_of_L1StarGen`).
* **`L1Blocked`**: every *blocked* instance is good. An instance is blocked if `G` has a vertex `g`
  of positive even degree, `c ∉ N(g)`, and every neighbour of `g` is adjacent to a vertex of
  `A ∖ {g}`.
* **`l1starGen_of_blocked`**: `L1Blocked → L1StarGen`. So a smallest counterexample to `L₁*` (in
  its general form) is blocked, and `ee_of_l1Blocked : L1Blocked → EE`.

The proof is Lovász's induction (measure `∑ deg + [no even vertex]`) with four reductions.
* `c ∈ N(g)` (`l1_case_adj`): delete `gc`; in `G − gc` the vertex `c` is even and `g` is odd. A
  decomposition whose path ending at `g` avoids `A ∪ {c}` gives, after appending `gc`, the claim.
  (Lift to the leaf graph at `g`, where the leaf stands for `c`, and merge: `avoid_of_leafSep`.)
* `u ∈ N(g)` with no neighbour in `A ∖ {g}` and `u ∉ N(c)` (`l1_case_target`): delete `gu`, solve
  `(G − gu, c, A)`, and restore `gu` by Fan's lemma with target `u` in the graph with a leaf hung
  at `c` (the end at `c` cannot move, since `c ∉ N(u)`); delete the leaf (`avoid_of_apexSep`).
* the same with `u ∈ N(c)` (`l1_case_target_adj`): solve `(G − gu − cu, u, A ∪ {c})`, lift to the
  leaf graph at `u` (the leaf stands for `c`), restore `gu` by Fan's lemma, merge.
* no even vertex (`l1_case_leaf`, `l1_case_big`): if `deg c = 1`, take the edge at `c` as a path;
  otherwise pass to the leaf graph `apex (G − cy) {y}`, where `c` is the even vertex and the leaf
  `ℓ` replaces `c`, and solve `(H, ℓ, A ∪ {c})`.
-/

open SimpleGraph

namespace Gallai

universe u

section defs

variable {V : Type u} [Fintype V]

/-- `A` is an admissible avoidance set for `c`: it contains neither `c`, nor a neighbour of `c`,
nor a neighbour of a vertex of positive even degree. -/
def Admissible (G : SimpleGraph V) [DecidableRel G.Adj] (c : V) (A : Finset V) : Prop :=
  ∀ a ∈ A, a ≠ c ∧ ¬ G.Adj c a ∧ ∀ g ∈ evenSet G, ¬ G.Adj g a

/-- Some Lovász decomposition has its paths ending at `c` disjoint from `A`. -/
def AvoidDecomp [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (c : V)
    (A : Finset V) : Prop :=
  ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
    ∀ P ∈ D.paths, (P.src = c ∨ P.tgt = c) → ∀ a ∈ A, a ∉ P.walk.support

end defs

/-- **Conjecture `L₁*`, general form**: every admissible set can be avoided (no bound on `|A|`).
The data of the manuscript support the strongest instance, `A = V ∖ (N[c] ∪ N(g))`. -/
def L1StarGen : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (evenSet G).card ≤ 1 → ∀ c : V, G.degree c % 2 = 1 → ∀ A : Finset V,
    Admissible G c A → AvoidDecomp G c A

/-- **`L₁*` on blocked instances**: `G` has a vertex `g` of positive even degree, `c ∉ N(g)`, and
every neighbour of `g` has a neighbour in `A ∖ {g}`. -/
def L1Blocked : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (evenSet G).card ≤ 1 → ∀ c : V, G.degree c % 2 = 1 → ∀ A : Finset V,
    Admissible G c A → ∀ g ∈ evenSet G, ¬ G.Adj g c →
    (∀ w, G.Adj g w → ∃ a ∈ A, a ≠ g ∧ G.Adj w a) → AvoidDecomp G c A

/-- The statement proved by strong induction on `n = ∑ deg + [no even vertex]`. -/
def L1Strong (n : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (evenSet G).card ≤ 1 → (∑ w, G.degree w) + (if (evenSet G).card = 0 then 1 else 0) = n →
    ∀ c : V, G.degree c % 2 = 1 → ∀ A : Finset V, Admissible G c A → AvoidDecomp G c A

variable {W : Type u} [Fintype W] [DecidableEq W]

section transfer

omit [DecidableEq W] in
/-- A vertex on a path of `K` has positive degree. -/
theorem GPath.degree_pos_of_mem {K : SimpleGraph W} [DecidableRel K.Adj]
    (P : GPath K) {x : W} (hx : x ∈ P.walk.support) : 0 < K.degree x := by
  have hnil : ¬ P.walk.Nil := by
    rw [← Walk.length_eq_zero_iff]; have := P.pos; omega
  obtain ⟨e, he, hxe⟩ := (Walk.mem_support_iff_exists_mem_edges_of_not_nil hnil).mp hx
  have heK := P.walk.edges_subset_edgeSet he
  induction e using Sym2.inductionOn with
  | hf a b =>
    rw [mem_edgeSet] at heK
    rcases Sym2.mem_iff.mp hxe with rfl | rfl
    · exact (K.degree_pos_iff_exists_adj _).mpr ⟨b, heK⟩
    · exact (K.degree_pos_iff_exists_adj _).mpr ⟨a, heK.symm⟩

omit [Fintype W] in
/-- **From the leaf graph back to `G`, with avoidance.** Let `xy ∈ E(G)` and let `DH` decompose
the leaf graph `apex (G − xy) {y}` (the leaf stands for `x`), with no end at `x`, one end at the
leaf, and no path containing the leaf together with `x` or with a vertex of `A ∌ x`. Merging the
leaf into `x` gives a decomposition of `G` with one end at `x`, the ends of `DH` elsewhere, whose
path ending at `x` avoids `A`. -/
theorem avoid_of_leafSep (G : SimpleGraph W) {x y : W} (hxy : G.Adj x y)
    (DH : PathDecomp (apex (delEdge G y x) {y}))
    (hsep : Separates DH (some x) none) (hx0 : DH.ends (some x) = 0)
    (hn1 : DH.ends none = 1) {A : Finset W} (hAx : x ∉ A)
    (hA : ∀ a ∈ A, Separates DH (some a) none) :
    ∃ D : PathDecomp G, D.ends x = 1 ∧ (∀ w, w ≠ x → D.ends w = DH.ends (some w)) ∧
      ∀ Q ∈ D.paths, (Q.src = x ∨ Q.tgt = x) → ∀ a ∈ A, a ∉ Q.walk.support := by
  classical
  obtain ⟨D, hDx, hDw, -, hfwd⟩ := leaf_merge G hxy DH hsep
  have hDx1 : D.ends x = 1 := by rw [hDx, hx0, hn1]
  refine ⟨D, hDx1, hDw, ?_⟩
  obtain ⟨Pℓ, hPℓ, hPℓend⟩ := DH.exists_end_of_pos (by rw [hn1]; omega)
  obtain ⟨Qℓ, hQℓ, hQs, hQt, hQe⟩ := hfwd Pℓ hPℓ
  have hQℓx : Qℓ.src = x ∨ Qℓ.tgt = x := by
    rcases hPℓend with h | h
    · left; rw [hQs, h, mergeMap_none]
    · right; rw [hQt, h, mergeMap_none]
  have hnoneP : (none : Option W) ∈ Pℓ.walk.support := by
    rcases hPℓend with h | h
    · rw [← h]; exact Pℓ.walk.start_mem_support
    · rw [← h]; exact Pℓ.walk.end_mem_support
  have hav : ∀ a ∈ A, a ∉ Qℓ.walk.support := by
    intro a ha hu
    have hax : x ≠ a := fun h => hAx (h ▸ ha)
    have hnil : ¬ Qℓ.walk.Nil := by
      rw [← Walk.length_eq_zero_iff]; have := Qℓ.pos; omega
    obtain ⟨e, he, hue⟩ := (Walk.mem_support_iff_exists_mem_edges_of_not_nil hnil).mp hu
    have he' : e ∈ Qℓ.edges := he
    rw [hQe, List.mem_map] at he'
    obtain ⟨e', he'P, rfl⟩ := he'
    rw [Sym2.mem_map] at hue
    obtain ⟨o, ho, hou⟩ := hue
    have ho' : o = some a := by
      cases o with
      | none => exact absurd hou (by simpa using hax)
      | some b => rw [mergeMap_some] at hou; rw [hou]
    subst ho'
    have hsP : some a ∈ Pℓ.walk.support :=
      (Walk.mem_support_iff_exists_mem_edges_of_not_nil (by
        rw [← Walk.length_eq_zero_iff]; have := Pℓ.pos; omega)).mpr ⟨e', he'P, ho⟩
    exact hA a ha Pℓ hPℓ ⟨hsP, hnoneP⟩
  intro Q hQ hQx
  by_cases hQQ : Q = Qℓ
  · rw [hQQ]; exact hav
  · have h2 := D.two_le_ends hQ hQℓ hQQ hQx hQℓx
    omega

/-- **Deleting a leaf hung at `c`, with avoidance.** Let `DH` decompose `apex G {c}` (a leaf hung
at the odd vertex `c`), with the Lovász end counts of `G` away from `c`, no end at `c`, and no
path containing the leaf together with a vertex of `A`. Deleting the leaf gives a Lovász
decomposition of `G` whose path ending at `c` avoids `A`. -/
theorem avoid_of_apexSep (G : SimpleGraph W) [DecidableRel G.Adj] {c : W}
    (hc : G.degree c % 2 = 1) (DH : PathDecomp (apex G {c}))
    (hDH : ∀ w, w ≠ c → DH.ends (some w) = G.degree w % 2) (hc0 : DH.ends (some c) = 0)
    {A : Finset W}
    (hsep : ∀ P ∈ DH.paths, (none : Option W) ∈ P.walk.support →
      ∀ a ∈ A, some a ∉ P.walk.support) :
    AvoidDecomp G c A := by
  classical
  obtain ⟨D, hD, hcov⟩ := (apexRetract G {c} c).delete_supp DH (by
    intro P _ y hy hky
    cases y with
    | some _ => simp [apexRetract] at hky
    | none => exact (P.end_of_pendant apex_none_pendant hy).imp Eq.symm Eq.symm)
  refine ⟨D, fun w => ?_, ?_⟩
  · by_cases hwc : w = c
    · subst hwc
      have hle := (hD w).2 (fun e₁ he₁ e₂ he₂ hk₁ hk₂ hv₁ hv₂ => by
        rw [(apex_nonkept he₁ hk₁ hv₁).1, (apex_nonkept he₂ hk₂ hv₂).1])
      change D.ends w ≤ DH.ends (some w) + 1 at hle
      rw [hc0] at hle
      have hp := D.ends_mod_two w
      rw [hc] at hp ⊢
      omega
    · rw [(hD w).1 (fun e he hk hwe => hwc (Finset.mem_singleton.mp (apex_nonkept he hk hwe).2))]
      change DH.ends (some w) = _
      exact hDH w hwc
  · intro Q hQ hend y hy hyQ
    obtain ⟨P, hP, hPs, hperm⟩ := hcov Q hQ
    have hyP : some y ∈ P.walk.support := hPs y hyQ
    have hnoneP : none ∉ P.walk.support := fun h => hsep P hP h y hy hyP
    have hsome : ∀ e ∈ P.edges, ∃ x y : W, e = s(some x, some y) := by
      intro e he
      induction e using Sym2.inductionOn with
      | hf x y =>
        have hx : x ∈ P.walk.support := Walk.fst_mem_support_of_mem_edges _ he
        have hy : y ∈ P.walk.support := Walk.snd_mem_support_of_mem_edges _ he
        cases x with
        | none => exact absurd hx hnoneP
        | some x' =>
          cases y with
          | none => exact absurd hy hnoneP
          | some y' => exact ⟨x', y', rfl⟩
    have hfilt : P.edges.filter (bothKept (apexRetract G {c} c).kept) = P.edges := by
      rw [List.filter_eq_self]
      intro e he
      obtain ⟨x, y, rfl⟩ := hsome e he
      simp [apexRetract, bothKept_mk]
    rw [hfilt] at hperm
    have hQc : Q.incid c = 1 := by
      have h := Q.endsAt_eq_ite c
      have h1 : 1 ≤ Q.endsAt c := by
        unfold GPath.endsAt
        rcases hend with h' | h' <;> simp [h']
      split_ifs at h with hh
      · exact hh
      · omega
    have hPc : P.incid (some c) = 1 := by
      rw [← hQc]
      unfold GPath.incid
      rw [hperm.countP_eq, List.countP_map]
      apply List.countP_congr
      intro e he
      obtain ⟨x, y, rfl⟩ := hsome e he
      simp [apexRetract]
    have hPend : P.endsAt (some c) = 1 := by rw [P.endsAt_eq_ite, hPc]; rfl
    have hle : P.endsAt (some c) ≤ DH.ends (some c) := by
      unfold PathDecomp.ends
      exact List.le_sum_of_mem (List.mem_map_of_mem hP)
    omega

omit [Fintype W] [DecidableEq W] in
/-- Edges of `apex (K − ab) T`: those of `apex K T` other than `ab`. -/
theorem apex_delEdge_edge_iff (K : SimpleGraph W) (T : Finset W) (a b : W)
    (e : Sym2 (Option W)) :
    e ∈ (apex (delEdge K a b) T).edgeSet ↔ e ∈ (apex K T).edgeSet ∧ e ≠ s(some b, some a) := by
  induction e using Sym2.inductionOn with
  | hf x y =>
    rw [mem_edgeSet, mem_edgeSet]
    cases x with
    | none =>
      cases y with
      | none => simp
      | some y => simp
    | some x =>
      cases y with
      | none => simp
      | some y =>
        simp only [apex_adj_some_some, delEdge, ne_eq, Sym2.eq_iff, Option.some.injEq]
        constructor
        · rintro ⟨hxy, h⟩
          refine ⟨hxy, fun h' => h ?_⟩
          rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · right; exact ⟨rfl, rfl⟩
          · left; exact ⟨rfl, rfl⟩
        · rintro ⟨hxy, h⟩
          refine ⟨hxy, fun h' => h ?_⟩
          rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · right; exact ⟨rfl, rfl⟩
          · left; exact ⟨rfl, rfl⟩

end transfer

section cases

variable {n : ℕ}

/-- **Case `c ∈ N(g)`.** Delete `gc`: in `G − gc` the vertex `g` is odd and `c` is even (or
isolated). A decomposition whose path ending at `g` avoids `A ∪ {c}` lifts to the leaf graph at
`g` (the leaf stands for `c`) and merges back. -/
theorem l1_case_adj (ih : ∀ m < n, L1Strong.{u} m) (G : SimpleGraph W) [DecidableRel G.Adj]
    (hev : (evenSet G).card ≤ 1)
    (hn : (∑ w, G.degree w) + (if (evenSet G).card = 0 then 1 else 0) = n)
    {g c : W} (hg : g ∈ evenSet G) (hgc : G.Adj g c) (hc : G.degree c % 2 = 1)
    {A : Finset W} (hA : Admissible G c A) : AvoidDecomp G c A := by
  classical
  have hgc' : g ≠ c := hgc.ne
  have huniq : ∀ v ∈ evenSet G, v = g := fun v hv => Finset.card_le_one.mp hev v hv g hg
  have hodd : ∀ v, v ≠ g → 0 < G.degree v → G.degree v % 2 = 1 := by
    intro v hvg hpos
    have : v ∉ evenSet G := fun h => hvg (huniq v h)
    rw [mem_evenSet_iff] at this
    omega
  have hgd := mem_evenSet_iff.mp hg
  have hdeg := delEdge_degree G hgc
  have hevsub : evenSet (delEdge G g c) ⊆ {c} := by
    intro v hv
    rw [mem_evenSet_iff] at hv
    rw [Finset.mem_singleton]
    by_contra hvc
    have h := hdeg v
    by_cases hvg : v = g
    · subst hvg; simp only [hvc, ite_true, ite_false] at h; omega
    · simp only [hvg, hvc, ite_false, add_zero] at h
      have := hodd v hvg (by omega); omega
  have hev' : (evenSet (delEdge G g c)).card ≤ 1 := (Finset.card_le_card hevsub).trans (by simp)
  have hg' : (delEdge G g c).degree g % 2 = 1 := by
    have h := hdeg g; simp only [hgc', ite_true, ite_false] at h; omega
  have hA' : Admissible (delEdge G g c) g (insert c A) := by
    intro a ha
    rw [Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · refine ⟨hgc'.symm, fun h => h.2 rfl, fun g' hg' h => ?_⟩
      rw [Finset.mem_singleton.mp (hevsub hg')] at h
      exact h.1.ne rfl
    · obtain ⟨hac, hca, hga⟩ := hA a ha
      refine ⟨fun h => hca (by rw [h]; exact hgc.symm), fun h => hga g hg h.1, fun g' hg' h => ?_⟩
      rw [Finset.mem_singleton.mp (hevsub hg')] at h
      exact hca h.1
  have hsum := delEdge_sum_degree G hgc
  have hlt : (∑ w, (delEdge G g c).degree w) +
      (if (evenSet (delEdge G g c)).card = 0 then 1 else 0) < n := by
    have h1 : (evenSet G).card ≠ 0 := Finset.card_ne_zero.mpr ⟨g, hg⟩
    simp only [h1, ite_false, add_zero] at hn
    split_ifs <;> omega
  obtain ⟨D', hD', hav'⟩ := ih _ hlt W (delEdge G g c) hev' rfl g hg' (insert c A) hA'
  have hD'g : D'.ends g = 1 := by rw [hD']; exact hg'
  obtain ⟨P, hP, hPend⟩ := D'.exists_end_of_pos (by rw [hD'g]; omega)
  have hPav := hav' P hP hPend
  obtain ⟨D₃, hD₃some, hD₃none, hD₃cov⟩ := D'.liftLeaf hP hPend
  have hsep₃ : ∀ a ∈ insert c A, Separates D₃ (some a) none := by
    intro a ha Q' hQ' ⟨hx, hn⟩
    rcases hD₃cov Q' hQ' with h | ⟨Q, hQ, hs⟩
    · rcases h (some a) hx with h | ⟨y', hy', h⟩
      · exact Option.some_ne_none _ h
      · rw [Option.some.injEq] at h
        subst h
        exact hPav _ ha hy'
    · rw [hs, List.mem_map] at hn
      obtain ⟨_, _, h⟩ := hn
      exact Option.some_ne_none _ h
  have hc0 : D₃.ends (some c) = 0 := by
    have h := hD₃some c
    simp only [hgc'.symm, ite_false, add_zero] at h
    rw [h, hD']
    have := hdeg c
    simp only [hgc'.symm, ite_true, ite_false] at this
    omega
  obtain ⟨D, hDc, hDw, hav⟩ := avoid_of_leafSep G hgc.symm D₃
    (hsep₃ c (Finset.mem_insert_self _ _)) hc0 hD₃none (A := A) (fun h => (hA c h).1 rfl)
    (fun a ha => hsep₃ a (Finset.mem_insert_of_mem ha))
  refine ⟨D, fun v => ?_, hav⟩
  by_cases hvc : v = c
  · rw [hvc, hDc, hc]
  · rw [hDw v hvc]
    have h := hD₃some v
    by_cases hvg : v = g
    · subst hvg
      simp only [ite_true] at h
      rw [hD'g] at h
      omega
    · simp only [hvg, ite_false, add_zero] at h
      rw [h, hD']
      have := hdeg v
      simp only [hvg, hvc, ite_false, add_zero] at this
      rw [this]

/-- **Case `u ∈ N(g)` free of `A ∖ {g}`, `u ∉ N(c)`.** Delete `gu`, solve `(G − gu, c, A)`, hang a
leaf at `c`, restore `gu` by Fan's lemma with target `u` (the end at `c` is not touched since
`c ∉ N(u)`), and delete the leaf. -/
theorem l1_case_target (ih : ∀ m < n, L1Strong.{u} m) (G : SimpleGraph W) [DecidableRel G.Adj]
    (hev : (evenSet G).card ≤ 1)
    (hn : (∑ w, G.degree w) + (if (evenSet G).card = 0 then 1 else 0) = n)
    {g c x : W} (hg : g ∈ evenSet G) (hgc : ¬ G.Adj g c) (hgx : G.Adj g x) (hcx : ¬ G.Adj c x)
    (hc : G.degree c % 2 = 1) {A : Finset W} (hA : Admissible G c A)
    (hfx : ∀ a ∈ A, a ≠ g → ¬ G.Adj x a) : AvoidDecomp G c A := by
  classical
  have hgx' : g ≠ x := hgx.ne
  have huniq : ∀ v ∈ evenSet G, v = g := fun v hv => Finset.card_le_one.mp hev v hv g hg
  have hodd : ∀ v, v ≠ g → 0 < G.degree v → G.degree v % 2 = 1 := by
    intro v hvg hpos
    have : v ∉ evenSet G := fun h => hvg (huniq v h)
    rw [mem_evenSet_iff] at this
    omega
  have hgd := mem_evenSet_iff.mp hg
  have hcg : c ≠ g := fun h => by rw [h] at hc; omega
  have hcx' : c ≠ x := fun h => hgc (h ▸ hgx)
  have hdeg := delEdge_degree G hgx
  have hevsub : evenSet (delEdge G g x) ⊆ {x} := by
    intro v hv
    rw [mem_evenSet_iff] at hv
    rw [Finset.mem_singleton]
    by_contra hvx
    have h := hdeg v
    by_cases hvg : v = g
    · subst hvg; simp only [hvx, ite_true, ite_false] at h; omega
    · simp only [hvg, hvx, ite_false, add_zero] at h
      have := hodd v hvg (by omega); omega
  have hev' : (evenSet (delEdge G g x)).card ≤ 1 := (Finset.card_le_card hevsub).trans (by simp)
  have hc' : (delEdge G g x).degree c % 2 = 1 := by
    have h := hdeg c; simp only [hcg, hcx', ite_false, add_zero] at h; omega
  have hA' : Admissible (delEdge G g x) c A := by
    intro a ha
    obtain ⟨hac, hca, hga⟩ := hA a ha
    refine ⟨hac, fun h => hca h.1, fun g' hg' h => ?_⟩
    rw [Finset.mem_singleton.mp (hevsub hg')] at h
    have hag : a ≠ g := fun hag => h.2 (by rw [hag, Sym2.eq_swap])
    exact hfx a ha hag h.1
  have hsum := delEdge_sum_degree G hgx
  have hlt : (∑ w, (delEdge G g x).degree w) +
      (if (evenSet (delEdge G g x)).card = 0 then 1 else 0) < n := by
    have h1 : (evenSet G).card ≠ 0 := Finset.card_ne_zero.mpr ⟨g, hg⟩
    simp only [h1, ite_false, add_zero] at hn
    split_ifs <;> omega
  obtain ⟨D', hD', hav'⟩ := ih _ hlt W (delEdge G g x) hev' rfl c hc' A hA'
  have hD'c : D'.ends c = 1 := by rw [hD']; exact hc'
  obtain ⟨P, hP, hPend⟩ := D'.exists_end_of_pos (by rw [hD'c]; omega)
  have hPav := hav' P hP hPend
  obtain ⟨D₃, hD₃some, hD₃none, hD₃cov⟩ := D'.liftLeaf hP hPend
  have hsep₃ : ∀ Q' ∈ D₃.paths, (none : Option W) ∈ Q'.walk.support →
      ∀ a ∈ A, some a ∉ Q'.walk.support := by
    intro Q' hQ' hn a ha hx
    rcases hD₃cov Q' hQ' with h | ⟨Q, hQ, hs⟩
    · rcases h (some a) hx with h | ⟨y', hy', h⟩
      · exact Option.some_ne_none _ h
      · rw [Option.some.injEq] at h
        subst h
        exact hPav _ ha hy'
    · rw [hs, List.mem_map] at hn
      obtain ⟨_, _, h⟩ := hn
      exact Option.some_ne_none _ h
  -- Fan's lemma in `apex G {c}`: restore `gx`, moving the end at `g` to `x`
  have hK : (apex G {c}).Adj (some x) (some g) := by
    rw [apex_adj_some_some]; exact hgx.symm
  have hD₃g : D₃.ends (some g) = 1 := by
    have h := hD₃some g
    simp only [hcg.symm, ite_false, add_zero] at h
    rw [h, hD']
    have := hdeg g
    simp only [hgx', ite_true, ite_false] at this
    omega
  have hcount : (Finset.univ.filter (fun v => (apex (delEdge G g x) {c}).Adj (some x) v ∧
      D₃.ends v = 0)).card < D₃.ends (some g) := by
    have hempty : Finset.univ.filter (fun v => (apex (delEdge G g x) {c}).Adj (some x) v ∧
        D₃.ends v = 0) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
      rw [Finset.mem_filter] at hv
      obtain ⟨-, hadj, h0⟩ := hv
      cases v with
      | none =>
        rw [apex_adj_some_none, Finset.mem_singleton] at hadj
        exact hcx' hadj.symm
      | some w =>
        rw [apex_adj_some_some] at hadj
        have hwc : w ≠ c := fun h => hcx (h ▸ hadj.1.symm)
        have hwg : w ≠ g := fun h => hadj.2 (by rw [h, Sym2.eq_swap])
        have hwx : w ≠ x := hadj.ne.symm
        have h := hD₃some w
        simp only [hwc, ite_false, add_zero] at h
        rw [h, hD'] at h0
        have hdw := hdeg w
        simp only [hwg, hwx, ite_false, add_zero] at hdw
        have := hodd w hwg ((G.degree_pos_iff_exists_adj w).mpr ⟨x, hadj.1.symm⟩)
        omega
    rw [hempty, Finset.card_empty, hD₃g]
    omega
  obtain ⟨DH, -, hDHx, hDHg, hDHrest, hcovH⟩ :=
    fan_single_supp (G := apex G {c}) hK (apex_delEdge_edge_iff G {c} g x) D₃ hcount
  have hsepH : ∀ Q ∈ DH.paths, (none : Option W) ∈ Q.walk.support →
      ∀ a ∈ A, some a ∉ Q.walk.support := by
    intro Q hQ hn a ha hx
    obtain ⟨Q', hQ', hsub⟩ := hcovH Q hQ
    have hn' : (none : Option W) ∈ Q'.walk.support :=
      (hsub none hn).resolve_right (by simp)
    rcases hsub (some a) hx with h | h
    · exact hsep₃ Q' hQ' hn' a ha h
    · rw [Option.some.injEq] at h
      exact (hA a ha).2.2 g hg (h ▸ hgx)
  refine avoid_of_apexSep G hc DH (fun w hwc => ?_) ?_ hsepH
  · by_cases hwx : w = x
    · subst hwx
      rw [hDHx]
      have h := hD₃some w
      simp only [hwc, ite_false, add_zero] at h
      rw [h, hD']
      have := hdeg w
      simp only [hgx'.symm, ite_true, ite_false] at this
      have := hodd w hgx'.symm ((G.degree_pos_iff_exists_adj w).mpr ⟨g, hgx.symm⟩)
      omega
    · by_cases hwg : w = g
      · subst hwg
        rw [hD₃g] at hDHg
        have : DH.ends (some w) = 0 := by omega
        rw [this, hgd.2]
      · rw [hDHrest (some w) (by simp [hwx]) (by simp [hwg])]
        have h := hD₃some w
        simp only [hwc, ite_false, add_zero] at h
        rw [h, hD']
        have := hdeg w
        simp only [hwg, hwx, ite_false, add_zero] at this
        rw [this]
  · rw [hDHrest (some c) (by simp [hcx']) (by simp [hcg])]
    have h := hD₃some c
    simp only [ite_true] at h
    rw [hD'c] at h
    omega

/-- **Case `u ∈ N(g) ∩ N(c)` free of `A ∖ {g}`.** Solve `(G − cu − gu, u, A ∪ {c})` (there `c` is
the even vertex), lift to the leaf graph at `u` (the leaf stands for `c`), restore `gu` by Fan's
lemma with target `u`, and merge the leaf into `c`. -/
theorem l1_case_target_adj (ih : ∀ m < n, L1Strong.{u} m) (G : SimpleGraph W)
    [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1)
    (hn : (∑ w, G.degree w) + (if (evenSet G).card = 0 then 1 else 0) = n)
    {g c x : W} (hg : g ∈ evenSet G) (hgc : ¬ G.Adj g c) (hgx : G.Adj g x) (hcx : G.Adj c x)
    (hc : G.degree c % 2 = 1) {A : Finset W} (hA : Admissible G c A)
    (hfx : ∀ a ∈ A, a ≠ g → ¬ G.Adj x a) : AvoidDecomp G c A := by
  classical
  have hgx' : g ≠ x := hgx.ne
  have hcx' : c ≠ x := hcx.ne
  have huniq : ∀ v ∈ evenSet G, v = g := fun v hv => Finset.card_le_one.mp hev v hv g hg
  have hodd : ∀ v, v ≠ g → 0 < G.degree v → G.degree v % 2 = 1 := by
    intro v hvg hpos
    have : v ∉ evenSet G := fun h => hvg (huniq v h)
    rw [mem_evenSet_iff] at this
    omega
  have hgd := mem_evenSet_iff.mp hg
  have hcg : c ≠ g := fun h => by rw [h] at hc; omega
  have hF : (delEdge G x c).Adj g x := ⟨hgx, fun h => by
    rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨h, -⟩
    · exact hgx' h
    · exact hcg h.symm⟩
  have hd₁ := delEdge_degree G hcx.symm
  have hd₂ := delEdge_degree (delEdge G x c) hF
  have hdeg : ∀ v, (delEdge (delEdge G x c) g x).degree v + (if v = g then 1 else 0) +
      2 * (if v = x then 1 else 0) + (if v = c then 1 else 0) = G.degree v := by
    intro v; have := hd₁ v; have := hd₂ v; omega
  have hevsub : evenSet (delEdge (delEdge G x c) g x) ⊆ {c} := by
    intro v hv
    rw [mem_evenSet_iff] at hv
    rw [Finset.mem_singleton]
    by_contra hvc
    have h := hdeg v
    by_cases hvg : v = g
    · subst hvg; simp only [hvc, hgx', ite_true, ite_false] at h; omega
    · by_cases hvx : v = x
      · subst hvx
        simp only [hvc, hvg, ite_true, ite_false] at h
        have := hodd v hvg (by omega); omega
      · simp only [hvg, hvx, hvc, ite_false, add_zero, mul_zero] at h
        have := hodd v hvg (by omega); omega
  have hev' : (evenSet (delEdge (delEdge G x c) g x)).card ≤ 1 :=
    (Finset.card_le_card hevsub).trans (by simp)
  have hxodd := hodd x hgx'.symm ((G.degree_pos_iff_exists_adj x).mpr ⟨g, hgx.symm⟩)
  have hx' : (delEdge (delEdge G x c) g x).degree x % 2 = 1 := by
    have h := hdeg x
    simp only [hgx'.symm, hcx'.symm, ite_true, ite_false] at h
    omega
  have hA' : Admissible (delEdge (delEdge G x c) g x) x (insert c A) := by
    intro a ha
    rw [Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · refine ⟨hcx', fun h => h.1.2 rfl, fun g' hg' h => ?_⟩
      rw [Finset.mem_singleton.mp (hevsub hg')] at h
      exact h.1.1.ne rfl
    · obtain ⟨hac, hca, hga⟩ := hA a ha
      refine ⟨fun h => hga g hg (h ▸ hgx), fun h => ?_, fun g' hg' h => ?_⟩
      · have hag : a ≠ g := fun hag => h.2 (by rw [hag, Sym2.eq_swap])
        exact hfx a ha hag h.1.1
      · rw [Finset.mem_singleton.mp (hevsub hg')] at h
        exact hca h.1.1
  have hsum₁ := delEdge_sum_degree G hcx.symm
  have hsum₂ := delEdge_sum_degree (delEdge G x c) hF
  have hlt : (∑ w, (delEdge (delEdge G x c) g x).degree w) +
      (if (evenSet (delEdge (delEdge G x c) g x)).card = 0 then 1 else 0) < n := by
    have h1 : (evenSet G).card ≠ 0 := Finset.card_ne_zero.mpr ⟨g, hg⟩
    simp only [h1, ite_false, add_zero] at hn
    split_ifs <;> omega
  obtain ⟨D', hD', hav'⟩ :=
    ih _ hlt W (delEdge (delEdge G x c) g x) hev' rfl x hx' (insert c A) hA'
  have hD'x : D'.ends x = 1 := by rw [hD']; exact hx'
  obtain ⟨P, hP, hPend⟩ := D'.exists_end_of_pos (by rw [hD'x]; omega)
  have hPav := hav' P hP hPend
  obtain ⟨D₃, hD₃some, hD₃none, hD₃cov⟩ := D'.liftLeaf hP hPend
  have hsep₃ : ∀ a ∈ insert c A, Separates D₃ (some a) none := by
    intro a ha Q' hQ' ⟨hx, hn⟩
    rcases hD₃cov Q' hQ' with h | ⟨Q, hQ, hs⟩
    · rcases h (some a) hx with h | ⟨y', hy', h⟩
      · exact Option.some_ne_none _ h
      · rw [Option.some.injEq] at h
        subst h
        exact hPav _ ha hy'
    · rw [hs, List.mem_map] at hn
      obtain ⟨_, _, h⟩ := hn
      exact Option.some_ne_none _ h
  -- Fan's lemma in the leaf graph `apex (G − xc) {x}`: restore `gx`
  have hK : (apex (delEdge G x c) {x}).Adj (some x) (some g) := by
    rw [apex_adj_some_some]; exact hF.symm
  have hD₃g : D₃.ends (some g) = 1 := by
    have h := hD₃some g
    simp only [hgx', ite_false, add_zero] at h
    rw [h, hD']
    have := hdeg g
    simp only [hgx', hcg.symm, ite_true, ite_false] at this
    omega
  have hcount : (Finset.univ.filter (fun v => (apex (delEdge (delEdge G x c) g x) {x}).Adj
      (some x) v ∧ D₃.ends v = 0)).card < D₃.ends (some g) := by
    have hempty : Finset.univ.filter (fun v => (apex (delEdge (delEdge G x c) g x) {x}).Adj
        (some x) v ∧ D₃.ends v = 0) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
      rw [Finset.mem_filter] at hv
      obtain ⟨-, hadj, h0⟩ := hv
      cases v with
      | none => rw [hD₃none] at h0; exact one_ne_zero h0
      | some w =>
        rw [apex_adj_some_some] at hadj
        have hwc : w ≠ c := fun h => hadj.1.2 (by rw [h])
        have hwg : w ≠ g := fun h => hadj.2 (by rw [h, Sym2.eq_swap])
        have hwx : w ≠ x := hadj.ne.symm
        have h := hD₃some w
        simp only [hwx, ite_false, add_zero] at h
        rw [h, hD'] at h0
        have hdw := hdeg w
        simp only [hwg, hwx, hwc, ite_false, add_zero, mul_zero] at hdw
        have := hodd w hwg ((G.degree_pos_iff_exists_adj w).mpr ⟨x, hadj.1.1.symm⟩)
        omega
    rw [hempty, Finset.card_empty, hD₃g]
    omega
  obtain ⟨DH, -, hDHx, hDHg, hDHrest, hcovH⟩ :=
    fan_single_supp (G := apex (delEdge G x c) {x}) hK
      (apex_delEdge_edge_iff (delEdge G x c) {x} g x) D₃ hcount
  have hsepH : ∀ a ∈ insert c A, Separates DH (some a) none := by
    intro a ha
    have hxa : some x ≠ some a := by
      rw [Finset.mem_insert] at ha
      rcases ha with rfl | ha
      · simp [Ne.symm hcx']
      · simp only [ne_eq, Option.some.injEq]
        intro h
        exact (hA a ha).2.2 g hg (h ▸ hgx)
    exact separates_of_cover hxa (by simp) (hsep₃ a ha) hcovH
  have hDHnone : DH.ends none = 1 := by rw [hDHrest none (by simp) (by simp), hD₃none]
  have hc0 : DH.ends (some c) = 0 := by
    rw [hDHrest (some c) (by simp [hcx']) (by simp [hcg])]
    have h := hD₃some c
    simp only [hcx', ite_false, add_zero] at h
    rw [h, hD']
    have := hdeg c
    simp only [hcg, hcx', ite_true, ite_false, add_zero, mul_zero] at this
    omega
  obtain ⟨D, hDc, hDw, hav⟩ := avoid_of_leafSep G hcx DH
    (hsepH c (Finset.mem_insert_self _ _)) hc0 hDHnone (A := A) (fun h => (hA c h).1 rfl)
    (fun a ha => hsepH a (Finset.mem_insert_of_mem ha))
  refine ⟨D, fun v => ?_, hav⟩
  by_cases hvc : v = c
  · rw [hvc, hDc, hc]
  · rw [hDw v hvc]
    by_cases hvx : v = x
    · subst hvx
      rw [hDHx]
      have h := hD₃some v
      simp only [ite_true] at h
      rw [hD'x] at h
      omega
    · by_cases hvg : v = g
      · subst hvg
        rw [hD₃g] at hDHg
        have : DH.ends (some v) = 0 := by omega
        rw [this, hgd.2]
      · rw [hDHrest (some v) (by simp [hvx]) (by simp [hvg])]
        have h := hD₃some v
        simp only [hvx, ite_false, add_zero] at h
        rw [h, hD']
        have := hdeg v
        simp only [hvg, hvx, hvc, ite_false, add_zero, mul_zero] at this
        rw [this]

/-- **No even vertex, `deg c = 1`.** The edge at `c` is a path of its own. -/
theorem l1_case_leaf (G : SimpleGraph W) [DecidableRel G.Adj] (hnone : ∀ z, z ∉ evenSet G)
    {c : W} (hc1 : G.degree c = 1) {A : Finset W} (hA : Admissible G c A) :
    AvoidDecomp G c A := by
  classical
  obtain ⟨y, hcy⟩ := (G.degree_pos_iff_exists_adj c).mp (by omega)
  have hcy' : c ≠ y := hcy.ne
  have hpar : ∀ w, 0 < G.degree w → G.degree w % 2 = 1 := fun w hw => by
    have := hnone w
    rw [mem_evenSet_iff] at this
    omega
  have hdeg := delEdge_degree G hcy
  have hc0 : (delEdge G c y).degree c = 0 := by
    have h := hdeg c; simp only [hcy', ite_true, ite_false] at h; omega
  have hevsub : evenSet (delEdge G c y) ⊆ {y} := by
    intro v hv
    rw [mem_evenSet_iff] at hv
    rw [Finset.mem_singleton]
    by_contra hvy
    by_cases hvc : v = c
    · subst hvc; omega
    · have h := hdeg v
      simp only [hvc, hvy, ite_false, add_zero] at h
      have := hpar v (by omega); omega
  have hev' : (evenSet (delEdge G c y)).card ≤ 1 := (Finset.card_le_card hevsub).trans (by simp)
  obtain ⟨D', hD'⟩ := lovasz_ends (delEdge G c y) hev'
  obtain ⟨D, hDe, hcov⟩ := PathDecomp.add_edge_supp hcy (delEdge_edgeSet G c y) D'
  refine ⟨D, fun v => ?_, ?_⟩
  · rw [hDe, hD']
    have h := hdeg v
    by_cases hvc : v = c
    · subst hvc
      rw [hc0, hc1]
      simp [Ne.symm hcy']
    · by_cases hvy : v = y
      · subst hvy
        simp only [hvc, hcy', ite_true, ite_false, add_zero] at h ⊢
        have := hpar v ((G.degree_pos_iff_exists_adj v).mpr ⟨c, hcy.symm⟩)
        omega
      · simp only [hvc, hvy, ite_false, add_zero, Ne.symm hvc, Ne.symm hvy] at h ⊢
        rw [h]
  · intro Q hQ hend a ha haQ
    obtain ⟨hac, hca, -⟩ := hA a ha
    have hcQ : c ∈ Q.walk.support := by
      rcases hend with h | h
      · rw [← h]; exact Q.walk.start_mem_support
      · rw [← h]; exact Q.walk.end_mem_support
    rcases hcov Q hQ with h | ⟨Q', hQ', hsub⟩
    · rcases h a haQ with h | h
      · exact hac h
      · exact hca (h ▸ hcy)
    · have := GPath.degree_pos_of_mem Q' (hsub c hcQ)
      omega

/-- **No even vertex, `deg c ≥ 3`.** Pass to the leaf graph `apex (G − cy) {y}`: there `c` is the
only even vertex and the leaf replaces `c`; solve `(H, leaf, A ∪ {c})` and merge. -/
theorem l1_case_big (ih : ∀ m < n, L1Strong.{u} m) (G : SimpleGraph W) [DecidableRel G.Adj]
    (hn : (∑ w, G.degree w) + (if (evenSet G).card = 0 then 1 else 0) = n)
    (hnone : ∀ z, z ∉ evenSet G) {c : W} (hc : G.degree c % 2 = 1) (hc3 : 3 ≤ G.degree c)
    {A : Finset W} (hA : Admissible G c A) : AvoidDecomp G c A := by
  classical
  obtain ⟨y, hcy⟩ := (G.degree_pos_iff_exists_adj c).mp (by omega)
  have hyc : G.Adj y c := hcy.symm
  have hcy' : c ≠ y := hcy.ne
  have hpar : ∀ w, 0 < G.degree w → G.degree w % 2 = 1 := fun w hw => by
    have := hnone w
    rw [mem_evenSet_iff] at this
    omega
  have hdeg := delEdge_degree G hyc
  have hHsome : ∀ w, (apex (delEdge G y c) {y}).degree (some w) =
      (delEdge G y c).degree w + (if w = y then 1 else 0) := by
    intro w
    rw [apex_degree_some]
    simp [Finset.mem_singleton]
  have hHnone : (apex (delEdge G y c) {y}).degree none = 1 := by
    rw [apex_degree_none]; simp
  have hHc : (apex (delEdge G y c) {y}).degree (some c) + 1 = G.degree c := by
    rw [hHsome]
    have h := hdeg c
    simp only [hcy', ite_true, ite_false] at h ⊢
    omega
  have hHw : ∀ w, w ≠ c → (apex (delEdge G y c) {y}).degree (some w) = G.degree w := by
    intro w hwc
    rw [hHsome]
    have h := hdeg w
    by_cases hwy : w = y
    · subst hwy; simp only [hwc, ite_true, ite_false] at h ⊢; omega
    · simp only [hwy, hwc, ite_false, add_zero] at h ⊢; exact h
  have hevH : evenSet (apex (delEdge G y c) {y}) ⊆ {some c} := by
    intro w hw
    rw [mem_evenSet_iff] at hw
    rw [Finset.mem_singleton]
    cases w with
    | none => rw [hHnone] at hw; omega
    | some w =>
      by_contra hwc
      have hwc' : w ≠ c := fun h => hwc (h ▸ rfl)
      rw [hHw w hwc'] at hw
      have := hpar w hw.1
      omega
  have hcH : some c ∈ evenSet (apex (delEdge G y c) {y}) := by
    rw [mem_evenSet_iff]; omega
  have hcardH : (evenSet (apex (delEdge G y c) {y})).card ≤ 1 :=
    (Finset.card_le_card hevH).trans (by simp)
  have hsumH : ∑ w, (apex (delEdge G y c) {y}).degree w = ∑ w, G.degree w := by
    rw [Fintype.sum_option, hHnone, ← delEdge_sum_degree G hyc]
    simp only [hHsome, Finset.sum_add_distrib]
    simp
    omega
  have hlt : (∑ w, (apex (delEdge G y c) {y}).degree w) +
      (if (evenSet (apex (delEdge G y c) {y})).card = 0 then 1 else 0) < n := by
    have h1 : (evenSet (apex (delEdge G y c) {y})).card ≠ 0 :=
      Finset.card_ne_zero.mpr ⟨_, hcH⟩
    have h2 : (evenSet G).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem hnone)
    simp only [h2, ite_true] at hn
    simp only [h1, ite_false, add_zero, hsumH]
    omega
  have hnoneodd : (apex (delEdge G y c) {y}).degree none % 2 = 1 := by rw [hHnone]
  have hAH : Admissible (apex (delEdge G y c) {y}) none (insert (some c) (A.image some)) := by
    intro b hb
    rw [Finset.mem_insert, Finset.mem_image] at hb
    rcases hb with rfl | ⟨a, ha, rfl⟩
    · refine ⟨by simp, fun h => hcy' ?_, fun g' hg' h => ?_⟩
      · rw [apex_adj_none_some, Finset.mem_singleton] at h; exact h
      · rw [Finset.mem_singleton.mp (hevH hg')] at h
        exact h.ne rfl
    · obtain ⟨hac, hca, -⟩ := hA a ha
      refine ⟨by simp, fun h => hca ?_, fun g' hg' h => hca ?_⟩
      · rw [apex_adj_none_some, Finset.mem_singleton] at h; rw [h]; exact hcy
      · rw [Finset.mem_singleton.mp (hevH hg'), apex_adj_some_some] at h
        exact h.1
  obtain ⟨DH, hDH, havH⟩ := ih _ hlt (Option W) (apex (delEdge G y c) {y}) hcardH rfl none
    hnoneodd _ hAH
  have hsepH : ∀ a, (a = c ∨ a ∈ A) → Separates DH (some a) none := by
    intro a ha P hP ⟨hs, hn⟩
    have hend := P.end_of_pendant apex_none_pendant hn
    refine havH P (hP) (hend.imp Eq.symm Eq.symm |>.imp Eq.symm Eq.symm) (some a) ?_ hs
    rcases ha with rfl | ha
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ha)
  have hc0 : DH.ends (some c) = 0 := by
    rw [hDH]
    have := hHc
    omega
  have hn1 : DH.ends none = 1 := by rw [hDH, hHnone]
  obtain ⟨D, hDc, hDw, hav⟩ := avoid_of_leafSep G hcy DH (hsepH c (Or.inl rfl)) hc0 hn1
    (A := A) (fun h => (hA c h).1 rfl) (fun a ha => hsepH a (Or.inr ha))
  refine ⟨D, fun v => ?_, hav⟩
  by_cases hvc : v = c
  · rw [hvc, hDc, hc]
  · rw [hDw v hvc, hDH, hHw v hvc]

/-- **The induction.** Every instance of size `n` is good, given `L1Blocked`. -/
theorem l1_strong (hB : L1Blocked.{u}) (n : ℕ) : L1Strong.{u} n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ G _ hev hn c hc A hA
  by_cases hz : ∃ g, g ∈ evenSet G
  · obtain ⟨g, hg⟩ := hz
    by_cases hgc : G.Adj g c
    · exact l1_case_adj ih G hev hn hg hgc hc hA
    · by_cases hfree : ∃ x, G.Adj g x ∧ ∀ a ∈ A, a ≠ g → ¬ G.Adj x a
      · obtain ⟨x, hgx, hfx⟩ := hfree
        by_cases hcx : G.Adj c x
        · exact l1_case_target_adj ih G hev hn hg hgc hgx hcx hc hA hfx
        · exact l1_case_target ih G hev hn hg hgc hgx hcx hc hA hfx
      · refine hB V G hev c hc A hA g hg hgc fun w hw => ?_
        by_contra hno
        exact hfree ⟨w, hw, fun a ha hag haw => hno ⟨a, ha, hag, haw⟩⟩
  · simp only [not_exists] at hz
    by_cases h1 : G.degree c = 1
    · exact l1_case_leaf G hz h1 hA
    · exact l1_case_big ih G hn hz hc (by omega) hA

end cases

/-- **Reduction to blocked instances.** If every blocked instance is good, every instance is good:
`L1Blocked → L1StarGen`. Equivalently, a smallest counterexample to `L₁*` in its general form is
blocked. -/
theorem l1starGen_of_blocked (hB : L1Blocked.{u}) : L1StarGen.{u} :=
  fun V _ _ G _ hev c hc A hA => l1_strong hB _ V G hev rfl c hc A hA

/-- The general form implies the stated conjecture `L₁*` (`|A| ≤ 2`). -/
theorem l1star_of_gen (h : L1StarGen.{u}) : L1Star.{u} :=
  fun V _ _ G _ hev c hc A _ hA => h V G hev c hc A hA

/-- **EE from the general form of `L₁*`.** -/
theorem ee_of_L1StarGen (h : L1StarGen.{u}) (G : SimpleGraph W) [DecidableRel G.Adj]
    (hev : (evenSet G).card ≤ 1) {z x : W} (hz : z ∈ evenSet G) (hzx : G.Adj z x) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∃ P ∈ D.paths, (P.src = x ∨ P.tgt = x) ∧ s(x, z) ∈ P.edges :=
  ee_of_L1Star (l1star_of_gen h) G hev hz hzx

/-- **EE from the blocked case of `L₁*`.** If `z` is the only vertex of positive even degree and
`x ∈ N(z)`, then `xz` is the terminal edge at `x` of some Lovász decomposition, provided every
blocked instance of `L₁*` is good. -/
theorem ee_of_l1Blocked (hB : L1Blocked.{u}) (G : SimpleGraph W) [DecidableRel G.Adj]
    (hev : (evenSet G).card ≤ 1) {z x : W} (hz : z ∈ evenSet G) (hzx : G.Adj z x) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∃ P ∈ D.paths, (P.src = x ∨ P.tgt = x) ∧ s(x, z) ∈ P.edges :=
  ee_of_L1StarGen (l1starGen_of_blocked hB) G hev hz hzx

end Gallai
