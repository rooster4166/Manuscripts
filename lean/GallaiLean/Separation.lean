import GallaiLean.FanSupport
import GallaiLean.Lovasz

/-!
# Lovász decompositions that separate two vertices

Route-descent manuscript, Theorem "separation".

**Theorem** (`separation_set`). If `G` has at most one vertex of positive even degree and the
vertices of `X` are pairwise at distance at least three (`Packed`), then some Lovász decomposition
has every path meeting `X` at most once (`MeetsOnce`).

**Theorem** (`separation`, the case `X = {c, a}`). Let `G` have at most one vertex of positive even degree, and let `c`,
`a` be at distance at least three (`FarApart`: distinct, non-adjacent, no common neighbour). Then
`G` has a path decomposition with `ends v = deg v mod 2` for every `v` (a Lovász decomposition) in
which no path contains both `c` and `a` (`Separates`).

Corollary (`lovasz_avoid`): the path ending at `c` avoids `a` (conjecture `L₁` of the manuscript
at distance three).

Proof: Lovász's induction (`Lovasz.lean`, cases I–IV), carrying the separation invariant.
* Case I (a vertex `z` of positive even degree): delete `uz` for a neighbour `u ∉ {c, a}` of `z`,
  and restore it by Fan's lemma towards `u`. `fan_single_supp` keeps every vertex set except that
  one path gains `u ∉ {c, a}`, so separation survives.
* Case II (all degrees odd or zero, some `x ∉ {c, a}` of degree ≥ 3): Lovász's leaf trick on
  `Option W`, deleting the leaf by `Retract.delete_supp`, then a new path `ux` or Fan's lemma
  towards `x ∉ {c, a}`.
* Case III (all degrees odd or zero, every vertex outside `{c, a}` of degree ≤ 2, and one of
  positive degree, hence a leaf `v`): delete the leaf edge `vw`, restore it as the path `vw`.
* Case IV: no vertex outside `{c, a}` has positive degree; then there are no edges.

Corollary (`lovasz_avoid_set`, `lovasz_avoid_nonadj`: conjecture `L₁` of the manuscript, now a
theorem): in a graph
with no vertex of positive even degree, for every odd `c` and every `a` not adjacent to `c`, some
Lovász decomposition has the path ending at `c` avoiding `a`. Proof: attach a leaf `ℓ` at `c`; then
`c` is the only vertex of positive even degree and `ℓ`, `a` are at distance at least three, so
`separation` applies; deleting `ℓ` turns the path through `ℓ` into the path ending at `c`.

Support bookkeeping: `PathDecomp.eq_of_mem_edges` (each edge lies on one path),
`Retract.delete_supp`, `PathDecomp.add_edge_supp` (copies of `Retract.delete` and
`PathDecomp.add_edge` with a vertex-set conclusion).
-/

open SimpleGraph

namespace Gallai

universe u v

section owner

variable {U : Type v} {K : SimpleGraph U}

/-- Each edge lies on exactly one path of a decomposition. -/
theorem PathDecomp.eq_of_mem_edges (D : PathDecomp K) {P Q : GPath K} (hP : P ∈ D.paths)
    (hQ : Q ∈ D.paths) {e : Sym2 U} (heP : e ∈ P.edges) (heQ : e ∈ Q.edges) : P = Q := by
  have key : ∀ l : List (GPath K), (l.flatMap GPath.edges).Nodup → P ∈ l → Q ∈ l → P = Q := by
    intro l
    induction l with
    | nil => intro _ hP; simp at hP
    | cons R l ih =>
      intro hnd hP hQ
      rw [List.flatMap_cons, List.nodup_append] at hnd
      obtain ⟨-, hl, hdis⟩ := hnd
      rcases List.mem_cons.mp hP with rfl | hP' <;> rcases List.mem_cons.mp hQ with rfl | hQ'
      · rfl
      · exact absurd rfl (hdis e heP e (List.mem_flatMap.mpr ⟨Q, hQ', heQ⟩))
      · exact absurd rfl (hdis e heQ e (List.mem_flatMap.mpr ⟨P, hP', heP⟩))
      · exact ih hl hP' hQ'
  exact key D.paths D.nodup_edges hP hQ

end owner

namespace Retract

variable {U : Type v} {V : Type u} {K : SimpleGraph U} {G : SimpleGraph V} (R : Retract K G)

/-- **Deleting the non-kept vertices**, with control of the end counts. -/
theorem delete_supp [DecidableEq U] [DecidableEq V] (D : PathDecomp K)
    (hD : ∀ P ∈ D.paths, ∀ x ∈ P.walk.support, R.kept x = false → x = P.src ∨ x = P.tgt) :
    ∃ D' : PathDecomp G, (∀ v,
      ((∀ e ∈ K.edgeSet, bothKept R.kept e = false → R.ι v ∉ e) →
        D'.ends v = D.ends (R.ι v)) ∧
      ((∀ e₁ ∈ K.edgeSet, ∀ e₂ ∈ K.edgeSet, bothKept R.kept e₁ = false →
          bothKept R.kept e₂ = false → R.ι v ∈ e₁ → R.ι v ∈ e₂ → e₁ = e₂) →
        D'.ends v ≤ D.ends (R.ι v) + 1)) ∧
      ∀ Q' ∈ D'.paths, ∃ P ∈ D.paths, (∀ x ∈ Q'.walk.support, R.ι x ∈ P.walk.support) ∧
        Q'.edges.Perm ((P.edges.filter (bothKept R.kept)).map (Sym2.map R.f)) := by
  obtain ⟨D', -, hpieces, hends⟩ := D.project_full R.f (bothKept R.kept) _ R.injOn R.hT R.hcov
    (fun P hP => R.hasPiece P (hD P hP))
  refine ⟨D', fun v => ?_, ?_⟩
  · let c : GPath K → ℕ := fun P =>
      (P.edges.filter (bothKept R.kept)).countP (fun e => decide (v ∈ e.map R.f))
    let k : GPath K → ℕ := fun P =>
      (P.edges.filter (fun e => !bothKept R.kept e)).countP (fun e => decide (R.ι v ∈ e))
    have hid : ∀ P : GPath K, c P + k P = P.incid (R.ι v) := fun P => R.count_split v P.edges
    have hD' : D'.ends v = (D.paths.map (fun P => if c P = 1 then 1 else 0)).sum := by
      rw [hends v]
      congr 1
      apply List.map_congr_left
      intro P _
      simp only [c, List.countP_map, Function.comp_def]
    have hDι : D.ends (R.ι v) = (D.paths.map (fun P => if c P + k P = 1 then 1 else 0)).sum := by
      unfold PathDecomp.ends
      congr 1
      apply List.map_congr_left
      intro P _
      rw [GPath.endsAt_eq_ite, hid]
    constructor
    · intro hno
      rw [hD', hDι]
      congr 1
      apply List.map_congr_left
      intro P _
      have : k P = 0 := by
        simp only [k]
        rw [List.countP_eq_zero]
        intro e he hve
        rw [List.mem_filter] at he
        have heK := P.walk.edges_subset_edgeSet he.1
        exact hno e heK (by simpa using he.2) (by simpa using hve)
      rw [this, add_zero]
    · intro hone
      rw [hD', hDι]
      have hk1 : (D.paths.map k).sum ≤ 1 := by
        have h1 : (D.paths.map k).sum = (D.paths.flatMap GPath.edges).countP
            (fun e => decide (R.ι v ∈ e) && !bothKept R.kept e) := by
          rw [List.countP_flatMap]
          congr 1
          apply List.map_congr_left
          intro P _
          simp only [k, List.countP_filter, Function.comp_apply]
        rw [h1]
        apply countP_le_one_of_nodup D.nodup_edges
        intro x hx y hy hpx hpy
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hpx hpy
        exact hone x ((D.covers x).2 hx) y ((D.covers y).2 hy) hpx.2 hpy.2 hpx.1 hpy.1
      calc (D.paths.map (fun P => if c P = 1 then 1 else 0)).sum
          ≤ (D.paths.map (fun P => (if c P + k P = 1 then 1 else 0) + k P)).sum :=
            sum_map_le_sum_map _ _ _ (fun P _ => by split_ifs <;> omega)
        _ = (D.paths.map (fun P => if c P + k P = 1 then 1 else 0)).sum + (D.paths.map k).sum :=
            sum_map_add' _ _ _
        _ ≤ _ := by omega

  · intro Q' hQ'
    obtain ⟨e'₀, he'₀⟩ := List.exists_mem_of_ne_nil _ Q'.edges_ne_nil
    have he'₀G : e'₀ ∈ G.edgeSet := (D'.covers e'₀).2 (List.mem_flatMap.mpr ⟨Q', hQ', he'₀⟩)
    obtain ⟨e₀, he₀K, hS₀, rfl⟩ := (R.hcov _).1 he'₀G
    obtain ⟨P, hP, he₀P⟩ := List.mem_flatMap.mp ((D.covers e₀).1 he₀K)
    have hany : P.edges.any (bothKept R.kept) = true := List.any_eq_true.mpr ⟨e₀, he₀P, hS₀⟩
    obtain ⟨Q, hQ, hperm⟩ := hpieces P hP hany
    have he₀Q : e₀.map R.f ∈ Q.edges :=
      hperm.mem_iff.mpr (List.mem_map_of_mem (List.mem_filter.mpr ⟨he₀P, hS₀⟩))
    have hQQ' : Q = Q' := D'.eq_of_mem_edges hQ hQ' he₀Q he'₀
    subst hQQ'
    refine ⟨P, hP, fun x hx => ?_, hperm⟩
    have hnil : ¬ Q.walk.Nil := fun h => by
      have := Q.pos; rw [← SimpleGraph.Walk.length_eq_zero_iff] at h; omega
    obtain ⟨e', he', hxe'⟩ := (Walk.mem_support_iff_exists_mem_edges_of_not_nil hnil).mp hx
    have he'' : e' ∈ (P.edges.filter (bothKept R.kept)).map (Sym2.map R.f) := hperm.mem_iff.mp he'
    obtain ⟨e, heP, rfl⟩ := List.mem_map.mp he''
    rw [List.mem_filter] at heP
    obtain ⟨y, hye, rfl⟩ := Sym2.mem_map.mp hxe'
    have hky := (bothKept_iff _ e).1 heP.2 y hye
    obtain ⟨b, rfl⟩ := (R.kept_iff y).1 hky
    rw [R.f_ι]
    exact Walk.mem_support_of_mem_edges heP.1 hye

end Retract

section addEdge

variable {W : Type u} [DecidableEq W]

theorem PathDecomp.add_edge_supp {W : Type u} [DecidableEq W] {G G' : SimpleGraph W} {a b : W}
    (hab : G.Adj a b) (hG' : ∀ e, e ∈ G'.edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(a, b))
    (D' : PathDecomp G') :
    ∃ D : PathDecomp G, (∀ w,
      D.ends w = D'.ends w + (if a = w then 1 else 0) + (if b = w then 1 else 0)) ∧
      ∀ Q ∈ D.paths, (∀ x ∈ Q.walk.support, x = a ∨ x = b) ∨
        ∃ Q' ∈ D'.paths, ∀ x ∈ Q.walk.support, x ∈ Q'.walk.support := by
  have h₁ : ∀ Q ∈ D'.paths, ∀ e ∈ Q.edges, e ∈ G.edgeSet := fun Q hQ e he =>
    ((hG' e).1 ((D'.covers e).2 (List.mem_flatMap.mpr ⟨Q, hQ, he⟩))).1
  let L := D'.paths.pmap (fun Q hQ => Q.transfer hQ) h₁ ++ [GPath.ofAdj hab]
  have hL : L.flatMap GPath.edges = D'.paths.flatMap GPath.edges ++ [s(a, b)] := by
    simp only [L, List.flatMap_append, flatMap_pmap_transfer, List.flatMap_cons,
      List.flatMap_nil, GPath.ofAdj_edges, List.append_nil]
  have hnd : (L.flatMap GPath.edges).Nodup := by
    rw [hL, List.nodup_append]
    refine ⟨D'.nodup_edges, List.nodup_singleton _, ?_⟩
    intro e he f hf hef
    rw [List.mem_singleton] at hf
    subst hf hef
    exact ((hG' _).1 ((D'.covers _).2 he)).2 rfl
  have hcov : ∀ e, e ∈ G.edgeSet ↔ e ∈ L.flatMap GPath.edges := by
    intro e
    rw [hL, List.mem_append, List.mem_singleton, ← D'.covers, hG']
    constructor
    · intro he
      by_cases h : e = s(a, b)
      · exact Or.inr h
      · exact Or.inl ⟨he, h⟩
    · rintro (⟨he, -⟩ | rfl)
      · exact he
      · exact hab
  refine ⟨⟨L, hnd, hcov⟩, fun w => ?_, ?_⟩
  · unfold PathDecomp.ends
    simp only [L, List.map_append, List.sum_append, sum_endsAt_pmap_transfer, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have : (GPath.ofAdj hab).endsAt w = (if a = w then 1 else 0) + (if b = w then 1 else 0) := rfl
    rw [this]
    omega
  · intro Q hQ
    change Q ∈ L at hQ
    simp only [L, List.mem_append, List.mem_pmap, List.mem_singleton] at hQ
    rcases hQ with ⟨Q', hQ', rfl⟩ | rfl
    · exact Or.inr ⟨Q', hQ', fun x hx => by rwa [GPath.transfer_support] at hx⟩
    · left
      intro x hx
      have : x ∈ (Walk.cons hab Walk.nil : G.Walk a b).support := hx
      simpa using this

end addEdge

section separation

variable {W : Type u}

/-- No path of `D` contains both `c` and `a`. -/
def Separates {G : SimpleGraph W} (D : PathDecomp G) (c a : W) : Prop :=
  ∀ P ∈ D.paths, ¬ (c ∈ P.walk.support ∧ a ∈ P.walk.support)

/-- Every path of `D` meets `X` in at most one vertex. -/
def MeetsOnce {G : SimpleGraph W} (D : PathDecomp G) (X : Finset W) : Prop :=
  ∀ P ∈ D.paths, ∀ x ∈ X, ∀ y ∈ X, x ∈ P.walk.support → y ∈ P.walk.support → x = y

/-- The vertices of `X` are pairwise at distance at least three: no two are adjacent or have a
common neighbour. -/
def Packed (G : SimpleGraph W) (X : Finset W) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → ¬ G.Adj x y ∧ ∀ w, ¬ (G.Adj x w ∧ G.Adj w y)

/-- `c` and `a` are at distance at least three: distinct, non-adjacent, no common neighbour. -/
def FarApart (G : SimpleGraph W) (c a : W) : Prop :=
  c ≠ a ∧ ¬ G.Adj c a ∧ ∀ w, ¬ (G.Adj c w ∧ G.Adj w a)

theorem FarApart.mono {G H : SimpleGraph W} {c a : W} (h : FarApart G c a)
    (hle : ∀ x y, H.Adj x y → G.Adj x y) : FarApart H c a :=
  ⟨h.1, fun hca => h.2.1 (hle _ _ hca), fun w hw => h.2.2 w ⟨hle _ _ hw.1, hle _ _ hw.2⟩⟩

theorem Packed.mono {G H : SimpleGraph W} {X : Finset W} (h : Packed G X)
    (hle : ∀ x y, H.Adj x y → G.Adj x y) : Packed H X := fun x hx y hy hxy =>
  ⟨fun h' => (h x hx y hy hxy).1 (hle _ _ h'),
    fun w hw => (h x hx y hy hxy).2 w ⟨hle _ _ hw.1, hle _ _ hw.2⟩⟩

/-- `MeetsOnce` passes to a decomposition whose paths lie in old paths plus a vertex `g ∉ X`. -/
theorem meetsOnce_of_cover {G G' : SimpleGraph W} {D : PathDecomp G} {D' : PathDecomp G'}
    {X : Finset W} {g : W} (hg : g ∉ X) (hD' : MeetsOnce D' X)
    (hcov : ∀ Q ∈ D.paths, ∃ Q' ∈ D'.paths, ∀ x ∈ Q.walk.support, x ∈ Q'.walk.support ∨ x = g) :
    MeetsOnce D X := by
  intro Q hQ x hx y hy hxQ hyQ
  obtain ⟨Q', hQ', h⟩ := hcov Q hQ
  have hxg : x ≠ g := fun h' => hg (h' ▸ hx)
  have hyg : y ≠ g := fun h' => hg (h' ▸ hy)
  exact hD' Q' hQ' x hx y hy ((h x hxQ).resolve_right hxg) ((h y hyQ).resolve_right hyg)

/-- Separation passes to a decomposition whose paths lie in old paths plus a vertex `g ∉ {c, a}`. -/
theorem separates_of_cover {G G' : SimpleGraph W} {D : PathDecomp G} {D' : PathDecomp G'}
    {c a g : W} (hgc : g ≠ c) (hga : g ≠ a) (hD' : Separates D' c a)
    (hcov : ∀ Q ∈ D.paths, ∃ Q' ∈ D'.paths, ∀ x ∈ Q.walk.support, x ∈ Q'.walk.support ∨ x = g) :
    Separates D c a := by
  intro Q hQ ⟨hc, ha⟩
  obtain ⟨Q', hQ', h⟩ := hcov Q hQ
  exact hD' Q' hQ' ⟨(h c hc).resolve_right (Ne.symm hgc), (h a ha).resolve_right (Ne.symm hga)⟩

/-- The statement proved by strong induction on `n = ν(G)`. -/
def SepStrong (n : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (X : Finset W), (evenSet G).card ≤ 1 → Packed G X →
    (∑ w, G.degree w) + (if (evenSet G).card = 0 then 1 else 0) = n →
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ MeetsOnce D X

variable [Fintype W] [DecidableEq W]

omit [DecidableEq W] in
/-- A vertex of degree at least two has a neighbour outside a packed set `X`. -/
theorem exists_adj_not_mem {G : SimpleGraph W} [DecidableRel G.Adj] {X : Finset W} {z : W}
    (hX : Packed G X) (hz : 2 ≤ G.degree z) : ∃ u, G.Adj z u ∧ u ∉ X := by
  classical
  by_contra hno
  simp only [not_exists, not_and, not_not] at hno
  have h1 : 1 < (G.neighborFinset z).card := by rw [card_neighborFinset_eq_degree]; omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h1
  rw [mem_neighborFinset] at hp hq
  by_cases hzX : z ∈ X
  · exact (hX z hzX p (hno p hp) hp.ne).1 hp
  · exact (hX p (hno p hp) q (hno q hq) hpq).2 z ⟨hp.symm, hq⟩

/-- Case I: there is a vertex of positive even degree. -/
theorem sep_case_even {n : ℕ} (ih : ∀ m < n, SepStrong.{u} m)
    (G : SimpleGraph W) [DecidableRel G.Adj] {X : Finset W} (hev : (evenSet G).card ≤ 1)
    (hfar : Packed G X)
    (hn : (∑ w, G.degree w) + (if (evenSet G).card = 0 then 1 else 0) = n)
    {z : W} (hz : z ∈ evenSet G) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ MeetsOnce D X := by
  have hzd := mem_evenSet_iff.mp hz
  obtain ⟨u, hzu, huX⟩ := exists_adj_not_mem hfar (by omega : 2 ≤ G.degree z)
  have huz : G.Adj u z := hzu.symm
  have hne : u ≠ z := huz.ne
  have huniq : ∀ w ∈ evenSet G, w = z := fun w hw => Finset.card_le_one.mp hev w hw z hz
  have hdeg := delEdge_degree G huz
  have hupos : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).mpr ⟨z, huz⟩
  have huodd : G.degree u % 2 = 1 := by
    have : u ∉ evenSet G := fun h => hne (huniq u h)
    rw [mem_evenSet_iff] at this
    omega
  have hdu := hdeg u
  have hdz := hdeg z
  simp only [hne, hne.symm, ite_true, ite_false, add_zero] at hdu hdz
  have hev' : evenSet (delEdge G u z) ⊆ {u} := by
    intro w hw
    rw [Finset.mem_singleton]
    obtain ⟨hpos, heven⟩ := mem_evenSet_iff.mp hw
    by_contra hwu
    by_cases hwz : w = z
    · subst hwz
      omega
    · have h := hdeg w
      simp only [hwu, hwz, ite_false, add_zero] at h
      exact hwz (huniq w (mem_evenSet_iff.mpr ⟨h ▸ hpos, h ▸ heven⟩))
  have hcard' : (evenSet (delEdge G u z)).card ≤ 1 :=
    (Finset.card_le_card hev').trans (by simp)
  have hsum := delEdge_sum_degree G huz
  have hlt : (∑ w, (delEdge G u z).degree w) +
      (if (evenSet (delEdge G u z)).card = 0 then 1 else 0) < n := by
    have : (evenSet G).card ≠ 0 := Finset.card_ne_zero.mpr ⟨z, hz⟩
    simp only [this, ite_false, add_zero] at hn
    split_ifs <;> omega
  have hfar' : Packed (delEdge G u z) X := hfar.mono (fun _ _ h => h.1)
  obtain ⟨D', hD', hsep'⟩ := ih _ hlt W (delEdge G u z) X hcard' hfar' rfl
  have hD'z : D'.ends z = 1 := by rw [hD' z]; omega
  obtain ⟨D, -, hDu, hDz, hDo, hcov⟩ := fan_single_supp huz (delEdge_edgeSet G u z) D' (by
    rw [hD'z]
    have : Finset.univ.filter (fun w => (delEdge G u z).Adj u w ∧ D'.ends w = 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro w - ⟨hadj, h0⟩
      have hwu : w ≠ u := hadj.ne.symm
      have hpos : 0 < (delEdge G u z).degree w :=
        ((delEdge G u z).degree_pos_iff_exists_adj w).mpr ⟨u, hadj.symm⟩
      rw [hD' w] at h0
      exact hwu (Finset.mem_singleton.mp (hev' (mem_evenSet_iff.mpr ⟨hpos, h0⟩)))
    rw [this, Finset.card_empty]
    exact Nat.one_pos)
  refine ⟨D, fun w => ?_, meetsOnce_of_cover huX hsep' hcov⟩
  by_cases hwu : w = u
  · subst hwu
    rw [hDu, hD' w]
    omega
  · by_cases hwz : w = z
    · subst hwz
      omega
    · rw [hDo w hwu hwz, hD' w]
      have h := hdeg w
      simp only [hwu, hwz, ite_false, add_zero] at h
      rw [h]

/-- Case II: every vertex of positive degree is odd and some `x ∉ {c, a}` has degree `≥ 3`. -/
theorem sep_case_big {n : ℕ} (ih : ∀ m < n, SepStrong.{u} m)
    (G : SimpleGraph W) [DecidableRel G.Adj] {X : Finset W} (hfar : Packed G X)
    (hn : (∑ w, G.degree w) + (if (evenSet G).card = 0 then 1 else 0) = n)
    (hnone : ∀ z, z ∉ evenSet G) {x : W} (hxX : x ∉ X) (hx : 3 ≤ G.degree x) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ MeetsOnce D X := by
  obtain ⟨u, hxu⟩ := (G.degree_pos_iff_exists_adj x).mp (by omega)
  have hux : G.Adj u x := hxu.symm
  have hne : u ≠ x := hux.ne
  have hpar : ∀ w, 0 < G.degree w → G.degree w % 2 = 1 := fun w hw => by
    have := hnone w
    rw [mem_evenSet_iff] at this
    omega
  have hdeg := delEdge_degree G hux
  have hupos : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).mpr ⟨x, hux⟩
  have hdu := hdeg u
  have hdx := hdeg x
  simp only [hne, hne.symm, ite_true, ite_false, add_zero] at hdu hdx
  have hux_odd := hpar u hupos
  have hx_odd := hpar x (by omega)
  have hHsome : ∀ w, (apex (delEdge G u x) {u}).degree (some w) =
      (delEdge G u x).degree w + (if w = u then 1 else 0) := by
    intro w
    rw [apex_degree_some]
    simp [Finset.mem_singleton]
  have hHnone : (apex (delEdge G u x) {u}).degree none = 1 := by
    rw [apex_degree_none]; simp
  have hevH : evenSet (apex (delEdge G u x) {u}) ⊆ {some x} := by
    intro w hw
    rw [mem_evenSet_iff] at hw
    rw [Finset.mem_singleton]
    cases w with
    | none => rw [hHnone] at hw; omega
    | some y =>
      rw [hHsome] at hw
      by_contra hyx
      have hyx' : y ≠ x := fun h => hyx (h ▸ rfl)
      by_cases hyu : y = u
      · subst hyu
        simp only [ite_true] at hw
        omega
      · have h := hdeg y
        simp only [hyu, hyx', ite_false, add_zero] at h hw
        have := hpar y (h ▸ hw.1)
        omega
  have hxH : some x ∈ evenSet (apex (delEdge G u x) {u}) := by
    rw [mem_evenSet_iff, hHsome]
    simp only [hne.symm, ite_false, add_zero]
    omega
  have hcardH : (evenSet (apex (delEdge G u x) {u})).card ≤ 1 :=
    (Finset.card_le_card hevH).trans (by simp)
  have hsumH : ∑ w, (apex (delEdge G u x) {u}).degree w = ∑ w, G.degree w := by
    rw [Fintype.sum_option, hHnone, ← delEdge_sum_degree G hux]
    simp only [hHsome, Finset.sum_add_distrib]
    simp
    omega
  have hlt : (∑ w, (apex (delEdge G u x) {u}).degree w) +
      (if (evenSet (apex (delEdge G u x) {u})).card = 0 then 1 else 0) < n := by
    have h1 : (evenSet (apex (delEdge G u x) {u})).card ≠ 0 :=
      Finset.card_ne_zero.mpr ⟨_, hxH⟩
    have h2 : (evenSet G).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem hnone)
    simp only [h2, ite_true] at hn
    simp only [h1, ite_false, add_zero, hsumH]
    omega
  have hfarH : Packed (apex (delEdge G u x) {u}) (X.image some) := by
    intro p hp q hq hpq
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
    have hpq' : p' ≠ q' := fun h => hpq (h ▸ rfl)
    refine ⟨fun h => (hfar p' hp' q' hq' hpq').1 h.1, fun w hw => ?_⟩
    cases w with
    | none =>
      obtain ⟨h1, h2⟩ := hw
      rw [apex_adj_some_none, Finset.mem_singleton] at h1
      rw [apex_adj_none_some, Finset.mem_singleton] at h2
      exact hpq' (h1.trans h2.symm)
    | some w' => exact (hfar p' hp' q' hq' hpq').2 w' ⟨hw.1.1, hw.2.1⟩
  obtain ⟨DH, hDH, hsepH⟩ :=
    ih _ hlt (Option W) (apex (delEdge G u x) {u}) (X.image some) hcardH hfarH rfl
  -- delete the new leaf
  obtain ⟨D', hD', hcovD'⟩ := (apexRetract (delEdge G u x) {u} x).delete_supp DH (by
    intro P _ y hy hky
    cases y with
    | some _ => simp [apexRetract] at hky
    | none => exact (P.end_of_pendant apex_none_pendant hy).imp Eq.symm Eq.symm)
  have hsep' : MeetsOnce D' X := by
    intro Q hQ p hp q hq hpQ hqQ
    obtain ⟨P, hP, hPs, -⟩ := hcovD' Q hQ
    exact Option.some.inj (hsepH P hP (some p) (Finset.mem_image_of_mem _ hp) (some q)
      (Finset.mem_image_of_mem _ hq) (hPs p hpQ) (hPs q hqQ))
  have hD'w : ∀ w, w ≠ u → D'.ends w = (delEdge G u x).degree w % 2 := by
    intro w hwu
    rw [(hD' w).1 (fun e he hk hwe => hwu (Finset.mem_singleton.mp (apex_nonkept he hk hwe).2))]
    change DH.ends (some w) = _
    rw [hDH, hHsome]
    simp [hwu]
  have hD'u : D'.ends u = 0 ∨ D'.ends u = 2 := by
    have hle := (hD' u).2 (fun e₁ he₁ e₂ he₂ hk₁ hk₂ hv₁ hv₂ => by
      rw [(apex_nonkept he₁ hk₁ hv₁).1, (apex_nonkept he₂ hk₂ hv₂).1])
    change D'.ends u ≤ DH.ends (some u) + 1 at hle
    rw [hDH, hHsome] at hle
    simp only [ite_true] at hle
    have hp := D'.ends_mod_two u
    omega
  rcases hD'u with h0 | h2
  · -- `u` has no end: add `ux` as a new path
    obtain ⟨D, hD, hcovD⟩ := PathDecomp.add_edge_supp hux (delEdge_edgeSet G u x) D'
    refine ⟨D, fun w => ?_, ?_⟩
    · rw [hD w]
      by_cases hwu : w = u
      · subst hwu
        simp only [h0, Ne.symm hne, ite_true, ite_false]
        omega
      · rw [hD'w w hwu]
        by_cases hwx : w = x
        · subst hwx
          simp only [Ne.symm hwu, ite_true, ite_false]
          omega
        · have h := hdeg w
          simp only [hwu, hwx, Ne.symm hwu, Ne.symm hwx, ite_false, add_zero] at h ⊢
          rw [h]
    · intro Q hQ p hp q hq hpQ hqQ
      rcases hcovD Q hQ with hsmall | ⟨Q', hQ', hs⟩
      · rcases hsmall p hpQ with h1 | h1
        · rcases hsmall q hqQ with h2 | h2
          · exact h1.trans h2.symm
          · exact absurd (h2 ▸ hq) hxX
        · exact absurd (h1 ▸ hp) hxX
      · exact hsep' Q' hQ' p hp q hq (hs p hpQ) (hs q hqQ)
  · -- `u` has two ends: Fan's transfer `u → x`
    have hG'x : ∀ e, e ∈ (delEdge G u x).edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(x, u) := by
      intro e
      rw [delEdge_edgeSet, Sym2.eq_swap]
    obtain ⟨D, -, hDx, hDu, hDo, hcov⟩ := fan_single_supp hxu hG'x D' (by
      rw [h2]
      have : Finset.univ.filter (fun w => (delEdge G u x).Adj x w ∧ D'.ends w = 0) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        rintro w - ⟨hadj, h0⟩
        by_cases hwu : w = u
        · subst hwu; omega
        · have hwx : w ≠ x := hadj.ne.symm
          have hpos : 0 < (delEdge G u x).degree w :=
            ((delEdge G u x).degree_pos_iff_exists_adj w).mpr ⟨x, hadj.symm⟩
          have h := hdeg w
          simp only [hwu, hwx, ite_false, add_zero] at h
          rw [hD'w w hwu, h] at h0
          have := hpar w (h ▸ hpos)
          omega
      rw [this, Finset.card_empty]
      omega)
    refine ⟨D, fun w => ?_, meetsOnce_of_cover hxX hsep' hcov⟩
    by_cases hwx : w = x
    · subst hwx
      rw [hDx, hD'w w (Ne.symm hne)]
      omega
    · by_cases hwu : w = u
      · subst hwu
        omega
      · rw [hDo w hwx hwu, hD'w w hwu]
        have h := hdeg w
        simp only [hwu, hwx, ite_false, add_zero] at h
        rw [h]

/-- Case III: all degrees odd or zero, every vertex outside `{c, a}` has degree `< 3`, and some
vertex `v ∉ {c, a}` has positive degree (so it is a leaf). -/
theorem sep_case_leaf {n : ℕ} (ih : ∀ m < n, SepStrong.{u} m)
    (G : SimpleGraph W) [DecidableRel G.Adj] {X : Finset W} (hfar : Packed G X)
    (hn : (∑ w, G.degree w) + (if (evenSet G).card = 0 then 1 else 0) = n)
    (hnone : ∀ z, z ∉ evenSet G) (hsmall : ∀ x, x ∉ X → G.degree x < 3)
    {v : W} (hvX : v ∉ X) (hv : 0 < G.degree v) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ MeetsOnce D X := by
  obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp hv
  have hne : v ≠ w := hvw.ne
  have hpar : ∀ y, 0 < G.degree y → G.degree y % 2 = 1 := fun y hy => by
    have := hnone y
    rw [mem_evenSet_iff] at this
    omega
  have hwpos : 0 < G.degree w := (G.degree_pos_iff_exists_adj w).mpr ⟨v, hvw.symm⟩
  have hdv1 : G.degree v = 1 := by have := hpar v hv; have := hsmall v hvX; omega
  have hdwo := hpar w hwpos
  have hdeg := delEdge_degree G hvw
  have hdv := hdeg v
  have hdw := hdeg w
  simp only [hne, hne.symm, ite_true, ite_false, add_zero] at hdv hdw
  have hev' : evenSet (delEdge G v w) ⊆ {w} := by
    intro y hy
    rw [Finset.mem_singleton]
    obtain ⟨hpos, heven⟩ := mem_evenSet_iff.mp hy
    by_contra hyw
    by_cases hyv : y = v
    · subst hyv; omega
    · have h := hdeg y
      simp only [hyv, hyw, ite_false, add_zero] at h
      have := hpar y (h ▸ hpos)
      omega
  have hcard' : (evenSet (delEdge G v w)).card ≤ 1 :=
    (Finset.card_le_card hev').trans (by simp)
  have hsum := delEdge_sum_degree G hvw
  have hlt : (∑ y, (delEdge G v w).degree y) +
      (if (evenSet (delEdge G v w)).card = 0 then 1 else 0) < n := by
    have h2 : (evenSet G).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem hnone)
    simp only [h2, ite_true] at hn
    split_ifs <;> omega
  have hfar' : Packed (delEdge G v w) X := hfar.mono (fun _ _ h => h.1)
  obtain ⟨D', hD', hsep'⟩ := ih _ hlt W (delEdge G v w) X hcard' hfar' rfl
  obtain ⟨D, hD, hcovD⟩ := PathDecomp.add_edge_supp hvw (delEdge_edgeSet G v w) D'
  refine ⟨D, fun y => ?_, ?_⟩
  · rw [hD y, hD' y]
    by_cases hyv : y = v
    · subst hyv
      simp only [Ne.symm hne, ite_true, ite_false]
      omega
    · by_cases hyw : y = w
      · subst hyw
        simp only [Ne.symm hyv, ite_true, ite_false]
        omega
      · have h := hdeg y
        simp only [hyv, hyw, Ne.symm hyv, Ne.symm hyw, ite_false, add_zero] at h ⊢
        rw [h]
  · intro Q hQ p hp q hq hpQ hqQ
    rcases hcovD Q hQ with hsm | ⟨Q', hQ', hs⟩
    · rcases hsm p hpQ with h1 | h1
      · exact absurd (h1 ▸ hp) hvX
      · rcases hsm q hqQ with h2 | h2
        · exact absurd (h2 ▸ hq) hvX
        · exact h1.trans h2.symm
    · exact hsep' Q' hQ' p hp q hq (hs p hpQ) (hs q hqQ)

/-- Case IV: no vertex outside `X` has positive degree; then there are no edges. -/
theorem sep_case_empty (G : SimpleGraph W) [DecidableRel G.Adj] {X : Finset W} (hfar : Packed G X)
    (hzero : ∀ x, x ∉ X → G.degree x = 0) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ MeetsOnce D X := by
  have hnoadj : ∀ x y, ¬ G.Adj x y := by
    intro x y hxy
    have hx : 0 < G.degree x := (G.degree_pos_iff_exists_adj x).mpr ⟨y, hxy⟩
    have hy : 0 < G.degree y := (G.degree_pos_iff_exists_adj y).mpr ⟨x, hxy.symm⟩
    by_cases hxX : x ∈ X
    · by_cases hyX : y ∈ X
      · exact (hfar x hxX y hyX hxy.ne).1 hxy
      · have := hzero y hyX; omega
    · have := hzero x hxX; omega
  have hdeg0 : ∀ x, G.degree x = 0 := fun x => by
    rcases Nat.eq_zero_or_pos (G.degree x) with h | h
    · exact h
    · obtain ⟨y, hxy⟩ := (G.degree_pos_iff_exists_adj x).mp h
      exact absurd hxy (hnoadj x y)
  obtain ⟨D, hD⟩ := lovasz_case_empty G hdeg0
  refine ⟨D, hD, fun P hP _ _ _ _ _ _ => ?_⟩
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ P.edges_ne_nil
  have heG := (D.covers e).2 (List.mem_flatMap.mpr ⟨P, hP, he⟩)
  induction e using Sym2.inductionOn with
  | hf x y => exact absurd heG (hnoadj x y)

theorem sep_strong (n : ℕ) : SepStrong.{u} n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W _ _ G _ X hev hfar hn
  by_cases hz : ∃ z, z ∈ evenSet G
  · obtain ⟨z, hz⟩ := hz
    exact sep_case_even ih G hev hfar hn hz
  · simp only [not_exists] at hz
    by_cases hx : ∃ x, x ∉ X ∧ 3 ≤ G.degree x
    · obtain ⟨x, hxX, hx⟩ := hx
      exact sep_case_big ih G hfar hn hz hxX hx
    · have hsmall : ∀ x, x ∉ X → G.degree x < 3 := fun x hxX => by
        by_contra h
        exact hx ⟨x, hxX, by omega⟩
      by_cases hv : ∃ v, v ∉ X ∧ 0 < G.degree v
      · obtain ⟨v, hvX, hv⟩ := hv
        exact sep_case_leaf ih G hfar hn hz hsmall hvX hv
      · have hzero : ∀ x, x ∉ X → G.degree x = 0 := fun x hxX => by
          by_contra h
          exact hv ⟨x, hxX, Nat.pos_of_ne_zero h⟩
        exact sep_case_empty G hfar hzero

end separation

/-- **Separation theorem, set form.** If `G` has at most one vertex of positive even degree and
the vertices of `X` are pairwise at distance at least three, then `G` has a decomposition into
paths with `ends v = deg v mod 2` for all `v`, in which every path meets `X` at most once. -/
theorem separation_set {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1) {X : Finset W} (hX : Packed G X) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ MeetsOnce D X :=
  sep_strong _ W G X hev hX rfl

/-- **Separation theorem.** If `G` has at most one vertex of positive even degree and `c`, `a`
are distinct, non-adjacent and have no common neighbour, then `G` has a decomposition into paths
with `ends v = deg v mod 2` for all `v`, in which no path contains both `c` and `a`. -/
theorem separation {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1) {c a : W} (hfar : FarApart G c a) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ Separates D c a := by
  have hX : Packed G {c, a} := by
    intro x hx y hy hxy
    rw [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact ⟨hfar.2.1, hfar.2.2⟩
    · exact ⟨fun h => hfar.2.1 h.symm, fun w hw => hfar.2.2 w ⟨hw.2.symm, hw.1.symm⟩⟩
    · exact absurd rfl hxy
  obtain ⟨D, hD, hm⟩ := separation_set G hev hX
  exact ⟨D, hD, fun P hP ⟨hc, ha⟩ => hfar.1 (hm P hP c (by simp) a (by simp) hc ha)⟩

/-- **`L₁` at distance three.** In a graph with at most one vertex of positive even degree, if
`c, a` are distinct, non-adjacent and have no common neighbour, some Lovász decomposition has
every path ending at `c` avoiding `a` (and every path ending at `a` avoiding `c`). -/
theorem lovasz_avoid {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1) {c a : W} (hfar : FarApart G c a) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∀ P ∈ D.paths, (P.src = c ∨ P.tgt = c) → a ∉ P.walk.support := by
  obtain ⟨D, hD, hsep⟩ := separation G hev hfar
  refine ⟨D, hD, fun P hP hend ha => hsep P hP ⟨?_, ha⟩⟩
  rcases hend with h | h
  · rw [← h]; exact P.walk.start_mem_support
  · rw [← h]; exact P.walk.end_mem_support

/-- **`L₁`, set form** (route-descent manuscript, Theorem "L₁"). In a graph with no vertex of
positive even degree, let `c` have odd degree and let `Y` be a packed set containing neither `c` nor a
neighbour of `c`. Then some Lovász decomposition has every path meeting `Y` at most once and every
path ending at `c` disjoint from `Y`.

Proof: attach a leaf `ℓ = none` at `c` (the apex graph on `{c}`). There `c` is the only vertex of
positive even degree, and `{ℓ} ∪ Y` is packed, so `separation_set` applies. Delete `ℓ`. A path ending
at `c` is the kept part of a path `P` of the leaf graph; if it met `Y`, then `P` would avoid `ℓ`, so
all of `P` is kept and `P` itself would end at `c`, which has no end in the leaf graph. -/
theorem lovasz_avoid_set {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (hev : (evenSet G).card = 0) {c : W} (hc : G.degree c % 2 = 1)
    {Y : Finset W} (hY : Packed G Y) (hYc : ∀ y ∈ Y, y ≠ c ∧ ¬ G.Adj c y) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ MeetsOnce D Y ∧
      ∀ P ∈ D.paths, (P.src = c ∨ P.tgt = c) → ∀ y ∈ Y, y ∉ P.walk.support := by
  classical
  have hHsome : ∀ w, (apex G {c}).degree (some w) = G.degree w + (if w = c then 1 else 0) := by
    intro w; rw [apex_degree_some]; simp [Finset.mem_singleton]
  have hHnone : (apex G {c}).degree none = 1 := by rw [apex_degree_none]; simp
  have hnoev : ∀ w, w ∉ evenSet G := fun w hw => by
    rw [Finset.card_eq_zero] at hev; rw [hev] at hw; simp at hw
  have hpar : ∀ w, 0 < G.degree w → G.degree w % 2 = 1 := fun w hw => by
    have := hnoev w; rw [mem_evenSet_iff] at this; omega
  have hevH : evenSet (apex G {c}) ⊆ {some c} := by
    intro w hw
    rw [mem_evenSet_iff] at hw
    rw [Finset.mem_singleton]
    cases w with
    | none => rw [hHnone] at hw; omega
    | some y =>
      rw [hHsome] at hw
      by_cases hyc : y = c
      · rw [hyc]
      · simp only [hyc, ite_false, add_zero] at hw
        have := hpar y hw.1
        omega
  have hcardH : (evenSet (apex G {c})).card ≤ 1 := (Finset.card_le_card hevH).trans (by simp)
  -- the leaf together with `Y` is packed
  have hnone_far : ∀ q ∈ Y, ¬ (apex G {c}).Adj none (some q) ∧
      ∀ w, ¬ ((apex G {c}).Adj none w ∧ (apex G {c}).Adj w (some q)) := by
    intro q hq
    refine ⟨fun h => (hYc q hq).1 ?_, fun w hw => ?_⟩
    · rw [apex_adj_none_some, Finset.mem_singleton] at h; exact h
    · cases w with
      | none => exact apex_not_adj_none_none hw.1
      | some w' =>
        obtain ⟨h1, h2⟩ := hw
        rw [apex_adj_none_some, Finset.mem_singleton] at h1
        subst h1
        exact (hYc q hq).2 h2
  have hfar : Packed (apex G {c}) (insert none (Y.image some)) := by
    intro x hx y hy hxy
    rw [Finset.mem_insert] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact absurd rfl hxy
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
      exact hnone_far q hq
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨h1, h2⟩ := hnone_far p hp
      exact ⟨fun h => h1 h.symm, fun w hw => h2 w ⟨hw.2.symm, hw.1.symm⟩⟩
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
      have hpq : p ≠ q := fun h => hxy (h ▸ rfl)
      refine ⟨fun h => (hY p hp q hq hpq).1 h, fun w hw => ?_⟩
      cases w with
      | none =>
        obtain ⟨h1, -⟩ := hw
        rw [apex_adj_some_none, Finset.mem_singleton] at h1
        exact (hYc p hp).1 h1
      | some w' => exact (hY p hp q hq hpq).2 w' ⟨hw.1, hw.2⟩
  obtain ⟨DH, hDH, hsep⟩ := separation_set (apex G {c}) hcardH hfar
  obtain ⟨D, hD, hcov⟩ := (apexRetract G {c} c).delete_supp DH (by
    intro P _ y hy hky
    cases y with
    | some _ => simp [apexRetract] at hky
    | none => exact (P.end_of_pendant apex_none_pendant hy).imp Eq.symm Eq.symm)
  have hDc0 : DH.ends (some c) = 0 := by
    rw [hDH, hHsome]; simp only [ite_true]; omega
  have hmemX : ∀ q ∈ Y, some q ∈ insert none (Y.image some) := fun q hq =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hq)
  refine ⟨D, fun w => ?_, ?_, ?_⟩
  · by_cases hwc : w = c
    · subst hwc
      have hle := (hD w).2 (fun e₁ he₁ e₂ he₂ hk₁ hk₂ hv₁ hv₂ => by
        rw [(apex_nonkept he₁ hk₁ hv₁).1, (apex_nonkept he₂ hk₂ hv₂).1])
      change D.ends w ≤ DH.ends (some w) + 1 at hle
      have hp := D.ends_mod_two w
      rw [hc] at hp ⊢
      omega
    · rw [(hD w).1 (fun e he hk hwe => hwc (Finset.mem_singleton.mp (apex_nonkept he hk hwe).2))]
      change DH.ends (some w) = _
      rw [hDH, hHsome]
      simp [hwc]
  · intro Q hQ p hp q hq hpQ hqQ
    obtain ⟨P, hP, hPs, -⟩ := hcov Q hQ
    exact Option.some.inj (hsep P hP (some p) (hmemX p hp) (some q) (hmemX q hq)
      (hPs p hpQ) (hPs q hqQ))
  · intro Q hQ hend y hy hyQ
    obtain ⟨P, hP, hPs, hperm⟩ := hcov Q hQ
    have hyP : some y ∈ P.walk.support := hPs y hyQ
    have hnoneP : none ∉ P.walk.support := fun h =>
      absurd (hsep P hP none (Finset.mem_insert_self _ _) (some y) (hmemX y hy) h hyP)
        (by simp)
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

/-- **`L₁`** (route-descent manuscript, Theorem "L₁", the case `Y = {a}`). In a graph with no vertex
of positive even degree, let `c` have odd degree and let `a ≠ c` be non-adjacent to `c`. Then some
Lovász decomposition has every path ending at `c` avoiding `a`. -/
theorem lovasz_avoid_nonadj {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (hev : (evenSet G).card = 0) {c a : W} (hc : G.degree c % 2 = 1)
    (hca : c ≠ a) (hadj : ¬ G.Adj c a) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∀ P ∈ D.paths, (P.src = c ∨ P.tgt = c) → a ∉ P.walk.support := by
  have hY : Packed G {a} := by
    intro x hx y hy hxy
    rw [Finset.mem_singleton] at hx hy
    exact absurd (hx.trans hy.symm) hxy
  obtain ⟨D, hD, -, hav⟩ := lovasz_avoid_set G hev hc hY (fun y hy => by
    rw [Finset.mem_singleton] at hy; subst hy; exact ⟨Ne.symm hca, hadj⟩)
  exact ⟨D, hD, fun P hP hend => hav P hP hend a (Finset.mem_singleton_self a)⟩

end Gallai
