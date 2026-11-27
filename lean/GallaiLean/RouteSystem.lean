import GallaiLean.RouteDescent
import GallaiLean.FanSupport

/-!
# Route systems: route-respecting realisations from compatible decompositions

Route-descent manuscript, Proposition "rr" (the direction used for TRC).

Let a pairing of the even vertices be routed by edge-disjoint paths, and let `M` be a transversal.
Orient each route from its *tail* (outside `M`) to its *head* (in `M`), and let `F` be `G` minus all
route edges. A decomposition `D` of `F` is **compatible** (`Compatible`) if
* (RR1) a path with an end at a tail `c` meets the route of `c` only in `c`, and
* (RR2) a path whose two ends are tails `c, c'` has the routes of `c` and `c'` vertex-disjoint.

**Theorem** (`append_routes`, `realisable_of_compatible`). If every vertex is an end of at most
one path of `D`, every tail is an end, and `D` is compatible, then appending every route at its tail
gives a realisation of `M` in `G`.

So the conjecture RR of the manuscript (compatible Lovász decompositions exist) implies TRC, and
hence Gallai's conjecture (`gallai_of_routeRR`).

The proof appends the routes one at a time by `PathDecomp.route_append_cls`, a form of
`route_append` that lists the paths of the new decomposition. Compatibility passes to the new
decomposition: the new path `Q ∪ R` ends at a head, which is not a tail, and at the other end of `Q`,
where (RR1) for `Q` and (RR2) for `Q` give (RR1) for `Q ∪ R`.

The hypothesis "at most one end everywhere" is equivalent to `D` being a Lovász decomposition of
`F`, by the parity lemma.
-/

open SimpleGraph

namespace Gallai

universe u

section appendCls

variable {U : Type u} [DecidableEq U]

/-- Two graphs with the same edges have the same decompositions. -/
theorem PathDecomp.congrGraph {K G : SimpleGraph U} (D : PathDecomp K)
    (h : ∀ e, e ∈ K.edgeSet ↔ e ∈ G.edgeSet) :
    ∃ D' : PathDecomp G, ∀ w, D'.ends w = D.ends w := by
  have H : ∀ Q ∈ D.paths, ∀ e ∈ Q.edges, e ∈ G.edgeSet := fun Q hQ e he =>
    (h e).1 ((D.covers e).2 (List.mem_flatMap.mpr ⟨Q, hQ, he⟩))
  have hflat : (D.paths.pmap (fun Q hQ => Q.transfer hQ) H).flatMap GPath.edges =
      D.paths.flatMap GPath.edges := flatMap_pmap_transfer _ _
  refine ⟨⟨D.paths.pmap (fun Q hQ => Q.transfer hQ) H, by rw [hflat]; exact D.nodup_edges,
    fun e => by rw [hflat, ← D.covers e]; exact (h e).symm⟩, fun w => ?_⟩
  exact sum_endsAt_pmap_transfer _ _ w

/-- **Appending a route**, with the list of new paths. As `PathDecomp.route_append`; moreover every
path of the new decomposition is either a copy (same ends, same vertex set) of a path of `D'`, or the
new path `Q ∪ R`. That path ends at `a`, starts at the end of `Q` other than `c`, and has vertex set
`V(Q) ∪ V(R)`. -/
theorem PathDecomp.route_append_cls {G K : SimpleGraph U} {R : GPath G} {a c : U}
    (hRs : R.src = c) (hRt : R.tgt = a)
    (hK : ∀ e, e ∈ K.edgeSet ↔ e ∈ G.edgeSet ∧ e ∉ R.edges)
    (D' : PathDecomp K) {Q : GPath K} (hQ : Q ∈ D'.paths) (hQc : Q.src = c ∨ Q.tgt = c)
    (hdisj : ∀ x ∈ Q.walk.support, x ∈ R.walk.support → x = c) :
    ∃ D : PathDecomp G,
      (∀ w, D.ends w + (if c = w then 1 else 0) = D'.ends w + (if a = w then 1 else 0)) ∧
      ∀ T ∈ D.paths, (∃ Q' ∈ D'.paths, T.src = Q'.src ∧ T.tgt = Q'.tgt ∧
          T.walk.support = Q'.walk.support) ∨
        (T.tgt = a ∧ T.src ≠ c ∧ (T.src = Q.src ∨ T.src = Q.tgt) ∧
          ∀ x, x ∈ T.walk.support ↔ x ∈ Q.walk.support ∨ x ∈ R.walk.support) := by
  obtain ⟨Q₁, hQ₁s, hQ₁e, hQ₁ends, hQ₁supp⟩ := Q.exists_orient hQc
  have hKG : ∀ e ∈ Q₁.walk.reverse.edges, e ∈ G.edgeSet := by
    intro e he
    rw [Walk.edges_reverse, List.mem_reverse] at he
    exact ((hK e).1 (Q₁.walk.edges_subset_edgeSet he)).1
  let A : G.Walk Q₁.tgt c := (Q₁.walk.reverse.transfer G hKG).copy rfl hQ₁s
  let B : G.Walk c a := R.walk.copy hRs hRt
  have hAsupp : ∀ x, x ∈ A.support ↔ x ∈ Q.walk.support := by
    intro x
    simp only [A, Walk.support_copy, Walk.support_transfer, Walk.support_reverse, List.mem_reverse]
    exact hQ₁supp x
  have hBsupp : B.support = R.walk.support := by simp [B]
  have hAedges : A.edges = Q₁.edges.reverse := by
    simp [A, GPath.edges, Walk.edges_copy, Walk.edges_transfer, Walk.edges_reverse]
  have hBedges : B.edges = R.edges := by simp [B, GPath.edges]
  have hWpath : (A.append B).IsPath := by
    rw [Walk.isPath_append]
    refine ⟨?_, ?_, ?_⟩
    · simp only [A, Walk.isPath_copy]
      exact (Walk.isPath_transfer _).mpr Q₁.isPath.reverse
    · have hB : B.IsPath := by simp only [B, Walk.isPath_copy]; exact R.isPath
      exact hB.tail
    · intro x hxA hxB
      have hBnd : B.support.Nodup :=
        (Walk.isPath_def _).mp (by simp only [B, Walk.isPath_copy]; exact R.isPath)
      have hxc : x ≠ c := by
        rintro rfl
        have hsc : ∀ {u v : U} (p : G.Walk u v), p.support = u :: p.support.tail := by
          intro u v p; cases p <;> rfl
        rw [hsc B] at hBnd
        exact (List.nodup_cons.mp hBnd).1 hxB
      have hxR : x ∈ R.walk.support := by
        rw [← hBsupp]; exact List.mem_of_mem_tail hxB
      exact hxc (hdisj x ((hAsupp x).1 hxA) hxR)
  have hpos : 0 < (A.append B).length := by
    rw [Walk.length_append]
    have : 0 < B.length := by simp only [B, Walk.length_copy]; exact R.pos
    omega
  let P' : GPath G := ⟨Q₁.tgt, a, A.append B, hWpath, hpos⟩
  have hP'edges : P'.edges = Q₁.edges.reverse ++ R.edges := by
    show (A.append B).edges = _
    rw [Walk.edges_append, hAedges, hBedges]
  have hmemP' : ∀ e, e ∈ P'.edges ↔ e ∈ Q.edges ∨ e ∈ R.edges := by
    intro e
    rw [hP'edges, List.mem_append, List.mem_reverse, hQ₁e.mem_iff]
  obtain ⟨D, -, -, hends, -, hcls⟩ := D'.replace_supp hQ P' (by
      intro e
      rw [hmemP' e]
      constructor
      · intro he
        by_cases heR : e ∈ R.edges
        · exact Or.inr (Or.inr heR)
        · by_cases heQ : e ∈ Q.edges
          · exact Or.inr (Or.inl heQ)
          · exact Or.inl ⟨(hK e).2 ⟨he, heR⟩, heQ⟩
      · rintro (⟨he, -⟩ | heQ | heR)
        · exact ((hK e).1 he).1
        · exact ((hK e).1 (Q.walk.edges_subset_edgeSet heQ)).1
        · exact R.walk.edges_subset_edgeSet heR)
    (by
      intro e he
      rcases (hmemP' e).1 he with heQ | heR
      · exact Or.inl heQ
      · exact Or.inr (fun hk => ((hK e).1 hk).2 heR))
  refine ⟨D, fun w => ?_, fun T hT => ?_⟩
  · have h1 := hends w
    have h2 : P'.endsAt w = (if Q₁.tgt = w then 1 else 0) + (if a = w then 1 else 0) := rfl
    have h3 : Q.endsAt w = (if c = w then 1 else 0) + (if Q₁.tgt = w then 1 else 0) := by
      rw [← hQ₁ends w]; simp only [GPath.endsAt, hQ₁s]
    omega
  · rcases hcls T hT with rfl | ⟨Q', hQ', hs, ht, hsupp⟩
    · right
      refine ⟨rfl, fun h => Q₁.src_ne_tgt (hQ₁s.trans h.symm), ?_, fun x => ?_⟩
      · by_contra hno
        push_neg at hno
        have h1 : 1 ≤ Q₁.endsAt Q₁.tgt := by unfold GPath.endsAt; rw [if_pos rfl]; omega
        have h2 : Q.endsAt Q₁.tgt = 0 := by
          have hn1 : ¬ Q.src = Q₁.tgt := fun h => hno.1 h.symm
          have hn2 : ¬ Q.tgt = Q₁.tgt := fun h => hno.2 h.symm
          unfold GPath.endsAt; rw [if_neg hn1, if_neg hn2]
        have := hQ₁ends Q₁.tgt
        omega
      · show x ∈ (A.append B).support ↔ _
        rw [Walk.mem_support_append_iff, hAsupp, hBsupp]
    · exact Or.inl ⟨Q', hQ', hs, ht, hsupp⟩

end appendCls

section routes

variable {U : Type u} [DecidableEq U]

/-- `G` with the edges of the paths of `L` removed. -/
def delPaths (G : SimpleGraph U) (L : List (GPath G)) : SimpleGraph U where
  Adj x y := G.Adj x y ∧ ∀ R ∈ L, s(x, y) ∉ R.edges
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun R hR he => h.2 R hR (by rw [Sym2.eq_swap]; exact he)⟩⟩
  loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩

theorem delPaths_edgeSet (G : SimpleGraph U) (L : List (GPath G)) (e : Sym2 U) :
    e ∈ (delPaths G L).edgeSet ↔ e ∈ G.edgeSet ∧ ∀ R ∈ L, e ∉ R.edges := by
  induction e using Sym2.inductionOn with
  | hf x y => exact Iff.rfl

/-- A decomposition `D` is **compatible** with the oriented routes `L` (each route `R` runs from its
tail `R.src` to its head `R.tgt`): (RR1) a path with an end at a tail meets that route only in the
tail; (RR2) a path whose ends are the tails of two routes has the two routes vertex-disjoint. -/
def Compatible {G K : SimpleGraph U} (L : List (GPath G)) (D : PathDecomp K) : Prop :=
  (∀ Q ∈ D.paths, ∀ R ∈ L, (Q.src = R.src ∨ Q.tgt = R.src) →
    ∀ x ∈ Q.walk.support, x ∈ R.walk.support → x = R.src) ∧
  (∀ Q ∈ D.paths, ∀ R₁ ∈ L, ∀ R₂ ∈ L, Q.src = R₁.src → Q.tgt = R₂.src →
    ∀ x ∈ R₁.walk.support, x ∉ R₂.walk.support)

/-- **Appending all routes** (Proposition "rr", compatible ⇒ route-respecting). Let `L` be
pairwise edge-disjoint paths of `G` with distinct tails, no head being a tail, and let `D` decompose
`G` minus their edges, compatibly, with an end at every tail. Then `G` has a decomposition whose end
counts are those of `D`, minus one at each tail, plus one at each head. -/
theorem append_routes {G : SimpleGraph U} :
    ∀ (L : List (GPath G)) (K : SimpleGraph U),
      (∀ e, e ∈ K.edgeSet ↔ e ∈ G.edgeSet ∧ ∀ R ∈ L, e ∉ R.edges) →
      L.Pairwise (fun R R' => ∀ e ∈ R.edges, e ∉ R'.edges) →
      (L.map GPath.src).Nodup → (∀ R ∈ L, ∀ R' ∈ L, R.tgt ≠ R'.src) →
      ∀ D : PathDecomp K, Compatible L D → (∀ R ∈ L, 1 ≤ D.ends R.src) →
      ∃ D' : PathDecomp G, ∀ w, D'.ends w + L.countP (fun R => decide (R.src = w)) =
        D.ends w + L.countP (fun R => decide (R.tgt = w))
  | [], K, hK, _, _, _, D, _, _ => by
      obtain ⟨D', hD'⟩ := D.congrGraph (G := G) (fun e => by rw [hK e]; simp)
      exact ⟨D', fun w => by simp [hD' w]⟩
  | R :: L', K, hK, hpw, hnd, hht, D, hcomp, hend => by
      rw [List.pairwise_cons] at hpw
      obtain ⟨hRL', hpw'⟩ := hpw
      rw [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hRnot, hnd'⟩ := hnd
      have hH : ∀ e, e ∈ (delPaths G L').edgeSet ↔ e ∈ G.edgeSet ∧ ∀ R' ∈ L', e ∉ R'.edges :=
        delPaths_edgeSet G L'
      have hRH : ∀ e ∈ R.edges, e ∈ (delPaths G L').edgeSet := fun e he =>
        (hH e).2 ⟨R.walk.edges_subset_edgeSet he, fun R' hR' => hRL' R' hR' e he⟩
      have hKH : ∀ e, e ∈ K.edgeSet ↔ e ∈ (delPaths G L').edgeSet ∧ e ∉ (R.transfer hRH).edges := by
        intro e
        rw [hK e, hH e, GPath.transfer_edges]
        simp only [List.forall_mem_cons]
        tauto
      have hRmem : R ∈ R :: L' := List.mem_cons_self ..
      obtain ⟨Q, hQ, hQc⟩ : ∃ Q ∈ D.paths, Q.src = R.src ∨ Q.tgt = R.src := by
        have h1 := hend R hRmem
        by_contra hno
        push_neg at hno
        have h0 : D.ends R.src = 0 := by
          unfold PathDecomp.ends
          rw [List.sum_eq_zero]
          intro x hx
          obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hx
          obtain ⟨h1, h2⟩ := hno P hP
          simp [GPath.endsAt, h1, h2]
        omega
      have hdisj : ∀ x ∈ Q.walk.support, x ∈ (R.transfer hRH).walk.support → x = R.src := by
        intro x hx hxR
        rw [GPath.transfer_support] at hxR
        exact hcomp.1 Q hQ R hRmem hQc x hx hxR
      obtain ⟨D₁, hends₁, hcls⟩ :=
        D.route_append_cls (R := R.transfer hRH) (c := R.src) (a := R.tgt) rfl rfl hKH hQ hQc hdisj
      have hcomp' : Compatible L' D₁ := by
        constructor
        · intro T hT R' hR' hTc x hxT hxR'
          have hR'm : R' ∈ R :: L' := List.mem_cons_of_mem _ hR'
          rcases hcls T hT with ⟨Q', hQ', hs, ht, hsupp⟩ | ⟨hTt, hTs, hTQ, hTsupp⟩
          · rw [hs, ht] at hTc
            rw [hsupp] at hxT
            exact hcomp.1 Q' hQ' R' hR'm hTc x hxT hxR'
          · have hTc' : T.src = R'.src := by
              rcases hTc with h | h
              · exact h
              · exact absurd (hTt.symm.trans h) (hht R hRmem R' hR'm)
            rcases (hTsupp x).1 hxT with hxQ | hxR
            · have hQR' : Q.src = R'.src ∨ Q.tgt = R'.src := by
                rcases hTQ with h | h
                · left; rw [← h, hTc']
                · right; rw [← h, hTc']
              exact hcomp.1 Q hQ R' hR'm hQR' x hxQ hxR'
            · rw [GPath.transfer_support] at hxR
              exfalso
              rcases hQc with hQs | hQt
              · have hQt : Q.tgt = R'.src := by
                  rcases hTQ with h | h
                  · exact absurd (h.trans hQs) hTs
                  · rw [← h, hTc']
                exact hcomp.2 Q hQ R hRmem R' hR'm hQs hQt x hxR hxR'
              · have hQs : Q.src = R'.src := by
                  rcases hTQ with h | h
                  · rw [← h, hTc']
                  · exact absurd (h.trans hQt) hTs
                exact hcomp.2 Q hQ R' hR'm R hRmem hQs hQt x hxR' hxR
        · intro T hT R₁ hR₁ R₂ hR₂ hs ht x hx1 hx2
          rcases hcls T hT with ⟨Q', hQ', hs', ht', -⟩ | ⟨hTt, -, -, -⟩
          · exact hcomp.2 Q' hQ' R₁ (List.mem_cons_of_mem _ hR₁) R₂ (List.mem_cons_of_mem _ hR₂)
              (hs'.symm.trans hs) (ht'.symm.trans ht) x hx1 hx2
          · exact hht R hRmem R₂ (List.mem_cons_of_mem _ hR₂) (hTt.symm.trans ht)
      have hend' : ∀ R' ∈ L', 1 ≤ D₁.ends R'.src := by
        intro R' hR'
        have h := hends₁ R'.src
        have hne : ¬ R.src = R'.src := fun h' =>
          hRnot (by rw [h']; exact List.mem_map_of_mem hR')
        rw [if_neg hne] at h
        have := hend R' (List.mem_cons_of_mem _ hR')
        omega
      obtain ⟨D', hD'⟩ := append_routes L' (delPaths G L') hH hpw' hnd'
        (fun R₁ h₁ R₂ h₂ => hht R₁ (List.mem_cons_of_mem _ h₁) R₂ (List.mem_cons_of_mem _ h₂))
        D₁ hcomp' hend'
      refine ⟨D', fun w => ?_⟩
      have h1 := hD' w
      have h2 := hends₁ w
      rw [List.countP_cons, List.countP_cons]
      by_cases hs : R.src = w <;> by_cases ht : R.tgt = w <;>
        simp only [hs, ht, decide_true, decide_false, ite_true, ite_false, Bool.false_eq_true]
          at h2 ⊢ <;> omega

end routes

section system

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A **route system** for an even pairing `σ` of `G`: for every even vertex `v`, a path of `G`
from `v` to `σ v`, such that routes of different pairs are edge-disjoint. -/
structure RouteSystem (G : SimpleGraph V) [DecidableRel G.Adj] (σ : V → V) where
  route : V → GPath G
  src : ∀ v ∈ evenSet G, (route v).src = v
  tgt : ∀ v ∈ evenSet G, (route v).tgt = σ v
  disj : ∀ v ∈ evenSet G, ∀ w ∈ evenSet G, w ≠ v → w ≠ σ v →
    ∀ e ∈ (route v).edges, e ∉ (route w).edges

/-- The routes of a transversal `M`, each oriented from its tail (outside `M`) to its head. -/
noncomputable def RouteSystem.tails {G : SimpleGraph V} [DecidableRel G.Adj] {σ : V → V}
    (ρ : RouteSystem G σ) (M : Finset V) : List (GPath G) :=
  (evenSet G \ M).toList.map ρ.route

omit [Fintype V] in
theorem countP_toList_eq_ite (T : Finset V) (p : V → Bool) (a : V)
    (hp : ∀ x ∈ T, p x = true ↔ x = a) : T.toList.countP p = if a ∈ T then 1 else 0 := by
  rw [List.countP_congr (q := fun x => x == a) (fun x hx => by
    rw [Finset.mem_toList] at hx; simp [hp x hx])]
  change List.count a T.toList = _
  split_ifs with ha
  · exact List.count_eq_one_of_mem (Finset.nodup_toList T) (Finset.mem_toList.mpr ha)
  · exact List.count_eq_zero.mpr (by rwa [Finset.mem_toList])

/-- **Compatible decompositions give realisations** (Proposition "rr"). Let `ρ` route an even
pairing `σ` of `G`, let `M` be a transversal, and let `D` decompose `G` minus the routes, with at
most one end at every vertex and an end at every tail, compatibly with the routes oriented from
their tails. Then `M` is realisable. -/
theorem realisable_of_compatible {G : SimpleGraph V} [DecidableRel G.Adj] {σ : V → V}
    (hσ : IsEvenPairing G σ) (ρ : RouteSystem G σ) {M : Finset V} (hM : IsTransversal G σ M)
    (D : PathDecomp (delPaths G (ρ.tails M))) (h1 : ∀ w, D.ends w ≤ 1)
    (ht : ∀ c ∈ evenSet G \ M, 1 ≤ D.ends c) (hcomp : Compatible (ρ.tails M) D) :
    Realisable G M := by
  classical
  have hTE : ∀ c ∈ evenSet G \ M, c ∈ evenSet G := fun c hc => (Finset.mem_sdiff.mp hc).1
  have hTM : ∀ c ∈ evenSet G \ M, c ∉ M := fun c hc => (Finset.mem_sdiff.mp hc).2
  have hσM : ∀ c ∈ evenSet G \ M, σ c ∈ M := fun c hc => by
    by_contra h
    exact hTM c hc ((hM.2 c (hTE c hc)).2 h)
  have hmemT : ∀ R ∈ ρ.tails M, ∃ c ∈ evenSet G \ M, R = ρ.route c := by
    intro R hR
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hR
    exact ⟨c, Finset.mem_toList.mp hc, rfl⟩
  have hpw : (ρ.tails M).Pairwise (fun R R' => ∀ e ∈ R.edges, e ∉ R'.edges) := by
    unfold RouteSystem.tails
    rw [List.pairwise_map]
    refine (Finset.nodup_toList _).imp_of_mem ?_
    intro c c' hc hc' hne
    rw [Finset.mem_toList] at hc hc'
    exact ρ.disj c (hTE c hc) c' (hTE c' hc') (Ne.symm hne)
      (fun h => hTM c' hc' (h ▸ hσM c hc))
  have hnd : ((ρ.tails M).map GPath.src).Nodup := by
    unfold RouteSystem.tails
    rw [List.map_map]
    refine (Finset.nodup_toList _).map_on ?_
    intro x hx y hy hxy
    rw [Finset.mem_toList] at hx hy
    simp only [Function.comp_apply, ρ.src x (hTE x hx), ρ.src y (hTE y hy)] at hxy
    exact hxy
  have hht : ∀ R ∈ ρ.tails M, ∀ R' ∈ ρ.tails M, R.tgt ≠ R'.src := by
    intro R hR R' hR'
    obtain ⟨c, hc, rfl⟩ := hmemT R hR
    obtain ⟨c', hc', rfl⟩ := hmemT R' hR'
    rw [ρ.tgt c (hTE c hc), ρ.src c' (hTE c' hc')]
    exact fun h => hTM c' hc' (h ▸ hσM c hc)
  have hend : ∀ R ∈ ρ.tails M, 1 ≤ D.ends R.src := by
    intro R hR
    obtain ⟨c, hc, rfl⟩ := hmemT R hR
    rw [ρ.src c (hTE c hc)]
    exact ht c hc
  obtain ⟨D', hD'⟩ := append_routes (ρ.tails M) _ (delPaths_edgeSet G _) hpw hnd hht D hcomp hend
  -- the two counts
  have hcs : ∀ w, (ρ.tails M).countP (fun R => decide (R.src = w)) =
      if w ∈ evenSet G \ M then 1 else 0 := by
    intro w
    unfold RouteSystem.tails
    rw [List.countP_map]
    apply countP_toList_eq_ite
    intro x hx
    simp [ρ.src x (hTE x hx)]
  have hct : ∀ w, (ρ.tails M).countP (fun R => decide (R.tgt = w)) =
      if σ w ∈ evenSet G \ M ∧ w ∈ evenSet G then 1 else 0 := by
    intro w
    unfold RouteSystem.tails
    rw [List.countP_map]
    by_cases hw : w ∈ evenSet G
    · rw [countP_toList_eq_ite _ _ (σ w) (fun x hx => by
        simp only [Function.comp_apply, ρ.tgt x (hTE x hx), decide_eq_true_eq]
        constructor
        · rintro rfl; exact (hσ.invol x (hTE x hx)).symm
        · rintro rfl; exact hσ.invol w hw)]
      simp [hw]
    · rw [List.countP_eq_zero.mpr (fun x hx => by
        rw [Finset.mem_toList] at hx
        simp only [Function.comp_apply, ρ.tgt x (hTE x hx), decide_eq_true_eq]
        rintro rfl
        exact hw (hσ.mem x (hTE x hx)))]
      simp [hw]
  refine ⟨hM.1, D', fun w => ?_⟩
  have h := hD' w
  rw [hcs w, hct w] at h
  have hp := D'.ends_mod_two w
  have hDw := h1 w
  unfold profile
  by_cases hwE : w ∈ evenSet G
  · have hev := mem_evenSet_iff.mp hwE
    have hnodd : ¬ Odd (G.degree w) := Nat.not_odd_iff_even.mpr (Nat.even_iff.mpr hev.2)
    rw [if_neg hnodd]
    by_cases hwM : w ∈ M
    · have hσw : σ w ∈ evenSet G \ M := by
        refine Finset.mem_sdiff.mpr ⟨hσ.mem w hwE, fun h' => ?_⟩
        exact ((hM.2 w hwE).1 hwM) h'
      have hwT : w ∉ evenSet G \ M := fun h' => (Finset.mem_sdiff.mp h').2 hwM
      rw [if_pos hwM]
      rw [if_neg hwT, if_pos ⟨hσw, hwE⟩] at h
      omega
    · have hwT : w ∈ evenSet G \ M := Finset.mem_sdiff.mpr ⟨hwE, hwM⟩
      have hσw : ¬ (σ w ∈ evenSet G \ M ∧ w ∈ evenSet G) := by
        rintro ⟨h', -⟩
        exact (Finset.mem_sdiff.mp h').2 (by
          by_contra h''
          exact hwM ((hM.2 w hwE).2 h''))
      rw [if_neg hwM]
      rw [if_pos hwT, if_neg hσw] at h
      omega
  · have hwT : w ∉ evenSet G \ M := fun h' => hwE (Finset.mem_sdiff.mp h').1
    have hσw : ¬ (σ w ∈ evenSet G \ M ∧ w ∈ evenSet G) := fun h' => hwE h'.2
    rw [if_neg hwT, if_neg hσw] at h
    have hwM : w ∉ M := fun h' => hwE (hM.1 h')
    rw [mem_evenSet_iff] at hwE
    by_cases hodd : Odd (G.degree w)
    · rw [if_pos hodd]; rw [Nat.odd_iff] at hodd; omega
    · rw [if_neg hodd, if_neg hwM]; rw [Nat.odd_iff] at hodd; omega

/-- **RR** in the form that gives Gallai's conjecture: every connected graph of even order has an
even pairing with a route system such that, for every transversal, the graph minus the routes has a
compatible decomposition with at most one end at every vertex and an end at every tail (that is, an
`M`-compatible Lovász decomposition of the free graph). -/
def RouteRR : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
    H.Connected → Even (Fintype.card W) →
    ∃ σ : W → W, IsEvenPairing H σ ∧ ∃ ρ : RouteSystem H σ, ∀ M, IsTransversal H σ M →
      ∃ D : PathDecomp (delPaths H (ρ.tails M)), (∀ w, D.ends w ≤ 1) ∧
        (∀ c ∈ evenSet H \ M, 1 ≤ D.ends c) ∧ Compatible (ρ.tails M) D

/-- Existential RR: for every even vertex `y` some transversal containing `y` has a compatible
decomposition. -/
def RouteRRExists : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
    H.Connected → Even (Fintype.card W) →
    ∃ σ : W → W, IsEvenPairing H σ ∧ ∃ ρ : RouteSystem H σ, ∀ y ∈ evenSet H,
      ∃ M, IsTransversal H σ M ∧ y ∈ M ∧
        ∃ D : PathDecomp (delPaths H (ρ.tails M)), (∀ w, D.ends w ≤ 1) ∧
          (∀ c ∈ evenSet H \ M, 1 ≤ D.ends c) ∧ Compatible (ρ.tails M) D

theorem pairingTRC_of_routeRR (h : RouteRR.{u}) : PairingTRC.{u} := by
  intro W _ _ H _ hconn hev
  obtain ⟨σ, hσ, ρ, hall⟩ := h W H hconn hev
  refine ⟨σ, hσ, fun M hM => ?_⟩
  obtain ⟨D, h1, ht, hc⟩ := hall M hM
  exact realisable_of_compatible hσ ρ hM D h1 ht hc

theorem pairingTRCExists_of_routeRRExists (h : RouteRRExists.{u}) : PairingTRCExists.{u} := by
  intro W _ _ H _ hconn hev
  obtain ⟨σ, hσ, ρ, hall⟩ := h W H hconn hev
  refine ⟨σ, hσ, fun y hy => ?_⟩
  obtain ⟨M, hM, hyM, D, h1, ht, hc⟩ := hall y hy
  exact ⟨M, hM, hyM, realisable_of_compatible hσ ρ hM D h1 ht hc⟩

/-- **Gallai's conjecture follows from RR**: compatible Lovász decompositions of the free graphs of
some routed pairing, for every transversal. -/
theorem gallai_of_routeRR (h : RouteRR.{u}) : GallaiConjecture.{u} :=
  gallai_of_pairingTRC (pairingTRC_of_routeRR h)

/-- **Gallai's conjecture follows from existential RR.** -/
theorem gallai_of_routeRRExists (h : RouteRRExists.{u}) : GallaiConjecture.{u} :=
  gallai_of_pairingTRCExists (pairingTRCExists_of_routeRRExists h)

end system

end Gallai
