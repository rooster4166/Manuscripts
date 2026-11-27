import GallaiLean.EulerianCone

/-!
# Cycle insertion (manuscript `eulerian-cone`, Lemma 5.2 and Proposition 5.3)

Let `D'` decompose `K`, let `a` have a `K`-edge, and let `C = a c₁ ⋯ c_l a` be a cycle, given as a
path `R : a → c` (`c = c_l`) of `G` together with the edge `c a`, edge-disjoint from `K`, with
`E(G) = E(K) ∪ E(R) ∪ {ca}`. Suppose `c` has no `K`-edge and every vertex of `R` other than `a`
and one designated vertex `b` has no `K`-edge. Then `G` has a decomposition with one more path,
the same number of ends as `D'` at every vertex except `c`, and two more ends at `c`.

* `GPath.liftTo`: a path of a subgraph as a path of `G`.
* `PathDecomp.replaceList`: replace one path by a list of new paths in a larger graph.
* `GPath.exists_split_avoid`: split a path at an internal vertex `a` into a piece ending at `a`
  that avoids a given vertex `b ≠ a` and a piece starting at `a`.
* **`PathDecomp.cycle_insert`**: the lemma (both cases of the manuscript's proof).
* **`PathDecomp.ear_insert`**: the triangle `a b v a` with `v` new (manuscript Prop. 5.3).
-/

open SimpleGraph

namespace Gallai

universe u

variable {U : Type u}

/-! ### Small path tools -/

/-- A path of `K` as a path of `G`, when its edges are edges of `G`. -/
def GPath.liftTo {K : SimpleGraph U} (P : GPath K) (G : SimpleGraph U)
    (h : ∀ e ∈ P.walk.edges, e ∈ G.edgeSet) : GPath G where
  src := P.src
  tgt := P.tgt
  walk := P.walk.transfer G h
  isPath := P.isPath.transfer h
  pos := by rw [Walk.length_transfer]; exact P.pos

@[simp] theorem GPath.liftTo_src {K G : SimpleGraph U} (P : GPath K) (h) :
    (P.liftTo G h).src = P.src := rfl
@[simp] theorem GPath.liftTo_tgt {K G : SimpleGraph U} (P : GPath K) (h) :
    (P.liftTo G h).tgt = P.tgt := rfl
@[simp] theorem GPath.liftTo_edges {K G : SimpleGraph U} (P : GPath K) (h) :
    (P.liftTo G h).edges = P.edges := by
  simp [GPath.liftTo, GPath.edges, Walk.edges_transfer]
@[simp] theorem GPath.liftTo_support {K G : SimpleGraph U} (P : GPath K) (h) :
    (P.liftTo G h).walk.support = P.walk.support := by
  simp [GPath.liftTo, Walk.support_transfer]

@[simp] theorem GPath.ofAdj_src' {G : SimpleGraph U} {x y : U} (h : G.Adj x y) :
    (GPath.ofAdj h).src = x := rfl
@[simp] theorem GPath.ofAdj_tgt' {G : SimpleGraph U} {x y : U} (h : G.Adj x y) :
    (GPath.ofAdj h).tgt = y := rfl
@[simp] theorem GPath.ofAdj_support' {G : SimpleGraph U} {x y : U} (h : G.Adj x y) :
    (GPath.ofAdj h).walk.support = [x, y] := rfl

theorem GPath.edges_nodup' {G : SimpleGraph U} (P : GPath G) : P.edges.Nodup :=
  P.isPath.isTrail.edges_nodup

/-- A vertex of a path lies on one of its edges, hence has an edge of the graph. -/
theorem GPath.adj_of_mem_support {K : SimpleGraph U} (P : GPath K) {v : U}
    (hv : v ∈ P.walk.support) : ∃ y, K.Adj v y := by
  obtain ⟨e, he, hve⟩ := GPath.exists_mem_edge_of_support P hv
  have heK := P.walk.edges_subset_edgeSet he
  induction e using Sym2.inductionOn with
  | hf x y =>
    rcases Sym2.mem_iff.mp hve with rfl | rfl
    · exact ⟨y, heK⟩
    · exact ⟨x, heK.symm⟩

variable [DecidableEq U]

theorem GPath.liftTo_endsAt {K G : SimpleGraph U} (P : GPath K) (h) (w : U) :
    (P.liftTo G h).endsAt w = P.endsAt w := rfl

/-! ### Replacing one path by several -/

/-- **Replace one path `Q` of `D'` by a list of new paths** in a graph `G ⊇ K` with
`E(G) = E(K) ⊔ extra`, when the new paths use exactly the edges of `Q` and `extra`. -/
theorem PathDecomp.replaceList {K G : SimpleGraph U} (D' : PathDecomp K) {Q : GPath K}
    (hQ : Q ∈ D'.paths) (new : List (GPath G)) (extra : List (Sym2 U))
    (hKG : ∀ e ∈ K.edgeSet, e ∈ G.edgeSet)
    (hperm : (new.flatMap GPath.edges).Perm (Q.edges ++ extra)) (hnd : extra.Nodup)
    (hdisj : ∀ e ∈ extra, e ∉ K.edgeSet)
    (hcov : ∀ e, e ∈ G.edgeSet ↔ e ∈ K.edgeSet ∨ e ∈ extra) :
    ∃ D : PathDecomp G, D.size + 1 = D'.size + new.length ∧
      ∀ w, D.ends w + Q.endsAt w = D'.ends w + (new.map (fun P => P.endsAt w)).sum := by
  classical
  let lift : GPath K → GPath G := fun P =>
    P.liftTo G (fun e he => hKG e (P.walk.edges_subset_edgeSet he))
  have hlift_e : ∀ l : List (GPath K), (l.map lift).flatMap GPath.edges = l.flatMap GPath.edges := by
    intro l; induction l with
    | nil => rfl
    | cons P l ih => simp [List.flatMap_cons, ih, lift]
  have hlift_w : ∀ (l : List (GPath K)) (w : U),
      ((l.map lift).map (fun P => P.endsAt w)).sum = (l.map (fun P => P.endsAt w)).sum := by
    intro l w; induction l with
    | nil => rfl
    | cons P l ih => simp only [List.map_cons, List.sum_cons, ih]; rfl
  have hP := List.perm_cons_erase hQ
  have hDe : (D'.paths.flatMap GPath.edges).Perm (Q.edges ++ (D'.paths.erase Q).flatMap GPath.edges) := by
    have := hP.flatMap_right GPath.edges
    simpa [List.flatMap_cons] using this
  let L : List (GPath G) := new ++ (D'.paths.erase Q).map lift
  let M : List (Sym2 U) := extra ++ D'.paths.flatMap GPath.edges
  have hLM : (L.flatMap GPath.edges).Perm M := by
    simp only [L, M, List.flatMap_append, hlift_e]
    refine (hperm.append_right _).trans ((List.perm_append_comm.append_right _).trans ?_)
    rw [List.append_assoc]
    exact (hDe.symm).append_left extra
  have hMnd : M.Nodup := by
    simp only [M]
    rw [List.nodup_append]
    refine ⟨hnd, D'.nodup_edges, fun e he e' he' hee => ?_⟩
    subst hee
    exact hdisj e he ((D'.covers e).2 he')
  have hMcov : ∀ e, e ∈ G.edgeSet ↔ e ∈ M := by
    intro e
    simp only [M, List.mem_append]
    rw [hcov e, D'.covers e, or_comm]
  refine ⟨PathDecomp.ofPerm L M hLM hMnd hMcov, ?_, fun w => ?_⟩
  · simp only [PathDecomp.size, PathDecomp.ofPerm_paths, L, List.length_append, List.length_map]
    have := hP.length_eq
    simp only [List.length_cons] at this
    omega
  · simp only [PathDecomp.ends, PathDecomp.ofPerm_paths, L, List.map_append, List.sum_append,
      hlift_w]
    have := (hP.map (fun P => P.endsAt w)).sum_eq
    simp only [List.map_cons, List.sum_cons] at this
    rw [this]
    omega

/-! ### Splitting at `a` away from `b` -/

/-- Split a path at an internal vertex `a` into `X` ending at `a` and `Y` starting at `a`, with
`X` avoiding a given vertex `b ≠ a`. -/
theorem GPath.exists_split_avoid {K : SimpleGraph U} (Q : GPath K) {a : U}
    (haQ : a ∈ Q.walk.support) (hs : Q.src ≠ a) (ht : Q.tgt ≠ a) (b : U) :
    ∃ X Y : GPath K, X.tgt = a ∧ Y.src = a ∧ (X.edges ++ Y.edges).Perm Q.edges ∧
      (∀ w, (if X.src = w then 1 else 0) + (if Y.tgt = w then 1 else 0) = Q.endsAt w) ∧
      (b ∈ X.walk.support → b = a) ∧ (∀ v ∈ X.walk.support, v ∈ Q.walk.support) ∧
      (∀ v ∈ Y.walk.support, v ∈ Q.walk.support) := by
  obtain ⟨q₁, q₂, hq⟩ := Walk.mem_support_iff_exists_append.mp haQ
  have hpath : (q₁.append q₂).IsPath := hq ▸ Q.isPath
  have hnd : (q₁.append q₂).support.Nodup := hpath.support_nodup
  rw [Walk.support_append, List.nodup_append] at hnd
  have h₁ : 0 < q₁.length := by
    by_contra hc
    exact hs (Walk.eq_of_length_eq_zero (p := q₁) (by omega))
  have h₂ : 0 < q₂.length := by
    by_contra hc
    exact ht (Walk.eq_of_length_eq_zero (p := q₂) (by omega)).symm
  let Q₁ : GPath K := ⟨_, _, q₁, Walk.isPath_of_append_left hpath, h₁⟩
  let Q₂ : GPath K := ⟨_, _, q₂, Walk.isPath_of_append_right hpath, h₂⟩
  have hQe : Q.edges = Q₁.edges ++ Q₂.edges := by
    show Q.walk.edges = q₁.edges ++ q₂.edges
    rw [hq, Walk.edges_append]
  have hsupp : ∀ v, v ∈ Q.walk.support ↔ v ∈ q₁.support ∨ v ∈ q₂.support := by
    intro v; rw [hq]; exact Walk.mem_support_append_iff _ _
  -- the pieces meet only at `a`
  have hmeet : ∀ v ∈ q₁.support, v ∈ q₂.support → v = a := by
    intro v h1 h2
    by_contra hva
    have h2' : v ∈ q₂.support.tail := by
      rw [← Walk.cons_tail_support q₂, List.mem_cons] at h2
      rcases h2 with h | h
      · exact absurd h hva
      · exact h
    exact hnd.2.2 v h1 v h2' rfl
  have hEnds : ∀ w, Q.endsAt w = (if Q.src = w then 1 else 0) + (if Q.tgt = w then 1 else 0) :=
    fun w => rfl
  by_cases hb : b ∈ q₁.support ∧ b ≠ a
  · -- reverse: `X = Q₂⁻¹`, `Y = Q₁⁻¹`
    refine ⟨Q₂.reverse, Q₁.reverse, rfl, rfl, ?_, fun w => ?_, fun h => ?_, ?_, ?_⟩
    · rw [hQe]
      simp only [GPath.edges, GPath.reverse, Walk.edges_reverse]
      exact ((List.reverse_perm _).append (List.reverse_perm _)).trans List.perm_append_comm
    · show (if Q.tgt = w then 1 else 0) + (if Q.src = w then 1 else 0) = Q.endsAt w
      unfold GPath.endsAt
      split_ifs <;> omega
    · exfalso
      simp only [GPath.reverse, Walk.support_reverse, List.mem_reverse] at h
      exact hb.2 (hmeet b hb.1 h)
    · intro v hv
      simp only [GPath.reverse, Walk.support_reverse, List.mem_reverse] at hv
      exact (hsupp v).2 (Or.inr hv)
    · intro v hv
      simp only [GPath.reverse, Walk.support_reverse, List.mem_reverse] at hv
      exact (hsupp v).2 (Or.inl hv)
  · refine ⟨Q₁, Q₂, rfl, rfl, by rw [hQe], fun w => ?_, fun h => ?_, ?_, ?_⟩
    · rw [hEnds]
    · by_contra hba; exact hb ⟨h, hba⟩
    · intro v hv; exact (hsupp v).2 (Or.inl hv)
    · intro v hv; exact (hsupp v).2 (Or.inr hv)

/-! ### Cycle insertion -/

/-- **Cycle insertion** (manuscript Lemma 5.2). -/
theorem PathDecomp.cycle_insert {K G : SimpleGraph U} (D' : PathDecomp K) {a c b : U}
    (R : GPath G) (hRs : R.src = a) (hRt : R.tgt = c) (hca : G.Adj c a)
    (hG : ∀ e, e ∈ G.edgeSet ↔ e ∈ K.edgeSet ∨ e ∈ R.edges ∨ e = s(c, a))
    (hRK : ∀ e ∈ R.edges, e ∉ K.edgeSet) (hcaK : s(c, a) ∉ K.edgeSet)
    (hcaR : s(c, a) ∉ R.edges)
    (hc : ∀ y, ¬ K.Adj c y)
    (hnew : ∀ x ∈ R.walk.support, x ≠ a → x ≠ b → ∀ y, ¬ K.Adj x y)
    (ha : ∃ y, K.Adj a y) :
    ∃ D : PathDecomp G, D.size = D'.size + 1 ∧
      ∀ w, D.ends w = D'.ends w + (if w = c then 2 else 0) := by
  classical
  have hac : a ≠ c := fun h => by obtain ⟨y, hy⟩ := ha; exact hc y (h ▸ hy)
  have hc_supp : ∀ P : GPath K, c ∉ P.walk.support := fun P hP => by
    obtain ⟨y, hy⟩ := P.adj_of_mem_support hP; exact hc y hy
  have hKG : ∀ e ∈ K.edgeSet, e ∈ G.edgeSet := fun e he => (hG e).2 (Or.inl he)
  let extra : List (Sym2 U) := R.edges ++ [s(c, a)]
  have hext_nd : extra.Nodup := by
    simp only [extra, List.nodup_append, List.nodup_cons, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_self, List.mem_singleton, true_and]
    exact ⟨R.edges_nodup', fun e he e' he' hee => by subst he'; subst hee; exact hcaR he⟩
  have hext_disj : ∀ e ∈ extra, e ∉ K.edgeSet := by
    intro e he
    simp only [extra, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact hRK e he
    · exact hcaK
  have hcov : ∀ e, e ∈ G.edgeSet ↔ e ∈ K.edgeSet ∨ e ∈ extra := by
    intro e; rw [hG e]; simp [extra]
  by_cases hend : ∃ P ∈ D'.paths, P.src = a ∨ P.tgt = a
  · ---------------------------------------------------------------- Case E
    obtain ⟨P, hP, hPa⟩ := hend
    obtain ⟨P₁, hP₁s, hP₁e, hP₁v, hP₁ends⟩ := GPath.exists_orient_src P hPa
    let P₁G := P₁.liftTo G (fun e he => hKG e (P₁.walk.edges_subset_edgeSet he))
    obtain ⟨N₁, hN₁s, hN₁t, hN₁e, -⟩ := GPath.exists_join (GPath.ofAdj hca) P₁G (x := a) rfl
      (by simp [P₁G, hP₁s]) (by
        intro v hv hv'
        simp only [GPath.ofAdj_support', List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · simp only [P₁G, GPath.liftTo_support] at hv'
          exact absurd hv' (hc_supp P₁)
        · rfl)
    obtain ⟨D, hDs, hDe⟩ := D'.replaceList hP [N₁, R.reverse] extra hKG (by
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hN₁e, GPath.ofAdj_edges,
          P₁G, GPath.liftTo_edges, extra]
        simp only [GPath.edges, GPath.reverse, Walk.edges_reverse]
        have h1 := hP₁e
        simp only [GPath.edges] at h1
        refine List.Perm.trans ?_ (h1.append_right (R.walk.edges ++ [s(c, a)]))
        refine (List.perm_append_comm.append_right _).trans ?_
        rw [List.append_assoc]
        refine List.Perm.append_left _ ?_
        exact List.perm_append_comm.trans ((List.reverse_perm _).append_right _))
      hext_nd hext_disj hcov
    refine ⟨D, by simp at hDs; omega, fun w => ?_⟩
    have hPe : P.endsAt w = (if a = w then 1 else 0) + (if P₁.tgt = w then 1 else 0) := by
      have := hP₁ends w
      unfold GPath.endsAt
      rw [← hP₁s]
      by_cases h₁ : P.src = w <;> by_cases h₂ : P.tgt = w <;>
        by_cases h₃ : P₁.src = w <;> by_cases h₄ : P₁.tgt = w <;> simp_all
    have hN₁w : N₁.endsAt w = (if c = w then 1 else 0) + (if P₁.tgt = w then 1 else 0) := by
      simp only [GPath.endsAt, hN₁s, hN₁t, GPath.ofAdj_src', P₁G, GPath.liftTo_tgt]
    have hRrw : R.reverse.endsAt w = (if c = w then 1 else 0) + (if a = w then 1 else 0) := by
      simp only [GPath.endsAt, GPath.reverse, hRs, hRt]
    have h1 := hDe w
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h1
    rw [hPe, hN₁w, hRrw] at h1
    by_cases hcw : w = c
    · subst hcw; simp only [ite_true, hac, ite_false] at h1 ⊢; omega
    · have : ¬ c = w := fun h => hcw h.symm
      simp only [this, hcw, ite_false] at h1 ⊢; omega
  · ---------------------------------------------------------------- Case I
    push Not at hend
    obtain ⟨y, hy⟩ := ha
    have hay : s(a, y) ∈ K.edgeSet := hy
    obtain ⟨Q, hQ, hQay⟩ := List.mem_flatMap.mp ((D'.covers _).1 hay)
    have haQ : a ∈ Q.walk.support := Q.walk.fst_mem_support_of_mem_edges hQay
    obtain ⟨hQs, hQt⟩ := hend Q hQ
    obtain ⟨X, Y, hXt, hYs, hXYe, hXYw, hXb, -, -⟩ := Q.exists_split_avoid haQ hQs hQt b
    let XG := X.liftTo G (fun e he => hKG e (X.walk.edges_subset_edgeSet he))
    let YG := Y.liftTo G (fun e he => hKG e (Y.walk.edges_subset_edgeSet he))
    obtain ⟨N₁, hN₁s, hN₁t, hN₁e, -⟩ := GPath.exists_join XG R (x := a) hXt hRs (by
      intro v hv hvR
      simp only [XG, GPath.liftTo_support] at hv
      by_contra hva
      by_cases hvb : v = b
      · subst hvb; exact hva (hXb hv)
      · obtain ⟨z, hz⟩ := X.adj_of_mem_support hv
        exact hnew v hvR hva hvb z hz)
    obtain ⟨N₂, hN₂s, hN₂t, hN₂e, -⟩ := GPath.exists_join (GPath.ofAdj hca) YG (x := a) rfl
      (by simp [YG, hYs]) (by
        intro v hv hv'
        simp only [GPath.ofAdj_support', List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · simp only [YG, GPath.liftTo_support] at hv'
          exact absurd hv' (hc_supp Y)
        · rfl)
    obtain ⟨D, hDs, hDe⟩ := D'.replaceList hQ [N₁, N₂] extra hKG (by
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hN₁e, hN₂e,
          GPath.ofAdj_edges, XG, YG, GPath.liftTo_edges, extra]
        have h := hXYe
        refine List.Perm.trans ?_ (h.append_right (R.edges ++ [s(c, a)]))
        simp only [List.append_assoc]
        refine List.Perm.append_left _ ?_
        -- R ++ ([ca] ++ Y) ~ Y ++ (R ++ [ca])
        rw [← List.append_assoc]
        exact List.perm_append_comm)
      hext_nd hext_disj hcov
    refine ⟨D, by simp at hDs; omega, fun w => ?_⟩
    have hN₁w : N₁.endsAt w = (if X.src = w then 1 else 0) + (if c = w then 1 else 0) := by
      simp only [GPath.endsAt, hN₁s, hN₁t, hRt, XG, GPath.liftTo_src]
    have hN₂w : N₂.endsAt w = (if c = w then 1 else 0) + (if Y.tgt = w then 1 else 0) := by
      simp only [GPath.endsAt, hN₂s, hN₂t, GPath.ofAdj_src', YG, GPath.liftTo_tgt]
    have h1 := hDe w
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h1
    rw [hN₁w, hN₂w, ← hXYw w] at h1
    by_cases hcw : w = c
    · subst hcw; simp only [ite_true] at h1 ⊢; omega
    · have : ¬ c = w := fun h => hcw h.symm
      simp only [this, hcw, ite_false] at h1 ⊢; omega

/-- **Inserting a triangle ear** (manuscript Prop. 5.3): if `v` has no `K`-edge and
`E(G) = E(K) ⊔ {ab, bv, va}`, a decomposition of `K` gives one of `G` with one more path, the same
ends at every vertex other than `v`, and two ends at `v`. -/
theorem PathDecomp.ear_insert {K G : SimpleGraph U} (D' : PathDecomp K) {a b v : U}
    (hab : G.Adj a b) (hbv : G.Adj b v) (hva : G.Adj v a)
    (hG : ∀ e, e ∈ G.edgeSet ↔ e ∈ K.edgeSet ∨ e = s(a, b) ∨ e = s(b, v) ∨ e = s(v, a))
    (habK : s(a, b) ∉ K.edgeSet) (hbvK : s(b, v) ∉ K.edgeSet) (hvaK : s(v, a) ∉ K.edgeSet)
    (hv : ∀ y, ¬ K.Adj v y) (ha : ∃ y, K.Adj a y) :
    ∃ D : PathDecomp G, D.size = D'.size + 1 ∧
      ∀ w, D.ends w = D'.ends w + (if w = v then 2 else 0) := by
  have hab' := hab.ne
  have hbv' := hbv.ne
  have hva' := hva.ne
  let R : GPath G := ⟨a, v, Walk.cons hab (Walk.cons hbv Walk.nil),
    (Walk.IsPath.nil.cons (by simpa using hbv')).cons
      (by simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false, not_or]; exact ⟨hab', fun h => hva' h.symm⟩), by simp⟩
  have hRe : R.edges = [s(a, b), s(b, v)] := rfl
  refine D'.cycle_insert (a := a) (c := v) (b := b) R rfl rfl hva
    (fun e => by rw [hG e, hRe]; simp [or_assoc])
    (fun e he => by rw [hRe] at he; simp at he; rcases he with rfl | rfl <;> assumption) hvaK
    (by
      rw [hRe]; intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false, Sym2.eq_iff] at h
      rcases h with (⟨h1, -⟩ | ⟨h1, -⟩) | (⟨h1, -⟩ | ⟨-, h2⟩)
      · exact hva' h1
      · exact hbv' h1.symm
      · exact hbv' h1.symm
      · exact hab' h2)
    hv ?_ ha
  intro x hx hxa hxb y hy
  have : x ∈ [a, b, v] := hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl
  · exact hxa rfl
  · exact hxb rfl
  · exact hv y hy

end Gallai
