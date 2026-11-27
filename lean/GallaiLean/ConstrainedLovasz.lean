import GallaiLean.L1Induction
import GallaiLean.MultiSepEE

/-!
# Constrained Lovász decompositions (session `claude/clt`)

Manuscript `manuscripts/clt/clt.tex`.

A *Lovász decomposition* of a graph with at most one vertex of positive even degree has
`ends v = deg v mod 2` everywhere.  A *constraint system* (`CSys`) asks for two kinds of
end-path conditions:

* avoidance `(c, A)`: every path with an end at `c` avoids `A`;
* distinctness `(p, q)`: no path has both `p` and `q` as ends.

## Fan's lemma with end paths

Fan's lemma (`fan_single`) is proved by a chain of re-routings `t = x₀, x₁, …, x_k` followed by
one append at the target `u`.  A re-routing keeps the vertex set of the re-routed path and moves
its end from `xᵢ` to `xᵢ₊₁`; the append adds `u` to one path.  So every path of the new
decomposition comes from **one** old path, has its vertex set inside that path plus `u`, and keeps
every end of it that is not a chain vertex or `u` (`Tracks`).  The chain vertices after `t` are
neighbours of `u`.

* **`fan_single_track`**: `fan_single_supp` with this end-path tracking.  This is Lemma 4.1 of
  `manuscripts/t6-dense` ("Fan with end paths"), until now paper only.

## Constraint systems

* **`csys_fan_transfer`**: a Fan transfer with target `u` carries a whole constraint system,
  provided no constrained vertex is `u`, the source, or a neighbour of `u`, and `u` is not avoided.
* **`csys_caseI`**: Lovász's Case I for constraint systems: if `g` is the even vertex and
  `u ∈ N(g)` is *free* (no constrained vertex in `N[u] ∪ {g}`, `u` not avoided), a Lovász
  decomposition of `G − gu` satisfying the system gives one of `G`.  No admissibility of the
  child is assumed.  For one avoidance constraint this is `avoid_of_target_child` (l1-induction),
  now without the leaf graph.
-/

open SimpleGraph

namespace Gallai

universe u v

section track

variable {U : Type v} [DecidableEq U]

/-- `D'` is *tracked* by `D` away from `S`, up to the vertex `u`: every path of `D'` comes from a
path of `D` whose vertex set contains it up to `u`, and which has every end of it outside `S`. -/
def Tracks {K K' : SimpleGraph U} (D : PathDecomp K) (D' : PathDecomp K') (S : Set U) (u : U) :
    Prop :=
  ∀ Q' ∈ D'.paths, ∃ Q ∈ D.paths, (∀ x ∈ Q'.walk.support, x ∈ Q.walk.support ∨ x = u) ∧
    ∀ w, w ∉ S → (Q'.src = w ∨ Q'.tgt = w) → (Q.src = w ∨ Q.tgt = w)

omit [DecidableEq U] in
theorem Tracks.mono {K K' : SimpleGraph U} {D : PathDecomp K} {D' : PathDecomp K'} {S S' : Set U}
    {u : U} (h : Tracks D D' S u) (hS : S ⊆ S') : Tracks D D' S' u := by
  intro Q' hQ'
  obtain ⟨Q, hQ, h1, h2⟩ := h Q' hQ'
  exact ⟨Q, hQ, h1, fun w hw => h2 w (fun h => hw (hS h))⟩

omit [DecidableEq U] in
theorem Tracks.trans {K₀ K₁ K₂ : SimpleGraph U} {D₀ : PathDecomp K₀} {D₁ : PathDecomp K₁}
    {D₂ : PathDecomp K₂} {S₁ S₂ : Set U} {u : U} (h₁ : Tracks D₀ D₁ S₁ u)
    (h₂ : Tracks D₁ D₂ S₂ u) : Tracks D₀ D₂ (S₁ ∪ S₂) u := by
  intro Q₂ hQ₂
  obtain ⟨Q₁, hQ₁, a₁, b₁⟩ := h₂ Q₂ hQ₂
  obtain ⟨Q₀, hQ₀, a₀, b₀⟩ := h₁ Q₁ hQ₁
  refine ⟨Q₀, hQ₀, fun x hx => ?_, fun w hw hend => ?_⟩
  · rcases a₁ x hx with h | h
    · exact a₀ x h
    · exact Or.inr h
  · exact b₀ w (fun h => hw (Or.inl h)) (b₁ w (fun h => hw (Or.inr h)) hend)

/-- An end of an oriented copy of `P` is an end of `P`. -/
theorem GPath.end_of_endsAt_eq {K : SimpleGraph U} {P Q : GPath K}
    (h : ∀ w, Q.endsAt w = P.endsAt w) {w : U} (hw : Q.src = w ∨ Q.tgt = w) :
    P.src = w ∨ P.tgt = w := by
  have h1 := h w
  unfold GPath.endsAt at h1
  by_contra hn
  obtain ⟨h1', h2'⟩ := not_or.mp hn
  rcases hw with hw | hw <;> simp [hw, h1', h2'] at h1

variable {K K' : SimpleGraph U}

/-- `append_move` with end-path tracking. -/
theorem PathDecomp.append_move_track (D : PathDecomp K) {t u : U} (hadj : ¬ K.Adj t u)
    (hK' : ∀ e, e ∈ K'.edgeSet ↔ e ∈ K.edgeSet ∨ e = s(t, u))
    {P : GPath K} (hP : P ∈ D.paths) (hend : P.src = t ∨ P.tgt = t)
    (hu : u ∉ P.walk.support) :
    ∃ D' : PathDecomp K', D'.size = D.size ∧
      (∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if u = w then 1 else 0)) ∧
      Tracks D D' {t, u} u ∧
      ∀ Q' ∈ D'.paths, (∀ x ∈ Q'.walk.support, x ∈ P.walk.support ∨ x = u) ∨
        ∃ Q₀ ∈ D.paths, Q'.src = Q₀.src ∧ Q'.tgt = Q₀.tgt ∧ Q'.walk.support = Q₀.walk.support := by
  obtain ⟨Q, hQs, hQe, hQends, hQsupp⟩ := P.exists_orient hend
  have hQK : ∀ e ∈ Q.walk.edges, e ∈ K'.edgeSet := fun e he =>
    (hK' e).2 (Or.inl (Q.walk.edges_subset_edgeSet he))
  have hs : s(u, Q.src) = s(t, u) := by rw [hQs, Sym2.eq_swap]
  have hut : K'.Adj u Q.src := by
    rw [← mem_edgeSet, hK', hs]; exact Or.inr rfl
  have huQ : u ∉ Q.walk.support := fun h => hu ((hQsupp u).1 h)
  let P' : GPath K' :=
    ⟨u, Q.tgt, Walk.cons hut (Q.walk.transfer K' hQK),
      by
        rw [Walk.cons_isPath_iff]
        exact ⟨by simpa using Q.isPath, by simpa using huQ⟩,
      by simp⟩
  have hP'e : P'.edges = s(t, u) :: Q.edges := by
    show (Walk.cons hut (Q.walk.transfer K' hQK)).edges = _
    rw [Walk.edges_cons, Walk.edges_transfer, hs]
    rfl
  have hPK : ∀ e ∈ P.edges, e ∈ K.edgeSet := fun e he => P.walk.edges_subset_edgeSet he
  have htuK : s(t, u) ∉ K.edgeSet := hadj
  obtain ⟨D', hsize, -, hends, -, hcovr⟩ := D.replace_supp hP P' (by
      intro e
      rw [hK' e, hP'e, List.mem_cons, hQe.mem_iff]
      constructor
      · rintro (h | h)
        · by_cases heP : e ∈ P.edges
          · exact Or.inr (Or.inr heP)
          · exact Or.inl ⟨h, heP⟩
        · exact Or.inr (Or.inl h)
      · rintro (⟨h, -⟩ | h | h)
        · exact Or.inl h
        · exact Or.inr h
        · exact Or.inl (hPK e h))
    (by
      intro e he
      rw [hP'e, List.mem_cons, hQe.mem_iff] at he
      rcases he with rfl | he
      · exact Or.inr htuK
      · exact Or.inl he)
  refine ⟨D', hsize, fun w => ?_, fun Q' hQ' => ?_, fun Q' hQ' => ?_⟩
  · have h1 := hends w
    have h2 : P'.endsAt w = (if u = w then 1 else 0) + (if Q.tgt = w then 1 else 0) := rfl
    have h3 : P.endsAt w = (if t = w then 1 else 0) + (if Q.tgt = w then 1 else 0) := by
      rw [← hQends]; simp only [GPath.endsAt, hQs]
    omega
  swap
  · rcases hcovr Q' hQ' with rfl | ⟨Q₀, hQ₀, hsrc, htgt, hs₀⟩
    · left
      intro x hx
      have : x ∈ (Walk.cons hut (Q.walk.transfer K' hQK)).support := hx
      rw [Walk.support_cons, Walk.support_transfer, List.mem_cons] at this
      rcases this with rfl | h
      · exact Or.inr rfl
      · exact Or.inl ((hQsupp x).1 h)
    · exact Or.inr ⟨Q₀, hQ₀, hsrc, htgt, hs₀⟩
  rcases hcovr Q' hQ' with rfl | ⟨Q₀, hQ₀, hsrc, htgt, hs₀⟩
  · refine ⟨P, hP, fun x hx => ?_, fun w hw hwe => ?_⟩
    · have : x ∈ (Walk.cons hut (Q.walk.transfer K' hQK)).support := hx
      rw [Walk.support_cons, Walk.support_transfer, List.mem_cons] at this
      rcases this with rfl | h
      · exact Or.inr rfl
      · exact Or.inl ((hQsupp x).1 h)
    · have hwu : w ≠ u := fun h => hw (Or.inr h)
      rcases hwe with h | h
      · exact absurd h.symm hwu
      · exact GPath.end_of_endsAt_eq hQends (Or.inr h)
  · exact ⟨Q₀, hQ₀, fun x hx => Or.inl (hs₀ ▸ hx), fun w _ h => by
      rw [← hsrc, ← htgt]; exact h⟩

/-- `reroute_core` with end-path tracking. -/
theorem PathDecomp.reroute_core_track (D : PathDecomp K) {t u y : U} (hadj : ¬ K.Adj t u)
    (hK' : ∀ e, e ∈ K'.edgeSet ↔ (e ∈ K.edgeSet ∧ e ≠ s(y, u)) ∨ e = s(t, u))
    {P : GPath K} (hP : P ∈ D.paths) (Q : GPath K) (hQs : Q.src = t)
    (hQinf : [y, u] <:+: Q.walk.support) (hQe : Q.edges.Perm P.edges)
    (hQends : ∀ w, Q.endsAt w = P.endsAt w)
    (hQsupp : ∀ w, w ∈ Q.walk.support ↔ w ∈ P.walk.support) :
    ∃ D' : PathDecomp K', D'.size = D.size ∧
      (∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if y = w then 1 else 0)) ∧
      (∀ Q ∈ D.paths, Q ≠ P → ∃ Q' ∈ D'.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
        Q'.walk.support = Q.walk.support) ∧
      Tracks D D' {t, y} u ∧
      ∃ P' ∈ D'.paths, P'.tgt = Q.tgt ∧
        ∀ z, [u, z] <:+: Q.walk.support → [u, z] <:+: P'.walk.support := by
  obtain ⟨hyu, q₁, q₂, hq⟩ := Walk.exists_append_cons_of_infix Q.walk hQinf
  have hpath : (q₁.append (Walk.cons hyu q₂)).IsPath := hq ▸ Q.isPath
  have hsupp : (q₁.append (Walk.cons hyu q₂)).support = q₁.support ++ q₂.support := by
    rw [Walk.support_append, Walk.support_cons, List.tail_cons]
  have hsnd : (q₁.support ++ q₂.support).Nodup := by
    rw [← hsupp]; exact (Walk.isPath_def _).mp hpath
  have hedges : Q.edges = q₁.edges ++ s(y, u) :: q₂.edges := by
    show Q.walk.edges = _
    rw [hq, Walk.edges_append, Walk.edges_cons]
  have hend : (q₁.edges ++ s(y, u) :: q₂.edges).Nodup := by
    rw [← hedges]; exact Q.isPath.isTrail.edges_nodup
  have hyq₁ : s(y, u) ∉ q₁.edges := fun h =>
    (List.nodup_append.mp hend).2.2 _ h _ List.mem_cons_self rfl
  have hyq₂ : s(y, u) ∉ q₂.edges := (List.nodup_cons.mp (List.nodup_append.mp hend).2.1).1
  have huq₁ : u ∉ q₁.support := fun h =>
    (List.nodup_append.mp hsnd).2.2 u h u q₂.start_mem_support rfl
  have h₁ : ∀ e ∈ q₁.reverse.edges, e ∈ K'.edgeSet := by
    intro e he
    rw [Walk.edges_reverse, List.mem_reverse] at he
    exact (hK' e).2 (Or.inl ⟨q₁.edges_subset_edgeSet he, fun h => hyq₁ (h ▸ he)⟩)
  have h₂ : ∀ e ∈ q₂.edges, e ∈ K'.edgeSet := by
    intro e he
    exact (hK' e).2 (Or.inl ⟨q₂.edges_subset_edgeSet he, fun h => hyq₂ (h ▸ he)⟩)
  have hst : s(Q.src, u) = s(t, u) := by rw [hQs]
  have htu' : K'.Adj Q.src u := by
    rw [← mem_edgeSet, hK', hst]; exact Or.inr rfl
  let W : K'.Walk y Q.tgt :=
    (q₁.reverse.transfer K' h₁).append (Walk.cons htu' (q₂.transfer K' h₂))
  have hWsupp : W.support = q₁.support.reverse ++ q₂.support := by
    simp only [W, Walk.support_append, Walk.support_cons, List.tail_cons, Walk.support_transfer,
      Walk.support_reverse]
  have hWedges : W.edges = q₁.edges.reverse ++ s(t, u) :: q₂.edges := by
    simp only [W, Walk.edges_append, Walk.edges_cons, Walk.edges_transfer, Walk.edges_reverse]
    rw [hst]
  have hWpath : W.IsPath := by
    rw [Walk.isPath_def, hWsupp]
    exact ((List.reverse_perm _).append_right _).nodup_iff.mpr hsnd
  have hWpos : 0 < W.length := by
    have : 0 < W.edges.length := by rw [hWedges]; simp
    rwa [Walk.length_edges] at this
  let P' : GPath K' := ⟨y, Q.tgt, W, hWpath, hWpos⟩
  have hmemP : ∀ e, e ∈ P.edges ↔ e ∈ q₁.edges ∨ e = s(y, u) ∨ e ∈ q₂.edges := by
    intro e; rw [← hQe.mem_iff, hedges]; simp
  have hmemP' : ∀ e, e ∈ P'.edges ↔ e ∈ q₁.edges ∨ e = s(t, u) ∨ e ∈ q₂.edges := by
    intro e; show e ∈ W.edges ↔ _; rw [hWedges]; simp
  have htuK : s(t, u) ∉ K.edgeSet := hadj
  have hcov : ∀ e, e ∈ K'.edgeSet ↔ (e ∈ K.edgeSet ∧ e ∉ P.edges) ∨ e ∈ P'.edges := by
    intro e
    rw [hK' e, hmemP e, hmemP' e]
    have a1 : e ∈ q₁.edges → e ∈ K.edgeSet := fun h => q₁.edges_subset_edgeSet h
    have a2 : e ∈ q₂.edges → e ∈ K.edgeSet := fun h => q₂.edges_subset_edgeSet h
    have a3 : e ∈ q₁.edges → e ≠ s(y, u) := fun h h' => hyq₁ (h' ▸ h)
    have a4 : e ∈ q₂.edges → e ≠ s(y, u) := fun h h' => hyq₂ (h' ▸ h)
    constructor
    · rintro (⟨hK, hy⟩ | h)
      · by_cases h1 : e ∈ q₁.edges
        · exact Or.inr (Or.inl h1)
        · by_cases h2 : e ∈ q₂.edges
          · exact Or.inr (Or.inr (Or.inr h2))
          · refine Or.inl ⟨hK, ?_⟩
            rintro (h | h | h)
            · exact h1 h
            · exact hy h
            · exact h2 h
      · exact Or.inr (Or.inr (Or.inl h))
    · rintro (⟨hK, hn⟩ | h1 | h2 | h3)
      · exact Or.inl ⟨hK, fun h => hn (Or.inr (Or.inl h))⟩
      · exact Or.inl ⟨a1 h1, a3 h1⟩
      · exact Or.inr h2
      · exact Or.inl ⟨a2 h3, a4 h3⟩
  have hnew : ∀ e ∈ P'.edges, e ∈ P.edges ∨ e ∉ K.edgeSet := by
    intro e he
    rw [hmemP' e] at he
    rw [hmemP e]
    rcases he with he | rfl | he
    · exact Or.inl (Or.inl he)
    · exact Or.inr htuK
    · exact Or.inl (Or.inr (Or.inr he))
  obtain ⟨D', hsize, hP'mem, hends, htrans, hcovr⟩ := D.replace_supp hP P' hcov hnew
  refine ⟨D', hsize, fun w => ?_, htrans, fun Q' hQ' => ?_, P', hP'mem, rfl, fun z hz => ?_⟩
  · have h1 := hends w
    have h2 : P'.endsAt w = (if y = w then 1 else 0) + (if Q.tgt = w then 1 else 0) := rfl
    have h3 : P.endsAt w = (if t = w then 1 else 0) + (if Q.tgt = w then 1 else 0) := by
      rw [← hQends]; simp only [GPath.endsAt, hQs]
    omega
  · rcases hcovr Q' hQ' with rfl | ⟨Q₀, hQ₀, hsrc, htgt, hs₀⟩
    · refine ⟨P, hP, fun x hx => ?_, fun w hw hwe => ?_⟩
      · have hx' : x ∈ W.support := hx
        rw [hWsupp, List.mem_append, List.mem_reverse] at hx'
        have : x ∈ Q.walk.support := by
          rw [hq, hsupp, List.mem_append]; exact hx'
        exact Or.inl ((hQsupp x).1 this)
      · have hwy : w ≠ y := fun h => hw (Or.inr h)
        rcases hwe with h | h
        · exact absurd h.symm hwy
        · exact GPath.end_of_endsAt_eq hQends (Or.inr h)
    · exact ⟨Q₀, hQ₀, fun x hx => Or.inl (hs₀ ▸ hx), fun w _ h => by
        rw [← hsrc, ← htgt]; exact h⟩
  · have : [u, z] <:+: q₁.support ++ q₂.support := by
      rw [← hsupp, ← hq]; exact hz
    have h2 := infix_pair_of_append this huq₁
    show [u, z] <:+: W.support
    rw [hWsupp]
    exact h2.trans (List.suffix_append _ _).isInfix

/-- `reroute_move` with end-path tracking. -/
theorem PathDecomp.reroute_move_track (D : PathDecomp K) {t u y : U}
    (hadj : ¬ K.Adj t u)
    (hK' : ∀ e, e ∈ K'.edgeSet ↔ (e ∈ K.edgeSet ∧ e ≠ s(y, u)) ∨ e = s(t, u))
    {P : GPath K} (hP : P ∈ D.paths)
    (hocc : (P.src = t ∧ [y, u] <:+: P.walk.support) ∨ (P.tgt = t ∧ [u, y] <:+: P.walk.support)) :
    ∃ D' : PathDecomp K', D'.size = D.size ∧
      (∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if y = w then 1 else 0)) ∧
      (∀ Q ∈ D.paths, Q ≠ P → ∃ Q' ∈ D'.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
        Q'.walk.support = Q.walk.support) ∧
      Tracks D D' {t, y} u ∧
      ∃ P' ∈ D'.paths, ∀ x z, x ≠ t →
        ((P.src = x ∧ [z, u] <:+: P.walk.support) ∨ (P.tgt = x ∧ [u, z] <:+: P.walk.support)) →
        (P'.tgt = x ∧ [u, z] <:+: P'.walk.support) := by
  rcases hocc with ⟨hs, hinf⟩ | ⟨ht, hinf⟩
  · obtain ⟨D', h1, h2, h3, h4, P', hP', hP't, hP'inf⟩ :=
      D.reroute_core_track hadj hK' hP P hs hinf (List.Perm.refl _) (fun _ => rfl)
        (fun _ => Iff.rfl)
    refine ⟨D', h1, h2, h3, h4, P', hP', fun x z hx hxz => ?_⟩
    rcases hxz with ⟨h, -⟩ | ⟨h, hz⟩
    · exact absurd (h.symm.trans hs) hx
    · exact ⟨hP't.trans h, hP'inf z hz⟩
  · have hinf' : [y, u] <:+: P.reverse.walk.support := by
      simpa [GPath.reverse, Walk.support_reverse] using hinf.reverse
    obtain ⟨D', h1, h2, h3, h4, P', hP', hP't, hP'inf⟩ :=
      D.reroute_core_track hadj hK' hP P.reverse ht hinf' (by simp [List.reverse_perm])
        (fun w => P.reverse_endsAt w) (fun w => by simp [GPath.reverse, Walk.support_reverse])
    refine ⟨D', h1, h2, h3, h4, P', hP', fun x z hx hxz => ?_⟩
    rcases hxz with ⟨h, hz⟩ | ⟨h, -⟩
    · refine ⟨hP't.trans h, hP'inf z ?_⟩
      simpa [GPath.reverse, Walk.support_reverse] using hz.reverse
    · exact absurd (h.symm.trans ht) hx

/-- `fan_exec` with end-path tracking: away from the chain and the target, ends stay on the same
paths, whose vertex sets grow by at most `u`. -/
theorem fan_exec_track (u : U) (xs : List U) : ∀ {K : SimpleGraph U} (D : PathDecomp K) (t : U),
    (t :: xs).Nodup → FanChain D u (t :: xs) → t ≠ u → ¬ K.Adj t u →
    ∀ K' : SimpleGraph U, (∀ e, e ∈ K'.edgeSet ↔ e ∈ K.edgeSet ∨ e = s(t, u)) →
    ∃ D' : PathDecomp K', D'.size = D.size ∧
      (∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if u = w then 1 else 0)) ∧
      Tracks D D' {w | w ∈ t :: xs ∨ w = u} u := by
  induction xs with
  | nil =>
    intro K D t _ hch _ hadj K' hK'
    obtain ⟨-, x, hx, P, hP, hend, hu⟩ := hch
    simp only [List.getLast?_singleton, Option.some.injEq] at hx
    subst hx
    obtain ⟨D', h1, h2, h3, -⟩ := D.append_move_track hadj hK' hP hend hu
    refine ⟨D', h1, h2, h3.mono ?_⟩
    intro w hw
    rcases hw with rfl | rfl
    · exact Or.inl List.mem_cons_self
    · exact Or.inr rfl
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
    obtain ⟨D₁, hs₁, he₁, htrans, htr₁, hP'⟩ := D.reroute_move_track hadj hK₁ hP hocc
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
    obtain ⟨D', hs', he', htr'⟩ := ih D₁ y (List.nodup_cons.mp hnd).2 hch₁ hyu' hadj₁ K' hK'₁
    refine ⟨D', hs'.trans hs₁, fun w => ?_, (htr₁.trans htr').mono ?_⟩
    · have a := he' w
      have b := he₁ w
      omega
    · intro w hw
      rcases hw with (rfl | rfl) | (hw | hw)
      · exact Or.inl List.mem_cons_self
      · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
      · exact Or.inl (List.mem_cons_of_mem _ hw)
      · exact Or.inr hw

omit [DecidableEq U] in
/-- Every vertex of a Fan chain after the first is a neighbour of the target. -/
theorem FanPre.adj_of_mem {D : PathDecomp K} {u : U} :
    ∀ (t : U) (xs : List U), FanPre D u (t :: xs) → ∀ x ∈ xs, K.Adj x u
  | _, [], _, x, hx => absurd hx List.not_mem_nil
  | _, y :: rest, h, x, hx => by
    obtain ⟨hp, h'⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact FanPred.adj hp
    · exact FanPre.adj_of_mem y rest h' x hx

/-- **Fan's lemma with end paths** (t6-dense, Lemma 4.1).  As `fan_single_supp`: from `D'` of
`G' = G − uv` with `ends v > #{w ∈ N_{G'}(u) : ends w = 0}`, a decomposition `D` of `G` moving one
end from `v` to `u`.  Moreover every path of `D` comes from one path of `D'`: its vertex set lies
in that path plus `u`, and each of its ends `w ∉ {u, v} ∪ N_{G'}(u)` is an end of that path. -/
theorem fan_single_track [Fintype U] {G G' : SimpleGraph U} [DecidableRel G'.Adj] {u v : U}
    (huv : G.Adj u v) (hG' : ∀ e, e ∈ G'.edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(u, v))
    (D' : PathDecomp G')
    (h : (Finset.univ.filter (fun w => G'.Adj u w ∧ D'.ends w = 0)).card < D'.ends v) :
    ∃ D : PathDecomp G, D.size = D'.size ∧ D.ends u = D'.ends u + 1 ∧
      D.ends v + 1 = D'.ends v ∧ (∀ w, w ≠ u → w ≠ v → D.ends w = D'.ends w) ∧
      Tracks D' D {w | w = u ∨ w = v ∨ G'.Adj w u} u := by
  have huv' : u ≠ v := huv.ne
  have hvu : ¬ G'.Adj v u := by
    rw [← mem_edgeSet, hG']
    rintro ⟨-, h⟩
    exact h Sym2.eq_swap
  obtain ⟨t, ht, xs, hnd, hch⟩ := fan_exists_chain D' u {v} (by simpa using huv')
    (by
      intro t ht
      rw [Finset.mem_singleton] at ht
      subst ht
      exact hvu)
    (by simpa using h)
  obtain rfl : t = v := Finset.mem_singleton.mp ht
  have hK : ∀ e, e ∈ G.edgeSet ↔ e ∈ G'.edgeSet ∨ e = s(t, u) := by
    intro e
    rw [hG' e]
    have hvu' : s(t, u) = s(u, t) := Sym2.eq_swap
    have : s(u, t) ∈ G.edgeSet := huv
    constructor
    · intro he
      by_cases h' : e = s(u, t)
      · exact Or.inr (h'.trans hvu'.symm)
      · exact Or.inl ⟨he, h'⟩
    · rintro (⟨he, -⟩ | rfl)
      · exact he
      · rw [hvu']; exact this
  obtain ⟨D, hs, he, htr⟩ := fan_exec_track u xs D' t hnd hch (fun h => huv' h.symm) hvu G hK
  refine ⟨D, hs, ?_, ?_, ?_, htr.mono ?_⟩
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
  · intro w hw
    rcases hw with hw | hw
    · rcases List.mem_cons.mp hw with rfl | hw
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (FanPre.adj_of_mem t xs hch.1 w hw))
    · exact Or.inl hw

end track

section systems

variable {V : Type u} [DecidableEq V]

/-- A **constraint system** on end paths: avoidance constraints `(c, A)` (every path with an end
at `c` avoids `A`) and distinctness constraints `(p, q)` (no path has both `p` and `q` as ends). -/
structure CSys (V : Type u) where
  /-- avoidance constraints `(c, A)` -/
  av : List (V × Finset V)
  /-- distinctness constraints `(p, q)` -/
  ne : List (V × V)

/-- `w` is a constrained vertex: a tail of an avoidance constraint or an end of a distinctness
constraint. -/
def CSys.Touched (S : CSys V) (w : V) : Prop :=
  (∃ cA ∈ S.av, cA.1 = w) ∨ (∃ pq ∈ S.ne, pq.1 = w ∨ pq.2 = w)

/-- `w` is avoided by some avoidance constraint (a *head*). -/
def CSys.Avoided (S : CSys V) (w : V) : Prop := ∃ cA ∈ S.av, w ∈ cA.2

/-- `D` satisfies the system `S`. -/
def CSys.Sat {G : SimpleGraph V} (S : CSys V) (D : PathDecomp G) : Prop :=
  (∀ cA ∈ S.av, ∀ P ∈ D.paths, (P.src = cA.1 ∨ P.tgt = cA.1) → ∀ a ∈ cA.2, a ∉ P.walk.support) ∧
  (∀ pq ∈ S.ne, ∀ P ∈ D.paths, (P.src = pq.1 ∨ P.tgt = pq.1) → ¬ (P.src = pq.2 ∨ P.tgt = pq.2))

/-- `G` has a Lovász decomposition satisfying `S`. -/
def CSys.Good [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : CSys V) : Prop :=
  ∃ D : PathDecomp G, (∀ w, D.ends w = G.degree w % 2) ∧ S.Sat D

/-- A one-constraint system is `AvoidDecomp`. -/
theorem CSys.good_single_iff [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (c : V)
    (A : Finset V) : CSys.Good G ⟨[(c, A)], []⟩ ↔ AvoidDecomp G c A := by
  constructor
  · rintro ⟨D, hD, hav, -⟩
    exact ⟨D, hD, fun P hP hend => hav (c, A) List.mem_cons_self P hP hend⟩
  · rintro ⟨D, hD, hav⟩
    refine ⟨D, hD, fun cA hcA => ?_, fun pq hpq => absurd hpq List.not_mem_nil⟩
    rw [List.mem_singleton] at hcA
    subst hcA
    exact hav

omit [DecidableEq V] in
/-- **Tracking carries systems.** If every path of `D` is tracked by `D'` away from a set that
contains no constrained vertex, and `u` is not avoided, then `D` satisfies every system that `D'`
satisfies. -/
theorem CSys.sat_of_tracks [DecidableEq V] {K K' : SimpleGraph V} {D' : PathDecomp K'}
    {D : PathDecomp K} {T : Set V} {u : V} (S : CSys V) (htr : Tracks D' D T u)
    (hT : ∀ w, S.Touched w → w ∉ T) (hu : ¬ S.Avoided u) (hS : S.Sat D') : S.Sat D := by
  refine ⟨fun cA hcA P hP hend a ha haP => ?_, fun pq hpq P hP h1 h2 => ?_⟩
  · obtain ⟨Q, hQ, hsub, hends⟩ := htr P hP
    have hQend := hends cA.1 (hT _ (Or.inl ⟨cA, hcA, rfl⟩)) hend
    rcases hsub a haP with h | h
    · exact hS.1 cA hcA Q hQ hQend a ha h
    · exact hu ⟨cA, hcA, h ▸ ha⟩
  · obtain ⟨Q, hQ, -, hends⟩ := htr P hP
    have e1 := hends pq.1 (hT _ (Or.inr ⟨pq, hpq, Or.inl rfl⟩)) h1
    have e2 := hends pq.2 (hT _ (Or.inr ⟨pq, hpq, Or.inr rfl⟩)) h2
    exact hS.2 pq hpq Q hQ e1 e2

/-- **Fan transfers carry constraint systems.**  As `fan_single_supp`, and the new decomposition
satisfies every system `S` satisfied by the old one, provided no constrained vertex is `u`, `v` or
a neighbour of `u` in `G'`, and `u` is not avoided. -/
theorem csys_fan_transfer [Fintype V] {G G' : SimpleGraph V} [DecidableRel G'.Adj] {u v : V}
    (huv : G.Adj u v) (hG' : ∀ e, e ∈ G'.edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(u, v))
    (D' : PathDecomp G')
    (h : (Finset.univ.filter (fun w => G'.Adj u w ∧ D'.ends w = 0)).card < D'.ends v)
    (S : CSys V) (hfar : ∀ w, S.Touched w → w ≠ u ∧ w ≠ v ∧ ¬ G'.Adj w u)
    (hu : ¬ S.Avoided u) (hS : S.Sat D') :
    ∃ D : PathDecomp G, D.size = D'.size ∧ D.ends u = D'.ends u + 1 ∧
      D.ends v + 1 = D'.ends v ∧ (∀ w, w ≠ u → w ≠ v → D.ends w = D'.ends w) ∧ S.Sat D := by
  obtain ⟨D, h1, h2, h3, h4, htr⟩ := fan_single_track huv hG' D' h
  refine ⟨D, h1, h2, h3, h4, S.sat_of_tracks htr (fun w hw hwT => ?_) hu hS⟩
  obtain ⟨a, b, c⟩ := hfar w hw
  rcases hwT with h | h | h
  · exact a h
  · exact b h
  · exact c h

variable [Fintype V]

/-- **Lovász's Case I for constraint systems.**  Let `g` be the even vertex of `G` and `u ∈ N(g)`
a *free* target: no constrained vertex lies in `N[u] ∪ {g}`, and `u` is not avoided.  If `G − gu`
has a Lovász decomposition satisfying `S`, so does `G`.  No admissibility of the child
`(G − gu, S)` is assumed. -/
theorem csys_caseI (G : SimpleGraph V) [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1)
    {g u : V} (hg : g ∈ evenSet G) (hgu : G.Adj g u) (S : CSys V)
    (hfar : ∀ w, S.Touched w → w ≠ u ∧ w ≠ g ∧ ¬ G.Adj w u) (hu : ¬ S.Avoided u)
    (hchild : S.Good (delEdge G g u)) : S.Good G := by
  classical
  obtain ⟨D', hD', hS'⟩ := hchild
  have hgu' : g ≠ u := hgu.ne
  have huniq : ∀ w ∈ evenSet G, w = g := fun w hw => Finset.card_le_one.mp hev w hw g hg
  have hodd : ∀ w, w ≠ g → 0 < G.degree w → G.degree w % 2 = 1 := by
    intro w hwg hpos
    have : w ∉ evenSet G := fun h => hwg (huniq w h)
    rw [mem_evenSet_iff] at this
    omega
  have hgd := mem_evenSet_iff.mp hg
  have hdeg := delEdge_degree G hgu
  have hG' : ∀ e, e ∈ (delEdge G g u).edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(u, g) := by
    intro e
    rw [delEdge_edgeSet, Sym2.eq_swap (a := u)]
  have hD'g : D'.ends g = 1 := by
    rw [hD']
    have := hdeg g
    simp only [hgu', ite_true, ite_false] at this
    omega
  have hcount : (Finset.univ.filter (fun w => (delEdge G g u).Adj u w ∧ D'.ends w = 0)).card <
      D'.ends g := by
    have hempty : Finset.univ.filter (fun w => (delEdge G g u).Adj u w ∧ D'.ends w = 0) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun w hw => ?_
      rw [Finset.mem_filter] at hw
      obtain ⟨-, hadj, h0⟩ := hw
      have hwg : w ≠ g := fun h => hadj.2 (by rw [h, Sym2.eq_swap])
      have hwu : w ≠ u := hadj.ne.symm
      rw [hD'] at h0
      have hdw := hdeg w
      simp only [hwg, hwu, ite_false, add_zero] at hdw
      have := hodd w hwg ((G.degree_pos_iff_exists_adj w).mpr ⟨u, hadj.1.symm⟩)
      omega
    rw [hempty, Finset.card_empty, hD'g]
    omega
  have hfar' : ∀ w, S.Touched w → w ≠ u ∧ w ≠ g ∧ ¬ (delEdge G g u).Adj w u :=
    fun w hw => ⟨(hfar w hw).1, (hfar w hw).2.1, fun h => (hfar w hw).2.2 h.1⟩
  obtain ⟨D, -, hDu, hDg, hDrest, hSD⟩ :=
    csys_fan_transfer hgu.symm hG' D' hcount S hfar' hu hS'
  refine ⟨D, fun w => ?_, hSD⟩
  by_cases hwu : w = u
  · subst hwu
    rw [hDu, hD']
    have := hdeg w
    simp only [hgu'.symm, ite_true, ite_false] at this
    have := hodd w hgu'.symm ((G.degree_pos_iff_exists_adj w).mpr ⟨g, hgu.symm⟩)
    omega
  · by_cases hwg : w = g
    · subst hwg
      rw [hD'g] at hDg
      rw [show D.ends w = 0 by omega, hgd.2]
    · rw [hDrest w hwu hwg, hD']
      have := hdeg w
      simp only [hwg, hwu, ite_false, add_zero] at this
      rw [this]

end systems

section caseAdj

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- A sub-system is satisfied when the system is. -/
theorem CSys.sat_cons {G : SimpleGraph V} {D : PathDecomp G} {cA : V × Finset V} {S : CSys V}
    (h : CSys.Sat ⟨cA :: S.av, S.ne⟩ D) : S.Sat D :=
  ⟨fun dB hdB => h.1 dB (List.mem_cons_of_mem _ hdB), h.2⟩

omit [Fintype V] in
/-- A path with an end at `v` contributes to `ends v`. -/
theorem PathDecomp.ends_pos_of_end {G : SimpleGraph V} (D : PathDecomp G) {P : GPath G}
    (hP : P ∈ D.paths) {v : V} (h : P.src = v ∨ P.tgt = v) : 0 < D.ends v := by
  have hle : P.endsAt v ≤ D.ends v := by
    unfold PathDecomp.ends
    exact List.le_sum_of_mem (List.mem_map_of_mem hP)
  have : 0 < P.endsAt v := by
    unfold GPath.endsAt
    rcases h with h | h <;> simp [h]
  omega

/-- **Move (M2), a tail at the even vertex, for constraint systems.**  Let `g` be the even vertex,
`c ∈ N(g)` an odd tail with avoid set `A ∌ c`, and `S` further constraints touching neither `g` nor
`c` and not avoiding `c`.  If `G − gc` (where `c` is even) has a Lovász decomposition whose path
ending at `g` avoids `A ∪ {c}` and which satisfies `S`, then appending `gc` gives a Lovász
decomposition of `G` whose path ending at `c` avoids `A` and which satisfies `S`. -/
theorem csys_case_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    {g c : V} (hg : g ∈ evenSet G) (hgc : G.Adj g c) (hc : G.degree c % 2 = 1) {A : Finset V}
    (hcA : c ∉ A) (S : CSys V) (hS : ∀ w, S.Touched w → w ≠ g ∧ w ≠ c) (hcS : ¬ S.Avoided c)
    (hchild : CSys.Good (delEdge G g c) ⟨(g, insert c A) :: S.av, S.ne⟩) :
    CSys.Good G ⟨(c, A) :: S.av, S.ne⟩ := by
  classical
  obtain ⟨D', hD', hsat⟩ := hchild
  have hgc' : g ≠ c := hgc.ne
  have hgd := mem_evenSet_iff.mp hg
  have hdeg := delEdge_degree G hgc
  have hD'g : D'.ends g = 1 := by
    rw [hD']
    have := hdeg g
    simp only [hgc', ite_true, ite_false] at this
    omega
  have hD'c : D'.ends c = 0 := by
    rw [hD']
    have := hdeg c
    simp only [hgc'.symm, ite_true, ite_false] at this
    omega
  obtain ⟨P, hP, hPend⟩ := D'.exists_end_of_pos (by rw [hD'g]; omega)
  have hPav : ∀ a ∈ insert c A, a ∉ P.walk.support :=
    hsat.1 (g, insert c A) List.mem_cons_self P hP hPend
  have hcP : c ∉ P.walk.support := hPav c (Finset.mem_insert_self _ _)
  have hnadj : ¬ (delEdge G g c).Adj g c := fun h => h.2 rfl
  have hK : ∀ e, e ∈ G.edgeSet ↔ e ∈ (delEdge G g c).edgeSet ∨ e = s(g, c) := by
    intro e
    rw [delEdge_edgeSet]
    constructor
    · intro he
      by_cases h : e = s(g, c)
      · exact Or.inr h
      · exact Or.inl ⟨he, h⟩
    · rintro (⟨he, -⟩ | rfl)
      · exact he
      · exact hgc
  obtain ⟨D, -, hends, htr, hcopy⟩ := D'.append_move_track hnadj hK hP hPend hcP
  have hSD : S.Sat D := S.sat_of_tracks htr (fun w hw hwT => by
      obtain ⟨h1, h2⟩ := hS w hw
      rcases hwT with h | h
      · exact h1 h
      · exact h2 h) hcS (CSys.sat_cons hsat)
  refine ⟨D, fun w => ?_, ⟨fun cA hcA' => ?_, hSD.2⟩⟩
  · have h := hends w
    by_cases hwg : w = g
    · rw [hwg] at h ⊢
      have e1 : (if g = g then 1 else 0) = 1 := by simp
      have e2 : (if c = g then 1 else 0) = 0 := by simp [hgc'.symm]
      rw [e1, e2, hD'g] at h
      rw [show D.ends g = 0 by omega, hgd.2]
    · by_cases hwc : w = c
      · rw [hwc] at h ⊢
        have e1 : (if g = c then 1 else 0) = 0 := by simp [hgc']
        have e2 : (if c = c then 1 else 0) = 1 := by simp
        rw [e1, e2, hD'c] at h
        rw [show D.ends c = 1 by omega, hc]
      · simp only [Ne.symm hwg, Ne.symm hwc, ite_false, add_zero] at h
        rw [h, hD']
        have := hdeg w
        simp only [hwg, hwc, ite_false, add_zero] at this
        rw [this]
  · rcases List.mem_cons.mp hcA' with rfl | hcA'
    · intro Q hQ hQend a ha haQ
      rcases hcopy Q hQ with hsub | ⟨Q₀, hQ₀, hsrc, htgt, -⟩
      · rcases hsub a haQ with h | h
        · exact hPav a (Finset.mem_insert_of_mem ha) h
        · exact hcA (h ▸ ha)
      · have := D'.ends_pos_of_end hQ₀ (v := c) (by rw [← hsrc, ← htgt]; exact hQend)
        omega
    · exact hSD.1 cA hcA'

end caseAdj

section caseLeaf

variable {V : Type u} [DecidableEq V]

omit [DecidableEq V] in
/-- Ends of a path whose support is the image of another path's support. -/
theorem GPath.ends_of_support_map {W' : Type*} {G : SimpleGraph V} {H : SimpleGraph W'}
    (Q : GPath G) (P : GPath H) (f : W' → V) (h : Q.walk.support = P.walk.support.map f) :
    Q.src = f P.src ∧ Q.tgt = f P.tgt := by
  constructor
  · have h1 := Q.walk.cons_tail_support
    have h2 := P.walk.cons_tail_support
    rw [← h1, ← h2, List.map_cons] at h
    exact (List.cons.inj h).1
  · have hq : Q.walk.support.getLast? = some Q.tgt := by
      rw [List.getLast?_eq_some_getLast Q.walk.support_ne_nil, Walk.getLast_support]
    have hp : P.walk.support.getLast? = some P.tgt := by
      rw [List.getLast?_eq_some_getLast P.walk.support_ne_nil, Walk.getLast_support]
    rw [h, List.getLast?_map, hp] at hq
    simpa using hq.symm

/-- The system on the leaf graph `apex (G − yc) {y}` used by move (M4): the leaf `none` stands for
the tail `c` and avoids `A ∪ {c}`; every other constraint is lifted along `some`. -/
def CSys.liftLeaf (c : V) (A : Finset V) (S : CSys V) : CSys (Option V) :=
  ⟨(none, insert (some c) (A.image some)) :: S.av.map (fun dB => (some dB.1, dB.2.image some)),
    S.ne.map (fun pq => (some pq.1, some pq.2))⟩

/-- **Move (M4), the leaf step at a tail, for constraint systems.**  Let `cy ∈ E(G)`, and let `DH`
decompose the leaf graph `apex (G − yc) {y}` (the leaf `none` at `y` stands for `c`), with no end at
`c` and one at the leaf, satisfying the lifted system.  Merging the leaf into `c` gives a
decomposition of `G` with one end at `c`, the ends of `DH` elsewhere, whose path ending at `c` avoids
`A` and which satisfies `S`, provided `S` does not touch or avoid `c` and `c ∉ A`. -/
theorem csys_case_leaf [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {c y : V}
    (hcy : G.Adj c y) {A : Finset V} (hcA : c ∉ A) (S : CSys V) (hS : ∀ w, S.Touched w → w ≠ c)
    (hcS : ¬ S.Avoided c) (DH : PathDecomp (apex (delEdge G y c) {y}))
    (hc0 : DH.ends (some c) = 0) (hn1 : DH.ends none = 1) (hsat : (CSys.liftLeaf c A S).Sat DH) :
    ∃ D : PathDecomp G, D.ends c = 1 ∧ (∀ w, w ≠ c → D.ends w = DH.ends (some w)) ∧
      CSys.Sat ⟨(c, A) :: S.av, S.ne⟩ D := by
  classical
  -- the leaf path avoids `some c`
  have hleaf : ∀ P ∈ DH.paths, (P.src = none ∨ P.tgt = none) →
      ∀ o ∈ insert (some c) (A.image some), o ∉ P.walk.support :=
    hsat.1 _ List.mem_cons_self
  have hsep : Separates DH (some c) none := by
    rintro P hP ⟨hc, hn⟩
    exact hleaf P hP (P.end_of_pendant apex_none_pendant hn) (some c)
      (Finset.mem_insert_self _ _) hc
  obtain ⟨D, hDc, hDw, hback, -⟩ := leaf_merge G hcy DH hsep
  refine ⟨D, by rw [hDc, hc0, hn1], hDw, ⟨fun cA hcA' => ?_, fun pq hpq Q hQ h1 h2 => ?_⟩⟩
  · -- avoidance constraints
    intro Q hQ hQend a ha haQ
    obtain ⟨P, hP, hsupp⟩ := hback Q hQ
    obtain ⟨hs, ht⟩ := Q.ends_of_support_map P (mergeMap c) hsupp
    have hmem : a ∈ (P.walk.support).map (mergeMap c) := hsupp ▸ haQ
    obtain ⟨o, ho, hoa⟩ := List.mem_map.mp hmem
    rcases List.mem_cons.mp hcA' with rfl | hcA'
    · -- the tail `c`: `P` ends at the leaf
      have hPn : P.src = none ∨ P.tgt = none := by
        have hpos : ∀ x, (P.src = some x ∨ P.tgt = some x) → x ≠ c := by
          rintro x hx rfl
          have := DH.ends_pos_of_end hP hx
          omega
        rcases hQend with h | h
        · left
          rw [hs] at h
          cases hsrc : P.src with
          | none => rfl
          | some x =>
            rw [hsrc, mergeMap_some] at h
            exact absurd h (hpos x (Or.inl hsrc))
        · right
          rw [ht] at h
          cases htgt : P.tgt with
          | none => rfl
          | some x =>
            rw [htgt, mergeMap_some] at h
            exact absurd h (hpos x (Or.inr htgt))
      cases o with
      | none => rw [mergeMap_none] at hoa; exact hcA (hoa ▸ ha)
      | some b =>
        rw [mergeMap_some] at hoa
        subst hoa
        exact hleaf P hP hPn (some b) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ha)) ho
    · -- another tail `d ≠ c`
      have hdc : cA.1 ≠ c := hS cA.1 (Or.inl ⟨cA, hcA', rfl⟩)
      have hPend : P.src = some cA.1 ∨ P.tgt = some cA.1 := by
        rcases hQend with h | h
        · left
          rw [hs] at h
          cases hsrc : P.src with
          | none => rw [hsrc, mergeMap_none] at h; exact absurd h.symm hdc
          | some x => rw [hsrc, mergeMap_some] at h; rw [h]
        · right
          rw [ht] at h
          cases htgt : P.tgt with
          | none => rw [htgt, mergeMap_none] at h; exact absurd h.symm hdc
          | some x => rw [htgt, mergeMap_some] at h; rw [h]
      have hlift := hsat.1 (some cA.1, cA.2.image some)
        (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨cA, hcA', rfl⟩)) P hP hPend
      cases o with
      | none => rw [mergeMap_none] at hoa; exact hcS ⟨cA, hcA', hoa ▸ ha⟩
      | some b =>
        rw [mergeMap_some] at hoa
        subst hoa
        exact hlift (some b) (Finset.mem_image_of_mem _ ha) ho
  · -- distinctness constraints
    obtain ⟨P, hP, hsupp⟩ := hback Q hQ
    obtain ⟨hs, ht⟩ := Q.ends_of_support_map P (mergeMap c) hsupp
    have hp1 : pq.1 ≠ c := hS pq.1 (Or.inr ⟨pq, hpq, Or.inl rfl⟩)
    have hp2 : pq.2 ≠ c := hS pq.2 (Or.inr ⟨pq, hpq, Or.inr rfl⟩)
    have lift : ∀ x, x ≠ c → (Q.src = x ∨ Q.tgt = x) → (P.src = some x ∨ P.tgt = some x) := by
      intro x hx h
      rcases h with h | h
      · left
        rw [hs] at h
        cases hsrc : P.src with
        | none => rw [hsrc, mergeMap_none] at h; exact absurd h.symm hx
        | some z => rw [hsrc, mergeMap_some] at h; rw [h]
      · right
        rw [ht] at h
        cases htgt : P.tgt with
        | none => rw [htgt, mergeMap_none] at h; exact absurd h.symm hx
        | some z => rw [htgt, mergeMap_some] at h; rw [h]
    exact hsat.2 (some pq.1, some pq.2) (List.mem_map.mpr ⟨pq, hpq, rfl⟩) P hP
      (lift pq.1 hp1 h1) (lift pq.2 hp2 h2)

end caseLeaf

section conjectures

/-- **The local bipartite in-degree-one condition** on a list of avoidance constraints (CLT form B):
the tails are odd and pairwise distinct, the avoid sets are pairwise disjoint (every vertex is
avoided by at most one end path), no tail is avoided, and every avoid set is admissible for its
tail (it misses `N[c] ∪ N(g)`). -/
def BLocal {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : List (V × Finset V)) : Prop :=
  (L.map Prod.fst).Nodup ∧ (∀ cA ∈ L, G.degree cA.1 % 2 = 1) ∧
  L.Pairwise (fun p q => Disjoint p.2 q.2) ∧ (∀ cA ∈ L, ∀ dB ∈ L, dB.1 ∉ cA.2) ∧
  ∀ cA ∈ L, Admissible G cA.1 cA.2

/-- **Cross-locality**: no avoided vertex is adjacent to any tail. -/
def CrossLocal {V : Type u} (G : SimpleGraph V) (L : List (V × Finset V)) : Prop :=
  ∀ cA ∈ L, ∀ dB ∈ L, ∀ a ∈ cA.2, ¬ G.Adj dB.1 a

/-- **Conjecture CLT-B1.** Every locally bipartite in-degree-one, cross-local system of avoidance
constraints is satisfied by some Lovász decomposition.  (No counterexample: every graph with at
most one even vertex to order 9, random graphs to order 16; manuscript `clt`, experiment E29.) -/
def CLTB1 : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (evenSet G).card ≤ 1 → ∀ L : List (V × Finset V), BLocal G L → CrossLocal G L →
      CSys.Good G ⟨L, []⟩

/-- **Conjecture CLT-B.** The same without cross-locality, when the even vertex (if any) does not
have degree two.  (No counterexample to order 9; every failure of the statement without the degree
condition has `d(g) = 2`.) -/
def CLTB : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (evenSet G).card ≤ 1 → (∀ g ∈ evenSet G, G.degree g ≠ 2) → ∀ L : List (V × Finset V),
      BLocal G L → CSys.Good G ⟨L, []⟩

/-- **Conjecture `L_N`** (route-descent, §V.3): in a graph with all degrees odd, for disjoint
non-adjacent pairs `(cᵢ, aᵢ)`, some Lovász decomposition has the path ending at each `cᵢ` avoiding
`aᵢ`. -/
def LN : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (evenSet G).card = 0 → ∀ L : List (V × V), (L.map Prod.fst ++ L.map Prod.snd).Nodup →
    (∀ p ∈ L, G.degree p.1 % 2 = 1 ∧ ¬ G.Adj p.1 p.2) →
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∀ p ∈ L, ∀ P ∈ D.paths, (P.src = p.1 ∨ P.tgt = p.1) → p.2 ∉ P.walk.support

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- A single admissible constraint is locally bipartite and cross-local. -/
theorem bLocal_single (G : SimpleGraph W) [DecidableRel G.Adj] {c : W} (hc : G.degree c % 2 = 1)
    {A : Finset W} (hA : Admissible G c A) : BLocal G [(c, A)] ∧ CrossLocal G [(c, A)] := by
  refine ⟨⟨by simp, ?_, by simp, ?_, ?_⟩, ?_⟩
  · intro cA hcA; rw [List.mem_singleton] at hcA; subst hcA; exact hc
  · intro cA hcA dB hdB
    rw [List.mem_singleton] at hcA hdB
    subst hcA; subst hdB
    exact fun h => (hA c h).1 rfl
  · intro cA hcA; rw [List.mem_singleton] at hcA; subst hcA; exact hA
  · intro cA hcA dB hdB a ha
    rw [List.mem_singleton] at hcA hdB
    subst hcA; subst hdB
    exact (hA a ha).2.1

/-- `CLT-B1 ⇒ L₁*` (general form): one tail. -/
theorem l1StarGen_of_cltB1 (h : CLTB1.{u}) : L1StarGen.{u} := by
  intro V _ _ G _ hev c hc A hA
  obtain ⟨hB, hX⟩ := bLocal_single G hc hA
  exact (CSys.good_single_iff G c A).mp (h V G hev [(c, A)] hB hX)

/-- `CLT-B1 ⇒ L∞`. -/
theorem lInfty_of_cltB1 (h : CLTB1.{u}) : LInfty.{u} := lInfty_of_l1StarGen (l1StarGen_of_cltB1 h)

/-- `CLT-B1 ⇒ EE`: if `z` is the only even vertex and `x ∈ N(z)`, then `xz` is the terminal edge
at `x` of some Lovász decomposition. -/
theorem ee_of_cltB1 (h : CLTB1.{u}) (G : SimpleGraph W) [DecidableRel G.Adj]
    (hev : (evenSet G).card ≤ 1) {z x : W} (hz : z ∈ evenSet G) (hzx : G.Adj z x) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∃ P ∈ D.paths, (P.src = x ∨ P.tgt = x) ∧ s(x, z) ∈ P.edges :=
  ee_of_L1StarGen (l1StarGen_of_cltB1 h) G hev hz hzx

/-- `CLT-B ⇒ L_N`: a matching of non-adjacent pairs in an all-odd graph is locally bipartite
(heads are distinct, no head is a tail, and there is no even vertex). -/
theorem lN_of_cltB (h : CLTB.{u}) : LN.{u} := by
  intro V _ _ G _ hev L hnd hL
  classical
  have hnone : ∀ g, g ∉ evenSet G := by
    intro g hg; rw [Finset.card_eq_zero] at hev; rw [hev] at hg; exact Finset.notMem_empty g hg
  let L' : List (V × Finset V) := L.map (fun p => (p.1, {p.2}))
  have hnd1 : (L.map Prod.fst).Nodup := (List.nodup_append.mp hnd).1
  have hnd2 : (L.map Prod.snd).Nodup := (List.nodup_append.mp hnd).2.1
  have hdisj : ∀ a ∈ L.map Prod.fst, ∀ b ∈ L.map Prod.snd, a ≠ b :=
    fun a ha b hb => (List.nodup_append.mp hnd).2.2 a ha b hb
  have hB : BLocal G L' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [L', List.map_map]
      exact hnd1
    · intro cA hcA
      simp only [L', List.mem_map] at hcA
      obtain ⟨p, hp, rfl⟩ := hcA
      exact (hL p hp).1
    · simp only [L', List.pairwise_map]
      have h2 : L.Pairwise (fun a b => a.2 ≠ b.2) := List.pairwise_map.mp hnd2
      exact h2.imp (fun hab => Finset.disjoint_singleton.mpr hab)
    · intro cA hcA dB hdB
      simp only [L', List.mem_map] at hcA hdB
      obtain ⟨p, hp, rfl⟩ := hcA
      obtain ⟨q, hq, rfl⟩ := hdB
      rw [Finset.mem_singleton]
      exact hdisj q.1 (List.mem_map_of_mem hq) p.2 (List.mem_map_of_mem hp)
    · intro cA hcA
      simp only [L', List.mem_map] at hcA
      obtain ⟨p, hp, rfl⟩ := hcA
      intro a ha
      rw [Finset.mem_singleton] at ha
      subst ha
      exact ⟨fun h => hdisj p.1 (List.mem_map_of_mem hp) p.2 (List.mem_map_of_mem hp) h.symm,
        (hL p hp).2, fun g hg => absurd hg (hnone g)⟩
  obtain ⟨D, hD, hS, -⟩ := h V G (by rw [hev]; omega) (fun g hg => absurd hg (hnone g)) L' hB
  refine ⟨D, hD, fun p hp P hP hend => hS (p.1, {p.2}) (List.mem_map.mpr ⟨p, hp, rfl⟩) P hP hend
    p.2 (Finset.mem_singleton_self _)⟩

end conjectures

section special

variable {W : Type u} [Fintype W] [DecidableEq W]

omit [Fintype W] [DecidableEq W] in
/-- An end of a path lies on it. -/
theorem GPath.end_mem_support' {G : SimpleGraph W} (P : GPath G) {c : W}
    (h : P.src = c ∨ P.tgt = c) : c ∈ P.walk.support := by
  rcases h with h | h
  · rw [← h]; exact P.walk.start_mem_support
  · rw [← h]; exact P.walk.end_mem_support

/-- **Packed systems are satisfiable** (from `separation_set`).  If all constrained and all avoided
vertices lie in a packed set `X` (pairwise distance at least three), with no tail avoided by its own
constraint and no distinctness constraint of the form `(p, p)`, then some Lovász decomposition
satisfies the whole system: every path meets `X` at most once. -/
theorem csys_good_of_packed (G : SimpleGraph W) [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1)
    {X : Finset W} (hX : Packed G X) (S : CSys W)
    (hav : ∀ cA ∈ S.av, cA.1 ∈ X ∧ cA.2 ⊆ X ∧ cA.1 ∉ cA.2)
    (hne : ∀ pq ∈ S.ne, pq.1 ∈ X ∧ pq.2 ∈ X ∧ pq.1 ≠ pq.2) : S.Good G := by
  obtain ⟨D, hD, hm⟩ := separation_set G hev hX
  refine ⟨D, hD, fun cA hcA P hP hend a ha haP => ?_, fun pq hpq P hP h1 h2 => ?_⟩
  · obtain ⟨hc, hA, hcA'⟩ := hav cA hcA
    have := hm P hP cA.1 hc a (hA ha) (P.end_mem_support' hend) haP
    exact hcA' (this ▸ ha)
  · obtain ⟨hp, hq, hpq'⟩ := hne pq hpq
    exact hpq' (hm P hP pq.1 hp pq.2 hq (P.end_mem_support' h1) (P.end_mem_support' h2))

/-- **Sparse systems are satisfiable** (from `separation_sparse_set`).  If every vertex has at
most one neighbour in `X`, every tail and every avoided vertex lie in `X`, and no avoided vertex is
equal or adjacent to its own tail, then some Lovász decomposition satisfies every avoidance
constraint.  Neither disjointness nor cross-locality is needed. -/
theorem csys_good_of_sparse (G : SimpleGraph W) [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1)
    {X : Finset W} (hone : ∀ v p q, G.Adj v p → G.Adj v q → p ∈ X → q ∈ X → p = q)
    (L : List (W × Finset W)) (hX : ∀ cA ∈ L, cA.1 ∈ X ∧ cA.2 ⊆ X)
    (hloc : ∀ cA ∈ L, ∀ a ∈ cA.2, a ≠ cA.1 ∧ ¬ G.Adj cA.1 a) : CSys.Good G ⟨L, []⟩ := by
  obtain ⟨D, hD, hm⟩ := separation_sparse_set G hev hone
  refine ⟨D, hD, fun cA hcA P hP hend a ha haP => ?_, fun pq hpq => absurd hpq List.not_mem_nil⟩
  rcases hm P hP cA.1 (hX cA hcA).1 a ((hX cA hcA).2 ha) (P.end_mem_support' hend) haP with h | h
  · exact (hloc cA hcA a ha).1 h.symm
  · exact (hloc cA hcA a ha).2 h

end special

end Gallai
