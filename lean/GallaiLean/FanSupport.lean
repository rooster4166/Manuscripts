import GallaiLean.Fan

/-!
# Fan's lemma with vertex sets

Route-descent manuscript, Lemma "Fan's lemma with vertex sets". Fan's addible-edge lemma
(`fan_single`, `fan_grouped`) is proved by a chain of re-routings followed by one append. A
re-routing reverses an initial segment of a path and trades one edge at `u` for another, so it
keeps the vertex set of the path; the append adds `u` to one path. Hence:

* **`fan_single_supp`**, **`fan_grouped_supp`**, **`fan_exec_supp`**: as `fan_single`,
  `fan_grouped`, `fan_exec`, with the extra conclusion that every path of the new decomposition
  has its vertex set inside the vertex set of some path of the old one, together with `u`.

The proofs are those of `FanMoves.lean` and `Fan.lean` (`replace`, `append_move`,
`reroute_core`, `reroute_move`, `fan_exec`, `fan_grouped`, `fan_single`) with the support
bookkeeping added (`*_supp`). The originals are untouched.
-/

open SimpleGraph

namespace Gallai

universe v

variable {U : Type v}

section replace

variable [DecidableEq U] {K K' : SimpleGraph U}

/-- `PathDecomp.replace`, recording that every new path is the new one or keeps the support of
an old one. -/
theorem PathDecomp.replace_supp (D : PathDecomp K) {P : GPath K} (hP : P ∈ D.paths) (P' : GPath K')
    (hcov : ∀ e, e ∈ K'.edgeSet ↔ (e ∈ K.edgeSet ∧ e ∉ P.edges) ∨ e ∈ P'.edges)
    (hnew : ∀ e ∈ P'.edges, e ∈ P.edges ∨ e ∉ K.edgeSet) :
    ∃ D' : PathDecomp K', D'.size = D.size ∧ P' ∈ D'.paths ∧
      (∀ w, D'.ends w + P.endsAt w = D.ends w + P'.endsAt w) ∧
      (∀ Q ∈ D.paths, Q ≠ P → ∃ Q' ∈ D'.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
        Q'.walk.support = Q.walk.support) ∧
      ∀ Q' ∈ D'.paths, Q' = P' ∨ ∃ Q ∈ D.paths, Q'.walk.support = Q.walk.support := by
  obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hP
  have hnd := D.nodup_edges
  rw [hl, List.flatMap_append, List.flatMap_cons] at hnd
  have hmemK : ∀ e, e ∈ K.edgeSet ↔
      e ∈ l₁.flatMap GPath.edges ∨ e ∈ P.edges ∨ e ∈ l₂.flatMap GPath.edges := by
    intro e
    rw [D.covers e, hl, List.flatMap_append, List.flatMap_cons]
    simp only [List.mem_append]
  rw [List.nodup_append, List.nodup_append] at hnd
  obtain ⟨hndA, ⟨hndP, hndB, hPB⟩, hA⟩ := hnd
  have hAP : ∀ e ∈ l₁.flatMap GPath.edges, e ∉ P.edges := fun e he heP =>
    hA e he e (List.mem_append_left _ heP) rfl
  have hAB : ∀ e ∈ l₁.flatMap GPath.edges, e ∉ l₂.flatMap GPath.edges := fun e he heB =>
    hA e he e (List.mem_append_right _ heB) rfl
  have hBP : ∀ e ∈ l₂.flatMap GPath.edges, e ∉ P.edges := fun e he heP =>
    hPB e heP e he rfl
  have h₁ : ∀ Q ∈ l₁, ∀ e ∈ Q.edges, e ∈ K'.edgeSet := fun Q hQ e he => by
    have heA : e ∈ l₁.flatMap GPath.edges := List.mem_flatMap.mpr ⟨Q, hQ, he⟩
    exact (hcov e).2 (Or.inl ⟨(hmemK e).2 (Or.inl heA), hAP e heA⟩)
  have h₂ : ∀ Q ∈ l₂, ∀ e ∈ Q.edges, e ∈ K'.edgeSet := fun Q hQ e he => by
    have heB : e ∈ l₂.flatMap GPath.edges := List.mem_flatMap.mpr ⟨Q, hQ, he⟩
    exact (hcov e).2 (Or.inl ⟨(hmemK e).2 (Or.inr (Or.inr heB)), hBP e heB⟩)
  let L := l₁.pmap (fun Q hQ => Q.transfer hQ) h₁ ++ P' :: l₂.pmap (fun Q hQ => Q.transfer hQ) h₂
  have hLe : L.flatMap GPath.edges =
      l₁.flatMap GPath.edges ++ (P'.edges ++ l₂.flatMap GPath.edges) := by
    simp only [L, List.flatMap_append, List.flatMap_cons, flatMap_pmap_transfer]
  have hP'nd : P'.edges.Nodup := P'.isPath.isTrail.edges_nodup
  have hnd' : (L.flatMap GPath.edges).Nodup := by
    rw [hLe, List.nodup_append, List.nodup_append]
    refine ⟨hndA, ⟨hP'nd, hndB, ?_⟩, ?_⟩
    · intro a ha b hb hab
      subst hab
      rcases hnew a ha with h | h
      · exact hBP a hb h
      · exact h ((hmemK a).2 (Or.inr (Or.inr hb)))
    · intro a ha b hb hab
      subst hab
      rcases List.mem_append.mp hb with hb | hb
      · rcases hnew a hb with h | h
        · exact hAP a ha h
        · exact h ((hmemK a).2 (Or.inl ha))
      · exact hAB a ha hb
  have hcov' : ∀ e, e ∈ K'.edgeSet ↔ e ∈ L.flatMap GPath.edges := by
    intro e
    rw [hcov e, hLe, hmemK e]
    simp only [List.mem_append]
    constructor
    · rintro (⟨h | h | h, hn⟩ | h)
      · exact Or.inl h
      · exact absurd h hn
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · rintro (h | h | h)
      · exact Or.inl ⟨Or.inl h, hAP e h⟩
      · exact Or.inr h
      · exact Or.inl ⟨Or.inr (Or.inr h), hBP e h⟩
  let D' : PathDecomp K' := ⟨L, hnd', hcov'⟩
  refine ⟨D', ?_, ?_, ?_, ?_, ?_⟩
  · simp [D', PathDecomp.size, L, hl]
  · simp [D', L]
  · intro w
    unfold PathDecomp.ends
    simp only [D', L, hl, List.map_append, List.map_cons, List.sum_append, List.sum_cons,
      sum_endsAt_pmap_transfer]
    omega
  · intro Q hQ hQP
    rw [hl, List.mem_append, List.mem_cons] at hQ
    rcases hQ with hQ | hQ | hQ
    · exact ⟨Q.transfer (h₁ Q hQ), List.mem_append_left _ (List.mem_pmap_of_mem hQ),
        rfl, rfl, GPath.transfer_support _ _⟩
    · exact absurd hQ hQP
    · exact ⟨Q.transfer (h₂ Q hQ),
        List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_pmap_of_mem hQ)),
        rfl, rfl, GPath.transfer_support _ _⟩
  · intro Q' hQ'
    change Q' ∈ L at hQ'
    simp only [L, List.mem_append, List.mem_cons, List.mem_pmap] at hQ'
    rcases hQ' with ⟨Q, hQ, rfl⟩ | rfl | ⟨Q, hQ, rfl⟩
    · exact Or.inr ⟨Q, by rw [hl]; exact List.mem_append_left _ hQ, GPath.transfer_support _ _⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨Q, by rw [hl]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hQ),
        GPath.transfer_support _ _⟩

end replace

section moves

variable [DecidableEq U] {K K' : SimpleGraph U}

/-- `append_move`, recording supports: every new path lies in an old path plus `u`. -/
theorem PathDecomp.append_move_supp (D : PathDecomp K) {t u : U} (hadj : ¬ K.Adj t u)
    (hK' : ∀ e, e ∈ K'.edgeSet ↔ e ∈ K.edgeSet ∨ e = s(t, u))
    {P : GPath K} (hP : P ∈ D.paths) (hend : P.src = t ∨ P.tgt = t)
    (hu : u ∉ P.walk.support) :
    ∃ D' : PathDecomp K', D'.size = D.size ∧
      (∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if u = w then 1 else 0)) ∧
      ∀ Q' ∈ D'.paths, ∃ Q ∈ D.paths, ∀ x ∈ Q'.walk.support, x ∈ Q.walk.support ∨ x = u := by
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
  refine ⟨D', hsize, fun w => ?_, fun Q' hQ' => ?_⟩
  have h1 := hends w
  have h2 : P'.endsAt w = (if u = w then 1 else 0) + (if Q.tgt = w then 1 else 0) := rfl
  have h3 : P.endsAt w = (if t = w then 1 else 0) + (if Q.tgt = w then 1 else 0) := by
    rw [← hQends]; simp only [GPath.endsAt, hQs]
  omega
  rcases hcovr Q' hQ' with rfl | ⟨Q₀, hQ₀, hs₀⟩
  · refine ⟨P, hP, fun x hx => ?_⟩
    have : x ∈ (Walk.cons hut (Q.walk.transfer K' hQK)).support := hx
    rw [Walk.support_cons, Walk.support_transfer, List.mem_cons] at this
    rcases this with rfl | h
    · exact Or.inr rfl
    · exact Or.inl ((hQsupp x).1 h)
  · exact ⟨Q₀, hQ₀, fun x hx => Or.inl (hs₀ ▸ hx)⟩

/-- `reroute_core`, recording supports: rerouting keeps every vertex set. -/
theorem PathDecomp.reroute_core_supp (D : PathDecomp K) {t u y : U} (hadj : ¬ K.Adj t u)
    (hK' : ∀ e, e ∈ K'.edgeSet ↔ (e ∈ K.edgeSet ∧ e ≠ s(y, u)) ∨ e = s(t, u))
    {P : GPath K} (hP : P ∈ D.paths) (Q : GPath K) (hQs : Q.src = t)
    (hQinf : [y, u] <:+: Q.walk.support) (hQe : Q.edges.Perm P.edges)
    (hQends : ∀ w, Q.endsAt w = P.endsAt w)
    (hQsupp : ∀ w, w ∈ Q.walk.support ↔ w ∈ P.walk.support) :
    ∃ D' : PathDecomp K', D'.size = D.size ∧
      (∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if y = w then 1 else 0)) ∧
      (∀ Q ∈ D.paths, Q ≠ P → ∃ Q' ∈ D'.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
        Q'.walk.support = Q.walk.support) ∧
      (∀ Q' ∈ D'.paths, ∃ Q₀ ∈ D.paths, ∀ x ∈ Q'.walk.support, x ∈ Q₀.walk.support) ∧
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
  · rcases hcovr Q' hQ' with rfl | ⟨Q₀, hQ₀, hs₀⟩
    · refine ⟨P, hP, fun x hx => ?_⟩
      have hx' : x ∈ W.support := hx
      rw [hWsupp, List.mem_append, List.mem_reverse] at hx'
      have : x ∈ Q.walk.support := by
        rw [hq, hsupp, List.mem_append]; exact hx'
      exact (hQsupp x).1 this
    · exact ⟨Q₀, hQ₀, fun x hx => hs₀ ▸ hx⟩
  · have : [u, z] <:+: q₁.support ++ q₂.support := by
      rw [← hsupp, ← hq]; exact hz
    have h2 := infix_pair_of_append this huq₁
    show [u, z] <:+: W.support
    rw [hWsupp]
    exact h2.trans (List.suffix_append _ _).isInfix

/-- `reroute_move`, recording supports. -/
theorem PathDecomp.reroute_move_supp (D : PathDecomp K) {t u y : U}
    (hadj : ¬ K.Adj t u)
    (hK' : ∀ e, e ∈ K'.edgeSet ↔ (e ∈ K.edgeSet ∧ e ≠ s(y, u)) ∨ e = s(t, u))
    {P : GPath K} (hP : P ∈ D.paths)
    (hocc : (P.src = t ∧ [y, u] <:+: P.walk.support) ∨ (P.tgt = t ∧ [u, y] <:+: P.walk.support)) :
    ∃ D' : PathDecomp K', D'.size = D.size ∧
      (∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if y = w then 1 else 0)) ∧
      (∀ Q ∈ D.paths, Q ≠ P → ∃ Q' ∈ D'.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
        Q'.walk.support = Q.walk.support) ∧
      (∀ Q' ∈ D'.paths, ∃ Q₀ ∈ D.paths, ∀ x ∈ Q'.walk.support, x ∈ Q₀.walk.support) ∧
      ∃ P' ∈ D'.paths, ∀ x z, x ≠ t →
        ((P.src = x ∧ [z, u] <:+: P.walk.support) ∨ (P.tgt = x ∧ [u, z] <:+: P.walk.support)) →
        (P'.tgt = x ∧ [u, z] <:+: P'.walk.support) := by
  rcases hocc with ⟨hs, hinf⟩ | ⟨ht, hinf⟩
  · obtain ⟨D', h1, h2, h3, h4, P', hP', hP't, hP'inf⟩ :=
      D.reroute_core_supp hadj hK' hP P hs hinf (List.Perm.refl _) (fun _ => rfl) (fun _ => Iff.rfl)
    refine ⟨D', h1, h2, h3, h4, P', hP', fun x z hx hxz => ?_⟩
    rcases hxz with ⟨h, -⟩ | ⟨h, hz⟩
    · exact absurd (h.symm.trans hs) hx
    · exact ⟨hP't.trans h, hP'inf z hz⟩
  · have hinf' : [y, u] <:+: P.reverse.walk.support := by
      simpa [GPath.reverse, Walk.support_reverse] using hinf.reverse
    obtain ⟨D', h1, h2, h3, h4, P', hP', hP't, hP'inf⟩ :=
      D.reroute_core_supp hadj hK' hP P.reverse ht hinf' (by simp [List.reverse_perm])
        (fun w => P.reverse_endsAt w) (fun w => by simp [GPath.reverse, Walk.support_reverse])
    refine ⟨D', h1, h2, h3, h4, P', hP', fun x z hx hxz => ?_⟩
    rcases hxz with ⟨h, hz⟩ | ⟨h, -⟩
    · refine ⟨hP't.trans h, hP'inf z ?_⟩
      simpa [GPath.reverse, Walk.support_reverse] using hz.reverse
    · exact absurd (h.symm.trans ht) hx

end moves

section chain

variable [DecidableEq U] {K : SimpleGraph U}

/-- `fan_exec`, recording supports: every new path lies in an old path plus `u`.

**Executing a chain**: along a chain from a non-neighbour `t` of `u`, add the edge `tu`. -/
theorem fan_exec_supp (u : U) (xs : List U) : ∀ {K : SimpleGraph U} (D : PathDecomp K) (t : U),
    (t :: xs).Nodup → FanChain D u (t :: xs) → t ≠ u → ¬ K.Adj t u →
    ∀ K' : SimpleGraph U, (∀ e, e ∈ K'.edgeSet ↔ e ∈ K.edgeSet ∨ e = s(t, u)) →
    ∃ D' : PathDecomp K', D'.size = D.size ∧
      (∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if u = w then 1 else 0)) ∧
      ∀ Q' ∈ D'.paths, ∃ Q ∈ D.paths, ∀ x ∈ Q'.walk.support, x ∈ Q.walk.support ∨ x = u := by
  induction xs with
  | nil =>
    intro K D t _ hch _ hadj K' hK'
    obtain ⟨-, x, hx, P, hP, hend, hu⟩ := hch
    simp only [List.getLast?_singleton, Option.some.injEq] at hx
    subst hx
    exact D.append_move_supp hadj hK' hP hend hu
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
    obtain ⟨D₁, hs₁, he₁, htrans, hcov₁, hP'⟩ := D.reroute_move_supp hadj hK₁ hP hocc
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
    obtain ⟨D', hs', he', hcov'⟩ := ih D₁ y (List.nodup_cons.mp hnd).2 hch₁ hyu' hadj₁ K' hK'₁
    refine ⟨D', hs'.trans hs₁, fun w => ?_, fun Q' hQ' => ?_⟩
    · have a := he' w
      have b := he₁ w
      omega
    · obtain ⟨Q₁, hQ₁, h₁⟩ := hcov' Q' hQ'
      obtain ⟨Q₀, hQ₀, h₀⟩ := hcov₁ Q₁ hQ₁
      exact ⟨Q₀, hQ₀, fun x hx => (h₁ x hx).imp_left (h₀ x)⟩

end chain

section counting

variable [DecidableEq U] [Fintype U] {K : SimpleGraph U} [DecidableRel K.Adj]

/-- `fan_grouped`, recording supports.

**Fan's grouped transfer** (Lemma 3.3 as used; six-clique paper, Lemma 2). Let `T` be a set
of non-neighbours of `u` with `u ∉ T` and `∑_{t ∈ T} ends t > #{w ∈ N(u) : ends w = 0}`. Then
for some `t ∈ T`, every graph `K'` with edge set `E(K) ∪ {tu}` has a decomposition of the same
size with one more end at `u`, one fewer at `t`, and the same ends elsewhere. -/
theorem fan_grouped_supp (D : PathDecomp K) (u : U) (T : Finset U) (huT : u ∉ T)
    (hT : ∀ t ∈ T, ¬ K.Adj t u)
    (hsum : (Finset.univ.filter (fun w => K.Adj u w ∧ D.ends w = 0)).card <
      ∑ t ∈ T, D.ends t) :
    ∃ t ∈ T, ∀ K' : SimpleGraph U, (∀ e, e ∈ K'.edgeSet ↔ e ∈ K.edgeSet ∨ e = s(t, u)) →
      ∃ D' : PathDecomp K', D'.size = D.size ∧
        (∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if u = w then 1 else 0)) ∧
        ∀ Q' ∈ D'.paths, ∃ Q ∈ D.paths, ∀ x ∈ Q'.walk.support, x ∈ Q.walk.support ∨ x = u := by
  obtain ⟨t, ht, xs, hnd, hch⟩ := fan_exists_chain D u T huT hT hsum
  exact ⟨t, ht, fun K' hK' =>
    fan_exec_supp u xs D t hnd hch (fun h => huT (h ▸ ht)) (hT t ht) K' hK'⟩

/-- `fan_single`, recording supports: every path of the new decomposition lies in a path of the
old one plus `u`.

**Fan's Lemma 3.4** (single edge). Let `uv ∈ E(G)`, let `G'` be `G − uv`, and let `D'`
decompose `G'`. If `ends v > #{w ∈ N_{G'}(u) : ends w = 0}`, then `G` has a decomposition of the
same size with one more end at `u`, one fewer at `v`, and the same ends elsewhere. -/
theorem fan_single_supp {G G' : SimpleGraph U} [DecidableRel G'.Adj] {u v : U} (huv : G.Adj u v)
    (hG' : ∀ e, e ∈ G'.edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(u, v)) (D' : PathDecomp G')
    (h : (Finset.univ.filter (fun w => G'.Adj u w ∧ D'.ends w = 0)).card < D'.ends v) :
    ∃ D : PathDecomp G, D.size = D'.size ∧ D.ends u = D'.ends u + 1 ∧
      D.ends v + 1 = D'.ends v ∧ (∀ w, w ≠ u → w ≠ v → D.ends w = D'.ends w) ∧
      ∀ Q ∈ D.paths, ∃ Q' ∈ D'.paths, ∀ x ∈ Q.walk.support, x ∈ Q'.walk.support ∨ x = u := by
  have huv' : u ≠ v := huv.ne
  obtain ⟨t, ht, hK⟩ := fan_grouped_supp D' u {v} (by simpa using huv')
    (by
      intro t ht
      rw [Finset.mem_singleton] at ht
      subst ht
      rw [← mem_edgeSet, hG']
      rintro ⟨-, h⟩
      exact h Sym2.eq_swap)
    (by simpa using h)
  obtain rfl : t = v := Finset.mem_singleton.mp ht
  obtain ⟨D, hs, he, hcovD⟩ := hK G (by
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
  refine ⟨D, hs, ?_, ?_, ?_, hcovD⟩
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

end counting

end Gallai
