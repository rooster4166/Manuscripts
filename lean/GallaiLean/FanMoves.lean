import GallaiLean.LeafDictionary

/-!
# Elementary moves for Fan's addible-edge lemma

* `PathDecomp.replace`: replace one path by a path of a new graph whose edge set differs only
  on that path. The other paths are transferred unchanged.
* `PathDecomp.append_move`: a path with an end at `t` that avoids `u` absorbs the new edge `tu`.
  The end moves from `t` to `u`.
* `PathDecomp.reroute_move`: a path read from its end `t` that reaches `u` through the edge
  `yu` is rerouted. The segment from `t` to `y` is reversed and `yu` is traded for the new edge
  `tu`, so the end moves from `t` to `y`. The reading from the other end is unchanged up to `u`.
-/

open SimpleGraph

namespace Gallai

universe v

variable {U : Type v}

section walk

variable {K : SimpleGraph U}

theorem Walk.adj_of_infix_support {a b x y : U} (p : K.Walk x y) (h : [a, b] <:+: p.support) :
    K.Adj a b := by
  induction p with
  | nil => exact absurd h.length_le (by simp)
  | @cons x c y hxc p ih =>
    rw [Walk.support_cons, List.infix_cons_iff] at h
    rcases h with h | h
    · rw [List.cons_prefix_cons] at h
      obtain ⟨rfl, hb⟩ := h
      rw [← Walk.cons_map_snd_darts, List.cons_prefix_cons] at hb
      rw [hb.1]
      exact hxc
    · exact ih h

/-- Split a walk at a dart. -/
theorem Walk.exists_append_cons_of_mem_darts {a b : U} (p : K.Walk a b) {d : K.Dart}
    (hd : d ∈ p.darts) :
    ∃ (q₁ : K.Walk a d.fst) (q₂ : K.Walk d.snd b), p = q₁.append (Walk.cons d.adj q₂) := by
  induction p with
  | nil => simp at hd
  | @cons a c b h p ih =>
    rw [Walk.darts_cons, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact ⟨Walk.nil, p, rfl⟩
    · obtain ⟨q₁, q₂, hq⟩ := ih hd
      exact ⟨Walk.cons h q₁, q₂, by rw [hq]; rfl⟩

theorem Walk.exists_append_cons_of_infix {a b x y : U} (p : K.Walk a b)
    (h : [x, y] <:+: p.support) :
    ∃ (hxy : K.Adj x y) (q₁ : K.Walk a x) (q₂ : K.Walk y b),
      p = q₁.append (Walk.cons hxy q₂) := by
  have hxy := Walk.adj_of_infix_support p h
  have hd : (⟨(x, y), hxy⟩ : K.Dart) ∈ p.darts := (Walk.mem_darts_iff_infix_support hxy).2 h
  obtain ⟨q₁, q₂, hq⟩ := Walk.exists_append_cons_of_mem_darts p hd
  exact ⟨hxy, q₁, q₂, hq⟩

theorem Walk.exists_dart_snd_eq {a b w : U} (p : K.Walk a b) (hw : w ∈ p.support)
    (hwa : w ≠ a) : ∃ d ∈ p.darts, d.snd = w := by
  rw [← Walk.cons_map_snd_darts, List.mem_cons] at hw
  rcases hw with rfl | hw
  · exact absurd rfl hwa
  · exact List.mem_map.mp hw

theorem Walk.exists_dart_fst_eq {a b w : U} (p : K.Walk a b) (hw : w ∈ p.support)
    (hwb : w ≠ b) : ∃ d ∈ p.darts, d.fst = w := by
  rw [← Walk.map_fst_darts_append, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · exact List.mem_map.mp hw
  · exact absurd rfl hwb

theorem infix_pair_of_append {a b : U} {l₁ l₂ : List U} (h : [a, b] <:+: l₁ ++ l₂)
    (ha : a ∉ l₁) : [a, b] <:+: l₂ := by
  induction l₁ with
  | nil => simpa using h
  | cons c l₁ ih =>
    rw [List.cons_append, List.infix_cons_iff] at h
    rcases h with h | h
    · rw [List.cons_prefix_cons] at h
      exact absurd (h.1 ▸ List.mem_cons_self) ha
    · exact ih h (fun h' => ha (List.mem_cons_of_mem _ h'))

end walk

/-! ### Paths -/

namespace GPath

variable {K K' : SimpleGraph U}

/-- Transfer a path to a graph containing its edges. -/
def transfer (P : GPath K) (h : ∀ e ∈ P.edges, e ∈ K'.edgeSet) : GPath K' :=
  ⟨P.src, P.tgt, P.walk.transfer K' (fun e he => h e he),
    (Walk.isPath_transfer _ _).mpr P.isPath, by rw [Walk.length_transfer]; exact P.pos⟩

@[simp] theorem transfer_edges (P : GPath K) (h : ∀ e ∈ P.edges, e ∈ K'.edgeSet) :
    (P.transfer h).edges = P.edges := by simp [transfer, GPath.edges]

@[simp] theorem transfer_src (P : GPath K) (h : ∀ e ∈ P.edges, e ∈ K'.edgeSet) :
    (P.transfer h).src = P.src := rfl

@[simp] theorem transfer_tgt (P : GPath K) (h : ∀ e ∈ P.edges, e ∈ K'.edgeSet) :
    (P.transfer h).tgt = P.tgt := rfl

@[simp] theorem transfer_support (P : GPath K) (h : ∀ e ∈ P.edges, e ∈ K'.edgeSet) :
    (P.transfer h).walk.support = P.walk.support := by simp [transfer]

theorem transfer_endsAt [DecidableEq U] (P : GPath K) (h : ∀ e ∈ P.edges, e ∈ K'.edgeSet)
    (w : U) : (P.transfer h).endsAt w = P.endsAt w := rfl

theorem reverse_endsAt [DecidableEq U] (P : GPath K) (w : U) :
    P.reverse.endsAt w = P.endsAt w := by
  simp only [endsAt, reverse]; exact Nat.add_comm _ _

end GPath

/-! ### Replacing one path -/

section replace

variable [DecidableEq U] {K K' : SimpleGraph U}

omit [DecidableEq U] in
theorem flatMap_pmap_transfer (l : List (GPath K))
    (H : ∀ Q ∈ l, ∀ e ∈ Q.edges, e ∈ K'.edgeSet) :
    (l.pmap (fun Q hQ => Q.transfer hQ) H).flatMap GPath.edges = l.flatMap GPath.edges := by
  induction l with
  | nil => rfl
  | cons Q l ih =>
    rw [List.pmap_cons, List.flatMap_cons, List.flatMap_cons, GPath.transfer_edges, ih]

theorem sum_endsAt_pmap_transfer (l : List (GPath K))
    (H : ∀ Q ∈ l, ∀ e ∈ Q.edges, e ∈ K'.edgeSet) (w : U) :
    ((l.pmap (fun Q hQ => Q.transfer hQ) H).map (fun P => P.endsAt w)).sum =
      (l.map (fun P => P.endsAt w)).sum := by
  induction l with
  | nil => rfl
  | cons Q l ih =>
    rw [List.pmap_cons, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih]
    rfl

/-- **Replacing one path.** -/
theorem PathDecomp.replace (D : PathDecomp K) {P : GPath K} (hP : P ∈ D.paths) (P' : GPath K')
    (hcov : ∀ e, e ∈ K'.edgeSet ↔ (e ∈ K.edgeSet ∧ e ∉ P.edges) ∨ e ∈ P'.edges)
    (hnew : ∀ e ∈ P'.edges, e ∈ P.edges ∨ e ∉ K.edgeSet) :
    ∃ D' : PathDecomp K', D'.size = D.size ∧ P' ∈ D'.paths ∧
      (∀ w, D'.ends w + P.endsAt w = D.ends w + P'.endsAt w) ∧
      ∀ Q ∈ D.paths, Q ≠ P → ∃ Q' ∈ D'.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
        Q'.walk.support = Q.walk.support := by
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
  refine ⟨D', ?_, ?_, ?_, ?_⟩
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
        rfl, rfl, by simp⟩
    · exact absurd hQ hQP
    · exact ⟨Q.transfer (h₂ Q hQ),
        List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_pmap_of_mem hQ)),
        rfl, rfl, by simp⟩

end replace

/-! ### The two moves -/

section moves

variable [DecidableEq U] {K K' : SimpleGraph U}

/-- Orient a path so that it starts at a given end. -/
theorem GPath.exists_orient (P : GPath K) {t : U} (h : P.src = t ∨ P.tgt = t) :
    ∃ Q : GPath K, Q.src = t ∧ Q.edges.Perm P.edges ∧ (∀ w, Q.endsAt w = P.endsAt w) ∧
      (∀ w, w ∈ Q.walk.support ↔ w ∈ P.walk.support) := by
  rcases h with h | h
  · exact ⟨P, h, List.Perm.refl _, fun _ => rfl, fun _ => Iff.rfl⟩
  · refine ⟨P.reverse, h, by simp [List.reverse_perm], fun w => P.reverse_endsAt w,
      fun w => ?_⟩
    simp [GPath.reverse, Walk.support_reverse]

/-- **Append move.** -/
theorem PathDecomp.append_move (D : PathDecomp K) {t u : U} (hadj : ¬ K.Adj t u)
    (hK' : ∀ e, e ∈ K'.edgeSet ↔ e ∈ K.edgeSet ∨ e = s(t, u))
    {P : GPath K} (hP : P ∈ D.paths) (hend : P.src = t ∨ P.tgt = t)
    (hu : u ∉ P.walk.support) :
    ∃ D' : PathDecomp K', D'.size = D.size ∧
      ∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if u = w then 1 else 0) := by
  obtain ⟨Q, hQs, hQe, hQends, hQsupp⟩ := P.exists_orient hend
  have hQK : ∀ e ∈ Q.walk.edges, e ∈ K'.edgeSet := fun e he =>
    (hK' e).2 (Or.inl (Q.walk.edges_subset_edgeSet he))
  have hut : K'.Adj u Q.src := by
    rw [← mem_edgeSet, hK', hQs, Sym2.eq_swap]; exact Or.inr rfl
  have huQ : u ∉ Q.walk.support := fun h => hu ((hQsupp u).1 h)
  let P' : GPath K' :=
    ⟨u, Q.tgt, Walk.cons hut (Q.walk.transfer K' hQK),
      by
        rw [Walk.cons_isPath_iff]
        exact ⟨by simpa using Q.isPath, by simpa using huQ⟩,
      by simp⟩
  have hP'e : P'.edges = s(t, u) :: Q.edges := by
    show (Walk.cons hut (Q.walk.transfer K' hQK)).edges = _
    have hs : s(u, Q.src) = s(t, u) := by rw [hQs, Sym2.eq_swap]
    rw [Walk.edges_cons, Walk.edges_transfer, hs]
    rfl
  have hPK : ∀ e ∈ P.edges, e ∈ K.edgeSet := fun e he => P.walk.edges_subset_edgeSet he
  have htuK : s(t, u) ∉ K.edgeSet := hadj
  obtain ⟨D', hsize, -, hends, -⟩ := D.replace hP P' (by
      intro e
      rw [hK' e, hP'e, List.mem_cons, hQe.mem_iff]
      by_cases heP : e ∈ P.edges
      · have := hPK e heP; tauto
      · tauto)
    (by
      intro e he
      rw [hP'e, List.mem_cons, hQe.mem_iff] at he
      rcases he with rfl | he
      · exact Or.inr htuK
      · exact Or.inl he)
  refine ⟨D', hsize, fun w => ?_⟩
  have h1 := hends w
  have h2 : P'.endsAt w = (if u = w then 1 else 0) + (if Q.tgt = w then 1 else 0) := rfl
  have h3 : P.endsAt w = (if t = w then 1 else 0) + (if Q.tgt = w then 1 else 0) := by
    rw [← hQends]; simp only [GPath.endsAt, hQs]
  omega

/-- The reroute on a path oriented from `t`. -/
theorem PathDecomp.reroute_core (D : PathDecomp K) {t u y : U} (hadj : ¬ K.Adj t u)
    (hK' : ∀ e, e ∈ K'.edgeSet ↔ (e ∈ K.edgeSet ∧ e ≠ s(y, u)) ∨ e = s(t, u))
    {P : GPath K} (hP : P ∈ D.paths) (Q : GPath K) (hQs : Q.src = t)
    (hQinf : [y, u] <:+: Q.walk.support) (hQe : Q.edges.Perm P.edges)
    (hQends : ∀ w, Q.endsAt w = P.endsAt w) :
    ∃ D' : PathDecomp K', D'.size = D.size ∧
      (∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if y = w then 1 else 0)) ∧
      (∀ Q ∈ D.paths, Q ≠ P → ∃ Q' ∈ D'.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
        Q'.walk.support = Q.walk.support) ∧
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
  obtain ⟨D', hsize, hP'mem, hends, htrans⟩ := D.replace hP P' hcov hnew
  refine ⟨D', hsize, fun w => ?_, htrans, P', hP'mem, rfl, fun z hz => ?_⟩
  · have h1 := hends w
    have h2 : P'.endsAt w = (if y = w then 1 else 0) + (if Q.tgt = w then 1 else 0) := rfl
    have h3 : P.endsAt w = (if t = w then 1 else 0) + (if Q.tgt = w then 1 else 0) := by
      rw [← hQends]; simp only [GPath.endsAt, hQs]
    omega
  · have : [u, z] <:+: q₁.support ++ q₂.support := by
      rw [← hsupp, ← hq]; exact hz
    have h2 := infix_pair_of_append this huq₁
    show [u, z] <:+: W.support
    rw [hWsupp]
    exact h2.trans (List.suffix_append _ _).isInfix

/-- **Reroute move.** -/
theorem PathDecomp.reroute_move (D : PathDecomp K) {t u y : U}
    (hadj : ¬ K.Adj t u)
    (hK' : ∀ e, e ∈ K'.edgeSet ↔ (e ∈ K.edgeSet ∧ e ≠ s(y, u)) ∨ e = s(t, u))
    {P : GPath K} (hP : P ∈ D.paths)
    (hocc : (P.src = t ∧ [y, u] <:+: P.walk.support) ∨ (P.tgt = t ∧ [u, y] <:+: P.walk.support)) :
    ∃ D' : PathDecomp K', D'.size = D.size ∧
      (∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if y = w then 1 else 0)) ∧
      (∀ Q ∈ D.paths, Q ≠ P → ∃ Q' ∈ D'.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
        Q'.walk.support = Q.walk.support) ∧
      ∃ P' ∈ D'.paths, ∀ x z, x ≠ t →
        ((P.src = x ∧ [z, u] <:+: P.walk.support) ∨ (P.tgt = x ∧ [u, z] <:+: P.walk.support)) →
        (P'.tgt = x ∧ [u, z] <:+: P'.walk.support) := by
  rcases hocc with ⟨hs, hinf⟩ | ⟨ht, hinf⟩
  · obtain ⟨D', h1, h2, h3, P', hP', hP't, hP'inf⟩ :=
      D.reroute_core hadj hK' hP P hs hinf (List.Perm.refl _) (fun _ => rfl)
    refine ⟨D', h1, h2, h3, P', hP', fun x z hx hxz => ?_⟩
    rcases hxz with ⟨h, -⟩ | ⟨h, hz⟩
    · exact absurd (h.symm.trans hs) hx
    · exact ⟨hP't.trans h, hP'inf z hz⟩
  · have hinf' : [y, u] <:+: P.reverse.walk.support := by
      simpa [GPath.reverse, Walk.support_reverse] using hinf.reverse
    obtain ⟨D', h1, h2, h3, P', hP', hP't, hP'inf⟩ :=
      D.reroute_core hadj hK' hP P.reverse ht hinf' (by simp [List.reverse_perm])
        (fun w => P.reverse_endsAt w)
    refine ⟨D', h1, h2, h3, P', hP', fun x z hx hxz => ?_⟩
    rcases hxz with ⟨h, hz⟩ | ⟨h, -⟩
    · refine ⟨hP't.trans h, hP'inf z ?_⟩
      simpa [GPath.reverse, Walk.support_reverse] using hz.reverse
    · exact absurd (h.symm.trans ht) hx

end moves from `t` to `u`.
* `PathDecomp.reroute_move`: a path read from its end `t` that reaches `u` through the edge
  `yu` is rerouted. The segment from `t` to `y` is reversed and `yu` is traded for the new edge
  `tu`, so the end moves from `t` to `y`. The reading from the other end is unchanged up to `u`.
-/

open SimpleGraph

namespace Gallai

universe v

variable {U : Type v}

section walk

variable {K : SimpleGraph U}

theorem Walk.adj_of_infix_support {a b x y : U} (p : K.Walk x y) (h : [a, b] <:+: p.support) :
    K.Adj a b := by
  induction p with
  | nil => exact absurd h.length_le (by simp)
  | @cons x c y hxc p ih =>
    rw [Walk.support_cons, List.infix_cons_iff] at h
    rcases h with h | h
    · rw [List.cons_prefix_cons] at h
      obtain ⟨rfl, hb⟩ := h
      rw [← Walk.cons_map_snd_darts, List.cons_prefix_cons] at hb
      rw [hb.1]
      exact hxc
    · exact ih h

/-- Split a walk at a dart. -/
theorem Walk.exists_append_cons_of_mem_darts {a b : U} (p : K.Walk a b) {d : K.Dart}
    (hd : d ∈ p.darts) :
    ∃ (q₁ : K.Walk a d.fst) (q₂ : K.Walk d.snd b), p = q₁.append (Walk.cons d.adj q₂) := by
  induction p with
  | nil => simp at hd
  | @cons a c b h p ih =>
    rw [Walk.darts_cons, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact ⟨Walk.nil, p, rfl⟩
    · obtain ⟨q₁, q₂, hq⟩ := ih hd
      exact ⟨Walk.cons h q₁, q₂, by rw [hq]; rfl⟩

theorem Walk.exists_append_cons_of_infix {a b x y : U} (p : K.Walk a b)
    (h : [x, y] <:+: p.support) :
    ∃ (hxy : K.Adj x y) (q₁ : K.Walk a x) (q₂ : K.Walk y b),
      p = q₁.append (Walk.cons hxy q₂) := by
  have hxy := Walk.adj_of_infix_support p h
  have hd : (⟨(x, y), hxy⟩ : K.Dart) ∈ p.darts := (Walk.mem_darts_iff_infix_support hxy).2 h
  obtain ⟨q₁, q₂, hq⟩ := Walk.exists_append_cons_of_mem_darts p hd
  exact ⟨hxy, q₁, q₂, hq⟩

theorem Walk.exists_dart_snd_eq {a b w : U} (p : K.Walk a b) (hw : w ∈ p.support)
    (hwa : w ≠ a) : ∃ d ∈ p.darts, d.snd = w := by
  rw [← Walk.cons_map_snd_darts, List.mem_cons] at hw
  rcases hw with rfl | hw
  · exact absurd rfl hwa
  · exact List.mem_map.mp hw

theorem Walk.exists_dart_fst_eq {a b w : U} (p : K.Walk a b) (hw : w ∈ p.support)
    (hwb : w ≠ b) : ∃ d ∈ p.darts, d.fst = w := by
  rw [← Walk.map_fst_darts_append, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · exact List.mem_map.mp hw
  · exact absurd rfl hwb

theorem infix_pair_of_append {a b : U} {l₁ l₂ : List U} (h : [a, b] <:+: l₁ ++ l₂)
    (ha : a ∉ l₁) : [a, b] <:+: l₂ := by
  induction l₁ with
  | nil => simpa using h
  | cons c l₁ ih =>
    rw [List.cons_append, List.infix_cons_iff] at h
    rcases h with h | h
    · rw [List.cons_prefix_cons] at h
      exact absurd (h.1 ▸ List.mem_cons_self) ha
    · exact ih h (fun h' => ha (List.mem_cons_of_mem _ h'))

end walk

/-! ### Paths -/

namespace GPath

variable {K K' : SimpleGraph U}

/-- Transfer a path to a graph containing its edges. -/
def transfer (P : GPath K) (h : ∀ e ∈ P.edges, e ∈ K'.edgeSet) : GPath K' :=
  ⟨P.src, P.tgt, P.walk.transfer K' (fun e he => h e he),
    (Walk.isPath_transfer _ _).mpr P.isPath, by rw [Walk.length_transfer]; exact P.pos⟩

@[simp] theorem transfer_edges (P : GPath K) (h : ∀ e ∈ P.edges, e ∈ K'.edgeSet) :
    (P.transfer h).edges = P.edges := by simp [transfer, GPath.edges]

@[simp] theorem transfer_src (P : GPath K) (h : ∀ e ∈ P.edges, e ∈ K'.edgeSet) :
    (P.transfer h).src = P.src := rfl

@[simp] theorem transfer_tgt (P : GPath K) (h : ∀ e ∈ P.edges, e ∈ K'.edgeSet) :
    (P.transfer h).tgt = P.tgt := rfl

@[simp] theorem transfer_support (P : GPath K) (h : ∀ e ∈ P.edges, e ∈ K'.edgeSet) :
    (P.transfer h).walk.support = P.walk.support := by simp [transfer]

theorem transfer_endsAt [DecidableEq U] (P : GPath K) (h : ∀ e ∈ P.edges, e ∈ K'.edgeSet)
    (w : U) : (P.transfer h).endsAt w = P.endsAt w := rfl

theorem reverse_endsAt [DecidableEq U] (P : GPath K) (w : U) :
    P.reverse.endsAt w = P.endsAt w := by
  simp only [endsAt, reverse]; exact Nat.add_comm _ _

end GPath

/-! ### Replacing one path -/

section replace

variable [DecidableEq U] {K K' : SimpleGraph U}

omit [DecidableEq U] in
theorem flatMap_pmap_transfer (l : List (GPath K))
    (H : ∀ Q ∈ l, ∀ e ∈ Q.edges, e ∈ K'.edgeSet) :
    (l.pmap (fun Q hQ => Q.transfer hQ) H).flatMap GPath.edges = l.flatMap GPath.edges := by
  induction l with
  | nil => rfl
  | cons Q l ih =>
    rw [List.pmap_cons, List.flatMap_cons, List.flatMap_cons, GPath.transfer_edges, ih]

theorem sum_endsAt_pmap_transfer (l : List (GPath K))
    (H : ∀ Q ∈ l, ∀ e ∈ Q.edges, e ∈ K'.edgeSet) (w : U) :
    ((l.pmap (fun Q hQ => Q.transfer hQ) H).map (fun P => P.endsAt w)).sum =
      (l.map (fun P => P.endsAt w)).sum := by
  induction l with
  | nil => rfl
  | cons Q l ih =>
    rw [List.pmap_cons, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih]
    rfl

/-- **Replacing one path.** -/
theorem PathDecomp.replace (D : PathDecomp K) {P : GPath K} (hP : P ∈ D.paths) (P' : GPath K')
    (hcov : ∀ e, e ∈ K'.edgeSet ↔ (e ∈ K.edgeSet ∧ e ∉ P.edges) ∨ e ∈ P'.edges)
    (hnew : ∀ e ∈ P'.edges, e ∈ P.edges ∨ e ∉ K.edgeSet) :
    ∃ D' : PathDecomp K', D'.size = D.size ∧ P' ∈ D'.paths ∧
      (∀ w, D'.ends w + P.endsAt w = D.ends w + P'.endsAt w) ∧
      ∀ Q ∈ D.paths, Q ≠ P → ∃ Q' ∈ D'.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
        Q'.walk.support = Q.walk.support := by
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
  refine ⟨D', ?_, ?_, ?_, ?_⟩
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
        rfl, rfl, by simp⟩
    · exact absurd hQ hQP
    · exact ⟨Q.transfer (h₂ Q hQ),
        List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_pmap_of_mem hQ)),
        rfl, rfl, by simp⟩

end replace

/-! ### The two moves -/

section moves

variable [DecidableEq U] {K K' : SimpleGraph U}

/-- Orient a path so that it starts at a given end. -/
theorem GPath.exists_orient (P : GPath K) {t : U} (h : P.src = t ∨ P.tgt = t) :
    ∃ Q : GPath K, Q.src = t ∧ Q.edges.Perm P.edges ∧ (∀ w, Q.endsAt w = P.endsAt w) ∧
      (∀ w, w ∈ Q.walk.support ↔ w ∈ P.walk.support) := by
  rcases h with h | h
  · exact ⟨P, h, List.Perm.refl _, fun _ => rfl, fun _ => Iff.rfl⟩
  · refine ⟨P.reverse, h, by simp [List.reverse_perm], fun w => P.reverse_endsAt w,
      fun w => ?_⟩
    simp [GPath.reverse, Walk.support_reverse]

/-- **Append move.** -/
theorem PathDecomp.append_move (D : PathDecomp K) {t u : U} (hadj : ¬ K.Adj t u)
    (hK' : ∀ e, e ∈ K'.edgeSet ↔ e ∈ K.edgeSet ∨ e = s(t, u))
    {P : GPath K} (hP : P ∈ D.paths) (hend : P.src = t ∨ P.tgt = t)
    (hu : u ∉ P.walk.support) :
    ∃ D' : PathDecomp K', D'.size = D.size ∧
      ∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if u = w then 1 else 0) := by
  obtain ⟨Q, hQs, hQe, hQends, hQsupp⟩ := P.exists_orient hend
  have hQK : ∀ e ∈ Q.walk.edges, e ∈ K'.edgeSet := fun e he =>
    (hK' e).2 (Or.inl (Q.walk.edges_subset_edgeSet he))
  have hut : K'.Adj u Q.src := by
    rw [← mem_edgeSet, hK', hQs, Sym2.eq_swap]; exact Or.inr rfl
  have huQ : u ∉ Q.walk.support := fun h => hu ((hQsupp u).1 h)
  let P' : GPath K' :=
    ⟨u, Q.tgt, Walk.cons hut (Q.walk.transfer K' hQK),
      by
        rw [Walk.cons_isPath_iff]
        exact ⟨by simpa using Q.isPath, by simpa using huQ⟩,
      by simp⟩
  have hP'e : P'.edges = s(t, u) :: Q.edges := by
    show (Walk.cons hut (Q.walk.transfer K' hQK)).edges = _
    have hs : s(u, Q.src) = s(t, u) := by rw [hQs, Sym2.eq_swap]
    rw [Walk.edges_cons, Walk.edges_transfer, hs]
    rfl
  have hPK : ∀ e ∈ P.edges, e ∈ K.edgeSet := fun e he => P.walk.edges_subset_edgeSet he
  have htuK : s(t, u) ∉ K.edgeSet := hadj
  obtain ⟨D', hsize, -, hends, -⟩ := D.replace hP P' (by
      intro e
      rw [hK' e, hP'e, List.mem_cons, hQe.mem_iff]
      by_cases heP : e ∈ P.edges
      · have := hPK e heP; tauto
      · tauto)
    (by
      intro e he
      rw [hP'e, List.mem_cons, hQe.mem_iff] at he
      rcases he with rfl | he
      · exact Or.inr htuK
      · exact Or.inl he)
  refine ⟨D', hsize, fun w => ?_⟩
  have h1 := hends w
  have h2 : P'.endsAt w = (if u = w then 1 else 0) + (if Q.tgt = w then 1 else 0) := rfl
  have h3 : P.endsAt w = (if t = w then 1 else 0) + (if Q.tgt = w then 1 else 0) := by
    rw [← hQends]; simp only [GPath.endsAt, hQs]
  omega

/-- **Reroute move.** -/
theorem PathDecomp.reroute_move (D : PathDecomp K) {t u y : U} (htu : t ≠ u)
    (hadj : ¬ K.Adj t u)
    (hK' : ∀ e, e ∈ K'.edgeSet ↔ (e ∈ K.edgeSet ∧ e ≠ s(y, u)) ∨ e = s(t, u))
    {P : GPath K} (hP : P ∈ D.paths)
    (hocc : (P.src = t ∧ [y, u] <:+: P.walk.support) ∨ (P.tgt = t ∧ [u, y] <:+: P.walk.support)) :
    ∃ D' : PathDecomp K', D'.size = D.size ∧
      (∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if y = w then 1 else 0)) ∧
      (∀ Q ∈ D.paths, Q ≠ P → ∃ Q' ∈ D'.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
        Q'.walk.support = Q.walk.support) ∧
      ∃ P' ∈ D'.paths, ∀ x z, x ≠ t →
        ((P.src = x ∧ [z, u] <:+: P.walk.support) ∨ (P.tgt = x ∧ [u, z] <:+: P.walk.support)) →
        (P'.tgt = x ∧ [u, z] <:+: P'.walk.support) := by
  -- orient the path from `t`
  obtain ⟨Q, hQs, hQinf, hQe, hQends, hQocc⟩ : ∃ Q : GPath K, Q.src = t ∧
      [y, u] <:+: Q.walk.support ∧ Q.edges.Perm P.edges ∧ (∀ w, Q.endsAt w = P.endsAt w) ∧
      ∀ x z, x ≠ t → ((P.src = x ∧ [z, u] <:+: P.walk.support) ∨
        (P.tgt = x ∧ [u, z] <:+: P.walk.support)) → Q.tgt = x ∧ [u, z] <:+: Q.walk.support := by
    rcases hocc with ⟨hs, hinf⟩ | ⟨ht, hinf⟩
    · refine ⟨P, hs, hinf, List.Perm.refl _, fun _ => rfl, fun x z hx hxz => ?_⟩
      rcases hxz with ⟨h1, -⟩ | h
      · exact absurd (h1.symm.trans hs) hx
      · exact h
    · refine ⟨P.reverse, ht, ?_, by simp [List.reverse_perm], fun w => P.reverse_endsAt w,
        fun x z hx hxz => ?_⟩
      · simpa [GPath.reverse, Walk.support_reverse] using hinf.reverse
      · rcases hxz with ⟨h1, h2⟩ | ⟨h1, -⟩
        · refine ⟨h1, ?_⟩
          simpa [GPath.reverse, Walk.support_reverse] using h2.reverse
        · exact absurd (h1.symm.trans ht) hx
  -- split at the dart `y → u`
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
  -- the new path `y … t u …`
  have h₁ : ∀ e ∈ q₁.reverse.edges, e ∈ K'.edgeSet := by
    intro e he
    rw [Walk.edges_reverse, List.mem_reverse] at he
    exact (hK' e).2 (Or.inl ⟨q₁.edges_subset_edgeSet he, fun h => hyq₁ (h ▸ he)⟩)
  have h₂ : ∀ e ∈ q₂.edges, e ∈ K'.edgeSet := by
    intro e he
    exact (hK' e).2 (Or.inl ⟨q₂.edges_subset_edgeSet he, fun h => hyq₂ (h ▸ he)⟩)
  have htu' : K'.Adj Q.src u := by
    rw [← mem_edgeSet, hK', hQs]; exact Or.inr rfl
  let W : K'.Walk y Q.tgt :=
    (q₁.reverse.transfer K' h₁).append (Walk.cons htu' (q₂.transfer K' h₂))
  have hWsupp : W.support = q₁.support.reverse ++ q₂.support := by
    simp only [W, Walk.support_append, Walk.support_cons, List.tail_cons, Walk.support_transfer,
      Walk.support_reverse]
  have hWedges : W.edges = q₁.edges.reverse ++ s(Q.src, u) :: q₂.edges := by
    simp only [W, Walk.edges_append, Walk.edges_cons, Walk.edges_transfer, Walk.edges_reverse]
  have hWpath : W.IsPath := by
    rw [Walk.isPath_def, hWsupp]
    exact ((List.reverse_perm _).append_right _).nodup_iff.mpr hsnd
  let P' : GPath K' := ⟨y, Q.tgt, W, hWpath, by
    have : 0 < W.edges.length := by rw [hWedges]; simp
    rwa [Walk.length_edges] at this⟩
  have hP'e : P'.edges = q₁.edges.reverse ++ s(t, u) :: q₂.edges := by
    show W.edges = _; rw [hWedges, hQs]
  have hmemP : ∀ e, e ∈ P.edges ↔ e ∈ q₁.edges ∨ e = s(y, u) ∨ e ∈ q₂.edges := by
    intro e; rw [← hQe.mem_iff, hedges]; simp
  have hmemP' : ∀ e, e ∈ P'.edges ↔ e ∈ q₁.edges ∨ e = s(t, u) ∨ e ∈ q₂.edges := by
    intro e; rw [hP'e]; simp
  have htuK : s(t, u) ∉ K.edgeSet := hadj
  obtain ⟨D', hsize, hP'mem, hends, htrans⟩ := D.replace hP P' (by
      intro e
      rw [hK' e, hmemP e, hmemP' e]
      have a1 : e ∈ q₁.edges → e ∈ K.edgeSet := fun h => q₁.edges_subset_edgeSet h
      have a2 : e ∈ q₂.edges → e ∈ K.edgeSet := fun h => q₂.edges_subset_edgeSet h
      have a3 : e ∈ q₁.edges → e ≠ s(y, u) := fun h h' => hyq₁ (h' ▸ h)
      have a4 : e ∈ q₂.edges → e ≠ s(y, u) := fun h h' => hyq₂ (h' ▸ h)
      tauto)
    (by
      intro e he
      rw [hmemP' e] at he
      rw [hmemP e]
      rcases he with he | rfl | he
      · exact Or.inl (Or.inl he)
      · exact Or.inr htuK
      · exact Or.inl (Or.inr (Or.inr he)))
  refine ⟨D', hsize, fun w => ?_, htrans, P', hP'mem, fun x z hx hxz => ?_⟩
  · have h1 := hends w
    have h2 : P'.endsAt w = (if y = w then 1 else 0) + (if Q.tgt = w then 1 else 0) := rfl
    have h3 : P.endsAt w = (if t = w then 1 else 0) + (if Q.tgt = w then 1 else 0) := by
      rw [← hQends]; simp only [GPath.endsAt, hQs]
    omega
  · obtain ⟨hxt, hinf⟩ := hQocc x z hx hxz
    refine ⟨hxt, ?_⟩
    have : [u, z] <:+: q₁.support ++ q₂.support := by
      rw [← hsupp, ← hq]; exact hinf
    have h2 := infix_pair_of_append this huq₁
    show [u, z] <:+: W.support
    rw [hWsupp]
    exact h2.trans (List.suffix_append _ _).isInfix

end moves

end Gallai
