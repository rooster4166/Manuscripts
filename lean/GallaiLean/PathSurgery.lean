import GallaiLean.ThreeConnected

/-!
# Path surgery in the complete graph

Toolkit for the separator theorem (marked-reduction Theorem 113). Decompositions of different
graphs on the same vertex type are cut and glued as paths of the complete graph `⊤` (`TPath V`);
edge bookkeeping is done with multisets (`edgesM`), end bookkeeping with `endsL`.

* `GPath.toTop`, `PathDecomp.edgesM_toTop`, `PathDecomp.endsL_toTop`: a decomposition of `G` as a
  list of `TPath`s whose edge multiset is `G.edgeFinset.val`.
* `exists_decomp_of_edgesM`: conversely, such a list is a decomposition of `G`.
* `edgeFinset_val_eq_add`: edge multisets of graphs built from others by adding edges.
* `plusEdge G a b`: `G` plus the edge `ab`; `plusEdge_degree`.
* `nodup_support_append`, `joinT`: gluing walks of `⊤` into paths.
* `exists_subst_path`, `exists_subst_list`: replace an edge of a path by a path through new
  vertices.
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u}

/-- Paths of the complete graph on `V`. -/
abbrev TPath (V : Type u) := GPath (⊤ : SimpleGraph V)

namespace GPath

variable {G : SimpleGraph V}

/-- A path of `G`, viewed in the complete graph. -/
def toTop (P : GPath G) : TPath V :=
  ⟨P.src, P.tgt, P.walk.mapLe le_top, P.isPath.mapLe le_top,
    by rw [Walk.length_mapLe]; exact P.pos⟩

@[simp] theorem toTop_src (P : GPath G) : P.toTop.src = P.src := rfl
@[simp] theorem toTop_tgt (P : GPath G) : P.toTop.tgt = P.tgt := rfl
@[simp] theorem toTop_edges (P : GPath G) : P.toTop.edges = P.edges :=
  Walk.edges_mapLe_eq_edges _ _
@[simp] theorem toTop_support (P : GPath G) : P.toTop.walk.support = P.walk.support :=
  Walk.support_mapLe_eq_support _ _
@[simp] theorem toTop_endsAt [DecidableEq V] (P : GPath G) (v : V) :
    P.toTop.endsAt v = P.endsAt v := rfl

/-- A path of the complete graph whose edges lie in `G`, as a path of `G`. -/
def ofTop (P : TPath V) (G : SimpleGraph V) (h : ∀ e ∈ P.walk.edges, e ∈ G.edgeSet) : GPath G :=
  ⟨P.src, P.tgt, P.walk.transfer G h, (Walk.isPath_transfer h).mpr P.isPath,
    by simpa using P.pos⟩

@[simp] theorem ofTop_edges (P : TPath V) (h : ∀ e ∈ P.walk.edges, e ∈ G.edgeSet) :
    (P.ofTop G h).edges = P.edges := Walk.edges_transfer _ _
@[simp] theorem ofTop_endsAt [DecidableEq V] (P : TPath V) (h : ∀ e ∈ P.walk.edges, e ∈ G.edgeSet)
    (v : V) : (P.ofTop G h).endsAt v = P.endsAt v := rfl

@[simp] theorem reverse_src (P : GPath G) : P.reverse.src = P.tgt := rfl
@[simp] theorem reverse_tgt (P : GPath G) : P.reverse.tgt = P.src := rfl
@[simp] theorem reverse_support (P : GPath G) : P.reverse.walk.support = P.walk.support.reverse :=
  Walk.support_reverse _
@[simp] theorem reverse_endsAt' [DecidableEq V] (P : GPath G) (v : V) :
    P.reverse.endsAt v = P.endsAt v := by
  unfold endsAt; simp only [reverse_src, reverse_tgt]; exact add_comm _ _

theorem endsAt_le_one [DecidableEq V] (P : GPath G) (v : V) : P.endsAt v ≤ 1 := by
  have := P.src_ne_tgt
  unfold endsAt
  split_ifs with h1 h2 <;> first | omega | exact absurd (h1.trans h2.symm) this

end GPath

/-! ### Edge multisets and end counts of lists of paths -/

/-- The multiset of edges of a list of paths. -/
def edgesM (L : List (TPath V)) : Multiset (Sym2 V) := (L.flatMap GPath.edges : List (Sym2 V))

@[simp] theorem edgesM_nil : edgesM ([] : List (TPath V)) = 0 := rfl
@[simp] theorem edgesM_cons (P : TPath V) (L : List (TPath V)) :
    edgesM (P :: L) = (P.edges : Multiset (Sym2 V)) + edgesM L := by
  simp [edgesM]
@[simp] theorem edgesM_append (L₁ L₂ : List (TPath V)) :
    edgesM (L₁ ++ L₂) = edgesM L₁ + edgesM L₂ := by
  simp [edgesM]

theorem mem_edgesM {L : List (TPath V)} {e : Sym2 V} :
    e ∈ edgesM L ↔ ∃ P ∈ L, e ∈ P.edges := by
  simp [edgesM, List.mem_flatMap]

/-- The number of ends at `v` of a list of paths. -/
def endsL [DecidableEq V] (L : List (TPath V)) (v : V) : ℕ := (L.map (fun P => P.endsAt v)).sum

@[simp] theorem endsL_nil [DecidableEq V] (v : V) : endsL ([] : List (TPath V)) v = 0 := rfl
@[simp] theorem endsL_cons [DecidableEq V] (P : TPath V) (L : List (TPath V)) (v : V) :
    endsL (P :: L) v = P.endsAt v + endsL L v := by
  simp [endsL]
@[simp] theorem endsL_append [DecidableEq V] (L₁ L₂ : List (TPath V)) (v : V) :
    endsL (L₁ ++ L₂) v = endsL L₁ v + endsL L₂ v := by
  simp [endsL]

section conversions

variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem PathDecomp.edgesM_toTop (D : PathDecomp G) :
    edgesM (D.paths.map GPath.toTop) = G.edgeFinset.val := by
  have h1 : edgesM (D.paths.map GPath.toTop) = (D.paths.flatMap GPath.edges : List (Sym2 V)) := by
    simp only [edgesM, List.flatMap_map, GPath.toTop_edges]
  rw [h1]
  refine (Multiset.Nodup.ext (Multiset.coe_nodup.mpr D.nodup_edges) G.edgeFinset.nodup).mpr ?_
  intro e
  rw [Multiset.mem_coe, Finset.mem_val, mem_edgeFinset, D.covers]

omit [Fintype V] [DecidableRel G.Adj] in
theorem PathDecomp.endsL_toTop (D : PathDecomp G) (v : V) :
    endsL (D.paths.map GPath.toTop) v = D.ends v := by
  simp [endsL, PathDecomp.ends, Function.comp_def]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem PathDecomp.length_toTop (D : PathDecomp G) : (D.paths.map GPath.toTop).length = D.size := by
  simp [PathDecomp.size]

/-- A list of paths of the complete graph whose edge multiset is that of `G` is a decomposition
of `G`. -/
theorem exists_decomp_of_edgesM (L : List (TPath V)) (h : edgesM L = G.edgeFinset.val) :
    ∃ D : PathDecomp G, D.size = L.length ∧ ∀ v, D.ends v = endsL L v := by
  have hmem : ∀ P ∈ L, ∀ e ∈ P.walk.edges, e ∈ G.edgeSet := by
    intro P hP e he
    have : e ∈ edgesM L := mem_edgesM.mpr ⟨P, hP, he⟩
    rw [h, Finset.mem_val, mem_edgeFinset] at this
    exact this
  let L' := L.pmap (fun P hP => P.ofTop G hP) hmem
  have hfl : ∀ (l : List (TPath V)) (hl : ∀ P ∈ l, ∀ e ∈ P.walk.edges, e ∈ G.edgeSet),
      (l.pmap (fun P hP => P.ofTop G hP) hl).flatMap GPath.edges = l.flatMap GPath.edges ∧
      ∀ v, ((l.pmap (fun P hP => P.ofTop G hP) hl).map (fun P => P.endsAt v)).sum = endsL l v := by
    intro l hl
    induction l with
    | nil => simp
    | cons P l ih =>
      obtain ⟨ih1, ih2⟩ := ih (fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ))
      refine ⟨?_, fun v => ?_⟩
      · simp [List.pmap, ih1]
      · simp [List.pmap, ih2 v]
  obtain ⟨h1, h2⟩ := hfl L hmem
  have hnd : (L.flatMap GPath.edges).Nodup := by
    have := G.edgeFinset.nodup
    rw [← h] at this
    exact Multiset.coe_nodup.mp this
  refine ⟨⟨L', by rw [h1]; exact hnd, fun e => ?_⟩, by simp [PathDecomp.size, L'], h2⟩
  rw [h1, ← mem_edgeFinset, ← Finset.mem_val, ← h, edgesM, Multiset.mem_coe]

omit [DecidableEq V] in
/-- Edge multisets of a graph obtained from `H` by adding the (new, distinct) edges `M`. -/
theorem edgeFinset_val_eq_add {H : SimpleGraph V} [DecidableRel H.Adj] (M : Multiset (Sym2 V))
    (hM : M.Nodup) (hdisj : ∀ e ∈ M, e ∉ H.edgeSet)
    (h : ∀ e, e ∈ G.edgeSet ↔ e ∈ H.edgeSet ∨ e ∈ M) :
    G.edgeFinset.val = H.edgeFinset.val + M := by
  refine (Multiset.Nodup.ext G.edgeFinset.nodup (Multiset.nodup_add.mpr
    ⟨H.edgeFinset.nodup, hM, ?_⟩)).mpr ?_
  · rw [Multiset.disjoint_left]
    intro e he he'
    rw [Finset.mem_val, mem_edgeFinset] at he
    exact hdisj e he' he
  · intro e
    rw [Multiset.mem_add, Finset.mem_val, Finset.mem_val, mem_edgeFinset, mem_edgeFinset, h]

end conversions

/-! ### Adding an edge -/

section plusEdge

/-- `G` plus the edge `ab`. -/
def plusEdge (G : SimpleGraph V) (a b : V) : SimpleGraph V where
  Adj p q := G.Adj p q ∨ (p ≠ q ∧ ((p = a ∧ q = b) ∨ (p = b ∧ q = a)))
  symm := ⟨fun _ _ h => by
    rcases h with h | ⟨hne, h⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hne.symm, by tauto⟩⟩
  loopless := ⟨fun p h => by
    rcases h with h | ⟨hne, -⟩
    · exact G.loopless.irrefl _ h
    · exact hne rfl⟩

variable {G : SimpleGraph V} {a b : V}

theorem plusEdge_adj {p q : V} :
    (plusEdge G a b).Adj p q ↔ G.Adj p q ∨ (p ≠ q ∧ ((p = a ∧ q = b) ∨ (p = b ∧ q = a))) :=
  Iff.rfl

instance plusEdge.decRel [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    DecidableRel (plusEdge G a b).Adj := fun p q => inferInstanceAs (Decidable (_ ∨ _))

theorem le_plusEdge : G ≤ plusEdge G a b := fun _ _ h => Or.inl h

theorem plusEdge_edgeSet (hab : a ≠ b) {e : Sym2 V} :
    e ∈ (plusEdge G a b).edgeSet ↔ e ∈ G.edgeSet ∨ e = s(a, b) := by
  induction e using Sym2.inductionOn with
  | hf p q =>
  simp only [mem_edgeSet, plusEdge_adj, Sym2.eq_iff]
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact Or.inl h
    · right; rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · rintro (h | h)
    · exact Or.inl h
    · right
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hab, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨hab.symm, Or.inr ⟨rfl, rfl⟩⟩

theorem plusEdge_degree [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hab : a ≠ b)
    (hn : ¬ G.Adj a b) (v : V) :
    (plusEdge G a b).degree v = G.degree v + if v = a ∨ v = b then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  by_cases hva : v = a
  · subst hva
    have : (plusEdge G v b).neighborFinset v = insert b (G.neighborFinset v) := by
      ext w
      simp only [mem_neighborFinset, plusEdge_adj, Finset.mem_insert]
      constructor
      · rintro (h | ⟨-, ⟨-, rfl⟩ | ⟨rfl, rfl⟩⟩)
        · exact Or.inr h
        · exact Or.inl rfl
        · exact Or.inl rfl
      · rintro (rfl | h)
        · exact Or.inr ⟨hab, by simp⟩
        · exact Or.inl h
    rw [this, Finset.card_insert_of_notMem (by simpa using hn)]
    simp
  by_cases hvb : v = b
  · subst hvb
    have : (plusEdge G a v).neighborFinset v = insert a (G.neighborFinset v) := by
      ext w
      simp only [mem_neighborFinset, plusEdge_adj, Finset.mem_insert]
      constructor
      · rintro (h | ⟨-, ⟨rfl, -⟩ | ⟨-, rfl⟩⟩)
        · exact Or.inr h
        · exact absurd rfl hva
        · exact Or.inl rfl
      · rintro (rfl | h)
        · exact Or.inr ⟨fun h => hab h.symm, by simp⟩
        · exact Or.inl h
    rw [this, Finset.card_insert_of_notMem (by simpa using fun h => hn h.symm)]
    simp [hva]
  · have : (plusEdge G a b).neighborFinset v = G.neighborFinset v := by
      ext w
      simp only [mem_neighborFinset, plusEdge_adj]
      constructor
      · rintro (h | ⟨-, ⟨h, -⟩ | ⟨h, -⟩⟩)
        · exact h
        · exact absurd h hva
        · exact absurd h hvb
      · exact Or.inl
    rw [this]
    simp [hva, hvb]

end plusEdge

/-! ### Gluing walks of the complete graph -/

section glue

theorem nodup_support_append {G : SimpleGraph V} {a b c : V} (p : G.Walk a b)
    (q : G.Walk b c) :
    (p.append q).support.Nodup ↔
      p.support.Nodup ∧ q.support.Nodup ∧ ∀ v ∈ p.support, v ∈ q.support → v = b := by
  rw [Walk.support_append, List.nodup_append]
  have hq : q.support = b :: q.support.tail := (Walk.cons_tail_support q).symm
  constructor
  · rintro ⟨hp, ht, hd⟩
    have hbt : b ∉ q.support.tail := fun h => hd b p.end_mem_support b h rfl
    refine ⟨hp, by rw [hq, List.nodup_cons]; exact ⟨hbt, ht⟩, fun v hv hvq => ?_⟩
    rw [hq, List.mem_cons] at hvq
    rcases hvq with h | h
    · exact h
    · exact absurd rfl (hd v hv v h)
  · rintro ⟨hp, hqn, hd⟩
    rw [hq, List.nodup_cons] at hqn
    refine ⟨hp, hqn.2, fun v hv w hw hvw => ?_⟩
    subst hvw
    have := hd v hv (by rw [hq]; exact List.mem_cons_of_mem _ hw)
    subst this
    exact hqn.1 hw

/-- Glue two walks of `⊤` at their common vertex into a path. -/
def joinT {a b c : V} (p : (⊤ : SimpleGraph V).Walk a b) (q : (⊤ : SimpleGraph V).Walk b c)
    (hp : p.support.Nodup) (hq : q.support.Nodup)
    (hd : ∀ v ∈ p.support, v ∈ q.support → v = b) (hpos : 0 < p.length + q.length) : TPath V :=
  ⟨a, c, p.append q, (Walk.isPath_def _).mpr ((nodup_support_append p q).mpr ⟨hp, hq, hd⟩),
    by rw [Walk.length_append]; exact hpos⟩

section
variable {a b c : V} {p : (⊤ : SimpleGraph V).Walk a b} {q : (⊤ : SimpleGraph V).Walk b c}
  {hp : p.support.Nodup} {hq : q.support.Nodup} {hd : ∀ v ∈ p.support, v ∈ q.support → v = b}
  {hpos : 0 < p.length + q.length}

@[simp] theorem joinT_src : (joinT p q hp hq hd hpos).src = a := rfl
@[simp] theorem joinT_tgt : (joinT p q hp hq hd hpos).tgt = c := rfl
@[simp] theorem joinT_edges : (joinT p q hp hq hd hpos).edges = p.edges ++ q.edges :=
  Walk.edges_append _ _
theorem joinT_support : (joinT p q hp hq hd hpos).walk.support = p.support ++ q.support.tail :=
  Walk.support_append _ _
theorem mem_joinT_support {v : V} :
    v ∈ (joinT p q hp hq hd hpos).walk.support ↔ v ∈ p.support ∨ v ∈ q.support := by
  exact Walk.mem_support_append_iff p q
end

/-- A path with its walk split at a vertex of its support. -/
theorem GPath.exists_split_support {G : SimpleGraph V} (P : GPath G) {v : V}
    (hv : v ∈ P.walk.support) :
    ∃ (q₁ : G.Walk P.src v) (q₂ : G.Walk v P.tgt), P.walk = q₁.append q₂ :=
  Walk.mem_support_iff_exists_append.mp hv

theorem support_nodup_of_append_left {G : SimpleGraph V} {a b c : V} {p : G.Walk a b}
    {q : G.Walk b c} (h : (p.append q).support.Nodup) : p.support.Nodup :=
  ((nodup_support_append p q).mp h).1

theorem support_nodup_of_append_right {G : SimpleGraph V} {a b c : V} {p : G.Walk a b}
    {q : G.Walk b c} (h : (p.append q).support.Nodup) : q.support.Nodup :=
  ((nodup_support_append p q).mp h).2.1

theorem GPath.support_nodup {G : SimpleGraph V} (P : GPath G) : P.walk.support.Nodup :=
  (Walk.isPath_def _).mp P.isPath

end glue

/-! ### Substituting a path for an edge -/

section subst

variable [DecidableEq V]

omit [DecidableEq V] in
/-- Replace the edge `ab` of `R` by a path `T` from `a` to `b` meeting `R` only in `a, b`. -/
theorem exists_subst_path (R T : TPath V) {a b : V} (hab : s(a, b) ∈ R.edges)
    (hTs : T.src = a) (hTt : T.tgt = b)
    (hdisj : ∀ w ∈ T.walk.support, w ∈ R.walk.support → w = a ∨ w = b) :
    ∃ R' : TPath V, R'.src = R.src ∧ R'.tgt = R.tgt ∧
      (R'.edges : Multiset (Sym2 V)) + {s(a, b)} = R.edges + T.edges ∧
      ∀ w ∈ R'.walk.support, w ∈ R.walk.support ∨ w ∈ T.walk.support := by
  obtain ⟨c, d, hcd, q, q', he, hR⟩ := Walk.exists_append_cons_of_mem_edges R.walk hab
  have hRnd := R.support_nodup
  rw [hR] at hRnd
  have hqn := support_nodup_of_append_left hRnd
  have hq'n' := support_nodup_of_append_right hRnd
  have hq'n : q'.support.Nodup := by
    rw [Walk.support_cons, List.nodup_cons] at hq'n'; exact hq'n'.2
  have hRd := ((nodup_support_append q _).mp hRnd).2.2
  -- `d` is not on `q`, `c` is not on `q'`
  have hdq : d ∉ q.support := by
    intro h
    have := hRd d h (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ q'.start_mem_support)
    exact hcd.ne this.symm
  have hcq' : c ∉ q'.support := by
    rw [Walk.support_cons, List.nodup_cons] at hq'n'; exact hq'n'.1
  have hqq' : ∀ w ∈ q.support, w ∉ q'.support := by
    intro w hw hw'
    have := hRd w hw (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hw')
    subst this; exact hcq' hw'
  have hmemR : ∀ w, w ∈ q.support ∨ w ∈ q'.support → w ∈ R.walk.support := by
    intro w hw
    rw [hR, Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons]
    tauto
  -- orient `T` from `c` to `d`
  obtain ⟨T', hT'e, hT's, hT'n, hT'l⟩ : ∃ T' : (⊤ : SimpleGraph V).Walk c d,
      (T'.edges : Multiset (Sym2 V)) = T.edges ∧ (∀ w, w ∈ T'.support ↔ w ∈ T.walk.support) ∧
      T'.support.Nodup ∧ 0 < T'.length := by
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨T.walk.copy hTs hTt, by simp [GPath.edges], by simp, by simpa using T.support_nodup,
        by simpa using T.pos⟩
    · refine ⟨(T.walk.copy hTs hTt).reverse, ?_, by simp, ?_, by simpa using T.pos⟩
      · simp [GPath.edges, Multiset.coe_reverse]
      · simpa using T.support_nodup
  have hTcd : ∀ w ∈ T'.support, w ∈ R.walk.support → w = c ∨ w = d := by
    intro w hw hwR
    have := hdisj w ((hT's w).mp hw) hwR
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
  have h2 : (T'.append q').support.Nodup := by
    refine (nodup_support_append T' q').mpr ⟨hT'n, hq'n, fun w hw hw' => ?_⟩
    rcases hTcd w hw (hmemR w (Or.inr hw')) with rfl | rfl
    · exact absurd hw' hcq'
    · rfl
  have h3 : (q.append (T'.append q')).support.Nodup := by
    refine (nodup_support_append q _).mpr ⟨hqn, h2, fun w hw hw' => ?_⟩
    rw [Walk.mem_support_append_iff] at hw'
    rcases hw' with hw' | hw'
    · rcases hTcd w hw' (hmemR w (Or.inl hw)) with rfl | rfl
      · rfl
      · exact absurd hw hdq
    · exact absurd hw' (hqq' w hw)
  refine ⟨⟨R.src, R.tgt, q.append (T'.append q'), (Walk.isPath_def _).mpr h3, ?_⟩, rfl, rfl,
    ?_, ?_⟩
  · simp only [Walk.length_append]; omega
  · show ((q.append (T'.append q')).edges : Multiset (Sym2 V)) + {s(a, b)} =
      (R.walk.edges : Multiset (Sym2 V)) + T.edges
    rw [hR, ← hT'e]
    simp only [Walk.edges_append, Walk.edges_cons, ← Multiset.coe_add, ← Multiset.cons_coe, he]
    rw [← Multiset.singleton_add]
    abel
  · intro w hw
    simp only [Walk.mem_support_append_iff] at hw
    rcases hw with hw | hw | hw
    · exact Or.inl (hmemR w (Or.inl hw))
    · exact Or.inr ((hT's w).mp hw)
    · exact Or.inl (hmemR w (Or.inr hw))

/-- Substitution inside a list of paths: the path carrying `ab` gets `T` in place of `ab`. -/
theorem exists_subst_list (L : List (TPath V)) {a b : V} (hab : s(a, b) ∈ edgesM L)
    (T : TPath V) (hTs : T.src = a) (hTt : T.tgt = b)
    (hdisj : ∀ R ∈ L, s(a, b) ∈ R.edges →
      ∀ w ∈ T.walk.support, w ∈ R.walk.support → w = a ∨ w = b) :
    ∃ L' : List (TPath V), L'.length = L.length ∧
      edgesM L' + {s(a, b)} = edgesM L + T.edges ∧ (∀ v, endsL L' v = endsL L v) ∧
      ∀ R' ∈ L', ∀ w ∈ R'.walk.support, (∃ R ∈ L, w ∈ R.walk.support) ∨ w ∈ T.walk.support := by
  obtain ⟨R, hRL, hR⟩ := mem_edgesM.mp hab
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hRL
  obtain ⟨R', h1, h2, h3, h4⟩ := exists_subst_path R T hR hTs hTt (hdisj R hRL hR)
  refine ⟨l₁ ++ R' :: l₂, by simp, ?_, fun v => ?_, ?_⟩
  · simp only [edgesM_append, edgesM_cons]
    rw [add_assoc, add_assoc, add_comm _ {s(a, b)}, ← add_assoc (R'.edges : Multiset (Sym2 V)),
      h3]
    abel
  · simp only [endsL_append, endsL_cons, GPath.endsAt, h1, h2]
  · intro Q hQ w hw
    rw [List.mem_append, List.mem_cons] at hQ
    rcases hQ with hQ | rfl | hQ
    · exact Or.inl ⟨Q, by simp [hQ], hw⟩
    · rcases h4 w hw with h | h
      · exact Or.inl ⟨R, hRL, h⟩
      · exact Or.inr h
    · exact Or.inl ⟨Q, by simp [hQ], hw⟩

end subst

end Gallai
