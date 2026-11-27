import GallaiLean.TerminalMatching

/-!
# Three terminal edges: the chained walk theorem (session `claude/ptm`)

Manuscript: `manuscripts/terminal-matching/terminal-matching.tex`, Section 8 (`sec:six`).

Let `G` have no vertex of positive even degree and let `x₁y₁, x₂y₂, x₃y₃` be a matching of `G`.
We look for a Lovász decomposition in which `xᵢyᵢ` is terminal at `xᵢ` (`i = 1, 2, 3`) on three
different paths (`PTM3At`).

* `AdmChain` (Definition 8.1, admissible chain): two duplicate-free edge-disjoint chains,
  `P₂ = y₃ ⋯ x₂` and `P₁ = y₂ ⋯ x₁`, with the vertex and neighbourhood conditions (i), (ii).
  The paper's `y₁ ∉ V(P₂)` is not needed, and `y₁ ∉ V(P₁)` is only used as `x₁y₁ ∉ E(P₁)`;
  `AdmChain.of_paper` builds an `AdmChain` from the paper's conditions.
* `base3G` (the base graph `M`): `((G − x₁y₁) + ℓ₁y₁) − x₂y₂ − x₃y₃ − E(P₁) − E(P₂)`, on `Option W`
  with `ℓ₁ = none`. `base3G_parity`: only `x₃` changes parity, and `ℓ₁` is odd.
* `ptm3_of_base` (**chained walk theorem**, Theorem 8.2): a Lovász decomposition of `M`
  separating the six pairs `{x₁,ℓ₁}, {x₂,y₂}, {x₃,y₃}, {ℓ₁,y₂}, {ℓ₁,y₃}, {y₂,y₃}` gives `PTM3At`.
  Proof: `leaf_walk` (a leaf at the start of a chain, then `walk_back` along it) twice, first
  along `P₂` from `y₃`, then along `P₁` from `y₂` (separations tracked by `leaf_walk_sep_some`,
  `leaf_walk_sep_none`); then `merge3` (`leaf_merge` three times; `merge_sep`, `merge_ne`).
* `base3_of_far`, `ptm3_of_far` (**far-apart form**, Proposition 8.3): when the six ends are
  pairwise at distance at least three in `G − F` (`FarEnds`), the base hypothesis follows from
  `separation_sparse` with `X = {x₁, x₂, x₃, y₂, y₃, ℓ₁}` and the sets `{x₁, ℓ₁}`, `{x₂, y₂}`,
  `{x₃, y₃}`, `{ℓ₁, y₂, y₃}`.
* `lift3`, `stl_of_ptm3`, `stl3_of_base`, `stl3_of_far`, `test1_of_chains3`, `test1_of_bases3`
  (**degree six**, Corollary 8.4): for `z` with `N(z) = {x₁, y₁, x₂, y₂, x₃, y₃}`, `PTM3At` in
  `(J − z) + x₁y₁ + x₂y₂ + x₃y₃` gives `STL J z yᵢ` for `i = 1, 2, 3` (un-lifting three times);
  with far-apart neighbours (`FarNbrs`) and chains for every neighbour, `Test1 J z` by
  `test1_of_stl`.
-/

open SimpleGraph

namespace Gallai

universe u v

/-! ### Edges of chains pushed into an apex graph -/

section mapSym2

variable {U : Type u}

theorem none_not_mem_map_sym2 (L : List (Sym2 U)) (z : Option U) :
    s(none, z) ∉ L.map (Sym2.map some) := by
  intro h
  rw [List.mem_map] at h
  obtain ⟨e, -, he⟩ := h
  have : (none : Option U) ∈ e.map some := by rw [he]; exact Sym2.mem_mk_left _ _
  rw [Sym2.mem_map] at this
  obtain ⟨_, -, h⟩ := this
  exact Option.some_ne_none _ h

theorem some_mem_map_sym2 (L : List (Sym2 U)) (r r' : U) :
    s(some r, some r') ∈ L.map (Sym2.map some) ↔ s(r, r') ∈ L := by
  rw [List.mem_map]
  constructor
  · rintro ⟨e, he, h⟩
    rw [show s(some r, some r') = s(r, r').map some from rfl] at h
    rwa [Sym2.map.injective (Option.some_injective _) h] at he
  · intro h; exact ⟨_, h, rfl⟩

theorem none_not_mem_map_some (l : List U) : (none : Option U) ∉ l.map some := by
  intro h; rw [List.mem_map] at h; obtain ⟨_, _, h⟩ := h; exact Option.some_ne_none _ h

theorem some_mem_map_some {l : List U} {a : U} : some a ∈ l.map some ↔ a ∈ l := by
  rw [List.mem_map]
  constructor
  · rintro ⟨b, hb, h⟩; rw [Option.some.injEq] at h; subst h; exact hb
  · intro h; exact ⟨a, h, rfl⟩

/-- Deleting a chain commutes with adding an apex vertex. -/
theorem apex_delChain_edge (K K₀ : SimpleGraph U) (r : U) (L : List U)
    (hK₀ : ∀ e, e ∈ K₀.edgeSet ↔ e ∈ K.edgeSet ∧ e ∉ chainEdges L) :
    ∀ e, e ∈ (apex K₀ {r}).edgeSet ↔ e ∈ (apex K {r}).edgeSet ∧ e ∉ chainEdges (L.map some) := by
  intro e
  rw [chainEdges_map]
  induction e using Sym2.inductionOn with
  | hf c d =>
    rw [mem_edgeSet, mem_edgeSet]
    cases c with
    | none =>
      cases d with
      | none => simp
      | some d =>
        simp only [apex_adj_none_some]
        exact ⟨fun h => ⟨h, none_not_mem_map_sym2 _ _⟩, fun h => h.1⟩
    | some c =>
      cases d with
      | none =>
        simp only [apex_adj_some_none]
        refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
        rw [Sym2.eq_swap]; exact none_not_mem_map_sym2 _ _
      | some d =>
        rw [apex_adj_some_some, apex_adj_some_some, some_mem_map_sym2]
        have := hK₀ s(c, d)
        rwa [mem_edgeSet, mem_edgeSet] at this

end mapSym2

/-! ### A leaf at the start of a chain, then a walk back along it -/

section leafWalk

variable {U : Type u} [Fintype U] [DecidableEq U]

/-- **Leaf and walk.** Let `w :: l` be a duplicate-free chain of `K`, `K₀ = K − E(chain)`, and `P` a
path of `D` (a decomposition of `K₀`) ending at `w`. Extending `P` by a leaf at `w` and walking the
end back along the chain gives a decomposition of `apex K {w}` in which the last vertex has lost
one end and the leaf has one; every new path lies in an old path `R` together with the leaf and the
targets (`initOf w l`), and `R = P` if the new path contains the leaf. -/
theorem leaf_walk (K : SimpleGraph U) [DecidableRel K.Adj] (w : U) (l : List U)
    (K₀ : SimpleGraph U) [DecidableRel K₀.Adj] (D : PathDecomp K₀)
    (hch : ChainAdj K (w :: l)) (hnd : (w :: l).Nodup)
    (hK₀ : ∀ e, e ∈ K₀.edgeSet ↔ e ∈ K.edgeSet ∧ e ∉ chainEdges (w :: l))
    {P : GPath K₀} (hP : P ∈ D.paths) (hPw : P.src = w ∨ P.tgt = w)
    (hZ : ∀ t ∈ initOf w l, ∀ v, K.Adj t v → v ≠ w → 1 ≤ D.ends v) :
    ∃ D' : PathDecomp (apex K {w}),
      (∀ v, D'.ends (some v) + (if v = chainLast w l then 1 else 0) = D.ends v) ∧
      D'.ends none = 1 ∧
      ∀ Q ∈ D'.paths, ∃ R ∈ D.paths, (none ∈ Q.walk.support → R = P) ∧
        ∀ z ∈ Q.walk.support, z = none ∨ ∃ y, z = some y ∧ (y ∈ R.walk.support ∨ y ∈ initOf w l) := by
  obtain ⟨D₁, hD₁some, hD₁none, hcov₁⟩ := D.liftLeaf hP hPw
  have hchH : ChainAdj (apex K {w}) ((w :: l).map some) :=
    chainAdj_map some (fun _ _ h => (apex_adj_some_some).mpr h) (w :: l) hch
  have hndH : ((w :: l).map some).Nodup := hnd.map (Option.some_injective _)
  have hK₀H := apex_delChain_edge K K₀ w (w :: l) hK₀
  have hZH : ∀ t ∈ initOf (some w) (l.map some), ∀ v, (apex K {w}).Adj t v → v ≠ some w →
      1 ≤ D₁.ends v := by
    intro t ht v htv hvw
    rw [initOf_map, List.mem_map] at ht
    obtain ⟨t', ht', rfl⟩ := ht
    cases v with
    | none => rw [hD₁none]
    | some v =>
      have hvw' : v ≠ w := fun h => hvw (by rw [h])
      have h1 := hD₁some v
      rw [ite_eq_right hvw', add_zero] at h1
      rw [h1]
      exact hZ t' ht' v ((apex_adj_some_some).mp htv) hvw'
  obtain ⟨D₂, hD₂e, hcov₂⟩ :=
    walk_back (apex K {w}) (l.map some) (some w) (apex K₀ {w}) D₁ hchH hndH hK₀H hZH
  rw [chainLast_map] at hD₂e
  refine ⟨D₂, fun v => ?_, ?_, fun Q hQ => ?_⟩
  · have h1 := hD₂e (some v)
    have h2 := hD₁some v
    simp only [Option.some.injEq] at h1
    omega
  · have h1 := hD₂e none
    simp only [reduceCtorEq, ite_false, add_zero] at h1
    rw [h1, hD₁none]
  · obtain ⟨Q₁, hQ₁, hs₁⟩ := hcov₂ Q hQ
    rw [initOf_map] at hs₁
    rcases hcov₁ Q₁ hQ₁ with hA | ⟨R, hR, hRs⟩
    · refine ⟨P, hP, fun _ => rfl, fun z hz => ?_⟩
      rcases hs₁ z hz with h | h
      · rcases hA z h with h' | ⟨y, hy, rfl⟩
        · exact Or.inl h'
        · exact Or.inr ⟨y, rfl, Or.inl hy⟩
      · rw [List.mem_map] at h
        obtain ⟨y, hy, rfl⟩ := h
        exact Or.inr ⟨y, rfl, Or.inr hy⟩
    · refine ⟨R, hR, fun hn => ?_, fun z hz => ?_⟩
      · exfalso
        rcases hs₁ none hn with h | h
        · rw [hRs] at h; exact none_not_mem_map_some _ h
        · exact none_not_mem_map_some _ h
      · rcases hs₁ z hz with h | h
        · rw [hRs, List.mem_map] at h
          obtain ⟨y, hy, rfl⟩ := h
          exact Or.inr ⟨y, rfl, Or.inl hy⟩
        · rw [List.mem_map] at h
          obtain ⟨y, hy, rfl⟩ := h
          exact Or.inr ⟨y, rfl, Or.inr hy⟩

omit [Fintype U] [DecidableEq U] in
/-- A separation of two vertices off the targets survives `leaf_walk`. -/
theorem leaf_walk_sep_some {K K₀ : SimpleGraph U} {w : U} {D : PathDecomp K₀}
    {D' : PathDecomp (apex K {w})} {P : GPath K₀} {T : List U}
    (hcov : ∀ Q ∈ D'.paths, ∃ R ∈ D.paths, (none ∈ Q.walk.support → R = P) ∧
      ∀ z ∈ Q.walk.support, z = none ∨ ∃ y, z = some y ∧ (y ∈ R.walk.support ∨ y ∈ T))
    {c d : U} (hc : c ∉ T) (hd : d ∉ T) (hs : Separates D c d) :
    Separates D' (some c) (some d) := by
  intro Q hQ ⟨h1, h2⟩
  obtain ⟨R, hR, -, hz⟩ := hcov Q hQ
  rcases hz _ h1 with h | ⟨y, hy, hy'⟩
  · exact Option.some_ne_none _ h
  rcases hz _ h2 with h | ⟨y', hy2, hy2'⟩
  · exact Option.some_ne_none _ h
  rw [Option.some.injEq] at hy hy2
  subst hy; subst hy2
  exact hs R hR ⟨hy'.resolve_right hc, hy2'.resolve_right hd⟩

omit [Fintype U] [DecidableEq U] in
/-- After `leaf_walk`, the new leaf is separated from every vertex off the targets and off `P`. -/
theorem leaf_walk_sep_none {K K₀ : SimpleGraph U} {w : U} {D : PathDecomp K₀}
    {D' : PathDecomp (apex K {w})} {P : GPath K₀} {T : List U}
    (hcov : ∀ Q ∈ D'.paths, ∃ R ∈ D.paths, (none ∈ Q.walk.support → R = P) ∧
      ∀ z ∈ Q.walk.support, z = none ∨ ∃ y, z = some y ∧ (y ∈ R.walk.support ∨ y ∈ T))
    {c : U} (hc : c ∉ T) (hcP : c ∉ P.walk.support) : Separates D' (some c) none := by
  intro Q hQ ⟨h1, h2⟩
  obtain ⟨R, hR, hRP, hz⟩ := hcov Q hQ
  obtain rfl := hRP h2
  rcases hz _ h1 with h | ⟨y, hy, hy'⟩
  · exact Option.some_ne_none _ h
  rw [Option.some.injEq] at hy; subst hy
  exact hcP (hy'.resolve_right hc)

end leafWalk

/-! ### Merging leaves -/

section merge

variable {W : Type u} [DecidableEq W]

omit [DecidableEq W] in
/-- A path ending at the leaf of `apex K {r}` contains the leaf edge. -/
theorem leaf_edge_of_end {K : SimpleGraph W} {r : W} {P : GPath (apex K {r})}
    (hPend : P.src = none ∨ P.tgt = none) : s(some r, none) ∈ P.edges := by
  have key : ∀ e ∈ P.edges, (none : Option W) ∈ e → s(some r, none) ∈ P.edges := by
    intro e he hne
    have heH := P.walk.edges_subset_edgeSet he
    rw [apex_none_pendant e heH hne, Sym2.eq_swap] at he
    exact he
  rcases hPend with h | h
  · obtain ⟨e, he, hx⟩ := P.exists_edge_at_src
    exact key e he (h ▸ hx)
  · obtain ⟨e, he, hx⟩ := P.exists_edge_at_tgt
    exact key e he (h ▸ hx)

/-- Separations of old vertices other than `x` pass through a leaf merge into `x`. -/
theorem merge_sep {H : SimpleGraph (Option W)} {G : SimpleGraph W} {x : W} {DH : PathDecomp H}
    {D : PathDecomp G}
    (hback : ∀ Q ∈ D.paths, ∃ P ∈ DH.paths, Q.walk.support = P.walk.support.map (mergeMap x))
    {c d : W} (hc : c ≠ x) (hd : d ≠ x) (hs : Separates DH (some c) (some d)) :
    Separates D c d := by
  intro Q hQ ⟨h1, h2⟩
  obtain ⟨P, hP, hs'⟩ := hback Q hQ
  rw [hs', List.mem_map] at h1 h2
  obtain ⟨p, hp, e1⟩ := h1
  obtain ⟨p', hp', e2⟩ := h2
  rw [mergeMap_eq_iff] at e1 e2
  rcases e1 with rfl | ⟨-, h⟩
  · rcases e2 with rfl | ⟨-, h⟩
    · exact hs P hP ⟨hp, hp'⟩
    · exact hd h
  · exact hc h

/-- Different paths stay different under a leaf merge. -/
theorem merge_ne (G : SimpleGraph W) {x u : W} (hxu : G.Adj x u)
    {DH : PathDecomp (apex (delEdge G u x) {u})} {P P' : GPath (apex (delEdge G u x) {u})}
    (hP : P ∈ DH.paths) (hP' : P' ∈ DH.paths) (hne : P ≠ P') {Q Q' : GPath G}
    (hQ : Q.edges = P.edges.map (Sym2.map (mergeMap x)))
    (hQ' : Q'.edges = P'.edges.map (Sym2.map (mergeMap x))) : Q ≠ Q' := by
  intro h
  obtain ⟨e, he, -⟩ := P.exists_edge_at_src
  have hmem : e.map (mergeMap x) ∈ Q'.edges := by
    rw [← h, hQ]; exact List.mem_map.mpr ⟨e, he, rfl⟩
  rw [hQ', List.mem_map] at hmem
  obtain ⟨e', he', heq⟩ := hmem
  have := merge_hEinj G hxu e' (P'.walk.edges_subset_edgeSet he') e
    (P.walk.edges_subset_edgeSet he) heq
  subst this
  exact hne (DH.eq_of_mem_edges hP hP' he he')

end merge

/-! ### Small facts -/

section small

variable {U : Type u}

theorem nodup6 {a b c d e f : U} (h : [a, b, c, d, e, f].Nodup) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ f ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧
      c ≠ d ∧ c ≠ e ∧ c ≠ f ∧ d ≠ e ∧ d ≠ f ∧ e ≠ f := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at h
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩, ⟨h10, h11, h12⟩, ⟨h13, h14⟩, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

theorem sym2_some_eq_iff {a b c d : U} :
    s(some a, some b) = s(some c, some d) ↔ s(a, b) = s(c, d) := by
  rw [show s(some a, some b) = s(a, b).map some from rfl,
    show s(some c, some d) = s(c, d).map some from rfl]
  exact (Sym2.map.injective (Option.some_injective _)).eq_iff

theorem sym2_none_ne {a b : U} {z : Option U} : s(none, z) ≠ s(some a, some b) := by
  intro h
  have : (none : Option U) ∈ s(some a, some b) := h ▸ Sym2.mem_mk_left _ _
  rcases Sym2.mem_iff.mp this with h | h <;> exact Option.some_ne_none _ h.symm

theorem sym2_ne_of {a b c d : U} (hac : a ≠ c) (had : a ≠ d) : s(a, b) ≠ s(c, d) := by
  intro h
  have : a ∈ s(c, d) := h ▸ Sym2.mem_mk_left _ _
  rcases Sym2.mem_iff.mp this with h | h
  · exact hac h
  · exact had h

theorem mem_of_chainEdges_eq {l : List U} {a b c d : U} (he : s(a, b) ∈ chainEdges l)
    (h : s(a, b) = s(c, d)) : c ∈ l ∧ d ∈ l :=
  ⟨mem_of_mem_chainEdges l he c (h ▸ Sym2.mem_mk_left c d),
    mem_of_mem_chainEdges l he d (h ▸ Sym2.mem_mk_right c d)⟩

theorem chainAdj_map_edge {U' : Type*} {K : SimpleGraph U} {K' : SimpleGraph U'} (f : U → U') :
    ∀ l : List U, ChainAdj K l → (∀ a b, K.Adj a b → s(a, b) ∈ chainEdges l → K'.Adj (f a) (f b)) →
      ChainAdj K' (l.map f)
  | a :: b :: t, h, hf => by
      simp only [List.map_cons, ChainAdj] at h ⊢
      refine ⟨hf a b h.1 (by simp [chainEdges]), ?_⟩
      rw [← List.map_cons]
      exact chainAdj_map_edge f (b :: t) h.2 (fun c d hcd he => hf c d hcd (by
        simp only [chainEdges, List.mem_cons]; exact Or.inr he))
  | [], _, _ => trivial
  | [_], _, _ => trivial

theorem none_not_mem_chainEdges_map (L : List U) (z : Option U) :
    s(none, z) ∉ chainEdges (L.map some) := fun h =>
  none_not_mem_map_some L (mem_of_mem_chainEdges _ h none (Sym2.mem_mk_left _ _))

end small

/-! ### The base graph and the admissible chain -/

section defs

variable {W : Type u}

/-- **Admissible chain** (Definition 8.1) for the lists `y₃ :: q₂` (the path `P₂` from `y₃` to
`x₂`) and `y₂ :: q₁` (the path `P₁` from `y₂` to `x₁`). Compared with the paper, `y₁ ∉ V(P₂)` is
not required, and `y₁ ∉ V(P₁)` is weakened to `x₁y₁ ∉ E(P₁)` (see `AdmChain.of_paper`). Neither
chain uses an edge `xᵢyᵢ`: this follows from the vertex conditions. -/
structure AdmChain (G : SimpleGraph W) (x₁ y₁ x₂ y₂ x₃ y₃ : W) (q₁ q₂ : List W) : Prop where
  last₂ : chainLast y₃ q₂ = x₂
  chain₂ : ChainAdj G (y₃ :: q₂)
  nodup₂ : (y₃ :: q₂).Nodup
  x₁_notMem₂ : x₁ ∉ y₃ :: q₂
  y₂_notMem₂ : y₂ ∉ y₃ :: q₂
  x₃_notMem₂ : x₃ ∉ y₃ :: q₂
  nadj₂ : ∀ t ∈ initOf y₃ q₂, t ≠ y₃ → ¬ G.Adj t x₃
  last₁ : chainLast y₂ q₁ = x₁
  chain₁ : ChainAdj G (y₂ :: q₁)
  nodup₁ : (y₂ :: q₁).Nodup
  f₁_notMem₁ : s(x₁, y₁) ∉ chainEdges (y₂ :: q₁)
  x₂_notMem₁ : x₂ ∉ y₂ :: q₁
  x₃_notMem₁ : x₃ ∉ y₂ :: q₁
  nadj₁ : ∀ t ∈ initOf y₂ q₁, t ≠ y₂ → ¬ G.Adj t x₂
  nadj₁' : ∀ t ∈ initOf y₂ q₁, ¬ G.Adj t x₃
  disj : ∀ e ∈ chainEdges (y₂ :: q₁), e ∉ chainEdges (y₃ :: q₂)

/-- The paper's form of Definition 8.1 (with `y₁ ∉ V(P₁)`, `y₁ ∉ V(P₂)`) gives an admissible
chain. -/
theorem AdmChain.of_paper {G : SimpleGraph W} {x₁ y₁ x₂ y₂ x₃ y₃ : W} {q₁ q₂ : List W}
    (last₂ : chainLast y₃ q₂ = x₂) (chain₂ : ChainAdj G (y₃ :: q₂)) (nodup₂ : (y₃ :: q₂).Nodup)
    (v₂ : x₁ ∉ y₃ :: q₂ ∧ y₁ ∉ y₃ :: q₂ ∧ y₂ ∉ y₃ :: q₂ ∧ x₃ ∉ y₃ :: q₂)
    (nadj₂ : ∀ t ∈ initOf y₃ q₂, t ≠ y₃ → ¬ G.Adj t x₃)
    (last₁ : chainLast y₂ q₁ = x₁) (chain₁ : ChainAdj G (y₂ :: q₁)) (nodup₁ : (y₂ :: q₁).Nodup)
    (v₁ : y₁ ∉ y₂ :: q₁ ∧ x₂ ∉ y₂ :: q₁ ∧ x₃ ∉ y₂ :: q₁)
    (nadj₁ : ∀ t ∈ initOf y₂ q₁, t ≠ y₂ → ¬ G.Adj t x₂) (nadj₁' : ∀ t ∈ initOf y₂ q₁, ¬ G.Adj t x₃)
    (disj : ∀ e ∈ chainEdges (y₂ :: q₁), e ∉ chainEdges (y₃ :: q₂)) :
    AdmChain G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂ :=
  ⟨last₂, chain₂, nodup₂, v₂.1, v₂.2.2.1, v₂.2.2.2, nadj₂, last₁, chain₁, nodup₁,
    fun h => v₁.1 (mem_of_mem_chainEdges _ h y₁ (Sym2.mem_mk_right _ _)), v₁.2.1, v₁.2.2,
    nadj₁, nadj₁', disj⟩

/-- `L₁ − x₂y₂ − x₃y₃`, where `L₁ = (G − x₁y₁) + ℓ₁y₁` (`ℓ₁ = none`). -/
abbrev mid3G (G : SimpleGraph W) (x₁ y₁ x₂ y₂ x₃ y₃ : W) : SimpleGraph (Option W) :=
  delEdge (delEdge (leafG G x₁ y₁) (some y₂) (some x₂)) (some y₃) (some x₃)

/-- `M + E(P₂) = L₁ − x₂y₂ − x₃y₃ − E(P₁)`. -/
abbrev half3G (G : SimpleGraph W) (x₁ y₁ x₂ y₂ x₃ y₃ : W) (q₁ : List W) :
    SimpleGraph (Option W) :=
  delChain (mid3G G x₁ y₁ x₂ y₂ x₃ y₃) ((y₂ :: q₁).map some)

/-- **The base graph** `M = ((G − x₁y₁) + ℓ₁y₁) − x₂y₂ − x₃y₃ − E(P₁) − E(P₂)` (`ℓ₁ = none`). -/
abbrev base3G (G : SimpleGraph W) (x₁ y₁ x₂ y₂ x₃ y₃ : W) (q₁ q₂ : List W) :
    SimpleGraph (Option W) :=
  delChain (half3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁) ((y₃ :: q₂).map some)

/-- The three-leaf graph `H = (G − x₁y₁ − x₂y₂ − x₃y₃) + ℓ₁y₁ + ℓ₂y₂ + ℓ₃y₃`, built as a leaf graph
of a leaf graph of a leaf graph (`ℓ₂ = none`, `ℓ₃ = some none`, `ℓ₁ = some (some none)`). -/
abbrev leaf3G (G : SimpleGraph W) (x₁ y₁ x₂ y₂ x₃ y₃ : W) :
    SimpleGraph (Option (Option (Option W))) :=
  leafG (leafG (leafG G x₁ y₁) (some x₃) (some y₃)) (some (some x₂)) (some (some y₂))

/-- Named decidability instances, so that statements about `base3G` elaborate without raising
`synthInstance.maxSize`. -/
instance mid3G.decRel [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (x₁ y₁ x₂ y₂ x₃ y₃ : W) : DecidableRel (mid3G G x₁ y₁ x₂ y₂ x₃ y₃).Adj :=
  inferInstanceAs (DecidableRel
    (delEdge (delEdge (leafG G x₁ y₁) (some y₂) (some x₂)) (some y₃) (some x₃)).Adj)

instance half3G.decRel [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (x₁ y₁ x₂ y₂ x₃ y₃ : W) (q₁ : List W) : DecidableRel (half3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁).Adj :=
  inferInstanceAs (DecidableRel (delChain (mid3G G x₁ y₁ x₂ y₂ x₃ y₃) ((y₂ :: q₁).map some)).Adj)

instance base3G.decRel [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (x₁ y₁ x₂ y₂ x₃ y₃ : W) (q₁ q₂ : List W) :
    DecidableRel (base3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂).Adj :=
  inferInstanceAs
    (DecidableRel (delChain (half3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁) ((y₃ :: q₂).map some)).Adj)

theorem leafG_adj_some_some (G : SimpleGraph W) (a b u w : W) :
    (leafG G a b).Adj (some u) (some w) ↔ G.Adj u w ∧ s(u, w) ≠ s(b, a) := Iff.rfl

theorem leafG_adj_none (G : SimpleGraph W) (a b : W) (z : Option W) :
    (leafG G a b).Adj none z ↔ z = some b := by
  cases z with
  | none => exact ⟨fun h => absurd h apex_not_adj_none_none, fun h => absurd h (by simp)⟩
  | some c =>
    show c ∈ ({b} : Finset W) ↔ _
    rw [Finset.mem_singleton, Option.some.injEq]

theorem mid3G_adj_some_some (G : SimpleGraph W) (x₁ y₁ x₂ y₂ x₃ y₃ u w : W) :
    (mid3G G x₁ y₁ x₂ y₂ x₃ y₃).Adj (some u) (some w) ↔
      G.Adj u w ∧ s(u, w) ≠ s(y₁, x₁) ∧ s(u, w) ≠ s(y₂, x₂) ∧ s(u, w) ≠ s(y₃, x₃) := by
  show (((leafG G x₁ y₁).Adj (some u) (some w) ∧ ¬ s(some u, some w) = s(some y₂, some x₂)) ∧
    ¬ s(some u, some w) = s(some y₃, some x₃)) ↔ _
  rw [leafG_adj_some_some, sym2_some_eq_iff, sym2_some_eq_iff]
  tauto

theorem mid3G_adj_none (G : SimpleGraph W) (x₁ y₁ x₂ y₂ x₃ y₃ : W) (z : Option W) :
    (mid3G G x₁ y₁ x₂ y₂ x₃ y₃).Adj none z ↔ z = some y₁ := by
  show (((leafG G x₁ y₁).Adj none z ∧ ¬ s(none, z) = s(some y₂, some x₂)) ∧
    ¬ s(none, z) = s(some y₃, some x₃)) ↔ _
  rw [leafG_adj_none]
  exact ⟨fun h => h.1.1, fun h => ⟨⟨h, sym2_none_ne⟩, sym2_none_ne⟩⟩

theorem base3G_adj_some_some (G : SimpleGraph W) (x₁ y₁ x₂ y₂ x₃ y₃ : W) (q₁ q₂ : List W)
    (u w : W) :
    (base3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂).Adj (some u) (some w) ↔
      G.Adj u w ∧ s(u, w) ≠ s(y₁, x₁) ∧ s(u, w) ≠ s(y₂, x₂) ∧ s(u, w) ≠ s(y₃, x₃) ∧
        s(u, w) ∉ chainEdges (y₂ :: q₁) ∧ s(u, w) ∉ chainEdges (y₃ :: q₂) := by
  classical
  rw [base3G, delChain_adj, half3G, delChain_adj, mid3G_adj_some_some, mem_chainEdges_map_some,
    mem_chainEdges_map_some]
  tauto

theorem base3G_adj_none (G : SimpleGraph W) (x₁ y₁ x₂ y₂ x₃ y₃ : W) (q₁ q₂ : List W)
    (z : Option W) : (base3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂).Adj none z ↔ z = some y₁ := by
  rw [base3G, delChain_adj, half3G, delChain_adj, mid3G_adj_none]
  exact ⟨fun h => h.1.1, fun h => ⟨⟨h, none_not_mem_chainEdges_map _ _⟩,
    none_not_mem_chainEdges_map _ _⟩⟩

/-- Edges of `P₁` are edges of `L₁ − x₂y₂ − x₃y₃`. -/
theorem chain₁_mid {G : SimpleGraph W} {x₁ y₁ x₂ y₂ x₃ y₃ : W} {q₁ q₂ : List W}
    (hC : AdmChain G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂) :
    ChainAdj (mid3G G x₁ y₁ x₂ y₂ x₃ y₃) ((y₂ :: q₁).map some) :=
  chainAdj_map_edge some (y₂ :: q₁) hC.chain₁ fun a b hab he => by
    rw [mid3G_adj_some_some]
    refine ⟨hab, fun h => hC.f₁_notMem₁ ?_, fun h => hC.x₂_notMem₁ (mem_of_chainEdges_eq he h).2,
      fun h => hC.x₃_notMem₁ (mem_of_chainEdges_eq he h).2⟩
    rw [h, Sym2.eq_swap] at he; exact he

/-- Edges of `P₂` are edges of `L₁ − x₂y₂ − x₃y₃ − E(P₁)`. -/
theorem chain₂_half [DecidableEq W] {G : SimpleGraph W} {x₁ y₁ x₂ y₂ x₃ y₃ : W} {q₁ q₂ : List W}
    (hC : AdmChain G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂) :
    ChainAdj (half3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁) ((y₃ :: q₂).map some) :=
  chainAdj_map_edge some (y₃ :: q₂) hC.chain₂ fun a b hab he => by
    rw [half3G, delChain_adj, mid3G_adj_some_some, mem_chainEdges_map_some]
    exact ⟨⟨hab, fun h => hC.x₁_notMem₂ (mem_of_chainEdges_eq he h).2,
      fun h => hC.y₂_notMem₂ (mem_of_chainEdges_eq he h).1,
      fun h => hC.x₃_notMem₂ (mem_of_chainEdges_eq he h).2⟩, fun h => hC.disj _ h he⟩

end defs

section parity

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- **Degree parities in the base graph**: only `x₃` changes parity, and the leaf `ℓ₁` is odd. -/
theorem base3G_parity (G : SimpleGraph W) [DecidableRel G.Adj] {x₁ y₁ x₂ y₂ x₃ y₃ : W}
    (h₁ : G.Adj x₁ y₁) (h₂ : G.Adj x₂ y₂) (h₃ : G.Adj x₃ y₃)
    (hne : [x₁, y₁, x₂, y₂, x₃, y₃].Nodup) {q₁ q₂ : List W}
    (hC : AdmChain G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂) :
    (∀ v, (base3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂).degree (some v) % 2 =
        (G.degree v + if v = x₃ then 1 else 0) % 2) ∧
      (base3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂).degree none % 2 = 1 := by
  obtain ⟨hx₁y₁, hx₁x₂, hx₁y₂, hx₁x₃, hx₁y₃, hy₁x₂, hy₁y₂, hy₁x₃, hy₁y₃, hx₂y₂, hx₂x₃, hx₂y₃,
    hy₂x₃, hy₂y₃, hx₃y₃⟩ := nodup6 hne
  have hq₁ : q₁.map some ≠ [] := by
    intro h; rw [List.map_eq_nil_iff] at h; subst h
    exact hx₁y₂ (hC.last₁.symm.trans rfl)
  have hq₂ : q₂.map some ≠ [] := by
    intro h; rw [List.map_eq_nil_iff] at h; subst h
    exact hx₂y₃ (hC.last₂.symm.trans rfl)
  have hL₁ : (leafG G x₁ y₁).Adj (some y₂) (some x₂) :=
    ⟨h₂.symm, sym2_ne_of (Ne.symm hy₁y₂) (Ne.symm hx₁y₂)⟩
  have hN₁ : (delEdge (leafG G x₁ y₁) (some y₂) (some x₂)).Adj (some y₃) (some x₃) := by
    refine ⟨⟨h₃.symm, sym2_ne_of (Ne.symm hy₁y₃) (Ne.symm hx₁y₃)⟩, ?_⟩
    rw [sym2_some_eq_iff]; exact sym2_ne_of (Ne.symm hy₂y₃) (Ne.symm hx₂y₃)
  have hch₁ := chain₁_mid hC
  have hch₂ := chain₂_half hC
  have hnd₁ : ((y₂ :: q₁).map some).Nodup := hC.nodup₁.map (Option.some_injective _)
  have hnd₂ : ((y₃ :: q₂).map some).Nodup := hC.nodup₂.map (Option.some_injective _)
  have hl₁ : chainLast (some y₂) (q₁.map some) = some x₁ := by rw [chainLast_map, hC.last₁]
  have hl₂ : chainLast (some y₃) (q₂.map some) = some x₂ := by rw [chainLast_map, hC.last₂]
  have hd₁ : ∀ w, ((base3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂).degree w + (if w = some y₃ then 1 else 0) +
      (if w = some x₂ then 1 else 0)) % 2 = (half3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁).degree w % 2 := by
    intro w
    have := delChain_degree_mod (half3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁) (some y₃) (q₂.map some) hq₂
      hch₂ hnd₂ w
    rwa [hl₂] at this
  have hd₂ : ∀ w, ((half3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁).degree w + (if w = some y₂ then 1 else 0) +
      (if w = some x₁ then 1 else 0)) % 2 = (mid3G G x₁ y₁ x₂ y₂ x₃ y₃).degree w % 2 := by
    intro w
    have := delChain_degree_mod (mid3G G x₁ y₁ x₂ y₂ x₃ y₃) (some y₂) (q₁.map some) hq₁
      hch₁ hnd₁ w
    rwa [hl₁] at this
  have hd₃ : ∀ w, (mid3G G x₁ y₁ x₂ y₂ x₃ y₃).degree w + (if w = some y₃ then 1 else 0) +
      (if w = some x₃ then 1 else 0) =
        (delEdge (leafG G x₁ y₁) (some y₂) (some x₂)).degree w :=
    fun w => delEdge_degree (delEdge (leafG G x₁ y₁) (some y₂) (some x₂)) hN₁ w
  have hd₄ : ∀ w, (delEdge (leafG G x₁ y₁) (some y₂) (some x₂)).degree w +
      (if w = some y₂ then 1 else 0) + (if w = some x₂ then 1 else 0) = (leafG G x₁ y₁).degree w :=
    fun w => delEdge_degree (leafG G x₁ y₁) hL₁ w
  have hd₅ : ∀ v, (leafG G x₁ y₁).degree (some v) =
      (delEdge G y₁ x₁).degree v + if v = y₁ then 1 else 0 := by
    intro v
    show (apex (delEdge G y₁ x₁) {y₁}).degree (some v) = _
    rw [apex_degree_some]; simp only [Finset.mem_singleton]
  have hd₅' : (leafG G x₁ y₁).degree none = 1 := by
    show (apex (delEdge G y₁ x₁) {y₁}).degree none = _
    rw [apex_degree_none]; simp
  have hd₆ := fun v => delEdge_degree G h₁.symm v
  refine ⟨fun v => ?_, ?_⟩
  · have e₁ := hd₁ (some v)
    have e₂ := hd₂ (some v)
    have e₃ := hd₃ (some v)
    have e₄ := hd₄ (some v)
    have e₅ := hd₅ v
    have e₆ := hd₆ v
    simp only [Option.some.injEq] at e₁ e₂ e₃ e₄
    omega
  · have e₁ := hd₁ none
    have e₂ := hd₂ none
    have e₃ := hd₃ none
    have e₄ := hd₄ none
    simp only [reduceCtorEq, ite_false, add_zero] at e₁ e₂ e₃ e₄
    omega

end parity

/-! ### Step 5: merging the three leaves -/

section merge3

theorem mem_support_of_end {T : Type*} {K : SimpleGraph T} {P : GPath K} {t : T}
    (h : P.src = t ∨ P.tgt = t) : t ∈ P.walk.support := by
  rcases h with h | h
  · rw [← h]; exact P.walk.start_mem_support
  · rw [← h]; exact P.walk.end_mem_support

theorem merge_end {T : Type*} {x : T} {ps pt : Option T} {qs qt : T} (hs : qs = mergeMap x ps)
    (ht : qt = mergeMap x pt) {t : Option T} (h : ps = t ∨ pt = t) :
    qs = mergeMap x t ∨ qt = mergeMap x t := by
  rcases h with h | h
  · left; rw [hs, h]
  · right; rw [ht, h]

theorem merge_edge {T : Type*} {x : T} {l : List (Sym2 (Option T))} {a b : Option T}
    (h : s(a, b) ∈ l) : s(mergeMap x a, mergeMap x b) ∈ l.map (Sym2.map (mergeMap x)) :=
  List.mem_map.mpr ⟨_, h, rfl⟩

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- `xᵢyᵢ` is terminal at `xᵢ` for `i = 1, 2, 3`, on three different paths of a Lovász
decomposition of `G`. -/
def PTM3At (G : SimpleGraph W) [DecidableRel G.Adj] (x₁ y₁ x₂ y₂ x₃ y₃ : W) : Prop :=
  ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
    ∃ P₁ ∈ D.paths, ∃ P₂ ∈ D.paths, ∃ P₃ ∈ D.paths, P₁ ≠ P₂ ∧ P₁ ≠ P₃ ∧ P₂ ≠ P₃ ∧
      (P₁.src = x₁ ∨ P₁.tgt = x₁) ∧ s(x₁, y₁) ∈ P₁.edges ∧
      (P₂.src = x₂ ∨ P₂.tgt = x₂) ∧ s(x₂, y₂) ∈ P₂.edges ∧
      (P₃.src = x₃ ∨ P₃.tgt = x₃) ∧ s(x₃, y₃) ∈ P₃.edges

/-- **Step 5: merging the three leaves.** A decomposition of the three-leaf graph with the end
counts produced by the two walks, in which no path contains `xᵢ` and `ℓᵢ` and no path contains
two leaves, gives `PTM3At`: merge `ℓ₂` into `x₂`, then `ℓ₃` into `x₃`, then `ℓ₁` into `x₁`. -/
theorem merge3 (G : SimpleGraph W) [DecidableRel G.Adj] (hodd : ∀ v, v ∉ evenSet G)
    {x₁ y₁ x₂ y₂ x₃ y₃ : W} (h₁ : G.Adj x₁ y₁) (h₂ : G.Adj x₂ y₂) (h₃ : G.Adj x₃ y₃)
    (hne : [x₁, y₁, x₂, y₂, x₃, y₃].Nodup) (D : PathDecomp (leaf3G G x₁ y₁ x₂ y₂ x₃ y₃))
    (hD : ∀ v, D.ends (some (some (some v))) + (if v = x₁ then 1 else 0) +
      (if v = x₂ then 1 else 0) = (G.degree v + if v = x₃ then 1 else 0) % 2)
    (hℓ₁ : D.ends (some (some none)) = 1) (hℓ₃ : D.ends (some none) = 1) (hℓ₂ : D.ends none = 1)
    (s₁ : Separates D (some (some (some x₁))) (some (some none)))
    (s₂ : Separates D (some (some (some x₂))) none)
    (s₃ : Separates D (some (some (some x₃))) (some none))
    (s₁₂ : Separates D (some (some none)) none) (s₃₂ : Separates D (some none) none)
    (s₁₃ : Separates D (some (some none)) (some none)) :
    PTM3At G x₁ y₁ x₂ y₂ x₃ y₃ := by
  obtain ⟨hx₁y₁, hx₁x₂, hx₁y₂, hx₁x₃, hx₁y₃, hy₁x₂, hy₁y₂, hy₁x₃, hy₁y₃, hx₂y₂, hx₂x₃, hx₂y₃,
    hy₂x₃, hy₂y₃, hx₃y₃⟩ := nodup6 hne
  have hdpos : ∀ v w, G.Adj v w → G.degree v % 2 = 1 := fun v w h => by
    have := hodd v
    rw [mem_evenSet_iff] at this
    have : 0 < G.degree v := (G.degree_pos_iff_exists_adj v).mpr ⟨w, h⟩
    omega
  have hA₁ : (leafG G x₁ y₁).Adj (some x₃) (some y₃) :=
    ⟨h₃, sym2_ne_of (Ne.symm hy₁x₃) (Ne.symm hx₁x₃)⟩
  have hA₂ : (leafG (leafG G x₁ y₁) (some x₃) (some y₃)).Adj (some (some x₂)) (some (some y₂)) := by
    refine ⟨⟨h₂, sym2_ne_of (Ne.symm hy₁x₂) (Ne.symm hx₁x₂)⟩, ?_⟩
    rw [sym2_some_eq_iff]; exact sym2_ne_of hx₂y₃ hx₂x₃
  -- merge `ℓ₂` into `x₂`
  obtain ⟨D₅, hD₅x, hD₅w, hback₅, hfwd₅⟩ :=
    leaf_merge (leafG (leafG G x₁ y₁) (some x₃) (some y₃)) hA₂ D s₂
  have t₃ : Separates D₅ (some (some x₃)) none :=
    merge_sep hback₅ (fun h => hx₂x₃ (Option.some_injective _ (Option.some_injective _ h)).symm)
      (by simp) s₃
  have t₁ : Separates D₅ (some (some x₁)) (some none) :=
    merge_sep hback₅ (fun h => hx₁x₂ (Option.some_injective _ (Option.some_injective _ h)))
      (by simp) s₁
  -- merge `ℓ₃` into `x₃`
  obtain ⟨D₆, hD₆x, hD₆w, hback₆, hfwd₆⟩ := leaf_merge (leafG G x₁ y₁) hA₁ D₅ t₃
  have u₁ : Separates D₆ (some x₁) none :=
    merge_sep hback₆ (fun h => hx₁x₃ (Option.some_injective _ h)) (by simp) t₁
  -- merge `ℓ₁` into `x₁`
  obtain ⟨D₇, hD₇x, hD₇w, -, hfwd₇⟩ := leaf_merge G h₁ D₆ u₁
  -- end counts
  have hD₇ : ∀ v, D₇.ends v = G.degree v % 2 := by
    intro v
    have e := hD v
    by_cases hv1 : v = x₁
    · rw [hv1] at e ⊢
      rw [ite_eq_left rfl, ite_eq_right hx₁x₂, ite_eq_right hx₁x₃] at e
      have k1 := hD₆w (some x₁) (fun h => hx₁x₃ (Option.some_injective _ h))
      have k2 := hD₆w none (by simp)
      have k3 := hD₅w (some (some x₁))
        (fun h => hx₁x₂ (Option.some_injective _ (Option.some_injective _ h)))
      have k4 := hD₅w (some none) (by simp)
      have := hdpos x₁ y₁ h₁
      rw [hD₇x]; omega
    · rw [hD₇w v hv1]
      by_cases hv3 : v = x₃
      · rw [hv3] at e ⊢
        rw [ite_eq_right (Ne.symm hx₁x₃), ite_eq_right (Ne.symm hx₂x₃), ite_eq_left rfl] at e
        have k1 := hD₅w (some (some x₃))
          (fun h => hx₂x₃ (Option.some_injective _ (Option.some_injective _ h)).symm)
        have k2 := hD₅w none (by simp)
        have := hdpos x₃ y₃ h₃
        rw [hD₆x]; omega
      · rw [hD₆w (some v) (fun h => hv3 (Option.some_injective _ h))]
        by_cases hv2 : v = x₂
        · rw [hv2] at e ⊢
          rw [ite_eq_right (Ne.symm hx₁x₂), ite_eq_left rfl, ite_eq_right hx₂x₃] at e
          have := hdpos x₂ y₂ h₂
          rw [hD₅x]; omega
        · rw [hD₅w (some (some v))
            (fun h => hv2 (Option.some_injective _ (Option.some_injective _ h)))]
          rw [ite_eq_right hv1, ite_eq_right hv2, ite_eq_right hv3] at e
          omega
  -- the three leaf paths of `D`
  obtain ⟨R₁, hR₁, hR₁e⟩ := D.exists_end_of_pos (by rw [hℓ₁]; omega)
  obtain ⟨R₂, hR₂, hR₂e⟩ := D.exists_end_of_pos (by rw [hℓ₂]; omega)
  obtain ⟨R₃, hR₃, hR₃e⟩ := D.exists_end_of_pos (by rw [hℓ₃]; omega)
  have n₁₂ : R₁ ≠ R₂ := fun h =>
    s₁₂ R₁ hR₁ ⟨mem_support_of_end hR₁e, by rw [h]; exact mem_support_of_end hR₂e⟩
  have n₁₃ : R₁ ≠ R₃ := fun h =>
    s₁₃ R₁ hR₁ ⟨mem_support_of_end hR₁e, by rw [h]; exact mem_support_of_end hR₃e⟩
  have n₂₃ : R₂ ≠ R₃ := fun h =>
    s₃₂ R₂ hR₂ ⟨by rw [h]; exact mem_support_of_end hR₃e, mem_support_of_end hR₂e⟩
  have f₂ : s(some (some (some y₂)), none) ∈ R₂.edges := leaf_edge_of_end hR₂e
  -- after the first merge
  obtain ⟨R₁', hR₁', hs₁', ht₁', he₁'⟩ := hfwd₅ R₁ hR₁
  obtain ⟨R₂', hR₂', hs₂', ht₂', he₂'⟩ := hfwd₅ R₂ hR₂
  obtain ⟨R₃', hR₃', hs₃', ht₃', he₃'⟩ := hfwd₅ R₃ hR₃
  have n₁₂' := merge_ne _ hA₂ hR₁ hR₂ n₁₂ he₁' he₂'
  have n₁₃' := merge_ne _ hA₂ hR₁ hR₃ n₁₃ he₁' he₃'
  have n₂₃' := merge_ne _ hA₂ hR₂ hR₃ n₂₃ he₂' he₃'
  have e₁' := merge_end hs₁' ht₁' hR₁e
  have e₂' := merge_end hs₂' ht₂' hR₂e
  have e₃' := merge_end hs₃' ht₃' hR₃e
  simp only [mergeMap_some, mergeMap_none] at e₁' e₂' e₃'
  have f₂' : s(some (some y₂), some (some x₂)) ∈ R₂'.edges := by
    rw [he₂']; exact merge_edge f₂
  have f₃' : s(some (some y₃), none) ∈ R₃'.edges := leaf_edge_of_end e₃'
  -- after the second merge
  obtain ⟨R₁'', hR₁'', hs₁'', ht₁'', he₁''⟩ := hfwd₆ R₁' hR₁'
  obtain ⟨R₂'', hR₂'', hs₂'', ht₂'', he₂''⟩ := hfwd₆ R₂' hR₂'
  obtain ⟨R₃'', hR₃'', hs₃'', ht₃'', he₃''⟩ := hfwd₆ R₃' hR₃'
  have n₁₂'' := merge_ne _ hA₁ hR₁' hR₂' n₁₂' he₁'' he₂''
  have n₁₃'' := merge_ne _ hA₁ hR₁' hR₃' n₁₃' he₁'' he₃''
  have n₂₃'' := merge_ne _ hA₁ hR₂' hR₃' n₂₃' he₂'' he₃''
  have e₁'' := merge_end hs₁'' ht₁'' e₁'
  have e₂'' := merge_end hs₂'' ht₂'' e₂'
  have e₃'' := merge_end hs₃'' ht₃'' e₃'
  simp only [mergeMap_some, mergeMap_none] at e₁'' e₂'' e₃''
  have f₂'' : s(some y₂, some x₂) ∈ R₂''.edges := by rw [he₂'']; exact merge_edge f₂'
  have f₃'' : s(some y₃, some x₃) ∈ R₃''.edges := by rw [he₃'']; exact merge_edge f₃'
  have f₁'' : s(some y₁, none) ∈ R₁''.edges := leaf_edge_of_end e₁''
  -- after the third merge
  obtain ⟨R₁''', hR₁''', hs₁''', ht₁''', he₁'''⟩ := hfwd₇ R₁'' hR₁''
  obtain ⟨R₂''', hR₂''', hs₂''', ht₂''', he₂'''⟩ := hfwd₇ R₂'' hR₂''
  obtain ⟨R₃''', hR₃''', hs₃''', ht₃''', he₃'''⟩ := hfwd₇ R₃'' hR₃''
  have n₁₂''' := merge_ne _ h₁ hR₁'' hR₂'' n₁₂'' he₁''' he₂'''
  have n₁₃''' := merge_ne _ h₁ hR₁'' hR₃'' n₁₃'' he₁''' he₃'''
  have n₂₃''' := merge_ne _ h₁ hR₂'' hR₃'' n₂₃'' he₂''' he₃'''
  have e₁''' := merge_end hs₁''' ht₁''' e₁''
  have e₂''' := merge_end hs₂''' ht₂''' e₂''
  have e₃''' := merge_end hs₃''' ht₃''' e₃''
  simp only [mergeMap_some, mergeMap_none] at e₁''' e₂''' e₃'''
  have f₁''' : s(y₁, x₁) ∈ R₁'''.edges := by rw [he₁''']; exact merge_edge f₁''
  have f₂''' : s(y₂, x₂) ∈ R₂'''.edges := by rw [he₂''']; exact merge_edge f₂''
  have f₃''' : s(y₃, x₃) ∈ R₃'''.edges := by rw [he₃''']; exact merge_edge f₃''
  rw [Sym2.eq_swap] at f₁''' f₂''' f₃'''
  exact ⟨D₇, hD₇, R₁''', hR₁''', R₂''', hR₂''', R₃''', hR₃''', n₁₂''', n₁₃''', n₂₃''', e₁''',
    f₁''', e₂''', f₂''', e₃''', f₃'''⟩

end merge3
/-! ### The chained walk theorem -/

section chained

variable {W : Type u} [Fintype W] [DecidableEq W]

omit [Fintype W] [DecidableEq W] in
/-- The second walk restores `P₁` in the two-leaf graph: `apex (M + E(P₂)) {y₃}` is
`L₂ − y₂x₂` minus the edges of `P₁`. -/
theorem half3_apex_edge (G : SimpleGraph W) (x₁ y₁ x₂ y₂ x₃ y₃ : W) (q₁ : List W) :
    ∀ e, e ∈ (apex (half3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁) {some y₃}).edgeSet ↔
      e ∈ (delEdge (leafG (leafG G x₁ y₁) (some x₃) (some y₃)) (some (some y₂))
        (some (some x₂))).edgeSet ∧ e ∉ chainEdges (((y₂ :: q₁).map some).map some) := by
  intro e
  rw [chainEdges_map]
  induction e using Sym2.inductionOn with
  | hf c d =>
    rw [mem_edgeSet, mem_edgeSet]
    cases c with
    | none =>
      cases d with
      | none =>
        exact ⟨fun h => absurd h apex_not_adj_none_none,
          fun h => absurd h.1.1 apex_not_adj_none_none⟩
      | some d =>
        show d ∈ ({some y₃} : Finset _) ↔ (d ∈ ({some y₃} : Finset _) ∧
          ¬ s(none, some d) = s(some (some y₂), some (some x₂))) ∧ _
        exact ⟨fun h => ⟨⟨h, sym2_none_ne⟩, none_not_mem_map_sym2 _ _⟩, fun h => h.1.1⟩
    | some c =>
      cases d with
      | none =>
        show c ∈ ({some y₃} : Finset _) ↔ (c ∈ ({some y₃} : Finset _) ∧
          ¬ s(some c, none) = s(some (some y₂), some (some x₂))) ∧ _
        refine ⟨fun h => ⟨⟨h, ?_⟩, ?_⟩, fun h => h.1.1⟩
        · rw [Sym2.eq_swap]; exact sym2_none_ne
        · rw [Sym2.eq_swap]; exact none_not_mem_map_sym2 _ _
      | some d =>
        rw [some_mem_map_sym2]
        show (half3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁).Adj c d ↔
          (((leafG G x₁ y₁).Adj c d ∧ ¬ s(c, d) = s(some y₃, some x₃)) ∧
            ¬ s(some c, some d) = s(some (some y₂), some (some x₂))) ∧ _
        rw [half3G, delChain_adj, sym2_some_eq_iff]
        show ((((leafG G x₁ y₁).Adj c d ∧ ¬ s(c, d) = s(some y₂, some x₂)) ∧
          ¬ s(c, d) = s(some y₃, some x₃)) ∧ _) ↔ _
        tauto

/-- **The chained walk theorem** (Theorem 8.2). Let `G` have no vertex of positive even degree,
`x₁y₁, x₂y₂, x₃y₃` a matching of `G` (six distinct vertices), and `P₂ = y₃ :: q₂`,
`P₁ = y₂ :: q₁` an admissible chain. If the base graph `M` has a Lovász decomposition in which no
path contains both vertices of any of the pairs `{x₁, ℓ₁}`, `{x₂, y₂}`, `{x₃, y₃}`, `{ℓ₁, y₂}`,
`{ℓ₁, y₃}`, `{y₂, y₃}` (`ℓ₁ = none`), then `G` has a Lovász decomposition in which `xᵢyᵢ` is
terminal at `xᵢ` for `i = 1, 2, 3`, on three different paths. -/
theorem ptm3_of_base (G : SimpleGraph W) [DecidableRel G.Adj] (hodd : ∀ v, v ∉ evenSet G)
    {x₁ y₁ x₂ y₂ x₃ y₃ : W} (h₁ : G.Adj x₁ y₁) (h₂ : G.Adj x₂ y₂) (h₃ : G.Adj x₃ y₃)
    (hne : [x₁, y₁, x₂, y₂, x₃, y₃].Nodup) {q₁ q₂ : List W}
    (hC : AdmChain G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂)
    (D₀ : PathDecomp (base3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂))
    (hD₀ : ∀ v, D₀.ends v = (base3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂).degree v % 2)
    (s₁ : Separates D₀ (some x₁) none) (s₂ : Separates D₀ (some x₂) (some y₂))
    (s₃ : Separates D₀ (some x₃) (some y₃)) (s₄ : Separates D₀ none (some y₂))
    (s₅ : Separates D₀ none (some y₃)) (s₆ : Separates D₀ (some y₂) (some y₃)) :
    PTM3At G x₁ y₁ x₂ y₂ x₃ y₃ := by
  obtain ⟨hx₁y₁, hx₁x₂, hx₁y₂, hx₁x₃, hx₁y₃, hy₁x₂, hy₁y₂, hy₁x₃, hy₁y₃, hx₂y₂, hx₂x₃, hx₂y₃,
    hy₂x₃, hy₂y₃, hx₃y₃⟩ := nodup6 hne
  have hdpos : ∀ v w, G.Adj v w → G.degree v % 2 = 1 := fun v w h => by
    have := hodd v
    rw [mem_evenSet_iff] at this
    have : 0 < G.degree v := (G.degree_pos_iff_exists_adj v).mpr ⟨w, h⟩
    omega
  obtain ⟨hMsome, hMnone⟩ := base3G_parity G h₁ h₂ h₃ hne hC
  have hD₀some : ∀ v, D₀.ends (some v) = (G.degree v + if v = x₃ then 1 else 0) % 2 := fun v => by
    rw [hD₀, hMsome]
  have hD₀none : D₀.ends none = 1 := by rw [hD₀, hMnone]
  -- Steps 1–2: a leaf `ℓ₃` at `y₃`, then walk back along `P₂`
  have hD₀y₃ : D₀.ends (some y₃) = 1 := by
    rw [hD₀some, ite_eq_right (Ne.symm hx₃y₃), add_zero]; exact hdpos y₃ x₃ h₃.symm
  obtain ⟨Q₃, hQ₃, hQ₃e⟩ := D₀.exists_end_of_pos (by rw [hD₀y₃]; omega)
  have hy₃Q₃ := mem_support_of_end hQ₃e
  have hZ₂ : ∀ t ∈ initOf (some y₃) (q₂.map some), ∀ v,
      (half3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁).Adj t v → v ≠ some y₃ → 1 ≤ D₀.ends v := by
    intro t ht v htv _
    rw [initOf_map, List.mem_map] at ht
    obtain ⟨t', ht', rfl⟩ := ht
    cases v with
    | none => rw [hD₀none]
    | some v =>
      rw [half3G, delChain_adj, mid3G_adj_some_some] at htv
      obtain ⟨⟨hG, -, -, hF₃⟩, -⟩ := htv
      have hvx₃ : v ≠ x₃ := by
        rintro rfl
        by_cases hty : t' = y₃
        · subst hty; exact hF₃ rfl
        · exact hC.nadj₂ t' ht' hty hG
      rw [hD₀some, ite_eq_right hvx₃, add_zero, hdpos v t' hG.symm]
  obtain ⟨D₂, hD₂e, hD₂n, hcov₂⟩ := leaf_walk (half3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁) (some y₃)
    (q₂.map some) (base3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂) D₀ (chain₂_half hC)
    (hC.nodup₂.map (Option.some_injective _)) (fun e => delChain_edgeSet _ _ e) hQ₃ hQ₃e hZ₂
  have hl₂ : chainLast (some y₃) (q₂.map some) = some x₂ := by rw [chainLast_map, hC.last₂]
  rw [hl₂] at hD₂e
  have hT₂ : ∀ c, some c ∈ initOf (some y₃) (q₂.map some) → c ∈ y₃ :: q₂ := by
    intro c h
    rw [initOf_map, some_mem_map_some] at h
    exact mem_initOf_mem _ _ h
  have hT₂x₂ : some x₂ ∉ initOf (some y₃) (q₂.map some) := by
    rw [initOf_map, some_mem_map_some, ← hC.last₂]
    exact chainLast_not_mem_initOf _ _ hC.nodup₂
  have hT₂n : (none : Option W) ∉ initOf (some y₃) (q₂.map some) := by
    rw [initOf_map]; exact none_not_mem_map_some _
  have t₁ : Separates D₂ (some (some x₁)) (some none) :=
    leaf_walk_sep_some hcov₂ (fun h => hC.x₁_notMem₂ (hT₂ _ h)) hT₂n s₁
  have t₂ : Separates D₂ (some (some x₂)) (some (some y₂)) :=
    leaf_walk_sep_some hcov₂ hT₂x₂ (fun h => hC.y₂_notMem₂ (hT₂ _ h)) s₂
  have t₃ : Separates D₂ (some (some x₃)) none :=
    leaf_walk_sep_none hcov₂ (fun h => hC.x₃_notMem₂ (hT₂ _ h)) (fun h => s₃ Q₃ hQ₃ ⟨h, hy₃Q₃⟩)
  have t₄ : Separates D₂ (some none) (some (some y₂)) :=
    leaf_walk_sep_some hcov₂ hT₂n (fun h => hC.y₂_notMem₂ (hT₂ _ h)) s₄
  have t₅ : Separates D₂ (some none) none :=
    leaf_walk_sep_none hcov₂ hT₂n (fun h => s₅ Q₃ hQ₃ ⟨h, hy₃Q₃⟩)
  have t₆ : Separates D₂ (some (some y₂)) none :=
    leaf_walk_sep_none hcov₂ (fun h => hC.y₂_notMem₂ (hT₂ _ h)) (fun h => s₆ Q₃ hQ₃ ⟨h, hy₃Q₃⟩)
  -- Steps 3–4: a leaf `ℓ₂` at `y₂`, then walk back along `P₁`
  have hD₂y₂ : D₂.ends (some (some y₂)) = 1 := by
    have := hD₂e (some y₂)
    rw [ite_eq_right (fun h => hx₂y₂ (Option.some_injective _ h).symm), add_zero, hD₀some,
      ite_eq_right hy₂x₃, add_zero, hdpos y₂ x₂ h₂.symm] at this
    exact this
  obtain ⟨Q₂, hQ₂, hQ₂e⟩ := D₂.exists_end_of_pos (by rw [hD₂y₂]; omega)
  have hy₂Q₂ := mem_support_of_end hQ₂e
  have hch₄ : ChainAdj (delEdge (leafG (leafG G x₁ y₁) (some x₃) (some y₃)) (some (some y₂))
      (some (some x₂))) (((y₂ :: q₁).map some).map some) := by
    refine chainAdj_map some (fun a b h => ?_) _ (chain₁_mid hC)
    obtain ⟨⟨hL, hF₂⟩, hF₃⟩ := h
    exact ⟨⟨hL, hF₃⟩, by rw [sym2_some_eq_iff]; exact hF₂⟩
  have hZ₄ : ∀ t ∈ initOf (some (some y₂)) ((q₁.map some).map some), ∀ v,
      (delEdge (leafG (leafG G x₁ y₁) (some x₃) (some y₃)) (some (some y₂))
        (some (some x₂))).Adj t v → v ≠ some (some y₂) → 1 ≤ D₂.ends v := by
    intro t ht v htv _
    rw [initOf_map, initOf_map, List.mem_map] at ht
    obtain ⟨t₁, ht₁, rfl⟩ := ht
    rw [List.mem_map] at ht₁
    obtain ⟨t', ht', rfl⟩ := ht₁
    rcases v with _ | _ | v
    · rw [hD₂n]
    · have := hD₂e none
      rw [ite_eq_right (by simp), add_zero, hD₀none] at this
      rw [this]
    · obtain ⟨⟨⟨hG, -⟩, -⟩, hF₂⟩ := htv
      have hF₂' : s(t', v) ≠ s(y₂, x₂) := fun h =>
        hF₂ (by rw [sym2_some_eq_iff, sym2_some_eq_iff]; exact h)
      have hvx₂ : v ≠ x₂ := by
        rintro rfl
        by_cases hty : t' = y₂
        · subst hty; exact hF₂' rfl
        · exact hC.nadj₁ t' ht' hty hG
      have hvx₃ : v ≠ x₃ := by rintro rfl; exact hC.nadj₁' t' ht' hG
      have := hD₂e (some v)
      rw [ite_eq_right (fun h => hvx₂ (Option.some_injective _ h)), add_zero, hD₀some,
        ite_eq_right hvx₃, add_zero, hdpos v t' hG.symm] at this
      rw [this]
  obtain ⟨D₄, hD₄e, hD₄n, hcov₄⟩ := leaf_walk
    (delEdge (leafG (leafG G x₁ y₁) (some x₃) (some y₃)) (some (some y₂)) (some (some x₂)))
    (some (some y₂)) ((q₁.map some).map some) (apex (half3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁) {some y₃}) D₂
    hch₄ ((hC.nodup₁.map (Option.some_injective _)).map (Option.some_injective _))
    (half3_apex_edge G x₁ y₁ x₂ y₂ x₃ y₃ q₁) hQ₂ hQ₂e hZ₄
  have hl₁ : chainLast (some (some y₂)) ((q₁.map some).map some) = some (some x₁) := by
    rw [chainLast_map, chainLast_map, hC.last₁]
  rw [hl₁] at hD₄e
  have hT₁ : ∀ c, some (some c) ∈ initOf (some (some y₂)) ((q₁.map some).map some) →
      c ∈ y₂ :: q₁ := by
    intro c h
    rw [initOf_map, initOf_map, some_mem_map_some, some_mem_map_some] at h
    exact mem_initOf_mem _ _ h
  have hT₁x₁ : some (some x₁) ∉ initOf (some (some y₂)) ((q₁.map some).map some) := by
    rw [initOf_map, initOf_map, some_mem_map_some, some_mem_map_some, ← hC.last₁]
    exact chainLast_not_mem_initOf _ _ hC.nodup₁
  have hT₁n : (none : Option (Option W)) ∉ initOf (some (some y₂)) ((q₁.map some).map some) := by
    rw [initOf_map]; exact none_not_mem_map_some _
  have hT₁sn : (some none : Option (Option W)) ∉
      initOf (some (some y₂)) ((q₁.map some).map some) := by
    rw [initOf_map, initOf_map, some_mem_map_some]; exact none_not_mem_map_some _
  have r₁ : Separates D₄ (some (some (some x₁))) (some (some none)) :=
    leaf_walk_sep_some hcov₄ hT₁x₁ hT₁sn t₁
  have r₂ : Separates D₄ (some (some (some x₂))) none :=
    leaf_walk_sep_none hcov₄ (fun h => hC.x₂_notMem₁ (hT₁ _ h)) (fun h => t₂ Q₂ hQ₂ ⟨h, hy₂Q₂⟩)
  have r₃ : Separates D₄ (some (some (some x₃))) (some none) :=
    leaf_walk_sep_some hcov₄ (fun h => hC.x₃_notMem₁ (hT₁ _ h)) hT₁n t₃
  have r₁₂ : Separates D₄ (some (some none)) none :=
    leaf_walk_sep_none hcov₄ hT₁sn (fun h => t₄ Q₂ hQ₂ ⟨h, hy₂Q₂⟩)
  have r₃₂ : Separates D₄ (some none) none :=
    leaf_walk_sep_none hcov₄ hT₁n (fun h => t₆ Q₂ hQ₂ ⟨hy₂Q₂, h⟩)
  have r₁₃ : Separates D₄ (some (some none)) (some none) :=
    leaf_walk_sep_some hcov₄ hT₁sn hT₁n t₅
  -- end counts of `D₄`
  have hD₄ : ∀ v, D₄.ends (some (some (some v))) + (if v = x₁ then 1 else 0) +
      (if v = x₂ then 1 else 0) = (G.degree v + if v = x₃ then 1 else 0) % 2 := by
    intro v
    have e₁ := hD₄e (some (some v))
    have e₂ := hD₂e (some v)
    have e₃ := hD₀some v
    simp only [Option.some.injEq] at e₁ e₂
    omega
  have hℓ₁ : D₄.ends (some (some none)) = 1 := by
    have e₁ := hD₄e (some none)
    have e₂ := hD₂e none
    simp only [Option.some.injEq, reduceCtorEq, ite_false, add_zero] at e₁ e₂
    rw [e₁, e₂, hD₀none]
  have hℓ₃ : D₄.ends (some none) = 1 := by
    have e₁ := hD₄e none
    simp only [reduceCtorEq, ite_false, add_zero] at e₁
    rw [e₁, hD₂n]
  -- Step 5
  exact merge3 G hodd h₁ h₂ h₃ hne D₄ hD₄ hℓ₁ hℓ₃ hD₄n r₁ r₂ r₃ r₁₂ r₃₂ r₁₃

end chained
/-! ### Far-apart ends -/

section far

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- `e` is one of the three edges of the matching `F`. -/
def InF3 (x₁ y₁ x₂ y₂ x₃ y₃ : W) (e : Sym2 W) : Prop :=
  e = s(x₁, y₁) ∨ e = s(x₂, y₂) ∨ e = s(x₃, y₃)

/-- **Far-apart ends**: the six ends of `F = {x₁y₁, x₂y₂, x₃y₃}` are pairwise at distance at least
three in `G − F`. No edge of `G − F` joins two of them, and no vertex is joined to two of them by
edges of `G − F`. -/
structure FarEnds (G : SimpleGraph W) (x₁ y₁ x₂ y₂ x₃ y₃ : W) : Prop where
  adj : ∀ u ∈ [x₁, y₁, x₂, y₂, x₃, y₃], ∀ v ∈ [x₁, y₁, x₂, y₂, x₃, y₃], G.Adj u v →
    InF3 x₁ y₁ x₂ y₂ x₃ y₃ s(u, v)
  common : ∀ u ∈ [x₁, y₁, x₂, y₂, x₃, y₃], ∀ v ∈ [x₁, y₁, x₂, y₂, x₃, y₃], u ≠ v → ∀ w,
    G.Adj w u → G.Adj w v → InF3 x₁ y₁ x₂ y₂ x₃ y₃ s(w, u) ∨ InF3 x₁ y₁ x₂ y₂ x₃ y₃ s(w, v)

/-- The six special vertices of the base graph: `X = {x₁, x₂, x₃, y₂, y₃, ℓ₁}`. -/
abbrev base3X (x₁ x₂ y₂ x₃ y₃ : W) : Finset (Option W) :=
  {some x₁, some x₂, some x₃, some y₂, some y₃, none}

/-- The four sets to be met at most once per path: `{x₁, ℓ₁}`, `{x₂, y₂}`, `{x₃, y₃}`,
`{ℓ₁, y₂, y₃}`. -/
abbrev base3Fam (x₁ x₂ y₂ x₃ y₃ : W) : Finset (Finset (Option W)) :=
  {{some x₁, none}, {some x₂, some y₂}, {some x₃, some y₃}, {none, some y₂, some y₃}}

omit [Fintype W] [DecidableEq W] in
/-- A family of subsets of `X` is sparse and packed as soon as no two vertices of `X` are adjacent
and every vertex has at most one neighbour in `X`. -/
theorem sparseFam_of_one {U : Type*} {M : SimpleGraph U} {X : Finset U} {𝒜 : Finset (Finset U)}
    (hsub : ∀ A ∈ 𝒜, A ⊆ X) (hnadj : ∀ p ∈ X, ∀ q ∈ X, ¬ M.Adj p q)
    (hone : ∀ v p q, M.Adj v p → M.Adj v q → p ∈ X → q ∈ X → p = q) : SparseFam M X 𝒜 :=
  ⟨fun A hA x hx y hy hxy => ⟨hnadj x (hsub A hA hx) y (hsub A hA hy), fun w ⟨h1, h2⟩ =>
    hxy (hone w x y h1.symm h2 (hsub A hA hx) (hsub A hA hy))⟩, hsub, hone⟩

omit [Fintype W] [DecidableEq W] in
theorem separates_of_meetsOnce_mem {K : SimpleGraph W} {D : PathDecomp K} {A : Finset W}
    (h : MeetsOnce D A) {c d : W} (hc : c ∈ A) (hd : d ∈ A) (hcd : c ≠ d) : Separates D c d :=
  fun P hP ⟨h1, h2⟩ => hcd (h P hP c hc d hd h1 h2)

/-- **The base hypothesis for far-apart ends** (Proposition 8.3, first part). If the six ends are
pairwise far apart in `G − F`, then for every admissible chain the base graph `M` has a Lovász
decomposition separating the six pairs of `ptm3_of_base` (by `separation_sparse`, with
`X = {x₁, x₂, x₃, y₂, y₃, ℓ₁}` and the sets `{x₁, ℓ₁}`, `{x₂, y₂}`, `{x₃, y₃}`, `{ℓ₁, y₂, y₃}`). -/
theorem base3_of_far (G : SimpleGraph W) [DecidableRel G.Adj] (hodd : ∀ v, v ∉ evenSet G)
    {x₁ y₁ x₂ y₂ x₃ y₃ : W} (h₁ : G.Adj x₁ y₁) (h₂ : G.Adj x₂ y₂) (h₃ : G.Adj x₃ y₃)
    (hne : [x₁, y₁, x₂, y₂, x₃, y₃].Nodup) (hfar : FarEnds G x₁ y₁ x₂ y₂ x₃ y₃)
    {q₁ q₂ : List W} (hC : AdmChain G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂) :
    ∃ D₀ : PathDecomp (base3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂),
      (∀ v, D₀.ends v = (base3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂).degree v % 2) ∧
      Separates D₀ (some x₁) none ∧ Separates D₀ (some x₂) (some y₂) ∧
      Separates D₀ (some x₃) (some y₃) ∧ Separates D₀ none (some y₂) ∧
      Separates D₀ none (some y₃) ∧ Separates D₀ (some y₂) (some y₃) := by
  obtain ⟨hx₁y₁, hx₁x₂, hx₁y₂, hx₁x₃, hx₁y₃, hy₁x₂, hy₁y₂, hy₁x₃, hy₁y₃, hx₂y₂, hx₂x₃, hx₂y₃,
    hy₂x₃, hy₂y₃, hx₃y₃⟩ := nodup6 hne
  have hdpos : ∀ v w, G.Adj v w → G.degree v % 2 = 1 := fun v w h => by
    have := hodd v
    rw [mem_evenSet_iff] at this
    have : 0 < G.degree v := (G.degree_pos_iff_exists_adj v).mpr ⟨w, h⟩
    omega
  obtain ⟨hMsome, hMnone⟩ := base3G_parity G h₁ h₂ h₃ hne hC
  -- adjacency in `M` is adjacency in `G − F`, plus the leaf edge `ℓ₁y₁`
  have hMn := base3G_adj_none G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂
  have hMss : ∀ a b, (base3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂).Adj (some a) (some b) →
      G.Adj a b ∧ ¬ InF3 x₁ y₁ x₂ y₂ x₃ y₃ s(a, b) := by
    intro a b h
    rw [base3G_adj_some_some] at h
    obtain ⟨hG, hF₁, hF₂, hF₃, -, -⟩ := h
    refine ⟨hG, ?_⟩
    rintro (h | h | h)
    · exact hF₁ (h.trans Sym2.eq_swap)
    · exact hF₂ (h.trans Sym2.eq_swap)
    · exact hF₃ (h.trans Sym2.eq_swap)
  have memX : ∀ p ∈ base3X x₁ x₂ y₂ x₃ y₃, p = none ∨
      ∃ p', p = some p' ∧ p' ∈ [x₁, y₁, x₂, y₂, x₃, y₃] ∧ p' ≠ y₁ := by
    intro p hp
    simp only [base3X, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨x₁, rfl, by simp, hx₁y₁⟩
    · exact Or.inr ⟨x₂, rfl, by simp, Ne.symm hy₁x₂⟩
    · exact Or.inr ⟨x₃, rfl, by simp, Ne.symm hy₁x₃⟩
    · exact Or.inr ⟨y₂, rfl, by simp, Ne.symm hy₁y₂⟩
    · exact Or.inr ⟨y₃, rfl, by simp, Ne.symm hy₁y₃⟩
    · exact Or.inl rfl
  have hy₁6 : y₁ ∈ [x₁, y₁, x₂, y₂, x₃, y₃] := by simp
  have hone : ∀ v p q, (base3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂).Adj v p →
      (base3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂).Adj v q →
      p ∈ base3X x₁ x₂ y₂ x₃ y₃ → q ∈ base3X x₁ x₂ y₂ x₃ y₃ → p = q := by
    intro v p q hp hq hpX hqX
    cases v with
    | none => rw [(hMn p).mp hp, (hMn q).mp hq]
    | some w =>
      rcases memX p hpX with rfl | ⟨p', rfl, hp'6, -⟩ <;>
        rcases memX q hqX with rfl | ⟨q', rfl, hq'6, -⟩
      · rfl
      · obtain rfl := Option.some_injective _ ((hMn _).mp hp.symm)
        obtain ⟨hG, hnF⟩ := hMss _ _ hq
        exact absurd (hfar.adj w hy₁6 q' hq'6 hG) hnF
      · obtain rfl := Option.some_injective _ ((hMn _).mp hq.symm)
        obtain ⟨hG, hnF⟩ := hMss _ _ hp
        exact absurd (hfar.adj w hy₁6 p' hp'6 hG) hnF
      · by_cases hpq : p' = q'
        · rw [hpq]
        · obtain ⟨hG₁, hnF₁⟩ := hMss _ _ hp
          obtain ⟨hG₂, hnF₂⟩ := hMss _ _ hq
          rcases hfar.common p' hp'6 q' hq'6 hpq w hG₁ hG₂ with h | h
          · exact absurd h hnF₁
          · exact absurd h hnF₂
  have hnadj : ∀ p ∈ base3X x₁ x₂ y₂ x₃ y₃, ∀ q ∈ base3X x₁ x₂ y₂ x₃ y₃,
      ¬ (base3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂).Adj p q := by
    intro p hpX q hqX hpq
    rcases memX p hpX with rfl | ⟨p', rfl, hp'6, hp'y⟩
    · rw [hMn] at hpq
      subst hpq
      rcases memX _ hqX with h | ⟨q', h, -, hq'y⟩
      · exact Option.some_ne_none _ h
      · exact hq'y (Option.some_injective _ h).symm
    · rcases memX q hqX with rfl | ⟨q', rfl, hq'6, -⟩
      · exact hp'y (Option.some_injective _ ((hMn _).mp hpq.symm))
      · obtain ⟨hG, hnF⟩ := hMss _ _ hpq
        exact hnF (hfar.adj p' hp'6 q' hq'6 hG)
  have hsub : ∀ A ∈ base3Fam x₁ x₂ y₂ x₃ y₃, A ⊆ base3X x₁ x₂ y₂ x₃ y₃ := by
    intro A hA
    simp only [base3Fam, Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl | rfl <;> intro z hz <;>
      simp only [base3X, Finset.mem_insert, Finset.mem_singleton] at hz ⊢ <;> tauto
  have hSF := sparseFam_of_one hsub hnadj hone
  -- at most one even vertex
  have hev : ∀ w ∈ evenSet (base3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂), w = some x₃ := by
    intro w hw
    rw [mem_evenSet_iff] at hw
    cases w with
    | none => rw [hMnone] at hw; omega
    | some v =>
      by_cases hvx : v = x₃
      · rw [hvx]
      · exfalso
        obtain ⟨z, hz⟩ := ((base3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂).degree_pos_iff_exists_adj
          (some v)).mp hw.1
        have hGv : G.degree v % 2 = 1 := by
          cases z with
          | none =>
            rw [Option.some_injective _ ((hMn _).mp hz.symm)]
            exact hdpos y₁ x₁ h₁.symm
          | some z => exact hdpos v z (hMss _ _ hz).1
        have := hMsome v
        rw [ite_eq_right hvx, add_zero, hGv] at this
        omega
  have hcard : (evenSet (base3G G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂)).card ≤ 1 :=
    Finset.card_le_one.mpr fun w₁ h₁ w₂ h₂ => (hev w₁ h₁).trans (hev w₂ h₂).symm
  obtain ⟨D₀, hD₀, hmeet⟩ := separation_sparse _ hcard hSF
  have m₁ := hmeet {some x₁, none} (by simp [base3Fam])
  have m₂ := hmeet {some x₂, some y₂} (by simp [base3Fam])
  have m₃ := hmeet {some x₃, some y₃} (by simp [base3Fam])
  have m₄ := hmeet {none, some y₂, some y₃} (by simp [base3Fam])
  refine ⟨D₀, hD₀, separates_of_meetsOnce_mem m₁ (by simp) (by simp) (by simp),
    separates_of_meetsOnce_mem m₂ (by simp) (by simp) (by simpa using hx₂y₂),
    separates_of_meetsOnce_mem m₃ (by simp) (by simp) (by simpa using hx₃y₃),
    separates_of_meetsOnce_mem m₄ (by simp) (by simp) (by simp),
    separates_of_meetsOnce_mem m₄ (by simp) (by simp) (by simp),
    separates_of_meetsOnce_mem m₄ (by simp) (by simp) (by simpa using hy₂y₃)⟩

/-- **Far-apart form** (Proposition 8.3). Let `G` have no vertex of positive even degree, and
`x₁y₁, x₂y₂, x₃y₃` a matching of `G` whose six ends are pairwise at distance at least three in
`G − F`. For every admissible chain, `G` has a Lovász decomposition in which `xᵢyᵢ` is terminal
at `xᵢ` for `i = 1, 2, 3`, on three different paths. -/
theorem ptm3_of_far (G : SimpleGraph W) [DecidableRel G.Adj] (hodd : ∀ v, v ∉ evenSet G)
    {x₁ y₁ x₂ y₂ x₃ y₃ : W} (h₁ : G.Adj x₁ y₁) (h₂ : G.Adj x₂ y₂) (h₃ : G.Adj x₃ y₃)
    (hne : [x₁, y₁, x₂, y₂, x₃, y₃].Nodup) (hfar : FarEnds G x₁ y₁ x₂ y₂ x₃ y₃)
    {q₁ q₂ : List W} (hC : AdmChain G x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂) :
    PTM3At G x₁ y₁ x₂ y₂ x₃ y₃ := by
  obtain ⟨D₀, hD₀, s₁, s₂, s₃, s₄, s₅, s₆⟩ := base3_of_far G hodd h₁ h₂ h₃ hne hfar hC
  exact ptm3_of_base G hodd h₁ h₂ h₃ hne hC D₀ hD₀ s₁ s₂ s₃ s₄ s₅ s₆

end far
/-! ### Degree six: from three terminal edges to STL and Test 1 -/

section degreeSix

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The lifted graph `(J − z) + x₁y₁ + x₂y₂ + x₃y₃`, as three transitions lifted at `z`. -/
abbrev lift3 (J : SimpleGraph V) (z x₁ y₁ x₂ y₂ x₃ y₃ : V) : SimpleGraph V :=
  swapG (liftJ J z x₁ y₁ x₂ y₂) z x₃ y₃

omit [Fintype V] [DecidableEq V] in
theorem sym2_ne_of_ne_ne {u v z c : V} (hu : u ≠ z) (hv : v ≠ z) : s(u, v) ≠ s(z, c) := by
  intro h
  have : z ∈ s(u, v) := h ▸ Sym2.mem_mk_left z c
  rcases Sym2.mem_iff.mp this with h | h
  · exact hu h.symm
  · exact hv h.symm

omit [Fintype V] in
/-- Away from `z`, lifting the transition `c z d` only adds the edge `cd`. -/
theorem swapG_adj_off (K : SimpleGraph V) {z c d u v : V} (hcd : c ≠ d) (hu : u ≠ z)
    (hv : v ≠ z) : (swapG K z c d).Adj u v ↔ K.Adj u v ∨ s(u, v) = s(c, d) := by
  rw [swapG_adj]
  constructor
  · rintro ⟨-, ⟨h, -⟩ | h⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨h.ne, Or.inl ⟨h, sym2_ne_of_ne_ne hu hv, sym2_ne_of_ne_ne hu hv⟩⟩
    · refine ⟨fun huv => ?_, Or.inr h⟩
      subst huv
      rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hcd rfl

/-- Facts about the intermediate graphs of the triple lift. -/
theorem lift3_mid (J : SimpleGraph V) {z x₁ y₁ x₂ y₂ x₃ y₃ : V}
    (hN : ∀ w, J.Adj z w ↔ w = x₁ ∨ w = y₁ ∨ w = x₂ ∨ w = y₂ ∨ w = x₃ ∨ w = y₃)
    (hne : [x₁, y₁, x₂, y₂, x₃, y₃].Nodup) (hp₂ : ¬ J.Adj x₂ y₂) (hp₃ : ¬ J.Adj x₃ y₃) :
    (swapG J z x₁ y₁).Adj z x₂ ∧ (swapG J z x₁ y₁).Adj z y₂ ∧ ¬ (swapG J z x₁ y₁).Adj x₂ y₂ ∧
      (liftJ J z x₁ y₁ x₂ y₂).Adj z x₃ ∧ (liftJ J z x₁ y₁ x₂ y₂).Adj z y₃ ∧
      ¬ (liftJ J z x₁ y₁ x₂ y₂).Adj x₃ y₃ := by
  obtain ⟨hx₁y₁, hx₁x₂, hx₁y₂, hx₁x₃, hx₁y₃, hy₁x₂, hy₁y₂, hy₁x₃, hy₁y₃, hx₂y₂, hx₂x₃, hx₂y₃,
    hy₂x₃, hy₂y₃, hx₃y₃⟩ := nodup6 hne
  have hzx₁ := (hN x₁).2 (Or.inl rfl)
  have hzy₁ := (hN y₁).2 (Or.inr (Or.inl rfl))
  have hzx₂ := (hN x₂).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hzy₂ := (hN y₂).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hzx₃ := (hN x₃).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hzy₃ := (hN y₃).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  obtain ⟨k₂x, k₂y, k₂n⟩ := liftJ_mid J hzx₁ hzy₁ hzx₂ hzy₂ hx₁x₂ hx₁y₂ hy₁x₂ hy₁y₂ hp₂
  obtain ⟨k₃x, k₃y, k₃n⟩ := liftJ_mid J hzx₁ hzy₁ hzx₃ hzy₃ hx₁x₃ hx₁y₃ hy₁x₃ hy₁y₃ hp₃
  obtain ⟨m₃x, m₃y, m₃n⟩ := liftJ_mid (swapG J z x₁ y₁) k₂x k₂y k₃x k₃y hx₂x₃ hx₂y₃ hy₂x₃ hy₂y₃ k₃n
  exact ⟨k₂x, k₂y, k₂n, m₃x, m₃y, m₃n⟩

theorem lift3_degree (J : SimpleGraph V) [DecidableRel J.Adj] {z x₁ y₁ x₂ y₂ x₃ y₃ : V}
    (hN : ∀ w, J.Adj z w ↔ w = x₁ ∨ w = y₁ ∨ w = x₂ ∨ w = y₂ ∨ w = x₃ ∨ w = y₃)
    (hne : [x₁, y₁, x₂, y₂, x₃, y₃].Nodup)
    (hp₁ : ¬ J.Adj x₁ y₁) (hp₂ : ¬ J.Adj x₂ y₂) (hp₃ : ¬ J.Adj x₃ y₃) (v : V) :
    (lift3 J z x₁ y₁ x₂ y₂ x₃ y₃).degree v + (if v = z then 6 else 0) = J.degree v := by
  obtain ⟨hx₁y₁, hx₁x₂, hx₁y₂, hx₁x₃, hx₁y₃, hy₁x₂, hy₁y₂, hy₁x₃, hy₁y₃, hx₂y₂, hx₂x₃, hx₂y₃,
    hy₂x₃, hy₂y₃, hx₃y₃⟩ := nodup6 hne
  have hzx₁ := (hN x₁).2 (Or.inl rfl)
  have hzy₁ := (hN y₁).2 (Or.inr (Or.inl rfl))
  have hzx₂ := (hN x₂).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hzy₂ := (hN y₂).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  obtain ⟨-, -, -, m₃x, m₃y, m₃n⟩ := lift3_mid J hN hne hp₂ hp₃
  have h1 := liftJ_degree J hzx₁ hzy₁ hzx₂ hzy₂ hx₁y₁ hx₁x₂ hx₁y₂ hy₁x₂ hy₁y₂ hx₂y₂ hp₁ hp₂ v
  have h2 := swapG_degree (liftJ J z x₁ y₁ x₂ y₂) m₃x m₃y m₃n hx₃y₃ v
  show (swapG (liftJ J z x₁ y₁ x₂ y₂) z x₃ y₃).degree v + _ = _
  split_ifs at h1 h2 ⊢ <;> omega

theorem degree_eq_six (J : SimpleGraph V) [DecidableRel J.Adj] {z x₁ y₁ x₂ y₂ x₃ y₃ : V}
    (hN : ∀ w, J.Adj z w ↔ w = x₁ ∨ w = y₁ ∨ w = x₂ ∨ w = y₂ ∨ w = x₃ ∨ w = y₃)
    (hne : [x₁, y₁, x₂, y₂, x₃, y₃].Nodup) : J.degree z = 6 := by
  have hset : J.neighborFinset z = [x₁, y₁, x₂, y₂, x₃, y₃].toFinset := by
    ext w; simp only [mem_neighborFinset, List.mem_toFinset, List.mem_cons, List.not_mem_nil,
      or_false, hN]
  rw [← card_neighborFinset_eq_degree, hset, List.toFinset_card_of_nodup hne]
  rfl

omit [Fintype V] in
/-- Adjacency in the lifted graph, away from `z`: `J` plus the three pairs. -/
theorem lift3_adj (J : SimpleGraph V) {z x₁ y₁ x₂ y₂ x₃ y₃ u v : V}
    (hne : [x₁, y₁, x₂, y₂, x₃, y₃].Nodup) (hu : u ≠ z) (hv : v ≠ z) :
    (lift3 J z x₁ y₁ x₂ y₂ x₃ y₃).Adj u v ↔
      J.Adj u v ∨ s(u, v) = s(x₁, y₁) ∨ s(u, v) = s(x₂, y₂) ∨ s(u, v) = s(x₃, y₃) := by
  obtain ⟨hx₁y₁, -, -, -, -, -, -, -, -, hx₂y₂, -, -, -, -, hx₃y₃⟩ := nodup6 hne
  rw [lift3, swapG_adj_off _ hx₃y₃ hu hv, liftJ, swapG_adj_off _ hx₂y₂ hu hv,
    swapG_adj_off _ hx₁y₁ hu hv]
  tauto

/-- **From `PTM3At` to STL** (un-lifting three times). Let `N(z) = {x₁, y₁, x₂, y₂, x₃, y₃}`
(six distinct vertices) with `xᵢyᵢ ∉ E(J)`. A Lovász decomposition of
`(J − z) + x₁y₁ + x₂y₂ + x₃y₃` with `xᵢyᵢ` terminal at `xᵢ` on three different paths lifts to a
star-terminal Lovász decomposition of `J` in which every `yᵢ` is on a long side (or some path
through `z` has length two): `STL J z yᵢ` for `i = 1, 2, 3`. -/
theorem stl_of_ptm3 (J : SimpleGraph V) [DecidableRel J.Adj] {z x₁ y₁ x₂ y₂ x₃ y₃ : V}
    (hN : ∀ w, J.Adj z w ↔ w = x₁ ∨ w = y₁ ∨ w = x₂ ∨ w = y₂ ∨ w = x₃ ∨ w = y₃)
    (hne : [x₁, y₁, x₂, y₂, x₃, y₃].Nodup)
    (hp₁ : ¬ J.Adj x₁ y₁) (hp₂ : ¬ J.Adj x₂ y₂) (hp₃ : ¬ J.Adj x₃ y₃)
    (h : PTM3At (lift3 J z x₁ y₁ x₂ y₂ x₃ y₃) x₁ y₁ x₂ y₂ x₃ y₃) :
    STL J z y₁ ∧ STL J z y₂ ∧ STL J z y₃ := by
  obtain ⟨hx₁y₁, -, -, -, -, -, -, -, -, hx₂y₂, -, -, -, -, hx₃y₃⟩ := nodup6 hne
  have hzx₁ := (hN x₁).2 (Or.inl rfl)
  have hzy₁ := (hN y₁).2 (Or.inr (Or.inl rfl))
  obtain ⟨k₂x, k₂y, k₂n, m₃x, m₃y, m₃n⟩ := lift3_mid J hN hne hp₂ hp₃
  have hdeg := lift3_degree J hN hne hp₁ hp₂ hp₃
  have hJz := degree_eq_six J hN hne
  have hiso : ∀ w, ¬ (lift3 J z x₁ y₁ x₂ y₂ x₃ y₃).Adj z w := by
    intro w hw
    have h0 := hdeg z
    rw [ite_eq_left rfl, hJz] at h0
    have : (lift3 J z x₁ y₁ x₂ y₂ x₃ y₃).degree z = 0 := by omega
    rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero] at this
    have : w ∈ (lift3 J z x₁ y₁ x₂ y₂ x₃ y₃).neighborFinset z := (mem_neighborFinset _ _ _).2 hw
    simp_all
  have hzP : ∀ P : GPath (lift3 J z x₁ y₁ x₂ y₂ x₃ y₃), z ∉ P.walk.support := fun P =>
    P.not_mem_of_isolated hiso
  have hpar : ∀ v, (lift3 J z x₁ y₁ x₂ y₂ x₃ y₃).degree v % 2 = J.degree v % 2 := by
    intro v; have := hdeg v; split_ifs at this <;> omega
  obtain ⟨D, hD, P₁, hP₁, P₂, hP₂, P₃, hP₃, n₁₂, n₁₃, n₂₃, e₁, f₁, e₂, f₂, e₃, f₃⟩ := h
  -- un-lift `x₃y₃`
  obtain ⟨D₁, hD₁, P₃', hP₃', s₃, cz₃, zd₃, t₃, hz₃, pres₁, back₁⟩ :=
    unlift (liftJ J z x₁ y₁ x₂ y₂) m₃x m₃y m₃n hx₃y₃ D hP₃ e₃ f₃ (hzP P₃)
  obtain ⟨P₁b, hP₁b, s₁b, t₁b, supp₁b, edges₁b⟩ := pres₁ P₁ hP₁ n₁₃
  obtain ⟨P₂b, hP₂b, s₂b, t₂b, supp₂b, edges₂b⟩ := pres₁ P₂ hP₂ n₂₃
  have n₁₂b : P₁b ≠ P₂b := fun h' =>
    n₁₂ (D.eq_of_mem_edges hP₁ hP₂ f₁ (by rw [← edges₂b, ← h', edges₁b]; exact f₁))
  -- un-lift `x₂y₂`
  have z₂b : z ∉ P₂b.walk.support := by rw [supp₂b]; exact hzP P₂
  obtain ⟨D₂, hD₂, P₂', hP₂', s₂, cz₂, zd₂, t₂, hz₂, pres₂, back₂⟩ :=
    unlift (swapG J z x₁ y₁) k₂x k₂y k₂n hx₂y₂ D₁ hP₂b (by rw [s₂b, t₂b]; exact e₂)
      (by rw [edges₂b]; exact f₂) z₂b
  obtain ⟨P₁c, hP₁c, s₁c, t₁c, supp₁c, edges₁c⟩ := pres₂ P₁b hP₁b n₁₂b
  have n₃b : P₃' ≠ P₂b := fun h' => z₂b (h' ▸ hz₃)
  obtain ⟨P₃c, hP₃c, s₃c, t₃c, supp₃c, edges₃c⟩ := pres₂ P₃' hP₃' n₃b
  -- un-lift `x₁y₁`
  have z₁c : z ∉ P₁c.walk.support := by rw [supp₁c, supp₁b]; exact hzP P₁
  obtain ⟨D₃, hD₃, P₁', hP₁', s₁, cz₁, zd₁, t₁, -, pres₃, back₃⟩ :=
    unlift J hzx₁ hzy₁ hp₁ hx₁y₁ D₂ hP₁c (by rw [s₁c, t₁c, s₁b, t₁b]; exact e₁)
      (by rw [edges₁c, edges₁b]; exact f₁) z₁c
  have n₂c : P₂' ≠ P₁c := fun h' => z₁c (h' ▸ hz₂)
  obtain ⟨P₂d, hP₂d, s₂d, t₂d, -, edges₂d⟩ := pres₃ P₂' hP₂' n₂c
  have n₃c : P₃c ≠ P₁c := fun h' => z₁c (by rw [← h', supp₃c]; exact hz₃)
  obtain ⟨P₃d, hP₃d, s₃d, t₃d, -, edges₃d⟩ := pres₃ P₃c hP₃c n₃c
  -- the star-terminal decomposition of `J`
  have hends : ∀ v, D₃.ends v = J.degree v % 2 := fun v => by rw [hD₃, hD₂, hD₁, hD, hpar]
  have hstar : StarAt D₃ z := by
    intro Q hQ hzQ
    rcases back₃ Q hQ with rfl | ⟨Q₂, hQ₂, -, hs, -, hsupp, hedges⟩
    · left; rw [s₁]; exact cz₁
    · rw [hsupp] at hzQ
      rcases back₂ Q₂ hQ₂ with rfl | ⟨Q₁, hQ₁, -, hs', -, hsupp', hedges'⟩
      · left; rw [hs, hedges, s₂]; exact cz₂
      · rw [hsupp'] at hzQ
        rcases back₁ Q₁ hQ₁ with rfl | ⟨Q₀, hQ₀, -, -, -, hsupp'', -⟩
        · left; rw [hs, hs', hedges, hedges', s₃]; exact cz₃
        · rw [hsupp''] at hzQ; exact absurd hzQ (hzP Q₀)
  refine ⟨⟨D₃, hends, hstar, ?_⟩, ⟨D₃, hends, hstar, ?_⟩, ⟨D₃, hends, hstar, ?_⟩⟩
  · rcases t₁ with ht | hall
    · exact Or.inl ⟨P₁', hP₁', zd₁, by rw [s₁]; exact hx₁y₁, ht⟩
    · exact Or.inr ⟨P₁', hP₁', hall⟩
  · rcases t₂ with ht | hall
    · exact Or.inl ⟨P₂d, hP₂d, by rw [edges₂d]; exact zd₂, by rw [s₂d, s₂]; exact hx₂y₂,
        by rw [t₂d]; exact ht⟩
    · exact Or.inr ⟨P₂d, hP₂d, by rw [edges₂d]; exact hall⟩
  · rcases t₃ with ht | hall
    · exact Or.inl ⟨P₃d, hP₃d, by rw [edges₃d, edges₃c]; exact zd₃,
        by rw [s₃d, s₃c, s₃]; exact hx₃y₃, by rw [t₃d, t₃c]; exact ht⟩
    · exact Or.inr ⟨P₃d, hP₃d, by rw [edges₃d, edges₃c]; exact hall⟩

/-- The lifted graph has no vertex of positive even degree when `z` is the only even vertex of
`J`. -/
theorem lift3_odd (J : SimpleGraph V) [DecidableRel J.Adj] {z x₁ y₁ x₂ y₂ x₃ y₃ : V}
    (hev : ∀ v, Even (J.degree v) ↔ v = z)
    (hN : ∀ w, J.Adj z w ↔ w = x₁ ∨ w = y₁ ∨ w = x₂ ∨ w = y₂ ∨ w = x₃ ∨ w = y₃)
    (hne : [x₁, y₁, x₂, y₂, x₃, y₃].Nodup)
    (hp₁ : ¬ J.Adj x₁ y₁) (hp₂ : ¬ J.Adj x₂ y₂) (hp₃ : ¬ J.Adj x₃ y₃) :
    ∀ v, v ∉ evenSet (lift3 J z x₁ y₁ x₂ y₂ x₃ y₃) := by
  have hdeg := lift3_degree J hN hne hp₁ hp₂ hp₃
  have hJz := degree_eq_six J hN hne
  intro v hv
  rw [mem_evenSet_iff] at hv
  have h0 := hdeg v
  by_cases hvz : v = z
  · rw [hvz, ite_eq_left rfl, hJz] at h0
    rw [hvz] at hv
    omega
  · rw [ite_eq_right hvz, add_zero] at h0
    have : ¬ Even (J.degree v) := fun h => hvz ((hev v).1 h)
    rw [Nat.not_even_iff] at this
    omega

/-- The neighbours of `z` are pairwise at distance at least three in `J − z`. -/
def FarNbrs (J : SimpleGraph V) (z : V) : Prop :=
  ∀ u v, J.Adj z u → J.Adj z v → u ≠ v → ¬ J.Adj u v ∧ ∀ w, w ≠ z → ¬ (J.Adj u w ∧ J.Adj w v)

/-- Far-apart neighbours of `z` in `J − z` are far-apart ends in the lifted graph. -/
theorem farEnds_lift3 (J : SimpleGraph V) [DecidableRel J.Adj] {z x₁ y₁ x₂ y₂ x₃ y₃ : V}
    (hN : ∀ w, J.Adj z w ↔ w = x₁ ∨ w = y₁ ∨ w = x₂ ∨ w = y₂ ∨ w = x₃ ∨ w = y₃)
    (hne : [x₁, y₁, x₂, y₂, x₃, y₃].Nodup) (hfar : FarNbrs J z)
    (hp₁ : ¬ J.Adj x₁ y₁) (hp₂ : ¬ J.Adj x₂ y₂) (hp₃ : ¬ J.Adj x₃ y₃) :
    FarEnds (lift3 J z x₁ y₁ x₂ y₂ x₃ y₃) x₁ y₁ x₂ y₂ x₃ y₃ := by
  have hdeg := lift3_degree J hN hne hp₁ hp₂ hp₃
  have hJz := degree_eq_six J hN hne
  have hiso : ∀ w, ¬ (lift3 J z x₁ y₁ x₂ y₂ x₃ y₃).Adj z w := by
    intro w hw
    have h0 := hdeg z
    rw [ite_eq_left rfl, hJz] at h0
    have : (lift3 J z x₁ y₁ x₂ y₂ x₃ y₃).degree z = 0 := by omega
    rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero] at this
    have : w ∈ (lift3 J z x₁ y₁ x₂ y₂ x₃ y₃).neighborFinset z := (mem_neighborFinset _ _ _).2 hw
    simp_all
  have hz6 : ∀ u ∈ [x₁, y₁, x₂, y₂, x₃, y₃], J.Adj z u := fun u hu =>
    (hN u).2 (by simpa using hu)
  refine ⟨fun u hu v hv huv => ?_, fun u hu v hv hne' w hwu hwv => ?_⟩
  · rw [lift3_adj J hne (hz6 u hu).ne.symm (hz6 v hv).ne.symm] at huv
    rcases huv with h | h
    · exact absurd h (hfar u v (hz6 u hu) (hz6 v hv) h.ne).1
    · exact h
  · have hwz : w ≠ z := fun h => hiso u (h ▸ hwu)
    rw [lift3_adj J hne hwz (hz6 u hu).ne.symm] at hwu
    rw [lift3_adj J hne hwz (hz6 v hv).ne.symm] at hwv
    rcases hwu with h₁ | h₁
    · rcases hwv with h₂ | h₂
      · exact absurd ⟨h₁.symm, h₂⟩ ((hfar u v (hz6 u hu) (hz6 v hv) hne').2 w hwz)
      · exact Or.inr h₂
    · exact Or.inl h₁

/-- **Degree six, the base form.** Let `z` be the only even vertex of `J`, with
`N(z) = {x₁, y₁, x₂, y₂, x₃, y₃}` (six distinct vertices) and `xᵢyᵢ ∉ E(J)`. If the lifted graph
`(J − z) + x₁y₁ + x₂y₂ + x₃y₃` has an admissible chain whose base graph has a Lovász
decomposition separating the six pairs of `ptm3_of_base`, then `STL J z yᵢ` for `i = 1, 2, 3`. -/
theorem stl3_of_base (J : SimpleGraph V) [DecidableRel J.Adj] {z x₁ y₁ x₂ y₂ x₃ y₃ : V}
    (hev : ∀ v, Even (J.degree v) ↔ v = z)
    (hN : ∀ w, J.Adj z w ↔ w = x₁ ∨ w = y₁ ∨ w = x₂ ∨ w = y₂ ∨ w = x₃ ∨ w = y₃)
    (hne : [x₁, y₁, x₂, y₂, x₃, y₃].Nodup)
    (hp₁ : ¬ J.Adj x₁ y₁) (hp₂ : ¬ J.Adj x₂ y₂) (hp₃ : ¬ J.Adj x₃ y₃) {q₁ q₂ : List V}
    (hC : AdmChain (lift3 J z x₁ y₁ x₂ y₂ x₃ y₃) x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂)
    (D₀ : PathDecomp (base3G (lift3 J z x₁ y₁ x₂ y₂ x₃ y₃) x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂))
    (hD₀ : ∀ v, D₀.ends v =
      (base3G (lift3 J z x₁ y₁ x₂ y₂ x₃ y₃) x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂).degree v % 2)
    (s₁ : Separates D₀ (some x₁) none) (s₂ : Separates D₀ (some x₂) (some y₂))
    (s₃ : Separates D₀ (some x₃) (some y₃)) (s₄ : Separates D₀ none (some y₂))
    (s₅ : Separates D₀ none (some y₃)) (s₆ : Separates D₀ (some y₂) (some y₃)) :
    STL J z y₁ ∧ STL J z y₂ ∧ STL J z y₃ := by
  have hz : ∀ u, J.Adj z u → u ≠ z := fun u h => h.ne.symm
  have hzx₁ := hz x₁ ((hN x₁).2 (Or.inl rfl))
  have hzy₁ := hz y₁ ((hN y₁).2 (Or.inr (Or.inl rfl)))
  have hzx₂ := hz x₂ ((hN x₂).2 (Or.inr (Or.inr (Or.inl rfl))))
  have hzy₂ := hz y₂ ((hN y₂).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hzx₃ := hz x₃ ((hN x₃).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have hzy₃ := hz y₃ ((hN y₃).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  have h₁ := (lift3_adj J hne hzx₁ hzy₁ (x₂ := x₂) (y₂ := y₂) (x₃ := x₃) (y₃ := y₃)).2
    (Or.inr (Or.inl rfl))
  have h₂ := (lift3_adj J hne hzx₂ hzy₂ (x₁ := x₁) (y₁ := y₁) (x₃ := x₃) (y₃ := y₃)).2
    (Or.inr (Or.inr (Or.inl rfl)))
  have h₃ := (lift3_adj J hne hzx₃ hzy₃ (x₁ := x₁) (y₁ := y₁) (x₂ := x₂) (y₂ := y₂)).2
    (Or.inr (Or.inr (Or.inr rfl)))
  exact stl_of_ptm3 J hN hne hp₁ hp₂ hp₃ (ptm3_of_base _ (lift3_odd J hev hN hne hp₁ hp₂ hp₃)
    h₁ h₂ h₃ hne hC D₀ hD₀ s₁ s₂ s₃ s₄ s₅ s₆)

/-- **Degree six, far-apart neighbours** (Corollary 8.4, first part). Let `z` be the only even
vertex of `J`, with `N(z) = {x₁, y₁, x₂, y₂, x₃, y₃}` (six distinct vertices) pairwise at
distance at least three in `J − z`. If the lifted graph `(J − z) + x₁y₁ + x₂y₂ + x₃y₃` has an
admissible chain for this labelling, then `STL J z yᵢ` for `i = 1, 2, 3`. -/
theorem stl3_of_far (J : SimpleGraph V) [DecidableRel J.Adj] {z x₁ y₁ x₂ y₂ x₃ y₃ : V}
    (hev : ∀ v, Even (J.degree v) ↔ v = z)
    (hN : ∀ w, J.Adj z w ↔ w = x₁ ∨ w = y₁ ∨ w = x₂ ∨ w = y₂ ∨ w = x₃ ∨ w = y₃)
    (hne : [x₁, y₁, x₂, y₂, x₃, y₃].Nodup) (hfar : FarNbrs J z) {q₁ q₂ : List V}
    (hC : AdmChain (lift3 J z x₁ y₁ x₂ y₂ x₃ y₃) x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂) :
    STL J z y₁ ∧ STL J z y₂ ∧ STL J z y₃ := by
  obtain ⟨hx₁y₁, -, -, -, -, -, -, -, -, hx₂y₂, -, -, -, -, hx₃y₃⟩ := nodup6 hne
  have hzx₁ := (hN x₁).2 (Or.inl rfl)
  have hzy₁ := (hN y₁).2 (Or.inr (Or.inl rfl))
  have hzx₂ := (hN x₂).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hzy₂ := (hN y₂).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hzx₃ := (hN x₃).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hzy₃ := (hN y₃).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have hp₁ := (hfar x₁ y₁ hzx₁ hzy₁ hx₁y₁).1
  have hp₂ := (hfar x₂ y₂ hzx₂ hzy₂ hx₂y₂).1
  have hp₃ := (hfar x₃ y₃ hzx₃ hzy₃ hx₃y₃).1
  have h₁ := (lift3_adj J hne hzx₁.ne.symm hzy₁.ne.symm (x₂ := x₂) (y₂ := y₂) (x₃ := x₃)
    (y₃ := y₃)).2 (Or.inr (Or.inl rfl))
  have h₂ := (lift3_adj J hne hzx₂.ne.symm hzy₂.ne.symm (x₁ := x₁) (y₁ := y₁) (x₃ := x₃)
    (y₃ := y₃)).2 (Or.inr (Or.inr (Or.inl rfl)))
  have h₃ := (lift3_adj J hne hzx₃.ne.symm hzy₃.ne.symm (x₁ := x₁) (y₁ := y₁) (x₂ := x₂)
    (y₂ := y₂)).2 (Or.inr (Or.inr (Or.inr rfl)))
  exact stl_of_ptm3 J hN hne hp₁ hp₂ hp₃ (ptm3_of_far _ (lift3_odd J hev hN hne hp₁ hp₂ hp₃)
    h₁ h₂ h₃ hne (farEnds_lift3 J hN hne hfar hp₁ hp₂ hp₃) hC)

/-- **Test 1 at degree six, far-apart neighbours** (Corollary 8.4, second part). Let every
neighbour of `z` have degree at least three, and let the neighbours of `z` be pairwise at distance
at least three in `J − z`. If for every `r ∈ N(z)` some labelling
`N(z) = {x₁, y₁, x₂, y₂, x₃, y₃}` with `r ∈ {y₁, y₂, y₃}` has an admissible chain in
`(J − z) + x₁y₁ + x₂y₂ + x₃y₃`, then `Test1 J z`. -/
theorem test1_of_chains3 (J : SimpleGraph V) [DecidableRel J.Adj] {z : V}
    (hdeg : ∀ r, J.Adj z r → 3 ≤ J.degree r) (hfar : FarNbrs J z)
    (hch : ∀ r, J.Adj z r → ∃ x₁ y₁ x₂ y₂ x₃ y₃ : V, ∃ q₁ q₂ : List V,
      (∀ w, J.Adj z w ↔ w = x₁ ∨ w = y₁ ∨ w = x₂ ∨ w = y₂ ∨ w = x₃ ∨ w = y₃) ∧
      [x₁, y₁, x₂, y₂, x₃, y₃].Nodup ∧ (r = y₁ ∨ r = y₂ ∨ r = y₃) ∧
      AdmChain (lift3 J z x₁ y₁ x₂ y₂ x₃ y₃) x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂) :
    Test1 J z :=
  test1_of_stl z hdeg fun hev r hr => by
    obtain ⟨x₁, y₁, x₂, y₂, x₃, y₃, q₁, q₂, hN, hne, hr', hC⟩ := hch r hr
    obtain ⟨t₁, t₂, t₃⟩ := stl3_of_far J hev hN hne hfar hC
    rcases hr' with rfl | rfl | rfl
    · exact t₁
    · exact t₂
    · exact t₃

/-- **Test 1 at degree six, the base form.** If every neighbour of `z` has degree at least three
and for every `r ∈ N(z)` some labelling `N(z) = {x₁, y₁, x₂, y₂, x₃, y₃}` with `xᵢyᵢ ∉ E(J)` and
`r ∈ {y₁, y₂, y₃}` has an admissible chain in `(J − z) + x₁y₁ + x₂y₂ + x₃y₃` whose base graph has
a Lovász decomposition separating the six pairs, then `Test1 J z`. -/
theorem test1_of_bases3 (J : SimpleGraph V) [DecidableRel J.Adj] {z : V}
    (hdeg : ∀ r, J.Adj z r → 3 ≤ J.degree r)
    (hch : ∀ r, J.Adj z r → ∃ x₁ y₁ x₂ y₂ x₃ y₃ : V, ∃ q₁ q₂ : List V,
      (∀ w, J.Adj z w ↔ w = x₁ ∨ w = y₁ ∨ w = x₂ ∨ w = y₂ ∨ w = x₃ ∨ w = y₃) ∧
      [x₁, y₁, x₂, y₂, x₃, y₃].Nodup ∧ ¬ J.Adj x₁ y₁ ∧ ¬ J.Adj x₂ y₂ ∧ ¬ J.Adj x₃ y₃ ∧
      (r = y₁ ∨ r = y₂ ∨ r = y₃) ∧
      AdmChain (lift3 J z x₁ y₁ x₂ y₂ x₃ y₃) x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂ ∧
      ∃ D₀ : PathDecomp (base3G (lift3 J z x₁ y₁ x₂ y₂ x₃ y₃) x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂),
        (∀ v, D₀.ends v =
          (base3G (lift3 J z x₁ y₁ x₂ y₂ x₃ y₃) x₁ y₁ x₂ y₂ x₃ y₃ q₁ q₂).degree v % 2) ∧
        Separates D₀ (some x₁) none ∧ Separates D₀ (some x₂) (some y₂) ∧
        Separates D₀ (some x₃) (some y₃) ∧ Separates D₀ none (some y₂) ∧
        Separates D₀ none (some y₃) ∧ Separates D₀ (some y₂) (some y₃)) :
    Test1 J z :=
  test1_of_stl z hdeg fun hev r hr => by
    obtain ⟨x₁, y₁, x₂, y₂, x₃, y₃, q₁, q₂, hN, hne, hp₁, hp₂, hp₃, hr', hC, D₀, hD₀, s₁, s₂, s₃,
      s₄, s₅, s₆⟩ := hch r hr
    obtain ⟨t₁, t₂, t₃⟩ :=
      stl3_of_base J hev hN hne hp₁ hp₂ hp₃ hC D₀ hD₀ s₁ s₂ s₃ s₄ s₅ s₆
    rcases hr' with rfl | rfl | rfl
    · exact t₁
    · exact t₂
    · exact t₃

end degreeSix
end Gallai
