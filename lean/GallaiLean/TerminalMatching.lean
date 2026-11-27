import GallaiLean.StarTerminal

/-!
# Two terminal edges at once (session `claude/ptm`)

Manuscript: `manuscripts/terminal-matching/terminal-matching.tex`.

**PTM₂.** Let `G` have no vertex of positive even degree, and let `ab`, `xy` be disjoint edges.
We look for a Lovász decomposition in which `ab` is the terminal edge at `a` of the path ending
at `a`, `xy` is the terminal edge at `x` of the path ending at `x`, and the two paths differ.

**The walk theorem** (`ptm2_of_base`). Let `p = [y, p_{k-1}, …, p₁, a]` be a path of `G` from
`y` to `a` avoiding `b` and `x`, whose vertices other than `y` and `a` are not adjacent to `x`.
Let `M` be the leaf graph `H₁ = (G − ab) + ℓ₁b` minus `xy` and minus the edges of `p`. If `M`
has a Lovász decomposition in which no path contains `x, y`, nor `a, ℓ₁`, nor `ℓ₁, y`, then PTM₂
holds with short ends `a` and `x`.

Proof: attach a second leaf `ℓ₂` at `y` (`liftLeaf`), restore the edges of `p` one at a time by
Fan's lemma (`walk_back`) inside the two-leaf graph, where both prescriptions are vertex-set
separations, and merge the two leaves (`leaf_merge` twice). Every Fan target lies on `p`, away
from `x`, `a` and the leaves, so the separations survive.

`base_of_fix`: the hypothesis on `M` follows from `separation_sparse` when the four vertices
`x, y, a, ℓ₁` are sparse in `M` except for at most one vertex adjacent to `x`.
-/

open SimpleGraph

namespace Gallai

universe u v

/-! ### Chains of edges -/

section chain

variable {U : Type v}

/-- Edges between consecutive vertices of a list. -/
def chainEdges : List U → List (Sym2 U)
  | a :: b :: t => s(a, b) :: chainEdges (b :: t)
  | _ => []

/-- Consecutive vertices of the list are adjacent in `K`. -/
def ChainAdj (K : SimpleGraph U) : List U → Prop
  | a :: b :: t => K.Adj a b ∧ ChainAdj K (b :: t)
  | _ => True

/-- The last vertex of `w :: l`. -/
def chainLast : U → List U → U
  | w, [] => w
  | _, b :: t => chainLast b t

/-- The vertices of `w :: l` except the last one. -/
def initOf : U → List U → List U
  | _, [] => []
  | w, b :: t => w :: initOf b t

theorem mem_of_mem_chainEdges : ∀ (l : List U) {e : Sym2 U}, e ∈ chainEdges l → ∀ z ∈ e, z ∈ l
  | a :: b :: t, e, he, z, hz => by
      simp only [chainEdges, List.mem_cons] at he
      rcases he with rfl | he
      · rcases Sym2.mem_iff.mp hz with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_of_mem_chainEdges (b :: t) he z hz)
  | [], _, he, _, _ => by simp [chainEdges] at he
  | [_], _, he, _, _ => by simp [chainEdges] at he

theorem mem_initOf_mem : ∀ (w : U) (l : List U) {z : U}, z ∈ initOf w l → z ∈ w :: l
  | _, [], _, h => by simp [initOf] at h
  | w, b :: t, z, h => by
      simp only [initOf, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_initOf_mem b t h)

theorem chainLast_mem : ∀ (w : U) (l : List U), chainLast w l ∈ w :: l
  | _, [] => List.mem_cons_self
  | _, b :: t => List.mem_cons_of_mem _ (chainLast_mem b t)

/-- The last vertex of a duplicate-free list is not among the others. -/
theorem chainLast_not_mem_initOf : ∀ (w : U) (l : List U), (w :: l).Nodup → chainLast w l ∉ initOf w l
  | _, [], _ => by simp [initOf]
  | w, b :: t, hnd => by
      simp only [chainLast, initOf, List.mem_cons, not_or]
      rw [List.nodup_cons] at hnd
      refine ⟨fun h => hnd.1 (h ▸ chainLast_mem b t), chainLast_not_mem_initOf b t hnd.2⟩

theorem chainEdges_map {U' : Type*} (f : U → U') :
    ∀ l : List U, chainEdges (l.map f) = (chainEdges l).map (Sym2.map f)
  | a :: b :: t => by
      simp only [List.map_cons, chainEdges, Sym2.map_mk]
      rw [← List.map_cons, chainEdges_map f (b :: t)]
  | [] => rfl
  | [_] => rfl

theorem chainAdj_map_mem {U' : Type*} {K : SimpleGraph U} {K' : SimpleGraph U'} (f : U → U') :
    ∀ l : List U, ChainAdj K l → (∀ a ∈ l, ∀ b ∈ l, K.Adj a b → K'.Adj (f a) (f b)) →
      ChainAdj K' (l.map f)
  | a :: b :: t, h, hf => by
      simp only [List.map_cons, ChainAdj] at h ⊢
      refine ⟨hf a List.mem_cons_self b (List.mem_cons_of_mem _ List.mem_cons_self) h.1, ?_⟩
      rw [← List.map_cons]
      exact chainAdj_map_mem f (b :: t) h.2 (fun c hc d hd => hf c (List.mem_cons_of_mem _ hc) d
        (List.mem_cons_of_mem _ hd))
  | [], _, _ => trivial
  | [_], _, _ => trivial

theorem chainAdj_map {U' : Type*} {K : SimpleGraph U} {K' : SimpleGraph U'} (f : U → U')
    (hf : ∀ a b, K.Adj a b → K'.Adj (f a) (f b)) :
    ∀ l : List U, ChainAdj K l → ChainAdj K' (l.map f)
  | a :: b :: t, h => by
      simp only [List.map_cons, ChainAdj] at h ⊢
      exact ⟨hf a b h.1, by rw [← List.map_cons]; exact chainAdj_map f hf (b :: t) h.2⟩
  | [], _ => trivial
  | [_], _ => trivial

theorem chainLast_map {U' : Type*} (f : U → U') :
    ∀ (w : U) (l : List U), chainLast (f w) (l.map f) = f (chainLast w l)
  | _, [] => rfl
  | _, b :: t => chainLast_map f b t

theorem initOf_map {U' : Type*} (f : U → U') :
    ∀ (w : U) (l : List U), initOf (f w) (l.map f) = (initOf w l).map f
  | _, [] => rfl
  | w, b :: t => by
      simp only [List.map_cons, initOf]
      rw [initOf_map f b t]

end chain

/-! ### Deleting the edges of a chain -/

section delChain

variable {U : Type u}

/-- `K` with the edges of a chain removed, one at a time. -/
def delChain (K : SimpleGraph U) : List U → SimpleGraph U
  | a :: b :: t => delChain (delEdge K a b) (b :: t)
  | _ => K

theorem delChain_edgeSet : ∀ (K : SimpleGraph U) (l : List U) (e : Sym2 U),
    e ∈ (delChain K l).edgeSet ↔ e ∈ K.edgeSet ∧ e ∉ chainEdges l
  | K, a :: b :: t, e => by
      rw [show delChain K (a :: b :: t) = delChain (delEdge K a b) (b :: t) from rfl,
        delChain_edgeSet (delEdge K a b) (b :: t) e, delEdge_edgeSet]
      simp only [chainEdges, List.mem_cons, not_or]
      tauto
  | K, [], e => by simp [delChain, chainEdges]
  | K, [_], e => by simp [delChain, chainEdges]

theorem delChain_adj (K : SimpleGraph U) (l : List U) (a b : U) :
    (delChain K l).Adj a b ↔ K.Adj a b ∧ s(a, b) ∉ chainEdges l := by
  rw [← mem_edgeSet, delChain_edgeSet, mem_edgeSet]

variable [DecidableEq U]

/-- Decidability of adjacency after deleting a chain. -/
@[reducible] def delChainDec : ∀ (K : SimpleGraph U) [DecidableRel K.Adj] (l : List U),
    DecidableRel (delChain K l).Adj
  | K, _, a :: b :: t => delChainDec (delEdge K a b) (b :: t)
  | _, h, [] => h
  | _, h, [_] => h

instance delChain.decRel (K : SimpleGraph U) [DecidableRel K.Adj] (l : List U) :
    DecidableRel (delChain K l).Adj := delChainDec K l

end delChain

/-! ### Restoring a path by Fan steps -/

section walkBack

variable {U : Type u} [Fintype U] [DecidableEq U]

/-- **Walking an end back along a path.** Let `w :: l` be a duplicate-free chain of `K`, and let
`K₀` be `K` without the chain edges. Suppose every vertex adjacent (in `K`) to a vertex of the
chain other than the last one, except `w` itself, has an end in `D`. Restoring the chain edges by
Fan's lemma, from `w` onwards, gives a decomposition of `K` in which `w` has gained one end and the
last vertex has lost one; every new path lies in an old path plus vertices of the chain other
than the last. -/
theorem walk_back (K : SimpleGraph U) [DecidableRel K.Adj] :
    ∀ (l : List U) (w : U) (K₀ : SimpleGraph U) [DecidableRel K₀.Adj] (D : PathDecomp K₀),
      ChainAdj K (w :: l) → (w :: l).Nodup →
      (∀ e, e ∈ K₀.edgeSet ↔ e ∈ K.edgeSet ∧ e ∉ chainEdges (w :: l)) →
      (∀ t ∈ initOf w l, ∀ v, K.Adj t v → v ≠ w → 1 ≤ D.ends v) →
      ∃ D' : PathDecomp K,
        (∀ v, D'.ends v + (if v = chainLast w l then 1 else 0) =
          D.ends v + (if v = w then 1 else 0)) ∧
        ∀ Q ∈ D'.paths, ∃ Q' ∈ D.paths, ∀ z ∈ Q.walk.support,
          z ∈ Q'.walk.support ∨ z ∈ initOf w l
  | [], w, K₀, _, D, _, _, hK₀, _ => by
      have hK : K₀ = K := by
        ext a b
        have := hK₀ s(a, b)
        simp only [mem_edgeSet, chainEdges, List.not_mem_nil, not_false_eq_true, and_true] at this
        exact this
      subst hK
      refine ⟨D, fun v => rfl, fun Q hQ => ⟨Q, hQ, fun z hz => Or.inl hz⟩⟩
  | b :: t, w, K₀, _, D, hch, hnd, hK₀, hZ => by
      obtain ⟨hwb, hch'⟩ := hch
      have hwnot : w ∉ b :: t := (List.nodup_cons.mp hnd).1
      have hnd' : (b :: t).Nodup := (List.nodup_cons.mp hnd).2
      have hwb' : w ≠ b := fun h => hwnot (h ▸ List.mem_cons_self)
      -- the intermediate graph `K₁ = K − (edges of b :: t)`
      have hK₁w : (delChain K (b :: t)).Adj w b := by
        rw [delChain_adj]
        refine ⟨hwb, fun h => hwnot ?_⟩
        exact mem_of_mem_chainEdges (b :: t) h w (Sym2.mem_mk_left w b)
      have hG' : ∀ e, e ∈ K₀.edgeSet ↔ e ∈ (delChain K (b :: t)).edgeSet ∧ e ≠ s(w, b) := by
        intro e
        rw [hK₀, delChain_edgeSet]
        simp only [chainEdges, List.mem_cons, not_or]
        tauto
      have hwinit : w ∈ initOf w (b :: t) := by simp [initOf]
      have hcount : (Finset.univ.filter (fun v => K₀.Adj w v ∧ D.ends v = 0)).card < D.ends b := by
        have hempty : Finset.univ.filter (fun v => K₀.Adj w v ∧ D.ends v = 0) = ∅ := by
          refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
          rw [Finset.mem_filter] at hv
          obtain ⟨-, hadj, h0⟩ := hv
          have hadjK : K.Adj w v := by
            have := (hK₀ s(w, v)).1 hadj
            exact this.1
          have := hZ w hwinit v hadjK hadjK.ne.symm
          omega
        rw [hempty, Finset.card_empty]
        exact hZ w hwinit b hwb (Ne.symm hwb')
      obtain ⟨D₁, -, hD₁w, hD₁b, hD₁rest, hcov₁⟩ :=
        fan_single_supp (G := delChain K (b :: t)) (G' := K₀) hK₁w hG' D hcount
      have hZ₁ : ∀ s ∈ initOf b t, ∀ v, K.Adj s v → v ≠ b → 1 ≤ D₁.ends v := by
        intro s hs v hsv hvb
        by_cases hvw : v = w
        · subst hvw; omega
        · rw [hD₁rest v hvw hvb]
          exact hZ s (by simp only [initOf, List.mem_cons]; exact Or.inr hs) v hsv hvw
      obtain ⟨D', hD'e, hcov'⟩ := walk_back K t b (delChain K (b :: t)) D₁ hch' hnd'
        (fun e => delChain_edgeSet K (b :: t) e) hZ₁
      refine ⟨D', fun v => ?_, fun Q hQ => ?_⟩
      · have h1 := hD'e v
        show D'.ends v + (if v = chainLast b t then 1 else 0) = D.ends v + (if v = w then 1 else 0)
        by_cases hvw : v = w
        · subst hvw
          simp only [hwb', ite_false, ite_true, add_zero] at h1 ⊢
          omega
        · by_cases hvb : v = b
          · subst hvb
            simp only [hvw, ite_true, ite_false, add_zero] at h1 ⊢
            omega
          · rw [hD₁rest v hvw hvb] at h1
            simp only [hvb, hvw, ite_false, add_zero] at h1 ⊢
            exact h1
      · obtain ⟨Q₁, hQ₁, hs₁⟩ := hcov' Q hQ
        obtain ⟨Q₀, hQ₀, hs₀⟩ := hcov₁ Q₁ hQ₁
        refine ⟨Q₀, hQ₀, fun z hz => ?_⟩
        rcases hs₁ z hz with h | h
        · rcases hs₀ z h with h' | rfl
          · exact Or.inl h'
          · exact Or.inr hwinit
        · exact Or.inr (by simp only [initOf, List.mem_cons]; exact Or.inr h)

end walkBack

/-! ### Degrees after deleting a chain -/

section chainDegree

variable {U : Type u} [Fintype U] [DecidableEq U]

omit [Fintype U] [DecidableEq U] in
theorem chainAdj_delEdge {K : SimpleGraph U} {w b : U} :
    ∀ l : List U, ChainAdj K l → (∀ e ∈ chainEdges l, e ≠ s(w, b)) → ChainAdj (delEdge K w b) l
  | c :: d :: t, h, hne => by
      simp only [ChainAdj, chainEdges, List.mem_cons, forall_eq_or_imp] at h hne ⊢
      exact ⟨⟨h.1, hne.1⟩, chainAdj_delEdge (d :: t) h.2 hne.2⟩
  | [], _, _ => trivial
  | [_], _, _ => trivial

/-- Deleting the edges of a duplicate-free chain of length `≥ 1` changes the parity of the degree
exactly at the two ends of the chain. -/
theorem delChain_degree_mod (K : SimpleGraph U) [DecidableRel K.Adj] :
    ∀ (w : U) (l : List U), l ≠ [] → ChainAdj K (w :: l) → (w :: l).Nodup → ∀ v,
      ((delChain K (w :: l)).degree v + (if v = w then 1 else 0) +
        (if v = chainLast w l then 1 else 0)) % 2 = K.degree v % 2
  | _, [], h, _, _, _ => absurd rfl h
  | w, b :: t, _, hch, hnd, v => by
      obtain ⟨hwb, hch'⟩ := hch
      have hwnot : w ∉ b :: t := (List.nodup_cons.mp hnd).1
      have hd := delEdge_degree K hwb v
      have hwb' : w ≠ b := hwb.ne
      rw [show chainLast w (b :: t) = chainLast b t from rfl]
      by_cases ht : t = []
      · subst ht
        rw [show chainLast b ([] : List U) = b from rfl]
        show ((delEdge K w b).degree v + _ + _) % 2 = _
        split_ifs at hd ⊢ <;> (try subst_vars) <;> omega
      · have hch'' : ChainAdj (delEdge K w b) (b :: t) := chainAdj_delEdge (b :: t) hch'
          (fun e he h => hwnot (mem_of_mem_chainEdges (b :: t) he w (h ▸ Sym2.mem_mk_left w b)))
        have ih := delChain_degree_mod (delEdge K w b) b t ht hch'' (List.nodup_cons.mp hnd).2 v
        show ((delChain (delEdge K w b) (b :: t)).degree v + _ + _) % 2 = _
        split_ifs at hd ih ⊢ <;> (try subst_vars) <;> omega

/-- A vertex off the chain keeps its degree. -/
theorem delChain_degree_of_not_mem (K : SimpleGraph U) [DecidableRel K.Adj] :
    ∀ (l : List U) (v : U), ChainAdj K l → l.Nodup → v ∉ l → (delChain K l).degree v = K.degree v
  | c :: d :: t, v, hch, hnd, hv => by
      obtain ⟨hcd, hch'⟩ := hch
      have h1 : v ≠ c := fun h => hv (h ▸ List.mem_cons_self)
      have h2 : v ≠ d := fun h => hv (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)
      have hcnot : c ∉ d :: t := (List.nodup_cons.mp hnd).1
      have hch'' : ChainAdj (delEdge K c d) (d :: t) := chainAdj_delEdge (d :: t) hch'
        (fun e he h => hcnot (mem_of_mem_chainEdges (d :: t) he c (h ▸ Sym2.mem_mk_left c d)))
      show (delChain (delEdge K c d) (d :: t)).degree v = _
      rw [delChain_degree_of_not_mem (delEdge K c d) (d :: t) v hch'' (List.nodup_cons.mp hnd).2
        (fun h => hv (List.mem_cons_of_mem _ h))]
      have := delEdge_degree K hcd v
      rw [if_neg h1, if_neg h2] at this
      omega
  | [], _, _, _, _ => rfl
  | [_], _, _, _, _ => rfl

end chainDegree

/-! ### The base case from sparse separation -/

section sparseFix

variable {U : Type u} [Fintype U] [DecidableEq U]

/-- **Sparse separation with one exceptional vertex.** Let `g` be the only vertex of `K` that can
have positive even degree, with `deg g` even, and let `v` be a neighbour of `g`. If the family is
sparse in `K − gv` and `v ∉ X`, then `K` has a Lovász decomposition meeting every set of the
family at most once per path. (Separate in `K − gv`, where `v` is the even vertex, and restore `gv`
by Fan's lemma with target `v`.) -/
theorem sep_sparse_fix (K : SimpleGraph U) [DecidableRel K.Adj] {g v : U}
    (hev : ∀ w ∈ evenSet K, w = g) (hg : K.degree g % 2 = 0) (hgv : K.Adj g v)
    {X : Finset U} {𝒜 : Finset (Finset U)} (hX : SparseFam (delEdge K g v) X 𝒜) (hvX : v ∉ X) :
    ∃ D : PathDecomp K, (∀ w, D.ends w = K.degree w % 2) ∧ ∀ A ∈ 𝒜, MeetsOnce D A := by
  have hgv' : g ≠ v := hgv.ne
  have hd := delEdge_degree K hgv
  have hvodd : K.degree v % 2 = 1 := by
    have hpos : 0 < K.degree v := (K.degree_pos_iff_exists_adj v).mpr ⟨g, hgv.symm⟩
    by_contra h
    have : v ∈ evenSet K := by rw [mem_evenSet_iff]; omega
    exact hgv' (hev v this).symm
  have hev' : (evenSet (delEdge K g v)).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun w₁ h₁ w₂ h₂ => ?_
    have key : ∀ w ∈ evenSet (delEdge K g v), w = v := by
      intro w hw
      rw [mem_evenSet_iff] at hw
      have := hd w
      by_cases hwg : w = g
      · subst hwg; simp only [ite_true, hgv', ite_false, add_zero] at this; omega
      · by_cases hwv : w = v
        · exact hwv
        · simp only [hwg, hwv, ite_false, add_zero] at this
          exact absurd (hev w (by rw [mem_evenSet_iff]; omega)) hwg
    rw [key w₁ h₁, key w₂ h₂]
  obtain ⟨D', hD', hmeet⟩ := separation_sparse (delEdge K g v) hev' hX
  have hG' : ∀ e, e ∈ (delEdge K g v).edgeSet ↔ e ∈ K.edgeSet ∧ e ≠ s(v, g) := by
    intro e; rw [delEdge_edgeSet, Sym2.eq_swap]
  have hD'g : D'.ends g = 1 := by
    rw [hD']; have := hd g; simp only [ite_true, hgv', ite_false, add_zero] at this; omega
  have hD'v : D'.ends v = 0 := by
    rw [hD']; have := hd v; simp only [Ne.symm hgv', ite_true, ite_false, zero_add] at this; omega
  have hcount : (Finset.univ.filter (fun w => (delEdge K g v).Adj v w ∧ D'.ends w = 0)).card <
      D'.ends g := by
    have hempty : Finset.univ.filter (fun w => (delEdge K g v).Adj v w ∧ D'.ends w = 0) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun w hw => ?_
      rw [Finset.mem_filter] at hw
      obtain ⟨-, hadj, h0⟩ := hw
      have hwv : w ≠ v := hadj.ne.symm
      have hpos : 0 < (delEdge K g v).degree w :=
        ((delEdge K g v).degree_pos_iff_exists_adj w).mpr ⟨v, hadj.symm⟩
      rw [hD'] at h0
      have hmem : w ∈ evenSet (delEdge K g v) := by rw [mem_evenSet_iff]; omega
      have := hd w
      by_cases hwg : w = g
      · subst hwg; simp only [ite_true, hgv', ite_false, add_zero] at this; omega
      · simp only [hwg, hwv, ite_false, add_zero] at this
        exact hwg (hev w (by rw [mem_evenSet_iff]; omega))
    rw [hempty, Finset.card_empty, hD'g]; omega
  obtain ⟨D, -, hDv, hDg, hDrest, hcov⟩ := fan_single_supp (G := K) hgv.symm hG' D' hcount
  refine ⟨D, fun w => ?_, fun A hA => meetsAll_of_cover hX.sub hvX hmeet hcov A hA⟩
  by_cases hwv : w = v
  · subst hwv; rw [hDv, hD'v, hvodd]
  · by_cases hwg : w = g
    · subst hwg; rw [hg]; omega
    · rw [hDrest w hwv hwg, hD']
      have := hd w
      simp only [hwg, hwv, ite_false, add_zero] at this
      rw [this]

end sparseFix

/-! ### The walk theorem -/

section main

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- The leaf graph of the edge `ab` at `a`: `ab` replaced by the pendant edge `b ℓ₁`
(`ℓ₁ = none` stands for `a`). -/
abbrev leafG (G : SimpleGraph W) (a b : W) : SimpleGraph (Option W) := apex (delEdge G b a) {b}

/-- The leaf graph of `ab` at `a`, minus the edge `xy`. -/
abbrev midG (G : SimpleGraph W) (a b x y : W) : SimpleGraph (Option W) :=
  delEdge (leafG G a b) (some y) (some x)

/-- The base graph of the walk theorem: the leaf graph of `ab` at `a`, minus `xy`, minus the
edges of the chain `y :: q`. -/
abbrev baseG (G : SimpleGraph W) (a b x y : W) (q : List W) : SimpleGraph (Option W) :=
  delChain (midG G a b x y) ((y :: q).map some)

omit [Fintype W] in
theorem separates_of_cover_list {U : Type*} [DecidableEq U] {K K' : SimpleGraph U}
    {D : PathDecomp K} {D' : PathDecomp K'} {c d : U} {T : List U} (hc : c ∉ T) (hd : d ∉ T)
    (hD' : Separates D' c d)
    (hcov : ∀ Q ∈ D.paths, ∃ Q' ∈ D'.paths, ∀ z ∈ Q.walk.support, z ∈ Q'.walk.support ∨ z ∈ T) :
    Separates D c d := by
  intro Q hQ ⟨hcQ, hdQ⟩
  obtain ⟨Q', hQ', h⟩ := hcov Q hQ
  exact hD' Q' hQ' ⟨(h c hcQ).resolve_right hc, (h d hdQ).resolve_right hd⟩

/-- Degree parities in the base graph: only `x` changes parity, and the leaf `ℓ₁` is odd. -/
theorem baseG_parity (G : SimpleGraph W) [DecidableRel G.Adj] (hodd : ∀ v, v ∉ evenSet G)
    {a b x y : W} (hab : G.Adj a b) (hxy : G.Adj x y)
    (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y)
    (q : List W) (hlast : chainLast y q = a)
    (hch : ChainAdj G (y :: q)) (hnd : (y :: q).Nodup) (hbq : b ∉ y :: q) (hxq : x ∉ y :: q) :
    (∀ v, (baseG G a b x y q).degree (some v) % 2 = (G.degree v + if v = x then 1 else 0) % 2) ∧
      (baseG G a b x y q).degree none % 2 = 1 := by
  classical
  have hab' : a ≠ b := hab.ne
  have hxy' : x ≠ y := hxy.ne
  have hoddv : ∀ v, 0 < G.degree v → G.degree v % 2 = 1 := by
    intro v hv
    have := hodd v
    rw [mem_evenSet_iff] at this
    omega
  have hq : q ≠ [] := by
    rintro rfl
    exact hay (hlast.symm.trans rfl)
  have hK₁yx : (leafG G a b).Adj (some y) (some x) := by
    rw [apex_adj_some_some]
    refine ⟨hxy.symm, fun h => ?_⟩
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hby h1.symm
    · exact hay h1.symm
  have hK₂adj : ∀ u w, (midG G a b x y).Adj (some u) (some w) ↔
      G.Adj u w ∧ s(u, w) ≠ s(b, a) ∧ s(u, w) ≠ s(y, x) := by
    intro u w
    show ((leafG G a b).Adj (some u) (some w) ∧ ¬ s(some u, some w) = s(some y, some x)) ↔ _
    rw [apex_adj_some_some]
    show ((G.Adj u w ∧ ¬ s(u, w) = s(b, a)) ∧ _) ↔ _
    have : s(some u, some w) = s(some y, some x) ↔ s(u, w) = s(y, x) := by
      constructor
      · intro h
        have := congrArg (Sym2.map (Option.getD · y)) h
        simpa using this
      · intro h; rw [show s(some u, some w) = s(u, w).map some from rfl, h]; rfl
    rw [this]
    tauto
  have hlist : ∀ u ∈ y :: q, ∀ w ∈ y :: q, G.Adj u w → (midG G a b x y).Adj (some u) (some w) := by
    intro u hu w hw huw
    rw [hK₂adj]
    refine ⟨huw, fun h => ?_, fun h => ?_⟩
    · rcases Sym2.eq_iff.mp h with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact hbq hu
      · exact hbq hw
    · rcases Sym2.eq_iff.mp h with ⟨-, rfl⟩ | ⟨rfl, -⟩
      · exact hxq hw
      · exact hxq hu
  have hchK₂ : ChainAdj (midG G a b x y) ((y :: q).map some) := chainAdj_map_mem some (y :: q) hch hlist
  have hndK₂ : ((y :: q).map some).Nodup := hnd.map (Option.some_injective W)
  have hlastK₂ : chainLast (some y) (q.map some) = some a := by
    rw [chainLast_map, hlast]
  -- degrees in the base graph
  have hdG := fun v => delEdge_degree G hab.symm v
  have hdK₁ : ∀ v, (leafG G a b).degree (some v) = (delEdge G b a).degree v + if v = b then 1 else 0 := by
    intro v
    show (apex (delEdge G b a) {b}).degree (some v) = _
    rw [apex_degree_some]; simp only [Finset.mem_singleton]
  have hdK₁none : (leafG G a b).degree none = 1 := by
    show (apex (delEdge G b a) {b}).degree none = _
    rw [apex_degree_none]; simp
  have hdK₂ := fun w => delEdge_degree (leafG G a b) hK₁yx w
  have hdM := delChain_degree_mod (midG G a b x y) (some y) (q.map some) (by simpa using hq) hchK₂ hndK₂
  rw [hlastK₂] at hdM
  have hMsome : ∀ v, (baseG G a b x y q).degree (some v) % 2 = (G.degree v + if v = x then 1 else 0) % 2 := by
    intro v
    have h1 : ((baseG G a b x y q).degree (some v) + (if some v = some y then 1 else 0) +
        (if some v = some a then 1 else 0)) % 2 = (midG G a b x y).degree (some v) % 2 :=
      hdM (some v)
    have h2 : (midG G a b x y).degree (some v) + (if some v = some y then 1 else 0) +
        (if some v = some x then 1 else 0) = (leafG G a b).degree (some v) := hdK₂ (some v)
    have h3 := hdK₁ v
    have h4 := hdG v
    simp only [Option.some.injEq] at h1 h2
    by_cases hva : v = a
    · subst hva
      simp only [hay, hax, hab', ite_true, ite_false, add_zero] at h1 h2 h3 h4 ⊢
      omega
    · by_cases hvb : v = b
      · subst hvb
        simp only [hby, hbx, hva, ite_true, ite_false, add_zero] at h1 h2 h3 h4 ⊢
        omega
      · by_cases hvx : v = x
        · subst hvx
          simp only [hxy', hva, hvb, ite_true, ite_false, add_zero] at h1 h2 h3 h4 ⊢
          omega
        · by_cases hvy : v = y
          · subst hvy
            simp only [hvx, hva, hvb, ite_true, ite_false, add_zero] at h1 h2 h3 h4 ⊢
            omega
          · simp only [hvx, hva, hvb, hvy, ite_false, add_zero] at h1 h2 h3 h4 ⊢
            omega
  have hMnone : (baseG G a b x y q).degree none % 2 = 1 := by
    have h1 : ((baseG G a b x y q).degree none + (if (none : Option W) = some y then 1 else 0) +
        (if (none : Option W) = some a then 1 else 0)) % 2 = (midG G a b x y).degree none % 2 :=
      hdM none
    have h2 : (midG G a b x y).degree none + (if (none : Option W) = some y then 1 else 0) +
        (if (none : Option W) = some x then 1 else 0) = (leafG G a b).degree none := hdK₂ none
    simp only [reduceCtorEq, ite_false, add_zero] at h1 h2
    rw [hdK₁none] at h2
    omega
  exact ⟨hMsome, hMnone⟩

/-- Adjacency in the base graph comes from `G` or from the leaf edge `bℓ₁`. -/
theorem baseG_adj_some (G : SimpleGraph W) {a b x y : W} (q : List W) {u : W} {z : Option W}
    (h : (baseG G a b x y q).Adj (some u) z) : (z = none ∧ u = b) ∨ ∃ w, z = some w ∧ G.Adj u w := by
  rw [baseG, delChain_adj] at h
  have h1 := h.1.1
  cases z with
  | none => exact Or.inl ⟨rfl, by simpa using h1⟩
  | some w => exact Or.inr ⟨w, rfl, (apex_adj_some_some.mp h1).1⟩

/-- **The walk theorem.** Let `ab`, `xy` be disjoint edges of `G` (no vertex of positive even
degree), and `y :: q` a duplicate-free chain from `y` to `a` avoiding `b` and `x`, whose
vertices other than `y` and `a` are not adjacent to `x`. If the base graph has a Lovász
decomposition in which no path contains `x, y`, nor `a, ℓ₁`, nor `ℓ₁, y`, then `G` has a Lovász
decomposition with `ab` terminal at `a` and `xy` terminal at `x`, on different paths. -/
theorem ptm2_of_base (G : SimpleGraph W) [DecidableRel G.Adj] (hodd : ∀ v, v ∉ evenSet G)
    {a b x y : W} (hab : G.Adj a b) (hxy : G.Adj x y)
    (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y)
    (q : List W) (hlast : chainLast y q = a)
    (hch : ChainAdj G (y :: q)) (hnd : (y :: q).Nodup) (hbq : b ∉ y :: q) (hxq : x ∉ y :: q)
    (hZ : ∀ t ∈ initOf y q, t ≠ y → ¬ G.Adj t x)
    (D₀ : PathDecomp (baseG G a b x y q))
    (hD₀ : ∀ v, D₀.ends v = (baseG G a b x y q).degree v % 2)
    (hs1 : Separates D₀ (some x) (some y)) (hs2 : Separates D₀ (some a) none)
    (hs3 : Separates D₀ none (some y)) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∃ P₁ ∈ D.paths, ∃ P₂ ∈ D.paths, P₁ ≠ P₂ ∧ (P₁.src = a ∨ P₁.tgt = a) ∧
        s(a, b) ∈ P₁.edges ∧ (P₂.src = x ∨ P₂.tgt = x) ∧ s(x, y) ∈ P₂.edges := by
  classical
  have hab' : a ≠ b := hab.ne
  have hxy' : x ≠ y := hxy.ne
  have hoddv : ∀ v, 0 < G.degree v → G.degree v % 2 = 1 := by
    intro v hv
    have := hodd v
    rw [mem_evenSet_iff] at this
    omega
  have hq : q ≠ [] := by
    rintro rfl
    exact hay (hlast.symm.trans rfl)
  have hK₁yx : (leafG G a b).Adj (some y) (some x) := by
    rw [apex_adj_some_some]
    refine ⟨hxy.symm, fun h => ?_⟩
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hby h1.symm
    · exact hay h1.symm
  have hK₂adj : ∀ u w, (midG G a b x y).Adj (some u) (some w) ↔
      G.Adj u w ∧ s(u, w) ≠ s(b, a) ∧ s(u, w) ≠ s(y, x) := by
    intro u w
    show ((leafG G a b).Adj (some u) (some w) ∧ ¬ s(some u, some w) = s(some y, some x)) ↔ _
    rw [apex_adj_some_some]
    show ((G.Adj u w ∧ ¬ s(u, w) = s(b, a)) ∧ _) ↔ _
    have : s(some u, some w) = s(some y, some x) ↔ s(u, w) = s(y, x) := by
      constructor
      · intro h
        have := congrArg (Sym2.map (Option.getD · y)) h
        simpa using this
      · intro h; rw [show s(some u, some w) = s(u, w).map some from rfl, h]; rfl
    rw [this]
    tauto
  have hlist : ∀ u ∈ y :: q, ∀ w ∈ y :: q, G.Adj u w → (midG G a b x y).Adj (some u) (some w) := by
    intro u hu w hw huw
    rw [hK₂adj]
    refine ⟨huw, fun h => ?_, fun h => ?_⟩
    · rcases Sym2.eq_iff.mp h with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact hbq hu
      · exact hbq hw
    · rcases Sym2.eq_iff.mp h with ⟨-, rfl⟩ | ⟨rfl, -⟩
      · exact hxq hw
      · exact hxq hu
  have hchK₂ : ChainAdj (midG G a b x y) ((y :: q).map some) := chainAdj_map_mem some (y :: q) hch hlist
  have hndK₂ : ((y :: q).map some).Nodup := hnd.map (Option.some_injective W)
  have hlastK₂ : chainLast (some y) (q.map some) = some a := by
    rw [chainLast_map, hlast]
  -- degrees in the base graph
  have hdG := fun v => delEdge_degree G hab.symm v
  have hdK₁ : ∀ v, (leafG G a b).degree (some v) = (delEdge G b a).degree v + if v = b then 1 else 0 := by
    intro v
    show (apex (delEdge G b a) {b}).degree (some v) = _
    rw [apex_degree_some]; simp only [Finset.mem_singleton]
  have hdK₁none : (leafG G a b).degree none = 1 := by
    show (apex (delEdge G b a) {b}).degree none = _
    rw [apex_degree_none]; simp
  have hdK₂ := fun w => delEdge_degree (leafG G a b) hK₁yx w
  have hdM := delChain_degree_mod (midG G a b x y) (some y) (q.map some) (by simpa using hq) hchK₂ hndK₂
  rw [hlastK₂] at hdM
  have hMsome : ∀ v, (baseG G a b x y q).degree (some v) % 2 = (G.degree v + if v = x then 1 else 0) % 2 := by
    intro v
    have h1 : ((baseG G a b x y q).degree (some v) + (if some v = some y then 1 else 0) +
        (if some v = some a then 1 else 0)) % 2 = (midG G a b x y).degree (some v) % 2 :=
      hdM (some v)
    have h2 : (midG G a b x y).degree (some v) + (if some v = some y then 1 else 0) +
        (if some v = some x then 1 else 0) = (leafG G a b).degree (some v) := hdK₂ (some v)
    have h3 := hdK₁ v
    have h4 := hdG v
    simp only [Option.some.injEq] at h1 h2
    by_cases hva : v = a
    · subst hva
      simp only [hay, hax, hab', ite_true, ite_false, add_zero] at h1 h2 h3 h4 ⊢
      omega
    · by_cases hvb : v = b
      · subst hvb
        simp only [hby, hbx, hva, ite_true, ite_false, add_zero] at h1 h2 h3 h4 ⊢
        omega
      · by_cases hvx : v = x
        · subst hvx
          simp only [hxy', hva, hvb, ite_true, ite_false, add_zero] at h1 h2 h3 h4 ⊢
          omega
        · by_cases hvy : v = y
          · subst hvy
            simp only [hvx, hva, hvb, ite_true, ite_false, add_zero] at h1 h2 h3 h4 ⊢
            omega
          · simp only [hvx, hva, hvb, hvy, ite_false, add_zero] at h1 h2 h3 h4 ⊢
            omega
  have hMnone : (baseG G a b x y q).degree none % 2 = 1 := by
    have h1 : ((baseG G a b x y q).degree none + (if (none : Option W) = some y then 1 else 0) +
        (if (none : Option W) = some a then 1 else 0)) % 2 = (midG G a b x y).degree none % 2 :=
      hdM none
    have h2 : (midG G a b x y).degree none + (if (none : Option W) = some y then 1 else 0) +
        (if (none : Option W) = some x then 1 else 0) = (leafG G a b).degree none := hdK₂ none
    simp only [reduceCtorEq, ite_false, add_zero] at h1 h2
    rw [hdK₁none] at h2
    omega
  have hD₀some : ∀ v, D₀.ends (some v) = (G.degree v + if v = x then 1 else 0) % 2 := by
    intro v; rw [hD₀, hMsome]
  have hD₀none : D₀.ends none = 1 := by rw [hD₀, hMnone]
  have hdpos : ∀ v w, G.Adj v w → G.degree v % 2 = 1 := fun v w h =>
    hoddv v ((G.degree_pos_iff_exists_adj v).mpr ⟨w, h⟩)
  -- Step 1: the second leaf `ℓ₂ = none` at `y`
  have hD₀y : D₀.ends (some y) = 1 := by
    rw [hD₀some, if_neg (Ne.symm hxy'), add_zero]; exact hdpos y x hxy.symm
  obtain ⟨Py, hPy, hPyend⟩ := D₀.exists_end_of_pos (by rw [hD₀y]; omega)
  have hyPy : some y ∈ Py.walk.support := by
    rcases hPyend with h | h
    · rw [← h]; exact Py.walk.start_mem_support
    · rw [← h]; exact Py.walk.end_mem_support
  obtain ⟨D₃, hD₃some, hD₃none, hcov₃⟩ := D₀.liftLeaf hPy hPyend
  have hnotmap : ∀ (l : List (Option W)), (none : Option (Option W)) ∉ l.map some := by
    intro l h; rw [List.mem_map] at h; obtain ⟨_, _, h⟩ := h; exact Option.some_ne_none _ h
  have hSa₃ : Separates D₃ (some (some a)) (some none) := by
    intro Q' hQ' ⟨h1, h2⟩
    rcases hcov₃ Q' hQ' with h | ⟨Q, hQ, hs⟩
    · rcases h _ h1 with h1 | ⟨y₁, hy₁, e₁⟩
      · exact Option.some_ne_none _ h1
      rcases h _ h2 with h2 | ⟨y₂, hy₂, e₂⟩
      · exact Option.some_ne_none _ h2
      rw [Option.some.injEq] at e₁ e₂
      subst e₁; subst e₂
      exact hs2 Py hPy ⟨hy₁, hy₂⟩
    · rw [hs, List.mem_map] at h1 h2
      obtain ⟨_, ha, e₁⟩ := h1
      obtain ⟨_, hn, e₂⟩ := h2
      rw [Option.some.injEq] at e₁ e₂
      subst e₁; subst e₂
      exact hs2 Q hQ ⟨ha, hn⟩
  have hSx₃ : Separates D₃ (some (some x)) none := by
    intro Q' hQ' ⟨h1, h2⟩
    rcases hcov₃ Q' hQ' with h | ⟨Q, hQ, hs⟩
    · rcases h _ h1 with h1 | ⟨y₁, hy₁, e₁⟩
      · exact Option.some_ne_none _ h1
      rw [Option.some.injEq] at e₁
      subst e₁
      exact hs1 Py hPy ⟨hy₁, hyPy⟩
    · rw [hs] at h2; exact hnotmap _ h2
  have hSl₃ : Separates D₃ (some none) none := by
    intro Q' hQ' ⟨h1, h2⟩
    rcases hcov₃ Q' hQ' with h | ⟨Q, hQ, hs⟩
    · rcases h _ h1 with h1 | ⟨y₁, hy₁, e₁⟩
      · exact Option.some_ne_none _ h1
      rw [Option.some.injEq] at e₁
      subst e₁
      exact hs3 Py hPy ⟨hy₁, hyPy⟩
    · rw [hs] at h2; exact hnotmap _ h2
  -- Step 2: walk the end back along the chain, inside the two-leaf graph
  have hchH : ChainAdj (apex (midG G a b x y) {some y}) (((y :: q).map some).map some) :=
    chainAdj_map some (fun _ _ h => (apex_adj_some_some).mpr h) ((y :: q).map some) hchK₂
  have hndH : (((y :: q).map some).map some).Nodup := hndK₂.map (Option.some_injective _)
  have hmemmap : ∀ (L : List (Sym2 (Option W))) (r r' : Option W),
      s(some r, some r') ∈ L.map (Sym2.map some) ↔ s(r, r') ∈ L := by
    intro L r r'
    rw [List.mem_map]
    constructor
    · rintro ⟨e, he, h⟩
      rw [show s(some r, some r') = s(r, r').map some from rfl] at h
      rwa [Sym2.map.injective (Option.some_injective _) h] at he
    · intro h; exact ⟨_, h, rfl⟩
  have hnonemap : ∀ (L : List (Sym2 (Option W))) (z : Option (Option W)),
      s(none, z) ∉ L.map (Sym2.map some) := by
    intro L z h
    rw [List.mem_map] at h
    obtain ⟨e, -, he⟩ := h
    have : (none : Option (Option W)) ∈ e.map some := by rw [he]; exact Sym2.mem_mk_left _ _
    rw [Sym2.mem_map] at this
    obtain ⟨_, -, h⟩ := this
    exact Option.some_ne_none _ h
  have hK₀ : ∀ e, e ∈ (apex (baseG G a b x y q) {some y}).edgeSet ↔
      e ∈ (apex (midG G a b x y) {some y}).edgeSet ∧
        e ∉ chainEdges (((y :: q).map some).map some) := by
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
          exact ⟨fun h => ⟨h, hnonemap _ _⟩, fun h => h.1⟩
      | some c =>
        cases d with
        | none =>
          simp only [apex_adj_some_none]
          refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
          rw [Sym2.eq_swap]; exact hnonemap _ _
        | some d =>
          rw [apex_adj_some_some, apex_adj_some_some, hmemmap]
          exact delChain_adj _ _ c d
  have hinitH : initOf (some (some y)) ((q.map some).map some) = ((initOf y q).map some).map some := by
    rw [initOf_map, initOf_map]
  have hlastH : chainLast (some (some y)) ((q.map some).map some) = some (some a) := by
    rw [chainLast_map, chainLast_map, hlast]
  have hZH : ∀ t ∈ initOf (some (some y)) ((q.map some).map some), ∀ v,
      (apex (midG G a b x y) {some y}).Adj t v → v ≠ some (some y) → 1 ≤ D₃.ends v := by
    intro t ht v htv hvy
    rw [hinitH, List.map_map, List.mem_map] at ht
    obtain ⟨t', ht', rfl⟩ := ht
    cases v with
    | none => rw [hD₃none]
    | some v =>
      cases v with
      | none =>
        have := hD₃some none
        simp only [reduceCtorEq, ite_false, add_zero] at this
        rw [this, hD₀none]
      | some v =>
        have hadj : (midG G a b x y).Adj (some t') (some v) := (apex_adj_some_some).mp htv
        rw [hK₂adj] at hadj
        obtain ⟨hGtv, -, hne⟩ := hadj
        have hvy' : v ≠ y := fun h => hvy (by rw [h])
        have hvx : v ≠ x := by
          rintro rfl
          by_cases hty : t' = y
          · subst hty; exact hne rfl
          · exact hZ t' ht' hty hGtv
        have h1 := hD₃some (some v)
        rw [if_neg (fun h => hvy' (Option.some_injective _ h)), add_zero, hD₀some,
          if_neg hvx, add_zero, hdpos v t' hGtv.symm] at h1
        omega
  obtain ⟨D₄, hD₄e, hcov₄⟩ := walk_back (apex (midG G a b x y) {some y}) ((q.map some).map some)
    (some (some y)) (apex (baseG G a b x y q) {some y}) D₃ hchH hndH hK₀ hZH
  rw [hlastH] at hD₄e
  -- separations survive: the targets are vertices `some (some t)` of the chain other than `a`
  have hTa : some (some a) ∉ initOf (some (some y)) ((q.map some).map some) := by
    rw [← hlastH]
    exact chainLast_not_mem_initOf _ _ hndH
  have hTx : some (some x) ∉ initOf (some (some y)) ((q.map some).map some) := by
    rw [hinitH, List.map_map, List.mem_map]
    rintro ⟨t, ht, h⟩
    simp only [Function.comp_apply, Option.some.injEq] at h
    subst h
    exact hxq (mem_initOf_mem y q ht)
  have hTn : (none : Option (Option W)) ∉ initOf (some (some y)) ((q.map some).map some) := by
    rw [hinitH]; exact hnotmap _
  have hTsn : (some none : Option (Option W)) ∉
      initOf (some (some y)) ((q.map some).map some) := by
    rw [hinitH, List.mem_map]
    rintro ⟨t, ht, h⟩
    rw [Option.some.injEq] at h
    subst h
    rw [List.mem_map] at ht
    obtain ⟨_, _, h⟩ := ht
    exact Option.some_ne_none _ h
  have hSa₄ : Separates D₄ (some (some a)) (some none) :=
    separates_of_cover_list hTa hTsn hSa₃ hcov₄
  have hSx₄ : Separates D₄ (some (some x)) none := separates_of_cover_list hTx hTn hSx₃ hcov₄
  have hSl₄ : Separates D₄ (some none) none := separates_of_cover_list hTsn hTn hSl₃ hcov₄
  -- end counts of `D₄`
  have hD₄ss : ∀ v, D₄.ends (some (some v)) + (if v = a then 1 else 0) =
      (G.degree v + if v = x then 1 else 0) % 2 := by
    intro v
    have h1 := hD₄e (some (some v))
    have h2 := hD₃some (some v)
    rw [hD₀some] at h2
    simp only [Option.some.injEq] at h1 h2
    by_cases hvy : v = y
    · subst hvy
      simp only [ite_true, Ne.symm hay, Ne.symm hxy', ite_false, add_zero] at h1 h2 ⊢
      omega
    · simp only [hvy, ite_false, add_zero] at h1 h2
      omega
  have hD₄sn : D₄.ends (some none) = 1 := by
    have h1 := hD₄e (some none)
    have h2 := hD₃some none
    simp only [Option.some.injEq, reduceCtorEq, ite_false, add_zero] at h1 h2
    rw [h1, h2, hD₀none]
  have hD₄n : D₄.ends none = 1 := by
    have h1 := hD₄e none
    simp only [reduceCtorEq, ite_false, add_zero] at h1
    rw [h1, hD₃none]
  -- Step 3: merge `ℓ₂` into `x`, then `ℓ₁` into `a`
  obtain ⟨D₅, hD₅x, hD₅w, hback₅, hfwd₅⟩ := leaf_merge (leafG G a b) hK₁yx.symm D₄ hSx₄
  have hS₅ : Separates D₅ (some a) none := by
    intro Q hQ ⟨h1, h2⟩
    obtain ⟨P, hP, hs⟩ := hback₅ Q hQ
    rw [hs, List.mem_map] at h1 h2
    obtain ⟨z₁, hz₁, e₁⟩ := h1
    obtain ⟨z₂, hz₂, e₂⟩ := h2
    rw [mergeMap_eq_iff] at e₁ e₂
    rcases e₁ with rfl | ⟨-, h⟩
    · rcases e₂ with rfl | ⟨-, h⟩
      · exact hSa₄ P hP ⟨hz₁, hz₂⟩
      · exact Option.some_ne_none _ h.symm
    · exact hax (Option.some_injective _ h)
  obtain ⟨D₆, hD₆a, hD₆w, -, hfwd₆⟩ := leaf_merge G hab D₅ hS₅
  -- end counts of `D₆`
  have hD₅some : ∀ v, v ≠ x → D₅.ends (some v) = D₄.ends (some (some v)) := fun v hv =>
    hD₅w (some v) (fun h => hv (Option.some_injective _ h))
  have hD₅none : D₅.ends none = 1 := by
    rw [hD₅w none (by simp), hD₄sn]
  have hD₆ : ∀ v, D₆.ends v = G.degree v % 2 := by
    intro v
    by_cases hva : v = a
    · subst hva
      rw [hD₆a, hD₅some v hax, hD₅none]
      have := hD₄ss v
      simp only [ite_true, hax, ite_false, add_zero] at this
      have := hdpos v b hab
      omega
    · rw [hD₆w v hva]
      by_cases hvx : v = x
      · subst hvx
        rw [hD₅x, hD₄n]
        have := hD₄ss v
        simp only [hva, ite_true, ite_false, add_zero] at this
        have := hdpos v y hxy
        omega
      · rw [hD₅some v hvx]
        have := hD₄ss v
        simp only [hva, hvx, ite_false, add_zero] at this
        exact this
  -- Step 4: the two terminal paths
  have hleaf : ∀ {T : Type u} [DecidableEq T] {K : SimpleGraph T} {r : T} {D : PathDecomp (apex K {r})}
      {P : GPath (apex K {r})}, P ∈ D.paths → (P.src = none ∨ P.tgt = none) →
      s(some r, none) ∈ P.edges := by
    intro T _ K r D P _ hPend
    have key : ∀ e ∈ P.edges, (none : Option T) ∈ e → s(some r, none) ∈ P.edges := by
      intro e he hne
      have heH := P.walk.edges_subset_edgeSet he
      rw [apex_none_pendant e heH hne, Sym2.eq_swap] at he
      exact he
    rcases hPend with h | h
    · obtain ⟨e, he, hx⟩ := P.exists_edge_at_src
      exact key e he (h ▸ hx)
    · obtain ⟨e, he, hx⟩ := P.exists_edge_at_tgt
      exact key e he (h ▸ hx)
  -- the path through `ℓ₁` becomes the path ending at `a` through `ab`
  obtain ⟨R₁, hR₁, hR₁end⟩ := D₅.exists_end_of_pos (by rw [hD₅none]; omega)
  obtain ⟨Q₁, hQ₁, hQ₁s, hQ₁t, hQ₁e⟩ := hfwd₆ R₁ hR₁
  -- the path through `ℓ₂` becomes the path ending at `x` through `xy`
  obtain ⟨R₂', hR₂', hR₂'end⟩ := D₄.exists_end_of_pos (by rw [hD₄n]; omega)
  obtain ⟨R₂, hR₂, hR₂s, hR₂t, hR₂e⟩ := hfwd₅ R₂' hR₂'
  obtain ⟨Q₂, hQ₂, hQ₂s, hQ₂t, hQ₂e⟩ := hfwd₆ R₂ hR₂
  have hQ₁end : Q₁.src = a ∨ Q₁.tgt = a := by
    rcases hR₁end with h | h
    · left; rw [hQ₁s, h, mergeMap_none]
    · right; rw [hQ₁t, h, mergeMap_none]
  have hQ₁ab : s(b, a) ∈ Q₁.edges := by
    rw [hQ₁e, List.mem_map]
    exact ⟨_, hleaf hR₁ hR₁end, by simp [Sym2.map_mk]⟩
  have hQ₂end : Q₂.src = x ∨ Q₂.tgt = x := by
    rcases hR₂'end with h | h
    · left; rw [hQ₂s, hR₂s, h, mergeMap_none, mergeMap_some]
    · right; rw [hQ₂t, hR₂t, h, mergeMap_none, mergeMap_some]
  have hR₂yx : s(some y, some x) ∈ R₂.edges := by
    rw [hR₂e, List.mem_map]
    exact ⟨_, hleaf hR₂' hR₂'end, by simp [Sym2.map_mk]⟩
  have hQ₂xy : s(y, x) ∈ Q₂.edges := by
    rw [hQ₂e, List.mem_map]
    exact ⟨_, hR₂yx, by simp [Sym2.map_mk]⟩
  -- the two paths differ: otherwise the leaf path of `ℓ₂` would contain `ℓ₁`
  have hne : Q₁ ≠ Q₂ := by
    intro hQ
    rw [hQ, hQ₂e, List.mem_map] at hQ₁ab
    obtain ⟨e, he, hemap⟩ := hQ₁ab
    have hnone : (none : Option W) ∈ e := by
      have heH : e ∈ (leafG G a b).edgeSet := R₂.walk.edges_subset_edgeSet he
      induction e using Sym2.inductionOn with
      | hf c d =>
        cases c with
        | none => exact Sym2.mem_mk_left _ _
        | some c =>
          cases d with
          | none => exact Sym2.mem_mk_right _ _
          | some d =>
            exfalso
            rw [mem_edgeSet, apex_adj_some_some] at heH
            simp only [Sym2.map_mk, mergeMap_some] at hemap
            exact heH.2 hemap
    rw [hR₂e, List.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    rw [Sym2.mem_map] at hnone
    obtain ⟨z, hz, hzn⟩ := hnone
    rw [mergeMap_eq_iff] at hzn
    rcases hzn with rfl | ⟨-, h⟩
    · have hsn : (some none : Option (Option W)) ∈ R₂'.walk.support := by
        induction e' using Sym2.inductionOn with
        | hf c d =>
          rcases Sym2.mem_iff.mp hz with rfl | rfl
          · exact R₂'.walk.fst_mem_support_of_mem_edges he'
          · exact R₂'.walk.snd_mem_support_of_mem_edges he'
      have hn : (none : Option (Option W)) ∈ R₂'.walk.support := by
        rcases hR₂'end with h | h
        · rw [← h]; exact R₂'.walk.start_mem_support
        · rw [← h]; exact R₂'.walk.end_mem_support
      exact hSl₄ R₂' hR₂' ⟨hsn, hn⟩
    · exact Option.some_ne_none _ h.symm
  exact ⟨D₆, hD₆, Q₁, hQ₁, Q₂, hQ₂, hne, hQ₁end, by rw [Sym2.eq_swap]; exact hQ₁ab, hQ₂end,
    by rw [Sym2.eq_swap]; exact hQ₂xy⟩

/-- `ab` is terminal at `a`, `xy` is terminal at `x`, on two different paths of a Lovász
decomposition of `G`. -/
def PTM2At (G : SimpleGraph W) [DecidableRel G.Adj] (a b x y : W) : Prop :=
  ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
    ∃ P₁ ∈ D.paths, ∃ P₂ ∈ D.paths, P₁ ≠ P₂ ∧ (P₁.src = a ∨ P₁.tgt = a) ∧
      s(a, b) ∈ P₁.edges ∧ (P₂.src = x ∨ P₂.tgt = x) ∧ s(x, y) ∈ P₂.edges

omit [Fintype W] in
theorem separates_of_meetsOnce {K : SimpleGraph W} {D : PathDecomp K} {c d : W} (hcd : c ≠ d)
    (h : MeetsOnce D {c, d}) : Separates D c d := fun P hP ⟨hc, hd⟩ =>
  hcd (h P hP c (Finset.mem_insert_self _ _) d (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    hc hd)

/-- The four special vertices of the base graph. -/
abbrev baseX (a x y : W) : Finset (Option W) := {some x, some y, some a, none}

/-- The three pairs to be separated in the base graph. -/
abbrev baseFam (a x y : W) : Finset (Finset (Option W)) :=
  {{some x, some y}, {some a, none}, {none, some y}}

/-- **The walk theorem, sparse form.** The base hypothesis of `ptm2_of_base` holds when the four
special vertices `x, y, a, ℓ₁` are sparse in the base graph, possibly after deleting one edge
`x v` with `v` not special. -/
theorem ptm2_of_sparse (G : SimpleGraph W) [DecidableRel G.Adj] (hodd : ∀ v, v ∉ evenSet G)
    {a b x y : W} (hab : G.Adj a b) (hxy : G.Adj x y)
    (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y)
    (q : List W) (hlast : chainLast y q = a)
    (hch : ChainAdj G (y :: q)) (hnd : (y :: q).Nodup) (hbq : b ∉ y :: q) (hxq : x ∉ y :: q)
    (hZ : ∀ t ∈ initOf y q, t ≠ y → ¬ G.Adj t x)
    (hsp : SparseFam (baseG G a b x y q) (baseX a x y) (baseFam a x y) ∨
      ∃ v, (baseG G a b x y q).Adj (some x) v ∧ v ∉ baseX a x y ∧
        SparseFam (delEdge (baseG G a b x y q) (some x) v) (baseX a x y) (baseFam a x y)) :
    PTM2At G a b x y := by
  classical
  have hxy' : x ≠ y := hxy.ne
  obtain ⟨hMsome, hMnone⟩ := baseG_parity G hodd hab hxy hax hay hbx hby q hlast hch hnd hbq hxq
  have hoddv : ∀ v w, G.Adj v w → G.degree v % 2 = 1 := by
    intro v w h
    have := hodd v
    rw [mem_evenSet_iff] at this
    have : 0 < G.degree v := (G.degree_pos_iff_exists_adj v).mpr ⟨w, h⟩
    omega
  have hev : ∀ w ∈ evenSet (baseG G a b x y q), w = some x := by
    intro w hw
    rw [mem_evenSet_iff] at hw
    cases w with
    | none => rw [hMnone] at hw; omega
    | some v =>
      by_cases hvx : v = x
      · rw [hvx]
      · exfalso
        obtain ⟨z, hz⟩ := ((baseG G a b x y q).degree_pos_iff_exists_adj (some v)).mp hw.1
        have hGv : G.degree v % 2 = 1 := by
          rcases baseG_adj_some G q hz with ⟨-, rfl⟩ | ⟨w, -, h⟩
          · exact hoddv v a hab.symm
          · exact hoddv v w h
        have := hMsome v
        rw [if_neg hvx, add_zero, hGv] at this
        omega
  have hcard : (evenSet (baseG G a b x y q)).card ≤ 1 :=
    Finset.card_le_one.mpr fun w₁ h₁ w₂ h₂ => (hev w₁ h₁).trans (hev w₂ h₂).symm
  have hgx : (baseG G a b x y q).degree (some x) % 2 = 0 := by
    rw [hMsome, if_pos rfl]; have := hoddv x y hxy; omega
  obtain ⟨D₀, hD₀, hmeet⟩ : ∃ D₀ : PathDecomp (baseG G a b x y q),
      (∀ v, D₀.ends v = (baseG G a b x y q).degree v % 2) ∧
        ∀ A ∈ baseFam a x y, MeetsOnce D₀ A := by
    rcases hsp with h | ⟨v, hxv, hvX, h⟩
    · exact separation_sparse _ hcard h
    · exact sep_sparse_fix _ hev hgx hxv h hvX
  have hs1 : Separates D₀ (some x) (some y) :=
    separates_of_meetsOnce (by simpa using hxy') (hmeet _ (by simp))
  have hs2 : Separates D₀ (some a) none :=
    separates_of_meetsOnce (by simp) (hmeet _ (by simp))
  have hs3 : Separates D₀ none (some y) :=
    separates_of_meetsOnce (by simp) (hmeet _ (by simp))
  exact ptm2_of_base G hodd hab hxy hax hay hbx hby q hlast hch hnd hbq hxq hZ D₀ hD₀ hs1 hs2 hs3

end main

end Gallai
