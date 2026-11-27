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

**Sparse form** (`sep_sparse_fix`, `ptm2_of_sparse`): the hypothesis on `M` follows from
`separation_sparse` when the four vertices `x, y, a, ℓ₁` are sparse and the three pairs packed,
in `M` or in `M − xv` for one neighbour `v` of `x` (one more Fan transfer restores `xv`).

**Girth five** (`ptm2_girth5`): with no triangle and no 4-cycle, a shortest path between the two
edges is an admissible walk satisfying the sparse hypotheses.

**STL** (`swapG`, `liftJ`, `unlift`, `stl_of_ptm2`, `stl_of_girth5`, `test1_of_girth5`): for `z`
of degree four with `N(z) = {a, b, c, d}` and `ab, cd ∉ E(J)`, PTM₂ in `(J − z) + ab + cd` gives
`STL J z b` and `STL J z d`; at girth five every neighbour, and `Test1 J z` by `test1_of_stl`.
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
      rw [ite_eq_right h1, ite_eq_right h2] at this
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

/-! ### Walks as chains, and adjacency in the base graph -/

section walks

variable {W : Type u} {G : SimpleGraph W}

theorem walk_support_eq_cons {u v : W} (p : G.Walk u v) : p.support = u :: p.support.tail := by
  cases p <;> rfl

theorem chainLast_walk : ∀ {u v : W} (p : G.Walk u v), chainLast u p.support.tail = v
  | _, _, .nil => rfl
  | _, _, .cons _ p => by
      simp only [Walk.support_cons, List.tail_cons]
      rw [walk_support_eq_cons p]
      exact chainLast_walk p

theorem chainAdj_walk : ∀ {u v : W} (p : G.Walk u v), ChainAdj G p.support
  | _, _, .nil => trivial
  | _, _, .cons h p => by
      rw [Walk.support_cons, walk_support_eq_cons p]
      exact ⟨h, by rw [← walk_support_eq_cons p]; exact chainAdj_walk p⟩

end walks


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


omit [Fintype W] in
theorem mem_chainEdges_map_some {L : List W} {c d : W} :
    s(some c, some d) ∈ chainEdges (L.map some) ↔ s(c, d) ∈ chainEdges L := by
  rw [chainEdges_map, List.mem_map]
  constructor
  · rintro ⟨e, he, h⟩
    rw [show s(some c, some d) = s(c, d).map some from rfl] at h
    rwa [Sym2.map.injective (Option.some_injective _) h] at he
  · intro h; exact ⟨_, h, rfl⟩

omit [Fintype W] in
theorem baseG_adj_none (G : SimpleGraph W) {a b x y : W} (q : List W) (z : Option W) :
    (baseG G a b x y q).Adj none z ↔ z = some b := by
  rw [baseG, delChain_adj]
  constructor
  · rintro ⟨⟨h, -⟩, -⟩
    cases z with
    | none => exact absurd h apex_not_adj_none_none
    | some r => rw [apex_adj_none_some, Finset.mem_singleton] at h; rw [h]
  · rintro rfl
    refine ⟨⟨by simp, by simp⟩, fun h => ?_⟩
    have := mem_of_mem_chainEdges _ h none (Sym2.mem_mk_left _ _)
    rw [List.mem_map] at this
    obtain ⟨_, _, h⟩ := this
    exact Option.some_ne_none _ h

omit [Fintype W] in
theorem baseG_adj_some_some (G : SimpleGraph W) {a b x y : W} (q : List W) (u w : W) :
    (baseG G a b x y q).Adj (some u) (some w) ↔
      G.Adj u w ∧ s(u, w) ≠ s(b, a) ∧ s(u, w) ≠ s(y, x) ∧ s(u, w) ∉ chainEdges (y :: q) := by
  rw [baseG, delChain_adj, mem_chainEdges_map_some]
  show ((apex (delEdge G b a) {b}).Adj (some u) (some w) ∧ ¬ s(some u, some w) = s(some y, some x))
    ∧ _ ↔ _
  rw [apex_adj_some_some]
  have : s(some u, some w) = s(some y, some x) ↔ s(u, w) = s(y, x) := by
    rw [show s(some u, some w) = s(u, w).map some from rfl,
      show s(some y, some x) = s(y, x).map some from rfl]
    exact (Sym2.map.injective (Option.some_injective _)).eq_iff
  rw [this]
  show ((G.Adj u w ∧ ¬ s(u, w) = s(b, a)) ∧ ¬ s(u, w) = s(y, x)) ∧ _ ↔ _
  tauto


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
    rw [hD₀some, ite_eq_right (Ne.symm hxy'), add_zero]; exact hdpos y x hxy.symm
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
        rw [ite_eq_right (fun h => hvy' (Option.some_injective _ h)), add_zero, hD₀some,
          ite_eq_right hvx, add_zero, hdpos v t' hGtv.symm] at h1
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
        rw [ite_eq_right hvx, add_zero, hGv] at this
        omega
  have hcard : (evenSet (baseG G a b x y q)).card ≤ 1 :=
    Finset.card_le_one.mpr fun w₁ h₁ w₂ h₂ => (hev w₁ h₁).trans (hev w₂ h₂).symm
  have hgx : (baseG G a b x y q).degree (some x) % 2 = 0 := by
    rw [hMsome, ite_eq_left rfl]; have := hoddv x y hxy; omega
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

/-! ### Girth at least five -/

section girth

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- No triangles. -/
def NoTriangle (G : SimpleGraph W) : Prop := ∀ u v w, G.Adj u v → G.Adj v w → G.Adj w u → False

/-- No four-cycles. -/
def NoSquare (G : SimpleGraph W) : Prop :=
  ∀ u v w t, G.Adj u v → G.Adj v w → G.Adj w t → G.Adj t u → u ≠ w → v ≠ t → False

/-- No triangle and no four-cycle passes through a vertex of `S` (local girth five at `S`). -/
def NoShortCycleAt (G : SimpleGraph W) (S : W → Prop) : Prop :=
  (∀ u v w, S u → G.Adj u v → G.Adj v w → G.Adj w u → False) ∧
  (∀ u v w t, S u → G.Adj u v → G.Adj v w → G.Adj w t → G.Adj t u → u ≠ w → v ≠ t → False)

theorem NoShortCycleAt.mono {G : SimpleGraph W} {S T : W → Prop} (h : NoShortCycleAt G S)
    (hTS : ∀ v, T v → S v) : NoShortCycleAt G T :=
  ⟨fun u v w hu => h.1 u v w (hTS u hu), fun u v w t hu => h.2 u v w t (hTS u hu)⟩

theorem noShortCycleAt_of_girth {G : SimpleGraph W} (h3 : NoTriangle G) (h4 : NoSquare G)
    (S : W → Prop) : NoShortCycleAt G S :=
  ⟨fun u v w _ => h3 u v w, fun u v w t _ => h4 u v w t⟩

omit [Fintype W] in
/-- A path of length one or two, read off. -/
theorem walk_len_one {G : SimpleGraph W} {u v : W} (p : G.Walk u v) (h : p.length = 1) :
    p.support.tail = [v] := by
  cases p with
  | nil => simp at h
  | cons _ p' =>
    cases p' with
    | nil => rfl
    | cons _ p'' => simp at h

omit [Fintype W] in
theorem walk_len_two {G : SimpleGraph W} {u v : W} (p : G.Walk u v) (h : p.length = 2) :
    ∃ m, G.Adj u m ∧ G.Adj m v ∧ p.support.tail = [m, v] := by
  cases p with
  | nil => simp at h
  | cons h₁ p' =>
    cases p' with
    | nil => simp at h
    | cons h₂ p'' =>
      cases p'' with
      | nil => exact ⟨_, h₁, h₂, rfl⟩
      | cons _ _ => simp at h

/-- **Core of the girth theorem.** Let `p` be a shortest walk between the edges `ab` and `xy`,
running from `y` to `a`. If no triangle and no four-cycle passes through `a`, `b`, `x` or `y`, the
walk theorem applies with short ends `a` and `x`. -/
theorem ptm2_girth_core (G : SimpleGraph W) [DecidableRel G.Adj] (hodd : ∀ v, v ∉ evenSet G)
    {a b x y : W} (hS : NoShortCycleAt G (fun v => v = a ∨ v = b ∨ v = x ∨ v = y))
    (hab : G.Adj a b) (hxy : G.Adj x y)
    (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y)
    (p : G.Walk y a) (hp : p.IsPath)
    (hmin : ∀ u w, (u = a ∨ u = b) → (w = x ∨ w = y) → ∀ r : G.Walk w u, p.length ≤ r.length) :
    PTM2At G a b x y := by
  classical
  have h3 := hS.1
  have h4 := hS.2
  have hab' : a ≠ b := hab.ne
  have hxy' : x ≠ y := hxy.ne
  set q := p.support.tail with hq
  have hsupp : p.support = y :: q := walk_support_eq_cons p
  have hlast : chainLast y q = a := chainLast_walk p
  have hch : ChainAdj G (y :: q) := hsupp ▸ chainAdj_walk p
  have hnd : (y :: q).Nodup := hsupp ▸ hp.support_nodup
  have hlen : 1 ≤ p.length := by
    by_contra h
    exact hay (Walk.eq_of_length_eq_zero (by omega : p.length = 0)).symm
  -- lengths of the two pieces at a vertex of the walk
  have hsplit : ∀ t (ht : t ∈ p.support),
      (p.takeUntil t ht).length + (p.dropUntil t ht).length = p.length := by
    intro t ht
    rw [← Walk.length_append, Walk.take_spec]
  have hpos : ∀ {c d : W} (r : G.Walk c d), c ≠ d → 1 ≤ r.length := by
    intro c d r hcd
    by_contra h
    exact hcd (Walk.eq_of_length_eq_zero (by omega : r.length = 0))
  have hbq : b ∉ y :: q := by
    rw [← hsupp]; intro hb
    have h1 := hmin b y (Or.inr rfl) (Or.inr rfl) (p.takeUntil b hb)
    have h2 := hpos (p.dropUntil b hb) (Ne.symm hab')
    have := hsplit b hb
    omega
  have hxq : x ∉ y :: q := by
    rw [← hsupp]; intro hx
    have h1 := hmin a x (Or.inl rfl) (Or.inl rfl) (p.dropUntil x hx)
    have h2 := hpos (p.takeUntil x hx) (Ne.symm hxy')
    have := hsplit x hx
    omega
  have hZ : ∀ t ∈ initOf y q, t ≠ y → ¬ G.Adj t x := by
    intro t ht hty htx
    have ht' : t ∈ p.support := by rw [hsupp]; exact mem_initOf_mem y q ht
    have h1 := hmin a x (Or.inl rfl) (Or.inl rfl) (Walk.cons htx.symm (p.dropUntil t ht'))
    rw [Walk.length_cons] at h1
    have h2 := hpos (p.takeUntil t ht') (Ne.symm hty)
    have := hsplit t ht'
    have h1' : (p.takeUntil t ht').length = 1 := by omega
    exact h3 x y t (Or.inr (Or.inr (Or.inl rfl))) hxy (Walk.adj_of_length_eq_one h1') htx
  -- short distances
  have hlen1 : ∀ {c d : W}, G.Adj c d → (d = a ∨ d = b) → (c = x ∨ c = y) → p.length = 1 := by
    intro c d hcd hd hc
    have := hmin d c hd hc (Walk.cons hcd Walk.nil)
    simp only [Walk.length_cons, Walk.length_nil] at this
    omega
  have hya1 : p.length = 1 → G.Adj y a := fun h => Walk.adj_of_length_eq_one h
  have hbx' : ¬ G.Adj b x := by
    intro h
    exact h4 a y x b (Or.inl rfl) (hya1 (hlen1 h.symm (Or.inr rfl) (Or.inl rfl))).symm hxy.symm h.symm hab.symm
      hax (Ne.symm hby)
  have hby' : ¬ G.Adj b y := by
    intro h
    exact h3 a b y (Or.inl rfl) hab h (hya1 (hlen1 h.symm (Or.inr rfl) (Or.inr rfl)))
  have hya_chain : G.Adj y a → s(y, a) ∈ chainEdges (y :: q) := by
    intro h
    have h1 := hlen1 h (Or.inl rfl) (Or.inr rfl)
    have : q = [a] := walk_len_one p h1
    rw [this]; simp [chainEdges]
  have hxy_common : ∀ u, G.Adj u x → G.Adj u y → False := fun u h1 h2 =>
    h3 x y u (Or.inr (Or.inr (Or.inl rfl))) hxy h2.symm h1
  have hxa_common : ∀ u u', G.Adj u x → G.Adj u a → G.Adj u' x → G.Adj u' a → u = u' := by
    intro u u' h1 h2 h1' h2'
    by_contra hne
    exact h4 x u a u' (Or.inr (Or.inr (Or.inl rfl))) h1.symm h2 h2'.symm h1' hax.symm hne
  have hya_common : ∀ u, G.Adj u y → G.Adj u a → s(u, a) ∉ chainEdges (y :: q) → False := by
    intro u h1 h2 hch2
    have hle := hmin a y (Or.inl rfl) (Or.inr rfl) (Walk.cons h1.symm (Walk.cons h2 Walk.nil))
    simp only [Walk.length_cons, Walk.length_nil] at hle
    by_cases h1' : p.length = 1
    · exact h3 y a u (Or.inr (Or.inr (Or.inr rfl))) (hya1 h1') h2.symm h1
    · obtain ⟨m, hym, hma, hq2⟩ := walk_len_two p (by omega)
      by_cases hum : u = m
      · subst hum
        apply hch2
        have : q = [u, a] := hq2
        rw [this]; simp [chainEdges]
      · exact h4 y u a m (Or.inr (Or.inr (Or.inr rfl))) h1.symm h2 hma.symm hym.symm hay.symm hum
  -- adjacency facts in the base graph `M`
  have hNs : ∀ u, (baseG G a b x y q).Adj (some u) none → u = b := by
    intro u h
    have := (baseG_adj_none G (a := a) (b := b) (x := x) (y := y) q (some u)).mp h.symm
    exact Option.some_injective _ this
  have hSS := baseG_adj_some_some G (a := a) (b := b) (x := x) (y := y) q
  have F_xy : ∀ u, (baseG G a b x y q).Adj (some u) (some x) →
      (baseG G a b x y q).Adj (some u) (some y) → False := fun u h1 h2 =>
    hxy_common u ((hSS u x).mp h1).1 ((hSS u y).mp h2).1
  have F_ya : ∀ u, (baseG G a b x y q).Adj (some u) (some y) →
      (baseG G a b x y q).Adj (some u) (some a) → False := fun u h1 h2 =>
    hya_common u ((hSS u y).mp h1).1 ((hSS u a).mp h2).1 ((hSS u a).mp h2).2.2.2
  have F_bx : ¬ (baseG G a b x y q).Adj (some b) (some x) := fun h => hbx' ((hSS b x).mp h).1
  have F_by : ¬ (baseG G a b x y q).Adj (some b) (some y) := fun h => hby' ((hSS b y).mp h).1
  have F_ba : ¬ (baseG G a b x y q).Adj (some b) (some a) := fun h => ((hSS b a).mp h).2.1 rfl
  have F_xy' : ¬ (baseG G a b x y q).Adj (some x) (some y) := fun h =>
    ((hSS x y).mp h).2.2.1 (Sym2.eq_swap)
  have F_nn : ¬ (baseG G a b x y q).Adj none none := fun h => by
    have := (baseG_adj_none G (a := a) (b := b) (x := x) (y := y) q none).mp h
    exact absurd this (by simp)
  -- sparseness for every subgraph of `M` without a common neighbour of `x` and `a`
  have hsparse : ∀ M' : SimpleGraph (Option W), (∀ c d, M'.Adj c d → (baseG G a b x y q).Adj c d) →
      (∀ u, M'.Adj (some u) (some x) → M'.Adj (some u) (some a) → False) →
      SparseFam M' (baseX a x y) (baseFam a x y) := by
    intro M' hle hxa
    refine ⟨?_, ?_, ?_⟩
    · intro A hA
      simp only [baseFam, Finset.mem_insert, Finset.mem_singleton] at hA
      rcases hA with rfl | rfl | rfl
      · intro c hc d hd hcd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc hd
        rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
        · exact absurd rfl hcd
        · refine ⟨fun h => F_xy' (hle _ _ h), fun w ⟨h1, h2⟩ => ?_⟩
          cases w with
          | none => exact hbx (hNs x (hle _ _ h1)).symm
          | some u => exact F_xy u (hle _ _ h1).symm (hle _ _ h2)
        · refine ⟨fun h => F_xy' (hle _ _ h).symm, fun w ⟨h1, h2⟩ => ?_⟩
          cases w with
          | none => exact hbx (hNs x (hle _ _ h2).symm).symm
          | some u => exact F_xy u (hle _ _ h2) (hle _ _ h1).symm
        · exact absurd rfl hcd
      · intro c hc d hd hcd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc hd
        rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
        · exact absurd rfl hcd
        · refine ⟨fun h => hab' (hNs a (hle _ _ h)), fun w ⟨h1, h2⟩ => ?_⟩
          cases w with
          | none => exact F_nn (hle _ _ h2)
          | some u => obtain rfl := hNs u (hle _ _ h2); exact F_ba (hle _ _ h1).symm
        · refine ⟨fun h => hab' (hNs a (hle _ _ h).symm), fun w ⟨h1, h2⟩ => ?_⟩
          cases w with
          | none => exact F_nn (hle _ _ h1)
          | some u => obtain rfl := hNs u (hle _ _ h1).symm; exact F_ba (hle _ _ h2)
        · exact absurd rfl hcd
      · intro c hc d hd hcd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc hd
        rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
        · exact absurd rfl hcd
        · refine ⟨fun h => hby (hNs y (hle _ _ h).symm).symm, fun w ⟨h1, h2⟩ => ?_⟩
          cases w with
          | none => exact F_nn (hle _ _ h1)
          | some u => obtain rfl := hNs u (hle _ _ h1).symm; exact F_by (hle _ _ h2)
        · refine ⟨fun h => hby (hNs y (hle _ _ h)).symm, fun w ⟨h1, h2⟩ => ?_⟩
          cases w with
          | none => exact F_nn (hle _ _ h2)
          | some u => obtain rfl := hNs u (hle _ _ h2); exact F_by (hle _ _ h1).symm
        · exact absurd rfl hcd
    · intro A hA z hz
      simp only [baseFam, Finset.mem_insert, Finset.mem_singleton] at hA
      rcases hA with rfl | rfl | rfl <;>
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz <;>
        rcases hz with rfl | rfl <;> simp [baseX]
    · intro v c d hvc hvd hc hd
      simp only [baseX, Finset.mem_insert, Finset.mem_singleton] at hc hd
      cases v with
      | none =>
        have h1 := (baseG_adj_none G (a := a) (b := b) (x := x) (y := y) q c).mp (hle _ _ hvc)
        have h2 := (baseG_adj_none G (a := a) (b := b) (x := x) (y := y) q d).mp (hle _ _ hvd)
        rw [h1, h2]
      | some u =>
        rcases hc with rfl | rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl | rfl
        · rfl
        · exact (F_xy u (hle _ _ hvc) (hle _ _ hvd)).elim
        · exact (hxa u hvc hvd).elim
        · obtain rfl := hNs u (hle _ _ hvd); exact (F_bx (hle _ _ hvc)).elim
        · exact (F_xy u (hle _ _ hvd) (hle _ _ hvc)).elim
        · rfl
        · exact (F_ya u (hle _ _ hvc) (hle _ _ hvd)).elim
        · obtain rfl := hNs u (hle _ _ hvd); exact (F_by (hle _ _ hvc)).elim
        · exact (hxa u hvd hvc).elim
        · exact (F_ya u (hle _ _ hvd) (hle _ _ hvc)).elim
        · rfl
        · obtain rfl := hNs u (hle _ _ hvd); exact (F_ba (hle _ _ hvc)).elim
        · obtain rfl := hNs u (hle _ _ hvc); exact (F_bx (hle _ _ hvd)).elim
        · obtain rfl := hNs u (hle _ _ hvc); exact (F_by (hle _ _ hvd)).elim
        · obtain rfl := hNs u (hle _ _ hvc); exact (F_ba (hle _ _ hvd)).elim
        · rfl
  have hsp : SparseFam (baseG G a b x y q) (baseX a x y) (baseFam a x y) ∨
      ∃ v, (baseG G a b x y q).Adj (some x) v ∧ v ∉ baseX a x y ∧
        SparseFam (delEdge (baseG G a b x y q) (some x) v) (baseX a x y) (baseFam a x y) := by
    by_cases hbad : ∃ u, (baseG G a b x y q).Adj (some u) (some x) ∧
        (baseG G a b x y q).Adj (some u) (some a)
    · obtain ⟨u₀, hu₀x, hu₀a⟩ := hbad
      right
      refine ⟨some u₀, hu₀x.symm, ?_, hsparse _ (fun c d h => h.1) ?_⟩
      · have hx' := ((hSS u₀ x).mp hu₀x).1
        have ha' := (hSS u₀ a).mp hu₀a
        simp only [baseX, Finset.mem_insert, Finset.mem_singleton, Option.some.injEq,
          reduceCtorEq, or_false, not_or]
        refine ⟨hx'.ne, fun h => ?_, ha'.1.ne⟩
        subst h
        exact ha'.2.2.2 (hya_chain ha'.1)
      · intro u h1 h2
        have hu : u ≠ u₀ := by
          rintro rfl
          exact h1.2 (Sym2.eq_swap)
        exact hu (hxa_common u u₀ ((hSS u x).mp h1.1).1 ((hSS u a).mp h2.1).1
          ((hSS u₀ x).mp hu₀x).1 ((hSS u₀ a).mp hu₀a).1)
    · left
      exact hsparse _ (fun _ _ h => h) (fun u h1 h2 => hbad ⟨u, h1, h2⟩)
  exact ptm2_of_sparse G hodd hab hxy hax hay hbx hby q hlast hch hnd hbq hxq hZ hsp

omit [Fintype W] in
theorem PTM2At.symm {G : SimpleGraph W} [DecidableRel G.Adj] {a b x y : W} [Fintype W]
    (h : PTM2At G a b x y) : PTM2At G x y a b := by
  obtain ⟨D, hD, P₁, hP₁, P₂, hP₂, hne, h1, h2, h3, h4⟩ := h
  exact ⟨D, hD, P₂, hP₂, P₁, hP₁, Ne.symm hne, h3, h4, h1, h2⟩

/-- **PTM₂ at local girth five.** Let `G` have no vertex of positive even degree, and let `ab`,
`cd` be disjoint edges with `c` reachable from `a`, such that no triangle and no four-cycle passes
through `a`, `b`, `c` or `d`. Then some Lovász decomposition has `ab` terminal at the prescribed
end `a`, `cd` terminal at one of its ends, and the two edges on different paths. -/
theorem ptm2_localgirth (G : SimpleGraph W) [DecidableRel G.Adj] (hodd : ∀ v, v ∉ evenSet G)
    {a b c d : W} (hS : NoShortCycleAt G (fun v => v = a ∨ v = b ∨ v = c ∨ v = d))
    (hconn : G.Reachable c a)
    (hab : G.Adj a b) (hcd : G.Adj c d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) :
    PTM2At G a b c d ∨ PTM2At G a b d c := by
  classical
  have hex : ∃ n, ∃ u w, (u = a ∨ u = b) ∧ (w = c ∨ w = d) ∧ ∃ r : G.Walk w u, r.length = n := by
    obtain ⟨r⟩ := hconn
    exact ⟨r.length, a, c, Or.inl rfl, Or.inl rfl, r, rfl⟩
  obtain ⟨u₀, w₀, hu₀, hw₀, r₀, hr₀⟩ := Nat.find_spec hex
  have hmin : ∀ u w, (u = a ∨ u = b) → (w = c ∨ w = d) → ∀ r : G.Walk w u,
      Nat.find hex ≤ r.length := fun u w hu hw r =>
    Nat.find_min' hex ⟨u, w, hu, hw, r, rfl⟩
  obtain ⟨p, hp, hplen⟩ : ∃ p : G.Walk w₀ u₀, p.IsPath ∧ p.length = Nat.find hex := by
    refine ⟨r₀.bypass, r₀.bypass_isPath, ?_⟩
    have h1 := r₀.length_bypass_le_length
    have h2 := hmin u₀ w₀ hu₀ hw₀ r₀.bypass
    omega
  rcases hu₀ with h | h <;> rcases hw₀ with h' | h' <;> subst u₀ <;> subst w₀
  · right
    exact ptm2_girth_core G hodd (hS.mono (fun v hv => by tauto)) hab hcd.symm had hac hbd hbc p hp
      (fun u w hu hw r => hplen ▸ hmin u w hu hw.symm r)
  · left
    exact ptm2_girth_core G hodd (hS.mono (fun v hv => by tauto)) hab hcd hac had hbc hbd p hp
      (fun u w hu hw r => hplen ▸ hmin u w hu hw r)
  · left
    refine PTM2At.symm (ptm2_girth_core G hodd (hS.mono (fun v hv => by tauto)) hcd hab (Ne.symm hac) (Ne.symm hbc)
      (Ne.symm had) (Ne.symm hbd) p.reverse hp.reverse ?_)
    intro u w hu hw r
    rw [Walk.length_reverse, hplen]
    have := hmin w u hw hu r.reverse
    rwa [Walk.length_reverse] at this
  · right
    refine PTM2At.symm (ptm2_girth_core G hodd (hS.mono (fun v hv => by tauto)) hcd.symm hab (Ne.symm had) (Ne.symm hbd)
      (Ne.symm hac) (Ne.symm hbc) p.reverse hp.reverse ?_)
    intro u w hu hw r
    rw [Walk.length_reverse, hplen]
    have := hmin w u hw hu.symm r.reverse
    rwa [Walk.length_reverse] at this

/-- **PTM₂ at girth five.** Let `G` be connected, without vertices of positive even degree, and
without triangles and four-cycles (it suffices that `c` is reachable from `a`; isolated vertices
are allowed). For disjoint edges `ab` and `cd` there is a Lovász
decomposition in which `ab` is terminal at the prescribed end `a`, `cd` is terminal at one of
its ends, and the two edges lie on different paths. -/
theorem ptm2_girth5 (G : SimpleGraph W) [DecidableRel G.Adj] (hodd : ∀ v, v ∉ evenSet G)
    (h3 : NoTriangle G) (h4 : NoSquare G) {a b c d : W} (hconn : G.Reachable c a)
    (hab : G.Adj a b) (hcd : G.Adj c d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) :
    PTM2At G a b c d ∨ PTM2At G a b d c :=
  ptm2_localgirth G hodd (noShortCycleAt_of_girth h3 h4 _) hconn hab hcd hac had hbc hbd

end girth

/-! ### From two terminal edges to a star-terminal decomposition -/

section stlLift

variable {U : Type v} [DecidableEq U] {K K' : SimpleGraph U}

/-- `PathDecomp.replace_supp`, recording also that the other paths keep their edges. -/
theorem PathDecomp.replace_edges (D : PathDecomp K) {P : GPath K} (hP : P ∈ D.paths) (P' : GPath K')
    (hcov : ∀ e, e ∈ K'.edgeSet ↔ (e ∈ K.edgeSet ∧ e ∉ P.edges) ∨ e ∈ P'.edges)
    (hnew : ∀ e ∈ P'.edges, e ∈ P.edges ∨ e ∉ K.edgeSet) :
    ∃ D' : PathDecomp K', D'.size = D.size ∧ P' ∈ D'.paths ∧
      (∀ w, D'.ends w + P.endsAt w = D.ends w + P'.endsAt w) ∧
      (∀ Q ∈ D.paths, Q ≠ P → ∃ Q' ∈ D'.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
        Q'.walk.support = Q.walk.support ∧ Q'.edges = Q.edges) ∧
      ∀ Q' ∈ D'.paths, Q' = P' ∨ ∃ Q ∈ D.paths, Q ≠ P ∧ Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
        Q'.walk.support = Q.walk.support ∧ Q'.edges = Q.edges := by
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
        rfl, rfl, GPath.transfer_support _ _, GPath.transfer_edges _ _⟩
    · exact absurd hQ hQP
    · exact ⟨Q.transfer (h₂ Q hQ),
        List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_pmap_of_mem hQ)),
        rfl, rfl, GPath.transfer_support _ _, GPath.transfer_edges _ _⟩
  · have hlenE : ∀ R : GPath K, 0 < R.edges.length := fun R => by
      show 0 < R.walk.edges.length
      rw [Walk.length_edges]; exact R.pos
    intro Q' hQ'
    change Q' ∈ L at hQ'
    simp only [L, List.mem_append, List.mem_cons, List.mem_pmap] at hQ'
    rcases hQ' with ⟨Q, hQ, rfl⟩ | rfl | ⟨Q, hQ, rfl⟩
    · refine Or.inr ⟨Q, by rw [hl]; exact List.mem_append_left _ hQ, ?_, rfl, rfl,
        GPath.transfer_support _ _, GPath.transfer_edges _ _⟩
      intro hQP
      obtain ⟨e, he⟩ := List.exists_mem_of_length_pos (hlenE Q)
      exact hAP e (List.mem_flatMap.mpr ⟨Q, hQ, he⟩) (hQP ▸ he)
    · exact Or.inl rfl
    · refine Or.inr ⟨Q, by rw [hl]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hQ), ?_,
        rfl, rfl, GPath.transfer_support _ _, GPath.transfer_edges _ _⟩
      intro hQP
      obtain ⟨e, he⟩ := List.exists_mem_of_length_pos (hlenE Q)
      exact hBP e (List.mem_flatMap.mpr ⟨Q, hQ, he⟩) (hQP ▸ he)


/-- Subdividing the terminal edge `ab` of a path starting at `a` by a vertex `z` off the path. -/
theorem GPath.subdivide_start {G J : SimpleGraph U} (P : GPath G) {a b z : U} (hsrc : P.src = a)
    (hab : s(a, b) ∈ P.edges) (hz : z ∉ P.walk.support) (haz : J.Adj a z) (hzb : J.Adj z b)
    (hJ : ∀ e ∈ P.edges, e ≠ s(a, b) → e ∈ J.edgeSet) :
    ∃ P' : GPath J, P'.src = a ∧ P'.tgt = P.tgt ∧ P.edges = s(a, b) :: P.edges.tail ∧
      P'.edges = s(a, z) :: s(z, b) :: P.edges.tail ∧
      (∀ w, w ∈ P'.walk.support ↔ w = z ∨ w ∈ P.walk.support) ∧
      (P.tgt = b → P.edges.tail = []) := by
  obtain ⟨src, tgt, w, hw, hpos⟩ := P
  simp only at hsrc
  subst hsrc
  cases w with
  | nil => simp at hpos
  | @cons _ m _ h rest =>
    have hpath := (Walk.cons_isPath_iff h rest).mp hw
    have hnotin : ∀ e ∈ rest.edges, src ∉ e := by
      intro e he hse
      induction e using Sym2.inductionOn with
      | hf c d =>
        rcases Sym2.mem_iff.mp hse with rfl | rfl
        · exact hpath.2 (rest.fst_mem_support_of_mem_edges he)
        · exact hpath.2 (rest.snd_mem_support_of_mem_edges he)
    have hedges : (GPath.edges ⟨src, tgt, Walk.cons h rest, hw, hpos⟩) = s(src, m) :: rest.edges := rfl
    rw [hedges] at hab
    have hmb : m = b := by
      rcases List.mem_cons.mp hab with h' | h'
      · rcases Sym2.eq_iff.mp h' with ⟨-, h''⟩ | ⟨h'', -⟩
        · exact h''.symm
        · exact absurd h'' h.ne
      · exact absurd (Sym2.mem_mk_left _ _) (hnotin _ h')
    subst hmb
    have hrest : ∀ e ∈ rest.edges, e ∈ J.edgeSet := fun e he =>
      hJ e (by rw [hedges]; exact List.mem_cons_of_mem _ he)
        (fun h' => hnotin e he (h' ▸ Sym2.mem_mk_left _ _))
    have hzrest : z ∉ rest.support := fun h' => hz (by simp [h'])
    have hP' : (Walk.cons haz (Walk.cons hzb (rest.transfer J hrest))).IsPath := by
      rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff, Walk.isPath_transfer, Walk.support_cons,
        Walk.support_transfer, List.mem_cons, not_or]
      exact ⟨⟨hpath.1, hzrest⟩, haz.ne, hpath.2⟩
    refine ⟨⟨src, tgt, _, hP', by simp⟩, rfl, rfl, rfl, ?_, fun w => ?_, fun htgt => ?_⟩
    · show (Walk.cons haz (Walk.cons hzb (rest.transfer J hrest))).edges = _
      simp [Walk.edges_transfer, GPath.edges]
    · show w ∈ (Walk.cons haz (Walk.cons hzb (rest.transfer J hrest))).support ↔
        w = z ∨ w ∈ (Walk.cons h rest).support
      simp only [Walk.support_cons, Walk.support_transfer, List.mem_cons]
      tauto
    · simp only at htgt
      subst htgt
      have := (Walk.isPath_iff_nil.mp hpath.1).eq_nil
      subst this
      rfl

end stlLift

section swapGraph

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- `K − zc − zd + cd`: the transition `c z d` at `z` lifted to the edge `cd`. -/
def swapG (K : SimpleGraph V) (z c d : V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ((K.Adj u v ∧ s(u, v) ≠ s(z, c) ∧ s(u, v) ≠ s(z, d)) ∨ s(u, v) = s(c, d))
  symm := ⟨fun u v h => ⟨h.1.symm, by
    rcases h.2 with h | h
    · exact Or.inl ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2.1, by rw [Sym2.eq_swap]; exact h.2.2⟩
    · exact Or.inr (by rw [Sym2.eq_swap]; exact h)⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

instance swapG.decRel (K : SimpleGraph V) [DecidableRel K.Adj] (z c d : V) :
    DecidableRel (swapG K z c d).Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ ((K.Adj u v ∧ s(u, v) ≠ s(z, c) ∧ s(u, v) ≠ s(z, d)) ∨
    s(u, v) = s(c, d))))

omit [Fintype V] in
theorem swapG_adj (K : SimpleGraph V) (z c d u v : V) : (swapG K z c d).Adj u v ↔
    u ≠ v ∧ ((K.Adj u v ∧ s(u, v) ≠ s(z, c) ∧ s(u, v) ≠ s(z, d)) ∨ s(u, v) = s(c, d)) := Iff.rfl

omit [Fintype V] in
theorem swapG_edgeSet (K : SimpleGraph V) (z c d : V) (e : Sym2 V) (hcd : c ≠ d) :
    e ∈ (swapG K z c d).edgeSet ↔
      (e ∈ K.edgeSet ∧ e ≠ s(z, c) ∧ e ≠ s(z, d)) ∨ e = s(c, d) := by
  induction e using Sym2.inductionOn with
  | hf u v =>
    rw [mem_edgeSet, mem_edgeSet]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h
      refine ⟨fun huv => ?_, h⟩
      subst huv
      rcases h with ⟨h, -⟩ | h
      · exact K.loopless.irrefl u h
      · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hcd rfl

omit [Fintype V] in
theorem swapG_symm (K : SimpleGraph V) (z c d : V) : swapG K z c d = swapG K z d c := by
  ext u v
  simp only [swapG, Sym2.eq_swap (a := c)]
  tauto

omit [Fintype V] in
theorem swapG_comm (K : SimpleGraph V) {z a b c d : V} (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c)
    (hzd : z ≠ d) : swapG (swapG K z a b) z c d = swapG (swapG K z c d) z a b := by
  ext u v
  simp only [swapG]
  have h1 : s(u, v) = s(a, b) → s(u, v) ≠ s(z, c) ∧ s(u, v) ≠ s(z, d) := by
    intro h; rw [h]
    refine ⟨fun h' => ?_, fun h' => ?_⟩ <;> rcases Sym2.eq_iff.mp h' with ⟨h'', -⟩ | ⟨-, h''⟩
    all_goals first | exact hza h''.symm | exact hzb h''.symm
  have h2 : s(u, v) = s(c, d) → s(u, v) ≠ s(z, a) ∧ s(u, v) ≠ s(z, b) := by
    intro h; rw [h]
    refine ⟨fun h' => ?_, fun h' => ?_⟩ <;> rcases Sym2.eq_iff.mp h' with ⟨h'', -⟩ | ⟨-, h''⟩
    all_goals first | exact hzc h''.symm | exact hzd h''.symm
  tauto

/-- A vertex that trades its edge to `z` for an edge to `p` keeps its degree. -/
theorem degree_trade (L J : SimpleGraph V) [DecidableRel L.Adj] [DecidableRel J.Adj] {v p z : V}
    (hvz : J.Adj v z) (hvp : ¬ J.Adj v p) (h : ∀ w, L.Adj v w ↔ w = p ∨ (J.Adj v w ∧ w ≠ z)) :
    L.degree v = J.degree v := by
  have hset : L.neighborFinset v = insert p ((J.neighborFinset v).erase z) := by
    ext w
    simp only [mem_neighborFinset, Finset.mem_insert, Finset.mem_erase, h]
    tauto
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree, hset,
    Finset.card_insert_of_notMem (by simp [hvp]),
    Finset.card_erase_of_mem (by simpa using hvz)]
  have : 0 < (J.neighborFinset v).card := Finset.card_pos.mpr ⟨z, by simpa using hvz⟩
  omega

/-- Degrees in `K − zc − zd + cd`: unchanged away from `z`, two less at `z`. -/
theorem swapG_degree (K : SimpleGraph V) [DecidableRel K.Adj] {z c d : V} (hzc : K.Adj z c)
    (hzd : K.Adj z d) (hcd : ¬ K.Adj c d) (hcd' : c ≠ d) (v : V) :
    (swapG K z c d).degree v + (if v = z then 2 else 0) = K.degree v := by
  have hzc' : z ≠ c := hzc.ne
  have hzd' : z ≠ d := hzd.ne
  by_cases hvz : v = z
  · subst hvz
    rw [ite_eq_left rfl]
    have hset : (swapG K v c d).neighborFinset v = ((K.neighborFinset v).erase c).erase d := by
      ext w
      rw [Finset.mem_erase, Finset.mem_erase, mem_neighborFinset, mem_neighborFinset, swapG_adj]
      constructor
      · rintro ⟨hvw, ⟨h, h1, h2⟩ | h⟩
        · refine ⟨fun hw => h2 (by rw [hw]), fun hw => h1 (by rw [hw]), h⟩
        · rcases Sym2.eq_iff.mp h with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · exact absurd rfl hzc'
          · exact absurd rfl hzd'
      · rintro ⟨hwd, hwc, h⟩
        refine ⟨h.ne, Or.inl ⟨h, fun h' => ?_, fun h' => ?_⟩⟩
        · rcases Sym2.eq_iff.mp h' with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
          · exact hwc rfl
          · exact hwc rfl
        · rcases Sym2.eq_iff.mp h' with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
          · exact hwd rfl
          · exact hwd rfl
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree, hset,
      Finset.card_erase_of_mem (by simp [hzd, Ne.symm hcd']),
      Finset.card_erase_of_mem (by simpa using hzc)]
    have : 1 < (K.neighborFinset v).card := by
      rw [Finset.one_lt_card]; exact ⟨c, by simpa using hzc, d, by simpa using hzd, hcd'⟩
    omega
  · rw [ite_eq_right hvz, add_zero]
    by_cases hvc : v = c
    · subst hvc
      refine degree_trade _ _ hzc.symm hcd (fun w => ?_)
      rw [swapG_adj]
      constructor
      · rintro ⟨hvw, ⟨h, h1, -⟩ | h⟩
        · exact Or.inr ⟨h, fun hw => h1 (by rw [hw, Sym2.eq_swap])⟩
        · rcases Sym2.eq_iff.mp h with ⟨-, rfl⟩ | ⟨rfl, -⟩
          · exact Or.inl rfl
          · exact absurd rfl hcd'
      · rintro (rfl | ⟨h, hw⟩)
        · exact ⟨hcd', Or.inr rfl⟩
        · refine ⟨h.ne, Or.inl ⟨h, fun h' => hw ?_, fun h' => ?_⟩⟩
          · rcases Sym2.eq_iff.mp h' with ⟨h'', -⟩ | ⟨-, rfl⟩
            · exact absurd h'' hvz
            · rfl
          · rcases Sym2.eq_iff.mp h' with ⟨h'', -⟩ | ⟨h'', -⟩
            · exact absurd h'' hvz
            · exact absurd h'' hcd'
    · by_cases hvd : v = d
      · subst hvd
        refine degree_trade _ _ hzd.symm (fun h => hcd h.symm) (fun w => ?_)
        rw [swapG_adj]
        constructor
        · rintro ⟨hvw, ⟨h, -, h2⟩ | h⟩
          · exact Or.inr ⟨h, fun hw => h2 (by rw [hw, Sym2.eq_swap])⟩
          · rcases Sym2.eq_iff.mp h with ⟨rfl, -⟩ | ⟨-, rfl⟩
            · exact absurd rfl hvc
            · exact Or.inl rfl
        · rintro (rfl | ⟨h, hw⟩)
          · exact ⟨fun h => hcd' h.symm, Or.inr Sym2.eq_swap⟩
          · refine ⟨h.ne, Or.inl ⟨h, fun h' => ?_, fun h' => hw ?_⟩⟩
            · rcases Sym2.eq_iff.mp h' with ⟨h'', -⟩ | ⟨h'', -⟩
              · exact absurd h'' hvz
              · exact absurd h'' hvc
            · rcases Sym2.eq_iff.mp h' with ⟨h'', -⟩ | ⟨-, rfl⟩
              · exact absurd h'' hvz
              · rfl
      · rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
        congr 1
        ext w
        rw [mem_neighborFinset, mem_neighborFinset, swapG_adj]
        constructor
        · rintro ⟨-, ⟨h, -⟩ | h⟩
          · exact h
          · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
            · exact absurd h1 hvc
            · exact absurd h1 hvd
        · intro h
          refine ⟨h.ne, Or.inl ⟨h, fun h' => ?_, fun h' => ?_⟩⟩ <;>
            rcases Sym2.eq_iff.mp h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
          all_goals first | exact hvz h1 | exact hvc h1 | exact hvd h1

end swapGraph

section stlFinal

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Un-lifting one pair.** A path of `K − zc − zd + cd` ending at `c` through `cd`, and avoiding
`z`, becomes the path `c z d ⋯` of `K`; every other path is kept with its edges. -/
theorem unlift (K : SimpleGraph V) {z c d : V} (hzc : K.Adj z c) (hzd : K.Adj z d)
    (hcd : ¬ K.Adj c d) (hcd' : c ≠ d) (D : PathDecomp (swapG K z c d))
    {P : GPath (swapG K z c d)} (hP : P ∈ D.paths) (hend : P.src = c ∨ P.tgt = c)
    (hPcd : s(c, d) ∈ P.edges) (hz : z ∉ P.walk.support) :
    ∃ D' : PathDecomp K, (∀ w, D'.ends w = D.ends w) ∧ ∃ P' ∈ D'.paths, P'.src = c ∧
      s(c, z) ∈ P'.edges ∧ s(z, d) ∈ P'.edges ∧ (P'.tgt ≠ d ∨ ∀ e ∈ P'.edges, z ∈ e) ∧
      z ∈ P'.walk.support ∧
      (∀ Q ∈ D.paths, Q ≠ P → ∃ Q' ∈ D'.paths, Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
        Q'.walk.support = Q.walk.support ∧ Q'.edges = Q.edges) ∧
      ∀ Q' ∈ D'.paths, Q' = P' ∨ ∃ Q ∈ D.paths, Q ≠ P ∧ Q'.src = Q.src ∧ Q'.tgt = Q.tgt ∧
        Q'.walk.support = Q.walk.support ∧ Q'.edges = Q.edges := by
  obtain ⟨Q, hQs, hQe, hQends, hQsupp⟩ := P.exists_orient hend
  have hQcd : s(c, d) ∈ Q.edges := hQe.mem_iff.mpr hPcd
  have hzQ : z ∉ Q.walk.support := fun h => hz ((hQsupp z).mp h)
  have hJ : ∀ e ∈ Q.edges, e ≠ s(c, d) → e ∈ K.edgeSet := by
    intro e he hne
    have := Q.walk.edges_subset_edgeSet he
    rw [swapG_edgeSet K z c d e hcd'] at this
    rcases this with h | h
    · exact h.1
    · exact absurd h hne
  obtain ⟨P', hP's, hP't, hQedges, hP'e, hP'supp, htail⟩ :=
    Q.subdivide_start hQs hQcd hzQ hzc.symm hzd hJ
  have hnd : Q.edges.Nodup := Q.isPath.isTrail.edges_nodup
  rw [hQedges, List.nodup_cons] at hnd
  have hcdK : s(c, d) ∉ K.edgeSet := hcd
  have hzcS : s(c, z) ∉ (swapG K z c d).edgeSet := by
    rw [swapG_edgeSet K z c d _ hcd']
    rintro (⟨-, h, -⟩ | h)
    · exact h Sym2.eq_swap
    · rcases Sym2.eq_iff.mp h with ⟨-, h'⟩ | ⟨h', -⟩
      · exact hzd.ne h'
      · exact hcd' h'
  have hzdS : s(z, d) ∉ (swapG K z c d).edgeSet := by
    rw [swapG_edgeSet K z c d _ hcd']
    rintro (⟨-, -, h⟩ | h)
    · exact h rfl
    · rcases Sym2.eq_iff.mp h with ⟨h', -⟩ | ⟨h', -⟩
      · exact hzc.ne h'
      · exact hzd.ne h'
  have hmemP : ∀ e, e ∈ P.edges ↔ e = s(c, d) ∨ e ∈ Q.edges.tail := by
    intro e
    rw [← hQe.mem_iff]
    conv_lhs => rw [hQedges]
    rw [List.mem_cons]
  obtain ⟨D', -, hP'mem, hends, hpres, hback⟩ := D.replace_edges hP P' (by
      intro e
      rw [hP'e, hmemP, swapG_edgeSet K z c d e hcd']
      simp only [List.mem_cons]
      constructor
      · intro he
        by_cases h1 : e = s(z, c)
        · right; left; rw [h1, Sym2.eq_swap]
        · by_cases h2 : e = s(z, d)
          · right; right; left; exact h2
          · by_cases h3 : e ∈ Q.edges.tail
            · right; right; right; exact h3
            · left
              refine ⟨Or.inl ⟨he, h1, h2⟩, ?_⟩
              rintro (rfl | h)
              · exact hcdK he
              · exact h3 h
      · rintro (⟨h | rfl, hn⟩ | rfl | rfl | h)
        · exact h.1
        · exact absurd (Or.inl rfl) hn
        · rw [Sym2.eq_swap]; exact hzc
        · exact hzd
        · exact hJ e (List.mem_of_mem_tail h) (fun h' => hnd.1 (h' ▸ h)))
    (by
      intro e he
      rw [hP'e, List.mem_cons, List.mem_cons] at he
      rcases he with rfl | rfl | h
      · exact Or.inr hzcS
      · exact Or.inr hzdS
      · exact Or.inl ((hmemP e).2 (Or.inr h)))
  have hP'ends : ∀ w, P'.endsAt w = P.endsAt w := by
    intro w
    rw [← hQends w]
    simp only [GPath.endsAt, hP's, hP't, hQs]
  refine ⟨D', fun w => by have := hends w; rw [hP'ends] at this; omega, P', hP'mem, hP's,
    by rw [hP'e]; exact List.mem_cons_self, by rw [hP'e]; exact List.mem_cons_of_mem _ List.mem_cons_self,
    ?_, (hP'supp z).2 (Or.inl rfl), hpres, hback⟩
  by_cases ht : P'.tgt = d
  · right
    rw [hP't] at ht
    rw [hP'e, htail ht]
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Sym2.mem_mk_right _ _
    · exact Sym2.mem_mk_left _ _
  · exact Or.inl ht

omit [Fintype V] in
theorem sym2_ne_left {z c a : V} (hca : c ≠ a) (hza : z ≠ a) : s(z, c) ≠ s(z, a) := fun h => by
  rcases Sym2.eq_iff.mp h with ⟨-, h'⟩ | ⟨h', -⟩
  · exact hca h'
  · exact hza h'

/-- The lifted graph `(J − z) + ab + cd`, as two transitions lifted at `z`. -/
abbrev liftJ (J : SimpleGraph V) (z a b c d : V) : SimpleGraph V := swapG (swapG J z a b) z c d

/-- Facts about the intermediate graph `J − za − zb + ab`. -/
theorem liftJ_mid (J : SimpleGraph V) {z a b c d : V} (hza : J.Adj z a) (hzb : J.Adj z b)
    (hzc : J.Adj z c) (hzd : J.Adj z d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : ¬ J.Adj c d) :
    (swapG J z a b).Adj z c ∧ (swapG J z a b).Adj z d ∧ ¬ (swapG J z a b).Adj c d := by
  refine ⟨⟨hzc.ne, Or.inl ⟨hzc, sym2_ne_left (Ne.symm hac) hza.ne,
      sym2_ne_left (Ne.symm hbc) hzb.ne⟩⟩,
    ⟨hzd.ne, Or.inl ⟨hzd, sym2_ne_left (Ne.symm had) hza.ne, sym2_ne_left (Ne.symm hbd) hzb.ne⟩⟩,
    ?_⟩
  rintro ⟨-, ⟨h, -⟩ | h⟩
  · exact hcd h
  · rcases Sym2.eq_iff.mp h with ⟨h', -⟩ | ⟨h', -⟩
    · exact hac h'.symm
    · exact hbc h'.symm

/-- Degrees of the lifted graph. -/
theorem liftJ_degree (J : SimpleGraph V) [DecidableRel J.Adj] {z a b c d : V}
    (hza : J.Adj z a) (hzb : J.Adj z b) (hzc : J.Adj z c) (hzd : J.Adj z d)
    (hab' : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd' : c ≠ d)
    (hab : ¬ J.Adj a b) (hcd : ¬ J.Adj c d) (v : V) :
    (liftJ J z a b c d).degree v + (if v = z then 4 else 0) = J.degree v := by
  obtain ⟨h1c, h1d, h1cd⟩ := liftJ_mid J hza hzb hzc hzd hac had hbc hbd hcd
  have h1 := swapG_degree J hza hzb hab hab' v
  have h2 := swapG_degree (swapG J z a b) h1c h1d h1cd hcd' v
  show (swapG (swapG J z a b) z c d).degree v + _ = _
  split_ifs at h1 h2 ⊢ <;> omega

/-- **From PTM₂ to STL.** Let `z` be the only even vertex of `J`, with `N(z) = {a, b, c, d}` and
`ab, cd ∉ E(J)`. A Lovász decomposition of `(J − z) + ab + cd` with `ab` terminal at `a` and `cd`
terminal at `c`, on different paths, lifts to a star-terminal Lovász decomposition of `J` in
which `b` and `d` are on long sides (or a path through `z` has length two): STL holds at `b` and
at `d`. -/
theorem stl_of_ptm2 (J : SimpleGraph V) [DecidableRel J.Adj] {z a b c d : V}
    (hN : ∀ w, J.Adj z w ↔ w = a ∨ w = b ∨ w = c ∨ w = d)
    (hab' : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd' : c ≠ d)
    (hab : ¬ J.Adj a b) (hcd : ¬ J.Adj c d) (h : PTM2At (liftJ J z a b c d) a b c d) :
    STL J z b ∧ STL J z d := by
  have hza : J.Adj z a := (hN a).2 (Or.inl rfl)
  have hzb : J.Adj z b := (hN b).2 (Or.inr (Or.inl rfl))
  have hzc : J.Adj z c := (hN c).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hzd : J.Adj z d := (hN d).2 (Or.inr (Or.inr (Or.inr rfl)))
  obtain ⟨h1c, h1d, h1cd⟩ := liftJ_mid J hza hzb hzc hzd hac had hbc hbd hcd
  have hdeg := liftJ_degree J hza hzb hzc hzd hab' hac had hbc hbd hcd' hab hcd
  -- `z` has degree four in `J`, hence is isolated in the lifted graph
  have hJz : J.degree z = 4 := by
    have hset : J.neighborFinset z = {a, b, c, d} := by
      ext w; simp only [mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton, hN]
    rw [← card_neighborFinset_eq_degree, hset, Finset.card_insert_of_notMem (by simp [hab', hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd']
  have hiso : ∀ w, ¬ (liftJ J z a b c d).Adj z w := by
    intro w hw
    have h0 := hdeg z
    rw [ite_eq_left rfl, hJz] at h0
    have : (liftJ J z a b c d).degree z = 0 := by omega
    rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero] at this
    have : w ∈ (liftJ J z a b c d).neighborFinset z := (mem_neighborFinset _ _ _).2 hw
    simp_all
  have hzP : ∀ P : GPath (liftJ J z a b c d), z ∉ P.walk.support := fun P =>
    P.not_mem_of_isolated hiso
  have hpar : ∀ v, (liftJ J z a b c d).degree v % 2 = J.degree v % 2 := by
    intro v; have := hdeg v; split_ifs at this <;> omega
  obtain ⟨D, hD, P₁, hP₁, P₂, hP₂, hne, h1e, h1ab, h2e, h2cd⟩ := h
  -- un-lift `cd`, then `ab`
  obtain ⟨D₁, hD₁, P₂', hP₂', h2s, h2cz, h2zd, h2t, hz2, hpres₁, hback₁⟩ :=
    unlift (swapG J z a b) h1c h1d h1cd hcd' D hP₂ h2e h2cd (hzP P₂)
  obtain ⟨P₁b, hP₁b, h1s, h1t, h1supp, h1edges⟩ := hpres₁ P₁ hP₁ hne
  have h1e' : P₁b.src = a ∨ P₁b.tgt = a := by rw [h1s, h1t]; exact h1e
  obtain ⟨D₂, hD₂, P₁', hP₁', h1s', h1az, h1zb, h1t', hz1, hpres₂, hback₂⟩ :=
    unlift J hza hzb hab hab' D₁ hP₁b h1e' (h1edges ▸ h1ab) (h1supp ▸ hzP P₁)
  have hne₂ : P₂' ≠ P₁b := fun h' => (h1supp ▸ hzP P₁) (h' ▸ hz2)
  obtain ⟨P₂'', hP₂'', h2s'', h2t'', h2supp'', h2edges''⟩ := hpres₂ P₂' hP₂' hne₂
  have hends : ∀ v, D₂.ends v = J.degree v % 2 := fun v => by
    rw [hD₂, hD₁, hD, hpar]
  have hstar : StarAt D₂ z := by
    intro Q hQ hzQ
    rcases hback₂ Q hQ with rfl | ⟨Q₁, hQ₁, -, hs, -, hsupp, hedges⟩
    · left; rw [h1s']; exact h1az
    · rw [hsupp] at hzQ
      rcases hback₁ Q₁ hQ₁ with rfl | ⟨Q₀, hQ₀, -, -, -, hsupp₀, -⟩
      · left; rw [hs, hedges, h2s]; exact h2cz
      · rw [hsupp₀] at hzQ; exact absurd hzQ (hzP Q₀)
  refine ⟨⟨D₂, hends, hstar, ?_⟩, ⟨D₂, hends, hstar, ?_⟩⟩
  · rcases h1t' with ht | hall
    · exact Or.inl ⟨P₁', hP₁', h1zb, by rw [h1s']; exact hab', ht⟩
    · exact Or.inr ⟨P₁', hP₁', hall⟩
  · rcases h2t with ht | hall
    · exact Or.inl ⟨P₂'', hP₂'', h2edges'' ▸ h2zd, by rw [h2s'', h2s]; exact hcd',
        by rw [h2t'']; exact ht⟩
    · exact Or.inr ⟨P₂'', hP₂'', h2edges'' ▸ hall⟩

omit [Fintype V] in
theorem PTM2At.congr [Fintype V] {G G' : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (hG : G = G') {a b x y : V} (h : PTM2At G a b x y) : PTM2At G' a b x y := by
  subst hG; convert h

/-- **STL at local girth five.** Let `z` be the only even vertex of `J`, with
`N(z) = {a, b, c, d}` and `ab, cd ∉ E(J)`. If in the lifted graph `(J − z) + ab + cd` no triangle
and no four-cycle passes through `a`, `b`, `c` or `d`, and `c` is reachable from `a` in it, then
STL holds at every neighbour of `z` (`STL J z r`). -/
theorem stl_of_localgirth (J : SimpleGraph V) [DecidableRel J.Adj] {z a b c d : V}
    (hev : ∀ v, Even (J.degree v) ↔ v = z)
    (hN : ∀ w, J.Adj z w ↔ w = a ∨ w = b ∨ w = c ∨ w = d)
    (hab' : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd' : c ≠ d)
    (hab : ¬ J.Adj a b) (hcd : ¬ J.Adj c d)
    (hreach : (liftJ J z a b c d).Reachable c a)
    (hS : NoShortCycleAt (liftJ J z a b c d) (fun v => v = a ∨ v = b ∨ v = c ∨ v = d)) :
    ∀ r, J.Adj z r → STL J z r := by
  have hza : J.Adj z a := (hN a).2 (Or.inl rfl)
  have hzb : J.Adj z b := (hN b).2 (Or.inr (Or.inl rfl))
  have hzc : J.Adj z c := (hN c).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hzd : J.Adj z d := (hN d).2 (Or.inr (Or.inr (Or.inr rfl)))
  have hdeg := liftJ_degree J hza hzb hzc hzd hab' hac had hbc hbd hcd' hab hcd
  have hJz : J.degree z = 4 := by
    have hset : J.neighborFinset z = {a, b, c, d} := by
      ext w; simp only [mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton, hN]
    rw [← card_neighborFinset_eq_degree, hset, Finset.card_insert_of_notMem (by simp [hab', hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd']
  have hodd : ∀ v, v ∉ evenSet (liftJ J z a b c d) := by
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
      have : (liftJ J z a b c d).degree v % 2 = 0 := hv.2
      omega
  have hGab : (liftJ J z a b c d).Adj a b := ⟨hab', Or.inl ⟨⟨hab', Or.inr rfl⟩, fun h => by
    rcases Sym2.eq_iff.mp h with ⟨h', -⟩ | ⟨h', -⟩
    · exact hza.ne h'.symm
    · exact hac h', fun h => by
    rcases Sym2.eq_iff.mp h with ⟨h', -⟩ | ⟨h', -⟩
    · exact hza.ne h'.symm
    · exact had h'⟩⟩
  have hGcd : (liftJ J z a b c d).Adj c d := ⟨hcd', Or.inr rfl⟩
  have e1 : liftJ J z a b c d = liftJ J z a b d c := swapG_symm _ _ _ _
  have e2 : liftJ J z a b c d = liftJ J z b a c d := by rw [liftJ, liftJ, swapG_symm J z a b]
  have e3 : liftJ J z a b c d = liftJ J z b a d c := by rw [e2, liftJ, liftJ, swapG_symm _ z c d]
  have e4 : liftJ J z a b c d = liftJ J z c d a b := swapG_comm J hza.ne hzb.ne hzc.ne hzd.ne
  have e5 : liftJ J z a b c d = liftJ J z c d b a := by rw [e4, liftJ, liftJ, swapG_symm _ z a b]
  have e6 : liftJ J z a b c d = liftJ J z d c a b := by rw [e4, liftJ, liftJ, swapG_symm J z c d]
  have e7 : liftJ J z a b c d = liftJ J z d c b a := by rw [e6, liftJ, liftJ, swapG_symm _ z a b]
  have hN' : ∀ {p q r s : V}, ({p, q, r, s} : Finset V) = {a, b, c, d} →
      ∀ w, J.Adj z w ↔ w = p ∨ w = q ∨ w = r ∨ w = s := by
    intro p q r s hpq w
    rw [hN]
    have := congrArg (w ∈ ·) hpq
    simp only [Finset.mem_insert, Finset.mem_singleton, eq_iff_iff] at this
    exact this.symm
  intro r hr
  rcases (hN r).1 hr with hr' | hr' | hr' | hr' <;> subst r
  · -- `r = a`: prescribe `b` short
    rcases ptm2_localgirth (liftJ J z a b c d) hodd (hS.mono (fun v hv => by tauto)) (hreach.trans hGab.reachable) hGab.symm hGcd
      hbc hbd hac had with h | h
    · exact (stl_of_ptm2 J (hN' (by ext; simp; tauto)) (Ne.symm hab') hbc hbd hac had hcd'
        (fun h => hab h.symm) hcd (h.congr e2)).1
    · exact (stl_of_ptm2 J (hN' (by ext; simp; tauto)) (Ne.symm hab') hbd hbc had hac
        (Ne.symm hcd') (fun h => hab h.symm) (fun h => hcd h.symm) (h.congr e3)).1
  · -- `r = b`: prescribe `a` short
    rcases ptm2_localgirth (liftJ J z a b c d) hodd (hS.mono (fun v hv => by tauto)) hreach hGab hGcd hac had hbc hbd with h | h
    · exact (stl_of_ptm2 J hN hab' hac had hbc hbd hcd' hab hcd h).1
    · exact (stl_of_ptm2 J (hN' (by ext; simp; tauto)) hab' had hac hbd hbc (Ne.symm hcd') hab
        (fun h => hcd h.symm) (h.congr e1)).1
  · -- `r = c`: prescribe `d` short
    rcases ptm2_localgirth (liftJ J z a b c d) hodd (hS.mono (fun v hv => by tauto)) (hreach.symm.trans hGcd.reachable) hGcd.symm hGab
      (Ne.symm had) (Ne.symm hbd) (Ne.symm hac) (Ne.symm hbc) with h | h
    · exact (stl_of_ptm2 J (hN' (by ext; simp; tauto)) (Ne.symm hcd') (Ne.symm had) (Ne.symm hbd)
        (Ne.symm hac) (Ne.symm hbc) hab' (fun h => hcd h.symm) hab (h.congr e6)).1
    · exact (stl_of_ptm2 J (hN' (by ext; simp; tauto)) (Ne.symm hcd') (Ne.symm hbd) (Ne.symm had)
        (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab') (fun h => hcd h.symm) (fun h => hab h.symm)
        (h.congr e7)).1
  · -- `r = d`: prescribe `c` short
    rcases ptm2_localgirth (liftJ J z a b c d) hodd (hS.mono (fun v hv => by tauto)) hreach.symm hGcd hGab (Ne.symm hac) (Ne.symm hbc)
      (Ne.symm had) (Ne.symm hbd) with h | h
    · exact (stl_of_ptm2 J (hN' (by ext; simp; tauto)) hcd' (Ne.symm hac) (Ne.symm hbc)
        (Ne.symm had) (Ne.symm hbd) hab' hcd hab (h.congr e4)).1
    · exact (stl_of_ptm2 J (hN' (by ext; simp; tauto)) hcd' (Ne.symm hbc) (Ne.symm hac)
        (Ne.symm hbd) (Ne.symm had) (Ne.symm hab') hcd (fun h => hab h.symm) (h.congr e5)).1

/-- **STL at girth five**: the lifted graph has no triangle and no four-cycle. -/
theorem stl_of_girth5 (J : SimpleGraph V) [DecidableRel J.Adj] {z a b c d : V}
    (hev : ∀ v, Even (J.degree v) ↔ v = z)
    (hN : ∀ w, J.Adj z w ↔ w = a ∨ w = b ∨ w = c ∨ w = d)
    (hab' : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd' : c ≠ d)
    (hab : ¬ J.Adj a b) (hcd : ¬ J.Adj c d)
    (hreach : (liftJ J z a b c d).Reachable c a)
    (h3 : NoTriangle (liftJ J z a b c d)) (h4 : NoSquare (liftJ J z a b c d)) :
    ∀ r, J.Adj z r → STL J z r :=
  stl_of_localgirth J hev hN hab' hac had hbc hbd hcd' hab hcd hreach
    (noShortCycleAt_of_girth h3 h4 _)

/-- **Test 1 at local girth five**, the spine form. -/
theorem test1_of_localgirth (J : SimpleGraph V) [DecidableRel J.Adj] {z a b c d : V}
    (hN : ∀ w, J.Adj z w ↔ w = a ∨ w = b ∨ w = c ∨ w = d)
    (hab' : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd' : c ≠ d)
    (hab : ¬ J.Adj a b) (hcd : ¬ J.Adj c d) (hdeg : ∀ r, J.Adj z r → 3 ≤ J.degree r)
    (hreach : (liftJ J z a b c d).Reachable c a)
    (hS : NoShortCycleAt (liftJ J z a b c d) (fun v => v = a ∨ v = b ∨ v = c ∨ v = d)) :
    Test1 J z :=
  test1_of_stl z hdeg fun hev =>
    stl_of_localgirth J hev hN hab' hac had hbc hbd hcd' hab hcd hreach hS

/-- **Test 1 at girth five**, the spine form. -/
theorem test1_of_girth5 (J : SimpleGraph V) [DecidableRel J.Adj] {z a b c d : V}
    (hN : ∀ w, J.Adj z w ↔ w = a ∨ w = b ∨ w = c ∨ w = d)
    (hab' : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd' : c ≠ d)
    (hab : ¬ J.Adj a b) (hcd : ¬ J.Adj c d) (hdeg : ∀ r, J.Adj z r → 3 ≤ J.degree r)
    (hreach : (liftJ J z a b c d).Reachable c a)
    (h3 : NoTriangle (liftJ J z a b c d)) (h4 : NoSquare (liftJ J z a b c d)) :
    Test1 J z :=
  test1_of_stl z hdeg fun hev =>
    stl_of_girth5 J hev hN hab' hac had hbc hbd hcd' hab hcd hreach h3 h4

end stlFinal

end Gallai
