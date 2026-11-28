import GallaiLean.JointR
import GallaiLean.PrescribedEnd
import GallaiLean.Test2Converse

/-!
# Conjecture AE is Conjecture EE

Manuscript `manuscripts/ae`. Conjecture AE (`ConjAE`, conj-r): if `g` is the only vertex of
positive even degree of `K`, `c` is odd and `c ≁ g`, some Lovász decomposition of `K` has
`g ∉ Q(c)`. Conjecture EE (prescribed-end): if `z` is the only vertex of positive even degree of
`G` and `u ∈ N(z)`, some Lovász decomposition of `G` has `uz` as the terminal edge at `u`.

The two are the same statement, read in `K` and in `G = K + gc` (`z = c`, `u = g`, so `K = G − uz`):

* `ee_of_avoid` (multi-sep) is AE ⇒ EE, instance by instance.
* **`avoidDecomp_of_terminal`** is EE ⇒ AE, instance by instance. The path ending at `g` in `K + gc`
  is `g c Y`. Removing the terminal edge `gc` (`PathDecomp.drop_terminal`) leaves `Q(c) = cY`, which
  misses `g`.
* **`conjAE_iff_conjEE`**: the two conjectures are equivalent.
* **`avoidDecomp_of_atMostOneCommon`**: AE holds whenever `g` and `c` have at most one common
  neighbour (from `ee_atMostOneCommon`, prescribed-end).
* **`ln2_of_leaf_at_head_of_atMostOneCommon`**: the leaf-at-head case of `L_N(2)`
  (`ln2_of_leaf_at_head`) without the hypothesis AE, when `cⱼ` and `aⱼ` have at most one common
  neighbour other than `cᵢ`.
-/

open SimpleGraph

namespace Gallai

universe u

/-- **Conjecture EE** (prescribed-end): if `z` is the only vertex of positive even degree and
`u ∈ N(z)`, some Lovász decomposition has `uz` in the path ending at `u` (its terminal edge). -/
def ConjEE : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    (evenSet G).card ≤ 1 → ∀ z u : W, z ∈ evenSet G → G.Adj z u →
      ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
        ∃ P ∈ D.paths, (P.src = u ∨ P.tgt = u) ∧ s(u, z) ∈ P.edges

section equiv

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- A path starting at `u` whose edges contain `uz` has `z` as its second vertex. -/
theorem GPath.support_of_src_mem_edges {G : SimpleGraph V} (P : GPath G) {u z : V}
    (hs : P.src = u) (he : s(u, z) ∈ P.edges) : ∃ l, P.walk.support = u :: z :: l := by
  obtain ⟨a, b, w, hw, hpos⟩ := P
  simp only at hs
  subst hs
  cases w with
  | nil => simp at hpos
  | @cons _ x _ h p =>
    simp only [GPath.edges, Walk.edges_cons, List.mem_cons] at he
    rcases he with he | he
    · rcases Sym2.eq_iff.mp he with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨p.support.tail, by rw [Walk.support_cons, walk_support_eq_cons p]; rfl⟩
      · exact absurd h (G.loopless.irrefl _)
    · exact absurd (Walk.fst_mem_support_of_mem_edges p he)
        ((Walk.cons_isPath_iff h p).mp hw).2

/-- The even set of `K + gc`, when `g` is the only even vertex of `K` and `c` is odd: it is `{c}`. -/
theorem evenSet_plusEdge_sub {K : SimpleGraph V} [DecidableRel K.Adj] (hev : (evenSet K).card ≤ 1)
    {c g : V} (hg : g ∈ evenSet K) (hc : K.degree c % 2 = 1) (hcg : ¬ K.Adj c g) :
    evenSet (plusEdge K g c) ⊆ {c} := by
  have hgc : g ≠ c := by
    rintro rfl; have := (mem_evenSet_iff.mp hg).2; omega
  have hn : ¬ K.Adj g c := fun h => hcg h.symm
  have huniq : ∀ w ∈ evenSet K, w = g := fun w hw => Finset.card_le_one.mp hev w hw g hg
  intro v hv
  rw [mem_evenSet_iff, plusEdge_degree hgc hn] at hv
  rw [Finset.mem_singleton]
  by_contra hvc
  by_cases hvg : v = g
  · subst hvg
    have := (mem_evenSet_iff.mp hg).2
    simp at hv; omega
  · simp only [hvg, hvc, or_self, ite_false, add_zero] at hv
    exact hvg (huniq v (mem_evenSet_iff.mpr hv))

/-- `c` is the even vertex of `K + gc`. -/
theorem mem_evenSet_plusEdge {K : SimpleGraph V} [DecidableRel K.Adj] {c g : V} (hgc : g ≠ c)
    (hc : K.degree c % 2 = 1) (hcg : ¬ K.Adj c g) : c ∈ evenSet (plusEdge K g c) := by
  rw [mem_evenSet_iff, plusEdge_degree hgc (fun h => hcg h.symm)]
  simp only [or_true, ite_true]
  omega

/-- **EE ⇒ AE, instance by instance.** Let `g` be the only vertex of positive even degree of `K`, `c`
odd with `c ≁ g`. If `K + gc` has a Lovász decomposition whose path ending at `g` contains `gc`, then
`K` has a Lovász decomposition whose path ending at `c` misses `g`. -/
theorem avoidDecomp_of_terminal {K : SimpleGraph V} [DecidableRel K.Adj] {c g : V}
    (hg : g ∈ evenSet K) (hc : K.degree c % 2 = 1) (hcg : ¬ K.Adj c g)
    (hEE : ∃ D : PathDecomp (plusEdge K g c), (∀ v, D.ends v = (plusEdge K g c).degree v % 2) ∧
      ∃ P ∈ D.paths, (P.src = g ∨ P.tgt = g) ∧ s(g, c) ∈ P.edges) :
    AvoidDecomp K c {g} := by
  classical
  have hgc : g ≠ c := by
    rintro rfl; have := (mem_evenSet_iff.mp hg).2; omega
  have hn : ¬ K.Adj g c := fun h => hcg h.symm
  have hgev := (mem_evenSet_iff.mp hg).2
  set L := plusEdge K g c with hL
  have hLdeg : ∀ v, L.degree v = K.degree v + if v = g ∨ v = c then 1 else 0 :=
    fun v => plusEdge_degree hgc hn v
  obtain ⟨D, hD, P, hP, hend, he⟩ := hEE
  -- `c` has no end in `D`
  have hDc : D.ends c = 0 := by
    rw [hD c, hLdeg c]; simp only [or_true, ite_true]; omega
  -- orient `P` to start at `g`
  obtain ⟨R, hRs, hRperm, hRends, hRsupp⟩ := P.exists_orient hend
  have hRe : s(g, c) ∈ R.edges := hRperm.symm.subset he
  obtain ⟨l, hl⟩ := R.support_of_src_mem_edges hRs hRe
  have hlen : 2 ≤ R.walk.length := by
    have h1 := R.walk.length_support
    rw [hl] at h1
    cases l with
    | nil =>
      exfalso
      have htgt : R.tgt = c := R.tgt_of_support (l := [g]) (by rw [hl]; rfl)
      have h2 : 1 ≤ R.endsAt c := by unfold GPath.endsAt; rw [htgt]; simp
      rw [hRends] at h2
      have := D.endsAt_le_ends' hP c
      omega
    | cons x l' => simp at h1; omega
  have hK' : ∀ e, e ∈ K.edgeSet ↔ e ∈ L.edgeSet ∧ e ≠ s(g, c) := by
    intro e
    rw [hL, plusEdge_edgeSet hgc]
    constructor
    · intro h
      exact ⟨Or.inl h, by rintro rfl; exact hn h⟩
    · rintro ⟨h | h, hne⟩
      · exact h
      · exact absurd h hne
  obtain ⟨D', hends', hcls, -, -⟩ :=
    D.drop_terminal hP R (Multiset.coe_eq_coe.mpr hRperm) hRends hRs hl hlen hK'
  refine ⟨D', fun v => ?_, fun Q hQ hQc a ha => ?_⟩
  · have h1 := hends' v
    rw [hD v, hLdeg v] at h1
    by_cases hvg : v = g
    · rw [hvg] at h1 ⊢
      rw [ite_eq_left rfl, ite_eq_left (Or.inl rfl), ite_eq_right (Ne.symm hgc)] at h1
      omega
    · by_cases hvc : v = c
      · rw [hvc] at h1 ⊢
        rw [ite_eq_right hgc, ite_eq_left (Or.inr rfl), ite_eq_left rfl] at h1
        omega
      · rw [ite_eq_right (Ne.symm hvg), ite_eq_right (by tauto), ite_eq_right (Ne.symm hvc), add_zero] at h1
        omega
  · rw [Finset.mem_singleton] at ha
    subst ha
    rcases hcls Q hQ with ⟨hs, -, hsupp⟩ | ⟨Q₀, hQ₀, hs, ht, -⟩
    · rw [hsupp]
      have hnd := R.isPath.support_nodup
      rw [hl] at hnd
      exact (List.nodup_cons.mp hnd).1
    · exfalso
      have h2 : 1 ≤ Q₀.endsAt c := by
        unfold GPath.endsAt; rcases hQc with h | h
        · rw [← hs, h]; simp
        · rw [← ht, h]; simp
      have := D.endsAt_le_ends' hQ₀ c
      omega

/-- **AE ⇒ EE, instance by instance** (`ee_of_avoid`, multi-sep), from `ConjAE`. -/
theorem terminal_of_conjAE (hAE : ConjAE.{u}) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hev : (evenSet G).card ≤ 1) {z u : V} (hz : z ∈ evenSet G) (hzu : G.Adj z u) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∃ P ∈ D.paths, (P.src = u ∨ P.tgt = u) ∧ s(u, z) ∈ P.edges := by
  classical
  obtain ⟨hsub, hzodd, -⟩ := delEdge_even_facts hev hz hzu
  have hcard : (evenSet (delEdge G u z)).card ≤ 1 :=
    (Finset.card_le_card hsub).trans (by simp)
  have hnadj : ¬ (delEdge G u z).Adj z u := fun h => h.2 (Sym2.eq_swap)
  have hav : AvoidDecomp (delEdge G u z) z {u} := by
    by_cases hu : u ∈ evenSet (delEdge G u z)
    · exact hAE V (delEdge G u z) hcard z u hu hzodd hnadj
    · -- `u` is isolated in `G − uz`
      have hu0 : (delEdge G u z).degree u = 0 := by
        have h1 := delEdge_degree G hzu.symm u
        simp only [ite_true, hzu.ne.symm, ite_false, add_zero] at h1
        have huodd : G.degree u % 2 = 1 := by
          have hne : u ≠ z := hzu.ne.symm
          have huniq : ∀ w ∈ evenSet G, w = z := fun w hw => Finset.card_le_one.mp hev w hw z hz
          have hpos : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).mpr ⟨z, hzu.symm⟩
          by_contra hodd
          exact hne (huniq u (mem_evenSet_iff.mpr ⟨hpos, by omega⟩))
        rw [mem_evenSet_iff] at hu
        omega
      obtain ⟨D₀, hD₀⟩ := lovasz_ends (delEdge G u z) hcard
      refine ⟨D₀, hD₀, fun Q _ _ a ha haQ => ?_⟩
      rw [Finset.mem_singleton] at ha
      subst ha
      have hadj := (Walk.mem_support_iff_exists_mem_edges_of_not_nil
        (Walk.not_nil_of_ne Q.src_ne_tgt)).mp haQ
      obtain ⟨e, heQ, hae⟩ := hadj
      have heK : e ∈ (delEdge G a z).edgeSet := Q.walk.edges_subset_edgeSet heQ
      induction e using Sym2.inductionOn with
      | hf x y =>
        rcases Sym2.mem_iff.mp hae with rfl | rfl
        · have := (delEdge G a z).degree_pos_iff_exists_adj a |>.mpr ⟨y, heK⟩
          omega
        · have := (delEdge G a z).degree_pos_iff_exists_adj a |>.mpr ⟨x, heK.symm⟩
          omega
  obtain ⟨D', hD', hav'⟩ := hav
  exact ee_of_avoid G hev hz hzu D' hD' fun P hP hend =>
    hav' P hP hend u (Finset.mem_singleton_self u)

end equiv

/-- **AE is EE.** -/
theorem conjAE_iff_conjEE : ConjAE.{u} ↔ ConjEE.{u} := by
  constructor
  · intro hAE W _ _ G _ hev z u hz hzu
    exact terminal_of_conjAE hAE G hev hz hzu
  · intro hEE V _ _ K _ hev c g hg hc hcg
    classical
    have hgc : g ≠ c := by
      rintro rfl; have := (mem_evenSet_iff.mp hg).2; omega
    refine avoidDecomp_of_terminal hg hc hcg ?_
    have hev' : (evenSet (plusEdge K g c)).card ≤ 1 :=
      (Finset.card_le_card (evenSet_plusEdge_sub hev hg hc hcg)).trans (by simp)
    exact hEE V (plusEdge K g c) hev' c g (mem_evenSet_plusEdge hgc hc hcg)
      ((plusEdge_adj).mpr (Or.inr ⟨hgc.symm, Or.inr ⟨rfl, rfl⟩⟩))

section commonNbr

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **AE with at most one common neighbour.** If `g` is the only vertex of positive even degree of
`K`, `c` is odd, `c ≁ g`, and `g` and `c` have at most one common neighbour, then some Lovász
decomposition of `K` has its path ending at `c` avoiding `g`. -/
theorem avoidDecomp_of_atMostOneCommon {K : SimpleGraph V} [DecidableRel K.Adj]
    (hev : (evenSet K).card ≤ 1) {c g : V} (hg : g ∈ evenSet K) (hc : K.degree c % 2 = 1)
    (hcg : ¬ K.Adj c g)
    (hcom : ∀ w w', K.Adj g w → K.Adj w c → K.Adj g w' → K.Adj w' c → w = w') :
    AvoidDecomp K c {g} := by
  classical
  have hgc : g ≠ c := by
    rintro rfl; have := (mem_evenSet_iff.mp hg).2; omega
  refine avoidDecomp_of_terminal hg hc hcg ?_
  have hev' : (evenSet (plusEdge K g c)).card ≤ 1 :=
    (Finset.card_le_card (evenSet_plusEdge_sub hev hg hc hcg)).trans (by simp)
  refine ee_atMostOneCommon (plusEdge K g c) hev' (mem_evenSet_plusEdge hgc hc hcg)
    ((plusEdge_adj).mpr (Or.inr ⟨hgc.symm, Or.inr ⟨rfl, rfl⟩⟩)) ?_
  -- common neighbours of `g` and `c` in `K + gc` are common neighbours in `K`
  have hback : ∀ w, (plusEdge K g c).Adj g w → (plusEdge K g c).Adj w c → K.Adj g w ∧ K.Adj w c := by
    intro w h1 h2
    have hwg : w ≠ g := fun h => by subst h; exact (plusEdge K w c).loopless.irrefl w h1
    have hwc : w ≠ c := fun h => by subst h; exact (plusEdge K g w).loopless.irrefl w h2
    refine ⟨?_, ?_⟩
    · rcases (plusEdge_adj).mp h1 with h | ⟨-, ⟨-, h⟩ | ⟨h, -⟩⟩
      · exact h
      · exact absurd h hwc
      · exact absurd h hgc
    · rcases (plusEdge_adj).mp h2 with h | ⟨-, ⟨h, -⟩ | ⟨h, -⟩⟩
      · exact h
      · exact absurd h hwg
      · exact absurd h hwc
  intro w w' h1 h2 h3 h4
  obtain ⟨a1, a2⟩ := hback w h1 h2
  obtain ⟨a3, a4⟩ := hback w' h3 h4
  exact hcom w w' a1 a2 a3 a4

section leafHead

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **A leaf at the other head, without AE**, when `aⱼ` and `cⱼ` have at most one common
neighbour: `ln2_of_leaf_at_head` with `ConjAE` replaced by `avoidDecomp_of_atMostOneCommon` for
`F − cᵢaⱼ`. -/
theorem ln2_of_leaf_at_head_of_atMostOneCommon (G : SimpleGraph V) [DecidableRel G.Adj]
    (hodd : ∀ v, G.degree v % 2 = 1) {ci ai cj aj : V} (hcij : ci ≠ cj) (haici : ai ≠ ci)
    (haiaj : ai ≠ aj) (hajcj : aj ≠ cj) (hadj : ¬ G.Adj cj aj) (hca : G.Adj ci aj)
    (hleaf : G.degree ci = 1)
    (hcom : ∀ w w', G.Adj aj w → G.Adj w cj → G.Adj aj w' → G.Adj w' cj → w = w') :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      (∀ Q ∈ D.paths, (Q.src = ci ∨ Q.tgt = ci) → ai ∉ Q.walk.support) ∧
      (∀ Q ∈ D.paths, (Q.src = cj ∨ Q.tgt = cj) → aj ∉ Q.walk.support) := by
  classical
  set P : GPath G := GPath.ofAdj hca with hP
  have hPs : P.src = ci := rfl
  have hPt : P.tgt = aj := rfl
  have hPsupp : P.walk.support = [ci, aj] := rfl
  have hai : ai ∉ P.walk.support := by rw [hPsupp]; simp [haici, haiaj]
  have hne : ci ≠ aj := hca.ne
  -- even vertices of `K₀ = G − ciaj` lie in `{ci, aj}`, and `ci` is isolated
  have hci0 : (delEdgeList G P.edges).degree ci = 0 := by
    have h1 := delEdgeList_degree_le G P.edges ci
    have h2 := delEdgeList_degree_mod G P ci
    have h3 : P.endsAt ci = 1 := by simp [GPath.endsAt, hPs, hPt, Ne.symm hne]
    rw [h3] at h2
    have := hodd ci
    omega
  have hevsub : ∀ v ∈ evenSet (delEdgeList G P.edges), v = aj := by
    intro v hv
    rcases evenSet_delEdgeList_sub G hodd P v hv with h | h
    · rw [hPs] at h; subst h
      rw [mem_evenSet_iff, hci0] at hv; omega
    · rw [h, hPt]
  have hcard : (evenSet (delEdgeList G P.edges)).card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb => by rw [hevsub a ha, hevsub b hb]
  have hcjodd : (delEdgeList G P.edges).degree cj % 2 = 1 := by
    rw [delEdgeList_degree_mod]
    have : P.endsAt cj = 0 := by simp [GPath.endsAt, hPs, hPt, hcij, hajcj]
    rw [this, add_zero, hodd]
  have hnadj : ¬ (delEdgeList G P.edges).Adj cj aj := fun h => hadj h.1
  -- a Lovász decomposition of `K₀` whose path ending at `cⱼ` avoids `aⱼ`
  have hD : AvoidDecomp (delEdgeList G P.edges) cj {aj} := by
    by_cases hajev : aj ∈ evenSet (delEdgeList G P.edges)
    · exact avoidDecomp_of_atMostOneCommon hcard hajev hcjodd hnadj
        fun w w' h1 h2 h3 h4 => hcom w w' h1.1 h2.1 h3.1 h4.1
    · -- `aⱼ` is isolated in `K₀`: no path meets it
      obtain ⟨D₀, hD₀⟩ := lovasz_ends (delEdgeList G P.edges) hcard
      refine ⟨D₀, hD₀, fun Q _ _ a ha haQ => ?_⟩
      rw [Finset.mem_singleton] at ha; subst ha
      have hpos := Q.degree_pos_of_mem haQ
      have h2 := delEdgeList_degree_mod G P a
      have h3 : P.endsAt a = 1 := by simp [GPath.endsAt, hPs, hPt, hne]
      rw [h3] at h2
      have := hodd a
      exact hajev (mem_evenSet_iff.mpr ⟨hpos, by omega⟩)
  obtain ⟨D₀, hD₀, hav⟩ := hD
  exact lemmaR G (fun v _ => hodd v) P hPs hai hcij D₀ (fun v => by rw [hD₀ v]; omega)
    (fun h => absurd (hPt.symm.trans h) hajcj)
    (fun _ Q hQ hQc => hav Q hQ hQc aj (Finset.mem_singleton_self _))

end leafHead

end commonNbr

end Gallai
