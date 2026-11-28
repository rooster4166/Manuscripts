import GallaiLean.LemmaR

/-!
# Joint pre-committed paths: proved cases of Conjecture J (session `claude/conj-r`)

Manuscript `manuscripts/conj-r`, Section 5.

Case (a) of Lemma R: `P` is a path from `c₁` to `c₂` avoiding `a₁, a₂`, and `K₀ = G − E(P)`
needs a parity decomposition. Its even vertices lie in `{c₁, c₂}` (`evenSet_delEdgeList_sub`).
Three ways to get one, each giving `L_N(2)` with `Q(c₁) = Q(c₂) = P`:
* **`joint_of_card`**: `K₀` has at most one even vertex (Lovász); e.g. `d(c₁) = 1`
  (**`joint_of_leaf`**).
* **`joint_of_supp`**: `c₁` (or `c₂`) has exactly two neighbours in `K₀`, and they are
  non-adjacent: suppress it.
* **`joint_of_steer`**: a steering sequence (NA's `Steer`) from one end avoiding a set `X ⊇ N_{K₀}[h]`,
  where `h` is the other end: the token walks to retirement while the other token stays put
  (**`steerK_of_steer`**: such a sequence is a multi-token schedule).
-/

open SimpleGraph

namespace Gallai

universe u

section steer

variable {U : Type u} [Fintype U] [DecidableEq U]

/-- **A steering sequence is a two-token schedule.** If `h ∈ X ⊇ N(h)`, the even vertices of `K`
are `g` and possibly `h`, and `Steer X K g`, then `(K, ∅)` has a multi-token schedule: the token at
`g` walks along the sequence (every target lies outside `X`, so it is never adjacent to the token
at `h`) and retires at its end. -/
theorem steerK_of_steer {X : Finset U} {h : U} (hhX : h ∈ X) :
    ∀ {K : SimpleGraph U} {g : U}, Steer X K g → ∀ [DecidableRel K.Adj],
      (∀ v, K.Adj h v → v ∈ X) → g ∈ evenSet K → (∀ v ∈ evenSet K, v = g ∨ v = h) →
      SteerK (∅ : Finset (U × U × U)) K (evenSet K) := by
  intro K g hS
  induction hS with
  | @last K g u hgu huX hiso =>
    intro _ hX hg hev
    classical
    have hug : u ≠ g := hgu.ne.symm
    have hun : u ∉ evenSet K := by
      intro hu
      rcases hev u hu with h1 | h1
      · exact hug h1
      · exact huX (h1 ▸ hhX)
    set τ' := Finset.univ.filter (fun v => (v ∈ evenSet K ∧ v ≠ g) ∨
      (v = u ∧ ∃ q, (delEdge K u g).Adj u q)) with hτ'
    have hchar : ∀ v, v ∈ τ' ↔ (v ∈ evenSet K ∧ v ≠ g) ∨
        (v = u ∧ ∃ q, (delEdge K u g).Adj u q) := by
      intro v; simp [hτ']
    refine SteerK.move hg hgu hun (fun t ht => absurd ht (Finset.notMem_empty t)) ?_ hchar ?_
    · intro v hv hvg hadj
      rcases hev v hv with h1 | h1
      · exact hvg h1
      · subst h1
        exact huX (hX u hadj.1.symm)
    · refine SteerK.fin ?_ (fun t ht => absurd ht (Finset.notMem_empty t))
      refine Finset.card_le_one.mpr fun a ha b hb => ?_
      have hno : ¬ ∃ q, (delEdge K u g).Adj u q := by
        rintro ⟨q, hq⟩
        exact hq.2 (by rw [hiso q hq.1])
      have key : ∀ v ∈ τ', v = h := by
        intro v hv
        rcases (hchar v).mp hv with ⟨hv1, hv2⟩ | ⟨-, hq⟩
        · exact (hev v hv1).resolve_left hv2
        · exact absurd hq hno
      rw [key a ha, key b hb]
  | @step K g u hgu huX hS' ih =>
    intro _ hX hg hev
    classical
    have hug : u ≠ g := hgu.ne.symm
    have hun : u ∉ evenSet K := by
      intro hu
      rcases hev u hu with h1 | h1
      · exact hug h1
      · exact huX (h1 ▸ hhX)
    have hchar : ∀ v, v ∈ evenSet (delEdge K u g) ↔ (v ∈ evenSet K ∧ v ≠ g) ∨
        (v = u ∧ ∃ q, (delEdge K u g).Adj u q) := by
      intro v
      set τ' := Finset.univ.filter (fun v => (v ∈ evenSet K ∧ v ≠ g) ∨
        (v = u ∧ ∃ q, (delEdge K u g).Adj u q)) with hτ'
      have hc : ∀ v, v ∈ τ' ↔ (v ∈ evenSet K ∧ v ≠ g) ∨
          (v = u ∧ ∃ q, (delEdge K u g).Adj u q) := by
        intro v; simp [hτ']
      rw [evenSet_move K hg hgu hun hc, hc]
    refine SteerK.move hg hgu hun (fun t ht => absurd ht (Finset.notMem_empty t)) ?_ hchar ?_
    · intro v hv hvg hadj
      rcases hev v hv with h1 | h1
      · exact hvg h1
      · subst h1
        exact huX (hX u hadj.1.symm)
    · refine ih (fun v hv => hX v hv.1) ((hchar u).mpr (Or.inr ⟨rfl, hS'.exists_adj⟩)) ?_
      intro v hv
      rcases (hchar v).mp hv with ⟨hv1, hv2⟩ | ⟨rfl, -⟩
      · exact Or.inr ((hev v hv1).resolve_left hv2)
      · exact Or.inl rfl

end steer

section joint

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The even vertices of `G − E(P)` are ends of `P`, when `G` has no even vertex. -/
theorem evenSet_delEdgeList_sub (G : SimpleGraph V) [DecidableRel G.Adj]
    (hodd : ∀ v, G.degree v % 2 = 1) (P : GPath G) :
    ∀ v ∈ evenSet (delEdgeList G P.edges), v = P.src ∨ v = P.tgt := by
  intro v hv
  rw [mem_evenSet_iff] at hv
  have h := delEdgeList_degree_mod G P v
  rw [hv.2] at h
  have hgv := hodd v
  by_contra hne
  push Not at hne
  have : P.endsAt v = 0 := by simp [GPath.endsAt, Ne.symm hne.1, Ne.symm hne.2]
  rw [this] at h
  omega

/-- `G − E(P)` is a subgraph of `G`. -/
theorem delEdgeList_degree_le (G : SimpleGraph V) [DecidableRel G.Adj] (S : List (Sym2 V))
    (v : V) : (delEdgeList G S).degree v ≤ G.degree v := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  exact Finset.card_le_card fun w hw => by
    rw [mem_neighborFinset] at hw ⊢; exact hw.1

/-- The joint form of Lemma R: a parity decomposition of `K₀` finishes. -/
theorem joint_of_D₀ (G : SimpleGraph V) [DecidableRel G.Adj] (hodd : ∀ v, G.degree v % 2 = 1)
    {c₁ a₁ c₂ a₂ : V} (h12 : c₁ ≠ c₂) (P : GPath G) (hPs : P.src = c₁) (hPt : P.tgt = c₂)
    (ha₁ : a₁ ∉ P.walk.support) (ha₂ : a₂ ∉ P.walk.support)
    (D₀ : PathDecomp (delEdgeList G P.edges))
    (hD₀ : ∀ v, D₀.ends v = (delEdgeList G P.edges).degree v % 2) :
    LN2Good G c₁ a₁ c₂ a₂ :=
  lemmaR G (fun v _ => hodd v) P hPs ha₁ h12 D₀ (fun v => by rw [hD₀ v]; omega)
    (fun _ => ha₂) (fun h => absurd hPt h)

/-- **Joint case with at most one even vertex left** (Lovász). -/
theorem joint_of_card (G : SimpleGraph V) [DecidableRel G.Adj] (hodd : ∀ v, G.degree v % 2 = 1)
    {c₁ a₁ c₂ a₂ : V} (h12 : c₁ ≠ c₂) (P : GPath G) (hPs : P.src = c₁) (hPt : P.tgt = c₂)
    (ha₁ : a₁ ∉ P.walk.support) (ha₂ : a₂ ∉ P.walk.support)
    (hcard : (evenSet (delEdgeList G P.edges)).card ≤ 1) : LN2Good G c₁ a₁ c₂ a₂ := by
  obtain ⟨D₀, hD₀⟩ := lovasz_ends (delEdgeList G P.edges) hcard
  exact joint_of_D₀ G hodd h12 P hPs hPt ha₁ ha₂ D₀ hD₀

/-- **(C1) A leaf at one end.** If `c₁` and `c₂` are joined by a path avoiding `a₁, a₂` and `c₁` has
degree one, then `L_N(2)` holds, with `Q(c₁) = Q(c₂)`. -/
theorem joint_of_leaf (G : SimpleGraph V) [DecidableRel G.Adj] (hodd : ∀ v, G.degree v % 2 = 1)
    {c₁ a₁ c₂ a₂ : V} (h12 : c₁ ≠ c₂) (P : GPath G) (hPs : P.src = c₁) (hPt : P.tgt = c₂)
    (ha₁ : a₁ ∉ P.walk.support) (ha₂ : a₂ ∉ P.walk.support) (hleaf : G.degree c₁ = 1) :
    LN2Good G c₁ a₁ c₂ a₂ := by
  refine joint_of_card G hodd h12 P hPs hPt ha₁ ha₂ ?_
  have hc₁ : c₁ ∉ evenSet (delEdgeList G P.edges) := by
    rw [mem_evenSet_iff]
    rintro ⟨hpos, hev⟩
    have := delEdgeList_degree_le G P.edges c₁
    omega
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  have key : ∀ v ∈ evenSet (delEdgeList G P.edges), v = c₂ := by
    intro v hv
    rcases evenSet_delEdgeList_sub G hodd P v hv with h | h
    · rw [hPs] at h; subst h; exact absurd hv hc₁
    · rw [h, hPt]
  rw [key a ha, key b hb]

/-- **(C2) Suppression at one end.** If an end `g ∈ {c₁, c₂}` of the joint path has exactly two
neighbours `y ≠ z` in `K₀`, and `y ≁ z` in `K₀`, then `L_N(2)` holds with `Q(c₁) = Q(c₂) = P`. -/
theorem joint_of_supp (G : SimpleGraph V) [DecidableRel G.Adj] (hodd : ∀ v, G.degree v % 2 = 1)
    {c₁ a₁ c₂ a₂ : V} (h12 : c₁ ≠ c₂) (P : GPath G) (hPs : P.src = c₁) (hPt : P.tgt = c₂)
    (ha₁ : a₁ ∉ P.walk.support) (ha₂ : a₂ ∉ P.walk.support) {g y z : V} (hg : g = c₁ ∨ g = c₂)
    (hN : ∀ v, (delEdgeList G P.edges).Adj g v ↔ v = y ∨ v = z) (hyz : y ≠ z)
    (hnyz : ¬ (delEdgeList G P.edges).Adj y z) : LN2Good G c₁ a₁ c₂ a₂ := by
  classical
  have hgdeg : (delEdgeList G P.edges).degree g = 2 := by
    rw [← card_neighborFinset_eq_degree]
    have : (delEdgeList G P.edges).neighborFinset g = {y, z} := by
      ext v; rw [mem_neighborFinset, hN, Finset.mem_insert, Finset.mem_singleton]
    rw [this, Finset.card_pair hyz]
  have hgev : g ∈ evenSet (delEdgeList G P.edges) := by rw [mem_evenSet_iff, hgdeg]; omega
  have hsys : TailSys (∅ : Finset (V × V × V)) :=
    ⟨fun t ht => absurd ht (Finset.notMem_empty t), fun t ht => absurd ht (Finset.notMem_empty t),
      fun t ht => absurd ht (Finset.notMem_empty t)⟩
  have hS : SteerK (∅ : Finset (V × V × V)) (delEdgeList G P.edges) (evenSet (delEdgeList G P.edges)) := by
    refine SteerK.supp hgev hN hyz hnyz (fun t ht => absurd ht (Finset.notMem_empty t)) ?_
    refine SteerK.fin ?_ (fun t ht => absurd ht (Finset.notMem_empty t))
    have key : ∀ v ∈ (evenSet (delEdgeList G P.edges)).erase g, v = (if g = c₁ then c₂ else c₁) := by
      intro v hv
      rw [Finset.mem_erase] at hv
      rcases evenSet_delEdgeList_sub G hodd P v hv.2 with h | h
      · rw [hPs] at h
        rcases hg with rfl | rfl
        · exact absurd h hv.1
        · simp [Ne.symm h12, h]
      · rw [hPt] at h
        rcases hg with rfl | rfl
        · simp [h]
        · exact absurd h hv.1
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    rw [key a ha, key b hb]
  obtain ⟨D₀, hD₀, -⟩ := steerK_good hsys hS rfl (fun t ht => absurd ht (Finset.notMem_empty t))
  exact joint_of_D₀ G hodd h12 P hPs hPt ha₁ ha₂ D₀ hD₀

/-- **(C3) Static steering at one end.** Let `{g, h} = {c₁, c₂}` and let `X ∋ h` contain every
neighbour of `h` in `K₀ = G − E(P)`. A steering sequence from `g` avoiding `X` in `K₀` gives `L_N(2)` with
`Q(c₁) = Q(c₂) = P`. -/
theorem joint_of_steer (G : SimpleGraph V) [DecidableRel G.Adj] (hodd : ∀ v, G.degree v % 2 = 1)
    {c₁ a₁ c₂ a₂ : V} (h12 : c₁ ≠ c₂) (P : GPath G) (hPs : P.src = c₁) (hPt : P.tgt = c₂)
    (ha₁ : a₁ ∉ P.walk.support) (ha₂ : a₂ ∉ P.walk.support) {g h : V}
    (hgh : (g = c₁ ∧ h = c₂) ∨ (g = c₂ ∧ h = c₁)) {X : Finset V} (hhX : h ∈ X)
    (hX : ∀ v, (delEdgeList G P.edges).Adj h v → v ∈ X)
    (hS : Steer X (delEdgeList G P.edges) g) : LN2Good G c₁ a₁ c₂ a₂ := by
  classical
  have hgend : P.src = g ∨ P.tgt = g := by
    rcases hgh with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl hPs
    · exact Or.inr hPt
  have hgev : g ∈ evenSet (delEdgeList G P.edges) := by
    rw [mem_evenSet_iff]
    obtain ⟨u, hu⟩ := hS.exists_adj
    refine ⟨((delEdgeList G P.edges).degree_pos_iff_exists_adj g).mpr ⟨u, hu⟩, ?_⟩
    have h1 := delEdgeList_degree_mod G P g
    have h2 : P.endsAt g = 1 := by
      have := P.incid_add_endsAt g
      have hmem : g ∈ P.walk.support := by
        rcases hgend with h | h
        · rw [← h]; exact P.walk.start_mem_support
        · rw [← h]; exact P.walk.end_mem_support
      simp only [P.incid_of_end hgend, hmem, ite_true] at this
      omega
    rw [h2] at h1
    have := hodd g
    omega
  have hev : ∀ v ∈ evenSet (delEdgeList G P.edges), v = g ∨ v = h := by
    intro v hv
    rcases evenSet_delEdgeList_sub G hodd P v hv with e | e <;>
      rcases hgh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (e.trans hPs)
    · exact Or.inr (e.trans hPs)
    · exact Or.inr (e.trans hPt)
    · exact Or.inl (e.trans hPt)
  have hsys : TailSys (∅ : Finset (V × V × V)) :=
    ⟨fun t ht => absurd ht (Finset.notMem_empty t), fun t ht => absurd ht (Finset.notMem_empty t),
      fun t ht => absurd ht (Finset.notMem_empty t)⟩
  have hSK := steerK_of_steer hhX hS hX hgev hev
  obtain ⟨D₀, hD₀, -⟩ := steerK_good hsys hSK rfl (fun t ht => absurd ht (Finset.notMem_empty t))
  exact joint_of_D₀ G hodd h12 P hPs hPt ha₁ ha₂ D₀ hD₀

/-- **(C3), structural form** (manuscript Lemma S with the subgraph of NA's walking lemma). Let
`{g, h} = {c₁, c₂}`, `X ∋ h` with `N_{K₀}(h) ⊆ X`, and let `S ≤ K₀` have no edge at `X`, contain every
edge of `K₀` at the vertices satisfying `A`, have all its odd vertices other than `g` in `A`, and
have `g` odd in `S` (or `A g`) with `d_S(g) > 0`. Then `L_N(2)` holds with `Q(c₁) = Q(c₂) = P`. -/
theorem joint_of_inv (G : SimpleGraph V) [DecidableRel G.Adj] (hodd : ∀ v, G.degree v % 2 = 1)
    {c₁ a₁ c₂ a₂ : V} (h12 : c₁ ≠ c₂) (P : GPath G) (hPs : P.src = c₁) (hPt : P.tgt = c₂)
    (ha₁ : a₁ ∉ P.walk.support) (ha₂ : a₂ ∉ P.walk.support) {g h : V}
    (hgh : (g = c₁ ∧ h = c₂) ∨ (g = c₂ ∧ h = c₁)) {X : Finset V} (hhX : h ∈ X)
    (hX : ∀ v, (delEdgeList G P.edges).Adj h v → v ∈ X)
    (A : V → Prop) (S : SimpleGraph V) [DecidableRel S.Adj] (hSK : S ≤ delEdgeList G P.edges)
    (hSX : ∀ a b, S.Adj a b → b ∉ X)
    (hAK : ∀ v, A v → ∀ w, (delEdgeList G P.edges).Adj v w → S.Adj v w)
    (hoddA : ∀ v, v ≠ g → S.degree v % 2 = 1 → A v) (hg : A g ∨ S.degree g % 2 = 1)
    (hgpos : 0 < S.degree g) : LN2Good G c₁ a₁ c₂ a₂ :=
  joint_of_steer G hodd h12 P hPs hPt ha₁ ha₂ hgh hhX hX
    (steer_of_inv A _ (delEdgeList G P.edges) S g rfl hSK hSX hAK hoddA hg hgpos)

end joint

end Gallai
