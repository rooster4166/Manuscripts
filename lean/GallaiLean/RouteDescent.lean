import GallaiLean.BranchBase
import GallaiLean.CutSelection

/-!
# Route descent: the formal spine of TRC, and minimum T-joins

Route-descent manuscript (`manuscripts/route-descent`), Proposition "existential form and the Lean
spine" and Lemma "minimum T-joins".

* `desc_of_rootedHalfSet`: a realisable set `M ∋ y` of at most half the even vertices gives
  `Desc H k y ∅` for every `k` with `2k ≤ |Ev|` (upward closure on `R ⊆ Ev ∖ M`).
* **`gallai_of_rootedHalfSets`**: if every connected graph of even order has, for each even `y`, a
  realisable set containing `y` of at most half the even vertices, then Gallai's conjecture holds.
  It goes through `BranchBase k` for *every* `k`, without its side hypotheses.
* Pairings and transversals: `IsEvenPairing H σ` (a fixed-point-free involution of `evenSet H`),
  `IsTransversal H σ M`. `two_mul_card_transversal`: transversals have exactly half the even
  vertices. `exists_transversal`: every even vertex lies in some transversal.
* **`gallai_of_pairingTRC`**: abstract TRC ⇒ Gallai. If every connected graph of even order has
  a pairing of its even vertices all of whose transversals are realisable (for instance a
  cut-selection pairing, if TRC holds), then Gallai's conjecture holds.
  `gallai_of_pairingTRCExists` needs, for each even `y`, only one realisable transversal
  containing `y` (the existential form).
* `IsEvenPairing.of_isPairing`: the cut-selection pairings of `cs_all` are even pairings, with the
  same transversals; so `cs_all` supplies the cut-feasibility half of TRC, and `gallai_of_pairingTRC`
  needs only the realisability half.
* **`realisable_of_even_matching`**: TRC for one-edge routes when every even vertex has exactly one
  even neighbour (`G[Ev]` a perfect matching): every transversal is realisable, by Fan descent
  (`realisable_transfer`).
* **`PathDecomp.route_append`**: the extension step of route descent. If the path of `D'` (a
  decomposition of `G − E(R)`) ending at `c` meets the route `R` (from `c` to `a`) only in `c`,
  appending `R` gives a decomposition of `G` of the same size with one end moved from `c` to `a`.
* T-joins: `IsTJoin G T J`, `IsMinTJoin G T J`.
  **`isMinTJoin_sdiff`**: deleting a sub-edge-set `R` of a minimum `T`-join leaves a minimum join
  of `G − R` (for the parity set it induces); this is the heredity of minimality under route
  deletion. `card_le_two_mul_of_isTJoin`, `isMinTJoin_of_two_mul_card_le`: a `T`-join with
  `2|J| ≤ |T|` (e.g. a matching) is minimum.
-/

open SimpleGraph Finset

namespace Gallai

universe u

section spine

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Rooted half-sets.** Every connected graph of even order has, for each even vertex `y`, a
realisable set of even vertices containing `y`, of size at most half the number of even
vertices. -/
def RootedHalfSets : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
    H.Connected → Even (Fintype.card W) → ∀ y ∈ evenSet H,
    ∃ M : Finset W, M ⊆ evenSet H ∧ y ∈ M ∧ 2 * M.card ≤ (evenSet H).card ∧ Realisable H M

/-- A realisable `M ∋ y` with `2|M| ≤ |Ev|` gives `k`-step descent keeping `y`, for every `k`
with `2k ≤ |Ev|`. -/
theorem desc_of_rootedHalfSet {H : SimpleGraph V} [DecidableRel H.Adj] {y : V}
    {M : Finset V} (hM : M ⊆ evenSet H) (hy : y ∈ M) (hcard : 2 * M.card ≤ (evenSet H).card)
    (hR : Realisable H M) {k : ℕ} (hk : 2 * k ≤ (evenSet H).card) : Desc H k y ∅ := by
  have hsize : k ≤ (evenSet H \ M).card := by
    have := Finset.card_sdiff_add_card_eq_card hM
    omega
  obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq hsize
  refine ⟨R, hRsub.trans Finset.sdiff_subset, hRcard, Finset.empty_subset _, ?_, ?_⟩
  · intro hyR
    exact (Finset.mem_sdiff.mp (hRsub hyR)).2 hy
  · refine hR.mono ?_ Finset.sdiff_subset
    intro x hx
    rw [Finset.mem_sdiff]
    exact ⟨hM hx, fun hxR => (Finset.mem_sdiff.mp (hRsub hxR)).2 hx⟩

/-- Rooted half-sets give `BranchBase k` for every `k`. -/
theorem branchBase_of_rootedHalfSets (h : RootedHalfSets.{u}) (k : ℕ) : BranchBase.{u} k := by
  intro W _ _ H _ hconn hev hk y hy _ _
  obtain ⟨M, hM, hyM, hcard, hR⟩ := h W H hconn hev y hy
  exact desc_of_rootedHalfSet hM hyM hcard hR hk

/-- **Rooted half-sets imply Gallai's conjecture.** -/
theorem gallai_of_rootedHalfSets (h : RootedHalfSets.{u}) : GallaiConjecture.{u} :=
  gallai_of_branchBase (branchBase_of_rootedHalfSets h)

/-! ### Pairings and transversals -/

/-- `σ` pairs the even vertices of `H`: it maps `evenSet H` to itself, has no fixed point there,
and is an involution there. -/
structure IsEvenPairing (H : SimpleGraph V) [DecidableRel H.Adj] (σ : V → V) : Prop where
  mem : ∀ v ∈ evenSet H, σ v ∈ evenSet H
  ne : ∀ v ∈ evenSet H, σ v ≠ v
  invol : ∀ v ∈ evenSet H, σ (σ v) = v

omit [DecidableEq V] in
/-- The pairings of `cs_all` (`IsPairing (evenSet H) π`, `PairingLemma.lean`) are even pairings in
the present sense, and `cs_all`'s transversal condition is `IsTransversal`. -/
theorem IsEvenPairing.of_isPairing {H : SimpleGraph V} [DecidableRel H.Adj] {π : V → V}
    (h : IsPairing (evenSet H) π) : IsEvenPairing H π :=
  ⟨fun v hv => (h v hv).1, fun v hv => (h v hv).2.1, fun v hv => (h v hv).2.2⟩

/-- `M` is a transversal of the pairing `σ`: it contains exactly one vertex of every pair. -/
def IsTransversal (H : SimpleGraph V) [DecidableRel H.Adj] (σ : V → V) (M : Finset V) : Prop :=
  M ⊆ evenSet H ∧ ∀ v ∈ evenSet H, (v ∈ M ↔ σ v ∉ M)

/-- A transversal contains exactly half of the even vertices. -/
theorem two_mul_card_transversal {H : SimpleGraph V} [DecidableRel H.Adj] {σ : V → V}
    {M : Finset V} (hσ : IsEvenPairing H σ) (hM : IsTransversal H σ M) :
    2 * M.card = (evenSet H).card := by
  have himg : M.image σ = evenSet H \ M := by
    ext w
    simp only [Finset.mem_image, Finset.mem_sdiff]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hvE := hM.1 hv
      exact ⟨hσ.mem v hvE, (hM.2 v hvE).mp hv⟩
    · rintro ⟨hwE, hwM⟩
      have h1 : σ w ∈ M := by
        by_contra hc
        exact hwM ((hM.2 w hwE).mpr hc)
      exact ⟨σ w, h1, hσ.invol w hwE⟩
  have hinj : Set.InjOn σ M := by
    intro u hu v hv huv
    have hu' := hσ.invol u (hM.1 hu)
    have hv' := hσ.invol v (hM.1 hv)
    rw [← hu', ← hv']
    exact congrArg σ huv
  have hc1 : (M.image σ).card = M.card := Finset.card_image_of_injOn hinj
  have hc2 := Finset.card_sdiff_add_card_eq_card hM.1
  rw [← himg] at hc2
  omega

/-- Every even vertex lies in some transversal. (Choose the earlier vertex of each other pair in
an enumeration of `V`.) -/
theorem exists_transversal {H : SimpleGraph V} [DecidableRel H.Adj] {σ : V → V}
    (hσ : IsEvenPairing H σ) {y : V} (hy : y ∈ evenSet H) :
    ∃ M, IsTransversal H σ M ∧ y ∈ M := by
  classical
  let e := Fintype.equivFin V
  let M : Finset V := (evenSet H).filter (fun v => v = y ∨ (σ v ≠ y ∧ e v < e (σ v)))
  refine ⟨M, ⟨Finset.filter_subset _ _, ?_⟩, ?_⟩
  · intro v hv
    have hσv := hσ.mem v hv
    have hσσ := hσ.invol v hv
    have hne := hσ.ne v hv
    simp only [M, Finset.mem_filter, hv, hσv, true_and, hσσ]
    by_cases hvy : v = y
    · subst hvy
      simp [hne]
    · by_cases hsy : σ v = y
      · simp [hvy, hsy]
      · have hlt : e v ≠ e (σ v) := fun h => hne (e.injective h).symm
        have key : (e v < e (σ v)) ↔ ¬ (e (σ v) < e v) :=
          ⟨fun h1 h2 => lt_asymm h1 h2, fun h => (lt_or_gt_of_ne hlt).resolve_right h⟩
        simpa [hvy, hsy, hσσ] using key
  · simp [M, hy]

/-- Abstract TRC: every connected graph of even order has a pairing of its even vertices all of
whose transversals are realisable. -/
def PairingTRC : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
    H.Connected → Even (Fintype.card W) →
    ∃ σ : W → W, IsEvenPairing H σ ∧ ∀ M, IsTransversal H σ M → Realisable H M

/-- Existential TRC: some pairing has, for every even vertex `y`, a realisable transversal
containing `y`. -/
def PairingTRCExists : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
    H.Connected → Even (Fintype.card W) →
    ∃ σ : W → W, IsEvenPairing H σ ∧ ∀ y ∈ evenSet H, ∃ M, IsTransversal H σ M ∧ y ∈ M ∧
      Realisable H M

theorem pairingTRCExists_of_pairingTRC (h : PairingTRC.{u}) : PairingTRCExists.{u} := by
  intro W _ _ H _ hconn hev
  obtain ⟨σ, hσ, hall⟩ := h W H hconn hev
  refine ⟨σ, hσ, fun y hy => ?_⟩
  obtain ⟨M, hM, hyM⟩ := exists_transversal hσ hy
  exact ⟨M, hM, hyM, hall M hM⟩

theorem rootedHalfSets_of_pairingTRCExists (h : PairingTRCExists.{u}) : RootedHalfSets.{u} := by
  intro W _ _ H _ hconn hev y hy
  obtain ⟨σ, hσ, hex⟩ := h W H hconn hev
  obtain ⟨M, hM, hyM, hR⟩ := hex y hy
  exact ⟨M, hM.1, hyM, (two_mul_card_transversal hσ hM).le, hR⟩

/-- **Existential TRC implies Gallai's conjecture.** -/
theorem gallai_of_pairingTRCExists (h : PairingTRCExists.{u}) : GallaiConjecture.{u} :=
  gallai_of_rootedHalfSets (rootedHalfSets_of_pairingTRCExists h)

/-- **TRC (in the abstract form `PairingTRC`) implies Gallai's conjecture.** -/
theorem gallai_of_pairingTRC (h : PairingTRC.{u}) : GallaiConjecture.{u} :=
  gallai_of_pairingTRCExists (pairingTRCExists_of_pairingTRC h)

end spine

/-! ### Minimum T-joins -/

section tjoins

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- `J` is a `T`-join of `G`: a set of edges of `G` whose odd-degree vertices are exactly `T`. -/
def IsTJoin (G : SimpleGraph V) (T : Finset V) (J : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ J, e ∈ G.edgeSet) ∧ ∀ v, (Odd (edgeDeg J v) ↔ v ∈ T)

/-- `J` is a minimum `T`-join of `G` (fewest edges). -/
def IsMinTJoin (G : SimpleGraph V) (T : Finset V) (J : Finset (Sym2 V)) : Prop :=
  IsTJoin G T J ∧ ∀ K, IsTJoin G T K → J.card ≤ K.card

omit [Fintype V] in
theorem edgeDeg_union_of_disjoint {A B : Finset (Sym2 V)} (h : Disjoint A B) (v : V) :
    edgeDeg (A ∪ B) v = edgeDeg A v + edgeDeg B v := by
  unfold edgeDeg
  rw [Finset.filter_union, Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter h)]

/-- **Heredity of minimality.** If `J` is a minimum `T`-join of `G` and `R ⊆ J`, then `J ∖ R` is
a minimum join of `G − R` for its own odd set. (Route deletion: `R` the edges of a route.) -/
theorem isMinTJoin_sdiff {G : SimpleGraph V} {T : Finset V} {J R : Finset (Sym2 V)}
    (hJ : IsMinTJoin G T J) (hRJ : R ⊆ J) :
    IsMinTJoin (G.deleteEdges (R : Set (Sym2 V)))
      (Finset.univ.filter (fun v => Odd (edgeDeg (J \ R) v))) (J \ R) := by
  refine ⟨⟨fun e he => ?_, fun v => by simp⟩, fun K hK => ?_⟩
  · rw [Finset.mem_sdiff] at he
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact ⟨hJ.1.1 e he.1, by simpa using he.2⟩
  · -- `K ∪ R` is a `T`-join of `G`
    have hKR : Disjoint K R := by
      rw [Finset.disjoint_left]
      intro e heK heR
      have := hK.1 e heK
      rw [SimpleGraph.edgeSet_deleteEdges] at this
      exact this.2 (by simpa using heR)
    have hJR : J = (J \ R) ∪ R := (Finset.sdiff_union_of_subset hRJ).symm
    have hdisjJ : Disjoint (J \ R) R := Finset.sdiff_disjoint
    have hT : IsTJoin G T (K ∪ R) := by
      refine ⟨fun e he => ?_, fun v => ?_⟩
      · rcases Finset.mem_union.mp he with he | he
        · have := hK.1 e he
          rw [SimpleGraph.edgeSet_deleteEdges] at this
          exact this.1
        · exact hJ.1.1 e (hRJ he)
      · rw [edgeDeg_union_of_disjoint hKR, ← hJ.1.2 v, hJR,
          edgeDeg_union_of_disjoint hdisjJ, Nat.odd_add, Nat.odd_add]
        have hk := hK.2 v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        rw [hk]
    have h1 := hJ.2 _ hT
    rw [Finset.card_union_of_disjoint hKR] at h1
    have h2 : J.card = (J \ R).card + R.card := by
      rw [← Finset.card_union_of_disjoint hdisjJ, ← hJR]
    omega

/-- Every `T`-join has at least `|T| / 2` edges. -/
theorem card_le_two_mul_of_isTJoin {G : SimpleGraph V} {T : Finset V} {K : Finset (Sym2 V)}
    (hK : IsTJoin G T K) : T.card ≤ 2 * K.card := by
  classical
  have hsum : ∑ v, edgeDeg K v = 2 * K.card := by
    unfold edgeDeg
    have : ∀ v, #(K.filter (fun e => v ∈ e)) = ∑ e ∈ K, (if v ∈ e then 1 else 0) := by
      intro v
      rw [Finset.card_filter]
    simp_rw [this]
    rw [Finset.sum_comm, mul_comm, Finset.sum_const_nat]
    intro e he
    have hnd : ¬ e.IsDiag := G.not_isDiag_of_mem_edgeSet (hK.1 e he)
    induction e using Sym2.inductionOn with
    | hf a b =>
      have hab : a ≠ b := fun h => hnd (by simp [h])
      rw [← Finset.card_filter,
        show (Finset.univ.filter (fun v => v ∈ s(a, b))) = {a, b} by ext v; simp]
      exact Finset.card_pair hab
  have hle : ∑ v ∈ T, 1 ≤ ∑ v, edgeDeg K v := by
    calc ∑ v ∈ T, 1 ≤ ∑ v ∈ T, edgeDeg K v := by
          apply Finset.sum_le_sum
          intro v hv
          have := (hK.2 v).mpr hv
          exact Nat.one_le_iff_ne_zero.mpr (fun h => by rw [h] at this; exact Nat.not_odd_zero this)
      _ ≤ ∑ v, edgeDeg K v := Finset.sum_le_sum_of_subset (Finset.subset_univ T)
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hle
  omega

/-- A `T`-join with at most `|T| / 2` edges (for instance a matching) is minimum. -/
theorem isMinTJoin_of_two_mul_card_le {G : SimpleGraph V} {T : Finset V} {K : Finset (Sym2 V)}
    (hK : IsTJoin G T K) (h : 2 * K.card ≤ T.card) : IsMinTJoin G T K :=
  ⟨hK, fun K' hK' => by have := card_le_two_mul_of_isTJoin hK'; omega⟩

end tjoins

/-! ### TRC for one-edge routes when `G[Ev]` is a perfect matching -/

section evenMatching

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **TRC for one-edge routes in the Fan-isolated case** (route-descent manuscript, Theorem
"Fan-isolated routes" with every route an edge). If every even vertex has exactly one even
neighbour, then every set `M` of even vertices containing exactly one end of every edge of
`G[Ev]` is realisable. Induction on `|Ev|`: delete the edge `ac` at some `a ∈ M` and restore it by
Fan's transfer (`realisable_transfer`), which applies because `a` has no other even neighbour. -/
theorem realisable_of_even_matching : ∀ (n : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj],
    (evenSet G).card = n →
    (∀ u ∈ evenSet G, ∀ v ∈ evenSet G, ∀ w ∈ evenSet G, G.Adj u v → G.Adj u w → v = w) →
    (∀ u ∈ evenSet G, ∃ v ∈ evenSet G, G.Adj u v) →
    ∀ M : Finset V, M ⊆ evenSet G →
      (∀ u ∈ evenSet G, ∀ v ∈ evenSet G, G.Adj u v → (u ∈ M ↔ v ∉ M)) →
      Realisable G M := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ hn huniq hex M hM htr
  by_cases hMe : M = ∅
  · subst hMe
    have hE : evenSet G = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro u hu
      obtain ⟨v, hv, huv⟩ := hex u hu
      have := htr u hu v hv huv
      simp at this
    have h := realisable_evenSet_ni G
    rwa [hE] at h
  · obtain ⟨a, haM⟩ := Finset.nonempty_iff_ne_empty.mpr hMe
    have haE := hM haM
    obtain ⟨c, hcE, hac⟩ := hex a haE
    have hcM : c ∉ M := (htr a haE c hcE hac).mp haM
    have hEK := evenSet_delE_even haE hcE hac
    have hne : a ≠ c := hac.ne
    have hmemK : ∀ u, u ∈ evenSet (delE G {s(a, c)}) ↔ u ∈ evenSet G ∧ u ≠ a ∧ u ≠ c := by
      intro u
      rw [hEK, Finset.mem_erase, Finset.mem_erase]
      tauto
    have hKG : ∀ x y, (delE G {s(a, c)}).Adj x y → G.Adj x y := fun x y h => (delE_adj.mp h).1
    have hcardK : (evenSet (delE G {s(a, c)})).card < n := by
      rw [hEK]
      have h1 := Finset.card_erase_of_mem haE
      have h2 : c ∈ (evenSet G).erase a := Finset.mem_erase.mpr ⟨hne.symm, hcE⟩
      have h3 := Finset.card_erase_of_mem h2
      have hpos : 0 < (evenSet G).card := Finset.card_pos.mpr ⟨a, haE⟩
      omega
    have hR : Realisable (delE G {s(a, c)}) (M.erase a) := by
      refine ih _ hcardK (delE G {s(a, c)}) rfl ?_ ?_ (M.erase a) ?_ ?_
      · intro u hu v hv w hw huv huw
        exact huniq u ((hmemK u).1 hu).1 v ((hmemK v).1 hv).1 w ((hmemK w).1 hw).1
          (hKG _ _ huv) (hKG _ _ huw)
      · intro u hu
        obtain ⟨huE, hua, huc⟩ := (hmemK u).1 hu
        obtain ⟨v, hvE, huv⟩ := hex u huE
        have hva : v ≠ a := by
          rintro rfl
          exact huc (huniq v hvE u huE c hcE huv.symm hac)
        have hvc : v ≠ c := by
          rintro rfl
          exact hua (huniq v hvE u huE a haE huv.symm hac.symm)
        refine ⟨v, (hmemK v).2 ⟨hvE, hva, hvc⟩, delE_adj.mpr ⟨huv, ?_⟩⟩
        rw [Finset.mem_singleton]
        intro h
        rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hua h1
        · exact huc h1
      · intro x hx
        obtain ⟨hxa, hxM⟩ := Finset.mem_erase.mp hx
        exact (hmemK x).2 ⟨hM hxM, hxa, fun h => hcM (h ▸ hxM)⟩
      · intro u hu v hv huv
        obtain ⟨huE, hua, -⟩ := (hmemK u).1 hu
        obtain ⟨hvE, hva, -⟩ := (hmemK v).1 hv
        rw [Finset.mem_erase, Finset.mem_erase]
        have := htr u huE v hvE (hKG _ _ huv)
        tauto
    have hfinal := realisable_transfer haE hcE hac hR (by
      intro u hu _ hau
      obtain ⟨huE, -, huc⟩ := (hmemK u).1 hu
      exact huc (huniq a haE u huE c hcE hau hac))
    rwa [Finset.insert_erase haM] at hfinal

end evenMatching

/-! ### The extension step: appending a route -/

section append

variable {U : Type u} [DecidableEq U]

/-- **Appending a route** (route-descent manuscript, Lemma "extension", (i) ⇒ (ii)). Let `R` be a
path of `G` from `c` to `a`, let `K = G − E(R)`, and let `D'` decompose `K`. If some path `Q` of
`D'` ends at `c` and meets `R` only in `c`, then `Q ∪ R` is a path, and replacing `Q` by it gives
a decomposition of `G` of the same size with one end moved from `c` to `a`, in which `R` is a terminal
segment, ending at `a`, of some path. -/
theorem PathDecomp.route_append {G K : SimpleGraph U} {R : GPath G} {a c : U}
    (hRs : R.src = c) (hRt : R.tgt = a)
    (hK : ∀ e, e ∈ K.edgeSet ↔ e ∈ G.edgeSet ∧ e ∉ R.edges)
    (D' : PathDecomp K) {Q : GPath K} (hQ : Q ∈ D'.paths) (hQc : Q.src = c ∨ Q.tgt = c)
    (hdisj : ∀ x ∈ Q.walk.support, x ∈ R.walk.support → x = c) :
    ∃ D : PathDecomp G, D.size = D'.size ∧
      (∀ w, D.ends w + (if c = w then 1 else 0) = D'.ends w + (if a = w then 1 else 0)) ∧
      ∃ P ∈ D.paths, ∃ hPt : P.tgt = a, ∃ p : G.Walk P.src c,
        P.walk.copy rfl hPt = p.append (R.walk.copy hRs hRt) := by
  obtain ⟨Q₁, hQ₁s, hQ₁e, hQ₁ends, hQ₁supp⟩ := Q.exists_orient hQc
  have hKG : ∀ e ∈ Q₁.walk.reverse.edges, e ∈ G.edgeSet := by
    intro e he
    rw [Walk.edges_reverse, List.mem_reverse] at he
    exact ((hK e).1 (Q₁.walk.edges_subset_edgeSet he)).1
  let A : G.Walk Q₁.tgt c := (Q₁.walk.reverse.transfer G hKG).copy rfl hQ₁s
  let B : G.Walk c a := R.walk.copy hRs hRt
  have hAsupp : ∀ x, x ∈ A.support ↔ x ∈ Q.walk.support := by
    intro x
    simp only [A, Walk.support_copy, Walk.support_transfer, Walk.support_reverse, List.mem_reverse]
    exact hQ₁supp x
  have hBsupp : B.support = R.walk.support := by simp [B]
  have hAedges : A.edges = Q₁.edges.reverse := by
    simp [A, GPath.edges, Walk.edges_copy, Walk.edges_transfer, Walk.edges_reverse]
  have hBedges : B.edges = R.edges := by simp [B, GPath.edges]
  have hWpath : (A.append B).IsPath := by
    rw [Walk.isPath_append]
    refine ⟨?_, ?_, ?_⟩
    · simp only [A, Walk.isPath_copy]
      exact (Walk.isPath_transfer _).mpr Q₁.isPath.reverse
    · have hB : B.IsPath := by simp only [B, Walk.isPath_copy]; exact R.isPath
      exact hB.tail
    · intro x hxA hxB
      have hBnd : B.support.Nodup := (Walk.isPath_def _).mp (by simp only [B, Walk.isPath_copy]; exact R.isPath)
      have hxc : x ≠ c := by
        rintro rfl
        have hsc : ∀ {u v : U} (p : G.Walk u v), p.support = u :: p.support.tail := by
          intro u v p; cases p <;> rfl
        rw [hsc B] at hBnd
        exact (List.nodup_cons.mp hBnd).1 hxB
      have hxR : x ∈ R.walk.support := by
        rw [← hBsupp]; exact List.mem_of_mem_tail hxB
      exact hxc (hdisj x ((hAsupp x).1 hxA) hxR)
  have hpos : 0 < (A.append B).length := by
    rw [Walk.length_append]
    have : 0 < B.length := by simp only [B, Walk.length_copy]; exact R.pos
    omega
  let P' : GPath G := ⟨Q₁.tgt, a, A.append B, hWpath, hpos⟩
  have hP'edges : P'.edges = Q₁.edges.reverse ++ R.edges := by
    show (A.append B).edges = _
    rw [Walk.edges_append, hAedges, hBedges]
  have hmemP' : ∀ e, e ∈ P'.edges ↔ e ∈ Q.edges ∨ e ∈ R.edges := by
    intro e
    rw [hP'edges, List.mem_append, List.mem_reverse, hQ₁e.mem_iff]
  obtain ⟨D, hsize, hP'mem, hends, -⟩ := D'.replace hQ P' (by
      intro e
      rw [hmemP' e]
      constructor
      · intro he
        by_cases heR : e ∈ R.edges
        · exact Or.inr (Or.inr heR)
        · by_cases heQ : e ∈ Q.edges
          · exact Or.inr (Or.inl heQ)
          · exact Or.inl ⟨(hK e).2 ⟨he, heR⟩, heQ⟩
      · rintro (⟨he, -⟩ | heQ | heR)
        · exact ((hK e).1 he).1
        · exact ((hK e).1 (Q.walk.edges_subset_edgeSet heQ)).1
        · exact R.walk.edges_subset_edgeSet heR)
    (by
      intro e he
      rcases (hmemP' e).1 he with heQ | heR
      · exact Or.inl heQ
      · exact Or.inr (fun hk => ((hK e).1 hk).2 heR))
  refine ⟨D, hsize, fun w => ?_, P', hP'mem, rfl, A, rfl⟩
  have h1 := hends w
  have h2 : P'.endsAt w = (if Q₁.tgt = w then 1 else 0) + (if a = w then 1 else 0) := rfl
  have h3 : Q.endsAt w = (if c = w then 1 else 0) + (if Q₁.tgt = w then 1 else 0) := by
    rw [← hQ₁ends w]; simp only [GPath.endsAt, hQ₁s]
  omega

end append

end Gallai
