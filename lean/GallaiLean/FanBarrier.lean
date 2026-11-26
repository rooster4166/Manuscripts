import GallaiLean.BranchBase
import GallaiLean.Critical

/-!
# Stronger induction hypotheses: what transfers can and cannot do

Two results about the transfer steps of the descent reduction (`BranchBase.lean`).

**Two even neighbours reduce** (manuscript: endpoint-structure, Section 7).
If the even vertex `y` has exactly two even neighbours `a, b`, delete `ya` and use descent in
`G − ya` keeping `b`; the transfer of `ya` towards `y` then needs no other prescribed vertex
(`desc_succ_of_transfer_two`). So the branching base case only has to treat vertices with at least
three even neighbours:

* `BranchBase3 k`: `BranchBase k` restricted to `y` with three distinct even neighbours;
* `branchBase_of_three`: `D⁰_k` and `BranchBase3 (k+1)` give `BranchBase (k+1)`;
* `gallai_of_branchBase3`: `(∀ k ≥ 3, BranchBase3 k) → GallaiConjecture`.

**The last-edge barrier.** Every certificate built from a decomposition of a proper spanning
subgraph by Fan moves ends by re-inserting one edge `ut` into `H = G − ut`: by a single Fan
transfer, or as a new one-edge path. Both moves obey a counting bound.

* `fan_transfer_barrier`: if `D` decomposes `H`, `ut ∉ E(H)`, and Fan's condition
  `#{w ∈ N_H(u) : ends w = 0} < ends t` holds, then
  `ends u + 2·#{w ∈ N_H(u) : deg_H w even} + 2 ≤ 3·|D|`.
* `card_edgeFinset_le_size_mul`: `|E(H)| ≤ |D|·(n − 1)`.
* `fan_transfer_barrier_regular`, `newpath_barrier_regular`: the two bounds for `d`-regular `G`
  with `d` even.
* `cocktail`: the cocktail party graph `CP(m) = K_{2m}` minus a perfect matching, on
  `Fin m × Bool`; `cocktail_degree`: it is `(2m − 2)`-regular.
* `insertion_barrier_regular`, **`cocktail_insertion_barrier`**: a new path made of the held
  edges `F` can finish `CP(m)` with at most `m` paths only if `|F| ≥ m − 1`.
* **`cocktail_fan_barrier`**: for `m ≥ 4`, every edge `ut` of `CP(m)` and every decomposition `D`
  of `CP(m) − ut`, `m ≤ |D|`, and `m < |D|` if Fan's condition for a transfer towards `u` holds.
  So no Fan move on the last edge produces a decomposition of `CP(m)` into at most `m` paths,
  whatever the seed and whatever the induction hypothesis that produced `D`.
-/

open SimpleGraph Finset

namespace Gallai

universe u

section two

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Transfer with one prescribed vertex.** If the even vertex `y` has exactly the even
neighbours `a ≠ b`, then descent in `G − ya` keeping `b` transfers to descent in `G` keeping `y`,
one level higher. -/
theorem desc_succ_of_transfer_two {k : ℕ} {y a b : V} (hy : y ∈ evenSet G)
    (ha : a ∈ evenSet G) (hya : G.Adj y a) (hab : a ≠ b)
    (htwo : ∀ v ∈ evenSet G, G.Adj y v → v = a ∨ v = b)
    (hdesc : Desc (delE G {s(y, a)}) k b ∅) : Desc G (k + 1) y ∅ := by
  have hya' : y ≠ a := hya.ne
  have hEvK := evenSet_delE_even hy ha hya
  obtain ⟨W', hWK, hWc, -, hbW, hreal⟩ := hdesc
  have hWE : ∀ x ∈ W', x ∈ evenSet G ∧ x ≠ y ∧ x ≠ a := by
    intro x hx
    have := hWK hx
    rw [hEvK] at this
    simp only [Finset.mem_erase] at this
    exact ⟨this.2.2, this.2.1, this.1⟩
  have htrans := realisable_transfer hy ha hya hreal (by
    intro x hx hxS hadj
    have hxW : x ∈ W' := by
      by_contra h; exact hxS (Finset.mem_sdiff.mpr ⟨hx, h⟩)
    rcases htwo x (hWE x hxW).1 hadj with h | h
    · exact (hWE x hxW).2.2 h
    · exact hbW (h ▸ hxW))
  have haW : a ∉ W' := fun h => (hWE a h).2.2 rfl
  have hyW : y ∉ W' := fun h => (hWE y h).2.1 rfl
  refine ⟨insert a W', ?_, ?_, Finset.empty_subset _, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    · exact (hWE x hx).1
  · rw [Finset.card_insert_of_notMem haW, hWc]
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hya' h
    · exact hyW h
  · convert htrans using 1
    ext x
    rw [hEvK]
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    by_cases h1 : x = y
    · rw [h1]; simp [hy, hya', hyW]
    by_cases h2 : x = a
    · rw [h2]; simp [Ne.symm hya']
    simp [h1, h2]

end two

/-- **The branching base case, three even neighbours.** `k`-step descent keeping `y`, for even
vertices `y` with at least three even neighbours and no bridge to a vertex of degree at least
two. -/
def BranchBase3 (k : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
    H.Connected → Even (Fintype.card W) → 2 * k ≤ (evenSet H).card →
    ∀ y, y ∈ evenSet H →
    (∃ v₁ ∈ evenSet H, ∃ v₂ ∈ evenSet H, ∃ v₃ ∈ evenSet H, v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ ∧
      H.Adj y v₁ ∧ H.Adj y v₂ ∧ H.Adj y v₃) →
    (∀ t, H.Adj y t → H.IsBridge s(y, t) → H.degree t ≤ 1) → Desc H k y ∅

/-- **Two even neighbours reduce.** `D⁰_k` and `BranchBase3 (k+1)` give `BranchBase (k+1)`. -/
theorem branchBase_of_three (k : ℕ) (hlow : DStmt0.{u} k) (hB3 : BranchBase3.{u} (k + 1)) :
    BranchBase.{u} (k + 1) := by
  intro W _ _ H _ hc hn h2 y hy htwo hbr
  by_cases h3 : ∃ v₁ ∈ evenSet H, ∃ v₂ ∈ evenSet H, ∃ v₃ ∈ evenSet H, v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧
      v₂ ≠ v₃ ∧ H.Adj y v₁ ∧ H.Adj y v₂ ∧ H.Adj y v₃
  · exact hB3 W H hc hn h2 y hy h3 hbr
  obtain ⟨a, ha, b, hb, hab, hya, hyb⟩ := htwo
  have hall : ∀ v ∈ evenSet H, H.Adj y v → v = a ∨ v = b := by
    intro v hv hyv
    by_contra h
    push Not at h
    exact h3 ⟨a, ha, b, hb, v, hv, hab, Ne.symm h.1, Ne.symm h.2, hya, hyb, hyv⟩
  have hnb : ¬ H.IsBridge s(y, a) := by
    intro hbr'
    have hle := hbr a hya hbr'
    obtain ⟨hpos, j, hj⟩ := mem_evenSet_iff_even.mp ha
    omega
  have hKconn := connected_delE_of_not_isBridge hc hnb
  have hEvK := evenSet_delE_even hy ha hya
  have hbK : b ∈ evenSet (delE H {s(y, a)}) := by
    rw [hEvK]
    exact Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_erase.mpr ⟨hyb.ne.symm, hb⟩⟩
  have hcardK : 2 * k ≤ (evenSet (delE H {s(y, a)})).card := by
    rw [hEvK, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hya.ne.symm, ha⟩),
      Finset.card_erase_of_mem hy]
    omega
  exact desc_succ_of_transfer_two hy ha hya hab hall (hlow W _ hKconn hn hcardK b hbK)

/-- `BranchBase3 k` for all `k ≥ 3` gives `BranchBase k` for all `k ≥ 3`. -/
theorem branchBase_of_branchBase3 (hB : ∀ k, 3 ≤ k → BranchBase3.{u} k) :
    ∀ k, 3 ≤ k → BranchBase.{u} k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk3
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hD : DStmt0.{u} m :=
    dstmt0_of_branchBase m (fun j hj3 hjm => ih j (by omega) hj3) m (by omega) le_rfl
  exact branchBase_of_three m hD (hB (m + 1) hk3)

/-- **Gallai's conjecture from the three-neighbour branching case.** -/
theorem gallai_of_branchBase3 (hB : ∀ k, 3 ≤ k → BranchBase3.{u} k) : GallaiConjecture.{u} :=
  gallai_of_branchBase_three (branchBase_of_branchBase3 hB)

/-! ## The last-edge barrier -/

section barrier

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem GPath.endsAt_le_one_fb {H : SimpleGraph V} (P : GPath H) (v : V) : P.endsAt v ≤ 1 := by
  have hne := P.src_ne_tgt
  unfold GPath.endsAt
  by_cases h1 : P.src = v
  · have h2 : ¬ P.tgt = v := fun h => hne (h1.trans h.symm)
    simp [h1, h2]
  · split_ifs <;> simp_all

omit [Fintype V] in
/-- A vertex is an end of at most one end of each path. -/
theorem PathDecomp.ends_le_size {H : SimpleGraph V} (D : PathDecomp H) (v : V) :
    D.ends v ≤ D.size := by
  unfold PathDecomp.ends PathDecomp.size
  generalize D.paths = l
  induction l with
  | nil => simp
  | cons P l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := P.endsAt_le_one_fb v
    omega

/-- **Fan's condition is expensive.** If `D` decomposes `H`, `ut ∉ E(H)` and the condition of
Fan's lemma for transferring `ut` towards `u` holds, then
`ends u + 2·#{even-degree neighbours of u} + 2 ≤ 3·|D|`. -/
theorem fan_transfer_barrier {H : SimpleGraph V} [DecidableRel H.Adj] (D : PathDecomp H)
    {u t : V} (hut : u ≠ t) (htu : ¬ H.Adj u t)
    (hcond : (univ.filter (fun w => H.Adj u w ∧ D.ends w = 0)).card < D.ends t) :
    D.ends u + 2 * (univ.filter (fun w => H.Adj u w ∧ Even (H.degree w))).card + 2 ≤
      3 * D.size := by
  set NE := univ.filter (fun w => H.Adj u w ∧ Even (H.degree w)) with hNE
  set Z := univ.filter (fun w => H.Adj u w ∧ D.ends w = 0) with hZ
  -- every even-degree neighbour with an end has at least two
  have hpt : ∀ w ∈ NE, 2 ≤ D.ends w + 2 * (if D.ends w = 0 then 1 else 0) := by
    intro w hw
    rw [hNE, mem_filter] at hw
    have hpar := D.ends_mod_two w
    obtain ⟨j, hj⟩ := hw.2.2
    split_ifs with h0
    · omega
    · omega
  have hsum1 : 2 * NE.card ≤ ∑ w ∈ NE, D.ends w +
      2 * (NE.filter (fun w => D.ends w = 0)).card := by
    have h := Finset.sum_le_sum hpt
    rw [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_boole] at h
    simpa [mul_comm] using h
  have hsub : NE.filter (fun w => D.ends w = 0) ⊆ Z := by
    intro w hw
    rw [mem_filter, hNE, mem_filter] at hw
    rw [hZ, mem_filter]
    exact ⟨mem_univ _, hw.1.2.1, hw.2⟩
  have hZle := Finset.card_le_card hsub
  -- the ends at `u`, at `t` and at the even-degree neighbours of `u` are counted separately
  have huNE : u ∉ NE := by
    rw [hNE, mem_filter]; exact fun h => H.irrefl h.2.1
  have htNE : t ∉ NE := by
    rw [hNE, mem_filter]; exact fun h => htu h.2.1
  have htot : D.ends u + D.ends t + ∑ w ∈ NE, D.ends w ≤ ∑ v, D.ends v := by
    have hsplit : ∑ v ∈ insert u (insert t NE), D.ends v =
        D.ends u + (D.ends t + ∑ w ∈ NE, D.ends w) := by
      rw [Finset.sum_insert (by
        rw [Finset.mem_insert]; rintro (h | h)
        · exact hut h
        · exact huNE h), Finset.sum_insert htNE]
    have := Finset.sum_le_sum_of_subset (f := fun v => D.ends v)
      (Finset.subset_univ (insert u (insert t NE)))
    omega
  have hS := D.sum_ends
  have hts := D.ends_le_size t
  omega

/-- Every path has at most `n − 1` edges, so `|E(H)| ≤ |D|·(n − 1)`. -/
theorem card_edgeFinset_le_size_mul {H : SimpleGraph V} [DecidableRel H.Adj] (D : PathDecomp H) :
    H.edgeFinset.card ≤ D.size * (Fintype.card V - 1) := by
  rw [← D.sum_length_eq_card]
  have hlen : ∀ x ∈ D.paths.map (fun P => P.edges.length), x ≤ Fintype.card V - 1 := by
    intro x hx
    obtain ⟨P, -, rfl⟩ := List.mem_map.mp hx
    have := P.isPath.length_lt
    rw [P.length_edges]
    omega
  have := List.sum_le_length_nsmul _ _ hlen
  simpa [PathDecomp.size] using this

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The transfer bound for an even-regular graph: a Fan transfer of `ut` towards `u` needs
`2d + 1 ≤ 3|D|`. -/
theorem fan_transfer_barrier_regular {d : ℕ} (hd : ∀ v, G.degree v = d) (hde : Even d)
    {u t : V} (hut : G.Adj u t) (D : PathDecomp (delE G {s(u, t)}))
    (hcond : (univ.filter (fun w => (delE G {s(u, t)}).Adj u w ∧ D.ends w = 0)).card <
      D.ends t) :
    2 * d + 1 ≤ 3 * D.size := by
  have hne : u ≠ t := hut.ne
  have htu : ¬ (delE G {s(u, t)}).Adj u t := by simp [delE_adj]
  have hb := fan_transfer_barrier D hne htu hcond
  obtain ⟨hKu, -, hKo⟩ := delE_single_facts hut
  have hNE : univ.filter (fun w => (delE G {s(u, t)}).Adj u w ∧
      Even ((delE G {s(u, t)}).degree w)) = (delE G {s(u, t)}).neighborFinset u := by
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_neighborFinset]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      have hwu : w ≠ u := fun h' => (delE G {s(u, t)}).irrefl (h' ▸ h)
      have hwt : w ≠ t := fun h' => htu (h' ▸ h)
      rw [hKo w hwu hwt, hd w]
      exact hde
  rw [hNE, card_neighborFinset_eq_degree] at hb
  have hpar := D.ends_mod_two u
  have hdu := hd u
  obtain ⟨j, hj⟩ := hde
  have hdeg : (delE G {s(u, t)}).degree u + 1 = d := by rw [← hdu]; exact hKu
  have hu1 : 1 ≤ D.ends u := by omega
  omega

/-- The new-path bound for a `d`-regular graph: if `G − ut` has a decomposition `D`, then
`n·d ≤ 2|D|(n − 1) + 2`. -/
theorem newpath_barrier_regular {d : ℕ} (hd : ∀ v, G.degree v = d) {u t : V} (hut : G.Adj u t)
    (D : PathDecomp (delE G {s(u, t)})) :
    Fintype.card V * d ≤ 2 * D.size * (Fintype.card V - 1) + 2 := by
  have hne : u ≠ t := hut.ne
  have hE := card_edgeFinset_le_size_mul D
  have hhs := (delE G {s(u, t)}).sum_degrees_eq_twice_card_edges
  have hdeg := degree_delE_single G hut
  have hsum : ∑ v, (delE G {s(u, t)}).degree v + 2 = Fintype.card V * d := by
    have h1 : ∑ v, ((delE G {s(u, t)}).degree v + (if v = u ∨ v = t then 1 else 0)) =
        ∑ v, G.degree v := Finset.sum_congr rfl (fun v _ => hdeg v)
    rw [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id] at h1
    have h2 : (univ.filter (fun v => v = u ∨ v = t)).card = 2 := by
      have : univ.filter (fun v => v = u ∨ v = t) = {u, t} := by
        ext v; simp
      rw [this, Finset.card_pair hne]
    rw [h2] at h1
    rw [h1]
    simp [hd, mul_comm]
  have : 2 * (delE G {s(u, t)}).edgeFinset.card + 2 = Fintype.card V * d := by
    rw [← hhs]; exact hsum
  nlinarith

/-- **Path insertion.** If `D` decomposes `G − F` for a set `F` of edges of the `d`-regular
graph `G`, then `n·d ≤ 2(|D|(n − 1) + |F|)`. (A new path made of the held edges `F` is the only
Fan-game move that adds a path.) -/
theorem insertion_barrier_regular {d : ℕ} (hd : ∀ v, G.degree v = d) (F : Finset (Sym2 V))
    (D : PathDecomp (delE G F)) :
    Fintype.card V * d ≤ 2 * (D.size * (Fintype.card V - 1) + F.card) := by
  have hE := card_edgeFinset_le_size_mul D
  have hsub : G.edgeFinset ⊆ (delE G F).edgeFinset ∪ F := by
    intro e he
    rw [mem_edgeFinset] at he
    rw [Finset.mem_union, mem_edgeFinset]
    by_cases h : e ∈ F
    · exact Or.inr h
    · left
      simp only [delE, edgeSet_deleteEdges, Set.mem_sdiff, Finset.mem_coe]
      exact ⟨he, h⟩
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hhs := G.sum_degrees_eq_twice_card_edges
  have hsum : ∑ v, G.degree v = Fintype.card V * d := by simp [hd, mul_comm]
  omega

end barrier

/-! ## The cocktail party graphs -/

/-- The cocktail party graph `CP(m)`: `K_{2m}` minus the perfect matching `{(i,0),(i,1)}`. -/
def cocktail (m : ℕ) : SimpleGraph (Fin m × Bool) where
  Adj a b := a.1 ≠ b.1
  symm := ⟨fun _ _ h => Ne.symm h⟩
  loopless := ⟨fun _ h => h rfl⟩

instance cocktail.decRel (m : ℕ) : DecidableRel (cocktail m).Adj :=
  fun a b => inferInstanceAs (Decidable (a.1 ≠ b.1))

theorem cocktail_degree (m : ℕ) (a : Fin m × Bool) : (cocktail m).degree a = 2 * (m - 1) := by
  rw [← card_neighborFinset_eq_degree]
  have h : (cocktail m).neighborFinset a = (univ.erase a.1) ×ˢ (univ : Finset Bool) := by
    ext b
    simp only [mem_neighborFinset, mem_product, mem_erase, mem_univ, and_true]
    exact ⟨fun h => Ne.symm h, fun h => Ne.symm h⟩
  rw [h, card_product, card_erase_of_mem (mem_univ _), card_univ, card_univ, Fintype.card_fin,
    Fintype.card_bool]
  ring

/-- **No Fan move finishes `CP(m)`, `m ≥ 4`.** Let `ut` be an edge of `CP(m)` and `D` any
decomposition of `CP(m) − ut`. Adding `ut` as a new path gives at least `m + 1` paths, and if
Fan's condition for transferring `ut` towards `u` holds, then `D` (and the transferred
decomposition, which has the same size) has more than `m` paths. -/
theorem cocktail_fan_barrier {m : ℕ} (hm : 4 ≤ m) {u t : Fin m × Bool}
    (hut : (cocktail m).Adj u t) (D : PathDecomp (delE (cocktail m) {s(u, t)})) :
    m ≤ D.size ∧
    ((univ.filter (fun w => (delE (cocktail m) {s(u, t)}).Adj u w ∧ D.ends w = 0)).card <
      D.ends t → m < D.size) := by
  have hcard : Fintype.card (Fin m × Bool) = 2 * m := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; ring
  refine ⟨?_, fun hcond => ?_⟩
  · have h := newpath_barrier_regular (cocktail_degree m) hut D
    rw [hcard] at h
    by_contra hlt
    push Not at hlt
    have h1 : D.size ≤ m - 1 := by omega
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 4 := ⟨m - 4, by omega⟩
    have h2 : D.size * (2 * (m' + 4) - 1) ≤ (m' + 3) * (2 * (m' + 4) - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h3 : 2 * (m' + 4) - 1 = 2 * m' + 7 := by omega
    have h4 : m' + 4 - 1 = m' + 3 := by omega
    rw [h3] at h2 h
    rw [h4] at h
    nlinarith
  · have h := fan_transfer_barrier_regular (cocktail_degree m) ⟨m - 1, by ring⟩ hut D hcond
    omega

/-- **Path insertion needs a long path.** If `CP(m)` has a decomposition into at most `m` paths
obtained from a decomposition `D` of `CP(m) − F` by adding one new path made of the edges `F`
(so `|D| + 1 ≤ m`), then `|F| ≥ m − 1`. -/
theorem cocktail_insertion_barrier {m : ℕ} (F : Finset (Sym2 (Fin m × Bool)))
    (D : PathDecomp (delE (cocktail m) F)) (hD : D.size + 1 ≤ m) : m - 1 ≤ F.card := by
  have hcard : Fintype.card (Fin m × Bool) = 2 * m := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; ring
  have h := insertion_barrier_regular (cocktail_degree m) F D
  rw [hcard] at h
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h3 : 2 * (m' + 1) - 1 = 2 * m' + 1 := by omega
  have h4 : m' + 1 - 1 = m' := by omega
  rw [h3, h4] at h
  rw [h4]
  have h2 : D.size * (2 * m' + 1) ≤ m' * (2 * m' + 1) := Nat.mul_le_mul_right _ (by omega)
  nlinarith

end Gallai
