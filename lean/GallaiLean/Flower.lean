import GallaiLean.FanBarrier
import GallaiLean.PathSurgery
import GallaiLean.HubPhases
import GallaiLean.MissingMove

/-!
# The flower move

The positive counterpart of the last-edge barrier (`FanBarrier.lean`); manuscript endpoint-structure
§7 and missing-move Lemma 5.4, Proposition 5.5.

**The flower lemma** (`flower_decomp`). Let `P₁, …, P_k` be paths of the complete graph. Close each
`Pᵢ` into the cycle `Cᵢ = Pᵢ + (src, tgt)`, and let `L` be a path whose edges are one edge `eᵢ` from
each `Cᵢ`. Then the paths `Cᵢ − eᵢ` together with `L` have the edges of all the cycles, there are
`k + 1` of them, and they have two ends at every vertex of `L` and none elsewhere. If the cycles
are the edges of `G`, this is a decomposition of `G` into `k + 1` paths.

**Equality forces a flower** (`hub_cycles`). If a decomposition `D` of `H` has `|T|` ends at `s`,
one at each vertex of `T` (`s ∉ T`) and none elsewhere, then every path joins `s` to a vertex of `T`,
each vertex of `T` is the end of exactly one path, and the paths, oriented from `s`, have the edges
of `H`. With the edges `st` (`t ∈ T`) they close into cycles through `s`. This is the state left
when the receipts at a hub stop at Fan's equality (supply = number of blank neighbours).

**Transversals.** `Transversal ps` asks for a path through `s` that takes exactly one edge from each
cycle. `RainbowTransversal k`: every system of `k` Hamiltonian cycles through `s` on `2k + 2`
vertices has one. `rainbowTransversal_three`, `rainbowTransversal_four`: proved, by a greedy choice
and, for `k = 4`, one rotation.

**Cocktail party graphs.** `cocktail_passes_of_rt`: for `m ≥ 4`, `RainbowTransversal (m − 1)`
gives the two-end test at every vertex of `CP(m)`: Lovász on `CP(m) − s`, `m − 1` grouped receipts,
the `m`-th fails at equality, the cycles are Hamiltonian by an edge count, and a transversal
recombines them into `m` paths with two ends at `s`. `cocktail_passes_four`, `cocktail_passes_five`
are unconditional.
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u}

/-- `e` lies on the cycle obtained by closing `P` with the edge joining its ends. -/
def OnCycle (P : TPath V) (e : Sym2 V) : Prop := e ∈ P.edges ∨ e = s(P.src, P.tgt)

section close

variable [DecidableEq V]

theorem endsAt_eq_mem (P : TPath V) (v : V) :
    P.endsAt v = if v ∈ s(P.src, P.tgt) then 1 else 0 := by
  have hst := P.src_ne_tgt
  unfold GPath.endsAt
  by_cases h1 : P.src = v
  · subst h1
    simp [Ne.symm hst]
  · by_cases h2 : P.tgt = v
    · subst h2; simp [h1]
    · have : v ∉ s(P.src, P.tgt) := by
        rw [Sym2.mem_iff]; rintro (h | h)
        · exact h1 h.symm
        · exact h2 h.symm
      simp [h1, h2, this]

/-- **Close and cut.** Close `P` into a cycle and cut the cycle at one of its edges `e`: the result
is a path with the remaining edges of the cycle, ending at the two ends of `e`. -/
theorem exists_close_cut (P : TPath V) {e : Sym2 V} (he : OnCycle P e) :
    ∃ Q : TPath V, (Q.edges : Multiset (Sym2 V)) + {e} =
        (P.edges : Multiset (Sym2 V)) + {s(P.src, P.tgt)} ∧
      ∀ v, Q.endsAt v = if v ∈ e then 1 else 0 := by
  have hst : P.src ≠ P.tgt := P.src_ne_tgt
  rcases he with he | he
  · induction e using Sym2.ind with
    | _ a b =>
    obtain ⟨c, d, hcd, q, q', hce, hR⟩ := Walk.exists_append_cons_of_mem_edges P.walk he
    have hRn := P.support_nodup
    rw [hR] at hRn
    have hqn := support_nodup_of_append_left hRn
    have hq'n' := support_nodup_of_append_right hRn
    rw [Walk.support_cons, List.nodup_cons] at hq'n'
    have hRd := ((nodup_support_append q _).mp hRn).2.2
    have hdisj : ∀ v ∈ q.support, v ∉ q'.support := by
      intro v hv hv'
      have := hRd v hv (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hv')
      subst this
      exact hq'n'.1 hv'
    have hsq' : P.src ∉ q'.support := hdisj _ q.start_mem_support
    let W1 := q.reverse
    let W2 : (⊤ : SimpleGraph V).Walk P.src d :=
      Walk.cons (show (⊤ : SimpleGraph V).Adj P.src P.tgt from hst) q'.reverse
    have hW1 : W1.support.Nodup := by
      simp only [W1, Walk.support_reverse, List.nodup_reverse]; exact hqn
    have hW2 : W2.support.Nodup := by
      simp only [W2, Walk.support_cons, Walk.support_reverse, List.nodup_cons, List.mem_reverse,
        List.nodup_reverse]
      exact ⟨hsq', hq'n'.2⟩
    have hd : ∀ v ∈ W1.support, v ∈ W2.support → v = P.src := by
      intro v hv hv'
      simp only [W1, W2, Walk.support_reverse, List.mem_reverse, Walk.support_cons,
        List.mem_cons] at hv hv'
      rcases hv' with h | h
      · exact h
      · exact absurd h (hdisj v hv)
    refine ⟨joinT W1 W2 hW1 hW2 hd (by simp only [W2, Walk.length_cons]; omega), ?_, fun v => ?_⟩
    · rw [joinT_edges]
      simp only [W1, W2, Walk.edges_reverse, Walk.edges_cons]
      show _ = ((P.walk.edges : Multiset (Sym2 V))) + _
      rw [hR, Walk.edges_append, Walk.edges_cons, hce]
      simp only [← Multiset.coe_add, Multiset.coe_reverse, ← Multiset.cons_coe,
        ← Multiset.singleton_add]
      abel
    · simp only [GPath.endsAt, joinT_src, joinT_tgt]
      have hcd' : c ≠ d := hcd
      rw [← hce]
      by_cases h1 : c = v
      · subst h1; simp [hcd', Ne.symm hcd']
      · by_cases h2 : d = v
        · subst h2; simp [h1]
        · have : v ∉ s(c, d) := by
            rw [Sym2.mem_iff]; rintro (h | h)
            · exact h1 h.symm
            · exact h2 h.symm
          simp [h1, h2, this]
  · refine ⟨P, by rw [he], fun v => ?_⟩
    rw [he]
    exact endsAt_eq_mem P v

/-- A path meets `v` in `incid v` of its edges. -/
theorem incid_eq_count (L : TPath V) (v : V) :
    ((L.edges.map (fun e => if v ∈ e then 1 else 0)).sum) = L.incid v := by
  unfold GPath.incid
  generalize L.edges = l
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    by_cases h : v ∈ e <;> simp [h, add_comm]

/-- **The flower lemma**, as a statement about lists of paths. The pairs `(P, e)` list the
paths `P` and the edge `e` at which the closed cycle of `P` is cut; `L` is a path whose edges are
exactly the cut edges. -/
theorem flower_list (ps : List (TPath V × Sym2 V)) (hcut : ∀ x ∈ ps, OnCycle x.1 x.2)
    (L : TPath V) (hL : (L.edges : Multiset (Sym2 V)) = (ps.map Prod.snd : Multiset (Sym2 V))) :
    ∃ Qs : List (TPath V), Qs.length = ps.length ∧
      edgesM (Qs ++ [L]) = edgesM (ps.map Prod.fst) +
        ((ps.map (fun x => s(x.1.src, x.1.tgt))) : Multiset (Sym2 V)) ∧
      ∀ v, endsL (Qs ++ [L]) v = if v ∈ L.walk.support then 2 else 0 := by
  -- first cut every cycle
  have hstep : ∀ (l : List (TPath V × Sym2 V)), (∀ x ∈ l, OnCycle x.1 x.2) →
      ∃ Qs : List (TPath V), Qs.length = l.length ∧
        edgesM Qs + ((l.map Prod.snd) : Multiset (Sym2 V)) = edgesM (l.map Prod.fst) +
          ((l.map (fun x => s(x.1.src, x.1.tgt))) : Multiset (Sym2 V)) ∧
        ∀ v, endsL Qs v = ((l.map Prod.snd).map (fun e => if v ∈ e then 1 else 0)).sum := by
    intro l hl
    induction l with
    | nil => exact ⟨[], rfl, by simp, fun v => by simp⟩
    | cons x l ih =>
      obtain ⟨Qs, hlen, hE, hends⟩ := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
      obtain ⟨Q, hQE, hQends⟩ := exists_close_cut x.1 (hl x List.mem_cons_self)
      refine ⟨Q :: Qs, by simp [hlen], ?_, fun v => ?_⟩
      · have e1 : (((x.2 :: l.map Prod.snd : List (Sym2 V))) : Multiset (Sym2 V)) =
            {x.2} + ((l.map Prod.snd : List (Sym2 V)) : Multiset (Sym2 V)) := by
          rw [Multiset.singleton_add, Multiset.cons_coe]
        have e2 : (((s(x.1.src, x.1.tgt) :: l.map (fun x => s(x.1.src, x.1.tgt)) :
            List (Sym2 V))) : Multiset (Sym2 V)) = {s(x.1.src, x.1.tgt)} +
            ((l.map (fun x => s(x.1.src, x.1.tgt)) : List (Sym2 V)) : Multiset (Sym2 V)) := by
          rw [Multiset.singleton_add, Multiset.cons_coe]
        calc edgesM (Q :: Qs) + (((x :: l).map Prod.snd : List (Sym2 V)) : Multiset (Sym2 V))
            = ((Q.edges : Multiset (Sym2 V)) + {x.2}) +
              (edgesM Qs + ((l.map Prod.snd : List (Sym2 V)) : Multiset (Sym2 V))) := by
              rw [edgesM_cons, List.map_cons, e1]; abel
          _ = ((x.1.edges : Multiset (Sym2 V)) + {s(x.1.src, x.1.tgt)}) +
              (edgesM (l.map Prod.fst) + ((l.map (fun x => s(x.1.src, x.1.tgt)) : List (Sym2 V)) :
                Multiset (Sym2 V))) := by
              rw [hQE, hE]
          _ = _ := by
              rw [List.map_cons, edgesM_cons, List.map_cons, e2]; abel
      · simp only [endsL_cons, List.map_cons, List.sum_cons, hQends v, hends v]
  obtain ⟨Qs, hlen, hE, hends⟩ := hstep ps hcut
  refine ⟨Qs, hlen, ?_, fun v => ?_⟩
  · rw [edgesM_append, edgesM_cons, edgesM_nil, add_zero, hL]
    exact hE
  · rw [endsL_append, endsL_cons, endsL_nil, add_zero, hends v]
    have h1 : ((ps.map Prod.snd).map (fun e => if v ∈ e then 1 else 0)).sum = L.incid v := by
      rw [← incid_eq_count L v]
      have h2 : ((L.edges : Multiset (Sym2 V)).map (fun e => if v ∈ e then 1 else 0)).sum =
          (((ps.map Prod.snd : List (Sym2 V)) : Multiset (Sym2 V)).map
            (fun e => if v ∈ e then 1 else 0)).sum := by rw [hL]
      simpa using h2.symm
    rw [h1]
    have := L.incid_add_endsAt v
    split_ifs at this ⊢ <;> omega

/-- **The flower lemma for a graph.** If the cycles of the pairs in `ps` are the edges of `G`,
the cut cycles and `L` decompose `G` into `|ps| + 1` paths with two ends at every vertex of `L`
and none elsewhere. -/
theorem flower_decomp [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (ps : List (TPath V × Sym2 V)) (hcut : ∀ x ∈ ps, OnCycle x.1 x.2)
    (L : TPath V) (hL : (L.edges : Multiset (Sym2 V)) = (ps.map Prod.snd : Multiset (Sym2 V)))
    (hG : edgesM (ps.map Prod.fst) + ((ps.map (fun x => s(x.1.src, x.1.tgt))) : Multiset (Sym2 V)) =
      G.edgeFinset.val) :
    ∃ D : PathDecomp G, D.size = ps.length + 1 ∧
      ∀ v, D.ends v = if v ∈ L.walk.support then 2 else 0 := by
  obtain ⟨Qs, hlen, hE, hends⟩ := flower_list ps hcut L hL
  obtain ⟨D, hsize, hD⟩ := exists_decomp_of_edgesM (G := G) (Qs ++ [L]) (by rw [hE, hG])
  exact ⟨D, by rw [hsize]; simp [hlen], fun v => by rw [hD v, hends v]⟩

/-- **The flower lemma with untouched paths** (the receipt-or-flower move): the cut cycles, the
transversal `L`, and a list `rest` of further paths together decompose `G` into
`|ps| + 1 + |rest|` paths, with `2` extra ends on `L`. -/
theorem flower_decomp_rest [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (ps : List (TPath V × Sym2 V)) (hcut : ∀ x ∈ ps, OnCycle x.1 x.2)
    (L : TPath V) (hL : (L.edges : Multiset (Sym2 V)) = (ps.map Prod.snd : Multiset (Sym2 V)))
    (rest : List (TPath V))
    (hG : edgesM (ps.map Prod.fst) + ((ps.map (fun x => s(x.1.src, x.1.tgt))) : Multiset (Sym2 V)) +
      edgesM rest = G.edgeFinset.val) :
    ∃ D : PathDecomp G, D.size = ps.length + 1 + rest.length ∧
      ∀ v, D.ends v = (if v ∈ L.walk.support then 2 else 0) + endsL rest v := by
  obtain ⟨Qs, hlen, hE, hends⟩ := flower_list ps hcut L hL
  obtain ⟨D, hsize, hD⟩ := exists_decomp_of_edgesM (G := G) ((Qs ++ [L]) ++ rest)
    (by rw [edgesM_append, hE, hG])
  refine ⟨D, by rw [hsize]; simp [hlen]; omega, fun v => ?_⟩
  rw [hD v, endsL_append, hends v]

end close

/-! ### Equality forces a flower -/

section hub

variable [DecidableEq V]

theorem count_map_eq_sum {α : Type*} (l : List α) (g : α → V) (v : V) :
    (l.map g).count v = (l.map (fun x => if g x = v then 1 else 0)).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.count_cons, List.sum_cons, ih]
    by_cases h : g x = v
    · simp [h, add_comm]
    · simp [h]

/-- The path `P` read from the end `s`. -/
def orientFrom {G : SimpleGraph V} (s : V) (P : GPath G) : TPath V :=
  if P.src = s then P.toTop else P.toTop.reverse

theorem orientFrom_edges {G : SimpleGraph V} (s : V) (P : GPath G) :
    ((orientFrom s P).edges : Multiset (Sym2 V)) = (P.edges : Multiset (Sym2 V)) := by
  unfold orientFrom
  split_ifs
  · simp
  · show ((P.toTop.walk.reverse.edges : List (Sym2 V)) : Multiset (Sym2 V)) = _
    rw [Walk.edges_reverse, Multiset.coe_reverse]
    exact congrArg _ (P.toTop_edges)

theorem orientFrom_endsAt {G : SimpleGraph V} (s : V) (P : GPath G) (v : V) :
    (orientFrom s P).endsAt v = P.endsAt v := by
  unfold orientFrom
  split_ifs
  · rfl
  · rw [GPath.reverse_endsAt']; rfl

theorem orientFrom_src {G : SimpleGraph V} {s : V} (P : GPath G) (h : P.endsAt s = 1) :
    (orientFrom s P).src = s := by
  unfold orientFrom
  split_ifs with h1
  · exact h1
  · show P.tgt = s
    unfold GPath.endsAt at h
    by_contra h2
    simp [h1, h2] at h

/-- **Equality forces a flower.** Let `D` have `|T|` ends at `s`, one at each vertex of `T`, and
none elsewhere. Then the paths of `D`, read from `s`, start at `s`, end at the vertices of `T`
(each once), and carry the edges of `H`. -/
theorem hub_cycles [Fintype V] {H : SimpleGraph V} [DecidableRel H.Adj] (D : PathDecomp H)
    (s : V) (T : Finset V) (hsT : s ∉ T)
    (hends : ∀ v, D.ends v = if v = s then T.card else if v ∈ T then 1 else 0) :
    ∃ ps : List (TPath V), ps.length = T.card ∧ edgesM ps = H.edgeFinset.val ∧
      (∀ P ∈ ps, P.src = s) ∧ ((ps.map GPath.tgt : List V) : Multiset V) = T.val := by
  have hf : ∀ v, (if v = s then T.card else if v ∈ T then 1 else 0) =
      (if v = s then T.card else 0) + (if v ∈ T then 1 else 0) := by
    intro v
    by_cases h : v = s
    · subst h; simp [hsT]
    · simp [h]
  have hsum := D.sum_ends
  simp only [hends, hf, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id] at hsum
  have hsize : D.size = T.card := by omega
  -- every path ends once at `s`
  have hone : ∀ P ∈ D.paths, P.endsAt s = 1 := by
    have hle : ∀ x ∈ D.paths.map (fun P => P.endsAt s), x ≤ 1 := by
      intro x hx
      obtain ⟨P, -, rfl⟩ := List.mem_map.mp hx
      exact P.endsAt_le_one_fb s
    have hs : (D.paths.map (fun P => P.endsAt s)).sum =
        (D.paths.map (fun P => P.endsAt s)).length * 1 := by
      have := hends s
      simp only [ite_true] at this
      rw [List.length_map, mul_one]
      show D.ends s = D.size
      rw [this, hsize]
    intro P hP
    exact eq_of_sum_eq_length_mul hle hs _ (List.mem_map_of_mem hP)
  refine ⟨D.paths.map (orientFrom s), by rw [List.length_map]; exact hsize, ?_, ?_, ?_⟩
  · have h1 : edgesM (D.paths.map (orientFrom s)) = edgesM (D.paths.map GPath.toTop) := by
      unfold edgesM
      simp only [List.flatMap_map]
      generalize D.paths = l
      induction l with
      | nil => rfl
      | cons P l ih =>
        simp only [List.flatMap_cons, ← Multiset.coe_add, ih]
        rw [orientFrom_edges, GPath.toTop_edges]
    rw [h1, PathDecomp.edgesM_toTop]
  · intro P hP
    obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hP
    exact orientFrom_src Q (hone Q hQ)
  · ext v
    rw [Multiset.coe_count, List.map_map, count_map_eq_sum, Multiset.count_eq_of_nodup T.nodup]
    simp only [Finset.mem_val]
    -- ends of the oriented paths: one at `s` each, the rest at the targets
    have hsplit : ∀ P ∈ D.paths, P.endsAt v = (if s = v then 1 else 0) +
        (if (orientFrom s P).tgt = v then 1 else 0) := by
      intro P hP
      rw [← orientFrom_endsAt s P v]
      unfold GPath.endsAt
      rw [orientFrom_src P (hone P hP)]
    have hD : D.ends v = (D.paths.map (fun P => P.endsAt v)).sum := rfl
    have hsum2 : (D.paths.map (fun P => P.endsAt v)).sum =
        D.size * (if s = v then 1 else 0) +
          (D.paths.map (fun P => if (orientFrom s P).tgt = v then 1 else 0)).sum := by
      rw [List.map_congr_left hsplit, List.sum_map_add]
      simp [PathDecomp.size]
    have hev := hends v
    rw [hD, hsum2] at hev
    simp only [Function.comp_def]
    by_cases hvs : v = s
    · subst hvs
      simp only [ite_true, mul_one, hsT, ite_false] at hev ⊢
      omega
    · have hsv : s ≠ v := Ne.symm hvs
      simp only [hsv, ite_false, mul_zero, zero_add, hvs] at hev
      rw [hev]

end hub

/-! ### Transversals -/

/-- A **transversal** of the cycle system of `ps` through `s`: a path through `s` whose edges are
one edge of each closed cycle. -/
def Transversal (s : V) (ps : List (TPath V)) : Prop :=
  ∃ L : TPath V, s ∈ L.walk.support ∧ ∃ qs : List (TPath V × Sym2 V), qs.map Prod.fst = ps ∧
    (∀ x ∈ qs, OnCycle x.1 x.2) ∧
    (L.edges : Multiset (Sym2 V)) = ((qs.map Prod.snd : List (Sym2 V)) : Multiset (Sym2 V))

/-- **The rainbow transversal property** for `k` cycles: every system of `k` edge-disjoint
Hamiltonian cycles through `s`, on `2k + 2` vertices, has a transversal through `s`. Each cycle is
given as a Hamiltonian path from `s` closed by the edge joining its ends. -/
def RainbowTransversal (k : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (s : W) (ps : List (TPath W)),
    Fintype.card W = 2 * k + 2 → ps.length = k → (∀ P ∈ ps, P.src = s ∧ ∀ v, v ∈ P.walk.support) →
    (edgesM ps + ((ps.map (fun P => s(P.src, P.tgt)) : List (Sym2 W)) : Multiset (Sym2 W))).Nodup →
    Transversal s ps

/-! ### Cocktail party graphs -/

section cocktail

open Finset

theorem cocktail_card (m : ℕ) : Fintype.card (Fin m × Bool) = 2 * m := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; ring

theorem cocktail_card_edges (m : ℕ) : (cocktail m).edgeFinset.card = m * (2 * (m - 1)) := by
  have h := (cocktail m).sum_degrees_eq_twice_card_edges
  simp only [cocktail_degree, Finset.sum_const, Finset.card_univ, cocktail_card, smul_eq_mul] at h
  have h2 : 2 * (m * (2 * (m - 1))) = 2 * (cocktail m).edgeFinset.card := by rw [← h]; ring
  exact (Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h2).symm

/-- A duplicate-free list with as many entries as the type has elements contains everything. -/
theorem mem_of_nodup_length {W : Type*} [Fintype W] [DecidableEq W] {l : List W} (hl : l.Nodup)
    (hlen : l.length = Fintype.card W) (v : W) : v ∈ l := by
  have h1 : l.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup hl, hlen]
  rw [← List.mem_toFinset, h1]
  exact Finset.mem_univ v

/-- **`CP(m)` passes the two-end test at every vertex, given rainbow transversals.** Lovász's
theorem on `CP(m) − s`, `m − 1` grouped receipts at `s`, and the flower recombination of the
`m − 1` Hamiltonian cycles left at Fan's equality. -/
theorem cocktail_passes_of_rt {m : ℕ} (hm : 4 ≤ m) (hRT : RainbowTransversal.{0} (m - 1))
    (s : Fin m × Bool) : PassesAt (cocktail m) s := by
  classical
  set G := cocktail m with hGdef
  set K := isolate G s with hKdef
  have hKs : K.degree s = 0 := isolate_degree_self G s
  have hKdeg : ∀ v, v ≠ s → K.degree v + (if G.Adj v s then 1 else 0) = 2 * (m - 1) := by
    intro v hv
    have := isolate_degree (G := G) hv
    rw [cocktail_degree] at this
    exact this
  have hadj : ∀ a b : Fin m × Bool, G.Adj a b ↔ a.1 ≠ b.1 := fun _ _ => Iff.rfl
  -- at most one even vertex in `K`: the antipode of `s`
  have hev : (evenSet K).card ≤ 1 := by
    have key : ∀ x ∈ evenSet K, x = (s.1, !s.2) := by
      intro x hx
      rw [mem_evenSet_iff_even] at hx
      by_cases hxs : x = s
      · rw [hxs, hKs] at hx; exact absurd hx.1 (lt_irrefl 0)
      have h1 := hKdeg x hxs
      by_cases hxa : G.Adj x s
      · rw [ite_eq_left hxa] at h1
        obtain ⟨j, hj⟩ := hx.2
        omega
      · have hx1 : x.1 = s.1 := by
          by_contra h; exact hxa ((hadj x s).mpr h)
        obtain ⟨x1, x2⟩ := x
        obtain ⟨s1, s2⟩ := s
        simp only at hx1
        subst hx1
        have : x2 ≠ s2 := fun h => hxs (by rw [h])
        cases x2 <;> cases s2 <;> simp_all
    apply Finset.card_le_one.mpr
    intro a ha b hb
    rw [key a ha, key b hb]
  obtain ⟨D0, hD0⟩ := lovasz_ends K hev
  have hA0 : Ach K.edgeSet (fun v => D0.ends v) := Ach.of_decomp D0
  set S := univ.filter (fun v => G.Adj s v) with hSdef
  have hScard : S.card = 2 * (m - 1) := by
    rw [← cocktail_degree m s, ← card_neighborFinset_eq_degree]
    congr 1
    ext v
    simp [S, mem_neighborFinset, G]
  have hsS : s ∉ S := by simp [S]
  have hSE : ∀ t ∈ S, s(t, s) ∉ K.edgeSet := fun t _ h =>
    ((isolate_edgeSet G s _).mp h).2 (Sym2.mem_mk_right t s)
  have hS1 : ∀ t ∈ S, D0.ends t = 1 := by
    intro t ht
    rw [hD0 t]
    have hts : t ≠ s := fun h => hsS (h ▸ ht)
    have hta : G.Adj t s := ((Finset.mem_filter.mp ht).2).symm
    have := hKdeg t hts
    rw [ite_eq_left hta] at this
    omega
  have hbl : blankNbrs K.edgeSet (fun v => D0.ends v) s = 0 :=
    blankNbrs_eq_zero_of_isolated (fun w h => ((isolate_edgeSet G s _).mp h).2
      (Sym2.mem_mk_left s w))
  obtain ⟨Z, hZS, hZc, hZ⟩ := hA0.receiveMany s S hsS hSE hS1 (m - 1)
    (by intro j hj; rw [hbl, hScard]; omega)
  set T := S \ Z with hTdef
  have hTc : T.card = m - 1 := by rw [Finset.card_sdiff_of_subset hZS, hScard, hZc]; omega
  have hsT : s ∉ T := fun h => hsS (Finset.mem_sdiff.mp h).1
  set E1 := K.edgeSet ∪ hubSpokes s Z with hE1
  obtain ⟨D, hD⟩ := hZ
  have hends : ∀ v, D.ends v = if v = s then T.card else if v ∈ T then 1 else 0 := by
    intro v
    rw [hD v]
    unfold recvEnds
    beta_reduce
    by_cases hvs : v = s
    · subst hvs
      rw [ite_eq_left rfl, ite_eq_left rfl, hD0, hKs, hTc, hZc]
      omega
    · rw [ite_eq_right hvs, ite_eq_right hvs]
      by_cases hvZ : v ∈ Z
      · rw [ite_eq_left hvZ, hS1 v (hZS hvZ)]
        have : v ∉ T := fun h => (Finset.mem_sdiff.mp h).2 hvZ
        simp [this]
      · rw [ite_eq_right hvZ]
        by_cases hvS : v ∈ S
        · rw [hS1 v hvS]
          have : v ∈ T := Finset.mem_sdiff.mpr ⟨hvS, hvZ⟩
          simp [this]
        · have hvT : v ∉ T := fun h => hvS (Finset.mem_sdiff.mp h).1
          rw [ite_eq_right hvT, hD0 v]
          have hna : ¬ G.Adj v s := fun h => hvS (Finset.mem_filter.mpr ⟨mem_univ _, h.symm⟩)
          have := hKdeg v hvs
          rw [ite_eq_right hna] at this
          omega
  obtain ⟨ps, hpl, hpE, hpsrc, hptgt⟩ := hub_cycles D s T hsT hends
  -- the closing edges are the spokes to `T`
  have hclose : ((ps.map (fun P => s(P.src, P.tgt)) : List (Sym2 (Fin m × Bool))) :
      Multiset (Sym2 (Fin m × Bool))) = T.val.map (fun t => s(s, t)) := by
    have : ps.map (fun P => s(P.src, P.tgt)) = (ps.map GPath.tgt).map (fun t => s(s, t)) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro P hP
      simp [hpsrc P hP]
    rw [this, ← Multiset.map_coe, hptgt]
  have hinj : Function.Injective (fun t : Fin m × Bool => s(s, t)) := fun a b h =>
    Sym2.congr_right.mp h
  have hGE : G.edgeFinset.val = edgesM ps + T.val.map (fun t => s(s, t)) := by
    rw [hpE]
    apply edgeFinset_val_eq_add
    · exact T.nodup.map hinj
    · intro e he
      obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp he
      rw [Finset.mem_val] at ht
      rw [edgeSet_fromEdgeSet, Set.mem_sdiff, not_and_or]
      left
      rintro (h | h)
      · exact ((isolate_edgeSet G s _).mp h).2 (Sym2.mem_mk_left s t)
      · rcases mem_hubSpokes.mp h with ⟨-, htZ⟩ | ⟨hts, -⟩
        · exact (Finset.mem_sdiff.mp ht).2 htZ
        · exact hsT (hts ▸ ht)
    · intro e
      induction e using Sym2.ind with
      | _ a b =>
      simp only [edgeSet_fromEdgeSet, Set.mem_sdiff, Sym2.diagSet_eq_setOfPred_isDiag,
        Set.mem_ofPred_eq, Sym2.mk_isDiag_iff, mem_edgeSet, Multiset.mem_map]
      constructor
      · intro hab
        by_cases hsab : s = a ∨ s = b
        · rcases hsab with rfl | rfl
          · by_cases hbZ : b ∈ Z
            · left
              exact ⟨Or.inr (mem_hubSpokes.mpr (Or.inl ⟨rfl, hbZ⟩)), hab.ne⟩
            · right
              exact ⟨b, Finset.mem_val.mpr (Finset.mem_sdiff.mpr
                ⟨Finset.mem_filter.mpr ⟨mem_univ _, hab⟩, hbZ⟩), rfl⟩
          · by_cases haZ : a ∈ Z
            · left
              exact ⟨Or.inr (mem_hubSpokes.mpr (Or.inr ⟨rfl, haZ⟩)), hab.ne⟩
            · right
              exact ⟨a, Finset.mem_val.mpr (Finset.mem_sdiff.mpr
                ⟨Finset.mem_filter.mpr ⟨mem_univ _, hab.symm⟩, haZ⟩), Sym2.eq_swap⟩
        · push Not at hsab
          left
          refine ⟨Or.inl ((isolate_edgeSet G s _).mpr ⟨hab, ?_⟩), hab.ne⟩
          rw [Sym2.mem_iff]
          rintro (h | h)
          · exact hsab.1 h
          · exact hsab.2 h
      · rintro (⟨h | h, -⟩ | ⟨t, ht, he⟩)
        · exact ((isolate_edgeSet G s _).mp h).1
        · rcases mem_hubSpokes.mp h with ⟨rfl, hbZ⟩ | ⟨rfl, haZ⟩
          · exact (Finset.mem_filter.mp (hZS hbZ)).2
          · exact ((Finset.mem_filter.mp (hZS haZ)).2).symm
        · rw [Finset.mem_val] at ht
          have hst : G.Adj s t := (Finset.mem_filter.mp (Finset.mem_sdiff.mp ht).1).2
          rw [← mem_edgeSet, ← he]
          exact hst
  -- the cycles are Hamiltonian
  have hcardE : G.edgeFinset.card = m * (2 * (m - 1)) := cocktail_card_edges m
  have hHcard : (edgesM ps).card = (m - 1) * (2 * m - 1) := by
    have h1 := congrArg Multiset.card hGE
    rw [Multiset.card_add, Multiset.card_map, Finset.card_val, Finset.card_val, hTc] at h1
    rw [hcardE] at h1
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at h1 ⊢
    have h3 : 2 * (m' + 1) - 1 = 2 * m' + 1 := by omega
    rw [h3]
    nlinarith
  have hlen : (ps.map (fun P => P.edges.length)).sum = (m - 1) * (2 * m - 1) := by
    rw [← hHcard]
    unfold edgesM
    rw [Multiset.coe_card, List.length_flatMap]
  have hle : ∀ x ∈ ps.map (fun P => P.edges.length), x ≤ 2 * m - 1 := by
    intro x hx
    obtain ⟨P, -, rfl⟩ := List.mem_map.mp hx
    have := P.isPath.length_lt
    rw [cocktail_card] at this
    rw [show P.edges.length = P.walk.length from P.walk.length_edges]
    omega
  have hsum : (ps.map (fun P => P.edges.length)).sum =
      (ps.map (fun P => P.edges.length)).length * (2 * m - 1) := by
    rw [hlen, List.length_map, hpl, hTc]
  have hham : ∀ P ∈ ps, ∀ v, v ∈ P.walk.support := by
    intro P hP v
    have h1 := eq_of_sum_eq_length_mul hle hsum _ (List.mem_map_of_mem hP)
    apply mem_of_nodup_length P.support_nodup
    rw [Walk.length_support, cocktail_card, ← P.walk.length_edges]
    change P.edges.length + 1 = 2 * m
    rw [h1]
    omega
  have hnodup : (edgesM ps + ((ps.map (fun P => s(P.src, P.tgt)) : List (Sym2 (Fin m × Bool))) :
      Multiset (Sym2 (Fin m × Bool)))).Nodup := by
    rw [hclose, ← hGE]
    exact G.edgeFinset.nodup
  obtain ⟨L, hsL, qs, hqs, hcut, hL⟩ := hRT (Fin m × Bool) s ps (by rw [cocktail_card]; omega)
    (by rw [hpl, hTc]) (fun P hP => ⟨hpsrc P hP, hham P hP⟩) hnodup
  have hG' : edgesM (qs.map Prod.fst) + ((qs.map (fun x => s(x.1.src, x.1.tgt)) :
      List (Sym2 (Fin m × Bool))) : Multiset (Sym2 (Fin m × Bool))) = G.edgeFinset.val := by
    have : qs.map (fun x => s(x.1.src, x.1.tgt)) =
        (qs.map Prod.fst).map (fun P => s(P.src, P.tgt)) := by rw [List.map_map]; rfl
    rw [this, hqs, hclose, hGE]
  obtain ⟨D', hsz, hends'⟩ := flower_decomp qs hcut L hL hG'
  have hql : qs.length = m - 1 := by
    have := congrArg List.length hqs
    rw [List.length_map, hpl, hTc] at this
    exact this
  refine ⟨D', ?_, ?_⟩
  · rw [hsz, hql, cocktail_card]
    omega
  · rw [hends' s, ite_eq_left hsL]

/-- The rooted test for `CP(m)`, given rainbow transversals. -/
theorem cocktail_rooted_of_rt {m : ℕ} (hm : 4 ≤ m) (hRT : RainbowTransversal.{0} (m - 1))
    (s : Fin m × Bool) :
    pathNumber (addLeaf (cocktail m) s) ≤ Fintype.card (Fin m × Bool) / 2 := by
  classical
  obtain ⟨D, hsz, h2⟩ := cocktail_passes_of_rt hm hRT s
  have hend : D.ends s ≠ 0 := by omega
  calc pathNumber (addLeaf (cocktail m) s) ≤ leafCost D s := pathNumber_addLeaf_le D s
    _ = D.size := by simp [leafCost, hend]
    _ ≤ _ := hsz

end cocktail

/-! ### Rainbow transversals for three and four cycles -/

section rainbow

variable [Fintype V] [DecidableEq V]

/-- The edges of the closed cycle of `P`. -/
def cycM (P : TPath V) : Multiset (Sym2 V) := (P.edges : Multiset (Sym2 V)) + {s(P.src, P.tgt)}

omit [Fintype V] [DecidableEq V] in
theorem onCycle_iff (P : TPath V) (e : Sym2 V) : OnCycle P e ↔ e ∈ cycM P := by
  unfold OnCycle cycM
  rw [Multiset.mem_add, Multiset.mem_coe, Multiset.mem_singleton]

omit [Fintype V] [DecidableEq V] in
theorem ne_of_onCycle {P : TPath V} {a b : V} (h : OnCycle P s(a, b)) : a ≠ b := by
  rintro rfl
  rcases h with h | h
  · have := P.walk.edges_subset_edgeSet h
    simp at this
  · rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact P.src_ne_tgt (h1.symm.trans h2)
    · exact P.src_ne_tgt (h2.symm.trans h1)

omit [Fintype V] [DecidableEq V] in
theorem disj_of_nodup {X Y R : Multiset (Sym2 V)} (h : (X + Y + R).Nodup) : Disjoint X Y :=
  (Multiset.nodup_add.mp (Multiset.nodup_add.mp h).1).2.2

omit [Fintype V] [DecidableEq V] in
theorem not_onCycle_both {P Q : TPath V} {R : Multiset (Sym2 V)}
    (h : (cycM P + cycM Q + R).Nodup) {e : Sym2 V} (hP : OnCycle P e) (hQ : OnCycle Q e) :
    False :=
  Multiset.disjoint_left.mp (disj_of_nodup h) ((onCycle_iff P e).mp hP) ((onCycle_iff Q e).mp hQ)

instance OnCycle.decidable (P : TPath V) (e : Sym2 V) : Decidable (OnCycle P e) := by
  unfold OnCycle; infer_instance

/-- The neighbours of `v` on the closed cycle of `P`. -/
def cnbr (P : TPath V) (v : V) : Finset V := Finset.univ.filter (fun w => OnCycle P s(v, w))

theorem mem_cnbr {P : TPath V} {v w : V} : w ∈ cnbr P v ↔ OnCycle P s(v, w) := by
  simp [cnbr]

/-- On a Hamiltonian cycle every vertex has exactly two neighbours. -/
theorem card_cnbr (P : TPath V) (hham : ∀ v, v ∈ P.walk.support)
    (hcl : s(P.src, P.tgt) ∉ P.edges) (v : V) : (cnbr P v).card = 2 := by
  have hsplit : cnbr P v = Finset.univ.filter (fun w => s(v, w) ∈ P.edges) ∪
      Finset.univ.filter (fun w => s(v, w) = s(P.src, P.tgt)) := by
    ext w; simp [cnbr, OnCycle]
  have hdisj : Disjoint (Finset.univ.filter (fun w => s(v, w) ∈ P.edges))
      (Finset.univ.filter (fun w => s(v, w) = s(P.src, P.tgt))) := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hcl (h2 ▸ h1)
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  -- the path edges at `v`
  have hA : (Finset.univ.filter (fun w => s(v, w) ∈ P.edges)).card = P.incid v := by
    have hnd : P.edges.Nodup := P.isPath.isTrail.edges_nodup
    have himg : (Finset.univ.filter (fun w => s(v, w) ∈ P.edges)).image (fun w => s(v, w)) =
        (P.edges.filter (fun e => v ∈ e)).toFinset := by
      ext e
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨hw, Sym2.mem_mk_left v w⟩
      · rintro ⟨he, hv⟩
        exact ⟨Sym2.Mem.other hv, by rw [Sym2.other_spec hv]; exact he, Sym2.other_spec hv⟩
    rw [← Finset.card_image_of_injective _ (fun a b h => Sym2.congr_right.mp h), himg,
      List.toFinset_card_of_nodup (hnd.filter _)]
    unfold GPath.incid
    rw [List.countP_eq_length_filter]
  have hB : (Finset.univ.filter (fun w => s(v, w) = s(P.src, P.tgt))).card = P.endsAt v := by
    have hst := P.src_ne_tgt
    unfold GPath.endsAt
    by_cases h1 : P.src = v
    · subst h1
      have : Finset.univ.filter (fun w => s(P.src, w) = s(P.src, P.tgt)) = {P.tgt} := by
        ext w; simp [hst]
      rw [this]; simp [Ne.symm hst]
    · by_cases h2 : P.tgt = v
      · subst h2
        have : Finset.univ.filter (fun w => s(P.tgt, w) = s(P.src, P.tgt)) = {P.src} := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          rw [Sym2.eq_swap (a := P.src), Sym2.congr_right]
        rw [this]; simp [h1]
      · have : Finset.univ.filter (fun w => s(v, w) = s(P.src, P.tgt)) = ∅ := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
            iff_false]
          intro h
          have : v ∈ s(P.src, P.tgt) := h ▸ Sym2.mem_mk_left v w
          rcases Sym2.mem_iff.mp this with h' | h'
          · exact h1 h'.symm
          · exact h2 h'.symm
        rw [this]; simp [h1, h2]
  rw [hA, hB]
  have := P.incid_add_endsAt v
  simp only [hham v, ite_true] at this
  omega

theorem exists_mem_cnbr_ne (P : TPath V) (hham : ∀ v, v ∈ P.walk.support)
    (hcl : s(P.src, P.tgt) ∉ P.edges) (v x : V) : ∃ w ∈ cnbr P v, w ≠ x := by
  have h := card_cnbr P hham hcl v
  have : ((cnbr P v).erase x).Nonempty := by
    rw [← Finset.card_pos]
    have := Finset.pred_card_le_card_erase (s := cnbr P v) (a := x)
    omega
  obtain ⟨w, hw⟩ := this
  exact ⟨w, Finset.mem_of_mem_erase hw, Finset.ne_of_mem_erase hw⟩

omit [Fintype V] [DecidableEq V] in
theorem hcl_of_nodup {P : TPath V} {R : Multiset (Sym2 V)} (h : (cycM P + R).Nodup) :
    s(P.src, P.tgt) ∉ P.edges := by
  have h1 := (Multiset.nodup_add.mp h).1
  unfold cycM at h1
  have hdj := (Multiset.nodup_add.mp h1).2.2
  intro hm
  exact Multiset.disjoint_left.mp hdj (Multiset.mem_coe.mpr hm) (Multiset.mem_singleton_self _)

omit [Fintype V] [DecidableEq V] in
theorem ofList_edges (a : V) (l : List V) (hl : l ≠ []) (hnd : (a :: l).Nodup) (h) :
    (GPath.ofList (⊤ : SimpleGraph V) a l hl hnd h).edges = lEdges a l := walkOf_edges _ _ _ _

omit [Fintype V] [DecidableEq V] in
theorem ofList_support (a : V) (l : List V) (hl : l ≠ []) (hnd : (a :: l).Nodup) (h) :
    (GPath.ofList (⊤ : SimpleGraph V) a l hl hnd h).walk.support = a :: l := walkOf_support _ _ _ _

omit [Fintype V] [DecidableEq V] in
theorem top_lEdges {a : V} {l : List V} (hnd : (a :: l).Nodup) :
    ∀ e ∈ lEdges a l, e ∈ (⊤ : SimpleGraph V).edgeSet := by
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
  rw [mem_edgeSet, top_adj]
  have := lEdges_not_diag hnd he
  simpa using this

end rainbow

/-- **Three cycles**: a greedy choice. -/
theorem rainbowTransversal_three : RainbowTransversal.{u} 3 := by
  intro W _ _ s ps hcard hlen hps hnd
  obtain ⟨P1, P2, P3, rfl⟩ := List.length_eq_three.mp hlen
  have hsum : edgesM [P1, P2, P3] + (([P1, P2, P3].map (fun P => s(P.src, P.tgt)) :
      List (Sym2 W)) : Multiset (Sym2 W)) = cycM P1 + cycM P2 + cycM P3 := by
    simp only [edgesM_cons, edgesM_nil, List.map_cons, List.map_nil, cycM,
      ← Multiset.singleton_add, ← Multiset.cons_coe]
    abel
  rw [hsum] at hnd
  have n12 : (cycM P1 + cycM P2 + cycM P3).Nodup := hnd
  have n23 : (cycM P2 + cycM P3 + cycM P1).Nodup := by
    rw [show cycM P2 + cycM P3 + cycM P1 = cycM P1 + cycM P2 + cycM P3 by abel]; exact hnd
  have n1 : (cycM P1 + (cycM P2 + cycM P3)).Nodup := by rw [← add_assoc]; exact hnd
  have n2 : (cycM P2 + (cycM P3 + cycM P1)).Nodup := by rw [← add_assoc]; exact n23
  have n3 : (cycM P3 + (cycM P1 + cycM P2)).Nodup := by
    rw [show cycM P3 + (cycM P1 + cycM P2) = cycM P1 + cycM P2 + cycM P3 by abel]; exact hnd
  obtain ⟨hs1, hh1⟩ := hps P1 (by simp)
  obtain ⟨hs2, hh2⟩ := hps P2 (by simp)
  obtain ⟨hs3, hh3⟩ := hps P3 (by simp)
  -- greedy choice
  obtain ⟨a1, ha1, -⟩ := exists_mem_cnbr_ne P1 hh1 (hcl_of_nodup n1) s s
  rw [mem_cnbr] at ha1
  obtain ⟨a2, ha2, -⟩ := exists_mem_cnbr_ne P2 hh2 (hcl_of_nodup n2) a1 a1
  rw [mem_cnbr] at ha2
  have ha2s : a2 ≠ s := by
    rintro rfl
    exact not_onCycle_both n12 ha1 (by rw [Sym2.eq_swap]; exact ha2)
  obtain ⟨a3, ha3, ha3s⟩ := exists_mem_cnbr_ne P3 hh3 (hcl_of_nodup n3) a2 s
  rw [mem_cnbr] at ha3
  have ha3a1 : a3 ≠ a1 := by
    rintro rfl
    exact not_onCycle_both n23 ha2 (by rw [Sym2.eq_swap]; exact ha3)
  have h01 := ne_of_onCycle ha1
  have h12 := ne_of_onCycle ha2
  have h23 := ne_of_onCycle ha3
  have hndL : [s, a1, a2, a3].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_or, List.nodup_nil, not_false_eq_true, and_true]
    exact ⟨⟨h01, ha2s.symm, ha3s.symm⟩, ⟨h12, ha3a1.symm⟩, h23⟩
  refine ⟨GPath.ofList ⊤ s [a1, a2, a3] (by simp) hndL (top_lEdges hndL), ?_,
    [(P1, s(s, a1)), (P2, s(a1, a2)), (P3, s(a2, a3))], rfl, ?_, ?_⟩
  · rw [ofList_support]; exact List.mem_cons_self
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha1
    · exact ha2
    · exact ha3
  · rw [ofList_edges]
    rfl

/-- **Four cycles**: a greedy choice, and one rotation when it gets stuck. -/
theorem rainbowTransversal_four : RainbowTransversal.{u} 4 := by
  intro W _ _ s ps hcard hlen hps hnd
  rcases ps with _ | ⟨P1, _ | ⟨P2, _ | ⟨P3, _ | ⟨P4, _ | ⟨P5, ps⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hlen <;> try omega
  have hsum : edgesM [P1, P2, P3, P4] + (([P1, P2, P3, P4].map (fun P => s(P.src, P.tgt)) :
      List (Sym2 W)) : Multiset (Sym2 W)) = cycM P1 + cycM P2 + cycM P3 + cycM P4 := by
    simp only [edgesM_cons, edgesM_nil, List.map_cons, List.map_nil, cycM,
      ← Multiset.singleton_add, ← Multiset.cons_coe]
    abel
  rw [hsum] at hnd
  have nd : ∀ X Y R : Multiset (Sym2 W), X + Y + R = cycM P1 + cycM P2 + cycM P3 + cycM P4 →
      (X + Y + R).Nodup := fun X Y R h => by rw [h]; exact hnd
  have n12 := nd (cycM P1) (cycM P2) (cycM P3 + cycM P4) (by abel)
  have n23 := nd (cycM P2) (cycM P3) (cycM P1 + cycM P4) (by abel)
  have n34 := nd (cycM P3) (cycM P4) (cycM P1 + cycM P2) (by abel)
  have n24 := nd (cycM P2) (cycM P4) (cycM P1 + cycM P3) (by abel)
  have c1 : (cycM P1 + (cycM P2 + cycM P3 + cycM P4)).Nodup := by
    rw [show cycM P1 + (cycM P2 + cycM P3 + cycM P4) = cycM P1 + cycM P2 + cycM P3 + cycM P4
      by abel]; exact hnd
  have c2 : (cycM P2 + (cycM P1 + cycM P3 + cycM P4)).Nodup := by
    rw [show cycM P2 + (cycM P1 + cycM P3 + cycM P4) = cycM P1 + cycM P2 + cycM P3 + cycM P4
      by abel]; exact hnd
  have c3 : (cycM P3 + (cycM P1 + cycM P2 + cycM P4)).Nodup := by
    rw [show cycM P3 + (cycM P1 + cycM P2 + cycM P4) = cycM P1 + cycM P2 + cycM P3 + cycM P4
      by abel]; exact hnd
  have c4 : (cycM P4 + (cycM P1 + cycM P2 + cycM P3)).Nodup := by
    rw [show cycM P4 + (cycM P1 + cycM P2 + cycM P3) = cycM P1 + cycM P2 + cycM P3 + cycM P4
      by abel]; exact hnd
  obtain ⟨hs1, hh1⟩ := hps P1 (by simp)
  obtain ⟨hs2, hh2⟩ := hps P2 (by simp)
  obtain ⟨hs3, hh3⟩ := hps P3 (by simp)
  obtain ⟨hs4, hh4⟩ := hps P4 (by simp)
  obtain ⟨a1, ha1, -⟩ := exists_mem_cnbr_ne P1 hh1 (hcl_of_nodup c1) s s
  rw [mem_cnbr] at ha1
  obtain ⟨a2, ha2, -⟩ := exists_mem_cnbr_ne P2 hh2 (hcl_of_nodup c2) a1 a1
  rw [mem_cnbr] at ha2
  have ha2s : a2 ≠ s := by
    rintro rfl
    exact not_onCycle_both n12 ha1 (by rw [Sym2.eq_swap]; exact ha2)
  obtain ⟨a3, ha3, ha3s⟩ := exists_mem_cnbr_ne P3 hh3 (hcl_of_nodup c3) a2 s
  rw [mem_cnbr] at ha3
  have ha3a1 : a3 ≠ a1 := by
    rintro rfl
    exact not_onCycle_both n23 ha2 (by rw [Sym2.eq_swap]; exact ha3)
  have h01 := ne_of_onCycle ha1
  have h12 := ne_of_onCycle ha2
  have h23 := ne_of_onCycle ha3
  by_cases hext : ∃ y ∈ cnbr P4 a3, y ≠ s ∧ y ≠ a1
  · -- the greedy path extends
    obtain ⟨y, hy, hys, hya1⟩ := hext
    rw [mem_cnbr] at hy
    have hya3 := ne_of_onCycle hy
    have hya2 : y ≠ a2 := by
      rintro rfl
      exact not_onCycle_both n34 ha3 (by rw [Sym2.eq_swap]; exact hy)
    have hndL : [s, a1, a2, a3, y].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
        not_or, List.nodup_nil, not_false_eq_true, and_true]
      exact ⟨⟨h01, ha2s.symm, ha3s.symm, hys.symm⟩, ⟨h12, ha3a1.symm, hya1.symm⟩,
        ⟨h23, hya2.symm⟩, hya3⟩
    refine ⟨GPath.ofList ⊤ s [a1, a2, a3, y] (by simp) hndL (top_lEdges hndL), ?_,
      [(P1, s(s, a1)), (P2, s(a1, a2)), (P3, s(a2, a3)), (P4, s(a3, y))], rfl, ?_, ?_⟩
    · rw [ofList_support]; exact List.mem_cons_self
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ha1
      · exact ha2
      · exact ha3
      · exact hy
    · rw [ofList_edges]; rfl
  · -- stuck: both neighbours of `a3` on the fourth cycle are `s` and `a1`; rotate
    push Not at hext
    have hsub : cnbr P4 a3 ⊆ {s, a1} := by
      intro y hy
      by_cases h : y = s
      · simp [h]
      · simp [hext y hy h]
    have hc4 := card_cnbr P4 hh4 (hcl_of_nodup c4) a3
    have heq : cnbr P4 a3 = {s, a1} :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hc4]; exact Finset.card_le_two)
    have h4s : OnCycle P4 s(a3, s) := mem_cnbr.mp (by rw [heq]; simp)
    have h4a1 : OnCycle P4 s(a3, a1) := mem_cnbr.mp (by rw [heq]; simp)
    obtain ⟨x, hx, hxa2⟩ := exists_mem_cnbr_ne P2 hh2 (hcl_of_nodup c2) a1 a2
    rw [mem_cnbr] at hx
    have hxs : x ≠ s := by
      rintro rfl
      exact not_onCycle_both n12 ha1 (by rw [Sym2.eq_swap]; exact hx)
    have hxa3 : x ≠ a3 := by
      rintro rfl
      exact not_onCycle_both n24 hx (by rw [Sym2.eq_swap]; exact h4a1)
    have hxa1 := ne_of_onCycle hx
    have hndL : [a2, a3, s, a1, x].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
        not_or, List.nodup_nil, not_false_eq_true, and_true]
      exact ⟨⟨h23, ha2s, h12.symm, hxa2.symm⟩, ⟨ha3s, ha3a1, hxa3.symm⟩, ⟨h01, hxs.symm⟩, hxa1⟩
    refine ⟨GPath.ofList ⊤ a2 [a3, s, a1, x] (by simp) hndL (top_lEdges hndL), ?_,
      [(P1, s(s, a1)), (P2, s(a1, x)), (P3, s(a2, a3)), (P4, s(a3, s))], rfl, ?_, ?_⟩
    · rw [ofList_support]; simp
    · intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact ha1
      · exact hx
      · exact ha3
      · exact h4s
    · rw [ofList_edges]
      simp only [lEdges_cons, lEdges_nil, List.map_cons, List.map_nil]
      exact Multiset.coe_eq_coe.mpr
        (List.perm_append_comm (l₁ := [s(a2, a3), s(a3, s)]) (l₂ := [s(s, a1), s(a1, x)]))

/-- **`CP(4)`**: the rooted test at every vertex (missing-move Proposition 5.5). -/
theorem cocktail_passes_four (s : Fin 4 × Bool) : PassesAt (cocktail 4) s :=
  cocktail_passes_of_rt le_rfl rainbowTransversal_three s

/-- **`CP(5)`**: the rooted test at every vertex. -/
theorem cocktail_passes_five (s : Fin 5 × Bool) : PassesAt (cocktail 5) s :=
  cocktail_passes_of_rt (by norm_num) rainbowTransversal_four s

end Gallai
