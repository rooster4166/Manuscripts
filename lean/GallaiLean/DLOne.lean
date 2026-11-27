import GallaiLean.TriangleBase
import GallaiLean.MultiSep
import GallaiLean.PathSurgery
import GallaiLean.ConstrainedLovasz

/-!
# The disjunctive avoidance conjecture for one pair: proved cases (session `claude/dl-one`)

Manuscript: `manuscripts/dl-one/dl-one.tex`. Conjecture DL(1) is `DisjL1` (TriangleBase.lean) for a
single pair; the disjunction is `TriangleDisj D [(a, b)]`.

* `exists_decomp_of_edgesM'`: `exists_decomp_of_edgesM`, also returning the paths.
* `append_edge_track`: append an edge at an end of a path, tracking every path.
* **`leaf_exchange`** (manuscript Lemma 4.1): a leaf `ℓ` at `x` whose path is the single edge `ℓx`,
  with `deg x ≥ 3`, can be exchanged into a path through `x` avoiding a prescribed vertex.
* **`not_paired_adj`** (Lemma NP, manuscript Lemma 4.2): with no vertex of positive even degree, two
  adjacent vertices `x, y` with `deg x ≥ 3` are not the two ends of one path of some Lovász
  decomposition.
* **`avoid_leaf`**, **`disjL1_leaf`** (Theorem 5.1): DL for one pair when `a` is a leaf at the even
  vertex `g` (outside universal twins), with `Q(b)` avoiding `a`.
* **`avoid_deg_two`** (Theorem 6.1), **`disjL1_deg_two`** (Corollary 6.2): DL for one pair when
  `N(g) = {a, b}` and `g` is the only common neighbour of `a, b`.
* **`avoid_free_target`**, **`disjL1_free_target`** (Proposition 7.1, the transfer): Lovász's Case I
  across a target outside `N[b] ∪ {a}` carries `Q(b) ∌ a` (via `csys_caseI`); so a target adjacent to
  neither `a` nor `b` carries the disjunction, with the same disjunct.
* **`univTwins_every_path`**, **`not_triangleDisj_of_twins`** (Proposition 3.1, connected form):
  universal twins lie on every path of every Lovász decomposition, so the exception is needed.
-/

open SimpleGraph

namespace Gallai

universe u

/-! ### Rebuilding a decomposition from a list of paths, keeping the paths -/

section rebuild

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `exists_decomp_of_edgesM`, also returning that every path of the new decomposition is a path
of the list (same ends, same support). -/
theorem exists_decomp_of_edgesM' (L : List (TPath V)) (h : edgesM L = G.edgeFinset.val) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = endsL L v) ∧
      ∀ Q ∈ D.paths, ∃ P ∈ L, Q.src = P.src ∧ Q.tgt = P.tgt ∧
        Q.walk.support = P.walk.support := by
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
  refine ⟨⟨L', by rw [h1]; exact hnd, fun e => ?_⟩, h2, fun Q hQ => ?_⟩
  · rw [h1, ← mem_edgeFinset, ← Finset.mem_val, ← h, edgesM, Multiset.mem_coe]
  · obtain ⟨P, hP, rfl⟩ := List.mem_pmap.mp hQ
    exact ⟨P, hP, rfl, rfl, Walk.support_transfer _ _⟩

end rebuild

/-! ### Small facts -/

section facts

variable {V : Type u} {K : SimpleGraph V}

theorem walk_length_one {a b : V} (w : K.Walk a b) (h : w.length = 1) :
    K.Adj a b ∧ w.support = [a, b] ∧ w.edges = [s(a, b)] := by
  cases w with
  | nil => simp at h
  | cons hadj p =>
    cases p with
    | nil => exact ⟨hadj, rfl, rfl⟩
    | cons _ q => simp at h

/-- The paths of a decomposition are pairwise distinct. -/
theorem PathDecomp.paths_nodup (D : PathDecomp K) : D.paths.Nodup := by
  classical
  have key : ∀ l : List (GPath K), (l.flatMap GPath.edges).Nodup → l.Nodup := by
    intro l
    induction l with
    | nil => intro _; exact List.nodup_nil
    | cons P l ih =>
      intro h
      rw [List.flatMap_cons, List.nodup_append] at h
      refine List.nodup_cons.mpr ⟨fun hP => ?_, ih h.2.1⟩
      obtain ⟨e, he, -⟩ := P.exists_edge_of_mem P.walk.start_mem_support
      exact h.2.2 e he e (List.mem_flatMap.mpr ⟨P, hP, he⟩) rfl
  exact key D.paths D.nodup_edges

theorem sum_map_le_of_ne {α : Type*} [DecidableEq α] (l : List α) (f : α → ℕ) {P Q : α}
    (hP : P ∈ l) (hQ : Q ∈ l) (hPQ : P ≠ Q) : f P + f Q ≤ (l.map f).sum := by
  have hperm := List.perm_cons_erase hP
  have hQ' : Q ∈ l.erase P := (List.mem_erase_of_ne (Ne.symm hPQ)).mpr hQ
  rw [(hperm.map f).sum_eq, List.map_cons, List.sum_cons]
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := f) hQ')
  omega

end facts

/-! ### The leaf exchange -/

section exchange

variable {V : Type u} [Fintype V] [DecidableEq V] {K : SimpleGraph V} [DecidableRel K.Adj]

/-- The core of the exchange: a path `R` split at an interior vertex `x` into `q₁` (from the start
to `x`) and `q₂`, and a vertex `ℓ ∉ R`.  Then `q₁ + xℓ` and `q₂` are paths of the complete graph
with the edges of `R` and `xℓ`. -/
theorem exchange_core (R : GPath K) {x ℓ : V} (q₁ : K.Walk R.src x) (q₂ : K.Walk x R.tgt)
    (hR : R.walk = q₁.append q₂) (hxs : R.src ≠ x) (hxt : x ≠ R.tgt)
    (hℓ : ℓ ∉ R.walk.support) (hxℓ : x ≠ ℓ) :
    ∃ N₁ N₂ : TPath V,
      (N₁.edges : Multiset (Sym2 V)) + N₂.edges = R.edges + {s(x, ℓ)} ∧
      N₁.src = R.src ∧ N₁.tgt = ℓ ∧ N₂.src = x ∧ N₂.tgt = R.tgt ∧
      (∀ w ∈ N₁.walk.support, w = ℓ ∨ w ∈ q₁.support) ∧
      (∀ w ∈ N₂.walk.support, w ∈ q₂.support) := by
  have hRn := R.support_nodup
  rw [hR] at hRn
  have hq₁ := support_nodup_of_append_left hRn
  have hq₂ := support_nodup_of_append_right hRn
  let p : (⊤ : SimpleGraph V).Walk R.src x := q₁.mapLe le_top
  let e : (⊤ : SimpleGraph V).Walk x ℓ := Walk.cons (by simpa using hxℓ) Walk.nil
  have hp : p.support.Nodup := by simpa [p] using hq₁
  have he : e.support.Nodup := by simp [e, hxℓ]
  have hd : ∀ v ∈ p.support, v ∈ e.support → v = x := by
    intro v hv hve
    simp only [e, Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hve
    rcases hve with h | h
    · exact h
    · subst h
      exfalso
      apply hℓ
      rw [hR]
      exact (Walk.mem_support_append_iff q₁ q₂).mpr (Or.inl (by simpa [p] using hv))
  have hlen2 : 0 < q₂.length := by
    rcases Nat.eq_zero_or_pos q₂.length with h | h
    · exact absurd (Walk.eq_of_length_eq_zero h) hxt
    · exact h
  let N₁ := joinT p e hp he hd (by simp [e])
  let N₂ : TPath V := ⟨x, R.tgt, q₂.mapLe le_top,
    (Walk.isPath_def _).mpr (by simpa using hq₂), by simpa using hlen2⟩
  refine ⟨N₁, N₂, ?_, rfl, rfl, rfl, rfl, fun w hw => ?_, fun w hw => ?_⟩
  · have h1 : (N₁.edges : List (Sym2 V)) = q₁.edges ++ [s(x, ℓ)] := by
      show (joinT p e hp he hd _).edges = _
      rw [joinT_edges]
      simp [p, e]
    have h2 : (N₂.edges : List (Sym2 V)) = q₂.edges := by
      show (q₂.mapLe le_top).edges = _
      simp
    rw [h1, h2]
    show _ = ((R.walk.edges : List (Sym2 V)) : Multiset (Sym2 V)) + _
    rw [hR, Walk.edges_append]
    simp only [← Multiset.coe_add, Multiset.coe_singleton]
    abel
  · rw [mem_joinT_support] at hw
    rcases hw with hw | hw
    · right; simpa [p] using hw
    · simp only [e, Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at hw
      rcases hw with h | h
      · right; rw [h]; exact q₁.end_mem_support
      · left; exact h
  · simpa [N₂] using hw

/-- **Leaf exchange.** Let `ℓ` be a leaf of `K` at `x`, let `deg x ≥ 3`, and let `D` decompose `K`
with exactly one end at `x`, carried by the one-edge path `ℓx`. For every `y ∉ {x, ℓ}` there is a
decomposition `D'` with the same ends in which every path through `ℓ` avoids `y` and does not end
at `x`, and every path lies in a path of `D` together with `ℓ`. -/
theorem leaf_exchange (D : PathDecomp K) {ℓ x y : V} (hℓ : ∀ v, K.Adj ℓ v ↔ v = x)
    (hx3 : 3 ≤ K.degree x) (hxe : D.ends x = 1) (hyx : y ≠ x) (hyℓ : y ≠ ℓ)
    {P₀ : GPath K} (hP₀ : P₀ ∈ D.paths) (hP₀l : P₀.walk.length = 1)
    (hℓP₀ : ℓ ∈ P₀.walk.support) :
    ∃ D' : PathDecomp K, (∀ v, D'.ends v = D.ends v) ∧
      (∀ Q ∈ D'.paths, ℓ ∈ Q.walk.support → y ∉ Q.walk.support ∧ Q.src ≠ x ∧ Q.tgt ≠ x) ∧
      (∀ Q ∈ D'.paths, ∃ P ∈ D.paths, ∀ w ∈ Q.walk.support, w = ℓ ∨ w ∈ P.walk.support) := by
  classical
  have hℓx : K.Adj ℓ x := (hℓ x).mpr rfl
  have hxℓ : x ≠ ℓ := hℓx.ne.symm
  -- the one-edge path `P₀`
  obtain ⟨hadj0, hsupp0, hedges0⟩ := walk_length_one P₀.walk hP₀l
  have hP0ends : (P₀.src = ℓ ∧ P₀.tgt = x) ∨ (P₀.src = x ∧ P₀.tgt = ℓ) := by
    rw [hsupp0] at hℓP₀
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓP₀
    rcases hℓP₀ with h | h
    · left; refine ⟨h.symm, ?_⟩; rw [← h] at hadj0; exact (hℓ _).mp hadj0
    · right; refine ⟨?_, h.symm⟩; rw [← h] at hadj0; exact (hℓ _).mp hadj0.symm
  have hP0end : ∀ v, P₀.endsAt v = (if x = v then 1 else 0) + (if ℓ = v then 1 else 0) := by
    intro v
    unfold GPath.endsAt
    rcases hP0ends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> omega
  have hP0x : P₀.endsAt x = 1 := by rw [hP0end]; simp [Ne.symm hxℓ]
  have hP0e : P₀.edges = [s(x, ℓ)] := by
    unfold GPath.edges; rw [hedges0]
    rcases hP0ends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2, Sym2.eq_swap]
  -- no other path ends at `x`
  have hother : ∀ P ∈ D.paths, P ≠ P₀ → P.endsAt x = 0 := by
    intro P hP hne
    have := sum_map_le_of_ne D.paths (fun P => P.endsAt x) hP₀ hP (Ne.symm hne)
    unfold PathDecomp.ends at hxe
    omega
  -- a path `R` through `x` other than `P₀`
  obtain ⟨z, hz, hzℓ⟩ : ∃ z ∈ K.neighborFinset x, z ≠ ℓ :=
    Finset.exists_mem_ne (by rw [card_neighborFinset_eq_degree]; omega) ℓ
  rw [mem_neighborFinset] at hz
  obtain ⟨R, hR, hzR⟩ : ∃ R ∈ D.paths, s(x, z) ∈ R.edges :=
    List.mem_flatMap.mp ((D.covers _).mp hz)
  have hRP0 : R ≠ P₀ := by
    rintro rfl
    rw [hP0e, List.mem_singleton, Sym2.eq_iff] at hzR
    rcases hzR with ⟨-, h⟩ | ⟨h, -⟩
    · exact hzℓ h
    · exact hxℓ h
  have hxR : x ∈ R.walk.support := Walk.fst_mem_support_of_mem_edges _ hzR
  have hRx := hother R hR hRP0
  -- `ℓ` lies on `P₀` only
  have honly : ∀ P ∈ D.paths, ℓ ∈ P.walk.support → P = P₀ := by
    intro P hP hℓP
    obtain ⟨e, he, hℓe⟩ := P.exists_edge_of_mem hℓP
    have heK := P.walk.edges_subset_edgeSet he
    have : e = s(x, ℓ) := by
      induction e using Sym2.inductionOn with
      | hf p q =>
        rw [mem_edgeSet] at heK
        rcases Sym2.mem_iff.mp hℓe with rfl | rfl
        · rw [(hℓ q).mp heK, Sym2.eq_swap]
        · rw [(hℓ p).mp heK.symm]
    exact D.eq_of_mem_edges hP hP₀ (this ▸ he) (by rw [hP0e]; exact List.mem_singleton_self _)
  have hℓR : ℓ ∉ R.walk.support := fun h => hRP0 (honly R hR h)
  -- split `R` at `x`, oriented so that `y` is not on the first half
  obtain ⟨q₁, q₂, hq⟩ := R.exists_split_support hxR
  obtain ⟨R', q₁', q₂', hq', hE', hends', hsupp', hy1⟩ :
      ∃ (R' : GPath K) (q₁' : K.Walk R'.src x) (q₂' : K.Walk x R'.tgt),
        R'.walk = q₁'.append q₂' ∧ (R'.edges : Multiset (Sym2 V)) = R.edges ∧
        (∀ v, R'.endsAt v = R.endsAt v) ∧ (∀ w, w ∈ R'.walk.support ↔ w ∈ R.walk.support) ∧
        y ∉ q₁'.support := by
    by_cases hy : y ∈ q₁.support
    · refine ⟨R.reverse, q₂.reverse, q₁.reverse, ?_, ?_, fun v => GPath.reverse_endsAt' R v,
        fun w => ?_, ?_⟩
      · show R.walk.reverse = _
        rw [hq, Walk.reverse_append]
        rfl
      · show ((R.walk.reverse.edges : List (Sym2 V)) : Multiset (Sym2 V)) = R.walk.edges
        rw [Walk.edges_reverse, Multiset.coe_reverse]
      · show w ∈ R.walk.reverse.support ↔ _
        rw [Walk.support_reverse, List.mem_reverse]
      · show y ∉ (q₂.reverse : K.Walk R.tgt x).support
        rw [Walk.support_reverse, List.mem_reverse]
        intro hy2
        have hRn := R.support_nodup
        rw [hq] at hRn
        exact hyx (((nodup_support_append q₁ q₂).mp hRn).2.2 y hy hy2)
    · exact ⟨R, q₁, q₂, hq, rfl, fun _ => rfl, fun _ => Iff.rfl, hy⟩
  have hR'x : R'.endsAt x = 0 := by rw [hends']; exact hRx
  have hR's : R'.src ≠ x := by
    intro h; unfold GPath.endsAt at hR'x; rw [if_pos h] at hR'x; omega
  have hR't : x ≠ R'.tgt := by
    intro h; unfold GPath.endsAt at hR'x; rw [if_pos h.symm] at hR'x; omega
  have hℓR' : ℓ ∉ R'.walk.support := fun h => hℓR ((hsupp' ℓ).mp h)
  obtain ⟨N₁, N₂, hNe, h1s, h1t, h2s, h2t, hN₁, hN₂⟩ :=
    exchange_core R' q₁' q₂' hq' hR's hR't hℓR' hxℓ
  have hq₁R : ∀ w ∈ q₁'.support, w ∈ R.walk.support := fun w hw =>
    (hsupp' w).mp (by rw [hq']; exact (Walk.mem_support_append_iff q₁' q₂').mpr (Or.inl hw))
  have hq₂R : ∀ w ∈ q₂'.support, w ∈ R.walk.support := fun w hw =>
    (hsupp' w).mp (by rw [hq']; exact (Walk.mem_support_append_iff q₁' q₂').mpr (Or.inr hw))
  -- the new list of paths
  set rest := (D.paths.erase P₀).erase R with hrest
  have hRmem : R ∈ D.paths.erase P₀ := (List.mem_erase_of_ne hRP0).mpr hR
  have hperm : D.paths.Perm (P₀ :: R :: rest) :=
    (List.perm_cons_erase hP₀).trans ((List.perm_cons_erase hRmem).cons P₀)
  have hpermT := hperm.map GPath.toTop
  let L' : List (TPath V) := N₁ :: N₂ :: rest.map GPath.toTop
  have hEL : edgesM L' = K.edgeFinset.val := by
    rw [← D.edgesM_toTop, edgesM_perm hpermT]
    simp only [L', edgesM_cons, List.map_cons, GPath.toTop_edges]
    rw [← add_assoc, hNe, hE', hP0e]
    simp only [Multiset.coe_singleton]
    abel
  have hendL : ∀ v, endsL L' v = D.ends v := by
    intro v
    rw [← D.endsL_toTop, endsL_perm hpermT]
    simp only [L', endsL_cons, List.map_cons, GPath.toTop_endsAt]
    rw [hP0end v, ← hends' v]
    unfold GPath.endsAt
    rw [h1s, h1t, h2s, h2t]
    omega
  obtain ⟨D', hD'e, hD'p⟩ := exists_decomp_of_edgesM' (G := K) L' hEL
  refine ⟨D', fun v => (hD'e v).trans (hendL v), ?_, ?_⟩
  · intro Q hQ hℓQ
    obtain ⟨T, hT, hTs, hTt, hTsupp⟩ := hD'p Q hQ
    rw [hTsupp] at hℓQ ⊢
    simp only [L', List.mem_cons, List.mem_map] at hT
    rcases hT with rfl | rfl | ⟨P, hP, rfl⟩
    · refine ⟨fun hy => ?_, ?_, ?_⟩
      · rcases hN₁ y hy with h | h
        · exact hyℓ h
        · exact hy1 h
      · rw [hTs, h1s]; exact hR's
      · rw [hTt, h1t]; exact Ne.symm hxℓ
    · exact absurd (hq₂R ℓ (hN₂ ℓ hℓQ)) hℓR
    · exfalso
      rw [GPath.toTop_support] at hℓQ
      have hP' : P ∈ D.paths := List.mem_of_mem_erase (List.mem_of_mem_erase hP)
      have := honly P hP' hℓQ
      subst this
      exact D.paths_nodup.not_mem_erase (List.mem_of_mem_erase hP)
  · intro Q hQ
    obtain ⟨T, hT, -, -, hTsupp⟩ := hD'p Q hQ
    rw [hTsupp]
    simp only [L', List.mem_cons, List.mem_map] at hT
    rcases hT with rfl | rfl | ⟨P, hP, rfl⟩
    · refine ⟨R, hR, fun w hw => ?_⟩
      rcases hN₁ w hw with h | h
      · exact Or.inl h
      · exact Or.inr (hq₁R w h)
    · exact ⟨R, hR, fun w hw => Or.inr (hq₂R w (hN₂ w hw))⟩
    · refine ⟨P, List.mem_of_mem_erase (List.mem_of_mem_erase hP), fun w hw => Or.inr ?_⟩
      rw [GPath.toTop_support] at hw
      exact hw

end exchange

/-! ### Lemma NP: adjacent vertices need not be paired -/

section NP

variable {W : Type u} [Fintype W] [DecidableEq W]

omit [Fintype W] [DecidableEq W] in
/-- A path with one end at a leaf `ℓ` (whose neighbour is `x`) and the other end at `x` is the
edge `ℓx`. -/
theorem leaf_path_length_one {K : SimpleGraph W} {ℓ x : W} (hℓ : ∀ v, K.Adj ℓ v ↔ v = x)
    (P : GPath K) (hend : (P.src = ℓ ∧ P.tgt = x) ∨ (P.src = x ∧ P.tgt = ℓ)) :
    P.walk.length = 1 := by
  have key : ∀ (w : K.Walk ℓ x), w.IsPath → w.length = 1 := by
    intro w hw
    cases w with
    | nil => exact absurd ((hℓ ℓ).mpr rfl) (K.irrefl)
    | cons h p =>
      have hv := (hℓ _).mp h
      subst hv
      have hp : p.IsPath := (Walk.cons_isPath_iff h p).mp hw |>.1
      rw [Walk.isPath_iff_nil] at hp
      cases hp
      rfl
  rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := key (P.walk.copy h1 h2) (by simpa using P.isPath)
    simpa using this
  · have := key (P.walk.reverse.copy h2 h1) (by simpa using P.isPath.reverse)
    simpa using this

/-- **Lemma NP.** Let `H` have no vertex of positive even degree, and let `x ∼ y` with
`deg x ≥ 3`. Then some Lovász decomposition of `H` has no path with ends `x` and `y`: the path
ending at `y` does not end at `x`. -/
theorem not_paired_adj (H : SimpleGraph W) [DecidableRel H.Adj] (hodd : ∀ z, z ∉ evenSet H)
    {x y : W} (hxy : H.Adj x y) (hx3 : 3 ≤ H.degree x) :
    ∃ D : PathDecomp H, (∀ v, D.ends v = H.degree v % 2) ∧
      ∀ P ∈ D.paths, (P.src = y ∨ P.tgt = y) → P.src ≠ x ∧ P.tgt ≠ x := by
  classical
  have hyx : H.Adj y x := hxy.symm
  have hxney : x ≠ y := hxy.ne
  obtain ⟨hKnone, hKy, hKw, hyodd, hevK⟩ := merge_degrees H hodd hyx
  have hcardK : (evenSet (apex (delEdge H x y) {x})).card ≤ 1 :=
    (Finset.card_le_card hevK).trans (by simp)
  have hPk : Packed H {y} := by
    intro p hp q hq hpq
    rw [Finset.mem_singleton] at hp hq
    exact absurd (hp.trans hq.symm) hpq
  have hXK := packed_lift H hyx hPk
  rw [if_pos (Finset.mem_singleton_self y)] at hXK
  obtain ⟨DH, hDH, hmeet⟩ := separation_set _ hcardK hXK
  have hleaf : ∀ v, (apex (delEdge H x y) {x}).Adj none v ↔ v = some x := by
    intro v
    cases v with
    | none => simp
    | some w => simp
  have hKx : (apex (delEdge H x y) {x}).degree (some x) = H.degree x := hKw x hxney
  have hxodd : H.degree x % 2 = 1 := by
    have h1 : x ∉ evenSet H := hodd x
    rw [mem_evenSet_iff_even] at h1
    have : ¬ Even (H.degree x) := fun he => h1 ⟨by omega, he⟩
    exact Nat.odd_iff.mp (Nat.not_even_iff_odd.mp this)
  have hDHx : DH.ends (some x) = 1 := by rw [hDH, hKx, hxodd]
  have hDHy : DH.ends (some y) = 0 := by rw [hDH]; omega
  have hDHn : DH.ends none = 1 := by rw [hDH, hKnone]
  obtain ⟨P, hP, hPend⟩ := DH.exists_end_of_pos (by rw [hDHn]; omega : 0 < DH.ends none)
  have hnP : none ∈ P.walk.support := by
    rcases hPend with h | h
    · rw [← h]; exact P.walk.start_mem_support
    · rw [← h]; exact P.walk.end_mem_support
  have hsep0 : Separates DH (some y) none := by
    intro Q hQ ⟨h1, h2⟩
    have := hmeet Q hQ (some y) (Finset.mem_insert_of_mem (by simp)) none
      (Finset.mem_insert_self _ _) h1 h2
    exact Option.some_ne_none _ this
  -- a decomposition of the leaf graph whose leaf path avoids `y` and does not end at `x`
  obtain ⟨DH', hDH'e, hsep', hC⟩ : ∃ DH' : PathDecomp (apex (delEdge H x y) {x}),
      (∀ v, DH'.ends v = (apex (delEdge H x y) {x}).degree v % 2) ∧
      Separates DH' (some y) none ∧
      ∀ Q ∈ DH'.paths, none ∈ Q.walk.support → Q.src ≠ some x ∧ Q.tgt ≠ some x := by
    by_cases hlen : P.walk.length = 1
    · obtain ⟨D', hD'e, hD'l, -⟩ := leaf_exchange (y := some y) DH hleaf (by rw [hKx]; exact hx3)
        hDHx (by simpa using Ne.symm hxney) (by simp) hP hlen hnP
      refine ⟨D', fun v => (hD'e v).trans (hDH v), fun Q hQ hyn => (hD'l Q hQ hyn.2).1 hyn.1,
        fun Q hQ hn => ⟨(hD'l Q hQ hn).2.1, (hD'l Q hQ hn).2.2⟩⟩
    · refine ⟨DH, hDH, hsep0, fun Q hQ hn => ?_⟩
      have hedge : ∀ R : GPath (apex (delEdge H x y) {x}), none ∈ R.walk.support →
          s(none, some x) ∈ R.edges := by
        intro R hR
        obtain ⟨e, he, hne⟩ := R.exists_edge_of_mem hR
        rw [← apex_none_pendant e (R.walk.edges_subset_edgeSet he) hne]
        exact he
      have hQP : Q = P := DH.eq_of_mem_edges hQ hP (hedge Q hn) (hedge P hnP)
      subst hQP
      constructor
      · intro hs
        refine hlen (leaf_path_length_one hleaf Q ?_)
        rcases hPend with h | h
        · exact absurd (hs.symm.trans h) (Option.some_ne_none x)
        · exact Or.inr ⟨hs, h⟩
      · intro ht
        refine hlen (leaf_path_length_one hleaf Q ?_)
        rcases hPend with h | h
        · exact Or.inl ⟨h, ht⟩
        · exact absurd (ht.symm.trans h) (Option.some_ne_none x)
  obtain ⟨D, hDy, hDw, hcov, -⟩ := leaf_merge H hyx DH' hsep'
  have hDH'y : DH'.ends (some y) = 0 := by rw [hDH'e]; omega
  refine ⟨D, fun v => ?_, fun Q hQ hQend => ?_⟩
  · by_cases hvy : v = y
    · subst hvy
      rw [hDy, hDH'y, hDH'e, hKnone, hyodd]
    · rw [hDw v hvy, hDH'e, hKw v hvy]
  · obtain ⟨P', hP', hsupp⟩ := hcov Q hQ
    obtain ⟨hs, ht⟩ := GPath.ends_of_support_map Q P' (mergeMap y) hsupp
    -- `P'` has an end at the leaf
    have hP'n : P'.src = none ∨ P'.tgt = none := by
      rcases hQend with h | h
      · rw [hs, mergeMap_eq_iff] at h
        rcases h with h | ⟨h, -⟩
        · exfalso
          have := DH'.ends_pos_of_end hP' (v := some y) (Or.inl h)
          omega
        · exact Or.inl h
      · rw [ht, mergeMap_eq_iff] at h
        rcases h with h | ⟨h, -⟩
        · exfalso
          have := DH'.ends_pos_of_end hP' (v := some y) (Or.inr h)
          omega
        · exact Or.inr h
    have hnP' : none ∈ P'.walk.support := by
      rcases hP'n with h | h
      · rw [← h]; exact P'.walk.start_mem_support
      · rw [← h]; exact P'.walk.end_mem_support
    obtain ⟨h1, h2⟩ := hC P' hP' hnP'
    constructor
    · intro h
      rw [hs, mergeMap_eq_iff] at h
      rcases h with h | ⟨-, h⟩
      · exact h1 h
      · exact hxney h
    · intro h
      rw [ht, mergeMap_eq_iff] at h
      rcases h with h | ⟨-, h⟩
      · exact h2 h
      · exact hxney h

end NP

/-! ### Appending an edge at an end, tracking every path -/

section append

variable {V : Type u} [Fintype V] [DecidableEq V] {G H : SimpleGraph V} [DecidableRel G.Adj]
  [DecidableRel H.Adj]

/-- Append the new edge `tu` to a path `P` ending at `t` with `u ∉ P`. Every path of the result is
an old path other than `P` (same ends and support), or the extended path (ends moved from `t` to
`u`, support that of `P` plus `u`). -/
theorem append_edge_track (D : PathDecomp H) {t u : V} (hnew : s(t, u) ∉ H.edgeSet)
    (hG : ∀ e, e ∈ G.edgeSet ↔ e ∈ H.edgeSet ∨ e = s(t, u))
    {P : GPath H} (hP : P ∈ D.paths) (hend : P.src = t ∨ P.tgt = t) (hu : u ∉ P.walk.support) :
    ∃ D' : PathDecomp G,
      (∀ w, D'.ends w + (if t = w then 1 else 0) = D.ends w + (if u = w then 1 else 0)) ∧
      ∀ Q ∈ D'.paths, (∃ R ∈ D.paths, R ≠ P ∧ Q.src = R.src ∧ Q.tgt = R.tgt ∧
          Q.walk.support = R.walk.support) ∨
        ((∀ w, Q.endsAt w + (if t = w then 1 else 0) = P.endsAt w + (if u = w then 1 else 0)) ∧
          ∀ w ∈ Q.walk.support, w = u ∨ w ∈ P.walk.support) := by
  classical
  obtain ⟨Q, hQs, hQe, hQends, hQsupp⟩ := P.exists_orient hend
  have hut : u ≠ Q.src := fun h => hu ((hQsupp u).1 (h ▸ Q.walk.start_mem_support))
  have huQ : u ∉ Q.walk.support := fun h => hu ((hQsupp u).1 h)
  let Pa : TPath V := ⟨u, Q.tgt, Walk.cons (by simpa using hut) (Q.walk.mapLe le_top),
    by
      rw [Walk.cons_isPath_iff]
      exact ⟨by simpa using Q.isPath, by simpa using huQ⟩,
    by simp⟩
  have hPae : Pa.edges = s(u, Q.src) :: Q.edges := by
    show (Walk.cons _ (Q.walk.mapLe le_top)).edges = _
    rw [Walk.edges_cons, Walk.edges_mapLe_eq_edges]
    rfl
  set rest := D.paths.erase P with hrest
  have hperm : D.paths.Perm (P :: rest) := List.perm_cons_erase hP
  let L' : List (TPath V) := Pa :: rest.map GPath.toTop
  have hEL : edgesM L' = G.edgeFinset.val := by
    have hGval : G.edgeFinset.val = H.edgeFinset.val + {s(t, u)} :=
      edgeFinset_val_eq_add {s(t, u)} (Multiset.nodup_singleton _)
        (fun e he => by rw [Multiset.mem_singleton] at he; rw [he]; exact hnew)
        (fun e => by rw [hG e, Multiset.mem_singleton])
    rw [hGval, ← D.edgesM_toTop, edgesM_perm (hperm.map GPath.toTop)]
    simp only [L', edgesM_cons, List.map_cons, GPath.toTop_edges, hPae]
    rw [show s(u, Q.src) = s(t, u) by rw [hQs, Sym2.eq_swap]]
    rw [show ((s(t, u) :: Q.edges : List (Sym2 V)) : Multiset (Sym2 V)) =
      {s(t, u)} + (Q.edges : Multiset (Sym2 V)) by simp]
    rw [Multiset.coe_eq_coe.mpr hQe]
    abel
  have hPaend : ∀ w, Pa.endsAt w + (if t = w then 1 else 0) = P.endsAt w + (if u = w then 1 else 0) := by
    intro w
    rw [← hQends w]
    show (if u = w then 1 else 0) + (if Q.tgt = w then 1 else 0) + _ = _
    unfold GPath.endsAt
    rw [hQs]
    omega
  have hendL : ∀ w, endsL L' w + (if t = w then 1 else 0) = D.ends w + (if u = w then 1 else 0) := by
    intro w
    rw [← D.endsL_toTop, endsL_perm (hperm.map GPath.toTop)]
    simp only [L', endsL_cons, List.map_cons, GPath.toTop_endsAt]
    have := hPaend w
    omega
  obtain ⟨D', hD'e, hD'p⟩ := exists_decomp_of_edgesM' (G := G) L' hEL
  refine ⟨D', fun w => by rw [hD'e w]; exact hendL w, fun R hR => ?_⟩
  obtain ⟨T, hT, hTs, hTt, hTsupp⟩ := hD'p R hR
  simp only [L', List.mem_cons, List.mem_map] at hT
  rcases hT with rfl | ⟨R₀, hR₀, rfl⟩
  · right
    refine ⟨fun w => ?_, fun w hw => ?_⟩
    · have : R.endsAt w = Pa.endsAt w := by unfold GPath.endsAt; rw [hTs, hTt]
      rw [this]; exact hPaend w
    · rw [hTsupp] at hw
      have : w ∈ (Walk.cons _ (Q.walk.mapLe le_top) : (⊤ : SimpleGraph V).Walk u Q.tgt).support := hw
      rw [Walk.support_cons, Walk.support_mapLe_eq_support, List.mem_cons] at this
      rcases this with h | h
      · exact Or.inl h
      · exact Or.inr ((hQsupp w).1 h)
  · left
    refine ⟨R₀, List.mem_of_mem_erase hR₀, fun h => ?_, hTs, hTt, by rw [hTsupp, GPath.toTop_support]⟩
    subst h
    exact D.paths_nodup.not_mem_erase hR₀

end append

/-! ### DL when `a` is a leaf at the even vertex -/

section leaf

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- A set containing `a` and closed under taking neighbours contains every vertex reachable from
`a`. -/
theorem reachable_mem_of_closed {G : SimpleGraph V} {S : Set V} {a x : V} (ha : a ∈ S)
    (hS : ∀ v ∈ S, ∀ w, G.Adj v w → w ∈ S) (hx : G.Reachable a x) : x ∈ S := by
  obtain ⟨p⟩ := hx
  revert ha
  induction p with
  | nil => exact id
  | cons h p ih => intro ha; exact ih (hS _ ha _ h)

/-- **DL when `a` is a leaf at the even vertex.** Let `G` have at most one vertex of positive even
degree, `g`, let `a` be a leaf whose neighbour is `g`, and let `b ≠ a` be odd. Unless `a, b` are
universal twins (the component is the path `a g b`), some Lovász decomposition has the path ending
at `b` avoiding `a`. -/
theorem avoid_leaf (G : SimpleGraph V) [DecidableRel G.Adj] (hev : (evenSet G).card ≤ 1)
    {g a b : V} (hg : g ∈ evenSet G) (hag : ∀ v, G.Adj a v ↔ v = g)
    (hb : G.degree b % 2 = 1) (hab : a ≠ b) (htw : ¬ UnivTwins G a b) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∀ P ∈ D.paths, (P.src = b ∨ P.tgt = b) → a ∉ P.walk.support := by
  classical
  have hag' : G.Adj a g := (hag g).mpr rfl
  have hga : G.Adj g a := hag'.symm
  have hgne : g ≠ a := hga.ne
  have hdeg := delEdge_degree G hga
  have hda : G.degree a = 1 := by
    rw [← card_neighborFinset_eq_degree]
    have : G.neighborFinset a = {g} := by ext v; simp [hag]
    rw [this, Finset.card_singleton]
  have hgeven := mem_evenSet_iff_even.mp hg
  have huniq : ∀ w ∈ evenSet G, w = g := fun w hw => Finset.card_le_one.mp hev w hw g hg
  have hHa : (delEdge G g a).degree a = 0 := by
    have := hdeg a; simp only [Ne.symm hgne, if_false, if_true] at this; omega
  have hHg : (delEdge G g a).degree g + 1 = G.degree g := by
    have := hdeg g; simp only [hgne, if_false, if_true] at this; omega
  have hHw : ∀ w, w ≠ g → w ≠ a → (delEdge G g a).degree w = G.degree w := by
    intro w h1 h2; have := hdeg w; simp only [h1, h2, if_false] at this; omega
  have hbg : b ≠ g := by
    intro h; subst h
    obtain ⟨k, hk⟩ := hgeven.2
    omega
  have hgodd : (delEdge G g a).degree g % 2 = 1 := by
    obtain ⟨k, hk⟩ := hgeven.2
    omega
  have hodd : ∀ z, z ∉ evenSet (delEdge G g a) := by
    intro z hz
    rw [mem_evenSet_iff_even] at hz
    by_cases hzg : z = g
    · subst hzg
      obtain ⟨k, hk⟩ := hz.2
      omega
    · by_cases hza : z = a
      · subst hza; omega
      · rw [hHw z hzg hza] at hz
        exact hzg (huniq z (mem_evenSet_iff_even.mpr hz))
  have hcard0 : (evenSet (delEdge G g a)).card = 0 :=
    Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem hodd)
  have hHb : (delEdge G g a).degree b % 2 = 1 := by rw [hHw b hbg (Ne.symm hab)]; exact hb
  have hoddpos : ∀ z, 0 < (delEdge G g a).degree z → (delEdge G g a).degree z % 2 = 1 := by
    intro z hz
    have h1 := hodd z
    rw [mem_evenSet_iff_even] at h1
    have : ¬ Even ((delEdge G g a).degree z) := fun he => h1 ⟨hz, he⟩
    exact Nat.odd_iff.mp (Nat.not_even_iff_odd.mp this)
  -- a decomposition of `G − ga` in which `g` and `b` are not the two ends of one path
  obtain ⟨DH, hDH, hnp⟩ : ∃ DH : PathDecomp (delEdge G g a),
      (∀ v, DH.ends v = (delEdge G g a).degree v % 2) ∧
      ∀ P ∈ DH.paths, (P.src = b ∨ P.tgt = b) → P.src ≠ g ∧ P.tgt ≠ g := by
    by_cases hadj : (delEdge G g a).Adj b g
    · by_cases hg3 : 3 ≤ (delEdge G g a).degree g
      · exact not_paired_adj _ hodd hadj.symm hg3
      · by_cases hb3 : 3 ≤ (delEdge G g a).degree b
        · obtain ⟨D, hD, h⟩ := not_paired_adj _ hodd hadj hb3
          refine ⟨D, hD, fun P hP hPb => ⟨fun hs => ?_, fun ht => ?_⟩⟩
          · have := h P hP (Or.inl hs)
            rcases hPb with h1 | h1
            · exact this.1 h1
            · exact this.2 h1
          · have := h P hP (Or.inr ht)
            rcases hPb with h1 | h1
            · exact this.1 h1
            · exact this.2 h1
        · -- both have degree one in `G − ga`: the component is the path `a g b`
          exfalso
          apply htw
          have hgpos : 0 < (delEdge G g a).degree g :=
            ((delEdge G g a).degree_pos_iff_exists_adj g).mpr ⟨b, hadj.symm⟩
          have hbpos : 0 < (delEdge G g a).degree b :=
            ((delEdge G g a).degree_pos_iff_exists_adj b).mpr ⟨g, hadj⟩
          have hg1 : (delEdge G g a).degree g = 1 := by have := hoddpos g hgpos; omega
          have hb1 : (delEdge G g a).degree b = 1 := by have := hoddpos b hbpos; omega
          have hNg : ∀ v, (delEdge G g a).Adj g v ↔ v = b := by
            intro v
            constructor
            · intro hv
              have hsub : ({v, b} : Finset V) ⊆ (delEdge G g a).neighborFinset g := by
                intro w hw
                simp only [Finset.mem_insert, Finset.mem_singleton] at hw
                rw [mem_neighborFinset]
                rcases hw with rfl | rfl
                · exact hv
                · exact hadj.symm
              by_contra hvb
              have := Finset.card_le_card hsub
              rw [card_neighborFinset_eq_degree, hg1, Finset.card_pair hvb] at this
              omega
            · rintro rfl; exact hadj.symm
          have hNb : ∀ v, (delEdge G g a).Adj b v ↔ v = g := by
            intro v
            constructor
            · intro hv
              have hsub : ({v, g} : Finset V) ⊆ (delEdge G g a).neighborFinset b := by
                intro w hw
                simp only [Finset.mem_insert, Finset.mem_singleton] at hw
                rw [mem_neighborFinset]
                rcases hw with rfl | rfl
                · exact hv
                · exact hadj
              by_contra hvg
              have := Finset.card_le_card hsub
              rw [card_neighborFinset_eq_degree, hb1, Finset.card_pair hvg] at this
              omega
            · rintro rfl; exact hadj
          have hGg : ∀ v, G.Adj g v → v = a ∨ v = b := by
            intro v hv
            by_cases hva : v = a
            · exact Or.inl hva
            · right
              refine (hNg v).mp ⟨hv, fun h => ?_⟩
              rw [Sym2.eq_iff] at h
              rcases h with ⟨-, h⟩ | ⟨h, -⟩
              · exact hva h
              · exact hgne.symm (h.symm.trans rfl) |>.elim
          have hGb : ∀ v, G.Adj b v → v = g := by
            intro v hv
            refine (hNb v).mp ⟨hv, fun h => ?_⟩
            rw [Sym2.eq_iff] at h
            rcases h with ⟨h, -⟩ | ⟨h, -⟩
            · exact hbg h
            · exact hab h.symm
          have hbgG : G.Adj b g := hadj.1
          have hclosed : ∀ v ∈ ({a, g, b} : Set V), ∀ w, G.Adj v w → w ∈ ({a, g, b} : Set V) := by
            intro v hv w hw
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv ⊢
            rcases hv with rfl | rfl | rfl
            · exact Or.inr (Or.inl ((hag w).mp hw))
            · rcases hGg w hw with h | h
              · exact Or.inl h
              · exact Or.inr (Or.inr h)
            · exact Or.inr (Or.inl (hGb w hw))
          refine ⟨hag'.reachable.trans hbgG.symm.reachable, fun x hxa hxb hx => ?_⟩
          have hmem := reachable_mem_of_closed (S := ({a, g, b} : Set V))
            (by simp) hclosed hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
          rcases hmem with h | h | h
          · exact absurd h hxa
          · subst h; exact ⟨hag', hbgG⟩
          · exact absurd h hxb
    · obtain ⟨D, hD, h⟩ := lovasz_avoid_nonadj _ hcard0 hHb hbg hadj
      exact ⟨D, hD, fun P hP hPb =>
        ⟨fun hs => h P hP hPb ((congrArg (fun v => v ∈ P.walk.support) hs).mp
            P.walk.start_mem_support),
          fun ht => h P hP hPb ((congrArg (fun v => v ∈ P.walk.support) ht).mp
            P.walk.end_mem_support)⟩⟩
  -- append `ga` to the path ending at `g`
  obtain ⟨Pg, hPg, hPgend⟩ := DH.exists_end_of_pos (x := g) (by rw [hDH, hgodd]; omega)
  have haPg : a ∉ Pg.walk.support := fun h => by
    have := GPath.degree_pos_of_mem Pg h; omega
  have hnew : s(g, a) ∉ (delEdge G g a).edgeSet := by
    rw [delEdge_edgeSet]; simp
  have hG : ∀ e, e ∈ G.edgeSet ↔ e ∈ (delEdge G g a).edgeSet ∨ e = s(g, a) := by
    intro e
    rw [delEdge_edgeSet]
    by_cases he : e = s(g, a)
    · subst he; simp [hga]
    · simp [he]
  obtain ⟨D, hDe, hDp⟩ := append_edge_track (G := G) DH hnew hG hPg hPgend haPg
  refine ⟨D, fun v => ?_, fun Q hQ hQb => ?_⟩
  · have h1 := hDe v
    rw [hDH v] at h1
    by_cases hvg : v = g
    · subst hvg
      simp only [if_true, Ne.symm hgne, if_false] at h1
      obtain ⟨k, hk⟩ := hgeven.2
      omega
    · by_cases hva : v = a
      · subst hva
        simp only [hgne, if_false, if_true] at h1
        rw [hHa] at h1
        omega
      · simp only [Ne.symm hvg, Ne.symm hva, if_false] at h1
        rw [hHw v hvg hva] at h1
        omega
  · rcases hDp Q hQ with ⟨R, hR, -, -, -, hsupp⟩ | ⟨hends, -⟩
    · rw [hsupp]
      intro ha
      have := GPath.degree_pos_of_mem R ha
      omega
    · exfalso
      have h1 := hends b
      simp only [Ne.symm hbg, hab, if_false, add_zero] at h1
      have hPgb : Pg.endsAt b = 0 := by
        unfold GPath.endsAt
        rcases hPgend with h | h
        · have hne : Pg.src ≠ b := by rw [h]; exact Ne.symm hbg
          have : Pg.tgt ≠ b := fun ht => (hnp Pg hPg (Or.inr ht)).1 h
          simp [hne, this]
        · have hne : Pg.tgt ≠ b := by rw [h]; exact Ne.symm hbg
          have : Pg.src ≠ b := fun hs => (hnp Pg hPg (Or.inl hs)).2 h
          simp [hne, this]
      have hQb' : 0 < Q.endsAt b := by
        unfold GPath.endsAt
        rcases hQb with h | h <;> simp [h]
      omega

end leaf

/-! ### DL when the even vertex has degree two -/

section degTwo

variable {V : Type u} [Fintype V] [DecidableEq V]

variable {G : SimpleGraph V} [DecidableRel G.Adj] {g a b : V}

theorem splitOff_facts (hNg : ∀ v, G.Adj g v ↔ v = a ∨ v = b) (hab : a ≠ b)
    (hnadj : ¬ G.Adj a b) :
    (∀ w, w ≠ g → (plusEdge (delEdge (delEdge G g a) g b) a b).degree w = G.degree w) ∧
    (plusEdge (delEdge (delEdge G g a) g b) a b).degree g = 0 ∧
    (plusEdge (delEdge (delEdge G g a) g b) a b).Adj a b ∧
    (∀ x y, (plusEdge (delEdge (delEdge G g a) g b) a b).Adj x y →
      (x = a ∧ y = b) ∨ (x = b ∧ y = a) ∨ (G.Adj x y ∧ x ≠ g ∧ y ≠ g)) ∧
    G.edgeFinset.val + {s(a, b)} =
      (plusEdge (delEdge (delEdge G g a) g b) a b).edgeFinset.val + ({s(g, a)} + {s(g, b)}) := by
  classical
  have hga : G.Adj g a := (hNg a).mpr (Or.inl rfl)
  have hgb : G.Adj g b := (hNg b).mpr (Or.inr rfl)
  have hgA : g ≠ a := hga.ne
  have hgB : g ≠ b := hgb.ne
  have hgb1 : (delEdge G g a).Adj g b := ⟨hgb, by
    rw [Sym2.eq_iff]; rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact hab h.symm
    · exact hgA h⟩
  have hn2 : ¬ (delEdge (delEdge G g a) g b).Adj a b := fun h => hnadj h.1.1
  have hd1 := delEdge_degree G hga
  have hd2 := delEdge_degree (delEdge G g a) hgb1
  have hd3 := plusEdge_degree (G := delEdge (delEdge G g a) g b) hab hn2
  have hdg : G.degree g = 2 := by
    rw [← card_neighborFinset_eq_degree]
    have : G.neighborFinset g = {a, b} := by ext v; simp [hNg]
    rw [this, Finset.card_pair hab]
  refine ⟨fun w hw => ?_, ?_, ?_, fun x y hxy => ?_, ?_⟩
  · have e1 := hd1 w; have e2 := hd2 w; have e3 := hd3 w
    by_cases hwa : w = a
    · subst hwa; simp [hw, hab] at e1 e2 e3; omega
    · by_cases hwb : w = b
      · subst hwb; simp [hw, hwa, Ne.symm hab] at e1 e2 e3; omega
      · simp [hw, hwa, hwb] at e1 e2 e3; omega
  · have e1 := hd1 g; have e2 := hd2 g; have e3 := hd3 g
    simp [hgA, hgB] at e1 e2 e3; omega
  · exact Or.inr ⟨hab, Or.inl ⟨rfl, rfl⟩⟩
  · rcases hxy with h | ⟨-, h⟩
    · right; right
      obtain ⟨⟨hG, h1⟩, h2⟩ := h
      refine ⟨hG, fun hx => ?_, fun hy => ?_⟩
      · subst hx
        rcases (hNg y).mp hG with rfl | rfl
        · exact h1 rfl
        · exact h2 rfl
      · subst hy
        rcases (hNg x).mp hG.symm with rfl | rfl
        · exact h1 (Sym2.eq_swap)
        · exact h2 (Sym2.eq_swap)
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  · have hE2 : ∀ e, e ∈ G.edgeSet ↔ e ∈ (delEdge (delEdge G g a) g b).edgeSet ∨
        e ∈ ({s(g, a)} + {s(g, b)} : Multiset (Sym2 V)) := by
      intro e
      rw [delEdge_edgeSet, delEdge_edgeSet, Multiset.mem_add, Multiset.mem_singleton,
        Multiset.mem_singleton]
      by_cases h1 : e = s(g, a)
      · subst h1; simp [hga]
      · by_cases h2 : e = s(g, b)
        · subst h2; simp [hgb]
        · simp [h1, h2]
    have hGv := edgeFinset_val_eq_add (G := G) ({s(g, a)} + {s(g, b)})
      (by
        rw [Multiset.nodup_add]
        refine ⟨Multiset.nodup_singleton _, Multiset.nodup_singleton _, ?_⟩
        rw [Multiset.disjoint_singleton]
        rw [Multiset.mem_singleton, Sym2.eq_iff]
        rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact hab h.symm
        · exact hgA h)
      (by
        intro e he
        rw [Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_singleton] at he
        rw [delEdge_edgeSet, delEdge_edgeSet]
        rcases he with rfl | rfl
        · simp
        · simp)
      hE2
    have hHv := edgeFinset_val_eq_add (G := plusEdge (delEdge (delEdge G g a) g b) a b) {s(a, b)} (Multiset.nodup_singleton _)
      (by intro e he; rw [Multiset.mem_singleton] at he; subst he; rw [mem_edgeSet]; exact hn2)
      (by intro e; rw [plusEdge_edgeSet hab, Multiset.mem_singleton])
    rw [hGv, hHv]
    abel

/-- The core of `avoid_deg_two`, for any graph `H` with the properties of `G − ga − gb + ab`.

Proof: split `g` off (`H = G − ga − gb + ab`, no vertex of positive even degree), hang a leaf at `a`
standing for `b` (now `b` is the only even vertex, and `a, b` are at distance at least three),
separate `a` from `b`, make `a` interior to the leaf path by a leaf exchange, merge the leaf into
`b`, and subdivide `ab` by `g`. -/
theorem avoid_deg_two_core (H : SimpleGraph V) [DecidableRel H.Adj]
    (hev : (evenSet G).card ≤ 1) (hg : g ∈ evenSet G)
    (hNg : ∀ v, G.Adj g v ↔ v = a ∨ v = b) (hab : a ≠ b)
    (hcn : ∀ w, G.Adj a w → G.Adj b w → w = g) (ha3 : 3 ≤ G.degree a)
    (hHw : ∀ w, w ≠ g → H.degree w = G.degree w) (hHg : H.degree g = 0) (hHab : H.Adj a b)
    (hHadj : ∀ x y, H.Adj x y → (x = a ∧ y = b) ∨ (x = b ∧ y = a) ∨ (G.Adj x y ∧ x ≠ g ∧ y ≠ g))
    (hval : G.edgeFinset.val + {s(a, b)} = H.edgeFinset.val + ({s(g, a)} + {s(g, b)})) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∀ P ∈ D.paths, (P.src = a ∨ P.tgt = a) → b ∉ P.walk.support := by
  classical
  have hga : G.Adj g a := (hNg a).mpr (Or.inl rfl)
  have hgb : G.Adj g b := (hNg b).mpr (Or.inr rfl)
  have hgA : g ≠ a := hga.ne
  have hgB : g ≠ b := hgb.ne
  have huniq : ∀ w ∈ evenSet G, w = g := fun w hw => Finset.card_le_one.mp hev w hw g hg
  have hoddG : ∀ w, w ≠ g → 0 < G.degree w → G.degree w % 2 = 1 := by
    intro w hwg hpos
    have : w ∉ evenSet G := fun h => hwg (huniq w h)
    rw [mem_evenSet_iff_even] at this
    have : ¬ Even (G.degree w) := fun he => this ⟨hpos, he⟩
    exact Nat.odd_iff.mp (Nat.not_even_iff_odd.mp this)
  have hodd : ∀ z, z ∉ evenSet H := by
    intro z hz
    rw [mem_evenSet_iff_even] at hz
    by_cases hzg : z = g
    · subst hzg; rw [hHg] at hz; omega
    · rw [hHw z hzg] at hz
      exact hzg (huniq z (mem_evenSet_iff_even.mpr hz))
  have hHba : H.Adj b a := hHab.symm
  have hadeg : H.degree a = G.degree a := hHw a (Ne.symm hgA)
  have haodd : G.degree a % 2 = 1 := hoddG a (Ne.symm hgA) (by omega)
  -- the leaf graph `K = apex (H − ab) {a}`: the leaf stands for `b`
  obtain ⟨hKnone, hKb, hKw, hbodd, hevK⟩ := merge_degrees H hodd hHba
  have hcardK : (evenSet (apex (delEdge H a b) {a})).card ≤ 1 :=
    (Finset.card_le_card hevK).trans (by simp)
  have hleaf : ∀ v, (apex (delEdge H a b) {a}).Adj none v ↔ v = some a := by
    intro v; cases v with
    | none => simp
    | some w => simp
  -- `a` and `b` are at distance at least three in `K`
  have hX : Packed (apex (delEdge H a b) {a}) {some a, some b} := by
    have key : ∀ w, ¬ ((apex (delEdge H a b) {a}).Adj (some a) w ∧
        (apex (delEdge H a b) {a}).Adj w (some b)) := by
      rintro w ⟨h1, h2⟩
      cases w with
      | none => simp at h2; exact hab h2.symm
      | some w =>
        simp only [apex_adj_some_some] at h1 h2
        obtain ⟨h1, h1'⟩ := h1
        obtain ⟨h2, h2'⟩ := h2
        have hwb : w ≠ b := by rintro rfl; exact h1' rfl
        have hwa : w ≠ a := by rintro rfl; exact h2' rfl
        rcases hHadj a w h1 with ⟨-, h⟩ | ⟨h, -⟩ | ⟨hGa, -, hwg⟩
        · exact hwb h
        · exact hab h
        · rcases hHadj w b h2 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨hGb, -, -⟩
          · exact hwa h
          · exact hwb h
          · exact hwg (hcn w hGa hGb.symm)
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · refine ⟨fun h => ?_, key⟩
      simp only [apex_adj_some_some] at h
      exact h.2 rfl
    · refine ⟨fun h => ?_, fun w hw => key w ⟨hw.2.symm, hw.1.symm⟩⟩
      simp only [apex_adj_some_some] at h
      exact h.2 Sym2.eq_swap
    · exact absurd rfl hxy
  obtain ⟨DK, hDK, hmeet⟩ := separation_set _ hcardK hX
  have hKa : (apex (delEdge H a b) {a}).degree (some a) = G.degree a := by
    rw [hKw a hab, hadeg]
  have hDKa : DK.ends (some a) = 1 := by rw [hDK, hKa, haodd]
  have hDKn : DK.ends none = 1 := by rw [hDK, hKnone]
  have hmeetab : ∀ Q ∈ DK.paths, ¬ (some a ∈ Q.walk.support ∧ some b ∈ Q.walk.support) := by
    intro Q hQ ⟨h1, h2⟩
    have := hmeet Q hQ (some a) (by simp) (some b) (by simp) h1 h2
    exact hab (Option.some_injective _ this)
  have hedge : ∀ R : GPath (apex (delEdge H a b) {a}), none ∈ R.walk.support →
      s(none, some a) ∈ R.edges := by
    intro R hR
    obtain ⟨e, he, hne⟩ := R.exists_edge_of_mem hR
    rw [← apex_none_pendant e (R.walk.edges_subset_edgeSet he) hne]
    exact he
  obtain ⟨P, hP, hPend⟩ := DK.exists_end_of_pos (by rw [hDKn]; omega : 0 < DK.ends none)
  have hnP : none ∈ P.walk.support := by
    rcases hPend with h | h
    · rw [← h]; exact P.walk.start_mem_support
    · rw [← h]; exact P.walk.end_mem_support
  -- a decomposition of `K` separating `a, b` whose leaf path does not end at `a`
  obtain ⟨DK', hDK'e, hsepab, hC⟩ : ∃ DK' : PathDecomp (apex (delEdge H a b) {a}),
      (∀ v, DK'.ends v = (apex (delEdge H a b) {a}).degree v % 2) ∧
      (∀ Q ∈ DK'.paths, ¬ (some a ∈ Q.walk.support ∧ some b ∈ Q.walk.support)) ∧
      ∀ Q ∈ DK'.paths, none ∈ Q.walk.support → Q.src ≠ some a ∧ Q.tgt ≠ some a := by
    by_cases hlen : P.walk.length = 1
    · obtain ⟨D', hD'e, hD'l, hD's⟩ := leaf_exchange (y := some b) DK hleaf
        (by rw [hKa]; exact ha3) hDKa (by simpa using Ne.symm hab) (by simp) hP hlen hnP
      refine ⟨D', fun v => (hD'e v).trans (hDK v), fun Q hQ ⟨h1, h2⟩ => ?_,
        fun Q hQ hn => ⟨(hD'l Q hQ hn).2.1, (hD'l Q hQ hn).2.2⟩⟩
      obtain ⟨P', hP', hsub⟩ := hD's Q hQ
      rcases hsub _ h1 with h | h
      · exact Option.some_ne_none _ h
      rcases hsub _ h2 with h' | h'
      · exact Option.some_ne_none _ h'
      exact hmeetab P' hP' ⟨h, h'⟩
    · refine ⟨DK, hDK, hmeetab, fun Q hQ hn => ?_⟩
      have hQP : Q = P := DK.eq_of_mem_edges hQ hP (hedge Q hn) (hedge P hnP)
      subst hQP
      constructor
      · intro hs
        refine hlen (leaf_path_length_one hleaf Q ?_)
        rcases hPend with h | h
        · exact absurd (hs.symm.trans h) (Option.some_ne_none a)
        · exact Or.inr ⟨hs, h⟩
      · intro ht
        refine hlen (leaf_path_length_one hleaf Q ?_)
        rcases hPend with h | h
        · exact Or.inl ⟨h, ht⟩
        · exact absurd (ht.symm.trans h) (Option.some_ne_none a)
  have hsep' : Separates DK' (some b) none := by
    intro Q hQ ⟨h1, h2⟩
    exact hsepab Q hQ ⟨Walk.snd_mem_support_of_mem_edges _ (hedge Q h2), h1⟩
  -- merge the leaf into `b`: a Lovász decomposition of `H`
  obtain ⟨DH, hDHb, hDHw, hcov, -⟩ := leaf_merge H hHba DK' hsep'
  have hDK'b : DK'.ends (some b) = 0 := by rw [hDK'e]; omega
  have hDH : ∀ v, DH.ends v = H.degree v % 2 := by
    intro v
    by_cases hvb : v = b
    · subst hvb; rw [hDHb, hDK'b, hDK'e, hKnone, hbodd]
    · rw [hDHw v hvb, hDK'e, hKw v hvb]
  have hkey : ∀ Q ∈ DH.paths, (Q.src = a ∨ Q.tgt = a) → b ∉ Q.walk.support := by
    intro Q hQ hQa hbQ
    obtain ⟨P', hP', hsupp⟩ := hcov Q hQ
    obtain ⟨hs, ht⟩ := GPath.ends_of_support_map Q P' (mergeMap b) hsupp
    have haP' : some a ∈ P'.walk.support ∧ (P'.src = some a ∨ P'.tgt = some a) := by
      rcases hQa with h | h
      · rw [hs, mergeMap_eq_iff] at h
        rcases h with h | ⟨-, h⟩
        · exact ⟨h ▸ P'.walk.start_mem_support, Or.inl h⟩
        · exact absurd h hab
      · rw [ht, mergeMap_eq_iff] at h
        rcases h with h | ⟨-, h⟩
        · exact ⟨h ▸ P'.walk.end_mem_support, Or.inr h⟩
        · exact absurd h hab
    have hnP' : none ∉ P'.walk.support := by
      intro hn
      obtain ⟨h1, h2⟩ := hC P' hP' hn
      rcases haP'.2 with h | h
      · exact h1 h
      · exact h2 h
    rw [hsupp, List.mem_map] at hbQ
    obtain ⟨v, hv, hvb⟩ := hbQ
    rw [mergeMap_eq_iff] at hvb
    rcases hvb with rfl | ⟨rfl, -⟩
    · exact hsepab P' hP' ⟨haP'.1, hv⟩
    · exact hnP' hv
  -- the path of `DH` through `ab`, and its subdivision by `g`
  obtain ⟨R, hR, habR⟩ : ∃ R ∈ DH.paths, s(a, b) ∈ R.edges :=
    List.mem_flatMap.mp ((DH.covers _).mp hHab)
  have hgR : g ∉ R.walk.support := fun h => by
    have := GPath.degree_pos_of_mem R h; omega
  have hbR : b ∈ R.walk.support := Walk.snd_mem_support_of_mem_edges _ habR
  have hRa : R.src ≠ a ∧ R.tgt ≠ a := ⟨fun h => hkey R hR (Or.inl h) hbR,
    fun h => hkey R hR (Or.inr h) hbR⟩
  let T : TPath V := ⟨a, b, Walk.cons (show (⊤ : SimpleGraph V).Adj a g from by simpa using Ne.symm hgA)
      (Walk.cons (show (⊤ : SimpleGraph V).Adj g b from by simpa using hgB) Walk.nil),
    by
      rw [Walk.isPath_def]
      simp [Ne.symm hgA, hab, hgB],
    by simp⟩
  have hTe : T.edges = [s(a, g), s(g, b)] := rfl
  obtain ⟨R', hR's, hR't, hR'e, hR'supp⟩ := exists_subst_path R.toTop T (by simpa using habR)
    rfl rfl (by
      intro w hw hwR
      simp only [T, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact Or.inl rfl
      · rw [GPath.toTop_support] at hwR
        exact absurd hwR hgR
      · exact Or.inr rfl)
  set rest := DH.paths.erase R with hrest
  have hperm : DH.paths.Perm (R :: rest) := List.perm_cons_erase hR
  let L' : List (TPath V) := R' :: rest.map GPath.toTop
  have hEL : edgesM L' = G.edgeFinset.val := by
    have h1 : edgesM L' + {s(a, b)} = H.edgeFinset.val + T.edges := by
      rw [← DH.edgesM_toTop, edgesM_perm (hperm.map GPath.toTop)]
      simp only [L', edgesM_cons, List.map_cons]
      rw [add_right_comm, hR'e]
      simp only [GPath.toTop_edges]
      abel
    have h2 : (T.edges : Multiset (Sym2 V)) = {s(g, a)} + {s(g, b)} := by
      rw [hTe, Sym2.eq_swap (a := a)]
      rfl
    rw [h2, ← hval] at h1
    exact add_right_cancel h1
  have hendL : ∀ v, endsL L' v = DH.ends v := by
    intro v
    rw [← DH.endsL_toTop, endsL_perm (hperm.map GPath.toTop)]
    simp only [L', endsL_cons, List.map_cons, GPath.toTop_endsAt]
    unfold GPath.endsAt
    rw [hR's, hR't]
    rfl
  obtain ⟨D, hDe, hDp⟩ := exists_decomp_of_edgesM' (G := G) L' hEL
  refine ⟨D, fun v => ?_, fun Q hQ hQa => ?_⟩
  · rw [hDe v, hendL v, hDH v]
    by_cases hvg : v = g
    · subst hvg
      rw [hHg]
      obtain ⟨k, hk⟩ := (mem_evenSet_iff_even.mp hg).2
      omega
    · rw [hHw v hvg]
  · obtain ⟨T', hT', hTs, hTt, hTsupp⟩ := hDp Q hQ
    simp only [L', List.mem_cons, List.mem_map] at hT'
    rcases hT' with rfl | ⟨R₀, hR₀, rfl⟩
    · exfalso
      rcases hQa with h | h
      · rw [hTs, hR's] at h; exact hRa.1 h
      · rw [hTt, hR't] at h; exact hRa.2 h
    · rw [hTsupp, GPath.toTop_support]
      have hs : Q.src = R₀.src := hTs
      have ht : Q.tgt = R₀.tgt := hTt
      exact hkey R₀ (List.mem_of_mem_erase hR₀) (by rw [← hs, ← ht]; exact hQa)

/-- **DL when the even vertex has degree two and is the only common neighbour.** Let `g` be the
even vertex, `N(g) = {a, b}`, `ab ∉ E`, `N(a) ∩ N(b) = {g}`, and `deg a ≥ 3`. Then some Lovász
decomposition of `G` has the path ending at `a` avoiding `b`.

Proof (`avoid_deg_two_core`): split `g` off (`H = G − ga − gb + ab`, no vertex of positive even
degree), hang a leaf at `a` standing for `b` (now `b` is the only even vertex, and `a, b` are at
distance at least three), separate `a` from `b`, make `a` interior to the leaf path by a leaf
exchange, merge the leaf into `b`, and subdivide `ab` by `g`. -/
theorem avoid_deg_two (hev : (evenSet G).card ≤ 1) (hg : g ∈ evenSet G)
    (hNg : ∀ v, G.Adj g v ↔ v = a ∨ v = b) (hab : a ≠ b) (hnadj : ¬ G.Adj a b)
    (hcn : ∀ w, G.Adj a w → G.Adj b w → w = g) (ha3 : 3 ≤ G.degree a) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∀ P ∈ D.paths, (P.src = a ∨ P.tgt = a) → b ∉ P.walk.support := by
  obtain ⟨hHw, hHg, hHab, hHadj, hval⟩ := splitOff_facts hNg hab hnadj
  exact avoid_deg_two_core _ hev hg hNg hab hcn ha3 hHw hHg hHab hHadj hval

end degTwo

/-! ### The cases of `DisjL1` for one pair -/

section disj

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {g a b : V}

/-- **DL, leaf case** (`DisjL1` for the single pair `(a, b)`): `a` a leaf at the even vertex. -/
theorem disjL1_leaf (hev : (evenSet G).card ≤ 1) (hg : g ∈ evenSet G)
    (hag : ∀ v, G.Adj a v ↔ v = g) (hb : G.degree b % 2 = 1) (hab : a ≠ b)
    (htw : ¬ UnivTwins G a b) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ TriangleDisj D [(a, b)] := by
  obtain ⟨D, hD, hav⟩ := avoid_leaf G hev hg hag hb hab htw
  refine ⟨D, hD, fun p hp => ?_⟩
  rw [List.mem_singleton] at hp
  subst hp
  exact Or.inl hav

/-- **DL when `d(g) = 2` and `g` is the only common neighbour** (`DisjL1` for the single pair
`(a, b)`). If `N(g) = {a, b}`, `a, b` odd and non-adjacent, `N(a) ∩ N(b) = {g}`, and `a, b` are not
universal twins, some Lovász decomposition satisfies the disjunction. -/
theorem disjL1_deg_two (hev : (evenSet G).card ≤ 1) (hg : g ∈ evenSet G)
    (hNg : ∀ v, G.Adj g v ↔ v = a ∨ v = b) (ha : G.degree a % 2 = 1)
    (hb : G.degree b % 2 = 1) (hab : a ≠ b) (hnadj : ¬ G.Adj a b)
    (hcn : ∀ w, G.Adj a w → G.Adj b w → w = g) (htw : ¬ UnivTwins G a b) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ TriangleDisj D [(a, b)] := by
  classical
  by_cases ha3 : 3 ≤ G.degree a
  · obtain ⟨D, hD, hav⟩ := avoid_deg_two hev hg hNg hab hnadj hcn ha3
    refine ⟨D, hD, fun p hp => ?_⟩
    rw [List.mem_singleton] at hp
    subst hp
    exact Or.inr hav
  · -- `d(a) = 1`: `a` is a leaf at `g`
    have hga : G.Adj g a := (hNg a).mpr (Or.inl rfl)
    have hpos : 0 < G.degree a := (G.degree_pos_iff_exists_adj a).mpr ⟨g, hga.symm⟩
    have hd1 : G.degree a = 1 := by omega
    have hag : ∀ v, G.Adj a v ↔ v = g := by
      intro v
      constructor
      · intro hv
        by_contra hvg
        have hsub : ({v, g} : Finset V) ⊆ G.neighborFinset a := by
          intro w hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rw [mem_neighborFinset]
          rcases hw with rfl | rfl
          · exact hv
          · exact hga.symm
        have := Finset.card_le_card hsub
        rw [card_neighborFinset_eq_degree, hd1, Finset.card_pair hvg] at this
        omega
      · rintro rfl; exact hga.symm
    exact disjL1_leaf hev hg hag hb hab htw

/-- **A target outside `N[b] ∪ {a}` carries `Q(b) ∌ a`** (Lovász's Case I, `csys_caseI`). If
`u ∈ N(g)` is neither `a` nor `b` nor adjacent to `b`, a Lovász decomposition of `G − gu` whose path
ending at `b` avoids `a` gives one of `G` with the same property. -/
theorem avoid_free_target (hev : (evenSet G).card ≤ 1) (hg : g ∈ evenSet G) {u : V}
    (hgu : G.Adj g u) (hua : u ≠ a) (hub : u ≠ b) (hbu : ¬ G.Adj b u) (hbg : b ≠ g)
    (hchild : ∃ D' : PathDecomp (delEdge G g u),
      (∀ v, D'.ends v = (delEdge G g u).degree v % 2) ∧
      ∀ P ∈ D'.paths, (P.src = b ∨ P.tgt = b) → a ∉ P.walk.support) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      ∀ P ∈ D.paths, (P.src = b ∨ P.tgt = b) → a ∉ P.walk.support := by
  obtain ⟨D', hD', hb'⟩ := hchild
  have hgood : CSys.Good G ⟨[(b, {a})], []⟩ := by
    refine csys_caseI G hev hg hgu ⟨[(b, {a})], []⟩ ?_ ?_ ?_
    · rintro w (⟨cA, hcA, rfl⟩ | ⟨pq, hpq, -⟩)
      · rw [List.mem_singleton] at hcA; subst hcA
        exact ⟨Ne.symm hub, hbg, hbu⟩
      · simp at hpq
    · rintro ⟨cA, hcA, hu⟩
      rw [List.mem_singleton] at hcA; subst hcA
      exact hua (Finset.mem_singleton.mp hu)
    · refine ⟨D', hD', fun cA hcA P hP hend x hx => ?_, fun pq hpq => by simp at hpq⟩
      rw [List.mem_singleton] at hcA; subst hcA
      rw [Finset.mem_singleton.mp hx]
      exact hb' P hP hend
  obtain ⟨D, hD, hsat, -⟩ := hgood
  exact ⟨D, hD, fun P hP hend => hsat (b, {a}) (List.mem_singleton_self _) P hP hend a
    (Finset.mem_singleton_self _)⟩

/-- **Free targets carry both orientations** (Lovász's Case I). If `u ∈ N(g)` is neither `a`, `b`
nor adjacent to either, a decomposition of `G − gu` satisfying the disjunction for `(a, b)` gives
one of `G`, with the same disjunct (`avoid_free_target` applied to that disjunct). -/
theorem disjL1_free_target (hev : (evenSet G).card ≤ 1) (hg : g ∈ evenSet G) {u : V}
    (hgu : G.Adj g u) (hua : u ≠ a) (hub : u ≠ b) (hau : ¬ G.Adj a u) (hbu : ¬ G.Adj b u)
    (hag : a ≠ g) (hbg : b ≠ g)
    (hchild : ∃ D' : PathDecomp (delEdge G g u),
      (∀ v, D'.ends v = (delEdge G g u).degree v % 2) ∧ TriangleDisj D' [(a, b)]) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧ TriangleDisj D [(a, b)] := by
  obtain ⟨D', hD', hdisj⟩ := hchild
  rcases hdisj (a, b) (List.mem_singleton_self _) with hb' | ha'
  · obtain ⟨D, hD, h⟩ := avoid_free_target hev hg hgu hua hub hbu hbg ⟨D', hD', hb'⟩
    refine ⟨D, hD, fun p hp => ?_⟩
    rw [List.mem_singleton] at hp; subst hp
    exact Or.inl h
  · obtain ⟨D, hD, h⟩ := avoid_free_target (a := b) (b := a) hev hg hgu hub hua hau hag
      ⟨D', hD', ha'⟩
    refine ⟨D, hD, fun p hp => ?_⟩
    rw [List.mem_singleton] at hp; subst hp
    exact Or.inr h

end disj

/-! ### The exception is needed: universal twins lie on every path -/

section twins

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- If every vertex other than the non-adjacent odd vertices `a, b` is adjacent to both, then every
path of every Lovász decomposition contains both `a` and `b`. (The component form of the exception
in `DisjL1`, for a connected graph; it generalises direct-test1 Proposition 7.5.) -/
theorem univTwins_every_path (hev : (evenSet G).card ≤ 1) {a b : V} (hab : a ≠ b)
    (hnadj : ¬ G.Adj a b) (ha : G.degree a % 2 = 1)
    (htw : ∀ x, x ≠ a → x ≠ b → G.Adj a x ∧ G.Adj b x)
    (D : PathDecomp G) (hD : ∀ v, D.ends v = G.degree v % 2) :
    ∀ P ∈ D.paths, a ∈ P.walk.support ∧ b ∈ P.walk.support := by
  classical
  have hN : ∀ c, (c = a ∨ c = b) → G.neighborFinset c = (Finset.univ.erase a).erase b := by
    intro c hc
    ext x
    simp only [mem_neighborFinset, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro h
      refine ⟨fun hxb => ?_, fun hxa => ?_⟩
      · subst hxb
        rcases hc with rfl | rfl
        · exact hnadj h
        · exact G.loopless.irrefl _ h
      · subst hxa
        rcases hc with rfl | rfl
        · exact G.loopless.irrefl _ h
        · exact hnadj h.symm
    · rintro ⟨hxb, hxa⟩
      rcases hc with rfl | rfl
      · exact (htw x hxa hxb).1
      · exact (htw x hxa hxb).2
  have hdeg : ∀ c, (c = a ∨ c = b) → G.degree c = Fintype.card V - 2 := by
    intro c hc
    rw [← card_neighborFinset_eq_degree, hN c hc, Finset.card_erase_of_mem (by simp [Ne.symm hab]),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  have hda := hdeg a (Or.inl rfl)
  have hdb := hdeg b (Or.inr rfl)
  have hcard : 3 ≤ Fintype.card V := by
    have : 0 < G.degree a := by omega
    omega
  -- every vertex has positive degree
  have hpos : ∀ v, 0 < G.degree v := by
    intro v
    by_cases hva : v = a
    · subst hva; omega
    · by_cases hvb : v = b
      · subst hvb; omega
      · exact (G.degree_pos_iff_exists_adj v).mpr ⟨a, (htw v hva hvb).1.symm⟩
  -- the number of paths: `2 |D| = n − |evenSet| = n − 1`
  have hsum : ∑ v, G.degree v % 2 = Fintype.card V - (evenSet G).card := by
    have h1 : ∀ v, G.degree v % 2 + (if v ∈ evenSet G then 1 else 0) = 1 := by
      intro v
      by_cases hv : v ∈ evenSet G
      · rw [if_pos hv]
        obtain ⟨k, hk⟩ := (mem_evenSet_iff_even.mp hv).2
        omega
      · rw [if_neg hv]
        have : ¬ Even (G.degree v) := fun he => hv (mem_evenSet_iff_even.mpr ⟨hpos v, he⟩)
        have := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp this)
        omega
    have h2 : ∑ v, (G.degree v % 2 + if v ∈ evenSet G then 1 else 0) = Fintype.card V := by
      rw [Finset.sum_congr rfl (fun v _ => h1 v)]
      simp
    have h3 : ∑ v, (if v ∈ evenSet G then 1 else 0 : ℕ) = (evenSet G).card := by
      rw [Finset.sum_boole]
      simp
    rw [Finset.sum_add_distrib, h3] at h2
    omega
  have hsz : 2 * D.size = Fintype.card V - (evenSet G).card := by
    rw [← D.sum_ends, ← hsum]
    exact Finset.sum_congr rfl (fun v _ => hD v)
  have hnodd : (Fintype.card V) % 2 = 1 := by omega
  have hsz' : 2 * D.size = Fintype.card V - 1 := by
    have : (evenSet G).card = 0 ∨ (evenSet G).card = 1 := by omega
    rcases this with h | h
    · rw [h] at hsz; omega
    · rw [h] at hsz; exact hsz
  -- every path contains `c` for `c ∈ {a, b}`
  have hall : ∀ c, (c = a ∨ c = b) → ∀ P ∈ D.paths, c ∈ P.walk.support := by
    intro c hc
    have hc1 : D.ends c = 1 := by rw [hD, hdeg c hc]; omega
    have hdsum := D.degree_eq_sum c
    have hes : (D.paths.map (fun P => P.endsAt c)).sum = 1 := hc1
    have htot : (D.paths.map (fun P => P.incid c + P.endsAt c)).sum = 2 * D.size := by
      have : (D.paths.map (fun P => P.incid c + P.endsAt c)).sum =
          (D.paths.map (fun P => P.incid c)).sum + (D.paths.map (fun P => P.endsAt c)).sum := by
        induction D.paths with
        | nil => simp
        | cons P l ih => simp only [List.map_cons, List.sum_cons, ih]; omega
      rw [this, ← hdsum, hes, hdeg c hc, hsz']
      omega
    intro P hP
    by_contra hcP
    have hle : ∀ Q ∈ D.paths, Q.incid c + Q.endsAt c ≤ 2 := by
      intro Q _
      have := Q.incid_add_endsAt c
      split_ifs at this <;> omega
    have hP0 : P.incid c + P.endsAt c = 0 := by
      have := P.incid_add_endsAt c
      rw [if_neg hcP] at this
      omega
    have hperm := List.perm_cons_erase hP
    rw [(hperm.map _).sum_eq, List.map_cons, List.sum_cons, hP0, zero_add] at htot
    have hbound : ((D.paths.erase P).map (fun Q => Q.incid c + Q.endsAt c)).sum ≤
        2 * (D.paths.erase P).length := by
      have := List.sum_le_length_nsmul ((D.paths.erase P).map (fun Q => Q.incid c + Q.endsAt c)) 2
        (fun x hx => by
          obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hx
          exact hle Q (List.mem_of_mem_erase hQ))
      simpa [mul_comm] using this
    have hlen : (D.paths.erase P).length + 1 = D.size := by
      rw [List.length_erase_of_mem hP, PathDecomp.size]
      have : 0 < D.paths.length := List.length_pos_of_mem hP
      omega
    omega
  exact fun P hP => ⟨hall a (Or.inl rfl) P hP, hall b (Or.inr rfl) P hP⟩

/-- Hence the disjunction fails for universal twins of a connected graph. -/
theorem not_triangleDisj_of_twins (hev : (evenSet G).card ≤ 1) {a b : V} (hab : a ≠ b)
    (hnadj : ¬ G.Adj a b) (ha : G.degree a % 2 = 1)
    (htw : ∀ x, x ≠ a → x ≠ b → G.Adj a x ∧ G.Adj b x)
    (D : PathDecomp G) (hD : ∀ v, D.ends v = G.degree v % 2) : ¬ TriangleDisj D [(a, b)] := by
  intro h
  have hall := univTwins_every_path hev hab hnadj ha htw D hD
  have hb1 : 0 < D.ends b := by
    rw [hD]
    have : G.degree b = G.degree a := by
      rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
      congr 1
      ext x
      simp only [mem_neighborFinset]
      by_cases hxa : x = a
      · subst hxa; exact ⟨fun h' => absurd h'.symm hnadj, fun h' => absurd h' (G.loopless.irrefl _)⟩
      · by_cases hxb : x = b
        · subst hxb; exact ⟨fun h' => absurd h' (G.loopless.irrefl _), fun h' => absurd h' hnadj⟩
        · exact ⟨fun _ => (htw x hxa hxb).1, fun _ => (htw x hxa hxb).2⟩
    omega
  have ha1 : 0 < D.ends a := by rw [hD]; omega
  obtain ⟨Pb, hPb, hPbe⟩ := D.exists_end_of_pos hb1
  obtain ⟨Pa, hPa, hPae⟩ := D.exists_end_of_pos ha1
  rcases h (a, b) (List.mem_singleton_self _) with h1 | h1
  · exact h1 Pb hPb hPbe (hall Pb hPb).1
  · exact h1 Pa hPa hPae (hall Pa hPa).2

end twins

end Gallai
