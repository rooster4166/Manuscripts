import GallaiLean.MultiToken
import GallaiLean.ConjNFar

/-!
# Pre-committed end paths: Lemma R and Criterion R (session `claude/conj-r`)

Manuscript `manuscripts/conj-r`, Section 3 (Lemma R, Definition 3.3, Proposition 3.4; in `manuscripts/ln` these are Lemma 6.1, Definition 6.2 and Proposition 6.3).

Let `G` have no vertex of positive even degree, and let `(cᵢ, aᵢ)`, `(cⱼ, aⱼ)` be two pairs.
Fix a path `P` from `cᵢ` avoiding `aᵢ`, and let `K₀ = G − E(P)` (`delEdgeList G P.edges`).

* **`PathDecomp.add_path_full`**: adding a path to a decomposition of the graph without its edges;
  every path of the result is `P` or a path of the old decomposition (same ends and support).
* **`delEdgeList_degree_mod`**: `d_{K₀}(v) ≡ d_G(v) + [v is an end of P] (mod 2)`.
* **`lemmaR`** (Lemma R): a decomposition `D₀` of `K₀` with at most one end at every vertex, whose
  paths ending at `cⱼ` avoid `aⱼ`, together with `P` (which must avoid `aⱼ` if it ends at `cⱼ`),
  is a Lovász decomposition of `G` whose path ending at `cᵢ` is `P` and whose paths ending at `cᵢ`,
  `cⱼ` avoid `aᵢ`, `aⱼ`. Case (a) of the manuscript is `P.tgt = cⱼ` (no condition on `D₀`, since
  `cⱼ` has no end in `D₀`); case (b) is `P.tgt ≠ cⱼ`.
* **`lemmaR_leaf`** (Lemma R(b) with a new leaf): a parity decomposition of `K₀ + cⱼℓ` in which no
  path contains both `ℓ` and `aⱼ` gives the decomposition.
* **`CriterionR`** (conj-r Definition 3.3 = ln Definition 6.2) and **`ln2_of_criterionR`** (conj-r Proposition 3.4 = ln Proposition 6.3): a
  multi-token schedule for `K₀` (case (a)), for `K₀ + cⱼℓ` with the tail `(ℓ, cⱼ, aⱼ)`, or for `K₀`
  with the tail `(cⱼ, w, aⱼ)` when `cⱼ` is a leaf of `K₀` at `w`, gives `L_N(2)` for the instance.
* **`LN2`**, **`ConjR`**, **`ln2_of_conjR`**: Conjecture R implies `L_N(2)`.
-/

open SimpleGraph

namespace Gallai

universe u

section addPath

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Adding a path**, with the full correspondence of paths: every path of the result has the
ends and the support of `P` or of a path of `D`. -/
theorem PathDecomp.add_path_full {G K : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel K.Adj]
    (P : GPath G) (hK : ∀ e, e ∈ K.edgeSet ↔ e ∈ G.edgeSet ∧ e ∉ P.edges) (D : PathDecomp K) :
    ∃ D' : PathDecomp G, (∀ v, D'.ends v = P.endsAt v + D.ends v) ∧
      ∀ Q ∈ D'.paths, (Q.src = P.src ∧ Q.tgt = P.tgt ∧ Q.walk.support = P.walk.support) ∨
        ∃ R ∈ D.paths, Q.src = R.src ∧ Q.tgt = R.tgt ∧ Q.walk.support = R.walk.support := by
  classical
  set L := P.toTop :: D.paths.map GPath.toTop with hL
  have hPnd : P.edges.Nodup := P.isPath.edges_nodup
  have hPG : ∀ e ∈ P.edges, e ∈ G.edgeSet := fun e he => P.walk.edges_subset_edgeSet he
  have hEL : edgesM L = G.edgeFinset.val := by
    rw [hL, edgesM_cons, D.edgesM_toTop, GPath.toTop_edges]
    refine (Multiset.Nodup.ext ?_ (Finset.nodup _)).mpr fun e => ?_
    · rw [Multiset.nodup_add]
      refine ⟨Multiset.coe_nodup.mpr hPnd, Finset.nodup _, Multiset.disjoint_left.mpr ?_⟩
      intro e h1 h2
      rw [Finset.mem_val, mem_edgeFinset, hK] at h2
      exact h2.2 (Multiset.mem_coe.mp h1)
    · rw [Multiset.mem_add, Finset.mem_val, Finset.mem_val, mem_edgeFinset, mem_edgeFinset, hK,
        Multiset.mem_coe]
      constructor
      · rintro (h | h)
        · exact hPG e h
        · exact h.1
      · intro h
        by_cases hp : e ∈ P.edges
        · exact Or.inl hp
        · exact Or.inr ⟨h, hp⟩
  obtain ⟨D', hD', hall⟩ := exists_decomp_of_edgesM' L hEL
  refine ⟨D', fun v => ?_, fun Q hQ => ?_⟩
  · rw [hD' v, hL, endsL_cons, D.endsL_toTop, GPath.toTop_endsAt]
  · obtain ⟨R, hR, h1, h2, h3⟩ := hall Q hQ
    rw [hL, List.mem_cons] at hR
    rcases hR with rfl | hR
    · exact Or.inl ⟨h1, h2, by rw [h3, GPath.toTop_support]⟩
    · obtain ⟨R', hR', rfl⟩ := List.mem_map.mp hR
      exact Or.inr ⟨R', hR', h1, h2, by rw [h3, GPath.toTop_support]⟩

/-- **Degrees after removing a path**: `d_{G − E(P)}(v) ≡ d_G(v) + [v is an end of P]`. -/
theorem delEdgeList_degree_mod (G : SimpleGraph V) [DecidableRel G.Adj] (P : GPath G) (v : V) :
    (delEdgeList G P.edges).degree v % 2 = (G.degree v + P.endsAt v) % 2 := by
  classical
  obtain ⟨D⟩ := PathDecomp.nonempty (delEdgeList G P.edges)
  obtain ⟨D', hD', -⟩ := PathDecomp.add_path_full P
    (fun e => delEdgeList_edgeSet G P.edges e) D
  have h1 := D.ends_mod_two v
  have h2 := D'.ends_mod_two v
  rw [hD' v] at h2
  omega

end addPath

/-! ### Lemma R -/

section lemmaR

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Lemma R** (pre-committed end path). Let `G` have no vertex of positive even degree, `P` a
path of `G` from `cᵢ` avoiding `aᵢ`, and `D₀` a decomposition of `K₀ = G − E(P)` with at most one
end at every vertex whose paths ending at `cⱼ` avoid `aⱼ`. If `P` ends at `cⱼ`, suppose it avoids
`aⱼ`. Then `D₀ ∪ {P}` is a Lovász decomposition of `G` whose paths ending at `cᵢ` and at `cⱼ` avoid
`aᵢ` and `aⱼ`. -/
theorem lemmaR (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnoev : ∀ v, 0 < G.degree v → G.degree v % 2 = 1)
    {ci ai cj aj : V} (P : GPath G) (hPs : P.src = ci) (hai : ai ∉ P.walk.support)
    (hcij : ci ≠ cj)
    (D₀ : PathDecomp (delEdgeList G P.edges)) (hD₀ : ∀ v, D₀.ends v ≤ 1)
    (hPj : P.tgt = cj → aj ∉ P.walk.support)
    (hD₀j : P.tgt ≠ cj → ∀ Q ∈ D₀.paths, (Q.src = cj ∨ Q.tgt = cj) → aj ∉ Q.walk.support) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      (∀ Q ∈ D.paths, (Q.src = ci ∨ Q.tgt = ci) → ai ∉ Q.walk.support) ∧
      (∀ Q ∈ D.paths, (Q.src = cj ∨ Q.tgt = cj) → aj ∉ Q.walk.support) := by
  classical
  obtain ⟨D, hD, hcor⟩ := PathDecomp.add_path_full P
    (fun e => delEdgeList_edgeSet G P.edges e) D₀
  -- at an end of `P`, `D₀` has no end
  have hend0 : ∀ v, (P.src = v ∨ P.tgt = v) → D₀.ends v = 0 := by
    intro v hv
    have hmem : v ∈ P.walk.support := by
      rcases hv with rfl | rfl
      · exact P.walk.start_mem_support
      · exact P.walk.end_mem_support
    have hodd := hnoev v (P.degree_pos_of_mem hmem)
    have hPe : P.endsAt v = 1 := by
      have := P.incid_add_endsAt v
      simp only [P.incid_of_end hv, hmem, ite_true] at this
      omega
    have h2 := D.ends_mod_two v
    rw [hD v, hPe, hodd] at h2
    have := hD₀ v
    omega
  have hzero : ∀ v, D₀.ends v = 0 → ∀ R ∈ D₀.paths, ¬ (R.src = v ∨ R.tgt = v) := by
    intro v h0 R hR hRv
    have h1 : 1 ≤ R.endsAt v := by
      unfold GPath.endsAt
      rcases hRv with h | h <;> simp [h]
    have hle : R.endsAt v ≤ D₀.ends v := by
      unfold PathDecomp.ends
      exact List.le_sum_of_mem (List.mem_map_of_mem hR)
    omega
  refine ⟨D, fun v => ?_, fun Q hQ hQc => ?_, fun Q hQ hQc => ?_⟩
  · have h2 := D.ends_mod_two v
    by_cases hv : P.src = v ∨ P.tgt = v
    · have hmem : v ∈ P.walk.support := by
        rcases hv with rfl | rfl
        · exact P.walk.start_mem_support
        · exact P.walk.end_mem_support
      have hPe : P.endsAt v = 1 := by
        have := P.incid_add_endsAt v
        simp only [P.incid_of_end hv, hmem, ite_true] at this
        omega
      rw [hD v, hPe, hend0 v hv]
      rw [hD v, hPe, hend0 v hv] at h2
      omega
    · have hPe : P.endsAt v = 0 := by
        push Not at hv
        simp [GPath.endsAt, hv.1, hv.2]
      rw [hD v, hPe, zero_add]
      rw [hD v, hPe, zero_add] at h2
      have := hD₀ v
      omega
  · rcases hcor Q hQ with ⟨-, -, hsupp⟩ | ⟨R, hR, h1, h2, -⟩
    · rw [hsupp]; exact hai
    · exact absurd (by rw [← h1, ← h2]; exact hQc) (hzero ci (hend0 ci (Or.inl hPs)) R hR)
  · rcases hcor Q hQ with ⟨h1, h2, hsupp⟩ | ⟨R, hR, h1, h2, hsupp⟩
    · rw [hsupp]
      apply hPj
      rcases hQc with h | h
      · exact absurd (hPs.symm.trans (h1.symm.trans h)) hcij
      · rw [← h2, h]
    · rw [hsupp]
      have hRc : R.src = cj ∨ R.tgt = cj := by rw [← h1, ← h2]; exact hQc
      by_cases hPt : P.tgt = cj
      · exact absurd hRc (hzero cj (hend0 cj (Or.inr hPt)) R hR)
      · exact hD₀j hPt R hR hRc

/-- **Lemma R(b) with a new leaf.** If `P` does not end at `cⱼ` and `K₀ + cⱼℓ` has a parity
decomposition in which no path contains both `ℓ` and `aⱼ`, the conclusion of `lemmaR` holds. -/
theorem lemmaR_leaf (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnoev : ∀ v, 0 < G.degree v → G.degree v % 2 = 1)
    {ci ai cj aj : V} (P : GPath G) (hPs : P.src = ci) (hai : ai ∉ P.walk.support)
    (hcij : ci ≠ cj) (hPt : P.tgt ≠ cj) (hcj : G.degree cj % 2 = 1)
    (DH : PathDecomp (apex (delEdgeList G P.edges) {cj}))
    (hDH : ∀ v, DH.ends v = (apex (delEdgeList G P.edges) {cj}).degree v % 2)
    (hsep : ∀ Q ∈ DH.paths, (none : Option V) ∈ Q.walk.support → some aj ∉ Q.walk.support) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      (∀ Q ∈ D.paths, (Q.src = ci ∨ Q.tgt = ci) → ai ∉ Q.walk.support) ∧
      (∀ Q ∈ D.paths, (Q.src = cj ∨ Q.tgt = cj) → aj ∉ Q.walk.support) := by
  classical
  have hPe : P.endsAt cj = 0 := by
    simp [GPath.endsAt, hPs, hcij, hPt]
  have hK₀ : (delEdgeList G P.edges).degree cj % 2 = 1 := by
    rw [delEdgeList_degree_mod, hPe, add_zero, hcj]
  obtain ⟨D₀, hD₀, hav⟩ := avoid_of_apexSep (delEdgeList G P.edges) hK₀ DH
    (fun w hw => by rw [hDH, apex_degree_some]; simp [hw])
    (by rw [hDH, apex_degree_some]; simp only [Finset.mem_singleton, ite_true]; omega)
    (A := {aj}) (fun Q hQ hn a ha => by
      rw [Finset.mem_singleton] at ha; subst ha; exact hsep Q hQ hn)
  refine lemmaR G hnoev P hPs hai hcij D₀ (fun v => by rw [hD₀ v]; omega)
    (fun h => absurd h hPt) (fun _ Q hQ hQc => hav Q hQ hQc aj (Finset.mem_singleton_self _))

end lemmaR

/-! ### Criterion R and Proposition 6.3 -/

section criterion

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Criterion R for an ordered choice and a path** (conj-r Definition 3.3 = ln Definition 6.2). `P` starts at `cᵢ`
and avoids `aᵢ`; with `K₀ = G − E(P)`, one of:
* (a) `P` ends at `cⱼ`, avoids `aⱼ`, and `(K₀, ∅)` has a multi-token schedule;
* (b) `P` ends outside `{cⱼ, aⱼ}`, and `(K₀ + cⱼℓ, {(ℓ, cⱼ, aⱼ)})` has a schedule (`ℓ = none`);
* (b') `P` ends outside `{cⱼ, aⱼ}`, `cⱼ` is a leaf of `K₀` at `w` with `aⱼ ∉ {w} ∪ N_{K₀}(w)`,
  and `(K₀, {(cⱼ, w, aⱼ)})` has a schedule. -/
def CritRPath (G : SimpleGraph V) [DecidableRel G.Adj] (ci ai cj aj : V) (P : GPath G) : Prop :=
  P.src = ci ∧ ai ∉ P.walk.support ∧
  ((P.tgt = cj ∧ aj ∉ P.walk.support ∧
      SteerK (∅ : Finset (V × V × V)) (delEdgeList G P.edges)
        (evenSet (delEdgeList G P.edges))) ∨
   (P.tgt ≠ cj ∧ P.tgt ≠ aj ∧
      SteerK ({((none : Option V), some cj, some aj)} : Finset (Option V × Option V × Option V))
        (apex (delEdgeList G P.edges) {cj}) (evenSet (apex (delEdgeList G P.edges) {cj}))) ∨
   (P.tgt ≠ cj ∧ P.tgt ≠ aj ∧ ∃ w, (∀ v, (delEdgeList G P.edges).Adj cj v ↔ v = w) ∧ aj ≠ w ∧
      ¬ (delEdgeList G P.edges).Adj aj w ∧
      SteerK ({(cj, w, aj)} : Finset (V × V × V)) (delEdgeList G P.edges)
        (evenSet (delEdgeList G P.edges))))

/-- **Criterion R** for the instance `(G; c₁, a₁; c₂, a₂)`: some orientation and some path. -/
def CriterionR (G : SimpleGraph V) [DecidableRel G.Adj] (c₁ a₁ c₂ a₂ : V) : Prop :=
  (∃ P : GPath G, CritRPath G c₁ a₁ c₂ a₂ P) ∨ (∃ P : GPath G, CritRPath G c₂ a₂ c₁ a₁ P)

/-- The conclusion of `L_N(2)` for the instance. -/
def LN2Good (G : SimpleGraph V) [DecidableRel G.Adj] (c₁ a₁ c₂ a₂ : V) : Prop :=
  ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
    (∀ Q ∈ D.paths, (Q.src = c₁ ∨ Q.tgt = c₁) → a₁ ∉ Q.walk.support) ∧
    (∀ Q ∈ D.paths, (Q.src = c₂ ∨ Q.tgt = c₂) → a₂ ∉ Q.walk.support)

/-- One oriented case of Proposition 6.3. -/
theorem ln2_of_critRPath (G : SimpleGraph V) [DecidableRel G.Adj]
    (hodd : ∀ v, G.degree v % 2 = 1) {ci ai cj aj : V}
    (hcij : ci ≠ cj) (hajci : aj ≠ ci) (hajcj : aj ≠ cj) (hadj : ¬ G.Adj cj aj)
    (P : GPath G) (hR : CritRPath G ci ai cj aj P) :
    ∃ D : PathDecomp G, (∀ v, D.ends v = G.degree v % 2) ∧
      (∀ Q ∈ D.paths, (Q.src = ci ∨ Q.tgt = ci) → ai ∉ Q.walk.support) ∧
      (∀ Q ∈ D.paths, (Q.src = cj ∨ Q.tgt = cj) → aj ∉ Q.walk.support) := by
  classical
  obtain ⟨hPs, hai, hcase⟩ := hR
  have hnoev : ∀ v, 0 < G.degree v → G.degree v % 2 = 1 := fun v _ => hodd v
  -- `aⱼ` is not an end of `P` once `P.tgt ≠ aⱼ`, so it stays odd in `K₀`
  have hajodd : P.tgt ≠ aj → (delEdgeList G P.edges).degree aj % 2 = 1 := by
    intro ht
    rw [delEdgeList_degree_mod]
    have : P.endsAt aj = 0 := by
      simp [GPath.endsAt, hPs, Ne.symm hajci, ht]
    rw [this, add_zero, hodd]
  have hnadjK : ∀ x y, ¬ G.Adj x y → ¬ (delEdgeList G P.edges).Adj x y := fun x y h hK => h hK.1
  rcases hcase with ⟨hPt, hajP, hS⟩ | ⟨hPt, hPa, hS⟩ | ⟨hPt, hPa, w, hcw, hajw, hnaw, hS⟩
  · -- (a)
    have hsys : TailSys (∅ : Finset (V × V × V)) :=
      ⟨fun t ht => absurd ht (Finset.notMem_empty t), fun t ht => absurd ht (Finset.notMem_empty t),
        fun t ht => absurd ht (Finset.notMem_empty t)⟩
    obtain ⟨D₀, hD₀, -⟩ := steerK_good hsys hS rfl
      (fun t ht => absurd ht (Finset.notMem_empty t))
    exact lemmaR G hnoev P hPs hai hcij D₀ (fun v => by rw [hD₀ v]; omega) (fun _ => hajP)
      (fun h => absurd hPt h)
  · -- (b), a new leaf `ℓ = none` at `cⱼ`
    have hsys : TailSys ({((none : Option V), some cj, some aj)} :
        Finset (Option V × Option V × Option V)) := by
      refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht t' ht' hne => ?_⟩
      · rw [Finset.mem_singleton] at ht; subst ht; simp
      · rw [Finset.mem_singleton] at ht; subst ht; simpa using hajcj
      · rw [Finset.mem_singleton] at ht ht'; exact absurd (ht.trans ht'.symm) hne
    have hinv : TailInv ({((none : Option V), some cj, some aj)} :
        Finset (Option V × Option V × Option V)) (apex (delEdgeList G P.edges) {cj}) := by
      intro t ht _
      rw [Finset.mem_singleton] at ht; subst ht
      refine ⟨fun v => ?_, ?_, ?_⟩
      · cases v with
        | none => simp
        | some v => simp [apex_adj_none_some, eq_comm]
      · rw [apex_degree_some]
        simp only [Finset.mem_singleton, hajcj, ite_false, add_zero]
        exact hajodd hPa
      · rw [apex_adj_some_some]
        exact hnadjK aj cj (fun h => hadj h.symm)
    obtain ⟨DH, hDH, hmeet⟩ := steerK_good hsys hS rfl hinv
    have hlive : (apex (delEdgeList G P.edges) {cj}).Adj (none : Option V) (some cj) := by
      rw [apex_adj_none_some]; exact Finset.mem_singleton_self _
    have hm := hmeet _ (Finset.mem_singleton_self _) hlive
    exact lemmaR_leaf G hnoev P hPs hai hcij hPt (hodd cj) DH hDH (fun Q hQ hn hs => by
      have := hm Q hQ none (by simp) (some aj) (by simp) hn hs
      cases this)
  · -- (b'), `cⱼ` is a leaf of `K₀`
    have hsys : TailSys ({(cj, w, aj)} : Finset (V × V × V)) := by
      refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht t' ht' hne => ?_⟩
      · rw [Finset.mem_singleton] at ht; subst ht; exact hajcj
      · rw [Finset.mem_singleton] at ht; subst ht; exact hajw
      · rw [Finset.mem_singleton] at ht ht'; exact absurd (ht.trans ht'.symm) hne
    have hinv : TailInv ({(cj, w, aj)} : Finset (V × V × V)) (delEdgeList G P.edges) := by
      intro t ht _
      rw [Finset.mem_singleton] at ht; subst ht
      exact ⟨hcw, hajodd hPa, hnaw⟩
    obtain ⟨D₀, hD₀, hmeet⟩ := steerK_good hsys hS rfl hinv
    have hlive : (delEdgeList G P.edges).Adj cj w := (hcw w).mpr rfl
    have hm := hmeet _ (Finset.mem_singleton_self _) hlive
    refine lemmaR G hnoev P hPs hai hcij D₀ (fun v => by rw [hD₀ v]; omega)
      (fun h => absurd h hPt) (fun _ Q hQ hQc haQ => ?_)
    have hcQ : cj ∈ Q.walk.support := by
      rcases hQc with h | h
      · rw [← h]; exact Q.walk.start_mem_support
      · rw [← h]; exact Q.walk.end_mem_support
    exact hajcj (hm Q hQ aj (by simp) cj (by simp) haQ hcQ)

/-- **Proposition 6.3.** An instance of `L_N(2)` (all degrees odd, `c₁, a₁, c₂, a₂` distinct,
`cᵢ ≁ aᵢ`) that satisfies Criterion R satisfies `L_N(2)`. -/
theorem ln2_of_criterionR (G : SimpleGraph V) [DecidableRel G.Adj]
    (hodd : ∀ v, G.degree v % 2 = 1) {c₁ a₁ c₂ a₂ : V}
    (hd : [c₁, a₁, c₂, a₂].Nodup) (h₁ : ¬ G.Adj c₁ a₁) (h₂ : ¬ G.Adj c₂ a₂)
    (hR : CriterionR G c₁ a₁ c₂ a₂) : LN2Good G c₁ a₁ c₂ a₂ := by
  have hc₁c₂ : c₁ ≠ c₂ := fun h => by simp [h] at hd
  have hc₁a₂ : c₁ ≠ a₂ := fun h => by simp [h] at hd
  have hc₂a₂ : c₂ ≠ a₂ := fun h => by simp [h] at hd
  have ha₁c₂ : a₁ ≠ c₂ := fun h => by simp [h] at hd
  have hc₁a₁ : c₁ ≠ a₁ := fun h => by simp [h] at hd
  rcases hR with ⟨P, hP⟩ | ⟨P, hP⟩
  · exact ln2_of_critRPath G hodd hc₁c₂ (Ne.symm hc₁a₂) (Ne.symm hc₂a₂) h₂ P hP
  · obtain ⟨D, hD, h2, h1⟩ :=
      ln2_of_critRPath G hodd (Ne.symm hc₁c₂) ha₁c₂ (Ne.symm hc₁a₁) h₁ P hP
    exact ⟨D, hD, h1, h2⟩

end criterion

/-! ### Conjecture R implies `L_N(2)` -/

/-- **`L_N(2)`**: in a graph with all degrees odd, two disjoint non-adjacent pairs can be avoided at
once. -/
def LN2 : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, G.degree v % 2 = 1) → ∀ c₁ a₁ c₂ a₂ : V, [c₁, a₁, c₂, a₂].Nodup →
      ¬ G.Adj c₁ a₁ → ¬ G.Adj c₂ a₂ → LN2Good G c₁ a₁ c₂ a₂

/-- **Conjecture R**: every instance of `L_N(2)` satisfies Criterion R. -/
def ConjR : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, G.degree v % 2 = 1) → ∀ c₁ a₁ c₂ a₂ : V, [c₁, a₁, c₂, a₂].Nodup →
      ¬ G.Adj c₁ a₁ → ¬ G.Adj c₂ a₂ → CriterionR G c₁ a₁ c₂ a₂

/-- **Conjecture R implies `L_N(2)`** (Lemma R, Proposition 6.3 and the transfer theorem). -/
theorem ln2_of_conjR (h : ConjR.{u}) : LN2.{u} := by
  intro V _ _ G _ hodd c₁ a₁ c₂ a₂ hd h₁ h₂
  exact ln2_of_criterionR G hodd hd h₁ h₂ (h V G hodd c₁ a₁ c₂ a₂ hd h₁ h₂)

end Gallai
