import GallaiLean.SeparatorOdd

/-!
# Theorem 113, even component, both ports even in `A`

`|C| = 2s`, every vertex of `C` odd in `B`, and `d_A(x)`, `d_A(y)` both even. The exterior graph
is `W = E` itself on `U = V ∖ C`; the whole work is the lift of a decomposition `D_E` of `E` to one
of `B` with `s` more paths and the same ends outside `C`. Let `R₀ ∈ D_E` pass through `x`.

* `y ∉ R₀` (`case1_lift`): a decomposition `D^x` of `A` with `s + 1` paths, two ends at `x` and
  none at `y` (Lovász on `A` plus a private leaf at `x`, `exists_localX`) is grafted at `x` into
  `R₀`.
* `y ∈ R₀` (`case2_lift`): orient `R₀ = q₁ · m · q₃` (`x` then `y`). Let `w₀ ∉ C ∪ {x, y}` and
  `A' = A + x w₀ + w₀ y`; Lovász (tight) on `C ∪ {x, y, w₀}` gives `s + 1` paths with one end at
  each of `x`, `y`, `c ∈ C` (`exists_localA'`). The path through `w₀` reads
  `R_x · (x w₀ y) · R_y` (`exists_split_at_mid`). If `R_x` is nontrivial, graft `R_x` and the
  other `x`-ended path at `x` into `R₀` (`exists_graft_x` keeps the explicit piece
  `R_x · m · q₃`); then, if `R_y` is nontrivial, graft `R_y` and the remaining `y`-ended path at
  `y` into the path carrying `y`. The four sub-cases of the manuscript (`R_x`, `R_y` trivial or
  not; for both nontrivial, the `x`- and `y`-ended paths equal or not) are these two optional
  grafts.

In all cases the edges are `E + A = B`, the size is `|D_E| + s` and the ends outside `C` are those
of `D_E`; `rootedAt_of_lift` concludes (`rootedAt_evenComp_evenPorts`).
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u}

/-! ### Lists of paths -/

section lists

variable [DecidableEq V]

omit [DecidableEq V] in
theorem edgesM_perm {L L' : List (TPath V)} (h : L.Perm L') : edgesM L = edgesM L' := by
  unfold edgesM
  exact Multiset.coe_eq_coe.mpr (h.flatMap_right _)

theorem endsL_perm {L L' : List (TPath V)} (h : L.Perm L') (v : V) : endsL L v = endsL L' v := by
  unfold endsL
  exact (h.map _).sum_eq

/-- A list with an end at `v` has a member with exactly one end at `v`. -/
theorem exists_endsL_one : ∀ (L : List (TPath V)) {v : V}, 1 ≤ endsL L v →
    ∃ X rest, L.Perm (X :: rest) ∧ X.endsAt v = 1
  | [], v, h => by simp at h
  | P :: L, v, h => by
    by_cases hP : P.endsAt v = 1
    · exact ⟨P, L, List.Perm.refl _, hP⟩
    · have h0 : P.endsAt v = 0 := by have := P.endsAt_le_one v; omega
      rw [endsL_cons, h0, zero_add] at h
      obtain ⟨X, rest, h1, h2⟩ := exists_endsL_one L h
      exact ⟨X, P :: rest, (h1.cons P).trans (List.Perm.swap X P rest), h2⟩

theorem endsL_eq_zero_of_notMem {L : List (TPath V)} {S : Finset V}
    (hL : ∀ P ∈ L, ∀ w ∈ P.walk.support, w ∈ S) {v : V} (hv : v ∉ S) : endsL L v = 0 := by
  unfold endsL
  refine List.sum_eq_zero_iff_forall_eq_nat.mpr (fun n hn => ?_)
  obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hn
  have h1 : P.src ≠ v := fun h => hv (h ▸ hL P hP _ P.walk.start_mem_support)
  have h2 : P.tgt ≠ v := fun h => hv (h ▸ hL P hP _ P.walk.end_mem_support)
  simp [GPath.endsAt, h1, h2]

end lists

/-! ### Path surgery -/

section surgery

variable [DecidableEq V]

/-- **Graft at `p`, keeping the second piece explicit.** `R = q₁ · m · q₃` with `q₁` ending at
`p`; attach `X₁` (from `p`) after `q₁` and the reverse of `X₂` (from `p`) before `m · q₃`. The
second new path is `X₂⁻¹ · m · q₃`, split again at the end `y` of `m`. -/
theorem exists_graft_x (R X₁ X₂ : TPath V) {p y : V} (q₁ : (⊤ : SimpleGraph V).Walk R.src p)
    (m : (⊤ : SimpleGraph V).Walk p y) (q₃ : (⊤ : SimpleGraph V).Walk y R.tgt)
    (hR : R.walk = q₁.append (m.append q₃)) (h1 : X₁.src = p) (h2 : X₂.src = p)
    (hd1 : ∀ w ∈ X₁.walk.support, w ∈ q₁.support → w = p)
    (hd2 : ∀ w ∈ X₂.walk.support, w ∈ (m.append q₃).support → w = p) :
    ∃ N₁ N₂ : TPath V,
      (N₁.edges : Multiset (Sym2 V)) + N₂.edges = R.edges + X₁.edges + X₂.edges ∧
      (∀ v, N₁.endsAt v + N₂.endsAt v + 2 * (if p = v then 1 else 0) =
        R.endsAt v + X₁.endsAt v + X₂.endsAt v) ∧
      (∀ w ∈ N₁.walk.support, w ∈ q₁.support ∨ w ∈ X₁.walk.support) ∧
      N₂.src = X₂.tgt ∧ N₂.tgt = R.tgt ∧
      ∃ (u : (⊤ : SimpleGraph V).Walk N₂.src y) (q₃' : (⊤ : SimpleGraph V).Walk y N₂.tgt),
        N₂.walk = u.append q₃' ∧ (∀ w ∈ u.support, w ∈ X₂.walk.support ∨ w ∈ m.support) ∧
        ∀ w ∈ q₃'.support, w ∈ q₃.support := by
  have hRn := R.support_nodup
  rw [hR] at hRn
  have hq₁ := support_nodup_of_append_left hRn
  have hq₂ := support_nodup_of_append_right hRn
  let X₁w := X₁.walk.copy h1 rfl
  let X₂w := (X₂.walk.copy h2 rfl).reverse
  have hX₁ : X₁w.support.Nodup := by simpa [X₁w] using X₁.support_nodup
  have hX₂ : X₂w.support.Nodup := by simpa [X₂w] using X₂.support_nodup
  let N₁ := joinT q₁ X₁w hq₁ hX₁ (fun w hw hw' => hd1 w (by simpa [X₁w] using hw') hw)
    (by have := X₁.pos; simp only [X₁w, Walk.length_copy]; omega)
  let N₂ := joinT X₂w (m.append q₃) hX₂ hq₂ (fun w hw hw' => hd2 w (by simpa [X₂w] using hw) hw')
    (by have := X₂.pos; simp only [X₂w, Walk.length_reverse, Walk.length_copy]; omega)
  refine ⟨N₁, N₂, ?_, fun v => ?_, fun w hw => ?_, rfl, rfl, X₂w.append m, q₃, ?_,
    fun w hw => ?_, fun w hw => hw⟩
  · simp only [N₁, N₂, joinT_edges, X₁w, X₂w, Walk.edges_reverse, Walk.edges_copy,
      ← Multiset.coe_add, Multiset.coe_reverse]
    show _ = ((R.walk.edges : Multiset (Sym2 V)) + X₁.walk.edges) + X₂.walk.edges
    rw [hR]
    simp only [Walk.edges_append, ← Multiset.coe_add]
    abel
  · simp only [N₁, N₂, GPath.endsAt, joinT_src, joinT_tgt, h1, h2]
    by_cases e1 : R.src = v <;> by_cases e2 : R.tgt = v <;> by_cases e3 : X₁.tgt = v <;>
      by_cases e4 : X₂.tgt = v <;> by_cases e5 : p = v <;> simp [e1, e2, e3, e4, e5]
  · rw [mem_joinT_support] at hw
    rcases hw with hw | hw
    · exact Or.inl hw
    · right; simpa [X₁w] using hw
  · exact (Walk.append_assoc _ _ _)
  · rcases (Walk.mem_support_append_iff X₂w m).mp hw with hw | hw
    · left; simpa [X₂w] using hw
    · exact Or.inr hw

/-- Orient a path through `x` and `y` so that it reads `q₁ · m · q₃`, `x` before `y`. -/
theorem exists_orient_two (R : TPath V) {x y : V} (hx : x ∈ R.walk.support)
    (hy : y ∈ R.walk.support) :
    ∃ R' : TPath V, (R'.edges : Multiset (Sym2 V)) = R.edges ∧ (∀ w, R'.endsAt w = R.endsAt w) ∧
      (∀ w, w ∈ R'.walk.support ↔ w ∈ R.walk.support) ∧
      ∃ (q₁ : (⊤ : SimpleGraph V).Walk R'.src x) (m : (⊤ : SimpleGraph V).Walk x y)
        (q₃ : (⊤ : SimpleGraph V).Walk y R'.tgt), R'.walk = q₁.append (m.append q₃) := by
  obtain ⟨q₁, q₂, hq⟩ := R.exists_split_support hx
  by_cases hy2 : y ∈ q₂.support
  · obtain ⟨m, q₃, hm⟩ := Walk.mem_support_iff_exists_append.mp hy2
    exact ⟨R, rfl, fun _ => rfl, fun _ => Iff.rfl, q₁, m, q₃, by rw [hq, hm]⟩
  · have hy1 : y ∈ q₁.support := by
      rw [hq, Walk.mem_support_append_iff] at hy; tauto
    have hy1' : y ∈ q₁.reverse.support := by
      rw [Walk.support_reverse]; exact List.mem_reverse.mpr hy1
    obtain ⟨m, q₃, hm⟩ := Walk.mem_support_iff_exists_append.mp hy1'
    refine ⟨R.reverse, by simp [Multiset.coe_reverse], fun w => GPath.reverse_endsAt' R w,
      fun w => by rw [GPath.reverse_support, List.mem_reverse], q₂.reverse, m, q₃, ?_⟩
    show R.walk.reverse = _
    rw [hq, Walk.reverse_append, hm]
    rfl

/-- Orient a path through the edge `ab` so that it reads `q · ab · q'`. -/
theorem exists_orient_edge (R : TPath V) {a b : V} (hab : s(a, b) ∈ R.edges) :
    ∃ R' : TPath V, (R'.edges : Multiset (Sym2 V)) = R.edges ∧ (∀ w, R'.endsAt w = R.endsAt w) ∧
      (∀ w, w ∈ R'.walk.support ↔ w ∈ R.walk.support) ∧
      ∃ (q : (⊤ : SimpleGraph V).Walk R'.src a) (h : (⊤ : SimpleGraph V).Adj a b)
        (q' : (⊤ : SimpleGraph V).Walk b R'.tgt), R'.walk = q.append (Walk.cons h q') := by
  obtain ⟨c, d, hcd, q, q', he, hR⟩ := Walk.exists_append_cons_of_mem_edges R.walk hab
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨R, rfl, fun _ => rfl, fun _ => Iff.rfl, q, hcd, q', hR⟩
  · refine ⟨R.reverse, by simp [Multiset.coe_reverse], fun w => GPath.reverse_endsAt' R w,
      fun w => by rw [GPath.reverse_support, List.mem_reverse], q'.reverse, hcd.symm,
      q.reverse, ?_⟩
    show R.walk.reverse = _
    rw [hR, Walk.reverse_append, Walk.reverse_cons, ← Walk.append_assoc]
    rfl

/-- In a list of paths covering `x w₀`, where `w₀` is an end of no path and all edges at `w₀` go
to `x` or `y`, the path through `x w₀` reads `q · (x w₀ y) · q''` once oriented. -/
theorem exists_split_at_mid (LA : List (TPath V)) {x y w₀ : V}
    (hxw₀ : s(x, w₀) ∈ edgesM LA) (hw₀e : ∀ b, s(w₀, b) ∈ edgesM LA → b = x ∨ b = y)
    (hends : endsL LA w₀ = 0) :
    ∃ (R : TPath V) (rest : List (TPath V)),
      edgesM LA = R.edges + edgesM rest ∧ (∀ v, endsL LA v = R.endsAt v + endsL rest v) ∧
      LA.length = rest.length + 1 ∧ (∀ P ∈ rest, P ∈ LA) ∧
      (∃ P ∈ LA, ∀ w, w ∈ R.walk.support ↔ w ∈ P.walk.support) ∧
      ∃ (q : (⊤ : SimpleGraph V).Walk R.src x) (h₁ : (⊤ : SimpleGraph V).Adj x w₀)
        (h₂ : (⊤ : SimpleGraph V).Adj w₀ y) (q'' : (⊤ : SimpleGraph V).Walk y R.tgt),
        R.walk = q.append (Walk.cons h₁ (Walk.cons h₂ q'')) := by
  obtain ⟨R₁, hR₁, hR₁e⟩ := mem_edgesM.mp hxw₀
  obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hR₁
  have hperm : LA.Perm (R₁ :: (l₁ ++ l₂)) := hl ▸ List.perm_middle
  obtain ⟨R, hRe, hRends, hRsupp, q, h₁, q', hR⟩ := exists_orient_edge R₁ hR₁e
  have hR₁le : R₁.endsAt w₀ ≤ endsL LA w₀ := by
    unfold endsL; exact List.le_sum_of_mem (List.mem_map_of_mem hR₁)
  have hq'pos : 0 < q'.length := by
    by_contra h0
    have hw := Walk.eq_of_length_eq_zero (p := q') (by omega)
    have h1 : 1 ≤ R.endsAt w₀ := by unfold GPath.endsAt; rw [← hw]; simp
    rw [hRends] at h1
    omega
  obtain ⟨b, h₂, q'', hq'⟩ := Walk.exists_eq_cons_of_length_pos q' hq'pos
  have hbR : s(w₀, b) ∈ R₁.edges := by
    have : s(w₀, b) ∈ (R.edges : Multiset (Sym2 V)) := by
      rw [Multiset.mem_coe]
      show s(w₀, b) ∈ R.walk.edges
      rw [hR, hq']; simp
    rw [hRe, Multiset.mem_coe] at this
    exact this
  have hbx : b ≠ x := by
    have hn := R.support_nodup
    rw [hR, hq'] at hn
    have hn2 := support_nodup_of_append_right hn
    simp only [Walk.support_cons, List.nodup_cons, List.mem_cons, not_or] at hn2
    intro hbx
    exact hn2.1.2 (hbx ▸ q''.start_mem_support)
  have hby : b = y := (hw₀e b (mem_edgesM.mpr ⟨R₁, hR₁, hbR⟩)).resolve_left hbx
  subst hby
  refine ⟨R, l₁ ++ l₂, ?_, fun v => ?_, ?_, fun P hP => ?_, ⟨R₁, hR₁, hRsupp⟩, q, h₁, h₂, q'',
    by rw [hR, hq']⟩
  · rw [edgesM_perm hperm, edgesM_cons, hRe]
  · rw [endsL_perm hperm, endsL_cons, hRends]
  · rw [hperm.length_eq, List.length_cons]
  · rw [hl]; rw [List.mem_append] at hP ⊢; rw [List.mem_cons]; tauto

end surgery

/-! ### The lift when `R₀` omits `y` -/

section lifts

variable [DecidableEq V]

/-- **Case `y ∉ R₀`**: graft the two `x`-ended paths of `D^x` into `R₀` at `x`. -/
theorem case1_lift (R₀ : TPath V) {C : Finset V} {x y : V} (hxC : x ∉ C)
    (hR₀C : ∀ w ∈ R₀.walk.support, w ∉ C) (hx : x ∈ R₀.walk.support) (hy : y ∉ R₀.walk.support)
    (LX : List (TPath V)) (Aval : Multiset (Sym2 V)) {s : ℕ} (hLXe : edgesM LX = Aval)
    (hLXl : LX.length ≤ s + 1) (hLXs : ∀ P ∈ LX, ∀ w ∈ P.walk.support, w ∈ localSet C x y)
    (hLXends : ∀ v, v ∉ C → endsL LX v = 2 * (if x = v then 1 else 0)) {r : V} (hr : r ∉ C) :
    ∃ M : List (TPath V), edgesM M = (R₀.edges : Multiset (Sym2 V)) + Aval ∧
      M.length ≤ s + 1 ∧ endsL M r = R₀.endsAt r := by
  have hLXx := hLXends x hxC
  simp only [ite_true] at hLXx
  obtain ⟨X₁, rest₁, hp₁, hX₁⟩ := exists_endsL_one LX (v := x) (by omega)
  have h₁ : endsL rest₁ x = 1 := by
    have := endsL_perm hp₁ x; rw [endsL_cons, hX₁] at this; omega
  obtain ⟨X₂, rest, hp₂, hX₂⟩ := exists_endsL_one rest₁ (v := x) (by omega)
  have hp : LX.Perm (X₁ :: X₂ :: rest) := hp₁.trans (hp₂.cons X₁)
  have hX₁L : X₁ ∈ LX := hp.symm.subset (by simp)
  have hX₂L : X₂ ∈ LX := hp.symm.subset (by simp)
  obtain ⟨X₁', hX₁'s, hX₁'e, hX₁'supp, hX₁'ends⟩ := X₁.exists_orientT hX₁
  obtain ⟨X₂', hX₂'s, hX₂'e, hX₂'supp, hX₂'ends⟩ := X₂.exists_orientT hX₂
  obtain ⟨q₁, q₂, hq⟩ := R₀.exists_split_support hx
  have hmem : ∀ w, w ∈ q₁.support ∨ w ∈ q₂.support → w ∈ R₀.walk.support := by
    intro w hw; rw [hq, Walk.mem_support_append_iff]; exact hw
  have hdisj : ∀ X ∈ LX, ∀ w ∈ X.walk.support, w ∈ R₀.walk.support → w = x := by
    intro X hX w hw hwR
    have h1 := hLXs X hX w hw
    rw [mem_localSet] at h1
    rcases h1 with h1 | h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hwR) hy
    · exact absurd h1 (hR₀C w hwR)
  obtain ⟨N₁, N₂, he, hends, -, -⟩ := exists_graft R₀ X₁' X₂' q₁ q₂ hq hX₁'s hX₂'s
    (fun w hw hw' => hdisj X₁ hX₁L w ((hX₁'supp w).mp hw) (hmem w (Or.inl hw')))
    (fun w hw hw' => hdisj X₂ hX₂L w ((hX₂'supp w).mp hw) (hmem w (Or.inr hw')))
  refine ⟨N₁ :: N₂ :: rest, ?_, ?_, ?_⟩
  · rw [← hLXe, edgesM_perm hp]
    simp only [edgesM_cons]
    rw [← add_assoc, he, hX₁'e, hX₂'e]
    abel
  · have := hp.length_eq
    simp only [List.length_cons] at this ⊢
    omega
  · have h1 := hends r
    have h2 := hLXends r hr
    rw [endsL_perm hp] at h2
    simp only [endsL_cons] at h2 ⊢
    rw [hX₁'ends, hX₂'ends] at h1
    omega

/-- **Case `y ∈ R₀`**: use the local decomposition of `A' = A + x w₀ + w₀ y`. -/
theorem case2_lift (R₀ : TPath V) {C : Finset V} {x y w₀ : V} (hxC : x ∉ C) (hyC : y ∉ C)
    (hxy : x ≠ y) (hw₀C : w₀ ∉ C) (hw₀x : w₀ ≠ x) (hw₀y : w₀ ≠ y)
    (hR₀C : ∀ w ∈ R₀.walk.support, w ∉ C) (hx : x ∈ R₀.walk.support) (hy : y ∈ R₀.walk.support)
    (LA : List (TPath V)) (Aval : Multiset (Sym2 V)) {s : ℕ}
    (hLAe : edgesM LA = Aval + {s(x, w₀)} + {s(w₀, y)}) (hnd : (edgesM LA).Nodup)
    (hAval : ∀ e ∈ Aval, w₀ ∉ e) (hLAl : LA.length = s + 1)
    (hLAs : ∀ P ∈ LA, ∀ w ∈ P.walk.support, w ∈ insert w₀ (localSet C x y))
    (hLAends : ∀ v, v ∉ C → endsL LA v = (if x = v then 1 else 0) + (if y = v then 1 else 0))
    {r : V} (hr : r ∉ C) :
    ∃ M : List (TPath V), edgesM M = (R₀.edges : Multiset (Sym2 V)) + Aval ∧
      M.length ≤ s + 1 ∧ endsL M r = R₀.endsAt r := by
  ----------------------------------------------------------------------------
  -- orient `R₀ = q₁ · m · q₃`
  obtain ⟨R₀', hR₀'e, hR₀'ends, hR₀'supp, q₁, m, q₃, hq⟩ := exists_orient_two R₀ hx hy
  have hR₀'C : ∀ w ∈ R₀'.walk.support, w ∉ C := fun w hw => hR₀C w ((hR₀'supp w).mp hw)
  have hn₀ := R₀'.support_nodup
  rw [hq] at hn₀
  obtain ⟨-, hmq₃n, hd₀⟩ := (nodup_support_append q₁ (m.append q₃)).mp hn₀
  obtain ⟨-, -, hd₀'⟩ := (nodup_support_append m q₃).mp hmq₃n
  have hq₁R : ∀ w ∈ q₁.support, w ∉ C := fun w hw => hR₀'C w (by
    rw [hq, Walk.mem_support_append_iff]; exact Or.inl hw)
  have hmR : ∀ w ∈ m.support, w ∉ C := fun w hw => hR₀'C w (by
    rw [hq, Walk.mem_support_append_iff, Walk.mem_support_append_iff]; exact Or.inr (Or.inl hw))
  have hq₃R : ∀ w ∈ q₃.support, w ∉ C := fun w hw => hR₀'C w (by
    rw [hq, Walk.mem_support_append_iff, Walk.mem_support_append_iff]; exact Or.inr (Or.inr hw))
  have hyq₁ : y ∉ q₁.support := fun h =>
    hxy (hd₀ y h (by rw [Walk.mem_support_append_iff]; exact Or.inr q₃.start_mem_support)).symm
  have hxq₃ : x ∉ q₃.support := fun h => hxy (hd₀' x m.start_mem_support h)
  have hq₁q₃ : ∀ w ∈ q₁.support, w ∉ q₃.support := by
    intro w hw hw'
    have := hd₀ w hw (by rw [Walk.mem_support_append_iff]; exact Or.inr hw')
    exact hxq₃ (this ▸ hw')
  ----------------------------------------------------------------------------
  -- the local path through `w₀`: `R = q · (x w₀ y) · q''`
  have hmemLA : ∀ e, e ∈ edgesM LA ↔ e ∈ Aval ∨ e = s(x, w₀) ∨ e = s(w₀, y) := by
    intro e; rw [hLAe]; simp only [Multiset.mem_add, Multiset.mem_singleton, or_assoc]
  have hxw₀ : s(x, w₀) ∈ edgesM LA := (hmemLA _).mpr (Or.inr (Or.inl rfl))
  have hw₀e : ∀ b, s(w₀, b) ∈ edgesM LA → b = x ∨ b = y := by
    intro b hb
    rcases (hmemLA _).mp hb with h | h | h
    · exact absurd (Sym2.mem_mk_left w₀ b) (hAval _ h)
    · rw [Sym2.eq_iff] at h
      rcases h with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h hw₀x
      · exact Or.inl h
    · rw [Sym2.eq_iff] at h
      rcases h with ⟨-, h⟩ | ⟨h, -⟩
      · exact Or.inr h
      · exact absurd h hw₀y
  have hends₀ : endsL LA w₀ = 0 := by
    rw [hLAends w₀ hw₀C]; simp [hw₀x.symm, hw₀y.symm]
  obtain ⟨R, rest, hRe, hRends, hRl, hrestLA, ⟨PR, hPR, hRsupp⟩, q, h₁, h₂, q'', hR⟩ :=
    exists_split_at_mid LA hxw₀ hw₀e hends₀
  have hnR := R.support_nodup
  rw [hR] at hnR
  obtain ⟨hqn, hTn, hdR⟩ := (nodup_support_append q _).mp hnR
  have hmemT : ∀ w, w ∈ q''.support → w ∈ (Walk.cons h₁ (Walk.cons h₂ q'')).support :=
    fun w hw => by simp [Walk.support_cons, hw]
  simp only [Walk.support_cons, List.nodup_cons, List.mem_cons, not_or] at hTn
  obtain ⟨⟨-, hxq''⟩, hw₀q'', hq''n⟩ := hTn
  have hyq : y ∉ q.support := fun h =>
    hxy (hdR y h (hmemT y q''.start_mem_support)).symm
  have hw₀q : w₀ ∉ q.support := fun h => hw₀x (hdR w₀ h (by simp [Walk.support_cons]))
  have hqq'' : ∀ w ∈ q.support, w ∉ q''.support := fun w hw hw' =>
    hxq'' ((hdR w hw (hmemT w hw')) ▸ hw')
  have hRsupp' : ∀ w ∈ R.walk.support, w ∈ insert w₀ (localSet C x y) :=
    fun w hw => hLAs PR hPR w ((hRsupp w).mp hw)
  have hqloc : ∀ w ∈ q.support, w ∈ C ∨ w = x := by
    intro w hw
    have h1 := hRsupp' w (by rw [hR, Walk.mem_support_append_iff]; exact Or.inl hw)
    rw [Finset.mem_insert, mem_localSet] at h1
    rcases h1 with h1 | h1 | h1 | h1
    · exact absurd (h1 ▸ hw) hw₀q
    · exact Or.inr h1
    · exact absurd (h1 ▸ hw) hyq
    · exact Or.inl h1
  have hq''loc : ∀ w ∈ q''.support, w ∈ C ∨ w = y := by
    intro w hw
    have h1 := hRsupp' w (by rw [hR, Walk.mem_support_append_iff]; exact Or.inr (hmemT w hw))
    rw [Finset.mem_insert, mem_localSet] at h1
    rcases h1 with h1 | h1 | h1 | h1
    · exact absurd (h1 ▸ hw) hw₀q''
    · exact absurd (h1 ▸ hw) hxq''
    · exact Or.inr h1
    · exact Or.inl h1
  have hRedges : (R.edges : Multiset (Sym2 V)) =
      q.edges + {s(x, w₀)} + {s(w₀, y)} + q''.edges := by
    show (R.walk.edges : Multiset (Sym2 V)) = _
    rw [hR]
    simp only [Walk.edges_append, Walk.edges_cons, ← Multiset.coe_add, ← Multiset.cons_coe]
    rw [← Multiset.singleton_add, ← Multiset.singleton_add]
    abel
  have hrestloc : ∀ P ∈ rest, ∀ w ∈ P.walk.support, w ∈ localSet C x y := by
    intro P hP w hw
    rcases Finset.mem_insert.mp (hLAs P (hrestLA P hP) w hw) with h1 | h1
    · exfalso
      obtain ⟨e, he, hwe⟩ := (Walk.mem_support_iff_exists_mem_edges_of_not_nil
        (Walk.not_nil_iff_lt_length.mpr P.pos)).mp hw
      have heR : e ∈ edgesM rest := mem_edgesM.mpr ⟨P, hP, he⟩
      have heLA : e ∈ edgesM LA := by rw [hRe]; exact Multiset.mem_add.mpr (Or.inr heR)
      have hnd' := hnd
      rw [hRe] at hnd'
      have hdisj := (Multiset.nodup_add.mp hnd').2.2
      rcases (hmemLA e).mp heLA with h | h | h
      · exact hAval e h (by rw [← h1]; exact hwe)
      · refine Multiset.disjoint_left.mp hdisj ?_ heR
        rw [hRedges, h]; simp
      · refine Multiset.disjoint_left.mp hdisj ?_ heR
        rw [hRedges, h]; simp
    · exact h1
  have hAedges : edgesM rest + q.edges + q''.edges = Aval := by
    have h' : (edgesM rest + q.edges + q''.edges) + {s(x, w₀)} + {s(w₀, y)} =
        Aval + {s(x, w₀)} + {s(w₀, y)} := by
      rw [← hLAe, hRe, hRedges]; abel
    exact (add_left_inj _).mp ((add_left_inj _).mp h')
  have hRends' : ∀ v, v ∉ C → R.endsAt v + endsL rest v =
      (if x = v then 1 else 0) + (if y = v then 1 else 0) :=
    fun v hv => by rw [← hLAends v hv, hRends]
  have hrestl : rest.length = s := by omega
  ----------------------------------------------------------------------------
  -- phase `x`: if `R_x = q` is nontrivial, graft it and the other `x`-ended path into `R₀'`
  obtain ⟨P, M₁, u, q₃', hP, hu, hq₃', hPy, hM₁s, hM₁l, hM₁e, hM₁ends⟩ :
      ∃ (P : TPath V) (M₁ : List (TPath V)) (u : (⊤ : SimpleGraph V).Walk P.src y)
        (q₃' : (⊤ : SimpleGraph V).Walk y P.tgt), P.walk = u.append q₃' ∧
        (∀ w ∈ u.support, w ∈ q''.support → w = y) ∧ (∀ w ∈ q₃'.support, w ∈ q₃.support) ∧
        P.endsAt y ≤ R₀'.endsAt y ∧
        (∀ Q ∈ M₁, ∀ w ∈ Q.walk.support, w ∈ q₁.support ∨ w ∈ localSet C x y) ∧
        M₁.length = s ∧
        edgesM (P :: M₁) + q''.edges = (R₀'.edges : Multiset (Sym2 V)) + Aval ∧
        ∀ v, v ∉ C → endsL (P :: M₁) v + (if R.tgt = v then 1 else 0) =
          R₀'.endsAt v + (if y = v then 1 else 0) := by
    by_cases ha : q.length = 0
    · -- `R_x` trivial
      have hsx : R.src = x := Walk.eq_of_length_eq_zero ha
      have hqe : q.edges = [] := by rw [← List.length_eq_zero_iff, Walk.length_edges, ha]
      refine ⟨R₀', rest, q₁.append m, q₃, by rw [hq, Walk.append_assoc], ?_, fun w hw => hw,
        le_refl _, fun Q hQ w hw => Or.inr (hrestloc Q hQ w hw), hrestl, ?_, ?_⟩
      · intro w hw hw'
        have hwC : w ∉ C := by
          rcases (Walk.mem_support_append_iff q₁ m).mp hw with h | h
          · exact hq₁R w h
          · exact hmR w h
        rcases hq''loc w hw' with h | h
        · exact absurd h hwC
        · exact h
      · rw [edgesM_cons, ← hAedges, hqe]
        simp only [Multiset.coe_nil, add_zero]
        abel
      · intro v hv
        rw [endsL_cons]
        have := hRends' v hv
        unfold GPath.endsAt at this
        rw [hsx] at this
        omega
    · -- `R_x` nontrivial
      have hqpos : 0 < q.length := Nat.pos_of_ne_zero ha
      let Rx : TPath V := ⟨R.src, x, q, (Walk.isPath_def _).mpr hqn, hqpos⟩
      have hRxsrc : R.src ∈ C := by
        rcases hqloc R.src q.start_mem_support with h | h
        · exact h
        · exact absurd h Rx.src_ne_tgt
      have hRtx : R.tgt ≠ x := fun h => hxq'' (h ▸ q''.end_mem_support)
      have hRsx : R.src ≠ x := fun h => hxC (h ▸ hRxsrc)
      have hrx : endsL rest x = 1 := by
        have := hRends' x hxC
        unfold GPath.endsAt at this
        have hyx : y ≠ x := hxy.symm
        simp only [hRsx, hRtx, hyx, ite_true, ite_false] at this
        omega
      obtain ⟨X, rest₁, hp₁, hX⟩ := exists_endsL_one rest (v := x) (by omega)
      have hXrest : X ∈ rest := hp₁.symm.subset List.mem_cons_self
      obtain ⟨X', hX's, hX'e, hX'supp, hX'ends⟩ := X.exists_orientT hX
      have hRxsupp : ∀ w, w ∈ Rx.reverse.walk.support ↔ w ∈ q.support := by
        intro w; rw [GPath.reverse_support, List.mem_reverse]
      obtain ⟨N₁, N₂, he, hends, hN₁s, hN₂s, hN₂t, u, q₃', hN₂, hu, hq₃'⟩ :=
        exists_graft_x R₀' X' Rx.reverse q₁ m q₃ hq hX's rfl
          (by
            intro w hw hw'
            have h1 := hrestloc X hXrest w ((hX'supp w).mp hw)
            rw [mem_localSet] at h1
            rcases h1 with h1 | h1 | h1
            · exact h1
            · exact absurd (h1 ▸ hw') hyq₁
            · exact absurd h1 (hq₁R w hw'))
          (by
            intro w hw hw'
            have hwC : w ∉ C := by
              rcases (Walk.mem_support_append_iff m q₃).mp hw' with h | h
              · exact hmR w h
              · exact hq₃R w h
            rcases hqloc w ((hRxsupp w).mp hw) with h | h
            · exact absurd h hwC
            · exact h)
      have hN₂src : N₂.src = R.src := hN₂s
      refine ⟨N₂, N₁ :: rest₁, u, q₃', hN₂, ?_, hq₃', ?_, ?_, ?_, ?_, ?_⟩
      · intro w hw hw'
        rcases hu w hw with h | h
        · exact absurd hw' (hqq'' w ((hRxsupp w).mp h))
        · rcases hq''loc w hw' with h' | h'
          · exact absurd h' (hmR w h)
          · exact h'
      · have hRsy : R.src ≠ y := fun h => hyC (h ▸ hRxsrc)
        unfold GPath.endsAt
        rw [hN₂src, hN₂t]
        simp only [hRsy, ite_false, zero_add]
        omega
      · intro Q hQ w hw
        rcases List.mem_cons.mp hQ with rfl | hQ
        · rcases hN₁s w hw with h | h
          · exact Or.inl h
          · exact Or.inr (hrestloc X hXrest w ((hX'supp w).mp h))
        · exact Or.inr (hrestloc Q (hp₁.symm.subset (List.mem_cons_of_mem _ hQ)) w hw)
      · have := hp₁.length_eq
        simp only [List.length_cons] at this ⊢
        omega
      · have hRxe : (Rx.reverse.edges : Multiset (Sym2 V)) = q.edges := by
          rw [GPath.reverse_edges, Multiset.coe_reverse]; rfl
        have he' : (N₁.edges : Multiset (Sym2 V)) + N₂.edges =
            R₀'.edges + X.edges + q.edges := by
          rw [he, hX'e, hRxe]
        rw [← hAedges, edgesM_perm hp₁]
        simp only [edgesM_cons]
        rw [show (N₂.edges : Multiset (Sym2 V)) + (N₁.edges + edgesM rest₁) + q''.edges =
          (N₁.edges + N₂.edges) + edgesM rest₁ + q''.edges by abel, he']
        abel
      · intro v hv
        have h1 := hends v
        have h2 := hRends' v hv
        have h3 := endsL_perm hp₁ v
        have hRsv : R.src ≠ v := fun h => hv (h ▸ hRxsrc)
        have hRxv : Rx.reverse.endsAt v = if x = v then 1 else 0 := by
          rw [GPath.reverse_endsAt']
          show (if R.src = v then 1 else 0) + (if x = v then 1 else 0) = _
          simp [hRsv]
        rw [hX'ends, hRxv] at h1
        unfold GPath.endsAt at h2
        simp only [hRsv, ite_false, zero_add] at h2
        simp only [endsL_cons] at h3 ⊢
        omega
  ----------------------------------------------------------------------------
  -- phase `y`: if `R_y = q''` is nontrivial, graft it and the other `y`-ended path into `P`
  by_cases hb : q''.length = 0
  · have hty : y = R.tgt := Walk.eq_of_length_eq_zero hb
    have hq''e : q''.edges = [] := by rw [← List.length_eq_zero_iff, Walk.length_edges, hb]
    refine ⟨P :: M₁, ?_, ?_, ?_⟩
    · rw [← hR₀'e, ← hM₁e, hq''e]; simp
    · simp [hM₁l]
    · have := hM₁ends r hr
      rw [← hty] at this
      rw [← hR₀'ends r]
      omega
  · have hq''pos : 0 < q''.length := Nat.pos_of_ne_zero hb
    let Ry : TPath V := ⟨y, R.tgt, q'', (Walk.isPath_def _).mpr hq''n, hq''pos⟩
    have hRtC : R.tgt ∈ C := by
      rcases hq''loc R.tgt q''.end_mem_support with h | h
      · exact h
      · exact absurd h.symm Ry.src_ne_tgt
    have hM₁y : 1 ≤ endsL M₁ y := by
      have := hM₁ends y hyC
      rw [endsL_cons] at this
      have hne : R.tgt ≠ y := fun h => hyC (h ▸ hRtC)
      simp only [hne, ite_false, ite_true, add_zero] at this
      omega
    obtain ⟨Y, M₂, hp₂, hY⟩ := exists_endsL_one M₁ hM₁y
    have hYM₁ : Y ∈ M₁ := hp₂.symm.subset List.mem_cons_self
    obtain ⟨Y', hY's, hY'e, hY'supp, hY'ends⟩ := Y.exists_orientT hY
    obtain ⟨N₁, N₂, he, hends, -, -⟩ := exists_graft P Ry Y' u q₃' hP rfl hY's
      (fun w hw hw' => hu w hw' hw)
      (by
        intro w hw hw'
        have hw3 := hq₃' w hw'
        rcases hM₁s Y hYM₁ w ((hY'supp w).mp hw) with h | h
        · exact absurd hw3 (hq₁q₃ w h)
        · rw [mem_localSet] at h
          rcases h with h | h | h
          · exact absurd (h ▸ hw3) hxq₃
          · exact h
          · exact absurd h (hq₃R w hw3))
    refine ⟨N₁ :: N₂ :: M₂, ?_, ?_, ?_⟩
    · rw [← hR₀'e, ← hM₁e]
      simp only [edgesM_cons]
      rw [edgesM_perm hp₂, edgesM_cons, ← add_assoc, he, hY'e]
      have hRye : (Ry.edges : Multiset (Sym2 V)) = q''.edges := rfl
      rw [hRye]
      abel
    · have := hp₂.length_eq
      simp only [List.length_cons] at this ⊢
      omega
    · have h1 := hends r
      have h2 := hM₁ends r hr
      have h3 := endsL_perm hp₂ r
      have hRtr : R.tgt ≠ r := fun h => hr (h ▸ hRtC)
      have hRyr : Ry.endsAt r = if y = r then 1 else 0 := by
        show (if y = r then 1 else 0) + (if R.tgt = r then 1 else 0) = _
        simp [hRtr]
      rw [hRyr, hY'ends] at h1
      simp only [hRtr, ite_false, add_zero, endsL_cons] at h2
      simp only [endsL_cons] at h3 ⊢
      rw [← hR₀'ends r]
      omega

end lifts

/-! ### The local decompositions and the theorem -/

section main

variable [Fintype V] [DecidableEq V] {B : SimpleGraph V} [DecidableRel B.Adj] {C : Finset V}
  {x y : V}

/-- **`D^x`**: a decomposition of `A` with at most `s + 1` paths, two ends at `x` and none at any
other vertex outside `C` (Lovász on `A` with a private leaf at `x`, then counting ends). -/
theorem exists_localX (hL : LovaszStatement.{u}) (hB : KConnected 2 B)
    (hC : IsSepComponent B x y C) (hodd : ∀ c ∈ C, Odd (B.degree c)) {s : ℕ}
    (hs : C.card = s + s) (hx : Even ((sideA B C x y).degree x)) :
    ∃ LX : List (TPath V), edgesM LX = (sideA B C x y).edgeFinset.val ∧ LX.length ≤ s + 1 ∧
      (∀ P ∈ LX, ∀ w ∈ P.walk.support, w ∈ localSet C x y) ∧
      ∀ v, v ∉ C → endsL LX v = 2 * (if x = v then 1 else 0) := by
  have hAU := sideA_support_local hC
  have hxC := hC.x_notMem
  have hyC := hC.y_notMem
  have hxy := hC.ne
  have hxL : x ∈ localSet C x y := mem_localSet.mpr (Or.inl rfl)
  set F := (sideA B C x y).induce ((localSet C x y : Finset V) : Set V) with hF
  set x' : ((localSet C x y : Finset V) : Set V) := ⟨x, hxL⟩ with hx'
  have hcard : Fintype.card ((localSet C x y : Finset V) : Set V) = s + s + 2 := by
    have h : Fintype.card ((localSet C x y : Finset V) : Set V) = (localSet C x y).card := by
      simp
    rw [h, card_localSet hC, hs]
  have hdegF : ∀ v : ((localSet C x y : Finset V) : Set V),
      F.degree v = (sideA B C x y).degree v := fun v => degree_induce_eq hAU v
  have hcnt : (Finset.univ.filter (fun w => Even ((addLeaf F x').degree w))).card ≤ 1 := by
    rw [card_filter_option, addLeaf_degree_none]
    simp only [Nat.not_even_one, ite_false, zero_add]
    have key : ∀ a : ((localSet C x y : Finset V) : Set V),
        Even ((addLeaf F x').degree (some a)) → a.1 = y := by
      intro a ha
      rw [addLeaf_degree_some, hdegF] at ha
      by_cases hax : a = x'
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hax), show (a : V) = x from congrArg Subtype.val hax]
          at ha
        exact absurd hx (Nat.even_add_one.mp ha)
      · simp only [hax, ite_false, add_zero] at ha
        rcases mem_localSet.mp a.2 with h | h | haC
        · exact absurd (Subtype.ext h) hax
        · exact h
        · rw [sideA_degree_of_mem haC] at ha
          exact absurd (hodd _ haC) (Nat.not_odd_iff_even.mpr ha)
    refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact Subtype.ext ((key a ha).trans (key b hb).symm)
  have hp := hL _ (addLeaf F x') hcnt
  rw [Fintype.card_option, hcard] at hp
  obtain ⟨D₀, hD₀⟩ := exists_leafCost_le F x'
  have hApos := (sideA_port_pos hC hB).1
  obtain ⟨D₁, h11, h12⟩ := exists_two_ends D₀ (x := x') (k := s + 1) (by omega)
    (by rw [hdegF]; exact hx) (by rw [hdegF]; exact hApos)
  obtain ⟨D, hD1, hD2⟩ := decomp_of_induce hAU D₁
  have hDx : 2 ≤ D.ends x := by
    have h : D.ends x = D₁.ends x' := hD2 x'
    omega
  -- counting ends: every vertex of `C` is odd, so `x` has exactly two ends and `y` none
  have hsum := D.sum_ends
  have hloc : ∑ v ∈ localSet C x y, D.ends v = D.ends x + D.ends y + ∑ v ∈ C, D.ends v := by
    rw [localSet, Finset.sum_insert (by simp [hxy, hxC]), Finset.sum_insert hyC, add_assoc]
  have hsub : ∑ v ∈ localSet C x y, D.ends v ≤ ∑ v, D.ends v :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hCsum : C.card ≤ ∑ v ∈ C, D.ends v := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum (fun c hc => ?_)
    have h1 := D.ends_mod_two c
    rw [sideA_degree_of_mem hc] at h1
    have h2 := hodd c hc
    rw [Nat.odd_iff] at h2
    omega
  have hDy : D.ends y = 0 := by omega
  have hDx2 : D.ends x = 2 := by omega
  have hsupp : ∀ P ∈ D.paths.map GPath.toTop, ∀ w ∈ P.walk.support, w ∈ localSet C x y := by
    intro P hP w hw
    obtain ⟨P₀, -, rfl⟩ := List.mem_map.mp hP
    rw [GPath.toTop_support] at hw
    exact GPath.support_subset hAU P₀ w hw
  refine ⟨D.paths.map GPath.toTop, D.edgesM_toTop, ?_, hsupp, fun v hv => ?_⟩
  · rw [D.length_toTop]; omega
  · by_cases hvx : v = x
    · rw [D.endsL_toTop, hvx, hDx2]; simp
    by_cases hvy : v = y
    · rw [D.endsL_toTop, hvy, hDy]; simp [hxy]
    · have hxv : x ≠ v := fun h => hvx h.symm
      rw [endsL_eq_zero_of_notMem hsupp (by rw [mem_localSet]; tauto)]
      simp [hxv]

/-- **The local decomposition of `A' = A + x w₀ + w₀ y`**: `s + 1` paths with one end at each of
`x`, `y` and the vertices of `C`, and none at `w₀` (Lovász, tight form). -/
theorem exists_localA' (hL : LovaszStatement.{u}) (hC : IsSepComponent B x y C)
    (hodd : ∀ c ∈ C, Odd (B.degree c)) {s : ℕ} (hs : C.card = s + s)
    (hx : Even ((sideA B C x y).degree x)) (hy : Even ((sideA B C x y).degree y))
    {w₀ : V} (hw₀C : w₀ ∉ C) (hw₀x : w₀ ≠ x) (hw₀y : w₀ ≠ y) :
    ∃ LA : List (TPath V),
      edgesM LA = (sideA B C x y).edgeFinset.val + {s(x, w₀)} + {s(w₀, y)} ∧
      (edgesM LA).Nodup ∧ LA.length = s + 1 ∧
      (∀ P ∈ LA, ∀ w ∈ P.walk.support, w ∈ insert w₀ (localSet C x y)) ∧
      ∀ v, v ∉ C → endsL LA v = (if x = v then 1 else 0) + (if y = v then 1 else 0) := by
  have hAU := sideA_support_local hC
  have hxy := hC.ne
  have hw₀L : w₀ ∉ localSet C x y := by rw [mem_localSet]; tauto
  have hnA : ∀ a, ¬ (sideA B C x y).Adj w₀ a := fun a h => hw₀L (hAU _ _ h)
  have hn1 : ¬ (sideA B C x y).Adj x w₀ := fun h => hnA x h.symm
  have hn2 : ¬ (plusEdge (sideA B C x y) x w₀).Adj w₀ y := by
    rintro (h | ⟨-, ⟨h, -⟩ | ⟨-, h⟩⟩)
    · exact hnA y h
    · exact hw₀x h
    · exact hxy h.symm
  set A₁ := plusEdge (sideA B C x y) x w₀ with hA₁
  set A' := plusEdge A₁ w₀ y with hA'
  have hdegv : ∀ v, A'.degree v = (sideA B C x y).degree v +
      (if v = x ∨ v = w₀ then 1 else 0) + (if v = w₀ ∨ v = y then 1 else 0) := by
    intro v
    rw [plusEdge_degree hw₀y hn2, plusEdge_degree hw₀x.symm hn1]
  have hA'U : ∀ a b, A'.Adj a b → a ∈ insert w₀ (localSet C x y) := by
    intro a b h
    rcases h with (h | ⟨-, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩) | ⟨-, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
    · exact Finset.mem_insert_of_mem (hAU a b h)
    · exact Finset.mem_insert_of_mem (mem_localSet.mpr (Or.inl rfl))
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (mem_localSet.mpr (Or.inr (Or.inl rfl)))
  have hdx : Odd (A'.degree x) := by
    rw [hdegv]; simp [hw₀x.symm, hxy]; exact hx.add_one
  have hdy : Odd (A'.degree y) := by
    rw [hdegv]; simp [hw₀y.symm, hxy.symm]; exact hy.add_one
  have hdw : A'.degree w₀ = 2 := by
    rw [hdegv, sideA_degree_of_ext hC hw₀C hw₀x hw₀y]; simp
  have hdc : ∀ c ∈ C, A'.degree c = B.degree c := by
    intro c hc
    have h1 : c ≠ x := fun h => hC.x_notMem (h ▸ hc)
    have h2 : c ≠ y := fun h => hC.y_notMem (h ▸ hc)
    have h3 : c ≠ w₀ := fun h => hw₀C (h ▸ hc)
    rw [hdegv, sideA_degree_of_mem hc]; simp [h1, h2, h3]
  have heven : (insert w₀ (localSet C x y)).filter (fun v => Even (A'.degree v)) = {w₀} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_insert, mem_localSet, Finset.mem_singleton]
    constructor
    · rintro ⟨hv, he⟩
      rcases hv with h | h | h | h
      · exact h
      · rw [h] at he; exact absurd hdx (Nat.not_odd_iff_even.mpr he)
      · rw [h] at he; exact absurd hdy (Nat.not_odd_iff_even.mpr he)
      · rw [hdc v h] at he; exact absurd (hodd v h) (Nat.not_odd_iff_even.mpr he)
    · rintro rfl
      exact ⟨Or.inl rfl, by rw [hdw]; decide⟩
  obtain ⟨DA, hDA1, hDA2⟩ := lovasz_tight hL hA'U (by rw [heven]; simp)
  rw [heven, Finset.card_singleton, Finset.card_insert_of_notMem hw₀L, card_localSet hC]
    at hDA1
  have hA'val : A'.edgeFinset.val =
      (sideA B C x y).edgeFinset.val + {s(x, w₀)} + {s(w₀, y)} := by
    have h1 : A₁.edgeFinset.val = (sideA B C x y).edgeFinset.val + {s(x, w₀)} := by
      refine edgeFinset_val_eq_add _ (Multiset.nodup_singleton _) ?_ ?_
      · intro e he; rw [Multiset.mem_singleton] at he; subst he; exact hn1
      · intro e; rw [plusEdge_edgeSet hw₀x.symm, Multiset.mem_singleton]
    have h2 : A'.edgeFinset.val = A₁.edgeFinset.val + {s(w₀, y)} := by
      refine edgeFinset_val_eq_add _ (Multiset.nodup_singleton _) ?_ ?_
      · intro e he; rw [Multiset.mem_singleton] at he; subst he; exact hn2
      · intro e; rw [plusEdge_edgeSet hw₀y, Multiset.mem_singleton]
    rw [h2, h1]
  refine ⟨DA.paths.map GPath.toTop, by rw [DA.edgesM_toTop, hA'val],
    by rw [DA.edgesM_toTop]; exact A'.edgeFinset.nodup, by rw [DA.length_toTop]; omega,
    fun P hP w hw => ?_, fun v hv => ?_⟩
  · obtain ⟨P₀, -, rfl⟩ := List.mem_map.mp hP
    rw [GPath.toTop_support] at hw
    exact GPath.support_subset hA'U P₀ w hw
  · rw [DA.endsL_toTop, hDA2]
    by_cases hvx : v = x
    · rw [hvx]; simp [hdx, hxy.symm]
    by_cases hvy : v = y
    · rw [hvy]; simp [hdy, hxy]
    have hxv : x ≠ v := fun h => hvx h.symm
    have hyv : y ≠ v := fun h => hvy h.symm
    by_cases hvw : v = w₀
    · have h2 : ¬ Odd 2 := by decide
      rw [hvw, hdw]; simp [h2, hw₀x.symm, hw₀y.symm]
    · have h0 : A'.degree v = 0 := by
        rw [hdegv, sideA_degree_of_ext hC hv hvx hvy]; simp [hvx, hvy, hvw]
      rw [h0]; simp [hxv, hyv]

/-- **Theorem 113, even component, both ports even in `A`.** -/
theorem rootedAt_evenComp_evenPorts (hL : LovaszStatement.{u})
    (hMB : MarkedBoundUpTo.{u} (Fintype.card V - 2)) (hB : KConnected 2 B)
    (hC : IsSepComponent B x y C) (hodd : ∀ c ∈ C, Odd (B.degree c)) {r : V} (hr : r ∉ C)
    (hCeven : Even C.card) (hx : Even ((sideA B C x y).degree x))
    (hy : Even ((sideA B C x y).degree y)) : RootedAt B r := by
  obtain ⟨s, hs⟩ := hCeven
  have hs1 : 1 ≤ s := by
    have := Finset.card_pos.mpr hC.nonempty; omega
  have hxC := hC.x_notMem
  have hyC := hC.y_notMem
  have hxy := hC.ne
  have hAU := sideA_support_local hC
  obtain ⟨LX, hLXe, hLXl, hLXs, hLXends⟩ := exists_localX hL hB hC hodd hs hx
  obtain ⟨w₀, hw₀C, hw₀x, hw₀y⟩ := hC.sep
  obtain ⟨LA, hLAe, hLAnd, hLAl, hLAs, hLAends⟩ :=
    exists_localA' hL hC hodd hs hx hy hw₀C hw₀x hw₀y
  have hw₀L : w₀ ∉ localSet C x y := by rw [mem_localSet]; tauto
  have hAval : ∀ e ∈ (sideA B C x y).edgeFinset.val, w₀ ∉ e := by
    intro e he hw
    rw [Finset.mem_val, mem_edgeFinset] at he
    induction e using Sym2.inductionOn with
    | hf a b =>
      rcases Sym2.mem_iff.mp hw with h | h
      · have he' : (sideA B C x y).Adj a b := he
        exact hw₀L (h ▸ hAU _ _ he')
      · have he' : (sideA B C x y).Adj b a := (show (sideA B C x y).Adj a b from he).symm
        exact hw₀L (h ▸ hAU _ _ he')
  have hEpos := sideE_port_pos hC hB
  have hdegB := degree_sides (B := B) (C := C) (x := x) (y := y) r
  have hB2 := hB.le_degree r
  have hcardU : (Cᶜ : Finset V).card + 2 * s = Fintype.card V := by
    rw [Finset.card_compl]; have := Finset.card_le_univ C; omega
  have hrU : r ∈ (Cᶜ : Finset V) := by simpa using hr
  have hEU : ∀ a b, (sideE B C x y).Adj a b → a ∈ (Cᶜ : Finset V) :=
    fun a b h => by simpa using sideE_notMem h
  refine rootedAt_of_lift hMB hB r (sideE B C x y) (Cᶜ) s hs1 hEU
    (sideE_induce_connected hC hB) hcardU hrU ?_ ?_ ?_
  · -- parity at the root: `d_A(r)` is even
    rw [← hdegB]
    have hAr : Even ((sideA B C x y).degree r) := by
      by_cases hrx : r = x
      · rw [hrx]; exact hx
      by_cases hry : r = y
      · rw [hry]; exact hy
      · rw [sideA_degree_of_ext hC hr hrx hry]; exact ⟨0, rfl⟩
    obtain ⟨k, hk⟩ := hAr
    omega
  · -- positivity at the root
    by_cases hrx : r = x
    · rw [hrx]; exact hEpos.1
    by_cases hry : r = y
    · rw [hry]; exact hEpos.2
    · rw [sideA_degree_of_ext hC hr hrx hry] at hdegB; omega
  · -- the lift
    intro DE
    obtain ⟨L, hL⟩ : ∃ L, L = DE.paths.map GPath.toTop := ⟨_, rfl⟩
    have hLe : edgesM L = (sideE B C x y).edgeFinset.val := by rw [hL]; exact DE.edgesM_toTop
    obtain ⟨b, hb⟩ := ((sideE B C x y).degree_pos_iff_exists_adj x).mp hEpos.1
    have hxbL : s(x, b) ∈ edgesM L := by rw [hLe, Finset.mem_val, mem_edgeFinset]; exact hb
    obtain ⟨R₀, hR₀L, hR₀e⟩ := mem_edgesM.mp hxbL
    have hxR₀ : x ∈ R₀.walk.support := R₀.walk.fst_mem_support_of_mem_edges hR₀e
    have hR₀C : ∀ w ∈ R₀.walk.support, w ∉ C := by
      rw [hL] at hR₀L
      obtain ⟨P, -, rfl⟩ := List.mem_map.mp hR₀L
      intro w hw
      rw [GPath.toTop_support] at hw
      simpa using GPath.support_subset hEU P w hw
    have finish : ∀ M : List (TPath V),
        edgesM M = (R₀.edges : Multiset (Sym2 V)) + (sideA B C x y).edgeFinset.val →
        M.length ≤ s + 1 → endsL M r = R₀.endsAt r →
        ∃ D' : PathDecomp B, D'.size ≤ DE.size + s ∧ D'.ends r = DE.ends r := by
      intro M hM1 hM2 hM3
      obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hR₀L
      obtain ⟨D', h1, h2⟩ := exists_decomp_of_edgesM (G := B) (l₁ ++ l₂ ++ M) (by
        rw [edgesM_append, edgesM_append, hM1, edgeFinset_sides (B := B) (C := C) (x := x) (y := y),
          ← hLe, hl]
        simp only [edgesM_append, edgesM_cons]
        abel)
      refine ⟨D', ?_, ?_⟩
      · rw [h1]
        have := DE.length_toTop
        rw [← hL, hl] at this
        simp only [List.length_append, List.length_cons] at this ⊢
        omega
      · rw [h2, ← DE.endsL_toTop, ← hL, hl]
        simp only [endsL_append, endsL_cons, hM3]
        ring
    by_cases hyR₀ : y ∈ R₀.walk.support
    · obtain ⟨M, h1, h2, h3⟩ := case2_lift R₀ hxC hyC hxy hw₀C hw₀x hw₀y hR₀C hxR₀ hyR₀ LA _
        hLAe hLAnd hAval hLAl hLAs hLAends hr
      exact finish M h1 h2 h3
    · obtain ⟨M, h1, h2, h3⟩ := case1_lift R₀ hxC hR₀C hxR₀ hyR₀ LX _ hLXe hLXl hLXs
        hLXends hr
      exact finish M h1 h2 h3

end main

end Gallai
