import GallaiLean.SixCliqueBuild

/-!
# Prescribed path ends at a clique of six even vertices (Theorem 1)

Source: *Prescribed path ends at a clique of six even vertices*, Theorem 1
(`gallai/04-research-studies/six-clique-prescribed-ends.pdf`); audit A6 (§1.3, items C1–C8).

**Theorem 1** (`six_clique_prescribed_ends`). Let `U` be a clique of six even-degree vertices of a
finite graph `G`, and let every other vertex (the set `X`, `m = |X|`) have odd degree and exactly
five neighbours in `U`. For every 3-subset `T ⊆ U` there is a partition of `E(G)` into
`(m + 6)/2` paths with exactly one end at each vertex of `X`, two at each member of `T` and none
at `U \ T`. Edges inside `X` are arbitrary.

## The proof at full detail

Throughout, a *state* is a pair (present edge set `E`, end vector `b`) for which `E` has a path
decomposition with `b v` ends at every `v` (`Ach E b`, `Insertion.lean`). The number of paths is
never tracked: `∑ ends = 2 · size` recovers it at the end. A vertex is *blank* if `b v = 0`.
We write `t → u` for adding the missing edge `tu` while moving one end from `t` to `u`.

**Lemma 2 (Fan's grouped transfer; `fan_grouped`, `Ach.grouped`).** If `T` is a set of
non-neighbours of `u` (with `u ∉ T`) and `∑_{t ∈ T} b t > #{blank neighbours of u}`, then some
`t ∈ T` with `b t ≥ 1` admits `t → u`.
*Chain step, expanded (audit F10).* Read paths from their ends. For an end occurrence at `x` on a
path through `u`, the vertex before `u` is a *predecessor* of `x`. Let `R` be the closure of `T`
under predecessors. If every end occurrence at `R` lay on a path through `u`, each such occurrence
would determine the edge from its predecessor to `u`; distinct occurrences give distinct edges
(one path, read from its two ends, gives the two different edges at `u`). Hence
`∑_{T} b + ∑_{R ∩ N(u)} b ≤ |R ∩ N(u)|`. With `∑_{R ∩ N(u)} b ≥ |R ∩ N(u)| − #blank` this
contradicts the hypothesis (`fan_exists_chain`). So some duplicate-free chain
`t = x₀, x₁, …, x_k` exists: `x_{i+1}` is the predecessor of `u` on a path `P_i` read from its end
`x_i`, and some path with an end at `x_k` avoids `u`. Execute it *forwards* (`fan_exec`). On `P_0`,
reverse the segment from `x₀` to `x₁` and trade the edge `x₁u` for `x₀u`. The result is a path of
`K + x₀u − x₁u` whose end moves from `x₀` to `x₁`. Read from its other end it is unchanged up
to `u`, so every later chain step remains valid. This includes the case where the same path is
entered again from its other end: the two reversals lie on opposite sides of `u`. Then add `x₁u`
along the shorter chain, by induction. At the last vertex, append `u` to the path avoiding it.
The intermediate substitutions cancel: exactly the edge `tu` is added, and only `b t` and `b u`
change.

**Lemma 3 (`Ach.insert_even`).** Let `S` be independent in `E`, with every `v ∈ S` having
`b v ≥ 1` and at most one blank neighbour. Then any finite even graph `F` on `S` can be inserted
with the same end vector. By strong induction on `|F|`, remove a shortest cycle `C`
(`exists_chordless`: a chord would give a shorter cycle). `F − C` is even
(`even_cycle_degree`). Insert `F − C` by induction, then insert `C` into the graph containing
`F − C`; no pair of vertices of `C` is adjacent there (`Ach.insert_cycle`). For
`C = (a, v, …, z)`, offer `{v, z}` to `a`: the supply is at least `2` and `a` sees at most one
blank. If `z → a` succeeds, do `a → v` and then the chain `v → ⋯ → z` (`Ach.chain`). Each donor
then holds two ends, and the only possible new blank, `z`, is adjacent to no receiver before the
last step. If `v → a` succeeds, do the same on the reversed cycle.

**Types.** Label `U` by `0, …, 5`, with `T` at `0, 2, 3`. A vertex of `X` has *type* `h` if it
misses `h`. Let `n_h` be the number of vertices of type `h`. Then `d(h) = 5 + m − n_h` is even,
and `m` is even (handshake), so every `n_h` is odd. Pick a representative `h'` of each type and
pair up the rest of each type. `F = G[X]` is even since `d_F(x) = d(x) − 5`.

**The core** (`SixCliqueModel`, 12 vertices `0..5, 0'..5'`). Seed edges
`D₀ = {23, 45}`. `0'` and `1'` carry all five spokes. `2', 3', 5'` withhold the spokes to `0` and
to the mate of their omitted vertex in `{2,3}` or `{4,5}`. `4'` withholds the spokes to `1` and
`5`. These 24 edges form the five paths `mpaths`, with core end vector `c1 = (0,0,1,1,1,1 | 1⁶)`.
Each pair `x, y` of type `h` gets the row `x, p, y` with `p = 2` for `h ∈ {0,1}` and `p = 0`
otherwise (`ptc`). Initially every vertex of `X` has one end and sees at most one blank (`0` or
`1`; `seed_rep_blank`), and `X` is independent. Lemma 3 inserts all of `F` (`after_F`).

**Lemma 4 (`pairProg`, `pair_step`).** At a stage with blank clique vertices `h, j` (no common
clique neighbour) and all other vertices positive, a pair `x, y` of type `h` with its seed spoke to
`p` gets its other eight spokes. Let `u, v, w` be the positive clique vertices other than `p`.
Rectangle 1: offer `{x, y} → v` (supply 2, at most one blank). Call the returned donor `x`. Then
`u → x` (no blank neighbour: `x` misses `h`, `xj` is absent), `v → y` (no blank neighbour: `yu` is
absent), and `y → u` (supply 2, at most one blank). Rectangle 2: offer `{x, y} → j`. Call the
returned donor `x`. Then `w → x`, `j → y` (no blank neighbour: `yw` is absent), and `y → w`. The
end vector is restored. An edge `xy` and any edges from `x, y` to representatives are allowed
throughout (`cup14`). The four leaves of each type are checked by kernel evaluation (`pair_ok`).

**Stages.** Stage 0 has blanks `{0,1}` and processes types `0, 1` with `(j,u,v,w) = (1|0, 3,4,5)`
and `p = 2`; then `2 → 0, 3 → 1`. Stage 1 has blanks `{2,3}` and processes types `2, 3` with
`(j,u,v,w) = (3|2, 1,4,5)` and `p = 0`; then the eight transfers
`0→2', 2'→3, 4→1, 1→0, 3'→2, 3→0, 0→3', 5→3`. Stage 2 has blanks `{4,5}` and processes
types `4, 5` with `(j,u,v,w) = (5|4, 1,2,3)` and `p = 0`; then the six transfers
`5'→0, 0→4, 4→5', 1→4', 4'→5, 5→2`. Every single transfer is checked against the upper bound in
which all representative pairs are adjacent (`seg*_ok`). This is the paper's (supply, blanks) table.
The core ends become `(1,0,2,1,0,0 | 1⁶)`. The unused clique edges `05, 15, 12, 24, 34` form the
path `(0,5,1,2,4,3)`, which gives `(2,0,2,2,0,0 | 1⁶)`. Every clique edge and every true
representative spoke is used exactly once (`core_sound`, `core_complete`, `final_edges`).

**Transport.** Every finite check concerns a model (`Fin 12`, or `Fin 14` with the pair). The
insertion-schedule lemma `Prog.sound` replays it on `G`. Real blank neighbours of a model receiver
are model vertices, because all other vertices keep one end throughout. Their adjacency is
bounded by the model's allowed relation (`core_mem`, `nc_mem`).

## The triple rectangle of Corollary 5 (audit F11; not formalized here)

For a pair `x, y` with the same clique neighbourhood `A = {p, q, r}`, choose a stage whose blanks
`h, j` meet `A` at most once and seed `x, p, y` with `p` positive. If `q, r` are both positive,
then `x, y` never see a blank clique vertex, and rectangle 1 with `(u, v) = (q, r)` applies. The
supply and blank counts are `(2, ≤1), (1, 0), (2, 0), (2, ≤1)`. If one of them is blank, say
`r = j`, use rectangle 2 with `(w, j) = (q, r)`. The counts are `(2, ≤1), (1, 0), (1, 0), (2, ≤1)`:
`x` and `y` do not see `h ∉ A`, and `yq` is absent when `q` is blank.

## Formal statement

`six_clique_prescribed_ends` is the theorem for any `[Fintype V]` graph with decidable
adjacency. The degree parity hypotheses are stated with `G.degree`, and the conclusion gives
`2 · |D| = |X| + 6` together with the exact end vector. Everything is proved, with standard axioms
only. Kernel `decide` is used for the finite checks of the model.
-/

open SimpleGraph

namespace Gallai

universe u

/-- A finite set of even size is the vertex set of a list of disjoint pairs. -/
theorem exists_pairing {V : Type u} [DecidableEq V] :
    ∀ (n : ℕ) (s : Finset V), s.card = n → Even n →
      ∃ L : List (V × V), (L.flatMap (fun p => [p.1, p.2])).Nodup ∧
        ∀ v, v ∈ L.flatMap (fun p => [p.1, p.2]) ↔ v ∈ s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hs hn
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact ⟨[], by simp, by simp⟩
  · have hpos : 0 < n := hs ▸ Finset.card_pos.mpr ⟨a, ha⟩
    obtain ⟨k, hk⟩ := hn
    have h1 : (s.erase a).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem ha]
      omega
    obtain ⟨b, hb⟩ := h1
    have hba : b ≠ a := Finset.ne_of_mem_erase hb
    have hbs : b ∈ s := Finset.mem_of_mem_erase hb
    have hcard : ((s.erase a).erase b).card = n - 2 := by
      rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha, hs]
      omega
    obtain ⟨L, hL, hLs⟩ := ih (n - 2) (by omega) _ hcard ⟨k - 1, by omega⟩
    refine ⟨(a, b) :: L, ?_, ?_⟩
    · rw [List.flatMap_cons, List.nodup_append]
      refine ⟨by simp [Ne.symm hba], hL, ?_⟩
      intro x hx y hy hxy
      subst hxy
      rw [hLs] at hy
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hy) rfl
      · exact Finset.ne_of_mem_erase hy rfl
    · intro v
      rw [List.flatMap_cons, List.mem_append, hLs]
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
        Finset.mem_erase]
      constructor
      · rintro ((rfl | rfl) | ⟨-, -, h⟩)
        · exact ha
        · exact hbs
        · exact h
      · intro hv
        by_cases h1 : v = a
        · exact Or.inl (Or.inl h1)
        · by_cases h2 : v = b
          · exact Or.inl (Or.inr h2)
          · exact Or.inr ⟨h2, h1, hv⟩

section theorem1

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Theorem 1** (six-clique paper): prescribed ends at a clique of six even vertices. -/
theorem six_clique_prescribed_ends (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (hU : U.card = 6) (hclique : ∀ a ∈ U, ∀ b ∈ U, a ≠ b → G.Adj a b)
    (heven : ∀ u ∈ U, Even (G.degree u)) (hodd : ∀ x ∉ U, Odd (G.degree x))
    (hfive : ∀ x ∉ U, (U.filter (G.Adj x)).card = 5)
    (T : Finset V) (hTU : T ⊆ U) (hT : T.card = 3) :
    ∃ D : PathDecomp G, 2 * D.size = Uᶜ.card + 6 ∧
      ∀ v, D.ends v = if v ∈ T then 2 else if v ∈ U then 0 else 1 := by
  classical
  /- 1. Label the clique, with `T` at `0, 2, 3`. -/
  obtain ⟨t0, t2, t3, h02, h03, h23, hTe⟩ := Finset.card_eq_three.mp hT
  have hUT : (U \ T).card = 3 := by rw [Finset.card_sdiff_of_subset hTU, hU, hT]
  obtain ⟨t1, t4, t5, h14, h15, h45, hUTe⟩ := Finset.card_eq_three.mp hUT
  let lab : Fin 6 → V := ![t0, t1, t2, t3, t4, t5]
  have hinT : ∀ x, x ∈ T ↔ x = t0 ∨ x = t2 ∨ x = t3 := by intro x; rw [hTe]; simp
  have hinUT : ∀ x, x ∈ U \ T ↔ x = t1 ∨ x = t4 ∨ x = t5 := by intro x; rw [hUTe]; simp
  have hT' : ∀ x, x = t1 ∨ x = t4 ∨ x = t5 → x ∉ T := fun x hx => (Finset.mem_sdiff.mp
    ((hinUT x).mpr hx)).2
  have hcross : ∀ a b, (a = t0 ∨ a = t2 ∨ a = t3) → (b = t1 ∨ b = t4 ∨ b = t5) → a ≠ b := by
    intro a b ha hb hab
    subst hab
    exact hT' a hb ((hinT a).mpr ha)
  have c01 := hcross t0 t1 (by simp) (by simp)
  have c04 := hcross t0 t4 (by simp) (by simp)
  have c05 := hcross t0 t5 (by simp) (by simp)
  have c21 := hcross t2 t1 (by simp) (by simp)
  have c24 := hcross t2 t4 (by simp) (by simp)
  have c25 := hcross t2 t5 (by simp) (by simp)
  have c31 := hcross t3 t1 (by simp) (by simp)
  have c34 := hcross t3 t4 (by simp) (by simp)
  have c35 := hcross t3 t5 (by simp) (by simp)
  have hlabT : ∀ k : Fin 6, lab k ∈ T ↔ (k.val = 0 ∨ k.val = 2 ∨ k.val = 3) := by
    intro k
    fin_cases k <;> simp [lab, hinT, h02, h03, h23, Ne.symm c01, Ne.symm c04, Ne.symm c05,
      Ne.symm c21, Ne.symm c24, Ne.symm c25, Ne.symm c31, Ne.symm c34, Ne.symm c35]
  have hlabU : ∀ k : Fin 6, lab k ∈ U := by
    intro k
    fin_cases k
    · exact hTU ((hinT _).mpr (Or.inl rfl))
    · exact (Finset.mem_sdiff.mp ((hinUT _).mpr (Or.inl rfl))).1
    · exact hTU ((hinT _).mpr (Or.inr (Or.inl rfl)))
    · exact hTU ((hinT _).mpr (Or.inr (Or.inr rfl)))
    · exact (Finset.mem_sdiff.mp ((hinUT _).mpr (Or.inr (Or.inl rfl)))).1
    · exact (Finset.mem_sdiff.mp ((hinUT _).mpr (Or.inr (Or.inr rfl)))).1
  have hlab_inj : Function.Injective lab := by
    rw [← List.nodup_ofFn]
    have : List.ofFn lab = [t0, t1, t2, t3, t4, t5] := by
      simp [lab, List.ofFn_succ]
    rw [this]
    simp [h02, h03, h23, h14, h15, h45, c01, c04, c05, c21, c24, c25, c31, c34, c35,
      Ne.symm c21, Ne.symm c31]
  have hUlab : ∀ x ∈ U, ∃ k, lab k = x := by
    intro x hx
    by_cases hxT : x ∈ T
    · rcases (hinT x).mp hxT with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    · rcases (hinUT x).mp (Finset.mem_sdiff.mpr ⟨hx, hxT⟩) with rfl | rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
  /- 2. Types: every exterior vertex misses exactly one clique vertex. -/
  have htype : ∀ x ∉ U, ∃ h : Fin 6, ∀ k, ¬ G.Adj x (lab k) ↔ k = h := by
    intro x hx
    have himg : U.filter (G.Adj x) = (Finset.univ.filter (fun k => G.Adj x (lab k))).image lab := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hw, hadj⟩
        obtain ⟨k, rfl⟩ := hUlab w hw
        exact ⟨k, hadj, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨hlabU k, hk⟩
    have h5 := hfive x hx
    rw [himg, Finset.card_image_of_injective _ hlab_inj] at h5
    have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun k : Fin 6 => G.Adj x (lab k))
    rw [h5, Finset.card_univ, Fintype.card_fin] at hsum
    obtain ⟨h, hh⟩ := Finset.card_eq_one.mp (show (Finset.univ.filter
      (fun k : Fin 6 => ¬ G.Adj x (lab k))).card = 1 by omega)
    refine ⟨h, fun k => ?_⟩
    have := congrArg (k ∈ ·) hh
    simpa using this
  let ty : V → Fin 6 := fun x => if hx : x ∉ U then (htype x hx).choose else 0
  have hty : ∀ x ∉ U, ∀ k, G.Adj x (lab k) ↔ k ≠ ty x := by
    intro x hx k
    have := (htype x hx).choose_spec k
    simp only [ty, hx, not_false_eq_true, dite_true]
    constructor
    · intro hadj hk; exact (this.mpr hk) hadj
    · intro hk; by_contra hn; exact hk (this.mp hn)
  /- 3. Parity: `m` is even and every type count is odd. -/
  have hm : Even Uᶜ.card := by
    have h := G.even_card_odd_degree_vertices
    have : Finset.univ.filter (fun v => Odd (G.degree v)) = Uᶜ := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
      constructor
      · intro hv hvU
        exact (Nat.not_even_iff_odd.mpr hv) (heven v hvU)
      · exact hodd v
    rwa [this] at h
  have hdeg : ∀ v, G.degree v = (U.filter (G.Adj v)).card + (Uᶜ.filter (G.Adj v)).card := by
    intro v
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter,
      ← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (G.Adj v)) (· ∈ U)]
    congr 1
    · congr 1; ext w; simp [and_comm]
    · congr 1; ext w; simp [and_comm]
  have hnodd : ∀ h : Fin 6, Odd (Uᶜ.filter (fun x => ty x = h)).card := by
    intro h
    have h1 : U.filter (G.Adj (lab h)) = U.erase (lab h) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hw, hadj⟩; exact ⟨fun h' => hadj.ne h'.symm, hw⟩
      · rintro ⟨hne, hw⟩; exact ⟨hw, hclique _ (hlabU h) _ hw (Ne.symm hne)⟩
    have h2 : Uᶜ.filter (G.Adj (lab h)) = Uᶜ.filter (fun x => ¬ ty x = h) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_compl]
      constructor
      · rintro ⟨hw, hadj⟩
        exact ⟨hw, fun h' => (hty w hw h).mp hadj.symm h'.symm⟩
      · rintro ⟨hw, hne⟩
        exact ⟨hw, ((hty w hw h).mpr (Ne.symm hne)).symm⟩
    have h3 := Finset.card_filter_add_card_filter_not (s := Uᶜ) (fun x => ty x = h)
    have hd := hdeg (lab h)
    rw [h1, h2, Finset.card_erase_of_mem (hlabU h), hU] at hd
    have he := heven _ (hlabU h)
    rw [hd] at he
    obtain ⟨a, ha⟩ := he
    obtain ⟨b, hb⟩ := hm
    refine ⟨((Uᶜ.filter (fun x => ty x = h)).card - 1) / 2, ?_⟩
    omega
  /- 4. Representatives. -/
  have hrep : ∀ h : Fin 6, ∃ x, x ∉ U ∧ ty x = h := by
    intro h
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (hnodd h).pos
    simp only [Finset.mem_filter, Finset.mem_compl] at hx
    exact ⟨x, hx⟩
  let rep : Fin 6 → V := fun h => (hrep h).choose
  have hrepU : ∀ h, rep h ∉ U := fun h => (hrep h).choose_spec.1
  have hrepty : ∀ h, ty (rep h) = h := fun h => (hrep h).choose_spec.2
  let ι : Fin 12 → V := fun i => if hi : i.val < 6 then lab ⟨i.val, hi⟩ else rep ⟨i.val - 6, by omega⟩
  have hι_lt : ∀ i : Fin 12, (hi : i.val < 6) → ι i = lab ⟨i.val, hi⟩ := by
    intro i hi; simp [ι, hi]
  have hι_ge : ∀ i : Fin 12, (hi : ¬ i.val < 6) → ι i = rep ⟨i.val - 6, by omega⟩ := by
    intro i hi; simp [ι, hi]
  have hι_inj : Function.Injective ι := by
    intro i j hij
    by_cases hi : i.val < 6 <;> by_cases hj : j.val < 6
    · rw [hι_lt i hi, hι_lt j hj] at hij
      exact Fin.ext (by simpa using hlab_inj hij)
    · rw [hι_lt i hi, hι_ge j hj] at hij
      exact absurd (hij ▸ hlabU _) (hrepU _)
    · rw [hι_ge i hi, hι_lt j hj] at hij
      exact absurd (hij.symm ▸ hlabU _) (hrepU _)
    · rw [hι_ge i hi, hι_ge j hj] at hij
      have := congrArg ty hij
      rw [hrepty, hrepty] at this
      have := congrArg Fin.val this
      simp only at this
      exact Fin.ext (by omega)
  have hcl : ∀ v, (∃ i : Fin 12, i.val < 6 ∧ ι i = v) ↔ v ∈ U := by
    intro v
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [hι_lt i hi]; exact hlabU _
    · intro hv
      obtain ⟨k, rfl⟩ := hUlab v hv
      exact ⟨⟨k.val, by omega⟩, k.isLt, by rw [hι_lt _ k.isLt]⟩
  /- 5. Pairs. -/
  have hpair : ∀ h : Fin 6, ∃ L : List (V × V), (L.flatMap (fun p => [p.1, p.2])).Nodup ∧
      ∀ v, v ∈ L.flatMap (fun p => [p.1, p.2]) ↔
        v ∈ (Uᶜ.filter (fun x => ty x = h)).erase (rep h) := by
    intro h
    have hmem : rep h ∈ Uᶜ.filter (fun x => ty x = h) := by
      simp [hrepU h, hrepty h]
    obtain ⟨k, hk⟩ := hnodd h
    exact exists_pairing _ _ rfl ⟨k, by rw [Finset.card_erase_of_mem hmem]; omega⟩
  let Lh : Fin 6 → List (V × V) := fun h => (hpair h).choose
  have hLh_nd : ∀ h, ((Lh h).flatMap (fun p => [p.1, p.2])).Nodup :=
    fun h => (hpair h).choose_spec.1
  have hLh_mem : ∀ h v, v ∈ (Lh h).flatMap (fun p => [p.1, p.2]) ↔
      v ∈ (Uᶜ.filter (fun x => ty x = h)).erase (rep h) := fun h => (hpair h).choose_spec.2
  let prs : List (V × V) := (List.finRange 6).flatMap Lh
  have hprs_vert : prs.flatMap (fun p => [p.1, p.2]) =
      (List.finRange 6).flatMap (fun h => (Lh h).flatMap (fun p => [p.1, p.2])) :=
    List.flatMap_assoc
  have hvert : ∀ v, v ∈ prs.flatMap (fun p => [p.1, p.2]) ↔
      v ∉ U ∧ v ≠ rep (ty v) := by
    intro v
    rw [hprs_vert, List.mem_flatMap]
    constructor
    · rintro ⟨h, -, hv⟩
      rw [hLh_mem] at hv
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_compl] at hv
      obtain ⟨hne, hvU, rfl⟩ := hv
      exact ⟨hvU, hne⟩
    · rintro ⟨hvU, hne⟩
      refine ⟨ty v, List.mem_finRange _, ?_⟩
      rw [hLh_mem]
      simp [hvU, hne]
  have hrange : ∀ v, v ∉ Set.range ι ↔ v ∉ U ∧ v ≠ rep (ty v) := by
    intro v
    constructor
    · intro hv
      refine ⟨fun hvU => hv ?_, fun h => hv ?_⟩
      · obtain ⟨i, -, hi⟩ := (hcl v).mpr hvU
        exact ⟨i, hi⟩
      · refine ⟨⟨(ty v).val + 6, by omega⟩, ?_⟩
        rw [hι_ge _ (by simp)]
        exact (congrArg rep (Fin.ext (by simp))).trans h.symm
    · rintro ⟨hvU, hne⟩ ⟨i, rfl⟩
      by_cases hi : i.val < 6
      · rw [hι_lt i hi] at hvU; exact hvU (hlabU _)
      · rw [hι_ge i hi] at hne
        exact hne (by rw [hrepty])
  have hpr : ∀ p ∈ prs, p.1 ∈ prs.flatMap (fun p => [p.1, p.2]) ∧
      p.2 ∈ prs.flatMap (fun p => [p.1, p.2]) ∧ ty p.1 = ty p.2 := by
    intro p hp
    obtain ⟨h, -, hph⟩ := List.mem_flatMap.mp hp
    have h1 : p.1 ∈ (Lh h).flatMap (fun p => [p.1, p.2]) :=
      List.mem_flatMap.mpr ⟨p, hph, by simp⟩
    have h2 : p.2 ∈ (Lh h).flatMap (fun p => [p.1, p.2]) :=
      List.mem_flatMap.mpr ⟨p, hph, by simp⟩
    refine ⟨List.mem_flatMap.mpr ⟨p, hp, by simp⟩, List.mem_flatMap.mpr ⟨p, hp, by simp⟩, ?_⟩
    rw [hLh_mem] at h1 h2
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_compl] at h1 h2
    rw [h1.2.2, h2.2.2]
  /- 6. Assemble the labelled data and run the construction. -/
  let S : SixData V :=
    { G := G
      ι := ι
      inj := hι_inj
      ty := ty
      prs := prs
      adj_cc := by
        intro i j hi hj hij
        rw [hι_lt i hi, hι_lt j hj]
        refine hclique _ (hlabU _) _ (hlabU _) (fun h => hij ?_)
        exact Fin.ext (by simpa using hlab_inj h)
      adj_ext := by
        intro v hv k hk
        have hvU : v ∉ U := fun h => hv ((hcl v).mpr h)
        rw [hι_lt k hk, hty v hvU]
        constructor
        · intro h h'; exact h (Fin.ext h')
        · intro h h'; exact h (congrArg Fin.val h')
      ty_rep := by
        intro i hi
        rw [hι_ge i (by omega), hrepty]
      ext_even := by
        intro v hv
        have hvU : v ∉ U := fun h => hv ((hcl v).mpr h)
        have h1 : {w | G.Adj v w ∧ ¬ ∃ i : Fin 12, i.val < 6 ∧ ι i = w}.ncard =
            (Uᶜ.filter (G.Adj v)).card := by
          rw [← Set.ncard_coe_finset]
          congr 1
          ext w
          simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_compl, hcl]
          exact and_comm
        rw [h1]
        have hd := hdeg v
        rw [hfive v hvU] at hd
        have ho := hodd v hvU
        rw [hd] at ho
        obtain ⟨a, ha⟩ := ho
        exact ⟨a - 2, by omega⟩
      prs_nc := by
        intro p hp
        obtain ⟨h1, h2, h3⟩ := hpr p hp
        rw [hvert] at h1 h2
        exact ⟨(hrange _).mpr h1, (hrange _).mpr h2, h3⟩
      prs_nodup := by
        rw [hprs_vert, List.nodup_flatMap]
        refine ⟨fun h _ => hLh_nd h, ?_⟩
        refine List.Pairwise.imp_of_mem ?_ (List.nodup_finRange 6)
        intro a b _ _ hab x hxa hxb
        rw [hLh_mem] at hxa hxb
        simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_compl] at hxa hxb
        exact hab (hxa.2.2.symm.trans hxb.2.2)
      prs_cover := by
        intro v hv
        have := (hvert v).mpr ((hrange v).mp hv)
        obtain ⟨p, hp, hvp⟩ := List.mem_flatMap.mp this
        refine ⟨p, hp, ?_⟩
        simpa using hvp }
  obtain ⟨D, hD⟩ := S.main
  have hends : ∀ v, D.ends v = if v ∈ T then 2 else if v ∈ U then 0 else 1 := by
    intro v
    rw [hD v]
    by_cases hv : v ∈ Set.range ι
    · obtain ⟨a, rfl⟩ := hv
      rw [SixData.B_iota (S := S), SixModel.cfin_spec]
      by_cases ha : a.val < 6
      · rw [hι_lt a ha]
        by_cases hT1 : lab ⟨a.val, ha⟩ ∈ T
        · have h1 := (hlabT _).mp hT1
          simp only at h1
          rw [if_pos hT1, if_pos h1]
        · have h1 := mt (hlabT _).mpr hT1
          simp only at h1
          rw [if_neg hT1, if_pos (hlabU _), if_neg h1, if_pos ha]
      · have hU' : ι a ∉ U := by rw [hι_ge a ha]; exact hrepU _
        have hT'' : ι a ∉ T := fun h => hU' (hTU h)
        rw [if_neg hT'', if_neg hU']
        simp only [ha, ite_false]
        split_ifs with h <;> omega
    · rw [SixData.B_nc (S := S) _ hv]
      have hvU := ((hrange v).mp hv).1
      rw [if_neg (fun h => hvU (hTU h)), if_neg hvU]
  refine ⟨D, ?_, hends⟩
  have hsum := D.sum_ends
  have hfun : ∀ v, D.ends v = 2 * (if v ∈ T then 1 else 0) + (if v ∈ Uᶜ then 1 else 0) := by
    intro v
    rw [hends v]
    by_cases hvT : v ∈ T
    · simp [hvT, hTU hvT]
    · by_cases hvU : v ∈ U <;> simp [hvT, hvU]
  simp only [hfun, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole,
    Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id] at hsum
  rw [hT] at hsum
  omega

end theorem1

end Gallai
