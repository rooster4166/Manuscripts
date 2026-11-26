import GallaiLean.Insertion

/-!
# Inserting an even graph by chordless cycles (six-clique paper, Lemma 3)

**Lemma 3.** Let `S` be a set of vertices that is independent in the present graph `E`, such that
every `v ∈ S` has at least one end and at most one blank neighbour. Then every finite even graph
`F` on `S` can be inserted, preserving the whole end vector (`Ach.insert_even`).

Proof, as formalized:

* `Ach.chain`: along a duplicate-free list `x, c₁, …, c_k, z`, transfers `x → c₁ → ⋯ → c_k → z`
  move one end from `x` to `z`, provided `x` starts with two ends, the receivers have at least
  one end (except possibly `z`), no edge of `E` joins a receiver to a list vertex, and each
  receiver has at most one blank neighbour. Each donor holds two ends when it gives one away,
  so no new blank vertex appears among the neighbours of later receivers.
* `Ach.insert_cycle`: for a cycle `a, v, …, z` none of whose vertex pairs is an edge of `E`,
  offer `{v, z}` to `a` (supply ≥ 2 against ≤ 1 blank neighbour). If `z → a` succeeds, use
  `a → v` and then the chain from `v` back to `z` (`Ach.cycle_of_last`); if `v → a` succeeds,
  do the same on the reversed cycle.
* `exists_cyc`: an even graph with an edge contains a cycle (extend a path at its head until the
  head's second edge returns to the path). `exists_chordless`: a shortest cycle has no chord.
* `even_cycle_degree`: every vertex meets an even number of cycle edges, so `F` minus a cycle is
  even. Strong induction on `|F|` removes a shortest cycle, inserts the rest by induction, and then
  inserts the cycle into the graph containing the rest; the cycle has no chord there.
-/

open SimpleGraph

namespace Gallai

universe u

variable {V : Type u} [DecidableEq V]

theorem mv_mv {W : Type*} [DecidableEq W] (b : W → ℕ) {x c z : W} (hxc : x ≠ c) (hxz : x ≠ z)
    (hcz : c ≠ z) (hx : 1 ≤ b x) : mv (mv b x c) c z = mv b x z := by
  funext w
  unfold mv
  by_cases hwz : w = z
  · subst hwz; simp [Ne.symm hcz, Ne.symm hxz]
  · by_cases hwc : w = c
    · subst hwc; simp [hwz, Ne.symm hxc]
    · by_cases hwx : w = x
      · subst hwx; simp [hwz, hwc]
      · simp [hwz, hwc, hwx]

section cycles

variable [Fintype V]

/-- **Chain of transfers** `x → c₁ → ⋯ → c_k → z`. -/
theorem Ach.chain : ∀ (m : List V) (x z : V) (E : Set (Sym2 V)) (b : V → ℕ),
    Ach E b → (x :: (m ++ [z])).Nodup → 2 ≤ b x → (∀ c ∈ m, 1 ≤ b c) →
    (∀ c ∈ m ++ [z], ∀ d ∈ x :: (m ++ [z]), s(c, d) ∉ E) →
    (∀ c ∈ m ++ [z], blankNbrs E b c ≤ 1) →
    Ach (E ∪ {e | e ∈ lEdges x (m ++ [z])}) (mv b x z)
  | [], x, z, E, b, h, hnd, hx, _, hno, hbl => by
    have hxz : x ≠ z := by simpa using hnd
    have h1 := h.transfer hxz (fun h' => hno z (by simp) x (by simp) (by rwa [Sym2.eq_swap]))
      (by have := hbl z (by simp); omega)
    refine h1.congr ?_ (fun _ => rfl)
    ext e
    simp [or_comm]
  | c :: m, x, z, E, b, h, hnd, hx, hpos, hno, hbl => by
    have hnd' : (c :: (m ++ [z])).Nodup := (List.nodup_cons.mp hnd).2
    have hx' : x ∉ c :: (m ++ [z]) := (List.nodup_cons.mp hnd).1
    have hc' : c ∉ m ++ [z] := (List.nodup_cons.mp hnd').1
    have hxc : x ≠ c := fun h => hx' (h ▸ List.mem_cons_self)
    have hxz : x ≠ z := fun h => hx' (h ▸ by simp)
    have hcz : c ≠ z := fun h => hc' (h ▸ by simp)
    have h1 := h.transfer hxc
      (fun h' => hno c (by simp) x (by simp) (by rwa [Sym2.eq_swap]))
      (by have := hbl c (by simp); omega)
    have h2 := Ach.chain m c z (insert s(x, c) E) (mv b x c) h1 hnd'
      (by rw [mv_apply_recv]; have := hpos c (by simp); omega)
      (by
        intro c' hc'm
        have h1 : c' ≠ x := fun h => hx' (h ▸ by simp [hc'm])
        have h2 : c' ≠ c := fun h => hc' (h ▸ by simp [hc'm])
        rw [mv_apply_other _ h1 h2]
        exact hpos c' (by simp [hc'm]))
      (by
        intro c' hc'' d hd hmem
        rw [Set.mem_insert_iff] at hmem
        rcases hmem with hmem | hmem
        · rcases Sym2.eq_iff.mp hmem with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · exact hx' (List.mem_cons_of_mem _ hc'')
          · exact hc' hc''
        · exact hno c' (List.mem_cons_of_mem _ hc'') d (List.mem_cons_of_mem _ hd) hmem)
      (by
        intro c' hc''
        refine (blankNbrs_mono ?_).trans (hbl c' (List.mem_cons_of_mem _ hc''))
        intro w hw hwc hw0
        rw [Set.mem_insert_iff] at hw
        rcases hw with hw | hw
        · rcases Sym2.eq_iff.mp hw with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · exact absurd (List.mem_cons_of_mem _ hc'') hx'
          · exact absurd hc'' hc'
        · refine ⟨hw, ?_⟩
          by_cases h1 : w = c
          · subst h1; rw [mv_apply_recv] at hw0; omega
          · by_cases h2 : w = x
            · subst h2; rw [mv_apply_donor _ hxc] at hw0; omega
            · rwa [mv_apply_other _ h2 h1] at hw0)
    refine h2.congr ?_ (fun w => congrFun (mv_mv b hxc hxz hcz (by omega)) w)
    ext e
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_ofPred_eq, List.cons_append,
      lEdges_cons, List.mem_cons]
    tauto

/-- Inserting a cycle `a, v, …, z` after `z` has given an end to `a`. -/
theorem Ach.cycle_of_last (a v : V) (m : List V) (z : V) {E : Set (Sym2 V)} {b : V → ℕ}
    (hnd : (a :: v :: (m ++ [z])).Nodup)
    (hind : ∀ x ∈ a :: v :: (m ++ [z]), ∀ y ∈ a :: v :: (m ++ [z]), s(x, y) ∉ E)
    (hpos : ∀ x ∈ a :: v :: (m ++ [z]), 1 ≤ b x)
    (hbl : ∀ x ∈ a :: v :: (m ++ [z]), blankNbrs E b x ≤ 1)
    (h : Ach (insert s(z, a) E) (mv b z a)) :
    Ach (E ∪ {e | e ∈ lEdges a (v :: (m ++ [z]) ++ [a])}) b := by
  have ha : a ∉ v :: (m ++ [z]) := (List.nodup_cons.mp hnd).1
  have hnd' : (v :: (m ++ [z])).Nodup := (List.nodup_cons.mp hnd).2
  have hv : v ∉ m ++ [z] := (List.nodup_cons.mp hnd').1
  have hav : a ≠ v := fun h => ha (h ▸ List.mem_cons_self)
  have haz : a ≠ z := fun h => ha (h ▸ by simp)
  have hvz : v ≠ z := fun h => hv (h ▸ by simp)
  have hmz : ∀ c ∈ m, c ≠ z := by
    intro c hc h
    have := (List.nodup_cons.mp hnd').2
    rw [List.nodup_append] at this
    exact this.2.2 c hc z (by simp) h
  -- the transfer `a → v`
  have h2 := h.transfer hav
    (by
      rw [Set.mem_insert_iff]
      rintro (h' | h')
      · rcases Sym2.eq_iff.mp h' with ⟨h1, -⟩ | ⟨-, h1⟩
        · exact haz h1
        · exact hvz h1
      · exact hind a (by simp) v (by simp) h')
    (by
      rw [mv_apply_recv]
      refine Nat.lt_of_le_of_lt ((blankNbrs_mono ?_).trans (hbl v (by simp)))
        (by have := hpos a (by simp); omega)
      intro w hw hwv hw0
      rw [Set.mem_insert_iff] at hw
      rcases hw with hw | hw
      · rcases Sym2.eq_iff.mp hw with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact absurd h1 hvz
        · exact absurd h1.symm hav
      · refine ⟨hw, ?_⟩
        unfold mv at hw0
        by_cases h1 : w = a
        · simp [h1] at hw0
        · by_cases h2 : w = z
          · subst h2; exact absurd hw (hind v (by simp) w (by simp))
          · simpa [h1, h2] using hw0)
  -- the chain `v → ⋯ → z`
  have hb2v : mv (mv b z a) a v v = b v + 1 := by
    rw [mv_apply_recv, mv_apply_other _ hvz (Ne.symm hav)]
  have hb2a : mv (mv b z a) a v a = b a := by
    rw [mv_apply_donor _ hav, mv_apply_recv]; omega
  have h3 := Ach.chain m v z _ _ h2 hnd'
    (by rw [hb2v]; have := hpos v (by simp); omega)
    (by
      intro c hc
      have h1 : c ≠ v := fun h => hv (h ▸ by simp [hc])
      have h2 : c ≠ a := fun h => ha (h ▸ by simp [hc])
      rw [mv_apply_other _ h2 h1, mv_apply_other _ (hmz c hc) h2]
      exact hpos c (by simp [hc]))
    (by
      intro c hc d hd hmem
      simp only [Set.mem_insert_iff] at hmem
      rcases hmem with hmem | hmem | hmem
      · rcases Sym2.eq_iff.mp hmem with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact ha (List.mem_cons_of_mem _ hc)
        · exact hv hc
      · rcases Sym2.eq_iff.mp hmem with ⟨-, rfl⟩ | ⟨rfl, -⟩
        · exact ha hd
        · exact ha (List.mem_cons_of_mem _ hc)
      · exact hind c (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)) d
          (List.mem_cons_of_mem _ hd) hmem)
    (by
      intro c hc
      have hca : c ≠ a := fun h => ha (h ▸ List.mem_cons_of_mem _ hc)
      have hcv : c ≠ v := fun h => hv (h ▸ hc)
      refine (blankNbrs_mono ?_).trans (hbl c (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)))
      intro w hw hwc hw0
      simp only [Set.mem_insert_iff] at hw
      rcases hw with hw | hw | hw
      · rcases Sym2.eq_iff.mp hw with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact absurd h1 hca
        · exact absurd h1 hcv
      · rcases Sym2.eq_iff.mp hw with ⟨-, h1⟩ | ⟨h1, -⟩
        · subst h1; rw [hb2a] at hw0; have := hpos w (by simp); omega
        · exact absurd h1 hca
      · refine ⟨hw, ?_⟩
        by_cases h1 : w = v
        · subst h1; rw [hb2v] at hw0; omega
        · by_cases h2 : w = a
          · subst h2; rw [hb2a] at hw0; exact hw0
          · by_cases h3 : w = z
            · subst h3
              exact absurd hw (hind c (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)) w
                (by simp))
            · rwa [mv_apply_other _ h2 h1, mv_apply_other _ h3 h2] at hw0)
  refine h3.congr ?_ ?_
  · ext e
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_ofPred_eq, List.cons_append,
      lEdges_cons, List.mem_cons, lEdges_append, lastOf_concat, List.mem_append, lEdges_nil,
      List.not_mem_nil, or_false]
    tauto
  · intro w
    rw [mv_mv (mv b z a) hav haz hvz (by rw [mv_apply_recv]; omega)]
    by_cases h1 : w = z
    · subst h1
      rw [mv_apply_recv, mv_apply_donor _ (Ne.symm haz)]
      have := hpos w (by simp)
      omega
    · by_cases h2 : w = a
      · subst h2; rw [mv_apply_donor _ haz, mv_apply_recv]; omega
      · rw [mv_apply_other _ h2 h1, mv_apply_other _ h1 h2]

theorem mem_lEdges_of_reverse {W : Type*} {a b : W} {l l' : List W}
    (h : a :: l' = (b :: l).reverse) {e : Sym2 W} : e ∈ lEdges a l' ↔ e ∈ lEdges b l := by
  rw [mem_lEdges_iff, mem_lEdges_iff, h]
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    refine ⟨y, x, ?_, Sym2.eq_swap⟩
    rw [← List.reverse_infix]
    simpa using hxy
  · rintro ⟨x, y, hxy, rfl⟩
    refine ⟨y, x, ?_, Sym2.eq_swap⟩
    rw [← List.reverse_infix] at hxy
    simpa using hxy

/-- **Inserting a cycle** `a :: l` (closing edge back to `a`) none of whose vertex pairs is
present, every vertex having an end and at most one blank neighbour. -/
theorem Ach.insert_cycle (a : V) (l : List V) (hl : 2 ≤ l.length) {E : Set (Sym2 V)}
    {b : V → ℕ} (hnd : (a :: l).Nodup) (hind : ∀ x ∈ a :: l, ∀ y ∈ a :: l, s(x, y) ∉ E)
    (hpos : ∀ x ∈ a :: l, 1 ≤ b x) (hbl : ∀ x ∈ a :: l, blankNbrs E b x ≤ 1) (h : Ach E b) :
    Ach (E ∪ {e | e ∈ lEdges a (l ++ [a])}) b := by
  obtain ⟨v, l₁, rfl⟩ : ∃ v l₁, l = v :: l₁ := by
    cases l with
    | nil => simp at hl
    | cons v l₁ => exact ⟨v, l₁, rfl⟩
  obtain ⟨m, z, rfl⟩ : ∃ m z, l₁ = m ++ [z] := by
    rcases List.eq_nil_or_concat' l₁ with h' | ⟨m, z, h'⟩
    · subst h'; simp at hl
    · exact ⟨m, z, h'⟩
  have ha : a ∉ v :: (m ++ [z]) := (List.nodup_cons.mp hnd).1
  have hv : v ∉ m ++ [z] := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
  have hvz : v ≠ z := fun h => hv (h ▸ by simp)
  have haT : a ∉ ({v, z} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => ha (h ▸ List.mem_cons_self), fun h => ha (h ▸ by simp)⟩
  obtain ⟨t, ht, -, h'⟩ := h.grouped a {v, z} haT
    (by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hind t (by simp) a (by simp)
      · exact hind t (by simp) a (by simp))
    (by
      rw [Finset.sum_pair hvz]
      have := hbl a (by simp)
      have := hpos v (by simp)
      have := hpos z (by simp)
      omega)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl
  · -- `v → a`: use the reversed cycle `a, z, …, v`
    have e1 : z :: (m.reverse ++ [t]) = (t :: (m ++ [z])).reverse := by simp
    have hperm : ∀ x, x ∈ a :: z :: (m.reverse ++ [t]) ↔ x ∈ a :: t :: (m ++ [z]) := by
      intro x
      rw [e1, List.mem_cons, List.mem_reverse, ← List.mem_cons]
    have hnd' : (a :: z :: (m.reverse ++ [t])).Nodup := by
      rw [e1, List.nodup_cons, List.mem_reverse, List.nodup_reverse]
      exact List.nodup_cons.mp hnd
    have h3 := Ach.cycle_of_last a z m.reverse t hnd'
      (fun x hx y hy => hind x ((hperm x).mp hx) y ((hperm y).mp hy))
      (fun x hx => hpos x ((hperm x).mp hx)) (fun x hx => hbl x ((hperm x).mp hx)) h'
    refine h3.congr ?_ (fun _ => rfl)
    ext e
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    rw [mem_lEdges_of_reverse (b := a) (l := t :: (m ++ [z]) ++ [a]) (by simp)]
  · exact Ach.cycle_of_last a v m t hnd hind hpos hbl h'

end cycles

/-! ### Even graphs contain chordless cycles -/

section evengraph

variable [Fintype V]

/-- The degree of `v` in a finite edge set. -/
def fdeg (F : Finset (Sym2 V)) (v : V) : ℕ := (F.filter (fun e => v ∈ e)).card

/-- A cycle `a :: l` (closing back to `a`) with all edges in `F`. -/
def IsCyc (F : Finset (Sym2 V)) (a : V) (l : List V) : Prop :=
  2 ≤ l.length ∧ (a :: l).Nodup ∧ ∀ e ∈ lEdges a (l ++ [a]), e ∈ F

omit [DecidableEq V] [Fintype V] in
theorem lEdges_sublist_concat (a : V) (l : List V) (z : V) :
    ∀ e ∈ lEdges a l, e ∈ lEdges a (l ++ [z]) := by
  intro e he
  rw [lEdges_append]
  exact List.mem_append_left _ he

/-- A path that cannot be extended at its head closes a cycle. -/
theorem exists_cyc_aux (F : Finset (Sym2 V)) (hdiag : ∀ e ∈ F, ¬ e.IsDiag)
    (heven : ∀ v, Even (fdeg F v)) :
    ∀ (k : ℕ) (a : V) (l : List V), (a :: l).Nodup → (∀ e ∈ lEdges a l, e ∈ F) → l ≠ [] →
      Fintype.card V ≤ l.length + k → ∃ a' l', IsCyc F a' l' := by
  intro k
  induction k with
  | zero =>
    intro a l hnd _ _ hk
    have := hnd.length_le_card
    rw [List.length_cons] at this
    omega
  | succ k ih =>
    intro a l hnd hF hl hk
    obtain ⟨u, rest, rfl⟩ : ∃ u rest, l = u :: rest := by
      cases l with
      | nil => exact absurd rfl hl
      | cons u rest => exact ⟨u, rest, rfl⟩
    have hau : s(a, u) ∈ F := hF _ (by simp)
    -- a second edge at `a`
    have hdeg : 2 ≤ fdeg F a := by
      have h1 : 1 ≤ fdeg F a :=
        Finset.card_pos.mpr ⟨s(a, u), Finset.mem_filter.mpr ⟨hau, Sym2.mem_mk_left a u⟩⟩
      obtain ⟨k', hk'⟩ := heven a
      omega
    obtain ⟨e', he', hne⟩ := Finset.exists_mem_ne (by omega : 1 < fdeg F a) s(a, u)
    rw [Finset.mem_filter] at he'
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp he'.2
    have haw : a ≠ w := fun h => hdiag _ he'.1 (by simp [h])
    have hwu : w ≠ u := fun h => hne (h ▸ rfl)
    by_cases hw : w ∈ a :: u :: rest
    · have hwr : w ∈ rest := by
        simp only [List.mem_cons] at hw
        rcases hw with h | h | h
        · exact absurd h.symm haw
        · exact absurd h hwu
        · exact h
      obtain ⟨p, q, rfl⟩ := List.append_of_mem hwr
      refine ⟨a, u :: (p ++ [w]), ⟨by simp, ?_, ?_⟩⟩
      · refine hnd.sublist ?_
        refine List.Sublist.cons_cons a (List.Sublist.cons_cons u ?_)
        exact List.Sublist.append_left (List.singleton_sublist.mpr List.mem_cons_self) p
      · intro e he
        rw [lEdges_append] at he
        simp only [lastOf_cons, lastOf_concat, lEdges_cons, lEdges_nil, List.mem_append,
          List.mem_singleton] at he
        rcases he with he | rfl
        · apply hF
          have : lEdges a (u :: (p ++ [w])) ++ lEdges w q = lEdges a (u :: (p ++ w :: q)) := by
            rw [show u :: (p ++ w :: q) = u :: (p ++ [w]) ++ q by simp, lEdges_append]
            simp
          rw [← this]
          exact List.mem_append_left _ he
        · rw [Sym2.eq_swap]; exact he'.1
    · refine ih w (a :: u :: rest) (List.nodup_cons.mpr ⟨hw, hnd⟩) ?_ (by simp)
        (by simp only [List.length_cons] at hk ⊢; omega)
      intro e he
      rw [lEdges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · rw [Sym2.eq_swap]; exact he'.1
      · exact hF e he

theorem exists_cyc (F : Finset (Sym2 V)) (hdiag : ∀ e ∈ F, ¬ e.IsDiag)
    (heven : ∀ v, Even (fdeg F v)) (hne : F.Nonempty) : ∃ a l, IsCyc F a l := by
  obtain ⟨e, he⟩ := hne
  induction e using Sym2.ind with
  | _ x y =>
  have hxy : x ≠ y := fun h => hdiag _ he (by simp [h])
  exact exists_cyc_aux F hdiag heven (Fintype.card V) x [y] (by simp [hxy])
    (by simpa using he) (by simp) (by simp)

omit [Fintype V] in
theorem split_two {W : Type*} {C : List W} {x y : W} (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    ∃ p q r, C = p ++ x :: (q ++ y :: r) ∨ C = p ++ y :: (q ++ x :: r) := by
  obtain ⟨p, s, rfl⟩ := List.append_of_mem hx
  rw [List.mem_append, List.mem_cons] at hy
  rcases hy with hy | hy | hy
  · obtain ⟨p', q', rfl⟩ := List.append_of_mem hy
    exact ⟨p', q', s, Or.inr (by simp)⟩
  · exact absurd hy.symm hxy
  · obtain ⟨q, r, rfl⟩ := List.append_of_mem hy
    exact ⟨p, q, r, Or.inl rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- A chord of a cycle gives a strictly shorter cycle. -/
theorem shorter_of_chord (F : Finset (Sym2 V)) (hdiag : ∀ e ∈ F, ¬ e.IsDiag) {a : V}
    {l : List V} (hc : IsCyc F a l) {x y : V} (hx : x ∈ a :: l) (hy : y ∈ a :: l)
    (hF : s(x, y) ∈ F) (hch : s(x, y) ∉ lEdges a (l ++ [a])) :
    ∃ a' l', IsCyc F a' l' ∧ l'.length < l.length := by
  obtain ⟨hl, hnd, hcF⟩ := hc
  have hxy : x ≠ y := fun h => hdiag _ hF (by simp [h])
  -- WLOG `x` comes before `y`
  suffices H : ∀ x y, s(x, y) ∈ F → s(x, y) ∉ lEdges a (l ++ [a]) →
      ∀ p q r, a :: l = p ++ x :: (q ++ y :: r) → ∃ a' l', IsCyc F a' l' ∧ l'.length < l.length by
    obtain ⟨p, q, r, h | h⟩ := split_two hx hy hxy
    · exact H x y hF hch p q r h
    · exact H y x (by rwa [Sym2.eq_swap]) (by rwa [Sym2.eq_swap]) p q r h
  intro x y hF hch p q r hC
  have hsub : ∀ e ∈ lEdges a l, e ∈ F := fun e he => hcF e (lEdges_sublist_concat a l a e he)
  have hinf : (x :: (q ++ [y])) <:+: a :: l := by
    rw [hC]
    refine List.infix_iff_prefix_suffix.mpr ⟨x :: (q ++ y :: r), ?_, List.suffix_append _ _⟩
    exact ⟨r, by simp⟩
  have hq : q ≠ [] := by
    rintro rfl
    apply hch
    refine lEdges_sublist_concat a l a _ (mem_lEdges_iff.mpr ⟨x, y, ?_, rfl⟩)
    simpa using hinf
  have hpr : p ≠ [] ∨ r ≠ [] := by
    by_contra hcon
    simp only [not_or, not_not] at hcon
    obtain ⟨rfl, rfl⟩ := hcon
    simp only [List.nil_append, List.cons.injEq] at hC
    obtain ⟨rfl, rfl⟩ := hC
    apply hch
    rw [mem_lEdges_iff]
    refine ⟨y, a, ?_, Sym2.eq_swap⟩
    exact (List.suffix_iff_eq_append.mpr (by simp)).isInfix
  refine ⟨x, q ++ [y], ⟨?_, hnd.sublist hinf.sublist, ?_⟩, ?_⟩
  · cases q with
    | nil => exact absurd rfl hq
    | cons _ _ => simp
  · intro e he
    rw [lEdges_append, lastOf_concat] at he
    simp only [lEdges_cons, lEdges_nil, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · obtain ⟨u, w, huw, rfl⟩ := mem_lEdges_iff.mp he
      exact hsub _ (mem_lEdges_iff.mpr ⟨u, w, huw.trans hinf, rfl⟩)
    · rwa [Sym2.eq_swap]
  · have := congrArg List.length hC
    simp only [List.length_cons, List.length_append] at this
    rcases hpr with h | h
    · have := List.length_pos_of_ne_nil h; simp; omega
    · have := List.length_pos_of_ne_nil h; simp; omega

/-- **A shortest cycle is chordless.** -/
theorem exists_chordless (F : Finset (Sym2 V)) (hdiag : ∀ e ∈ F, ¬ e.IsDiag)
    (heven : ∀ v, Even (fdeg F v)) (hne : F.Nonempty) :
    ∃ a l, IsCyc F a l ∧ ∀ x ∈ a :: l, ∀ y ∈ a :: l, s(x, y) ∈ F →
      s(x, y) ∈ lEdges a (l ++ [a]) := by
  classical
  have hex : ∃ n, ∃ a l, IsCyc F a l ∧ l.length = n := by
    obtain ⟨a, l, h⟩ := exists_cyc F hdiag heven hne
    exact ⟨_, a, l, h, rfl⟩
  obtain ⟨a, l, hc, hlen⟩ := Nat.find_spec hex
  refine ⟨a, l, hc, fun x hx y hy hF => ?_⟩
  by_contra hch
  obtain ⟨a', l', hc', hlt⟩ := shorter_of_chord F hdiag hc hx hy hF hch
  exact Nat.find_min hex (hlen ▸ hlt) ⟨a', l', hc', rfl⟩

omit [Fintype V] in
/-- Along any list without loops, `#(edges at v) + [first = v] + [last = v]` is even. -/
theorem even_countP_lEdges (v : V) :
    ∀ (a : V) (l : List V), (∀ e ∈ lEdges a l, ¬ e.IsDiag) →
      Even ((lEdges a l).countP (fun e => v ∈ e) +
        ((if a = v then 1 else 0) + (if lastOf a l = v then 1 else 0)))
  | a, [], _ => by by_cases h : a = v <;> simp [h]
  | a, b :: l, hd => by
    have hab : a ≠ b := fun h => hd s(a, b) (by simp) (by simp [h])
    have ih := even_countP_lEdges v b l (fun e he => hd e (by simp [he]))
    rw [lEdges_cons, List.countP_cons, lastOf_cons]
    obtain ⟨k, hk⟩ := ih
    by_cases hva : v = a
    · subst hva
      have hbv : b ≠ v := Ne.symm hab
      simp only [hbv, ite_false, zero_add] at hk
      refine ⟨k + 1, ?_⟩
      simp only [Sym2.mem_mk_left, decide_true, ite_true]
      omega
    · by_cases hvb : v = b
      · subst hvb
        refine ⟨k, ?_⟩
        simp only [Sym2.mem_mk_right, decide_true, ite_true, Ne.symm hva, ite_false]
        simp only [ite_true] at hk
        omega
      · refine ⟨k, ?_⟩
        have : ¬ v ∈ s(a, b) := by simp [hva, hvb]
        simp only [this, decide_false, Bool.false_eq_true, ite_false, Ne.symm hva,
          Ne.symm hvb] at hk ⊢
        omega

omit [DecidableEq V] [Fintype V] in
theorem cyc_edges_nodup {a : V} {l : List V} (hl : 2 ≤ l.length) (hnd : (a :: l).Nodup) :
    (lEdges a (l ++ [a])).Nodup := by
  rw [lEdges_append]
  simp only [lEdges_cons, lEdges_nil]
  rw [List.nodup_append]
  refine ⟨lEdges_nodup hnd, by simp, ?_⟩
  intro e he e' he' hee'
  rw [List.mem_singleton] at he'
  subst hee' he'
  obtain ⟨x, y, hxy, he⟩ := mem_lEdges_iff.mp he
  have ha : a ∉ l := (List.nodup_cons.mp hnd).1
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `[x, a]` would be consecutive
    subst h2
    rcases List.infix_cons_iff.mp hxy with h | h
    · rw [List.cons_prefix_cons] at h
      obtain ⟨-, h⟩ := h
      cases l with
      | nil => simp at hl
      | cons c l => rw [List.cons_prefix_cons] at h; exact ha (h.1 ▸ List.mem_cons_self)
    · exact ha (h.subset (by simp))
  · subst h1
    rcases List.infix_cons_iff.mp hxy with h | h
    · rw [List.cons_prefix_cons] at h
      obtain ⟨-, h⟩ := h
      obtain ⟨c, l', rfl⟩ : ∃ c l', l = c :: l' := by
        cases l with
        | nil => simp at hl
        | cons c l' => exact ⟨c, l', rfl⟩
      rw [List.cons_prefix_cons] at h
      obtain ⟨hyc, -⟩ := h
      have hl' : l' ≠ [] := by rintro rfl; simp at hl
      have hmem := lastOf_mem_of_ne_nil c hl'
      have hyc' : lastOf c l' = c := hyc
      rw [hyc'] at hmem
      exact (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 hmem
    · exact ha (h.subset (by simp [h2]))

omit [Fintype V] in
theorem card_filter_toFinset {W : Type*} [DecidableEq W] {L : List W} (hL : L.Nodup)
    (p : W → Prop) [DecidablePred p] :
    (L.toFinset.filter p).card = L.countP (fun a => decide (p a)) := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hL.filter _)]
  congr 1
  ext a
  simp

omit [Fintype V] in
/-- Every vertex meets an even number of edges of a cycle. -/
theorem even_cycle_degree {a : V} {l : List V} (hl : 2 ≤ l.length) (hnd : (a :: l).Nodup)
    (v : V) : Even (fdeg (lEdges a (l ++ [a])).toFinset v) := by
  have hd : ∀ e ∈ lEdges a (l ++ [a]), ¬ e.IsDiag := by
    intro e he
    rw [lEdges_append] at he
    simp only [lEdges_cons, lEdges_nil, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact lEdges_not_diag hnd he
    · have hm := lastOf_mem_of_ne_nil a (show l ≠ [] by rintro rfl; simp at hl)
      have ha : a ∉ l := (List.nodup_cons.mp hnd).1
      rw [Sym2.mk_isDiag_iff]
      rintro h
      exact ha (h ▸ hm)
  have h := even_countP_lEdges v a (l ++ [a]) hd
  rw [lastOf_concat] at h
  unfold fdeg
  rw [card_filter_toFinset (cyc_edges_nodup hl hnd)]
  obtain ⟨k, hk⟩ := h
  refine ⟨k - (if a = v then 1 else 0), ?_⟩
  split_ifs at hk ⊢ <;> omega

omit [DecidableEq V] [Fintype V] in
/-- Every vertex of a cycle lies on one of its edges. -/
theorem mem_edge_of_mem_cyc {a : V} {l : List V} (hl : l ≠ []) {x : V} (hx : x ∈ a :: l) :
    ∃ e ∈ lEdges a (l ++ [a]), x ∈ e := by
  rw [List.mem_cons] at hx
  rcases hx with rfl | hx
  · obtain ⟨c, l', rfl⟩ : ∃ c l', l = c :: l' := by
      cases l with
      | nil => exact absurd rfl hl
      | cons c l' => exact ⟨c, l', rfl⟩
    exact ⟨s(x, c), by simp, Sym2.mem_mk_left _ _⟩
  · obtain ⟨p, q, rfl⟩ := List.append_of_mem hx
    obtain ⟨p', w, hp⟩ : ∃ p' w, a :: p = p' ++ [w] := by
      rcases List.eq_nil_or_concat' (a :: p) with h | ⟨p', w, h⟩
      · simp at h
      · exact ⟨p', w, h⟩
    refine ⟨s(w, x), lEdges_sublist_concat a _ a _ (mem_lEdges_iff.mpr ⟨w, x, ?_, rfl⟩),
      Sym2.mem_mk_right _ _⟩
    rw [← List.cons_append, hp]
    exact List.infix_iff_prefix_suffix.mpr ⟨[w, x] ++ q, ⟨q, rfl⟩, ⟨p', by simp⟩⟩

end evengraph

/-! ### Lemma 3 -/

section lemma3

variable [Fintype V]

/-- **Lemma 3 of the six-clique paper.** Let `S` be independent in `E`, with every `v ∈ S` having
at least one end and at most one blank neighbour. Any finite even graph `F` on `S` can be inserted
without changing the end vector. -/
theorem Ach.insert_even (S : Set V) {E : Set (Sym2 V)} {b : V → ℕ}
    (hind : ∀ v ∈ S, ∀ w ∈ S, s(v, w) ∉ E) (hpos : ∀ v ∈ S, 1 ≤ b v)
    (hbl : ∀ v ∈ S, blankNbrs E b v ≤ 1) :
    ∀ (F : Finset (Sym2 V)), (∀ e ∈ F, ¬ e.IsDiag) → (∀ v, Even (fdeg F v)) →
      (∀ e ∈ F, ∀ v ∈ e, v ∈ S) → Ach E b → Ach (E ∪ ↑F) b := by
  classical
  intro F
  induction' hF : F.card using Nat.strong_induction_on with k ih generalizing F
  intro hdiag heven hFS h
  rcases F.eq_empty_or_nonempty with rfl | hne
  · simpa using h
  obtain ⟨a, l, ⟨hl, hnd, hcF⟩, hchord⟩ := exists_chordless F hdiag heven hne
  set C : Finset (Sym2 V) := (lEdges a (l ++ [a])).toFinset with hCdef
  have hCF : C ⊆ F := fun e he => hcF e (List.mem_toFinset.mp he)
  set F' := F \ C with hF'
  have hCne : C.Nonempty := ⟨s(lastOf a l, a), by simp [hCdef, lEdges_append]⟩
  have hlt : F'.card < k := by
    rw [← hF]
    exact Finset.card_lt_card (Finset.sdiff_ssubset hCF hCne)
  have hF'F : F' ⊆ F := Finset.sdiff_subset
  have heven' : ∀ v, Even (fdeg F' v) := by
    intro v
    have h1 : fdeg F' v = fdeg F v - fdeg C v := by
      unfold fdeg
      have : F'.filter (fun e => v ∈ e) = F.filter (fun e => v ∈ e) \ C.filter (fun e => v ∈ e) := by
        ext e
        simp only [hF', Finset.mem_filter, Finset.mem_sdiff]
        tauto
      rw [this, Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ hCF)]
    have h2 : fdeg C v ≤ fdeg F v := Finset.card_le_card (Finset.filter_subset_filter _ hCF)
    rw [h1]
    exact (Nat.even_sub h2).mpr (iff_of_true (heven v) (even_cycle_degree hl hnd v))
  have h' := ih F'.card hlt F' rfl (fun e he => hdiag e (hF'F he)) heven'
    (fun e he => hFS e (hF'F he)) h
  have hS : ∀ x ∈ a :: l, x ∈ S := by
    intro x hx
    obtain ⟨e, he, hxe⟩ := mem_edge_of_mem_cyc (show l ≠ [] by rintro rfl; simp at hl) hx
    exact hFS e (hcF e he) x hxe
  have h'' := h'.insert_cycle a l hl hnd
    (by
      intro x hx y hy hmem
      rcases hmem with hmem | hmem
      · exact hind x (hS x hx) y (hS y hy) hmem
      · rw [Finset.mem_coe, hF', Finset.mem_sdiff] at hmem
        exact hmem.2 (List.mem_toFinset.mpr (hchord x hx y hy hmem.1)))
    (fun x hx => hpos x (hS x hx))
    (by
      intro x hx
      refine (blankNbrs_mono ?_).trans (hbl x (hS x hx))
      intro w hw _ hw0
      refine ⟨?_, hw0⟩
      rcases hw with hw | hw
      · exact hw
      · have := hpos w (hFS _ (hF'F hw) w (Sym2.mem_mk_right _ _))
        omega)
  refine h''.congr ?_ (fun _ => rfl)
  ext e
  simp only [Set.mem_union, Finset.mem_coe, hF', Finset.mem_sdiff, Set.mem_ofPred_eq]
  constructor
  · rintro ((h | ⟨h, -⟩) | h)
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr (hcF e h)
  · rintro (h | h)
    · exact Or.inl (Or.inl h)
    · by_cases hc : e ∈ lEdges a (l ++ [a])
      · exact Or.inr hc
      · exact Or.inl (Or.inr ⟨h, fun h' => hc (List.mem_toFinset.mp h')⟩)

end lemma3

end Gallai
