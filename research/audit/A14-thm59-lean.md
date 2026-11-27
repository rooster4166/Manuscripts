# Audit A14: Theorem 59 in Lean

**Scope.** Marked-reduction (MR) Theorem 59 (p. 84), in the finite-order form `Thm59Statement` (audit A2, finding F1), together with the parts of Theorem 7, Lemma 6 and §2–§2.1 that it uses. Lean branch: `claude/lean-thm59`.

**Result.** `thm59 : Thm59Statement` is proved (`lean/GallaiLean/Thm59.lean`). Theorem 114 now holds with no hypothesis: `gallai_iff_spineTests'` (`Separator.lean`). `#print axioms` on both gives only `propext`, `Classical.choice`, `Quot.sound`.

## Verdict

**No gap found.**

* `Thm59Statement` is correct as stated. No change to the statement was needed.
* MR's proof, read with the A1 fixes G7 and G10, goes through.
* The rooted tests are used only on `B` and on cones `B + z` over at least two marks. Both have order at most `n + 1 ≤ m + 1`, as A1/G10 says.

## Where the formal proof differs from MR (the mathematics is the same)

1. **Order of the induction.** The proof inducts on the bound `j ≤ m` for the block order: it proves `MarkedBoundUpTo j` from `MarkedBoundUpTo (n − 1)` for every block of order `n ≤ j`. This order is necessary.
   * The parts of Theorem 7 that carry leaves can have order `≥ |B|`. What is smaller is only their block order.
   * MR's phrase "induct on the order of a two-connected block" says this; the formal statement makes it explicit.

2. **One assignment lemma replaces two arguments of §2.1.** MR uses the private-leaf identity `q(G, A) = p(L_A(G)) − |A|` for even marks, and the rank inequality `ρ(A ∪ O) ≥ ρ(A) + ⌈o/2⌉` for odd marks. The Lean proof uses one lemma instead, `markedNumber_add_card_le`, proved by Hall's theorem with `⌊|O|/2⌋` dummy slots:
   * **Hypothesis.** Every mark has an end of `D`, and every mark outside `O` has two.
   * **Conclusion.** `q(F, T) + |T| ≤ |D| + ⌊|O|/2⌋`.

   In the matching-cut step:
   * after trimming, the even marks whose leaf path survived have one end, hence two by parity;
   * the odd marks have one end by parity.

   This gives `q(B, A ∪ O) ≤ ⌊(n + a)/2⌋ − a − ⌈o/2⌉ ≤ ⌊(n − a − o)/2⌋` in one step.

3. **Singletons at odd order.** MR adjoins `w` adjacent to `x` and to one other vertex `y`, applies test 1 at `w`, and trims. That graph is the cone over `{x, y}`. The Lean proof instead combines:
   * the two-mark cone bound `q(B, {x, y}) ≤ (n − 3)/2`;
   * `q(B, {x}) ≤ q(B, {x, y}) + 1` (forget one site).

4. **Connected shores.** MR takes an inclusion-minimal disconnecting sub-matching. The Lean proof takes a component `C` of one side, then a component `D` of `V ∖ C`. Both `D` and `V ∖ D` are connected, and the crossing edges are still a matching (`exists_connected_matchingCut`).

5. **Matching-cut step needs only connectivity.** `matchingCut_markedBound` assumes `B` connected, not two-connected. With `S = ∅` it gives `p(B) ≤ ⌊n/2⌋`, so the three-end test is vacuous on such `B`, as MR says.

6. **Block transfer.** MR §2 "Transfer through a block tree" is realised by re-running the Theorem 1 induction of `MarkedBlocks.lean` in place, with two changes:
   * the induction hypothesis ranges over restrictions of the current instance;
   * the two tests are bounded by the block order (`mbOn_of_testsUpTo`).

   All sub-instances of that induction are restrictions, so small blocks are inherited. The original `mbOn_of_tests` / `gallai_iff_tests` statements are unchanged.
