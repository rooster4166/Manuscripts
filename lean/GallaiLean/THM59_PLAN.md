# Theorem 59 in Lean: plan

**Status: done.** `thm59 : Thm59Statement` and `gallai_iff_spineTests'` are proved, with no
`sorry` and only the standard axioms. The tree below is what was formalised.

Target: `thm59 : Thm59Statement` (`ThreeConnected.lean`), then the unconditional
`gallai_iff_spineTests'` in `Separator.lean`.

`Thm59Statement`: for every `m`, if both rooted assertions (`RootedAt`) hold on every member of
`C` (`InClassC`: `KConnected 2`, no matching cut) with at most `m + 1` vertices, then
`MarkedBoundUpTo m`: the marked bound on every connected graph whose two-connected blocks have
order `≤ m`.

Notation: `MBU(j)` = `MarkedBoundUpTo j`; `RT(m)` = the hypothesis of `Thm59Statement`.

## Dependency tree

```
thm59  (Thm59.lean)
 └─ strong induction on m' ≤ m:  MBU(j) for all j < m'  ⟹  MBU(m')
     ├─ [T] block transfer (MarkedBlocks.lean, generalised in place)
     │     MTC(m') ∧ TET(m') ⟹ MBU(m')
     │     MTC = marked bound on two-connected graphs of order ≤ m'
     │     TET = three-end test on two-connected graphs of order ≤ m'
     │     * SmallerMB only on restrictions of the current instance; small blocks inherited
     │     * twoConnStep / pendantStep with order-bounded tests
     │     * TwoConnOn (restrict F U) U ⟹ KConnected 2 (F.induce U)   (Thm59Transfer.lean)
     └─ for B two-connected of order n ≤ m':
         ├─ B ∈ C:            [C] Thm59ClassC.lean  (MR §17 proof, ¶1)
         │     * cone B S ∈ C for |S| ≥ 2 (order n + 1 ≤ m + 1)
         │     * cone identity (Marked.lean, `le_outEnds`, `two_mul_size_eq`):
         │       |S| + 2 q(B,S) ≤ 2|D| − b_D(z)
         │     * n − |S| odd: rooted test at the apex (test 2 at even n, test 1 at odd n)
         │     * n − |S| even: drop a mark (q is antitone in S)
         │     * singletons: even n by test 1 / Lovász + parity; odd n by q(B,{x}) ≤ q(B,{x,y}) + 1
         │     * three ends: test 2 directly
         └─ B has a matching cut: [M] Thm59MatchingCut.lean  (MR Thm 7 + Lemma 6 + §2.1),
               using MBU(n − 1) for the shores
               * shores can be taken connected (component of a component)
               * L_A(B) on V ⊕ V: private leaves at the even marks A ⊆ S  (Thm59Leaves.lean)
               * [Lemma 6, two parts] p(L_A(B)) ≤ t + q(shore₁⁺, A₁) + q(shore₂⁺, A₂)
                 ≤ ⌊(n + |A|)/2⌋   (Thm59Lemma6.lean, PMP surgery)
                 shores⁺ have blocks ≤ n − 1, so MBU(n − 1) applies whatever their order
               * trim the leaves: |D'| + #{a ∈ A : b_{D'}(a) = 0} ≤ |D|  (project_full)
               * Hall (Mathlib `Finset.all_card_le_biUnion_card_iff_exists_injective`)
                 with ⌊o/2⌋ dummies: marks with ≥ 2 ends (even) and ≥ 1 end (odd)
                 give q(B, T) + |T| ≤ |D'| + ⌊o/2⌋   (Thm59Hall.lean)
               * combine: q(B, A ∪ O) ≤ ⌊(n + a)/2⌋ − a − ⌈o/2⌉ ≤ ⌊(n − a − o)/2⌋;
                 with S = ∅ this is p(B) ≤ ⌊n/2⌋, so TET is vacuous
```

The private-leaf identity and the odd-mark rank inequality of MR §2.1 are both replaced by the
single Hall-defect lemma.  The matching-cut step needs only `B` connected.

## Files

| File | Content |
|---|---|
| `MarkedBlocks.lean` (edited) | `SmallerMB G U` on restrictions; `MarkedTwoConnTestUpTo`, `ThreeEndsTestUpTo`, `SmallOn`; `mbOn_of_testsUpTo`; old API unchanged |
| `Thm59Transfer.lean` | 2-connectivity conversions; `markedBoundUpTo_of_tests` |
| `Thm59ClassC.lean` | step [C] |
| `Thm59Hall.lean` | Hall assignment lemma |
| `Thm59Leaves.lean` | leaf graph on `V ⊕ V`, trimming with ends |
| `Thm59Lemma6.lean` | Lemma 6 for a matching cut (PMP assembly) |
| `Thm59MatchingCut.lean` | connected shores, local bounds, step [M] |
| `Thm59.lean` | `thm59 : Thm59Statement` |
| `Separator.lean` (edited) | `gallai_iff_spineTests'` |
