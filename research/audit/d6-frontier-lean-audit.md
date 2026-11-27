# d6-frontier: formalization audit (companion to A9)

**Paper.** `manuscripts/d6-frontier/d6-frontier.tex` (26 November 2026 draft).

**Scope.** Lemma 2.3 (relay and carry), Lemma 3.2 (seeds), Theorem 4.1(i) (root hub),
Theorem 5.2 (full hub) and Theorem 6.1 (hubs at every deletion degree), together with the
Remark after Theorem 6.1. Theorem 4.1(ii), (iii) were formalized afterwards, with the hypothesis
added in F1.

**Method.** Every statement in scope was formalized in Lean 4 + Mathlib (branch
`claude/lean-d6-frontier`; files `lean/GallaiLean/Relay.lean`, `HubPhases.lean`,
`D6Frontier.lean`). Each row of a step table is one application of Fan's lemma
(`fan_single`/`fan_grouped`, via `Ach.transfer`/`Ach.grouped`), so the kernel checks every
"(supply, bound)" pair, every blank-neighbour bound, the seed parities and the final profile.
Lovász's theorem is a theorem in the library (`lovaszStatement`), so the Lean results are
unconditional. `#print axioms` on every main result shows only `propext`, `Classical.choice`,
`Quot.sound`. No `sorry`.

This is not a replacement for audit A9 (which covers the whole manuscript and the new descent
sections). It records what the formalization found.

## 0. Verdict

**No ERROR.** Every formalized statement holds as stated, or under a hypothesis that is implicit
in the setting. Two wording gaps were found (F1, F2), both outside the four formalization
targets, and both fixed in the text. Theorem 4.1(ii), (iii) were then formalized with the F1
hypothesis, which confirms the fix. The Lean statements are in places more general than the
paper (F3, F4).

## 1. Verdict table

| # | Item | Verdict | Lean |
|---|---|---|---|
| 1 | Lemma 2.3(a), forward relay | SOUND | `Ach.forwardRelay` |
| 2 | Lemma 2.3(b), carry | SOUND; the hypothesis can be weakened (F3) | `Ach.carry` |
| 3 | Lemma 3.2(a), (b), seeds | SOUND | `seed_odd`, `seed_pair` |
| 4 | Remark 3.4 counting: grouped receipts, donations, paybacks | SOUND | `Ach.receiveMany`, `Ach.giveAll`, `hub_receive`, `hub_give`, `hub_payback` |
| 5 | Thm 4.1(i) | SOUND | `root_hub_six`, `root_hub_six_passes` |
| 6 | Thm 4.1(ii), (iii) | **GAP (wording, F1)**: the seed needs the vertices of `Q` to be non-isolated; SOUND with that hypothesis | `root_hub_six_Q1`, `root_hub_six_Q2` (and `_passes`) |
| 7 | Thm 5.2, two quiet batteries | SOUND | `full_hub_six` |
| 8 | Thm 5.2, battery and pendant | SOUND | `full_hub_six_pendant` |
| 9 | Thm 6.1(a) | SOUND; `d ≥ 4` is not needed (F4) | `root_hub_uniform`, `root_hub_uniform_passes` |
| 10 | Thm 6.1(b), batteries | SOUND; `d ≥ 4` is not needed | `full_hub_uniform`, `full_hub_uniform_passes` |
| 11 | Thm 6.1(b), batteries and pendant | SOUND | `full_hub_pendant_uniform`, `full_hub_pendant_uniform_passes` |
| 12 | Remark after Thm 6.1, `d = 4` without quietness | **GAP (wording, F2)**: needs an odd neighbour of degree ≥ 3 | not formalized |

## 2. Findings

**F1 (Thm 4.1(ii), (iii): isolated core vertices).** In (ii) the vertex `q` keeps all its edges
in `B₀ = B − H`, and in (iii) so do `q₁, q₂`. Lemma 3.2(b) requires `B₀` to have no isolated
vertex. The theorem's hypotheses (`B` of even order, `U = Ev(B)`) do not exclude an isolated
`q ∈ U`, and §1 does not state that `B` is connected (only the abstract does). So the proof
applies Lemma 3.2(b) outside its hypotheses. The damage is limited:

* (ii) with `q` isolated: the seed still exists (Lovász on `B₀ − q`, which has odd order and the
  single even vertex `r`, gives `k − 1` paths with no end at `r`; split one of them at `r`), and
  the table goes through, because an isolated `q` is never a blank neighbour. The theorem holds
  as stated.
* (iii) with one of `q₁, q₂` isolated: the roles of `q₁, q₂` must be exchanged (the isolated one
  is the blank one), and then `bq₂ ∉ E` is not needed. With both isolated the run ends with
  `k − 1` paths and only two doubled vertices (`r` and `s`). Then `r` still passes, but the last
  sentence of the theorem ("exactly `k` paths, … three doubled vertices of `U`") is false.

In the setting of the test (`B` connected; `δ(B) ≥ 6` in the apex class) the issue does not
arise, so no result of the programme is affected. In (i), and in Theorems 4.2, 4.4, 5.2 and 6.1,
every vertex of `U` is adjacent to the hub, so they need no such hypothesis.
*Fix (applied in the text):* (ii) and (iii) now assume that the vertices of `Q` are not isolated
(automatic when `B` is connected).

**F2 (Remark after Thm 6.1, `d = 4`).** The remark says that for `d = 4` the root hub "needs no
battery and no quietness", and that this "recovers T(4)-i at every universal root with at least
three odd neighbours". The counting is right: with `|T| = 3`, two receipts, one donation with
supply 4 against at most 3 blank neighbours (`Z` and possibly `y`), and the payback to `y` with
supply 3 against at most `|N(y) ∩ Z| ≤ 2`. But the seed still needs `d(y) ≥ 3` (otherwise `y` is
isolated in `B₀`) and `d(r) ≥ 6`. "At least three odd neighbours" gives the second condition,
not the first.
*Fix (applied in the text):* "at every universal root with at least three odd neighbours, one of
which has degree at least 3".

**F3 (Lemma 2.3(b): a weaker hypothesis suffices).** Not a gap. The manuscript asks that none of
`v₀, …, v_{m−1}` is adjacent *in `H_m`* to a blank vertex of `D`. The proof only needs it *in `H`*,
and only for blank vertices other than `v₀`: if `v₀` is blank it receives at the first step,
before any later receiver sees it. `Ach.carry` is stated with this weaker hypothesis, and with
`b(v_i) ≥ 1` instead of `b(v_i) = 1` (then `b(v_m)` drops by one rather than to zero).

**F4 (Theorem 6.1: no lower bound on `d`).** Not a gap. The proofs of (a) and (b) never use
`d ≥ 4`; the Lean statements hold for every even `d` (`|U|` is even automatically at even
order). Also, in (a) and (b) the number of receipts is `d/2`, so `d` even is used, and it follows
from the handshake lemma (`even_card_of_hU`).

**F5 (order of batteries).** Not a gap, a reading. "`a_i b_j ∉ E` for `i < j`" is used exactly
when `b_j` is carried while `a_i` is parked, so the batteries must be carried in index order.
The Lean statements take the batteries as a list, carried in list order, with
`L.Pairwise (fun p q => ¬ G.Adj p.1 q.2)`.

**F6 (uncontrolled donors in Thm 4.1(i)).** Checked, sound. The receivers `s₁, s₂ = T − Z` are
known only after the two grouped receipts. The proof orders them after the fact so that
`s₂ ≠ p'`; `s₂ ≠ p` holds because `p ∈ Z`. The Lean proof does the same (`root_hub_six`,
"order the two receivers").

## 3. What the Lean statements say

* `PassesAt G r`: some path decomposition has at most `|V|/2` paths and at least two ends at `r`.
* Hypotheses are in the form `hU : ∀ v, v ∈ U ↔ Even (G.degree v)` (so `U = Ev(B)`, isolated
  vertices included) and `Even (Fintype.card V)`.
* Every theorem is proved in the stronger form "some `S ⊆ U` with `r ∈ S` and `2|S| = |U|` is
  realisable" (`Realisable G S`: one end at every odd vertex, two on `S`, none on `U \ S`), and
  `passesAt_of_realisable` gives the rooted test.
* Batteries are a list `L` of pairs `(a, b)` (parked vertex first). Distinctness is a `Nodup`
  hypothesis on the hub (or pendant) followed by `L.map Prod.fst ++ L.map Prod.snd`.
