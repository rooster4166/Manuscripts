# near-dirac: returning the exceptional set below the Dirac threshold (Target D)

`near-dirac.tex` / `near-dirac.pdf` are a standalone manuscript with complete proofs. Exact statements of the external theorems used are in `CITATIONS.md`.

## Main result

**Theorem 1.1 (balanced return theorem).** Let G have shores A and B with |A| = m and |B| = m + ρ, where ρ ∈ {0, 1}, and let X be a set of at most cm exceptional vertices. Suppose:

- (a) every vertex outside X has at most cm own-shore neighbours and at most cm cross non-neighbours;
- (b) every vertex x of X has degree (1 ± c)m and at least m/4 cross neighbours; its own-shore degree is otherwise unrestricted, up to about 3m/4;
- (c) the balance condition holds: I_X(A) + ρm/2 ≤ e(B) + 250cm and I_X(B) ≤ e(A) + ρm/2 + 250cm, where I_X(S) counts the edges inside S that meet X.

Then every degree-parity profile b ≤ 2 with b(V) = 2m and |b(A) − b(B)| ≤ cm is realised by exactly m paths.

Consequences:

- **SP Theorem 14.27** is the special case X = ∅, ρ = 0.
- **Corollary 1.2.** Near-regular graphs near K_{n/2,n/2} whose degree excess over ⌊n/2⌋ balances across a bisection satisfy the floor bound at both parities and the rooted private-leaf bound at even order.
- **Corollary 1.3.** In every failure sequence (SP Cor 14.24), every admissible partition and exceptional set with |X| ≤ cm violates the balance condition.

## Proof

The proof extends SP Theorem 14.27:

- q = θm preliminary slots;
- a membership matrix (Lemma 3.1, by max-flow);
- a weaving lemma (Lemma 3.2, by Hall);
- a two-apex Hamilton finish via CKLOT Theorem 1.3.5 (Lemma 4.2).

Exceptional vertices enter the slots only through prebuilt partner blocks u x u'. Their internal edges are kept for the Hamilton phase, and the imbalance is absorbed exactly by kept healthy internal edges and by the slot end patterns. Lemma 4.1 is the counting identity behind the balance condition (Remark 4.3). Its bipartite case is SP's counting obstruction in §14.18. The u x u' threading device is SP's own (Thm 14.30). Balance is sufficient for the construction, not claimed necessary.

## Relation to SP §14 (manuscript §7)

- Theorem 1.1 contains SP 14.27.
- It neither contains nor is contained in SP 14.31, 14.33 and 14.37 (unequal shores, one apex, vertex removal).
- It returns the Cor 14.39 exceptional set whenever the configuration is balanced (Remark 6.2).

## What remains for full Target D

- **Problem 7.1.** Two-sided removal: extend SP Thm 14.33 so that removed vertices may have neighbours in both shores.
  - **Counting half: proved in §8 under (B1).** Condition (B1) asks that every exceptional vertex has at most D healthy neighbours in each shore. It excludes intermediate vertices (Remark 8.4 gives the precise form).
    - Lemma 8.1 (exact balancing) uses a mirror symmetry; Lemma 8.2 is its robust form.
    - Proposition 8.3, due to audit A19, is a two-sided exact sweep with nested removed sets and a zero-stage fallback. It meets the one-apex window e_X(I) − e_X(K∖W) ∈ [D(t−1)/2, D(t+1)/2] exactly, for every |X|, under (B1). It also needs the degree window D + |Δ| + 2|X| + 2 ≤ d_x ≤ 5D/4 and |Δ| + 5|X| + 1 < D.
  - **Scheduling half: open.** It is stated precisely as the **Scheduling Hypothesis SH** (Def. 9.1, not proved). With X = ∅, SH is the regime of the penultimate sentence of SP 14.37's proof, together with Thm 1.1 at equal shores.
  - **Theorem 9.3 (conditional, proved).** Assume SH. Then every failure sequence with Δ ≤ (1/2 + o(1))n must, at all large n and for every maximum cut, contain an intermediate vertex: λ_n ≤ own(v) < d(v) − D_n + σ_n (Problem 9.4).

## Lean

`lean/GallaiLean/NearDirac.lean` is sorry-free and uses only the standard axioms. It proves:

- `matrix_cut_ineq`, the cut inequality of Lemma 3.1;
- `dense_bipartite_hall`, the Hall step of Lemma 3.2.

Build: `cd lean && lake build GallaiLean.NearDirac` (Lean 4.36.0, Mathlib v4.36.0).
