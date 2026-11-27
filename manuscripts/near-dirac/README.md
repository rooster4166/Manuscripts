# near-dirac: returning the exceptional set below the Dirac threshold (Target D)

`near-dirac.tex` / `near-dirac.pdf` are a standalone manuscript with complete proofs. Exact statements of the external theorems used are in `CITATIONS.md`.

## Main result

**Theorem 1.1 (balanced return theorem).** Let G have shores A and B with |A| = m and |B| = m + ρ, where ρ ∈ {0, 1}, and let X be a set of at most cm exceptional vertices. Suppose:

- (a) every vertex outside X has at most cm own-shore neighbours and at most cm cross non-neighbours;
- (b) every vertex x of X has degree (1 ± c)m and at least m/4 cross neighbours; its own-shore degree is otherwise unrestricted, up to about 3m/4;
- (c) the balance condition holds: I_X(A) + ρm/2 ≤ e(B) + cm and I_X(B) ≤ e(A) + ρm/2 + cm, where I_X(S) counts the edges inside S that meet X.

Then every degree-parity profile b ≤ 2 with b(V) = 2m and |b(A) − b(B)| ≤ cm is realised by exactly m paths.

Consequences:

- **SP Theorem 14.27** is the special case X = ∅, ρ = 0.
- **Corollary 1.2.** Near-regular graphs near K_{n/2,n/2} whose degree excess over ⌊n/2⌋ balances across a bisection satisfy the floor bound at both parities and the rooted private-leaf bound at even order.
- **Corollary 1.3.** In every failure sequence (SP Cor 14.24), every admissible partition and exceptional set violates the balance condition.

## Proof

The proof extends SP Theorem 14.27:

- q = θm preliminary slots;
- a membership matrix (Lemma 3.1, by max-flow);
- a weaving lemma (Lemma 3.2, by Hall);
- a two-apex Hamilton finish via CKLOT Theorem 1.3.5 (Lemma 4.2).

Exceptional vertices enter the slots only through prebuilt partner blocks u x u'. Their internal edges are kept for the Hamilton phase, and the imbalance is absorbed exactly by kept healthy internal edges and by the slot end patterns. Lemma 4.1 is the counting identity that makes the balance condition necessary for this two-apex architecture (Remark 4.3).

## Relation to SP §14 (manuscript §7)

- Theorem 1.1 contains SP 14.27.
- It neither contains nor is contained in SP 14.31, 14.33 and 14.37 (unequal shores, one apex, vertex removal).
- It returns the Cor 14.39 exceptional set whenever the configuration is balanced (Remark 6.2).

## What remains for full Target D

- **Problem 7.1.** Two-sided removal: extend SP Thm 14.33 so that removed vertices may have neighbours in both shores. The one-apex identity and the greedy side-choice are done; the scheduling of pairs on the bin shore is open.
- **Problem 7.2.** Exceptional vertices of degree at least (1/2 + β)n. NH handles at most two, under exact regularity.

## Lean

`lean/GallaiLean/NearDirac.lean` is sorry-free and uses only the standard axioms. It proves:

- `matrix_cut_ineq`, the cut inequality of Lemma 3.1;
- `dense_bipartite_hall`, the Hall step of Lemma 3.2.

Build: `cd lean && lake build GallaiLean.NearDirac` (Lean 4.36.0, Mathlib v4.36.0).
