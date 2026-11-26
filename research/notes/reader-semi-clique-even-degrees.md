# Reader notes: odd-semi-clique-boundary (A), even-degrees (B), September note (S)

These notes have not been independently verified.

## Exact results at every order

**A Thm 4 (= S Thm 2.4).** Let G = K_{2k+1} − H with m = e(H).
- If m < k: p(G) = k+1, and any path Q of length k − m completes to an optimum using k Hamilton paths.
- If m = k: p = k, and every optimum consists of Hamilton paths.
- If m > k and H is supported on ≤ k+1 vertices: p = k.

**Dependence on Javadi–Miralaei.** JM is needed only for k ≥ 6, ⌈(k+4)/2⌉ ≤ m ≤ k−1, and H sparse and not a linear forest. Liu–Chen covers the rest. The smallest case needing JM is K_{1,3} ∪ 2K_2 at n = 13.

**Endpoint and spanning results (A).**
- **Thm 11 / Cor 12.** All endpoint vectors with b ≥ d_H. Computer- and Lean-checked for k < 130.
- **Thm 3 (= Thm 16 + Cor 18).** With k + x deletions and k ≥ 6x: x paths of length 2k−1 plus k − x Hamilton paths. For x = 1, 2 this holds for every k. Uses 61 machine-checked shapes.
- **Prop 47 / Cor 49.** Floor bound when the blocks are cliques, connected 3-degenerate graphs, or large dense blocks.

## Sufficiently large n only (A)

- **Thm 2.** Δ(H) ≤ k/100.
- **Thms 1/19, 24, 28, 35; Cors 30, 36/37.** The floor holds outside odd semi-cliques for ≤ 4n − 20007 missing edges.
- **Thm 38.** Up to n²/6000 missing edges, with root prescriptions.
- **Dependencies.** Kühn–Osthus (Kelly / robust expanders), Csaba et al., Pfenninger, and an in-paper random degree-partition lemma (§11.1). **That lemma is a sketch**, and it is applied at √N log N discrepancy although it is stated for O(1).
- **Thresholds** are ineffective.

## Equivalences

- **S Cor 1.5.** Botler–Sambinelli ⇔ Bonamy–Perrett.
- **A Cor 44.** Gallai ⇔ Gallai restricted to sufficiently large connected graphs of even order N with ≤ CN missing edges, for any fixed C > 0. So the linear-deletion dense regime is as hard as Gallai itself.
- **A Thm 46.** Ceiling ⇔ floor for graphs with a leaf ⇔ floor for graphs with a cut vertex.
- **A Thm 48.** Gallai ⇔ the floor on a 2-connected D with one leaf at x (|D| even) or two leaves at x (|D| odd).
- **A Thm 50.** Gallai ⇔ the ceiling on bridge-doubles and diamond-doubles.
- **A Cor 51.** Gallai ⇔ [ceiling for bridgeless graphs] ∧ [no (k, k+1, k+1) optimum pattern at an even x].
- **A Thm 52.** Restricted D: degree-2 vertices on triangles, x with ≥ 3 even neighbours, d(x) ≥ 4 (even core) or ≥ 7 (odd core).
- **B Prop 15 / Thm 19 / Cor 21.** Gallai ⇔ for every bandwidth b, every cycle of a finite automaton has mean weight ≤ 1/2.
  - Gallai at a fixed bandwidth is decidable.
  - A counterexample at bandwidth b forces a bad cycle at bandwidth b+2.

## Elementary results (B)

- **Thm 1.** p ≤ n/2 + 3n/√(d+1) when all even vertices have degree ≥ d.
- **Cor 5.** The floor holds for an independent set U satisfying a neighbourhood condition.
- **Thm 7.** Girth > L(Δ) + 1 gives the floor, where L(D) = 2⌊(D−1)/2⌋ + 4. At even order, girth > L suffices and also gives the root prescription.
- **Thm 12.** Cones.
- **Thm 22.** Perfect-matching lifts.
- **Prop 20** (computer). Bandwidth ≤ 3 gives the floor except for K3 and K5−e. The b = 3 automaton has 627,458 states.
- **Thms 35/38/47.** The four-even-vertex prescription problem, Fan certificates and modules. Thm 47 (twin cancellation) is open.

## Comparison with the literature

- Chu–Fan–Zhou: (4n+6)/7 for odd semi-cliques. Thm 4 is new for n ≥ 9.
- Wang–Zhang: stars and tadpoles.
- **Settled:** the exceptional side of the Botler–Sambinelli dichotomy.
- **Open:** Bonamy–Perrett. It contains Gallai by A Thm 46.

## Flags

1. **e(G) notation clash.** In Thms 20, 28, 31 and Cors 23, 27, 33/34, 40, e(G) means the number of *missing* edges. Elsewhere it means the edges of G. Read literally, those statements are about sparse graphs. Should be e(Ḡ).
2. **JM citation.** "Theorem 3.8" does not exist in arXiv 2403.17290v1. The matching-extension statement is Theorem 8 there. Correct the number.
3. **§11.1 lemma.** A probabilistic sketch, extended to √N log N discrepancy in one paragraph. Every large-n result rests on it.
4. **Botler–Sambinelli.** S's summary is imprecise: components of max degree ≤ 3 may contain any number of triangle blocks.

The reader found no logical errors in the proofs traced (Thms 4, 16, 42–52; Prop 15; Thm 19; Cor 21).
