# Reader notes: separating-pairs.pdf (+ dense-exact-counts note)

"Separators and endpoint exchange in the rooted Gallai problem" (177 pp., Nov 25). These notes have not been independently verified.

## Main alternative

R<n: for every connected H of even order m < n and every r, p(H^r) ≤ m/2. By doubling, R<n for all n is equivalent to Gallai.

**Thm 10.16 (p.40).** Let 2h+2 be the least even order at which the rooted test fails. Then at least one of the following holds:

1. There is a 2-connected W of order 2h+1 with no matching cut, at least h+1 missing edges, and p(W) > h. This is a Bonamy–Perrett floor counterexample. It is not necessarily a Gallai counterexample.
2. Every failing host is 2-connected and 4-edge-connected, has no matching cut, and has δ ≥ 5.

### Strengthenings when alternative 1 is absent

- δ ≥ 6 (Thm 12.28).
- Six-edge-connected (Cor 13.5).
- Eulerian failing hosts have δ ≥ 10 (Cor 13.12).
- Every degree-8 vertex has an odd neighbour.
- Unconditionally: if λ = r ≥ 5 then δ ≤ 2r − 4 (Thm 13.1).

### Other properties

- Separating pairs leave exactly two odd components and at most three components overall (Cors 4.2–4.4). Components avoiding the root have order 1 or ≥ 5 (Thm A.1, computer: 2,832 patterns).
- λ ≥ ⌊(δ+1)/2⌋ + 1 (Cor 11.3).

### The odd witness (minimal by order, then by number of edges)

- No cut of ≤ 3 edges, and p(W) = h+1.
- It has at most one degree-2 vertex. If it has one, every other vertex has degree ≥ 5, the supports have degree ≥ 6, and W − {z,a,b} is connected.
- Every quintic vertex has five odd neighbours (Thm 13.34, Python-certified).
- It has at most one cubic vertex. If it has one, its neighbours have degree ≥ 6 and every other vertex has degree ≥ 5.
- **Not covered:** odd witnesses with δ ≥ 4 and no degree-2 or cubic vertex. Quartic and quintic vertices are not excluded there.

## Dense results (§14)

- **Thm 14.1.** For fixed ε, r and large n with δ ≥ (1/2+ε)n, every endpoint vector b with entries ≤ r is realised by k paths iff:
  - Σb = 2k;
  - b(v) ≡ d(v) (mod 2);
  - b(v) ≤ min{d(v), 2k − d(v)}.
- **Cor 14.2.** Gallai and the rooted bound hold exactly at δ ≥ (1/2+ε)n.
- **Thm 14.5.** At odd n = 2k+1 above the Dirac threshold, p = k iff ≥ k edges are missing. So the Bonamy–Perrett floor holds there, and the odd semi-cliques are exactly the exceptions.
- **Thm 14.8, Cor 14.9.** The same holds for robust expanders with δ ≥ αn.
- **Cors 14.24, 14.26.** Failures with δ ≥ n/2 − o(n) are within o(n²) edits of K_{n/2,n/2}.
- **Cor 14.36.** Bipartite graphs with δ ≥ (1/2−γ)n satisfy the floor and the private-leaf bound.

**Inputs.** Pfenninger (carrying the Kühn–Osthus robust-expander decomposition), Kühn–Osthus–Treglown, Ore, Bahmanian–Rodger, Csaba et al., GKO.

**dense-exact-counts note.** At δ ≥ (1/2+ε)n with Δ − δ ≤ C or (Δ − o)+ ≤ C:

p(G) = max{o/2, ⌈Δ/2⌉, ⌈m/(n−1)⌉}.

Dense Eulerian graphs decompose into exactly Δ/2 cycles. The reader checked the case analysis and found it sound.

## Open

- "The selection of a clean single split at the original budget for arbitrary two-connected odd cores remains open."
- Alternative 1 needs the Bonamy–Perrett floor for 2-connected odd graphs with no matching cut and ≥ h+1 missing edges.
- The general-δ odd witness.
- The Eulerian degree-10 configuration.
- Near-half-degree failures.

## Computation

The main even-host chain appears to be computer-free, except that Cor 4.4 uses Thm A.1.

Load-bearing computations:

- the Thm 13.34 table;
- Cor 12.18 (Lean "FiveTip.dense");
- Thm A.1 (2,832 patterns);
- the Thm 7.1 table.

No supplement is in the collection.

## Flags

- **Javadi–Miralaei is used more than 40 times**, including the equality case inside Thm 10.16.
- Many dependencies are cited only by descriptive names, which is hard to audit.
- Extraction lost the overlines in "|E(W)| ≥ h+1", which means missing edges.
- Thm 12.6 attributes a result to [6], a paper on transversal matroids. Check this.
- References [15] (Lovász 1968) and [16] (Hilton) are never cited in the text.
