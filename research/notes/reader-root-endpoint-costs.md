# Reader notes: root-endpoint-costs.pdf

"Root endpoints and cut inequalities in path decompositions" (157 pp., Nov 25). These notes have not been independently verified.

**Terminology.** F^z means F with a private leaf at z. L is the E-subgraph of F^z, i.e. the subgraph induced by the even vertices.

A "smallest failed pair" is chosen by minimising the order 2k, then |E|, then maximising the number of leaves. Later sections drift to "first failed host", and §§17–22 use "least-order failure", which minimises by order only. The abstract's "(2,2)-circuit" is never defined in the body.

## Unconditional floor results on E-subgraph classes

Write h for the number of vertices of E-degree ≥ 4 in a component.

**Thm 13.20.** If every E-component satisfies one of the following rows:

| Girth | h |
|---|---|
| ≥ 4 | ≤ 2 |
| ≥ 5 | ≤ 3 |
| ≥ 6 | ≤ 4 |
| ≥ 6t+1 | ≤ 2·3^t − 2 |

then p ≤ ⌊n/2⌋. At even order, a private leaf also fits at any vertex.

**Comparison with Fan's theorem** (each block of the E-subgraph triangle-free and subcubic). The two are incomparable:
- On single-block components, Thm 13.20 is strictly stronger.
- Fan allows unboundedly many E-degree ≥ 4 cut vertices, which Thm 13.20 does not.

**Thm 16.1.** The rows above, or E-components equal to K_{s,m} with 2 ≤ s ≤ 5 and (s even or m odd), give the floor.

**Cor 16.2.**
- E = K_{4,m} plus isolates: the rooted bound holds.
- K_{3,m}, K_{5,m}: the ceiling holds.
- K_{6,m}: the ceiling holds in some cases.

Further classes:
- **Thms 18.1, 18.3.** K_{6,m} with twin hubs; K_{2r,2s} with exterior-free vertices.
- **Cor 13.14.** A class built from Botler–Sambinelli plus a degree condition at z.
- **Two Hamilton cycles as the E-graph** (§22.14).
- **K6,6** (Thm 20.5 and others, computer-checked).
- **Theta graphs** (Thm 4.1). **Two private graphs on s, t** (Thm 5.1).

## Reductions

- **§1.** Gallai ⇔ p(G^z) ≤ k for every connected G on 2k vertices and every z. When d(z) is even and positive, p(G^z) = F2(G,z).
- **Cor 13.8.** One may restrict to z even with ≥ 3 even neighbours, where ≥ 2 of them have degree ≥ 6 (≥ 3 if j is even). Further conditions: Thm 13.7, Cor 13.9.

## Smallest failed host

- Deleting an induced path or cycle keeps the graph connected and keeps the path number at k (Thm 8.1).
- It is one 2-connected block plus at most one leaf (Thm 10.4).
- z has ≥ 3 even neighbours.
- A cubic vertex on no triangle has three even neighbours of degree ≥ 6, and is the only cubic vertex.
- Cuts have size ≥ 4.
- **Cor 12.5.** A triangle-free host has ≤ 1 degree-4 vertex.
- **Thm 14.6.** If triangle-free with a cubic vertex: every other vertex has degree ≥ 6, d(z) ≥ 8, and the mean degree is ≥ 6.
- **Thm 15.3.** No sextic vertex has 4 or 5 odd neighbours (triangle-free cubic case).
- **Thm 17.6.** A nine-common-vertex obstruction statement for two paths with the same ends.

## Finite tests (decidability only; none run except small slices)

| Result | Class | Cutoff |
|---|---|---|
| Thm 20.1 | fixed E-graph, odd components of order ≤ h | k + h·B_h(k) |
| Thm 20.3 | E = K6,6, independent exterior | 488 |
| Thm 22.4 | E = K6,6, independent exterior (improved) | 276 |
| Thm 21.1 | odd subgraph Δ ≤ 2 | 10,664 for K6,6 |
| Thms 21.3, 21.5 | forests or subcubic after ≤ b deletions | polynomial |
| Thm 22.10, Cors 22.11–22.12 | exterior Δ ≤ 4 | computable |

The triangle unions remain: "Five of the seven edge unions… remain possible."

## Computation

Load-bearing:
- Prop 3.3;
- Lemma 7.5 (with Lean);
- Prop 10.10;
- Thm 16.5;
- Thms 17.1, 17.2;
- Prop 17.5 (K9 rainbow step, Lean plus 58,905 subsets);
- Thm 20.5;
- Cor 20.6;
- Thm 20.7;
- Cor 20.8;
- Prop 20.9.

No supplement is in the collection.

**The reader independently rechecked:**
- the Thm 16.5 table (h = 2..8);
- the Thm 17.1 counts at h = 9;
- the §9 example (2,910 paths, no two-path partition);
- the Prop 17.12 order-17 example;
- the Thm 20.5 count of 184,016.

All agree with the paper.

## Flags

**Explicitly open in the text:**
- the compatible-partition existence of Cor 10.3;
- the finite-test equivalence at exterior girth ≥ 5;
- the bounded-partition hypothesis in Thm 17.6.

**Other issues:**
- The §7 results assume the odd floor.
- Superseded bounds are kept alongside newer ones.
- The same class gets two cutoffs, 488 and 276.
- The §9 example implicitly says that Arumugam–Sahul Hamid–Abraham [1, Lemma 18] fails.
- The paper cites none of the author's other manuscripts.
