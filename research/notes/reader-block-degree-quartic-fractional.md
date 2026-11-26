# Reader notes: block-degree, quartic-exterior, fractional-paths

These are a reader's notes on the three papers. They have not been verified independently.

## block-degree.pdf (54 pp.)

### Main results

- **Thm 1.** If every block has Δ ≤ 9:
  - the marked bound q(F,S) ≤ ⌊(|V|−|S|)/2⌋ holds;
  - p ≤ ⌊n/2⌋ holds outside odd semi-cliques.

  The odd semi-cliques in this class have at most 9 vertices (16 graphs).
- **Thm 2** (no degree hypothesis). Absorbing an intersecting path into an odd semi-clique: p(J ∪ P) = k + 1, with both ends of P kept.
- **Thm 3:** block degree ≤ 7. **Thm 6:** block degree ≤ 8.
- **Thm 4** (any block degree). A cycle-minimum feasible mixed partition has no 9-cycle.
- **Thm 5** (degree 8). Residual cycles are disjoint, with nine path-only types.
- **Thm 7.** Hereditary block conditions, each giving the result:
  - λ(C) ≤ 3|V(C)|;
  - Δ ≤ 9;
  - edge density on cycles;
  - mad < 74/13;
  - and others.

  Corollaries: arboricity 3, planar, 3-degenerate, K5-minor-free, K3,3-minor-free, projective-planar, and surfaces with large edge-width.
- **Thm 9.** Cutwidth ≤ 8, with exceptions K3, K5−e, K5.
- **Thm 10.** Triangle-free blocks of cutwidth ≤ 10; girth-dependent cutwidth bounds.
- **Thms 11–13.** Bandwidth 5 gives p ≤ 1 + ⌊n/2⌋. Bandwidth 6 with three end-to-end paths gives p ≤ 3 + ⌊n/2⌋.
- **Thm 14.** If every two branch vertices are joined by a path with a degree-2 interior, the floor holds except for odd complete graphs.

### Architecture

1. Simultaneous induction on the marked bound and the floor.
2. Lovász's mixed partition, via an auxiliary vertex z adjacent to S.
3. Cycle-minimum residual cycles.
4. Contact thresholds: at least 6 (§3), 7 (§4), 8 (§5) common vertices.
5. Eight-contact classification (§6): the unique bad order 03476125.
6. Nine-cycle with three paths (§8); cluster restoration (§9) completes degree 7.
7. Degree 8: §10 (Thm 4), §11 (Thm 5), §12 (three-row openings).
8. Degree 9: §13, octagon packing, then four centers opened by machine.
9. Extensions: §14.

### The readiness caveat is too narrow — important

Thm 4 contains the 25,003 three-path configurations and the 1,154 boundary certificates, and it feeds Thm 5. So the following all depend on unreplayed computation, not just degree 9 and cutwidth 8:

- **degree 8** (Thm 6);
- all of Thms 7–10;
- Thms 11–13, which go through Thm 1.

**Only Thm 3 (block degree ≤ 7) and Thm 2 avoid it.**

Degree 9 also rests on further computations:

- about 4.86M placements in §13;
- 29,077 three-row openings (§12);
- the 4,477, 311,352 and 7,481 checks in §14.

Other computer checks:

| Where | What | Count |
|---|---|---|
| §4 | 6-contact subdivision sets | 494 |
| §5 | 7-contact sets | 1,348 + 989 |
| §6 | 8-contact path templates | 1,320 |
| §6 | 8-contact cycle templates | 202 |
| §11 | two-cycle tests | 36,268 |

**The paper and the index disagree.** The paper claims "The independent replay generates precisely these 25 003 cases…" and further enumerations for the 1,154. The index says there is no complete independent replay. No code is in the collection.

### Load-bearing citations

- Lovász (mixed decomposition).
- Zhang–Liu–Hong [17, Lemmas 2.5–2.6]: path–cycle pairs with ≤ 5 common vertices, exception K5 − ab plus pendants.
- Chu–Fan–Liu [8]: two cycles with ≤ 5 common vertices, exceptions K5 and K5 with one edge subdivided into a path.
- Javadi–Miralaei (full rainbow theorem).

Check the exception lists of [17] and [8] against the sources.

### Comparison with the frontier

Even Thm 3 alone (block degree ≤ 7, cut vertices unrestricted, the floor outside semi-cliques) goes strictly beyond Bonamy–Perrett (Δ ≤ 5, ceiling) and Chu–Fan–Liu (Δ ≤ 6 with independent degree-6 vertices, floor).

## quartic-exterior.pdf (25 pp.)

### Setting

S is a set of k vertices containing all even vertices. Exterior degrees are in {0, 2, 4} (Thm 2), or Δ(exterior) ≤ 4 with at most b odd exterior degrees (Cor 3).

The graph reduces to H of order ≤ N(k), with partitions lifting at exactly half the order difference. This holds for both the ordinary and the rooted versions. So the class is decidable by a finite test.

### The bound

N(k) is doubly exponential:

| k | N(k) |
|---|---|
| 1 | 55,002 |
| 2 | ≈ 5.2 × 10^12 |
| 3 | ≈ 10^22.7 |
| 4 | ≈ 10^42.4 |

The finite tests have not been run and are infeasible. This is a decidability result, not a proof.

Pyber and Fan already settle the ordinary bound for k ≤ 2. The open ordinary instances need k ≥ 3 with a triangle or a higher-degree block among the even vertices.

### Component bounds

Components are bounded when:

- they are triangle-free (Thm 9);
- triangles are disjoint (Cor 10);
- every triangle-intersection component has ≤ 2 triangles (Cor 11).

The residual obstruction is connected groups of three triangles. Five edge unions remain after the K4 return.

## fractional-paths.pdf (20 pp.)

### Main results

- **Thm 1.** max p/p_f is 2⌊n/2⌋/3 for n ≥ 6, and (n−1)/3 for 3-connected graphs of even order.
- **Thm 2.** Planar subcubic graphs with p_f = 3/2, p = ⌊n/2⌋ and log den ≈ ½√(n log n).
- Composition laws at cut vertices and bridges; endpoint realizability via blocks.
- Repeated copies sharing T: p(H_r) = rλ + O(1), by a finite LP test (Thm 13).
- **Near odd cliques:**
  - K_{2k+1} − H with m ≤ k: p_f = k + (k−m)/(2k);
  - k + x deletions: p_f = k − x/(2k).

### Bearing on Gallai

- p_f ≤ n/2 always, via Li's perfect path double cover. So fractional Gallai is a theorem, and Gallai is purely an integrality question.
- The integrality gap reaches about n/3, so LP rounding alone cannot work.
- The marked fractional bound holds unconditionally (Thm 17), but integral marked gaps are unbounded for one marked leaf.
